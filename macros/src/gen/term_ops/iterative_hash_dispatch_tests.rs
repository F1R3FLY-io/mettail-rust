use super::*;

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn function<'a>(file: &'a syn::File, name: &Ident) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item) if item.sig.ident == *name => Some(item),
            _ => None,
        })
        .expect("generated category handler")
}

fn nested_helpers(function: &syn::ItemFn) -> Vec<&syn::ItemFn> {
    function
        .block
        .stmts
        .iter()
        .filter_map(|statement| match statement {
            syn::Stmt::Item(syn::Item::Fn(helper)) => Some(helper),
            _ => None,
        })
        .collect()
}

#[test]
fn hash_inspection_dispatch_stays_discriminant_only_as_grammar_width_grows() {
    for width in [1, 64, 256] {
        let constructors = (0..width)
            .map(|index| format!("C{index} . child:Proc |- \"c{index}\" child : Proc;"))
            .collect::<String>();
        let language: LanguageDef = syn::parse_str(&format!(
            "name: HashInspectionWidth, types {{ Proc }}, terms {{ \
             Zero . |- \"zero\" : Proc; {constructors} }}, equations {{}}, rewrites {{}},"
        ))
        .expect("actual growing language constructor inventory");
        let emission = HashEmissionNames::inspect_contributions();
        let file = syn::parse2::<syn::File>(generate_hash_engine(&language, &emission))
            .expect("inspection engine syntax");
        let category = function(&file, &emission.handler(&format_ident!("Proc")));
        let helpers = nested_helpers(category);
        assert_eq!(helpers.len(), width + 2);
        let selector = category
            .block
            .stmts
            .iter()
            .find_map(|statement| {
                let syn::Stmt::Local(local) = statement else {
                    return None;
                };
                let syn::Pat::Type(pattern) = &local.pat else {
                    return None;
                };
                let syn::Pat::Ident(binding) = pattern.pat.as_ref() else {
                    return None;
                };
                if binding.ident != "execute" {
                    return None;
                }
                let syn::Expr::Match(selector) = local.init.as_ref()?.expr.as_ref() else {
                    return None;
                };
                Some(selector)
            })
            .expect("one typed function pointer selector");
        assert_eq!(selector.arms.len(), width + 2);
        for arm in &selector.arms {
            let syn::Expr::Path(path) = arm.body.as_ref() else {
                panic!("selector performs no payload work or calls")
            };
            let name = &path.path.segments.last().expect("helper path").ident;
            let helper = helpers
                .iter()
                .find(|helper| helper.sig.ident == *name)
                .expect("co-generated single-constructor helper");
            assert!(helper.attrs.iter().any(|attribute| match &attribute.meta {
                syn::Meta::List(list) =>
                    list.path.is_ident("inline") && list.tokens.to_string() == "never",
                _ => false,
            }));
        }
        let text = compact(quote! { #category });
        assert_eq!(text.matches("execute(stack,state,val,reserve)").count(), 1);
        assert_eq!(text.matches("reserve_binding_parts(3,1,0,reserve)").count(), 1);
        let index = text
            .find("&variant_index_proc(val)")
            .expect("existing discriminant prefix");
        let charge = text.find("reserve_binding_parts(3,1,0,reserve)").unwrap();
        let selection = text.find("letexecute:").unwrap();
        assert!(index < charge && charge < selection);
        for emission in [HashEmissionNames::ordinary(), HashEmissionNames::checked()] {
            let file = syn::parse2::<syn::File>(generate_hash_engine(&language, &emission))
                .expect("unchanged execution engine syntax");
            let category = function(&file, &emission.handler(&format_ident!("Proc")));
            assert!(nested_helpers(category).is_empty());
            assert!(!compact(quote! { #category }).contains("letexecute:"));
        }
    }
}

#[test]
fn hash_inspection_helpers_preserve_every_original_arm_and_receipt() {
    let language = checked_tests::fixture_language();
    let emission = HashEmissionNames::inspect_contributions();
    let file = syn::parse2::<syn::File>(generate_hash_engine(&language, &emission))
        .expect("full supported and refused inspection syntax");
    for ty in &language.types {
        let category_name = emission.handler(&ty.name);
        let category = function(&file, &category_name);
        let helpers = nested_helpers(category);
        let selector = category
            .block
            .stmts
            .iter()
            .find_map(|statement| {
                let syn::Stmt::Local(local) = statement else {
                    return None;
                };
                let syn::Expr::Match(selector) = local.init.as_ref()?.expr.as_ref() else {
                    return None;
                };
                Some(selector)
            })
            .expect("constructor selector match");
        let variants = collect_category_variants(&ty.name, &language);
        assert_eq!(helpers.len(), variants.len());
        for variant in &variants {
            let name = format_ident!("{}_{}", category_name, variant.label());
            let helper = helpers
                .iter()
                .find(|helper| helper.sig.ident == name)
                .expect("matching constructor helper");
            let selected = selector
                .arms
                .iter()
                .find(|arm| match arm.body.as_ref() {
                    syn::Expr::Path(path) => {
                        path.path.segments.last().expect("helper path").ident == name
                    },
                    _ => false,
                })
                .expect("matching selector arm");
            let cat = &ty.name;
            let label = variant.label();
            let expected_pattern = match variant {
                VariantKind::Nullary { .. } => quote! { #cat::#label },
                _ => quote! { #cat::#label(..) },
            };
            let selected_pattern = &selected.pat;
            assert_eq!(compact(quote! { #selected_pattern }), compact(expected_pattern));
            let syn::Stmt::Expr(syn::Expr::Match(dispatch), _) = &helper.block.stmts[0] else {
                panic!("single unchanged arm plus impossible-selector mismatch")
            };
            let actual = &dispatch.arms[0];
            let expected = generate_hash_variant_arm(&ty.name, variant, &language, &emission);
            assert_eq!(compact(quote! { #actual }), compact(expected));
            assert_eq!(dispatch.arms.len(), if variants.len() > 1 { 2 } else { 1 });
            assert_eq!(
                helper.block.stmts.len(),
                if checked_hash_variant_supported(&ty.name, variant, &language) {
                    2
                } else {
                    1
                },
                "unsupported helpers have no unreachable success tail"
            );
            assert!(!compact(quote! { #helper }).contains("reserve_binding_parts(3,1,0,reserve)"));
        }
    }
}
