use super::*;

fn function<'a>(file: &'a syn::File, name: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item) if item.sig.ident == name => Some(item),
            _ => None,
        })
        .expect("generated function")
}

fn selector<'a>(block: &'a syn::Block, name: &str) -> &'a syn::ExprMatch {
    block
        .stmts
        .iter()
        .find_map(|statement| {
            let syn::Stmt::Local(local) = statement else {
                return None;
            };
            let syn::Pat::Type(typed) = &local.pat else {
                return None;
            };
            let syn::Pat::Ident(binding) = typed.pat.as_ref() else {
                return None;
            };
            if binding.ident != name {
                return None;
            }
            let syn::Expr::Match(selection) = local.init.as_ref()?.expr.as_ref() else {
                return None;
            };
            Some(selection)
        })
        .expect("typed function-pointer selector")
}

#[test]
fn checked_dispatch_is_discriminant_only_at_both_levels_as_grammar_width_grows() {
    for width in [1, 64, 256] {
        let constructors = (0..width)
            .map(|index| format!("C{index} . child:Proc |- \"c{index}\" child : Proc;"))
            .collect::<String>();
        let language: LanguageDef = syn::parse_str(&format!(
            "name: DispatchWidth, types {{ Proc }}, terms {{ \
             Zero . |- \"zero\" : Proc; {constructors} }}, equations {{}}, rewrites {{}},"
        ))
        .expect("growing real LanguageDef constructor family");
        let plan = super::super::iterative_drop::select_dummy_plan(&language);
        let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
            .expect("fixture dummy receipts");
        let emission = CloneEmissionNames::checked(&language, &receipts);
        let file = syn::parse2::<syn::File>(generate_engine(&language, &emission))
            .expect("generated checked engine syntax");
        let driver = function(&file, "copy_binding_iterative");
        let syn::Stmt::Expr(syn::Expr::While(worklist), _) = &driver.block.stmts[0] else {
            panic!("one existing iterative worklist")
        };
        let tasks = selector(&worklist.body, "execute");
        assert_eq!(
            tasks.arms.len(),
            width + 1,
            "one Visit and one Assemble per recursive constructor"
        );
        let category = function(&file, "binding_handle_proc");
        let constructors = selector(&category.block, "visit");
        assert_eq!(constructors.arms.len(), width + 2, "recursive constructors, zero and variable");
        for arm in tasks.arms.iter().chain(&constructors.arms) {
            let syn::Expr::Path(helper) = arm.body.as_ref() else {
                panic!("selector must not contain arm-local calls, Results or payload work")
            };
            let helper = function(
                &file,
                &helper
                    .path
                    .segments
                    .last()
                    .expect("helper name")
                    .ident
                    .to_string(),
            );
            assert!(
                helper.attrs.iter().any(|attribute| match &attribute.meta {
                    syn::Meta::List(list) =>
                        list.path.is_ident("inline") && list.tokens.to_string() == "never",
                    _ => false,
                }),
                "selected helper must retain its own native frame"
            );
        }
        let driver_source = quote! { #driver }.to_string();
        assert_eq!(
            driver_source
                .matches("execute (stack , results , task , operation , reserve , dummy_charges)")
                .count(),
            1
        );
        let ordinary = generate_engine(&language, &CloneEmissionNames::ordinary()).to_string();
        assert!(!ordinary.contains("binding_task_"));
        assert!(!ordinary.contains("reserve_binding_parts"));
        assert!(!ordinary.contains("let execute"));
    }
}

#[test]
fn refused_constructor_helper_has_no_unreachable_success_tail() {
    let language: LanguageDef = syn::parse_str(
        "name: RefusedDispatch, types { ![foreign::Opaque] as Proc }, \
         terms { Zero . |- \"zero\" : Proc; }, equations {}, rewrites {},",
    )
    .expect("partial checked profile");
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
        .expect("known nullary default");
    let emission = CloneEmissionNames::checked(&language, &receipts);
    let category = format_ident!("Proc");
    let literal = collect_category_variants(&category, &language)
        .into_iter()
        .find(|variant| matches!(variant, VariantKind::Literal { .. }))
        .expect("unknown native literal");
    assert!(!checked_constructor_supported(&category, &literal, &emission));
    let file = syn::parse2::<syn::File>(generate_engine(&language, &emission))
        .expect("checked helper syntax");
    let helper = function(&file, &format!("binding_handle_proc_{}", literal.label()));
    assert!(matches!(
        helper.block.stmts.last(),
        Some(syn::Stmt::Expr(syn::Expr::Match(_), None))
    ));
    assert!(quote! { #helper }
        .to_string()
        .contains("UnsupportedConstructor"));
}
