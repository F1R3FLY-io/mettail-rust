//! Ordinary Eq/Ord emitter baselines, using the production grammar parser.
//! These pin emitted syntax and scheduling; they are not native execution tests.

use super::*;

fn fixture_language() -> LanguageDef {
    syn::parse_str(
        r#"
        name: OrdinaryCmpSurfaces,
        types {
            Proc ![i64] as Int ![bool] as Bool ![str] as Text
            ![Vec<u8>] as Bytes ![Vec<Proc>] as List
            ![mettail_runtime::HashBag<Proc>] as Bag
            ![mettail_runtime::HashSetLit<Proc>] as Set
            ![mettail_runtime::HashMapLit<Proc, Proc>] as Map
            ![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap
        },
        terms {
            PZero . |- "0" : Proc;
            PScalars . number:Int, flag:Bool, text:Text |- "scalars" number flag text : Proc;
            PMixed . child:Proc |- before@Word child *flt(node, Open, Close) after@Word : Proc;
            POptional . *opt(child:Proc)
                |- prefix@Word *opt(before@Word child *flt(node, Open, Close)) : Proc;
            POptionalVec . *opt(children:Vec(Proc)) |- *opt(children) : Proc;
            PVector . children:Vec(Proc) |- "vector" children : Proc;
            PBag . children:HashBag(Proc) |- "bag" children : Proc;
            PSingle . pre:Proc, ^x.body:[Proc -> Proc] |- "single" pre x body : Proc;
            PMulti . children:Vec(Proc), ^[xs].body:[Proc* -> Proc]
                |- "multi" children xs body : Proc;
        },
        equations {}, rewrites {},
        "#,
    )
    .expect("ordinary comparison fixture uses the production language parser")
}

fn variant(language: &LanguageDef, label: &str) -> VariantKind {
    collect_category_variants(&format_ident!("Proc"), language)
        .into_iter()
        .find(|variant| variant.label() == label)
        .unwrap_or_else(|| panic!("missing actual Proc::{label} classification"))
}

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn ordered(source: &str, needles: &[&str]) {
    let mut remaining = source;
    for needle in needles {
        let offset = remaining
            .find(needle)
            .unwrap_or_else(|| panic!("missing ordered fragment {needle} in {source}"));
        remaining = &remaining[offset + needle.len()..];
    }
}

fn arms(language: &LanguageDef, label: &str) -> (String, String) {
    let category = format_ident!("Proc");
    let variant = variant(language, label);
    (
        compact(generate_eq_variant_arm(
            &category,
            &variant,
            language,
            &CmpEmissionNames::ordinary(),
        )),
        compact(generate_cmp_variant_arm(
            &category,
            &variant,
            language,
            &CmpEmissionNames::ordinary(),
        )),
    )
}

#[test]
fn ordinary_comparison_surface_census_and_exact_expansion_capture() {
    let language = fixture_language();
    for category in ["Int", "Bool", "Text", "Bytes"] {
        let category = format_ident!("{}", category);
        let variants = collect_category_variants(&category, &language);
        let leaf = variants
            .iter()
            .find(|v| matches!(v, VariantKind::Literal { .. }))
            .expect("actual native literal classification");
        assert!(compact(generate_eq_variant_arm(
            &category,
            leaf,
            &language,
            &CmpEmissionNames::ordinary()
        ))
        .contains("ifa!=b{returnfalse;}"));
        assert!(compact(generate_cmp_variant_arm(
            &category,
            leaf,
            &language,
            &CmpEmissionNames::ordinary()
        ))
        .contains("a.cmp(b)"));
    }
    let proc = format_ident!("Proc");
    let variants = collect_category_variants(&proc, &language);
    let variable = variants
        .iter()
        .find(|v| matches!(v, VariantKind::Var { .. }))
        .expect("actual OrdVar variant");
    assert!(compact(generate_eq_variant_arm(
        &proc,
        variable,
        &language,
        &CmpEmissionNames::ordinary()
    ))
    .contains("ifa!=b{returnfalse;}"));
    assert!(compact(generate_cmp_variant_arm(
        &proc,
        variable,
        &language,
        &CmpEmissionNames::ordinary()
    ))
    .contains("a.cmp(b)"));
    for (category, expected) in [
        ("List", CollectionType::Vec),
        ("Bag", CollectionType::HashBag),
        ("Set", CollectionType::HashSet),
        ("Map", CollectionType::HashMap),
        ("Pathmap", CollectionType::PathMap),
    ] {
        assert!(collect_category_variants(&format_ident!("{}", category), &language)
            .iter()
            .any(|v| matches!(v, VariantKind::CollectionLiteral { element_cat, coll_type, .. }
                if element_cat == "Proc" && *coll_type == expected)));
    }
    assert!(matches!(variant(&language, "PSingle"), VariantKind::Binder { .. }));
    assert!(matches!(variant(&language, "PMulti"), VariantKind::MultiBinder { .. }));
    assert!(matches!(
        variant(&language, "PVector"),
        VariantKind::Collection { coll_type: CollectionType::Vec, .. }
    ));
    assert!(matches!(
        variant(&language, "PBag"),
        VariantKind::Collection { coll_type: CollectionType::HashBag, .. }
    ));
    for (name, language) in [
        ("ordinary-surfaces", language),
        ("singleton", crate::gen::singleton_collection_language_for_tests()),
    ] {
        // Capture the real assembly: task/pools, discriminants, both engines,
        // and every category's Eq/Ord implementations, with no filtered arms.
        let expansion = generate_iterative_cmp(&language);
        syn::parse2::<syn::File>(expansion.clone()).expect("ordinary comparison Rust item syntax");
        if let Ok(phase) = std::env::var("METTAIL_CMP_EXPANSION_PHASE") {
            assert!(matches!(phase.as_str(), "before" | "after"));
            let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../target/verification/cmp-emitter")
                .join(&phase);
            std::fs::create_dir_all(&directory).expect("create comparison capture directory");
            let path = directory.join(format!("{name}.tokens"));
            let tokens = expansion.to_string();
            if phase == "before" && path.exists() {
                assert_eq!(
                    std::fs::read_to_string(path).expect("read baseline"),
                    tokens,
                    "never overwrite a changed ordinary comparison baseline"
                );
            } else {
                std::fs::write(path, tokens).expect("capture exact ordinary comparison output");
            }
        }
    }
}

#[test]
fn ordinary_native_comparisons_remain_at_their_original_evaluation_positions() {
    let language = fixture_language();
    let VariantKind::Regular { fields, .. } = variant(&language, "PMixed") else {
        panic!("actual mixed regular variant")
    };
    assert_eq!(fields.len(), 4);
    assert!(fields[0].is_opaque_leaf() && fields[2].is_opaque_leaf());
    let (eq, cmp) = arms(&language, "PMixed");
    ordered(&eq, &["ifl0!=r0", "CmpTask::CmpProc(&**l1", "ifl2!=r2", "ifl3!=r3"]);
    ordered(
        &cmp,
        &[
            "letord=l0.cmp(r0)",
            "stack.push(CmpTask::Verdict(l3.cmp(r3)))",
            "stack.push(CmpTask::Verdict(l2.cmp(r2)))",
            "CmpTask::CmpProc(&**l1",
        ],
    );
    assert!(!cmp.contains("l1.cmp(r1)"), "category child must remain deferred");
    let VariantKind::Regular { fields, .. } = variant(&language, "POptional") else {
        panic!("actual optional regular variant")
    };
    assert_eq!(fields.len(), 4);
    assert!(fields[1].is_optional && fields[1].is_opaque_leaf());
    assert!(fields[2].is_optional && !fields[2].is_opaque_leaf());
    assert!(fields[3].is_optional && fields[3].is_opaque_leaf());
    let (eq, cmp) = arms(&language, "POptional");
    ordered(&eq, &["ifl1!=r1", "l2.as_ref()", "ifl3!=r3"]);
    ordered(&cmp, &["letord=l1.cmp(r1)", "Verdict(l3.cmp(r3))", "l2.as_ref()"]);
    let engine =
        syn::parse2::<syn::File>(generate_cmp_engine(&language, &CmpEmissionNames::ordinary()))
            .expect("Ord engine syntax");
    let driver = engine
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item) if item.sig.ident == "cmp_iterative" => Some(&item.block),
            _ => None,
        })
        .expect("ordinary Ord driver");
    let driver = compact(quote! { #driver });
    assert!(driver.contains("CmpTask::Verdict(ord)=>"));
    assert!(
        !driver.contains(".cmp("),
        "the driver consumes verdicts, not native leaf comparisons"
    );
}

#[test]
fn ordinary_collection_comparisons_keep_existing_pda_and_vector_order() {
    let language = fixture_language();
    for label in ["PVector", "POptionalVec"] {
        let (eq, cmp) = arms(&language, label);
        ordered(&eq, &[".len()!=", "CmpTask::CmpProc("]);
        ordered(&cmp, &["CmpTask::Verdict(", ".len().cmp(", "CmpTask::CmpProc("]);
        assert!(cmp.contains(".rev()"), "vector elements precede the length verdict on pop");
    }
    for category in ["Bag", "Map"] {
        let category = format_ident!("{}", category);
        let variant = collect_category_variants(&category, &language)
            .into_iter()
            .find(|v| matches!(v, VariantKind::CollectionLiteral { .. }))
            .expect("actual unordered literal");
        let eq = compact(generate_eq_variant_arm(
            &category,
            &variant,
            &language,
            &CmpEmissionNames::ordinary(),
        ));
        let cmp = compact(generate_cmp_variant_arm(
            &category,
            &variant,
            &language,
            &CmpEmissionNames::ordinary(),
        ));
        assert!(eq.contains("eq_unordered_collection(mettail_runtime::CollectionCmpPda::new("));
        assert!(cmp
            .contains("CmpTask::StartCollection(Box::new(mettail_runtime::CollectionCmpPda::new("));
        for arm in [&eq, &cmp] {
            assert!(!arm.contains(".sort"), "reuse the existing resumable collection machine");
            let item = if category == "Map" {
                "pair(__key,__value)"
            } else {
                "repeated(__item,__count)"
            };
            assert_eq!(arm.matches(item).count(), 2, "preserve both complete input rosters");
        }
    }
}

#[test]
fn ordinary_scope_patterns_keep_native_identity_and_evaluation_order() {
    let language = fixture_language();
    for label in ["PSingle", "PMulti"] {
        let (eq, cmp) = arms(&language, label);
        ordered(&eq, &["CmpTask::CmpProc(", "ifl_pat!=r_pat", "CmpTask::CmpProc(l_body,r_body)"]);
        ordered(
            &cmp,
            &[
                "DefaultHasher::new()",
                "Hash::hash(p,&muth)",
                "Hasher::finish(&h)",
                "letpat_ord=",
                "CmpTask::CmpProc(l_body,r_body)",
                "CmpTask::Verdict(pat_ord)",
                "CmpTask::CmpProc(",
            ],
        );
        assert!(!cmp.contains("FxHasher"), "scope ordering is not the Fx Hash profile");
        if label == "PMulti" {
            ordered(
                &cmp,
                &["l_pats.len().cmp(&r_pats.len()).then_with(", ".zip(r_pats.iter())", ".find("],
            );
        }
    }
}
