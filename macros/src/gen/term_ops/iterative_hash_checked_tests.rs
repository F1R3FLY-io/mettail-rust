//! Focused generated-code checks, plus an opt-in standalone Rust fixture.

use super::*;

pub(in crate::gen::term_ops) fn fixture_language() -> LanguageDef {
    syn::parse_str(
        r#"
        name: CheckedHashFixture,
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
            PUnary . child:Proc |- "unary" child : Proc;
            PPair . left:Proc, right:Proc |- "pair" left right : Proc;
            PScalars . number:Int, flag:Bool, text:Text |- "scalars" number flag text : Proc;
            PToken . |- token@Word : Proc;
            PGuest . |- *flt(node, Open, Close) : Proc;
            PMixed . child:Proc |- before@Word child *flt(node, Open, Close) after@Word : Proc;
            POptional . *opt(child:Proc)
                |- prefix@Word *opt(before@Word child *flt(node, Open, Close)) : Proc;
            POptionalVec . *opt(children:Vec(Proc)) |- *opt(children) : Proc;
            PVector . children:Vec(Proc) |- "vector" children : Proc;
            PBag . children:HashBag(Proc) |- "bag" children : Proc;
            PSingle . pre:Proc, ^x.body:[Proc -> Proc] |- "single" pre x body : Proc;
            PMulti . children:Vec(Proc), ^[xs].body:[Proc* -> Proc]
                |- "multi" children xs body : Proc;
            PPredicate . ?guard:Guard |- "predicate" guard : Proc;
        },
        equations {}, rewrites {},
        "#,
    )
    .expect("checked hash fixture uses the production language parser")
}

fn variant(language: &LanguageDef, category: &str, label: &str) -> VariantKind {
    collect_category_variants(&format_ident!("{}", category), language)
        .into_iter()
        .find(|variant| variant.label() == label)
        .unwrap_or_else(|| panic!("missing actual {category}::{label}"))
}

pub(in crate::gen::term_ops) fn literal_label(language: &LanguageDef, category: &str) -> Ident {
    collect_category_variants(&format_ident!("{}", category), language)
        .into_iter()
        .find_map(|variant| match variant {
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                Some(label)
            },
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing native literal in {category}"))
}

#[test]
fn checked_opaque_constructor_defers_native_execution_to_its_callback() {
    let language = fixture_language();
    let emission = HashEmissionNames::checked();
    let items = syn::parse2::<syn::File>(generate_hash_task_enum(&language, &emission))
        .expect("checked task declarations parse");
    let constructor = items
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item) if item.sig.ident == emission.opaque_constructor => Some(item),
            _ => None,
        })
        .expect("checked opaque task constructor");
    let mut callbacks = Vec::new();
    let mut construction = Vec::new();
    for statement in &constructor.block.stmts {
        match statement {
            syn::Stmt::Item(syn::Item::Fn(callback)) => callbacks.push(callback),
            statement => construction.push(statement),
        }
    }
    let callbacks = quote! { #(#callbacks)* }.to_string();
    let construction = quote! { #(#construction)* }.to_string();
    assert!(callbacks.contains("try_hash_fx"), "the stored callback uses the audited leaf");
    assert!(!construction.contains("try_hash_fx"));
    assert!(!construction.contains("Hash :: hash"));
    assert!(construction.contains("Opaque"));
}

#[test]
fn checked_unsupported_whole_arms_never_emit_native_sorting_or_predicate_hashing() {
    let language = fixture_language();
    let emission = HashEmissionNames::checked();
    for category in ["Map", "Set", "Pathmap", "Bytes"] {
        let label = literal_label(&language, category);
        let arm = generate_hash_variant_arm(
            &format_ident!("{}", category),
            &variant(&language, category, &label.to_string()),
            &language,
            &emission,
        )
        .to_string();
        assert!(arm.contains("UnsupportedConstructor"), "{category}::{label}: {arm}");
        assert!(arm.contains(category) && arm.contains(&label.to_string()));
        assert!(!arm.contains("sort_by"), "refusal must precede native sorting: {arm}");
        assert!(!arm.contains("collect"), "refusal must precede entry materialization: {arm}");
        assert!(!arm.contains("try_hash_fx"), "no unaudited native leaf call: {arm}");
    }
    let arm = generate_hash_variant_arm(
        &format_ident!("Proc"),
        &variant(&language, "Proc", "PPredicate"),
        &language,
        &emission,
    )
    .to_string();
    assert!(arm.contains("UnsupportedConstructor") && arm.contains("PPredicate"));
    assert!(!arm.contains("try_hash_fx"));
}

#[test]
fn checked_generated_fixture_uses_production_layout_and_captures_executable() {
    let language = fixture_language();
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("production enum declarations");
    let enum_types: Vec<_> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(mut item) if language.types.iter().any(|ty| ty.name == item.ident) => {
                // Keep actual production fields and variants; unrelated derive
                // implementations are replaced by the existing focused emitters.
                item.attrs.clear();
                Some(item)
            },
            _ => None,
        })
        .collect();
    assert_eq!(enum_types.len(), language.types.len());
    let ordinary_clone = crate::gen::term_ops::iterative_clone::generate_iterative_clone(&language);
    let ordinary_cmp = crate::gen::term_ops::iterative_cmp::generate_iterative_cmp(&language);
    let ordinary_hash = generate_iterative_hash(&language);
    let ordinary_drop = crate::gen::term_ops::iterative_drop::generate_iterative_drop(&language);
    let emission = HashEmissionNames::checked();
    let checked_tasks = generate_hash_task_enum(&language, &emission);
    let checked_engine = generate_hash_engine(&language, &emission);
    let checked_impls = generate_hash_impls(&language, &emission);
    let proc_var = crate::gen::generate_var_label(&format_ident!("Proc"));
    let int_literal = literal_label(&language, "Int");
    let bool_literal = literal_label(&language, "Bool");
    let text_literal = literal_label(&language, "Text");
    let list_literal = literal_label(&language, "List");
    let bag_literal = literal_label(&language, "Bag");
    let map_literal = literal_label(&language, "Map");
    let set_literal = literal_label(&language, "Set");
    let pathmap_literal = literal_label(&language, "Pathmap");
    let bytes_literal = literal_label(&language, "Bytes");

    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
        use std::hash::{Hash, Hasher};
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, CheckedFxHasher, CheckedIterativeHash,
            FltHole, FltHoleId, FltNode, FltSourceRange, FltTemplateBounds, FltTemplatePiece,
            FreeVar, KeyHashFailure, OrdVar, Scope, Var};
        #(#enum_types)*
        #ordinary_clone #ordinary_cmp #ordinary_hash #ordinary_drop
        #checked_tasks #checked_engine #checked_impls

        fn initial(seed: usize) -> CheckedFxHasher {
            let mut state = CheckedFxHasher::with_seed(seed);
            29u8.hash(&mut state);
            "already populated".hash(&mut state);
            state
        }

        fn exercise<T: Hash + CheckedIterativeHash>(value: &T) {
            for seed in [0, 1, usize::MAX] {
                let start = initial(seed);
                let mut expected = start.clone();
                value.hash(&mut expected);
                let mut actual = start.clone();
                let mut trace = Vec::new();
                value.try_hash_iterative(&mut actual, &mut |work, units| {
                    trace.push((work, units)); Ok::<_, usize>(())
                }).expect("admitted generated hash");
                assert_eq!(actual.finish(), expected.finish());
                let total = trace.iter().fold((0usize, 0usize), |(w,u),(x,y)| {
                    (
                        w.checked_add(*x).expect("finite fixture work total fits usize"),
                        u.checked_add(*y).expect("finite fixture retention total fits usize"),
                    )
                });
                assert!(total.0 > 0 && total.1 > 0);
                for stop in 1..=trace.len() {
                    let mut state = start.clone();
                    let mut observed = Vec::new();
                    let failed = value.try_hash_iterative(&mut state, &mut |work, units| {
                        observed.push((work, units));
                        if observed.len() == stop { Err(stop) } else { Ok(()) }
                    });
                    assert!(matches!(failed,
                        Err(KeyHashFailure::Admission(BindingFailure::Reservation(n))) if n == stop));
                    assert_eq!(observed, trace[..stop]);
                    // Composite failure may have absorbed an admitted prefix.
                    // Discard that state; the source remains borrowed for retry.
                }
                for limit in [(total.0 - 1, total.1), (total.0, total.1 - 1), total] {
                    let mut state = start.clone();
                    let mut used = (0usize, 0usize);
                    let result = value.try_hash_iterative(&mut state, &mut |work, units| {
                        if work > limit.0 - used.0 || units > limit.1 - used.1 {
                            return Err("limit");
                        }
                        used.0 += work; used.1 += units; Ok(())
                    });
                    if limit == total {
                        assert!(result.is_ok());
                        assert_eq!(used, total);
                        assert_eq!(state.finish(), expected.finish());
                    } else {
                        assert!(matches!(result,
                            Err(KeyHashFailure::Admission(BindingFailure::Reservation("limit")))));
                    }
                }
            }
        }

        fn refuse<T: CheckedIterativeHash>(value: &T, category: &str, constructor: &str) {
            let mut state = initial(17);
            let mut calls = 0usize;
            let error = value.try_hash_iterative(&mut state, &mut |_,_| {
                calls += 1; Ok::<_, ()>(())
            }).expect_err("unsupported constructor remains explicit");
            assert!(calls > 0, "source routing is admitted");
            assert!(matches!(error,
                KeyHashFailure::UnsupportedConstructor { category: c, constructor: k }
                    if c == category && k == constructor));
        }

        fn guest() -> Arc<FltNode> {
            // Hashing observes all captured fields; it is not FLT validation.
            Arc::new(FltNode {
                selector: OrdVar(Var::Free(FreeVar::fresh_named("selector hint"))),
                selector_name: "guest".into(), category: "Syntax.Term".into(),
                open_src: "`".into(), body_src: "unparsed diagnostics".into(),
                holes: vec![
                    FltHole { id: FltHoleId(0), name: "x".into(), category: None,
                        first_occurrence: FltSourceRange::new(0, 4) },
                    FltHole { id: FltHoleId(1), name: "y".into(), category: Some("Term".into()),
                        first_occurrence: FltSourceRange::new(4, 8) },
                ],
                pieces: vec![
                    FltTemplatePiece::Text { text: "λ".into(), range: FltSourceRange::new(0,2) },
                    FltTemplatePiece::Hole { id: FltHoleId(0), range: FltSourceRange::new(2,6) },
                    FltTemplatePiece::Text { text: "x".repeat(33), range: FltSourceRange::new(6,39) },
                ],
                close_src: "`".into(), bounds: FltTemplateBounds::default(), position: 11,
            })
        }

        fn deep_small_stack() {
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                let mut value = Proc::PToken("bottom".into());
                for depth in 0..20_000 {
                    value = if depth % 2 == 0 {
                        Proc::PVector(vec![value])
                    } else {
                        // The empty-pattern closed scope is assembled without
                        // cloning, freshening or repeated binding traversal.
                        Proc::PMulti(Vec::new(), Scope::from_parts_unsafe(Vec::new(), Arc::new(value)))
                    };
                }
                let start = initial(313);
                let mut expected = start.clone();
                value.hash(&mut expected);
                let mut state = start.clone();
                let mut calls = 0usize;
                value.try_hash_iterative(&mut state, &mut |_,_| {
                    calls += 1; Ok::<_, ()>(())
                }).expect("deep admitted generated hash");
                assert_eq!(state.finish(), expected.finish());
                for stop in [1, calls / 2, calls] {
                    let mut state = start.clone();
                    let mut seen = 0usize;
                    let result = value.try_hash_iterative(&mut state, &mut |_,_| {
                        seen += 1; if seen == stop { Err(()) } else { Ok(()) }
                    });
                    assert!(matches!(result,
                        Err(KeyHashFailure::Admission(BindingFailure::Reservation(())))));
                    assert_eq!(seen, stop);
                }
                drop(value);
            }).expect("spawn small-stack hash worker").join().expect("small-stack hash worker");
        }

        fn main() {
            assert!(mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE);
            exercise(&Proc::PZero);
            exercise(&Int::#int_literal(i64::MIN));
            exercise(&Int::#int_literal(i64::MAX));
            exercise(&Bool::#bool_literal(false));
            exercise(&Bool::#bool_literal(true));
            for width in [0,1,3,4,7,8,16,17,32,33] {
                exercise(&Text::#text_literal("x".repeat(width)));
            }
            let free = FreeVar::fresh_named("diagnostic identity hint");
            exercise(&Proc::#proc_var(OrdVar(Var::Free(free.clone()))));
            exercise(&Proc::#proc_var(OrdVar(Var::Bound(mettail_runtime::BoundVar {
                scope: moniker::ScopeOffset(3), binder: moniker::BinderIndex(2),
                pretty_name: Some("ignored hint".into()),
            }))));
            exercise(&Proc::PScalars(Arc::new(Int::#int_literal(-7)),
                Arc::new(Bool::#bool_literal(true)), Arc::new(Text::#text_literal("text".into()))));
            let child = Arc::new(Proc::PToken("shared".into()));
            exercise(&Proc::PPair(child.clone(), child.clone()));
            exercise(&Proc::PGuest(guest()));
            exercise(&Proc::PMixed("prefix".into(), child.clone(), guest(), "suffix".into()));
            exercise(&Proc::POptional("prefix".into(), None, None, None));
            exercise(&Proc::POptional("prefix".into(), Some(String::new()), Some(child.clone()), Some(guest())));
            exercise(&Proc::POptionalVec(None));
            exercise(&Proc::POptionalVec(Some(Vec::new())));
            exercise(&Proc::POptionalVec(Some(vec![Proc::PZero, Proc::PToken("last".into())])));
            exercise(&Proc::PVector((0..32).map(|i| Proc::PToken(i.to_string())).collect()));
            exercise(&List::#list_literal(vec![Proc::PZero, Proc::PToken("list".into())]));
            exercise(&Proc::PSingle(Arc::new(Proc::PZero),
                Scope::from_parts_unsafe(Binder(free.clone()), child.clone())));
            exercise(&Proc::PMulti(vec![Proc::PZero],
                Scope::from_parts_unsafe(vec![Binder(free)], child)));
            let mut bag = mettail_runtime::HashBag::new();
            bag.insert_n(Proc::PToken("member".into()), 7);
            exercise(&Proc::PBag(bag));
            exercise(&Bag::#bag_literal(mettail_runtime::HashBag::new()));
            let predicate = mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "unadmitted".into(), args: Vec::new(), negated: false,
            };
            refuse(&Proc::PPredicate(predicate), "Proc", "PPredicate");
            refuse(&Map::#map_literal(mettail_runtime::HashMapLit::new()), "Map", stringify!(#map_literal));
            refuse(&Set::#set_literal(mettail_runtime::HashSetLit::new()), "Set", stringify!(#set_literal));
            refuse(&Pathmap::#pathmap_literal(mettail_runtime::PathMapLit::new()), "Pathmap", stringify!(#pathmap_literal));
            refuse(&Bytes::#bytes_literal(vec![0,1,255]), "Bytes", stringify!(#bytes_literal));
            // A cached bag hash is not a profile certificate for its members.
            let mut hidden = mettail_runtime::HashBag::new();
            hidden.insert(Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "hidden under cached summary".into(), args: Vec::new(), negated: false,
            }));
            exercise(&Proc::PBag(hidden));
            deep_small_stack();
            println!("checked generated Hash matches native streams; all cutpoints, cumulative limits, unsupported arms and 20k small-stack traversal verified");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("actual checked hash fixture Rust syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_HASH").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/hash-emitter");
        std::fs::create_dir_all(&directory).expect("create checked hash fixture directory");
        std::fs::write(directory.join("checked.rs"), fixture.to_string())
            .expect("capture actual checked hash fixture");
    }
}
