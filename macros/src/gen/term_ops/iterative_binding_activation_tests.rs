//! Production checked-binding activation and original Rholang layout capture.
//!
//! Token tests establish emission boundaries. The opt-in standalone fixture
//! must additionally be compiled and executed; capture alone is not evidence
//! that the Rholang worker ran or that a public parser entrypoint is activated.

use super::*;

fn literal(language: &LanguageDef, category: &Ident) -> Ident {
    collect_category_variants(category, language)
        .into_iter()
        .find_map(|variant| match variant {
            VariantKind::Literal { label } | VariantKind::CollectionLiteral { label, .. } => {
                Some(label)
            },
            _ => None,
        })
        .expect("actual native literal constructor")
}

fn unknown_language(with_zero: bool) -> LanguageDef {
    let terms = if with_zero {
        "PZero . |- \"0\" : Proc;"
    } else {
        ""
    };
    syn::parse_str(&format!(
        "name: NativeAdmission, types {{ ![foreign::Opaque] as Proc }}, \
         terms {{ {terms} }}, equations {{}}, rewrites {{}},"
    ))
    .expect("native capability fixture uses the production language parser")
}

// Preserve every emitted category and field. Derives are replaced only by the
// ordinary operation emitters also used by the production CmpHash concern.
fn production_bundle(language: &LanguageDef) -> TokenStream {
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(language))
            .expect("production enum declarations");
    let enums: Vec<_> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(mut item) if language.types.iter().any(|ty| ty.name == item.ident) => {
                item.attrs.clear();
                Some(item)
            },
            _ => None,
        })
        .collect();
    assert_eq!(enums.len(), language.types.len(), "retain every production category");
    for item in &enums {
        assert_eq!(
            item.variants.len(),
            collect_category_variants(&item.ident, language).len(),
            "retain every variant of {}",
            item.ident
        );
    }
    let clone = generate_iterative_clone(language);
    let drop = super::super::iterative_drop::generate_iterative_drop(language);
    let cmp = super::super::iterative_cmp::generate_iterative_cmp(language);
    let hash = super::super::iterative_hash::generate_iterative_hash(language);
    let checked = generate_checked_iterative_binding(language)
        .expect("production checked companion emission");
    quote! { #(#enums)* #clone #drop #cmp #hash #checked }
}

fn assert_private_single_authorities(language: &LanguageDef, bundle: TokenStream) {
    let file = syn::parse2::<syn::File>(bundle).expect("co-located declarations parse");
    assert_eq!(
        file.items
            .iter()
            .filter(|item| matches!(item, syn::Item::Enum(item) if item.ident == "AnyClonedTerm"))
            .count(),
        1
    );
    for ty in &language.types {
        let index = format!("variant_index_{}", ty.name.to_string().to_lowercase());
        assert_eq!(
            file.items
                .iter()
                .filter(|item| matches!(item, syn::Item::Fn(item) if item.sig.ident == index))
                .count(),
            1,
            "one existing variant-index authority for {}",
            ty.name
        );
    }
    for item in file.items {
        if let syn::Item::Fn(item) = item {
            assert!(
                matches!(item.vis, syn::Visibility::Inherited),
                "generated helper {} must remain private",
                item.sig.ident
            );
        }
    }
}

#[test]
fn unknown_selected_native_default_refuses_whole_checked_profile() {
    let language = unknown_language(false);
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    assert!(matches!(plan.selected.get("Proc"), Some(VariantKind::Literal { .. })));
    assert!(!super::super::dummy_receipts::selected_defaults_supported(&language, &plan));
    let checked = generate_checked_iterative_binding(&language).expect("explicit profile refusal");
    let source = checked.to_string();
    assert!(source.contains("UnsupportedProfile"));
    for excluded in [
        "CheckedBindingLeaf",
        "CheckedBindingTask",
        "BINDING_DUMMY_CHARGES",
        "inspect_hash",
        "inspect_comparison",
        "admit_bag",
        "reserve_binding_parts",
    ] {
        assert!(!source.contains(excluded), "unexpected {excluded}: {source}");
    }
    let file = syn::parse2::<syn::File>(checked).expect("refusing trait implementation parses");
    assert_eq!(file.items.len(), language.types.len());
    assert!(
        file.items
            .iter()
            .all(|item| matches!(item, syn::Item::Impl(_))),
        "full-profile refusal emits trait implementations only, not workers or receipts"
    );
}

#[test]
fn unknown_unselected_literal_refuses_only_its_constructor() {
    let language = unknown_language(true);
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    assert!(
        matches!(plan.selected.get("Proc"), Some(VariantKind::Nullary { label }) if label == "PZero")
    );
    assert!(super::super::dummy_receipts::selected_defaults_supported(&language, &plan));
    let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
        .expect("selected PZero receipt is independent of unknown literal");
    let names = CloneEmissionNames::checked(&language, &receipts);
    let category = format_ident!("Proc");
    let variant = VariantKind::Literal { label: literal(&language, &category) };
    let arm = generate_visit_arm(&category, &variant, &names).to_string();
    assert!(arm.contains("UnsupportedConstructor"));
    assert!(arm.contains("\"Proc\""));
    assert!(arm.contains(&format!("\"{}\"", variant.label())));
    assert!(!arm.contains("CheckedBindingLeaf"));
    assert!(!arm.contains("clone"));
    let companion = generate_checked_iterative_binding(&language).expect("partial profile");
    assert!(companion.to_string().contains("BINDING_DUMMY_CHARGES"));
    assert!(companion.to_string().contains("CheckedBindingTask"));
    assert_private_single_authorities(&language, production_bundle(&language));
}

#[test]
fn known_fixture_keeps_one_private_wrapper_and_variant_index() {
    let language = super::super::iterative_hash::checked_tests::fixture_language();
    assert_private_single_authorities(&language, production_bundle(&language));
}

#[test]
fn actual_rholang_profile_and_original_layout_binding_capture() {
    let language = super::super::iterative_cmp::census_tests::actual_rholang();
    assert!(
        language.types.len() > 20,
        "the actual specification, not a reduced Bag language"
    );
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    assert!(
        super::super::dummy_receipts::selected_defaults_supported(&language, &plan),
        "actual Rholang selected defaults must have a checked profile"
    );
    super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
        .expect("actual Rholang selected receipt projection");
    let proc = format_ident!("Proc");
    let variants = collect_category_variants(&proc, &language);
    assert!(variants.iter().any(|v| matches!(v,
        VariantKind::Collection { label, coll_type: CollectionType::HashBag, .. } if label == "PPar")));
    assert!(variants.iter().any(|v| matches!(v,
        VariantKind::MultiBinder { label, binder_cat, body_cat, .. }
        if label == "PNew" && binder_cat == "Name" && body_cat == "Proc")));
    let name_var = crate::gen::generate_var_label(&format_ident!("Name"));
    let set_literal = literal(&language, &format_ident!("Set"));
    let set_literal_name = set_literal.to_string();
    let bundle = production_bundle(&language);
    assert_private_single_authorities(&language, bundle.clone());

    // These negative modules compile ordinary unknown payloads without giving
    // them any checked leaf trait. The partial profile still executes PZero.
    let unknown_full = unknown_language(false);
    let unknown_partial = unknown_language(true);
    let full_label = literal(&unknown_full, &proc);
    let partial_label = literal(&unknown_partial, &proc);
    let partial_label_name = partial_label.to_string();
    let full_bundle = production_bundle(&unknown_full);
    let partial_bundle = production_bundle(&unknown_partial);
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case,
            non_camel_case_types, unused_imports)]
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, BindingOperation, CheckedIterativeBinding,
            FreeVar, HashBag, OrdVar, Scope, Var};
        #bundle

        mod unsupported_default {
            use super::{Binder, BindingFailure, BindingOperation, CheckedIterativeBinding,
                FreeVar, OrdVar, Scope, Var};
            mod foreign {
                #[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
                pub struct Opaque;
            }
            #full_bundle
            pub fn check() {
                let value = Proc::#full_label(foreign::Opaque);
                let mut calls = 0;
                let result = value.try_copy_iterative(BindingOperation::Clone,
                    &mut |_, _| { calls += 1; Ok::<_, ()>(()) });
                assert!(matches!(result, Err(BindingFailure::UnsupportedProfile)));
                assert_eq!(calls, 0, "profile refusal precedes worker admission");
            }
        }
        mod unsupported_literal {
            use super::{Binder, BindingFailure, BindingOperation, CheckedIterativeBinding,
                FreeVar, OrdVar, Scope, Var};
            mod foreign {
                #[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
                pub struct Opaque;
            }
            #partial_bundle
            pub fn check() {
                assert!(matches!(Proc::PZero.try_copy_iterative(BindingOperation::Clone,
                    &mut |_, _| Ok::<_, ()>(())), Ok(Proc::PZero)));
                let value = Proc::#partial_label(foreign::Opaque);
                assert!(matches!(value.try_copy_iterative(BindingOperation::Clone,
                    &mut |_, _| Ok::<_, ()>(())),
                    Err(BindingFailure::UnsupportedConstructor { category: "Proc", constructor })
                        if constructor == #partial_label_name));
            }
        }

        fn pools_empty() {
            CHECKED_BINDING_TASK_POOL.with(|pool| {
                let tasks = pool.take(); assert!(tasks.is_empty()); pool.set(tasks);
            });
            CHECKED_BINDING_RESULT_POOL.with(|pool| {
                let slots = pool.take(); assert!(slots.is_empty()); pool.set(slots);
            });
        }
        fn exercise(source: &Proc, operation: BindingOperation<'_>) -> Proc {
            let mut trace = Vec::new();
            let result = source.try_copy_iterative(operation, &mut |w, u| {
                trace.push((w, u)); Ok::<_, ()>(())
            }).expect("actual Rholang checked binding");
            pools_empty();
            let total = trace.iter().fold((0usize, 0usize), |(w, u), (x, y)|
                (w.checked_add(*x).expect("test work total"),
                 u.checked_add(*y).expect("test retention total")));
            assert!(total.0 > 0 && total.1 > 0);
            for limit in [total, (total.0 - 1, total.1), (total.0, total.1 - 1)] {
                let mut remaining = limit;
                let checked = source.try_copy_iterative(operation, &mut |w, u| {
                    if w > remaining.0 || u > remaining.1 { return Err(()); }
                    remaining.0 -= w; remaining.1 -= u; Ok(())
                });
                assert_eq!(checked.is_ok(), limit == total, "one shared finite budget");
                pools_empty();
            }
            #[derive(Debug)] struct Stop(Box<usize>);
            let mut cuts = vec![1, 2, trace.len() / 2, trace.len()];
            cuts.retain(|&cut| cut > 0 && cut <= trace.len());
            cuts.sort_unstable(); cuts.dedup();
            for stop in cuts {
                let mut failure = Some(Stop(Box::new(stop)));
                let identity = failure.as_ref().expect("test refusal").0.as_ref() as *const usize;
                let mut seen = 0;
                let failed = source.try_copy_iterative(operation, &mut |_, _| {
                    seen += 1;
                    if seen == stop { Err(failure.take().expect("single refusal")) } else { Ok(()) }
                });
                match failed {
                    Err(BindingFailure::Reservation(error)) => {
                        assert_eq!(error.0.as_ref() as *const usize, identity);
                        assert_eq!(*error.0, stop);
                    },
                    _ => panic!("preserve the original non-Clone reservation error"),
                }
                assert_eq!(seen, stop); pools_empty();
            }
            result
        }
        fn free(name: &FreeVar<String>) -> Proc {
            Proc::PDrop(Arc::new(Name::#name_var(OrdVar(Var::Free(name.clone())))))
        }
        fn entries(value: &Proc) -> &HashBag<Proc> {
            match value { Proc::PPar(entries) => entries, _ => panic!("actual PPar") }
        }
        fn bound(value: &Proc, depth: u32) {
            let Proc::PDrop(name) = value else { panic!("actual drop/name edge") };
            assert!(matches!(name.as_ref(), Name::#name_var(OrdVar(Var::Bound(v)))
                if v.scope == moniker::ScopeOffset(depth) && v.binder == moniker::BinderIndex(0)));
        }
        fn main() {
            unsupported_default::check(); unsupported_literal::check();
            let name = FreeVar::fresh_named("actual-rholang");
            let binders = [Binder(name.clone())];
            let mut bag = HashBag::new(); bag.insert_n(free(&name), 3); bag.insert_n(Proc::PZero, 2);
            let source = Proc::PPar(bag);
            let original = entries(&source).iter().map(|(key, count)|
                (key as *const Proc, count)).collect::<Vec<_>>();
            assert!(exercise(&source, BindingOperation::Clone) == source.clone());
            for state in [moniker::ScopeState::new(), moniker::ScopeState::new().incr().incr()] {
                let close = BindingOperation::Close { state, binders: &binders };
                let open = BindingOperation::Open { state, binders: &binders };
                let closed = exercise(&source, close);
                assert_eq!(entries(&closed).len(), 5);
                assert_eq!(entries(&closed).distinct_len(), 2);
                let (child, count) = entries(&closed).iter().find(|(key, _)|
                    matches!(key, Proc::PDrop(_))).expect("bound original entry");
                assert_eq!(count, 3); bound(child, state.depth().0);
                assert!(exercise(&closed, open) == source);
                let body = Arc::new(source.clone());
                let scoped = Proc::PNew(Scope::from_parts_unsafe(Vec::new(), body.clone()));
                let cloned = exercise(&scoped, BindingOperation::Clone);
                let Proc::PNew(scope) = &cloned else { panic!("actual PNew") };
                assert!(Arc::ptr_eq(scope.unsafe_body(), &body), "Clone keeps scope body shallow");
                let closed = exercise(&scoped, close);
                let Proc::PNew(scope) = &closed else { panic!("actual PNew") };
                let (child, count) = entries(scope.unsafe_body()).iter().find(|(key, _)|
                    matches!(key, Proc::PDrop(_))).expect("bound scoped entry");
                assert_eq!(count, 3); bound(child, state.depth().0 + 1);
                assert!(exercise(&closed, open) == scoped);
            }
            let anomalous = Proc::PPar(entries(&source).rebuild_binding_entries(
                vec![(free(&name), 0), (Proc::PZero, 2)]));
            assert_eq!(entries(&anomalous).len(), 5);
            assert_eq!(entries(&anomalous).distinct_len(), 2);
            let cloned = exercise(&anomalous, BindingOperation::Clone);
            assert_eq!(entries(&cloned).len(), 2);
            assert_eq!(entries(&cloned).distinct_len(), 1);
            let closed = exercise(&anomalous, BindingOperation::Close {
                state: moniker::ScopeState::new(), binders: &binders,
            });
            assert_eq!(entries(&closed).len(), 5);
            assert_eq!(entries(&closed).distinct_len(), 2);
            let (zero, count) = entries(&closed).iter().find(|(_, count)| *count == 0)
                .expect("stored zero retained by binding");
            assert_eq!(count, 0); bound(zero, 0);
            assert_eq!(entries(&source).iter().map(|(key, count)|
                (key as *const Proc, count)).collect::<Vec<_>>(), original);
            let unsupported = Set::#set_literal(mettail_runtime::HashSetLit::new());
            assert!(matches!(unsupported.try_copy_iterative(BindingOperation::Clone,
                &mut |_, _| Ok::<_, ()>(())),
                Err(BindingFailure::UnsupportedConstructor { category: "Set", constructor })
                    if constructor == #set_literal_name));
            pools_empty();
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("full actual Rholang binding fixture parses");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_BINDING").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/clone-emitter");
        std::fs::create_dir_all(&directory)
            .expect("create actual Rholang binding capture directory");
        std::fs::write(directory.join("checked-rholang.rs"), fixture.to_string())
            .expect("capture all actual Rholang layouts and production binding companion");
    }
}
