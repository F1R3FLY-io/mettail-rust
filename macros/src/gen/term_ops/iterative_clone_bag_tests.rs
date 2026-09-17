//! Actual-layout checked Bag binding fixture; captured for standalone execution.

use super::*;

#[test]
fn unsupported_checked_shapes_refuse_without_ordinary_assembly() {
    let language = super::super::iterative_hash::checked_tests::fixture_language();
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
        .expect("complete fixture receipt projection");
    let checked = CloneEmissionNames::checked(&language, &receipts);
    let ordinary = CloneEmissionNames::ordinary();
    let mut rejected = Vec::new();
    for ty in &language.types {
        for variant in collect_category_variants(&ty.name, &language) {
            let label = variant.label().to_string();
            assert!(checked_constructor_supported(&ty.name, &variant, &ordinary));
            if checked_constructor_supported(&ty.name, &variant, &checked) {
                continue;
            }
            let arm = generate_visit_arm(&ty.name, &variant, &checked).to_string();
            assert!(arm.contains("UnsupportedConstructor"), "{arm}");
            assert!(arm.contains(&format!("\"{}\"", ty.name)));
            assert!(arm.contains(&format!("\"{label}\"")));
            for forbidden in ["clone", "stack", "results", "collect", "reserve"] {
                assert!(!arm.contains(forbidden), "refusal entered {forbidden}: {arm}");
            }
            assert!(generate_assemble_task(&ty.name, &variant, &checked).is_none());
            assert!(generate_assemble_arm(&ty.name, &variant, false, &checked).is_none());
            assert!(generate_assemble_task(&ty.name, &variant, &ordinary).is_some());
            assert!(!generate_visit_arm(&ty.name, &variant, &ordinary)
                .to_string()
                .contains("UnsupportedConstructor"));
            rejected.push((ty.name.to_string(), label));
        }
    }
    for category in ["Set", "Map", "Pathmap"] {
        assert!(rejected.iter().any(|(name, _)| name == category));
    }
    assert!(rejected.iter().any(|(_, label)| label == "POptionalVec"));
    // Exercise closed classifier branches absent from the parsed Hash fixture.
    // These are the production descriptors, not a second eligibility model.
    let category = format_ident!("Proc");
    let assert_refused = |variant: &VariantKind| {
        assert!(!checked_constructor_supported(&category, variant, &checked));
        assert!(checked_constructor_supported(&category, variant, &ordinary));
        let label = variant.label().to_string();
        let arm = generate_visit_arm(&category, variant, &checked).to_string();
        assert!(arm.contains("UnsupportedConstructor"), "{arm}");
        assert!(arm.contains("\"Proc\""));
        assert!(arm.contains(&format!("\"{label}\"")));
        for forbidden in ["clone", "stack", "results", "collect", "reserve"] {
            assert!(!arm.contains(forbidden), "refusal entered {forbidden}: {arm}");
        }
        assert!(generate_assemble_task(&category, variant, &checked).is_none());
        assert!(generate_assemble_arm(&category, variant, false, &checked).is_none());
        assert!(!generate_visit_arm(&category, variant, &ordinary)
            .to_string()
            .contains("UnsupportedConstructor"));
    };
    for coll_type in [CollectionType::HashSet, CollectionType::HashMap, CollectionType::PathMap] {
        assert_refused(&VariantKind::Collection {
            label: format_ident!("ExcludedDirect"),
            element_cat: category.clone(),
            coll_type,
        });
    }
    let optional_bag = FieldInfo {
        category: category.clone(),
        is_collection: true,
        coll_type: Some(CollectionType::HashBag),
        is_predicate: false,
        is_optional: true,
        opaque_leaf: None,
    };
    assert_refused(&VariantKind::Regular {
        label: format_ident!("ExcludedOptionalBag"),
        fields: vec![optional_bag.clone()],
    });
    // A non-collection optional scope prefield is also outside the admitted
    // scope recipe; refusal must not depend merely on collection presence.
    let optional_scalar = FieldInfo {
        is_collection: false,
        coll_type: None,
        ..optional_bag.clone()
    };
    for field in [optional_bag, optional_scalar] {
        assert_refused(&VariantKind::Binder {
            label: format_ident!("ExcludedSingle"),
            pre_scope_fields: vec![field.clone()],
            binder_cat: category.clone(),
            body_cat: category.clone(),
        });
        assert_refused(&VariantKind::MultiBinder {
            label: format_ident!("ExcludedMulti"),
            pre_scope_fields: vec![field],
            binder_cat: category.clone(),
            body_cat: category.clone(),
        });
    }
    use crate::gen::native_carrier::{NativeCarrierStorage, ZipperAccess};
    for storage in [NativeCarrierStorage::Direct, NativeCarrierStorage::Arc] {
        for access in [ZipperAccess::Read, ZipperAccess::Write] {
            assert_refused(&VariantKind::RecursiveNativeLiteral {
                label: format_ident!("ExcludedZipper"),
                carrier: NativeRecursiveCarrier::Zipper {
                    storage,
                    access,
                    key_category: category.clone(),
                    value_category: category.clone(),
                },
            });
        }
    }
    let refused = VariantKind::Refused {
        label: format_ident!("BadCarrier"),
        message: "unknown recursive carrier".into(),
    };
    assert!(generate_visit_arm(&format_ident!("Proc"), &refused, &checked)
        .to_string()
        .contains("compile_error"));
    syn::parse2::<syn::File>(generate_task_enum(&language, &checked))
        .expect("checked task census parses");
    syn::parse2::<syn::File>(generate_engine(&language, &checked))
        .expect("checked handlers contain only supported assembly shapes");
}

#[test]
fn checked_bags_preserve_binding_order_counts_scopes_and_cleanup() {
    let language: LanguageDef = syn::parse_str(
        r#"
        name: CheckedBagBindingFixture,
        types { Proc ![mettail_runtime::HashBag<Proc>] as Bag },
        terms {
            PZero . |- "0" : Proc;
            PUnary . child:Proc |- "unary" child : Proc;
            PBag . entries:HashBag(Proc) |- "bag" entries : Proc;
            PLiteral . entries:Bag |- "literal" entries : Proc;
            PMixed . first:HashBag(Proc), tail:Proc, second:HashBag(Proc)
                |- "mixed" first tail second : Proc;
            PBagScope . entries:HashBag(Proc), ^x.body:[Proc -> Proc]
                |- "bagScope" entries x body : Proc;
        },
        equations {}, rewrites {},
        "#,
    )
    .expect("required Bag binding language");
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("production enum declarations");
    let enum_types: Vec<_> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(mut item) if language.types.iter().any(|ty| ty.name == item.ident) => {
                // Retain every production field and variant; only replace
                // derives by the same standalone production operation emitters.
                item.attrs.clear();
                Some(item)
            },
            _ => None,
        })
        .collect();
    assert_eq!(enum_types.len(), language.types.len());
    let var = crate::gen::generate_var_label(&format_ident!("Proc"));
    let bag_label = collect_category_variants(&format_ident!("Bag"), &language)
        .into_iter()
        .find_map(|variant| match variant {
            VariantKind::CollectionLiteral {
                label,
                coll_type: CollectionType::HashBag,
                ..
            } => Some(label),
            _ => None,
        })
        .expect("production Bag literal variant");
    let plan = super::super::iterative_drop::select_dummy_plan(&language);
    let receipts = super::super::dummy_receipts::generate_dummy_receipts(&language, &plan)
        .expect("required Bag fixture dummy receipts");
    let checked = CloneEmissionNames::checked(&language, &receipts);
    let ordinary = generate_iterative_clone(&language);
    let tasks = generate_task_enum(&language, &checked);
    let engine = generate_engine(&language, &checked);
    let impls = generate_impls(&language, &checked);
    let drop = super::super::iterative_drop::generate_iterative_drop(&language);
    let cmp = super::super::iterative_cmp::generate_iterative_cmp(&language);
    let hash = super::super::iterative_hash::generate_iterative_hash(&language);
    let inspection = super::super::iterative_hash::generate_hash_contribution_inspection(&language);
    let admission =
        super::super::hashbag_rebuild_admission::generate_hashbag_rebuild_admission(&language);
    let table = receipts.tokens;
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case)]
        use std::sync::Arc;
        use mettail_runtime::{Binder, BindingFailure, BindingOperation,
            CheckedIterativeBinding, FreeVar, HashBag, OrdVar, Scope, Var};
        #(#enum_types)*
        #ordinary #tasks #engine #impls #drop #cmp #hash #table
        #inspection #admission

        fn pools_empty() {
            CHECKED_BINDING_TASK_POOL.with(|pool| {
                let tasks = pool.take(); assert!(tasks.is_empty()); pool.set(tasks);
            });
            CHECKED_BINDING_RESULT_POOL.with(|pool| {
                let results = pool.take(); assert!(results.is_empty()); pool.set(results);
            });
        }
        fn exercise<T: CheckedIterativeBinding>(source: &T, operation: BindingOperation<'_>) -> T {
            let mut trace = Vec::new();
            let result = source.try_copy_iterative(operation, &mut |w,u| {
                trace.push((w,u)); Ok::<_, ()>(())
            }).expect("checked Bag copy succeeds");
            pools_empty();
            // The bounded fixture checks every cut for short runs, and selected
            // early/middle/late cuts for larger native admission traces.
            let mut cuts = vec![1, 2, 3, trace.len()/4, trace.len()/2,
                trace.len().saturating_sub(1), trace.len()];
            if trace.len() <= 64 { cuts.extend(1..=trace.len()); }
            cuts.retain(|&n| n > 0 && n <= trace.len());
            cuts.sort_unstable(); cuts.dedup();
            #[derive(Debug)] struct Stop(Box<usize>);
            for stop in cuts {
                let mut error = Some(Stop(Box::new(stop)));
                let identity = error.as_ref().expect("fresh refusal payload").0.as_ref() as *const usize;
                let mut observed = Vec::new();
                let refused = source.try_copy_iterative(operation, &mut |w,u| {
                    observed.push((w,u));
                    if observed.len() == stop { Err(error.take().expect("single refusal consumes payload")) } else { Ok(()) }
                });
                match refused {
                    Err(BindingFailure::Reservation(error)) => {
                        assert_eq!(error.0.as_ref() as *const usize, identity);
                        assert_eq!(*error.0, stop);
                    },
                    _ => panic!("original non-Clone refusal payload must propagate"),
                }
                assert_eq!(observed, trace[..stop]); pools_empty();
            }
            let total = trace.iter().fold((0usize,0usize), |(w,u),(x,y)| (w+x,u+y));
            for limit in [total, (total.0-1,total.1), (total.0,total.1-1)] {
                let mut used = (0,0);
                let copied = source.try_copy_iterative(operation, &mut |w,u| {
                    if w > limit.0-used.0 || u > limit.1-used.1 { return Err(()); }
                    used.0 += w; used.1 += u; Ok(())
                });
                assert_eq!(copied.is_ok(), limit == total); pools_empty();
            }
            result
        }
        fn free(name: &FreeVar<String>) -> Proc { Proc::#var(OrdVar(Var::Free(name.clone()))) }
        fn bag(name: &FreeVar<String>, count: usize) -> HashBag<Proc> {
            let mut result = HashBag::new();
            result.insert_n(free(name), count); result.insert_n(Proc::PZero, 2); result
        }
        fn direct(value: &Proc) -> &HashBag<Proc> {
            match value { Proc::PBag(entries) => entries, _ => panic!("direct Bag") }
        }
        fn bound(value: &Proc, depth: u32) {
            assert!(matches!(value, Proc::#var(OrdVar(Var::Bound(v)))
                if v.scope == moniker::ScopeOffset(depth) && v.binder == moniker::BinderIndex(0)));
        }
        fn check_entries(entries: &HashBag<Proc>, expected: &Proc, count: usize) {
            assert_eq!(entries.len(), count+2);
            assert_eq!(entries.iter().count(), 2);
            assert_eq!(entries.iter().find(|(key,_)| *key == expected).map(|(_,n)| n), Some(count));
            assert_eq!(entries.iter().find(|(key,_)| matches!(key,Proc::PZero)).map(|(_,n)| n), Some(2));
        }
        fn main() {
            let name = FreeVar::fresh_named("bag-free");
            let roster = [Binder(name.clone())];
            let child = Arc::new(free(&name));
            let pattern = Binder(FreeVar::fresh_named("inner"));
            let source = Proc::PBag(bag(&name,3));
            let original = direct(&source).iter().map(|(k,n)| (k as *const Proc,n)).collect::<Vec<_>>();
            let copied = exercise(&source, BindingOperation::Clone);
            assert!(copied == source);
            assert_eq!(direct(&source).iter().map(|(k,n)| (k as *const Proc,n)).collect::<Vec<_>>(),original);
            // Native binding can retain a zero-count owned key. Width means
            // stored entries, not total multiplicity or positive survivors.
            let with_zero = Proc::PBag(direct(&source).rebuild_binding_entries(
                vec![(free(&name),0),(Proc::PZero,2)]));
            assert_eq!(direct(&with_zero).iter().count(),2);
            let clone_zero = exercise(&with_zero,BindingOperation::Clone);
            assert_eq!(direct(&clone_zero).iter().count(),1);
            assert_eq!(direct(&clone_zero).len(),2);
            let closed_zero = exercise(&with_zero,BindingOperation::Close {
                state:moniker::ScopeState::new(),binders:&roster,
            });
            assert_eq!(direct(&closed_zero).iter().count(),2);
            assert_eq!(direct(&closed_zero).len(),5);
            let (zero_key,_) = direct(&closed_zero).iter().find(|(_,n)| *n == 0).expect("stored zero key retained");
            bound(zero_key,0);
            for empty in [Proc::PBag(HashBag::new()),Proc::PLiteral(Arc::new(Bag::#bag_label(HashBag::new())))] {
                for operation in [BindingOperation::Clone, BindingOperation::Close {
                    state: moniker::ScopeState::new(), binders: &roster,
                }] { assert!(exercise(&empty,operation) == empty); }
            }
            for state in [moniker::ScopeState::new(),moniker::ScopeState::new().incr().incr()] {
                let close = BindingOperation::Close {state,binders:&roster};
                let open = BindingOperation::Open {state,binders:&roster};
                let expected = free(&name).try_copy_iterative(close,&mut |_,_| Ok::<_,()>(())).expect("single variable binding");
                for input in [Proc::PBag(bag(&name,3)),
                    Proc::PLiteral(Arc::new(Bag::#bag_label(bag(&name,3))))] {
                    let cloned = exercise(&input,BindingOperation::Clone);
                    assert!(cloned == input);
                    if let (Proc::PLiteral(before),Proc::PLiteral(after)) = (&input,&cloned) {
                        assert!(Arc::ptr_eq(before,after));
                        let Bag::#bag_label(_) = before.as_ref() else {panic!("literal source");};
                        let copied_literal = exercise(before.as_ref(),BindingOperation::Clone);
                        assert!(&copied_literal == before.as_ref());
                    }
                    let closed = exercise(&input,close);
                    let entries = match &closed {
                        Proc::PBag(entries) => entries,
                        Proc::PLiteral(entries) => match entries.as_ref() {
                            Bag::#bag_label(entries) => entries,
                            _ => panic!("literal Bag variant"),
                        },
                        _ => panic!("Bag surface"),
                    };
                    check_entries(entries,&expected,3);
                    let opened = exercise(&closed,open); assert!(opened == input);
                }
                let mixed = Proc::PMixed(bag(&name,3),child.clone(),bag(&name,7));
                for operation in [BindingOperation::Clone,close] {
                    let copied = exercise(&mixed,operation);
                    let Proc::PMixed(first,tail,second) = &copied else {panic!("mixed fields");};
                    if matches!(operation,BindingOperation::Clone) {
                        assert!(Arc::ptr_eq(tail,&child));
                        check_entries(first,&free(&name),3); check_entries(second,&free(&name),7);
                    } else {
                        bound(tail,state.depth().0);
                        check_entries(first,&expected,3); check_entries(second,&expected,7);
                        assert!(exercise(&copied,open) == mixed);
                    }
                }
                let scoped = Proc::PBagScope(bag(&name,3),
                    Scope::from_parts_unsafe(pattern.clone(),child.clone()));
                for operation in [BindingOperation::Clone,close] {
                    let copied = exercise(&scoped,operation);
                    let Proc::PBagScope(entries,scope) = &copied else {panic!("Bag pre-scope");};
                    assert_eq!(scope.unsafe_pattern().0.unique_id,pattern.0.unique_id);
                    if matches!(operation,BindingOperation::Clone) {
                        assert!(Arc::ptr_eq(scope.unsafe_body(),&child));
                        check_entries(entries,&free(&name),3);
                    } else {
                        check_entries(entries,&expected,3); bound(scope.unsafe_body(),state.depth().0+1);
                        assert!(exercise(&copied,open) == scoped);
                    }
                }
            }
            // Opening distinct binder indices to one identity creates a real
            // binding collision. Pretty names reveal which original key won.
            let a = FreeVar::fresh_named("a"); let b = FreeVar::fresh_named("b");
            let mut entries = HashBag::new(); entries.insert_n(free(&a),3); entries.insert_n(free(&b),7);
            let distinct = Proc::PBag(entries);
            let closed = exercise(&distinct, BindingOperation::Close {
                state: moniker::ScopeState::new(),binders:&[Binder(a),Binder(b)],
            });
            let common = FreeVar::fresh_named("common");
            let mut first = common.clone(); first.pretty_name = Some("index zero".into());
            let mut second = common.clone(); second.pretty_name = Some("index one".into());
            let merged_roster = [Binder(first),Binder(second)];
            let order = direct(&closed).iter().map(|(key,count)| {
                let Proc::#var(OrdVar(Var::Bound(v))) = key else {panic!("bound collision key");};
                assert_eq!(count,if v.binder.0 == 0 {3} else {7});
                (v.binder.0 as usize,count)
            }).collect::<Vec<_>>();
            assert_eq!(order.len(),2);
            let merged = exercise(&closed, BindingOperation::Open {
                state: moniker::ScopeState::new(),binders:&merged_roster,
            });
            let entries = direct(&merged); assert_eq!(entries.len(),10); assert_eq!(entries.iter().count(),1);
            let (key,count) = entries.iter().next().expect("collision winner"); assert_eq!(count,order[1].1);
            let Proc::#var(OrdVar(Var::Free(winner))) = key else {panic!("opened collision key");};
            assert_eq!(winner.pretty_name,merged_roster[order[0].0].0.pretty_name);
            assert_eq!(winner.unique_id,common.unique_id);
            // Clone recomputes its native total from the surviving count;
            // binding deliberately retains the pre-collision total instead.
            let clone = exercise(&merged,BindingOperation::Clone);
            assert_eq!(direct(&clone).len(),order[1].1);
            assert_eq!(direct(&clone).iter().next().expect("cloned collision winner").1,order[1].1);

            std::thread::Builder::new().stack_size(256*1024).spawn(|| {
                let name = FreeVar::fresh_named("deep");
                let mut source = Proc::PBag(bag(&name,3));
                for _ in 0..4096 { source = Proc::PUnary(Arc::new(source)); }
                let copied = source.try_copy_iterative(BindingOperation::Close {
                    state: moniker::ScopeState::new(),binders:&[Binder(name)],
                }, &mut |_,_| Ok::<_,()>(())).expect("deep heap-worklist binding");
                let mut cursor = &copied;
                for _ in 0..4096 { cursor = match cursor {
                    Proc::PUnary(child) => child,
                    _ => panic!("deep shape preserved"),
                }; }
                let entries = direct(cursor); assert_eq!(entries.len(),5);
                let (key,_) = entries.iter().find(|(key,_)| !matches!(key,Proc::PZero)).expect("deep bound key");
                bound(key,0); pools_empty();
                drop(copied); drop(source); pools_empty();
            }).expect("spawn bounded-stack Bag fixture").join().expect("bounded-stack Bag fixture");
            pools_empty();
            println!("checked generated Bag binding: source-order collision, scopes, shallow sharing, refusal, and stack safety verified");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("generated checked Bag fixture syntax");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_BINDING").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/clone-emitter");
        std::fs::create_dir_all(&directory).expect("create checked Bag fixture directory");
        std::fs::write(directory.join("checked-bags.rs"), fixture.to_string())
            .expect("write actual-layout checked Bag fixture");
    }
}
