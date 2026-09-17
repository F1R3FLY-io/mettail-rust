//! Source-observation checks over every actual Rholang enum and field.
//!
//! The standalone fixture intentionally replaces unrelated term operations
//! with sentinels: cloning is unavailable, and hashing/equality are forbidden
//! during admission. Container construction uses distinct constructor tags,
//! not this fixture's equality as an implementation of Rholang semantics.
//! This is generated checker evidence, not parser/lowerer integration evidence.

use super::*;
use crate::gen::term_ops::iterative_cmp::census_tests::actual_rholang;
use crate::gen::term_ops::subst::collect_category_variants;
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn actual_rholang_checked_source_tags_cover_every_original_constructor() {
    let language = actual_rholang();
    let emitted = generate_checked_source(&language);
    let file = syn::parse2::<syn::File>(emitted.clone()).expect("generated checker syntax");
    let tags = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Mod(module) if module.ident == "source_constructor" => {
                module.content.as_ref()
            },
            _ => None,
        })
        .expect("public category-specific tags");
    let actual: BTreeMap<_, BTreeSet<_>> = tags
        .1
        .iter()
        .filter_map(|item| match item {
            syn::Item::Enum(item) => Some((
                item.ident.to_string(),
                item.variants.iter().map(|v| v.ident.to_string()).collect(),
            )),
            _ => None,
        })
        .collect();
    let expected: BTreeMap<_, BTreeSet<_>> = language
        .types
        .iter()
        .map(|category| {
            (
                category.name.to_string(),
                collect_category_variants(&category.name, &language)
                    .iter()
                    .map(|v| v.label().to_string())
                    .collect(),
            )
        })
        .collect();
    assert_eq!(actual, expected, "exact actual constructor identity, including refused forms");
    assert_eq!(actual.values().map(BTreeSet::len).sum::<usize>(), 1990);
    let compact: String = emitted.to_string().split_whitespace().collect();
    for forbidden in [
        ".clone(",
        ".unbind(",
        ".unbind2(",
        "unsafe{",
        "body_src",
        "parse_via_",
        "GroundTerm",
    ] {
        assert!(!compact.contains(forbidden), "source observation emitted {forbidden}");
    }
}

#[test]
fn actual_rholang_checked_source_capture() {
    let language = actual_rholang();
    let file = syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
        .expect("actual enum source");
    let enums: Vec<_> = file
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
    assert_eq!(enums.len(), language.types.len());
    for item in &enums {
        assert_eq!(item.variants.len(), collect_category_variants(&item.ident, &language).len());
    }
    let sentinels = enums.iter().map(|item| {
        let name = &item.ident;
        quote! {
            impl Clone for #name {
                fn clone(&self) -> Self { panic!("checker must not clone original terms") }
            }
            impl PartialEq for #name {
                fn eq(&self, other: &Self) -> bool {
                    GATE_ACTIVE.with(|active| assert!(!active.get(), "checker used term equality"));
                    std::mem::discriminant(self) == std::mem::discriminant(other)
                }
            }
            impl Eq for #name {}
            impl std::hash::Hash for #name {
                fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                    GATE_ACTIVE.with(|active| assert!(!active.get(), "checker hashed a term"));
                    std::hash::Hash::hash(&std::mem::discriminant(self), state)
                }
            }
        }
    });
    let all_tags = language.types.iter().flat_map(|category| {
        let cat = category.name.clone();
        collect_category_variants(&cat, &language).into_iter().map(move |variant| {
            let label = variant.label();
            let cat_name = cat.to_string();
            let constructor_name = label.to_string();
            quote! { (SourceConstructor::#cat(source_constructor::#cat::#label), #cat_name, #constructor_name) }
        })
    });
    let checker = generate_checked_source(&language);
    let policy_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../languages/src/rholang/source_profile.rs")
        .canonicalize()
        .expect("the actual host policy")
        .to_string_lossy()
        .into_owned();
    let fixture = quote! {
        #![allow(dead_code, unused_variables, unreachable_patterns, non_snake_case,
            non_camel_case_types, unused_imports)]
        use std::sync::Arc;
        use std::cell::{Cell, RefCell};
        use mettail_runtime::{Binder, BindingFailure, FltNode, FreeVar, HashBag,
            HashMapLit, OrdVar, Scope, Var};
        thread_local! { static GATE_ACTIVE: Cell<bool> = const { Cell::new(false) }; }
        #(#enums)*
        #(#sentinels)*
        #checker
        #[path = #policy_path]
        mod host_policy;
        use host_policy::{RholangSourceProfile, SourceRole};
        type GateError<E> = SourceProfileError<E, SourceRole>;
        type Transition = fn(SourceRole) -> SourceRole;

        struct Active;
        impl Active {
            fn enter() -> Self {
                GATE_ACTIVE.with(|active| assert!(!active.replace(true)));
                Self
            }
        }
        impl Drop for Active {
            fn drop(&mut self) { GATE_ACTIVE.with(|active| active.set(false)); }
        }
        struct Traced {
            seen: RefCell<Vec<SourceConstructor>>,
        }
        impl SourceProfile for Traced {
            type Role = SourceRole;
            fn fields(&self, tag: SourceConstructor) -> Option<&'static [Option<Transition>]> {
                self.seen.borrow_mut().push(tag);
                RholangSourceProfile.fields(tag)
            }
        }
        fn walk<E>(source: &Proc, reserve: &mut impl FnMut(usize, usize) -> Result<(), E>)
            -> (Result<(), GateError<E>>, Vec<SourceConstructor>)
        {
            let trace = Traced { seen: RefCell::new(Vec::new()) };
            let _active = Active::enter();
            let mut callback: &mut dyn FnMut(usize, usize) -> Result<(), E> = reserve;
            let result = source.try_check_source_profile(SourceRole::Term, &trace, &mut callback);
            (result, trace.seen.into_inner())
        }
        fn tags(source: &Proc) -> Vec<SourceConstructor> {
            let (result, seen) = walk(source, &mut |_, _| Ok::<_, ()>(()));
            result.expect("admitted actual source");
            seen
        }
        fn constructors(source: &Proc) -> Vec<&'static str> {
            tags(source).iter().map(|tag| tag.constructor_name()).collect()
        }
        fn refused(source: &Proc, expected: &'static str, role: SourceRole, ordinal: usize) {
            let (result, seen) = walk(source, &mut |_, _| Ok::<_, ()>(()));
            match result {
                Err(SourceProfileError::Unsupported { constructor, role: actual, ordinal: at }) => {
                    assert_eq!(constructor.constructor_name(), expected);
                    assert_eq!(actual, role); assert_eq!(at, ordinal);
                    assert_eq!(seen.last(), Some(&constructor));
                    assert_eq!(seen.len(), ordinal + 1);
                },
                other => panic!("wrong source refusal: {:?}", other),
            }
        }
        fn exercise_cuts(source: &Proc) {
            let mut trace = Vec::new();
            let (success, tags_before) = walk(source, &mut |w, u| {
                trace.push((w, u)); Ok::<_, ()>(())
            });
            success.expect("successful reference trace");
            let total = trace.iter().fold((0usize, 0usize), |(w, u), (x, y)|
                (w.checked_add(*x).expect("finite work"), u.checked_add(*y).expect("finite units")));
            assert!(total.0 > 0 && total.1 > 0);
            for limit in [(0, 0), total, (total.0 - 1, total.1), (total.0, total.1 - 1)] {
                let mut left = limit;
                let (result, _) = walk(source, &mut |w, u| {
                    if w > left.0 || u > left.1 { return Err(()); }
                    left.0 -= w; left.1 -= u; Ok(())
                });
                assert_eq!(result.is_ok(), limit == total);
                if limit == total { assert_eq!(left, (0, 0)); }
                else { assert!(matches!(result,
                    Err(SourceProfileError::Reservation(BindingFailure::Reservation(()))))); }
            }
            #[derive(Debug)] struct Cancel(Box<usize>);
            for cut in 1..=trace.len() {
                let mut failure = Some(Cancel(Box::new(cut)));
                let identity = failure.as_ref().unwrap().0.as_ref() as *const usize;
                let mut paid = Vec::new();
                let (result, seen) = walk(source, &mut |w, u| {
                    paid.push((w, u));
                    if paid.len() == cut { Err(failure.take().unwrap()) } else { Ok(()) }
                });
                match result {
                    Err(SourceProfileError::Reservation(BindingFailure::Reservation(cancel))) => {
                        assert_eq!(cancel.0.as_ref() as *const usize, identity);
                        assert_eq!(*cancel.0, cut);
                    },
                    _ => panic!("original non-Clone cancellation must survive every cut"),
                }
                assert_eq!(paid, trace[..cut]);
                assert!(tags_before.starts_with(&seen), "refusal cannot reorder source observations");
                assert_eq!(tags(source), tags_before, "normal failure cleanup cannot mutate source");
            }
        }
        fn input(guard: Proc) -> Proc {
            Proc::PForUser(vec![ForRow::ForRowSingleWhere(
                Arc::new(InputBind::InputBindEmpty(Arc::new(Name::NQuoteNil))),
                Arc::new(guard))], Arc::new(Proc::PZero))
        }
        fn scoped(body: Proc) -> Proc {
            Proc::PNew(Scope::from_parts_unsafe(
                vec![Binder(FreeVar::fresh_named("original"))], Arc::new(body)))
        }
        fn ddl(body: Proc) -> Proc {
            Proc::DdlModule("M".to_owned(), vec![
                DdlModuleItem::DdlModuleTheoryItem(Arc::new(
                    DdlTheoryExpr::DdlTheoryDataImplicit(Arc::new(body)))),
                DdlModuleItem::DdlModuleProcItem(Arc::new(Proc::PZero)),
            ])
        }
        fn invalid_policies() {
            enum Broken { Arity, MissingChild, InventedChild }
            impl SourceProfile for Broken {
                type Role = SourceRole;
                fn fields(&self, tag: SourceConstructor) -> Option<&'static [Option<Transition>]> {
                    fn same(role: SourceRole) -> SourceRole { role }
                    match self {
                        Self::Arity => Some(&[]),
                        Self::MissingChild => Some(&[None]),
                        Self::InventedChild => Some(&[Some(same)]),
                    }
                }
            }
            for (source, broken) in [
                (Proc::Not(Arc::new(Proc::PZero)), Broken::Arity),
                (Proc::Not(Arc::new(Proc::PZero)), Broken::MissingChild),
                (Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named("x")))), Broken::InventedChild),
            ] {
                let _active = Active::enter();
                assert!(matches!(source.try_check_source_profile(SourceRole::Term, &broken,
                    &mut |_, _| Ok::<_, ()>(())), Err(SourceProfileError::InvalidPolicy { ordinal: 0, .. })));
            }
        }
        fn production_policy_transitions() {
            use source_constructor as sc;
            use SourceConstructor as Tag;
            use SourceRole::*;
            for incoming in [Term, Name, Pattern, NamePattern, Guard, Declaration] {
                let policy = RholangSourceProfile;
                for tag in [Tag::Proc(sc::Proc::PPar), Tag::Name(sc::Name::NParen)] {
                    assert_eq!(policy.fields(tag).unwrap()[0].unwrap()(incoming), incoming);
                }
                for tag in [Tag::Name(sc::Name::NQuote), Tag::Name(sc::Name::NQuoteShort)] {
                    assert_eq!(policy.fields(tag).unwrap()[0].unwrap()(incoming),
                        if incoming == NamePattern { Pattern } else { Term });
                }
                for tag in [Tag::Proc(sc::Proc::And), Tag::Proc(sc::Proc::Or),
                    Tag::Proc(sc::Proc::Implies), Tag::Proc(sc::Proc::Not)] {
                    for field in policy.fields(tag).unwrap() {
                        assert_eq!(field.unwrap()(incoming), if incoming == Guard { Guard } else { Term });
                    }
                }
                for (tag, slot, expected) in [
                    (Tag::Proc(sc::Proc::POutput), 0, Name),
                    (Tag::Proc(sc::Proc::POutput), 1, Term),
                    (Tag::InputBind(sc::InputBind::InputBind), 0, NamePattern),
                    (Tag::InputBind(sc::InputBind::InputBindQuoted), 0, Pattern),
                    (Tag::ForRow(sc::ForRow::ForRowSingleWhere), 1, Guard),
                    (Tag::Proc(sc::Proc::DdlModule), 1, Declaration),
                    (Tag::DdlTheoryExpr(sc::DdlTheoryExpr::DdlTheoryData), 0, Declaration),
                    (Tag::DdlTheoryExpr(sc::DdlTheoryExpr::DdlTheoryData), 1, Term),
                ] {
                    assert_eq!(policy.fields(tag).unwrap()[slot].unwrap()(incoming), expected);
                }
            }
            for tag in [Tag::Proc(sc::Proc::PFlt), Tag::Proc(sc::Proc::PFltFence),
                Tag::Proc(sc::Proc::PFltBrace)] {
                assert!(RholangSourceProfile.fields(tag).unwrap()[0].is_none());
            }
            assert!(RholangSourceProfile.fields(Tag::Proc(sc::Proc::MethodCall)).unwrap()[1].is_none());
        }
        fn unsupported_carrier() {
            struct Permit;
            impl SourceProfile for Permit {
                type Role = SourceRole;
                fn fields(&self, _: SourceConstructor) -> Option<&'static [Option<Transition>]> {
                    fn same(role: SourceRole) -> SourceRole { role }
                    Some(&[Some(same)])
                }
            }
            let source = Set::SetLit(mettail_runtime::HashSetLit::new());
            let _active = Active::enter();
            assert!(matches!(source.try_check_source_profile(SourceRole::Term, &Permit,
                &mut |_, _| Ok::<_, ()>(())), Err(SourceProfileError::UnsupportedCarrier { ordinal: 0, .. })));
        }
        fn deep_small_stack() {
            std::thread::Builder::new().stack_size(128 * 1024).spawn(|| {
                eprintln!("small-stack: constructing original deep source");
                let mut source = Proc::PZero;
                for _ in 0..10_000 {
                    source = Proc::PParInfix(Arc::new(source), Arc::new(Proc::PZero));
                }
                eprintln!("small-stack: checking original source");
                assert_eq!(tags(&source).len(), 20_001);
                let mut calls = 0;
                let (result, prefix) = walk(&source, &mut |_, _| {
                    calls += 1;
                    if calls == 50_000 { Err(()) } else { Ok(()) }
                });
                assert!(result.is_err());
                assert!(prefix.len() > 1000 && prefix.len() < 10_000,
                    "cancellation drops a deep pending frontier of borrowed sibling jobs");
                eprintln!("small-stack: draining fixture ownership iteratively");
                // Fixture-only ownership drain; this checks no production Drop claim.
                loop {
                    match source {
                        Proc::PParInfix(inner, sibling) => {
                            assert!(matches!(sibling.as_ref(), Proc::PZero));
                            source = match Arc::try_unwrap(inner) {
                                Ok(value) => value,
                                Err(_) => panic!("checker retained source ownership"),
                            };
                        },
                        Proc::PZero => break,
                        _ => panic!("unexpected fixture chain"),
                    }
                }
            }).expect("small-stack checker thread").join().expect("stack-safe borrowed walk");
        }
        fn main() {
            let mut admitted = (0, 0);
            for (tag, category, constructor) in [#(#all_tags),*] {
                assert_eq!(tag.category_name(), category);
                assert_eq!(tag.constructor_name(), constructor);
                if let Some(fields) = RholangSourceProfile.fields(tag) {
                    admitted.0 += 1; admitted.1 += fields.len();
                }
            }
            assert_eq!(admitted, (144, 231));
            production_policy_transitions();
            let shared = Arc::new(Proc::PZero);
            let aliases = Proc::PParInfix(shared.clone(), shared.clone());
            assert_eq!(constructors(&aliases), ["PParInfix", "PZero", "PZero"]);
            exercise_cuts(&aliases);
            assert_eq!(Arc::strong_count(&shared), 3, "checker retains no owner");

            let scoped_source = scoped(Proc::POutputNil(Arc::new(Proc::PZero)));
            assert_eq!(constructors(&scoped_source), ["PNew", "POutputNil", "PZero"]);
            exercise_cuts(&scoped_source);
            let uris = Proc::PNewUris(vec![Uri::UriText("`rho:io:stdout`".to_owned())],
                Scope::from_parts_unsafe(Vec::new(), Arc::new(Proc::PZero)));
            assert_eq!(constructors(&uris), ["PNewUris", "UriText", "PZero"]);
            exercise_cuts(&uris);
            let boolean = Proc::CastBool(Arc::new(Bool::BoolLit(true)));
            let nested = ddl(input(Proc::Not(Arc::new(boolean))));
            exercise_cuts(&nested);
            assert!(constructors(&nested).contains(&"DdlTheoryDataImplicit"));
            let negative = Proc::CastInt(Arc::new(Int::NegInt(Arc::new(Int::NumLit(7)))));
            assert_eq!(constructors(&negative), ["CastInt", "NegInt", "NumLit"]);
            exercise_cuts(&negative);
            let method = Proc::MethodCall(Arc::new(Proc::PZero), "ignored method token".into(),
                vec![Proc::POutputNilEmpty, Proc::MapEmpty]);
            assert_eq!(constructors(&method), ["MethodCall", "PZero", "POutputNilEmpty", "MapEmpty"]);
            exercise_cuts(&method);
            let explicit_data = Proc::DdlTheory("T".into(), vec![], Arc::new(
                DdlTheoryExpr::DdlTheoryData(Arc::new(DdlTheoryExpr::DdlTheoryEmpty),
                    Arc::new(Proc::PZero))));
            assert_eq!(constructors(&explicit_data), ["DdlTheory", "DdlTheoryData", "DdlTheoryEmpty", "PZero"]);
            exercise_cuts(&explicit_data);

            let list = Proc::CastList(Arc::new(List::ListLit(vec![Proc::PZero,
                Proc::POutputNilEmpty, Proc::PPersistOutputNilEmpty])));
            assert_eq!(constructors(&list), ["CastList", "ListLit", "PZero", "POutputNilEmpty", "PPersistOutputNilEmpty"]);
            exercise_cuts(&list);
            let mut map = HashMapLit::new();
            map.insert(Proc::PZero, Proc::POutputNilEmpty);
            map.insert(Proc::PPersistOutputNilEmpty, Proc::MapEmpty);
            let map = Proc::CastMap(Arc::new(Map::MapLit(map)));
            assert_eq!(constructors(&map), ["CastMap", "MapLit", "PZero", "POutputNilEmpty", "PPersistOutputNilEmpty", "MapEmpty"]);
            exercise_cuts(&map);

            let mut bag = HashBag::new();
            bag.insert_n(Proc::PZero, 7); bag.insert_n(Proc::POutputNilEmpty, 3);
            let original = bag.iter().map(|(key, _)| match key {
                Proc::PZero => "PZero", Proc::POutputNilEmpty => "POutputNilEmpty", _ => unreachable!(),
            }).collect::<Vec<_>>();
            let bag = Proc::PPar(bag);
            assert_eq!(&constructors(&bag)[1..], original.as_slice());
            assert_eq!(tags(&bag).len(), 3, "multiplicity does not duplicate source occurrences");
            exercise_cuts(&bag);
            let Proc::PPar(entries) = &bag else { unreachable!() };
            let retained_zero = Proc::PPar(entries.rebuild_binding_entries(vec![
                (Proc::PZero, 0), (Proc::POutputNilEmpty, 3)]));
            assert_eq!(tags(&retained_zero).len(), 3, "stored zero-count keys remain original occurrences");
            exercise_cuts(&retained_zero);

            for source in [Proc::PFlt, Proc::PFltFence, Proc::PFltBrace] {
                let tiny = source(Arc::new(FltNode::new("rx".into(), "Regex".into(),
                    "x".into(), vec![], 0).unwrap()));
                let large = source(Arc::new(FltNode::new("rx".into(), "Regex".into(),
                    "/* Theory NeverParse { new x in error } */".repeat(1000), vec![], 0).unwrap()));
                let mut small_trace = Vec::new(); let mut large_trace = Vec::new();
                walk(&tiny, &mut |w, u| { small_trace.push((w, u)); Ok::<_, ()>(()) }).0.unwrap();
                walk(&large, &mut |w, u| { large_trace.push((w, u)); Ok::<_, ()>(()) }).0.unwrap();
                assert_eq!(small_trace, large_trace, "native FLT text is opaque to host source admission");
                assert_eq!(tags(&large).len(), 1);
                exercise_cuts(&tiny);
                for position in 0..5 {
                    let flt = source(Arc::new(FltNode::new("rx".into(), "Regex".into(),
                        "/* new x in error */".into(), vec![], 0).unwrap()));
                    let nested = match position {
                        0 => scoped(flt),
                        1 => { let mut entries = HashBag::new(); entries.insert(flt); Proc::PPar(entries) },
                        2 => ddl(flt),
                        3 => input(flt),
                        4 => Proc::PForUser(vec![ForRow::ForRowSingleNoWhere(Arc::new(
                            InputBind::InputBindQuoted(Arc::new(flt), Arc::new(Name::NQuoteNil))))],
                            Arc::new(Proc::PZero)),
                        _ => unreachable!(),
                    };
                    assert_eq!(constructors(&nested).iter().filter(|name|
                        matches!(**name, "PFlt" | "PFltFence" | "PFltBrace")).count(), 1);
                    exercise_cuts(&nested);
                }
            }
            refused(&Proc::Err, "Err", SourceRole::Term, 0);
            refused(&Proc::CastBag(Arc::new(Bag::BagLit(HashBag::new()))), "CastBag", SourceRole::Term, 0);
            refused(&Proc::CastSet(Arc::new(Set::SetLit(mettail_runtime::HashSetLit::new()))), "CastSet", SourceRole::Term, 0);
            refused(&Proc::LamProc(Scope::from_parts_unsafe(Binder(FreeVar::fresh_named("x")),
                Arc::new(Proc::Err))), "LamProc", SourceRole::Term, 0);
            refused(&scoped(Proc::Err), "Err", SourceRole::Term, 1);
            refused(&Proc::PParInfix(Arc::new(Proc::Err), Arc::new(Proc::PZero)), "Err", SourceRole::Term, 1);
            refused(&Proc::PParInfix(Arc::new(Proc::PZero), Arc::new(Proc::Err)), "Err", SourceRole::Term, 2);
            refused(&ddl(Proc::Err), "Err", SourceRole::Term, 3);
            refused(&input(Proc::Not(Arc::new(Proc::Err))), "Err", SourceRole::Guard, 5);
            let pattern = Proc::PForUser(vec![ForRow::ForRowSingleNoWhere(Arc::new(
                InputBind::InputBind(Arc::new(Name::NParen(Arc::new(Name::NQuote(Arc::new(Proc::Err))))),
                    Arc::new(Name::NQuoteNil))))], Arc::new(Proc::PZero));
            refused(&pattern, "Err", SourceRole::Pattern, 5);
            let query = Proc::PForUser(vec![ForRow::ForRowSingleNoWhere(Arc::new(
                InputBind::InputBindQuery(Arc::new(Name::NQuoteNil), Arc::new(Name::NQuoteNil),
                    vec![Proc::Err])))], Arc::new(Proc::PZero));
            refused(&query, "InputBindQuery", SourceRole::Term, 2);
            let mut first_map = HashMapLit::new();
            first_map.insert(Proc::PZero, Proc::Err);
            first_map.insert(Proc::Err, Proc::PZero);
            refused(&Proc::CastMap(Arc::new(Map::MapLit(first_map))), "Err", SourceRole::Term, 3);
            let mut bad_key = HashMapLit::new(); bad_key.insert(Proc::Err, Proc::PZero);
            refused(&Proc::CastMap(Arc::new(Map::MapLit(bad_key))), "Err", SourceRole::Term, 2);
            refused(&Proc::CastList(Arc::new(List::ListLit(vec![Proc::PZero, Proc::Err]))),
                "Err", SourceRole::Term, 3);
            let mut bad_bag = HashBag::new(); bad_bag.insert_n(Proc::Err, 100);
            refused(&Proc::PPar(bad_bag), "Err", SourceRole::Term, 1);
            invalid_policies();
            unsupported_carrier();
            let mut calls = 0;
            assert!(matches!(mettail_runtime::reserve_binding_parts(usize::MAX, 0, 1,
                &mut |_, _| { calls += 1; Ok::<_, ()>(()) }), Err(BindingFailure::SizeOverflow)));
            assert!(matches!(mettail_runtime::reserve_binding_parts(0, usize::MAX, 0,
                &mut |_, _| { calls += 1; Ok::<_, ()>(()) }), Err(BindingFailure::SizeOverflow)));
            assert_eq!(calls, 0, "charge arithmetic rejects before callback");
            deep_small_stack();
            println!("checked source fixture: all tags, original carriers, roles, cuts, opaque FLTs and deep stack passed");
        }
    };
    syn::parse2::<syn::File>(fixture.clone()).expect("actual source fixture parses");
    if std::env::var_os("METTAIL_CAPTURE_CHECKED_SOURCE").is_some() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/source-emitter");
        std::fs::create_dir_all(&directory).expect("source fixture directory");
        std::fs::write(directory.join("checked-rholang-source.rs"), fixture.to_string())
            .expect("write actual source fixture");
    }
}
