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
    for category in ["Set", "Pathmap", "Bytes"] {
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
fn checked_map_arm_uses_only_the_needed_element_category_scheduling_helper() {
    let language = fixture_language();
    let emission = HashEmissionNames::checked();
    let label = literal_label(&language, "Map");
    let arm = generate_hash_variant_arm(
        &format_ident!("Map"),
        &variant(&language, "Map", &label.to_string()),
        &language,
        &emission,
    )
    .to_string()
    .split_whitespace()
    .collect::<String>();
    assert!(arm.contains("checked_hash_schedule_map_proc("), "{arm}");
    for forbidden in ["UnsupportedConstructor", "collect", "sort_by", "Hash::hash", "try_hash_fx"] {
        assert!(!arm.contains(forbidden), "Map arm must route through its paid helper: {arm}");
    }
    let tasks = generate_hash_task_enum(&language, &emission);
    let engine = generate_hash_engine(&language, &emission);
    let interfaces = generate_hash_impls(&language, &emission);
    let items = syn::parse2::<syn::File>(quote! { #tasks #engine #interfaces })
        .expect("checked hash emission syntax");
    let helpers: Vec<_> = items
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Fn(item)
                if item
                    .sig
                    .ident
                    .to_string()
                    .starts_with("checked_hash_schedule_map_") =>
            {
                Some(item.sig.ident.to_string())
            },
            _ => None,
        })
        .collect();
    assert_eq!(
        helpers,
        ["checked_hash_schedule_map_proc"],
        "only the required element category gets a helper, not the outer Map or scalar categories"
    );
}

#[test]
fn contribution_inspection_shares_the_emitter_without_native_execution_or_sorting() {
    let language = fixture_language();
    let expansion = generate_hash_contribution_inspection(&language);
    syn::parse2::<syn::File>(expansion.clone())
        .expect("private contribution inspection declarations");
    let source = expansion.to_string();
    for required in [
        "try_inspect_hash_fx_work",
        "try_accumulate_parts",
        "try_for_each_entry",
        "BindingCharge",
    ] {
        assert!(source.contains(required), "missing shared inspection component: {required}");
    }
    for forbidden in [
        "CheckedFxHasher",
        "try_hash_fx",
        "Hash :: hash",
        "sort_by",
        "CheckedCollectionSortPda",
        "try_cmp_iterative",
    ] {
        assert!(!source.contains(forbidden), "metadata inspection must not execute {forbidden}");
    }
    let map_label = literal_label(&language, "Map");
    let map = generate_hash_variant_arm(
        &format_ident!("Map"),
        &variant(&language, "Map", &map_label.to_string()),
        &language,
        &HashEmissionNames::inspect_contributions(),
    )
    .to_string();
    assert!(map.contains("try_for_each_entry"));
    assert!(!map.contains("UnsupportedConstructor"));
    assert!(!map.contains("try_comparison_roster"));
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
    let checked_cmp =
        crate::gen::term_ops::iterative_cmp::generate_checked_iterative_cmp(&language);
    let ordinary_hash = generate_iterative_hash(&language);
    let ordinary_drop = crate::gen::term_ops::iterative_drop::generate_iterative_drop(&language);
    let emission = HashEmissionNames::checked();
    let checked_tasks = generate_hash_task_enum(&language, &emission);
    let checked_engine = generate_hash_engine(&language, &emission);
    let checked_impls = generate_hash_impls(&language, &emission);
    let contribution_inspection = generate_hash_contribution_inspection(&language);
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
        #ordinary_clone #ordinary_cmp #ordinary_hash #ordinary_drop #checked_cmp
        #checked_tasks #checked_engine #checked_impls
        #contribution_inspection

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

        fn token(text: &str) -> Proc { Proc::PToken(text.into()) }

        fn map(entries: impl IntoIterator<Item = (Proc, Proc)>) -> Map {
            Map::#map_literal(entries.into_iter().collect())
        }

        fn map_proc(value: Map) -> Proc {
            Proc::ApplyMap(Arc::new(Proc::PZero), Arc::new(value))
        }

        // Preserve both method boundaries and bytes, rather than accepting
        // digest equality as evidence of the generated Map task ordering.
        #[derive(Default, Debug, PartialEq, Eq)]
        struct NativeWrites(Vec<(&'static str, Vec<u8>)>);
        macro_rules! record_native_writes {
            ($($method:ident: $ty:ty),* $(,)?) => {
                $(fn $method(&mut self, value: $ty) {
                    self.0.push((stringify!($method), value.to_ne_bytes().to_vec()));
                })*
            };
        }
        impl Hasher for NativeWrites {
            fn write(&mut self, bytes: &[u8]) { self.0.push(("write", bytes.to_vec())); }
            fn finish(&self) -> u64 { panic!("native stream oracle must not compare digests") }
            record_native_writes! {
                write_u8: u8, write_u16: u16, write_u32: u32, write_u64: u64,
                write_u128: u128, write_usize: usize,
                write_i8: i8, write_i16: i16, write_i32: i32, write_i64: i64,
                write_i128: i128, write_isize: isize,
            }
        }

        fn exercise_map(value: &Map) {
            let Map::#map_literal(source) = value else { panic!("original Map literal") };
            let original: Vec<_> = source.iter()
                .map(|(key, value)| (key as *const Proc, value as *const Proc)).collect();
            let lower = Proc::PZero;
            for seed in [0, 1, usize::MAX] {
                let mut stack = vec![CheckedHashTask::<()>::HashProc(&lower)];
                // This production helper accepts no hasher: it only schedules
                // the original child borrows and the native length prefix.
                checked_hash_schedule_map_proc(source, &mut stack, &mut |_,_| Ok(()))
                    .expect("actual generated Map scheduling");
                assert_eq!(stack.len(), 2 * source.len() + 2,
                    "one length, both original children per entry, and untouched lower task");
                let mut expected = NativeWrites::default();
                let mut actual = NativeWrites::default();
                for writes in [&mut expected, &mut actual] {
                    seed.hash(writes);
                    29u8.hash(writes);
                    "already populated".hash(writes);
                }
                source.hash(&mut expected);
                match stack.pop().expect("Map length prefix") {
                    CheckedHashTask::AbsorbUsize(length) => {
                        assert_eq!(length, source.len()); length.hash(&mut actual);
                    },
                    _ => panic!("Map length must precede its entry children"),
                }
                let mut remaining = original.clone();
                for _ in 0..source.len() {
                    let (Some(CheckedHashTask::HashProc(key)), Some(CheckedHashTask::HashProc(value))) =
                        (stack.pop(), stack.pop()) else { panic!("original typed key then value") };
                    let index = remaining.iter().position(|pair| *pair == (key, value))
                        .expect("each scheduled pair is one exact, unrepeated original entry");
                    remaining.swap_remove(index);
                    // The immutable Map outlives these actual generated tasks;
                    // both typed pointers were checked against its own pairs.
                    unsafe { (&*key).hash(&mut actual); (&*value).hash(&mut actual); }
                }
                assert!(remaining.is_empty());
                assert_eq!(actual, expected, "exact native method/byte stream, not digest-only");
                assert!(matches!(stack.pop(), Some(CheckedHashTask::HashProc(ptr))
                    if ptr == &lower as *const Proc));
                assert!(stack.is_empty());
                assert_eq!(source.iter().map(|(k,v)| (k as *const Proc, v as *const Proc))
                    .collect::<Vec<_>>(), original, "source insertion order and borrows are unchanged");
            }
            // Reuse every reservation cut, exact/one-under limits and all Fx
            // seeds; the stream oracle above does not replace admission tests.
            exercise(value);
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

        fn assert_hash_pool_empty() {
            HASH_TASK_POOL.with(|cell| {
                let stack = cell.take();
                assert!(stack.is_empty(), "the private pool must not retain borrowed tasks");
                cell.set(stack);
            });
        }

        // Source correspondence for the ordinary wrapper, not a resource
        // bound for arbitrary user-supplied Hashers. Reentry must not consume
        // the outer driver's pending tasks or alter either native stream.
        #[derive(Default)]
        struct ReentrantWrites {
            writes: NativeWrites,
            nested_calls: usize,
            word_writes: usize,
        }
        macro_rules! forward_reentrant_writes {
            ($($method:ident: $ty:ty),* $(,)?) => {
                $(fn $method(&mut self, value: $ty) {
                    self.writes.$method(value);
                })*
            };
        }
        impl Hasher for ReentrantWrites {
            fn finish(&self) -> u64 { panic!("compare native streams, not digests") }
            fn write(&mut self, bytes: &[u8]) { self.writes.write(bytes); }
            fn write_usize(&mut self, value: usize) {
                self.word_writes += 1;
                // The first word is PPair's discriminant. On the second,
                // its left child is active and the right child is pending.
                if self.word_writes == 2 {
                    self.nested_calls += 1;
                    assert_hash_pool_empty();
                    let nested = Proc::PUnary(Arc::new(token("nested")));
                    let mut expected = NativeWrites::default();
                    let mut tasks = vec![HashTask::HashProc(&nested)];
                    hash_iterative(&mut tasks, &mut expected);
                    assert!(tasks.is_empty());
                    let mut actual = NativeWrites::default();
                    nested.hash(&mut actual);
                    assert_eq!(actual, expected, "nested wrapper preserves driver stream");
                    assert_hash_pool_empty();
                }
                self.writes.write_usize(value);
            }
            forward_reentrant_writes! {
                write_u8: u8, write_u16: u16, write_u32: u32, write_u64: u64,
                write_u128: u128, write_i8: i8, write_i16: i16, write_i32: i32,
                write_i64: i64, write_i128: i128, write_isize: isize,
            }
        }

        static SHUTDOWN_HASH_COMPLETED: std::sync::atomic::AtomicBool =
            std::sync::atomic::AtomicBool::new(false);
        struct HashDuringShutdown(std::cell::RefCell<Option<NativeWrites>>);
        impl Drop for HashDuringShutdown {
            fn drop(&mut self) {
                assert!(HASH_TASK_POOL.try_with(|_| ()).is_err(),
                    "exercise actual TLS unavailability, not an injected branch");
                let expected = self.0.get_mut().take().expect("normal-thread hash stream");
                let mut actual = NativeWrites::default();
                Proc::PZero.hash(&mut actual);
                assert_eq!(actual, expected, "local fallback preserves the native stream");
                SHUTDOWN_HASH_COMPLETED.store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
        thread_local! {
            static HASH_DURING_SHUTDOWN: HashDuringShutdown =
                HashDuringShutdown(std::cell::RefCell::new(None));
        }

        fn exercise_native_hash_wrapper() {
            let source = Proc::PPair(Arc::new(token("left")), Arc::new(token("right")));
            let mut expected = NativeWrites::default();
            let mut tasks = vec![HashTask::HashProc(&source)];
            hash_iterative(&mut tasks, &mut expected);
            assert!(tasks.is_empty());
            let mut pooled = NativeWrites::default();
            source.hash(&mut pooled);
            assert_eq!(pooled, expected, "ordinary wrapper preserves the driver stream");
            assert_hash_pool_empty();
            let mut actual = ReentrantWrites::default();
            source.hash(&mut actual);
            assert_eq!(actual.nested_calls, 1);
            assert_eq!(actual.writes, expected, "reentry must preserve outer pending tasks");
            assert_hash_pool_empty();

            std::thread::spawn(|| {
                // Register this destructor before the pool's destructor, so
                // it runs after the pool has become permanently unavailable.
                HASH_DURING_SHUTDOWN.with(|_| ());
                let source = Proc::PZero;
                let mut expected = NativeWrites::default();
                let mut tasks = vec![HashTask::HashProc(&source)];
                hash_iterative(&mut tasks, &mut expected);
                assert!(tasks.is_empty());
                let mut pooled = NativeWrites::default();
                source.hash(&mut pooled);
                assert_eq!(pooled, expected, "first-use wrapper preserves the driver stream");
                assert_hash_pool_empty();
                HASH_DURING_SHUTDOWN.with(|probe| *probe.0.borrow_mut() = Some(expected));
            }).join().expect("ordinary Hash TLS-fallback thread");
            assert!(SHUTDOWN_HASH_COMPLETED.load(std::sync::atomic::Ordering::SeqCst),
                "the destructor must actually have exercised local fallback");
        }

        fn deep_small_stack() {
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                for nested_maps in [false, true] {
                    let mut value = Proc::PToken("bottom".into());
                    for depth in 0..20_000 {
                        value = if nested_maps {
                            // Insertion hashes only these distinct shallow keys;
                            // sorting never needs to descend into the deep values.
                            map_proc(map([(token("a"), value), (token("z"), Proc::PZero)]))
                        } else if depth % 2 == 0 {
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
                }
            }).expect("spawn small-stack hash worker").join().expect("small-stack hash worker");
        }

        fn contribution_inspection_examples() {
            use mettail_runtime::binding_receipt::BindingCharge;
            let inspect = |value: &Proc, expected_work, expected_records| {
                let mut trace = Vec::new();
                let result = inspect_hash_contribution_proc(value, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }).expect("admitted metadata-only contribution walk");
                assert_eq!(result, BindingCharge::new(expected_work,expected_records,0)
                    .expect("leaf, driver/wrapper and handler contribution"));
                // Every refusal stops at its original metadata boundary and
                // exposes no partial additive result or hasher state.
                for stop in 0..trace.len() {
                    let mut seen = 0;
                    let result = inspect_hash_contribution_proc(value, &mut |w,u| {
                        assert_eq!((w,u), trace[seen]);
                        let current = seen; seen += 1;
                        if current == stop { Err(stop) } else { Ok(()) }
                    });
                    assert_eq!(result, Err(KeyHashFailure::Admission(BindingFailure::Reservation(stop))));
                    assert_eq!(seen, stop+1);
                }
            };
            inspect(&Proc::PZero, 26, 3);
            let shared = Arc::new(Proc::PZero);
            inspect(&Proc::PPair(shared.clone(), shared.clone()), 52, 5);
            assert_eq!(Arc::strong_count(&shared), 1);
            inspect(&Proc::POptionalVec(None), 34, 4);
            inspect(&Proc::POptionalVec(Some(Vec::new())), 44, 6);
            inspect(&Proc::POptionalVec(Some(vec![Proc::PZero])), 57, 7);
            inspect(&Proc::PVector(vec![Proc::PZero, Proc::PZero]), 63, 7);
            inspect(&Proc::PSingle(Arc::new(Proc::PZero),
                Scope::from_parts_unsafe(Binder(FreeVar::fresh_named("binder")), Arc::new(Proc::PZero))), 70, 6);
            inspect(&Proc::PMulti(vec![Proc::PZero],
                Scope::from_parts_unsafe(Vec::new(), Arc::new(Proc::PZero))), 80, 8);
            let guest = guest();
            let guest_work = mettail_runtime::CheckedFxHashLeaf::try_inspect_hash_fx_work(
                &guest, &mut |_,_| Ok::<_, ()>(()),
            ).expect("existing sealed FLT leaf allowance");
            inspect(&Proc::PMixed("p".into(), Arc::new(Proc::PZero), guest, "s".into()),
                86 + guest_work, 6);
            let mut bag = mettail_runtime::HashBag::new();
            bag.insert_n(Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "not visited by cached bag Hash".into(), args: Vec::new(), negated: false,
            }), 3);
            inspect(&Proc::PBag(bag), 55, 4);
            for keys in [["a", "b"], ["b", "a"]] {
                let value = map(keys.into_iter().map(|key| (token(key), Proc::PZero)));
                let Map::#map_literal(source) = &value else { panic!("Map literal") };
                let original: Vec<_> = source.iter().map(|(k,v)| (k as *const Proc,v as *const Proc)).collect();
                let charge = inspect_hash_contribution_map(&value, &mut |_,_| Ok::<_, ()>(()))
                    .expect("unsorted metadata-only Map walk");
                assert_eq!(charge, BindingCharge::new(105,8,0).expect("original pair contributions"));
                assert_eq!(source.iter().map(|(k,v)| (k as *const Proc,v as *const Proc)).collect::<Vec<_>>(), original);
                inspect(&map_proc(value), 131, 10);
            }
            std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
                let depth = 20_000;
                let mut value = Proc::PZero;
                for _ in 0..depth { value = Proc::PUnary(Arc::new(value)); }
                let charge = inspect_hash_contribution_proc(&value, &mut |_,_| Ok::<_, ()>(()))
                    .expect("deep metadata traversal is iterative");
                assert_eq!(charge, BindingCharge::new(26 + 13*depth, 3 + depth, 0)
                    .expect("exact leaf, driver/wrapper and handler contribution"));
                drop(value);
            }).expect("spawn contribution inspection worker").join().expect("contribution inspection worker");
        }

        fn main() {
            assert!(mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE);
            contribution_inspection_examples();
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
            for keys in [vec![], vec!["one"], vec!["c", "a", "b"], vec!["b", "a", "c"]] {
                let value = map(keys.into_iter().map(|key| (token(key), token(&format!("value:{key}:λ")))));
                exercise_map(&value);
                exercise(&map_proc(value));
            }
            let nested = map([
                (map_proc(map([(token("k2"), token("v2")), (token("k1"), Proc::PZero)])),
                    map_proc(map([(token("child"), token("nested value"))]))),
                (map_proc(map([(token("k0"), Proc::PZero)])),
                    Proc::PVector(vec![map_proc(map([(token("vector child"), Proc::PZero)]))])),
            ]);
            exercise_map(&nested);
            exercise(&map_proc(nested));
            // A Map inside the existing multi-binder body follows the same
            // pattern-before-body scope schedule, not a separate Map entrypoint.
            exercise(&Proc::PMulti(vec![Proc::PZero], Scope::from_parts_unsafe(Vec::new(),
                Arc::new(map_proc(map([(token("scoped key"), token("scoped value"))]))))));
            let unadmitted = |name: &str| Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: name.into(), args: Vec::new(), negated: false,
            });
            refuse(&map([(token("supported key"), unadmitted("Map value"))]), "Proc", "PPredicate");
            let refused_keys = map([
                (unadmitted("first distinct key"), Proc::PZero),
                (unadmitted("second distinct key"), Proc::PZero),
            ]);
            let Map::#map_literal(source) = &refused_keys else { panic!("original Map literal") };
            let mut pending = Vec::<CheckedHashTask<()>>::new();
            let sort_error = checked_hash_schedule_map_proc(source, &mut pending, &mut |_,_| Ok(()))
                .expect_err("checked sorting refuses the original unsupported key category arm");
            assert!(matches!(sort_error, KeyHashFailure::UnsupportedConstructor {
                category: "Proc", constructor: "PPredicate",
            }));
            assert!(pending.is_empty(), "sorting fails before publishing any entry hash task");
            refuse(&refused_keys, "Proc", "PPredicate");
            let predicate = mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "unadmitted".into(), args: Vec::new(), negated: false,
            };
            refuse(&Proc::PPredicate(predicate), "Proc", "PPredicate");
            refuse(&Set::#set_literal(mettail_runtime::HashSetLit::new()), "Set", stringify!(#set_literal));
            refuse(&Pathmap::#pathmap_literal(mettail_runtime::PathMapLit::new()), "Pathmap", stringify!(#pathmap_literal));
            refuse(&Bytes::#bytes_literal(vec![0,1,255]), "Bytes", stringify!(#bytes_literal));
            // A cached bag hash is not a profile certificate for its members.
            let mut hidden = mettail_runtime::HashBag::new();
            hidden.insert(Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name: "hidden under cached summary".into(), args: Vec::new(), negated: false,
            }));
            exercise(&Proc::PBag(hidden));
            exercise_native_hash_wrapper();
            deep_small_stack();
            println!("checked generated Hash matches native streams, including exact original Map task methods/bytes; all cutpoints, cumulative limits, unsupported arms and 20k small-stack scope/Map-value traversals verified");
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
