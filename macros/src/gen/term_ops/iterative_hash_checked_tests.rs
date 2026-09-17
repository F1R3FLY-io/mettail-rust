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
        "inspect_native_map_hash_overhead",
        "inspect_map_hash_contributions_proc",
        "try_comparison_roster",
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
    assert!(map.contains("inspect_map_hash_contributions_proc"));
    assert!(!map.contains("UnsupportedConstructor"));
    assert!(!map.contains("sort_by"));
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
    let bag_admission =
        super::super::hashbag_rebuild_admission::generate_hashbag_rebuild_admission(&language);
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
        #bag_admission

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

        fn map_overhead_oracle(n: usize, c: usize) -> mettail_runtime::binding_receipt::BindingCharge {
            use mettail_runtime::binding_receipt::BindingCharge;
            // Independent named source components, computed wider than the
            // machine arithmetic under test. No task/leaf costs are re-added.
            let n = n as u128;
            let core = 320*n*n + 1024*n + 1133;
            let shell = 19 + 10*n + u128::from(n != 0);
            let mut work = core + shell + 2 + 2*(n+1) + 5*(c as u128);
            let mut records = core + (n+1) + 1;
            if n > 20 {
                work += 16 + 514;
                records += 1 + 257;
                let q = (n - n/2).max(n.min(500_000)).max(48);
                if q > 256 {
                    work += 2*(q+1);
                    records += q+1;
                }
            }
            BindingCharge::new(usize::try_from(work).expect("fixture work fits"),
                usize::try_from(records).expect("fixture records fit"), 0).expect("fixture projections fit")
        }

        fn native_map_overhead_boundaries() {
            use mettail_runtime::binding_receipt::BindingCharge;
            let initial = BindingCharge::new(7, 2, 3).expect("populated prefix");
            for n in [0usize, 1, 2, 3, 20, 21, 256, 257, 512, 513, 500_000, 500_001] {
                let c = if n < 2 { 0 } else { 10*n*n + 32*n };
                let expected = initial.checked_add(map_overhead_oracle(n, c)).expect("composed prefix");
                let mut state = initial;
                let mut trace = Vec::new();
                inspect_native_map_hash_overhead(&mut state, n, c, &mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }).expect("all named native Map overhead components");
                assert_eq!(state, expected, "width {n}");
                assert!(!trace.is_empty());
                for stop in 0..trace.len() {
                    let mut partial = initial;
                    let mut seen = 0;
                    let result = inspect_native_map_hash_overhead(&mut partial, n, c, &mut |w,u| {
                        assert_eq!((w,u), trace[seen]);
                        let current = seen; seen += 1;
                        if current == stop { Err(stop) } else { Ok(()) }
                    });
                    assert_eq!(result, Err(KeyHashFailure::Admission(BindingFailure::Reservation(stop))));
                    assert_eq!(seen, stop+1);
                }
            }
            for (n,c) in [(usize::MAX,0), (0,usize::MAX), (usize::MAX/2,0)] {
                let mut state = initial;
                let mut calls = 0;
                let result = inspect_native_map_hash_overhead(&mut state,n,c,&mut |_,_| {
                    calls += 1; Ok::<_, ()>(())
                });
                assert_eq!(result, Err(KeyHashFailure::Admission(BindingFailure::SizeOverflow)));
                assert!(calls > 0, "arithmetic follows paid inspection");
            }
            struct Stop(Box<u8>);
            let mut error = Some(Stop(Box::new(19)));
            let identity = &*error.as_ref().expect("original error").0 as *const u8;
            let mut state = initial;
            let result = inspect_native_map_hash_overhead(&mut state,usize::MAX,usize::MAX,
                &mut |_,_| Err(error.take().expect("single refusal")));
            match result {
                Err(KeyHashFailure::Admission(BindingFailure::Reservation(error))) =>
                    assert_eq!(&*error.0 as *const u8, identity),
                _ => panic!("reservation must precede arithmetic and preserve the non-Clone error"),
            }
            assert_eq!(state, initial);
        }

        fn original_map_contribution_oracle(value: &Map) -> mettail_runtime::binding_receipt::BindingCharge {
            use mettail_runtime::binding_receipt::BindingCharge;
            let Map::#map_literal(source) = value else { panic!("Map literal") };
            let n = source.len();
            let c = if n < 2 { 0 } else { 10*n*n + 32*n };
            // Empty literal Map: one root category, payload handoff, and the
            // existing AbsorbUsize task/leaf. Each child has no extra wrapper.
            let mut expected = BindingCharge::new(33,4,0).expect("literal Map base")
                .checked_add(map_overhead_oracle(n,c)).expect("Map overhead");
            for (key,value) in source.iter() {
                for child in [key,value] {
                    let charge = inspect_hash_contribution_proc(child,&mut |_,_| Ok::<_, ()>(()))
                        .expect("original Hash child contribution");
                    expected = expected.checked_add(BindingCharge::new(
                        charge.base_work()-15,charge.records()-2,charge.owned_bytes())
                        .expect("child without duplicate root wrapper")).expect("child sum");
                }
            }
            if c > 0 {
                for (lk,lv) in source.iter() {
                    for (rk,rv) in source.iter() {
                        for (left,right) in [(lk,rk),(lv,rv)] {
                            let charge = inspect_comparison_contributions_proc(left,right,
                                InspectCmpContributionMode::Ord,&mut |_,_| Ok::<_, ()>(()))
                                .expect("full public Ord callback contribution");
                            expected = expected.checked_add(charge.checked_scale(c).expect("callback factor"))
                                .expect("both directed callback roles");
                        }
                    }
                }
            }
            expected
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
                assert_eq!(charge, original_map_contribution_oracle(&value));
                assert_eq!(source.iter().map(|(k,v)| (k as *const Proc,v as *const Proc)).collect::<Vec<_>>(), original);
                inspect(&map_proc(value), charge.base_work()+26, charge.records()+2);
            }
            for value in [map([]), map([(Proc::PZero,Proc::PZero)]),
                map([(Proc::PZero,Proc::PZero),(token("unequal primary"),Proc::PUnary(Arc::new(Proc::PZero)))]),
                map([(token("a"),Proc::PPair(shared.clone(),shared.clone())),
                     (token("b"),map_proc(map([(Proc::PZero,Proc::PZero)]))),
                     (token("c"),Proc::PZero)])] {
                let expected = original_map_contribution_oracle(&value);
                let actual = inspect_hash_contribution_map(&value,&mut |_,_| Ok::<_, ()>(()))
                    .expect("original directed roles, aliases and nested Map");
                assert_eq!(actual,expected);
                // Native unequal primary results may skip values, but the
                // unknown-result cost cover must still include those values.
                let proc = map_proc(value);
                let mut trace = Vec::new();
                inspect_hash_contribution_proc(&proc,&mut |w,u| {
                    trace.push((w,u)); Ok::<_, usize>(())
                }).expect("nested original Map contribution");
                for stop in [0,trace.len()/2,trace.len()-1] {
                    let mut seen = 0;
                    let result = inspect_hash_contribution_proc(&proc,&mut |w,u| {
                        assert_eq!((w,u),trace[seen]);
                        let current = seen; seen += 1;
                        if current == stop { Err(stop) } else { Ok(()) }
                    });
                    assert_eq!(result,Err(KeyHashFailure::Admission(BindingFailure::Reservation(stop))));
                    assert_eq!(seen,stop+1);
                }
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
                let mut value = Proc::PZero;
                for _ in 0..depth { value = map_proc(map([(Proc::PZero,value)])); }
                let charge = inspect_hash_contribution_proc(&value,&mut |_,_| Ok::<_, ()>(()))
                    .expect("singleton Maps have no native sort callbacks or recursive inspection");
                let overhead = map_overhead_oracle(1,0);
                assert_eq!(charge,BindingCharge::new(26+depth*(55+overhead.base_work()),
                    3+depth*(5+overhead.records()),0).expect("linear singleton Map inventory"));
                drop(value);
            }).expect("spawn contribution inspection worker").join().expect("contribution inspection worker");
        }

        fn bag_stage_oracle(step: &mettail_runtime::HashBagRebuildStep<'_, Proc>) -> (usize, usize) {
            use mettail_runtime::{HashBagRebuildMode as Mode, HashBagRebuildStep as Step};
            // Independent StageCharge algebra in wider integers. Child costs
            // use metadata inspectors, never native Hash/Eq in this oracle.
            let mut parts = (0u128, 0u128, 0u128);
            let mut add = |charge: mettail_runtime::binding_receipt::BindingCharge, factor: u128| {
                parts.0 += factor * charge.base_work() as u128;
                parts.1 += factor * charge.records() as u128;
                parts.2 += factor * charge.owned_bytes() as u128;
            };
            let hash = |key: &Proc| inspect_hash_contribution_proc(key, &mut |_,_| Ok::<_, ()>(()))
                .expect("complete key metadata, not a native callback oracle");
            let eq = |left: &Proc, right: &Proc|
                inspect_comparison_contributions_proc(left, right, InspectCmpContributionMode::Eq,
                    &mut |_,_| Ok::<_, ()>(())).expect("directed Eq metadata");
            let groups = |buckets: usize| ((buckets as u128 + 15) / 16).max(1);
            let scan = |entries: u128, q: u128| 4*entries + 19*q;
            let probe = |q: u128, entries: u128| 22*q + 2*entries + 17;
            let flat = match step {
                Step::Start { width, .. } => (11+3*(*width as u128), 4+*width as u128, 0),
                Step::Insert { mode: Mode::CloneEntries, count: 0, .. } => (2,0,0),
                Step::Insert { mode, key, retained, .. } => {
                    let r = retained.distinct_len() as u128;
                    let old_b = retained.checked_bucket_count().expect("actual clean geometry");
                    let growth = retained.distinct_len() == retained.capacity();
                    let next_b = if growth { if old_b == 1 { 4 } else { 2*old_b } } else { old_b };
                    let old_q = groups(old_b);
                    let new_q = groups(next_b);
                    let bytes = if growth {
                        retained.checked_table_layout(next_b).expect("prospective native layout").0.size() as u128
                    } else { 0 };
                    add(hash(key), if *mode == Mode::CloneEntries { 3 } else { 1 });
                    for (stored, _) in retained.iter() {
                        let hash_factor = u128::from(growth) + if *mode == Mode::CloneEntries { 4 } else { 0 };
                        if hash_factor != 0 { add(hash(stored), hash_factor); }
                        add(if *mode == Mode::CloneEntries { eq(stored,key) } else { eq(key,stored) }, 1);
                    }
                    let resize = if growth {
                        scan(r,old_q) + r*probe(new_q,0) + r + 4*r
                            + r*std::mem::size_of::<(Proc,usize)>() as u128 + next_b as u128 + 16 + 3
                    } else { 0 };
                    let insertion = if *mode == Mode::CloneEntries {
                        probe(old_q,r) + probe(new_q,0) + 4
                    } else { probe(new_q,r) };
                    (1+insertion+resize+6+scan(r+1,new_q)+(r+1), u128::from(growth), bytes)
                },
                Step::FinalBindingSummary { retained } => {
                    let r = retained.distinct_len() as u128;
                    let q = groups(retained.checked_bucket_count().expect("final clean geometry"));
                    for (stored, _) in retained.iter() { add(hash(stored),2); }
                    (scan(r,q)+1+2*r,0,0)
                },
            };
            let work = parts.0 + flat.0 + parts.2 + flat.2;
            let units = 4*(parts.1 + flat.1) + parts.2 + flat.2;
            (usize::try_from(work).expect("fixture stage work fits"),
                usize::try_from(units).expect("fixture stage units fit"))
        }

        fn exercise_bag_provider(
            source: &mettail_runtime::HashBag<Proc>, entries: Vec<(Proc,usize)>,
            mode: mettail_runtime::HashBagRebuildMode,
        ) -> mettail_runtime::HashBag<Proc> {
            use mettail_runtime::{HashBag, HashBagRebuildMode as Mode, HashBagRebuildStep as Step};
            let original: Vec<_> = source.iter().map(|(key,count)| (key as *const Proc,count)).collect();
            let total = source.len();
            // Semantic reference is the existing native recipe, kept separate
            // from the metadata-only accounting oracle above.
            let expected = if mode == Mode::BindingEntries {
                source.rebuild_binding_entries(entries.clone())
            } else {
                let mut bag = HashBag::new();
                for (key,count) in entries.clone() { bag.insert_n(key,count); }
                bag
            };
            let mut trace = Vec::new();
            let mut stage_ends = Vec::new();
            let mut kinds = Vec::new();
            let mut growths = 0;
            let actual = source.try_rebuild_entries_with(entries.clone(),mode,|step| {
                match &step {
                    Step::Start { width,source_total,.. } => {
                        kinds.push(0); assert_eq!(*width,entries.len()); assert_eq!(*source_total,total);
                    },
                    Step::Insert { retained,count,.. } => {
                        kinds.push(1);
                        if !(*count == 0 && mode == Mode::CloneEntries)
                            && retained.distinct_len() == retained.capacity() { growths += 1; }
                    },
                    Step::FinalBindingSummary { .. } => kinds.push(2),
                }
                let expected_stage = bag_stage_oracle(&step);
                let before = trace.len();
                admit_bag_rebuild_proc(step,&mut |w,u| { trace.push((w,u)); Ok::<_, usize>(()) })?;
                assert!(trace.len() > before, "every stage prepays native work");
                assert_eq!(trace.last().copied(),Some(expected_stage), "exact composed stage payment");
                stage_ends.push(trace.len()-1);
                Ok(())
            }).expect("generated provider admits the original native rebuild");
            assert_eq!(kinds[0],0);
            assert_eq!(kinds.iter().filter(|&&kind| kind==1).count(),entries.len());
            assert_eq!(kinds.iter().filter(|&&kind| kind==2).count(),usize::from(mode==Mode::BindingEntries));
            assert_eq!(actual.len(),expected.len());
            assert_eq!(actual.iter().count(),expected.iter().count());
            for (key,count) in expected.iter() {
                assert_eq!(actual.iter().find(|(candidate,_)| *candidate==key).map(|(_,n)| n),Some(count));
            }
            let mut expected_stream = NativeWrites::default(); expected.hash(&mut expected_stream);
            let mut actual_stream = NativeWrites::default(); actual.hash(&mut actual_stream);
            assert_eq!(actual_stream,expected_stream,"native cached summary is preserved");
            if entries.len() >= 12 { assert!(growths >= 3,"exercise multiple native width growths"); }
            let costs = trace.iter().fold((0usize,0usize),|(w,u),(x,y)| (w+x,u+y));
            for limit in [costs,(costs.0-1,costs.1),(costs.0,costs.1-1)] {
                let mut used = (0usize,0usize);
                let result = source.try_rebuild_entries_with(entries.clone(),mode,|step|
                    admit_bag_rebuild_proc(step,&mut |w,u| {
                        if w>limit.0-used.0 || u>limit.1-used.1 { return Err("stage budget"); }
                        used.0+=w; used.1+=u; Ok(())
                    }));
                if limit==costs { assert!(result.is_ok()); assert_eq!(used,costs); }
                else { assert!(matches!(result,Err(BindingFailure::Reservation("stage budget")))); }
            }
            // Selected prefix boundaries include first inspection, native stage
            // payments and finalization. No Cartesian refusal-test explosion.
            let mut cuts = vec![0,trace.len()/2,trace.len()-1];
            cuts.extend(stage_ends.into_iter().take(3)); cuts.sort_unstable(); cuts.dedup();
            for stop in cuts {
                struct Stop(Box<usize>);
                let mut error = Some(Stop(Box::new(stop)));
                let identity = &*error.as_ref().expect("owned refusal").0 as *const usize;
                let mut seen = 0;
                let result = source.try_rebuild_entries_with(entries.clone(),mode,|step|
                    admit_bag_rebuild_proc(step,&mut |w,u| {
                        assert_eq!((w,u),trace[seen]); let current=seen; seen+=1;
                        if current==stop { Err(error.take().expect("refusal consumed once")) } else { Ok(()) }
                    }));
                match result {
                    Err(BindingFailure::Reservation(error)) => assert_eq!(&*error.0 as *const usize,identity),
                    _ => panic!("stage refusal must preserve its original non-Clone error"),
                }
                assert_eq!(seen,stop+1);
                assert_eq!(source.len(),total);
                assert_eq!(source.iter().map(|(k,n)| (k as *const Proc,n)).collect::<Vec<_>>(),original);
            }
            actual
        }

        fn generated_bag_provider_examples() {
            use mettail_runtime::{HashBag, HashBagRebuildMode as Mode};
            let mut source = HashBag::new();
            source.insert_n(token("source one"),11); source.insert_n(token("source two"),13);
            for mode in [Mode::BindingEntries,Mode::CloneEntries] {
                let empty = exercise_bag_provider(&source,Vec::new(),mode);
                assert_eq!(empty.len(),if mode==Mode::BindingEntries { 24 } else { 0 });
                let first = Arc::new(Proc::PZero);
                let later = Arc::new(Proc::PZero);
                let result = exercise_bag_provider(&source,vec![
                    (Proc::PUnary(first.clone()),2),(Proc::PUnary(later.clone()),5),(token("zero"),0),
                ],mode);
                let (Proc::PUnary(winner),count) = result.iter().find(|(key,_)|
                    matches!(key,Proc::PUnary(_))).expect("transformed equal key") else { unreachable!() };
                assert!(Arc::ptr_eq(winner,&first),"first equal key object survives");
                assert!(!Arc::ptr_eq(winner,&later));
                assert_eq!(count,if mode==Mode::BindingEntries { 5 } else { 7 });
                assert_eq!(result.iter().count(),if mode==Mode::BindingEntries { 2 } else { 1 });
                assert_eq!(result.len(),if mode==Mode::BindingEntries { 24 } else { 7 });
                exercise_bag_provider(&source,(0..12).map(|i| (token(&format!("key {i}")),i+1)).collect(),mode);
                exercise_bag_provider(&source,vec![
                    (map_proc(map([(token("a"),Proc::PZero),(token("z"),map_proc(map([(Proc::PZero,Proc::PZero)])))])),2),
                    (map_proc(map([(token("b"),Proc::PZero)])),3),
                ],mode);
            }
            // Zero Clone must not inspect an otherwise unsupported key, hash it,
            // compare it or allocate a native entry; its owned root still drops.
            let unsupported = Proc::PPredicate(mettail_runtime::BehavioralPred::RelationQuery {
                relation_name:"zero-count must not inspect me".into(),args:Vec::new(),negated:false,
            });
            let zero = exercise_bag_provider(&source,vec![(unsupported,0)],Mode::CloneEntries);
            assert_eq!(zero.len(),0); assert_eq!(zero.iter().count(),0);
            let overflow = source.try_rebuild_entries_with(
                vec![(token("maximum count"),usize::MAX),(token("overflow count"),1)],
                Mode::CloneEntries,|step| admit_bag_rebuild_proc(step,&mut |_,_| Ok::<_, ()>(())));
            assert!(matches!(overflow,Err(BindingFailure::SizeOverflow)),
                "native Clone's count guard rejects before overflowing insert_n");
            assert_eq!(source.len(),24);
            let mut seen = 0;
            let overflow = admit_bag_rebuild_proc(mettail_runtime::HashBagRebuildStep::Start {
                mode:Mode::BindingEntries,width:usize::MAX,source_total:24,
            },&mut |_,_| { seen+=1; Ok::<_, ()>(()) });
            assert_eq!(overflow,Err(BindingFailure::SizeOverflow));
            assert_eq!(seen,1,"Start arithmetic follows its one paid metadata group");
        }

        fn main() {
            assert!(mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE);
            generated_bag_provider_examples();
            native_map_overhead_boundaries();
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
