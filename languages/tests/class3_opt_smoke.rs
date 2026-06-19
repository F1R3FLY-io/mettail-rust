//! Phase 4 #4 (2026-05-12): Class-3 + Optional-Collection combined smoke test
//! for `PInputsOptTagged`.
//!
//! Validates that a binder rule combining a Class-3 ZIP-MAP-SEP BinderListLoop
//! (top-level multi-binder) AND a Class-2 SimpleCollection inside *opt(...)
//! parses end-to-end through the WPDS walker. This exercises the cross-product
//! of Phase 4 #2 (multi-collection-slot Class 3) and Phase 4 #3 (Class-2 inside
//! *opt). The term-ops codegen for MultiBinder pre_scope_fields must handle the
//! Optional+Collection field shape (`Option<Vec<Proc>>`) — Phase 4 #4 adds the
//! cloned-carrier branch to the binder/multi-binder paths in normalize, subst,
//! iterative_clone, iterative_drop, iterative_hash, iterative_cmp, and
//! match_pattern (the last three needed no change — derived Hash/Ord/PartialEq
//! on `Option<Vec<T>>` work directly).
//!
//! Grammar (languages/src/class3opt.rs):
//!   PInputsOptTagged . ns:Vec(Name), *opt(qs:Vec(Proc)), ^[xs].p:[Name* -> Proc]
//!       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")"
//!          "." "{" p "}"
//!          *opt("with" "[" qs.*sep("|") "]") : Proc;
//!
//! AST: `PInputsOptTagged(Vec<Name>, Option<Vec<Proc>>, Scope<...>)`.
//!
//! Test predictions:
//! - PRED-1: opt skipped + empty names → `( ) . { 0 }`
//!           → PInputsOptTagged(ns=[], qs=None, scope=...)
//! - PRED-2: opt skipped + single binder → `( @(0) ? x ) . { 0 }`
//!           → PInputsOptTagged(ns=[NQuote(PZero)], qs=None, scope=...)
//! - PRED-3: opt taken (empty inner) + empty names → `( ) . { 0 } with [ ]`
//!           → PInputsOptTagged(ns=[], qs=Some([]), scope=...)
//! - PRED-4: opt taken nonempty + single binder → `( @(0) ? x ) . { 0 } with [ 0 ]`
//!           → PInputsOptTagged(ns=[NQuote(PZero)], qs=Some([PZero]), scope=...)
//!
//! Construction/clone/eq/hash tests cover the AST-level codegen even for cases
//! whose parse-side wiring hasn't landed yet (per the Phase 4 #3 caveat for
//! class2optsmoke's "*opt taken nonempty" case).

use mettail_languages::class3opt::{Name, Proc};

// =============================================================================
// AST construction + Clone/PartialEq/Hash/Debug — these must work regardless of
// whether the parse-side has been wired through end-to-end.
// =============================================================================

#[test]
fn ast_pinputsopttagged_qs_none_empty_constructs_and_clones() {
    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let term = Proc::PInputsOptTagged(Vec::new(), None, scope);
    let cloned = term.clone();
    assert_eq!(term, cloned);
    let displayed = format!("{}", term);
    assert!(!displayed.is_empty());
}

#[test]
fn ast_pinputsopttagged_qs_some_empty_constructs_and_clones() {
    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let term = Proc::PInputsOptTagged(Vec::new(), Some(Vec::new()), scope);
    let cloned = term.clone();
    assert_eq!(term, cloned);
}

#[test]
fn ast_pinputsopttagged_qs_some_nonempty_constructs_and_clones() {
    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let term = Proc::PInputsOptTagged(Vec::new(), Some(vec![Proc::PZero, Proc::PZero]), scope);
    let cloned = term.clone();
    assert_eq!(term, cloned);
    // Debug format works.
    let debug = format!("{:?}", term);
    assert!(debug.contains("PInputsOptTagged"));
}

#[test]
fn ast_pinputsopttagged_qs_none_ne_qs_some() {
    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope_a = mettail_runtime::Scope::from_parts_unsafe(pat.clone(), body.clone());
    let scope_b = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let a = Proc::PInputsOptTagged(Vec::new(), None, scope_a);
    let b = Proc::PInputsOptTagged(Vec::new(), Some(Vec::new()), scope_b);
    assert_ne!(a, b);
}

#[test]
fn ast_pinputsopttagged_qs_some_different_lengths_ne() {
    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope_a = mettail_runtime::Scope::from_parts_unsafe(pat.clone(), body.clone());
    let scope_b = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let a = Proc::PInputsOptTagged(Vec::new(), Some(vec![Proc::PZero]), scope_a);
    let b = Proc::PInputsOptTagged(Vec::new(), Some(vec![Proc::PZero, Proc::PZero]), scope_b);
    assert_ne!(a, b);
}

#[test]
fn ast_pinputsopttagged_qs_some_hash_consistent_with_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let pat = Vec::<mettail_runtime::Binder<String>>::new();
    let body = std::sync::Arc::new(Proc::PZero);
    let scope_a = mettail_runtime::Scope::from_parts_unsafe(pat.clone(), body.clone());
    let scope_b = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let a = Proc::PInputsOptTagged(Vec::new(), Some(vec![Proc::PZero]), scope_a);
    let b = Proc::PInputsOptTagged(Vec::new(), Some(vec![Proc::PZero]), scope_b);
    assert_eq!(a, b);

    let mut h1 = DefaultHasher::new();
    a.hash(&mut h1);
    let mut h2 = DefaultHasher::new();
    b.hash(&mut h2);
    assert_eq!(h1.finish(), h2.finish());
}

#[test]
fn ast_pinputsopttagged_with_names_constructs_and_clones() {
    let pat = vec![mettail_runtime::Binder(mettail_runtime::FreeVar::fresh(Some("x".to_string())))];
    let body = std::sync::Arc::new(Proc::PZero);
    let scope = mettail_runtime::Scope::from_parts_unsafe(pat, body);
    let term = Proc::PInputsOptTagged(
        vec![Name::NQuote(std::sync::Arc::new(Proc::PZero))],
        Some(vec![Proc::PZero]),
        scope,
    );
    let cloned = term.clone();
    assert_eq!(term, cloned);
}

// =============================================================================
// Parse-side end-to-end via WPDS. The opt-skipped (None) cases should fire;
// the opt-taken (Some) cases share the parse-side caveat from Phase 4 #3
// (class2_opt_collection_smoke) — the Some-elements parser→builder wiring
// inside *opt isn't yet wired end-to-end. Commented-out tests document the
// expected semantics for when that wiring lands.
// =============================================================================

#[test]
fn pred1_opt_skipped_empty_names_via_wpds() {
    let result = Proc::parse_via_wpda("( ) . { 0 }").expect("'( ) . { 0 }' parses");
    match &result {
        Proc::PInputsOptTagged(ns, qs, _scope) => {
            assert_eq!(ns.len(), 0, "ns should be empty");
            assert!(qs.is_none(), "qs should be None when *opt skipped");
        },
        other => panic!("expected Proc::PInputsOptTagged([], None, _), got {:?}", other),
    }
}

#[test]
fn pred2_opt_skipped_single_binder_via_wpds() {
    let result =
        Proc::parse_via_wpda("( @(0) ? x ) . { 0 }").expect("'( @(0) ? x ) . { 0 }' parses");
    match &result {
        Proc::PInputsOptTagged(ns, qs, _scope) => {
            assert_eq!(ns.len(), 1, "ns should have 1 element");
            assert!(matches!(&ns[0], Name::NQuote(_)));
            assert!(qs.is_none(), "qs should be None when *opt skipped");
        },
        other => panic!("expected Proc::PInputsOptTagged([_], None, _), got {:?}", other),
    }
}

#[test]
fn pred3_opt_taken_empty_inner_via_wpds() {
    let result =
        Proc::parse_via_wpda("( ) . { 0 } with [ ]").expect("'( ) . { 0 } with [ ]' parses");
    match &result {
        Proc::PInputsOptTagged(ns, qs, _scope) => {
            assert_eq!(ns.len(), 0, "ns should be empty");
            match qs {
                Some(v) => assert_eq!(v.len(), 0, "qs Some should be empty"),
                None => panic!("qs should be Some when *opt taken"),
            }
        },
        other => panic!("expected Proc::PInputsOptTagged([], Some([]), _), got {:?}", other),
    }
}

#[test]
fn pred4_opt_taken_nonempty_via_wpds() {
    let result = Proc::parse_via_wpda("( @(0) ? x ) . { 0 } with [ 0 ]")
        .expect("'( @(0) ? x ) . { 0 } with [ 0 ]' parses");
    match &result {
        Proc::PInputsOptTagged(ns, qs, _scope) => {
            assert_eq!(ns.len(), 1, "ns should have 1 element");
            match qs {
                Some(v) => {
                    assert_eq!(v.len(), 1, "qs Some should have 1 element");
                    assert!(matches!(&v[0], Proc::PZero));
                },
                None => panic!("qs should be Some when *opt taken"),
            }
        },
        other => panic!("expected Proc::PInputsOptTagged([_], Some([_]), _), got {:?}", other),
    }
}
