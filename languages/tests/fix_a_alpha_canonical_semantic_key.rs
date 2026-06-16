//! FIX-A regression tests: the semantic-identity path (`semantic_hash` →
//! `exact_key`/`content_key`) is alpha-canonical and deterministic for
//! binder-bearing terms.
//!
//! Before FIX-A, the generated `semantic_hash` hashed a binder's moniker
//! `unique_id` — a process-global counter freshened by every `unbind` and never
//! reset — so two alpha-equivalent terms (or the same term hashed twice) produced
//! DIFFERENT keys, breaking ambiguity dedup and the WPDA seed identity. FIX-A
//! hashes the binder by ARITY and the body by its de-Bruijn `BoundVar`
//! coordinates, which are name-free and already alpha-canonical.
//!
//! `Lambda` is the minimal single-binder language; `λx.x` (`lam x. x`) exercises
//! the single-binder arm, and the nesting cases exercise de-Bruijn depth.
#![cfg(feature = "lambda")]

use mettail_languages::lambda::Term;
use mettail_runtime::FramedSemanticKeyHasher;

/// The exact semantic key (framed write-stream) recorded by `semantic_hash` —
/// the same stream that backs `exact_key` ambiguity dedup.
fn semantic_key(t: &Term) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    t.semantic_hash(&mut hasher);
    hasher.into_key()
}

#[test]
fn alpha_equivalent_binders_share_semantic_key() {
    // λx.x and λy.y are alpha-equivalent and differ ONLY in the bound-variable
    // name (hence in the binder's `unique_id`). FIX-A requires identical keys.
    let lam_x = Term::parse("lam x. x").expect("λx.x parses");
    let lam_y = Term::parse("lam y. y").expect("λy.y parses");
    assert_eq!(
        semantic_key(&lam_x),
        semantic_key(&lam_y),
        "λx.x and λy.y are alpha-equivalent — their semantic keys must be equal"
    );
}

#[test]
fn semantic_key_is_deterministic_across_parses() {
    // The same source parsed twice must yield byte-identical keys: no transient
    // `unique_id` may leak into the fingerprint.
    let a = Term::parse("lam x. lam y. x").expect("parses");
    let b = Term::parse("lam x. lam y. x").expect("parses again");
    assert_eq!(
        semantic_key(&a),
        semantic_key(&b),
        "the semantic key must be a deterministic function of the term"
    );
}

#[test]
fn distinct_terms_keep_distinct_keys() {
    // FIX-A must NOT over-collapse: structurally distinct terms keep distinct
    // keys. The de-Bruijn body disambiguates binder depth (`λx.x` binds at depth
    // 0; in `λx.λy.x` the `x` occurrence is at depth 1) and constructor shape.
    let id = Term::parse("lam x. x").expect("λx.x parses");
    let const_k = Term::parse("lam x. lam y. x").expect("λx.λy.x parses");
    let self_app = Term::parse("lam x. (x, x)").expect("λx.(x x) parses");

    assert_ne!(
        semantic_key(&id),
        semantic_key(&const_k),
        "λx.x and λx.λy.x are not alpha-equivalent"
    );
    assert_ne!(
        semantic_key(&id),
        semantic_key(&self_app),
        "λx.x and λx.(x x) differ structurally"
    );
    assert_ne!(
        semantic_key(&const_k),
        semantic_key(&self_app),
        "λx.λy.x and λx.(x x) differ structurally"
    );
}
