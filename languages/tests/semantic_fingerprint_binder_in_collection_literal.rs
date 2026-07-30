//! # #154 — a binder inside a COLLECTION LITERAL must not leak its `unique_id`
//!
//! `semantic_hash` is the alpha-canonical fingerprint of a term. It backs
//! `semantic_fingerprint` → `exact_key` / `content_key`, which is the realize
//! ambiguity-dedup surface, so **its value is consensus-visible**: two nodes that
//! disagree about a fingerprint disagree about which parse alternatives are the
//! same reading.
//!
//! ## The mechanism, confirmed at source before it was fixed
//!
//! `macros/src/gen/term_ops/semantic_hash.rs` had TWO arms for containers of
//! sub-terms, and only one of them was correct:
//!
//! * `VariantKind::Collection` — a category-DIRECT collection field such as
//!   `PPar . ps:HashBag(Proc)` — routed through `semantic_hash_collection`, which
//!   hashes each element with the ELEMENT's `semantic_hash`. That was FIX-A
//!   (2026-06-29), landed for exactly this defect.
//! * `VariantKind::CollectionLiteral` — a collection CATEGORY declared as a
//!   native-type alias (`![HashMapLit<Proc, Proc>] as Map`, `PathMapLit` as
//!   `Pathmap`, `Vec<Proc>` as `List`, …) — shared the `VariantKind::Literal`
//!   arm, whose body is
//!
//!   ```text
//!   state.write_u8(#variant_idx);
//!   std::hash::Hash::hash(v, state);      ← STRUCTURAL Hash
//!   ```
//!
//! Structural `Hash` on a binder-bearing `Proc` writes the binder's moniker
//! `unique_id` — a process-global counter freshened by every `unbind` and never
//! reset. So a binder reached through a MAP LITERAL was fingerprinted with a
//! run-varying number, while the same binder reached through a `PPar` bag was not.
//!
//! ★ #154 and #162 are therefore the SAME root cause seen from two angles: the
//! `CollectionLiteral` discriminant exists so every consumer declares its intent,
//! and `semantic_hash` was one of the consumers that had not.
//!
//! ## What these tests are
//!
//! Unlike `generated_traversal_boundary_laws.rs` (conservation laws, which pass
//! before and after by design), these are **fix gates**: each one is RED against
//! the structural-`Hash` arm and GREEN against the `semantic_hash_into` arm.
#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;
use mettail_runtime::FramedSemanticKeyHasher;

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{input}`: {e}"))
}

/// The exact framed write-stream `semantic_hash` records — the same stream that
/// backs `exact_key` ambiguity dedup.
fn semantic_key(term: &Proc) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    term.semantic_hash(&mut hasher);
    hasher.into_key()
}

/// The structural `Hash` stream, for CONTRAST. `semantic_hash` and `Hash` are
/// *supposed* to differ on binder-bearing terms: the first is alpha-canonical,
/// the second is structural and includes `unique_id`.
fn structural_key(term: &Proc) -> Vec<u8> {
    use std::hash::Hash;
    let mut hasher = FramedSemanticKeyHasher::default();
    term.hash(&mut hasher);
    hasher.into_key()
}

/// Sources whose binder sits INSIDE a collection literal, one per literal shape
/// the grammar admits. Each is paired with an ALPHA-EQUIVALENT twin that differs
/// only in the bound name — hence only in `unique_id`.
///
/// ⚠ The pairs are the instrument. "Hash the same source twice" is a weaker test:
/// a cache could return an identical `unique_id` for a repeated identifier and the
/// leak would still be there. Renaming the binder forces a genuinely different
/// `unique_id` for a term that must fingerprint identically.
///
/// ★★ **Why the binder is `new` and NOT `for`, and this is a MEASUREMENT.** The
/// first draft of this file used `for(@a <- @"c"){ Nil }`, and every row was red —
/// including the `PPar` CONTROL, which was supposed to be FIX-A's already-working
/// case. Probing the shapes separately (2026-07-30) found the reason:
///
/// ```text
///   new a in { Nil }                SAME  (alpha-canonical)
///   new a in { a!(1) }              SAME  (alpha-canonical)
///   for(@a <- @"c"){ Nil }          DIFFERS  ← leaks, with NO collection anywhere
///   for(@a <- @"c"){ @a!(1) }       DIFFERS  ← leaks
///   new a in { Nil } | 1            SAME
///   for(@a <- @"c"){ Nil } | 1      DIFFERS  ← the `PPar` control, red for the SAME reason
/// ```
///
/// So `for` carries an `unique_id` leak of its OWN, reachable with no collection in
/// the term at all. That is a DIFFERENT defect in a different arm (the
/// `PForUser` / `ForRow` / `InputBind` family, not the collection-literal arm), and
/// a #154 gate built on `for` would have conflated the two: it would have stayed
/// red after this fix and been blamed on the fix. `new` isolates the arm under
/// test. The `for` leak is reported separately.
const ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL: &[(&str, &str, &str)] = &[
    ("map VALUE position", "{1: new a in { a!(1) }}", "{1: new b in { b!(1) }}"),
    ("map KEY position", "{new a in { a!(1) }: 1}", "{new b in { b!(1) }: 1}"),
    ("list ELEMENT position", "[new a in { a!(1) }]", "[new b in { b!(1) }]"),
    ("set ELEMENT position", "Set(new a in { a!(1) })", "Set(new b in { b!(1) })"),
    (
        "pathmap VALUE position",
        "{|1 : new a in { a!(1) }|}",
        "{|1 : new b in { b!(1) }|}",
    ),
    (
        "nested — a list inside a map value",
        "{1: [new a in { a!(1) }]}",
        "{1: [new b in { b!(1) }]}",
    ),
];

/// ★★ **THE #154 GATE.**
///
/// A binder inside a collection literal must be fingerprinted alpha-canonically,
/// exactly as a binder inside a `PPar` bag already was. Two alpha-equivalent
/// terms must produce the IDENTICAL framed `semantic_hash` stream.
///
/// **What makes it red:** the arm calling structural `std::hash::Hash` instead of
/// the element's `semantic_hash`. Reverting `semantic_hash`'s `CollectionLiteral`
/// arm back onto the `Literal` arm turns every row below red.
#[test]
fn a_binder_inside_a_collection_literal_is_fingerprinted_alpha_canonically() {
    let mut leaked: Vec<String> = Vec::new();
    for (position, left_source, right_source) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        mettail_runtime::clear_var_cache();
        let left = parse(left_source);
        mettail_runtime::clear_var_cache();
        let right = parse(right_source);

        if semantic_key(&left) != semantic_key(&right) {
            leaked.push(format!(
                "  {position}: `{left_source}` vs `{right_source}`\n    left  = {:02x?}\n    \
                 right = {:02x?}",
                &semantic_key(&left)[..semantic_key(&left).len().min(40)],
                &semantic_key(&right)[..semantic_key(&right).len().min(40)],
            ));
        }
    }
    assert!(
        leaked.is_empty(),
        "#154: the semantic fingerprint of a binder inside a COLLECTION LITERAL varies with \
         the bound NAME, which means it varies with the binder's run-generated moniker \
         `unique_id`. `semantic_hash` is consensus-visible — it backs `exact_key` / \
         `content_key` realize dedup — so two nodes that generated different `unique_id`s \
         would disagree about which readings are the same.\n\
         The arm is calling structural `std::hash::Hash` on the container instead of the \
         element's `semantic_hash` (see this file's header, and \
         `semantic_hash.rs`'s `VariantKind::CollectionLiteral`).\n\
         Positions that leaked:\n{}",
        leaked.join("\n")
    );
}

/// ⚠ **THE NON-VACUITY CONTROL.** The test above would pass trivially if the
/// twins' fingerprints agreed for a reason that has nothing to do with the fix —
/// most obviously if `semantic_hash` collapsed the binder to nothing at all, or if
/// the two sources parsed to the same term because the renaming was ignored.
///
/// So: the STRUCTURAL keys of the same twins must DIFFER. That is the leak, still
/// present in `Hash` where it belongs, and it proves the twins really do carry
/// different `unique_id`s — which is what makes their `semantic_hash` agreement
/// meaningful.
#[test]
fn the_twins_really_do_carry_different_unique_ids() {
    let mut identical: Vec<&str> = Vec::new();
    for (position, left_source, right_source) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        mettail_runtime::clear_var_cache();
        let left = parse(left_source);
        mettail_runtime::clear_var_cache();
        let right = parse(right_source);
        if structural_key(&left) == structural_key(&right) {
            identical.push(position);
        }
    }
    assert!(
        identical.is_empty(),
        "the alpha-twins have IDENTICAL structural `Hash` streams at these positions: {identical:?}.\n\
         Then they do not carry different moniker `unique_id`s, and \
         `a_binder_inside_a_collection_literal_is_fingerprinted_alpha_canonically` is a \
         VACUOUS pass — it would stay green with the defect fully present. Either the \
         binder is not reaching the literal, or `Hash` stopped being structural."
    );
}

/// The sibling that proves the fix is about the LITERAL arm and not about binders
/// in general: a binder inside a `PPar` bag — a `VariantKind::Collection` FIELD,
/// fixed by FIX-A in 2026-06-29 — was already alpha-canonical. This row is the
/// CONTROL that says the defect was specific to the collection-LITERAL arm.
#[test]
fn a_binder_inside_a_par_bag_was_already_alpha_canonical() {
    mettail_runtime::clear_var_cache();
    let left = parse("new a in { a!(1) } | 1");
    mettail_runtime::clear_var_cache();
    let right = parse("new b in { b!(1) } | 1");
    assert_eq!(
        semantic_key(&left),
        semantic_key(&right),
        "a binder inside a `PPar(HashBag<Proc>)` must be alpha-canonical — this is FIX-A's \
         own property, and if it is red the regression is in `semantic_hash_collection`, \
         not in the collection-LITERAL arm"
    );
}

/// Determinism across repeated fingerprinting of the SAME term. Weaker than the
/// alpha-twin test, but it catches a different failure: a work-stack pool that
/// leaks state between `semantic_hash` calls.
#[test]
fn the_fingerprint_of_one_term_is_stable_across_repeated_calls() {
    for (position, source, _) in ALPHA_TWINS_WITH_A_BINDER_INSIDE_A_LITERAL {
        let term = parse(source);
        let first = semantic_key(&term);
        let second = semantic_key(&term);
        assert_eq!(
            first, second,
            "{position}: fingerprinting `{source}` twice gave different streams — the \
             `SEMANTIC_HASH_TASK_POOL` is leaking work between calls"
        );
        assert!(
            !first.is_empty(),
            "{position}: `{source}` fingerprinted to an EMPTY stream, so every assertion \
             about it is vacuous"
        );
    }
}
