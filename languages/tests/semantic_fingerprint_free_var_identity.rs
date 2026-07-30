//! # #190 — a FREE VARIABLE's semantic fingerprint must not be a process counter
//!
//! `semantic_hash` is the alpha-canonical fingerprint of a term. It backs
//! `semantic_fingerprint` → `exact_key` / `content_key`, the realize
//! ambiguity-dedup surface, so **its value is consensus-visible**: two nodes that
//! disagree about a fingerprint disagree about which parse alternatives are the
//! same reading.
//!
//! ## The mechanism, confirmed at the GENERATED arm before the fix
//!
//! `macros/src/gen/term_ops/semantic_hash.rs`'s `VariantKind::Var` arm emitted
//!
//! ```text
//!   #category::#label(v) => {
//!       state.write_u8(0xFBu8);
//!       std::hash::Hash::hash(v, state);      ← STRUCTURAL Hash on an `OrdVar`
//!   }
//! ```
//!
//! and `OrdVar(pub Var<String>)` derives `Hash`, so the payload written for a free
//! variable is whatever `moniker`'s `impl Hash for FreeVar` writes. That impl is
//! (`moniker-0.5.0/src/free_var.rs:45`):
//!
//! ```text
//!   fn hash<H: Hasher>(&self, state: &mut H) {
//!       self.unique_id.hash(state);           ← and NOTHING else
//!   }
//! ```
//!
//! `UniqueId(u32)` is drawn from a **process-global `AtomicUsize`** starting at 0 and
//! never reset (`moniker-0.5.0/src/unique_id.rs:9`). `pretty_name` — the SOURCE NAME,
//! the only deterministic identity a free variable has — was discarded entirely.
//!
//! So the entire payload of a free-variable leaf in a consensus-visible fingerprint
//! was an accident of how many variables the process had happened to allocate.
//!
//! ## ★★ The witness is stronger than alpha-renaming, and the difference matters
//!
//! The defect was first reported as "`for(@a <- @"c"){ Nil }` fingerprints
//! differently from its alpha-renamed twin, localised to the receive-binder family
//! `PForUser` / `ForRow` / `InputBind`". Measured 2026-07-30, that is **not** the
//! mechanism, and the correction is load-bearing in two directions:
//!
//! ```text
//!   PARSED AST of `for(@a <- @"c"){ Nil }`:
//!     PForUser([ForRowSingleNoWhere(InputBindQuoted(
//!         PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(0), pretty_name: Some("a") }))),
//!         NQuoteShort(CastStr(StringLit("c")))))],
//!       PZero)
//! ```
//!
//! 1. **There is no `Scope` anywhere in it.** Rholang's `for` binds `a` in the body
//!    *semantically*, but the AST layer represents the receive pattern as an ordinary
//!    **free** `PVar` and resolves the binding at COMM time through the substitution
//!    TRS. So `for(@a <- c){ Nil }` and `for(@b <- c){ Nil }` are **not** alpha-variants
//!    at this layer — they are two different terms that `Display` renders differently,
//!    and a fingerprint that merged them would merge two distinct source programs.
//!    ⇒ The "alpha-renamed twin" framing would have demanded the WRONG fix.
//! 2. **The family is not the receive-binder family.** The leak is in the auto-injected
//!    `Var` variant that EVERY category has, so the minimal witness has no `for` in it
//!    at all: the bare term `a`, 24 B, unstable across two parses of the SAME source.
//!    `new` is a true negative control, but for a different reason than reported — a
//!    `PNew` holds a real moniker `Scope` whose pattern contributes only
//!    `write_usize(len)` and whose body occurrences are `Var::Bound` (de Bruijn,
//!    already alpha-canonical), so no `Var::Free` arm is reached.
//!
//! The correct, unambiguous statement of the defect is therefore **determinism**, not
//! alpha-invariance: *the same source text, parsed twice, produced two different
//! consensus fingerprints.* Measured before the fix:
//!
//! ```text
//!   `a`                        63→24 B   UNSTABLE   UniqueId(0)  vs UniqueId(1)
//!   `a!(1)`                        55 B   UNSTABLE   UniqueId(2)  vs UniqueId(3)
//!   `for(@a <- @"c"){ Nil }`       63 B   UNSTABLE   UniqueId(4)  vs UniqueId(18)
//!   `for(@a <- @"c"){ Nil } | 1`   94 B   UNSTABLE   UniqueId(38) vs UniqueId(54)
//!   `new a in { Nil }`             21 B   stable
//!   `new a in { a!(1) }`           79 B   stable
//!   `@"c"!(1)`                     47 B   stable
//!   `1`                            29 B   stable
//! ```
//!
//! ★ Note the byte COUNTS: 63 B against 63 B, 94 B against 94 B. The leak is a
//! *value* in a fixed-width field, so a length- or count-based check is structurally
//! blind to it and **only a digest comparison can see it** — the same instrument
//! lesson #154's composition gate recorded.
//!
//! ## The fix, and the ONE thing it trades away
//!
//! A free variable is now fingerprinted by its **source name**:
//!
//! ```text
//!   Var::Free(fv)  →  tag 0  ++  (1 ++ hash(pretty_name)) | 0        [name-based]
//!   Var::Bound(bv) →  tag 1  ++  hash(scope) ++ hash(binder)         [de Bruijn]
//! ```
//!
//! There is no design freedom here: `FreeVar` has exactly two fields, `unique_id` is
//! nondeterministic by construction, so `pretty_name` is the only deterministic
//! identity available.
//!
//! ⚠ **The trade, stated as a live assertion below and not as prose:** two *distinct*
//! `FreeVar`s that share a `pretty_name` now fingerprint IDENTICALLY. That is exactly
//! what `languages/src/rholang/guard_substrate.rs`'s `var_key` refuses to do, and the
//! two are not in conflict — they answer different questions. `var_key` needs
//! *within-process binder identity* (which binder does this guard constrain?), so it
//! keys on `name$unique_id`. A consensus fingerprint needs *cross-process
//! determinism*, which forbids `unique_id` outright. The surface language cannot tell
//! two same-named free variables apart either: `Display` renders both as `a`, so
//! `parse(display(t))` already merges them.
#![cfg(feature = "rholang")]

use mettail_languages::rholang::Proc;
use mettail_runtime::{FramedSemanticKeyHasher, FreeVar, OrdVar, Var};

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
/// *supposed* to differ here: the first must be a function of the term's meaning,
/// the second is structural and includes `unique_id`.
fn structural_key(term: &Proc) -> Vec<u8> {
    use std::hash::Hash;
    let mut hasher = FramedSemanticKeyHasher::default();
    term.hash(&mut hasher);
    hasher.into_key()
}

/// Parse `source` twice with the name→`FreeVar` memo cleared in between, so the two
/// parses are forced to allocate genuinely different `unique_id`s for the same name.
fn parse_twice(source: &str) -> (Proc, Proc) {
    mettail_runtime::clear_var_cache();
    let first = parse(source);
    mettail_runtime::clear_var_cache();
    let second = parse(source);
    (first, second)
}

/// Sources that contain at least one FREE variable, one per shape that reaches the
/// `Var` arm by a different route. Every one of these must fingerprint identically
/// on two parses of the *same text*.
///
/// ⚠ `clear_var_cache()` is the instrument. Without it the process-wide name→var memo
/// hands both parses the same `FreeVar` and every row passes with the defect fully
/// present — which is precisely the situation two DIFFERENT nodes are never in.
const SOURCES_WITH_A_FREE_VARIABLE: &[(&str, &str)] = &[
    ("bare var — the MINIMAL witness, no binder and no collection", "a"),
    ("var in a Name position", "a!(1)"),
    ("var under a receive pattern (`PForUser`/`ForRow`/`InputBind`)", "for(@a <- @\"c\"){ Nil }"),
    ("var under an unquoted receive pattern", "for(a <- @\"c\"){ Nil }"),
    ("receive pattern inside a `PPar`", "for(@a <- @\"c\"){ Nil } | 1"),
    ("var inside a list literal", "[a]"),
    ("var inside a map literal VALUE", "{1: a}"),
    ("var inside a set literal", "Set(a)"),
    ("var inside a pathmap literal VALUE", "{|1 : a|}"),
    ("free var inside a `new` SCOPE body — bound sibling in the same term", "new x in { a!(1) }"),
    ("two DISTINCT free vars in one term", "a!(1) | b!(2)"),
    ("the SAME free var twice in one term", "a!(1) | a!(2)"),
];

/// ★★ **THE #190 GATE — determinism of a free variable's fingerprint.**
///
/// Two parses of the SAME source must produce the IDENTICAL framed `semantic_hash`
/// stream. Anything else means the fingerprint is a function of the process's
/// variable-allocation history rather than of the term.
///
/// **What makes it red:** the `Var` arm calling `std::hash::Hash::hash(v, state)` on
/// the `OrdVar`, which routes to `moniker`'s `impl Hash for FreeVar` and writes the
/// process-global `unique_id`. Reverting `semantic_hash.rs`'s `VariantKind::Var` arm
/// to that one line turns every row below red.
#[test]
fn the_fingerprint_of_a_free_variable_is_independent_of_the_process_counter() {
    let mut leaked: Vec<String> = Vec::new();
    for (shape, source) in SOURCES_WITH_A_FREE_VARIABLE {
        let (first, second) = parse_twice(source);
        let (left, right) = (semantic_key(&first), semantic_key(&second));
        if left != right {
            let at = left.iter().zip(right.iter()).position(|(a, b)| a != b);
            leaked.push(format!(
                "  {shape}\n    source     = `{source}`\n    first  ({:>3} B) = {:02x?}\n    \
                 second ({:>3} B) = {:02x?}\n    first differing byte index = {at:?}",
                left.len(),
                &left[..left.len().min(48)],
                right.len(),
                &right[..right.len().min(48)],
            ));
        }
    }
    assert!(
        leaked.is_empty(),
        "#190: the semantic fingerprint of a term containing a FREE VARIABLE changed \
         between two parses of the SAME SOURCE TEXT. `semantic_hash` is consensus-visible \
         — it backs `semantic_fingerprint` → `exact_key`/`content_key` realize dedup — so \
         two nodes whose process-global `moniker::UniqueId` counters had diverged (which is \
         always) would disagree about which readings are the same reading.\n\
         The `Var` arm is writing `moniker`'s structural `Hash for FreeVar`, which is \
         `self.unique_id.hash(state)` and NOTHING else: an `AtomicUsize` draw, not a \
         property of the term. See this file's header and \
         `macros/src/gen/term_ops/semantic_hash.rs`'s `VariantKind::Var`.\n\
         ★ Note the byte COUNTS below are equal — the leak is a value in a fixed-width \
         field, so only this digest comparison can see it.\n\
         Shapes that leaked:\n{}",
        leaked.join("\n")
    );
}

/// ⚠ **THE NON-VACUITY CONTROL for the gate above.** The gate would pass trivially
/// if the two parses somehow received the *same* `FreeVar` — most obviously if
/// `clear_var_cache()` stopped clearing, or if the parser started interning names in
/// a second cache the test does not reach. Then every row would agree for a reason
/// that has nothing to do with the fix.
///
/// So: the STRUCTURAL keys of the same pairs must DIFFER. That is the `unique_id`,
/// still present in `Hash` where it belongs, and it is what makes the `semantic_hash`
/// agreement above meaningful.
#[test]
fn the_two_parses_really_do_allocate_different_unique_ids() {
    let mut identical: Vec<&str> = Vec::new();
    for (shape, source) in SOURCES_WITH_A_FREE_VARIABLE {
        let (first, second) = parse_twice(source);
        if structural_key(&first) == structural_key(&second) {
            identical.push(shape);
        }
    }
    assert!(
        identical.is_empty(),
        "these shapes produced IDENTICAL structural `Hash` streams across two parses with \
         `clear_var_cache()` in between: {identical:?}.\n\
         Then the two parses share a `FreeVar`, and \
         `the_fingerprint_of_a_free_variable_is_independent_of_the_process_counter` is a \
         VACUOUS pass — it would stay green with the `unique_id` leak fully present. Either \
         `clear_var_cache` stopped clearing, or `Hash` stopped being structural."
    );
}

/// ⚠ **THE OVER-MERGE CONTROL.** Determinism is trivially achievable by writing
/// *nothing* for a variable, which would collapse every free variable in the language
/// to one fingerprint and silently merge unrelated readings at realize-time dedup.
/// The fix must keep DISTINCT source identifiers distinct.
///
/// ★ Note what this row asserts about `for`, and that it is the OPPOSITE of what the
/// defect report predicted: `for(@a <- @"c"){ Nil }` and `for(@b <- @"c"){ Nil }`
/// must **differ**. Rholang's `for` binds semantically, but the AST models the
/// receive pattern as a free `PVar` with no `Scope`, so these are two distinct terms
/// that `Display` renders differently. A fingerprint that merged them would merge two
/// distinct source programs.
#[test]
fn distinct_source_identifiers_stay_distinguished() {
    let pairs: &[(&str, &str, &str)] = &[
        ("bare vars", "a", "b"),
        ("vars in a Name position", "a!(1)", "b!(1)"),
        (
            "receive patterns — DISTINCT at the AST layer, `for` is not a `Scope`",
            "for(@a <- @\"c\"){ Nil }",
            "for(@b <- @\"c\"){ Nil }",
        ),
        ("one free var vs two", "a!(1) | a!(2)", "a!(1) | b!(2)"),
        ("free occurrence vs BOUND occurrence of the same name", "new a in { b!(1) }", "new a in { a!(1) }"),
    ];
    let mut merged: Vec<&str> = Vec::new();
    for (what, left_source, right_source) in pairs {
        mettail_runtime::clear_var_cache();
        let left = semantic_key(&parse(left_source));
        mettail_runtime::clear_var_cache();
        let right = semantic_key(&parse(right_source));
        if left == right {
            merged.push(what);
        }
    }
    assert!(
        merged.is_empty(),
        "these pairs now share a semantic fingerprint: {merged:?}.\n\
         Determinism was bought by throwing the variable's identity away, which merges \
         unrelated readings at realize-time observational dedup. The `Var` arm must write \
         the free variable's SOURCE NAME (and the bound variable's de-Bruijn coordinates), \
         not nothing."
    );
}

/// ★★ **THE ALPHA-CANONICITY CONTROL that survives the fix.** A binder that the AST
/// really does model as a `Scope` — `new` — must stay alpha-canonical: renaming it
/// changes nothing observable, so the fingerprint must not move. This is the property
/// #154 was gating, restated here because the `Var` arm now sits next to it: the fix
/// must not have made bound occurrences name-sensitive.
#[test]
fn a_scope_bound_binder_is_still_alpha_canonical() {
    let twins: &[(&str, &str, &str)] = &[
        ("unused binder", "new a in { Nil }", "new b in { Nil }"),
        ("used binder", "new a in { a!(1) }", "new b in { b!(1) }"),
        ("binder inside a list literal", "[new a in { a!(1) }]", "[new b in { b!(1) }]"),
        ("binder in a PPar bag", "new a in { a!(1) } | 1", "new b in { b!(1) } | 1"),
        (
            "nested binders — renaming both",
            "new a in { new c in { a!(*c) } }",
            "new b in { new d in { b!(*d) } }",
        ),
    ];
    let mut moved: Vec<String> = Vec::new();
    for (what, left_source, right_source) in twins {
        mettail_runtime::clear_var_cache();
        let left = semantic_key(&parse(left_source));
        mettail_runtime::clear_var_cache();
        let right = semantic_key(&parse(right_source));
        if left != right {
            moved.push(format!("  {what}: `{left_source}` vs `{right_source}`"));
        }
    }
    assert!(
        moved.is_empty(),
        "renaming a `Scope`-BOUND binder changed the semantic fingerprint:\n{}\n\
         A bound occurrence is a `Var::Bound` and must be keyed on its de-Bruijn \
         coordinates alone. If the `Var` arm started writing a bound variable's \
         `pretty_name`, alpha-canonicity — the whole point of `semantic_hash` — is gone.",
        moved.join("\n")
    );
}

/// ★★ **THE DECLARED RESIDUE, as a live assertion rather than a comment.**
///
/// Keying a free variable on its source name means two *distinct* `FreeVar`s that
/// share a `pretty_name` fingerprint identically. That is the one thing the fix trades
/// away, and it is recorded here so it cannot drift silently in either direction:
///
/// * if a future change re-separates them, this test goes RED and the change should
///   say what deterministic discriminator it found (there is no third field on
///   `FreeVar`, so it would have to be a new carrier);
/// * the paired `assert_ne!` on the STRUCTURAL keys proves the two really are distinct
///   `FreeVar`s, so the `assert_eq!` above it is not vacuous.
///
/// The surface language cannot separate them either — `Display` renders both as `a` —
/// so `parse(display(t))` already merges them.
#[test]
fn two_distinct_free_vars_sharing_a_name_are_the_declared_collision() {
    let named = |name: &str| Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named(name))));
    let (left, right) = (named("a"), named("a"));

    assert_ne!(
        structural_key(&left),
        structural_key(&right),
        "two `FreeVar::fresh_named(\"a\")` have the SAME structural `Hash` stream, so they \
         are not distinct `FreeVar`s and the collision assertion below is vacuous. \
         `FreeVar::fresh` draws a new `UniqueId` every call, so this cannot happen unless \
         the structural `Hash` stopped writing `unique_id`."
    );
    assert_eq!(
        semantic_key(&left),
        semantic_key(&right),
        "two DISTINCT `FreeVar`s sharing the pretty name `a` no longer share a semantic \
         fingerprint. That is the declared residue of #190 — a free variable is keyed on \
         its SOURCE NAME because `unique_id` is a process-global counter and there is no \
         third field on `moniker::FreeVar` to key on. If this is now RED, some new \
         deterministic discriminator was introduced and this file's header must name it."
    );

    // Different names must still separate — the residue is about EQUAL names only.
    assert_ne!(
        semantic_key(&named("a")),
        semantic_key(&named("b")),
        "free variables `a` and `b` share a semantic fingerprint. The name is not being \
         written at all, and every free variable in the language has collapsed to one key."
    );
}

/// An ANONYMOUS free variable (`pretty_name: None`) has no source identity to key on.
/// It is written as its own tag, which (a) separates it from every named variable and
/// (b) merges all anonymous ones — mirroring `Display`, which renders them all `_`.
///
/// Recorded as an assertion because "what happens with no name" is exactly the branch
/// a reader assumes rather than checks.
#[test]
fn an_anonymous_free_var_is_tagged_apart_from_every_named_one() {
    let anon = || Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_unnamed())));
    let named = |name: &str| Proc::PVar(OrdVar(Var::Free(FreeVar::fresh_named(name))));

    assert_eq!(
        semantic_key(&anon()),
        semantic_key(&anon()),
        "two anonymous free variables have DIFFERENT semantic fingerprints, so the \
         `pretty_name: None` branch is writing something process-dependent — the only \
         candidate is `unique_id`, i.e. #190 survives in the unnamed branch."
    );
    for name in ["", "_", "a"] {
        assert_ne!(
            semantic_key(&anon()),
            semantic_key(&named(name)),
            "an anonymous free variable collides with the free variable named `{name}`. \
             The `None` branch must write a tag that no `Some(name)` payload can forge, \
             or a term with a generated variable would dedup against a source-level one."
        );
    }
}

/// Determinism across repeated fingerprinting of the SAME term value. Weaker than the
/// two-parse gate, but it catches a different failure: a work-stack pool leaking state
/// between `semantic_hash` calls.
#[test]
fn the_fingerprint_of_one_term_is_stable_across_repeated_calls() {
    for (shape, source) in SOURCES_WITH_A_FREE_VARIABLE {
        let term = parse(source);
        let first = semantic_key(&term);
        let second = semantic_key(&term);
        assert_eq!(
            first, second,
            "{shape}: fingerprinting `{source}` twice gave different streams — the \
             `SEMANTIC_HASH_TASK_POOL` is leaking work between calls"
        );
        assert!(
            !first.is_empty(),
            "{shape}: `{source}` fingerprinted to an EMPTY stream, so every assertion \
             about it is vacuous"
        );
    }
}
