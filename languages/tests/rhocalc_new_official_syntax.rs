//! RhoCalc `new` vs official Rholang `new` — surface, scope, and ambiguity pins.
//!
//! RhoCalc IS Rholang. On 2026-07-24 the `new` production dropped its
//! RhoCalc-only GROUPING PARENTHESES, realigning the declaration list with both
//! normative sources:
//!
//! | source | production |
//! |---|---|
//! | `rholang-tree-sitter/grammar.js:89-93` | `new: prec(1, seq('new', $.name_decls, 'in', $._proc))` |
//! | `rholang_mercury.cf:72` | `PNew. Proc1 ::= "new" [NameDecl] "in" Proc1 ;` |
//!
//! ```text
//! before  PNew . ^[xs].p |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
//! after   PNew . ^[xs].p |- "new"     xs.*sep(",")     "in" "{" p "}" : Proc;
//! ```
//!
//! The body stays DELIMITED — the one remaining divergence, and a deliberate,
//! measured one. Official Rholang's body is any `_proc`; making RhoCalc's body a
//! bare trailing `Proc` was implemented and measured on 2026-07-24 and rejected
//! because a trailing OPEN-ENDED same-category operand stops at the first infix
//! operator (`new x in 1 + 2` realized `(new x in 1) + 2`, `new x in a or b`
//! realized `(new x in a) or b` — a SILENT mis-scope) and because it doubled
//! parse counts versus the un-wrapped control (`for(z <- a){*(z)}` 1 → 2;
//! `*(@(0))` 1 → 2). Neither was fixable with a binding-power annotation.
//! Tracked as convergence item §17.10-B1.
//!
//! What is pinned here:
//!
//! 1. **SURFACE** — the paren-free form parses at every arity; the retired
//!    grouping-paren form does NOT (clean break, no dual-accept, so no rule pair
//!    accepts one string — the failure mode behind the ROOT-P Layer-F blowup).
//! 2. **SCOPE** — the `}` closes the body before any following operator, so `|`
//!    scoping is context-INDEPENDENT and agrees with official Rholang, where
//!    `PNew`'s body (`Proc1`) is tighter than `PPar`'s (`Proc`).
//! 3. **AMBIGUITY** — every `new` surface realizes exactly ONE parse, and
//!    wrapping a process in `new x in { … }` never multiplies its parse count.

use mettail_languages::rhocalc::Proc;

/// Number of realized parses for `src` (the ambiguity-preserving count).
fn parse_count(src: &str) -> usize {
    mettail_runtime::clear_var_cache();
    Proc::parse_via_wpda_all_with_weights(src)
        .unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
        .0
        .len()
}

fn parse(src: &str) -> Proc {
    mettail_runtime::clear_var_cache();
    Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"))
}

fn binder_count(p: &Proc) -> usize {
    match p {
        Proc::PNew(scope) => scope.unsafe_pattern().len(),
        other => panic!("expected Proc::PNew, got {other:?}"),
    }
}

fn new_body(p: &Proc) -> &Proc {
    match p {
        Proc::PNew(scope) => scope.unsafe_body(),
        other => panic!("expected Proc::PNew, got {other:?}"),
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 1. SURFACE — the paren-free declaration list, and only that
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn official_paren_free_decl_list_parses_at_every_arity() {
    for (src, want_binders) in [
        ("new x in { Nil }", 1),
        ("new x, y in { Nil }", 2),
        ("new x, y, z in { Nil }", 3),
    ] {
        let t = parse(src);
        assert_eq!(binder_count(&t), want_binders, "`{src}` binder count");
        assert_eq!(parse_count(src), 1, "`{src}` must be unambiguous");
    }
}

#[test]
fn whitespace_around_the_decl_list_is_free() {
    // The list is delimited by the `new` keyword and the `in` keyword only —
    // there is no grouping bracket left to anchor on.
    for src in ["new x in { Nil }", "new  x  in  { Nil }", "new x,y in { Nil }", "new x ,  y in { Nil }"]
    {
        assert!(matches!(parse(src), Proc::PNew(_)), "`{src}` must be a PNew");
    }
}

#[test]
fn retired_grouping_paren_form_is_rejected() {
    // The pre-2026-07-24 RhoCalc-only shape is GONE — a clean break, no alias.
    // Retaining both would put two rules on one surface, the exact
    // enclosing-rule redundancy behind the ROOT-P Layer-F fork explosion
    // (`ForRowPersistentRuleRedundancy.v`).
    for src in ["new(x) in { Nil }", "new (flt) in { Nil }", "new(x, y) in { Nil }"] {
        mettail_runtime::clear_var_cache();
        assert!(
            Proc::parse(src).is_err(),
            "`{src}` is the retired grouping-paren form and must NOT parse",
        );
    }
}

#[test]
fn the_body_is_a_required_block_a_known_divergence() {
    // Official Rholang accepts any `_proc` as the body. RhoCalc requires the
    // block. Pinned as a REJECT so the day these start parsing is a deliberate
    // change (see the module header and §17.10-B1 for why, with measurements).
    for src in ["new x in Nil", "new x in x!(0)", "new x in 1 + 2", "new x in a or b"] {
        mettail_runtime::clear_var_cache();
        assert!(
            Proc::parse(src).is_err(),
            "`{src}`: RhoCalc's `new` body is currently a REQUIRED block (§17.10-B1)",
        );
    }
}

#[test]
fn display_round_trips_through_the_new_surface() {
    // Regression pin for the Display spacing fix that landed with this change:
    // `"new"` became the repo's ONLY word-literal immediately followed by a
    // `.*sep(…)` repetition. Without a trailing space it rendered `newx in …`,
    // which re-lexes as the single Ident `newx` and breaks the roundtrip.
    for src in [
        "new x in { Nil }",
        "new x, y in { Nil }",
        "new x in { Nil | Nil }",
        "new x in { x!(0) }",
        "new x in { new y in { Nil } }",
    ] {
        let shown = format!("{}", parse(src));
        assert!(
            shown.starts_with("new "),
            "`{src}` displayed as {shown:?} — `new` must not glom with the first binder",
        );
        mettail_runtime::clear_var_cache();
        Proc::parse(&shown)
            .unwrap_or_else(|e| panic!("display {shown:?} of `{src}` must re-parse: {e:?}"));
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 2. SCOPE — the `}` closes the body; `|` scoping is context-independent
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn a_following_par_stays_outside_the_new_body() {
    // Official: `PNew. Proc1` is TIGHTER than `PPar. Proc ::= Proc "|" Proc1`,
    // so a `|` after the `new` belongs to the enclosing par, not to the body.
    let t = parse("new x in { Nil } | Nil");
    match &t {
        Proc::PParInfix(lhs, _rhs) => {
            assert!(matches!(**lhs, Proc::PNew(_)), "the `new` is the LEFT par operand");
            assert!(matches!(new_body(lhs), Proc::PZero), "the body is the bare `Nil`");
        },
        other => panic!("expected PParInfix(PNew(..), ..), got {other:?}"),
    }
    assert_eq!(parse_count("new x in { Nil } | Nil"), 1);
}

#[test]
fn par_scope_is_context_independent() {
    // The same phrase must scope identically at top level and as a `{ … }`
    // collection element. A brace-free body did NOT satisfy this (measured
    // 2026-07-24: `|` outside at top level, INSIDE within a collection element)
    // — the delimited body does, because `}` ends the body unconditionally.
    match &parse("{ new x in { Nil } | Nil }") {
        Proc::PPar(members) => {
            assert_eq!(members.len(), 2, "a TWO-member par: the `|` is outside the `new` body")
        },
        other => panic!("expected PPar, got {other:?}"),
    }
    assert_eq!(parse_count("{ new x in { Nil } | Nil }"), 1);
    match &parse("{ new x in { 0 } | 0 }") {
        Proc::PPar(members) => assert_eq!(members.len(), 2),
        other => panic!("expected PPar, got {other:?}"),
    }
}

#[test]
fn braces_put_the_par_inside_the_new_body() {
    // The `{ … }` are `PNew`'s OWN delimiters, so the body is the raw
    // `PParInfix` chain (it folds to the `PPar` multiset at evaluation time via
    // `merge_pp_parallel`, not at parse time). Unchanged by the paren-drop.
    match new_body(&parse("new x in { Nil | Nil }")) {
        Proc::PParInfix(l, r) => {
            assert!(matches!(**l, Proc::PZero) && matches!(**r, Proc::PZero));
        },
        other => panic!("expected the body to be `Nil | Nil`, got {other:?}"),
    }
}

#[test]
fn new_nests_and_composes() {
    for src in [
        "new x in { new y in { Nil } }",
        "new x in { for(z <- x){ Nil } }",
        "for(p <- x){ new k in { k!(0) } }",
        "new x in { for(z <- a){*(z)} | a!(0) }",
        "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2){p} }",
    ] {
        mettail_runtime::clear_var_cache();
        Proc::parse(src).unwrap_or_else(|e| panic!("`{src}` must parse: {e:?}"));
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 3. AMBIGUITY — wrapping in `new` never multiplies the parse count
// ══════════════════════════════════════════════════════════════════════════

/// PARSE-COUNT GOLDEN. Every expected value below was MEASURED under the
/// PRE-CHANGE production (`"new" "(" xs.*sep(",") ")" "in" "{" p "}"`) on
/// 2026-07-24 and is reproduced EXACTLY by the paren-free production — the
/// paren-drop is ambiguity-neutral by measurement, not by assertion.
///
/// The two `2`s are PRE-EXISTING ambiguities of the BODY, not of `new`:
/// `for(…){…}` and `*(@(…))` bodies already realized two parses under the old
/// production. They are pinned here (rather than filed as `new` regressions) so
/// that if they ever change, the diff points at the body construct that owns
/// them. Do NOT "fix" a value here without re-measuring the control.
const PARSE_COUNT_GOLDEN: &[(&str, usize)] = &[
    ("new x in { Nil }", 1),
    ("new x, y in { Nil }", 1),
    ("new x, y, z in { Nil }", 1),
    ("new x in { Nil | Nil }", 1),
    ("new x in { x!(0) }", 1),
    ("new x, y in { x!(0) | y!(1) }", 1),
    ("new x in { new y in { Nil } }", 1),
    ("new x in { Nil } | Nil", 1),
    ("Nil | new x in { Nil }", 1),
    ("{ new x in { Nil } | Nil }", 1),
    ("new r in { x!(*r, a) | for(p <- r){p} }", 1),
    ("new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2){p} }", 1),
    // pre-existing body ambiguities, unchanged by the paren-drop
    ("new x in { for(z <- a){*(z)} }", 2),
    ("new x in { for(z <- a){*(z)} | a!(0) }", 2),
    ("new x in { *(@(0)) }", 2),
];

#[test]
fn parse_counts_match_the_pre_change_golden() {
    let mut wrong = Vec::new();
    for (src, want) in PARSE_COUNT_GOLDEN {
        let got = parse_count(src);
        if got != *want {
            wrong.push(format!("  `{src}`: want {want}, got {got}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "the paren-drop must be ambiguity-NEUTRAL; these surfaces moved:\n{}",
        wrong.join("\n"),
    );
}

#[test]
fn new_never_multiplies_the_ambiguity_of_a_non_ambiguous_body() {
    // The wrapper itself contributes no fork: for a body that is unambiguous on
    // its own, `new x in { body }` stays unambiguous at every binder arity.
    for body in ["Nil", "Nil | Nil", "x!(0)", "1 + 2", "true or false", "{ Nil | Nil }"] {
        let control = parse_count(body);
        assert_eq!(control, 1, "test premise: control `{body}` is unambiguous");
        for decls in ["x", "x, y", "x, y, z"] {
            let src = format!("new {decls} in {{ {body} }}");
            assert_eq!(
                parse_count(&src),
                1,
                "`{src}` must not multiply the parse count of an unambiguous body",
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// 4. Other known divergences from official Rholang (pinned as-is)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn empty_decl_list_is_accepted_a_known_divergence() {
    // Official `name_decls` is `commaSep1` / `separator nonempty NameDecl ","`
    // — at least ONE declaration. RhoCalc's PNew-style binder loop is lowered
    // with `allow_empty: true` (`wpda_codegen/binder.rs`), so a zero-binder
    // `new` parses. Pre-existing (the retired form accepted `new () in { P }`
    // the same way) and tracked as convergence item §17.10-A4; pinned so the
    // behaviour is a DECISION rather than an accident.
    assert_eq!(
        binder_count(&parse("new in { Nil }")),
        0,
        "RhoCalc accepts a zero-binder `new`; official Rholang does not",
    );
}

#[test]
fn uri_declarations_are_not_yet_supported() {
    // Official `name_decl: seq($.var, optional(seq('(', $.uri_literal, ')')))`
    // — e.g. ``new stdout(`rho:io:stdout`) in { … }``, the standard way a
    // Rholang program reaches a system channel. RhoCalc has neither a
    // `uri_literal` token nor a per-name URI slot in the binder loop. Tracked
    // as convergence item §17.10-C1. Pinned as a REJECT so the day it starts
    // parsing is a deliberate change.
    mettail_runtime::clear_var_cache();
    assert!(
        Proc::parse("new stdout(`rho:io:stdout`) in { stdout!(\"hi\") }").is_err(),
        "URI name-declarations are not implemented yet (§17.10-C1)",
    );
}
