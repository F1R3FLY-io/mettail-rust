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

use mettail_languages::rhocalc::{Name, Proc};

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
    for src in [
        "new x in { Nil }",
        "new  x  in  { Nil }",
        "new x,y in { Nil }",
        "new x ,  y in { Nil }",
    ] {
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

// ══════════════════════════════════════════════════════════════════════════
// 5. FENCE CAPTURE — `new x, y in { P }` is the repo's first depth-0 comma
// ══════════════════════════════════════════════════════════════════════════
//
// Dropping the grouping parens made a multi-binder `new` the first RhoCalc
// `Proc` whose SURFACE carries a comma at bracket depth 0. Any enclosing rule
// that locates a child's right edge by scanning for a literal — a `.*sep(",")`
// separator, or a plain `","` between two slots — then splits INSIDE the `new`.
//
// `Display` closes this with the fence-capture invariant
// (`runtime/src/display_grouping.rs`): a child is wrapped in PraTTaIL's
// TRANSPARENT `( … )` grouping exactly when its rendered text carries one of
// its right fences at depth 0. Two independent halves, both pinned here:
//
//   2026-07-24  ELEMENTS of a `.*sep(S)` repetition, fence `S`.
//   2026-07-25  PLAIN INTERIOR SLOTS, fence = the literal that follows the slot
//               in the template. Found by `gen_rhocalc_prop`, which is seeded
//               and therefore only reproduces the case on the seed that
//               generates it — hence these deterministic pins.

/// A `new a0, a1 in { <body> }` — two binders, so its surface carries a
/// depth-0 comma and every enclosing fence must group it.
fn two_binder_new(body: Proc) -> Proc {
    let binders: Vec<mettail_runtime::Binder<String>> = (0..2)
        .map(|j| mettail_runtime::Binder(mettail_runtime::get_or_create_var(&format!("a{j}"))))
        .collect();
    Proc::PNew(mettail_runtime::Scope::new(binders, std::sync::Arc::new(body)))
}

/// `Display → parse → Display` must reach a fixed point, and every string along
/// the way must parse. Evaluates to the canonical form.
///
/// A macro, not a generic fn: `parse` is an INHERENT method on each generated
/// category (`Proc::parse`, `Name::parse`), not a trait method, so there is no
/// bound to write. This is exactly the shape of the property the proptest
/// checks — `Parse(Display(Parse(s))) ≡ Parse(s)` — evaluated on a fixed term.
macro_rules! assert_display_parse_fixed_point {
    ($cat:ty, $term:expr, $what:expr) => {{
        let what: &str = $what;
        mettail_runtime::clear_var_cache();
        let displayed = format!("{}", $term);
        let parsed = <$cat>::parse(&displayed)
            .unwrap_or_else(|e| panic!("{what}: display {displayed:?} must parse: {e:?}"));
        let canonical = format!("{parsed}");
        mettail_runtime::clear_var_cache();
        let reparsed = <$cat>::parse(&canonical)
            .unwrap_or_else(|e| panic!("{what}: canonical {canonical:?} must parse: {e:?}"));
        assert_eq!(
            canonical,
            format!("{reparsed}"),
            "{}: Display must be idempotent after canonicalization",
            what,
        );
        canonical
    }};
}

#[test]
fn a_new_in_a_plain_comma_fenced_slot_is_grouped() {
    // ★ THE MINIMIZED PROPTEST FAILURE (2026-07-25).
    //
    //   gen_rhocalc_prop::name_display_parse_roundtrip
    //   term = NQuote(POutput2Plus(NParen(NQuoteNil), PNew([a0,a1], PZero), []))
    //
    // `POutput2Plus`'s surface is `"@" n "!" "(" a "," bs.*sep(",") ")"`. The
    // hazardous slot is `a` — a PLAIN child whose right fence is the LITERAL
    // `","`, NOT an element of the `bs` repetition the 2026-07-24 pass guarded.
    // So Display emitted, and could not re-read,
    //
    //     @@Nil!(new a0 , a1 in{Nil},)   ⟶  parse error at the leading `@`
    //
    // Grouping `a` restores the boundary.
    let term = Name::NQuote(std::sync::Arc::new(Proc::POutput2Plus(
        std::sync::Arc::new(Name::NParen(std::sync::Arc::new(Name::NQuoteNil))),
        std::sync::Arc::new(two_binder_new(Proc::PZero)),
        vec![],
    )));
    let canonical = assert_display_parse_fixed_point!(Name, &term, "POutput2Plus first operand");
    assert!(
        canonical.contains("(new a0 , a1 in{Nil})"),
        "the `new` must be parenthesized inside the comma-fenced slot; got {canonical:?}",
    );
}

#[test]
fn every_2plus_send_family_groups_a_comma_carrying_first_operand() {
    // The `a "," bs.*sep(",")` shape is shared by every `2Plus` send family
    // (plain / persistent × channel-first / `@`-led / `@Nil` / quoted). One
    // fence rule covers them all; a per-rule patch would have missed five.
    for src in [
        "@Nil!((new a0 , a1 in{Nil}), Nil)",
        "@Nil!!((new a0 , a1 in{Nil}), Nil)",
        "@(Nil)!((new a0 , a1 in{Nil}), Nil)",
        "x!((new a0 , a1 in{Nil}), Nil)",
        "x!!((new a0 , a1 in{Nil}), Nil)",
    ] {
        let canonical = assert_display_parse_fixed_point!(Proc, &parse(src), src);
        assert!(
            canonical.contains("(new a0 , a1 in{Nil})"),
            "`{src}` must keep its `new` grouped; got {canonical:?}",
        );
    }
}

#[test]
fn the_fence_rule_is_not_send_specific() {
    // The invariant is stated over the TEMPLATE, not over sends: any rule with
    // a `<slot> "," <slot>` shape inherits it. `int(a, w)` and `fraction(a, b)`
    // are the non-send witnesses.
    for src in ["int((new a0 , a1 in{Nil}), 32)", "fraction((new a0 , a1 in{Nil}), 1)"] {
        let canonical = assert_display_parse_fixed_point!(Proc, &parse(src), src);
        assert!(
            canonical.contains("(new a0 , a1 in{Nil})"),
            "`{src}` must keep its `new` grouped; got {canonical:?}",
        );
    }
}

#[test]
fn a_new_in_a_sep_joined_element_is_grouped() {
    // The 2026-07-24 half, kept as a pin: an ELEMENT of a `.*sep(",")` list.
    for src in ["@Nil!(0 , (new a0 , a1 in{Nil}))", "@Nil!(0 , (new a0 , a1 in{Nil}) , 1)"] {
        let canonical = assert_display_parse_fixed_point!(Proc, &parse(src), src);
        assert!(
            canonical.contains("(new a0 , a1 in{Nil})"),
            "`{src}` must keep its `new` grouped; got {canonical:?}",
        );
    }
}

#[test]
fn a_native_collection_literal_recovers_without_grouping() {
    // CONTRAST, and the reason the invariant is stated over RULE TEMPLATES
    // rather than "every comma-joined thing". A native collection LITERAL
    // (`[…]`, `#{…}#`, `Set(…)`) is not a rule template with a fence — its
    // elements are read by the ordinary GLL collection loop, which FORKS at
    // every comma and keeps only the realizable tilings. The three-element
    // reading of `[new a0 , a1 in{Nil}, Nil]` dies (`new a0` alone is not a
    // `Proc`), so the two-element reading survives and the roundtrip is stable
    // WITHOUT parentheses. Only the hand-rolled sigil-led send tiler cannot
    // re-merge, which is why the send families need the guard and this does not.
    //
    // Pinned so that a future change which DOES start grouping here is a
    // deliberate decision, and so the "no spurious parentheses" property of the
    // fence rule stays visible.
    let canonical =
        assert_display_parse_fixed_point!(Proc, &parse("[(new a0 , a1 in{Nil}), Nil]"), "list");
    assert_eq!(canonical, "[new a0 , a1 in{Nil}, Nil]");
    match &parse(&canonical) {
        Proc::CastList(l) => match &**l {
            mettail_languages::rhocalc::List::ListLit(items) => assert_eq!(
                items.len(),
                2,
                "the depth-0 comma inside the `new` must NOT split the list: {canonical:?}",
            ),
            other => panic!("expected a list literal, got {other:?}"),
        },
        other => panic!("expected Proc::CastList, got {other:?}"),
    }
}

#[test]
fn grouping_is_emitted_only_when_a_fence_is_actually_captured() {
    // The invariant must not degenerate into "always parenthesize": a
    // SINGLE-binder `new` carries no depth-0 comma, so it stays bare. This is
    // what makes the fix a no-op for every pre-2026-07-24 display, and what
    // keeps the canonical form parenthesis-minimal.
    for src in [
        "@Nil!(new a0 in{Nil}, Nil)",
        "@Nil!(0 , new a0 in{Nil})",
        "int(new a0 in{Nil}, 32)",
    ] {
        let canonical = assert_display_parse_fixed_point!(Proc, &parse(src), src);
        assert!(
            canonical.contains("new a0 in{Nil}") && !canonical.contains("(new a0 in{Nil})"),
            "a one-binder `new` needs no grouping; got {canonical:?}",
        );
    }
}

#[test]
fn grouping_preserves_the_term() {
    // `( P )` is PraTTaIL's TRANSPARENT grouping — it must yield the SAME term
    // as the bare form, otherwise the fix would trade a parse failure for a
    // semantic one. Checked against the ungrouped ONE-binder control, which is
    // the only version of this comparison that can be made: the two-binder form
    // does not parse bare, which is the whole point.
    //
    // Compared through `Display`, not `Debug`: each parse allocates FRESH
    // `UniqueId`s for its binders, so the debug forms differ in binder identity
    // even for terms that are alpha-equal and print identically.
    mettail_runtime::clear_var_cache();
    let bare = format!("{}", parse("@Nil!(new a0 in{Nil}, Nil)"));
    mettail_runtime::clear_var_cache();
    let grouped = format!("{}", parse("@Nil!((new a0 in{Nil}), Nil)"));
    assert_eq!(bare, grouped, "transparent grouping must not change the term");

    // The same for a `.*sep` element, where the bare form also parses.
    mettail_runtime::clear_var_cache();
    let bare_elem = format!("{}", parse("@Nil!(0 , new a0 in{Nil})"));
    mettail_runtime::clear_var_cache();
    let grouped_elem = format!("{}", parse("@Nil!(0 , (new a0 in{Nil}))"));
    assert_eq!(bare_elem, grouped_elem, "transparent grouping must not change the term");
}
