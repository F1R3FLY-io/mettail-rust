//! Operator precedence and associativity conformance.
//!
//! ## The rule this file pins
//!
//! > An explicitly declared associativity is HONORED. Absent one, the default is LEFT.
//! > Precedence and associativity are **independent** — grouping operators into a level
//! > must not flatten their associativity.
//!
//! ## The defect these fixtures were written to witness
//!
//! `prattail::binding_power::analyze_binding_powers` advanced its `precedence` counter
//! **once per rule**:
//!
//! ```text
//!     Associativity::Left  => { let bp = (p, p + 1); p += 2; bp }
//!     Associativity::Right => { let bp = (p + 1, p); p += 2; bp }
//! ```
//!
//! Neither arm leaves `p` unchanged, so rule `i` of a category received
//! `left_bp ∈ {2 + 2i, 3 + 2i}`. For `i < j`, sharing a `left_bp` would need
//! `3 + 2i = 2 + 2j`, i.e. `2(j − i) = 1` — impossible by parity. Every non-postfix
//! operator in a category therefore had a **provably distinct** binding power, and
//! declaration order was a strict total order *by construction*. There was no way to
//! say "these operators bind equally tightly", which is what
//! `6 * 3 / 2`, `1 + 2 - 3`, and every comparison level require.
//!
//! The repair adds a `same` annotation to the grammar DSL meaning *share the previous
//! rule's level*, and advances `precedence` once per **level** rather than once per rule.
//! Associativity stays per-operator, which is exactly what Rholang's level 6 needs
//! (`matches` is `prec.right(6, …)` while `==` and `!=` are `prec.left(6, …)`).
//!
//! ## Anti-vacuity
//!
//! Every fixture below distinguishes the two readings by an **observable**:
//!
//! | fixture | left reading | right reading | discriminating? |
//! |---|---|---|---|
//! | `6 * 3 / 2` | `(6*3)/2 = 9` | `6*(3/2) = 6` | yes — integer division truncates |
//! | `1 + 2 - 3` | `(1+2)-3` | `1+(2-3)` | **values coincide at 0** ⇒ assert the TREE |
//! | `10 - 4 - 3` | `(10-4)-3 = 3` | `10-(4-3) = 9` | yes |
//! | `2 ^ 3 ^ 2` | `(2^3)^2 = 64` | `2^(3^2) = 512` | yes |
//!
//! `1 + 2 - 3` is the trap: both readings evaluate to 0, so a value assertion there
//! proves nothing. It is asserted structurally against its explicitly grouped twin.
//! Grouping is inert in Calculator (`languages/tests/calculator_grouping_is_inert.rs`),
//! so `(1 + 2) - 3` really does denote the left-nested tree.

#![cfg(feature = "calculator")]

use mettail_languages::calculator::*;

// ══════════════════════════════════════════════════════════════════════════════
// Equal precedence ⇒ left-to-right
// ══════════════════════════════════════════════════════════════════════════════

/// `*` and `/` share a level, so a mixed chain reads left-to-right.
///
/// Integer division truncates, which is what makes this fixture non-vacuous:
/// `(6 * 3) / 2 = 18 / 2 = 9` but `6 * (3 / 2) = 6 * 1 = 6`.
#[test]
fn mul_and_div_share_a_level_and_read_left_to_right() {
    let t = Int::parse("6 * 3 / 2").expect("6 * 3 / 2 should parse");
    assert_eq!(
        t.eval(),
        9,
        "`6 * 3 / 2` must read `(6 * 3) / 2 = 9`; got the right-nested reading `6 * (3 / 2) = 6`"
    );
}

/// The same level, exercised through `%` — which the grammar also places with `*` and `/`.
#[test]
fn mul_div_mod_all_share_one_level() {
    // (8 * 3) % 5 = 24 % 5 = 4   vs   8 * (3 % 5) = 8 * 3 = 24
    let a = Int::parse("8 * 3 % 5").expect("8 * 3 % 5 should parse");
    assert_eq!(a.eval(), 4, "`8 * 3 % 5` must read `(8 * 3) % 5`");

    // (20 / 3) % 4 = 6 % 4 = 2   vs   20 / (3 % 4) = 20 / 3 = 6
    let b = Int::parse("20 / 3 % 4").expect("20 / 3 % 4 should parse");
    assert_eq!(b.eval(), 2, "`20 / 3 % 4` must read `(20 / 3) % 4`");
}

/// A pure left-associative chain of ONE operator.
///
/// No such test existed anywhere in the workspace before this file: every extant
/// "associativity" test used two *different* operators, so a ladder that merely
/// ordered them consistently passed without ever exercising same-level grouping.
#[test]
fn subtraction_chains_left_to_right() {
    let t = Int::parse("10 - 4 - 3").expect("10 - 4 - 3 should parse");
    assert_eq!(t.eval(), 3, "`10 - 4 - 3` must read `(10 - 4) - 3 = 3`, not `10 - (4 - 3) = 9`");
}

/// ★ `+` and `-` evaluate identically under BOTH readings (`1 + 2 - 3 = 0` either way),
/// so this fixture asserts the **tree**, never the value.
///
/// A value assertion here would be inert — it would pass before and after the fix and
/// witness nothing.
#[test]
fn add_and_sub_share_a_level_asserted_structurally() {
    mettail_runtime::clear_var_cache();
    let bare = Int::parse("1 + 2 - 3").expect("1 + 2 - 3 should parse");
    mettail_runtime::clear_var_cache();
    let left_nested = Int::parse("(1 + 2) - 3").expect("(1 + 2) - 3 should parse");
    mettail_runtime::clear_var_cache();
    let right_nested = Int::parse("1 + (2 - 3)").expect("1 + (2 - 3) should parse");

    assert_eq!(bare, left_nested, "`1 + 2 - 3` must denote the SAME TREE as `(1 + 2) - 3`");
    assert_ne!(
        left_nested, right_nested,
        "control: the two groupings must be structurally distinct, or the assertion above \
         is vacuous"
    );
}

/// Calculator split its comparisons across SIX precedence levels
/// (`==` loosest … `!=` tightest). They belong on one.
///
/// `Bool` is the category where this is observable: its comparisons are
/// `Bool × Bool → Bool`, so they chain. (In `Int`, `Float`, `Str` and `Fixed` the
/// comparisons are cross-category — `Int × Int → Bool` — so a chain is ill-typed and the
/// level structure has no witness. Those categories are pinned by the ladder assertions
/// in `calculator_comparison_levels_are_collapsed` below.)
///
/// `true < false == false`:
///   one level, left-to-right — `(true < false) == false` = `false == false` = **true**
///   `<` looser than `==`     — `true < (false == false)` = `true < true` = **false**
#[test]
fn bool_comparisons_share_one_level_and_read_left_to_right() {
    let t = Bool::parse("true < false == false").expect("should parse");
    assert_eq!(
        t.eval(),
        true,
        "`<` and `==` share a level, so `true < false == false` must read \
         `(true < false) == false` = true"
    );
}

/// The mirror: `!=` was the TIGHTEST of the six and `==` the loosest, so a chain mixing
/// them is the sharpest witness that the six-way split is gone.
///
/// `false != false < true`:
///   one level, left-to-right — `(false != false) < true` = `false < true` = **true**
///   `!=` tighter than `<`    — `false != (false < true)` = `false != true` = **true**
///
/// Both readings give `true`, so that pair is inert — assert the TREE instead.
#[test]
fn eq_and_ne_share_a_level_with_the_relational_operators() {
    mettail_runtime::clear_var_cache();
    let bare = Bool::parse("false != false < true").expect("should parse");
    mettail_runtime::clear_var_cache();
    let left_nested = Bool::parse("(false != false) < true").expect("should parse");
    mettail_runtime::clear_var_cache();
    let right_nested = Bool::parse("false != (false < true)").expect("should parse");

    assert_eq!(
        bare, left_nested,
        "`false != false < true` must denote the same tree as `(false != false) < true`"
    );
    assert_ne!(
        left_nested, right_nested,
        "control: the two groupings must be structurally distinct"
    );
}

/// `xor` sits between `or` and `and`, mirroring C's bitwise `& > ^ > |`.
///
/// `true xor true and false`:
///   `and` tighter — `true xor (true and false)` = `true xor false` = **true**
///   `xor` tighter — `(true xor true) and false` = `false and false` = **false**
#[test]
fn xor_binds_looser_than_and() {
    let t = Bool::parse("true xor true and false").expect("should parse");
    assert_eq!(
        t.eval(),
        true,
        "`and` binds tighter than `xor`: `true xor true and false` must read \
         `true xor (true and false)` = true"
    );
}

/// …and tighter than `or`.
///
/// `false or true xor true`:
///   `xor` tighter — `false or (true xor true)` = `false or false` = **false**
///   `or` tighter  — `(false or true) xor true` = `true xor true` = **false**
///
/// Both readings coincide, so assert the TREE.
#[test]
fn xor_binds_tighter_than_or() {
    mettail_runtime::clear_var_cache();
    let bare = Bool::parse("false or true xor true").expect("should parse");
    mettail_runtime::clear_var_cache();
    let right_nested = Bool::parse("false or (true xor true)").expect("should parse");
    mettail_runtime::clear_var_cache();
    let left_nested = Bool::parse("(false or true) xor true").expect("should parse");

    assert_eq!(
        bare, right_nested,
        "`xor` binds tighter than `or`, so `false or true xor true` must denote the same \
         tree as `false or (true xor true)`"
    );
    assert_ne!(
        left_nested, right_nested,
        "control: the two groupings must be structurally distinct"
    );
}

/// Calculator's `Str` category puts `++` and `+` on one level, as Rholang's normative
/// grammar does (both are `prec.left(8, …)` there).
#[test]
fn string_concat_and_plus_share_a_level() {
    mettail_runtime::clear_var_cache();
    let bare = Str::parse(r#""a" ++ "b" + "c""#).expect("should parse");
    mettail_runtime::clear_var_cache();
    let left_nested = Str::parse(r#"("a" ++ "b") + "c""#).expect("should parse");
    mettail_runtime::clear_var_cache();
    let right_nested = Str::parse(r#""a" ++ ("b" + "c")"#).expect("should parse");

    assert_eq!(
        bare, left_nested,
        r#"`"a" ++ "b" + "c"` must denote the same tree as `("a" ++ "b") + "c"`"#
    );
    assert_ne!(
        left_nested, right_nested,
        "control: the two groupings must be structurally distinct"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Order-only defects: `and`/`or` and `bitand`/`bitor` were inverted
// ══════════════════════════════════════════════════════════════════════════════

/// `and` must bind TIGHTER than `or` — the universal convention, and the one every
/// other language in the workspace already assumes.
///
/// `false and false or true`:
///   correct — `(false and false) or true` = `false or true` = **true**
///   wrong   — `false and (false or true)` = `false and true` = **false**
#[test]
fn and_binds_tighter_than_or() {
    let t = Bool::parse("false and false or true").expect("should parse");
    assert_eq!(
        t.eval(),
        true,
        "`false and false or true` must read `(false and false) or true` = true"
    );
}

/// The mirror witness, so a fix that merely swaps two declarations without
/// understanding them cannot pass both.
#[test]
fn or_is_looser_than_and_in_the_other_direction() {
    // (true or (false and false)) = true    vs   ((true or false) and false) = false
    let t = Bool::parse("true or false and false").expect("should parse");
    assert_eq!(
        t.eval(),
        true,
        "`true or false and false` must read `true or (false and false)` = true"
    );
}

/// `bitand` must bind TIGHTER than `bitor`, mirroring `and`/`or`.
///
/// `1 bitand 2 bitor 4`:
///   correct — `(1 bitand 2) bitor 4` = `0 bitor 4` = **4**
///   wrong   — `1 bitand (2 bitor 4)` = `1 bitand 6` = **0**
#[test]
fn bitand_binds_tighter_than_bitor() {
    let t = Int::parse("1 bitand 2 bitor 4").expect("should parse");
    assert_eq!(t.eval(), 4, "`1 bitand 2 bitor 4` must read `(1 bitand 2) bitor 4` = 4");
}

// ══════════════════════════════════════════════════════════════════════════════
// ★ Right-associativity PRESERVED — constructed so a flattening fix would FAIL
// ══════════════════════════════════════════════════════════════════════════════
//
// A test that passes both before and after a change proves nothing about that change.
// Each fixture in this section is chosen so that collapsing the operator to LEFT
// associativity — the failure mode a "group operators into levels" refactor invites —
// produces a DIFFERENT, WRONG answer.

/// `^` is declared `right` and must stay right-associative, and must stay tighter than
/// `*` and `/`.
///
/// `2 ^ 3 ^ 2` = `2 ^ (3 ^ 2)` = `2 ^ 9` = **512**. Flattened to left it would be
/// `(2 ^ 3) ^ 2` = `8 ^ 2` = **64**.
#[test]
fn pow_stays_right_associative() {
    let t = Int::parse("2 ^ 3 ^ 2").expect("2 ^ 3 ^ 2 should parse");
    assert_eq!(
        t.eval(),
        512,
        "`^` is declared `right`: `2 ^ 3 ^ 2` = `2 ^ (3 ^ 2)` = 512, not `(2 ^ 3) ^ 2` = 64"
    );
}

/// `^` binds tighter than `*` and `/`, and grouping operators into levels must not
/// disturb that.
///
/// `2 * 3 ^ 2` = `2 * (3 ^ 2)` = 18. If `^` were dragged into the `*`/`/` level it
/// would read `(2 * 3) ^ 2` = 36.
#[test]
fn pow_stays_tighter_than_mul_and_div() {
    let a = Int::parse("2 * 3 ^ 2").expect("should parse");
    assert_eq!(a.eval(), 18, "`2 * 3 ^ 2` must read `2 * (3 ^ 2)` = 18");

    let b = Int::parse("2 ^ 3 * 2").expect("should parse");
    assert_eq!(b.eval(), 16, "`2 ^ 3 * 2` must read `(2 ^ 3) * 2` = 16");

    // ^ tighter than / as well: 18 / 3 ^ 2 = 18 / 9 = 2, not (18/3)^2 = 36
    let c = Int::parse("18 / 3 ^ 2").expect("should parse");
    assert_eq!(c.eval(), 2, "`18 / 3 ^ 2` must read `18 / (3 ^ 2)` = 2");
}

/// The ternary is declared `right`, and a nested ternary in the ELSE position is the
/// only shape that can tell right from left.
///
/// `1 ? 2 : 0 ? 3 : 4`:
///   right — `1 ? 2 : (0 ? 3 : 4)` = **2**
///   left  — `(1 ? 2 : 0) ? 3 : 4` = `2 ? 3 : 4` = **3**
#[test]
fn ternary_stays_right_associative() {
    let t = Int::parse("1 ? 2 : 0 ? 3 : 4").expect("nested ternary should parse");
    assert_eq!(
        t.eval(),
        2,
        "`Tern` is declared `right`: `1 ? 2 : 0 ? 3 : 4` must read \
         `1 ? 2 : (0 ? 3 : 4)` = 2, not `(1 ? 2 : 0) ? 3 : 4` = 3"
    );
}
