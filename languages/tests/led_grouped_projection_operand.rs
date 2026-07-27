//! A parenthesised operand keeps its own scope: the cross-category projection
//! boundary walk must not read a floor from OUTSIDE a re-scoping frame.
//!
//! ## Why this file exists
//!
//! `(` … `)` is LedTest's pure grouping form — it carries no rule of its own —
//! so for every `E` in a category `C`, `C::parse(E)` and `C::parse("(" E ")")`
//! must agree, and a grouped operand must be readable wherever the bare one is.
//! Six shapes violated that:
//!
//! ```text
//!     Pred::parse("1 == (2 == 3)")          Ok    EqNum(1, PredToNum(EqNum(2, 3)))
//!     Pred::parse("1 == (true and true)")   Err   "no realizable readings"
//! ```
//!
//! Both groups sit at the same slot — `EqNum`'s `Num` right operand — and both
//! reach it by the same transparent projection `PredToNum . Pred : Num`. They
//! differ only in what the group's content is rooted at: a CROSS-category
//! operator (`EqNum : Num "==" Num : Pred`) versus an operator of the group's
//! OWN category (`AndPred : Pred "and" Pred : Pred`).
//!
//! ## The mechanism
//!
//! `cgll_pure_crosscat_boundaries` walks the caller chain from an operand frame
//! looking for an enclosing projection whose floor should take the pending
//! operator instead. Its stop set encodes the criterion that a frame which
//! RE-SCOPES its content behind a self-delimiting close cannot hand its interior
//! operators to anything outside it — `GroupingMarker` is in that set, and the
//! walk's verified model (`formal/rocq/prattail_wpda_runtime/theories/
//! CollectionElementProjectionBoundary.v`) proves `grouping_stops_walk`.
//!
//! A hop carrying EXPLICIT cross-category wrap evidence (`xcat == 4`) is exempt
//! from that stop, so that its OWN boundary mapping still runs — that exemption
//! is `5ec9f20f`, and Calculator's `(0 + bigrat(a))` needs it. But the exemption
//! was granted to the whole CHAIN rather than to the one hop: after failing to
//! produce a boundary the walk ASCENDED past the grouping and found the
//! enclosing `EqNum` frame's floor. `and` binds looser than that floor, so the
//! guard suppressed the `IterativeChainAbsorb` that builds `AndPred`, and the
//! reading was destroyed before the forest ever saw it.
//!
//! `5ec9f20f`'s own message states the intended scope verbatim: the pre-fix walk
//! was "discarding the hop's own evidence rather than merely refusing to ascend
//! past it".
//!
//! ## What these tests pin
//!
//! 1. Grouping is inert at a cross-category operand slot, for interiors rooted
//!    at BOTH an own-category and a cross-category operator.
//! 2. The projection is applied, i.e. the grouped `Pred` really does arrive as
//!    `PredToNum(...)` rather than the parse merely "succeeding".
//! 3. The fix is NOT an over-fix: with the parentheses removed, `and` binds
//!    looser than `==` and the outer-`and` reading must still win. A change that
//!    also "fixed" these would have broken precedence.

#[path = "definitions/led_test.rs"]
mod ledtest;

use ledtest::{Expr, Num, Pred};

/// `{:?}` of the parsed term, or `Err(..)`.
fn pred(src: &str) -> String {
    mettail_runtime::clear_var_cache();
    match Pred::parse(src) {
        Ok(t) => format!("{:?}", t),
        Err(e) => format!("Err({})", e),
    }
}

fn num(src: &str) -> String {
    mettail_runtime::clear_var_cache();
    match Num::parse(src) {
        Ok(t) => format!("{:?}", t),
        Err(e) => format!("Err({})", e),
    }
}

fn expr(src: &str) -> String {
    mettail_runtime::clear_var_cache();
    match Expr::parse(src) {
        Ok(t) => format!("{:?}", t),
        Err(e) => format!("Err({})", e),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// 1. The defect family — a group whose content is rooted at an operator of the
//    group's OWN category, sitting at a cross-category operand slot.
// ════════════════════════════════════════════════════════════════════════════

/// THE witness. `AndPred` is a `Pred → Pred` operator; the group sits at
/// `EqNum`'s `Num` operand and reaches it through `PredToNum`.
#[test]
fn grouped_own_category_operand_at_a_crosscat_slot() {
    assert_eq!(
        pred("1 == (true and true)"),
        "EqNum(NumLit(1), PredToNum(AndPred(BoolLit(true), BoolLit(true))))",
    );
}

/// The same group one operator deeper — the enclosing projection floor the walk
/// used to find is `MulNum`'s, not `EqNum`'s, and the shape still must not see it.
#[test]
fn grouped_own_category_operand_under_a_tighter_operator() {
    assert_eq!(
        pred("1 == 2 * (true and true)"),
        "EqNum(NumLit(1), MulNum(NumLit(2), \
         PredToNum(AndPred(BoolLit(true), BoolLit(true)))))",
    );
}

/// A group rooted at the own-category operator whose OWN left operand is a
/// cross-category one — the two mechanisms stacked.
#[test]
fn grouped_own_category_operand_with_a_crosscat_child() {
    assert_eq!(
        pred("1 == (1 == 1 and true)"),
        "EqNum(NumLit(1), PredToNum(AndPred(EqNum(NumLit(1), NumLit(1)), BoolLit(true))))",
    );
}

/// The sibling cross-category operator (`!=`) reaches the same slot the same way.
#[test]
fn grouped_own_category_operand_at_the_sibling_operator() {
    assert_eq!(
        pred("1 != (true and true)"),
        "NeNum(NumLit(1), PredToNum(AndPred(BoolLit(true), BoolLit(true))))",
    );
}

/// Both operands grouped: the LHS slot already worked (it is reached by the
/// cross-cat-LHS push, not by a delegate), the RHS slot is the defect.
#[test]
fn both_operands_grouped() {
    assert_eq!(
        pred("(true and true) == (true and true)"),
        "EqNum(PredToNum(AndPred(BoolLit(true), BoolLit(true))), \
         PredToNum(AndPred(BoolLit(true), BoolLit(true))))",
    );
}

/// The same shape at the `Expr` goal, which reaches `Pred` through `CastPred`.
#[test]
fn grouped_own_category_operand_at_the_sum_type_goal() {
    assert_eq!(
        expr("1 == (true and true)"),
        "CastPred(EqNum(NumLit(1), PredToNum(AndPred(BoolLit(true), BoolLit(true)))))",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// 2. Grouping is inert — the shapes that already worked must be unchanged, and
//    each must agree with its redundantly-parenthesised twin.
// ════════════════════════════════════════════════════════════════════════════

/// A redundant second pair of parentheses must not change the reading. Before
/// the fix this pair DISAGREED: the inner group supplied the `CategoryEntry`
/// pop the outer one could not, so `((…))` parsed while `(…)` did not.
#[test]
fn a_redundant_paren_pair_does_not_change_the_reading() {
    for (bare, wrapped) in [
        ("1 == (true and true)", "1 == ((true and true))"),
        ("1 == (2 == 3)", "1 == ((2 == 3))"),
    ] {
        assert_eq!(pred(bare), pred(wrapped), "grouping is not inert for {bare:?}");
    }
    for (bare, wrapped) in [
        ("1 * (true and true)", "1 * ((true and true))"),
        ("(true and true)", "((true and true))"),
    ] {
        assert_eq!(num(bare), num(wrapped), "grouping is not inert for {bare:?}");
    }
}

/// The cross-category-rooted interior — the control that always worked. It must
/// keep its exact reading.
#[test]
fn grouped_crosscat_rooted_interior_is_unchanged() {
    assert_eq!(
        pred("1 == (2 == 3)"),
        "EqNum(NumLit(1), PredToNum(EqNum(NumLit(2), NumLit(3))))",
    );
    assert_eq!(pred("1 == (2 + 3)"), "EqNum(NumLit(1), AddNum(NumLit(2), NumLit(3)))",);
    assert_eq!(
        pred("1 == (2 + 3) * 4"),
        "EqNum(NumLit(1), MulNum(AddNum(NumLit(2), NumLit(3)), NumLit(4)))",
    );
}

/// The same interior at a goal with no enclosing projection floor to find. This
/// always worked and is the control the defect was measured against.
#[test]
fn the_same_interior_at_a_num_goal_is_unchanged() {
    assert_eq!(
        num("1 * (true and true)"),
        "MulNum(NumLit(1), PredToNum(AndPred(BoolLit(true), BoolLit(true))))",
    );
    assert_eq!(num("(true and true)"), "PredToNum(AndPred(BoolLit(true), BoolLit(true)))",);
}

/// Non-`(` delimiters reach the grouped operand by other routes and must be
/// unchanged: a prefix operator, and a mixfix projection with its own parens.
#[test]
fn other_delimiters_around_the_same_interior_are_unchanged() {
    assert_eq!(
        pred("1 == -(true and true)"),
        "EqNum(NumLit(1), NegNum(PredToNum(AndPred(BoolLit(true), BoolLit(true)))))",
    );
    assert_eq!(
        pred("1 == to_num(true and true)"),
        "EqNum(NumLit(1), ExprToNum(CastPred(AndPred(BoolLit(true), BoolLit(true)))))",
    );
}

// ════════════════════════════════════════════════════════════════════════════
// 3. NOT an over-fix — without the parentheses the outer operator still wins.
// ════════════════════════════════════════════════════════════════════════════

/// `AndPred` is declared AFTER `EqNum` in `Pred`, so by the
/// BP-by-declaration-order convention `and` binds LOOSER than `==`: with no
/// parentheses the `and` belongs to the OUTER `Pred`, not to the `==` operand.
/// This is exactly the handoff the boundary walk exists to perform, and it must
/// still fire when nothing re-scopes the operand.
#[test]
fn without_parens_the_looser_operator_still_takes_the_operand() {
    assert_eq!(pred("1 == 2 and true"), "AndPred(EqNum(NumLit(1), NumLit(2)), BoolLit(true))",);
    assert_eq!(pred("true and 1 == 2"), "AndPred(BoolLit(true), EqNum(NumLit(1), NumLit(2)))",);
    assert_eq!(
        pred("true and (true and true)"),
        "AndPred(BoolLit(true), AndPred(BoolLit(true), BoolLit(true)))",
    );
}

/// Ordinary precedence and cross-category chaining, unchanged.
#[test]
fn ordinary_precedence_is_unchanged() {
    assert_eq!(pred("1 == 2 == 3"), "EqNum(PredToNum(EqNum(NumLit(1), NumLit(2))), NumLit(3))",);
    assert_eq!(
        pred("1 == 2 + 3 * 4"),
        "EqNum(NumLit(1), AddNum(NumLit(2), MulNum(NumLit(3), NumLit(4))))",
    );
    assert_eq!(num("1 * (2 + 3)"), "MulNum(NumLit(1), AddNum(NumLit(2), NumLit(3)))",);
}
