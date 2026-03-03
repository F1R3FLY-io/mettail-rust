#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

/// Minimal test language designed to exercise LED delegation code paths.
///
/// The operators (+, *, !, ==, !=, "and") live on the constituent categories
/// (Num, Pred), NOT on the sum type Expr. Expr only owns the "|" operator.
/// This forces the parser to use LED delegation when parsing expressions
/// like "1 + 2" at the Expr level.
///
/// Types:
/// - Num: "Int-like" constituent with infix (+, *), unary prefix (-), postfix (!), cross-cat (==, !=)
/// - Pred: "Bool-like" result category for cross-category operators and its own infix ("and")
/// - Expr: Sum type with cast rules from Num and Pred, owns only the "|" operator
language! {
    name: LedTest,

    types {
        ![i32] as Num
        ![bool] as Pred
        Expr
    },

    terms {
        // ── Num (constituent) operators ──
        AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] step;
        MulNum . a:Num, b:Num |- a "*" b : Num ![a * b] step;
        NegNum . a:Num |- "-" a : Num ![(-a)] step;
        FactNum . a:Num |- a "!" : Num ![{ (1..=a.max(0)).product::<i32>() }] step;

        // ── Cross-category: Num × Num → Pred ──
        EqNum . a:Num, b:Num |- a "==" b : Pred ![a == b] step;
        NeNum . a:Num, b:Num |- a "!=" b : Pred ![a != b] step;

        // ── Pred (result) operators ──
        AndPred . a:Pred, b:Pred |- a "and" b : Pred ![a && b] step;

        // ── Cast rules: constituent → Expr ──
        CastNum . a:Num |- a : Expr;
        CastPred . r:Pred |- r : Expr;

        // ── Projection rule: Expr → Num ──
        ExprToNum . s:Expr |- "to_num" "(" s ")" : Num;

        // ── Expr own operator ──
        EPar . a:Expr, b:Expr |- a "|" b : Expr;
    },

    equations {},

    rewrites {
        // Num operators
        AddNumCongL . | U ~> V |- (AddNum U W) ~> (AddNum V W);
        AddNumCongR . | U ~> V |- (AddNum W U) ~> (AddNum W V);
        MulNumCongL . | U ~> V |- (MulNum U W) ~> (MulNum V W);
        MulNumCongR . | U ~> V |- (MulNum W U) ~> (MulNum W V);
        NegNumCong . | U ~> V |- (NegNum U) ~> (NegNum V);
        FactNumCong . | U ~> V |- (FactNum U) ~> (FactNum V);

        // Cross-category
        EqNumCongL . | U ~> V |- (EqNum U W) ~> (EqNum V W);
        EqNumCongR . | U ~> V |- (EqNum W U) ~> (EqNum W V);
        NeNumCongL . | U ~> V |- (NeNum U W) ~> (NeNum V W);
        NeNumCongR . | U ~> V |- (NeNum W U) ~> (NeNum W V);

        // Pred operators
        AndPredCongL . | U ~> V |- (AndPred U W) ~> (AndPred V W);
        AndPredCongR . | U ~> V |- (AndPred W U) ~> (AndPred W V);

        // Cast rules (propagate inner reduction through cast wrappers)
        CastNumCong . | U ~> V |- (CastNum U) ~> (CastNum V);
        CastPredCong . | U ~> V |- (CastPred U) ~> (CastPred V);

        // Projection
        ExprToNumCong . | U ~> V |- (ExprToNum U) ~> (ExprToNum V);

        // Expr own operator
        EParCongL . | U ~> V |- (EPar U W) ~> (EPar V W);
        EParCongR . | U ~> V |- (EPar W U) ~> (EPar W V);
    },
}
