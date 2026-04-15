//! Free semiring: symbolic semiring expressions as an AST.
//!
//! The free semiring over a set of generators X is the initial object in the
//! category of semirings: it satisfies the semiring laws and no others. Each
//! element is a syntactic expression tree built from generators, `+`, `*`, `0`, and `1`.
//!
//! This semiring implements [`SemiringRef`](mettail_prattail::automata::semiring::SemiringRef)
//! rather than `Semiring` because `FreeExpr` is heap-allocated and not `Copy`.
//!
//! ## Applications
//!
//! - **Symbolic computation**: defer numeric evaluation, inspect expression structure
//! - **Provenance tracking**: each generator represents a data source, the expression
//!   records which sources contributed to a result
//! - **Optimization passes**: algebraic simplification, common subexpression elimination
//! - **Debugging**: print the full semiring expression for a path weight

use std::fmt;

use mettail_prattail::automata::semiring::SemiringRef;

/// A symbolic semiring expression.
///
/// Represents an unevaluated expression in the free semiring. The expression
/// tree preserves the algebraic structure of how a weight was computed,
/// enabling introspection, symbolic simplification, and deferred evaluation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FreeExpr {
    /// Additive identity (semiring zero).
    Zero,
    /// Multiplicative identity (semiring one).
    One,
    /// A named generator (atomic weight).
    Gen(String),
    /// Semiring addition: `a ⊕ b`.
    Plus(Box<FreeExpr>, Box<FreeExpr>),
    /// Semiring multiplication: `a ⊗ b`.
    Times(Box<FreeExpr>, Box<FreeExpr>),
}

impl FreeExpr {
    /// Create a generator expression from a name.
    #[inline]
    pub fn gen(name: impl Into<String>) -> Self {
        FreeExpr::Gen(name.into())
    }

    /// Simplify the expression using basic algebraic identities.
    ///
    /// Applies the following rewrites (iteratively via trampoline):
    /// - `0 + a → a`, `a + 0 → a`
    /// - `1 * a → a`, `a * 1 → a`
    /// - `0 * a → 0`, `a * 0 → 0`
    ///
    /// Does NOT apply commutativity, associativity, or distributivity
    /// (those would change the free semiring into a quotient).
    pub fn simplify(&self) -> Self {
        // Trampoline-based iterative simplification to avoid stack overflow
        // on deeply nested expressions.
        enum Frame {
            SimplifyPlus(Box<FreeExpr>),
            SimplifyTimes(Box<FreeExpr>),
            AssemblePlus(FreeExpr),
            AssembleTimes(FreeExpr),
        }

        let mut stack: Vec<Frame> = Vec::with_capacity(32);
        let mut current = self.clone();
        let mut result_stack: Vec<FreeExpr> = Vec::with_capacity(32);

        // Initial decomposition
        loop {
            match current {
                FreeExpr::Zero | FreeExpr::One | FreeExpr::Gen(_) => {
                    result_stack.push(current.clone());
                    break;
                }
                FreeExpr::Plus(left, right) => {
                    stack.push(Frame::SimplifyPlus(right));
                    current = *left;
                }
                FreeExpr::Times(left, right) => {
                    stack.push(Frame::SimplifyTimes(right));
                    current = *left;
                }
            }
        }

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::SimplifyPlus(right) => {
                    let left_result = result_stack.pop()
                        .expect("result_stack should have the left operand");
                    stack.push(Frame::AssemblePlus(left_result));
                    current = *right;
                    // Process the right operand
                    loop {
                        match current {
                            FreeExpr::Zero | FreeExpr::One | FreeExpr::Gen(_) => {
                                result_stack.push(current.clone());
                                break;
                            }
                            FreeExpr::Plus(l, r) => {
                                stack.push(Frame::SimplifyPlus(r));
                                current = *l;
                            }
                            FreeExpr::Times(l, r) => {
                                stack.push(Frame::SimplifyTimes(r));
                                current = *l;
                            }
                        }
                    }
                }
                Frame::SimplifyTimes(right) => {
                    let left_result = result_stack.pop()
                        .expect("result_stack should have the left operand");
                    stack.push(Frame::AssembleTimes(left_result));
                    current = *right;
                    loop {
                        match current {
                            FreeExpr::Zero | FreeExpr::One | FreeExpr::Gen(_) => {
                                result_stack.push(current.clone());
                                break;
                            }
                            FreeExpr::Plus(l, r) => {
                                stack.push(Frame::SimplifyPlus(r));
                                current = *l;
                            }
                            FreeExpr::Times(l, r) => {
                                stack.push(Frame::SimplifyTimes(r));
                                current = *l;
                            }
                        }
                    }
                }
                Frame::AssemblePlus(left) => {
                    let right = result_stack.pop()
                        .expect("result_stack should have the right operand");
                    let simplified = match (&left, &right) {
                        (FreeExpr::Zero, _) => right,
                        (_, FreeExpr::Zero) => left,
                        _ => FreeExpr::Plus(Box::new(left), Box::new(right)),
                    };
                    result_stack.push(simplified);
                }
                Frame::AssembleTimes(left) => {
                    let right = result_stack.pop()
                        .expect("result_stack should have the right operand");
                    let simplified = match (&left, &right) {
                        (FreeExpr::Zero, _) | (_, FreeExpr::Zero) => FreeExpr::Zero,
                        (FreeExpr::One, _) => right,
                        (_, FreeExpr::One) => left,
                        _ => FreeExpr::Times(Box::new(left), Box::new(right)),
                    };
                    result_stack.push(simplified);
                }
            }
        }

        result_stack.pop().unwrap_or(FreeExpr::Zero)
    }

    /// Count the number of generator occurrences in the expression.
    pub fn generator_count(&self) -> usize {
        let mut count = 0usize;
        let mut work: Vec<&FreeExpr> = vec![self];
        while let Some(expr) = work.pop() {
            match expr {
                FreeExpr::Zero | FreeExpr::One => {}
                FreeExpr::Gen(_) => count += 1,
                FreeExpr::Plus(l, r) | FreeExpr::Times(l, r) => {
                    work.push(l);
                    work.push(r);
                }
            }
        }
        count
    }

    /// Collect all unique generator names.
    pub fn generators(&self) -> std::collections::HashSet<String> {
        let mut gens = std::collections::HashSet::new();
        let mut work: Vec<&FreeExpr> = vec![self];
        while let Some(expr) = work.pop() {
            match expr {
                FreeExpr::Zero | FreeExpr::One => {}
                FreeExpr::Gen(name) => {
                    gens.insert(name.clone());
                }
                FreeExpr::Plus(l, r) | FreeExpr::Times(l, r) => {
                    work.push(l);
                    work.push(r);
                }
            }
        }
        gens
    }

    /// Evaluate the expression given a mapping from generator names to f64 values.
    ///
    /// Uses `+` for Plus and `*` for Times (the standard real-number semiring).
    /// Internally delegates to a trampoline-based evaluator to avoid stack
    /// overflow on deeply nested expressions.
    pub fn evaluate(&self, env: &std::collections::HashMap<String, f64>) -> f64 {
        self.evaluate_trampoline(env)
    }

    /// Trampoline-based evaluation to avoid stack overflow.
    fn evaluate_trampoline(&self, env: &std::collections::HashMap<String, f64>) -> f64 {
        enum Frame<'a> {
            Eval(&'a FreeExpr),
            ApplyPlus,
            ApplyTimes,
        }

        let mut stack: Vec<Frame<'_>> = vec![Frame::Eval(self)];
        let mut values: Vec<f64> = Vec::with_capacity(32);

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Eval(expr) => match expr {
                    FreeExpr::Zero => values.push(0.0),
                    FreeExpr::One => values.push(1.0),
                    FreeExpr::Gen(name) => {
                        values.push(*env.get(name).unwrap_or(&0.0));
                    }
                    FreeExpr::Plus(l, r) => {
                        stack.push(Frame::ApplyPlus);
                        stack.push(Frame::Eval(r));
                        stack.push(Frame::Eval(l));
                    }
                    FreeExpr::Times(l, r) => {
                        stack.push(Frame::ApplyTimes);
                        stack.push(Frame::Eval(r));
                        stack.push(Frame::Eval(l));
                    }
                },
                Frame::ApplyPlus => {
                    let b = values.pop().expect("values stack underflow in ApplyPlus (right)");
                    let a = values.pop().expect("values stack underflow in ApplyPlus (left)");
                    values.push(a + b);
                }
                Frame::ApplyTimes => {
                    let b = values.pop().expect("values stack underflow in ApplyTimes (right)");
                    let a = values.pop().expect("values stack underflow in ApplyTimes (left)");
                    values.push(a * b);
                }
            }
        }

        values.pop().unwrap_or(0.0)
    }
}

/// The `FreeWeight` is a wrapper around `FreeExpr` that implements `SemiringRef`.
///
/// Since `FreeExpr` involves heap allocation (`Box`, `String`), it cannot
/// implement `Copy` and thus cannot implement the `Semiring` trait.
/// Instead, it implements `SemiringRef` which drops the `Copy` requirement.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FreeWeight {
    /// The underlying symbolic expression.
    pub expr: FreeExpr,
}

impl FreeWeight {
    /// Create a FreeWeight from an expression.
    #[inline]
    pub fn new(expr: FreeExpr) -> Self {
        FreeWeight { expr }
    }

    /// Create a generator weight.
    #[inline]
    pub fn gen(name: impl Into<String>) -> Self {
        FreeWeight { expr: FreeExpr::gen(name) }
    }

    /// Simplify the underlying expression.
    #[inline]
    pub fn simplify(&self) -> Self {
        FreeWeight { expr: self.expr.simplify() }
    }
}

impl SemiringRef for FreeWeight {
    fn zero_ref() -> Self {
        FreeWeight { expr: FreeExpr::Zero }
    }

    fn one_ref() -> Self {
        FreeWeight { expr: FreeExpr::One }
    }

    fn plus_ref(&self, other: &Self) -> Self {
        // Short-circuit identity cases to avoid expression bloat
        if self.is_zero_ref() {
            return other.clone();
        }
        if other.is_zero_ref() {
            return self.clone();
        }
        FreeWeight {
            expr: FreeExpr::Plus(Box::new(self.expr.clone()), Box::new(other.expr.clone())),
        }
    }

    fn times_ref(&self, other: &Self) -> Self {
        // Short-circuit identity and annihilation cases
        if self.is_zero_ref() || other.is_zero_ref() {
            return Self::zero_ref();
        }
        if self.is_one_ref() {
            return other.clone();
        }
        if other.is_one_ref() {
            return self.clone();
        }
        FreeWeight {
            expr: FreeExpr::Times(Box::new(self.expr.clone()), Box::new(other.expr.clone())),
        }
    }

    fn is_zero_ref(&self) -> bool {
        self.expr == FreeExpr::Zero
    }

    fn is_one_ref(&self) -> bool {
        self.expr == FreeExpr::One
    }
}

impl fmt::Display for FreeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreeExpr::Zero => write!(f, "0"),
            FreeExpr::One => write!(f, "1"),
            FreeExpr::Gen(name) => write!(f, "{}", name),
            FreeExpr::Plus(l, r) => write!(f, "({} + {})", l, r),
            FreeExpr::Times(l, r) => write!(f, "({} * {})", l, r),
        }
    }
}

impl fmt::Display for FreeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

impl Default for FreeWeight {
    fn default() -> Self {
        Self::one_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_identity() {
        let a = FreeWeight::gen("x");
        let sum = a.plus_ref(&FreeWeight::zero_ref());
        assert_eq!(sum, a, "zero is additive identity");
        let sum2 = FreeWeight::zero_ref().plus_ref(&a);
        assert_eq!(sum2, a, "zero is left additive identity");
    }

    #[test]
    fn test_one_identity() {
        let a = FreeWeight::gen("x");
        let prod = a.times_ref(&FreeWeight::one_ref());
        assert_eq!(prod, a, "one is multiplicative identity");
        let prod2 = FreeWeight::one_ref().times_ref(&a);
        assert_eq!(prod2, a, "one is left multiplicative identity");
    }

    #[test]
    fn test_zero_annihilates() {
        let a = FreeWeight::gen("x");
        let prod = a.times_ref(&FreeWeight::zero_ref());
        assert!(prod.is_zero_ref(), "zero annihilates on right");
        let prod2 = FreeWeight::zero_ref().times_ref(&a);
        assert!(prod2.is_zero_ref(), "zero annihilates on left");
    }

    #[test]
    fn test_simplify() {
        let x = FreeExpr::gen("x");
        let zero_plus_x = FreeExpr::Plus(Box::new(FreeExpr::Zero), Box::new(x.clone()));
        assert_eq!(zero_plus_x.simplify(), x, "0 + x simplifies to x");

        let one_times_x = FreeExpr::Times(Box::new(FreeExpr::One), Box::new(x.clone()));
        assert_eq!(one_times_x.simplify(), x, "1 * x simplifies to x");

        let zero_times_x = FreeExpr::Times(Box::new(FreeExpr::Zero), Box::new(x.clone()));
        assert_eq!(zero_times_x.simplify(), FreeExpr::Zero, "0 * x simplifies to 0");
    }

    #[test]
    fn test_display() {
        let expr = FreeExpr::Plus(
            Box::new(FreeExpr::gen("x")),
            Box::new(FreeExpr::Times(
                Box::new(FreeExpr::gen("y")),
                Box::new(FreeExpr::gen("z")),
            )),
        );
        assert_eq!(format!("{}", expr), "(x + (y * z))");
    }

    #[test]
    fn test_generators() {
        let expr = FreeExpr::Plus(
            Box::new(FreeExpr::gen("a")),
            Box::new(FreeExpr::Times(
                Box::new(FreeExpr::gen("b")),
                Box::new(FreeExpr::gen("a")),
            )),
        );
        let gens = expr.generators();
        assert_eq!(gens.len(), 2);
        assert!(gens.contains("a"));
        assert!(gens.contains("b"));
    }

    #[test]
    fn test_generator_count() {
        let expr = FreeExpr::Plus(
            Box::new(FreeExpr::gen("a")),
            Box::new(FreeExpr::Times(
                Box::new(FreeExpr::gen("b")),
                Box::new(FreeExpr::gen("a")),
            )),
        );
        assert_eq!(expr.generator_count(), 3);
    }

    #[test]
    fn test_evaluate() {
        let expr = FreeExpr::Plus(
            Box::new(FreeExpr::gen("x")),
            Box::new(FreeExpr::Times(
                Box::new(FreeExpr::gen("y")),
                Box::new(FreeExpr::gen("z")),
            )),
        );
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 2.0);
        env.insert("y".to_string(), 3.0);
        env.insert("z".to_string(), 4.0);
        // x + y*z = 2 + 3*4 = 14
        let result = expr.evaluate(&env);
        assert!((result - 14.0).abs() < 1e-10, "result = {}", result);
    }

    #[test]
    fn test_deeply_nested_simplify() {
        // Build a deeply nested expression: 0 + (0 + (0 + ... + x))
        let mut expr = FreeExpr::gen("x");
        for _ in 0..100 {
            expr = FreeExpr::Plus(Box::new(FreeExpr::Zero), Box::new(expr));
        }
        let simplified = expr.simplify();
        assert_eq!(simplified, FreeExpr::gen("x"), "deep nesting simplifies correctly");
    }

    // ═══════════════════════════════════════════════════════════════════════
    // SemiringRef law tests for FreeWeight
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_free_weight_implements_semiring_ref() {
        // Verify FreeWeight satisfies SemiringRef by calling trait methods.
        let x = FreeWeight::gen("x");
        let y = FreeWeight::gen("y");

        let z = FreeWeight::zero_ref();
        let one = FreeWeight::one_ref();

        assert!(z.is_zero_ref());
        assert!(one.is_one_ref());
        assert!(!x.is_zero_ref());
        assert!(!x.is_one_ref());

        // Verify plus_ref and times_ref produce the expected structure.
        let sum = x.plus_ref(&y);
        assert_eq!(
            sum.expr,
            FreeExpr::Plus(
                Box::new(FreeExpr::gen("x")),
                Box::new(FreeExpr::gen("y")),
            ),
        );

        let prod = x.times_ref(&y);
        assert_eq!(
            prod.expr,
            FreeExpr::Times(
                Box::new(FreeExpr::gen("x")),
                Box::new(FreeExpr::gen("y")),
            ),
        );
    }

    /// Semiring law: additive identity (0 + a = a, a + 0 = a)
    #[test]
    fn test_semiring_ref_law_additive_identity() {
        let a = FreeWeight::gen("a");
        let z = FreeWeight::zero_ref();

        assert_eq!(z.plus_ref(&a), a, "0 + a = a");
        assert_eq!(a.plus_ref(&z), a, "a + 0 = a");
    }

    /// Semiring law: multiplicative identity (1 * a = a, a * 1 = a)
    #[test]
    fn test_semiring_ref_law_multiplicative_identity() {
        let a = FreeWeight::gen("a");
        let one = FreeWeight::one_ref();

        assert_eq!(one.times_ref(&a), a, "1 * a = a");
        assert_eq!(a.times_ref(&one), a, "a * 1 = a");
    }

    /// Semiring law: zero annihilates (0 * a = 0, a * 0 = 0)
    #[test]
    fn test_semiring_ref_law_zero_annihilates() {
        let a = FreeWeight::gen("a");
        let z = FreeWeight::zero_ref();

        assert!(z.times_ref(&a).is_zero_ref(), "0 * a = 0");
        assert!(a.times_ref(&z).is_zero_ref(), "a * 0 = 0");
    }

    /// Semiring law: additive commutativity verified structurally.
    ///
    /// In the free semiring, `a + b` and `b + a` are structurally distinct
    /// (different ASTs). However, they are semantically equivalent. We verify
    /// commutativity via evaluation: for any assignment, eval(a+b) == eval(b+a).
    #[test]
    fn test_semiring_ref_law_additive_commutativity_via_eval() {
        let a = FreeWeight::gen("x");
        let b = FreeWeight::gen("y");

        let sum_ab = a.plus_ref(&b);
        let sum_ba = b.plus_ref(&a);

        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 3.0);
        env.insert("y".to_string(), 7.0);

        let val_ab = sum_ab.expr.evaluate(&env);
        let val_ba = sum_ba.expr.evaluate(&env);
        assert!(
            (val_ab - val_ba).abs() < 1e-10,
            "a + b == b + a under evaluation: {} vs {}",
            val_ab,
            val_ba,
        );
    }

    /// Semiring law: left distributivity a * (b + c) = (a * b) + (a * c)
    /// Verified via evaluation since the free semiring preserves structure.
    #[test]
    fn test_semiring_ref_law_left_distributivity_via_eval() {
        let a = FreeWeight::gen("a");
        let b = FreeWeight::gen("b");
        let c = FreeWeight::gen("c");

        let lhs = a.times_ref(&b.plus_ref(&c));
        let rhs = a.times_ref(&b).plus_ref(&a.times_ref(&c));

        let mut env = std::collections::HashMap::new();
        env.insert("a".to_string(), 2.0);
        env.insert("b".to_string(), 3.0);
        env.insert("c".to_string(), 5.0);

        let val_lhs = lhs.expr.evaluate(&env);
        let val_rhs = rhs.expr.evaluate(&env);
        // 2*(3+5) = 16,  (2*3)+(2*5) = 6+10 = 16
        assert!(
            (val_lhs - val_rhs).abs() < 1e-10,
            "a*(b+c) == a*b + a*c under evaluation: {} vs {}",
            val_lhs,
            val_rhs,
        );
    }

    /// Semiring law: right distributivity (a + b) * c = (a * c) + (b * c)
    #[test]
    fn test_semiring_ref_law_right_distributivity_via_eval() {
        let a = FreeWeight::gen("a");
        let b = FreeWeight::gen("b");
        let c = FreeWeight::gen("c");

        let lhs = a.plus_ref(&b).times_ref(&c);
        let rhs = a.times_ref(&c).plus_ref(&b.times_ref(&c));

        let mut env = std::collections::HashMap::new();
        env.insert("a".to_string(), 2.0);
        env.insert("b".to_string(), 3.0);
        env.insert("c".to_string(), 5.0);

        let val_lhs = lhs.expr.evaluate(&env);
        let val_rhs = rhs.expr.evaluate(&env);
        // (2+3)*5 = 25,  (2*5)+(3*5) = 10+15 = 25
        assert!(
            (val_lhs - val_rhs).abs() < 1e-10,
            "(a+b)*c == a*c + b*c under evaluation: {} vs {}",
            val_lhs,
            val_rhs,
        );
    }

    /// Semiring law: multiplicative associativity a * (b * c) = (a * b) * c
    #[test]
    fn test_semiring_ref_law_multiplicative_associativity_via_eval() {
        let a = FreeWeight::gen("a");
        let b = FreeWeight::gen("b");
        let c = FreeWeight::gen("c");

        let lhs = a.times_ref(&b.times_ref(&c));
        let rhs = a.times_ref(&b).times_ref(&c);

        let mut env = std::collections::HashMap::new();
        env.insert("a".to_string(), 2.0);
        env.insert("b".to_string(), 3.0);
        env.insert("c".to_string(), 5.0);

        let val_lhs = lhs.expr.evaluate(&env);
        let val_rhs = rhs.expr.evaluate(&env);
        // 2*(3*5) = 30,  (2*3)*5 = 30
        assert!(
            (val_lhs - val_rhs).abs() < 1e-10,
            "a*(b*c) == (a*b)*c under evaluation: {} vs {}",
            val_lhs,
            val_rhs,
        );
    }

    /// Semiring law: additive associativity a + (b + c) = (a + b) + c
    #[test]
    fn test_semiring_ref_law_additive_associativity_via_eval() {
        let a = FreeWeight::gen("a");
        let b = FreeWeight::gen("b");
        let c = FreeWeight::gen("c");

        let lhs = a.plus_ref(&b.plus_ref(&c));
        let rhs = a.plus_ref(&b).plus_ref(&c);

        let mut env = std::collections::HashMap::new();
        env.insert("a".to_string(), 2.0);
        env.insert("b".to_string(), 3.0);
        env.insert("c".to_string(), 5.0);

        let val_lhs = lhs.expr.evaluate(&env);
        let val_rhs = rhs.expr.evaluate(&env);
        // 2+(3+5) = 10,  (2+3)+5 = 10
        assert!(
            (val_lhs - val_rhs).abs() < 1e-10,
            "a+(b+c) == (a+b)+c under evaluation: {} vs {}",
            val_lhs,
            val_rhs,
        );
    }

    /// Verify identity element detection.
    #[test]
    fn test_semiring_ref_identity_detection() {
        let z = FreeWeight::zero_ref();
        let one = FreeWeight::one_ref();
        let gen = FreeWeight::gen("x");

        assert!(z.is_zero_ref());
        assert!(!z.is_one_ref());

        assert!(one.is_one_ref());
        assert!(!one.is_zero_ref());

        assert!(!gen.is_zero_ref());
        assert!(!gen.is_one_ref());
    }

    /// Compound expression test: chain of operations preserving semiring laws.
    #[test]
    fn test_semiring_ref_compound_expression() {
        let x = FreeWeight::gen("x");
        let y = FreeWeight::gen("y");
        let z = FreeWeight::gen("z");

        // Build (x + y) * z and verify via evaluation
        let result = x.plus_ref(&y).times_ref(&z);

        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 2.0);
        env.insert("y".to_string(), 3.0);
        env.insert("z".to_string(), 4.0);

        let val = result.expr.evaluate(&env);
        // (2 + 3) * 4 = 20
        assert!(
            (val - 20.0).abs() < 1e-10,
            "(x + y) * z = {}, expected 20.0",
            val,
        );
    }
}
