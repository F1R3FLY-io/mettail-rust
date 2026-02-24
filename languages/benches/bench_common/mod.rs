//! Shared input generators for PraTTaIL parser benchmarks.
//!
//! These functions produce deterministic, syntactically valid strings
//! for each language's parser at various sizes. They are used across
//! multiple benchmark files to avoid duplication.

/// Standard scaling sizes used across most benchmarks.
pub const SIZES: &[usize] = &[1, 5, 10, 50, 100, 500, 1000];

/// Smaller sizes for features where large N causes very deep recursion.
pub const DEPTH_SIZES: &[usize] = &[1, 5, 10, 25, 50, 100];

/// Variable pool for random generation.
pub fn var_pool() -> Vec<String> {
    (0..20).map(|i| format!("v{}", i)).collect()
}

// =============================================================================
// Infix generators (Calculator: Int)
// =============================================================================

/// Left-associative infix chain: "1 + 2 + 3 + ... + N"
pub fn gen_infix_chain(n: usize, op: &str) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let terms: Vec<String> = (1..=n).map(|i| i.to_string()).collect();
    terms.join(&format!(" {} ", op))
}

/// Right-associative infix chain: "2 ^ 2 ^ 2 ^ ... ^ 2" (N operands)
pub fn gen_right_assoc_chain(n: usize) -> String {
    if n == 0 {
        return "2".to_string();
    }
    let terms: Vec<&str> = (0..n).map(|_| "2").collect();
    terms.join(" ^ ")
}

/// Mixed-precedence chain: "1 + 2 ^ 3 + 4 ^ 5 + ..."
/// Alternates low-precedence (+) and high-precedence (^) operators.
pub fn gen_mixed_precedence(n: usize) -> String {
    if n == 0 {
        return "1".to_string();
    }
    let mut parts = Vec::with_capacity(n);
    for i in 1..=n {
        parts.push(i.to_string());
    }
    let mut result = parts[0].clone();
    for (i, part) in parts.iter().enumerate().skip(1) {
        let op = if i % 2 == 1 { "+" } else { "^" };
        result.push_str(&format!(" {} {}", op, part));
    }
    result
}

/// Alternating left-assoc operators at same precedence: "1 + 2 - 3 + 4 - ..."
pub fn gen_alternating_add_sub(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let mut result = "1".to_string();
    for i in 2..=n {
        let op = if i % 2 == 0 { "+" } else { "-" };
        result.push_str(&format!(" {} {}", op, i));
    }
    result
}

// =============================================================================
// Prefix generators (Calculator: Int, Bool)
// =============================================================================

/// Chained unary prefix negation: "- - - ... - 42" (N negations)
pub fn gen_chained_negation(n: usize) -> String {
    let prefix = "- ".repeat(n);
    format!("{}42", prefix)
}

/// Prefix + infix interleaved: "- 1 + - 2 + - 3 + ... + - N"
pub fn gen_prefix_infix(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let terms: Vec<String> = (1..=n).map(|i| format!("- {}", i)).collect();
    terms.join(" + ")
}

/// Boolean NOT chain: "not not not ... not true" (N nots)
pub fn gen_not_chain(n: usize) -> String {
    let prefix = "not ".repeat(n);
    format!("{}true", prefix)
}

// =============================================================================
// Nesting generators (Lambda: Term, Calculator: Int)
// =============================================================================

/// Nested lambda abstraction: "lam x0.lam x1. ... lam xN.x0"
pub fn gen_nested_lambda(depth: usize) -> String {
    if depth == 0 {
        return "x".to_string();
    }
    let mut result = String::new();
    for i in 0..depth {
        result.push_str(&format!("lam x{}.{}", i, if i < depth - 1 { "" } else { "" }));
    }
    result.push_str("x0");
    result
}

/// Nested application: "(((x,y),z),w)..." (depth levels)
/// At depth 1: "(x,y)", at depth 2: "((x,y),z)", etc.
pub fn gen_nested_application(depth: usize) -> String {
    if depth == 0 {
        return "x".to_string();
    }
    let mut result = "x".to_string();
    for i in 0..depth {
        let var = format!("v{}", i);
        result = format!("({},{})", result, var);
    }
    result
}

/// Nested parenthesized expression: "(((...(42)...)))" (depth parens)
/// Uses Calculator Int with grouping parens.
pub fn gen_nested_parens(depth: usize) -> String {
    let inner = "42";
    let open: String = "(".repeat(depth);
    let close: String = ")".repeat(depth);
    format!("{}{}{}", open, inner, close)
}

/// Mixed lambda+application: "lam x0.lam x1. ... (x0, x1)"
pub fn gen_lambda_app_mix(depth: usize) -> String {
    if depth == 0 {
        return "x".to_string();
    }
    let mut result = String::new();
    for i in 0..depth {
        result.push_str(&format!("lam x{}.", i));
    }
    // End with nested application of first two vars
    if depth >= 2 {
        result.push_str("(x0,x1)");
    } else {
        result.push_str("x0");
    }
    result
}

// =============================================================================
// Collection generators (Ambient: Proc)
// =============================================================================

/// Flat parallel composition: "{p0 | p1 | ... | pN}" (N elements)
pub fn gen_parallel(n: usize, body: &str) -> String {
    if n == 0 {
        return "{}".to_string();
    }
    let terms: Vec<&str> = (0..n).map(|_| body).collect();
    format!("{{{}}}", terms.join(" | "))
}

/// Parallel with named ambients: "{n0[0] | n1[0] | ... | nN[0]}"
pub fn gen_parallel_amb(n: usize) -> String {
    if n == 0 {
        return "{}".to_string();
    }
    let terms: Vec<String> = (0..n).map(|i| format!("n{}[0]", i)).collect();
    format!("{{{}}}", terms.join(" | "))
}

/// Nested parallel composition: "{0 | {0 | {0 | ... }}}" (depth levels)
pub fn gen_nested_parallel(depth: usize) -> String {
    if depth == 0 {
        return "0".to_string();
    }
    let mut result = "0".to_string();
    for _ in 0..depth {
        result = format!("{{0 | {}}}", result);
    }
    result
}

// =============================================================================
// Binder generators (Ambient: Proc, RhoCalc: Proc)
// =============================================================================

/// Chained new-binders: "new(x0, new(x1, ... new(xN, 0)...))"
pub fn gen_chained_new(depth: usize) -> String {
    if depth == 0 {
        return "0".to_string();
    }
    let mut result = "0".to_string();
    for i in (0..depth).rev() {
        result = format!("new(x{},{})", i, result);
    }
    result
}

/// RhoCalc multi-input ZipMapSep: "(x0?a0, x1?a1, ..., xN?aN).{0}"
pub fn gen_multi_input(n: usize) -> String {
    if n == 0 {
        return "{}".to_string();
    }
    let bindings: Vec<String> = (0..n).map(|i| format!("c{}?x{}", i, i)).collect();
    format!("({}).{{{}}}", bindings.join(", "), "0")
}

/// RhoCalc nested output: "{c0!(0) | c1!(0) | ... | cN!(0)}"
pub fn gen_nested_output(n: usize) -> String {
    if n == 0 {
        return "{}".to_string();
    }
    let terms: Vec<String> = (0..n).map(|i| format!("c{}!(0)", i)).collect();
    format!("{{{}}}", terms.join(" | "))
}

// =============================================================================
// Cross-category generators (Calculator: Bool, RhoCalc: Proc)
// =============================================================================

/// Cross-category equality: "(1 + 2 + ... + N) == (N + ... + 2 + 1)"
pub fn gen_cross_cat_eq(n: usize) -> String {
    let lhs = gen_infix_chain(n, "+");
    let rhs_terms: Vec<String> = (1..=n).rev().map(|i| i.to_string()).collect();
    let rhs = rhs_terms.join(" + ");
    format!("{} == {}", lhs, rhs)
}

/// Cast chain in RhoCalc: "{1 | 2 | 3 | ... | N}" (ints cast to Proc)
pub fn gen_cast_chain(n: usize) -> String {
    if n == 0 {
        return "{}".to_string();
    }
    let terms: Vec<String> = (1..=n).map(|i| i.to_string()).collect();
    format!("{{{}}}", terms.join(" | "))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infix_chain() {
        assert_eq!(gen_infix_chain(3, "+"), "1 + 2 + 3");
        assert_eq!(gen_infix_chain(1, "-"), "1");
    }

    #[test]
    fn test_right_assoc_chain() {
        assert_eq!(gen_right_assoc_chain(3), "2 ^ 2 ^ 2");
    }

    #[test]
    fn test_mixed_precedence() {
        assert_eq!(gen_mixed_precedence(5), "1 + 2 ^ 3 + 4 ^ 5");
    }

    #[test]
    fn test_chained_negation() {
        assert_eq!(gen_chained_negation(3), "- - - 42");
    }

    #[test]
    fn test_prefix_infix() {
        assert_eq!(gen_prefix_infix(3), "- 1 + - 2 + - 3");
    }

    #[test]
    fn test_not_chain() {
        assert_eq!(gen_not_chain(3), "not not not true");
    }

    #[test]
    fn test_nested_lambda() {
        assert_eq!(gen_nested_lambda(3), "lam x0.lam x1.lam x2.x0");
    }

    #[test]
    fn test_nested_application() {
        assert_eq!(gen_nested_application(2), "((x,v0),v1)");
    }

    #[test]
    fn test_nested_parens() {
        assert_eq!(gen_nested_parens(3), "(((42)))");
    }

    #[test]
    fn test_parallel() {
        assert_eq!(gen_parallel(3, "0"), "{0 | 0 | 0}");
    }

    #[test]
    fn test_parallel_amb() {
        assert_eq!(gen_parallel_amb(2), "{n0[0] | n1[0]}");
    }

    #[test]
    fn test_nested_parallel() {
        assert_eq!(gen_nested_parallel(2), "{0 | {0 | 0}}");
    }

    #[test]
    fn test_chained_new() {
        assert_eq!(gen_chained_new(2), "new(x0,new(x1,0))");
    }

    #[test]
    fn test_multi_input() {
        assert_eq!(gen_multi_input(2), "(c0?x0, c1?x1).{0}");
    }

    #[test]
    fn test_nested_output() {
        assert_eq!(gen_nested_output(2), "{c0!(0) | c1!(0)}");
    }

    #[test]
    fn test_cross_cat_eq() {
        assert_eq!(gen_cross_cat_eq(3), "1 + 2 + 3 == 3 + 2 + 1");
    }

    #[test]
    fn test_cast_chain() {
        assert_eq!(gen_cast_chain(3), "{1 | 2 | 3}");
    }
}
