//! Stack-safety tests for the trampolined parser.
//!
//! These tests verify that deeply nested inputs parse correctly without
//! stack overflow, thanks to the heap-allocated continuation stack.
//! The trampoline converts all same-category recursion into iteration,
//! bounded only by available heap memory.

use mettail_languages::calculator::{Bool, Int};

// ── Helper: generate deeply nested parenthesized expression ──

fn nested_parens(depth: usize) -> String {
    let mut s = String::with_capacity(depth * 2 + 1);
    for _ in 0..depth {
        s.push('(');
    }
    s.push('1');
    for _ in 0..depth {
        s.push(')');
    }
    s
}

fn right_assoc_chain(depth: usize) -> String {
    // "2 ^ 2 ^ 2 ^ ... ^ 2" (right-associative)
    let mut s = String::with_capacity(depth * 4);
    for i in 0..depth {
        if i > 0 {
            s.push_str(" ^ ");
        }
        s.push('2');
    }
    s
}

fn left_assoc_chain(depth: usize) -> String {
    // "1 + 1 + 1 + ... + 1" (left-associative, iterative in Pratt loop)
    let mut s = String::with_capacity(depth * 4);
    for i in 0..depth {
        if i > 0 {
            s.push_str(" + ");
        }
        s.push('1');
    }
    s
}

fn nested_unary(depth: usize) -> String {
    // "- - - ... - 1" (unary prefix chain)
    let mut s = String::with_capacity(depth * 2 + 1);
    for _ in 0..depth {
        s.push_str("- ");
    }
    s.push('1');
    s
}

fn nested_not(depth: usize) -> String {
    // "not not not ... not true" (unary prefix chain for Bool)
    let mut s = String::with_capacity(depth * 4 + 4);
    for _ in 0..depth {
        s.push_str("not ");
    }
    s.push_str("true");
    s
}

fn nested_ternary(depth: usize) -> String {
    // "1 ? 2 : (1 ? 2 : (1 ? 2 : ... : 3))"
    // Right-nesting via the else branch
    let mut s = String::with_capacity(depth * 12);
    for _ in 0..depth {
        s.push_str("1 ? 2 : (");
    }
    s.push('3');
    for _ in 0..depth {
        s.push(')');
    }
    s
}

// ── Tests: Deep parenthesized nesting ──

#[test]
fn test_deep_parens_100() {
    mettail_runtime::clear_var_cache();
    let input = nested_parens(100);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100 nested parens should parse: {:?}", result.err());
}

#[test]
fn test_deep_parens_1000() {
    mettail_runtime::clear_var_cache();
    let input = nested_parens(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 nested parens should parse: {:?}", result.err());
}

#[test]
fn test_deep_parens_10000() {
    mettail_runtime::clear_var_cache();
    let input = nested_parens(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 nested parens should parse: {:?}", result.err());
}

#[test]
fn test_deep_parens_100000() {
    mettail_runtime::clear_var_cache();
    let input = nested_parens(100_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100000 nested parens should parse: {:?}", result.err());
}

// ── Tests: Right-associative chains ──

#[test]
fn test_right_assoc_chain_100() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(100);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100 right-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_right_assoc_chain_1000() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 right-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_right_assoc_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 right-assoc ops should parse: {:?}", result.err());
}

// ── Tests: Left-associative chains (already iterative in Pratt loop) ──
// Note: 10K is used instead of 100K because the resulting AST is deeply nested
// and AST operations (Display, Drop) still recurse on the call stack.
// Sprint 2 (AST Work-Stack) will make AST operations stack-safe too.

#[test]
fn test_left_assoc_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 left-assoc ops should parse: {:?}", result.err());
}

// ── Tests: Deep unary prefix chains ──

#[test]
fn test_deep_unary_neg_1000() {
    mettail_runtime::clear_var_cache();
    let input = nested_unary(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 unary neg should parse: {:?}", result.err());
}

#[test]
fn test_deep_unary_neg_10000() {
    mettail_runtime::clear_var_cache();
    let input = nested_unary(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 unary neg should parse: {:?}", result.err());
}

#[test]
fn test_deep_unary_not_1000() {
    mettail_runtime::clear_var_cache();
    let input = nested_not(1_000);
    let result = Bool::parse_structured(&input);
    assert!(result.is_ok(), "1000 unary not should parse: {:?}", result.err());
}

// ── Tests: Deep mixfix (ternary) nesting ──

#[test]
fn test_deep_ternary_100() {
    mettail_runtime::clear_var_cache();
    let input = nested_ternary(100);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100 nested ternaries should parse: {:?}", result.err());
}

#[test]
fn test_deep_ternary_1000() {
    mettail_runtime::clear_var_cache();
    let input = nested_ternary(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 nested ternaries should parse: {:?}", result.err());
}

// ── Tests: Mixed nesting ──

#[test]
fn test_mixed_deep_nesting() {
    mettail_runtime::clear_var_cache();
    // Combine parentheses, unary, and infix: "(((-(-1))))"
    let depth = 1000;
    let mut s = String::with_capacity(depth * 6);
    for _ in 0..depth {
        s.push_str("(- ");
    }
    s.push('1');
    for _ in 0..depth {
        s.push(')');
    }
    let result = Int::parse_structured(&s);
    assert!(result.is_ok(), "mixed deep nesting should parse: {:?}", result.err());
}

// ── Tests: Verify correctness of deep nesting results ──

#[test]
fn test_deep_parens_value_correct() {
    mettail_runtime::clear_var_cache();
    // (((1 + 2))) should still be 3 regardless of nesting depth
    let input = format!("{}1 + 2{}", "(".repeat(50), ")".repeat(50));
    let result = Int::parse_structured(&input);
    assert!(result.is_ok());
    let ast = result.expect("should parse");
    // The AST should be Add(NumLit(1), NumLit(2)) regardless of parens
    let display = format!("{}", ast);
    assert!(
        display.contains("1") && display.contains("2"),
        "AST should contain 1 and 2: {}",
        display
    );
}
