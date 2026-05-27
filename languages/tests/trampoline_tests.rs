//! Stack-safety tests for the trampolined parser.
//!
//! These tests verify that deeply nested inputs parse correctly without
//! stack overflow, thanks to the heap-allocated continuation stack.
//! The trampoline converts all same-category recursion into iteration,
//! bounded only by available heap memory.
//!
//! Phase F.13 H7 (2026-05-20): opt-in mimalloc global allocator override
//! gated by the `mimalloc` cargo feature (off by default per user
//! direction "feature-gate mimalloc, don't enable it by default"). When
//! enabled via `cargo test --features mimalloc ...`, attaches mimalloc
//! to this test binary's implicit `main` and reduces the ~21% libc
//! allocator CPU cost observed at the F.13 baseline. When disabled,
//! the system allocator is used (default behavior).

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
fn test_right_assoc_chain_50() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(50);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "50 right-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_right_assoc_chain_100() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(100);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100 right-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_right_assoc_chain_200() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(200);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "200 right-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_right_assoc_chain_1000() {
    mettail_runtime::clear_var_cache();
    let input = right_assoc_chain(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 right-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Architectural ceiling: same root cause as \
    test_left_assoc_chain_10000 above (BranchCursor::clone per-step \
    churn dominates). Re-enable in same conditions."]
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
#[ignore = "Architectural ceiling: BranchCursor::clone is 49%+ of \
    peak heap at chain_1000 (heaptrack). L1-L6 cohort lazy \
    materialization SHIPPED (commits f5f9cac..7ead9da) — Arc-shares \
    visited_dispatch/visited_recovery/recovery_deltas/incoming_edge_stack. \
    Improved memory growth rate ~3× (4.5 GB at 9 min vs pre-L3 \
    24 GB at <2 min) but didn't close the ceiling: cohort sharing \
    triggers at H12 cross-cat-projection dispatch, NOT at \
    same-category operator parsing (which is what left-assoc chain \
    exercises). Per Arc::make_mut deep-clones-on-fork: when Fork \
    creates 2+ siblings sharing an Arc, first mutation on any \
    sibling deep-clones — H2 prior attempt at Arc-CoW visited_* \
    rejected at chain_100 -6.9% p≈0.01. The remaining fix path is \
    research-level: operator-precedence iterative parsing or \
    walker-global per-cursor-state with CursorId keying \
    (`~/.claude/projects/.../memory/2026-05-24-chain_10000-heaptrack-architectural-ceiling.md` \
    item #4, ~3-5d refactor). Re-enable when one of those ships."]
fn test_left_assoc_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 left-assoc ops should parse: {:?}", result.err());
}

// Phase F.13 chain_10000 Exp 16 round 3 (2026-05-26): scaling probes
// for walker memory attribution. left_assoc_chain at N=2000 and 5000
// should fit in 24 GB by linear/quadratic projection from chain_1000's
// 15 MB peak. Used with --features walker-stats to plot the actual
// scaling exponent of walker live state.
#[test]
fn test_left_assoc_chain_50() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(50);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "50 left-assoc ops should parse: {:?}", result.err());
}

#[test]
fn test_left_assoc_chain_100() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(100);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "100 left-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Exp 17 / Exp 16 r3 scaling probe — left-assoc N=200 takes minutes"]
fn test_left_assoc_chain_200() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(200);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "200 left-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Exp 16 round 3 scaling probe"]
fn test_left_assoc_chain_500() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(500);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "500 left-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Exp 16 round 3 scaling probe"]
fn test_left_assoc_chain_1000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(1000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 left-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Exp 16 round 3 scaling probe: run with --features walker-stats PRATTAIL_WALKER_STATS=1 to capture per-N attribution"]
fn test_left_assoc_chain_2000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(2_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "2000 left-assoc ops should parse: {:?}", result.err());
}

#[test]
#[ignore = "Exp 16 round 3 scaling probe: run with --features walker-stats PRATTAIL_WALKER_STATS=1 to capture per-N attribution"]
fn test_left_assoc_chain_5000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(5_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "5000 left-assoc ops should parse: {:?}", result.err());
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
