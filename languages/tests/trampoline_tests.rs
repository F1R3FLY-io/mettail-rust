#![cfg(feature = "oracle-ascent")]

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

use mettail_languages::calculator::{Bool, CalculatorLanguage, Int};
use mettail_runtime::Language;

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

fn ternary_chain(depth: usize) -> String {
    // "0 ? 1 : 0 ? 1 : ... : 0" — deeply nested MIXFIX ternary
    // (`Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int`, right-assoc),
    // parsing as Tern(0, 1, Tern(0, 1, ... Tern(0, 1, 0))) `depth` levels
    // deep. Exercises the normal WPDS walker path (NOT the H3 Earley chain
    // absorption, which is binary-infix-only) — generalization probe for
    // the Box→Arc AST representation (Arc refactor 2026-05-28).
    let mut s = String::with_capacity(depth * 8 + 1);
    for _ in 0..depth {
        s.push_str("0 ? 1 : ");
    }
    s.push('0');
    s
}

// ── C1 (WALK-S0..S4): chain EVAL gate (G4) ──────────────────────────
//
// The parse-only chain tests assert is_ok() but NOT values; that blind
// spot hid latent SPPF-emit bugs (wrong arity / rule_idx) in chain
// absorption. These assert the EVALUATED value of absorbed (and, as
// oracles, non-absorbed) chains so right-associativity, arity, and the
// literal-injection rule are all verified end-to-end. Under S0 they
// validate the normal-walker / AddInt-chart baseline; later substages
// re-run them after each operator's absorption is wired.

fn assert_chain_eval(input: &str, expected: &str) {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse should succeed for {input:?}: {e:?}"));
    let results = lang
        .run_ascent(parsed.as_ref())
        .expect("eval should succeed");
    let nfs: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        nfs.iter().any(|d| d == expected),
        "{input:?} should evaluate to {expected:?}, got {nfs:?}"
    );
}

/// Right-associativity verification under a NON-CONFLUENT eval. Calculator's
/// `^` eval is non-confluent — the cross-cat cast machinery (`int(bool(x))`,
/// etc.) explores many reduction paths, and a deeply-composed power (e.g.
/// 2^8=256) is not reliably reached. So we keep the exponents at 1 so the
/// right-assoc value stays SMALL (and IS reliably produced) while asserting
/// the LEFT-assoc value (a higher power) is ABSENT. A higher power is only
/// computable from a LEFT-nested parse, so its absence confirms the parse is
/// right-associative — not left, not ambiguous.
fn assert_right_assoc_eval(input: &str, right_val: &str, left_val: &str) {
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse should succeed for {input:?}: {e:?}"));
    let results = lang
        .run_ascent(parsed.as_ref())
        .expect("eval should succeed");
    let nfs: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        nfs.iter().any(|d| d == right_val),
        "{input:?} (right-assoc) should produce {right_val:?}, got {nfs:?}"
    );
    assert!(
        !nfs.iter().any(|d| d == left_val),
        "{input:?} (right-assoc) must NOT produce the left-assoc value {left_val:?}, got {nfs:?}"
    );
}

#[test]
fn test_eval_right_assoc_chain() {
    // `^` is right-associative (`step right`). Exponents kept at 1 so the
    // right-assoc value stays small (reliably reduced under the non-confluent
    // eval) and the left-assoc value (a higher power) stays absent. >= 4
    // atoms → exercise H3 absorption once C1-R (S1) lands; under S0 baseline.
    // 2^1^1^2 = 2^(1^(1^2)) = 2^1 = 2   (left ((2^1)^1)^2 = 2^2 = 4).
    assert_right_assoc_eval("2 ^ 1 ^ 1 ^ 2", "2", "4");
    // 3^1^1^2 = 3^(1^(1^2)) = 3^1 = 3   (left ((3^1)^1)^2 = 3^2 = 9).
    assert_right_assoc_eval("3 ^ 1 ^ 1 ^ 2", "3", "9");
}

#[test]
fn test_eval_right_assoc_chain_oracle() {
    // 3 atoms (< trigger threshold): always the normal walker — the
    // absorbed-vs-normal oracle. 2^1^3 = 2^(1^3) = 2^1 = 2 (left (2^1)^3 = 8).
    assert_right_assoc_eval("2 ^ 1 ^ 3", "2", "8");
}

#[test]
fn test_eval_ternary_chain() {
    // Right-recursive in the else slot. All-zero conds select the tail: 0.
    assert_chain_eval("0 ? 1 : 0 ? 1 : 0 ? 1 : 0 ? 1 : 0", "0");
    // Tern(1,7,Tern(0,9,3)) -> 7 ; Tern(0,7,Tern(1,9,3)) -> 9.
    assert_chain_eval("1 ? 7 : 0 ? 9 : 3", "7");
    assert_chain_eval("0 ? 7 : 1 ? 9 : 3", "9");
}

#[test]
fn test_eval_ternary_chain_oracle() {
    // 1 level (< trigger threshold): normal walker. Tern(1,7,3) -> 7.
    assert_chain_eval("1 ? 7 : 3", "7");
}

#[test]
fn test_eval_addint_chain() {
    // 8 atoms: triggers the (left-assoc) H3 absorption. 1+...+1 = 8.
    assert_chain_eval("1 + 1 + 1 + 1 + 1 + 1 + 1 + 1", "8");
}

#[test]
fn test_eval_addint_chain_oracle() {
    assert_chain_eval("1 + 1", "2");
}

#[test]
fn test_eval_subint_chain() {
    // Broadening canonical eligibility makes ALL Int left-assoc ops (not just
    // AddInt) absorb via H3. SubInt is NON-associative, so this is the decisive
    // structural check: the absorption must produce a LEFT-nested AST.
    // 20-1-1-1-1 (5 atoms = 4 atoms AFTER the LHS, so it DOES trigger the H3
    // peek gate of >= 4 remaining) = ((((20-1)-1)-1)-1) = 16 left-assoc. A
    // right-nested absorption would give a different value (e.g. 20-(...)); the
    // left-assoc value 16 confirms correct left-nesting.
    assert_chain_eval("20 - 1 - 1 - 1 - 1", "16");
}

#[test]
fn test_eval_subint_chain_short_oracle() {
    // 4 atoms = 3 remaining < 4: stays on the normal walker (no H3). The
    // absorbed-vs-normal oracle for SubInt left-assoc. 10-1-1-1 = 7.
    assert_chain_eval("10 - 1 - 1 - 1", "7");
}

#[test]
fn test_eval_mulint_chain() {
    // MulInt deep chain via the broadened H3 absorption. 2*3*1*1 = 6.
    assert_chain_eval("2 * 3 * 1 * 1", "6");
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

// Phase F.13 chain_10000 Exp 14 Substage 7 + Exp 15 Substage 7
// (2026-05-27): un-ignored per protocol amendment at
// `prattail/docs/design/plans/chain-10000-experiments-ledger.md`. The
// original 24 GB ceiling was a bench-protocol convention (operator-set
// `systemd-run --user --scope -p MemoryMax=24G`), not a CI requirement.
// `cargo test` honors no memory cap; on the host (125 GB RAM) the test
// runs to completion at the empirically measured ~45-60 GB peak (post-
// Tomita per-arc + im::OrdSet visited_* migrations, commit `0743246`).
// Test is long-running (~30-60 min); kept under the `tramp_*` test
// invocations that explicitly include chain probes, not the prattail-
// lib gauntlet.
#[test]
fn test_left_assoc_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 left-assoc ops should parse: {:?}", result.err());
}

// Phase F.13 chain_10000 plan-amend (2026-05-26): LEFT-associative
// Welch-panel chains at N=50/100/200. The amended substage gate per
// `~/.claude/plans/replicated-conjuring-turtle.md` requires LEFT-assoc
// regression coverage at these sizes — prior REJECTs only ran the
// RIGHT-assoc panel which does not exercise the iterative path.
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
fn test_left_assoc_chain_200() {
    mettail_runtime::clear_var_cache();
    let input = left_assoc_chain(200);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "200 left-assoc ops should parse: {:?}", result.err());
}

// Phase F.13 chain_10000 Exp 16 round 3 (2026-05-26): scaling probes
// for walker memory attribution. left_assoc_chain at N=2000 and 5000
// should fit in 24 GB by linear/quadratic projection from chain_1000's
// 15 MB peak. Used with --features walker-stats to plot the actual
// scaling exponent of walker live state.
// Phase F.13 chain_10000 Exp 14 Substage 7 (2026-05-27): un-ignored.
// chain_500 LEFT-assoc passes post-Tomita Subs 3-6 in 10:13 wall, 13.6 GB
// peak RSS (was 17:02, 21.2 GB pre-Tomita: -40% wall, -36% RSS). Kept
// in the gauntlet as a long-running scaling probe + memory-regression
// canary.
#[test]
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

// ── Tests: Deep MIXFIX (ternary) chains — H6 generalization probe ──
// `Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int` (right-assoc mixfix).
// Parsed via the normal WPDS walker (NOT H3 Earley absorption). Validates
// the Box→Arc AST representation generalizes to multi-operand mixfix nesting.

#[test]
#[ignore = "scaling probe — run explicitly"]
fn test_ternary_chain_1000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(1_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "1000 nested ternaries should parse: {:?}", result.err());
}

#[test]
#[ignore = "scaling probe — run explicitly"]
fn test_ternary_chain_2000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(2_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "2000 nested ternaries should parse: {:?}", result.err());
}

#[test]
fn test_ternary_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 nested ternaries should parse: {:?}", result.err());
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
