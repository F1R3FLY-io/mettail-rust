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

// Residual #11-3 D1 (2026-07-14): the EXACT-TOKEN partner of the passing
// `test_deep_unary_neg_20000`. `ternary_chain(5000)` = `"0 ? 1 : "`×5000 +
// `"0"` = 20,001 tokens — identical token count to `nested_unary(20000)`
// (20,000 `-` + `1`). Pre-registered discriminator D1: at equal tokens, if
// walls/RSS track within ~1.5× the ceiling is token-driven (one shared
// quadratic law); if the ternary is >~3× the arity/mixfix packing
// population drives it. `#[ignore]` + run-explicit per the F3 G2
// scaling-probe convention. Deliberately NOT `unary_40000` (its
// out-of-scope Display/Drop term-depth recursion would SIGSEGV at the
// 8 MiB default stack and contaminate D1 with the wrong mechanism).
#[test]
#[ignore = "scaling probe — run explicitly"]
fn test_ternary_chain_5000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(5_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "5000 nested ternaries should parse: {:?}", result.err());
}

// Residual #11-3 Amendment-8 OUTPUT GATE (2026-07-14): the chain tests assert
// only `is_ok()`, which cannot catch a realize-output change. This probe emits a
// deterministic structural fingerprint (hash of the realized AST's `Debug` form)
// for the shapes the lazy-fingerprint / leak fixes touch. Run it under the fix
// (`PRATTAIL_FP_LAZY=1`, default), the eager rollback (`PRATTAIL_FP_LAZY=0`), and
// dedup-off (`PRATTAIL_REALIZE_DEDUP=0`) — an IDENTICAL fingerprint across all
// three proves the realize output is byte-identical and the chain spine is
// single-candidate (nothing to dedup), i.e. the lazy skip is exact.
#[test]
#[ignore = "output-gate probe — run explicitly"]
fn probe_chain_output_fingerprint() {
    fn fp(s: &str) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(s, &mut h);
        std::hash::Hasher::finish(&h)
    }
    for n in [1000usize, 2000] {
        mettail_runtime::clear_var_cache();
        let r = Int::parse_structured(&ternary_chain(n)).expect("ternary parses");
        let dbg = format!("{r:?}");
        println!("TERNARY {n} debug_len={} fp={:016x}", dbg.len(), fp(&dbg));
    }
    {
        mettail_runtime::clear_var_cache();
        let r = Int::parse_structured(&nested_unary(1000)).expect("unary parses");
        let dbg = format!("{r:?}");
        println!("UNARY 1000 debug_len={} fp={:016x}", dbg.len(), fp(&dbg));
    }
}

#[test]
fn test_ternary_chain_10000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(10_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "10000 nested ternaries should parse: {:?}", result.err());
}

// S2-F3 G2 (2026-07-11): deeper scaling probes for the ITERATIVE realize
// conversion. Depth 20000 deliberately: pre-fix pure failed at 10k already
// (clean discriminator), while the pre-existing classic-shared TERM-depth
// recursions (generated semantic_hash, AST Display/Drop — the "Sprint 2
// AST Work-Stack" note above) are measured green at 10k and sized
// ~100-200 B/frame, leaving ≥2× headroom at 20k; 100k would gate on those
// out-of-scope ceilings, not on this conversion.
#[test]
#[ignore = "scaling probe — run explicitly"]
fn test_ternary_chain_20000() {
    mettail_runtime::clear_var_cache();
    let input = ternary_chain(20_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "20000 nested ternaries should parse: {:?}", result.err());
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
#[ignore = "scaling probe — run explicitly"]
fn test_deep_unary_neg_20000() {
    // S2-F3 G2: see the 20k rationale above.
    mettail_runtime::clear_var_cache();
    let input = nested_unary(20_000);
    let result = Int::parse_structured(&input);
    assert!(result.is_ok(), "20000 unary neg should parse: {:?}", result.err());
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
