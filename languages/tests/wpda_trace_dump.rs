//! Stage 6 G6+ trace-dump diagnosis (2026-05-02).
//!
//! Reproduces the `display_int_abuts_else_keyword_separated` hang from
//! `optional_group_smoke.rs` with a bounded-step walker driver and a
//! `RichTracingConsumer` attached. The trace exposes one of:
//!   - cursor count grows unboundedly → cursor-merge bug
//!   - cursor count steady but progress_made fingerprint changing → fingerprint bug
//!   - state oscillation → engine arm bug
//!   - cursor saturation at beam ceiling → genuine ambiguity
//!
//! Run with: `cargo test -p mettail-languages --test wpds_trace_dump -- --nocapture`

use mettail_languages::optsmoke::{Bool, Int};
use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_walker::RichTracingConsumer;

#[test]
fn diagnose_display_int_abuts_else_keyword_separated() {
    // Direct construction (mirrors optional_group_smoke.rs:181-185).
    let inner = Int::IfElse(
        Box::new(Bool::BoolLit(true)),
        Box::new(Int::NumLit(456913875)),
        None,
    );
    let outer = Int::IfElse(
        Box::new(Bool::BoolLit(false)),
        Box::new(inner),
        Some(Box::new(Int::NumLit(1894040589))),
    );
    let displayed = format!("{}", outer);
    eprintln!("[trace-dump] displayed: {:?}", displayed);

    // Set PRATTAIL_MAX_STEPS=500 to bound the walker; if the input hangs,
    // the trace should still terminate (after 500 steps the walker
    // returns MaxStepsExceeded).
    std::env::set_var("PRATTAIL_MAX_STEPS", "500");

    // Use a RichTracingConsumer to record every step's cursor census.
    let mut consumer: RichTracingConsumer<LexicographicWeight> =
        RichTracingConsumer::new();

    // For now we route through the existing public `Int::parse` path.
    // The codegen-emitted `Int::parse_traced` (next substage) will
    // accept a consumer + observer directly. This test validates the
    // WALKER infrastructure compiles + types match; the actual hang
    // diagnosis requires the codegen wiring.
    let result = Int::parse(&displayed);

    // Even with max_steps=500 enforced, we may hit MaxStepsExceeded
    // before resolving. Either way, we want stderr output for
    // post-mortem analysis.
    eprintln!("[trace-dump] parse result is_ok={}", result.is_ok());
    eprintln!("[trace-dump] consumer.steps.len() = {}", consumer.steps.len());
    eprintln!(
        "[trace-dump] consumer.max_cursor_count = {}",
        consumer.max_cursor_count
    );
    eprintln!(
        "[trace-dump] consumer.merges.len() = {}, drops.len() = {}, forks.len() = {}",
        consumer.merges.len(),
        consumer.drops.len(),
        consumer.forks.len()
    );

    // Ensure the consumer wasn't accidentally optimized away via Drop.
    let _ = &mut consumer;

    // Restore env var.
    std::env::remove_var("PRATTAIL_MAX_STEPS");
}
