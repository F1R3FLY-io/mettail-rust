//! THROWAWAY diagnostic (root-cause investigation of the Dovetail saturation
//! anomaly for `1 + 2` vs nested arithmetic). Parses each Calculator term, runs
//! the production `dovetail_report_for`, prints report-level counts, and times
//! each term (warm) to check whether `1 + 2` is really slower than the larger
//! nested terms.
//!
//! Run: cargo test -p languages --test diag_calc_saturation -- --nocapture
//! With engine counts: DOVETAIL_DIAG=1 cargo test ... (counts only; skip timing)

use std::time::Instant;

use mettail_languages::calculator::CalculatorLanguage;
use mettail_runtime::Language;

const MAX_ITERS: usize = 64;
const MAX_NODES: usize = 100_000;

#[test]
fn diag_report_counts_for_three_terms() {
    let lang = CalculatorLanguage;
    let base: &[(&str, &str)] = &[
        ("add", "1 + 2"),
        ("nested", "(2 + 3) * (4 - 1)"),
        ("deep", "((1 + 2) * (3 + 4)) - ((5 - 1) * (2 + 2))"),
    ];
    // Probe terms isolating the top-operator × category-support effect.
    let probes: &[(&str, &str)] = &[
        ("mul_pp", "(2 + 3) * (4 + 1)"), // top *, operands + (BigRat-native)
        ("mul_mm", "(2 - 3) * (4 - 1)"), // top *, operands - (BigRat needs inject)
        ("sub_pp", "(2 + 3) - (4 + 1)"), // top -, operands + (BigRat blocked: no Sub)
        ("add_pp", "(2 + 3) + (4 + 1)"), // top +, operands + (+ in all cats)
        ("sub_mm", "(2 - 3) - (4 - 1)"), // top -, operands - (Int/BigInt only)
        ("bare_mul", "2 * 3"),           // bare * over literals
        ("bare_sub", "2 - 3"),           // bare - over literals
    ];
    let run_probes = std::env::var_os("DIAG_PROBES").is_some();
    let inputs: Vec<(&str, &str)> = if run_probes {
        base.iter().chain(probes.iter()).copied().collect()
    } else {
        base.to_vec()
    };
    let inputs: &[(&str, &str)] = &inputs;

    // Focused perf loop: DIAG_FOCUS=add|nested|deep runs ONLY that term in a
    // long tight loop (no prints) so `perf record` gets a clean per-term profile.
    if let Some(focus) = std::env::var_os("DIAG_FOCUS") {
        let focus = focus.to_string_lossy().to_string();
        let (_n, src) = inputs
            .iter()
            .find(|(n, _)| *n == focus)
            .expect("DIAG_FOCUS must be add|nested|deep");
        let term = lang.parse_term(src).expect("parse");
        // warm the OnceLock
        for _ in 0..100 {
            let _ = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
        }
        let iters: usize = std::env::var("DIAG_ITERS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(200_000);
        for _ in 0..iters {
            let r = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
            std::hint::black_box(&r);
        }
        return;
    }

    let diag = std::env::var_os("DOVETAIL_DIAG").is_some();

    for (name, src) in inputs {
        eprintln!("\n========== TERM `{name}` = {src:?} ==========");
        let term = lang.parse_term(src).expect("calculator term parses");
        let report = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
            .expect("dovetail report");
        let max_class_id = report.terms.iter().map(|t| t.class_id).max().unwrap_or(0);
        let total_firings: usize = report.rule_firings.iter().map(|f| f.count).sum();
        eprintln!(
            "[REPORT {name}] roots={} terms(derivnodes)={} edges={} completeness={:?} max_class_id={} total_firings={}",
            report.roots.len(),
            report.terms.len(),
            report.derivation_edges.len(),
            report.completeness,
            max_class_id,
            total_firings,
        );
        let mut firings = report.rule_firings.clone();
        firings.sort_by(|a, b| b.count.cmp(&a.count));
        for f in &firings {
            eprintln!("[FIRING {name}] {:>4}  {:?}", f.count, f.label);
        }
    }

    if diag {
        eprintln!("\n[timing skipped: DOVETAIL_DIAG set — eprintln overhead would dominate]");
        return;
    }

    // ---- WALL-CLOCK TIMING (warm; OnceLock rule-compilation pre-triggered) ----
    // Pre-warm ALL terms first so the shared `__DOVETAIL_COMPILED_RULES` OnceLock
    // and allocator are hot before ANY term is timed — this isolates steady-state
    // per-call cost from the one-time global rule-set compilation.
    let terms: Vec<(&str, Box<dyn mettail_runtime::Term>)> = inputs
        .iter()
        .map(|(n, s)| (*n, lang.parse_term(s).expect("parse")))
        .collect();
    for _ in 0..50 {
        for (_n, t) in &terms {
            let _ = CalculatorLanguage::dovetail_report_for(t.as_ref(), MAX_ITERS, MAX_NODES);
        }
    }

    const ITERS: usize = 2000;
    eprintln!("\n========== WALL-CLOCK ({ITERS} warm iters each) ==========");
    for (name, term) in &terms {
        let mut samples = Vec::with_capacity(ITERS);
        for _ in 0..ITERS {
            let t0 = Instant::now();
            let r = CalculatorLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES);
            let dt = t0.elapsed();
            std::hint::black_box(&r);
            samples.push(dt.as_nanos() as u64);
        }
        samples.sort_unstable();
        let min = samples[0];
        let median = samples[samples.len() / 2];
        let p90 = samples[samples.len() * 9 / 10];
        let mean = samples.iter().sum::<u64>() / samples.len() as u64;
        eprintln!(
            "[TIME {name:>7}] min={:>8.3}us median={:>8.3}us p90={:>8.3}us mean={:>8.3}us",
            min as f64 / 1000.0,
            median as f64 / 1000.0,
            p90 as f64 / 1000.0,
            mean as f64 / 1000.0,
        );
    }
}
