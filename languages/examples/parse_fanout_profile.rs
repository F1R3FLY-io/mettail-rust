//! Stage-2 isolation profile (task #10, step_fanout parallelization gate).
//!
//! Parses ONLY the cast-then-compare frontier-explosion inputs (the `~K^depth`
//! fan-out regime) in a tight loop, with NO light/lexing-dominated inputs, so a
//! perf profile attributes self-time to the fan-out machinery in isolation. If
//! `step_fanout`/`apply_action_to_cursor`/GSS ops are still not the dominant
//! in-parse self-time HERE — the best case for them being hot — the staged
//! parallelization design STOPs at Stage 2 with a data-backed finding.
//!
//! Run: `ITERS=400 taskset -c 4 perf record -e task-clock -F 1999 \
//!        --call-graph dwarf -- target/release/examples/parse_fanout_profile-*`

use mettail_languages::calculator::Bool;

fn main() {
    let iters: usize = std::env::var("ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(200);

    // The pure fan-out regime: cast-then-compare towers whose compare
    // continuation explodes the cursor frontier ~K^depth (cast_tower_bench
    // idx 4 and 6, the HEAVY tier). No bare casts / no light inputs.
    let inputs = ["int(float(int(3.14))) == 3", "int(float(int(float(int(3.14))))) == 3"];

    // Warm-up (untimed lazy inits).
    for inp in &inputs {
        mettail_runtime::clear_var_cache();
        let _ = Bool::parse(inp);
    }

    let mut ok = 0usize;
    for _ in 0..iters {
        for inp in &inputs {
            mettail_runtime::clear_var_cache();
            if Bool::parse(inp).is_ok() {
                ok += 1;
            }
        }
    }
    // Prevent the optimizer from eliding the parses.
    println!("parsed_ok={}", ok);
}
