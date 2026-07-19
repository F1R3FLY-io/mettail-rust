//! Track B — B6: the JSON-lines COUNTER driver for the naive-vs-optimized
//! matcher benchmark (`bench-naive-baseline` + the three demo-language
//! features; see the `[[bin]]` registration in `Cargo.toml`).
//!
//! One invocation runs `--reps` repetitions of ONE workload cell
//! `(workload, matcher, encoding, n)` and emits, to `--out` (or stdout):
//!
//! 1. ONE run-header JSON line
//!    (`{"header":{git_sha, hostname, scaling_governor, cpus_allowed_list,
//!    unix_time_secs, workload, matcher, encoding, n, reps,
//!    subject_node_count, expected_firings}}`) — the environment record the
//!    pre-registered protocol requires (governor/affinity are READ and
//!    recorded, never changed);
//! 2. one [`BenchRunResult`] JSON line PER REP
//!    (`bench_support::BenchRunResult::to_json_line`: phase timers in ns,
//!    program size, observed count, the bench-local secondary consumed-cost
//!    read, the COMM classification counters, and the spatial match-attempt
//!    counters) — each rep on a FRESH counting runtime, so counters are
//!    per-rep by construction;
//! 3. on a DNF (the 60 s per-rep tokio timeout, the 8 MiB emitted-program
//!    guard, an emitter fail-closed, or an observed-vs-expected mismatch): one
//!    `{"dnf":true,"workload":{…},"reason":"…"}` line, then the driver
//!    CONTINUES with the next rep.
//!
//! The workload registry, generators, drive functions, and verification live
//! in the shared module `benches/support/workloads.rs` (also compiled into the
//! criterion bench `benches/bench_sa_vs_naive.rs`).
//!
//! [`BenchRunResult`]: mettail_rholang_runtime::BenchRunResult

#[path = "../../benches/support/workloads.rs"]
mod workloads;

use std::fs::File;
use std::io::{BufWriter, Write as IoWrite};
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use workloads::{
    cell_width_probe, compile_workload, consume_test_admitted, matcher_admitted, node_count,
    run_compiled_workload, CellWidthProbe, GuardEncodingKind, MatcherKind, WorkloadKind,
    ALL_ENCODINGS, ALL_MATCHERS, ALL_WORKLOADS,
};

/// Per-rep wall-clock DNF guard: a rep that has not reached quiescence within
/// this budget is recorded as `"dnf":true` (reason `timeout-guard`) and the
/// driver continues with the next rep.
const REP_TIMEOUT: Duration = Duration::from_secs(60);

/// The parsed CLI of one driver invocation.
struct DriverArgs {
    workload: WorkloadKind,
    matcher: MatcherKind,
    encoding: GuardEncodingKind,
    n: u64,
    reps: u64,
    out: Option<String>,
}

fn usage() -> String {
    let mut text = String::with_capacity(2048);
    text.push_str(
        "bench_sa_vs_naive_driver — Track-B counter driver (JSON lines)\n\
         \n\
         USAGE:\n  bench_sa_vs_naive_driver --workload <name> --matcher <sa|naive|replay> \\\n    \
         [--encoding <pattern-guard|consume-test>] --n <int> --reps <int> \\\n    \
         [--out <path>] [--format json-lines]\n\
         \n\
         WORKLOADS (full-protocol size ladders; matcher columns):\n",
    );
    for kind in ALL_WORKLOADS {
        let sizes: Vec<String> = kind.full_sizes().iter().map(|n| n.to_string()).collect();
        let matchers: Vec<&str> = kind.matchers().iter().map(|m| m.name()).collect();
        text.push_str(&format!(
            "  {:<14} n ∈ {{{}}}  columns: {}  expected firings at max n: {}\n",
            kind.name(),
            sizes.join(", "),
            matchers.join("+"),
            kind.expected_firings(*kind.full_sizes().last().expect("non-empty ladder")),
        ));
    }
    text.push_str(
        "\nNOTES:\n  --encoding applies to the naive column only (default pattern-guard; \
         consume-test is single-candidate only).\n  --format accepts only json-lines (the \
         default).\n  --out defaults to stdout.\n",
    );
    text
}

/// Resolve a CLI token against a registry by its stable `name()`.
fn resolve<T: Copy>(token: &str, all: &[T], name_of: impl Fn(T) -> &'static str) -> Option<T> {
    all.iter().copied().find(|item| name_of(*item) == token)
}

fn parse_args(args: &[String]) -> Result<DriverArgs, String> {
    let mut workload: Option<WorkloadKind> = None;
    let mut matcher: Option<MatcherKind> = None;
    let mut encoding = GuardEncodingKind::PatternGuard;
    let mut n: Option<u64> = None;
    let mut reps: Option<u64> = None;
    let mut out: Option<String> = None;

    let mut index = 0usize;
    while index < args.len() {
        let flag = args[index].as_str();
        if flag == "--help" || flag == "-h" {
            return Err(usage());
        }
        let value = args
            .get(index + 1)
            .ok_or_else(|| format!("flag {flag} requires a value\n\n{}", usage()))?;
        match flag {
            "--workload" => {
                workload = Some(
                    resolve(value, &ALL_WORKLOADS, WorkloadKind::name)
                        .ok_or_else(|| format!("unknown workload `{value}`\n\n{}", usage()))?,
                );
            },
            "--matcher" => {
                matcher = Some(
                    resolve(value, &ALL_MATCHERS, MatcherKind::name)
                        .ok_or_else(|| format!("unknown matcher `{value}`\n\n{}", usage()))?,
                );
            },
            "--encoding" => {
                encoding = resolve(value, &ALL_ENCODINGS, GuardEncodingKind::name)
                    .ok_or_else(|| format!("unknown encoding `{value}`\n\n{}", usage()))?;
            },
            "--n" => {
                n = Some(
                    value
                        .parse::<u64>()
                        .map_err(|e| format!("--n must be an integer, got `{value}`: {e}"))?,
                );
            },
            "--reps" => {
                reps = Some(
                    value
                        .parse::<u64>()
                        .map_err(|e| format!("--reps must be an integer, got `{value}`: {e}"))?,
                );
            },
            "--out" => {
                out = Some(value.clone());
            },
            "--format" => {
                if value != "json-lines" {
                    return Err(format!("--format supports only json-lines, got `{value}`"));
                }
            },
            other => return Err(format!("unknown flag `{other}`\n\n{}", usage())),
        }
        index += 2;
    }

    let workload = workload.ok_or_else(|| format!("--workload is required\n\n{}", usage()))?;
    let matcher = matcher.ok_or_else(|| format!("--matcher is required\n\n{}", usage()))?;
    let n = n.ok_or_else(|| format!("--n is required\n\n{}", usage()))?;
    let reps = reps.ok_or_else(|| format!("--reps is required\n\n{}", usage()))?;
    if reps == 0 {
        return Err("--reps must be >= 1".to_string());
    }
    workload.admitted_size(n)?;
    if !matcher_admitted(workload, matcher) {
        return Err(format!(
            "matcher `{}` is not a column of workload `{}` (columns: {})",
            matcher.name(),
            workload.name(),
            workload
                .matchers()
                .iter()
                .map(|m| m.name())
                .collect::<Vec<_>>()
                .join(", "),
        ));
    }
    if matcher == MatcherKind::Naive
        && encoding == GuardEncodingKind::ConsumeTest
        && !consume_test_admitted(workload, n)
    {
        return Err(format!(
            "consume-test is single-candidate only: not admitted for `{}` n={n}",
            workload.name(),
        ));
    }
    Ok(DriverArgs { workload, matcher, encoding, n, reps, out })
}

/// Append `value` to `out` with JSON string escaping (quote, backslash, and
/// control characters) — the driver-local mirror of `bench_support`'s
/// serializer discipline for the header/DNF lines.
fn escape_json_into(value: &str, out: &mut String) {
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
}

fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    escape_json_into(value, &mut out);
    out.push('"');
    out
}

/// `git rev-parse HEAD` at RUNTIME, anchored at this crate's manifest directory
/// (stable on the build machine), falling back to `unknown`.
fn git_sha() -> String {
    std::process::Command::new("git")
        .args(["-C", env!("CARGO_MANIFEST_DIR"), "rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|sha| sha.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Read + trim a small pseudo-file (`/proc`, `/sys`), falling back to
/// `unknown` — the protocol RECORDS governor/affinity, it never changes them.
fn read_trimmed(path: &str) -> String {
    std::fs::read_to_string(path)
        .map(|text| text.trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
}

/// The `Cpus_allowed_list` line of `/proc/self/status` — the effective
/// `sched_getaffinity` mask (records any `taskset` pinning).
fn cpus_allowed_list() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status.lines().find_map(|line| {
                line.strip_prefix("Cpus_allowed_list:")
                    .map(|rest| rest.trim().to_string())
            })
        })
        .unwrap_or_else(|| "unknown".to_string())
}

fn header_line(args: &DriverArgs, subject_node_count: usize, probe: &Option<CellWidthProbe>) -> String {
    let unix_time_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|elapsed| elapsed.as_secs())
        .unwrap_or(0);
    let mut line = String::with_capacity(512);
    line.push_str("{\"header\":{\"git_sha\":");
    line.push_str(&json_string(&git_sha()));
    line.push_str(",\"hostname\":");
    line.push_str(&json_string(&read_trimmed("/proc/sys/kernel/hostname")));
    line.push_str(",\"scaling_governor\":");
    line.push_str(&json_string(&read_trimmed(
        "/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor",
    )));
    line.push_str(",\"cpus_allowed_list\":");
    line.push_str(&json_string(&cpus_allowed_list()));
    line.push_str(&format!(",\"unix_time_secs\":{unix_time_secs}"));
    line.push_str(",\"workload\":");
    line.push_str(&json_string(args.workload.name()));
    line.push_str(",\"matcher\":");
    line.push_str(&json_string(args.matcher.name()));
    line.push_str(",\"encoding\":");
    line.push_str(&json_string(match args.matcher {
        MatcherKind::Naive => args.encoding.name(),
        MatcherKind::Sa | MatcherKind::Replay => "-",
    }));
    // `max_eval_width = -1` when the offline probe itself fails closed (the
    // per-rep drive then emits the real reason as dnf lines).
    // `in_split_regression_zone` is PROVENANCE: some injection of this cell
    // has parallel eval width in [129, 256], the formerly-panicking f1r3node
    // split zone — safe on the fixed interpreter (see
    // `INTERPRETER_SPLIT_REGRESSION_MIN` in the shared module), recorded so
    // analysis can tell which cells depend on the fix. (This field replaces
    // the retired `interpreter_split_hazard` fail-closed flag.)
    let (max_eval_width, in_regression_zone) = match probe {
        Some(probe) => (
            i64::try_from(probe.max_eval_width).expect("eval width fits i64"),
            probe.regression_zone_width.is_some(),
        ),
        None => (-1, false),
    };
    line.push_str(&format!(
        ",\"n\":{},\"reps\":{},\"subject_node_count\":{subject_node_count},\
         \"expected_firings\":{},\"max_eval_width\":{max_eval_width},\
         \"in_split_regression_zone\":{in_regression_zone}}}}}",
        args.n,
        args.reps,
        args.workload.expected_firings(args.n),
    ));
    line
}

fn dnf_line(args: &DriverArgs, rep: u64, reason: &str) -> String {
    let mut line = String::with_capacity(256 + reason.len());
    line.push_str("{\"dnf\":true,\"workload\":{\"name\":");
    line.push_str(&json_string(args.workload.name()));
    line.push_str(",\"matcher\":");
    line.push_str(&json_string(args.matcher.name()));
    line.push_str(",\"encoding\":");
    line.push_str(&json_string(match args.matcher {
        MatcherKind::Naive => args.encoding.name(),
        MatcherKind::Sa | MatcherKind::Replay => "-",
    }));
    line.push_str(&format!(",\"n\":{},\"rep\":{rep}}},\"reason\":", args.n));
    line.push_str(&json_string(reason));
    line.push('}');
    line
}

fn main() -> ExitCode {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let args = match parse_args(&raw_args) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        },
    };

    // Demo-language reconstruction shares the process-global var-name cache;
    // clear it once up front (the same discipline as every B2 drive).
    mettail_runtime::clear_var_cache();

    let mut sink: BufWriter<Box<dyn IoWrite>> = match &args.out {
        Some(path) => match File::create(path) {
            Ok(file) => BufWriter::new(Box::new(file)),
            Err(error) => {
                eprintln!("cannot create --out {path}: {error}");
                return ExitCode::from(2);
            },
        },
        None => BufWriter::new(Box::new(std::io::stdout())),
    };
    let emit = |line: &str, sink: &mut BufWriter<Box<dyn IoWrite>>| {
        writeln!(sink, "{line}").expect("write JSON line");
        sink.flush().expect("flush JSON line");
    };

    // The B3 hoist: compile the workload cell ONCE, reuse across reps.
    let compiled = match compile_workload(args.workload, args.n) {
        Ok(compiled) => compiled,
        Err(message) => {
            eprintln!("compile_workload failed: {message}");
            return ExitCode::from(2);
        },
    };
    let probe = cell_width_probe(&compiled, args.matcher, args.encoding).ok();
    emit(&header_line(&args, node_count(&compiled.subject), &probe), &mut sink);
    if let Some(width) = probe.as_ref().and_then(|probe| probe.regression_zone_width) {
        eprintln!(
            "note: one of this cell's injections has parallel eval width {width}, inside the \
             FORMERLY-panicking f1r3node split zone [129, 256] — running against the fixed \
             interpreter (fix/split-byte-width-range: [129, 256] routes through split_short)"
        );
    }

    let mut dnf_count = 0u64;
    let mut emission_total = Duration::ZERO;
    let mut bringup_total = Duration::ZERO;
    for rep in 0..args.reps {
        // ONE tokio current-thread runtime per rep: a timed-out rep's dropped
        // future may have left spawned tasks behind, and dropping the whole
        // runtime discards them — no cross-rep contamination.
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("build the current-thread tokio runtime");
        // Panic guard (belt-and-suspenders under the fail-closed width guard):
        // an interpreter panic inside a rep becomes a dnf line, never a dead
        // protocol file with the remaining reps lost.
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            runtime.block_on(async {
                tokio::time::timeout(
                    REP_TIMEOUT,
                    run_compiled_workload(&compiled, args.matcher, args.encoding, rep),
                )
                .await
            })
        }));
        let outcome = match caught {
            Ok(outcome) => outcome,
            Err(panic_payload) => {
                let rendered = panic_payload
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                    .unwrap_or("non-string panic payload");
                dnf_count += 1;
                emit(&dnf_line(&args, rep, &format!("panic-guard: {rendered}")), &mut sink);
                continue;
            },
        };
        match outcome {
            Ok(Ok(rep_outcome)) => {
                emission_total += rep_outcome.emission;
                bringup_total += rep_outcome.bringup;
                emit(&rep_outcome.result.to_json_line(), &mut sink);
            },
            Ok(Err(failure)) => {
                dnf_count += 1;
                emit(&dnf_line(&args, rep, &failure.reason), &mut sink);
            },
            Err(_elapsed) => {
                dnf_count += 1;
                emit(
                    &dnf_line(
                        &args,
                        rep,
                        &format!("timeout-guard: rep exceeded {}s", REP_TIMEOUT.as_secs()),
                    ),
                    &mut sink,
                );
            },
        }
    }

    // Harness-level phase totals (the JSON lines carry build/inj/readback; the
    // emission + counting-runtime bring-up spans live OUTSIDE those timers).
    // Stderr, so the JSON stream stays pure.
    eprintln!(
        "harness totals across {} reps: emission {:?}, runtime bring-up {:?}",
        args.reps, emission_total, bringup_total
    );

    if dnf_count > 0 {
        eprintln!(
            "{dnf_count}/{} reps did not finish (see the \"dnf\":true lines)",
            args.reps
        );
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

// ─────────────────────────────────────────────────────────────────────────────
// Generator unit tests (subject sizes, expected firing counts, admission pins).
// They live HERE — the driver bin has a libtest harness — because the shared
// module is also compiled into the `harness = false` criterion bench, where a
// `#[cfg(test)]` module would have no harness to anchor it.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod workloads_tests {
    use super::workloads::{
        compile_workload, consume_test_admitted, emit_call, ground_to_observation,
        lambda_chain_subject, matcher_admitted, nested_spine_expected, nested_spine_ruleset,
        nested_spine_subject, node_count, swap_comb_leaf, swap_comb_subject, swap_small_subject,
        wrap_swap_ctx_subject, GuardEncodingKind, MatcherKind, WorkloadKind, ALL_ENCODINGS,
        ALL_MATCHERS, ALL_WORKLOADS, OUT_CHANNEL, ROOT_SITE,
    };
    use mettail_rholang_codegen::{
        contextual_match_call_par, in_rho_match_all_sites_call_par,
        naive_kt_contextual_match_call_par, naive_kt_match_call_par, AutomatonUnsupported,
        GroundTerm, NaiveGuardEncoding,
    };

    /// (i) `lambda_chain(n)`: node count `4n + 1`, expected firings `n`, and
    /// the per-step expected reducts are exactly the remaining chains down to
    /// the terminal `A`.
    #[test]
    fn lambda_chain_generator_pins_size_and_firings() {
        for n in [2usize, 4, 8, 16, 32, 64] {
            let subject = lambda_chain_subject(n);
            assert_eq!(node_count(&subject), 4 * n + 1, "chain n={n} node count");
            assert_eq!(WorkloadKind::LambdaChain.expected_firings(n as u64), n as u64);
        }
        mettail_runtime::clear_var_cache();
        let compiled =
            compile_workload(WorkloadKind::LambdaChain, 4).expect("lambda_chain(4) compiles");
        assert_eq!(compiled.expected.len(), 4, "one reduct per step");
        assert_eq!(
            compiled.expected[3],
            ground_to_observation(&GroundTerm::nullary("A")),
            "the last step lands the terminal normal form A"
        );
        assert_eq!(
            compiled.expected[0],
            ground_to_observation(&lambda_chain_subject(3)),
            "the first step lands the remaining chain of length 3"
        );
    }

    /// (i, admission) The per-step ROOT drives admit on both columns while the
    /// optimized locate-all fails closed on the n ≥ 2 chain (the B0 fact that
    /// forces the per-step discipline).
    #[test]
    fn lambda_chain_admission_root_drives_admit_locate_all_fails_closed() {
        mettail_runtime::clear_var_cache();
        let compiled =
            compile_workload(WorkloadKind::LambdaChain, 2).expect("lambda_chain(2) compiles");
        let ruleset = compiled.ruleset();
        let subject = &compiled.subject;
        assert_eq!(
            in_rho_match_all_sites_call_par(ruleset, subject, ROOT_SITE, OUT_CHANNEL),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "the optimized locate-all fails closed on the n = 2 λ-chain (B0)"
        );
        for matcher in [MatcherKind::Sa, MatcherKind::Naive] {
            let (call, count) = emit_call(
                WorkloadKind::LambdaChain,
                matcher,
                GuardEncodingKind::PatternGuard,
                ruleset,
                subject,
            )
            .expect("the per-step root drive emits on both columns");
            assert!(
                !call.sends.is_empty() || !call.receives.is_empty(),
                "the emitted per-step call is a real process"
            );
            if matcher == MatcherKind::Naive {
                assert_eq!(count, Some(1), "the root-restricted naive drive installs ONE receiver");
            }
        }
    }

    /// (ii) `swap_comb(m)`: m pairwise-distinct redexes AND contracta, pinned
    /// node count, and BOTH columns admit at every full-ladder width (flat
    /// entries co-install contention-free) with exactly m sites.
    #[test]
    fn swap_comb_generator_pins_distinctness_sizes_and_admission() {
        mettail_runtime::clear_var_cache();
        let compiled = compile_workload(WorkloadKind::SwapComb, 4).expect("swap_comb(4) compiles");
        let ruleset = compiled.ruleset();
        for m in [1usize, 2, 4, 8, 16, 32, 64] {
            let (subject, expected) = swap_comb_subject(m);
            // Distinctness: m distinct contracta (the multiset has no repeats).
            let mut renderings: Vec<String> =
                expected.iter().map(|v| format!("{v:?}")).collect();
            renderings.sort();
            renderings.dedup();
            assert_eq!(renderings.len(), m, "m={m}: the contracta are pairwise distinct");
            // Node count: (m − 1) spine Pairs + m Swaps of 2 nullary leaves.
            assert_eq!(node_count(&subject), 4 * m - 1, "m={m} node count");
            assert_eq!(WorkloadKind::SwapComb.expected_firings(m as u64), m as u64);
            // Admission on both columns, with exactly m located/installed sites.
            let (_, sites) =
                in_rho_match_all_sites_call_par(ruleset, &subject, ROOT_SITE, OUT_CHANNEL)
                    .expect("the flat Swap ruleset co-installs at every comb width");
            assert_eq!(sites, m, "m={m}: locate-all finds exactly the m Swap sites");
            let (_, installed) = naive_kt_match_call_par(
                ruleset,
                &subject,
                ROOT_SITE,
                OUT_CHANNEL,
                NaiveGuardEncoding::PatternGuard,
            )
            .expect("the naive comprehension admits every comb width");
            assert_eq!(installed, m, "m={m}: the comprehension installs at the same m sites");
        }
    }

    /// The nullary comb leaves are injective over the widest ladder run
    /// (2 × 64 leaves at m = 64).
    #[test]
    fn comb_leaves_are_pairwise_distinct() {
        let mut renderings: Vec<String> =
            (0..128).map(|i| format!("{:?}", swap_comb_leaf(i))).collect();
        renderings.sort();
        renderings.dedup();
        assert_eq!(renderings.len(), 128, "128 distinct indices ⇒ 128 distinct leaves");
    }

    /// (iv) `swap_small(k)`: node count `2k + 1`, ONE candidate site on both
    /// columns at every k ∈ 1..=8 (including the bare root redex), expected
    /// firing count 1.
    #[test]
    fn swap_small_generator_pins_size_and_single_site_admission() {
        mettail_runtime::clear_var_cache();
        let compiled =
            compile_workload(WorkloadKind::SwapSmall, 1).expect("swap_small(1) compiles");
        let ruleset = compiled.ruleset();
        for k in 1usize..=8 {
            let (subject, expected) = swap_small_subject(k);
            assert_eq!(node_count(&subject), 2 * k + 1, "k={k} node count");
            assert_eq!(expected.len(), 1, "one expected contractum");
            assert_eq!(WorkloadKind::SwapSmall.expected_firings(k as u64), 1);
            let (_, sites) =
                in_rho_match_all_sites_call_par(ruleset, &subject, ROOT_SITE, OUT_CHANNEL)
                    .expect("locate-all admits the single nested Swap at every depth");
            assert_eq!(sites, 1, "k={k}: exactly one located site");
            let (_, installed) = naive_kt_match_call_par(
                ruleset,
                &subject,
                ROOT_SITE,
                OUT_CHANNEL,
                NaiveGuardEncoding::PatternGuard,
            )
            .expect("the naive comprehension admits the single nested Swap");
            assert_eq!(installed, 1, "k={k}: exactly one installed receiver");
        }
    }

    /// (v) `wrap_swap_ctx`: depth 1 admits on BOTH contextual emitters; depth 2
    /// FAILS CLOSED on both (the single-congruence hole bijection) — the pin
    /// behind `WorkloadKind::admitted_size`'s `{1}` ladder.
    #[test]
    fn wrap_swap_ctx_depth_two_fails_closed_on_both_emitters() {
        mettail_runtime::clear_var_cache();
        let compiled =
            compile_workload(WorkloadKind::WrapSwapCtx, 1).expect("wrap_swap_ctx(1) compiles");
        let ruleset = compiled.ruleset();

        let (depth1, expected1) = wrap_swap_ctx_subject(1);
        // Wrap + Swap + A + B (depth d ⇒ d + 3 nodes).
        assert_eq!(node_count(&depth1), 4, "Wrap(Swap(A, B)) is 4 nodes");
        assert_eq!(expected1.len(), 1);
        contextual_match_call_par(ruleset, &depth1, ROOT_SITE, OUT_CHANNEL)
            .expect("the optimized contextual driver admits depth 1");
        naive_kt_contextual_match_call_par(
            ruleset,
            &depth1,
            ROOT_SITE,
            OUT_CHANNEL,
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the naive contextual driver admits depth 1");

        let (depth2, _) = wrap_swap_ctx_subject(2);
        assert!(
            contextual_match_call_par(ruleset, &depth2, ROOT_SITE, OUT_CHANNEL).is_err(),
            "depth 2 fails closed on the optimized contextual driver"
        );
        assert!(
            naive_kt_contextual_match_call_par(
                ruleset,
                &depth2,
                ROOT_SITE,
                OUT_CHANNEL,
                NaiveGuardEncoding::PatternGuard,
            )
            .is_err(),
            "depth 2 fails closed on the naive contextual driver"
        );
        assert!(
            WorkloadKind::WrapSwapCtx.admitted_size(2).is_err(),
            "the registry rejects depth 2 up front"
        );
    }

    /// (vi) `nested_spine(k)`: node count `4k − 1`, k pairwise-distinct
    /// expected leaves, the naive comprehension installs exactly k receivers,
    /// the optimized locate-all fails closed for k ≥ 2 (the divergent-admission
    /// regime that makes REPLAY the honest production column), and the replay
    /// emitter fires exactly k ground accept sends.
    #[test]
    fn nested_spine_generator_pins_sizes_and_divergent_admission() {
        let ruleset = nested_spine_ruleset();
        for k in [2usize, 4, 8, 16] {
            let (subject, expected) = nested_spine_subject(k);
            assert_eq!(node_count(&subject), 4 * k - 1, "k={k} node count");
            assert_eq!(expected.len(), k);
            assert_eq!(WorkloadKind::NestedSpine.expected_firings(k as u64), k as u64);
            assert_eq!(nested_spine_expected(WorkloadKind::NestedSpine, &subject), k as u64);
            assert_eq!(
                in_rho_match_all_sites_call_par(&ruleset, &subject, ROOT_SITE, OUT_CHANNEL),
                Err(AutomatonUnsupported::NestedEntryMultiSite),
                "k={k}: the optimized locate-all fails closed on nested multi-site (B0)"
            );
            let (_, installed) = naive_kt_match_call_par(
                &ruleset,
                &subject,
                ROOT_SITE,
                OUT_CHANNEL,
                NaiveGuardEncoding::PatternGuard,
            )
            .expect("the naive comprehension admits the nested spine");
            assert_eq!(installed, k, "k={k}: one naive receiver per head-f site");
            let (replay_call, count) = emit_call(
                WorkloadKind::NestedSpine,
                MatcherKind::Replay,
                GuardEncodingKind::PatternGuard,
                &ruleset,
                &subject,
            )
            .expect("the replay emitter always admits (host-side matching)");
            assert_eq!(count, Some(k));
            assert_eq!(
                replay_call.sends.len(),
                k,
                "k={k}: one ground accept send per host-computed firing"
            );
            assert!(replay_call.receives.is_empty(), "the replay call installs no matching");
        }
    }

    /// The registry matrices: matcher columns per workload and the
    /// single-candidate `ConsumeTest` admission.
    #[test]
    fn registry_matrices_are_pinned() {
        assert_eq!(
            WorkloadKind::LambdaChain.matchers(),
            &[MatcherKind::Sa, MatcherKind::Naive]
        );
        assert_eq!(
            WorkloadKind::NestedSpine.matchers(),
            &[MatcherKind::Naive, MatcherKind::Replay]
        );
        assert!(matcher_admitted(WorkloadKind::SwapComb, MatcherKind::Sa));
        assert!(!matcher_admitted(WorkloadKind::SwapComb, MatcherKind::Replay));
        assert!(!matcher_admitted(WorkloadKind::NestedSpine, MatcherKind::Sa));

        assert!(consume_test_admitted(WorkloadKind::SwapSmall, 8));
        assert!(consume_test_admitted(WorkloadKind::LambdaChain, 64));
        assert!(consume_test_admitted(WorkloadKind::WrapSwapCtx, 1));
        assert!(consume_test_admitted(WorkloadKind::SwapComb, 1));
        assert!(!consume_test_admitted(WorkloadKind::SwapComb, 2));
        assert!(!consume_test_admitted(WorkloadKind::NestedSpine, 2));

        for kind in ALL_WORKLOADS {
            for &n in kind.full_sizes() {
                kind.admitted_size(n).expect("every full-ladder size is admitted");
            }
        }
        assert!(WorkloadKind::SwapComb.admitted_size(0).is_err(), "n = 0 is rejected");
    }

    /// The FORMERLY-panicking f1r3node `split_byte(i8)` zone (parallel eval
    /// width 129..=256 at ANY single eval level — see the regression
    /// constants' rustdoc in the shared module), FIXED on the f1r3node branch
    /// `fix/split-byte-width-range` (commit 31b354e6: [129, 256] routes
    /// through `split_short(i16)`; widths ≤ 128 byte-identical): the SMOKE
    /// cells are all far below the zone, and the full-ladder in-zone cells
    /// are EXACTLY pinned — the λ-chain ladder n ∈ {16, 32, 64} (per-step
    /// width is 10 + 9·links, so every chain n ≥ 14 passes through in-zone
    /// steps at 14–27 links remaining, widths 136–253), `swap_comb` n = 16
    /// (width 175), and `nested_spine` naive n = 16 (width 174). Those cells
    /// now RUN — the pin is the regression ASSERTION documenting exactly
    /// which ladder cells exercise (and depend on) the fixed `split_short`
    /// routing, and `interpreter_split_regression_width_129_evaluates` below
    /// proves the zone actually evaluates; every other pinned cell stays
    /// clear of the zone (n = 32/64 single-injection cells exceed 256 and
    /// take the always-safe `split_short(i16)` branch).
    #[test]
    fn interpreter_split_regression_zone_cells_are_pinned_and_smoke_cells_are_clear() {
        use super::workloads::{cell_width_probe, ALL_WORKLOADS};
        mettail_runtime::clear_var_cache();

        // Smoke cells (smoke.sh): every one must be OUTSIDE the zone.
        let smoke_cells: [(WorkloadKind, u64); 5] = [
            (WorkloadKind::LambdaChain, 2),
            (WorkloadKind::SwapComb, 4),
            (WorkloadKind::NestedSpine, 2),
            (WorkloadKind::SwapSmall, 2),
            (WorkloadKind::WrapSwapCtx, 1),
        ];
        for (kind, n) in smoke_cells {
            let compiled = compile_workload(kind, n).expect("smoke cell compiles");
            for &matcher in kind.matchers() {
                let probe =
                    cell_width_probe(&compiled, matcher, GuardEncodingKind::PatternGuard)
                        .expect("smoke cell emits");
                assert_eq!(
                    probe.regression_zone_width,
                    None,
                    "smoke cell {}/{} n={n} has an injection INSIDE the regression zone \
                     (max width {})",
                    kind.name(),
                    matcher.name(),
                    probe.max_eval_width,
                );
            }
        }

        // Full-ladder probe: collect and PIN the in-zone cells (the protocol
        // documents these as the cells whose results depend on the fixed
        // interpreter; before the fix they failed closed — the
        // empirically-observed gate-3 panic was lambda_chain/16).
        let mut in_zone_cells: Vec<String> = Vec::new();
        for kind in ALL_WORKLOADS {
            for &n in kind.full_sizes() {
                let compiled = compile_workload(kind, n).expect("full-ladder cell compiles");
                for &matcher in kind.matchers() {
                    let probe =
                        cell_width_probe(&compiled, matcher, GuardEncodingKind::PatternGuard)
                            .expect("full-ladder cell emits");
                    println!(
                        "width {}/{} n={n}: max {}{}",
                        kind.name(),
                        matcher.name(),
                        probe.max_eval_width,
                        match probe.regression_zone_width {
                            Some(width) =>
                                format!("  << REGRESSION ZONE (injection width {width})"),
                            None => String::new(),
                        },
                    );
                    if probe.regression_zone_width.is_some() {
                        in_zone_cells.push(format!("{}/{}/{n}", kind.name(), matcher.name()));
                    }
                }
            }
        }
        assert_eq!(
            in_zone_cells,
            [
                "lambda_chain/sa/16",
                "lambda_chain/naive/16",
                "lambda_chain/sa/32",
                "lambda_chain/naive/32",
                "lambda_chain/sa/64",
                "lambda_chain/naive/64",
                "swap_comb/sa/16",
                "swap_comb/naive/16",
                "nested_spine/naive/16",
            ],
            "the pinned full-ladder regression-zone cell set changed — update the protocol \
             docs (README.md) alongside this pin"
        );
    }

    /// The fast ACTUAL-EVAL regression spot check for the formerly-panicking
    /// f1r3node split zone: a Par of 129 parallel sends (the zone's first
    /// width, `INTERPRETER_SPLIT_REGRESSION_MIN`) is injected on a real
    /// counting runtime and must reach quiescence. On the unfixed interpreter
    /// this panicked with `TryFromIntError(PosOverflow)` at term index 128
    /// (`split_byte(i8)` in reduce.rs); on the fixed interpreter (f1r3node
    /// branch `fix/split-byte-width-range`, commit 31b354e6) it routes
    /// through `split_short(i16)`.
    #[test]
    fn interpreter_split_regression_width_129_evaluates() {
        use super::workloads::INTERPRETER_SPLIT_REGRESSION_MIN;
        use crypto::rust::hash::blake2b512_random::Blake2b512Random;
        use mettail_rholang_runtime::bench_runtime_with_counters;
        use models::rhoapi::{Par, Send};
        use models::rust::utils::new_gint_par;
        use rho_pure_eval::Env;
        use rholang::rust::interpreter::accounting::costs::Cost;
        use rholang::rust::interpreter::accounting::has_cost::HasCost;
        use rholang::rust::interpreter::rho_runtime::RhoRuntime;

        let width = INTERPRETER_SPLIT_REGRESSION_MIN; // 129
        let mut sends: Vec<Send> = Vec::with_capacity(width);
        for i in 0..width {
            sends.push(Send {
                chan: Some(new_gint_par(i as i64, Vec::new(), false)),
                data: vec![new_gint_par(i as i64, Vec::new(), false)],
                persistent: false,
                locally_free: Vec::new(),
                connective_used: false,
            });
        }
        let mut wide_par = Par::default();
        wide_par.sends = sends;

        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("build the current-thread tokio runtime");
        runtime.block_on(async {
            let (rho_runtime, _comm_counters, _match_counters) =
                bench_runtime_with_counters(Vec::new(), OUT_CHANNEL)
                    .await
                    .expect("counting runtime bring-up");
            // The same per-injection funding `bench_inj_and_read` performs
            // (mirrors `inj_on_runtime`'s `Cost::unsafe_max()`).
            rho_runtime.cost().set(Cost::unsafe_max());
            rho_runtime
                .inj(wide_par, Env::new(), Blake2b512Random::create_from_bytes(&[]))
                .await
                .expect(
                    "width-129 Par must evaluate without the split_byte(i8) PosOverflow panic",
                );
        });
    }

    /// The stable names round-trip through the registries (the driver's CLI
    /// resolves tokens by scanning these).
    #[test]
    fn registry_names_are_stable() {
        let names: Vec<&str> = ALL_WORKLOADS.iter().map(|w| w.name()).collect();
        assert_eq!(
            names,
            ["lambda_chain", "swap_comb", "swap_small", "wrap_swap_ctx", "nested_spine"]
        );
        let matchers: Vec<&str> = ALL_MATCHERS.iter().map(|m| m.name()).collect();
        assert_eq!(matchers, ["sa", "naive", "replay"]);
        let encodings: Vec<&str> = ALL_ENCODINGS.iter().map(|e| e.name()).collect();
        assert_eq!(encodings, ["pattern-guard", "consume-test"]);
    }
}
