//! E-8a (pgmcp experiment 170) — the corrective JSON-lines timing driver for the
//! native `PathMap<Par>` subject-index treatment vs the current spread+drive control
//! (`bench-naive-baseline` + the demo-language features; see the `[[bin]]`
//! registration in `Cargo.toml`).
//!
//! One invocation runs `--reps` repetitions of ONE cell `(workload, arm, n)`
//! and emits, to `--out` (or stdout):
//!
//! 1. ONE run-header JSON line (`{"e6a_header":{…}}`) — git sha, hostname,
//!    governor, affinity, cell identity, and the cell's STATIC spread-send
//!    counts for both arms;
//! 2. one `{"e6a_rep":{…}}` JSON line PER REP — including the pre-registered
//!    PRIMARY timing source `inj_ns` (recorded as `inj_ms_per_normalization` in
//!    pgmcp), plus the diagnostic counter
//!    `spread_plus_matching_comms_per_normalization` (control: static spread
//!    sends + `matching_tau` COMMs; treatment: the 1+#ops index/discovery sends
//!    + `pathmap_index` COMMs), the full COMM classification snapshot, spatial
//!    match-attempt counters, the bench-local consumed-cost read, phase
//!    timers, program sizes, and (treatment) the machine-enumerated site
//!    counts per op. The first `--warmups` reps are flagged
//!    `"is_warmup":true` (recorded, excluded from analysis);
//! 3. on a DNF: one `{"dnf":true,…}` line, then the driver continues.
//!
//! Every rep runs on FRESH counting runtime(s) (per-step for `lambda_chain`),
//! under a per-rep tokio timeout and a panic guard.

// `dead_code` is wrong HERE: `workloads.rs` is ONE support module shared by FOUR
// consumers through `#[path]` (this file, the sibling bench, and the two driver
// bins), and each needs a different subset of the workload registry. The lint sees
// only this consumer, so every item the OTHER three use reads as dead. The module
// is not a dependency because a `[dev-dependencies]` crate cannot be shared with a
// `src/bin` target — one source, four consumers.
#[allow(dead_code)]
#[path = "../../benches/support/workloads.rs"]
mod workloads;

use std::fs::File;
use std::io::{BufWriter, Write as IoWrite};
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use workloads::{
    compile_workload, e6a_control_matcher, e6a_control_spread_sends, run_compiled_workload,
    run_e6a_treatment_workload, CompiledWorkload, GuardEncodingKind, MatcherKind, WorkloadKind,
    ALL_WORKLOADS,
};

use mettail_rholang_runtime::{BenchRunResult, CommCounterSnapshot, MatchAttemptSnapshot};

/// Per-rep wall-clock DNF guard.
const REP_TIMEOUT: Duration = Duration::from_secs(120);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Arm {
    Control,
    Treatment,
}

impl Arm {
    fn name(self) -> &'static str {
        match self {
            Arm::Control => "control",
            Arm::Treatment => "treatment",
        }
    }
}

struct DriverArgs {
    workload: WorkloadKind,
    arm: Arm,
    n: u64,
    reps: u64,
    warmups: u64,
    out: Option<String>,
}

fn usage() -> String {
    let mut text = String::with_capacity(1024);
    text.push_str(
        "bench_e6a_pathmap_driver — E-6a PathMap-index counter driver (JSON lines)\n\n\
         USAGE:\n  bench_e6a_pathmap_driver --workload <name> --arm <control|treatment> \\\n    \
         --n <int> --reps <int> [--warmups <int, default 3>] [--out <path>]\n\n\
         E-6a corpus cells (pre-registered):\n  \
         swap_comb n ∈ {4, 16, 64} · multi_rule_shared n ∈ {402, 803} · \
         nested_spine n ∈ {2, 8, 16} · lambda_chain n ∈ {4, 8}\n\n\
         Control columns: swap_comb/multi_rule_shared/lambda_chain = sa; nested_spine = naive.\n",
    );
    text.push_str("Workload registry: ");
    for kind in ALL_WORKLOADS {
        text.push_str(kind.name());
        text.push(' ');
    }
    text.push('\n');
    text
}

fn parse_args(args: &[String]) -> Result<DriverArgs, String> {
    let mut workload: Option<WorkloadKind> = None;
    let mut arm: Option<Arm> = None;
    let mut n: Option<u64> = None;
    let mut reps: Option<u64> = None;
    let mut warmups: u64 = 3;
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
                workload = ALL_WORKLOADS
                    .iter()
                    .copied()
                    .find(|kind| kind.name() == value);
                if workload.is_none() {
                    return Err(format!("unknown workload `{value}`\n\n{}", usage()));
                }
            },
            "--arm" => {
                arm = match value.as_str() {
                    "control" => Some(Arm::Control),
                    "treatment" => Some(Arm::Treatment),
                    other => return Err(format!("unknown arm `{other}`\n\n{}", usage())),
                };
            },
            "--n" => {
                n = Some(value.parse::<u64>().map_err(|e| format!("--n: {e}"))?);
            },
            "--reps" => {
                reps = Some(value.parse::<u64>().map_err(|e| format!("--reps: {e}"))?);
            },
            "--warmups" => {
                warmups = value
                    .parse::<u64>()
                    .map_err(|e| format!("--warmups: {e}"))?;
            },
            "--out" => out = Some(value.clone()),
            other => return Err(format!("unknown flag `{other}`\n\n{}", usage())),
        }
        index += 2;
    }
    let workload = workload.ok_or_else(|| format!("--workload is required\n\n{}", usage()))?;
    let arm = arm.ok_or_else(|| format!("--arm is required\n\n{}", usage()))?;
    let n = n.ok_or_else(|| format!("--n is required\n\n{}", usage()))?;
    let reps = reps.ok_or_else(|| format!("--reps is required\n\n{}", usage()))?;
    if reps == 0 {
        return Err("--reps must be >= 1".to_string());
    }
    workload.admitted_size(n)?;
    if e6a_control_matcher(workload).is_none() {
        return Err(format!("workload `{}` is out of E-6a scope", workload.name()));
    }
    Ok(DriverArgs { workload, arm, n, reps, warmups, out })
}

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

fn read_trimmed(path: &str) -> String {
    std::fs::read_to_string(path)
        .map(|text| text.trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
}

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

fn header_line(args: &DriverArgs, control_spread_sends: usize) -> String {
    let unix_time_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|elapsed| elapsed.as_secs())
        .unwrap_or(0);
    format!(
        "{{\"e6a_header\":{{\"experiment\":170,\"git_sha\":{},\"hostname\":{},\
         \"scaling_governor\":{},\"cpus_allowed_list\":{},\"unix_time_secs\":{unix_time_secs},\
         \"workload\":{},\"arm\":{},\"n\":{},\"reps\":{},\"warmups\":{},\
         \"control_matcher\":{},\"control_spread_sends_static\":{control_spread_sends}}}}}",
        json_string(&git_sha()),
        json_string(&read_trimmed("/proc/sys/kernel/hostname")),
        json_string(&read_trimmed("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")),
        json_string(&cpus_allowed_list()),
        json_string(args.workload.name()),
        json_string(args.arm.name()),
        args.n,
        args.reps,
        args.warmups,
        json_string(e6a_control_matcher(args.workload).expect("in scope").name()),
    )
}

fn dnf_line(args: &DriverArgs, rep: u64, reason: &str) -> String {
    format!(
        "{{\"dnf\":true,\"workload\":{},\"arm\":{},\"n\":{},\"rep\":{rep},\"reason\":{}}}",
        json_string(args.workload.name()),
        json_string(args.arm.name()),
        args.n,
        json_string(reason),
    )
}

fn comm_json(comm: &CommCounterSnapshot) -> String {
    format!(
        "{{\"matching_tau\":{},\"firing_visible\":{},\"subst_tau\":{},\"respread_tau\":{},\
         \"ac_carrier\":{},\"pathmap_index\":{},\"contextual_plumbing\":{},\"observation\":{},\
         \"other\":{},\"join_arity_gt1\":{}}}",
        comm.matching_tau,
        comm.firing_visible,
        comm.subst_tau,
        comm.respread_tau,
        comm.ac_carrier,
        comm.pathmap_index,
        comm.contextual_plumbing,
        comm.observation,
        comm.other,
        comm.join_arity_gt1,
    )
}

#[allow(clippy::too_many_arguments)]
fn rep_line(
    args: &DriverArgs,
    rep: u64,
    is_warmup: bool,
    result: &BenchRunResult,
    matches: &MatchAttemptSnapshot,
    spread_sends: usize,
    matching_comms: u64,
    machine_sites_json: &str,
    emission: Duration,
    bringup: Duration,
) -> String {
    let spread_plus_matching_comms = spread_sends as u64 + matching_comms;
    format!(
        "{{\"e6a_rep\":{{\"workload\":{},\"arm\":{},\"n\":{},\"rep\":{rep},\
         \"is_warmup\":{is_warmup},\
         \"spread_sends\":{spread_sends},\"matching_comms\":{matching_comms},\
         \"spread_plus_matching_comms_per_normalization\":{spread_plus_matching_comms},\
         \"comm\":{},\"attempts\":{},\"successes\":{},\"consumed_cost_units\":{},\
         \"observed_count\":{},\"build_ns\":{},\"inj_ns\":{},\"readback_ns\":{},\
         \"emission_ns\":{},\"bringup_ns\":{},\
         \"program_encoded_len\":{},\"program_receiver_count\":{},\
         \"machine_sites\":{machine_sites_json}}}}}",
        json_string(args.workload.name()),
        json_string(args.arm.name()),
        args.n,
        comm_json(&result.comm),
        matches.attempts,
        matches.successes,
        result.consumed_cost_units,
        result.observed.len(),
        result.build.as_nanos(),
        result.inj.as_nanos(),
        result.readback.as_nanos(),
        emission.as_nanos(),
        bringup.as_nanos(),
        result.program_encoded_len,
        result.program_receiver_count,
    )
}

/// One rep on one fresh current-thread tokio runtime, panic-guarded and
/// timeout-guarded, emitting either a rep line or a DNF line.
fn run_rep(
    args: &DriverArgs,
    compiled: &CompiledWorkload,
    control_spread_sends: usize,
    rep: u64,
    is_warmup: bool,
) -> Result<String, String> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("build the current-thread tokio runtime");
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        runtime.block_on(async {
            match args.arm {
                Arm::Control => {
                    let matcher: MatcherKind =
                        e6a_control_matcher(args.workload).expect("in scope");
                    tokio::time::timeout(
                        REP_TIMEOUT,
                        run_compiled_workload(
                            compiled,
                            matcher,
                            GuardEncodingKind::PatternGuard,
                            rep,
                        ),
                    )
                    .await
                    .map_err(|_| format!("timeout-guard: rep exceeded {}s", REP_TIMEOUT.as_secs()))
                    .and_then(|outcome| outcome.map_err(|failure| failure.reason))
                    .map(|outcome| {
                        rep_line(
                            args,
                            rep,
                            is_warmup,
                            &outcome.result,
                            &outcome.result.matches.clone(),
                            control_spread_sends,
                            outcome.result.comm.matching_tau,
                            "{}",
                            outcome.emission,
                            outcome.bringup,
                        )
                    })
                },
                Arm::Treatment => {
                    tokio::time::timeout(REP_TIMEOUT, run_e6a_treatment_workload(compiled, rep))
                        .await
                        .map_err(|_| {
                            format!("timeout-guard: rep exceeded {}s", REP_TIMEOUT.as_secs())
                        })
                        .and_then(|outcome| outcome.map_err(|failure| failure.reason))
                        .map(|outcome| {
                            let mut sites_json = String::from("{");
                            for (index, (op, sites)) in outcome.machine_sites.iter().enumerate() {
                                if index > 0 {
                                    sites_json.push(',');
                                }
                                sites_json.push_str(&json_string(op));
                                sites_json.push(':');
                                sites_json.push_str(&sites.len().to_string());
                            }
                            sites_json.push('}');
                            rep_line(
                                args,
                                rep,
                                is_warmup,
                                &outcome.result,
                                &outcome.result.matches.clone(),
                                outcome.treatment_spread_sends,
                                outcome.result.comm.pathmap_index,
                                &sites_json,
                                outcome.emission,
                                outcome.bringup,
                            )
                        })
                },
            }
        })
    }));
    match caught {
        Ok(result) => result,
        Err(panic_payload) => {
            let rendered = panic_payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                .unwrap_or("non-string panic payload");
            Err(format!("panic-guard: {rendered}"))
        },
    }
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

    let compiled = match compile_workload(args.workload, args.n) {
        Ok(compiled) => compiled,
        Err(message) => {
            eprintln!("compile_workload failed: {message}");
            return ExitCode::from(2);
        },
    };
    let control_spread_sends = e6a_control_spread_sends(&compiled);
    emit(&header_line(&args, control_spread_sends), &mut sink);

    let mut dnf_count = 0u64;
    for rep in 0..args.reps {
        let is_warmup = rep < args.warmups;
        match run_rep(&args, &compiled, control_spread_sends, rep, is_warmup) {
            Ok(line) => emit(&line, &mut sink),
            Err(reason) => {
                dnf_count += 1;
                emit(&dnf_line(&args, rep, &reason), &mut sink);
            },
        }
    }

    if dnf_count > 0 {
        eprintln!("{dnf_count}/{} reps did not finish", args.reps);
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
