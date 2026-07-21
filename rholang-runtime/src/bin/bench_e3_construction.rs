//! E-3 (lazy/incremental set-automaton construction) — the JSON-lines construction
//! driver (`bench-e3-construction` feature; see the `[[bin]]` registration in
//! `Cargo.toml`).
//!
//! One invocation runs `--warmup + --reps` repetitions of ONE cell and emits, to
//! `--out` (or stdout):
//!
//! 1. ONE run-header JSON line (`{"header":{git_sha, hostname, scaling_governor,
//!    cpus_allowed_list, unix_time_secs, mode, workload, r, shape, alphabet,
//!    source_bytes, pattern_nodes, warmup, reps, rust_min_stack}}`) — the environment
//!    record the pre-registered protocol requires (governor/affinity are READ and
//!    recorded, never changed);
//! 2. one JSON line PER RECORDED REP (warmup reps run identically but are not
//!    emitted), each rep on a FRESH thread — a fresh `thread_local!` artifact cache,
//!    so every rep is a true first touch by construction:
//!    * `--mode spans` — the Stage-0 phase-split cell: the full EAGER pipeline
//!      sequence under SELF-time span collection
//!      (`{"spans":{rep, wall_ns, installed_ok, mismatched_spans, self_ns_sum,
//!      phases:[{phase, activations, self_ns, total_ns} × 6]}}`). SELF time is the
//!      partition (the phases re-enter — EM-4); `total_ns` overlaps by design.
//!    * `--mode direct` — the W-A(b) entry mode: `SetAutomaton::compile_structural`
//!      alone on the ladder's pattern set
//!      (`{"direct":{rep, wall_ns, entry_count, state_count, pattern_nodes}}`).
//!    * `--mode h2 --arm <eager-control|lazy-gate-only|lazy-force-installed>` — one
//!      H2v2 first-touch arm (EM-1; ONE arm per invocation, per the one-cell-per-run
//!      protocol): `{"h2":{rep, arm, wall_ns, installed_ok,
//!      forced:{lowered, ruleset, installed_par}}}` (`installed_ok`/`forced` are `null`
//!      on the eager-control arm, which has no cells). A lazy rep whose cell-state
//!      validation fails (a forcing set that does not match its arm) is a DNF line.
//! 3. on a failure (a source that does not reconstruct): one
//!    `{"dnf":true,"reason":…}` line, then the driver CONTINUES with the next rep.
//!
//! Workload registry, generators, and cell runners live in the shared module
//! `benches/support/e3_construction.rs`. Measurement discipline (pinning, governor,
//! settle) is the CALLER's job; this bin only records what it sees.

#[path = "../../benches/support/e3_construction.rs"]
mod e3_construction;

use std::fs::File;
use std::io::{BufWriter, Write as IoWrite};
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use e3_construction::{
    in_fresh_thread, ladder_patterns, ladder_source, pattern_node_count, run_direct_compile_once,
    run_e6b_rep, run_eager_control_once, run_gate_cases_for, run_lazy_force_installed_once,
    run_lazy_gate_only_once, run_spans_once, run_wb_rep, validate_ladder_cell, AnchorLanguage,
    E6bStoreArm, LadderAlphabet, LadderShape, LazyCell, WbPolicy, ALL_ANCHORS, DEFAULT_LADDER_R,
};

/// The driver's cell modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    /// Stage-0 phase-split: the eager pipeline under SELF-time span collection.
    Spans,
    /// W-A(b): direct `compile_structural` on the ladder pattern set.
    Direct,
    /// One H2v2 first-touch arm (EM-1; requires `--arm`).
    H2,
    /// W-B extension ladder (H3v2, E-3 T-INCR): K single-rewrite appends over the
    /// ladder base under ONE policy (requires `--policy`; `--appends` defaults to
    /// the frozen K = 50).
    Wb,
    /// The pre-registered H3v2 equivalence gate at `--r` (all four cases, once per
    /// invocation) — MUST pass before any W-B cell is measured (a failure voids the
    /// incremental arm and exits non-zero).
    WbGate,
    /// T-E6B (H4v2): the W-B incremental extension ladder PLUS the
    /// construction-side fragment store under ONE store arm (requires `--store`;
    /// `--appends` defaults to the frozen K = 50). Emits one line per append
    /// (wall + the observed invalidation components) and one deterministic
    /// retention summary per rep. The H3v2 equivalence-gate discipline carries:
    /// `--mode wb-gate` must pass on the same tree BEFORE any e6b cell.
    E6b,
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Spans => "spans",
            Mode::Direct => "direct",
            Mode::H2 => "h2",
            Mode::Wb => "wb",
            Mode::WbGate => "wb-gate",
            Mode::E6b => "e6b",
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        [Mode::Spans, Mode::Direct, Mode::H2, Mode::Wb, Mode::WbGate, Mode::E6b]
            .into_iter()
            .find(|mode| mode.name() == name)
    }
}

/// The H2v2 arms (support-module docs: the EM-1 arm table).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum H2Arm {
    /// The pre-T-LAZY eager pipeline sequence — the control.
    EagerControl,
    /// Cache first-touch + `ruleset()` — the exec/gate forcing set (the win state).
    LazyGateOnly,
    /// Cache first-touch + `ruleset()` + `installed_par()` — the named forcing consumer
    /// (the ≤ 2% full-path guard state).
    LazyForceInstalled,
}

impl H2Arm {
    fn name(self) -> &'static str {
        match self {
            H2Arm::EagerControl => "eager-control",
            H2Arm::LazyGateOnly => "lazy-gate-only",
            H2Arm::LazyForceInstalled => "lazy-force-installed",
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        [H2Arm::EagerControl, H2Arm::LazyGateOnly, H2Arm::LazyForceInstalled]
            .into_iter()
            .find(|arm| arm.name() == name)
    }

    /// The arm's REQUIRED post-rep cell states `(lowered, ruleset, installed_par)`
    /// (`None` for the cell-free control arm) — a lazy rep observing anything else is a
    /// DNF.
    fn required_forcing(self) -> Option<(bool, bool, bool)> {
        match self {
            H2Arm::EagerControl => None,
            H2Arm::LazyGateOnly => Some((false, true, false)),
            H2Arm::LazyForceInstalled => Some((true, true, true)),
        }
    }
}

/// The workload of one invocation: a W-C anchor or one W-A ladder cell.
#[derive(Clone, Copy, Debug)]
enum Workload {
    Anchor(AnchorLanguage),
    Ladder { r: usize, shape: LadderShape, alphabet: LadderAlphabet },
}

impl Workload {
    fn name(self) -> String {
        match self {
            Workload::Anchor(anchor) => anchor.name().to_string(),
            Workload::Ladder { .. } => "ladder".to_string(),
        }
    }
}

/// The parsed CLI of one driver invocation.
struct DriverArgs {
    mode: Mode,
    workload: Workload,
    /// The H2v2 arm (`Some` exactly when `mode == Mode::H2`).
    arm: Option<H2Arm>,
    /// The W-B policy (`Some` exactly when `mode == Mode::Wb`).
    policy: Option<WbPolicy>,
    /// The T-E6B store arm (`Some` exactly when `mode == Mode::E6b`).
    store: Option<E6bStoreArm>,
    /// The W-B / T-E6B append count K (frozen default 50).
    appends: u64,
    warmup: u64,
    reps: u64,
    out: Option<String>,
}

fn usage() -> String {
    let anchors: Vec<&str> = ALL_ANCHORS.iter().map(|anchor| anchor.name()).collect();
    let ladder: Vec<String> = DEFAULT_LADDER_R.iter().map(|r| r.to_string()).collect();
    format!(
        "bench_e3_construction — E-3 construction-cost driver (JSON lines)\n\
         \n\
         USAGE:\n  bench_e3_construction --mode <spans|direct|h2|wb|wb-gate|e6b> --workload <name> \\\n    \
         [--arm <eager-control|lazy-gate-only|lazy-force-installed>] \\\n    \
         [--policy <incremental|full>] [--store <pathmap|hashmap>] [--appends <int>] \\\n    \
         [--r <int> --shape <multi1|multi3|mixed> --alphabet <distinct|shared16>] \\\n    \
         [--warmup <int>] --reps <int> [--out <path>]\n\
         \n\
         WORKLOADS:\n  \
         anchors: {}   (W-C production language bodies; --mode spans|h2)\n  \
         ladder:  --workload ladder --r <int> --shape … --alphabet …\n           \
         (W-A generated definitions; default r ladder {{{}}}; --mode spans|direct|h2|wb|wb-gate|e6b)\n\
         \n\
         NOTES:\n  \
         --mode h2 requires --arm (ONE arm per invocation — the one-cell-per-run\n  \
         protocol; the win/guard comparisons are computed offline from the JSONL).\n  \
         --mode direct requires the ladder workload (the anchors have no direct\n  \
         pattern-set arm — their patterns come from the full pipeline itself).\n  \
         --mode wb (E-3 T-INCR, H3v2) requires the ladder workload (multi* shape,\n  \
         distinct alphabet) + --policy; one rep = one K-append extension ladder\n  \
         (--appends, frozen default 50), one JSON line per append.\n  \
         --mode wb-gate runs the pre-registered equivalence gate at --r ONCE\n  \
         (all four cases; --reps must be 1); ANY failure exits non-zero — the\n  \
         incremental arm is then VOID and must not be measured.\n  \
         --mode e6b (T-E6B, H4v2) requires the ladder workload (multi* shape,\n  \
         distinct alphabet) + --store (ONE store arm per invocation); one rep =\n  \
         the W-B incremental K-append ladder PLUS the construction-side fragment\n  \
         store — one JSON line per append (wall + observed invalidation\n  \
         components) and one deterministic retention summary per rep. The\n  \
         wb-gate discipline carries: it must pass on the same tree first.\n  \
         --alphabet shared16 is defined for the multi* shapes only.\n  \
         --warmup defaults to 3 (recorded in the header; warmup reps are not emitted).\n  \
         --out defaults to stdout.\n",
        anchors.join(", "),
        ladder.join(", "),
    )
}

fn parse_args(args: &[String]) -> Result<DriverArgs, String> {
    let mut mode: Option<Mode> = None;
    let mut workload_token: Option<String> = None;
    let mut arm: Option<H2Arm> = None;
    let mut policy: Option<WbPolicy> = None;
    let mut store: Option<E6bStoreArm> = None;
    // The frozen H3v2 K (design §3: "W-B extension_ladder(r, K=50)"; the H4v2
    // registration rides the same ladder).
    let mut appends: u64 = 50;
    let mut r: Option<usize> = None;
    let mut shape: Option<LadderShape> = None;
    let mut alphabet: Option<LadderAlphabet> = None;
    let mut warmup: u64 = 3;
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
            "--mode" => {
                mode = Some(
                    Mode::from_name(value)
                        .ok_or_else(|| format!("unknown mode `{value}`\n\n{}", usage()))?,
                );
            },
            "--workload" => workload_token = Some(value.clone()),
            "--arm" => {
                arm = Some(
                    H2Arm::from_name(value)
                        .ok_or_else(|| format!("unknown arm `{value}`\n\n{}", usage()))?,
                );
            },
            "--policy" => {
                policy = Some(
                    WbPolicy::from_name(value)
                        .ok_or_else(|| format!("unknown policy `{value}`\n\n{}", usage()))?,
                );
            },
            "--store" => {
                store = Some(
                    E6bStoreArm::from_name(value)
                        .ok_or_else(|| format!("unknown store arm `{value}`\n\n{}", usage()))?,
                );
            },
            "--appends" => {
                appends = value
                    .parse::<u64>()
                    .map_err(|e| format!("--appends must be an integer, got `{value}`: {e}"))?;
            },
            "--r" => {
                r = Some(
                    value
                        .parse::<usize>()
                        .map_err(|e| format!("--r must be an integer, got `{value}`: {e}"))?,
                );
            },
            "--shape" => {
                shape = Some(
                    LadderShape::from_name(value)
                        .ok_or_else(|| format!("unknown shape `{value}`\n\n{}", usage()))?,
                );
            },
            "--alphabet" => {
                alphabet = Some(
                    LadderAlphabet::from_name(value)
                        .ok_or_else(|| format!("unknown alphabet `{value}`\n\n{}", usage()))?,
                );
            },
            "--warmup" => {
                warmup = value
                    .parse::<u64>()
                    .map_err(|e| format!("--warmup must be an integer, got `{value}`: {e}"))?;
            },
            "--reps" => {
                reps = Some(
                    value
                        .parse::<u64>()
                        .map_err(|e| format!("--reps must be an integer, got `{value}`: {e}"))?,
                );
            },
            "--out" => out = Some(value.clone()),
            other => return Err(format!("unknown flag `{other}`\n\n{}", usage())),
        }
        index += 2;
    }

    let mode = mode.ok_or_else(|| format!("--mode is required\n\n{}", usage()))?;
    let workload_token =
        workload_token.ok_or_else(|| format!("--workload is required\n\n{}", usage()))?;
    let reps = reps.ok_or_else(|| format!("--reps is required\n\n{}", usage()))?;
    if reps == 0 {
        return Err("--reps must be >= 1".to_string());
    }

    let workload = if workload_token == "ladder" {
        let r = r.ok_or_else(|| format!("--r is required for the ladder workload\n\n{}", usage()))?;
        let shape = shape
            .ok_or_else(|| format!("--shape is required for the ladder workload\n\n{}", usage()))?;
        let alphabet = alphabet.unwrap_or(LadderAlphabet::Distinct);
        validate_ladder_cell(r, shape, alphabet)?;
        Workload::Ladder { r, shape, alphabet }
    } else {
        let anchor = AnchorLanguage::from_name(&workload_token)
            .ok_or_else(|| format!("unknown workload `{workload_token}`\n\n{}", usage()))?;
        if r.is_some() || shape.is_some() || alphabet.is_some() {
            return Err("--r/--shape/--alphabet apply to the ladder workload only".to_string());
        }
        Workload::Anchor(anchor)
    };
    if mode == Mode::Direct && matches!(workload, Workload::Anchor(_)) {
        return Err(
            "--mode direct requires the ladder workload (anchors have no direct pattern-set arm)"
                .to_string(),
        );
    }
    match (mode, arm) {
        (Mode::H2, None) => {
            return Err(format!("--mode h2 requires --arm\n\n{}", usage()));
        },
        (Mode::Spans | Mode::Direct | Mode::Wb | Mode::WbGate | Mode::E6b, Some(_)) => {
            return Err("--arm applies to --mode h2 only".to_string());
        },
        _ => {},
    }
    match (mode, policy) {
        (Mode::Wb, None) => {
            return Err(format!("--mode wb requires --policy\n\n{}", usage()));
        },
        (Mode::Spans | Mode::Direct | Mode::H2 | Mode::WbGate | Mode::E6b, Some(_)) => {
            return Err("--policy applies to --mode wb only".to_string());
        },
        _ => {},
    }
    match (mode, store) {
        (Mode::E6b, None) => {
            return Err(format!("--mode e6b requires --store\n\n{}", usage()));
        },
        (Mode::Spans | Mode::Direct | Mode::H2 | Mode::Wb | Mode::WbGate, Some(_)) => {
            return Err("--store applies to --mode e6b only".to_string());
        },
        _ => {},
    }
    if matches!(mode, Mode::Wb | Mode::WbGate | Mode::E6b) {
        let Workload::Ladder { shape, alphabet, .. } = workload else {
            return Err(format!(
                "--mode {} requires the ladder workload (the W-B extension ladder rides the \
                 generated definitions)\n\n{}",
                mode.name(),
                usage()
            ));
        };
        if shape == LadderShape::Mixed || alphabet != LadderAlphabet::Distinct {
            return Err(
                "--mode wb/wb-gate/e6b is defined for the multi* shapes over the distinct \
                 alphabet (the W-B appends extend the shared S-chain one level over declared \
                 roots)"
                    .to_string(),
            );
        }
        if matches!(mode, Mode::Wb | Mode::E6b) && appends == 0 {
            return Err("--appends must be >= 1".to_string());
        }
        if mode == Mode::WbGate && reps != 1 {
            return Err("--mode wb-gate runs its cases once: --reps must be 1".to_string());
        }
    }
    Ok(DriverArgs { mode, workload, arm, policy, store, appends, warmup, reps, out })
}

/// Append `value` with JSON string escaping (the driver-local mirror of the Track-B
/// driver's serializer discipline).
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

/// `git rev-parse HEAD` at runtime, anchored at this crate's manifest directory.
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

/// Read + trim a small pseudo-file (`/proc`, `/sys`), falling back to `unknown` —
/// the protocol RECORDS governor/affinity, it never changes them.
fn read_trimmed(path: &str) -> String {
    std::fs::read_to_string(path)
        .map(|text| text.trim().to_string())
        .unwrap_or_else(|_| "unknown".to_string())
}

/// The `Cpus_allowed_list` line of `/proc/self/status` (records `taskset` pinning).
fn cpus_allowed_list() -> String {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status.lines().find_map(|line| {
                line.strip_prefix("Cpus_allowed_list:").map(|rest| rest.trim().to_string())
            })
        })
        .unwrap_or_else(|| "unknown".to_string())
}

fn header_line(args: &DriverArgs, source_bytes: usize, pattern_nodes: Option<usize>) -> String {
    let unix_time_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|elapsed| elapsed.as_secs())
        .unwrap_or(0);
    let (r, shape, alphabet) = match args.workload {
        Workload::Anchor(_) => (0usize, "-", "-"),
        Workload::Ladder { r, shape, alphabet } => (r, shape.name(), alphabet.name()),
    };
    let mut line = String::with_capacity(512);
    line.push_str("{\"header\":{\"bin\":\"bench_e3_construction\",\"git_sha\":");
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
    line.push_str(",\"mode\":");
    line.push_str(&json_string(args.mode.name()));
    line.push_str(",\"arm\":");
    line.push_str(&json_string(args.arm.map_or("-", H2Arm::name)));
    line.push_str(",\"policy\":");
    line.push_str(&json_string(args.policy.map_or("-", WbPolicy::name)));
    line.push_str(",\"store\":");
    line.push_str(&json_string(args.store.map_or("-", E6bStoreArm::name)));
    line.push_str(&format!(
        ",\"appends\":{}",
        if matches!(args.mode, Mode::Wb | Mode::E6b) { args.appends } else { 0 }
    ));
    line.push_str(",\"workload\":");
    line.push_str(&json_string(&args.workload.name()));
    line.push_str(&format!(",\"r\":{r},\"shape\":"));
    line.push_str(&json_string(shape));
    line.push_str(",\"alphabet\":");
    line.push_str(&json_string(alphabet));
    line.push_str(&format!(
        ",\"source_bytes\":{source_bytes},\"pattern_nodes\":{},\"warmup\":{},\"reps\":{},\
         \"rust_min_stack\":",
        pattern_nodes.map_or(-1i64, |nodes| nodes as i64),
        args.warmup,
        args.reps,
    ));
    line.push_str(&json_string(
        &std::env::var("RUST_MIN_STACK").unwrap_or_else(|_| "unset".to_string()),
    ));
    line.push_str("}}");
    line
}

fn main() -> ExitCode {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    let args = match parse_args(&raw_args) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        },
    };

    let mut sink: Box<dyn IoWrite> = match &args.out {
        Some(path) => match File::create(path) {
            Ok(file) => Box::new(BufWriter::new(file)),
            Err(err) => {
                eprintln!("cannot open --out {path}: {err}");
                return ExitCode::FAILURE;
            },
        },
        None => Box::new(BufWriter::new(std::io::stdout())),
    };

    // The cell's source (spans mode) / pattern-node count (direct mode), computed once
    // as setup — generation cost is NOT part of any measured region.
    let source: Option<String> = match (args.mode, args.workload) {
        (Mode::Spans | Mode::H2, Workload::Anchor(anchor)) => {
            Some(anchor.definition_source().to_string())
        },
        // The W-B / T-E6B modes record the BASE ladder source in the header (the
        // reps build their own base + appends internally).
        (
            Mode::Spans | Mode::H2 | Mode::Wb | Mode::WbGate | Mode::E6b,
            Workload::Ladder { r, shape, alphabet },
        ) => Some(ladder_source(r, shape, alphabet)),
        (Mode::Direct, _) => None,
        (Mode::Wb | Mode::WbGate | Mode::E6b, Workload::Anchor(_)) => {
            unreachable!("parse_args enforces the ladder workload for the W-B/T-E6B modes")
        },
    };
    let pattern_nodes: Option<usize> = match (args.mode, args.workload) {
        (Mode::Direct, Workload::Ladder { r, shape, alphabet }) => {
            Some(pattern_node_count(&ladder_patterns(r, shape, alphabet)))
        },
        _ => None,
    };
    let source_bytes = source.as_ref().map_or(0, String::len);

    let header = header_line(&args, source_bytes, pattern_nodes);
    if writeln!(sink, "{header}").is_err() {
        eprintln!("cannot write the header line");
        return ExitCode::FAILURE;
    }

    // The equivalence gate runs its four cases ONCE per invocation (no rep loop) and
    // exits non-zero on ANY failed component — the session protocol treats that as
    // the incremental arm being VOID (report, never measure a voided arm).
    if args.mode == Mode::WbGate {
        let Workload::Ladder { r, .. } = args.workload else {
            unreachable!("parse_args enforces the ladder workload for wb-gate")
        };
        let mut all_pass = true;
        for outcome in run_gate_cases_for(r) {
            let line = match outcome {
                Ok(report) => {
                    if !report.pass() {
                        all_pass = false;
                    }
                    format!(
                        "{{\"wb_gate\":{{\"case\":{},\"r\":{},\"path\":{},\
                         \"expected_path_ok\":{},\"fingerprint_equal\":{},\
                         \"state_count_incremental\":{},\"state_count_batch\":{},\
                         \"deferred_equal\":{},\"installed_ok_incremental\":{},\
                         \"installed_ok_batch\":{},\"installed_par_bytes_equal\":{},\
                         \"fired_multiset_equal\":{},\"fired_matches\":{},\
                         \"auto_injected_rewrites\":{},\"auto_entry_violations\":{},\
                         \"pass\":{}}}}}",
                        json_string(&report.case_name),
                        report.r,
                        json_string(&report.path),
                        report.expected_path_ok,
                        report.fingerprint_equal,
                        report.state_count_incremental,
                        report.state_count_batch,
                        report.deferred_equal,
                        report.installed_ok_incremental,
                        report.installed_ok_batch,
                        report.installed_par_bytes_equal,
                        report.fired_multiset_equal,
                        report.fired_matches,
                        report.auto_injected_rewrites,
                        report.auto_entry_violations,
                        report.pass(),
                    )
                },
                Err(reason) => {
                    all_pass = false;
                    format!("{{\"dnf\":true,\"reason\":{}}}", json_string(&reason))
                },
            };
            if writeln!(sink, "{line}").is_err() {
                eprintln!("cannot write a gate line");
                return ExitCode::FAILURE;
            }
        }
        if sink.flush().is_err() {
            eprintln!("cannot flush the output sink");
            return ExitCode::FAILURE;
        }
        return if all_pass {
            ExitCode::SUCCESS
        } else {
            eprintln!("bench_e3_construction: the H3v2 equivalence gate FAILED — the incremental arm is VOID");
            ExitCode::FAILURE
        };
    }

    let mut failures = 0u64;
    for rep in 0..(args.warmup + args.reps) {
        let recorded = rep >= args.warmup;
        let record_index = rep.saturating_sub(args.warmup);
        let line = match (args.mode, args.workload) {
            (Mode::Spans, _) => {
                let cell_source =
                    source.clone().expect("spans mode always carries a source");
                match in_fresh_thread(move || run_spans_once(&cell_source)) {
                    Ok(cell) => {
                        let mut phases = String::with_capacity(512);
                        phases.push('[');
                        for (position, (phase, stats)) in cell.report.phases().enumerate() {
                            if position > 0 {
                                phases.push(',');
                            }
                            phases.push_str(&format!(
                                "{{\"phase\":{},\"activations\":{},\"self_ns\":{},\
                                 \"total_ns\":{}}}",
                                json_string(phase.name()),
                                stats.activations,
                                stats.self_ns,
                                stats.total_ns,
                            ));
                        }
                        phases.push(']');
                        format!(
                            "{{\"spans\":{{\"rep\":{record_index},\"wall_ns\":{},\
                             \"installed_ok\":{},\"mismatched_spans\":{},\"self_ns_sum\":{},\
                             \"phases\":{phases}}}}}",
                            cell.wall_ns,
                            cell.installed_ok,
                            cell.report.mismatched_spans,
                            cell.report.self_ns_sum(),
                        )
                    },
                    Err(reason) => {
                        failures += 1;
                        format!("{{\"dnf\":true,\"rep\":{record_index},\"reason\":{}}}", json_string(&reason))
                    },
                }
            },
            (Mode::Direct, Workload::Ladder { r, shape, alphabet }) => {
                let cell =
                    in_fresh_thread(move || run_direct_compile_once(ladder_patterns(r, shape, alphabet)));
                format!(
                    "{{\"direct\":{{\"rep\":{record_index},\"wall_ns\":{},\"entry_count\":{},\
                     \"state_count\":{},\"pattern_nodes\":{}}}}}",
                    cell.wall_ns, cell.entry_count, cell.state_count, cell.pattern_nodes,
                )
            },
            (Mode::Direct, Workload::Anchor(_)) => {
                unreachable!("parse_args rejects direct mode over anchors")
            },
            (Mode::Wb, Workload::Ladder { r, shape, .. }) => {
                let policy = args.policy.expect("parse_args requires --policy for wb mode");
                let appends = usize::try_from(args.appends)
                    .expect("--appends fits a usize on every supported target");
                match in_fresh_thread(move || run_wb_rep(policy, r, shape, appends)) {
                    Ok(cells) => {
                        // A fell-back append inside the W-B ladder is an arm-voiding
                        // anomaly (the ladder is inside the admitted family by
                        // construction) — counted as a failure AND recorded on the line.
                        failures += cells.iter().filter(|cell| cell.fell_back).count() as u64;
                        cells
                            .iter()
                            .map(|cell| {
                                format!(
                                    "{{\"wb\":{{\"rep\":{record_index},\"append\":{},\
                                     \"policy\":{},\"wall_ns\":{},\"installed_ok\":{},\
                                     \"fell_back\":{},\"source_bytes\":{}}}}}",
                                    cell.append,
                                    json_string(policy.name()),
                                    cell.wall_ns,
                                    cell.installed_ok,
                                    cell.fell_back,
                                    cell.source_bytes,
                                )
                            })
                            .collect::<Vec<String>>()
                            .join("\n")
                    },
                    Err(reason) => {
                        failures += 1;
                        format!(
                            "{{\"dnf\":true,\"rep\":{record_index},\"reason\":{}}}",
                            json_string(&reason)
                        )
                    },
                }
            },
            (Mode::E6b, Workload::Ladder { r, shape, .. }) => {
                let store = args.store.expect("parse_args requires --store for e6b mode");
                let appends = usize::try_from(args.appends)
                    .expect("--appends fits a usize on every supported target");
                match in_fresh_thread(move || run_e6b_rep(store, r, shape, appends)) {
                    Ok((cells, summary)) => {
                        // A fell-back append or a violated deterministic predicate
                        // inside the T-E6B ladder is an arm-voiding anomaly —
                        // counted as a failure AND recorded on the lines.
                        failures += cells.iter().filter(|cell| cell.fell_back).count() as u64;
                        if !summary.retained_lt_whole || !summary.invalidation_exact_all {
                            failures += 1;
                        }
                        let mut lines: Vec<String> = cells
                            .iter()
                            .map(|cell| {
                                format!(
                                    "{{\"e6b\":{{\"rep\":{record_index},\"append\":{},\
                                     \"store\":{},\"wall_ns\":{},\"installed_ok\":{},\
                                     \"fell_back\":{},\"source_bytes\":{},\
                                     \"group_before\":{},\"group_after\":{},\
                                     \"invalidated_existing\":{},\"invalidated_removed\":{},\
                                     \"manifest_invalidated\":{},\"inserted_new\":{},\
                                     \"unchanged_group\":{},\"expected_invalidated\":{},\
                                     \"actual_invalidated\":{},\"store_entries\":{}}}}}",
                                    cell.append,
                                    json_string(store.name()),
                                    cell.wall_ns,
                                    cell.installed_ok,
                                    cell.fell_back,
                                    cell.source_bytes,
                                    cell.group_before,
                                    cell.group_after,
                                    cell.invalidated_existing,
                                    cell.invalidated_removed,
                                    cell.manifest_invalidated,
                                    cell.inserted_new,
                                    cell.unchanged_group,
                                    cell.expected_invalidated,
                                    cell.actual_invalidated,
                                    cell.store_entries,
                                )
                            })
                            .collect();
                        lines.push(format!(
                            "{{\"e6b_rep\":{{\"rep\":{record_index},\"store\":{},\
                             \"total_wall_ns\":{},\"snapshots\":{},\
                             \"total_fragment_refs\":{},\"distinct_fragments\":{},\
                             \"dedup_hits\":{},\"content_dedup_hits\":{},\
                             \"retained_fragment_bytes\":{},\"whole_artifact_bytes\":{},\
                             \"retained_lt_whole\":{},\"invalidation_exact_all\":{}}}}}",
                            json_string(store.name()),
                            summary.total_wall_ns,
                            summary.snapshots,
                            summary.total_fragment_refs,
                            summary.distinct_fragments,
                            summary.dedup_hits,
                            summary.content_dedup_hits,
                            summary.retained_fragment_bytes,
                            summary.whole_artifact_bytes,
                            summary.retained_lt_whole,
                            summary.invalidation_exact_all,
                        ));
                        lines.join("\n")
                    },
                    Err(reason) => {
                        failures += 1;
                        format!(
                            "{{\"dnf\":true,\"rep\":{record_index},\"reason\":{}}}",
                            json_string(&reason)
                        )
                    },
                }
            },
            (Mode::Wb | Mode::WbGate | Mode::E6b, Workload::Anchor(_)) | (Mode::WbGate, _) => {
                unreachable!("wb/e6b require the ladder workload; wb-gate returned above")
            },
            (Mode::H2, _) => {
                let arm = args.arm.expect("parse_args requires --arm for h2 mode");
                let cell_source = source.clone().expect("h2 mode always carries a source");
                match arm {
                    H2Arm::EagerControl => {
                        match in_fresh_thread(move || run_eager_control_once(&cell_source)) {
                            Ok(cell) => format!(
                                "{{\"h2\":{{\"rep\":{record_index},\"arm\":{},\"wall_ns\":{},\
                                 \"installed_ok\":{},\"forced\":null}}}}",
                                json_string(arm.name()),
                                cell.wall_ns,
                                cell.installed_ok,
                            ),
                            Err(reason) => {
                                failures += 1;
                                format!(
                                    "{{\"dnf\":true,\"rep\":{record_index},\"reason\":{}}}",
                                    json_string(&reason)
                                )
                            },
                        }
                    },
                    H2Arm::LazyGateOnly | H2Arm::LazyForceInstalled => {
                        let outcome: Result<LazyCell, String> =
                            in_fresh_thread(move || match arm {
                                H2Arm::LazyGateOnly => run_lazy_gate_only_once(&cell_source),
                                H2Arm::LazyForceInstalled => {
                                    run_lazy_force_installed_once(&cell_source)
                                },
                                H2Arm::EagerControl => {
                                    unreachable!("the outer match routes eager-control")
                                },
                            });
                        match outcome {
                            Ok(cell) => {
                                let required = arm
                                    .required_forcing()
                                    .expect("lazy arms declare required cell states");
                                let observed = (
                                    cell.forced_lowered,
                                    cell.forced_ruleset,
                                    cell.forced_installed_par,
                                );
                                if observed != required {
                                    failures += 1;
                                    format!(
                                        "{{\"dnf\":true,\"rep\":{record_index},\"reason\":\
                                         {}}}",
                                        json_string(&format!(
                                            "arm {} cell-state validation failed: required \
                                             (lowered,ruleset,installed_par)={required:?}, \
                                             observed {observed:?}",
                                            arm.name()
                                        )),
                                    )
                                } else {
                                    format!(
                                        "{{\"h2\":{{\"rep\":{record_index},\"arm\":{},\
                                         \"wall_ns\":{},\"installed_ok\":{},\
                                         \"forced\":{{\"lowered\":{},\"ruleset\":{},\
                                         \"installed_par\":{}}}}}}}",
                                        json_string(arm.name()),
                                        cell.wall_ns,
                                        cell.installed_ok
                                            .map_or("null".to_string(), |ok| ok.to_string()),
                                        cell.forced_lowered,
                                        cell.forced_ruleset,
                                        cell.forced_installed_par,
                                    )
                                }
                            },
                            Err(reason) => {
                                failures += 1;
                                format!(
                                    "{{\"dnf\":true,\"rep\":{record_index},\"reason\":{}}}",
                                    json_string(&reason)
                                )
                            },
                        }
                    },
                }
            },
        };
        if recorded {
            if writeln!(sink, "{line}").is_err() {
                eprintln!("cannot write a rep line");
                return ExitCode::FAILURE;
            }
        }
    }
    if sink.flush().is_err() {
        eprintln!("cannot flush the output sink");
        return ExitCode::FAILURE;
    }
    if failures > 0 {
        eprintln!("bench_e3_construction: {failures} rep(s) did not finish (dnf lines emitted)");
    }
    ExitCode::SUCCESS
}
