//! Main-thread zero-slope gate for the shared production Rholang formula PDA.
//!
//! This is a `harness = false` integration test because libtest executes test functions on a
//! spawned thread. The child mode runs the included production traversal directly on the process
//! main thread after the parent installs `RLIMIT_STACK` before `exec`.

#[path = "support/formula_pda_carrier.rs"]
mod rholang;

use rholang::{formula, Proc};
use std::{hint::black_box, os::unix::process::CommandExt, sync::Arc};

const CHILD_DEPTH: &str = "FORMULA_PDA_GATE_DEPTH";
const RESOLUTION: usize = 4 * 1024;
const ZERO_SLOPE_TOLERANCE: usize = 4 * RESOLUTION;

fn probe_body(depth: usize) {
    let mut root = formula::bool_formula(true);
    for _ in 0..depth {
        root = Proc::Not(Arc::new(root));
    }

    black_box(formula::is_statically_false(&root));
    black_box(formula::is_statically_true(&root));
    black_box(formula::host_matches_verdict(&Proc::PZero, &root));

    // The minimal carrier deliberately retains derived recursive Drop. Production's generated
    // AST has an iterative destructor, so forgetting only removes adapter teardown from this
    // measurement of the shared production traversal.
    std::mem::forget(root);
}

fn runs_within(stack: usize, depth: usize) -> bool {
    let executable = std::env::current_exe().expect("formula PDA gate: current executable");
    let mut command = std::process::Command::new(executable);
    command
        .env(CHILD_DEPTH, depth.to_string())
        .env_remove("RUST_MIN_STACK")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());

    // SAFETY: `setrlimit` is async-signal-safe and allocates nothing. The hook runs in the child
    // between `fork` and `exec`, before the kernel lays out the measured main-thread stack.
    unsafe {
        command.pre_exec(move || {
            let stack_limit = libc::rlimit {
                rlim_cur: stack as libc::rlim_t,
                rlim_max: stack as libc::rlim_t,
            };
            if libc::setrlimit(libc::RLIMIT_STACK, &stack_limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            let no_core = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
            if libc::setrlimit(libc::RLIMIT_CORE, &no_core) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }

    command.status().is_ok_and(|status| status.success())
}

fn minimum_stack(depth: usize) -> usize {
    let mut failing = 8 * 1024;
    let mut passing = 1024 * 1024;
    assert!(runs_within(passing, depth));
    while passing - failing > RESOLUTION {
        let midpoint = ((failing + passing) / (2 * RESOLUTION)) * RESOLUTION;
        if runs_within(midpoint, depth) {
            passing = midpoint;
        } else {
            failing = midpoint;
        }
    }
    passing
}

fn parent_gate() {
    for depth in [4usize, 512, 4096] {
        assert!(
            runs_within(128 * 1024, depth),
            "formula PDA exceeded a 128 KiB main-thread stack at depth {depth}"
        );
    }

    let low = minimum_stack(512);
    let high = minimum_stack(4096);
    let growth = high.saturating_sub(low);
    assert!(
        growth <= ZERO_SLOPE_TOLERANCE,
        "formula PDA native-stack requirement grew by {growth} B from depth 512 ({low} B) to \
         depth 4,096 ({high} B); the explicit traversal must be depth-independent"
    );
    println!(
        "formula PDA main-thread stack: depth 512 = {low} B, depth 4096 = {high} B, growth = \
         {growth} B"
    );
}

fn main() {
    match std::env::var(CHILD_DEPTH) {
        Ok(depth) => probe_body(
            depth
                .parse()
                .expect("formula PDA gate: numeric child depth"),
        ),
        Err(std::env::VarError::NotPresent) => parent_gate(),
        Err(error) => panic!("formula PDA gate: invalid {CHILD_DEPTH}: {error}"),
    }
}
