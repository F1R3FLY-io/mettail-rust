//! Main-thread zero-slope gate for the shared production Rholang formula PDA.
//!
//! Libtest may execute this parent on a spawned thread because only the dedicated child probe's
//! main-thread stack is measured. The parent installs `RLIMIT_STACK` before `exec` and the child
//! runs the production traversal directly on its process's main thread.

use std::os::unix::process::CommandExt;

const PROBE: &str = env!("CARGO_BIN_EXE_formula_pda_depth_probe");
const CHILD_DEPTH: &str = "FORMULA_PDA_GATE_DEPTH";
const RESOLUTION: usize = 4 * 1024;
const ZERO_SLOPE_TOLERANCE: usize = 4 * RESOLUTION;

fn runs_within(stack: usize, depth: usize) -> bool {
    let mut command = std::process::Command::new(PROBE);
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

#[test]
fn formula_pda_main_thread_stack_is_depth_independent() {
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
