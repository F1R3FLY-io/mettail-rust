//! Main-thread zero-slope gate for the unconditional observation PDAs.
//!
//! `RuntimeObservationValue` is recursive data, but its production traversals must recurse only
//! through explicit heap work stacks. The child binary runs on its process's main thread while
//! this test installs `RLIMIT_STACK` before `exec`; a spawned test thread would measure the wrong
//! stack and `RUST_MIN_STACK` would not constrain the production path.

use std::os::unix::process::CommandExt;

const PROBE: &str = env!("CARGO_BIN_EXE_observation_depth_probe");
const RESOLUTION: usize = 4 * 1024;
const ZERO_SLOPE_TOLERANCE: usize = 4 * RESOLUTION;

fn runs_within(stack: usize, depth: usize, subject: &str) -> bool {
    let mut command = std::process::Command::new(PROBE);
    command
        .env("GATE_SUBJECT", subject)
        .env("GATE_DEPTH", depth.to_string())
        .env_remove("RUST_MIN_STACK")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());

    // SAFETY: `setrlimit` is async-signal-safe and allocates nothing. This runs in the child
    // between `fork` and `exec`, before the kernel lays out the probe's main-thread stack.
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

fn minimum_stack(depth: usize, subject: &str) -> usize {
    let mut failing = 8 * 1024;
    let mut passing = 1024 * 1024;
    assert!(runs_within(passing, depth, subject));
    while passing - failing > RESOLUTION {
        let midpoint = ((failing + passing) / (2 * RESOLUTION)) * RESOLUTION;
        if runs_within(midpoint, depth, subject) {
            passing = midpoint;
        } else {
            failing = midpoint;
        }
    }
    passing
}

#[test]
fn observation_value_traits_are_depth_independent() {
    const SUBJECT: &str = "value_traits";
    for depth in [4usize, 512, 4096] {
        assert!(
            runs_within(128 * 1024, depth, SUBJECT),
            "observation value traversal exceeded a 128 KiB main-thread stack at depth {depth}"
        );
    }

    let low = minimum_stack(512, SUBJECT);
    let high = minimum_stack(4096, SUBJECT);
    let growth = high.saturating_sub(low);
    assert!(
        growth <= ZERO_SLOPE_TOLERANCE,
        "observation value native-stack requirement grew by {growth} B from depth 512 ({low} B) \
         to depth 4,096 ({high} B); explicit PDA traversals must be depth-independent"
    );
}
