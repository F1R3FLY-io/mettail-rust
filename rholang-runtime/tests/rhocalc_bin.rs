//! CI gate for the `rhocalc` interpreter binary (`src/bin/rhocalc.rs`).
//!
//! Runs the built binary on the committed demo `.rho` file and asserts the RhoCalc program — which
//! exercises the grammar's Foreign Language Term feature — actually reduces on the f1r3node
//! reducer, so "the demo works" is CI-gated rather than a one-time manual check. The full path is
//! the rho-native one: the GENERATED RhoCalc parser → `PFlt` lowering (lam → LambdaLanguage) → the
//! real reducer (never a host/Dovetail simulation). The send/receive rendezvous fires as one COMM;
//! the two typed `${x}` holes capture ⟦I⟧, ⟦K⟧ and the re-quote reconstructs App(I, K), which
//! comes to rest on `@"OUT"` and renders as `(λ.0 λ.λ.1)`.
#![cfg(all(feature = "rhocalc-runtime", feature = "lambda-runtime"))]

use std::path::PathBuf;
use std::process::{Command, Output};

/// Absolute path to a demo file under `<workspace>/demos/flt-foreign-exchange/`.
fn demo_path(file_name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../demos/flt-foreign-exchange")
        .join(file_name)
}

/// Run the built `rhocalc` binary on a demo file, capturing its output.
fn run_interpreter(demo_file: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rhocalc"))
        .arg(demo_path(demo_file))
        .env("RUST_MIN_STACK", "8388608")
        .output()
        .expect("the rhocalc binary must run")
}

#[test]
fn foreign_exchange_demo_binds_typed_holes_and_reconstructs() {
    let output = run_interpreter("foreign-exchange.rho");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "rhocalc exited non-zero on foreign-exchange.rho\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // The COMM fires; the two typed holes ${f}, ${k} capture ⟦I⟧, ⟦K⟧ and the re-quote
    // reconstructs App(I, K), which renders as (λ.0 λ.λ.1) on @"OUT".
    assert!(
        stdout.contains("(λ.0 λ.λ.1)"),
        "expected the reconstructed App(I, K) = (λ.0 λ.λ.1) on @\"OUT\"\nstdout:\n{stdout}"
    );
}
