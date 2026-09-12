use std::{env, process::Command};

fn main() {
    println!("cargo:rustc-check-cfg=cfg(mettail_checked_fx_profile)");
    for name in [
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_UNSTABLE_BUILD_STD",
    ] {
        println!("cargo:rerun-if-env-changed={name}");
    }
    // This profile is for the audited, trusted standard toolchain, not an
    // attestation of arbitrary compiler wrappers or rebuilt/replaced core.
    if ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_UNSTABLE_BUILD_STD"]
        .iter()
        .any(|name| env::var_os(name).is_some_and(|value| !value.is_empty()))
    {
        return;
    }
    let flags = env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
    if flags.contains("sysroot") || flags.contains("build-std") || flags.contains("--extern") {
        return;
    }
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64")
        || env::var("CARGO_CFG_TARGET_POINTER_WIDTH").as_deref() != Ok("64")
    {
        return;
    }
    let Some(rustc) = env::var_os("RUSTC") else {
        return;
    };
    println!("cargo:rerun-if-changed={}", rustc.to_string_lossy());
    let Ok(version) = Command::new(rustc).arg("-vV").output() else {
        return;
    };
    if version.status.success()
        && String::from_utf8_lossy(&version.stdout)
            .lines()
            .any(|line| line == "commit-hash: 2e2b193f8ada105f27608b7be81c293e0d7292cb")
    {
        println!("cargo:rustc-cfg=mettail_checked_fx_profile");
    }
}
