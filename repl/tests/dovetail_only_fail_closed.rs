//! A-S5.6 decision (4) — the Dovetail-only (no f1r3node) profile
//! (`--no-default-features --features bundled-languages`): Lambda + Ambient still REGISTER
//! and parse, but `exec` FAILS CLOSED with a typed error pointing at the rho build — their
//! production reduction semantics are the in-Rho quiescence driver, and this profile has
//! no Rho machine to run it on (no dual runtime path: the old generic-Dovetail exec is
//! NOT silently substituted).
//!
//! This suite compiles ONLY in that profile (it is feature-gated OUT of the default
//! `rho-languages` build, whose expectations live in `registry_exec.rs` /
//! `zero_dstage_exec.rs`). Gate evidence: `scratchpad/as56_dovetail_only_gate.log`.
#![cfg(all(feature = "bundled-languages", not(feature = "rho-languages")))]

use mettail_repl::build_registry;
use mettail_runtime::{Language, RuntimeBackend};

/// Both flipped languages register, parse, advertise their production `RhoMachine`
/// default, and fail exec CLOSED with the decision-(4) typed error naming the rho build.
#[test]
fn lambda_and_ambient_exec_fail_closed_pointing_at_the_rho_build() {
    let registry = build_registry().expect("the Dovetail-only registry builds");
    for (name, subject) in [
        ("Lambda", "(lam x. x, lam a. lam b. a)"),
        ("Ambient", "{open(n, a[{0}]) | n[{b[{0}]}]}"),
    ] {
        let language = registry.get(name).expect("the language registers");
        // Parse/introspection still work (decision (4)).
        let term = language
            .parse_term(subject)
            .unwrap_or_else(|err| panic!("{name} must still parse in this profile: {err}"));
        // The advertised default stays the PRODUCTION backend (RhoMachine) — the failure
        // names the missing build, never "no default backend".
        assert_eq!(
            language.selected_default_runtime_backend(),
            Some(RuntimeBackend::RhoMachine),
            "{name} advertises its production RhoMachine default even here"
        );
        let err = language
            .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
            .expect_err("exec must fail closed in the Dovetail-only profile");
        assert!(
            err.contains("in-Rho quiescence driver")
                && err.contains("rho-languages")
                && err.contains(name),
            "{name}'s fail-closed error must name the driver, the language, and the rho \
             build flag: {err}"
        );
    }
}
