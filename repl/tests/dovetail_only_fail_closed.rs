//! A-S5.6 decision (4) — the Dovetail-only (no f1r3node) profile
//! (`--no-default-features --features bundled-languages`): Lambda + Ambient still REGISTER
//! and parse, but `exec` FAILS CLOSED with a typed error pointing at the rho build — their
//! production reduction semantics are the in-Rho quiescence driver, and this profile has
//! no Rho machine to run it on (no dual runtime path: the old generic-Dovetail exec is
//! NOT silently substituted).
//!
//! A-S6 (the demo flip) makes the discipline UNIVERSAL: SwapDemo and the 12 rho_net demo
//! languages register through the same fail-closed wrapper — their production semantics
//! are the in-Rho set-automaton match, so this profile's `exec` fails closed for them
//! too, naming the mechanism and the rho build flag.
//!
//! This suite compiles ONLY in that profile (it is feature-gated OUT of the default
//! `rho-languages` build, whose expectations live in `registry_exec.rs` /
//! `zero_dstage_exec.rs`). Gate evidence: `scratchpad/as56_dovetail_only_gate.log`
//! (A-S5.6) and `scratchpad/as6_dovetail_only_gate.log` (A-S6).
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

// Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. This test iterated the
// TWELVE demo languages through the Dovetail-only REGISTRY and asserted each fails exec
// closed pointing at the rho build. Per the USER decision "I don't want REPL integration
// for the non-production grammars!" none of them registers any more, so the loop has no
// subjects at all — `registry.get(name)` would panic on the first entry. The subject was
// the REGISTRATION, not the language, so this is NOT relocatable. The decision-(4)
// fail-closed discipline itself is unchanged and stays pinned by the production half of
// this file (`lambda_and_ambient_exec_fail_closed_pointing_at_the_rho_build`), which
// exercises the identical `RhoBuildRequiredLanguage` wrapper.
// /// A-S6: every flipped demo language registers, parses, advertises its production
// /// `RhoMachine` default, and fails exec CLOSED with the decision-(4) typed error naming
// /// the in-Rho set-automaton match and the rho build.
// #[test]
// fn a_s6_demos_exec_fail_closed_pointing_at_the_rho_build() {
//     let registry = build_registry().expect("the Dovetail-only registry builds");
//     for (name, subject) in [
//         ("SwapDemo", "swap(A, B)"),
//         ("AcDemo", "#{A | B | C}#"),
//         ("AcBagDemo", "#{A | B | C}#"),
//         ("NlAcDemo", "#{A | A | B}#"),
//         ("AmbDemo", "{ open(na, A) | na[B] }"),
//         ("AmbNewDemo", "new(x, { open(na, A) | na[B] })"),
//         ("InOutDemo", "{ na[{ in(nb, A) }] | nb[B] }"),
//         ("CommDemo", "{ for(y <- na){ y!(nc) } | na!(nb) }"),
//         ("CtxDemo", "wrap(swap(A, B))"),
//         ("BiCongDemo", "node(swap(A, B), swap(C, D))"),
//         ("LambdaDemo", "(lam x. f(x), A)"),
//         ("NativeDemo", "2 ^ 3"),
//         // Task #11 (extended 2026-07-26): NativeFoldDemo is de-productionized out of the
//         // REPL registry (test-hosted definition), so it has no fail-closed wrapper here.
//         // ("NativeFoldDemo", "2 + 3"),
//     ] {
//         let language = registry.get(name).expect("the demo registers");
//         let term = language
//             .parse_term(subject)
//             .unwrap_or_else(|err| panic!("{name} must still parse in this profile: {err}"));
//         assert_eq!(
//             language.selected_default_runtime_backend(),
//             Some(RuntimeBackend::RhoMachine),
//             "{name} advertises its production RhoMachine default even here"
//         );
//         let err = language
//             .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//             .expect_err("demo exec must fail closed in the Dovetail-only profile");
//         assert!(
//             err.contains("in-Rho set-automaton match")
//                 && err.contains("rho-languages")
//                 && err.contains(name),
//             "{name}'s fail-closed error must name the match mechanism, the language, and \
//              the rho build flag: {err}"
//         );
//     }
// }
//
