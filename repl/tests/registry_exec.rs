//! Regression for the REPL `exec` bug: a raw `language!` value advertises NO default runtime
//! backend, so `exec` failed with "language X does not advertise a default runtime backend". The
//! production `build_registry` now wraps every bundled language in its checked backend. This test
//! asserts the fix end-to-end at the registry boundary — and, by building the registry, exercises
//! the runtime install (fingerprint + plan-gate checks) of every wrapper: the four production
//! languages plus, since A-S6 (the demo flip), SwapDemo and the 12 rho_net demo languages.
#![cfg(feature = "rho-languages")]

use std::collections::HashMap;

use mettail_repl::build_registry;
use mettail_runtime::RuntimeBackend;

fn default_backends() -> HashMap<String, Option<RuntimeBackend>> {
    build_registry()
        .expect("build_registry must construct + install every production backend")
        .list_with_runtime()
        .into_iter()
        .map(|info| (info.name.clone(), info.default_backend))
        .collect()
}

/// A-S6: the rho_net demo languages registered by the production `build_registry`.
///
/// Task #11 (extended 2026-07-26): EMPTY, by decision. Per the USER decision "I don't want
/// REPL integration for the non-production grammars!", SwapDemo and the eleven rho_net
/// DEMONSTRATION grammars are de-productionized out of the registry — REPL-unreachability
/// is the intended outcome. An entry removed here is not a lost assertion: the language
/// stops being a registry member by design, and its in-Rho behaviour is asserted directly
/// in `rholang-runtime/tests/rho_net_*_firing.rs`.
///
/// The constant and both loops below are KEPT rather than deleted: they are the standing
/// contract that WHATEVER the registry advertises must carry an installed default backend,
/// so re-adding a language here re-arms the check with no other edit. The four production
/// languages continue to be checked by name either way.
const A_S6_DEMOS: [&str; 0] = [
    // "SwapDemo",
    // "AcDemo",
    // "AcBagDemo",
    // "NlAcDemo",
    // "AmbDemo",
    // "AmbNewDemo",
    // "InOutDemo",
    // "CommDemo",
    // "CtxDemo",
    // "BiCongDemo",
    // "LambdaDemo",
    // "NativeDemo",
    // "NativeFoldDemo",  // de-productionized 2026-07-26 (test-hosted)
];

#[test]
fn every_bundled_language_advertises_a_default_runtime_backend() {
    let by_name = default_backends();
    for expected in ["RhoCalc", "Calculator", "Lambda", "Ambient"] {
        assert!(by_name.contains_key(expected), "registry must contain {expected}");
    }
    // A-S6: the demo languages are registry members too (the runtime mandate is universal).
    for expected in A_S6_DEMOS {
        assert!(by_name.contains_key(expected), "registry must contain the demo {expected}");
    }
    for (name, backend) in &by_name {
        assert!(
            backend.is_some(),
            "{name} must advertise a default runtime backend — without it `exec` fails with \
             'does not advertise a default runtime backend' (the original bug)"
        );
    }
}

#[test]
fn default_backends_are_capability_based() {
    let by_name = default_backends();
    // RhoCalc + Calculator run on the Rho machine (COMM / scalar dataflow); their Dovetail stage is
    // the fold prereduce + the fallback.
    assert_eq!(
        by_name.get("RhoCalc"),
        Some(&Some(RuntimeBackend::RhoMachine)),
        "RhoCalc defaults to the two-stage Dovetail+Rholang backend"
    );
    assert_eq!(
        by_name.get("Calculator"),
        Some(&Some(RuntimeBackend::RhoMachine)),
        "Calculator defaults to the two-stage Dovetail+Rholang backend (E3 fold-dataflow)"
    );
    // A-S5.6 (the production flip): Lambda + Ambient run on the Rho machine too — the in-Rho
    // quiescence driver (`^drive` seed) is their default exec path; Dovetail remains only the
    // lazy deferral stage inside the two-stage wrapper.
    assert_eq!(
        by_name.get("Lambda"),
        Some(&Some(RuntimeBackend::RhoMachine)),
        "Lambda defaults to the two-stage Dovetail+Rholang backend (in-Rho quiescence driver)"
    );
    assert_eq!(
        by_name.get("Ambient"),
        Some(&Some(RuntimeBackend::RhoMachine)),
        "Ambient defaults to the two-stage Dovetail+Rholang backend (in-Rho quiescence driver)"
    );
    // A-S6 (the demo flip): every rho_net demo runs on the Rho machine — the report-free
    // in-Rho set-automaton match (`rho_net_match_invocation_to`) is the default exec path;
    // demos are NOT drive-opted (`DRIVE_OPT_IN` stays exactly {Lambda, Ambient}).
    for demo in A_S6_DEMOS {
        assert_eq!(
            by_name.get(demo),
            Some(&Some(RuntimeBackend::RhoMachine)),
            "{demo} defaults to the two-stage Dovetail+Rholang backend (in-Rho set-automaton \
             match)"
        );
    }
}
