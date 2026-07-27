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

/// Task #22 (USER ruling 2026-07-27): the four GSLT omnibus conformance specs. `e1bfcd38`
/// promoted them out of their own test binaries into `languages/src/`, but the shipped
/// registry was still `{lambda, ambient, rhocalc, calculator}` — so a language that had
/// become a production spec was reachable from nothing but one test binary. Unlike
/// [`A_S6_DEMOS`], this list is NOT expected to be empty: emptying it would silently undo
/// the ruling.
const OMNIBUS_SPECS: [&str; 4] = ["Json", "Monoid", "Pi", "Turing"];

#[test]
fn every_bundled_language_advertises_a_default_runtime_backend() {
    let by_name = default_backends();
    for expected in ["Rholang", "Calculator", "Lambda", "Ambient"] {
        assert!(by_name.contains_key(expected), "registry must contain {expected}");
    }
    // Task #22: the four omnibus specs are registry members, and building the registry at all
    // exercises each one's `planned_rho_backend_for` + install (fingerprint + plan gate).
    for expected in OMNIBUS_SPECS {
        assert!(
            by_name.contains_key(expected),
            "registry must contain the omnibus spec {expected} (task #22 USER ruling)"
        );
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
    // Rholang + Calculator run on the Rho machine (COMM / scalar dataflow); their Dovetail stage is
    // the fold prereduce + the fallback.
    assert_eq!(
        by_name.get("Rholang"),
        Some(&Some(RuntimeBackend::RhoMachine)),
        "Rholang defaults to the two-stage Dovetail+Rholang backend"
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
    // Task #22: same shape for the four omnibus specs — none is drive-opted, so each defaults
    // to the in-Rho set-automaton match, not to a host Dovetail path.
    for spec in OMNIBUS_SPECS {
        assert_eq!(
            by_name.get(spec),
            Some(&Some(RuntimeBackend::RhoMachine)),
            "{spec} defaults to the two-stage Dovetail+Rholang backend (in-Rho set-automaton \
             match)"
        );
    }
}

/// Task #22 — REACHABILITY, not mere constructibility.
///
/// `build_registry` succeeding proves the four wrappers INSTALL. It does not prove a user can
/// get at them: [`LanguageRegistry::get`] keys on `language.name().to_lowercase()`, so what a
/// person types at the prompt (`lang json`) has to resolve through that map. This asserts the
/// lookup key each language actually answers to, in every case form the REPL accepts, and then
/// asserts each one PARSES a representative program of its own surface — the first thing a
/// user does after `lang <name>`.
#[test]
fn each_omnibus_spec_is_reachable_by_its_repl_key_and_parses() {
    let registry =
        build_registry().expect("build_registry must construct + install every production backend");

    // One representative program per language, in that language's own concrete syntax.
    let subjects: [(&str, &str); 4] = [
        ("json", r#"{"a": 1}"#),
        ("monoid", "(e * a)"),
        ("pi", "{ in(c,y).0 | c!c.0 }"),
        ("turing", "(q0 , <[] | 0 | [0,1]>)"),
    ];

    for (key, source) in subjects {
        // The exact string a user types, plus the case forms `get`/`contains` promise.
        for form in [key.to_string(), key.to_uppercase(), {
            let mut c = key.chars();
            match c.next() {
                Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
                None => String::new(),
            }
        }] {
            assert!(
                registry.contains(&form),
                "`lang {form}` must resolve — the REPL keys the registry on \
                 name().to_lowercase()"
            );
            let language = registry
                .get(&form)
                .unwrap_or_else(|err| panic!("registry.get({form:?}) failed: {err}"));
            assert_eq!(
                language.name().to_lowercase(),
                key,
                "the value behind key {form:?} must be the language that key names"
            );
        }

        let language = registry.get(key).expect("resolved above");
        let term = language
            .parse_term(source)
            .unwrap_or_else(|err| panic!("`lang {key}` then {source:?} must parse: {err}"));
        assert!(
            !language.format_term(term.as_ref()).is_empty(),
            "{key} must render the term it parsed — a registered language with no rendering \
             surface is not usable interactively"
        );
    }
}
