//! A-S5.2 open probe **P2** (plan v2 §4.2 / F10, amendment AM-7) + the F7 readback-API unit
//! tests — the reducer facts the in-Rho quiescence driver's GInt fuel arm depends on, proven
//! on the live f1r3node reducer BEFORE the driver codegen depends on them:
//!
//!  1. a `Match` case list with a ground `GInt(0)` pattern FIRST and a wildcard SECOND
//!     dispatches correctly (the ground case matches via the connective-free equality
//!     shortcut, `spatial_matcher.rs:178-181`);
//!  2. an `EMinus` expression in SEND DATA is evaluated by `eval_send`
//!     (`reduce.rs:1108-1115`, EMinus `:2105-2113`), so `probe!(fuel - 1)` re-sends the
//!     DECREMENTED ground integer, not the unevaluated expression;
//!  3. **arm order is load-bearing (AM-7)**: `wrapping_sub` + a mis-ordered wildcard-first
//!     case list would decrement `0` to `-1` and cascade negatively forever (the ground `0`
//!     case would never match again). Driving fuel from 2 TO EXHAUSTION catches a
//!     mis-ordering as a hang/wrong-count — a single-decrement probe would not.
//!
//! The probe is one PERSISTENT receiver on a GPrivate channel (the driver's `^drive`
//! discipline: in-Rho rendezvous are GPrivate; only observation channels are GString)
//! matching `[fuel]` data:
//!
//! ```text
//! contract ⌜probe⌝(@fuel) = {
//!   match fuel {
//!     0 => @"p2:exhausted"!(fuel)                        // ground GInt(0) case FIRST
//!     _ => { ⌜probe⌝!(fuel - 1) | @"p2:ledger"!("dec") } // wildcard SECOND
//!   }
//! } | ⌜probe⌝!(2)
//! ```
//!
//! Expected: exactly 2 ledger data ("dec", "dec"), exactly 1 exhaustion datum (`0`), and
//! termination (the evaluation quiesces — a mis-ordered arm list would never quiesce).
//!
//! The readback goes through the NEW A-S5.2 observation-set API
//! ([`run_installed_program_with_call_and_read_observation_set`]) so this file also
//! unit-tests that surface against hand-built programs (the second test populates all four
//! channels).
#![cfg(feature = "runtime-report")]

use mettail_rholang_codegen::{reflect_ground_term_par, GroundTerm};
use mettail_rholang_runtime::{
    par_as_runtime_observation_value, run_installed_program_with_call_and_read_observation_set,
    DriveObservationChannels,
};
use mettail_runtime::RuntimeObservationValue;
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EMinus, Expr, MatchCase, Par, Receive, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gint_par, new_gstring_par, new_match_par, new_send_par,
    new_wildcard_par,
};

/// The probe's GPrivate rendezvous channel (the `^drive` discipline: in-Rho-only
/// channels are unforgeable, never GString).
fn probe_channel() -> Par {
    GPrivateBuilder::new_par_from_string("a-s5-p2-fuel-probe".to_string())
}

/// A GString observation-channel `Par` (send-position channel).
fn gstring_channel(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// The persistent fuel-probe receiver (see the module docs for the Rholang shape).
fn probe_receiver() -> Par {
    // The one receive formal `@fuel` binds innermost: `BoundVar(0)` in the body.
    let fuel_bits = create_bit_vector(&[0]);

    // 0-arm (ground `GInt(0)` pattern, FIRST — AM-7): `@"p2:exhausted"!(fuel)`.
    let exhausted_send = new_send_par(
        gstring_channel("p2:exhausted"),
        vec![new_boundvar_par(0, Vec::new(), false)],
        false,
        fuel_bits.clone(),
        false,
        fuel_bits.clone(),
        false,
    );

    // Wildcard arm (SECOND): `⌜probe⌝!(fuel - 1) | @"p2:ledger"!("dec")` — the decrement is
    // an `EMinus` IN THE SEND DATUM (`eval_send` evaluates it; probe fact 2).
    let mut decrement_datum = Par::default();
    decrement_datum.exprs = vec![Expr {
        expr_instance: Some(ExprInstance::EMinusBody(EMinus {
            p1: Some(new_boundvar_par(0, Vec::new(), false)),
            p2: Some(new_gint_par(1, Vec::new(), false)),
        })),
    }];
    decrement_datum.locally_free = fuel_bits.clone();
    let resend = new_send_par(
        probe_channel(),
        vec![decrement_datum],
        false,
        fuel_bits.clone(),
        false,
        fuel_bits.clone(),
        false,
    );
    let ledger_send = new_send_par(
        gstring_channel("p2:ledger"),
        vec![new_gstring_par("dec".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    let wildcard_body = resend.append(ledger_send);

    // `match fuel { 0 => …exhausted… ; _ => …decrement… }` — GROUND `GInt(0)` case FIRST.
    let match_par = new_match_par(
        new_boundvar_par(0, Vec::new(), false),
        vec![
            MatchCase {
                pattern: Some(new_gint_par(0, Vec::new(), false)),
                source: Some(exhausted_send),
                free_count: 0,
                guard: None,
            },
            MatchCase {
                pattern: Some(new_wildcard_par(Vec::new(), true)),
                source: Some(wildcard_body),
                free_count: 0,
                guard: None,
            },
        ],
        fuel_bits.clone(),
        false,
        fuel_bits,
        false,
    );

    // The persistent contract `for(@fuel <= ⌜probe⌝){ … }` (closed: 1 formal, body free = {0}).
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(probe_channel()),
            remainder: None,
            free_count: 1,
        }],
        body: Some(match_par),
        persistent: true,
        peek: false,
        bind_count: 1,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    let mut par = Par::default();
    par.receives = vec![receive];
    par
}

/// ★ Probe P2 (AM-7): drive fuel from 2 TO EXHAUSTION on the live reducer — exactly 2
/// decrements, exactly 1 exhaustion datum (`0`), termination. A mis-ordered case list
/// (wildcard first) would never exhaust (`0 - 1 = -1`, negative cascade) and a
/// non-evaluated `EMinus` datum would never reach the ground `0` — both surface here as a
/// hang or a wrong count, so a green run pins ALL THREE reducer facts the driver's fuel
/// arm depends on.
#[tokio::test]
async fn p2_gint_zero_first_arm_order_drives_fuel_from_two_to_exhaustion() {
    let seed = new_send_par(
        probe_channel(),
        vec![new_gint_par(2, Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    let channels = DriveObservationChannels {
        out: "p2:unused-out".to_string(),
        fired: "p2:ledger".to_string(),
        err: "p2:unused-err".to_string(),
        fuel: "p2:exhausted".to_string(),
    };

    let set = run_installed_program_with_call_and_read_observation_set(
        &probe_receiver(),
        &seed,
        &channels,
    )
    .await
    .expect("the fuel probe must run to quiescence on the reducer");

    // Exactly 2 decrements: fuel 2 → 1 → 0.
    assert_eq!(
        set.fired_labels()
            .expect("every ledger datum is a ground GString"),
        vec!["dec".to_string(), "dec".to_string()],
        "fuel 2 must decrement exactly twice before the ground 0 case fires"
    );
    // Exactly 1 exhaustion datum, and it is the ground 0 the first case matched.
    assert_eq!(set.fuel_data.len(), 1, "exactly one exhaustion datum must rest");
    assert_eq!(
        par_as_runtime_observation_value(&set.fuel_data[0]),
        Some(RuntimeObservationValue::Int(0)),
        "the exhaustion datum is the matched ground 0"
    );
    // The unused channels are empty (nothing leaks across channels).
    assert!(set.out_values.is_empty(), "the probe publishes nothing on OUT");
    assert!(set.err_data.is_empty(), "the probe publishes nothing on the err channel");
}

/// F7 readback-API unit test: a hand-built program that populates ALL FOUR observation
/// channels — a reflected term on OUT (exercising the fail-loud decode), a GString rule
/// label on the ledger, a GString payload on err, a GInt remnant on fuel — read back in one
/// execution.
#[tokio::test]
async fn observation_set_reads_all_four_channels_from_one_execution() {
    const FP: &str = "readback-probe-fp";
    let out_datum = reflect_ground_term_par(
        &GroundTerm::new("Pair", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]),
        FP,
    );
    let program = new_send_par(
        gstring_channel("u:out"),
        vec![out_datum],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
    .append(new_send_par(
        gstring_channel("u:fired"),
        vec![new_gstring_par("RuleX".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    ))
    .append(new_send_par(
        gstring_channel("u:err"),
        vec![new_gstring_par("boom".to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    ))
    .append(new_send_par(
        gstring_channel("u:fuel"),
        vec![new_gint_par(7, Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    ));
    let channels = DriveObservationChannels {
        out: "u:out".to_string(),
        fired: "u:fired".to_string(),
        err: "u:err".to_string(),
        fuel: "u:fuel".to_string(),
    };

    let set = run_installed_program_with_call_and_read_observation_set(
        &program,
        &Par::default(),
        &channels,
    )
    .await
    .expect("the four-channel program must run to quiescence");

    // OUT decodes through the reflected-term ABI.
    assert_eq!(
        set.out_values,
        vec![RuntimeObservationValue::Term {
            constructor: "Pair".to_string(),
            children: vec![
                RuntimeObservationValue::Term {
                    constructor: "A".to_string(),
                    children: Vec::new()
                },
                RuntimeObservationValue::Term {
                    constructor: "B".to_string(),
                    children: Vec::new()
                },
            ],
        }],
        "OUT decodes the reflected Pair(A, B)"
    );
    // The ledger decodes to its rule label.
    assert_eq!(
        set.fired_labels()
            .expect("the ledger datum is a ground GString"),
        vec!["RuleX".to_string()]
    );
    // The err / fuel channels surface their raw resting data.
    assert_eq!(set.err_data.len(), 1);
    assert_eq!(
        par_as_runtime_observation_value(&set.err_data[0]),
        Some(RuntimeObservationValue::Text("boom".to_string()))
    );
    assert_eq!(set.fuel_data.len(), 1);
    assert_eq!(
        par_as_runtime_observation_value(&set.fuel_data[0]),
        Some(RuntimeObservationValue::Int(7))
    );
}
