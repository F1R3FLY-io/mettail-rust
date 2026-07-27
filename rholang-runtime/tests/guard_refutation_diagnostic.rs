//! **S-D0R — the refutation diagnostic.**
//!
//! A guard the compiler can prove statically FALSE is reported (`W1 GuardStaticallyFalse`) and
//! **nothing else happens**: the artifact is byte-identical, the exit status is success, and the
//! never-firing receive is emitted exactly as written.
//!
//! # Why refutation may not touch the artifact
//!
//! A `for` whose guard can never hold is *not* dead code. It is a **resting, observable
//! continuation**:
//!
//! ```text
//!    for(x <- c where false){ … } | c!(2)
//!         │                            │
//!         └─ stays in the normal form  └─ stays UNCONSUMED on `c`
//!            (and in the state hash,      (a validator replaying the deploy must
//!             and in tuplespace storage)   observe the same resting datum)
//! ```
//!
//! Six tests in the corpus assert precisely that shape — `assert_host_guard_on` requires the
//! normal form to still contain both the `where` clause and the unconsumed send, and the
//! `assert_never_reaches` family requires the datum to stay put. Deleting the receive, or
//! folding it to `Nil`, would change every one of those observables. So refutation is a
//! DIAGNOSTIC, never a transformation.
//!
//! Contrast [`GuardDischarge::Discharged`](mettail_rholang_runtime::GuardDischarge::Discharged),
//! which *does* change the artifact — soundly, because an omitted guard and a guard that
//! evaluates `true` drive `check_commit` to the identical verdict.

#![cfg(feature = "rholang-runtime")]

use std::sync::{Arc, Mutex};

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::{
    clear_guard_discharge_report, lower_rholang_proc_with_options, take_guard_discharge_report,
    LoweringOptions, GUARD_DISCHARGE_TARGET,
};
use mettail_runtime::clear_var_cache;
use models::rhoapi::Par;
use prost::Message;
use tracing::field::{Field, Visit};
use tracing::subscriber::with_default;
use tracing::{Event, Level, Metadata, Subscriber};

// ════════════════════════════════════════════════════════════════════════════════════════════
// A capturing subscriber
// ════════════════════════════════════════════════════════════════════════════════════════════

/// One captured `tracing` event, reduced to what the diagnostic contract is about.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CapturedEvent {
    target: String,
    level: String,
    /// `(field-name, rendered-value)` pairs, in emission order.
    fields: Vec<(String, String)>,
}

impl CapturedEvent {
    fn field(&self, name: &str) -> Option<&str> {
        self.fields
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v.as_str())
    }
}

#[derive(Default)]
struct FieldCollector(Vec<(String, String)>);

impl Visit for FieldCollector {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        self.0
            .push((field.name().to_string(), format!("{value:?}")));
    }
    fn record_str(&mut self, field: &Field, value: &str) {
        self.0.push((field.name().to_string(), value.to_string()));
    }
    fn record_u64(&mut self, field: &Field, value: u64) {
        self.0.push((field.name().to_string(), value.to_string()));
    }
    fn record_i64(&mut self, field: &Field, value: i64) {
        self.0.push((field.name().to_string(), value.to_string()));
    }
    fn record_bool(&mut self, field: &Field, value: bool) {
        self.0.push((field.name().to_string(), value.to_string()));
    }
}

/// A minimal `Subscriber` that records every event verbatim. Deliberately not
/// `tracing-subscriber`'s layered stack: the contract under test is "the event reaches a
/// subscriber with these fields", and a bespoke sink measures exactly that with no filtering
/// layer able to mask a regression.
#[derive(Clone, Default)]
struct EventSink(Arc<Mutex<Vec<CapturedEvent>>>);

impl EventSink {
    fn events(&self) -> Vec<CapturedEvent> {
        self.0.lock().expect("event sink poisoned").clone()
    }
}

/// The captured events emitted on `target`, in emission order.
fn sink_events_on_target<'a>(events: &'a [CapturedEvent], target: &str) -> Vec<&'a CapturedEvent> {
    events
        .iter()
        .filter(|event| event.target == target)
        .collect()
}

impl Subscriber for EventSink {
    fn enabled(&self, _metadata: &Metadata<'_>) -> bool {
        true
    }
    fn new_span(&self, _span: &tracing::span::Attributes<'_>) -> tracing::span::Id {
        tracing::span::Id::from_u64(1)
    }
    fn record(&self, _span: &tracing::span::Id, _values: &tracing::span::Record<'_>) {}
    fn record_follows_from(&self, _span: &tracing::span::Id, _follows: &tracing::span::Id) {}
    fn event(&self, event: &Event<'_>) {
        let mut collector = FieldCollector::default();
        event.record(&mut collector);
        self.0
            .lock()
            .expect("event sink poisoned")
            .push(CapturedEvent {
                target: event.metadata().target().to_string(),
                level: event.metadata().level().to_string(),
                fields: collector.0,
            });
    }
    fn enter(&self, _span: &tracing::span::Id) {}
    fn exit(&self, _span: &tracing::span::Id) {}
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Harness
// ════════════════════════════════════════════════════════════════════════════════════════════

fn program(guard: &str) -> String {
    format!(r#"{{ for(x <- c where {guard}){{ out!(*x) }} | c!(2) }}"#)
}

/// Parse once, lower under `options`, capturing every `tracing` event the lowering emits and
/// the guard-discharge report it accumulated.
fn lower_capturing(
    source: &str,
    options: LoweringOptions,
) -> (Par, Vec<CapturedEvent>, mettail_rholang_runtime::GuardDischargeReport) {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"));
    let sink = EventSink::default();
    let (par, report) = with_default(sink.clone(), || {
        clear_guard_discharge_report();
        let par = lower_rholang_proc_with_options(&proc, options)
            .unwrap_or_else(|err| panic!("rholang lowering failed for {source:?}: {err:?}"));
        (par, take_guard_discharge_report())
    });
    (par, sink.events(), report)
}

/// Lower the SAME parsed `Proc` twice under the two switch positions, so the only independent
/// variable is `guard_discharge` (see the byte-identity gate's note on `HashBag` ordering).
fn lower_both(source: &str) -> (Par, Par) {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err:?}"));
    let on = lower_rholang_proc_with_options(&proc, LoweringOptions::PRODUCTION)
        .unwrap_or_else(|err| panic!("lowering failed: {err:?}"));
    let off = lower_rholang_proc_with_options(&proc, LoweringOptions::NO_DISCHARGE)
        .unwrap_or_else(|err| panic!("lowering failed: {err:?}"));
    (on, off)
}

/// The statically-false guards in the corpus (one per distinct shape the refuter must reach).
const REFUTED_GUARDS: &[&str] = &[
    "false",
    "true implies false",
    "3 > 2 implies 2 > 3",
    "true implies false or false",
    "2 > 3",
    "1 == 2",
    "Set(1, 2) == Set(1, 3)",
    "not true",
    "true and false",
    "false or false",
    "x matches false", // folded to the constant `false` by `lower_proc` before S-D0 sees it
];

// ════════════════════════════════════════════════════════════════════════════════════════════
// The contract
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ A refuted guard leaves the artifact BYTE-IDENTICAL.
#[test]
fn refutation_never_changes_the_artifact() {
    for guard in REFUTED_GUARDS {
        let source = program(guard);
        let (on, off) = lower_both(&source);
        assert_eq!(
            on.encode_to_vec(),
            off.encode_to_vec(),
            "a REFUTED guard must not change the emitted `Par`: {guard:?}"
        );
        let condition = on
            .receives
            .first()
            .and_then(|receive| receive.condition.clone())
            .unwrap_or_else(|| panic!("a refuted guard must still be emitted: {guard:?}"));
        assert!(
            mettail_rholang_runtime::is_binder_closed(&condition),
            "precondition: {guard:?} must be binder-closed"
        );
        assert_eq!(
            mettail_rholang_runtime::machine_verdict(&condition),
            Some(false),
            "precondition: {guard:?} must be statically FALSE"
        );
    }
}

/// ★ The `W1 GuardStaticallyFalse` diagnostic actually fires — on
/// [`GUARD_DISCHARGE_TARGET`], at DEBUG, carrying `code`, `site` and `guard`.
#[test]
fn w1_guard_statically_false_is_emitted_with_its_code_site_and_guard() {
    let source = program("true implies false");
    let (_par, events, report) = lower_capturing(&source, LoweringOptions::PRODUCTION);

    let guard_events = sink_events_on_target(&events, GUARD_DISCHARGE_TARGET);
    let w1 = guard_events
        .iter()
        .find(|event| event.field("code") == Some("W1"))
        .unwrap_or_else(|| {
            panic!("no `W1` event on {GUARD_DISCHARGE_TARGET}; captured: {guard_events:#?}")
        });

    assert_eq!(w1.level, Level::DEBUG.to_string(), "W1 is a DEBUG diagnostic, not an error");
    assert_eq!(w1.field("site"), Some("0"), "the first guard site is site 0");
    assert!(
        w1.field("guard").is_some_and(|g| !g.is_empty()),
        "W1 must name the guard it refuted; got {:?}",
        w1.field("guard")
    );
    assert!(
        w1.field("message")
            .is_some_and(|m| m.contains("statically FALSE")),
        "W1's message must say what it found; got {:?}",
        w1.field("message")
    );

    // …and the same fact is on the report.
    assert_eq!(report.refuted.len(), 1, "one refutation recorded");
    assert_eq!(report.refuted[0].site, 0);
    assert_eq!(report.discharged, 0);
    assert_eq!(report.residual, 0);
    assert_eq!(report.disagreements, 0);
}

/// The report is a faithful census of the lowering: one entry per guard site, with the
/// refutations carrying their `W1` events.
#[test]
fn the_lowering_report_censuses_every_guard_site() {
    // Three guards in one program: one discharges, one is refuted, one is residual.
    let source = r#"{ for(x <- c where true){ out!(*x) }
                    | for(y <- d where false){ out!(*y) }
                    | for(z <- e where z > 0){ out!(*z) }
                    | c!(1) | d!(2) | e!(3) }"#;
    let (_par, _events, report) = lower_capturing(source, LoweringOptions::PRODUCTION);
    assert_eq!(report.total(), 3, "three guard sites, three report entries: {report:?}");
    assert_eq!(report.discharged, 1, "`true` discharges: {report:?}");
    assert_eq!(report.refuted.len(), 1, "`false` is refuted: {report:?}");
    assert_eq!(report.residual, 1, "`z > 0` is residual: {report:?}");
    assert_eq!(report.disagreements, 0);
}

/// With the switch OFF nothing is classified at all, so no diagnostic is emitted — the harness
/// arm is silent as well as byte-identical.
#[test]
fn the_switch_off_arm_emits_no_guard_diagnostic() {
    let source = program("false");
    let (_par, events, report) = lower_capturing(&source, LoweringOptions::NO_DISCHARGE);
    assert!(
        events
            .iter()
            .all(|event| event.target != GUARD_DISCHARGE_TARGET),
        "discharge-OFF must not classify, and therefore must not diagnose: {events:#?}"
    );
    assert_eq!(report.total(), 0, "no site is classified with the switch off: {report:?}");
}

/// Every refuted corpus guard raises exactly one `W1`, and none of them raises the
/// DISAGREEMENT warning (which would be a divergence-A-shaped defect).
#[test]
fn every_refuted_corpus_guard_raises_exactly_one_w1_and_no_disagreement() {
    for guard in REFUTED_GUARDS {
        let source = program(guard);
        let (_par, events, report) = lower_capturing(&source, LoweringOptions::PRODUCTION);
        let w1s = events
            .iter()
            .filter(|event| {
                event.target == GUARD_DISCHARGE_TARGET && event.field("code") == Some("W1")
            })
            .count();
        assert_eq!(w1s, 1, "{guard:?} must raise exactly one W1; events: {events:#?}");
        assert_eq!(report.refuted.len(), 1, "{guard:?}");
        assert_eq!(
            report.disagreements, 0,
            "{guard:?} must not trip the evaluator-disagreement fence"
        );
        assert!(
            events
                .iter()
                .all(|event| event.level != Level::WARN.to_string()),
            "{guard:?} must raise no WARN — a WARN on this target is an evaluator disagreement"
        );
    }
}

/// A DISCHARGED guard raises no `W1` (it is not false) and no warning (the evaluators agreed).
#[test]
fn a_discharged_guard_raises_no_w1() {
    let source = program("true");
    let (par, events, report) = lower_capturing(&source, LoweringOptions::PRODUCTION);
    assert!(
        par.receives
            .first()
            .is_some_and(|receive| receive.condition.is_none()),
        "precondition: this guard discharges"
    );
    assert!(
        events.iter().all(|event| event.field("code") != Some("W1")),
        "a discharged guard is not statically false: {events:#?}"
    );
    assert_eq!(report.discharged, 1);
    assert_eq!(report.refuted.len(), 0);
}
