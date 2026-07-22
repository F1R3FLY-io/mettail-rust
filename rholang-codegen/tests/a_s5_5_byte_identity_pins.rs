//! A-S5.5 NO-REGRESSION byte-identity pins (plan v2 §8 row A-S5.5; the task's item 5):
//! the AC-arm extension of the quiescence driver must leave every PRE-EXISTING emitted
//! artifact byte-for-byte unchanged. Pinned by prost-encoding the generated `Par`s and
//! comparing (length, hash) against goldens CAPTURED AT `ee1514da` (the pre-A-S5.5 HEAD,
//! `scratchpad/as55_golden_capture.log`):
//!
//! * production **Lambda**'s `^drive` receiver family `Par` — the driver codegen was
//!   restructured (subject threading, guarded matches, the `DriveArm` split) but Lambda
//!   compiles zero AC arms / bag arms / carriers, so its emission is BYTE-IDENTICAL;
//! * production **Lambda**'s full installed program (β seed + 5 TRS receivers + driver);
//! * production **Ambient**'s three LEGACY AC σ-receivers (`InRule` / `OutRule` /
//!   `OpenRule` — the non-driver locate-all path is untouched by A-S5.5).
//!
//! The hash is `std::hash::DefaultHasher` over the prost bytes — deterministic across
//! processes (SipHash-1-3 with fixed keys) — paired with the exact byte length; a
//! codegen change that alters any pinned emission flips at least one of the two.
//!
//! These goldens are FINGERPRINT-SENSITIVE: they legitimately move when
//! `languages/src/lambda.rs` / `languages/src/ambient.rs` (or the reflection ABI)
//! changes — re-capture then, with the diff explained in the commit.

use std::hash::{Hash, Hasher};

use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, RhoCoverageEvidence, RhoDefaultBackendPlan,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use prost::Message;

/// Extract the `language! { … }` body from a `languages/src/*.rs` source (the a_s5c
/// production-gate reconstruction path).
fn extract_language_body(source: &str) -> &str {
    let start = source.find("language! {").expect("language! block") + "language! {".len();
    let end = source.rfind('}').expect("closing brace");
    &source[start..end]
}

fn plan_for(source: &str) -> RhoDefaultBackendPlan {
    let body = extract_language_body(source);
    let def: LanguageDef =
        reconstruct_language_def(body).expect("the production body must reconstruct");
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    plan_rho_default_backend(&def, requirements).expect("the production language must plan")
}

/// The (length, `DefaultHasher`) fingerprint of a prost-encoded `Par`.
fn par_fingerprint(par: &models::rhoapi::Par) -> (usize, u64) {
    let bytes = par.encode_to_vec();
    let mut hasher = std::hash::DefaultHasher::new();
    bytes.hash(&mut hasher);
    (bytes.len(), hasher.finish())
}

/// ★ Item 5 (the Lambda no-regression pin): the emitted `^drive` receiver family for the
/// production Lambda is BYTE-IDENTICAL pre/post A-S5.5, and so is the full installed
/// program (β seed + five subst-TRS receivers + the driver, 7 receives).
#[test]
fn lambda_driver_par_is_byte_identical_to_the_pre_a_s5_5_golden() {
    let plan = plan_for(include_str!("../../languages/src/lambda.rs"));
    let lowered = plan.rho_net_lowered();
    let drive = lowered.drive().expect("production Lambda is drive-admitted");
    assert_eq!(
        par_fingerprint(drive),
        (4357, 0xcd74c7d13495d5d5),
        "the Lambda ^drive receiver family must be byte-identical to the pre-A-S5.5 \
         golden (captured at ee1514da)"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Lambda installs");
    assert_eq!(installed.receives.len(), 7, "β seed + 5 TRS + ^drive");
    assert_eq!(
        par_fingerprint(&installed),
        (12807, 0xa6eaeb15696e7583),
        "the full Lambda installed program must be byte-identical to the pre-A-S5.5 \
         golden (captured at ee1514da)"
    );
}

/// ★ The legacy-path pin: Ambient's three installed AC σ-receivers (`InRule` nested,
/// `OutRule` nested — the A-S5.4b C-G redeclaration — and `OpenRule` flat structural)
/// are BYTE-IDENTICAL pre/post A-S5.5. The driver's carrier receivers are NEW receives
/// appended to the drive program; the non-driver locate-all path is untouched.
#[test]
fn ambient_legacy_ac_receivers_are_byte_identical_to_the_pre_a_s5_5_goldens() {
    let plan = plan_for(include_str!("../../languages/src/ambient.rs"));
    let lowered = plan.rho_net_lowered();
    let goldens: &[(&str, (usize, u64))] = &[
        ("rule:rewrite:0:InRule", (610, 0xf464b25652689343)),
        ("rule:rewrite:1:OutRule", (627, 0x08d041e371a31213)),
        ("rule:rewrite:2:OpenRule", (533, 0xa7f563b1a93f4595)),
    ];
    for (rule_id, expected) in goldens {
        let par = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == *rule_id)
            .and_then(|rule| rule.par())
            .unwrap_or_else(|| panic!("Ambient must materialize {rule_id}"));
        assert_eq!(
            &par_fingerprint(par),
            expected,
            "the legacy {rule_id} σ-receiver must be byte-identical to the pre-A-S5.5 \
             golden (captured at ee1514da)"
        );
    }
}

