//! A-S5.6 NO-REGRESSION byte-identity pins (plan v2 §8 row A-S5.6; the task's scope
//! guard): the PRODUCTION FLIP is pure WRAPPER routing — `repl/src/rho_backends.rs` moves
//! Lambda + Ambient onto the generated `rho_net_drive_invocation_to` — so every emitted
//! driver artifact must stay byte-for-byte unchanged. Pinned by prost-encoding the
//! generated `Par`s and comparing (length, hash) against goldens CAPTURED AT `a9193914`
//! (the pre-flip HEAD, `scratchpad/as56_byte_pin_capture.log`):
//!
//! * production **Lambda**'s `^drive` receiver family `Par` and its full installed
//!   program (β seed + 5 TRS receivers + driver, 7 receives);
//! * production **Ambient**'s `^drive` receiver family `Par` (the A-S5.5 bag/nested-AC
//!   driver + the three per-rule AC-carrier receivers) and its full installed program.
//!
//! The hash is `std::hash::DefaultHasher` over the prost bytes — deterministic across
//! processes (SipHash-1-3 with fixed keys) — paired with the exact byte length; a codegen
//! change that alters any pinned emission flips at least one of the two.
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

/// CAPTURE (run once at the pre-flip HEAD, teed to `scratchpad/as56_byte_pin_capture.log`):
/// prints every pinned fingerprint. Kept as the re-capture path for legitimate
/// fingerprint moves.
#[test]
fn capture_a_s5_6_driver_fingerprints() {
    for (name, source) in [
        ("Lambda", include_str!("../../languages/src/lambda.rs")),
        ("Ambient", include_str!("../../languages/src/ambient.rs")),
    ] {
        let plan = plan_for(source);
        let lowered = plan.rho_net_lowered();
        let drive = lowered.drive().expect("the production language is drive-admitted");
        let installed =
            plan.installed_rho_net_program_par().expect("the production language installs");
        println!(
            "{name}: drive = {:?}; installed = {:?} ({} receives)",
            par_fingerprint(drive),
            par_fingerprint(&installed),
            installed.receives.len(),
        );
    }
}

/// ★ The Lambda no-regression pin: the emitted `^drive` receiver family and the full
/// installed program (β seed + five subst-TRS receivers + the driver, 7 receives) are
/// BYTE-IDENTICAL across the A-S5.6 flip commits. (These values also equal the A-S5.5
/// goldens — the driver emission has been stable since `ee1514da`.)
#[test]
fn lambda_driver_par_is_byte_identical_to_the_pre_a_s5_6_golden() {
    let plan = plan_for(include_str!("../../languages/src/lambda.rs"));
    let drive = plan
        .rho_net_lowered()
        .drive()
        .expect("production Lambda is drive-admitted");
    assert_eq!(
        par_fingerprint(drive),
        (3659, 0x320f25974908cc34),
        "the Lambda ^drive receiver family must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914)"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Lambda installs");
    assert_eq!(installed.receives.len(), 7, "β seed + 5 TRS + ^drive");
    assert_eq!(
        par_fingerprint(&installed),
        (11067, 0x9e919040a08bd1fc),
        "the full Lambda installed program must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914)"
    );
}

/// ★ The Ambient no-regression pin: the emitted `^drive` receiver family (the A-S5.5
/// bag/nested-AC driver + the three per-rule AC-carrier receivers) and the full installed
/// program (3 AC σ-receivers + `^drive` + 3 carriers, 7 receives) are BYTE-IDENTICAL
/// across the A-S5.6 flip commits.
#[test]
fn ambient_driver_par_is_byte_identical_to_the_pre_a_s5_6_golden() {
    let plan = plan_for(include_str!("../../languages/src/ambient.rs"));
    let drive = plan
        .rho_net_lowered()
        .drive()
        .expect("production Ambient is drive-admitted");
    assert_eq!(
        par_fingerprint(drive),
        (29640, 0xdf369fa1497e84c3),
        "the Ambient ^drive receiver family must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914)"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Ambient installs");
    assert_eq!(installed.receives.len(), 7, "3 AC σ-receivers + ^drive + 3 carriers");
    assert_eq!(
        par_fingerprint(&installed),
        (31301, 0xf7ff78aeca8ce63c),
        "the full Ambient installed program must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914)"
    );
}
