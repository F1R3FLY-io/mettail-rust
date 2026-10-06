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
//! changes — re-capture then, with the diff explained in the commit. The current
//! tuples were re-captured after the c387f4cc v2 language/fragment identity change;
//! the original captures above remain the historical A-S5.5 baseline.

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
    let drive = lowered
        .drive()
        .expect("production Lambda is drive-admitted");
    assert_eq!(
        par_fingerprint(drive),
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 4357 → 4429 = +72 = 2 scope insertions × 36, exactly (no name
        // crossed prost's 127-byte varint length-prefix boundary).
        // v2 RE-CAPTURE (c387f4cc): 4429 → 6429. The language fingerprint and
        // RhoNet fragment digests now carry 64 rather than 16 hex digits in
        // generated names; protobuf length prefixes can grow with those names.
        (6429, 0xbef07b595baddc0c),
        "the Lambda ^drive receiver family must match the reviewed v2 byte golden"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Lambda installs");
    assert_eq!(installed.receives.len(), 7, "β seed + 5 TRS + ^drive");
    assert_eq!(
        par_fingerprint(&installed),
        // ★ #36 S3 RE-CAPTURE (12807, 0xa6eaeb15696e7583) → (12824, 0x89ea12b54e7c61a0).
        // EXPLAINED DIFF: `Z`/`S` → `^Z`/`^S`, so each Peano `GPrivate(reflect_tag(…))`
        // tag string in the five subst-TRS receivers grew by one byte. The `^drive`
        // pin above is UNCHANGED (4357) — the driver family emits no Peano node — so the
        // delta is confined to the TRS half. Proof that nothing else moved: inverting S3
        // at its source restores this and every other byte pin exactly (see the `#36 S3`
        // note on `rho_net_subst_trs::reserved_subst_trs_labels`); and the doc-28 RENDERED
        // form of this same program differs from its predecessor only in lines a targeted
        // `.Z)`→`.^Z)` / `.S)`→`.^S)` substitution maps back byte-for-byte.
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 12824 → 12932 = +108 = 3 × 36, exactly.
        // v2 RE-CAPTURE (c387f4cc): 12932 → 18554, for the same identity
        // migration; the structural gate above still requires seven receives.
        (18554, 0x1c20e2739423e4ac),
        "the full Lambda installed program must match the reviewed v2 byte golden"
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
        // ★ #36 S6 RE-CAPTURE — see the note on the pins above. Each σ-receiver carries
        // FIVE scoped names (its `ac:` carrier plus the `loc:`/`cap:` positions it reads),
        // so each grows by 5 × 36 = 180 bytes plus the prost varint length-prefix bytes of
        // the names that crossed 127: InRule +1, OutRule +3, OpenRule +3.
        //   InRule    610 → 791  (+181 = 180 + 1)
        //   OutRule   627 → 810  (+183 = 180 + 3)
        //   OpenRule  533 → 716  (+183 = 180 + 3)
        // v2 RE-CAPTURE (c387f4cc): 791 → 1235, 810 → 1248, 716 → 1109.
        // The same widened language and fragment identities occur in the
        // legacy channels; the three rule IDs and receiver inventory persist.
        ("rule:rewrite:0:InRule", (1235, 0x5b9426c7b797bd71)),
        ("rule:rewrite:1:OutRule", (1248, 0xde1184e72bfbcdd1)),
        ("rule:rewrite:2:OpenRule", (1109, 0xf3d51e5dc9a44c33)),
    ];
    let actual = goldens
        .iter()
        .map(|(rule_id, _)| {
            let par = lowered
                .rules()
                .iter()
                .find(|rule| rule.rule_id() == *rule_id)
                .and_then(|rule| rule.par())
                .unwrap_or_else(|| panic!("Ambient must materialize {rule_id}"));
            (*rule_id, par_fingerprint(par))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual.as_slice(),
        goldens,
        "the three legacy AC σ-receivers must match the reviewed byte goldens"
    );
}
