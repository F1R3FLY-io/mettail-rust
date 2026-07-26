//! A-S5.6 NO-REGRESSION byte-identity pins (plan v2 §8 row A-S5.6; the task's scope
//! guard): the PRODUCTION FLIP is pure WRAPPER routing — `repl/src/rho_backends.rs` moves
//! Lambda + Ambient onto the generated `rho_net_drive_invocation_to` — so every emitted
//! driver artifact must stay byte-for-byte unchanged. Pinned by prost-encoding the
//! generated `Par`s and comparing (length, hash) against goldens CAPTURED AT `a9193914`
//! (the pre-flip HEAD, `scratchpad/as56_byte_pin_capture.log`):
//!
//! * production **Lambda**'s `^drive` receiver family `Par` and its full installed
//!   program (β seed + 5 TRS receivers + driver, 7 receives) — STILL the `a9193914`
//!   values (the A-S5.8 no-regression half: a non-float language's emissions are
//!   byte-identical);
//! * production **Ambient**'s `^drive` receiver family `Par` (the A-S5.5 bag/nested-AC
//!   driver + the three per-rule AC-carrier receivers) and its full installed program —
//!   RE-CAPTURED at A-S5.8 (float-routed firing emissions + the 8-receiver `^float`
//!   family, 7 → 15 receives; the per-value diffs are explained on the pin itself).
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
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 4357 → 4429 = +72 = 2 × 36, exactly.
        (4429, 0x0cfebce014446d5d),
        "the Lambda ^drive receiver family must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914)"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Lambda installs");
    assert_eq!(installed.receives.len(), 7, "β seed + 5 TRS + ^drive");
    assert_eq!(
        par_fingerprint(&installed),
        // ★ #36 S3 RE-CAPTURE (12807, 0xa6eaeb15696e7583) → (12824, 0x89ea12b54e7c61a0) —
        // the SAME artifact and the SAME delta as the `a_s5_5` pin (these two pins have
        // always agreed; S3 keeps them agreeing). EXPLAINED DIFF: `Z`/`S` → `^Z`/`^S`
        // grows each Peano tag string by one byte inside the subst-TRS receivers; the
        // `^drive` pin above is UNCHANGED (4357).
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 12824 → 12932 = +108 = 3 × 36, exactly.
        (12932, 0x87c0768a017c399d),
        "the full Lambda installed program must be byte-identical to the pre-A-S5.6 \
         golden (captured at a9193914; RE-CAPTURED at #36 S3, diff explained above)"
    );
}

/// ★ The Ambient pin, RE-CAPTURED at A-S5.8 (the pin file's re-capture protocol — a
/// DELIBERATE move, diff explained): the `^drive` receiver family moved because BOTH
/// firing-emission seams now route every contractum through the installed `^float`
/// dispatcher before the re-drive (decision Q-AB = A — `for(@c <- r){ new rf {
/// ⌜^float⌝!(c, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel - 1, ret) } } }`), growing the
/// drive `Par` 29640 → 33330 bytes (the drive still has exactly its 4 receives — the
/// `^drive` receiver + 3 UNCHANGED carriers); and the installed program gained the
/// 8-receiver `^float` family (dispatcher + `^float-merge:PPar` + 4 `^float-hoist` +
/// first-time `^shift`/`^cmp`), 7 → 15 receives, 31301 → 50744 bytes. Captured at the
/// A-S5.8 leg-1 tree (`scratchpad/as58_pin_capture.log`); the Lambda pins above are
/// UNCHANGED (the A-S5.8 no-regression half).
#[test]
fn ambient_driver_par_is_byte_identical_to_the_a_s5_8_golden() {
    let plan = plan_for(include_str!("../../languages/src/ambient.rs"));
    let drive = plan
        .rho_net_lowered()
        .drive()
        .expect("production Ambient is drive-admitted");
    assert_eq!(
        par_fingerprint(drive),
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 36836 → 39223 = +2387 = 66 × 36 + 11, where the 11 is the extra
        // prost varint length-prefix byte of the 11 names that crossed 127 bytes.
        (39223, 0x3f9161ce0bfe0793),
        "the Ambient ^drive receiver family must be byte-identical to the A-S5.8 golden \
         (float-routed firing emissions; captured at the A-S5.8 leg-1 tree)"
    );
    let installed = plan
        .installed_rho_net_program_par()
        .expect("production Ambient installs");
    assert_eq!(
        installed.receives.len(),
        15,
        "3 AC σ-receivers + ^drive + 3 carriers + the 8 A-S5.8 ^float-family receivers"
    );
    assert_eq!(
        par_fingerprint(&installed),
        // ★ #36 S3 RE-CAPTURE (56314, 0x4d95f2df46f3450a) → (56328, 0x021489df5ccd86cd).
        // EXPLAINED DIFF: `Z`/`S` → `^Z`/`^S`. Ambient's delta is +14 where Lambda's is
        // +17 because the two programs contain different counts of Peano tag occurrences
        // (Ambient's `^float` family carries no Peano node, and its `^drive` pin above is
        // likewise UNCHANGED at 36836); the delta is one byte per occurrence, not a
        // constant. Proof that nothing else moved: inverting S3 at its source restores
        // this pin exactly.
        // ★ #36 S6 RE-CAPTURE — INV-S6 fingerprint-scopes every driver-network channel
        // name, so every `sa:`/`loc:`/`col:`/`cap:`/`ac:` name in the emission grows by
        // the scope `"{fingerprint}/"` (36 bytes: 35-char fingerprint + separator).
        // PROVEN to be EXACTLY and ONLY that insertion: inverting the ONE line that adds
        // it (`rho_net::scoped_channel_name`) restores this pin byte-for-byte, and the
        // byte delta is fully accounted below. Nothing else moved — the receive counts
        // are unchanged.
        // ACCOUNTING: 56328 → 59442 = +3114 = 86 × 36 + 18 (18 names crossed 127 bytes).
        (59442, 0xa8ae1dcbd6979830),
        "the full Ambient installed program must be byte-identical to the A-S5.8 golden \
         (the ^float family appended; captured at the A-S5.8 leg-1 tree; RE-CAPTURED at \
         #36 S3, diff explained above)"
    );
}
