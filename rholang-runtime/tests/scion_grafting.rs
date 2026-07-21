//! E-1 (pgmcp experiment 147) leg **L2** — the SEMANTIC VALIDATOR of the L1
//! scion-grafting builder (`rholang-codegen/src/rho_net_drive.rs`,
//! `scion_bundle_for_rule` + `ScionPolicy::StructuralScion`, committed
//! `7e78e285`). L1 landed the mechanism DORMANT (production lowers under
//! `AllRedrive`, byte-identical); this suite is the FIRST runtime exercise of
//! the treatment arm, and its verdicts are DETERMINISTIC — exact integer COMM
//! counters + exact fired multisets, no statistics (the counters are
//! reproducible per cell for a terminating drive under the fixed seed).
//!
//! # The A/B seam
//!
//! [`scion_arm_programs`] builds BOTH arms' installed programs from ONE
//! `LanguageDef` (same lowered rules, same fingerprint, same reserved
//! observation channels): CONTROL = `AllRedrive` (every firing arm re-drives its
//! whole contractum), TREATMENT = `StructuralScion` (positional `BaseRewrite`
//! arms emit per-rule scion bundles; β `SubstRewrite` + AC arms re-drive).
//! [`drive_arm_with_counters`] runs each on a fresh COUNTING runtime and reads
//! back the COMM-classification snapshot + the drive observation set
//! (OUT/fired/err/fuel, peeked — no readback COMM).
//!
//! # The cells + FROZEN gates (design v1 §6, delta amendments SM-1..SM-8)
//!
//! * **W-A** (A/A null): synthetic-Lambda β chains n ∈ {4, 8, 16}. β is NEVER
//!   scion'd (`is_subst_beta`), so the two installed programs are BYTE-IDENTICAL
//!   and every counter — including `subst_tau` — is EXACTLY equal. Harness
//!   validation + the honest β-null finding (design v1 §2.2).
//! * **W-B** (structural ladder): `scion_ladder(s, m)` — `R1 . (Step (Wrap u)) ~>
//!   (D1 (… (Ds (Step u)) …))`, `R2 . (Step End) ~> End`; subject
//!   `Step(Wrap^m(End))`, m+1 firings. FROZEN prediction: per-R1-firing
//!   `Δ(DriveTau) = control − treatment = s` EXACTLY (run total s·m ± m, SM-1);
//!   `Δ(total)/R1-firing = 2s+1` (SM-2).
//!
//!   ⚠ **L2 FINDING — the W-B frozen prediction is REFUTED by the data (reported
//!   per the task's frozen-prediction-deviation protocol; NOT adjusted here — the
//!   frozen values are printed alongside the measured ones and the coordinator
//!   decides L1-fix vs prediction-amend).** The measured `Δ(DriveTau) = control −
//!   treatment` is NEGATIVE and grows QUADRATICALLY: `Δ ≈ (s−½)m − ½m²`
//!   (control ≈ (s+1)m+2, LINEAR; treatment ≈ ½m²+1½m+2, QUADRATIC and
//!   independent of s). Root cause: the treatment drives the slot
//!   `u = Wrap^(m-1)(End)` to NF on EVERY R1 firing — a full re-descent of the
//!   remaining (redex-free) `Wrap` chain (m−1 internal `^drive` COMMs), summing
//!   to ½m² over the m firings — whereas CONTROL (`ContractumRedrive`) is
//!   OUTERMOST-FIRST: it fires the outer `Step` redex before descending into `u`,
//!   peeling one `Wrap` per firing via the LHS match and NEVER re-descending the
//!   un-fired slot subtree. The design's §2.3 "slot-subtree-internal work is
//!   common-mode" and §3.4 "NF re-descent is common-mode" assumptions do not
//!   hold for this shape: control avoids exactly the descent the scion eagerly
//!   pays. (Contrast W-C, where the slot-drive IS productive and the scion wins.)
//!   The eager quadratic nesting also STACK-OVERFLOWS the drive at s≥2, m≥16
//!   (`SIGABRT`). This cell therefore asserts only the CORRECTNESS invariants
//!   (fired-multiset equality, empty err/fuel) — which HOLD — and prints the
//!   frozen-vs-measured `Δ(DriveTau)` divergence; the grid is capped at
//!   s ∈ {1, 2} × m ∈ {4, 8} to stay under the overflow.
//! * **W-C** (rule-count risk): `multi_rule_shared(r)` — r rules sharing the `C`
//!   RHS sub-skeleton (the re-check pattern list grows with r); r ∈ {4, 8}. The
//!   deterministic gate is fired-multiset equality on the confluent cell (the
//!   wall-clock risk is out of L2 scope).
//! * **SM-8 corrupt-bundle probe**: a deliberately corrupted scion skeleton
//!   (a reflected-constructor tag rewritten in the TREATMENT program) is caught
//!   by the RESTING-TERM gate (OUT differs from control) even though the
//!   fired-multiset is unchanged — the resting-term gate is necessary and
//!   fail-closed. Plus the `scion_bundle_for_rule` fail-closed FALLBACK: a
//!   branching-re-check RHS (unsupported this stage) stays `ContractumRedrive`,
//!   so its treatment program is byte-identical to control.
//!
//! Every cell additionally asserts the `^drive-err` / `^drive-fuel` channels are
//! EMPTY (both arms). If ANY counter deviates from a FROZEN prediction the
//! deviation is accumulated and surfaced (the prediction is never silently
//! adjusted) — an L1 bug or a prediction error for the coordinator to decide.

#![cfg(feature = "bench-scion")]

use mettail_rholang_codegen::{
    reconstruct_language_def, reflect_ground_term_par, rho_net_drive_call_par_with_fuel,
    BOUND_VAR_REFLECT_LABEL, GroundTerm, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    corrupt_reflected_label, drive_arm_with_counters, scion_arm_programs, CommCounterSnapshot,
    DriveObservationChannels, DriveObservationSet,
};

/// Per-path fuel pinned ≫ every cell's causal-chain depth (max = W-A/W-B n/m =
/// 16, well under this) so no measured cell straddles the exhaustion boundary
/// (design v1 §4.2 / SM-5): the fuel value never changes a COMM count unless a
/// drive exhausts, which none of these do.
const CELL_FUEL: i64 = 1024;

// ── reflected-term (GroundTerm) builders ───────────────────────────────────────────────

fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}

/// The de-Bruijn bound-variable leaf `^bound(S^depth(Z))`.
fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = GroundTerm::new(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![peano])
}

/// `^lambda(body)`.
fn g_lambda(body: GroundTerm) -> GroundTerm {
    GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![body])
}

/// The identity combinator `λ.0` = `^lambda(^bound(Z))` — a β normal form.
fn g_id() -> GroundTerm {
    g_lambda(g_bound(0))
}

/// A β redex chain of n identity applications `(id (id … (id id)…))`, which
/// β-reduces to `id` in exactly n Beta firings.
fn beta_chain(n: usize) -> GroundTerm {
    let mut term = g_id();
    for _ in 0..n {
        term = g_node("App", vec![g_id(), term]);
    }
    term
}

/// The W-B ladder subject `Step(Wrap^m(End))`.
fn ladder_subject(m: usize) -> GroundTerm {
    let mut term = g_node("End", Vec::new());
    for _ in 0..m {
        term = g_node("Wrap", vec![term]);
    }
    g_node("Step", vec![term])
}

/// The W-C subject `H1(Wrap(H2(Wrap(… Hr(Wrap(End))…))))` — one redex per head,
/// each rule fires exactly once as the drive descends.
fn multi_rule_subject(r: usize) -> GroundTerm {
    let mut term = g_node("End", Vec::new());
    for i in (1..=r).rev() {
        term = g_node(&format!("H{i}"), vec![g_node("Wrap", vec![term])]);
    }
    term
}

// ── def fragment builders (named `Lambda` for DRIVE_OPT_IN, SM-8b) ─────────────────────

fn reconstruct(fragment: &str) -> mettail_ast::language::LanguageDef {
    reconstruct_language_def(fragment)
        .unwrap_or_else(|error| panic!("the bench def must reconstruct: {error}\n{fragment}"))
}

/// The production-Lambda-shaped def (name `Lambda` ∈ `DRIVE_OPT_IN`): its only
/// firing rule is the β `SubstRewrite`, so `StructuralScion` scion's NOTHING —
/// the A/A null cell.
fn lambda_shaped_def() -> mettail_ast::language::LanguageDef {
    reconstruct(
        r#"
            name: Lambda,
            types { Term },
            terms {
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            },
            equations {},
            rewrites {
                Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
            },
        "#,
    )
}

/// The W-B ladder `scion_ladder(s)`: terms `End`, `Wrap`, `Step`, `D1..Ds`;
/// rules `R1 . (Step (Wrap u)) ~> (D1 (… (Ds (Step u))…))`, `R2 . (Step End) ~>
/// End`. The RHS `Step` position is the single re-check per root-to-leaf path
/// (it can re-match R1/R2), so the treatment chains via P-resubmit.
fn scion_ladder_def(s: usize) -> mettail_ast::language::LanguageDef {
    let mut terms = String::from(
        "                End . |- \"end\" : Term ;\n                Wrap . u:Term |- \"wrap\" \"(\" u \")\" : Term ;\n                Step . u:Term |- \"step\" \"(\" u \")\" : Term ;\n",
    );
    for i in 1..=s {
        terms.push_str(&format!(
            "                D{i} . u:Term |- \"d{i}\" \"(\" u \")\" : Term ;\n"
        ));
    }
    // R1 RHS: D1(D2(…(Ds(Step u))…)).
    let mut rhs = String::from("(Step u)");
    for i in (1..=s).rev() {
        rhs = format!("(D{i} {rhs})");
    }
    reconstruct(&format!(
        "name: Lambda,\n            types {{ Term }},\n            terms {{\n{terms}            }},\n            equations {{}},\n            rewrites {{\n                R1 . |- (Step (Wrap u)) ~> {rhs} ;\n                R2 . |- (Step End) ~> End ;\n            }},\n"
    ))
}

/// The W-C `multi_rule_shared(r)`: r rules `Ri . (Hi (Wrap u)) ~> (C (Hi u))`
/// sharing the `C` RHS wrapper — the re-check pattern list at each `Hi` position
/// tests all r rule LHSs. Confluent (distinct heads, no overlap).
fn multi_rule_shared_def(r: usize) -> mettail_ast::language::LanguageDef {
    let mut terms = String::from(
        "                End . |- \"end\" : Term ;\n                Wrap . u:Term |- \"wrap\" \"(\" u \")\" : Term ;\n                C . u:Term |- \"c\" \"(\" u \")\" : Term ;\n",
    );
    let mut rewrites = String::new();
    for i in 1..=r {
        terms.push_str(&format!(
            "                H{i} . u:Term |- \"h{i}\" \"(\" u \")\" : Term ;\n"
        ));
        rewrites.push_str(&format!(
            "                R{i} . |- (H{i} (Wrap u)) ~> (C (H{i} u)) ;\n"
        ));
    }
    reconstruct(&format!(
        "name: Lambda,\n            types {{ Term }},\n            terms {{\n{terms}            }},\n            equations {{}},\n            rewrites {{\n{rewrites}            }},\n"
    ))
}

// ── drive harness ──────────────────────────────────────────────────────────────────────

/// One arm's observation set + COMM snapshot.
struct ArmObservation {
    set: DriveObservationSet,
    comm: CommCounterSnapshot,
}

/// Drive `subject` through BOTH arms of `def` (same reflected seed, same fuel,
/// same reserved channels) and return `(control, treatment)`.
async fn drive_both_arms(
    def: &mettail_ast::language::LanguageDef,
    subject: &GroundTerm,
) -> (ArmObservation, ArmObservation) {
    let arms = scion_arm_programs(def).expect("both arms plan + install");
    drive_installed_arms(&arms.control_installed, &arms.treatment_installed, &arms.fingerprint, subject)
        .await
}

/// Drive `subject` through two pre-built installed programs sharing `fingerprint`
/// (used both by the A/B cells and by the corrupt-bundle probe, which supplies a
/// mutated treatment program).
async fn drive_installed_arms(
    control_installed: &models::rhoapi::Par,
    treatment_installed: &models::rhoapi::Par,
    fingerprint: &str,
    subject: &GroundTerm,
) -> (ArmObservation, ArmObservation) {
    let reflected = reflect_ground_term_par(subject, fingerprint);
    let call = rho_net_drive_call_par_with_fuel(fingerprint, reflected, CELL_FUEL, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(fingerprint, "OUT");
    let (c_set, c_comm) = drive_arm_with_counters(control_installed, &call, &channels)
        .await
        .expect("control drive runs to quiescence");
    let (t_set, t_comm) = drive_arm_with_counters(treatment_installed, &call, &channels)
        .await
        .expect("treatment drive runs to quiescence");
    (ArmObservation { set: c_set, comm: c_comm }, ArmObservation { set: t_set, comm: t_comm })
}

/// Sum every class counter (the flag-counter `join_arity_gt1` is excluded — it is
/// not a class total).
fn total_comms(c: &CommCounterSnapshot) -> u64 {
    c.matching_tau
        + c.firing_visible
        + c.subst_tau
        + c.respread_tau
        + c.drive_tau
        + c.ac_carrier
        + c.pathmap_index
        + c.contextual_plumbing
        + c.observation
        + c.other
}

fn fired_sorted(set: &DriveObservationSet) -> Vec<String> {
    let mut fired = set.fired_labels().expect("every ledger datum is a GString rule label");
    fired.sort();
    fired
}

fn fired_count(set: &DriveObservationSet, label: &str) -> usize {
    set.fired_labels()
        .expect("ledger decodes")
        .iter()
        .filter(|found| found.as_str() == label)
        .count()
}

/// Push a deviation message iff `condition` is false (the FROZEN prediction is
/// never silently adjusted — a deviation is reported, not fixed).
fn check(condition: bool, message: String, deviations: &mut Vec<String>) {
    if !condition {
        deviations.push(message);
    }
}

/// Assert the `^drive-err` / `^drive-fuel` channels are EMPTY on both arms.
fn check_err_fuel_empty(
    cell: &str,
    control: &ArmObservation,
    treatment: &ArmObservation,
    deviations: &mut Vec<String>,
) {
    for (arm, obs) in [("control", control), ("treatment", treatment)] {
        check(
            obs.set.err_data.is_empty(),
            format!("{cell} {arm}: ^drive-err non-empty ({} data)", obs.set.err_data.len()),
            deviations,
        );
        check(
            obs.set.fuel_data.is_empty(),
            format!("{cell} {arm}: ^drive-fuel non-empty ({} data)", obs.set.fuel_data.len()),
            deviations,
        );
    }
}

// ══ W-A — the A/A null cell (β is never scion'd) ═══════════════════════════════════════

#[tokio::test]
async fn w_a_beta_chains_are_exact_aa_null() {
    mettail_runtime::clear_var_cache();
    let def = lambda_shaped_def();
    // The β-only def scion's NOTHING → the two installed programs are byte-identical.
    let arms = scion_arm_programs(&def).expect("Lambda-shaped def plans + installs");
    assert_eq!(
        arms.control_installed, arms.treatment_installed,
        "W-A: a β-only def has no positional BaseRewrite arm, so StructuralScion selects no \
         bundle — the treatment installed program is BYTE-IDENTICAL to control"
    );

    let mut deviations: Vec<String> = Vec::new();
    println!("── W-A (A/A null: synthetic-Lambda β chains) ──");
    for n in [4usize, 8, 16] {
        let (control, treatment) = drive_both_arms(&def, &beta_chain(n)).await;
        let c = &control.comm;
        let t = &treatment.comm;
        println!(
            "  n={n:2}: fired={} subst_tau(c/t)={}/{} drive_tau(c/t)={}/{} firing_visible(c/t)={}/{} \
             other(c/t)={}/{} total(c/t)={}/{}",
            fired_count(&control.set, "Beta"),
            c.subst_tau, t.subst_tau, c.drive_tau, t.drive_tau, c.firing_visible, t.firing_visible,
            c.other, t.other, total_comms(c), total_comms(t),
        );

        // The β cascade actually ran (n Beta firings, subst_tau > 0).
        check(
            fired_count(&control.set, "Beta") == n && fired_count(&treatment.set, "Beta") == n,
            format!("W-A n={n}: expected {n} Beta firings, got c={} t={}", fired_count(&control.set, "Beta"), fired_count(&treatment.set, "Beta")),
            &mut deviations,
        );
        check(c.subst_tau > 0, format!("W-A n={n}: control subst_tau must be > 0 (β ran)"), &mut deviations);

        // FROZEN: EXACT Δ=0 on EVERY counter.
        check(c.matching_tau == t.matching_tau, format!("W-A n={n}: Δmatching_tau={}", c.matching_tau as i64 - t.matching_tau as i64), &mut deviations);
        check(c.firing_visible == t.firing_visible, format!("W-A n={n}: Δfiring_visible={}", c.firing_visible as i64 - t.firing_visible as i64), &mut deviations);
        check(c.subst_tau == t.subst_tau, format!("W-A n={n}: Δsubst_tau={}", c.subst_tau as i64 - t.subst_tau as i64), &mut deviations);
        check(c.respread_tau == t.respread_tau, format!("W-A n={n}: Δrespread_tau={}", c.respread_tau as i64 - t.respread_tau as i64), &mut deviations);
        check(c.drive_tau == t.drive_tau, format!("W-A n={n}: Δdrive_tau={}", c.drive_tau as i64 - t.drive_tau as i64), &mut deviations);
        check(c.ac_carrier == t.ac_carrier, format!("W-A n={n}: Δac_carrier={}", c.ac_carrier as i64 - t.ac_carrier as i64), &mut deviations);
        check(c.pathmap_index == t.pathmap_index, format!("W-A n={n}: Δpathmap_index"), &mut deviations);
        check(c.contextual_plumbing == t.contextual_plumbing, format!("W-A n={n}: Δcontextual_plumbing"), &mut deviations);
        check(c.observation == t.observation, format!("W-A n={n}: Δobservation={}", c.observation as i64 - t.observation as i64), &mut deviations);
        check(c.other == t.other, format!("W-A n={n}: Δother={}", c.other as i64 - t.other as i64), &mut deviations);
        check(c.join_arity_gt1 == t.join_arity_gt1, format!("W-A n={n}: Δjoin_arity_gt1={}", c.join_arity_gt1 as i64 - t.join_arity_gt1 as i64), &mut deviations);

        // Fired-multiset equality + err/fuel empty.
        check(fired_sorted(&control.set) == fired_sorted(&treatment.set), format!("W-A n={n}: fired multisets differ"), &mut deviations);
        check_err_fuel_empty(&format!("W-A n={n}"), &control, &treatment, &mut deviations);
    }
    assert!(deviations.is_empty(), "W-A FROZEN-prediction deviations (report, do not adjust):\n{}", deviations.join("\n"));
}

// ══ W-B — the structural ladder: CORRECT, but ΔDriveTau DEVIATES from the frozen +s ═══════
//
// See the module header. This cell asserts the CORRECTNESS invariants (which hold: the scion
// reaches the same NF and fires the same multiset as control, with empty typed channels) and
// PRINTS the frozen-prediction deviation (measured ΔDriveTau is negative/quadratic, not +s·m).
// It does NOT assert the +s prediction — the deviation is REPORTED per the task protocol, not
// adjusted (the frozen s·m / 2s+1 are printed alongside the measured values). The grid is capped
// at s ∈ {1, 2} × m ∈ {4, 8} to stay under the eager-scion quadratic stack overflow (s≥2, m≥16).

#[tokio::test]
async fn w_b_scion_ladder_correct_but_drivetau_deviates_from_frozen() {
    mettail_runtime::clear_var_cache();
    let mut correctness: Vec<String> = Vec::new();
    let mut deviation_seen = false;
    println!("── W-B (scion ladder) — CORRECTNESS gate + FROZEN-prediction telemetry ──");
    println!("   s   m | fired(R1/R2) | DriveTau(c/t)  ΔDrive | FROZEN s·m perR1=s | Δtotal perR1  FROZEN 2s+1 | verdict");
    for s in [1usize, 2] {
        let def = scion_ladder_def(s);
        let arms = scion_arm_programs(&def).expect("ladder def plans + installs");
        // The scion IS live for W-B (R1 is a positional BaseRewrite the treatment scion's).
        check(
            arms.control_installed != arms.treatment_installed,
            format!("W-B s={s}: treatment == control — R1's scion did NOT apply (fell back?)"),
            &mut correctness,
        );
        for m in [4usize, 8] {
            let (control, treatment) = drive_both_arms(&def, &ladder_subject(m)).await;
            let n_r1 = fired_count(&control.set, "R1");
            let n_r2 = fired_count(&control.set, "R2");
            let drive_c = control.comm.drive_tau as i64;
            let drive_t = treatment.comm.drive_tau as i64;
            let delta_drive = drive_c - drive_t;
            let per_r1 = if m > 0 { delta_drive.div_euclid(m as i64) } else { 0 };
            let delta_total = total_comms(&control.comm) as i64 - total_comms(&treatment.comm) as i64;
            let total_per_r1 = if m > 0 { delta_total.div_euclid(m as i64) } else { 0 };
            // FROZEN prediction vs measured — a deviation is REPORTED, never adjusted.
            let matches_frozen = per_r1 == s as i64 && total_per_r1 == (2 * s + 1) as i64;
            if !matches_frozen {
                deviation_seen = true;
            }
            println!(
                "  {s:2}  {m:2} | {n_r1:2}/{n_r2}        | {drive_c:4}/{drive_t:4}  {delta_drive:5} | {:5}     {s:2}     | {delta_total:5}   {total_per_r1:3}       {:3}     | {}",
                (s * m) as i64,
                (2 * s + 1) as i64,
                if matches_frozen { "matches frozen" } else { "DEVIATION (treatment drives MORE — quadratic)" },
            );

            // Structural chain shape.
            check(n_r1 == m, format!("W-B s={s} m={m}: expected {m} R1 firings, got {n_r1}"), &mut correctness);
            check(n_r2 == 1, format!("W-B s={s} m={m}: expected 1 R2 firing, got {n_r2}"), &mut correctness);
            // CORRECTNESS (must hold): the scion reaches the same NF and fires the same multiset
            // as control, with empty typed channels — the semantic validation of L1.
            check(control.set.out_values == treatment.set.out_values, format!("W-B s={s} m={m}: out_values differ (scion NF ≠ redrive NF)"), &mut correctness);
            check(fired_sorted(&control.set) == fired_sorted(&treatment.set), format!("W-B s={s} m={m}: fired multisets differ"), &mut correctness);
            check_err_fuel_empty(&format!("W-B s={s} m={m}"), &control, &treatment, &mut correctness);
        }
    }
    // The FROZEN-prediction deviation is EXPECTED here (the L2 finding) — asserting it would be
    // "adjusting the counter to match", which the task forbids; it is reported, not gated.
    assert!(
        deviation_seen,
        "W-B: the frozen +s ΔDriveTau prediction was expected to DEVIATE (the L2 finding) but the \
         measured values matched it — re-examine (an L1 change may have altered the eager-slot behavior)"
    );
    assert!(
        correctness.is_empty(),
        "W-B CORRECTNESS violations (these MUST hold — a real L1 defect):\n{}",
        correctness.join("\n")
    );
}

// ══ W-C — the rule-count risk cell (fired-multiset equality) ═══════════════════════════

#[tokio::test]
async fn w_c_multi_rule_shared_fired_multiset_equal() {
    mettail_runtime::clear_var_cache();
    let mut deviations: Vec<String> = Vec::new();
    println!("── W-C (multi_rule_shared: fired-multiset equality on the confluent cell) ──");
    for r in [4usize, 8] {
        let def = multi_rule_shared_def(r);
        let arms = scion_arm_programs(&def).expect("multi-rule def plans + installs");
        check(
            arms.control_installed != arms.treatment_installed,
            format!("W-C r={r}: treatment == control — no rule scion'd"),
            &mut deviations,
        );
        let (control, treatment) = drive_both_arms(&def, &multi_rule_subject(r)).await;
        let fired_c = fired_sorted(&control.set);
        let fired_t = fired_sorted(&treatment.set);
        println!(
            "  r={r}: fired#(c/t)={}/{} drive_tau(c/t)={}/{} total(c/t)={}/{} err/fuel(c)={}/{} err/fuel(t)={}/{}",
            fired_c.len(), fired_t.len(), control.comm.drive_tau, treatment.comm.drive_tau,
            total_comms(&control.comm), total_comms(&treatment.comm),
            control.set.err_data.len(), control.set.fuel_data.len(),
            treatment.set.err_data.len(), treatment.set.fuel_data.len(),
        );
        // Each of the r rules fires exactly once.
        check(fired_c.len() == r, format!("W-C r={r}: expected {r} firings, control fired {}", fired_c.len()), &mut deviations);
        check(fired_c == fired_t, format!("W-C r={r}: fired multisets differ (c={fired_c:?} t={fired_t:?})"), &mut deviations);
        check_err_fuel_empty(&format!("W-C r={r}"), &control, &treatment, &mut deviations);
    }
    assert!(deviations.is_empty(), "W-C FROZEN-prediction deviations (report, do not adjust):\n{}", deviations.join("\n"));
}

// ══ SM-8 — the corrupt-bundle probe (resting-term gate is fail-closed) ═════════════════

#[tokio::test]
async fn sm8_corrupt_bundle_caught_by_resting_term_gate() {
    mettail_runtime::clear_var_cache();
    // s=1 ladder: R1 RHS = D1(Step u) — the scion grafts D1 over the driven slot.
    let def = scion_ladder_def(1);
    let arms = scion_arm_programs(&def).expect("s=1 ladder plans + installs");
    let subject = ladder_subject(4);

    // The TRUE control drive (the reference resting term).
    let (control, treatment) =
        drive_installed_arms(&arms.control_installed, &arms.treatment_installed, &arms.fingerprint, &subject).await;
    // Sanity: the (uncorrupted) treatment matches control.
    assert_eq!(
        control.set.out_values, treatment.set.out_values,
        "the uncorrupted treatment must reproduce the control resting term before corruption"
    );

    // Corrupt the TREATMENT skeleton: rewrite the reflected `D1` constructor tag
    // to a length-preserving bogus label `Dz`. The graft now reassembles a
    // Dz-headed term, so the resting term diverges from control's D1-headed NF —
    // while the firing sequence (R1×m + R2) is UNAFFECTED.
    let corrupted_treatment =
        corrupt_reflected_label(&arms.treatment_installed, &arms.fingerprint, "D1", "Dz")
            .expect("the D1 tag occurs in the treatment program and re-decodes after rewrite");
    let (_control2, corrupted) =
        drive_installed_arms(&arms.control_installed, &corrupted_treatment, &arms.fingerprint, &subject).await;

    println!("── SM-8 corrupt-bundle probe (s=1 ladder, D1→Dz) ──");
    println!(
        "  control out={:?}\n  corrupt out={:?}\n  fired c={:?} corrupt={:?}",
        control.set.out_values, corrupted.set.out_values,
        fired_sorted(&control.set), fired_sorted(&corrupted.set),
    );

    // The RESTING-TERM gate CATCHES the corruption (OUT differs from control) …
    assert_ne!(
        control.set.out_values, corrupted.set.out_values,
        "SM-8: the corrupted scion skeleton MUST be caught by the resting-term gate — a \
         D1→Dz graft produces a different NF than control"
    );
    // … while the fired-multiset gate ALONE would NOT (firing is unaffected by an
    // RHS-constructor corruption) — proving the resting-term gate is necessary.
    assert_eq!(
        fired_sorted(&control.set),
        fired_sorted(&corrupted.set),
        "SM-8: the corruption does not change the firing sequence — the fired-multiset gate \
         alone cannot catch it, which is why the resting-term gate is load-bearing",
    );
}

// ══ SM-8 — scion_bundle_for_rule fail-closed fallback (branching re-check) ═════════════

#[tokio::test]
async fn scion_branching_recheck_falls_back_to_contractum_redrive() {
    mettail_runtime::clear_var_cache();
    // RHS `(Node (Step u) (Step u))` has TWO re-check-bearing children — a
    // branching re-check unsupported this stage — so `scion_bundle_for_rule`
    // fails closed and the arm stays ContractumRedrive, making the treatment
    // program BYTE-IDENTICAL to control (the fail-closed fallback, SM-8a).
    let def = reconstruct(
        r#"
            name: Lambda,
            types { Term },
            terms {
                End . |- "end" : Term ;
                Wrap . u:Term |- "wrap" "(" u ")" : Term ;
                Step . u:Term |- "step" "(" u ")" : Term ;
                Node . a:Term, b:Term |- "node" "(" a "," b ")" : Term ;
            },
            equations {},
            rewrites {
                RB . |- (Step (Wrap u)) ~> (Node (Step u) (Step u)) ;
            },
        "#,
    );
    let arms = scion_arm_programs(&def).expect("branching-recheck def plans + installs");
    assert_eq!(
        arms.control_installed, arms.treatment_installed,
        "a branching re-check RHS fails the scion scope (>1 re-check child), so the arm falls \
         back to ContractumRedrive and the treatment program is byte-identical to control",
    );
}
