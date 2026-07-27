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
//!   `Δ(DriveTau) = control − treatment = s` EXACTLY (run total s·m ± m, SM-1).
//!
//!   ✔ **L2 RE-VALIDATION (design v2 — the DEMAND-DRIVEN slot-scion, committed L1
//!   `08aab5b7`) RECOVERS the frozen prediction.** v1 drove the σ-slot
//!   `u = Wrap^(m-1)(End)` to NF on every R1 firing — a full re-descent of the
//!   remaining (redex-free) `Wrap` chain, summing to ½m² over the m firings
//!   (treatment ≈ ½m²+1½m+2, QUADRATIC; and a SIGABRT at s≥2,m≥16). v2 drives the
//!   RECHECK NODE `Step(σ_u)` (resubmitted RAW) rather than the slot, so the
//!   generic `^drive` — OUTERMOST-FIRST (`drive_program_par` step 1: a redex at
//!   this node fires before any descent) — peels one `Wrap` per firing via the
//!   R1/R2 match and NEVER re-descends the un-fired slot subtree, exactly as
//!   CONTROL does. Treatment DriveTau is now LINEAR (≈ m, control-mode) and
//!   `Δ(DriveTau)/R1-firing = s` (±1): control descends the s grafted `D1..Ds`
//!   wrappers per firing that the scion grafts inert. This cell UNCAPS the grid to
//!   s ∈ {1, 2, 4, 8} × m ∈ {4, 8, 16} and INVERTS the v1 deviation gate — it now
//!   asserts NO deviation (`per_r1 = s ±1` on every cell), plus the CORRECTNESS
//!   invariants (same NF, same fired multiset, empty err/fuel). A deviation here
//!   would be a real L1 regression (reported, never adjusted). ⚠ The drives run on
//!   a 512MB-stack thread (`drive_both_arms_big_stack`): with the 8MB default BOTH
//!   arms SIGABRT past NF-depth ≈ 17 — a SHARED f1r3node reducer recursion artifact
//!   on result-term depth (`s·m + 1`, up to 129), NOT the scion (proven: treatment
//!   DriveTau = 18 whether the NF is depth 17 or 33). The v1 "eager quadratic
//!   overflow" was partly this depth limit; v2 removes the quadratic, the depth
//!   artifact needs the bigger stack.
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
    CollectionType, GroundTerm, BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    corrupt_reflected_label, drive_arm_with_counters, scion_arm_programs, CommCounterSnapshot,
    DriveObservationChannels, DriveObservationSet,
};
// W-D (Ambient payoff) reuses the PRODUCTION Ambient language + the decoded-observation
// vocabulary (`bench-scion` now enables `ambient-runtime`, Cargo.toml).
use mettail_languages::ambient::AmbientLanguage;
use mettail_runtime::{Language, RuntimeObservationValue};

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
        rewrites
            .push_str(&format!("                R{i} . |- (H{i} (Wrap u)) ~> (C (H{i} u)) ;\n"));
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
    drive_installed_arms(
        &arms.control_installed,
        &arms.treatment_installed,
        &arms.fingerprint,
        subject,
    )
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
    (
        ArmObservation { set: c_set, comm: c_comm },
        ArmObservation { set: t_set, comm: t_comm },
    )
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
    let mut fired = set
        .fired_labels()
        .expect("every ledger datum is a GString rule label");
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
            format!(
                "W-A n={n}: expected {n} Beta firings, got c={} t={}",
                fired_count(&control.set, "Beta"),
                fired_count(&treatment.set, "Beta")
            ),
            &mut deviations,
        );
        check(
            c.subst_tau > 0,
            format!("W-A n={n}: control subst_tau must be > 0 (β ran)"),
            &mut deviations,
        );

        // FROZEN: EXACT Δ=0 on EVERY counter.
        check(
            c.matching_tau == t.matching_tau,
            format!("W-A n={n}: Δmatching_tau={}", c.matching_tau as i64 - t.matching_tau as i64),
            &mut deviations,
        );
        check(
            c.firing_visible == t.firing_visible,
            format!(
                "W-A n={n}: Δfiring_visible={}",
                c.firing_visible as i64 - t.firing_visible as i64
            ),
            &mut deviations,
        );
        check(
            c.subst_tau == t.subst_tau,
            format!("W-A n={n}: Δsubst_tau={}", c.subst_tau as i64 - t.subst_tau as i64),
            &mut deviations,
        );
        check(
            c.respread_tau == t.respread_tau,
            format!("W-A n={n}: Δrespread_tau={}", c.respread_tau as i64 - t.respread_tau as i64),
            &mut deviations,
        );
        check(
            c.drive_tau == t.drive_tau,
            format!("W-A n={n}: Δdrive_tau={}", c.drive_tau as i64 - t.drive_tau as i64),
            &mut deviations,
        );
        check(
            c.ac_carrier == t.ac_carrier,
            format!("W-A n={n}: Δac_carrier={}", c.ac_carrier as i64 - t.ac_carrier as i64),
            &mut deviations,
        );
        check(
            c.pathmap_index == t.pathmap_index,
            format!("W-A n={n}: Δpathmap_index"),
            &mut deviations,
        );
        check(
            c.contextual_plumbing == t.contextual_plumbing,
            format!("W-A n={n}: Δcontextual_plumbing"),
            &mut deviations,
        );
        check(
            c.observation == t.observation,
            format!("W-A n={n}: Δobservation={}", c.observation as i64 - t.observation as i64),
            &mut deviations,
        );
        check(
            c.other == t.other,
            format!("W-A n={n}: Δother={}", c.other as i64 - t.other as i64),
            &mut deviations,
        );
        check(
            c.join_arity_gt1 == t.join_arity_gt1,
            format!(
                "W-A n={n}: Δjoin_arity_gt1={}",
                c.join_arity_gt1 as i64 - t.join_arity_gt1 as i64
            ),
            &mut deviations,
        );

        // Fired-multiset equality + err/fuel empty.
        check(
            fired_sorted(&control.set) == fired_sorted(&treatment.set),
            format!("W-A n={n}: fired multisets differ"),
            &mut deviations,
        );
        check_err_fuel_empty(&format!("W-A n={n}"), &control, &treatment, &mut deviations);
    }
    assert!(
        deviations.is_empty(),
        "W-A FROZEN-prediction deviations (report, do not adjust):\n{}",
        deviations.join("\n")
    );
}

// ══ W-B — the structural ladder: demand-driven scion RECOVERS ΔDriveTau/firing = s (LINEAR) ══
//
// See the module header. The v2 demand-driven scion drives the RECHECK NODE `Step(σ_u)` (raw)
// rather than the σ-slot `u`, so the generic `^drive` fires the head R1/R2 redex before descending
// the un-fired `Wrap` spine — the v1 eager-slot ½m² COMM re-descent is GONE and the FROZEN
// `Δ(DriveTau)/firing = s` prediction is RECOVERED. This cell UNCAPS the grid to s ∈ {1,2,4,8} ×
// m ∈ {4,8,16} and INVERTS the v1 gate: it asserts NO deviation (`per_r1 = s ±1` on every cell —
// which also witnesses treatment DriveTau LINEAR: the treatment does an s-INDEPENDENT ≈ m+2 DriveTau
// while control does (s+1)m+2, so a ½m² treatment would drive `per_r1` hugely negative). CORRECTNESS
// (same NF, same fired multiset, empty typed channels) must hold. A deviation is REPORTED (the
// assertion below), never adjusted — the design is red-team-converged.
//
// ⚠ L2 FINDING (the design's "no SIGABRT at s≥2,m≥16" needed a stack caveat): with the 8MB default
// BOTH arms SIGABRT past NF-depth ≈ 17 — a SHARED f1r3node reducer stack-recursion artifact on
// RESULT-TERM DEPTH (`s·m + 1`, up to 129 here), NOT the scion (PROVEN: treatment DriveTau = 18 at
// both s=1,m=16 [depth 17, passes on 8MB] and s=2,m=16 [depth 33, SIGABRTs on 8MB] — identical COMM
// work, the overflow tracks DEPTH). The v1 SIGABRT conflated this with the quadratic; v2 removes the
// quadratic but the depth artifact remains. `drive_both_arms_big_stack` gives the drive a 512MB
// stack so the full uncapped grid runs and the recovery is validated on every cell.

#[tokio::test]
async fn w_b_scion_ladder_drivetau_linear_delta_s() {
    mettail_runtime::clear_var_cache();
    let mut correctness: Vec<String> = Vec::new();
    let mut deviation_seen = false;
    println!("── W-B (scion ladder) — demand-driven ΔDriveTau/firing = s (LINEAR) gate ──");
    println!("   s   m | fired(R1/R2) | DriveTau(c/t)  ΔDrive | per-R1 (frozen=s) | Δtotal perR1 | verdict");
    for s in [1usize, 2, 4, 8] {
        let def = scion_ladder_def(s);
        let arms = scion_arm_programs(&def).expect("ladder def plans + installs");
        // The scion IS live for W-B (R1 is a positional BaseRewrite the treatment scion's).
        check(
            arms.control_installed != arms.treatment_installed,
            format!("W-B s={s}: treatment == control — R1's scion did NOT apply (fell back?)"),
            &mut correctness,
        );
        for m in [4usize, 8, 16] {
            // Drive on a LARGE-STACK thread: the ladder NF reaches depth `s·m + 1` (up to 129),
            // past the 8MB default the f1r3node reducer recurses within — a SHARED reducer-depth
            // artifact (both arms, orthogonal to the scion), see `drive_both_arms_big_stack`.
            let (control, treatment) = drive_both_arms_big_stack(&def, &ladder_subject(m));
            let n_r1 = fired_count(&control.set, "R1");
            let n_r2 = fired_count(&control.set, "R2");
            let drive_c = control.comm.drive_tau as i64;
            let drive_t = treatment.comm.drive_tau as i64;
            let delta_drive = drive_c - drive_t;
            let per_r1 = if m > 0 {
                delta_drive.div_euclid(m as i64)
            } else {
                0
            };
            let delta_total =
                total_comms(&control.comm) as i64 - total_comms(&treatment.comm) as i64;
            let total_per_r1 = if m > 0 {
                delta_total.div_euclid(m as i64)
            } else {
                0
            };
            // FROZEN prediction (design v2 §5): `Δ(DriveTau)/firing = s` within ±1 — the demand-
            // driven recovery. `per_r1 = s ±1` at m=16 also certifies treatment DriveTau LINEAR
            // (a ½m² treatment would make `per_r1` hugely negative). A deviation is REPORTED below.
            let drivetau_matches = (per_r1 - s as i64).abs() <= 1;
            if !drivetau_matches {
                deviation_seen = true;
            }
            println!(
                "  {s:2}  {m:2} | {n_r1:2}/{n_r2}        | {drive_c:4}/{drive_t:4}  {delta_drive:5} | {per_r1:3} (frozen {s:2}) | {delta_total:5} {total_per_r1:3} | {}",
                if drivetau_matches { "= s ±1 (linear)" } else { "DEVIATION (re-examine L1)" },
            );

            // Structural chain shape.
            check(
                n_r1 == m,
                format!("W-B s={s} m={m}: expected {m} R1 firings, got {n_r1}"),
                &mut correctness,
            );
            check(
                n_r2 == 1,
                format!("W-B s={s} m={m}: expected 1 R2 firing, got {n_r2}"),
                &mut correctness,
            );
            // CORRECTNESS (must hold): the scion reaches the same NF and fires the same multiset
            // as control, with empty typed channels — the semantic validation of L1.
            check(
                control.set.out_values == treatment.set.out_values,
                format!("W-B s={s} m={m}: out_values differ (scion NF ≠ redrive NF)"),
                &mut correctness,
            );
            check(
                fired_sorted(&control.set) == fired_sorted(&treatment.set),
                format!("W-B s={s} m={m}: fired multisets differ"),
                &mut correctness,
            );
            check_err_fuel_empty(
                &format!("W-B s={s} m={m}"),
                &control,
                &treatment,
                &mut correctness,
            );
        }
    }
    // CORRECTNESS first (the most serious gate — a real L1 defect).
    assert!(
        correctness.is_empty(),
        "W-B CORRECTNESS violations (these MUST hold — a real L1 defect):\n{}",
        correctness.join("\n")
    );
    // v2 INVERTS the v1 finding: the demand-driven scion RECOVERS the frozen +s ΔDriveTau
    // prediction, so NO deviation is expected. A deviation is a real regression (the design is
    // red-team-converged) — reported, NOT adjusted to match.
    assert!(
        !deviation_seen,
        "W-B: the demand-driven scion was expected to RECOVER Δ(DriveTau)/firing = s (±1) on EVERY \
         cell, but at least one cell DEVIATED — an L1 regression or a design error to investigate \
         (do NOT adjust the gate to match; report the per-cell table above)"
    );
}

// ══ W-C — the rule-count risk cell (fired-multiset equality) ═══════════════════════════

#[tokio::test]
async fn w_c_multi_rule_shared_win_preserved() {
    mettail_runtime::clear_var_cache();
    let mut deviations: Vec<String> = Vec::new();
    println!("── W-C (multi_rule_shared: ΔDriveTau win preserved + fired-multiset equality) ──");
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
        let delta_drive = control.comm.drive_tau as i64 - treatment.comm.drive_tau as i64;
        println!(
            "  r={r}: fired#(c/t)={}/{} drive_tau(c/t)={}/{} ΔDrive={delta_drive} (v2 win = r = {r}; v1-eager was 2r = {}) total(c/t)={}/{} err/fuel(c)={}/{} err/fuel(t)={}/{}",
            fired_c.len(), fired_t.len(), control.comm.drive_tau, treatment.comm.drive_tau,
            2 * r,
            total_comms(&control.comm), total_comms(&treatment.comm),
            control.set.err_data.len(), control.set.fuel_data.len(),
            treatment.set.err_data.len(), treatment.set.fuel_data.len(),
        );
        // Each of the r rules fires exactly once.
        check(
            fired_c.len() == r,
            format!("W-C r={r}: expected {r} firings, control fired {}", fired_c.len()),
            &mut deviations,
        );
        check(
            fired_c == fired_t,
            format!("W-C r={r}: fired multisets differ (c={fired_c:?} t={fired_t:?})"),
            &mut deviations,
        );
        // The scion WIN is PRESERVED (design v2 §5 — "W-C win preserved"; Δ≥0 unconditional). The v2
        // mechanism grafts the shared `C` wrapper inert, saving the 1 `C`-descent DriveTau control
        // pays PER firing → ΔDriveTau = r (the r firings). ⚠ L2 FINDING: this is HALF the task's
        // stated v1-eager win of +2r (+8/+16). The eager path additionally short-circuited the `Hi`
        // descent; v2's recheck-resubmit re-descends `Hi` (its child `H_{i+1}` is not a redex head)
        // — exactly design red-team target 4 ("leaves inner-Skip savings on table but NEVER
        // negative; Δ≥0 not Δ>0-guaranteed"), the v2-for-W-B-linear trade. Gate on the mechanism-
        // predicted r (a positive win); a shortfall is a real regression, reported (not adjusted).
        check(
            delta_drive >= r as i64,
            format!("W-C r={r}: ΔDriveTau win NOT preserved — expected ≥ r={r} (v2 shared-C graft), got {delta_drive}"),
            &mut deviations,
        );
        // Confluent cell: same NF on both arms (strengthens the fired-multiset gate).
        check(
            control.set.out_values == treatment.set.out_values,
            format!("W-C r={r}: out_values differ (scion NF ≠ redrive NF)"),
            &mut deviations,
        );
        check_err_fuel_empty(&format!("W-C r={r}"), &control, &treatment, &mut deviations);
    }
    assert!(
        deviations.is_empty(),
        "W-C deviations (report, do not adjust):\n{}",
        deviations.join("\n")
    );
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
    let (control, treatment) = drive_installed_arms(
        &arms.control_installed,
        &arms.treatment_installed,
        &arms.fingerprint,
        &subject,
    )
    .await;
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
    let (_control2, corrupted) = drive_installed_arms(
        &arms.control_installed,
        &corrupted_treatment,
        &arms.fingerprint,
        &subject,
    )
    .await;

    println!("── SM-8 corrupt-bundle probe (s=1 ladder, D1→Dz) ──");
    println!(
        "  control out={:?}\n  corrupt out={:?}\n  fired c={:?} corrupt={:?}",
        control.set.out_values,
        corrupted.set.out_values,
        fired_sorted(&control.set),
        fired_sorted(&corrupted.set),
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

// ══ Fold 1 (R-3) — the inert-graft ROOTEDNESS guard prevents under-reduction ═══════════════
//
// The R-3 counter-example shape: rule `RTrig . (Trig u) ~> (Bar (Baz u))` whose RHS Skip
// constructor `Bar` IS a rule redex root (rule `RBar . (Bar (Foo x)) ~> (Done x)`) ABOVE a recheck
// (`Baz u`, which rule `RBaz . (Baz w) ~> (Foo w)` reduces). `scion_could_unify(Bar(Foo x),
// Bar(Baz u))` is FALSE (`Foo ≠ Baz`), so the static-shape mark would GRAFT `Bar` inert — but
// once `Baz u` reduces to `Foo (NF u)`, `Bar(Foo (NF u))` BECOMES an RBar redex control fires.
// Grafting `Bar` inert would return it UN-fired (`Bar(Foo (NF u))` ≠ `Done (NF u)`) — the
// divergence FOLD 1 closes by failing the RTrig arm CLOSED to `ContractumRedrive`; the drive then
// re-fires the whole contractum, reaching control's NF (`Done (NF u)`). The guard is validated by
// the semantic gate below (same NF + same fired multiset as control) — the Fold-1 correctness cell.
// (RBaz/RBar are safely scion'd — `Foo`/`Done` are never a rule root — so the scion IS live,
// isolating the guard's effect.)

#[tokio::test]
async fn fold1_inert_graft_rootedness_prevents_under_reduction() {
    mettail_runtime::clear_var_cache();
    let def = reconstruct(
        r#"
            name: Lambda,
            types { Term },
            terms {
                End . |- "end" : Term ;
                Trig . u:Term |- "trig" "(" u ")" : Term ;
                Baz . w:Term |- "baz" "(" w ")" : Term ;
                Foo . w:Term |- "foo" "(" w ")" : Term ;
                Bar . x:Term |- "bar" "(" x ")" : Term ;
                Done . t:Term |- "done" "(" t ")" : Term ;
            },
            equations {},
            rewrites {
                RTrig . |- (Trig u) ~> (Bar (Baz u)) ;
                RBaz . |- (Baz w) ~> (Foo w) ;
                RBar . |- (Bar (Foo x)) ~> (Done x) ;
            },
        "#,
    );
    let arms = scion_arm_programs(&def).expect("Fold-1 def plans + installs");
    // The scion IS live (RBaz/RBar are safely scion'd positional arms), so the two programs differ
    // — the DANGEROUS RTrig graft `(Bar (Baz u))` fell back to ContractumRedrive via Fold 1, not a
    // silent inert graft (otherwise this cell would exercise nothing).
    assert_ne!(
        arms.control_installed, arms.treatment_installed,
        "Fold-1: the scion must be live (RBaz/RBar scion'd) for this cell to isolate the guard"
    );

    let subject = g_node("Trig", vec![g_node("End", Vec::new())]);
    let (control, treatment) = drive_both_arms(&def, &subject).await;
    println!("── Fold 1 (inert-graft rootedness) — RTrig RHS (Bar (Baz u)), Bar is an RBar redex root ──");
    println!(
        "  control out={:?} fired={:?}\n  treat   out={:?} fired={:?}",
        control.set.out_values,
        fired_sorted(&control.set),
        treatment.set.out_values,
        fired_sorted(&treatment.set),
    );

    // Control must actually reach `Done(End)` (fire RBar) — otherwise the cell witnesses nothing.
    assert_eq!(
        fired_count(&control.set, "RBar"), 1,
        "Fold-1: control must fire RBar (reach the fully-reduced NF Done(End)) for the cell to be meaningful"
    );
    // The guard PREVENTS the under-reduction: treatment reaches control's NF (`Done(End)`) and fires
    // the same multiset {RTrig, RBaz, RBar}. Without Fold 1 the eager graft would return
    // `Bar(Foo(End))` un-fired (≠ Done(End)) — exactly the divergence the guard closes.
    assert_eq!(
        control.set.out_values, treatment.set.out_values,
        "Fold-1: the rootedness guard must prevent under-reduction — treatment NF must equal control NF Done(End)"
    );
    assert_eq!(
        fired_sorted(&control.set),
        fired_sorted(&treatment.set),
        "Fold-1: same fired multiset as control (RTrig re-drives; RBaz/RBar fire on the re-check)"
    );
    // Both typed channels empty (no err, no fuel exhaustion) on both arms.
    let mut dev: Vec<String> = Vec::new();
    check_err_fuel_empty("Fold-1", &control, &treatment, &mut dev);
    assert!(dev.is_empty(), "Fold-1 typed-channel deviations:\n{}", dev.join("\n"));
}

/// Drive `subject` through BOTH arms of `def` on a dedicated LARGE-STACK thread (design v2 §5, the
/// L2 SHARED-REDUCER-DEPTH finding). ROOT CAUSE (gdb-proven): the f1r3node reducer recurses on
/// RESULT-TERM DEPTH via a mutual recursion `eval_expr_to_par ↔ eval_expr ↔ eval_expr_to_expr`
/// (reduce.rs) that walks each nested reflected `EList` sub-`Par`, compounded by the prost-DERIVED
/// `Clone` for `Par`/`Expr`/`EList` (generated `rhoapi.rs`) which recurses ~8 frames/level. The W-B
/// ladder NF `(D1..Ds)^m (End)` reaches depth `s·m + 1` — up to 129 at s=8,m=16 — far past what the
/// 8MB test-thread default holds (≈ depth 17). Without more stack the drive SIGABRTs on BOTH arms
/// IDENTICALLY. That overflow is a SHARED reducer artifact, NOT a scion property: PROVEN by the
/// treatment doing exactly 18 DriveTau whether the NF is depth 17 (s=1,m=16 — PASSES on 8MB) or
/// depth 33 (s=2,m=16 — SIGABRTs on 8MB) — identical COMM work, the overflow tracks DEPTH not the
/// scion's COMM count. The principled fix (trampoline the reducer eval + Clone) is a core reducer
/// re-architecture (significant churn, generated-code Clone), so this test provisions a 512MB drive
/// stack (comfortably past 129·≈0.5MB/level) — localized, zero reducer churn — to run the full
/// uncapped grid and validate the ΔDriveTau/firing = s recovery on every cell. `#[tokio::test]` is
/// current-thread, so blocking the test thread on `join` while the big-stack thread drives is fine.
fn drive_both_arms_big_stack(
    def: &mettail_ast::language::LanguageDef,
    subject: &GroundTerm,
) -> (ArmObservation, ArmObservation) {
    let arms = scion_arm_programs(def).expect("both arms plan + install");
    let control = arms.control_installed.clone();
    let treatment = arms.treatment_installed.clone();
    let fingerprint = arms.fingerprint.clone();
    let subject = subject.clone();
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("drive runtime builds");
            rt.block_on(async move {
                let reflected = reflect_ground_term_par(&subject, &fingerprint);
                let call =
                    rho_net_drive_call_par_with_fuel(&fingerprint, reflected, CELL_FUEL, "OUT");
                let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
                let (c_set, c_comm) = drive_arm_with_counters(&control, &call, &channels)
                    .await
                    .expect("control drive runs to quiescence");
                let (t_set, t_comm) = drive_arm_with_counters(&treatment, &call, &channels)
                    .await
                    .expect("treatment drive runs to quiescence");
                (
                    ArmObservation { set: c_set, comm: c_comm },
                    ArmObservation { set: t_set, comm: t_comm },
                )
            })
        })
        .expect("spawn big-stack drive thread")
        .join()
        .expect("big-stack drive thread joined")
}

// ══ W-D — the Ambient payoff cell: the demand-driven scion is INERT on Ambient (ΔDriveTau = 0) ══
//
// E-1 leg W-D (pgmcp experiment 147). Design v2 §5 (re-measure) + §7 (Ambient residual); SM-1
// (the locked re-derivation procedure). Re-derived prediction (`scratchpad/e1_wd_predictions.md`,
// written BEFORE this measurement per Fold 2): under the DEMAND-DRIVEN M1, the three Ambient
// structural rewrites In/Out/Open predict `ΔDriveTau/firing = 0`.
//
// MECHANISM (re-derived from the LANDED A-S5.5 arm shapes, SM-1): In/Out/Open are AC-family arms —
// `InRule`/`OutRule` are NestedStructuralAcRewrite (`rho_net_inout_firing.rs:66-69` pins them as the
// two nested structural-AC injection sites) and `OpenRule` is StructuralAcRewrite. AC arms fire
// through `ac_fuel_gated_firing`, whose emission is HARD-WIRED `FiringEmission::ContractumRedrive`
// (`rho_net_drive.rs:2621`) — there is NO scion branch. (And even a hypothetical POSITIONAL bag RHS
// fails `scion_collect_slots` closed at `:2223` — a `PPar{…}` / rest-slot RHS is a "collection"
// shape → ContractumRedrive.) So `StructuralScion` emits NO bundle for any Ambient rule ⇒ the
// treatment installed program is BYTE-IDENTICAL to the AllRedrive control ⇒ Δ = 0 on EVERY counter.
//
// This is the HONEST M1 Ambient result (v2 §7): Δ=0 satisfies the `ΔDriveTau ≥ 0` invariant. The
// task's "In 5/5 Recheck → maximal-recheck-subtree = ROOT → resubmit-whole = redrive-whole → Δ=0"
// reaches the SAME value idealizedly; the landed L1 reaches it by the STRONGER fail-closed route
// (the scion is never even emitted). The `recheck-not-redrive Δ>0` (eager SM-1's In Δ=3) is the
// DOCUMENTED depth-d follow-on (v2 §7 — a bounded-depth `^drive-to-depth` receiver), NOT this leg.
//
// Correctness (Ambient is NON-confluent ⇒ valid-NF-set MEMBERSHIP, SM-7/R-4): each subject below
// contains exactly ONE redex pair (a single In/Out/Open firing) ⇒ the valid-NF-set is a SINGLETON
// ⇒ membership degenerates to equality with the known flat NF (the A-S5.5-validated NFs from
// `rho_net_ambient_full.rs`). The three AM-3 flattening subjects (g1 bag-bodied, g2 empty-bag, g3
// double-nested never-driven) are re-run under the treatment arm as the acceptance gates.
//
// Kept in its OWN module (`use super::*`) so the Ambient helpers cannot collide with anything else
// in this file (concurrent-agent hygiene).
mod w_d_ambient {
    use super::*;

    type Value = RuntimeObservationValue;

    /// The PRODUCTION Ambient `LanguageDef` (In/Out/Open C-G rules) — the SAME source
    /// `rho_net_ambient_full.rs` drives, reconstructed from the generated metadata.
    fn ambient_def() -> mettail_ast::language::LanguageDef {
        let source = AmbientLanguage
            .metadata()
            .definition_source()
            .expect("AmbientLanguage exposes its definition_source");
        reconstruct_language_def(source).expect("production Ambient def reconstructs")
    }

    // ── direct-seed GroundTerm builders (mirror rho_net_ambient_full.rs) ──
    fn g_bag(elements: Vec<GroundTerm>) -> GroundTerm {
        GroundTerm::collection(CollectionType::HashBag, "PPar", elements)
    }
    fn g_zero() -> GroundTerm {
        GroundTerm::nullary("PZero")
    }
    fn g_name(atom: &str) -> GroundTerm {
        GroundTerm::new(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(atom)])
    }
    fn g_amb(name: GroundTerm, body: GroundTerm) -> GroundTerm {
        GroundTerm::new("PAmb", vec![name, body])
    }
    fn g_in(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
        GroundTerm::new("PIn", vec![name, cont])
    }
    fn g_out(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
        GroundTerm::new("POut", vec![name, cont])
    }
    fn g_open(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
        GroundTerm::new("POpen", vec![name, cont])
    }
    fn g_leaf_amb(atom: &str) -> GroundTerm {
        g_amb(g_name(atom), g_bag(vec![g_zero()]))
    }

    // ── expected-NF decoded-observation builders (mirror rho_net_ambient_full.rs) ──
    fn oterm(constructor: &str, children: Vec<Value>) -> Value {
        Value::Term {
            constructor: constructor.to_string(),
            children,
        }
    }
    fn ozero() -> Value {
        oterm("PZero", Vec::new())
    }
    fn oname(atom: &str) -> Value {
        oterm(FREE_VAR_REFLECT_LABEL, vec![oterm(atom, Vec::new())])
    }
    fn oamb(name: Value, body: Value) -> Value {
        oterm("PAmb", vec![name, body])
    }
    fn obag(values: Vec<Value>) -> Value {
        let mut counts = std::collections::BTreeMap::<Value, usize>::new();
        for value in values {
            *counts.entry(value).or_insert(0) += 1;
        }
        Value::Bag(counts.into_iter().collect())
    }
    fn o_leaf_amb(atom: &str) -> Value {
        oamb(oname(atom), obag(vec![ozero()]))
    }

    /// The host FLATTEN mirror (`add_flattened_bag`) — canonicalizes every bag to FLAT form so the
    /// membership comparison is over the AM-3-canonical NF (idempotent on already-flat OUT).
    fn flatten(value: &Value) -> Value {
        match value {
            Value::Bag(entries) => {
                let mut flat: Vec<Value> = Vec::with_capacity(entries.len());
                for (element, count) in entries {
                    let element = flatten(element);
                    for _ in 0..*count {
                        match &element {
                            Value::Bag(inner) => {
                                for (inner_element, inner_count) in inner {
                                    for _ in 0..*inner_count {
                                        flat.push(inner_element.clone());
                                    }
                                }
                            },
                            other => flat.push(other.clone()),
                        }
                    }
                }
                obag(flat)
            },
            Value::Term { constructor, children } => {
                oterm(constructor, children.iter().map(flatten).collect())
            },
            other => other.clone(),
        }
    }

    /// The W-D subjects: `(label, fired-rule, direct-seed subject, expected flat NF)`. Each is a
    /// SINGLE-redex subject (one In/Out/Open firing) — the g1/g2/g3 rows are the three MANDATORY
    /// AM-3 flattening subjects (`rho_net_ambient_full.rs:749-841`).
    fn w_d_subjects() -> Vec<(&'static str, &'static str, GroundTerm, Value)> {
        vec![
            // OpenRule — the three AM-3 flattening acceptance gates.
            (
                "open g1 bag-bodied",
                "OpenRule",
                g_bag(vec![
                    g_open(g_name("n"), g_bag(vec![g_leaf_amb("a"), g_leaf_amb("b")])),
                    g_amb(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
                ]),
                obag(vec![o_leaf_amb("a"), o_leaf_amb("b"), o_leaf_amb("c")]),
            ),
            (
                "open g2 empty-bag",
                "OpenRule",
                g_bag(vec![
                    g_open(g_name("n"), g_bag(Vec::new())),
                    g_amb(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
                ]),
                obag(vec![o_leaf_amb("c")]),
            ),
            (
                "open g3 double-nested",
                "OpenRule",
                g_bag(vec![
                    g_open(
                        g_name("n"),
                        g_bag(vec![
                            g_leaf_amb("a"),
                            g_bag(vec![
                                g_leaf_amb("b"),
                                g_bag(vec![g_leaf_amb("c"), g_leaf_amb("d")]),
                            ]),
                        ]),
                    ),
                    g_amb(g_name("n"), g_bag(vec![g_leaf_amb("r")])),
                ]),
                obag(vec![
                    o_leaf_amb("a"),
                    o_leaf_amb("b"),
                    o_leaf_amb("c"),
                    o_leaf_amb("d"),
                    o_leaf_amb("r"),
                ]),
            ),
            // InRule — n moves INTO m; the delivered R splices flat.
            (
                "in",
                "InRule",
                g_bag(vec![
                    g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())])),
                    g_amb(g_name("m"), g_bag(vec![g_leaf_amb("r")])),
                ]),
                obag(vec![oamb(
                    oname("m"),
                    obag(vec![oamb(oname("n"), obag(vec![ozero()])), o_leaf_amb("r")]),
                )]),
            ),
            // OutRule (post-AM-1) — the residual stays INSIDE m: 3-element residual + singleton.
            (
                "out 3-elem residual",
                "OutRule",
                g_amb(
                    g_name("m"),
                    g_bag(vec![
                        g_amb(g_name("n"), g_bag(vec![g_out(g_name("m"), g_leaf_amb("a"))])),
                        g_leaf_amb("b"),
                        g_leaf_amb("c"),
                    ]),
                ),
                obag(vec![
                    oamb(oname("n"), obag(vec![o_leaf_amb("a")])),
                    oamb(oname("m"), obag(vec![o_leaf_amb("b"), o_leaf_amb("c")])),
                ]),
            ),
            (
                "out singleton empty-bag",
                "OutRule",
                g_amb(
                    g_name("m"),
                    g_bag(vec![g_amb(g_name("n"), g_bag(vec![g_out(g_name("m"), g_zero())]))]),
                ),
                obag(vec![
                    oamb(oname("n"), obag(vec![ozero()])),
                    oamb(oname("m"), obag(Vec::new())),
                ]),
            ),
        ]
    }

    #[tokio::test]
    async fn w_d_ambient_scion_delta_zero() {
        mettail_runtime::clear_var_cache();
        let def = ambient_def();
        let arms =
            scion_arm_programs(&def).expect("production Ambient def plans + installs both arms");

        // THE W-D STRUCTURAL RESULT (the re-derived prediction): no Ambient rule scions ⇒ the
        // StructuralScion treatment program is BYTE-IDENTICAL to the AllRedrive control. This is
        // WHY ΔDriveTau/firing = 0 on In/Out/Open (a stronger statement than equal-DriveTau).
        assert_eq!(
            arms.control_installed, arms.treatment_installed,
            "W-D: no Ambient rule scions (In/Out/Open are AC arms → always ContractumRedrive; a bag \
             RHS would also fail scion_collect_slots closed), so the StructuralScion treatment \
             program must be BYTE-IDENTICAL to the AllRedrive control"
        );

        let mut deviations: Vec<String> = Vec::new();
        println!("── W-D (Ambient payoff) — demand-driven ΔDriveTau/firing = 0 (scion INERT on AC rules) ──");
        println!(
            "   treatment == control : {} (both {} bytes) — the scion emits NO bundle for any \
             Ambient rule",
            arms.control_installed == arms.treatment_installed,
            prost::Message::encoded_len(&arms.control_installed),
        );
        println!("   subject                 | fires   | DriveTau(c/t) ΔDrive | firing_visible(c/t)=accept/sa | total(c/t) | fired");

        for (name, rule, subject, expected_nf) in w_d_subjects() {
            let (control, treatment) = drive_installed_arms(
                &arms.control_installed,
                &arms.treatment_installed,
                &arms.fingerprint,
                &subject,
            )
            .await;
            let c = &control.comm;
            let t = &treatment.comm;
            let delta_drive = c.drive_tau as i64 - t.drive_tau as i64;
            let fired = fired_sorted(&control.set);
            let n_fired = fired_count(&control.set, rule);
            println!(
                "  {name:23} | {rule:7} | {:5}/{:<5} {delta_drive:5} | {:4}/{:<4}                     | {:5}/{:<5} | {fired:?}",
                c.drive_tau, t.drive_tau, c.firing_visible, t.firing_visible,
                total_comms(c), total_comms(t),
            );

            // (1) FROZEN: ΔDriveTau/firing = 0 (the re-derived M1 prediction; `rule` is an AC arm
            // ⇒ ContractumRedrive on BOTH arms ⇒ 0). A deviation is REPORTED, never adjusted.
            check(
                delta_drive == 0,
                format!("W-D {name}: ΔDriveTau = {delta_drive}, predicted 0 ({rule} is an AC arm → no scion)"),
                &mut deviations,
            );
            // (2) Δ on EVERY counter = 0 (byte-identical installed programs). Δ(accept/sa) =
            // Δfiring_visible = 0 REFINES the design §5 "Δ(accept/sa)=1": with no ScionBundle
            // emitted there is NO accept bypass (SM-1 re-pin against the landed AC arms).
            check(
                c.matching_tau == t.matching_tau,
                format!(
                    "W-D {name}: Δmatching_tau={}",
                    c.matching_tau as i64 - t.matching_tau as i64
                ),
                &mut deviations,
            );
            check(
                c.firing_visible == t.firing_visible,
                format!(
                    "W-D {name}: Δ(accept/sa)=Δfiring_visible={}, predicted 0",
                    c.firing_visible as i64 - t.firing_visible as i64
                ),
                &mut deviations,
            );
            check(
                c.subst_tau == t.subst_tau,
                format!("W-D {name}: Δsubst_tau={}", c.subst_tau as i64 - t.subst_tau as i64),
                &mut deviations,
            );
            check(
                c.respread_tau == t.respread_tau,
                format!(
                    "W-D {name}: Δrespread_tau={}",
                    c.respread_tau as i64 - t.respread_tau as i64
                ),
                &mut deviations,
            );
            check(
                c.ac_carrier == t.ac_carrier,
                format!("W-D {name}: Δac_carrier={}", c.ac_carrier as i64 - t.ac_carrier as i64),
                &mut deviations,
            );
            check(
                c.pathmap_index == t.pathmap_index,
                format!("W-D {name}: Δpathmap_index"),
                &mut deviations,
            );
            check(
                c.contextual_plumbing == t.contextual_plumbing,
                format!("W-D {name}: Δcontextual_plumbing"),
                &mut deviations,
            );
            check(
                c.observation == t.observation,
                format!("W-D {name}: Δobservation={}", c.observation as i64 - t.observation as i64),
                &mut deviations,
            );
            check(
                c.other == t.other,
                format!("W-D {name}: Δother={}", c.other as i64 - t.other as i64),
                &mut deviations,
            );
            check(
                total_comms(c) == total_comms(t),
                format!("W-D {name}: Δtotal={}", total_comms(c) as i64 - total_comms(t) as i64),
                &mut deviations,
            );

            // (3) fired-multiset / ledger consistency: exactly `[rule]` on BOTH arms.
            check(
                fired == vec![rule.to_string()],
                format!("W-D {name}: control fired {fired:?}, expected [{rule:?}]"),
                &mut deviations,
            );
            check(
                n_fired == 1,
                format!("W-D {name}: expected exactly 1 {rule} firing, got {n_fired}"),
                &mut deviations,
            );
            check(
                fired == fired_sorted(&treatment.set),
                format!("W-D {name}: fired multisets differ across arms"),
                &mut deviations,
            );

            // (4) valid-NF-set MEMBERSHIP (singleton set = the known flat NF) on BOTH arms.
            if control.set.out_values.is_empty() || treatment.set.out_values.is_empty() {
                check(
                    false,
                    format!("W-D {name}: OUT is empty (subject did not reach a resting NF)"),
                    &mut deviations,
                );
                continue;
            }
            let observed_c = flatten(&control.set.out_values[0]);
            let observed_t = flatten(&treatment.set.out_values[0]);
            check(observed_c == expected_nf, format!("W-D {name}: control NF membership — flatten(OUT)={observed_c:?} != expected {expected_nf:?}"), &mut deviations);
            check(observed_t == expected_nf, format!("W-D {name}: treatment NF membership — flatten(OUT)={observed_t:?} != expected {expected_nf:?}"), &mut deviations);

            // (5) typed fail-close channels EMPTY on both arms.
            check_err_fuel_empty(&format!("W-D {name}"), &control, &treatment, &mut deviations);
        }
        assert!(
            deviations.is_empty(),
            "W-D FROZEN-prediction deviations (report, do NOT adjust — a counter ≠ 0 or a broken \
             NF/fired gate is a finding):\n{}",
            deviations.join("\n")
        );
    }
}
