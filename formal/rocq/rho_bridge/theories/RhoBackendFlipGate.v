(*
 * RhoBackendFlipGate: per-language default-backend switch safety.
 *
 * A language may select the Rho backend by default only when the Rust planner
 * can validate exact coverage, generated-artifact shape, and absence of new
 * static channel deadlocks.  Proof/oracle attribution lives in formal
 * commentary and CI, not in runtime gate data.
 *
 * The second section (`RhoGuardQualityGate`) models the predicate-substrate
 * QUALITY axis wired into the gate by `rholang-codegen/src/backend.rs`:
 * each covered guard obligation carries a `RhoGuardQuality`, and an `Unknown`
 * quality (the only one that `refuses_production_default`) contributes a
 * fail-closed `RhoFlipBlocker::GuardQuality`.  It COMPOSES with the M7 mixed-
 * guard soundness theorem (`RhoGuardedCommSoundness.v`) — cited, not re-proved —
 * to show that a flip-eligible (Unknown-free) plan licenses exactly the case in
 * which a fired guarded Comm satisfies the true guard.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From RhoBridge Require Import RhoGuardedCommSoundness.

Import ListNotations.

Section RhoBackendFlipGate.

  Record GateState : Type := {
    coverage_passed : bool;
    artifact_validated : bool;
    no_new_deadlocks : bool
  }.

  Definition can_flip_to_rho (g : GateState) : bool :=
    coverage_passed g
    && artifact_validated g
    && no_new_deadlocks g.

  Theorem can_flip_iff_all_gates : forall g,
    can_flip_to_rho g = true
    <-> coverage_passed g = true
        /\ artifact_validated g = true
        /\ no_new_deadlocks g = true.
  Proof.
    intros [c a d]. simpl. unfold can_flip_to_rho. simpl.
    repeat rewrite andb_true_iff.
    split.
    - intros [[Hc Ha] Hd]. repeat split; assumption.
    - intros [Hc [Ha Hd]]. repeat split; assumption.
  Qed.

  Theorem missing_coverage_blocks_flip : forall g,
    coverage_passed g = false -> can_flip_to_rho g = false.
  Proof. intros [c a d] H. simpl in *. rewrite H. reflexivity. Qed.

  Theorem missing_artifact_validation_blocks_flip : forall g,
    artifact_validated g = false -> can_flip_to_rho g = false.
  Proof.
    intros [c a d] H. simpl in *. rewrite H.
    destruct c; reflexivity.
  Qed.

  Theorem missing_deadlock_gate_blocks_flip : forall g,
    no_new_deadlocks g = false -> can_flip_to_rho g = false.
  Proof.
    intros [c a d] H. simpl in *. rewrite H.
    destruct c; destruct a; reflexivity.
  Qed.

  Definition deadlock_report_passes (diagnostic_count : nat) : bool :=
    Nat.eqb diagnostic_count 0.

  Definition gate_state_from_deadlock_report
      (coverage artifact : bool)
      (diagnostic_count : nat) : GateState :=
    {|
      coverage_passed := coverage;
      artifact_validated := artifact;
      no_new_deadlocks := deadlock_report_passes diagnostic_count
    |}.

  Theorem empty_deadlock_report_passes :
    deadlock_report_passes 0 = true.
  Proof. reflexivity. Qed.

  Theorem deadlock_report_passes_iff_empty : forall n,
    deadlock_report_passes n = true <-> n = 0.
  Proof.
    intros n. unfold deadlock_report_passes.
    rewrite Nat.eqb_eq. split; intro H; assumption.
  Qed.

  Theorem nonempty_deadlock_report_fails : forall n,
    n <> 0 ->
    deadlock_report_passes n = false.
  Proof.
    intros n Hnonzero. unfold deadlock_report_passes.
    destruct n.
    - contradiction.
    - reflexivity.
  Qed.

  Theorem deadlock_diagnostic_blocks_flip : forall coverage artifact n,
    n <> 0 ->
    can_flip_to_rho
      (gate_state_from_deadlock_report coverage artifact n) = false.
  Proof.
    intros coverage artifact n Hnonzero.
    unfold gate_state_from_deadlock_report. simpl.
    rewrite (nonempty_deadlock_report_fails n Hnonzero).
    destruct coverage; destruct artifact; reflexivity.
  Qed.

  Theorem clean_deadlock_report_reduces_to_other_gates : forall coverage artifact,
    can_flip_to_rho
      (gate_state_from_deadlock_report coverage artifact 0) = true
    <-> coverage = true /\ artifact = true.
  Proof.
    intros coverage artifact.
    unfold gate_state_from_deadlock_report. simpl.
    destruct coverage; destruct artifact; simpl; split; intro H;
      try discriminate H;
      try (repeat split; reflexivity);
      destruct H as [Hcoverage Hartifact]; discriminate.
  Qed.

  Definition bool_blocker_count (gate : bool) : nat :=
    if gate then 0 else 1.

  Definition flip_blocker_count (g : GateState) : nat :=
    bool_blocker_count (coverage_passed g)
    + bool_blocker_count (artifact_validated g)
    + bool_blocker_count (no_new_deadlocks g).

  Theorem no_blockers_iff_can_flip : forall g,
    flip_blocker_count g = 0 <-> can_flip_to_rho g = true.
  Proof.
    intros [c a d]. simpl.
    destruct c; destruct a; destruct d; simpl; split; intro H;
      try reflexivity;
      try discriminate H.
  Qed.

  Theorem any_blocker_blocks_flip : forall g,
    flip_blocker_count g <> 0 ->
    can_flip_to_rho g = false.
  Proof.
    intros [c a d] Hblocker. simpl in *.
    destruct c; destruct a; destruct d; simpl in *;
      try reflexivity;
      exfalso; apply Hblocker; reflexivity.
  Qed.

  Record CoverageState : Type := {
    coverage_audit_passed : bool;
    uncovered_rejections : nat;
    extraneous_dispositions : nat;
    invalid_dispositions : nat;
    uncovered_guard_obligations : nat;
    extraneous_guard_dispositions : nat;
    invalid_guard_dispositions : nat
  }.

  Definition exact_coverage_evidence (c : CoverageState) : bool :=
    coverage_audit_passed c
    && Nat.eqb (uncovered_rejections c) 0
    && Nat.eqb (extraneous_dispositions c) 0
    && Nat.eqb (invalid_dispositions c) 0
    && Nat.eqb (uncovered_guard_obligations c) 0
    && Nat.eqb (extraneous_guard_dispositions c) 0
    && Nat.eqb (invalid_guard_dispositions c) 0.

  (* Compatibility signature for dependent coverage proofs.  The first, second,
     and fourth parameters are intentionally ignored: they are not runtime gate
     data in the Rust implementation. *)
  Definition default_backend_gate
      (_proofs _oracle artifact _fairness : bool)
      (coverage : CoverageState)
      (diagnostic_count : nat) : bool :=
    can_flip_to_rho
      (gate_state_from_deadlock_report
        (exact_coverage_evidence coverage) artifact diagnostic_count).

  Theorem exact_coverage_evidence_iff : forall c,
    exact_coverage_evidence c = true
    <-> coverage_audit_passed c = true
        /\ uncovered_rejections c = 0
        /\ extraneous_dispositions c = 0
        /\ invalid_dispositions c = 0
        /\ uncovered_guard_obligations c = 0
        /\ extraneous_guard_dispositions c = 0
        /\ invalid_guard_dispositions c = 0.
  Proof.
    intros [audit uncovered extra invalid uncovered_guard extra_guard invalid_guard].
    unfold exact_coverage_evidence. simpl.
    destruct audit; simpl.
    - repeat rewrite andb_true_iff. repeat rewrite Nat.eqb_eq.
      split.
      + intros [[[[[Huncovered Hextra] Hinvalid] Huncovered_guard]
          Hextra_guard] Hinvalid_guard].
        repeat split; assumption.
      + intros [_ [Huncovered [Hextra [Hinvalid
          [Huncovered_guard [Hextra_guard Hinvalid_guard]]]]]].
        repeat split; assumption.
    - split; intro H.
      + discriminate H.
      + destruct H as [Haudit _]. discriminate Haudit.
  Qed.

  Theorem uncovered_rejection_blocks_default_backend :
    forall proofs oracle artifact fairness audit n extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    n <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := n;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit n extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Huncovered : Nat.eqb n 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Huncovered.
    destruct artifact; destruct audit; reflexivity.
  Qed.

  Theorem extraneous_delegation_blocks_default_backend :
    forall proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    extra <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := uncovered;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hextra : Nat.eqb extra 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hextra.
    destruct artifact; destruct audit; destruct (Nat.eqb uncovered 0); reflexivity.
  Qed.

  Theorem invalid_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    invalid <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := uncovered;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hinvalid : Nat.eqb invalid 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hinvalid.
    destruct artifact; destruct audit;
      destruct (Nat.eqb uncovered 0); destruct (Nat.eqb extra 0); reflexivity.
  Qed.

  Theorem uncovered_guard_obligation_blocks_default_backend :
    forall proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    uncovered_guard <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := uncovered;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hguard : Nat.eqb uncovered_guard 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hguard.
    destruct artifact; destruct audit;
      destruct (Nat.eqb uncovered 0); destruct (Nat.eqb extra 0);
      destruct (Nat.eqb invalid 0); reflexivity.
  Qed.

  Theorem extraneous_guard_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    extra_guard <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := uncovered;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hguard : Nat.eqb extra_guard 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hguard.
    destruct artifact; destruct audit;
      destruct (Nat.eqb uncovered 0); destruct (Nat.eqb extra 0);
      destruct (Nat.eqb invalid 0); destruct (Nat.eqb uncovered_guard 0); reflexivity.
  Qed.

  Theorem invalid_guard_disposition_blocks_default_backend :
    forall proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics,
    invalid_guard <> 0 ->
    default_backend_gate proofs oracle artifact fairness
      {| coverage_audit_passed := audit;
         uncovered_rejections := uncovered;
         extraneous_dispositions := extra;
         invalid_dispositions := invalid;
         uncovered_guard_obligations := uncovered_guard;
         extraneous_guard_dispositions := extra_guard;
         invalid_guard_dispositions := invalid_guard |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact fairness audit uncovered extra invalid
      uncovered_guard extra_guard invalid_guard diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hguard : Nat.eqb invalid_guard 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hguard.
    destruct artifact; destruct audit;
      destruct (Nat.eqb uncovered 0); destruct (Nat.eqb extra 0);
      destruct (Nat.eqb invalid 0); destruct (Nat.eqb uncovered_guard 0);
      destruct (Nat.eqb extra_guard 0); reflexivity.
  Qed.

  Theorem missing_artifact_validation_blocks_default_backend :
    forall proofs oracle fairness coverage diagnostics,
    default_backend_gate proofs oracle false fairness coverage diagnostics = false.
  Proof.
    intros proofs oracle fairness coverage diagnostics.
    unfold default_backend_gate, gate_state_from_deadlock_report. simpl.
    destruct (exact_coverage_evidence coverage); reflexivity.
  Qed.

  Theorem default_backend_gate_iff_all_requirements :
    forall proofs oracle artifact fairness coverage diagnostics,
    default_backend_gate proofs oracle artifact fairness coverage diagnostics = true
    <-> artifact = true
        /\ coverage_audit_passed coverage = true
        /\ uncovered_rejections coverage = 0
        /\ extraneous_dispositions coverage = 0
        /\ invalid_dispositions coverage = 0
        /\ uncovered_guard_obligations coverage = 0
        /\ extraneous_guard_dispositions coverage = 0
        /\ invalid_guard_dispositions coverage = 0
        /\ diagnostics = 0.
  Proof.
    intros proofs oracle artifact fairness coverage diagnostics.
    unfold default_backend_gate.
    rewrite can_flip_iff_all_gates.
    unfold gate_state_from_deadlock_report. simpl.
    rewrite exact_coverage_evidence_iff.
    rewrite deadlock_report_passes_iff_empty.
    split.
    - intros [Hcoverage [Hartifact Hdiagnostics]].
      destruct Hcoverage as
        [Haudit [Huncovered [Hextra [Hinvalid [Hguard [Hextra_guard Hinvalid_guard]]]]]].
      repeat split; assumption.
    - intro H.
      destruct H as [Hartifact [Haudit [Huncovered H]]].
      destruct H as [Hextra [Hinvalid [Hguard [Hextra_guard [Hinvalid_guard Hdiagnostics]]]]].
      repeat split; try assumption.
  Qed.

End RhoBackendFlipGate.

(* ──────────────────────────────────────────────────────────────────────────
 * RhoGuardQualityGate: the predicate-substrate QUALITY axis of the flip gate.
 *
 * Rust mirror: `rholang-codegen/src/{guard_quality,flip,backend}.rs`.
 *   - `RhoGuardQuality` (the documented 7-value vocabulary);
 *   - `RhoGuardQuality::refuses_production_default` = `Unknown`-only;
 *   - `RhoFlipBlocker::GuardQuality { obligation, quality }`, one per covered
 *     obligation whose quality refuses production-default lowering;
 *   - `decide_rho_flip` folds those blockers into the gate.
 * ────────────────────────────────────────────────────────────────────────── *)
Section RhoGuardQualityGate.

  (* The documented 7-value guard-quality vocabulary (docs §04 / Rust
     `RhoGuardQuality`).  Only `Unknown` is fail-closed. *)
  Inductive RhoGuardQuality : Type :=
    | ExactDecidable
    | BoundedDecidable
    | RejectSafeApprox
    | TrustedNativeGuard
    | MachineCheckedModel
    | RuntimeObservation
    | Unknown.

  (* Faithful image of `RhoGuardQuality::refuses_production_default`: the gate
     must refuse production-default lowering for exactly `Unknown`. *)
  Definition refuses_production_default (q : RhoGuardQuality) : bool :=
    match q with
    | Unknown => true
    | _ => false
    end.

  Theorem refuses_production_default_iff_unknown : forall q,
    refuses_production_default q = true <-> q = Unknown.
  Proof.
    intro q. destruct q; simpl; split; intro H;
      solve [ reflexivity | discriminate H ].
  Qed.

  (* A covered guard obligation paired with its substrate quality (the Rust
     `RhoGuardDispositionQuality`; `goq_id` mirrors the obligation id). *)
  Record GuardObligationQuality : Type := {
    goq_id : nat;
    goq_quality : RhoGuardQuality
  }.

  (* The number of `RhoFlipBlocker::GuardQuality` blockers the planner derives:
     one per covered obligation whose quality refuses production-default
     lowering (the image of `guard_quality_blockers_for`). *)
  Definition quality_blocker_count (qs : list GuardObligationQuality) : nat :=
    length (filter (fun q => refuses_production_default (goq_quality q)) qs).

  (* No quality blockers  <->  every covered obligation is non-refusing
     (non-`Unknown`).  This is the "non-`Unknown` disposition is the unique
     evidence-backed owner" statement: the gate accepts the guard-quality axis
     exactly when no covered obligation refuses production-default lowering. *)
  Theorem quality_blocker_count_zero_iff_all_usable : forall qs,
    quality_blocker_count qs = 0
    <-> (forall q, In q qs -> refuses_production_default (goq_quality q) = false).
  Proof.
    intros qs. unfold quality_blocker_count.
    induction qs as [| q qs IH]; simpl.
    - split; [intros _ q Hin; inversion Hin | reflexivity].
    - destruct (refuses_production_default (goq_quality q)) eqn:Hq; simpl.
      + (* head refuses: count = S _, never 0; and the head witnesses the RHS
           cannot hold. *)
        split.
        * intro H. discriminate H.
        * intro H. specialize (H q (or_introl eq_refl)).
          rewrite Hq in H. discriminate H.
      + (* head is usable: reduce to the tail. *)
        rewrite IH. split.
        * intros Htail q' [Heq | Hin].
          -- subst q'. exact Hq.
          -- apply Htail. exact Hin.
        * intros Hall q' Hin. apply Hall. right. exact Hin.
  Qed.

  (* An `Unknown` quality among the covered obligations forces at least one
     blocker — the necessity of the fail-closed `GuardQuality` blocker. *)
  Theorem unknown_quality_contributes_blocker : forall qs q,
    In q qs ->
    goq_quality q = Unknown ->
    quality_blocker_count qs <> 0.
  Proof.
    intros qs q Hin Hunknown Hzero.
    pose proof (proj1 (quality_blocker_count_zero_iff_all_usable qs) Hzero q Hin) as Husable.
    rewrite Hunknown in Husable. simpl in Husable. discriminate Husable.
  Qed.

  (* The full flip gate including the guard-quality axis: the Boolean gate AND
     no quality blockers (the image of `decide_rho_flip` with the derived
     `RhoFlipBlocker::GuardQuality` list folded in). *)
  Definition can_flip_with_qualities
      (g : GateState) (qs : list GuardObligationQuality) : bool :=
    can_flip_to_rho g && Nat.eqb (quality_blocker_count qs) 0.

  Theorem can_flip_with_qualities_iff : forall g qs,
    can_flip_with_qualities g qs = true
    <-> can_flip_to_rho g = true
        /\ (forall q, In q qs -> refuses_production_default (goq_quality q) = false).
  Proof.
    intros g qs. unfold can_flip_with_qualities.
    rewrite andb_true_iff.
    rewrite Nat.eqb_eq.
    rewrite quality_blocker_count_zero_iff_all_usable.
    reflexivity.
  Qed.

  (* MAIN (necessity): an `Unknown`-quality covered obligation makes the flip
     gate refuse — the new blocker is necessary (doc-08: "`Unknown` quality ⇒
     production-default refused"). *)
  Theorem unknown_guard_quality_blocks_flip : forall g qs q,
    In q qs ->
    goq_quality q = Unknown ->
    can_flip_with_qualities g qs = false.
  Proof.
    intros g qs q Hin Hunknown.
    unfold can_flip_with_qualities.
    assert (Hnz : quality_blocker_count qs <> 0)
      by (apply (unknown_quality_contributes_blocker qs q Hin Hunknown)).
    assert (Hfalse : Nat.eqb (quality_blocker_count qs) 0 = false)
      by (rewrite Nat.eqb_neq; exact Hnz).
    rewrite Hfalse. apply andb_false_r.
  Qed.

  (* The flip gate ALSO refuses whenever the Boolean gate refuses, regardless of
     the quality axis (the quality axis only ever ADDS blockers). *)
  Theorem boolean_gate_failure_blocks_flip_with_qualities : forall g qs,
    can_flip_to_rho g = false ->
    can_flip_with_qualities g qs = false.
  Proof.
    intros g qs Hg. unfold can_flip_with_qualities. rewrite Hg. reflexivity.
  Qed.

  (* ── Composition with M7 (`RhoGuardedCommSoundness`), CITED not re-proved ──
   *
   * A flip-eligible (Boolean-passing AND `Unknown`-free) plan licenses
   * production-default lowering.  Exactly under that licensing the M7 mixed-
   * guard soundness applies: a fired guarded Comm satisfies the TRUE guard
   * (structural ∧ behavioral_true) — the reject-safe behavioral leg never
   * wrongly admits a Comm.  The first conjunct consumes the flip-eligibility
   * premise (via `can_flip_with_qualities_iff`); the second is M7's
   * `comm_fires_implies_true_guard`, instantiated here, not rederived. *)
  Theorem licensed_flip_is_guard_sound :
    forall (g : GateState) (qs : list GuardObligationQuality)
           (Subst : Type)
           (name_match structural_eval behavioral_eval behavioral_true : Subst -> bool),
      (forall s, behavioral_eval s = true -> behavioral_true s = true) ->
      can_flip_with_qualities g qs = true ->
      forall s,
        comm_fires Subst name_match structural_eval behavioral_eval s = true ->
        can_flip_to_rho g = true
        /\ name_match s = true
        /\ product_true Subst structural_eval behavioral_true s = true.
  Proof.
    intros g qs Subst name_match structural_eval behavioral_eval behavioral_true
      Hsound Hflip s Hfires.
    apply can_flip_with_qualities_iff in Hflip.
    destruct Hflip as [Hgate _].
    split; [exact Hgate |].
    apply (comm_fires_implies_true_guard
             Subst name_match structural_eval behavioral_eval behavioral_true
             Hsound s Hfires).
  Qed.

  (* Conversely, the soundness licensing is genuinely GATED: if a covered
     obligation is `Unknown`, no such licensing is granted (the plan does not
     flip), so the reject-safe lowering is never installed on un-evidenced
     guards. *)
  Theorem unknown_guard_quality_denies_licensing : forall g qs q,
    In q qs ->
    goq_quality q = Unknown ->
    can_flip_with_qualities g qs = true -> False.
  Proof.
    intros g qs q Hin Hunknown Hflip.
    rewrite (unknown_guard_quality_blocks_flip g qs q Hin Hunknown) in Hflip.
    discriminate Hflip.
  Qed.

End RhoGuardQualityGate.

Print Assumptions refuses_production_default_iff_unknown.
Print Assumptions quality_blocker_count_zero_iff_all_usable.
Print Assumptions unknown_quality_contributes_blocker.
Print Assumptions can_flip_with_qualities_iff.
Print Assumptions unknown_guard_quality_blocks_flip.
Print Assumptions licensed_flip_is_guard_sound.
Print Assumptions unknown_guard_quality_denies_licensing.
