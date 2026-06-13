(*
 * RhoBackendFlipGate: per-language default-backend switch safety.
 *
 * A language may select the Rho backend by default only when its proof,
 * oracle-parity, coverage, generated-artifact validation, and deadlock gates
 * are all true.  This file proves the Boolean gate is exactly that conjunction
 * and that any missing gate blocks the flip.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Section RhoBackendFlipGate.

  Record GateState : Type := {
    proofs_passed : bool;
    oracle_parity_passed : bool;
    coverage_passed : bool;
    artifact_validated : bool;
    no_new_deadlocks : bool
  }.

  Definition can_flip_to_rho (g : GateState) : bool :=
    proofs_passed g
    && oracle_parity_passed g
    && coverage_passed g
    && artifact_validated g
    && no_new_deadlocks g.

  Theorem can_flip_iff_all_gates : forall g,
    can_flip_to_rho g = true
    <-> proofs_passed g = true
        /\ oracle_parity_passed g = true
        /\ coverage_passed g = true
        /\ artifact_validated g = true
        /\ no_new_deadlocks g = true.
  Proof.
    intros [p o c a d]. simpl. unfold can_flip_to_rho. simpl.
    repeat rewrite andb_true_iff.
    split.
    - intros [[[[Hp Ho] Hc] Ha] Hd].
      repeat split; assumption.
    - intros [Hp [Ho [Hc [Ha Hd]]]].
      repeat split; assumption.
  Qed.

  Theorem missing_proofs_blocks_flip : forall g,
    proofs_passed g = false -> can_flip_to_rho g = false.
  Proof. intros [p o c a d] H. simpl in *. rewrite H. reflexivity. Qed.

  Theorem missing_oracle_blocks_flip : forall g,
    oracle_parity_passed g = false -> can_flip_to_rho g = false.
  Proof.
    intros [p o c a d] H. simpl in *. rewrite H.
    destruct p; reflexivity.
  Qed.

  Theorem missing_coverage_blocks_flip : forall g,
    coverage_passed g = false -> can_flip_to_rho g = false.
  Proof.
    intros [p o c a d] H. simpl in *. rewrite H.
    destruct p; destruct o; reflexivity.
  Qed.

  Theorem missing_artifact_validation_blocks_flip : forall g,
    artifact_validated g = false -> can_flip_to_rho g = false.
  Proof.
    intros [p o c a d] H. simpl in *. rewrite H.
    destruct p; destruct o; destruct c; reflexivity.
  Qed.

  Theorem missing_deadlock_gate_blocks_flip : forall g,
    no_new_deadlocks g = false -> can_flip_to_rho g = false.
  Proof.
    intros [p o c a d] H. simpl in *. rewrite H.
    destruct p; destruct o; destruct c; destruct a; reflexivity.
  Qed.

  Definition deadlock_report_passes (diagnostic_count : nat) : bool :=
    Nat.eqb diagnostic_count 0.

  Definition gate_state_from_deadlock_report
      (proofs oracle coverage artifact : bool)
      (diagnostic_count : nat) : GateState :=
    {|
      proofs_passed := proofs;
      oracle_parity_passed := oracle;
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

  Theorem deadlock_diagnostic_blocks_flip : forall proofs oracle coverage artifact n,
    n <> 0 ->
    can_flip_to_rho
      (gate_state_from_deadlock_report proofs oracle coverage artifact n) = false.
  Proof.
    intros proofs oracle coverage artifact n Hnonzero.
    unfold gate_state_from_deadlock_report. simpl.
    rewrite (nonempty_deadlock_report_fails n Hnonzero).
    destruct proofs; destruct oracle; destruct coverage; destruct artifact; reflexivity.
  Qed.

  Theorem clean_deadlock_report_reduces_to_other_gates : forall proofs oracle coverage artifact,
    can_flip_to_rho
      (gate_state_from_deadlock_report proofs oracle coverage artifact 0) = true
    <-> proofs = true /\ oracle = true /\ coverage = true /\ artifact = true.
  Proof.
    intros proofs oracle coverage artifact.
    unfold gate_state_from_deadlock_report. simpl.
    destruct proofs; destruct oracle; destruct coverage; destruct artifact; simpl; split; intro H;
      try discriminate H;
      try (repeat split; reflexivity);
      destruct H as [Hp [Ho [Hc Ha]]]; discriminate.
  Qed.

  Definition bool_blocker_count (gate : bool) : nat :=
    if gate then 0 else 1.

  Definition flip_blocker_count (g : GateState) : nat :=
    bool_blocker_count (proofs_passed g)
    + bool_blocker_count (oracle_parity_passed g)
    + bool_blocker_count (coverage_passed g)
    + bool_blocker_count (artifact_validated g)
    + bool_blocker_count (no_new_deadlocks g).

  Theorem no_blockers_iff_can_flip : forall g,
    flip_blocker_count g = 0 <-> can_flip_to_rho g = true.
  Proof.
    intros [p o c a d]. simpl.
    destruct p; destruct o; destruct c; destruct a; destruct d; simpl; split; intro H;
      try reflexivity;
      try discriminate H.
  Qed.

  Theorem any_blocker_blocks_flip : forall g,
    flip_blocker_count g <> 0 ->
    can_flip_to_rho g = false.
  Proof.
    intros [p o c a d] Hblocker. simpl in *.
    destruct p; destruct o; destruct c; destruct a; destruct d; simpl in *;
      try reflexivity;
      exfalso; apply Hblocker; reflexivity.
  Qed.

  Record CoverageState : Type := {
    coverage_audit_passed : bool;
    uncovered_rejections : nat;
    extraneous_delegations : nat
  }.

  Definition exact_coverage_evidence (c : CoverageState) : bool :=
    coverage_audit_passed c
    && Nat.eqb (uncovered_rejections c) 0
    && Nat.eqb (extraneous_delegations c) 0.

  Definition default_backend_gate
      (proofs oracle artifact : bool)
      (coverage : CoverageState)
      (diagnostic_count : nat) : bool :=
    can_flip_to_rho
      (gate_state_from_deadlock_report
        proofs oracle (exact_coverage_evidence coverage) artifact diagnostic_count).

  Theorem exact_coverage_evidence_iff : forall c,
    exact_coverage_evidence c = true
    <-> coverage_audit_passed c = true
        /\ uncovered_rejections c = 0
        /\ extraneous_delegations c = 0.
  Proof.
    intros [audit uncovered extra]. simpl.
    destruct audit; simpl.
    - split.
      + intro H. apply andb_true_iff in H.
        destruct H as [Huncovered Hextra].
        apply Nat.eqb_eq in Huncovered.
        apply Nat.eqb_eq in Hextra.
        repeat split; assumption.
      + intros [_ [Huncovered Hextra]].
        apply andb_true_iff. split; apply Nat.eqb_eq; assumption.
    - split; intro H.
      + discriminate H.
      + destruct H as [Haudit _]. discriminate Haudit.
  Qed.

  Theorem uncovered_rejection_blocks_default_backend : forall proofs oracle artifact audit n extra diagnostics,
    n <> 0 ->
    default_backend_gate proofs oracle artifact
      {| coverage_audit_passed := audit;
         uncovered_rejections := n;
         extraneous_delegations := extra |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact audit n extra diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Huncovered : Nat.eqb n 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Huncovered.
    destruct proofs; destruct oracle; destruct artifact; destruct audit; reflexivity.
  Qed.

  Theorem extraneous_delegation_blocks_default_backend : forall proofs oracle artifact audit extra diagnostics,
    extra <> 0 ->
    default_backend_gate proofs oracle artifact
      {| coverage_audit_passed := audit;
         uncovered_rejections := 0;
         extraneous_delegations := extra |}
      diagnostics = false.
  Proof.
    intros proofs oracle artifact audit extra diagnostics Hnonzero.
    unfold default_backend_gate, gate_state_from_deadlock_report,
      exact_coverage_evidence, deadlock_report_passes.
    simpl.
    assert (Hextra : Nat.eqb extra 0 = false).
    { rewrite Nat.eqb_neq. assumption. }
    rewrite Hextra.
    destruct proofs; destruct oracle; destruct artifact; destruct audit; reflexivity.
  Qed.

  Theorem missing_artifact_validation_blocks_default_backend : forall proofs oracle coverage diagnostics,
    default_backend_gate proofs oracle false coverage diagnostics = false.
  Proof.
    intros proofs oracle coverage diagnostics.
    unfold default_backend_gate, gate_state_from_deadlock_report. simpl.
    destruct proofs; destruct oracle; destruct (exact_coverage_evidence coverage); reflexivity.
  Qed.

  Theorem default_backend_gate_iff_all_evidence : forall proofs oracle artifact coverage diagnostics,
    default_backend_gate proofs oracle artifact coverage diagnostics = true
    <-> proofs = true
        /\ oracle = true
        /\ artifact = true
        /\ coverage_audit_passed coverage = true
        /\ uncovered_rejections coverage = 0
        /\ extraneous_delegations coverage = 0
        /\ diagnostics = 0.
  Proof.
    intros proofs oracle artifact coverage diagnostics.
    unfold default_backend_gate.
    rewrite can_flip_iff_all_gates.
    unfold gate_state_from_deadlock_report. simpl.
    rewrite exact_coverage_evidence_iff.
    rewrite deadlock_report_passes_iff_empty.
    split.
    - intros [Hproofs [Horacle [Hcoverage [Hartifact Hdiagnostics]]]].
      destruct Hcoverage as [Haudit [Huncovered Hextra]].
      repeat split; assumption.
    - intros [Hproofs [Horacle [Hartifact [Haudit [Huncovered [Hextra Hdiagnostics]]]]]].
      split; [assumption|].
      split; [assumption|].
      split.
      + repeat split; assumption.
      + split; assumption.
  Qed.

End RhoBackendFlipGate.
