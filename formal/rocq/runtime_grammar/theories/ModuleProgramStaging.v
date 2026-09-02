From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

(** Ordinary Rholang processes inside Greg/Mike modules are program data, not
    language specifications and not installation authority.  The runtime walks
    module items once, with a heap worklist, and records each program's exact
    source ordinal. *)
Inductive ModuleItem : Type :=
| TheoryItem (theory : nat)
| ProgramItem (program : nat).

Record StagedProgram : Type := {
  staged_ordinal : nat;
  staged_body : nat
}.

Record StageState : Type := {
  staged_theories_rev : list nat;
  staged_programs_rev : list StagedProgram;
  staged_next_ordinal : nat
}.

(** Tail-recursive functional model of the Rust explicit worklist.  Only the
    pending list decreases; source-controlled module depth never consumes the
    native call stack in the implementation. *)
Fixpoint stage_worklist
    (pending : list ModuleItem)
    (ordinal : nat)
    (theories_rev : list nat)
    (programs_rev : list StagedProgram) : StageState :=
  match pending with
  | [] =>
      {| staged_theories_rev := theories_rev;
         staged_programs_rev := programs_rev;
         staged_next_ordinal := ordinal |}
  | TheoryItem theory :: rest =>
      stage_worklist rest (S ordinal) (theory :: theories_rev) programs_rev
  | ProgramItem program :: rest =>
      stage_worklist rest (S ordinal) theories_rev
        ({| staged_ordinal := ordinal; staged_body := program |} :: programs_rev)
  end.

Fixpoint theory_projection (items : list ModuleItem) : list nat :=
  match items with
  | [] => []
  | TheoryItem theory :: rest => theory :: theory_projection rest
  | ProgramItem _ :: rest => theory_projection rest
  end.

Fixpoint program_projection_from
    (ordinal : nat) (items : list ModuleItem) : list StagedProgram :=
  match items with
  | [] => []
  | TheoryItem _ :: rest => program_projection_from (S ordinal) rest
  | ProgramItem program :: rest =>
      {| staged_ordinal := ordinal; staged_body := program |}
        :: program_projection_from (S ordinal) rest
  end.

Lemma stage_worklist_refines_projections :
  forall items ordinal theories_rev programs_rev,
    staged_theories_rev
      (stage_worklist items ordinal theories_rev programs_rev) =
      rev (theory_projection items) ++ theories_rev /\
    staged_programs_rev
      (stage_worklist items ordinal theories_rev programs_rev) =
      rev (program_projection_from ordinal items) ++ programs_rev /\
    staged_next_ordinal
      (stage_worklist items ordinal theories_rev programs_rev) =
      ordinal + length items.
Proof.
  induction items as [| item rest IH]; intros ordinal theories_rev programs_rev.
  - simpl. repeat split; try reflexivity; lia.
  - destruct item as [theory | program]; simpl.
    + specialize (IH (S ordinal) (theory :: theories_rev) programs_rev).
      destruct IH as [Htheories [Hprograms Hnext]].
      split.
      * rewrite Htheories. simpl. rewrite <- app_assoc. reflexivity.
      * split.
        -- exact Hprograms.
        -- rewrite Hnext. lia.
    + specialize (IH (S ordinal) theories_rev
          ({| staged_ordinal := ordinal; staged_body := program |} :: programs_rev)).
      destruct IH as [Htheories [Hprograms Hnext]].
      split.
      * exact Htheories.
      * split.
        -- rewrite Hprograms. simpl. rewrite <- app_assoc. reflexivity.
        -- rewrite Hnext. lia.
Qed.

Definition stage_items (items : list ModuleItem)
    : list nat * list StagedProgram :=
  let state := stage_worklist items 0 [] [] in
  (rev (staged_theories_rev state), rev (staged_programs_rev state)).

Theorem iterative_staging_preserves_theory_order :
  forall items,
    fst (stage_items items) = theory_projection items.
Proof.
  intros items. unfold stage_items.
  destruct (stage_worklist_refines_projections items 0 [] [])
    as [Htheories _].
  rewrite Htheories, app_nil_r, rev_involutive. reflexivity.
Qed.

Theorem iterative_staging_preserves_program_order_and_ordinals :
  forall items,
    snd (stage_items items) = program_projection_from 0 items.
Proof.
  intros items. unfold stage_items.
  destruct (stage_worklist_refines_projections items 0 [] [])
    as [_ [Hprograms _]].
  rewrite Hprograms, app_nil_r, rev_involutive. reflexivity.
Qed.

(** Installation and program release are separate effects.  A failed install
    returns no handles and cannot release even one staged process. *)
Inductive InstallOutcome : Type :=
| InstallRejected
| InstallCommitted
    (handles : list nat)
    (programs : list StagedProgram).

Definition install_then_stage
    (validated : bool) (handles : list nat) (items : list ModuleItem)
    : InstallOutcome :=
  if validated then InstallCommitted handles (snd (stage_items items))
  else InstallRejected.

Definition program_released
    (outcome : InstallOutcome) (program : StagedProgram) : Prop :=
  match outcome with
  | InstallRejected => False
  | InstallCommitted _ programs => In program programs
  end.

Theorem failed_install_releases_no_program :
  forall handles items program,
    ~ program_released (install_then_stage false handles items) program.
Proof.
  intros. simpl. tauto.
Qed.

Theorem committed_install_releases_exact_staging_projection :
  forall handles items,
    install_then_stage true handles items =
      InstallCommitted handles (program_projection_from 0 items).
Proof.
  intros handles items.
  change (InstallCommitted handles (snd (stage_items items)) =
    InstallCommitted handles (program_projection_from 0 items)).
  rewrite iterative_staging_preserves_program_order_and_ordinals. reflexivity.
Qed.

(** The executable refinement obtains these two measures with bounded,
    heap-resident traversals of the complete normalized [Par] candidate before
    any program leaf is detached.  Keeping the measure abstract here separates
    the admission theorem from protobuf's concrete framing algebra. *)
Record CandidateMeasure : Type := {
  measured_nodes : nat;
  measured_bytes : nat
}.

Record AdmissionLimits : Type := {
  maximum_nodes : nat;
  maximum_bytes : nat
}.

Definition within_admission_limits
    (measure : CandidateMeasure) (limits : AdmissionLimits) : bool :=
  (measured_nodes measure <=? maximum_nodes limits) &&
  (measured_bytes measure <=? maximum_bytes limits).

(** Resource admission and semantic validation both precede the one commit
    point.  Staging is pure: the successful branch returns its projection,
    while either rejection branch exposes nothing. *)
Definition admitted_install_then_stage
    (measure : CandidateMeasure)
    (limits : AdmissionLimits)
    (validated : bool)
    (handles : list nat)
    (items : list ModuleItem) : InstallOutcome :=
  if within_admission_limits measure limits && validated
  then InstallCommitted handles (snd (stage_items items))
  else InstallRejected.

Theorem admitted_release_implies_resource_bounds :
  forall measure limits validated handles items program,
    program_released
      (admitted_install_then_stage measure limits validated handles items)
      program ->
    measured_nodes measure <= maximum_nodes limits /\
    measured_bytes measure <= maximum_bytes limits.
Proof.
  intros measure limits validated handles items program Hreleased.
  unfold admitted_install_then_stage in Hreleased.
  destruct (within_admission_limits measure limits && validated) eqn:Hgate;
    [| contradiction].
  apply andb_true_iff in Hgate as [Hlimits _].
  unfold within_admission_limits in Hlimits.
  apply andb_true_iff in Hlimits as [Hnodes Hbytes].
  apply Nat.leb_le in Hnodes. apply Nat.leb_le in Hbytes.
  auto.
Qed.

Theorem over_budget_releases_no_program :
  forall measure limits validated handles items program,
    (maximum_nodes limits <? measured_nodes measure) = true \/
    (maximum_bytes limits <? measured_bytes measure) = true ->
    ~ program_released
        (admitted_install_then_stage measure limits validated handles items)
        program.
Proof.
  intros measure limits validated handles items program Hover Hreleased.
  pose proof (admitted_release_implies_resource_bounds
    measure limits validated handles items program Hreleased) as [Hnodes Hbytes].
  destruct Hover as [Hover | Hover]; apply Nat.ltb_lt in Hover; lia.
Qed.

Theorem admitted_commit_releases_exact_staging_projection :
  forall measure limits handles items,
    within_admission_limits measure limits = true ->
    admitted_install_then_stage measure limits true handles items =
      InstallCommitted handles (program_projection_from 0 items).
Proof.
  intros measure limits handles items Hadmitted.
  unfold admitted_install_then_stage. rewrite Hadmitted. cbn [andb].
  rewrite iterative_staging_preserves_program_order_and_ordinals. reflexivity.
Qed.

(** Possessing staged data is not execution authority.  Execution additionally
    requires an explicit ordinary-Rholang authorization bit. *)
Definition execution_allowed
    (outcome : InstallOutcome) (execute_authority : bool)
    (program : StagedProgram) : Prop :=
  execute_authority = true /\ program_released outcome program.

Theorem execution_requires_commit_and_authority :
  forall outcome authority program,
    execution_allowed outcome authority program ->
    authority = true /\
    exists handles programs,
      outcome = InstallCommitted handles programs /\ In program programs.
Proof.
  intros outcome authority program [Hauthority Hreleased].
  split; [exact Hauthority |].
  destruct outcome as [| handles programs].
  - contradiction.
  - exists handles, programs. split; [reflexivity | exact Hreleased].
Qed.
