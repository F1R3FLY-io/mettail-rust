(** * Concrete resource and ownership glue for installed semantic services

    The kernel already has ten execution ceilings. Cumulative boundary payload
    is an eleventh, DIFFERENT measure: TheoryCore supplies no such allocation
    coordinate. Its ceiling therefore meets host and request policy, while the
    ten execution coordinates meet installed, host and request limits.

    Policy fields below are ordered numeric words BEFORE fixed-width encoding
    and hashing. Their injectivity does not assert collision-free hashes or
    prove Rust's integer-to-byte implementation. Restoration is a parameter
    applied to the exact owner's image, never an independent image argument.
    The factory relation requires successful incremental setup accounting and
    existing sealed-handle authorization before a restored bundle is admitted.
    This proves the factory contract, not arbitrary restorer correctness or a
    physical allocation bound. Runtime source tests establish the concrete
    flat-image schedule and policy encoding correspondence. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Strings.String Lia.
From RuntimeGrammar Require Import InstalledFltJudgments InstalledLanguageAuthority.
Import ListNotations.

Module InstalledSemanticService.
Module J := InstalledFltJudgments.InstalledFltJudgments.

(** Allocation-free exact name selection refines the existing dense-coordinate
    selection, without interpreting a name as authority. The installed source
    has unique names and the compiler preserves its action roster order. This
    tail-recursive cursor requires neither sorted names nor parser inference. *)
Fixpoint find_name_from (names : list string) (requested : string) (offset : nat)
    : option nat :=
  match names with
  | [] => None
  | name :: rest =>
      if String.eqb name requested then Some offset
      else find_name_from rest requested (S offset)
  end.

Theorem exact_name_selection_retains_the_source_coordinate :
  forall names requested offset selected,
    find_name_from names requested offset = Some selected ->
    exists local, selected = offset + local /\
      nth_error names local = Some requested.
Proof.
  induction names as [|name rest IH]; intros requested offset selected H; cbn in H.
  - discriminate.
  - destruct (String.eqb name requested) eqn:E.
    + apply String.eqb_eq in E. inversion H; subst.
      exists 0; split; [lia | reflexivity].
    + specialize (IH requested (S offset) selected H).
      destruct IH as [local [Hindex Hname]].
      exists (S local); split; [lia | exact Hname].
Qed.

Corollary exact_name_selection_refines_zero_based_rosters :
  forall names requested selected,
    find_name_from names requested 0 = Some selected ->
    nth_error names selected = Some requested.
Proof.
  intros names requested selected H.
  apply exact_name_selection_retains_the_source_coordinate in H.
  destruct H as [local [Hindex Hname]]. cbn in Hindex. now subst selected.
Qed.

Record ExecutionLimits := execution_limits {
  work : nat; normalization_steps : nat; outputs : nat; frontier : nat;
  proofs : nat; proof_nodes : nat; term_nodes : nat; term_bytes : nat;
  output_nodes : nat; output_bytes : nat
}.

Definition coordinate (limits : ExecutionLimits) (dimension : J.Dimension) :=
  match dimension with
  | J.LogicalWork => work limits
  | J.NormalizationSteps => normalization_steps limits
  | J.OutputCount => outputs limits
  | J.FrontierCount => frontier limits
  | J.ProofCount => proofs limits
  | J.ProofNodes => proof_nodes limits
  | J.InputNodes => term_nodes limits
  | J.InputBytes => term_bytes limits
  | J.OutputNodes => output_nodes limits
  | J.OutputAtoms => output_bytes limits
  end.

Definition execution_meet a b := execution_limits
  (Nat.min (work a) (work b))
  (Nat.min (normalization_steps a) (normalization_steps b))
  (Nat.min (outputs a) (outputs b)) (Nat.min (frontier a) (frontier b))
  (Nat.min (proofs a) (proofs b)) (Nat.min (proof_nodes a) (proof_nodes b))
  (Nat.min (term_nodes a) (term_nodes b)) (Nat.min (term_bytes a) (term_bytes b))
  (Nat.min (output_nodes a) (output_nodes b)) (Nat.min (output_bytes a) (output_bytes b)).

Record ServiceLimits := service_limits {
  execution : ExecutionLimits;
  boundary_payload : nat
}.

Definition effective installed host requested := service_limits
  (execution_meet installed (execution_meet (execution host) (execution requested)))
  (Nat.min (boundary_payload host) (boundary_payload requested)).

Theorem concrete_meet_refines_existing_dimensions : forall installed host requested dimension,
  coordinate (execution (effective installed host requested)) dimension =
  J.effective_limits (coordinate installed) (coordinate (execution host))
    (coordinate (execution requested)) dimension.
Proof. intros; destruct dimension; reflexivity. Qed.

Theorem execution_never_amplifies_a_ceiling : forall installed host requested dimension,
  let actual := coordinate (execution (effective installed host requested)) dimension in
  actual <= coordinate installed dimension /\
  actual <= coordinate (execution host) dimension /\
  actual <= coordinate (execution requested) dimension.
Proof.
  intros installed host requested dimension; cbv zeta.
  rewrite concrete_meet_refines_existing_dimensions.
  apply J.effective_limits_cannot_amplify_any_ceiling.
Qed.

Theorem boundary_payload_is_separate_and_attenuated : forall installed host requested,
  boundary_payload (effective installed host requested) <= boundary_payload host /\
  boundary_payload (effective installed host requested) <= boundary_payload requested.
Proof. intros; split; [apply Nat.le_min_l | apply Nat.le_min_r]. Qed.

(** A wire header may spend payload before the requested attenuation is known.
    Resume under the meet by subtracting that spent prefix, never by granting
    a fresh allowance. Checked subtraction refuses an already overdrawn prefix. *)
Definition resume_payload host requested spent :=
  let ceiling := Nat.min host requested in
  if Nat.leb spent ceiling then Some (ceiling - spent) else None.

Theorem resumed_payload_keeps_the_spent_prefix : forall host requested spent remaining,
  resume_payload host requested spent = Some remaining ->
  spent + remaining = Nat.min host requested /\
  spent <= host /\ spent <= requested.
Proof.
  intros host requested spent remaining H. unfold resume_payload in H.
  destruct (Nat.leb spent (Nat.min host requested)) eqn:E; try discriminate.
  apply Nat.leb_le in E. inversion H; subst.
  pose proof (Nat.le_min_l host requested).
  pose proof (Nat.le_min_r host requested). lia.
Qed.

Theorem overdrawn_payload_is_not_replenished : forall host requested spent,
  Nat.min host requested < spent -> resume_payload host requested spent = None.
Proof.
  intros host requested spent H. unfold resume_payload.
  assert (E : Nat.leb spent (Nat.min host requested) = false) by
    (apply Nat.leb_gt; exact H).
  now rewrite E.
Qed.

(** Existing TheoryLimitsV1 projection. These six source fields populate ten
    execution coordinates; no field is reinterpreted as cumulative payload. *)
Definition project_theory steps queue proof_limit terms nodes bytes :=
  execution_limits steps steps queue queue queue proof_limit terms bytes nodes bytes.

Theorem installed_projection_keeps_distinct_size_measures :
  forall steps queue proof_limit terms nodes bytes host requested,
  term_nodes (project_theory steps queue proof_limit terms nodes bytes) = terms /\
  output_nodes (project_theory steps queue proof_limit terms nodes bytes) = nodes /\
  term_bytes (project_theory steps queue proof_limit terms nodes bytes) = bytes /\
  output_bytes (project_theory steps queue proof_limit terms nodes bytes) = bytes /\
  boundary_payload (effective (project_theory steps queue proof_limit terms nodes bytes)
    host requested) = Nat.min (boundary_payload host) (boundary_payload requested).
Proof. intros; repeat split; reflexivity. Qed.

Definition policy_words schedule receipt_schedule limits :=
  let e := execution limits in
  [schedule; work e; normalization_steps e; outputs e; frontier e; proofs e;
   proof_nodes e; term_nodes e; term_bytes e; output_nodes e; output_bytes e;
   boundary_payload limits; receipt_schedule].

Theorem policy_words_retain_every_coordinate : forall version_a version_b receipt_a receipt_b a b,
  policy_words version_a receipt_a a = policy_words version_b receipt_b b ->
  version_a = version_b /\ receipt_a = receipt_b /\ a = b.
Proof.
  intros version_a version_b receipt_a receipt_b [[a0 a1 a2 a3 a4 a5 a6 a7 a8 a9] a10]
    [[b0 b1 b2 b3 b4 b5 b6 b7 b8 b9] b10] H.
  unfold policy_words in H; cbn in H. inversion H. subst; auto.
Qed.

Fixpoint charge_setup ceiling current charges : option nat :=
  match charges with
  | [] => J.charge_work ceiling current 0
  | amount :: rest =>
      match J.charge_work ceiling current amount with
      | None => None
      | Some next => charge_setup ceiling next rest
      end
  end.

Theorem successful_setup_keeps_prefix_and_total : forall charges ceiling current final,
  charge_setup ceiling current charges = Some final ->
  final = current + fold_right Nat.add 0 charges /\ final <= ceiling.
Proof.
  induction charges as [|amount rest IH]; intros ceiling current final H; cbn in H.
  - apply J.successful_charge_preserves_prefix_and_ceiling in H; cbn; lia.
  - destruct (J.charge_work ceiling current amount) as [next|] eqn:E; try discriminate.
    apply J.successful_charge_preserves_prefix_and_ceiling in E.
    specialize (IH ceiling next final H). cbn; lia.
Qed.

Section Factory.
  Context {Owner Image Matcher : Type}.
  Variable owner_image : Owner -> Image.
  Variable owner_commitment : Owner -> Commitment.
  Variable restore : Image -> option Matcher.
  Variable setup_plan : Owner -> list nat.

  Record Bundle := bundle { installed_owner : Owner; installed_matcher : Matcher }.

  Inductive Restores (entry : InstalledEntry) (handle : InstalledHandle)
      (selection : J.Selection) (owner : Owner) (ceiling current : nat)
      : Bundle -> nat -> Prop :=
  | RestoreAdmitted : forall matcher final,
      authorize_all entry handle (J.required_rights selection) ->
      owner_commitment owner = handle_commitment handle ->
      charge_setup ceiling current (setup_plan owner) = Some final ->
      restore (owner_image owner) = Some matcher ->
      Restores entry handle selection owner ceiling current (bundle owner matcher) final.

  Theorem restored_bundle_has_one_owner_and_the_precharged_matcher :
    forall entry handle selection owner ceiling current prepared final,
      Restores entry handle selection owner ceiling current prepared final ->
      installed_owner prepared = owner /\
      restore (owner_image (installed_owner prepared)) = Some (installed_matcher prepared) /\
      authorize_all entry handle (J.required_rights selection) /\
      owner_commitment owner = handle_commitment handle /\
      final = current + fold_right Nat.add 0 (setup_plan owner) /\ final <= ceiling.
  Proof.
    intros entry handle selection owner ceiling current prepared final H.
    destruct H. cbn. apply successful_setup_keeps_prefix_and_total in H1. tauto.
  Qed.

  Theorem exhausted_setup_cannot_admit_a_bundle :
    forall entry handle selection owner ceiling current prepared final,
      charge_setup ceiling current (setup_plan owner) = None ->
      ~ Restores entry handle selection owner ceiling current prepared final.
  Proof. intros entry handle selection owner ceiling current prepared final Hstop H.
    inversion H; subst. congruence. Qed.

  Theorem missing_action_authority_cannot_admit_a_bundle :
    forall entry handle selection owner ceiling current prepared final,
      ~ authorize_all entry handle (J.required_rights selection) ->
      ~ Restores entry handle selection owner ceiling current prepared final.
  Proof. intros entry handle selection owner ceiling current prepared final Hstop H.
    inversion H; subst. contradiction. Qed.
End Factory.

End InstalledSemanticService.

Print Assumptions InstalledSemanticService.concrete_meet_refines_existing_dimensions.
Print Assumptions InstalledSemanticService.execution_never_amplifies_a_ceiling.
Print Assumptions InstalledSemanticService.boundary_payload_is_separate_and_attenuated.
Print Assumptions InstalledSemanticService.resumed_payload_keeps_the_spent_prefix.
Print Assumptions InstalledSemanticService.overdrawn_payload_is_not_replenished.
Print Assumptions InstalledSemanticService.installed_projection_keeps_distinct_size_measures.
Print Assumptions InstalledSemanticService.policy_words_retain_every_coordinate.
Print Assumptions InstalledSemanticService.successful_setup_keeps_prefix_and_total.
Print Assumptions InstalledSemanticService.restored_bundle_has_one_owner_and_the_precharged_matcher.
Print Assumptions InstalledSemanticService.exhausted_setup_cannot_admit_a_bundle.
Print Assumptions InstalledSemanticService.missing_action_authority_cannot_admit_a_bundle.
Print Assumptions InstalledSemanticService.exact_name_selection_retains_the_source_coordinate.
Print Assumptions InstalledSemanticService.exact_name_selection_refines_zero_based_rosters.
