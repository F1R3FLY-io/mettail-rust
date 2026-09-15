(** Concrete Bag use of the existing shared collection core.
    The generated factory compares original stored totals, builds both original
    key/count rosters and calls the same from_parts initializer. Source sites:
    iterative_cmp.rs725-750,772-793 and collection_cmp_pda.rs159-165,309-328,
    378-416. The callback at iterative_cmp.rs1764-1815 pushes the SAME box's
    Resume task before the original typed primary pair. Valid immutable borrows
    and faithful pointer casts remain source-association obligations.

    Empty_set represents the secondary field that this actual factory sets to
    None. Its elimination alone is not a proof about arbitrary native entries:
    the field projection and successful original-roster initializer equations
    below provide the factory connection. Counts, stored-total lead, requested
    operands and supplied answers are not normalized or recomputed. These laws
    do not prove native work coverage, termination or a canonical Bag result. *)
From Stdlib Require Import List Arith.PeanoNat.
From RhoBridge Require Import GeneratedBagComparisonInitialization
  AdmittedCollectionComparisonOwnership GeneratedMapCoreSource GeneratedMapCoreErasure.
Import ListNotations.
Import GeneratedBagComparisonInitialization.GeneratedBagComparisonInitialization.
Import AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import GeneratedMapCoreErasure.GeneratedMapCoreErasure.

Module GeneratedBagCoreSource.
Definition empty_operand {Operand : Type} (impossible : Empty_set) : Operand :=
  match impossible with end.
Definition absent_alias (impossible other : Empty_set) : bool :=
  match impossible with end.

Section OriginalBag.
Context {Key : Type}.
Definition entry_pair (entry : @Entry Key Empty_set) : Key * nat :=
  (primary entry, repetitions entry).

Theorem original_repeated_item_has_the_exact_bag_fields : forall original,
  entry_pair (repeated_entry original) = original /\
  secondary (@repeated_entry Key Empty_set original) = None.
Proof. intros [key count]. split; reflexivity. Qed.

Theorem repeated_roster_projects_to_original_pairs : forall originals,
  map entry_pair (map repeated_entry originals) = originals.
Proof.
  induction originals as [|[key count] rest IH].
  - reflexivity.
  - change ((key, count) :: map entry_pair (map repeated_entry rest) =
      (key, count) :: rest). now rewrite IH.
Qed.

Theorem successful_bag_factory_has_the_original_complete_initial_state :
  forall maximum stored_left stored_right left_source right_source left_roster right_roster,
  append_repeated maximum left_source (empty_roster (length left_source)) = Built left_roster ->
  append_repeated maximum right_source (empty_roster (length right_source)) = Built right_roster ->
  initial_collection maximum (map entry_pair (entries left_roster))
    (map entry_pair (entries right_roster)) (Nat.compare stored_left stored_right)
    (running_total left_roster) (running_total right_roster) =
  initial_collection maximum left_source right_source (Nat.compare stored_left stored_right)
    (source_count left_source) (source_count right_source).
Proof.
  intros maximum stored_left stored_right left_source right_source left_roster right_roster LEFT RIGHT.
  pose proof (@successful_repeated_rosters_supply_identical_constructor_arguments
    Key Empty_set (@RawMapState Key nat)
    (fun lead left right left_total right_total => initial_collection maximum
      (map entry_pair left) (map entry_pair right) lead left_total right_total)
    maximum (Nat.compare stored_left stored_right) left_source right_source
    left_roster right_roster LEFT RIGHT) as INITIAL.
  cbn beta in INITIAL.
  rewrite !repeated_roster_projects_to_original_pairs,
    !repeated_entries_have_the_original_sum in INITIAL. exact INITIAL.
Qed.

Variable alias : Key -> Key -> bool.
Variable maximum : nat.
Local Notation BagResume := (@RawPayloadResume Key nat Empty_set
  (fun _ => None) (fun count => count) alias absent_alias maximum).

(** The callback result carries exactly the original requested pair, mapped
    only by the explicitly supplied faithful native operand representation. *)
Theorem an_actual_bag_request_restores_its_original_primary_pair :
  forall (NativeKey : Type) (erase_key : Key -> NativeKey) state input request next,
  BagResume state input (Requests request) next ->
  exists lhs rhs, request = PrimaryRequest lhs rhs /\
    erase_request erase_key (@empty_operand NativeKey) request =
      PrimaryRequest (erase_key lhs) (erase_key rhs).
Proof.
  intros NativeKey erase_key state input [lhs rhs|impossible rhs] next RESUME.
  - exists lhs, rhs. split; reflexivity.
  - destruct impossible.
Qed.

Section OperandTransport.
Context {NativeKey : Type}.
Variable erase_key : Key -> NativeKey.
Variable native_alias : NativeKey -> NativeKey -> bool.
Hypothesis alias_compatible : forall lhs rhs,
  native_alias (erase_key lhs) (erase_key rhs) = alias lhs rhs.

Theorem actual_bag_dialogue_retains_counts_and_original_callback_answers :
  forall control state answers last next,
  @RawPayloadDialogue Key nat Empty_set (fun _ => None) (fun count => count)
    alias absent_alias maximum control state answers last next ->
  @RawPayloadDialogue NativeKey nat NativeKey (fun _ => None) (fun count => count)
    native_alias native_alias maximum
    (erase_payload_control erase_key (fun count => count) (@empty_operand NativeKey) control)
    (erase_map erase_key (fun count => count) state)
    (map (erase_payload_answer erase_key (@empty_operand NativeKey)) answers)
    (erase_payload_control erase_key (fun count => count) (@empty_operand NativeKey) last)
    (erase_map erase_key (fun count => count) next).
Proof.
  intros. eapply (@actual_payload_dialogue_erasure Key nat Empty_set NativeKey nat NativeKey
    erase_key (fun count => count) (@empty_operand NativeKey)
    (fun _ => None) (fun count => count) (fun _ => None) (fun count => count)
    alias absent_alias native_alias native_alias); try reflexivity; try eassumption.
  intros impossible other. destruct impossible.
Qed.
End OperandTransport.
End OriginalBag.
End GeneratedBagCoreSource.

Print Assumptions GeneratedBagCoreSource.original_repeated_item_has_the_exact_bag_fields.
Print Assumptions GeneratedBagCoreSource.repeated_roster_projects_to_original_pairs.
Print Assumptions GeneratedBagCoreSource.successful_bag_factory_has_the_original_complete_initial_state.
Print Assumptions GeneratedBagCoreSource.an_actual_bag_request_restores_its_original_primary_pair.
Print Assumptions GeneratedBagCoreSource.actual_bag_dialogue_retains_counts_and_original_callback_answers.
