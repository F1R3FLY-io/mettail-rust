(** Successful child projections give a total reference comparison ONLY on
    their admitted original operands. An admitted operand retains its original
    term, comparison key and the equation connecting them. This is proof
    metadata, not a runtime representation or a replacement term comparator.

    The paired-roster theorem constructs these witnesses from existing
    position-preserving projection evidence. Erasing them returns the exact
    original roster, including duplicates and its original order. In
    particular, rejected terms never receive fabricated comparison keys.
    The final theorem reuses the existing native Map completion and event
    construction; it introduces neither another sorter nor a result oracle. *)
From Stdlib Require Import List.
From RuntimeGrammar Require Import SemanticComparisonLaws.
From RhoBridge Require Import GeneratedConstructorComparisonClasses
  NativeMapRunSuspension NativeSortedComparisonClasses MergeSortPdaNativeOuter.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import NativeMapRunSuspension.NativeMapRunSuspension.

Module GeneratedAdmittedMapReference.

Record AdmittedOperand {Term : Type} (order : Ordered)
    (project : Term -> option (carrier order)) := {
  original_operand : Term;
  operand_key : carrier order;
  operand_projection : project original_operand = Some operand_key
}.
Arguments original_operand {Term order project} _.
Arguments operand_key {Term order project} _.
Arguments operand_projection {Term order project} _.

Section Operand.
Context {Term : Type} {order : Ordered}.
Variable project : Term -> option (carrier order).

Theorem admitted_original_keeps_its_successful_projection :
  forall operand : AdmittedOperand order project,
  project (original_operand operand) = Some (operand_key operand).
Proof. exact operand_projection. Qed.

Theorem same_original_has_the_same_admitted_key :
  forall left right : AdmittedOperand order project,
  original_operand left = original_operand right ->
  operand_key left = operand_key right.
Proof.
  intros left right ORIGINAL.
  pose proof (operand_projection left) as LEFT.
  pose proof (operand_projection right) as RIGHT.
  rewrite ORIGINAL in LEFT. rewrite RIGHT in LEFT. now injection LEFT.
Qed.

Definition admitted_compare (left right : AdmittedOperand order project) :=
  comparison_function order (operand_key left) (operand_key right).

Theorem original_alias_is_sound_on_the_admitted_reference :
  forall alias : Term -> Term -> bool,
  (forall left right, alias left right = true -> left = right) ->
  forall left right : AdmittedOperand order project,
  alias (original_operand left) (original_operand right) = true ->
  admitted_compare left right = Eq.
Proof.
  intros alias SOUND left right ALIAS. unfold admitted_compare.
  rewrite (same_original_has_the_same_admitted_key left right (SOUND _ _ ALIAS)).
  apply (proj2 (SemanticComparisonLaws.SemanticComparisonLaws.comparison_eq
    (comparison_laws order) _ _)). reflexivity.
Qed.
End Operand.

Theorem list_comparison_commutes_with_a_faithful_view :
  forall (Source Target : Type) (view : Source -> Target)
    (source_compare : Source -> Source -> comparison)
    (target_compare : Target -> Target -> comparison),
  (forall left right, source_compare left right = target_compare (view left) (view right)) ->
  forall left right,
  list_compare source_compare left right =
    list_compare target_compare (map view left) (map view right).
Proof.
  intros Source Target view source_compare target_compare FAITHFUL left.
  induction left as [|head tail IH]; intros [|other rest];
    cbn [map list_compare]; try reflexivity.
  rewrite FAITHFUL. destruct (target_compare (view head) (view other));
    [apply IH|reflexivity|reflexivity].
Qed.

Section PairedRoster.
Context {KeyTerm ValueTerm : Type}.
Variable key_order value_order : Ordered.
Variable key_project : KeyTerm -> option (carrier key_order).
Variable value_project : ValueTerm -> option (carrier value_order).
Local Notation Key := (AdmittedOperand key_order key_project).
Local Notation Value := (AdmittedOperand value_order value_project).

Definition erase_pair (entry : Key * Value) :=
  (original_operand (fst entry), original_operand (snd entry)).
Definition admitted_pair_key (entry : Key * Value) :=
  (operand_key (fst entry), operand_key (snd entry)).

Theorem successful_paired_projection_constructs_exact_admitted_originals :
  forall originals keys,
  Forall2 (fun original key =>
    key_project (fst original) = Some (fst key) /\
    value_project (snd original) = Some (snd key)) originals keys ->
  exists admitted : list (Key * Value),
    map erase_pair admitted = originals /\ map admitted_pair_key admitted = keys.
Proof.
  intros originals keys PAIRED.
  induction PAIRED as [|[original_key original_value] [key value] originals keys
    [KEY VALUE] REST [admitted [ORIGINALS KEYS]]].
  - exists []. split; reflexivity.
  - cbn in KEY, VALUE.
    exists (({| original_operand := original_key; operand_key := key;
                operand_projection := KEY |},
             {| original_operand := original_value; operand_key := value;
                operand_projection := VALUE |}) :: admitted).
    cbn [map erase_pair admitted_pair_key original_operand operand_key].
    split; [now rewrite ORIGINALS|now rewrite KEYS].
Qed.

Variable key_alias : KeyTerm -> KeyTerm -> bool.
Variable value_alias : ValueTerm -> ValueTerm -> bool.

Definition admitted_key_alias (left right : Key) :=
  key_alias (original_operand left) (original_operand right).
Definition admitted_value_alias (left right : Value) :=
  value_alias (original_operand left) (original_operand right).

Theorem admitted_originals_construct_the_existing_native_map_events :
  (forall left right, key_alias left right = true -> left = right) ->
  (forall left right, value_alias left right = true -> left = right) ->
  forall maximum (left right : list (Key * Value)),
  length left <= maximum -> length right <= maximum ->
  exists left_output right_output result events,
    MapNativeCompletion (admitted_compare key_project) (admitted_compare value_project)
      admitted_key_alias admitted_value_alias
      maximum left right left_output right_output result /\
    MapEvents (admitted_compare key_project) (admitted_compare value_project)
      admitted_key_alias admitted_value_alias
      maximum left right left_output right_output result events.
Proof.
  intros KEY_ALIAS VALUE_ALIAS maximum left right LEFT RIGHT.
  assert (KEY_SOUND : forall x y, admitted_key_alias x y = true ->
      admitted_compare key_project x y = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact KEY_ALIAS. }
  assert (VALUE_SOUND : forall x y, admitted_value_alias x y = true ->
      admitted_compare value_project x y = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact VALUE_ALIAS. }
  destruct (original_pair_responses_construct_the_complete_map_phase_witness
    (admitted_compare key_project) (admitted_compare value_project)
    admitted_key_alias admitted_value_alias KEY_SOUND VALUE_SOUND
    maximum left right LEFT RIGHT) as [lo [ro [result COMPLETE]]].
  destruct (every_native_map_completion_constructs_its_resume_spine
    (admitted_compare key_project) (admitted_compare value_project)
    admitted_key_alias admitted_value_alias KEY_SOUND VALUE_SOUND
    maximum left right lo ro result COMPLETE) as [events EVENTS].
  exists lo, ro, result, events. split; assumption.
Qed.

(** Keys are canonicalized by the existing merge sort, not by a new oracle.
    Its sorted-permutation theorem and native sorted-class uniqueness connect
    actual native outputs to the successful source projection's canonical
    roster. Antisymmetry is used only for keys, never for original terms. *)
Local Notation PairCompare :=
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare
    (admitted_compare key_project) (admitted_compare value_project)).
Local Notation KeyCompare := (comparison_function (pair_order key_order value_order)).
Local Notation NativeCompare :=
  (fun (left right : Key * Value) (_ : unit) => (Some (PairCompare left right), tt)).

Theorem admitted_native_output_is_the_source_canonical_key_roster :
  forall maximum count input output scratch canonical,
  length input <= maximum ->
  MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.NativeOuterExecution
    NativeCompare maximum count 1 input None tt output scratch tt ->
  canonical_result (pair_order key_order value_order)
    (map admitted_pair_key input) = Some canonical ->
  map admitted_pair_key output = canonical.
Proof.
  intros maximum count input output scratch canonical WIDTH NATIVE CANONICAL.
  destruct (canonical_result_has_exact_sorted_permutation_evidence
    (pair_order key_order value_order) _ _ CANONICAL) as [SORTED PERMUTATION].
  eapply (NativeSortedComparisonClasses.NativeSortedComparisonClasses.native_output_matches_the_unique_canonical_class_roster
    KeyCompare (comparison_laws (pair_order key_order value_order))
    admitted_pair_key NativeCompare); [|exact WIDTH|exact NATIVE|exact SORTED|exact PERMUTATION].
  intros left right state decision next RESPONSE.
  injection RESPONSE as DECISION STATE. exact DECISION.
Qed.

Theorem completed_admitted_map_returns_the_source_canonical_comparison :
  (forall left right, key_alias left right = true -> left = right) ->
  (forall left right, value_alias left right = true -> left = right) ->
  forall maximum left right left_output right_output result left_canonical right_canonical,
  length left <= maximum -> length right <= maximum ->
  MapNativeCompletion (admitted_compare key_project) (admitted_compare value_project)
    admitted_key_alias admitted_value_alias maximum left right left_output right_output result ->
  canonical_result (pair_order key_order value_order)
    (map admitted_pair_key left) = Some left_canonical ->
  canonical_result (pair_order key_order value_order)
    (map admitted_pair_key right) = Some right_canonical ->
  result = list_compare KeyCompare left_canonical right_canonical.
Proof.
  intros KEY_ALIAS VALUE_ALIAS maximum left right left_output right_output result
    left_canonical right_canonical WIDTH_LEFT WIDTH_RIGHT COMPLETE CANONICAL_LEFT CANONICAL_RIGHT.
  assert (KEY_SOUND : forall x y, admitted_key_alias x y = true ->
      admitted_compare key_project x y = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact KEY_ALIAS. }
  assert (VALUE_SOUND : forall x y, admitted_value_alias x y = true ->
      admitted_compare value_project x y = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact VALUE_ALIAS. }
  pose proof (actual_map_completion_returns_the_sorted_roster_lex_result
    (admitted_compare key_project) (admitted_compare value_project)
    admitted_key_alias admitted_value_alias KEY_SOUND VALUE_SOUND
    maximum left right left_output right_output result COMPLETE) as RESULT.
  destruct COMPLETE as [lc ls rc rs n LEFT RIGHT LEX].
  pose proof (admitted_native_output_is_the_source_canonical_key_roster
    maximum lc left left_output ls left_canonical WIDTH_LEFT LEFT CANONICAL_LEFT) as LEFT_KEYS.
  pose proof (admitted_native_output_is_the_source_canonical_key_roster
    maximum rc right right_output rs right_canonical WIDTH_RIGHT RIGHT CANONICAL_RIGHT) as RIGHT_KEYS.
  rewrite RESULT.
  rewrite (list_comparison_commutes_with_a_faithful_view
    _ _ admitted_pair_key PairCompare KeyCompare (fun _ _ => eq_refl)).
  now rewrite LEFT_KEYS, RIGHT_KEYS.
Qed.
End PairedRoster.
End GeneratedAdmittedMapReference.

Print Assumptions GeneratedAdmittedMapReference.admitted_original_keeps_its_successful_projection.
Print Assumptions GeneratedAdmittedMapReference.same_original_has_the_same_admitted_key.
Print Assumptions GeneratedAdmittedMapReference.original_alias_is_sound_on_the_admitted_reference.
Print Assumptions GeneratedAdmittedMapReference.successful_paired_projection_constructs_exact_admitted_originals.
Print Assumptions GeneratedAdmittedMapReference.admitted_originals_construct_the_existing_native_map_events.
Print Assumptions GeneratedAdmittedMapReference.list_comparison_commutes_with_a_faithful_view.
Print Assumptions GeneratedAdmittedMapReference.admitted_native_output_is_the_source_canonical_key_roster.
Print Assumptions GeneratedAdmittedMapReference.completed_admitted_map_returns_the_source_canonical_comparison.
