(** Answer certificates for the existing raw Map dialogue.

    A reference event's answer is justified by its existing PairProtocol,
    not by the surrounding Map's final comparison. The event annotation
    theorem supplies every protocol, and the requested-answer projection
    retains its original operands. After erasing admitted-operand metadata,
    each answer still names successfully projected original terms and their
    exact key comparison. This is the premise needed for the lower-height
    child proof, including comparisons within a single sorting roster.
    No runtime key, parser, callback engine or fallback answer is added. *)
From Stdlib Require Import List.
From RhoBridge Require Import GeneratedAdmittedMapReference
  GeneratedConstructorComparisonClasses GeneratedMapCoreSource GeneratedMapCoreErasure
  NativeMapRunSuspension CollectionPairAndUnitLexResults.
Import ListNotations.
Import GeneratedAdmittedMapReference.GeneratedAdmittedMapReference.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import GeneratedMapCoreErasure.GeneratedMapCoreErasure.
Import NativeMapRunSuspension.NativeMapRunSuspension.
Import CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.

Module GeneratedAdmittedMapDialogue.
Section ReferenceAnswers.
Context {Key Value : Type}.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.

Definition faithful_answer (answer : @RawRequest Key Value * comparison) : Prop :=
  match fst answer with
  | PrimaryRequest lhs rhs => key_compare lhs rhs = snd answer
  | SecondaryRequest lhs rhs => value_compare lhs rhs = snd answer
  end.

Theorem existing_pair_protocol_justifies_every_raw_answer :
  forall left right answers result,
  PairProtocol key_compare value_compare key_alias value_alias left right answers result ->
  Forall faithful_answer (requested_answers left right answers).
Proof.
  intros left right answers result PAIR.
  pose proof (existing_pair_protocol_certifies_every_pending_answer
    key_compare value_compare key_alias value_alias left right answers result PAIR) as ALL.
  apply Forall_forall. intros answer MEMBER.
  unfold requested_answers in MEMBER. apply in_map_iff in MEMBER.
  destruct MEMBER as [[role response] [ERASE MEMBER]]. subst answer.
  rewrite Forall_forall in ALL. specialize (ALL _ MEMBER).
  destruct ALL as [PENDING RESPONSE]. destruct role; exact RESPONSE.
Qed.

Theorem certified_event_body_justifies_every_raw_answer : forall events,
  Forall (native_body_event_law key_compare value_compare key_alias value_alias) events ->
  Forall faithful_answer (event_requested_answers events).
Proof.
  intros events CERTIFIED. induction CERTIFIED as [|event rest HEAD TAIL IH].
  - constructor.
  - destruct event; cbn [event_requested_answers flat_map] in *; try exact IH.
    destruct HEAD as [FOCUS [result PAIR]]. apply Forall_app. split; [|exact IH].
    eapply existing_pair_protocol_justifies_every_raw_answer. exact PAIR.
Qed.

Theorem complete_native_events_justify_every_raw_answer :
  (forall lhs rhs, key_alias lhs rhs = true -> key_compare lhs rhs = Eq) ->
  (forall lhs rhs, value_alias lhs rhs = true -> value_compare lhs rhs = Eq) ->
  forall maximum left right left_output right_output result events,
  MapEvents key_compare value_compare key_alias value_alias
    maximum left right left_output right_output result events ->
  Forall faithful_answer (event_requested_answers events).
Proof.
  intros KEY_SOUND VALUE_SOUND maximum left right left_output right_output result events EVENTS.
  destruct (complete_spine_has_one_terminal_after_its_certified_body
    key_compare value_compare key_alias value_alias
    KEY_SOUND VALUE_SOUND
    maximum left right left_output right_output result events EVENTS)
    as [body [SPINE [CERTIFIED EDGES]]].
  rewrite SPINE, event_requested_answers_append. cbn [event_requested_answers flat_map].
  rewrite app_nil_r. now apply certified_event_body_justifies_every_raw_answer.
Qed.
End ReferenceAnswers.

Section OriginalAnswers.
Context {KeyTerm ValueTerm : Type}.
Variable key_order value_order : Ordered.
Variable key_project : KeyTerm -> option (carrier key_order).
Variable value_project : ValueTerm -> option (carrier value_order).
Local Notation Key := (AdmittedOperand key_order key_project).
Local Notation Value := (AdmittedOperand value_order value_project).

Definition original_answer_has_projected_operands
    (answer : @RawRequest KeyTerm ValueTerm * comparison) : Prop :=
  match fst answer with
  | PrimaryRequest lhs rhs => exists left_key right_key,
      key_project lhs = Some left_key /\ key_project rhs = Some right_key /\
      comparison_function key_order left_key right_key = snd answer
  | SecondaryRequest lhs rhs => exists left_key right_key,
      value_project lhs = Some left_key /\ value_project rhs = Some right_key /\
      comparison_function value_order left_key right_key = snd answer
  end.

Theorem erasing_an_admitted_answer_retains_its_original_projection_evidence :
  forall answer : @RawRequest Key Value * comparison,
  faithful_answer (admitted_compare key_project) (admitted_compare value_project) answer ->
  original_answer_has_projected_operands
    (erase_request original_operand original_operand (fst answer), snd answer).
Proof.
  intros [[left right|left right] response] FAITHFUL;
    (cbn [original_answer_has_projected_operands erase_request fst snd];
    exists (operand_key left), (operand_key right);
    split; [apply operand_projection|];
    split; [apply operand_projection|exact FAITHFUL]).
Qed.

(** Compose the already certified native event spine with complete raw-control
    erasure. The result runs on the original terms. Every supplied answer
    retains successful original projection evidence; a later child traversal
    must establish that answer rather than assuming the final Map result. *)
Theorem admitted_map_reference_runs_on_original_operands_with_certified_answers :
  forall (key_alias : KeyTerm -> KeyTerm -> bool)
    (value_alias : ValueTerm -> ValueTerm -> bool),
  (forall lhs rhs, key_alias lhs rhs = true -> lhs = rhs) ->
  (forall lhs rhs, value_alias lhs rhs = true -> lhs = rhs) ->
  forall maximum (left right : list (Key * Value)) left_canonical right_canonical,
  length left <= maximum -> length right <= maximum ->
  canonical_result (pair_order key_order value_order)
    (map (admitted_pair_key key_order value_order key_project value_project) left) = Some left_canonical ->
  canonical_result (pair_order key_order value_order)
    (map (admitted_pair_key key_order value_order key_project value_project) right) = Some right_canonical ->
  exists answers final,
    @RawDialogue KeyTerm ValueTerm key_alias value_alias maximum
      (Ingress None)
      (initial_map maximum
        (map (erase_entry original_operand original_operand) left)
        (map (erase_entry original_operand original_operand) right)
        (length left) (length right)) answers
      (ReturnReply (Completes (list_compare
        (comparison_function (pair_order key_order value_order)) left_canonical right_canonical))) final /\
    Forall original_answer_has_projected_operands answers.
Proof.
  intros key_alias value_alias KEY_IDENTITY VALUE_IDENTITY maximum left right
    left_canonical right_canonical WIDTH_LEFT WIDTH_RIGHT CANONICAL_LEFT CANONICAL_RIGHT.
  let key_alias_ref := constr:(fun lhs rhs : Key =>
    key_alias (original_operand lhs) (original_operand rhs)) in
  let value_alias_ref := constr:(fun lhs rhs : Value =>
    value_alias (original_operand lhs) (original_operand rhs)) in
  set (ka := key_alias_ref); set (va := value_alias_ref).
  assert (KEY_SOUND : forall lhs rhs, ka lhs rhs = true ->
    admitted_compare key_project lhs rhs = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact KEY_IDENTITY. }
  assert (VALUE_SOUND : forall lhs rhs, va lhs rhs = true ->
    admitted_compare value_project lhs rhs = Eq).
  { apply original_alias_is_sound_on_the_admitted_reference. exact VALUE_IDENTITY. }
  destruct (admitted_originals_construct_the_existing_native_map_events
    key_order value_order key_project value_project key_alias value_alias
    KEY_IDENTITY VALUE_IDENTITY maximum left right WIDTH_LEFT WIDTH_RIGHT)
    as [lo [ro [result [events [COMPLETE EVENTS]]]]].
  pose proof (completed_admitted_map_returns_the_source_canonical_comparison
    key_order value_order key_project value_project key_alias value_alias
    KEY_IDENTITY VALUE_IDENTITY maximum left right lo ro result left_canonical right_canonical
    WIDTH_LEFT WIDTH_RIGHT COMPLETE CANONICAL_LEFT CANONICAL_RIGHT) as RESULT.
  assert (CERTIFIED : Forall
    (faithful_answer (admitted_compare key_project) (admitted_compare value_project))
    (event_requested_answers events)).
  { eapply complete_native_events_justify_every_raw_answer;
      [exact KEY_SOUND|exact VALUE_SOUND|exact EVENTS]. }
  destruct (bounded_native_map_events_construct_the_complete_raw_dialogue
    ka va maximum (admitted_compare key_project) (admitted_compare value_project)
    KEY_SOUND VALUE_SOUND left right lo ro result events WIDTH_LEFT WIDTH_RIGHT EVENTS)
    as [last DIALOGUE].
  pose proof (actual_raw_dialogue_erasure original_operand original_operand
    ka va key_alias value_alias (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    maximum _ _ _ _ _ DIALOGUE) as ORIGINAL.
  cbn [erase_control erase_reply] in ORIGINAL.
  rewrite initial_map_erasure in ORIGINAL. rewrite RESULT in ORIGINAL.
  eexists. eexists. split; [exact ORIGINAL|].
  apply Forall_forall. intros answer MEMBER. apply in_map_iff in MEMBER.
  destruct MEMBER as [annotated [ERASE MEMBER]]. subst answer.
  apply erasing_an_admitted_answer_retains_its_original_projection_evidence.
  rewrite Forall_forall in CERTIFIED. exact (CERTIFIED _ MEMBER).
Qed.

Theorem successful_original_map_projections_construct_a_certified_raw_dialogue :
  forall (key_alias : KeyTerm -> KeyTerm -> bool)
    (value_alias : ValueTerm -> ValueTerm -> bool),
  (forall lhs rhs, key_alias lhs rhs = true -> lhs = rhs) ->
  (forall lhs rhs, value_alias lhs rhs = true -> lhs = rhs) ->
  forall maximum left right left_keys right_keys left_canonical right_canonical,
  length left <= maximum -> length right <= maximum ->
  Forall2 (fun original key =>
    key_project (fst original) = Some (fst key) /\
    value_project (snd original) = Some (snd key)) left left_keys ->
  Forall2 (fun original key =>
    key_project (fst original) = Some (fst key) /\
    value_project (snd original) = Some (snd key)) right right_keys ->
  canonical_result (pair_order key_order value_order) left_keys = Some left_canonical ->
  canonical_result (pair_order key_order value_order) right_keys = Some right_canonical ->
  exists answers final,
    @RawDialogue KeyTerm ValueTerm key_alias value_alias maximum (Ingress None)
      (initial_map maximum left right (length left) (length right)) answers
      (ReturnReply (Completes (list_compare
        (comparison_function (pair_order key_order value_order)) left_canonical right_canonical))) final /\
    Forall original_answer_has_projected_operands answers.
Proof.
  intros key_alias value_alias KEY_IDENTITY VALUE_IDENTITY maximum left right
    left_keys right_keys left_canonical right_canonical WIDTH_LEFT WIDTH_RIGHT
    PROJECT_LEFT PROJECT_RIGHT CANONICAL_LEFT CANONICAL_RIGHT.
  destruct (successful_paired_projection_constructs_exact_admitted_originals
    key_order value_order key_project value_project left left_keys PROJECT_LEFT)
    as [admitted_left [LEFT_ORIGINAL LEFT_KEYS]].
  destruct (successful_paired_projection_constructs_exact_admitted_originals
    key_order value_order key_project value_project right right_keys PROJECT_RIGHT)
    as [admitted_right [RIGHT_ORIGINAL RIGHT_KEYS]].
  pose proof (f_equal (@length _) LEFT_ORIGINAL) as LEFT_LENGTH.
  pose proof (f_equal (@length _) RIGHT_ORIGINAL) as RIGHT_LENGTH.
  rewrite length_map in LEFT_LENGTH, RIGHT_LENGTH.
  assert (LEFT_BOUND : length admitted_left <= maximum) by now rewrite LEFT_LENGTH.
  assert (RIGHT_BOUND : length admitted_right <= maximum) by now rewrite RIGHT_LENGTH.
  rewrite <- LEFT_KEYS in CANONICAL_LEFT. rewrite <- RIGHT_KEYS in CANONICAL_RIGHT.
  destruct (admitted_map_reference_runs_on_original_operands_with_certified_answers
    key_alias value_alias KEY_IDENTITY VALUE_IDENTITY maximum admitted_left admitted_right
    left_canonical right_canonical LEFT_BOUND RIGHT_BOUND CANONICAL_LEFT CANONICAL_RIGHT)
    as [answers [final [DIALOGUE CERTIFIED]]].
  change (map (erase_entry original_operand original_operand) admitted_left = left) in LEFT_ORIGINAL.
  change (map (erase_entry original_operand original_operand) admitted_right = right) in RIGHT_ORIGINAL.
  rewrite LEFT_ORIGINAL, RIGHT_ORIGINAL, LEFT_LENGTH, RIGHT_LENGTH in DIALOGUE.
  exists answers, final. split; assumption.
Qed.
End OriginalAnswers.
End GeneratedAdmittedMapDialogue.

Print Assumptions GeneratedAdmittedMapDialogue.existing_pair_protocol_justifies_every_raw_answer.
Print Assumptions GeneratedAdmittedMapDialogue.certified_event_body_justifies_every_raw_answer.
Print Assumptions GeneratedAdmittedMapDialogue.complete_native_events_justify_every_raw_answer.
Print Assumptions GeneratedAdmittedMapDialogue.erasing_an_admitted_answer_retains_its_original_projection_evidence.
Print Assumptions GeneratedAdmittedMapDialogue.admitted_map_reference_runs_on_original_operands_with_certified_answers.
Print Assumptions GeneratedAdmittedMapDialogue.successful_original_map_projections_construct_a_certified_raw_dialogue.
