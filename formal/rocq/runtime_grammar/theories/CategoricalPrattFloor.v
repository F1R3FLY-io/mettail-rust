(** * Category-indexed Pratt floors for closed delegates and prefix seeds

    A generalized Pratt parser must keep two independent facts about a
    left-attaching, self-delimited term such as a Rholang send:

    - attachment is checked in the left operand's category; and
    - after the term has produced its result, continuation is checked against
      the caller's floor in the result category.

    A bare numeric binding power cannot carry this distinction.  In
    particular, a [Name -> Proc] send completed while parsing the right-hand
    side of a left-associative [Proc] operator must resume at that [Proc]
    floor.  Resetting the floor to zero incorrectly admits another operator
    inside the right-hand side and creates a second association.

    The category parameter of [PrattFloor] is deliberately part of its type.
    Consequently a source-category floor cannot be supplied to a
    result-category continuation without an explicit, separately proved
    transport.

    Prefix dispatch introduces a second obligation.  A grammar rule whose
    first syntactic field is a category may be present in a token bucket even
    when that rule is itself a left-recursive Pratt operator.  Re-entering a
    same-category led rule from such a bucket is unsound even at the root: its
    generic grammar continuation bypasses the operator's right-power descent.
    Led rules therefore belong exclusively to led dispatch, where both powers
    are enforced. In contrast, a genuinely category-changing closed primary
    is admitted as a prefix delegate against its typed attachment floor; the
    caller's result floor governs only what may follow the completed primary. *)

From Stdlib Require Import Arith Bool Lia.
Set Implicit Arguments.

Inductive Category : Type :=
| NameCategory
| ProcCategory
| OtherCategory (identity : nat).

Record PrattFloor (category : Category) : Type := {
  minimum_power : nat
}.

Record InfixOperator (category : Category) : Type := {
  left_power : nat;
  right_power : nat
}.

Record ClosedMixfixOperator
    (attachment_category result_category : Category) : Type := {
  attachment_power : nat
}.

(** The control phase is intentionally independent of the continuation.
    Literal scanning, category-valued operands, captures, repetitions, and
    shared-prefix factoring may change the phase or the number of completed
    operands, but none of them is permitted to manufacture a new caller
    floor. *)
Inductive ClosedPhase : Type :=
| LeadingLiterals
| Operand
| Capture
| Repetition
| FollowingLiterals
| FactoredSpine.

Record ClosedMarker
    (attachment_category result_category : Category) : Type := {
  marker_operator : ClosedMixfixOperator attachment_category result_category;
  completed_operands : nat;
  marker_phase : ClosedPhase;
  result_continuation : PrattFloor result_category
}.

(** A category-changing descent has two independently typed Pratt floors.
    [source_entry_floor] controls operators while the attachment-category
    operand is being recognized.  [target_resume_floor] controls operators
    after that operand has produced a value in the result category.  The two
    floors may have the same numeric representation, but they are not the same
    continuation and must not share one runtime slot. *)
Record DelegatedPrattHandoff
    (attachment_category result_category : Category) : Type := {
  source_entry_floor : PrattFloor attachment_category;
  target_resume_floor : PrattFloor result_category
}.

Definition begin_closed_from_handoff {attachment result}
    (operator : ClosedMixfixOperator attachment result)
    (handoff : DelegatedPrattHandoff attachment result) :
    ClosedMarker attachment result :=
  {| marker_operator := operator;
     completed_operands := 0;
     marker_phase := LeadingLiterals;
     result_continuation := target_resume_floor handoff |}.

Definition advance_closed_marker {attachment result}
    (marker : ClosedMarker attachment result)
    (completed : nat)
    (phase : ClosedPhase) : ClosedMarker attachment result :=
  {| marker_operator := marker_operator marker;
     completed_operands := completed;
     marker_phase := phase;
     result_continuation := result_continuation marker |}.

(** A factored spine is a compression of control paths, not a new parser
    call.  Committing to a member changes only the operator identity and
    local control coordinate. *)
Definition commit_factored_member {attachment result}
    (member : ClosedMixfixOperator attachment result)
    (marker : ClosedMarker attachment result)
    (completed : nat)
    (phase : ClosedPhase) : ClosedMarker attachment result :=
  {| marker_operator := member;
     completed_operands := completed;
     marker_phase := phase;
     result_continuation := result_continuation marker |}.

Definition complete_closed_marker {attachment result}
    (marker : ClosedMarker attachment result) : PrattFloor result :=
  result_continuation marker.

(** The runtime marker key must distinguish incompatible result
    continuations.  The production representation additionally carries
    category and rule identities; this minimal projection isolates the floor
    component whose omission caused the regression. *)
Definition marker_floor_key {attachment result}
    (marker : ClosedMarker attachment result) : nat :=
  minimum_power (result_continuation marker).

(** The compact runtime symbol reuses one local byte for the completed
    operand count and a distinct optional byte for the result continuation.
    A pure-CGLL return slot must project the continuation before considering
    the local byte.  Otherwise the initial completed count [0] shadows a
    nonzero caller floor even though the marker itself retained that floor. *)
Record RuntimeMarkerEncoding : Type := {
  local_control_power : option nat;
  saved_continuation_power : option nat
}.

(** The pure-CGLL return slot is the runtime erasure of a typed delegated
    handoff.  The source floor belongs to cross-category boundary discovery;
    the target floor belongs to the return continuation. *)
Record RuntimeDelegationSlot : Type := {
  boundary_source_power : option nat;
  return_target_power : option nat
}.

Definition encode_delegated_handoff {attachment result}
    (handoff : DelegatedPrattHandoff attachment result) :
    RuntimeDelegationSlot :=
  {| boundary_source_power :=
       Some (minimum_power (source_entry_floor handoff));
     return_target_power :=
       Some (minimum_power (target_resume_floor handoff)) |}.

Definition marker_continuation_from_delegation
    (slot : RuntimeDelegationSlot) : option nat :=
  return_target_power slot.

(** Historical collapsed projection: the delegated source floor was reused
    as the result continuation.  This definition exists only to state the
    counterexample. *)
Definition collapsed_marker_continuation_from_delegation
    (slot : RuntimeDelegationSlot) : option nat :=
  boundary_source_power slot.

Definition return_slot_power
    (symbol : RuntimeMarkerEncoding) (edge_hint : option nat) : option nat :=
  match saved_continuation_power symbol with
  | Some power => Some power
  | None => match local_control_power symbol with
            | Some power => Some power
            | None => edge_hint
            end
  end.

(** This is the historical, incorrect projection order retained only as a
    counterexample. *)
Definition shadowed_return_slot_power
    (symbol : RuntimeMarkerEncoding) (edge_hint : option nat) : option nat :=
  match local_control_power symbol with
  | Some power => Some power
  | None => match saved_continuation_power symbol with
            | Some power => Some power
            | None => edge_hint
            end
  end.

Definition encode_closed_marker {attachment result}
    (marker : ClosedMarker attachment result) : RuntimeMarkerEncoding :=
  {| local_control_power := Some (completed_operands marker);
     saved_continuation_power :=
       Some (minimum_power (result_continuation marker)) |}.

Definition admits_infix {category}
    (floor : PrattFloor category) (operator : InfixOperator category) : bool :=
  minimum_power floor <=? left_power operator.

Definition admits_attachment {attachment result}
    (floor : PrattFloor attachment)
    (operator : ClosedMixfixOperator attachment result) : bool :=
  minimum_power floor <=? attachment_power operator.

(** A candidate's category does not by itself determine its parser phase.
    Same-category left-denotation ([led]) operators belong exclusively to led
    dispatch after a left operand exists.  Closed category-changing terms are
    prefix delegates in the result category and carry their independently
    typed attachment floor. *)
Inductive PrattDispatchPhase : Type :=
| PrefixDispatchPhase
| LedDispatchPhase.

Inductive PrattCandidate (result : Category) : Type :=
| SameCategoryLedCandidate : InfixOperator result -> PrattCandidate result
| DelegatedClosedCandidate :
    forall attachment,
      ClosedMixfixOperator attachment result ->
      PrattFloor attachment ->
      PrattCandidate result.

Definition admits_candidate {result}
    (phase : PrattDispatchPhase)
    (result_floor : PrattFloor result)
    (candidate : PrattCandidate result) : bool :=
  match phase, candidate with
  | PrefixDispatchPhase, SameCategoryLedCandidate _ => false
  | LedDispatchPhase, SameCategoryLedCandidate operator =>
      admits_infix result_floor operator
  | PrefixDispatchPhase, DelegatedClosedCandidate operator source_floor =>
      admits_attachment source_floor operator
  | LedDispatchPhase, DelegatedClosedCandidate _ _ => false
  end.

(** The historical generic prefix bucket admitted every syntactically matching
    category-leading rule, including led operators.  It is retained solely to
    state the counterexample below. *)
Definition admits_ungated_prefix_candidate {result}
    (_ : PrattFloor result) (_ : PrattCandidate result) : bool := true.

(** A machine transition exists exactly when the phase-indexed admission
    judgment succeeds.  Prefix buckets and led tables consume disjoint arms of
    this relation, so a generic grammar continuation cannot bypass the Pratt
    right-power transition. *)
Inductive CandidateTransition {result}
    (phase : PrattDispatchPhase)
    (result_floor : PrattFloor result) : PrattCandidate result -> Prop :=
| AdmittedCandidate :
    forall candidate,
      admits_candidate phase result_floor candidate = true ->
      CandidateTransition phase result_floor candidate.

Theorem same_category_led_is_never_a_prefix_candidate :
  forall result (floor : PrattFloor result)
         (operator : InfixOperator result),
    admits_candidate PrefixDispatchPhase floor
      (SameCategoryLedCandidate operator) = false.
Proof.
  reflexivity.
Qed.

Theorem same_category_led_uses_the_led_floor :
  forall result (floor : PrattFloor result)
         (operator : InfixOperator result),
    admits_candidate LedDispatchPhase floor
      (SameCategoryLedCandidate operator) = admits_infix floor operator.
Proof.
  reflexivity.
Qed.

Theorem delegated_prefix_uses_only_attachment_admission :
  forall result (left_floor right_floor : PrattFloor result)
         attachment
         (operator : ClosedMixfixOperator attachment result)
         (source_floor : PrattFloor attachment),
    admits_candidate PrefixDispatchPhase left_floor
      (DelegatedClosedCandidate operator source_floor) =
    admits_candidate PrefixDispatchPhase right_floor
      (DelegatedClosedCandidate operator source_floor).
Proof.
  reflexivity.
Qed.

(** Completion of a closed category-changing term is transparent to the
    caller's result-category continuation.  Internal operands have already
    been delimited and discharged; there is no right edge that may lower the
    caller's floor. *)
Definition complete_closed_mixfix {attachment result}
    (_ : ClosedMixfixOperator attachment result)
    (caller : PrattFloor result) : PrattFloor result :=
  caller.

(** The historical implementation behavior, modeled only as the
    counterexample rejected by this development. *)
Definition reset_closed_mixfix {attachment result}
    (_ : ClosedMixfixOperator attachment result)
    (_ : PrattFloor result) : PrattFloor result :=
  {| minimum_power := 0 |}.

Theorem every_local_phase_preserves_result_continuation :
  forall attachment result
         (marker : ClosedMarker attachment result)
         completed phase,
    result_continuation (advance_closed_marker marker completed phase) =
    result_continuation marker.
Proof.
  reflexivity.
Qed.

Theorem every_factored_commit_preserves_result_continuation :
  forall attachment result
         (member : ClosedMixfixOperator attachment result)
         (marker : ClosedMarker attachment result)
         completed phase,
    result_continuation
      (commit_factored_member member marker completed phase) =
    result_continuation marker.
Proof.
  reflexivity.
Qed.

Theorem completed_marker_returns_exact_caller_floor :
  forall attachment result (marker : ClosedMarker attachment result),
    complete_closed_marker marker = result_continuation marker.
Proof.
  reflexivity.
Qed.

Theorem marker_key_separates_incompatible_floors :
  forall attachment result
         (left right : ClosedMarker attachment result),
    marker_floor_key left = marker_floor_key right ->
    minimum_power (result_continuation left) =
    minimum_power (result_continuation right).
Proof.
  intros attachment result left right equal_keys.
  exact equal_keys.
Qed.

Theorem return_slot_projection_preserves_marker_continuation :
  forall attachment result
         (marker : ClosedMarker attachment result) edge_hint,
    return_slot_power (encode_closed_marker marker) edge_hint =
    Some (minimum_power (result_continuation marker)).
Proof.
  reflexivity.
Qed.

Theorem delegated_handoff_preserves_both_floors :
  forall attachment result
         (handoff : DelegatedPrattHandoff attachment result),
    boundary_source_power (encode_delegated_handoff handoff) =
      Some (minimum_power (source_entry_floor handoff)) /\
    return_target_power (encode_delegated_handoff handoff) =
      Some (minimum_power (target_resume_floor handoff)).
Proof.
  intros attachment result handoff.
  split; reflexivity.
Qed.

Theorem delegated_closed_marker_uses_only_target_continuation :
  forall attachment result
         (operator : ClosedMixfixOperator attachment result)
         (handoff : DelegatedPrattHandoff attachment result),
    result_continuation (begin_closed_from_handoff operator handoff) =
      target_resume_floor handoff.
Proof.
  reflexivity.
Qed.

Theorem phase_census_preserves_result_continuation :
  forall attachment result
         (marker : ClosedMarker attachment result)
         completed phase,
    match phase with
    | LeadingLiterals
    | Operand
    | Capture
    | Repetition
    | FollowingLiterals
    | FactoredSpine =>
        result_continuation
          (advance_closed_marker marker completed phase) =
        result_continuation marker
    end.
Proof.
  intros attachment result marker completed phase.
  destruct phase; reflexivity.
Qed.

Theorem closed_mixfix_preserves_result_floor :
  forall attachment result
         (operator : ClosedMixfixOperator attachment result)
         (caller : PrattFloor result),
    minimum_power (complete_closed_mixfix operator caller) =
    minimum_power caller.
Proof.
  reflexivity.
Qed.

Theorem closed_mixfix_completion_is_idempotent :
  forall attachment result
         (operator : ClosedMixfixOperator attachment result)
         (caller : PrattFloor result),
    complete_closed_mixfix operator
      (complete_closed_mixfix operator caller) =
    complete_closed_mixfix operator caller.
Proof.
  reflexivity.
Qed.

(** Adding unrelated categories or operators cannot perturb completion: the
    construction is polymorphic in both endpoint categories and observes only
    the supplied result-category continuation. *)
Theorem unrelated_category_extension_is_inert :
  forall attachment result unrelated
         (operator : ClosedMixfixOperator attachment result)
         (caller : PrattFloor result)
         (unrelated_operator : InfixOperator unrelated),
    complete_closed_mixfix operator caller = caller.
Proof.
  reflexivity.
Qed.

Definition rholang_send :
    ClosedMixfixOperator NameCategory ProcCategory :=
  {| attachment_power := 2 |}.

Definition rholang_parallel : InfixOperator ProcCategory :=
  {| left_power := 2; right_power := 3 |}.

Definition name_attachment_floor : PrattFloor NameCategory :=
  {| minimum_power := 0 |}.

Definition parallel_rhs_floor : PrattFloor ProcCategory :=
  {| minimum_power := right_power rholang_parallel |}.

Definition send_on_parallel_rhs :
    ClosedMarker NameCategory ProcCategory :=
  {| marker_operator := rholang_send;
     completed_operands := 0;
     marker_phase := LeadingLiterals;
     result_continuation := parallel_rhs_floor |}.

Definition send_rhs_handoff :
    DelegatedPrattHandoff NameCategory ProcCategory :=
  {| source_entry_floor := name_attachment_floor;
     target_resume_floor := parallel_rhs_floor |}.

Example send_attaches_to_name :
  admits_attachment name_attachment_floor rholang_send = true.
Proof.
  reflexivity.
Qed.

(** At the right-hand-side floor [3], the next left-associative parallel
    operator has left power [2] and must be rejected. *)
Theorem preserved_floor_rejects_right_association :
  admits_infix
    (complete_closed_mixfix rholang_send parallel_rhs_floor)
    rholang_parallel = false.
Proof.
  reflexivity.
Qed.

(** Resetting the floor to zero admits the same operator and is therefore a
    concrete counterexample to left-associative uniqueness. *)
Theorem reset_floor_admits_spurious_right_association :
  admits_infix
    (reset_closed_mixfix rholang_send parallel_rhs_floor)
    rholang_parallel = true.
Proof.
  reflexivity.
Qed.

Definition proc_root_floor : PrattFloor ProcCategory :=
  {| minimum_power := 0 |}.

Definition parallel_candidate : PrattCandidate ProcCategory :=
  SameCategoryLedCandidate rholang_parallel.

Definition delegated_send_candidate : PrattCandidate ProcCategory :=
  DelegatedClosedCandidate rholang_send name_attachment_floor.

(** Even at the root floor, parallel composition is not a prefix candidate.
    It becomes available only after a left operand has been recognized and the
    machine has entered led dispatch. *)
Theorem parallel_is_rejected_from_prefix_dispatch_at_root :
  admits_candidate PrefixDispatchPhase proc_root_floor parallel_candidate = false.
Proof.
  reflexivity.
Qed.

(** At the root led floor, parallel composition is admitted normally. *)
Theorem parallel_is_admitted_by_led_dispatch_at_root :
  admits_candidate LedDispatchPhase proc_root_floor parallel_candidate = true.
Proof.
  reflexivity.
Qed.

(** On a right-hand side, ordinary led dispatch rejects parallel composition
    because its left power [2] is below the active floor [3]. *)
Theorem parallel_is_rejected_by_led_dispatch_at_rhs_floor :
  admits_candidate LedDispatchPhase parallel_rhs_floor parallel_candidate = false.
Proof.
  reflexivity.
Qed.

(** A send remains a valid closed prefix delegate on that same right-hand side. Its
    attachment is checked in [NameCategory] at floor [0], independently of the
    [ProcCategory] continuation floor [3]. *)
Theorem delegated_send_prefix_candidate_remains_admitted :
  admits_candidate PrefixDispatchPhase parallel_rhs_floor
    delegated_send_candidate = true.
Proof.
  reflexivity.
Qed.

Theorem no_spurious_parallel_prefix_transition :
  ~ CandidateTransition PrefixDispatchPhase proc_root_floor parallel_candidate.
Proof.
  intro transition.
  inversion transition.
  discriminate.
Qed.

Theorem delegated_send_prefix_transition_exists :
  CandidateTransition PrefixDispatchPhase parallel_rhs_floor
    delegated_send_candidate.
Proof.
  constructor.
  reflexivity.
Qed.

(** The ungated historical bucket accepted the led candidate at the root. Its
    generic rule continuation then parsed the right operand at a prefix floor
    instead of the operator's right power, exhibiting the extra association
    independently of closed-term continuation preservation. *)
Theorem ungated_prefix_bucket_exhibits_the_regression :
  admits_ungated_prefix_candidate proc_root_floor parallel_candidate = true.
Proof.
  reflexivity.
Qed.

Inductive Association : Type :=
| LeftAssociation
| RightAssociation.

Definition association_after_send (floor : PrattFloor ProcCategory) : Association :=
  if admits_infix floor rholang_parallel
  then RightAssociation
  else LeftAssociation.

Theorem send_chain_has_unique_left_association_when_floor_is_preserved :
  association_after_send
    (complete_closed_mixfix rholang_send parallel_rhs_floor) =
  LeftAssociation.
Proof.
  reflexivity.
Qed.

Theorem zero_reset_exhibits_the_regression :
  association_after_send
    (reset_closed_mixfix rholang_send parallel_rhs_floor) =
  RightAssociation.
Proof.
  reflexivity.
Qed.

Example local_operand_count_must_not_shadow_parallel_rhs_floor :
  return_slot_power (encode_closed_marker send_on_parallel_rhs) None = Some 3.
Proof.
  reflexivity.
Qed.

Example historical_projection_shadows_parallel_rhs_floor :
  shadowed_return_slot_power
    (encode_closed_marker send_on_parallel_rhs) None = Some 0.
Proof.
  reflexivity.
Qed.

Example delegated_send_retains_distinct_source_and_target_floors :
  boundary_source_power (encode_delegated_handoff send_rhs_handoff) = Some 0 /\
  return_target_power (encode_delegated_handoff send_rhs_handoff) = Some 3.
Proof.
  split; reflexivity.
Qed.

Example delegated_send_marker_resumes_at_parallel_rhs_floor :
  marker_continuation_from_delegation
    (encode_delegated_handoff send_rhs_handoff) = Some 3.
Proof.
  reflexivity.
Qed.

Example collapsed_delegation_exhibits_zero_floor_loss :
  collapsed_marker_continuation_from_delegation
    (encode_delegated_handoff send_rhs_handoff) = Some 0.
Proof.
  reflexivity.
Qed.

Theorem handoff_started_send_rejects_spurious_parallel :
  admits_infix
    (complete_closed_marker
      (begin_closed_from_handoff rholang_send send_rhs_handoff))
    rholang_parallel = false.
Proof.
  reflexivity.
Qed.

Theorem all_send_machine_paths_reject_spurious_parallel :
  forall completed phase,
    admits_infix
      (complete_closed_marker
        (advance_closed_marker send_on_parallel_rhs completed phase))
      rholang_parallel = false.
Proof.
  intros completed phase.
  destruct phase; reflexivity.
Qed.

Theorem factored_send_machine_paths_reject_spurious_parallel :
  forall completed phase,
    admits_infix
      (complete_closed_marker
        (commit_factored_member
          rholang_send send_on_parallel_rhs completed phase))
      rholang_parallel = false.
Proof.
  intros completed phase.
  destruct phase; reflexivity.
Qed.

Print Assumptions every_local_phase_preserves_result_continuation.
Print Assumptions every_factored_commit_preserves_result_continuation.
Print Assumptions completed_marker_returns_exact_caller_floor.
Print Assumptions marker_key_separates_incompatible_floors.
Print Assumptions return_slot_projection_preserves_marker_continuation.
Print Assumptions delegated_handoff_preserves_both_floors.
Print Assumptions delegated_closed_marker_uses_only_target_continuation.
Print Assumptions phase_census_preserves_result_continuation.
Print Assumptions closed_mixfix_preserves_result_floor.
Print Assumptions closed_mixfix_completion_is_idempotent.
Print Assumptions unrelated_category_extension_is_inert.
Print Assumptions preserved_floor_rejects_right_association.
Print Assumptions reset_floor_admits_spurious_right_association.
Print Assumptions same_category_led_is_never_a_prefix_candidate.
Print Assumptions same_category_led_uses_the_led_floor.
Print Assumptions delegated_prefix_uses_only_attachment_admission.
Print Assumptions parallel_is_rejected_from_prefix_dispatch_at_root.
Print Assumptions parallel_is_admitted_by_led_dispatch_at_root.
Print Assumptions parallel_is_rejected_by_led_dispatch_at_rhs_floor.
Print Assumptions delegated_send_prefix_candidate_remains_admitted.
Print Assumptions no_spurious_parallel_prefix_transition.
Print Assumptions delegated_send_prefix_transition_exists.
Print Assumptions ungated_prefix_bucket_exhibits_the_regression.
Print Assumptions send_chain_has_unique_left_association_when_floor_is_preserved.
Print Assumptions zero_reset_exhibits_the_regression.
Print Assumptions local_operand_count_must_not_shadow_parallel_rhs_floor.
Print Assumptions historical_projection_shadows_parallel_rhs_floor.
Print Assumptions delegated_send_retains_distinct_source_and_target_floors.
Print Assumptions delegated_send_marker_resumes_at_parallel_rhs_floor.
Print Assumptions collapsed_delegation_exhibits_zero_floor_loss.
Print Assumptions handoff_started_send_rejects_spurious_parallel.
Print Assumptions all_send_machine_paths_reject_spurious_parallel.
Print Assumptions factored_send_machine_paths_reject_spurious_parallel.
