(** First-return uniqueness of the existing comparator-free Map source model.
    No comparator result is prescribed here: a fixed ingress ordering may be
    any ordering. The proof uses the disjoint source guards, functional indexed
    reads/copies and the existing RawCorePath. It adds no execution relation,
    runtime instruction, stored state, termination bound or result oracle.

    Uniqueness relates two successful invocations from the SAME complete raw
    payload and input. Linking a parked generated owner to that payload, and
    proving the ordering supplied by its actual child traversal, remain the
    separate source/ownership obligations. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import GeneratedMapCoreSource MergeSortPdaNativeRun.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import MergeSortPdaNativeRun.MergeSortPdaNativeRun.

Module GeneratedMapCoreDeterminism.
Section Merge.
Context {Entry : Type}.
Variable maximum : nat.

Lemma silent_merge_work_is_not_done : forall (state next : @RawMergeState Entry),
  RawMergeSilent maximum state next -> merge_done state = false.
Proof. intros state next STEP. destruct STEP; assumption. Qed.

Theorem raw_silent_merge_work_is_functional : forall (state left right : @RawMergeState Entry),
  RawMergeSilent maximum state left -> RawMergeSilent maximum state right -> left = right.
Proof.
  intros state left right FIRST SECOND.
  inversion FIRST; inversion SECOND; subst; congruence.
Qed.

Lemma silent_merge_work_excludes_a_ready_pair :
  forall (state next : @RawMergeState Entry) target lhs rhs,
  RawMergeSilent maximum state next -> merge_target state = Some target ->
  NativeRequest (merge_source state) (merge_cursor state) lhs rhs -> False.
Proof.
  intros state next target lhs rhs SILENT TARGET [LEFT [RIGHT READS]].
  destruct SILENT; congruence.
Qed.

Lemma original_indexed_requests_are_functional :
  forall (source : list Entry) cursor lhs rhs other_lhs other_rhs,
  NativeRequest source cursor lhs rhs -> NativeRequest source cursor other_lhs other_rhs ->
  lhs = other_lhs /\ rhs = other_rhs.
Proof. intros source cursor lhs rhs other_lhs other_rhs
  [_ [_ [LEFT RIGHT]]] [_ [_ [OTHER_LEFT OTHER_RIGHT]]]. split; congruence.
Qed.

Theorem raw_merge_step_has_one_reply_and_payload :
  forall (state : @RawMergeState Entry) reply next,
  RawMergeStep maximum state reply next ->
  forall other_reply other_next, RawMergeStep maximum state other_reply other_next ->
  reply = other_reply /\ next = other_next.
Proof.
  intros state reply next FIRST. induction FIRST as
    [state WAIT DONE|state target lhs rhs WAIT DONE TARGET REQUEST|
     state middle reply next SILENT REST IH]; intros other_reply other_next SECOND.
  - inversion SECOND; subst; try solve [split; reflexivity]; try congruence.
    match goal with QUIET : RawMergeSilent maximum state _ |- _ =>
      pose proof (silent_merge_work_is_not_done _ _ QUIET); congruence end.
  - inversion SECOND; subst; try congruence.
    + match goal with REQUEST2 : NativeRequest _ _ _ _ |- _ =>
        destruct (original_indexed_requests_are_functional _ _ _ _ _ _ REQUEST REQUEST2)
          as [LEFT RIGHT]; subst; split; reflexivity end.
    + exfalso. eapply silent_merge_work_excludes_a_ready_pair; eassumption.
  - inversion SECOND; subst.
    + pose proof (silent_merge_work_is_not_done _ _ SILENT). congruence.
    + exfalso. eapply silent_merge_work_excludes_a_ready_pair; eassumption.
    + match goal with QUIET : RawMergeSilent maximum state ?other_middle |- _ =>
        assert (SAME : middle = other_middle) by
          (eapply raw_silent_merge_work_is_functional; eassumption);
        subst other_middle
      end.
      apply IH. assumption.
Qed.
End Merge.

Section Map.
Context {Key Value : Type}.
Variables key_alias : Key -> Key -> bool.
Variables value_alias : Value -> Value -> bool.
Variable maximum : nat.
Local Notation Step := (@RawCoreStep Key Value key_alias value_alias maximum).
Local Notation Path := (@RawCorePath Key Value key_alias value_alias maximum).

Theorem original_map_control_has_one_next_control_and_payload :
  forall control state left_control left_state,
  Step control state left_control left_state ->
  forall right_control right_state, Step control state right_control right_state ->
  left_control = right_control /\ left_state = right_state.
Proof.
  intros control state left_control left_state FIRST right_control right_state SECOND.
  inversion FIRST; inversion SECOND; subst; try solve [split; congruence].
  all: match goal with
    LEFT : RawMergeStep maximum ?source ?left_reply ?left_after,
    RIGHT : RawMergeStep maximum ?source ?right_reply ?right_after |- _ =>
      destruct (raw_merge_step_has_one_reply_and_payload maximum source left_reply left_after
        LEFT right_reply right_after RIGHT) as [REPLY PAYLOAD];
      split; congruence
    end.
Qed.

Lemma original_map_return_paths_are_unique :
  forall control state last final,
  Path control state last final ->
  forall reply, last = ReturnReply reply ->
  forall other_reply other_final,
  Path control state (ReturnReply other_reply) other_final ->
  reply = other_reply /\ final = other_final.
Proof.
  intros control state last final FIRST.
  induction FIRST as [control state|
    control state middle middle_state last final STEP REST IH];
    intros reply RETURN other_reply other_final SECOND.
  - subst control.
    pose proof (a_path_cannot_cross_its_first_return key_alias value_alias maximum
      reply state (ReturnReply other_reply) other_final SECOND) as [REPLY STATE].
    split; congruence.
  - inversion SECOND; subst.
    + exfalso. eapply returned_reply_has_no_internal_successor; exact STEP.
    + match goal with
      NEXT : RawPayloadCoreStep _ _ _ _ _ control state ?other_control ?other_state |- _ =>
        destruct (original_map_control_has_one_next_control_and_payload
          control state middle middle_state STEP other_control other_state NEXT)
          as [CONTROL STATE]; subst other_control other_state
      end.
      eapply IH; [reflexivity|eassumption].
Qed.

Theorem same_actual_map_ingress_returns_the_same_reply_and_complete_payload :
  forall state input reply next other_reply other_next,
  @RawResume Key Value key_alias value_alias maximum state input reply next ->
  @RawResume Key Value key_alias value_alias maximum state input other_reply other_next ->
  reply = other_reply /\ next = other_next.
Proof.
  intros state input reply next other_reply other_next FIRST SECOND.
  eapply original_map_return_paths_are_unique; [exact FIRST|reflexivity|exact SECOND].
Qed.

(** Match an actual successful resume against the retained native dialogue.
    This does not assert that the child supplies the listed answer. That
    independent child theorem is what permits advancing to the returned tail.
    Crucially the tail starts at the actual returned complete payload, not a
    reconstructed initial state or a restarted sort. *)
Theorem actual_resume_keeps_the_exact_retained_dialogue_frontier :
  forall state input answers result final,
  @RawDialogue Key Value key_alias value_alias maximum (Ingress input) state
    answers (ReturnReply (Completes result)) final ->
  forall reply after,
  @RawResume Key Value key_alias value_alias maximum state input reply after ->
  match answers with
  | nil => reply = Completes result /\ after = final
  | (request, answer) :: rest =>
      reply = Requests request /\
      @RawDialogue Key Value key_alias value_alias maximum (Ingress (Some answer)) after
        rest (ReturnReply (Completes result)) final
  end.
Proof.
  intros state input answers result final DIALOGUE reply after ACTUAL.
  inversion DIALOGUE as [control initial last finish QUIET|
    control initial request parked answer rest last finish PREFIX SUFFIX]; subst.
  - destruct (same_actual_map_ingress_returns_the_same_reply_and_complete_payload
      state input (Completes result) final reply after QUIET ACTUAL) as [<- <-].
    split; reflexivity.
  - destruct (same_actual_map_ingress_returns_the_same_reply_and_complete_payload
      state input (Requests request) parked reply after PREFIX ACTUAL) as [<- <-].
    split; [reflexivity|exact SUFFIX].
Qed.
End Map.

Print Assumptions silent_merge_work_is_not_done.
Print Assumptions raw_silent_merge_work_is_functional.
Print Assumptions silent_merge_work_excludes_a_ready_pair.
Print Assumptions original_indexed_requests_are_functional.
Print Assumptions raw_merge_step_has_one_reply_and_payload.
Print Assumptions original_map_control_has_one_next_control_and_payload.
Print Assumptions original_map_return_paths_are_unique.
Print Assumptions same_actual_map_ingress_returns_the_same_reply_and_complete_payload.
Print Assumptions actual_resume_keeps_the_exact_retained_dialogue_frontier.
End GeneratedMapCoreDeterminism.
