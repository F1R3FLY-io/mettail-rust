(** Erasure of proof-only annotations from the EXISTING raw Map control.
    Erasure changes only carried operands. It retains original cursor values,
    widths, counts, pending destinations, buffer option shapes, control labels
    and supplied comparison answers. No comparator, fallback class, new
    executor or runtime storage is introduced.

    Later control lifting requires only compatibility of the original alias
    predicates with operand erasure, not injectivity or a semantic-result
    premise. These equalities describe the same successful source operations
    under a change of operand representation. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import GeneratedMapCoreSource MergeSortPdaCursor
  MergeSortPdaNativeRun.
Import ListNotations.
Import GeneratedMapCoreSource.GeneratedMapCoreSource.
Import MergeSortPdaCursor.MergeSortPdaCursor.

Module GeneratedMapCoreErasure.

Section MergeErasure.
Context {SourceEntry TargetEntry : Type}.
Variable erase : SourceEntry -> TargetEntry.

Definition erase_merge (state : @RawMergeState SourceEntry) : @RawMergeState TargetEntry :=
  merge_state (map erase (merge_source state))
    (option_map (map erase) (merge_target state))
    (merge_width state) (merge_cursor state) (merge_waiting state) (merge_done state).

Definition erase_merge_reply (reply : @RawMergeReply SourceEntry) : @RawMergeReply TargetEntry :=
  match reply with MergeRequests lhs rhs => MergeRequests (erase lhs) (erase rhs)
    | MergeCompletes => MergeCompletes end.

Theorem overwrite_erasure : forall index value items,
  overwrite index (erase value) (map erase items) =
    option_map (map erase) (overwrite index value items).
Proof.
  induction index as [|index IH]; intros value [|head rest];
    cbn [overwrite map]; try reflexivity.
  rewrite IH. destruct (overwrite index value rest); reflexivity.
Qed.

Theorem copy_record_erasure : forall side cursor source target,
  copy_record side cursor (map erase source) (map erase target) =
    option_map (fun output => (fst output, map erase (snd output)))
      (copy_record side cursor source target).
Proof.
  intros side cursor source target. unfold copy_record.
  rewrite nth_error_map.
  destruct (nth_error source (selected_index side cursor)) as [value|]; [|reflexivity].
  cbn [option_map]. rewrite overwrite_erasure.
  destruct (overwrite (output_index cursor) value target); reflexivity.
Qed.

Theorem original_indexed_request_erases_to_the_same_read_positions :
  forall source cursor lhs rhs,
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest source cursor lhs rhs ->
  MergeSortPdaNativeRun.MergeSortPdaNativeRun.NativeRequest
    (map erase source) cursor (erase lhs) (erase rhs).
Proof.
  intros source cursor lhs rhs [LEFT [RIGHT [READ_LEFT READ_RIGHT]]].
  split; [exact LEFT|]. split; [exact RIGHT|]. split;
    rewrite nth_error_map; [rewrite READ_LEFT|rewrite READ_RIGHT]; reflexivity.
Qed.

Theorem initial_merge_erasure : forall maximum source,
  erase_merge (initial_merge maximum source) = initial_merge maximum (map erase source).
Proof.
  intros. unfold erase_merge, initial_merge.
  cbn [merge_state merge_source merge_target merge_width merge_cursor merge_waiting merge_done].
  now rewrite length_map.
Qed.

Theorem scratch_replacement_erasure : forall state target,
  erase_merge (merge_set_target state target) =
    merge_set_target (erase_merge state) (option_map (map erase) target).
Proof. reflexivity. Qed.

Theorem waiting_flag_erasure : forall state waiting,
  erase_merge (merge_set_waiting state waiting) =
    merge_set_waiting (erase_merge state) waiting.
Proof. reflexivity. Qed.

Theorem indexed_copy_payload_erasure : forall state cursor target,
  erase_merge (merge_after_copy state cursor target) =
    merge_after_copy (erase_merge state) cursor (map erase target).
Proof. reflexivity. Qed.

Theorem original_run_boundary_erasure : forall maximum state completed,
  erase_merge (merge_after_run maximum state completed) =
    merge_after_run maximum (erase_merge state) (map erase completed).
Proof.
  intros maximum state completed. unfold merge_after_run.
  cbn [erase_merge merge_state merge_source merge_cursor merge_width].
  rewrite !length_map.
  destruct (run_end (merge_cursor state) <? length (merge_source state));
    [reflexivity|].
  destruct (length completed <=? saturated_double maximum (merge_width state)); reflexivity.
Qed.

Theorem supplied_merge_response_erasure : forall state ordering,
  raw_merge_accept (erase_merge state) ordering =
    option_map erase_merge (raw_merge_accept state ordering).
Proof.
  intros [source target width cursor waiting done] ordering.
  unfold raw_merge_accept.
  cbn [erase_merge merge_state merge_source merge_target merge_width merge_cursor merge_waiting merge_done].
  destruct waiting; [|reflexivity].
  destruct target as [target|]; [|reflexivity].
  cbn [option_map].
  rewrite copy_record_erasure.
  destruct (copy_record (accept_side ordering) cursor source target) as [[next_cursor next]|];
    reflexivity.
Qed.
End MergeErasure.

End GeneratedMapCoreErasure.

Print Assumptions GeneratedMapCoreErasure.overwrite_erasure.
Print Assumptions GeneratedMapCoreErasure.copy_record_erasure.
Print Assumptions GeneratedMapCoreErasure.original_indexed_request_erases_to_the_same_read_positions.
Print Assumptions GeneratedMapCoreErasure.initial_merge_erasure.
Print Assumptions GeneratedMapCoreErasure.scratch_replacement_erasure.
Print Assumptions GeneratedMapCoreErasure.waiting_flag_erasure.
Print Assumptions GeneratedMapCoreErasure.indexed_copy_payload_erasure.
Print Assumptions GeneratedMapCoreErasure.original_run_boundary_erasure.
Print Assumptions GeneratedMapCoreErasure.supplied_merge_response_erasure.
