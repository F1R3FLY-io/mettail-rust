(** Concrete flat-leaf cleanup accounting for checked_binding.rs.

    Reuse the existing FLT payload shapes and record/byte measurements.
    One logical teardown event is assigned to each FLT node, vector header,
    entry dispatch and owned String field. This is a contract for THESE flat
    Rust shapes, not a claim that any record has constant-cost Drop. Actual
    allocator time/capacity and unwind are not modeled. The selector has its
    own checked leaf admission and is deliberately excluded here.

    The independently source-reviewed BehavioralPred worker already prepays
    its flat and deep cleanup; it is not assigned this FLT contract. *)
From Stdlib Require Import List String Arith Lia.
From RhoBridge Require Import FltSelectorBinding GeneratedDummyCleanupReservation.
Import ListNotations.

Module FlatBindingLeafReservation.
Module F := SelectorPayloadComposition.
Module D := GeneratedDummyCleanupReservation.

Definition optional_text_cleanup (text : option string) : nat :=
  match text with None => 0 | Some _ => 1 end.
Definition name_copy_work text := 1 + optional_text_cleanup text + F.optional_bytes text.

Theorem absent_name_has_no_owned_text_cleanup :
  optional_text_cleanup None = 0 /\ name_copy_work None = 1.
Proof. split; reflexivity. Qed.

Theorem present_name_prepays_text_cleanup : forall text,
  name_copy_work (Some text) = 2 + String.length text.
Proof. reflexivity. Qed.

(** Entry dispatch, mandatory name String, and only a present category String.
    Option/range/identifier metadata introduce no recursive owned children. *)
Definition hole_cleanup hole :=
  1 + 1 + optional_text_cleanup (F.hole_category hole).
Definition piece_cleanup piece :=
  1 + match piece with F.TextPiece _ _ => 1 | F.HolePiece _ _ => 0 end.
Definition payload_cleanup payload :=
  1 + 5 + 2 +
  fold_right (fun hole rest => hole_cleanup hole + rest) 0 (F.holes payload) +
  fold_right (fun piece rest => piece_cleanup piece + rest) 0 (F.pieces payload).

Lemma hole_cleanup_matches_explicit_records : forall hole,
  hole_cleanup hole = F.hole_records hole.
Proof. intros [id name category range]. destruct category; reflexivity. Qed.

Lemma piece_cleanup_matches_explicit_records : forall piece,
  piece_cleanup piece = F.piece_records piece.
Proof. intros []; reflexivity. Qed.

Theorem flat_payload_cleanup_equals_its_explicit_record_tally : forall payload,
  payload_cleanup payload = F.payload_records payload.
Proof.
  intro payload. unfold payload_cleanup, F.payload_records.
  assert (HH :
    fold_right (fun hole rest => hole_cleanup hole + rest) 0 (F.holes payload) =
    fold_right (fun hole rest => F.hole_records hole + rest) 0 (F.holes payload)).
  { induction (F.holes payload) as [|hole rest IH]; cbn [fold_right];
      [reflexivity|now rewrite hole_cleanup_matches_explicit_records, IH]. }
  assert (HP :
    fold_right (fun piece rest => piece_cleanup piece + rest) 0 (F.pieces payload) =
    fold_right (fun piece rest => F.piece_records piece + rest) 0 (F.pieces payload)).
  { induction (F.pieces payload) as [|piece rest IH]; cbn [fold_right];
      [reflexivity|now rewrite piece_cleanup_matches_explicit_records, IH]. }
  now rewrite HH, HP.
Qed.

Definition payload_copy_and_cleanup_work payload :=
  F.payload_records payload + payload_cleanup payload + F.payload_bytes payload.

Theorem payload_total_work_is_double_records_plus_bytes : forall payload,
  payload_copy_and_cleanup_work payload =
    2 * F.payload_records payload + F.payload_bytes payload.
Proof.
  intro payload. unfold payload_copy_and_cleanup_work.
  rewrite flat_payload_cleanup_equals_its_explicit_record_tally. lia.
Qed.

Theorem declared_bounds_do_not_change_cleanup : forall payload bounds,
  payload_cleanup (F.with_bounds payload bounds) = payload_cleanup payload.
Proof. reflexivity. Qed.

(** Native optional fields differ from optional category Arc fields.
    iterative_drop.rs's regular arm skips opaque/predicate fields BEFORE the
    optional take branch. The native Option therefore drops in place: one
    logical output-shell construction and one flat shell teardown, whether
    None or Some. There is no replacement None, child DropTask or category
    dummy. A present native leaf retains its own already-paid copy/cleanup
    contract; the shell does not pay that leaf a second time.

    Mixed assembly must copy native leaves into paid locals before all
    fallible category takes. After those takes, wrappers and the parent are
    constructed with no fallible callback before publication. These facts
    specify local accounting, not a proof that Rust obeys that order. Parent,
    worker and slot charges, allocator behavior and unwind remain separate. *)
Definition native_optional_shell_events (_present : bool) : D.Counts := fun event =>
  D.atom D.NativeWork event + D.atom D.NativeRecord event +
  D.atom D.NativeWork event.

Theorem native_optional_shell_presence_inert : forall event,
  native_optional_shell_events true event = native_optional_shell_events false event.
Proof. reflexivity. Qed.

Theorem native_optional_shell_projection : forall present,
  D.weighted D.base_work_weight (native_optional_shell_events present) = 2 /\
  D.weighted D.record_weight (native_optional_shell_events present) = 1 /\
  D.weighted D.byte_weight (native_optional_shell_events present) = 0.
Proof. intro present; repeat split; reflexivity. Qed.

(** The leaf parameter is its established event contract, not a claim that
    every native type has the same cleanup or that a new meter is needed. *)
Definition native_optional_events {A}
    (leaf : A -> D.Counts) (value : option A) : D.Counts := fun event =>
  match value with
  | None => native_optional_shell_events false event
  | Some item => native_optional_shell_events true event + leaf item event
  end.

Theorem native_optional_none_has_no_child_credit : forall A leaf event,
  @native_optional_events A leaf None event =
  native_optional_shell_events false event.
Proof. reflexivity. Qed.

Theorem native_optional_none_projection : forall A leaf,
  D.weighted D.base_work_weight (@native_optional_events A leaf None) = 2 /\
  D.weighted D.record_weight (@native_optional_events A leaf None) = 1 /\
  D.weighted D.byte_weight (@native_optional_events A leaf None) = 0.
Proof. intros. apply native_optional_shell_projection. Qed.

Theorem native_optional_some_projection : forall A leaf (value : A),
  D.weighted D.base_work_weight (native_optional_events leaf (Some value)) =
    2 + D.weighted D.base_work_weight (leaf value) /\
  D.weighted D.record_weight (native_optional_events leaf (Some value)) =
    1 + D.weighted D.record_weight (leaf value) /\
  D.weighted D.byte_weight (native_optional_events leaf (Some value)) =
    D.weighted D.byte_weight (leaf value).
Proof.
  intros A leaf value.
  assert (Hadd : forall weight (left right : D.Counts),
    D.weighted weight (fun event => left event + right event) =
    D.weighted weight left + D.weighted weight right).
  { intros weight left right. unfold D.weighted.
    induction D.all_events as [|event rest IH]; cbn [D.weighted_over]; nia. }
  unfold native_optional_events. rewrite !Hadd.
  destruct (native_optional_shell_projection true) as [HW [HR HB]].
  rewrite HW, HR, HB. repeat split; lia.
Qed.

(** A standalone Arc wrapper is not a generated child-field extraction.
    Copying a source-pinned handle creates a logical output record but does
    not allocate its referent. A fresh wrapper allocates an Arc. Both later
    execute wrapper release and the final-owner check; the produced child's
    already-paid cleanup remains separate.

    An explicit Arc<FltNode> adapter must use this wrapper contract:
    Clone shares the source-pinned Arc and charges no referent copy; Open/Close
    use the checked FLT leaf plus a fresh wrapper. Neither invokes a category
    dummy. The source borrow remains alive through normal-error cleanup. *)
Definition arc_wrapper_events (fresh : bool) : D.Counts := fun event =>
  (if fresh then D.atom D.AllocateArc event
   else D.atom D.NativeWork event + D.atom D.NativeRecord event) +
  D.atom D.ReleaseFieldArc event + D.atom D.CheckArcOwner event.

Theorem standalone_arc_wrapper_projection : forall fresh,
  D.weighted D.base_work_weight (arc_wrapper_events fresh) = 3 /\
  D.weighted D.record_weight (arc_wrapper_events fresh) = 1 /\
  D.weighted D.byte_weight (arc_wrapper_events fresh) = 0.
Proof. intros []; repeat split; reflexivity. Qed.

Print Assumptions absent_name_has_no_owned_text_cleanup.
Print Assumptions present_name_prepays_text_cleanup.
Print Assumptions hole_cleanup_matches_explicit_records.
Print Assumptions piece_cleanup_matches_explicit_records.
Print Assumptions flat_payload_cleanup_equals_its_explicit_record_tally.
Print Assumptions payload_total_work_is_double_records_plus_bytes.
Print Assumptions declared_bounds_do_not_change_cleanup.
Print Assumptions native_optional_shell_presence_inert.
Print Assumptions native_optional_shell_projection.
Print Assumptions native_optional_none_has_no_child_credit.
Print Assumptions native_optional_none_projection.
Print Assumptions native_optional_some_projection.
Print Assumptions standalone_arc_wrapper_projection.
End FlatBindingLeafReservation.
