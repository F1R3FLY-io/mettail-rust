(*
 * BinderTraversalFrames: typed-continuation laws for the generated nested
 * Optional/BinderList PDA.
 *
 * Runtime correspondence:
 *   - ResumeRule       = RuleAt(next_pos)
 *   - ResumeOptional   = OptionalGroupAt(marker_id)
 *   - ResumeBinderList = BinderListLoopAt(marker_id)
 *
 * Optional/BinderList markers keep StackSymbolV2 at 14 bytes by storing a
 * dense u32 marker_id in its two existing u16 category/rule fields. Generated
 * metadata decodes that ID to the exact (result category, rule, frame,
 * sub-position) continuation. MarkerTable below states that generated-table
 * round trip explicitly; the Rust exhaustive oracle checks the constructed
 * finite table satisfies it.
 *
 * The Rust generator replaces the caller's current marker with one of these
 * continuations before entering a binder-list frame. Frame-local runtime
 * state therefore needs only (rule, frame_idx, sub_pos, outer_bp). These
 * theorems establish that enter/finish is an identity on the caller stack,
 * that marker kinds cannot alias, that distinct nested binder frames cannot
 * alias, and that the last child resumes the parent loop at sub-position 0.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.

Inductive Resume : Type :=
| ResumeRule (next_pos : nat)
| ResumeOptional (group_idx next_sub_pos : nat)
| ResumeBinderList (frame_idx next_sub_pos : nat).

Inductive MarkerKind : Type :=
| OptionalMarker
| BinderListMarker.

Inductive MarkerCoordinate : Type :=
| OptionalCoordinate (group_idx sub_pos : nat)
| BinderListCoordinate (frame_idx sub_pos : nat).

Record MarkerMetadata : Type := {
  marker_result_src_idx : nat;
  marker_rule_idx : nat;
  marker_coordinate : MarkerCoordinate
}.

Record MarkerTable : Type := {
  marker_id : MarkerMetadata -> nat;
  marker_at : nat -> option MarkerMetadata;
  marker_decode_encode :
    forall metadata, marker_at (marker_id metadata) = Some metadata
}.

Record RuntimeMarker : Type := {
  runtime_marker_kind : MarkerKind;
  runtime_marker_id : nat;
  runtime_outer_bp : nat
}.

Definition encode_optional
  (table : MarkerTable) (result_src_idx rule_idx group_idx sub_pos outer_bp : nat)
  : RuntimeMarker :=
  {| runtime_marker_kind := OptionalMarker;
     runtime_marker_id := marker_id table
       {| marker_result_src_idx := result_src_idx;
          marker_rule_idx := rule_idx;
          marker_coordinate := OptionalCoordinate group_idx sub_pos |};
     runtime_outer_bp := outer_bp |}.

Definition encode_binder_list
  (table : MarkerTable) (result_src_idx rule_idx frame_idx sub_pos outer_bp : nat)
  : RuntimeMarker :=
  {| runtime_marker_kind := BinderListMarker;
     runtime_marker_id := marker_id table
       {| marker_result_src_idx := result_src_idx;
          marker_rule_idx := rule_idx;
          marker_coordinate := BinderListCoordinate frame_idx sub_pos |};
     runtime_outer_bp := outer_bp |}.

Theorem generated_marker_decode_encode_identity :
  forall table metadata,
    marker_at table (marker_id table metadata) = Some metadata.
Proof. intros table metadata. apply marker_decode_encode. Qed.

Theorem generated_marker_ids_are_injective :
  forall table metadata_a metadata_b,
    marker_id table metadata_a = marker_id table metadata_b ->
    metadata_a = metadata_b.
Proof.
  intros table metadata_a metadata_b Hid.
  pose proof (marker_decode_encode table metadata_a) as Ha.
  pose proof (marker_decode_encode table metadata_b) as Hb.
  rewrite Hid in Ha. rewrite Hb in Ha. inversion Ha. reflexivity.
Qed.

Theorem encoded_optional_binder_markers_disjoint :
  forall table result_a rule_a group_idx sub_a bp_a
               result_b rule_b frame_idx sub_b bp_b,
    encode_optional table result_a rule_a group_idx sub_a bp_a <>
    encode_binder_list table result_b rule_b frame_idx sub_b bp_b.
Proof. discriminate. Qed.

Theorem optional_marker_preserves_outer_bp :
  forall table result_src_idx rule_idx group_idx sub_pos outer_bp,
    runtime_outer_bp
      (encode_optional table result_src_idx rule_idx group_idx sub_pos outer_bp)
      = outer_bp.
Proof. reflexivity. Qed.

Theorem binder_marker_preserves_outer_bp :
  forall table result_src_idx rule_idx frame_idx sub_pos outer_bp,
    runtime_outer_bp
      (encode_binder_list table result_src_idx rule_idx frame_idx sub_pos outer_bp)
      = outer_bp.
Proof. reflexivity. Qed.

Record BinderState : Type := {
  state_frame_idx : nat;
  state_sub_pos : nat
}.

Definition enter (continuation : Resume) (caller_stack : list Resume)
  : list Resume := continuation :: caller_stack.

Definition finish (entered_stack : list Resume)
  : option (Resume * list Resume) :=
  match entered_stack with
  | [] => None
  | continuation :: caller_stack => Some (continuation, caller_stack)
  end.

Theorem finish_enter_identity :
  forall continuation caller_stack,
    finish (enter continuation caller_stack)
      = Some (continuation, caller_stack).
Proof. reflexivity. Qed.

Theorem rule_optional_markers_disjoint :
  forall next_pos group_idx next_sub_pos,
    ResumeRule next_pos <> ResumeOptional group_idx next_sub_pos.
Proof. discriminate. Qed.

Theorem rule_binder_markers_disjoint :
  forall next_pos frame_idx next_sub_pos,
    ResumeRule next_pos <> ResumeBinderList frame_idx next_sub_pos.
Proof. discriminate. Qed.

Theorem optional_binder_markers_disjoint :
  forall group_idx optional_sub_pos frame_idx binder_sub_pos,
    ResumeOptional group_idx optional_sub_pos
      <> ResumeBinderList frame_idx binder_sub_pos.
Proof. discriminate. Qed.

Theorem binder_marker_frame_injective :
  forall frame_a frame_b sub_a sub_b,
    ResumeBinderList frame_a sub_a = ResumeBinderList frame_b sub_b ->
    frame_a = frame_b /\ sub_a = sub_b.
Proof.
  intros frame_a frame_b sub_a sub_b H.
  inversion H. auto.
Qed.

Theorem binder_state_frame_injective :
  forall frame_a frame_b sub_a sub_b,
    {| state_frame_idx := frame_a; state_sub_pos := sub_a |}
      = {| state_frame_idx := frame_b; state_sub_pos := sub_b |} ->
    frame_a = frame_b /\ sub_a = sub_b.
Proof.
  intros frame_a frame_b sub_a sub_b H.
  inversion H. auto.
Qed.

Definition binder_child_resume
  (parent_frame_idx child_index child_count : nat) : Resume :=
  ResumeBinderList parent_frame_idx
    (if Nat.eqb (S child_index) child_count then 0 else child_index + 2).

Theorem last_binder_child_resumes_loop_head :
  forall parent_frame_idx child_index,
    binder_child_resume parent_frame_idx child_index (S child_index)
      = ResumeBinderList parent_frame_idx 0.
Proof.
  intros parent_frame_idx child_index.
  unfold binder_child_resume.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem nonlast_binder_child_resumes_next_position :
  forall parent_frame_idx child_index child_count,
    S child_index <> child_count ->
    binder_child_resume parent_frame_idx child_index child_count
      = ResumeBinderList parent_frame_idx (child_index + 2).
Proof.
  intros parent_frame_idx child_index child_count Hneq.
  unfold binder_child_resume.
  apply Nat.eqb_neq in Hneq.
  rewrite Hneq. reflexivity.
Qed.

Theorem nested_finish_restores_exact_parent_marker :
  forall parent_frame parent_sub child_frame child_sub caller_stack,
    finish
      (enter
        (ResumeBinderList child_frame child_sub)
        (enter (ResumeBinderList parent_frame parent_sub) caller_stack))
      = Some
          (ResumeBinderList child_frame child_sub,
           enter (ResumeBinderList parent_frame parent_sub) caller_stack).
Proof. reflexivity. Qed.
