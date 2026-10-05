(** * Partitioning generated iterative-drop extraction by constructor

    The executable drop machine already owns a heap worklist and pushes each
    extracted child in its original order.  This model covers only the proposed
    code-generation refactoring: move each constructor arm into a separately
    called helper while leaving its child extraction body unchanged.  The
    worklist remains LIFO, so its next tasks are the reversed push sequence.

    [frame_units] is an abstract upper bound for one compiled helper.  The
    bound theorem is conditional on every helper satisfying that bound; Rocq
    cannot establish rustc's physical frame size.  Generated-code inspection
    and a deliberately small-stack execution test remain independent gates.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Module IterativeDropDispatch.

Record Arm := arm {
  extracted_children : list nat;
  frame_units : nat
}.

(** The old match and the new per-arm helper use the same ordered extraction
    recipe.  The caller's existing worklist tail is never reordered. *)
Definition monolithic_step (arms : list Arm) (tag : nat) (stack : list nat)
    : option (list nat) :=
  match nth_error arms tag with
  | Some selected => Some (rev (extracted_children selected) ++ stack)
  | None => None
  end.

Definition split_step (arms : list Arm) (tag : nat) (stack : list nat)
    : option (list nat) :=
  match nth_error (map extracted_children arms) tag with
  | Some children => Some (rev children ++ stack)
  | None => None
  end.

Theorem split_preserves_exact_push_order : forall arms tag stack,
  split_step arms tag stack = monolithic_step arms tag stack.
Proof.
  induction arms as [|first rest IH]; intros [|tag] stack; simpl;
    try reflexivity; exact (IH tag stack).
Qed.

Theorem split_preserves_invalid_tag_refusal : forall arms tag stack,
  length arms <= tag -> split_step arms tag stack = None.
Proof.
  induction arms as [|first rest IH]; intros [|tag] stack Bound;
    simpl in *; try lia; try reflexivity.
  apply IH. lia.
Qed.

Theorem split_preserves_every_existing_tail : forall arms tag tail result,
  monolithic_step arms tag tail = Some result ->
  split_step arms tag tail = Some result.
Proof.
  intros arms tag tail result Old.
  now rewrite split_preserves_exact_push_order.
Qed.

(** Helper calls are sequential, never nested by another helper; traversal
    still occurs only when the outer iterative drop loop pops the next task.
    Therefore the selected helper frame, rather than the sum over the full
    constructor roster, is the relevant local source-level bound. *)
Definition selected_frame (dispatcher_frame : nat) (arms : list Arm)
    (tag : nat) : nat :=
  match nth_error arms tag with
  | Some selected => dispatcher_frame + frame_units selected
  | None => dispatcher_frame
  end.

Theorem selected_helper_frame_is_roster_independent :
  forall arms tag dispatcher_frame helper_ceiling,
    (forall selected, In selected arms ->
       frame_units selected <= helper_ceiling) ->
    selected_frame dispatcher_frame arms tag <=
      dispatcher_frame + helper_ceiling.
Proof.
  intros arms tag dispatcher_frame helper_ceiling Bounded.
  unfold selected_frame.
  destruct (nth_error arms tag) as [selected|] eqn:Found; [|lia].
  apply nth_error_In in Found.
  specialize (Bounded selected Found).
  lia.
Qed.

Print Assumptions split_preserves_exact_push_order.
Print Assumptions split_preserves_invalid_tag_refusal.
Print Assumptions selected_helper_frame_is_roster_independent.

End IterativeDropDispatch.
