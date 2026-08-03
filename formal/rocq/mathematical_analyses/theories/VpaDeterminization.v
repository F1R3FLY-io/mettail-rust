(*
 * VpaDeterminization: summary-state transition equations.
 *
 * The model verifies the call/gamma/return correlation that ordinary subset
 * construction loses. Deterministic states contain `(S,R)`: a well-matched
 * relation `S` and the currently reachable source set `R`.
 *)

From Stdlib Require Import List.

Section Determinization.

Variables State CallSym ReturnSym InternalSym Stack : Type.
Variable InternalEdge : State -> InternalSym -> State -> Prop.
Variable CallEdge : State -> CallSym -> Stack -> State -> Prop.
Variable ReturnEdge : State -> ReturnSym -> Stack -> State -> Prop.
Variable BottomReturnEdge : State -> ReturnSym -> State -> Prop.

Definition relation := State -> State -> Prop.
Definition state_set := State -> Prop.

Record det_state : Type := DetState {
  summary : relation;
  reachable : state_set
}.

Definition identity_relation : relation := fun left right => left = right.

Definition internal_relation_update
    (before : relation) (symbol : InternalSym) : relation :=
  fun source target =>
    exists middle,
      before source middle /\ InternalEdge middle symbol target.

Definition internal_set_update
    (before : state_set) (symbol : InternalSym) : state_set :=
  fun target =>
    exists source,
      before source /\ InternalEdge source symbol target.

Definition internal_update (before : det_state) (symbol : InternalSym) : det_state :=
  DetState
    (internal_relation_update (summary before) symbol)
    (internal_set_update (reachable before) symbol).

Definition call_set_update (before : state_set) (symbol : CallSym) : state_set :=
  fun target =>
    exists source pushed,
      before source /\ CallEdge source symbol pushed target.

Definition call_update (before : det_state) (symbol : CallSym) : det_state :=
  DetState identity_relation (call_set_update (reachable before) symbol).

(* U relates a caller-side source to a target after one matched call/return
   around the current nested summary. The same `pushed` witness occurs in both
   transition predicates; this is the correlation subset construction loses. *)
Definition return_bridge
    (nested : det_state) (call : CallSym) (ret : ReturnSym) : relation :=
  fun caller_source target =>
    exists call_target nested_end pushed,
      CallEdge caller_source call pushed call_target /\
      summary nested call_target nested_end /\
      ReturnEdge nested_end ret pushed target.

Definition relation_compose (left right : relation) : relation :=
  fun source target =>
    exists middle, left source middle /\ right middle target.

Definition set_image (source : state_set) (edge : relation) : state_set :=
  fun target => exists middle, source middle /\ edge middle target.

Definition matched_return_update
    (caller nested : det_state) (call : CallSym) (ret : ReturnSym) : det_state :=
  let bridge := return_bridge nested call ret in
  DetState
    (relation_compose (summary caller) bridge)
    (set_image (reachable caller) bridge).

Definition bottom_relation_update
    (before : relation) (ret : ReturnSym) : relation :=
  fun source target =>
    exists middle,
      before source middle /\ BottomReturnEdge middle ret target.

Definition bottom_set_update
    (before : state_set) (ret : ReturnSym) : state_set :=
  fun target =>
    exists source,
      before source /\ BottomReturnEdge source ret target.

Definition bottom_return_update (before : det_state) (ret : ReturnSym) : det_state :=
  DetState
    (bottom_relation_update (summary before) ret)
    (bottom_set_update (reachable before) ret).

Theorem matched_return_reachable_iff :
  forall caller nested call ret target,
    reachable (matched_return_update caller nested call ret) target <->
    exists caller_source call_target nested_end pushed,
      reachable caller caller_source /\
      CallEdge caller_source call pushed call_target /\
      summary nested call_target nested_end /\
      ReturnEdge nested_end ret pushed target.
Proof.
  intros caller nested call ret target.
  unfold matched_return_update, set_image, return_bridge; simpl.
  split.
  - intros [caller_source [Hreachable
        [call_target [nested_end [pushed [Hcall [Hsummary Hreturn]]]]]]].
    exists caller_source, call_target, nested_end, pushed. auto.
  - intros [caller_source [call_target [nested_end [pushed
        [Hreachable [Hcall [Hsummary Hreturn]]]]]]].
    exists caller_source. split; [assumption |].
    exists call_target, nested_end, pushed. auto.
Qed.

Theorem matched_return_uses_one_stack_witness :
  forall nested call ret source target,
    return_bridge nested call ret source target ->
    exists call_target nested_end pushed,
      CallEdge source call pushed call_target /\
      summary nested call_target nested_end /\
      ReturnEdge nested_end ret pushed target.
Proof.
  intros nested call ret source target Hbridge.
  exact Hbridge.
Qed.

Theorem cross_gamma_cannot_create_bridge :
  forall nested call ret source target,
    (forall call_target nested_end pushed,
      CallEdge source call pushed call_target ->
      summary nested call_target nested_end ->
      ~ ReturnEdge nested_end ret pushed target) ->
    ~ return_bridge nested call ret source target.
Proof.
  intros nested call ret source target Hcross Hbridge.
  destruct Hbridge as
      [call_target [nested_end [pushed [Hcall [Hsummary Hreturn]]]]].
  eapply (Hcross call_target nested_end pushed); eauto.
Qed.

Theorem bottom_return_is_stack_neutral_relation :
  forall before ret source target,
    summary (bottom_return_update before ret) source target <->
    exists middle,
      summary before source middle /\ BottomReturnEdge middle ret target.
Proof.
  reflexivity.
Qed.

(* Each update is a total mathematical function; totalization in Rust interns
   the resulting predicate pair, including the empty/dead pair. *)
Theorem internal_update_total_function : forall before symbol,
  exists! after, after = internal_update before symbol.
Proof.
  intros. exists (internal_update before symbol). split; [reflexivity |].
  intros candidate ->. reflexivity.
Qed.

Theorem call_update_total_function : forall before symbol,
  exists! after, after = call_update before symbol.
Proof.
  intros. exists (call_update before symbol). split; [reflexivity |].
  intros candidate ->. reflexivity.
Qed.

Theorem matched_return_update_total_function : forall caller nested call ret,
  exists! after, after = matched_return_update caller nested call ret.
Proof.
  intros. exists (matched_return_update caller nested call ret).
  split; [reflexivity |]. intros candidate ->. reflexivity.
Qed.

Print Assumptions matched_return_reachable_iff.
Print Assumptions cross_gamma_cannot_create_bridge.
Print Assumptions matched_return_update_total_function.

End Determinization.
