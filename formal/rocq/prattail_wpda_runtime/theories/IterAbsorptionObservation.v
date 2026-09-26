(** Original emit_iter_eligible_fn query relocation, not a new absorber.

    The Rust worker retains category filtering, all disjointness diagnostics,
    candidate order, pointer-identity conflict check, then label and literal
    rule lookups. Missing literal-rule metadata causes the original match arm
    to be absent; querying that exact table returns None. An owned receipt must
    record this observed None explicitly, never default a missing receipt.

    Here State includes any lookup/construction observations. None exits do not
    hoist later callbacks. Canonical-op ranking is NOT inserted: the actual
    original emitter does not call is_canonical_iter_op.
    This finite model does not prove chain absorption or parser equivalence.
*)
From Stdlib Require Import List Bool.
Import ListNotations.
Module IterAbsorptionObservation.
Section Worker.
Context {State Coordinates Atom Spec : Type}.
Variable label : State -> option Coordinates * State.
Variable literal : Coordinates -> State -> option Atom * State.
Variable construct : Coordinates -> Atom -> State -> Spec * State.
Definition original_arm (conflict : bool) state :=
  if conflict then (None, state) else
  let '(coordinates, next) := label state in
  match coordinates with
  | None => (None, next)
  | Some coordinates =>
      let '(atom, after_literal) := literal coordinates next in
      match atom with
      | None => (None, after_literal)
      | Some atom => let '(spec, final) := construct coordinates atom after_literal in
          (Some spec, final)
      end
  end.
Definition shared_arm := original_arm.
Theorem same_source_worker_preserves_trace : forall conflict state,
  shared_arm conflict state = original_arm conflict state.
Proof. reflexivity. Qed.
Theorem conflict_does_not_read_label_or_literal : forall state,
  shared_arm true state = (None, state).
Proof. reflexivity. Qed.
Theorem missing_label_does_not_read_literal : forall state next,
  label state = (None, next) -> shared_arm false state = (None, next).
Proof. intros; unfold shared_arm, original_arm; now rewrite H. Qed.
Theorem missing_literal_does_not_construct_spec : forall state coordinates next after_literal,
  label state = (Some coordinates, next) ->
  literal coordinates next = (None, after_literal) ->
  shared_arm false state = (None, after_literal).
Proof. intros; unfold shared_arm, original_arm; now rewrite H, H0. Qed.
End Worker.
Section Query.
Context {Key Spec : Type}.
Variable same : Key -> Key -> bool.
Definition query (rows : list (Key * Spec)) key :=
  option_map snd (find (fun row => same (fst row) key) rows).
Theorem original_empty_match_is_explicit_none : forall key, query [] key = None.
Proof. reflexivity. Qed.
Theorem original_first_matching_arm_wins : forall key spec rest,
  same key key = true -> query ((key, spec) :: rest) key = Some spec.
Proof. intros; unfold query; cbn; now rewrite H. Qed.
Definition receipt rows key := (key, query rows key).
Theorem absence_of_arm_is_recorded_not_absence_of_receipt : forall rows key,
  query rows key = None -> receipt rows key = (key, None).
Proof. intros; unfold receipt; now rewrite H. Qed.
End Query.
Print Assumptions same_source_worker_preserves_trace.
Print Assumptions conflict_does_not_read_label_or_literal.
Print Assumptions missing_label_does_not_read_literal.
Print Assumptions missing_literal_does_not_construct_spec.
Print Assumptions original_empty_match_is_explicit_none.
Print Assumptions original_first_matching_arm_wins.
Print Assumptions absence_of_arm_is_recorded_not_absence_of_receipt.
End IterAbsorptionObservation.
