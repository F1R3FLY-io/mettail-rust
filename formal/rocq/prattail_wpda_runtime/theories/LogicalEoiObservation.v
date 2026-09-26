(** Source-owned logical end-of-input (EOI) observation, task 8514.

    This is predicate relocation/substitution, not a parser acceptance proof.
    RuntimeModel.runtime_logical_eoi remains the static default specification.
    Rust must move the original WpdaWalker::is_logical_eoi body unchanged into
    WpdaTokenSource::is_logical_eoi (tokens -> self), then delegate from the
    walker. In particular, retain the original short-circuit order and repeated
    len reads. TransitionBodyRelocation covers the complete observation state.

    The core predicate below is the original ForestBuilder root-boundary test:
      at_end := position.offset == input_end;
      after_eof := Some(position.offset) == input_end.checked_add(1)
                   && lexemes.node(position).is_some();
      position.is_balanced() && (at_end || after_eof).
    LexicalLattice will own this body; ForestBuilder and RuntimeLexicalSession
    will delegate to it. The lookup uses the full offset/context position and
    is evaluated BEFORE the final balance test, just as in the original body.
    No canonicalization, topology alias, token peek, or new lexer is involved.

    usize_max abstracts the target machine's maximum usize. Arithmetic inputs
    represent usize values (at most usize_max); checked_successor models only
    checked_add(1), not unbounded machine arithmetic. At input_end, a balanced
    position needs no existing node. Only the post-EOF boundary needs a node.
    Unknown adapter node IDs are a separate failed full-position lookup.

    Existing category/start/completed-root enumeration, root coverage, sorting,
    deduplication and NoParse behavior remain outside this boundary predicate.
    The final laws retain a supplied independent coverage obligation; they do
    not assert that reaching logical EOI is sufficient for parser acceptance.
*)
From Stdlib Require Import List Arith Bool Lia.
From PrattailWpdaRuntime Require Import RuntimeModel TransitionBodyRelocation.
Import ListNotations.

Module LogicalEoiObservation.

Definition default_source_eoi := runtime_logical_eoi.

Theorem static_default_is_original : forall space len eof pos peek,
    default_source_eoi space len eof pos peek =
    runtime_logical_eoi space len eof pos peek.
Proof. reflexivity. Qed.

Theorem default_nonlinear_keeps_exact_sentinel : forall len eof pos peek,
    default_source_eoi NonlinearNodePositions len eof pos peek = (pos =? eof).
Proof. apply nonlinear_logical_eoi_is_exact_eof_node. Qed.

(** Input/Output may include callback state and trace: forwarding must neither
    replay observations nor silently assume source methods are pure. *)
Theorem default_body_preserves_observations : forall Input Output
    (original : Input -> Output) input,
    shared_transition original input = original input.
Proof. apply original_body_is_called_unchanged. Qed.

Definition walker_eoi {Position : Type}
    (source_predicate : Position -> bool) position := source_predicate position.

Theorem walker_uses_actual_source_predicate : forall Position
    (source_predicate : Position -> bool) position,
    walker_eoi source_predicate position = source_predicate position.
Proof. reflexivity. Qed.

Record FullPosition := { offset : nat; context : nat }.

Definition checked_successor (usize_max input_end : nat) : option nat :=
  if input_end <? usize_max then Some (S input_end) else None.

Definition at_checked_successor (usize_max input_end pos : nat) : bool :=
  match checked_successor usize_max input_end with
  | Some finish => pos =? finish
  | None => false
  end.

(** The second component is the exact ordered list of node-lookup arguments. *)
Definition core_boundary_observation
    (usize_max input_end : nat) (node_exists : FullPosition -> bool)
    (position : FullPosition) : bool * list FullPosition :=
  let at_end := offset position =? input_end in
  let after_eof :=
    if at_checked_successor usize_max input_end (offset position)
    then (node_exists position, [position])
    else (false, []) in
  ((context position =? 0) && (at_end || fst after_eof), snd after_eof).

Definition core_boundary usize_max input_end node_exists position :=
  fst (core_boundary_observation usize_max input_end node_exists position).

Theorem checked_successor_does_not_wrap : forall usize_max,
    checked_successor usize_max usize_max = None.
Proof. intros; unfold checked_successor; now rewrite Nat.ltb_irrefl. Qed.

Theorem checked_successor_when_representable : forall usize_max input_end,
    input_end < usize_max ->
    checked_successor usize_max input_end = Some (S input_end).
Proof.
  intros usize_max input_end Hlt; unfold checked_successor.
  apply Nat.ltb_lt in Hlt; now rewrite Hlt.
Qed.

Theorem balanced_input_end_needs_no_node : forall usize_max input_end nodes,
    core_boundary usize_max input_end nodes
      {| offset := input_end; context := 0 |} = true.
Proof.
  intros; unfold core_boundary, core_boundary_observation; simpl.
  rewrite Nat.eqb_refl.
  destruct (at_checked_successor usize_max input_end input_end); reflexivity.
Qed.

Theorem post_eof_uses_full_position : forall usize_max input_end nodes position,
    at_checked_successor usize_max input_end (offset position) = true ->
    core_boundary_observation usize_max input_end nodes position =
      ((context position =? 0) &&
        ((offset position =? input_end) || nodes position), [position]).
Proof.
  intros usize_max input_end nodes position Hafter.
  unfold core_boundary_observation; now rewrite Hafter.
Qed.

Theorem post_eof_requires_balance_and_existing_node :
    forall usize_max input_end nodes position,
    offset position <> input_end ->
    at_checked_successor usize_max input_end (offset position) = true ->
    core_boundary_observation usize_max input_end nodes position =
      ((context position =? 0) && nodes position, [position]).
Proof.
  intros usize_max input_end nodes position Hneq Hafter.
  rewrite post_eof_uses_full_position by exact Hafter.
  apply Nat.eqb_neq in Hneq; now rewrite Hneq.
Qed.

Theorem missing_node_away_from_input_end_is_not_eoi :
    forall usize_max input_end nodes position,
    offset position <> input_end -> nodes position = false ->
    core_boundary usize_max input_end nodes position = false.
Proof.
  intros usize_max input_end nodes position Hneq Hmissing.
  unfold core_boundary, core_boundary_observation.
  apply Nat.eqb_neq in Hneq; rewrite Hneq.
  destruct (at_checked_successor usize_max input_end (offset position));
    simpl; rewrite ?Hmissing; apply andb_false_r.
Qed.

Theorem unbalanced_position_is_not_eoi :
    forall usize_max input_end nodes position,
    context position <> 0 ->
    core_boundary usize_max input_end nodes position = false.
Proof.
  intros usize_max input_end nodes position Hunbalanced.
  unfold core_boundary, core_boundary_observation.
  apply Nat.eqb_neq in Hunbalanced; rewrite Hunbalanced; reflexivity.
Qed.

Theorem overflow_disables_only_post_eof : forall usize_max nodes position,
    core_boundary_observation usize_max usize_max nodes position =
      ((context position =? 0) && (offset position =? usize_max), []).
Proof.
  intros; unfold core_boundary_observation, at_checked_successor.
  rewrite checked_successor_does_not_wrap; simpl.
  now rewrite orb_false_r.
Qed.

Theorem equal_offsets_do_not_erase_mode_context : forall usize_max input_end nodes,
    core_boundary usize_max input_end nodes
      {| offset := input_end; context := 0 |} = true /\
    core_boundary usize_max input_end nodes
      {| offset := input_end; context := 1 |} = false.
Proof.
  intros; split.
  - apply balanced_input_end_needs_no_node.
  - apply unbalanced_position_is_not_eoi; discriminate.
Qed.

Definition adapter_eoi (positions : nat -> option FullPosition)
    (source_predicate : FullPosition -> bool) node_id :=
  match positions node_id with
  | Some position => source_predicate position
  | None => false
  end.

Theorem unknown_adapter_node_is_not_eoi : forall positions predicate node_id,
    positions node_id = None -> adapter_eoi positions predicate node_id = false.
Proof. intros; unfold adapter_eoi; now rewrite H. Qed.

Theorem known_adapter_node_uses_exact_position :
    forall positions predicate node_id position,
    positions node_id = Some position ->
    adapter_eoi positions predicate node_id = predicate position.
Proof. intros; unfold adapter_eoi; now rewrite H. Qed.

Definition boundary_with_coverage {Position : Type}
    (predicate coverage : Position -> bool) position :=
  walker_eoi predicate position && coverage position.

Theorem predicate_substitution_keeps_coverage : forall Position
    (predicate coverage : Position -> bool) position,
    boundary_with_coverage predicate coverage position = true ->
    predicate position = true /\ coverage position = true.
Proof. intros; now apply andb_true_iff in H. Qed.

Theorem logical_eoi_alone_does_not_accept : forall Position
    (predicate coverage : Position -> bool) position,
    coverage position = false ->
    boundary_with_coverage predicate coverage position = false.
Proof. intros; unfold boundary_with_coverage; rewrite H; apply andb_false_r. Qed.

Print Assumptions static_default_is_original.
Print Assumptions default_nonlinear_keeps_exact_sentinel.
Print Assumptions default_body_preserves_observations.
Print Assumptions walker_uses_actual_source_predicate.
Print Assumptions checked_successor_does_not_wrap.
Print Assumptions checked_successor_when_representable.
Print Assumptions balanced_input_end_needs_no_node.
Print Assumptions post_eof_uses_full_position.
Print Assumptions post_eof_requires_balance_and_existing_node.
Print Assumptions missing_node_away_from_input_end_is_not_eoi.
Print Assumptions unbalanced_position_is_not_eoi.
Print Assumptions overflow_disables_only_post_eof.
Print Assumptions equal_offsets_do_not_erase_mode_context.
Print Assumptions unknown_adapter_node_is_not_eoi.
Print Assumptions known_adapter_node_uses_exact_position.
Print Assumptions predicate_substitution_keeps_coverage.
Print Assumptions logical_eoi_alone_does_not_accept.

End LogicalEoiObservation.
