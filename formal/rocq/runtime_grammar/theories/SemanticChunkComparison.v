(** Bounded charged chunks refine the existing Stdlib list comparison.

    Reuse: Stdlib.Lists.List.list_compare and its equality/antisymmetry/
    transitivity theorems; no second lexicographic order is introduced.
    The traversal follows metered_cmp in the sibling
    vinary-requirements/crates/vinary-math-ir/src/canonical.rs: compare equal-sized
    chunks of the common prefix, then compare lengths when one input ends.

    Each chunk is charged BEFORE it is inspected. Charge returns its updated
    state on success or refusal. The wrapper separately charges its entry visit.
    The specification uses list ranges and termination fuel; production may
    borrow slices and use iterative cursors without allocating these ranges.
    Concrete chunk size and ReflectedCodecBudget correspondence are separate
    instantiations. No receipt is encoded or materialized as a comparison key. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Module SemanticChunkComparison.

Section Traversal.
Context {A State : Type}.
Variable compare : A -> A -> comparison.
Variable charge : nat -> State -> bool * State.

Lemma common_prefix_decomposition : forall width (left right : list A),
  list_compare compare left right =
    match list_compare compare (firstn width left) (firstn width right) with
    | Eq => list_compare compare (skipn width left) (skipn width right)
    | decision => decision
    end.
Proof.
  induction width as [|width IH]; intros [|x xs] [|y ys]; cbn; try reflexivity.
  destruct (compare x y); [apply IH | reflexivity | reflexivity].
Qed.

Fixpoint chunks fuel width (left right : list A) state : option comparison * State :=
  match left, right with
  | [], [] => (Some Eq, state)
  | [], _ :: _ => (Some Lt, state)
  | _ :: _, [] => (Some Gt, state)
  | _ :: _, _ :: _ =>
      match fuel with
      | 0 => (None, state)
      | S smaller =>
          let size := Nat.min width (Nat.min (length left) (length right)) in
          let '(allowed, next) := charge size state in
          if allowed then
            match list_compare compare (firstn size left) (firstn size right) with
            | Eq => chunks smaller width (skipn size left) (skipn size right) next
            | decision => (Some decision, next)
            end
          else (None, next)
      end
  end.

Theorem chunks_refine_list_compare : forall fuel width left right state decision final,
  chunks fuel width left right state = (Some decision, final) ->
  decision = list_compare compare left right.
Proof.
  induction fuel as [|fuel IH]; intros width [|x xs] [|y ys] state decision final H;
    cbn [chunks] in H; try (inversion H; reflexivity); try discriminate.
  remember (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) as size in *.
  destruct (charge size state) as [allowed next] eqn:C.
  destruct allowed; [| discriminate].
  destruct (list_compare compare (firstn size (x :: xs)) (firstn size (y :: ys))) eqn:D.
  - rewrite (common_prefix_decomposition size (x :: xs) (y :: ys)), D.
    eapply IH; exact H.
  - inversion H; subst decision.
    now rewrite (common_prefix_decomposition size (x :: xs) (y :: ys)), D.
  - inversion H; subst decision.
    now rewrite (common_prefix_decomposition size (x :: xs) (y :: ys)), D.
Qed.

Theorem chunks_have_sufficient_fuel :
  (forall units state, exists next, charge units state = (true, next)) ->
  forall fuel width left right state,
  0 < width -> Nat.min (length left) (length right) <= fuel ->
  exists decision final, chunks fuel width left right state = (Some decision, final).
Proof.
  intros charges_succeed fuel. induction fuel as [|fuel IH];
    intros width [|x xs] [|y ys] state W B;
    try (eexists; eexists; reflexivity); cbn [length Nat.min] in B; try lia.
  remember (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) as size.
  assert (positive : 0 < size).
  { rewrite Heqsize. apply Nat.min_glb_lt; [exact W | apply Nat.min_glb_lt; cbn; lia]. }
  cbn [chunks]. rewrite <- Heqsize.
  destruct (charges_succeed size state) as [next C]. rewrite C.
  destruct (list_compare compare (firstn size (x :: xs)) (firstn size (y :: ys))) eqn:D;
    try (eexists; eexists; reflexivity).
  apply IH; [exact W |]. rewrite !length_skipn, Nat.sub_min_distr_r.
  cbn [length Nat.min]. lia.
Qed.

Definition metered fuel width left right state :=
  let '(allowed, next) := charge 1 state in
  if allowed then chunks fuel width left right next else (None, next).

Theorem metered_has_sufficient_fuel :
  (forall units state, exists next, charge units state = (true, next)) ->
  forall width left right state, 0 < width ->
  exists decision final,
    metered (Nat.min (length left) (length right)) width left right state =
      (Some decision, final).
Proof.
  intros charges_succeed width left right state W. unfold metered.
  destruct (charges_succeed 1 state) as [next C]. rewrite C.
  apply chunks_have_sufficient_fuel; auto.
Qed.

Theorem metered_refines_list_compare : forall fuel width left right state decision final,
  metered fuel width left right state = (Some decision, final) ->
  decision = list_compare compare left right.
Proof.
  intros fuel width left right state decision final H. unfold metered in H.
  destruct (charge 1 state) as [allowed next] eqn:C.
  destruct allowed; [eapply chunks_refine_list_compare; exact H | discriminate].
Qed.

Theorem refused_entry_preserves_updated_state : forall fuel width left right state next,
  charge 1 state = (false, next) -> metered fuel width left right state = (None, next).
Proof. intros. unfold metered. now rewrite H. Qed.

Theorem refused_chunk_preserves_updated_state : forall fuel width x xs y ys state next,
  charge (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) state =
    (false, next) ->
  chunks (S fuel) width (x :: xs) (y :: ys) state = (None, next).
Proof. intros. cbn [chunks]. now rewrite H. Qed.

Theorem chunks_preserve_state_property : forall (P : State -> Prop),
  (forall units before allowed after,
    P before -> charge units before = (allowed, after) -> P after) ->
  forall fuel width left right state,
    P state -> P (snd (chunks fuel width left right state)).
Proof.
  intros P preserves fuel. induction fuel as [|fuel IH];
    intros width [|x xs] [|y ys] state initial;
    cbn [chunks snd]; try exact initial.
  destruct (charge (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) state)
    as [allowed next] eqn:C.
  assert (next_property : P next) by (eapply preserves; [exact initial | exact C]).
  destruct allowed; [| exact next_property].
  destruct (list_compare compare
    (firstn (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) (x :: xs))
    (firstn (Nat.min width (Nat.min (length (x :: xs)) (length (y :: ys)))) (y :: ys)));
    [apply IH | |]; exact next_property.
Qed.

Theorem metered_preserves_state_property : forall (P : State -> Prop),
  (forall units before allowed after,
    P before -> charge units before = (allowed, after) -> P after) ->
  forall fuel width left right state,
    P state -> P (snd (metered fuel width left right state)).
Proof.
  intros P preserves fuel width left right state initial. unfold metered.
  destruct (charge 1 state) as [allowed next] eqn:C.
  assert (next_property : P next) by (eapply preserves; [exact initial | exact C]).
  destruct allowed; [apply chunks_preserve_state_property; assumption | exact next_property].
Qed.

End Traversal.
End SemanticChunkComparison.

Print Assumptions SemanticChunkComparison.common_prefix_decomposition.
Print Assumptions SemanticChunkComparison.chunks_refine_list_compare.
Print Assumptions SemanticChunkComparison.chunks_have_sufficient_fuel.
Print Assumptions SemanticChunkComparison.metered_refines_list_compare.
Print Assumptions SemanticChunkComparison.metered_has_sufficient_fuel.
Print Assumptions SemanticChunkComparison.refused_entry_preserves_updated_state.
Print Assumptions SemanticChunkComparison.refused_chunk_preserves_updated_state.
Print Assumptions SemanticChunkComparison.chunks_preserve_state_property.
Print Assumptions SemanticChunkComparison.metered_preserves_state_property.
