(** Structural category edges, not lexer tokens (task 8514).

    Source: grammar-core/runtime.rs complete_template_hole and the
    ForestNode::Nonterminal realization arm. Preserve canonical full-position
    lookup, hole lookup before category lookup, category existence, optional
    exact category equality, position.at(end) before canonicalization, and the
    original (category,start,end) completion key. A duplicate completion does
    not advance waiters again. A new completion publishes the actual hole ID
    and requested category; an untyped hole is not an unknown category.

    This model specifies the adapter boundary, not a second parser, a GSS
    simulation, or k-best completeness. Rust still owes a real category-forest
    alternative consumed by every realization family. A witness-only cache or
    an invented token/production is NOT an implementation of this boundary.
    Existing forest limits, semantic result budgets, root coverage and normal
    production alternatives stay independent. A structural template metavariable
    is not a guest-language native variable: the latter's admission bit must
    not affect this edge. Canonicalization is the existing worker, not offset
    sorting and not an assumed context-preserving function.
*)
From Stdlib Require Import List Arith Bool.
From PrattailWpdaRuntime Require Import OwnedLexicalAdapter TransitionBodyRelocation.
Import ListNotations.

Module StructuralHoleBridge.
Definition Position := OwnedLexicalAdapter.Position.
Definition offset := OwnedLexicalAdapter.offset.
Definition context := OwnedLexicalAdapter.context.

Definition position_at (position : Position) finish : Position :=
  {| OwnedLexicalAdapter.offset := finish;
     OwnedLexicalAdapter.context := context position |}.

Record Hole := { hole_id : nat; hole_category : option nat; hole_end : nat }.
Record Edge := {
  edge_id : nat; edge_category : nat;
  edge_start : Position; edge_end : Position
}.
Definition Key := (nat * Position * Position)%type.
Definition edge_key edge : Key :=
  (edge_category edge, edge_start edge, edge_end edge).

Inductive Observation :=
| CanonicalStart (position : Position)
| HoleLookup (byte : nat)
| CategoryLookup (category : nat)
| CanonicalEnd (position : Position).

Definition category_mismatch expected requested :=
  match expected with None => false | Some category => negb (category =? requested) end.

Definition observe_edge (canonical : Position -> Position)
    (holes : nat -> option Hole) (categories : nat -> option bool)
    requested position : option Edge * list Observation :=
  let start := canonical position in
  let prefix := [CanonicalStart position; HoleLookup (offset start)] in
  match holes (offset start) with
  | None => (None, prefix)
  | Some hole =>
      let trace := prefix ++ [CategoryLookup requested] in
      match categories requested with
      | None => (None, trace)
      | Some _ =>
          if category_mismatch (hole_category hole) requested
          then (None, trace)
          else
            let raw_end := position_at start (hole_end hole) in
            (Some {| edge_id := hole_id hole; edge_category := requested;
                     edge_start := start; edge_end := canonical raw_end |},
             trace ++ [CanonicalEnd raw_end])
      end
  end.

Theorem position_at_keeps_complete_context : forall position finish,
  context (position_at position finish) = context position.
Proof. reflexivity. Qed.

Theorem absent_hole_does_not_observe_category : forall canonical holes categories requested position,
  holes (offset (canonical position)) = None ->
  observe_edge canonical holes categories requested position =
    (None, [CanonicalStart position; HoleLookup (offset (canonical position))]).
Proof. intros; unfold observe_edge; now rewrite H. Qed.

Theorem unknown_category_does_not_observe_endpoint : forall canonical holes categories requested position hole,
  holes (offset (canonical position)) = Some hole -> categories requested = None ->
  observe_edge canonical holes categories requested position =
    (None, [CanonicalStart position; HoleLookup (offset (canonical position)); CategoryLookup requested]).
Proof. intros; unfold observe_edge; now rewrite H, H0. Qed.

Theorem native_variable_authority_cannot_change_structural_hole_edge :
  forall canonical holes categories requested position authority,
  observe_edge canonical holes (fun category =>
    if category =? requested then Some authority else categories category)
    requested position =
  observe_edge canonical holes (fun category =>
    if category =? requested then Some false else categories category)
    requested position.
Proof.
  intros; unfold observe_edge.
  destruct (holes (offset (canonical position))) as [hole|]; [|reflexivity].
  now rewrite Nat.eqb_refl.
Qed.

Theorem wrong_declared_category_is_rejected : forall canonical holes categories requested position hole expected authority,
  holes (offset (canonical position)) = Some hole -> categories requested = Some authority ->
  hole_category hole = Some expected -> expected <> requested ->
  fst (observe_edge canonical holes categories requested position) = None.
Proof.
  intros; unfold observe_edge; rewrite H, H0; simpl.
  unfold category_mismatch; rewrite H1.
  apply Nat.eqb_neq in H2; now rewrite H2.
Qed.

Theorem untyped_hole_uses_requested_category_and_exact_endpoint :
  forall canonical holes categories requested position hole authority,
  holes (offset (canonical position)) = Some hole -> categories requested = Some authority ->
  hole_category hole = None ->
  fst (observe_edge canonical holes categories requested position) =
    Some {| edge_id := hole_id hole; edge_category := requested;
            edge_start := canonical position;
            edge_end := canonical (position_at (canonical position) (hole_end hole)) |}.
Proof.
  intros; unfold observe_edge; rewrite H, H0; simpl.
  unfold category_mismatch; now rewrite H1.
Qed.

Theorem typed_hole_preserves_exact_requested_category :
  forall canonical holes categories requested position hole authority,
  holes (offset (canonical position)) = Some hole -> categories requested = Some authority ->
  hole_category hole = Some requested ->
  fst (observe_edge canonical holes categories requested position) =
    Some {| edge_id := hole_id hole; edge_category := requested;
            edge_start := canonical position;
            edge_end := canonical (position_at (canonical position) (hole_end hole)) |}.
Proof.
  intros; unfold observe_edge; rewrite H, H0; simpl.
  unfold category_mismatch; rewrite H1, Nat.eqb_refl; reflexivity.
Qed.

Inductive Completion := NoEdge | AlreadyCompleted | Publish (edge : Edge).
Definition complete_once (seen : Key -> bool) edge :=
  match edge with
  | None => NoEdge
  | Some value => if seen (edge_key value) then AlreadyCompleted else Publish value
  end.

Theorem duplicate_key_does_not_publish_again : forall seen edge,
  seen (edge_key edge) = true -> complete_once seen (Some edge) = AlreadyCompleted.
Proof. intros; unfold complete_once; now rewrite H. Qed.

Theorem fresh_key_retains_full_edge : forall seen edge,
  seen (edge_key edge) = false -> complete_once seen (Some edge) = Publish edge.
Proof. intros; unfold complete_once; now rewrite H. Qed.

(** Dense IDs may replace full positions only with an inverse on both ends. *)
Definition encoded_key (encode : Position -> nat) edge :=
  (edge_category edge, encode (edge_start edge), encode (edge_end edge)).
Theorem dense_key_does_not_merge_full_positions : forall encode decode left right,
  (forall position, decode (encode position) = position) ->
  encoded_key encode left = encoded_key encode right -> edge_key left = edge_key right.
Proof.
  intros encode decode left right Hinverse Hequal.
  unfold encoded_key in Hequal; inversion Hequal.
  assert (edge_start left = edge_start right) as Hstart.
  { rewrite <- (Hinverse (edge_start left)), <- (Hinverse (edge_start right)); congruence. }
  assert (edge_end left = edge_end right) as Hend.
  { rewrite <- (Hinverse (edge_end left)), <- (Hinverse (edge_end right)); congruence. }
  unfold edge_key; congruence.
Qed.

Inductive Alternative := StructuralHole (id category : nat) | Production (rule : nat).
Definition alternatives hole productions :=
  match hole with
  | Some edge => StructuralHole (edge_id edge) (edge_category edge) :: productions
  | None => productions
  end.
Theorem hole_precedes_unchanged_ordinary_alternatives : forall edge productions,
  alternatives (Some edge) productions =
    StructuralHole (edge_id edge) (edge_category edge) :: productions.
Proof. reflexivity. Qed.

(** The only semantics of this leaf is the existing structural-hole constructor.
    No decoder, action lookup, host call, rule rank, or source-text scan occurs. *)
Definition realize_hole {Value : Type} (construct : nat -> nat -> Value) edge :=
  construct (edge_id edge) (edge_category edge).
Theorem realization_preserves_hole_identity_and_category : forall Value construct edge,
  @realize_hole Value construct edge = construct (edge_id edge) (edge_category edge).
Proof. reflexivity. Qed.

(** Completion seeds the EXISTING category continuation, not a new recognizer.
    Rust supplies cgll_pure_descend unchanged: actual-category CategoryEntry,
    exact end, completed category Symbol as w0, original Pratt floor. Its GSS
    create/replay/pop/return and ordinary InfixLoop remain the only scheduler.
    The callback includes its complete mutable state, including forest/GSS.
    This law is conditional on that exact callback and supplied observations;
    it does not assert arbitrary node construction or frame selection lawful. *)
Section Seed.
Context {Symbol State Output : Type}.
Record Seed := {
  seed_category : nat; seed_end : Position; seed_floor : nat;
  seed_symbol : Symbol
}.
Definition category_seed edge floor symbol :=
  {| seed_category := edge_category edge; seed_end := edge_end edge;
     seed_floor := floor; seed_symbol := symbol |}.
Definition resume_hole
    (original_descend : Seed -> State -> Output) edge floor symbol state :=
  shared_transition (fun input => original_descend (fst input) (snd input))
    (category_seed edge floor symbol, state).
Theorem hole_seed_calls_original_descent_once : forall descend edge floor symbol state,
  resume_hole descend edge floor symbol state =
    descend (category_seed edge floor symbol) state.
Proof. reflexivity. Qed.
Theorem hole_seed_preserves_pratt_floor : forall edge floor symbol,
  seed_floor (category_seed edge floor symbol) = floor.
Proof. reflexivity. Qed.
Theorem hole_seed_preserves_actual_category_endpoint_and_symbol : forall edge floor symbol,
  (seed_category (category_seed edge floor symbol),
   seed_end (category_seed edge floor symbol),
   seed_symbol (category_seed edge floor symbol)) =
  (edge_category edge, edge_end edge, symbol).
Proof. reflexivity. Qed.
End Seed.

Print Assumptions position_at_keeps_complete_context.
Print Assumptions absent_hole_does_not_observe_category.
Print Assumptions unknown_category_does_not_observe_endpoint.
Print Assumptions native_variable_authority_cannot_change_structural_hole_edge.
Print Assumptions wrong_declared_category_is_rejected.
Print Assumptions untyped_hole_uses_requested_category_and_exact_endpoint.
Print Assumptions typed_hole_preserves_exact_requested_category.
Print Assumptions duplicate_key_does_not_publish_again.
Print Assumptions fresh_key_retains_full_edge.
Print Assumptions dense_key_does_not_merge_full_positions.
Print Assumptions hole_precedes_unchanged_ordinary_alternatives.
Print Assumptions realization_preserves_hole_identity_and_category.
Print Assumptions hole_seed_calls_original_descent_once.
Print Assumptions hole_seed_preserves_pratt_floor.
Print Assumptions hole_seed_preserves_actual_category_endpoint_and_symbol.
End StructuralHoleBridge.
