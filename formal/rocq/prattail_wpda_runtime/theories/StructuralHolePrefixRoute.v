(** * Structural holes at category-leading prefix sites

    A structural FLT hole carries a category but no lexer token. Token-first
    routing therefore cannot be the only way to enter a category-leading rule
    such as [PLiteral : Scalar -> Pattern]. The owned WPDA may additionally
    route through an authored leading-category or transparent projection row
    when the hole's category is that row's source or reaches that source by the
    existing category-reachability relation. The authored row roster is
    independent of lexical FIRST buckets, including empty or token-gated ones.
    Leading rows additionally respect their existing binding-power admission.
    No hole offers no such route.

    This is a local routing model, not a proof of the Rust GSS/SPPF engine.
    Rust correspondence must check the authored row order, exact hole-edge
    admission, transition-builder weights and continuations, and that normal
    token dispatch is unchanged. *)
From Stdlib Require Import List Bool Arith.
Import ListNotations.

Module StructuralHolePrefixRoute.

Inductive Kind := Leading | Projection.
Record Row := {
  rule_id : nat;
  source_category : nat;
  kind : Kind;
  leading_bp_admitted : bool;
  authored_weight : nat;
  continuation : nat
}.

Definition row_gate (row : Row) : bool :=
  match kind row with
  | Leading => leading_bp_admitted row
  | Projection => true
  end.

Definition eligible (hole : option (option nat))
    (reachable : nat -> nat -> bool) (row : Row) : bool :=
  row_gate row && match hole with
  | None => false
  | Some None => true
  | Some (Some category) =>
      Nat.eqb category (source_category row) ||
      reachable category (source_category row)
  end.

Definition route (rows : list Row) hole reachable : list Row :=
  filter (eligible hole reachable) rows.

Theorem no_hole_adds_no_category_route : forall rows reachable,
  route rows None reachable = [].
Proof.
  intros; unfold route; induction rows; simpl; auto.
  unfold eligible; simpl; rewrite Bool.andb_false_r; exact IHrows.
Qed.

Theorem eligible_route_is_sound : forall rows hole reachable row,
  In row (route rows hole reachable) ->
  In row rows /\ eligible hole reachable row = true.
Proof.
  intros; unfold route in H.
  apply filter_In in H; exact H.
Qed.

Theorem every_eligible_authored_row_survives : forall rows hole reachable row,
  In row rows -> eligible hole reachable row = true ->
  In row (route rows hole reachable).
Proof.
  intros; unfold route; apply filter_In; auto.
Qed.

Theorem exact_typed_hole_enters_its_source : forall rows reachable row,
  In row rows -> row_gate row = true ->
  In row (route rows (Some (Some (source_category row))) reachable).
Proof.
  intros; apply every_eligible_authored_row_survives; auto.
  unfold eligible; rewrite H0, Nat.eqb_refl; reflexivity.
Qed.

Theorem unrelated_typed_hole_cannot_enter : forall rows reachable row category,
  category <> source_category row ->
  reachable category (source_category row) = false ->
  ~ In row (route rows (Some (Some category)) reachable).
Proof.
  intros rows reachable row category distinct no_path admitted.
  apply eligible_route_is_sound in admitted as [_ H].
  unfold eligible in H.
  apply Nat.eqb_neq in distinct; rewrite distinct, no_path in H.
  now rewrite Bool.andb_false_r in H.
Qed.

Theorem untyped_hole_retains_exactly_bp_admitted_rows : forall rows reachable,
  route rows (Some None) reachable = filter row_gate rows.
Proof.
  intros; induction rows as [|row rows IH]; [reflexivity|].
  unfold route in *; simpl.
  replace (eligible (Some None) reachable row) with (row_gate row)
    by (unfold eligible; now rewrite Bool.andb_true_r).
  now rewrite IH.
Qed.

Theorem routed_row_preserves_authored_weight_and_continuation :
  forall rows hole reachable row,
  In row (route rows hole reachable) ->
  exists original, In original rows /\
    authored_weight row = authored_weight original /\
    continuation row = continuation original /\ row = original.
Proof.
  intros; exists row; split; [apply eligible_route_is_sound in H; exact (proj1 H)|].
  repeat split; reflexivity.
Qed.

Inductive Input (Token : Type) := TokenInput (token : Token) | HoleInput (category : option nat).

Definition dispatch {Token : Type} (lexical_route : Token -> list Row)
    (rows : list Row) (reachable : nat -> nat -> bool)
    (input : Input Token) : list Row :=
  match input with
  | TokenInput _ token => lexical_route token
  | HoleInput _ category => route rows (Some category) reachable
  end.

Theorem ordinary_token_dispatch_is_unchanged :
  forall (Token : Type) (lexical_route : Token -> list Row) rows reachable token,
  dispatch lexical_route rows reachable (TokenInput Token token) = lexical_route token.
Proof. reflexivity. Qed.

End StructuralHolePrefixRoute.
