(** * Explicit, bounded structural display projection

    This is a specification of the *display* relation, not a conversion of
    private names to public strings. Binary [Node] represents an ordered
    constructor spine; an n-ary constructor is encoded by its ordered child
    spine. The executable implementation uses an explicit work stack.

    [render_tree] is the mathematical catamorphism. Its tokens distinguish
    constructor symbols from quoted public literal payloads, so a literal
    cannot impersonate a constructor. UTF-8 and escaping are obligations of
    the checked String carrier codec, modeled separately by
    ExactStringCarrierProjection. Numeric identities stand for committed
    fingerprints and checked constructor IDs.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Module DerivedSExprProjection.

Inductive Tree :=
| PublicLiteral (sort : nat) (payload : list nat)
| PrivateName (payload : list nat)
| Node (constructor : nat) (lhs rhs : Tree).

Inductive Token :=
| Open | Close | Separator | Symbol (id : nat)
| QuotedLiteral (sort : nat) (payload : list nat).

Fixpoint safe_tree (term : Tree) : bool :=
  match term with
  | PublicLiteral _ _ => true
  | PrivateName _ => false
  | Node _ lhs rhs => safe_tree lhs && safe_tree rhs
  end.

Fixpoint render_tree (term : Tree) : option (list Token) :=
  match term with
  | PublicLiteral sort payload => Some [QuotedLiteral sort payload]
  | PrivateName _ => None
  | Node constructor lhs rhs =>
      match render_tree lhs, render_tree rhs with
      | Some l, Some r =>
          Some ([Open; Symbol constructor] ++ l ++ [Separator] ++ r ++ [Close])
      | _, _ => None
      end
  end.

Record Signature := signature {
  guest_owner : nat;
  guest_sort : nat;
  host_profile : nat;
  host_string_sort : nat
}.

Inductive DisplayValue :=
| DisplayString (profile sort : nat) (tokens : list Token).

Definition project (sig : Signature) (selected bridge : bool)
           (owner sort : nat) (term : Tree) (token_limit : nat)
           : option DisplayValue :=
  if selected && bridge && Nat.eqb owner (guest_owner sig) &&
     Nat.eqb sort (guest_sort sig) then
    match render_tree term with
    | Some tokens =>
        if Nat.leb (length tokens) token_limit
        then Some (DisplayString (host_profile sig) (host_string_sort sig) tokens)
        else None
    | None => None
    end
  else None.

Theorem render_requires_public_tree : forall term tokens,
  render_tree term = Some tokens -> safe_tree term = true.
Proof.
  induction term as [sort payload|payload|constructor lhs IHl rhs IHr];
    intros tokens Render; simpl in *.
  - reflexivity.
  - discriminate.
  - destruct (render_tree lhs) as [l|] eqn:Left;
      destruct (render_tree rhs) as [r|] eqn:Right;
      try discriminate.
    rewrite (IHl _ eq_refl), (IHr _ eq_refl). reflexivity.
Qed.

Theorem projection_requires_selection : forall sig bridge owner sort term limit,
  project sig false bridge owner sort term limit = None.
Proof. intros. reflexivity. Qed.

Theorem projection_requires_bridge : forall sig selected owner sort term limit,
  project sig selected false owner sort term limit = None.
Proof. intros. now destruct selected. Qed.

Theorem projection_is_typed_bounded_and_public :
  forall sig selected bridge owner sort term limit value,
    project sig selected bridge owner sort term limit = Some value ->
    exists tokens,
      value = DisplayString (host_profile sig) (host_string_sort sig) tokens /\
      owner = guest_owner sig /\
      sort = guest_sort sig /\
      safe_tree term = true /\
      render_tree term = Some tokens /\
      length tokens <= limit.
Proof.
  intros sig selected bridge owner sort term limit value Projected.
  unfold project in Projected.
  destruct (selected && bridge && Nat.eqb owner (guest_owner sig) &&
            Nat.eqb sort (guest_sort sig)) eqn:Authorized;
    try discriminate.
  destruct (render_tree term) as [tokens|] eqn:Rendered;
    try discriminate.
  destruct (Nat.leb (length tokens) limit) eqn:Within;
    try discriminate.
  inversion Projected; subst value.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end.
  exists tokens. repeat split; try assumption; try reflexivity.
  - now apply render_requires_public_tree in Rendered.
  - now apply Nat.leb_le.
Qed.

Theorem projection_refuses_private_subtrees :
  forall sig selected bridge owner sort term limit,
    safe_tree term = false ->
    project sig selected bridge owner sort term limit = None.
Proof.
  intros sig selected bridge owner sort term limit Unsafe.
  destruct (project sig selected bridge owner sort term limit) as [value|]
    eqn:Projected; [|reflexivity].
  apply projection_is_typed_bounded_and_public in Projected
    as [tokens [_ [_ [_ [Safe _]]]]].
  rewrite Unsafe in Safe. discriminate.
Qed.

Theorem projection_refuses_wrong_owner :
  forall sig selected bridge owner sort term limit,
    owner <> guest_owner sig ->
    project sig selected bridge owner sort term limit = None.
Proof.
  intros sig selected bridge owner sort term limit Distinct.
  unfold project. destruct selected, bridge; cbn; try reflexivity.
  destruct (Nat.eqb owner (guest_owner sig)) eqn:Equal;
    [apply Nat.eqb_eq in Equal; contradiction|reflexivity].
Qed.

Theorem projection_refuses_wrong_sort :
  forall sig selected bridge owner sort term limit,
    sort <> guest_sort sig ->
    project sig selected bridge owner sort term limit = None.
Proof.
  intros sig selected bridge owner sort term limit Distinct.
  unfold project. destruct selected, bridge; cbn; try reflexivity.
  destruct (Nat.eqb owner (guest_owner sig)); cbn; [|reflexivity].
  destruct (Nat.eqb sort (guest_sort sig)) eqn:Equal;
    [apply Nat.eqb_eq in Equal; contradiction|reflexivity].
Qed.

(** The two liveness observations are taken under one registry guard at
    publication. A result prepared earlier does not confer an authorization
    lease; either revocation suppresses the entire publication. *)
Definition publish_atomically (guest_live host_live : bool)
           (prepared : option DisplayValue) : option DisplayValue :=
  if guest_live && host_live then prepared else None.

Theorem publication_requires_both_live :
  forall guest_live host_live prepared output,
    publish_atomically guest_live host_live prepared = Some output ->
    guest_live = true /\ host_live = true /\ prepared = Some output.
Proof.
  intros guest_live host_live prepared output Published.
  unfold publish_atomically in Published.
  destruct guest_live, host_live; cbn in Published; try discriminate.
  repeat split; assumption || reflexivity.
Qed.

End DerivedSExprProjection.
