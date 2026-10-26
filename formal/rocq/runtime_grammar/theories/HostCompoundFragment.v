(** * Exact generated host-carrier fragments

    A V2 compound host profile is a selected route fragment of the generated
    adapter, not a purported complete semantic signature. This model covers
    the admission obligations at that boundary: an emitted route retains its
    original IDs and field schema, refused routes cannot enter the fragment,
    and every structural child is named in the fragment's category roster.

    The source layout, route-support decision, and cryptographic equality of
    canonical profile bytes are trusted implementation obligations. In
    particular, this model does not prove that an arbitrary nested Rholang
    value is supported by the trusted iterative lowerer. *)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Module HostCompoundFragment.

Record Route := route {
  operator_id : nat;
  category_id : nat;
  constructor_id : nat;
  generated_constructor_tag : nat;
  stable_discriminant : nat;
  field_schema : list nat;
  route_supported : bool
}.

Definition route_selected (selected : list nat) (r : Route) : bool :=
  existsb (Nat.eqb (operator_id r)) selected.

Definition selected_routes (layout : list Route) (selected : list nat) : list Route :=
  filter (route_selected selected) layout.

Definition admitted (categories : list nat) (r : Route) : bool :=
  route_supported r &&
  existsb (Nat.eqb (category_id r)) categories &&
  forallb (fun child => existsb (Nat.eqb child) categories) (field_schema r).

Definition fragment_valid (categories : list nat) (routes : list Route) : bool :=
  forallb (admitted categories) routes.

Theorem selected_route_is_original : forall layout selected r,
  In r (selected_routes layout selected) -> In r layout.
Proof.
  intros layout selected r H.
  unfold selected_routes in H.
  apply filter_In in H. exact (proj1 H).
Qed.

Theorem selected_route_keeps_all_generated_fields : forall layout selected r,
  In r (selected_routes layout selected) ->
  exists source, In source layout /\
    operator_id source = operator_id r /\
    category_id source = category_id r /\
    constructor_id source = constructor_id r /\
    generated_constructor_tag source = generated_constructor_tag r /\
    stable_discriminant source = stable_discriminant r /\
    field_schema source = field_schema r.
Proof.
  intros layout selected r H.
  exists r. split; [now apply selected_route_is_original with (selected := selected)|].
  repeat split; reflexivity.
Qed.

Theorem valid_fragment_refuses_unsupported_route : forall categories routes r,
  fragment_valid categories routes = true ->
  In r routes -> route_supported r = true.
Proof.
  intros categories routes r Hvalid Hin.
  unfold fragment_valid in Hvalid.
  apply forallb_forall with (x := r) in Hvalid; [|assumption].
  unfold admitted in Hvalid.
  repeat rewrite andb_true_iff in Hvalid.
  destruct Hvalid as [[Hs _] _]. exact Hs.
Qed.

Theorem valid_fragment_names_every_structural_child :
  forall categories routes r child,
  fragment_valid categories routes = true ->
  In r routes -> In child (field_schema r) -> In child categories.
Proof.
  intros categories routes r child Hvalid Hr Hchild.
  unfold fragment_valid in Hvalid.
  apply forallb_forall with (x := r) in Hvalid; [|assumption].
  unfold admitted in Hvalid.
  apply andb_true_iff in Hvalid as [_ Hchildren].
  apply forallb_forall with (x := child) in Hchildren; [|assumption].
  apply existsb_exists in Hchildren as [named [Hnamed Heq]].
  apply Nat.eqb_eq in Heq. subst named. exact Hnamed.
Qed.

Theorem unselected_route_is_unavailable : forall layout selected r,
  In r layout -> route_selected selected r = false ->
  ~ In r (selected_routes layout selected).
Proof.
  intros layout selected r _ Hnot Hin.
  unfold selected_routes in Hin.
  apply filter_In in Hin as [_ Hselected].
  rewrite Hnot in Hselected. discriminate.
Qed.

(** A full-signature coverage check would reject the second route, but the
    exact fragment may admit the first without pretending the second exists
    in the host codec. This is the case encountered for unrelated Rholang DDL
    productions absent from the generated semantic adapter. *)
Example unrelated_unsupported_route_does_not_refuse_selected_fragment :
  let selected := route 0 0 0 0 0 [] true in
  let unrelated := route 1 1 1 1 1 [] false in
  fragment_valid [0] (selected_routes [selected; unrelated] [0]) = true /\
  fragment_valid [0] [selected; unrelated] = false.
Proof. split; reflexivity. Qed.

End HostCompoundFragment.
