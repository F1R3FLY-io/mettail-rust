(** * Typed, selected guest-host projection relations

    This is a category-parametric boundary model for the projection DDL.  A
    projection declaration contributes directional rules to the same rule-image
    selection mechanism used by ordinary transitions.  Selection is explicit:
    dormant projection rules cannot become ordinary guest rewrites, and asking
    for one direction cannot execute its converse.  The model represents a
    rule's structural matcher by equality of admitted endpoint terms; the Rust
    implementation must separately establish that its full matcher refines
    this relation and preserves every source occurrence.

    Bidirectional source rows expand to two directional rules.  This proves
    relational reversal, not unique invertibility: a unique-value round trip
    additionally needs both functional and injective evidence.  The lemmas
    state those obligations explicitly rather than treating a pair of arrows
    as an unconditional isomorphism.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Module TypedProjectionRelation.

Inductive Endpoint := Guest (owner sort : nat) | Host (profile sort : nat).

Record Term := term {
  endpoint : Endpoint;
  payload : nat
}.

Inductive Direction := GuestToHost | HostToGuest.

Inductive Selector := Ordinary (guest_sort : nat)
                    | Projection (projection_id : nat) (direction : Direction).

Record Row := row {
  row_selector : Selector;
  row_origin : nat;
  row_input : Term;
  row_output : Term
}.

Record Signature := signature {
  guest_owner : nat;
  guest_sort : nat;
  host_profile : nat;
  host_sort : nat
}.

Definition direction_typed (sig : Signature) (dir : Direction)
           (input output : Term) : Prop :=
  match dir with
  | GuestToHost => endpoint input = Guest (guest_owner sig) (guest_sort sig) /\
                   endpoint output = Host (host_profile sig) (host_sort sig)
  | HostToGuest => endpoint input = Host (host_profile sig) (host_sort sig) /\
                   endpoint output = Guest (guest_owner sig) (guest_sort sig)
  end.

Definition selected (selector : Selector) (image : list Row) : list Row :=
  filter (fun rule =>
    match selector, row_selector rule with
    | Ordinary lhs_sort, Ordinary rhs_sort => Nat.eqb lhs_sort rhs_sort
    | Projection lhs_id left_dir, Projection rhs_id right_dir =>
        Nat.eqb lhs_id rhs_id &&
        match left_dir, right_dir with
        | GuestToHost, GuestToHost | HostToGuest, HostToGuest => true
        | _, _ => false
        end
    | _, _ => false
    end) image.

Definition applies (selector : Selector) (image : list Row)
           (input output : Term) (origin : nat) : Prop :=
  exists rule, In rule (selected selector image) /\
               row_input rule = input /\ row_output rule = output /\
               row_origin rule = origin.

Lemma selected_source_correspondence : forall selector image rule,
  In rule (selected selector image) <->
  In rule image /\ row_selector rule = selector.
Proof.
  intros selector image rule; unfold selected.
  rewrite filter_In. split.
  - intros [Member Eq]. split; [assumption|].
    destruct selector as [s|p d], (row_selector rule) as [s'|p' d'];
      simpl in Eq; try discriminate.
    + apply Nat.eqb_eq in Eq. now subst.
    + apply andb_true_iff in Eq as [P D].
      apply Nat.eqb_eq in P. subst p'.
      destruct d, d'; simpl in D; try discriminate; reflexivity.
  - intros [Member Eq]; split; [assumption|].
    rewrite Eq. destruct selector as [s|p d]; simpl.
    + apply Nat.eqb_refl.
    + rewrite Nat.eqb_refl. now destruct d.
Qed.

Lemma ordinary_projection_separation : forall image sort projection dir input output origin,
  applies (Ordinary sort) image input output origin ->
  ~ (exists rule, In rule (selected (Projection projection dir) image) /\
                  row_origin rule = origin /\ row_selector rule = Ordinary sort).
Proof.
  intros image sort projection dir input output origin _ [rule [Selected [_ Wrong]]].
  apply selected_source_correspondence in Selected as [_ Eq].
  rewrite Wrong in Eq. discriminate.
Qed.

Lemma projection_direction_separation : forall image id input output origin,
  applies (Projection id GuestToHost) image input output origin ->
  forall rule, In rule (selected (Projection id HostToGuest) image) ->
               row_selector rule <> Projection id GuestToHost.
Proof.
  intros image id input output origin _ rule Selected.
  apply selected_source_correspondence in Selected as [_ Eq].
  now rewrite Eq.
Qed.

Definition typed_image (id : nat) (sig : Signature) (image : list Row) : Prop :=
  forall rule dir, In rule image ->
    row_selector rule = Projection id dir ->
    direction_typed sig dir (row_input rule) (row_output rule).

Lemma selected_result_typed : forall id dir sig image input output origin,
  typed_image id sig image ->
  applies (Projection id dir) image input output origin ->
  direction_typed sig dir input output.
Proof.
  intros id dir sig image input output origin Typed
         [rule [Selected [Input [Output _]]]].
  apply selected_source_correspondence in Selected as [Member Selector].
  specialize (Typed rule dir Member Selector).
  now rewrite <- Input, <- Output.
Qed.

Definition forward_row (id origin : nat) (guest host : Term) : Row :=
  row (Projection id GuestToHost) origin guest host.
Definition reverse_row (id origin : nat) (guest host : Term) : Row :=
  row (Projection id HostToGuest) origin host guest.

Inductive SurfaceArrow := ForwardArrow | BackwardArrow | BothArrows.

(** The compiler stores only directed rules.  The surface arrow changes which
    endpoint is the input; it does not introduce a second execution engine. *)
Definition lower_surface_row (id origin : nat) (guest host : Term)
           (arrow : SurfaceArrow) : list Row :=
  match arrow with
  | ForwardArrow => [forward_row id origin guest host]
  | BackwardArrow => [reverse_row id origin guest host]
  | BothArrows => [forward_row id origin guest host;
                   reverse_row id origin guest host]
  end.

Lemma backward_is_directed_host_input : forall id origin guest host,
  lower_surface_row id origin guest host BackwardArrow =
  [row (Projection id HostToGuest) origin host guest].
Proof. reflexivity. Qed.

Lemma both_are_two_directed_rules : forall id origin guest host,
  lower_surface_row id origin guest host BothArrows =
  lower_surface_row id origin guest host ForwardArrow ++
  lower_surface_row id origin guest host BackwardArrow.
Proof. reflexivity. Qed.

Definition expand_bidirectional (id : nat)
           (pairs : list (nat * Term * Term)) : list Row :=
  flat_map (fun '(origin, guest, host) =>
              lower_surface_row id origin guest host BothArrows) pairs.

Lemma bidirectional_forward_source : forall id pairs origin guest host,
  In (origin, guest, host) pairs ->
  applies (Projection id GuestToHost) (expand_bidirectional id pairs)
          guest host origin.
Proof.
  intros id pairs origin guest host Member.
  unfold applies, expand_bidirectional.
  exists (forward_row id origin guest host).
  split.
  - apply selected_source_correspondence. split; [|reflexivity].
    apply in_flat_map. exists (origin, guest, host). split; [assumption|].
    simpl. now left.
  - repeat split; reflexivity.
Qed.

Lemma bidirectional_reverse_source : forall id pairs origin guest host,
  In (origin, guest, host) pairs ->
  applies (Projection id HostToGuest) (expand_bidirectional id pairs)
          host guest origin.
Proof.
  intros id pairs origin guest host Member.
  unfold applies, expand_bidirectional.
  exists (reverse_row id origin guest host).
  split.
  - apply selected_source_correspondence. split; [|reflexivity].
    apply in_flat_map. exists (origin, guest, host). split; [assumption|].
    simpl. now right; left.
  - repeat split; reflexivity.
Qed.

Lemma bidirectional_forward_complete : forall id pairs origin guest host,
  applies (Projection id GuestToHost) (expand_bidirectional id pairs)
          guest host origin -> In (origin, guest, host) pairs.
Proof.
  intros id pairs origin guest host [rule [Selected [Input [Output Origin]]]].
  apply selected_source_correspondence in Selected as [Member Selector].
  unfold expand_bidirectional in Member.
  apply in_flat_map in Member as [source [Pair Row]].
  destruct source as [[source_origin source_guest] source_host].
  simpl in Row. destruct Row as [Forward|[Reverse|[]]].
  - subst rule. simpl in *. now subst.
  - subst rule. simpl in Selector. discriminate.
Qed.

Lemma bidirectional_reverse_complete : forall id pairs origin guest host,
  applies (Projection id HostToGuest) (expand_bidirectional id pairs)
          host guest origin -> In (origin, guest, host) pairs.
Proof.
  intros id pairs origin guest host [rule [Selected [Input [Output Origin]]]].
  apply selected_source_correspondence in Selected as [Member Selector].
  unfold expand_bidirectional in Member.
  apply in_flat_map in Member as [source [Pair Row]].
  destruct source as [[source_origin source_guest] source_host].
  simpl in Row. destruct Row as [Forward|[Reverse|[]]].
  - subst rule. simpl in Selector. discriminate.
  - subst rule. simpl in *. now subst.
Qed.

Definition functional_forward (pairs : list (nat * Term * Term)) : Prop :=
  forall o1 o2 g h1 h2, In (o1, g, h1) pairs -> In (o2, g, h2) pairs -> h1 = h2.

Definition functional_reverse (pairs : list (nat * Term * Term)) : Prop :=
  forall o1 o2 g1 g2 h, In (o1, g1, h) pairs -> In (o2, g2, h) pairs -> g1 = g2.

Lemma checked_round_trip_guest : forall id pairs o guest host returned o',
  functional_reverse pairs ->
  applies (Projection id GuestToHost) (expand_bidirectional id pairs)
          guest host o ->
  applies (Projection id HostToGuest) (expand_bidirectional id pairs)
          host returned o' -> returned = guest.
Proof.
  intros id pairs o guest host returned o' Reverse Forward Backward.
  apply bidirectional_forward_complete in Forward.
  apply bidirectional_reverse_complete in Backward.
  eapply Reverse; eassumption.
Qed.

Lemma checked_round_trip_host : forall id pairs o guest host returned o',
  functional_forward pairs ->
  applies (Projection id HostToGuest) (expand_bidirectional id pairs)
          host guest o ->
  applies (Projection id GuestToHost) (expand_bidirectional id pairs)
          guest returned o' -> returned = host.
Proof.
  intros id pairs o guest host returned o' Forward Backward Again.
  apply bidirectional_reverse_complete in Backward.
  apply bidirectional_forward_complete in Again.
  eapply Forward; eassumption.
Qed.

Definition compose_via_host (first second : list Row) (first_id second_id : nat)
           (guest1 guest2 : Term) : Prop :=
  exists host first_origin second_origin,
    applies (Projection first_id GuestToHost) first guest1 host first_origin /\
    applies (Projection second_id HostToGuest) second host guest2 second_origin.

Lemma composition_requires_both_legs : forall first second first_id second_id guest1 guest2,
  compose_via_host first second first_id second_id guest1 guest2 ->
  exists host first_origin second_origin,
    applies (Projection first_id GuestToHost) first guest1 host first_origin /\
    applies (Projection second_id HostToGuest) second host guest2 second_origin.
Proof. intros; exact H. Qed.

End TypedProjectionRelation.
