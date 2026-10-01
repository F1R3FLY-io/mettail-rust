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

(** A compiler may keep independently authored projection groups in one flat
    image. Concatenation neither drops source occurrences nor changes their
    order within a selected relation. This is the layout obligation for the
    shared set-automaton input, not a permission to truncate its candidates. *)
Lemma selected_group_append : forall selector first second,
  selected selector (first ++ second) =
  selected selector first ++ selected selector second.
Proof.
  intros selector first second. unfold selected. now rewrite filter_app.
Qed.

Lemma selected_group_origins_append : forall selector first second,
  map row_origin (selected selector (first ++ second)) =
  map row_origin (selected selector first) ++
  map row_origin (selected selector second).
Proof.
  intros selector first second.
  rewrite selected_group_append. now rewrite map_app.
Qed.

Lemma absent_selector_has_no_candidates : forall selector image,
  (forall rule, In rule image -> row_selector rule <> selector) ->
  selected selector image = [].
Proof.
  intros selector image Absent.
  destruct (selected selector image) as [|rule rest] eqn:Selected;
    [reflexivity|].
  exfalso.
  assert (Member : In rule (selected selector image)).
  { rewrite Selected. now left. }
  apply selected_source_correspondence in Member as [Source Equal].
  exact (Absent rule Source Equal).
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

(** A separately added projection relation cannot change the candidate set
    selected for an ordinary guest rewrite.  This is stronger than checking a
    single projection row: it covers any finite projection image extension. *)
Definition only_projection_rows (rows : list Row) : Prop :=
  forall rule, In rule rows ->
    exists id direction, row_selector rule = Projection id direction.

Lemma ordinary_selection_conservative : forall image extension sort,
  only_projection_rows extension ->
  selected (Ordinary sort) (image ++ extension) = selected (Ordinary sort) image.
Proof.
  intros image extension sort Only.
  unfold selected. rewrite filter_app.
  assert (Empty : filter (fun rule : Row =>
      match row_selector rule with
      | Ordinary rhs_sort => Nat.eqb sort rhs_sort
      | Projection _ _ => false
      end) extension = []).
  { revert Only. induction extension as [|rule rest IH]; intros Only; simpl.
    - reflexivity.
    - destruct (Only rule (or_introl eq_refl)) as [id [direction Eq]].
      rewrite Eq. apply IH. intros candidate Member.
      apply Only. now right. }
  now rewrite Empty, app_nil_r.
Qed.

(** The executable image retains ordinary programs as a dense prefix and
    appends directional projection programs. A nested ordinary-transition
    premise is restricted to that prefix, even though the matcher was restored
    from the complete positional automaton. Thus its candidate set is exactly
    the old guest relation, independently of the projection rows' patterns. *)
Lemma ordinary_program_prefix : forall (ordinary projections : list Row),
  firstn (length ordinary) (ordinary ++ projections) = ordinary.
Proof.
  intros ordinary projections.
  rewrite firstn_app, firstn_all, Nat.sub_diag.
  simpl. now rewrite app_nil_r.
Qed.

Lemma bounded_ordinary_selection_exact : forall ordinary projections sort,
  selected (Ordinary sort)
    (firstn (length ordinary) (ordinary ++ projections)) =
  selected (Ordinary sort) ordinary.
Proof.
  intros ordinary projections sort.
  now rewrite ordinary_program_prefix.
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

(** A source declaration may request a host endpoint, but cannot populate the
    trusted host registry.  The signature and codec identifiers below model
    already checked commitments, not user-chosen display names or a claim that
    natural-number equality proves cryptographic collision resistance.  A
    successful binding must be unique: source order must not elect one of two
    registered profiles that satisfy the same request. *)
Record HostProfile := registered_host_profile {
  host_signature_id : nat;
  host_codec_id : nat;
  host_category_ids : list nat
}.

Record HostRequest := host_request {
  requested_signature : nat;
  requested_codec : nat;
  requested_category : nat
}.

Definition host_request_matches (request : HostRequest)
           (profile : HostProfile) : bool :=
  Nat.eqb (requested_signature request) (host_signature_id profile) &&
  Nat.eqb (requested_codec request) (host_codec_id profile) &&
  existsb (Nat.eqb (requested_category request))
          (host_category_ids profile).

Definition bind_registered_host (registry : list HostProfile)
           (request : HostRequest) : option HostProfile :=
  match filter (host_request_matches request) registry with
  | [profile] => Some profile
  | _ => None
  end.

Lemma bound_host_is_registered : forall registry request profile,
  bind_registered_host registry request = Some profile -> In profile registry.
Proof.
  intros registry request profile Bound.
  unfold bind_registered_host in Bound.
  destruct (filter (host_request_matches request) registry) as
    [|candidate remainder] eqn:Filtered; try discriminate.
  destruct remainder; try discriminate.
  inversion Bound; subst candidate.
  assert (Member : In profile
    (filter (host_request_matches request) registry)).
  { rewrite Filtered. now left. }
  apply filter_In in Member.
  exact (proj1 Member).
Qed.

Lemma bound_host_has_exact_commitments : forall registry request profile,
  bind_registered_host registry request = Some profile ->
  requested_signature request = host_signature_id profile /\
  requested_codec request = host_codec_id profile /\
  In (requested_category request) (host_category_ids profile).
Proof.
  intros registry request profile Bound.
  unfold bind_registered_host in Bound.
  destruct (filter (host_request_matches request) registry) as
    [|candidate remainder] eqn:Filtered; try discriminate.
  destruct remainder; try discriminate.
  inversion Bound; subst candidate.
  assert (Member : In profile
    (filter (host_request_matches request) registry)).
  { rewrite Filtered. now left. }
  apply filter_In in Member.
  destruct Member as [_ Matches].
  unfold host_request_matches in Matches.
  repeat rewrite andb_true_iff in Matches.
  destruct Matches as [[Signature Codec] Category].
  apply Nat.eqb_eq in Signature.
  apply Nat.eqb_eq in Codec.
  apply existsb_exists in Category as [category [Member Equal]].
  apply Nat.eqb_eq in Equal. subst category.
  now repeat split.
Qed.

Lemma duplicate_matching_host_is_refused : forall registry request profile,
  host_request_matches request profile = true ->
  bind_registered_host (profile :: profile :: registry) request = None.
Proof.
  intros registry request profile Matches.
  unfold bind_registered_host. cbn [filter].
  rewrite Matches.
  destruct (filter (host_request_matches request) registry); reflexivity.
Qed.

End TypedProjectionRelation.

(** The generated DDL grammar admits a remainder only as the final direct
    element of a collection: `{...rest}` or `{term, ..., ...rest}`.  The
    standalone author's iterative parser carries the term-frame context in
    each pending job, then checks the completed collection.  This model is
    deliberately about that control invariant, not about the structural
    matcher or the meaning of a remainder after elaboration. *)
Module ProjectionRemainderSurface.

Inductive TermFrame := Root | AbstractionBody | SubstitutionLeft
                    | SubstitutionRight | ConstructorArgument | CollectionElement.

Definition remainder_allowed (frame : TermFrame) : bool :=
  match frame with CollectionElement => true | _ => false end.

Lemma only_collection_elements_admit_remainders : forall frame,
  remainder_allowed frame = true -> frame = CollectionElement.
Proof.
  intros frame Allowed. destruct frame; simpl in Allowed;
    try discriminate; reflexivity.
Qed.

Lemma collection_elements_admit_remainders :
  remainder_allowed CollectionElement = true.
Proof. reflexivity. Qed.

Inductive DirectElement := OrdinaryElement | RemainderElement.

(** This is the parser's closing check after it has admitted direct elements
    in CollectionElement frames.  Seeing a remainder while there is any later
    element refuses the collection, irrespective of that later element's kind. *)
Fixpoint close_collection (elements : list DirectElement) : bool :=
  match elements with
  | [] => true
  | OrdinaryElement :: tail => close_collection tail
  | [RemainderElement] => true
  | RemainderElement :: _ :: _ => false
  end.

(** The corresponding generated grammar shape: ordinary direct elements may
    precede one final remainder; there is no constructor that can put a
    remainder before another element or outside a collection. *)
Inductive CollectionGrammar : list DirectElement -> Prop :=
| CollectionEmpty : CollectionGrammar []
| CollectionOrdinary : forall tail,
    CollectionGrammar tail -> CollectionGrammar (OrdinaryElement :: tail)
| CollectionFinalRemainder : CollectionGrammar [RemainderElement].

Theorem collection_close_exactly_matches_grammar : forall elements,
  close_collection elements = true <-> CollectionGrammar elements.
Proof.
  intro elements. split.
  - induction elements as [|head tail IH]; intro Closed.
    + constructor.
    + destruct head.
      * apply CollectionOrdinary. apply IH. exact Closed.
      * destruct tail as [|later rest].
        -- constructor.
        -- discriminate Closed.
  - intro Grammar. induction Grammar; simpl; try reflexivity.
    exact IHGrammar.
Qed.

End ProjectionRemainderSurface.

(** Native byte and floating-point projection atoms use distinct typed wire
    constructors.  The generated lexer has already produced bytes and a
    canonical Float value before this boundary; this model covers the
    structural transport and admission of those values, not decimal parsing
    or IEEE-754 canonicalization.  The Rust differential/property tests carry
    those latter obligations.  [finite_float_bits] is the checked admission
    predicate for a Float payload; it is deliberately not silently assumed of
    every possible 64-bit pattern. *)
From Stdlib Require Import NArith.NArith.

Module ProjectionNativeScalarWire.

Open Scope N_scope.

Inductive Scalar := ByteSequence (value : list N) | FiniteFloat (bits : N).
Inductive Wire := BytesNode (value : list N) | FloatNode (bits : N).

Definition byte_in_range (byte : N) : bool := byte <? 256.

Section Transport.
Variable finite_float_bits : N -> bool.

Definition encode (scalar : Scalar) : Wire :=
  match scalar with
  | ByteSequence bytes => BytesNode bytes
  | FiniteFloat bits => FloatNode bits
  end.

Definition decode (wire : Wire) : option Scalar :=
  match wire with
  | BytesNode bytes =>
      if forallb byte_in_range bytes then Some (ByteSequence bytes) else None
  | FloatNode bits =>
      if finite_float_bits bits then Some (FiniteFloat bits) else None
  end.

Theorem admitted_bytes_round_trip : forall bytes,
  forallb byte_in_range bytes = true ->
  decode (encode (ByteSequence bytes)) = Some (ByteSequence bytes).
Proof. intros bytes Valid. cbn [encode decode]. now rewrite Valid. Qed.

Theorem admitted_float_round_trip : forall bits,
  finite_float_bits bits = true ->
  decode (encode (FiniteFloat bits)) = Some (FiniteFloat bits).
Proof. intros bits Valid. cbn [encode decode]. now rewrite Valid. Qed.

Theorem accepted_wire_is_reconstructible : forall wire scalar,
  decode wire = Some scalar -> encode scalar = wire.
Proof.
  intros [bytes|bits] scalar Accepted; cbn [decode] in Accepted.
  - destruct (forallb byte_in_range bytes); inversion Accepted; reflexivity.
  - destruct (finite_float_bits bits); inversion Accepted; reflexivity.
Qed.

Theorem byte_and_float_tags_are_disjoint : forall bytes bits,
  encode (ByteSequence bytes) <> encode (FiniteFloat bits).
Proof. intros bytes bits Wrong. discriminate Wrong. Qed.

End Transport.
End ProjectionNativeScalarWire.
