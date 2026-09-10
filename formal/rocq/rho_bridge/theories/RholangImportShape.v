(** Read-only admission of the direct node import carrier.

    This is a finite abstraction of the fields inspected on an existing Par,
    not a second value representation or a decoder. Payloads are never rebuilt.
    AtomShape covers the explicitly admitted primitive expression variants;
    UnsupportedShape covers the remaining expression variants. The Rust
    variant-to-shape correspondence must be checked against the pinned schema.

    Metadata counts represent actual byte/vector lengths, not trusted claims
    of closedness. A zeroed parent summary alone does not admit its children:
    the separate worklist proof requires admission at every structural child.
    Name presence means an actual protobuf oneof value, not provider authority.
    The provider still checks the original token at its eventual semantic use.

    Empty Par is allowed inside a collection, but not as an import root:
    the existing node injection reducer accepts an expression or a name.
    Map order and multiplicity are preserved; this model does not assert that
    an arbitrary imported map is a sorted or duplicate-free normal form. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Inductive ImportShape :=
| NilShape | AtomShape | NameShape (present : bool)
| ListShape | MapShape (missing_fields : nat) | UnsupportedShape.

Record ImportHeader := {
  import_shape : ImportShape;
  expression_count : nat;
  name_count : nat;
  sidecar_lengths : list nat;
  local_bytes : nat;
  uses_connectives : bool;
  collection_local_bytes : nat;
  collection_uses_connectives : bool;
  has_remainder : bool
}.

Definition no_sidecars (header : ImportHeader) : bool :=
  forallb (fun size => Nat.eqb size 0) (sidecar_lengths header).
Definition closed_header (header : ImportHeader) : bool :=
  no_sidecars header && Nat.eqb (local_bytes header) 0 &&
  negb (uses_connectives header).
Definition closed_collection (header : ImportHeader) : bool :=
  Nat.eqb (collection_local_bytes header) 0 &&
  negb (collection_uses_connectives header) && negb (has_remainder header).
Definition expression_only (header : ImportHeader) : bool :=
  Nat.eqb (expression_count header) 1 && Nat.eqb (name_count header) 0.
Definition admit_header (root : bool) (header : ImportHeader) : bool :=
  closed_header header &&
  match import_shape header with
  | NilShape => negb root && Nat.eqb (expression_count header) 0 &&
      Nat.eqb (name_count header) 0
  | AtomShape => expression_only header
  | NameShape present => Nat.eqb (expression_count header) 0 &&
      Nat.eqb (name_count header) 1 && present
  | ListShape => expression_only header && closed_collection header
  | MapShape missing => expression_only header && closed_collection header &&
      Nat.eqb missing 0
  | UnsupportedShape => false
  end.

Theorem admitted_header_has_exact_closed_metadata : forall root header,
  admit_header root header = true ->
  Forall (fun size => size = 0) (sidecar_lengths header) /\
  local_bytes header = 0 /\ uses_connectives header = false.
Proof.
  intros root header H. unfold admit_header in H.
  apply andb_true_iff in H as [H _]. unfold closed_header in H.
  repeat rewrite andb_true_iff in H. destruct H as [[HS HL] HC].
  apply Nat.eqb_eq in HL. apply negb_true_iff in HC.
  split; [|auto]. unfold no_sidecars in HS.
  apply Forall_forall. intros size HI. apply forallb_forall with (x := size) in HS;
    [now apply Nat.eqb_eq|exact HI].
Qed.

Theorem admitted_collection_has_no_open_fields : forall root header,
  (import_shape header = ListShape \/ exists missing, import_shape header = MapShape missing) ->
  admit_header root header = true ->
  expression_count header = 1 /\ name_count header = 0 /\
  collection_local_bytes header = 0 /\
  collection_uses_connectives header = false /\ has_remainder header = false.
Proof.
  intros root header HS H. unfold admit_header in H.
  apply andb_true_iff in H as [_ H].
  assert (expression_only header && closed_collection header = true) as HE.
  { destruct HS as [HS|[missing HS]]; rewrite HS in H.
    - exact H.
    - now apply andb_true_iff in H as [H _]. }
  unfold expression_only, closed_collection in HE.
  repeat rewrite andb_true_iff in HE.
  destruct HE as [[HE HN] [[HL HC] HR]].
  apply Nat.eqb_eq in HE, HN, HL. apply negb_true_iff in HC, HR. auto.
Qed.

Theorem admitted_maps_have_every_key_and_value : forall root header missing,
  import_shape header = MapShape missing -> admit_header root header = true -> missing = 0.
Proof.
  intros root header missing HS H. unfold admit_header in H. rewrite HS in H.
  repeat rewrite andb_true_iff in H. apply Nat.eqb_eq. tauto.
Qed.

Theorem admitted_names_are_present_singletons : forall root header present,
  import_shape header = NameShape present -> admit_header root header = true ->
  expression_count header = 0 /\ name_count header = 1 /\ present = true.
Proof.
  intros root header present HS H. unfold admit_header in H. rewrite HS in H.
  repeat rewrite andb_true_iff in H. destruct H as [_ [[HE HN] HP]].
  apply Nat.eqb_eq in HE, HN. auto.
Qed.

Theorem root_nil_is_refused : forall header,
  import_shape header = NilShape -> admit_header true header = false.
Proof. intros header HS. unfold admit_header. rewrite HS. now rewrite andb_false_r. Qed.
Theorem unsupported_shape_is_refused : forall root header,
  import_shape header = UnsupportedShape -> admit_header root header = false.
Proof. intros root header HS. unfold admit_header. rewrite HS. apply andb_false_r. Qed.

(** Charge before scheduling children or copying a leaf. Naturals model a
    mathematical counter; Rust additionally uses checked_add to refuse usize
    overflow. An exhausted or cancelled attempt publishes no updated counter. *)
Definition import_charge (cancelled : bool) (limit used amount : nat) : option nat :=
  if cancelled then None else
  if used + amount <=? limit then Some (used + amount) else None.
Theorem successful_charge_is_exact_and_bounded : forall cancelled limit used amount next,
  import_charge cancelled limit used amount = Some next ->
  cancelled = false /\ next = used + amount /\ next <= limit.
Proof.
  intros [|] limit used amount next H; [discriminate|]. unfold import_charge in H.
  destruct (used + amount <=? limit) eqn:HB; [|discriminate].
  inversion H; subst. apply Nat.leb_le in HB. auto.
Qed.
Theorem cancelled_charge_refuses : forall limit used amount,
  import_charge true limit used amount = None.
Proof. reflexivity. Qed.
Theorem exhausted_charge_refuses : forall limit used amount,
  limit < used + amount -> import_charge false limit used amount = None.
Proof.
  intros limit used amount H. unfold import_charge. apply Nat.leb_gt in H. now rewrite H.
Qed.

Print Assumptions admitted_header_has_exact_closed_metadata.
Print Assumptions admitted_collection_has_no_open_fields.
Print Assumptions admitted_maps_have_every_key_and_value.
Print Assumptions admitted_names_are_present_singletons.
Print Assumptions root_nil_is_refused.
Print Assumptions unsupported_shape_is_refused.
Print Assumptions successful_charge_is_exact_and_bounded.
Print Assumptions cancelled_charge_refuses.
Print Assumptions exhausted_charge_refuses.
