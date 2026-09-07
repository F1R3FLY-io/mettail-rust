(** * Local typed views of existing theory-machine operators

    This is the local boundary used by the installed FLT adapter, not another
    operator encoding, graph validator or evaluator. Octets, little-endian
    identifiers, exact constructor-table lookup and native payload lengths
    are explicit. The existing framing checker and UTF-8 checker remain
    unchanged Rust primitives; the text theorem retains the exact bytes
    passed to that checker, not an assumed proof of the checker itself.

    Constructor success checks the full dense identifier, codomain and arity
    and returns every ordered child occurrence. This local observation does
    not establish descendant typing or graph finiteness. Those obligations
    belong to InstalledFltOccurrence and the admitted/published graph boundary.

    The extraction theorem states equality for every literal decoder, including
    errors and work traces: no codec-correctness premise is postulated. The
    concrete payload theorems below separately specify the decoder's new view.
    Rust standard-library integer/UTF-8 implementations and heap correspondence
    are checked by focused wire tests, not claimed as proved by this model. *)

From Stdlib Require Import Lists.List Strings.Ascii NArith ZArith Bool.Bool Lia.
From RuntimeGrammar Require Import InstalledFltJudgments.
Import ListNotations.

Module KernelPositionalNativeView.
Module Budget := InstalledFltJudgments.InstalledFltJudgments.

Fixpoint little_endian (bytes : list ascii) : N :=
  match bytes with
  | [] => 0%N
  | head :: tail => (N_of_ascii head + 256 * little_endian tail)%N
  end.

Record Signature := signature {
  identifier : nat;
  domain : list nat;
  codomain : nat
}.

Definition constructor_signature table expected payload count :=
  if Nat.eqb (length payload) 4 then
    let id := N.to_nat (little_endian payload) in
    match nth_error table id with
    | Some entry =>
        if Nat.eqb (identifier entry) id &&
           Nat.eqb (codomain entry) expected &&
           Nat.eqb (length (domain entry)) count
        then Some entry else None
    | None => None
    end
  else None.

Definition constructor_view table expected payload (children : list nat) :=
  option_map (fun entry => (entry, children))
    (constructor_signature table expected payload (length children)).

Theorem constructor_success_is_exact : forall table expected payload children entry output,
  constructor_view table expected payload children = Some (entry, output) ->
  length payload = 4 /\
  nth_error table (N.to_nat (little_endian payload)) = Some entry /\
  identifier entry = N.to_nat (little_endian payload) /\
  codomain entry = expected /\
  length (domain entry) = length children /\ output = children.
Proof.
  intros table expected payload children entry output H.
  unfold constructor_view, constructor_signature in H.
  destruct (Nat.eqb (length payload) 4) eqn:Hwidth; try discriminate.
  destruct (nth_error table (N.to_nat (little_endian payload))) as [candidate|]
    eqn:Hlookup; try discriminate.
  destruct (Nat.eqb (identifier candidate) (N.to_nat (little_endian payload)) &&
    Nat.eqb (codomain candidate) expected &&
    Nat.eqb (length (domain candidate)) (length children)) eqn:Hchecks;
    try discriminate.
  inversion H; subst. apply Nat.eqb_eq in Hwidth.
  repeat rewrite andb_true_iff in Hchecks.
  destruct Hchecks as [[Hid Hsort] Harity].
  apply Nat.eqb_eq in Hid, Hsort, Harity. repeat split; auto.
Qed.

Theorem constructor_view_does_not_prune_occurrences :
  forall table expected payload children entry output,
    constructor_view table expected payload children = Some (entry, output) ->
    output = children.
Proof.
  intros. apply constructor_success_is_exact in H. tauto.
Qed.

Inductive Carrier := TextCarrier | IntegerCarrier | BooleanCarrier | OtherCarrier.
Inductive Payload := TextBytes (bytes : list ascii) | IntegerValue (value : Z)
  | BooleanValue (value : bool).

Definition signed_i128 bytes : Z :=
  let unsigned := Z.of_N (little_endian bytes) in
  if Z.ltb unsigned (2 ^ 127) then unsigned else (unsigned - 2 ^ 128)%Z.

(** [None] means no supported local view was established. It includes both
    malformed inputs and unsupported carriers, never semantic refutation. *)
Definition native_payload carrier tag (payload : list ascii) : option Payload :=
  match carrier, tag with
  | TextCarrier, 0 =>
      if Nat.leb 8 (length payload) &&
         Nat.eqb (N.to_nat (little_endian (firstn 8 payload)))
           (length (skipn 8 payload))
      then Some (TextBytes (skipn 8 payload)) else None
  | IntegerCarrier, 2 =>
      if Nat.eqb (length payload) 16
      then Some (IntegerValue (signed_i128 payload)) else None
  | BooleanCarrier, 4 =>
      match payload with
      | [byte] =>
          if ascii_dec byte (ascii_of_nat 0) then Some (BooleanValue false)
          else if ascii_dec byte (ascii_of_nat 1) then Some (BooleanValue true)
          else None
      | _ => None
      end
  | _, _ => None
  end.

Theorem text_success_keeps_exact_framed_bytes : forall payload bytes,
  native_payload TextCarrier 0 payload = Some (TextBytes bytes) ->
  8 <= length payload /\ bytes = skipn 8 payload /\
  N.to_nat (little_endian (firstn 8 payload)) = length bytes.
Proof.
  intros payload bytes H. cbn [native_payload] in H.
  destruct (Nat.leb 8 (length payload) &&
    Nat.eqb (N.to_nat (little_endian (firstn 8 payload)))
      (length (skipn 8 payload))) eqn:E; try discriminate.
  inversion H; subst. apply andb_true_iff in E. destruct E as [Hwidth Hlength].
  apply Nat.leb_le in Hwidth. apply Nat.eqb_eq in Hlength. auto.
Qed.

Theorem integer_success_is_exact_signed_little_endian : forall payload value,
  native_payload IntegerCarrier 2 payload = Some (IntegerValue value) ->
  length payload = 16 /\ value = signed_i128 payload.
Proof.
  intros payload value H. cbn [native_payload] in H.
  destruct (Nat.eqb (length payload) 16) eqn:E; try discriminate.
  inversion H; subst. apply Nat.eqb_eq in E. auto.
Qed.

Theorem boolean_success_has_one_canonical_byte : forall payload value,
  native_payload BooleanCarrier 4 payload = Some (BooleanValue value) ->
  payload = [ascii_of_nat (if value then 1 else 0)].
Proof.
  intros [|head [|next tail]] value H; try discriminate.
  cbn [native_payload] in H.
  destruct (ascii_dec head (ascii_of_nat 0)) as [Hzero|Hzero].
  - inversion H; subst. reflexivity.
  - destruct (ascii_dec head (ascii_of_nat 1)) as [Hone|Hone];
      try discriminate. inversion H; subst. reflexivity.
Qed.

(** The new public entry must guard [used > ceiling] before using the existing
    one-unit helper, whose private callers maintain [used <= ceiling]. *)
Definition checked_entry ceiling used :=
  if Nat.ltb ceiling used then None
  else if Nat.eqb used ceiling then None else Some (S used).

Theorem checked_entry_refines_existing_budget : forall ceiling used,
  checked_entry ceiling used = Budget.charge_work ceiling used 1.
Proof.
  intros ceiling used. unfold checked_entry, Budget.charge_work.
  destruct (Nat.ltb ceiling used) eqn:Hover.
  - apply Nat.ltb_lt in Hover.
    assert (Hfits : Nat.leb (used + 1) ceiling = false) by
      (apply Nat.leb_gt; lia).
    now rewrite Hfits.
  - apply Nat.ltb_ge in Hover.
    destruct (Nat.eqb used ceiling) eqn:Hequal.
    + apply Nat.eqb_eq in Hequal.
      assert (Hfits : Nat.leb (used + 1) ceiling = false) by
        (apply Nat.leb_gt; lia).
      now rewrite Hfits.
    + apply Nat.eqb_neq in Hequal.
      assert (Hfits : Nat.leb (used + 1) ceiling = true) by
        (apply Nat.leb_le; lia).
      rewrite Hfits. f_equal. lia.
Qed.

Corollary checked_entry_cannot_overdraw : forall ceiling used total,
  checked_entry ceiling used = Some total -> used < total /\ total <= ceiling.
Proof.
  intros ceiling used total H. rewrite checked_entry_refines_existing_budget in H.
  apply Budget.successful_charge_preserves_prefix_and_ceiling in H. lia.
Qed.

(** Extracting the node body preserves the complete result, including the
    decoder's work/error observation, for every implementation of that body.
    No premise says that an arbitrary decoder is a correct codec. *)
Section ExtractBody.
  Context {Node Result : Type}.
  Definition inline_call (prefix : option Node) (body : Node -> Result)
      (failure : Result) :=
    match prefix with Some node => body node | None => failure end.
  Definition factored_call (prefix : option Node) (body : Node -> Result)
      (failure : Result) :=
    match prefix with Some node => let local_body := body in local_body node
    | None => failure end.
  Theorem extracting_node_body_preserves_all_observations : forall prefix body failure,
    factored_call prefix body failure = inline_call prefix body failure.
  Proof. intros [node|] body failure; reflexivity. Qed.
End ExtractBody.

Example overdrawn_entry_is_rejected : checked_entry 4 5 = None.
Proof. reflexivity. Qed.
Example repeated_children_survive :
  constructor_view [signature 0 [9; 3; 9] 7] 7
    (repeat (ascii_of_nat 0) 4) [41; 6; 41] =
    Some (signature 0 [9; 3; 9] 7, [41; 6; 41]).
Proof. reflexivity. Qed.
Example boolean_views_are_production_values :
  native_payload BooleanCarrier 4 [ascii_of_nat 0] = Some (BooleanValue false) /\
  native_payload BooleanCarrier 4 [ascii_of_nat 1] = Some (BooleanValue true) /\
  native_payload BooleanCarrier 4 [ascii_of_nat 2] = None.
Proof. repeat split; reflexivity. Qed.

End KernelPositionalNativeView.

Print Assumptions KernelPositionalNativeView.constructor_success_is_exact.
Print Assumptions KernelPositionalNativeView.constructor_view_does_not_prune_occurrences.
Print Assumptions KernelPositionalNativeView.text_success_keeps_exact_framed_bytes.
Print Assumptions KernelPositionalNativeView.integer_success_is_exact_signed_little_endian.
Print Assumptions KernelPositionalNativeView.boolean_success_has_one_canonical_byte.
Print Assumptions KernelPositionalNativeView.checked_entry_refines_existing_budget.
Print Assumptions KernelPositionalNativeView.checked_entry_cannot_overdraw.
Print Assumptions KernelPositionalNativeView.extracting_node_body_preserves_all_observations.
