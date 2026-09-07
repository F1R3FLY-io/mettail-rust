(** * Checked materialization of the existing positional/native operator carrier

    This model observes the existing byte writer, rather than defining another
    machine ABI. The supported forms are constructors and String, Integer and
    Boolean literals. Identifiers have four bytes, integers sixteen, and every
    variable-length segment has an eight-byte length prefix. The outer stable
    discriminant is itself framed: its contribution is twelve, not four.

    The fresh-insertion schedule follows EGraph::try_add_with_budget -> add:
    one caller node, two canonicalization copies, one class copy, and one parent
    copy per child occurrence. It is a conservative logical payload reservation,
    including discarded temporaries. It is not an allocator/RSS bound, an exact
    CPU or hash-probe cost, or a claim that the existing parent index is optimal.
    Duplicate insertion keeps its existing duplicate-before-node-limit policy.

    Finite-word overflow is represented by an explicit ceiling, while arithmetic
    is proved over naturals. Rust checked arithmetic must implement this observer;
    tests compare the plan to the actual existing writer and exercise overflow.
    Integer/UTF-8 library correctness and compiler extraction are not assumed. *)

From Stdlib Require Import Lists.List Strings.Ascii NArith ZArith Bool.Bool Lia.
From RuntimeGrammar Require Import ReflectedHeadEnrollment.
Import ListNotations.

Module KernelOperatorMaterialization.
Module Budget := ReflectedHeadEnrollment.ReflectedHeadEnrollment.

Fixpoint little_bytes (width : nat) (value : N) : list ascii :=
  match width with
  | 0 => []
  | S rest => ascii_of_N (N.modulo value 256) ::
      little_bytes rest (N.div value 256)
  end.

Lemma little_bytes_length : forall width value,
  length (little_bytes width value) = width.
Proof. induction width; intros; cbn; auto. Qed.

Definition frame (bytes : list ascii) :=
  little_bytes 8 (N.of_nat (length bytes)) ++ bytes.

Lemma frame_length : forall bytes, length (frame bytes) = 8 + length bytes.
Proof. intros. unfold frame. rewrite length_app, little_bytes_length. reflexivity. Qed.

Inductive Operator :=
| Constructor (identifier : N)
| Text (sort : N) (bytes : list ascii)
| Integer (sort : N) (value : Z)
| Boolean (sort : N) (value : bool).

Definition octet := ascii_of_nat.
Definition operator_bytes operator :=
  match operator with
  | Constructor id => octet 0 :: little_bytes 4 id
  | Text sort bytes => octet 5 :: little_bytes 4 sort ++ octet 0 :: frame bytes
  | Integer sort value => octet 5 :: little_bytes 4 sort ++
      octet 2 :: little_bytes 16 (Z.to_N (Z.modulo value (2 ^ 128)))
  | Boolean sort value => octet 5 :: little_bytes 4 sort ++
      [octet 4; octet (if value then 1 else 0)]
  end.

Definition inner_size operator :=
  match operator with
  | Constructor _ => 5
  | Text _ bytes => 14 + length bytes
  | Integer _ _ => 22
  | Boolean _ _ => 7
  end.

Theorem inner_observer_matches_existing_encoding : forall operator,
  length (operator_bytes operator) = inner_size operator.
Proof.
  intros []; unfold operator_bytes, inner_size;
    repeat rewrite length_app; repeat rewrite little_bytes_length;
    try rewrite frame_length; cbn; lia.
Qed.

Definition machine_bytes domain operator :=
  frame (little_bytes 4 4294967295%N) ++ frame domain ++ frame (operator_bytes operator).
Definition framed_size (domain : list ascii) operator :=
  28 + length domain + inner_size operator.

Theorem framed_observer_counts_the_discriminant_frame : forall domain operator,
  length (machine_bytes domain operator) = framed_size domain operator.
Proof.
  intros. unfold machine_bytes, framed_size.
  repeat rewrite length_app. repeat rewrite frame_length.
  rewrite little_bytes_length, inner_observer_matches_existing_encoding. lia.
Qed.

Record EncodingPlan := encoding_plan { inner : nat; framed : nat }.
Definition plan ceiling domain operator :=
  let content := inner_size operator in
  let complete := framed_size domain operator in
  if Nat.leb content ceiling && Nat.leb complete ceiling
  then Some (encoding_plan content complete) else None.

Theorem successful_plan_has_exact_representable_sizes :
  forall ceiling domain operator result,
    plan ceiling domain operator = Some result ->
    inner result = length (operator_bytes operator) /\
    framed result = length (machine_bytes domain operator) /\
    inner result <= ceiling /\ framed result <= ceiling.
Proof.
  intros ceiling domain operator result H. unfold plan in H.
  destruct (Nat.leb (inner_size operator) ceiling &&
    Nat.leb (framed_size domain operator) ceiling) eqn:E; try discriminate.
  inversion H; subst. apply andb_true_iff in E. destruct E as [Hi Hf].
  apply Nat.leb_le in Hi, Hf.
  change (inner_size operator = length (operator_bytes operator) /\
    framed_size domain operator = length (machine_bytes domain operator) /\
    inner_size operator <= ceiling /\ framed_size domain operator <= ceiling).
  rewrite inner_observer_matches_existing_encoding,
    framed_observer_counts_the_discriminant_frame. auto.
Qed.

(** Allocation reservation changes no operator bytes. The same existing writer
    is used after all reservations succeed. No alternative encoding is selected
    by capacity, resource limits, child count or hash-table layout. *)
Definition materialize ceiling domain operator :=
  option_map (fun _ => machine_bytes domain operator) (plan ceiling domain operator).

Theorem successful_materialization_preserves_exact_bytes :
  forall ceiling domain operator bytes,
    materialize ceiling domain operator = Some bytes ->
    bytes = machine_bytes domain operator.
Proof.
  intros ceiling domain operator bytes H. unfold materialize in H.
  destruct (plan ceiling domain operator); inversion H; reflexivity.
Qed.

Definition node_payload framed_bytes degree := framed_bytes + 4 * degree.
Definition fresh_payload_chunks framed_bytes degree :=
  let node := node_payload framed_bytes degree in
  [node; node; node; node] ++ repeat node degree ++ [4 * degree + 13].
Definition fresh_payload_size framed_bytes degree :=
  (degree + 4) * (framed_bytes + 4 * degree) + (4 * degree + 13).

Lemma repeated_payload_total : forall count bytes seed,
  fold_right Nat.add seed (repeat bytes count) = count * bytes + seed.
Proof. induction count; intros; cbn; [reflexivity|rewrite IHcount; lia]. Qed.

Theorem fresh_reservation_counts_every_materialization : forall framed_bytes degree,
  fold_right Nat.add 0 (fresh_payload_chunks framed_bytes degree) =
    fresh_payload_size framed_bytes degree.
Proof.
  intros. unfold fresh_payload_chunks.
  repeat rewrite fold_right_app. cbn [fold_right].
  rewrite repeated_payload_total.
  unfold node_payload, fresh_payload_size. nia.
Qed.

Definition reserve_fresh ceiling used available framed_bytes degree :=
  let bytes := fresh_payload_size framed_bytes degree in
  Budget.before_allocation ceiling used available bytes bytes.

Theorem fresh_allocation_follows_cumulative_reservation :
  forall ceiling used available framed_bytes degree total remaining,
    reserve_fresh ceiling used available framed_bytes degree =
      (Some (total, remaining),
        [Budget.AllocatePayload (fresh_payload_size framed_bytes degree)]) ->
    total = used + fresh_payload_size framed_bytes degree /\
    total <= ceiling /\
    remaining + fresh_payload_size framed_bytes degree = available.
Proof.
  intros ceiling used available framed_bytes degree total remaining H.
  unfold reserve_fresh, Budget.before_allocation in H.
  destruct (Budget.reserve ceiling used available
    (fresh_payload_size framed_bytes degree) (fresh_payload_size framed_bytes degree))
    as [[charged rest]|] eqn:E; try discriminate.
  inversion H; subst.
  apply Budget.successful_reservation_preserves_both_bounds in E. tauto.
Qed.

Example nullary_is_not_free : fresh_payload_size 40 0 = 173.
Proof. reflexivity. Qed.

End KernelOperatorMaterialization.

Print Assumptions KernelOperatorMaterialization.inner_observer_matches_existing_encoding.
Print Assumptions KernelOperatorMaterialization.framed_observer_counts_the_discriminant_frame.
Print Assumptions KernelOperatorMaterialization.successful_plan_has_exact_representable_sizes.
Print Assumptions KernelOperatorMaterialization.successful_materialization_preserves_exact_bytes.
Print Assumptions KernelOperatorMaterialization.fresh_reservation_counts_every_materialization.
Print Assumptions KernelOperatorMaterialization.fresh_allocation_follows_cumulative_reservation.
