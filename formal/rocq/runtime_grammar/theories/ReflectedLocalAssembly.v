(** * Factoring one positional reflected-node assembly

    The existing ground reflector and the checked installed-FLT adapter share
    one local assembly body. Children are already reflected and move in order;
    no fake GroundTerm children or second traversal is needed. This model keeps
    child identity, ground bits, marker selection and locally-free byte vectors
    explicit. It does not replace reflected-envelope or typed-child admission.

    The metadata byte schedule observes the existing padded bitwise union:
    clone each child's vector, allocate each prefix union, then copy the final
    vector twice (EList metadata and the temporary Par cloned by with_exprs).
    The length-only planning loop is tail recursive. No descendant is visited.
    This logical payload schedule excludes allocator headers/capacity/RSS. *)

From Stdlib Require Import Lists.List NArith Bool.Bool Arith.PeanoNat Lia.
From RuntimeGrammar Require Import ReflectedHeadEnrollment.
Import ListNotations.

Module ReflectedLocalAssembly.
Module Budget := ReflectedHeadEnrollment.ReflectedHeadEnrollment.

Fixpoint union_bytes (left right : list N) : list N :=
  match left, right with
  | [], rest | rest, [] => rest
  | x :: xs, y :: ys => N.lor x y :: union_bytes xs ys
  end.

Lemma union_bytes_length : forall left right,
  length (union_bytes left right) = Nat.max (length left) (length right).
Proof.
  induction left as [|x xs IH]; intros [|y ys]; cbn; auto.
Qed.

Record Child := child {
  payload : nat;
  ground : bool;
  locally_free : list N
}.

Inductive GroundPolicy := Bound | Free | Children.
Definition ground_result policy children :=
  match policy with
  | Bound => false
  | Free => true
  | Children => forallb ground children
  end.

Definition combined_free children :=
  fold_left (fun accumulated entry => union_bytes accumulated (locally_free entry)) children [].

Record Assembled := assembled {
  label : nat;
  marker : option bool;
  child_payloads : list nat;
  result_ground : bool;
  root_free : list N;
  list_free : list N
}.

Definition assemble (label : nat) (policy : GroundPolicy) (marked : bool)
    (children : list Child) :=
  let is_ground := ground_result policy children in
  let free := combined_free children in
  assembled label (if marked then Some is_ground else None)
    (map payload children) is_ground free free.

Record GroundHead := ground_head { head_label : nat; source_child_count : nat }.
Definition old_entry term policy marked children :=
  assemble (head_label term) policy marked children.
Definition checked_entry term policy marked children :=
  let label := head_label term in assemble label policy marked children.

Theorem factoring_preserves_every_local_observation :
  forall term policy marked children,
    checked_entry term policy marked children = old_entry term policy marked children.
Proof. reflexivity. Qed.

Theorem assembly_retains_order_and_multiplicity : forall name policy marked children,
  child_payloads (assemble name policy marked children) = map payload children.
Proof. reflexivity. Qed.

Theorem both_metadata_vectors_are_exact : forall name policy marked children,
  root_free (assemble name policy marked children) = combined_free children /\
  list_free (assemble name policy marked children) = combined_free children.
Proof. intros; split; reflexivity. Qed.

Theorem bound_free_and_unmarked_policies_are_unchanged : forall name children,
  marker (assemble name Bound true children) = Some false /\
  marker (assemble name Free true children) = Some true /\
  marker (assemble name Children false children) = None.
Proof. intros; repeat split; reflexivity. Qed.

(** Reference allocation trace: two allocations per child, then two copies of
    the final metadata. Empty vectors contribute zero bytes, not extra cases. *)
Fixpoint metadata_trace (accumulated : list N) (children : list Child) : list nat :=
  match children with
  | [] => [length accumulated; length accumulated]
  | entry :: rest =>
      let next := union_bytes accumulated (locally_free entry) in
      length (locally_free entry) :: length next :: metadata_trace next rest
  end.

Fixpoint metadata_size (current : nat) (lengths : list nat) : nat :=
  match lengths with
  | [] => 2 * current
  | size :: rest => size + Nat.max current size + metadata_size (Nat.max current size) rest
  end.

Theorem length_observer_counts_actual_metadata_copies : forall children accumulated,
  fold_right Nat.add 0 (metadata_trace accumulated children) =
    metadata_size (length accumulated) (map (fun entry => length (locally_free entry)) children).
Proof.
  induction children as [|entry rest IH]; intros accumulated; cbn [metadata_trace metadata_size map fold_right].
  - lia.
  - rewrite IH, union_bytes_length. lia.
Qed.

Fixpoint metadata_loop current charged lengths :=
  match lengths with
  | [] => charged + 2 * current
  | size :: rest =>
      let next := Nat.max current size in
      metadata_loop next (charged + size + next) rest
  end.

Theorem iterative_metadata_plan_matches_reference : forall lengths current charged,
  metadata_loop current charged lengths = charged + metadata_size current lengths.
Proof.
  induction lengths as [|size rest IH]; intros; cbn [metadata_loop metadata_size].
  - reflexivity.
  - rewrite IH. lia.
Qed.

Definition slot_count degree (marked : bool) :=
  (degree + 2) + (1 + if marked then 1 else 0) + 1.
Definition local_bytes scalar_bytes metadata_bytes degree marked :=
  scalar_bytes + metadata_bytes + 4 * slot_count degree marked.

Theorem local_allocation_requires_the_complete_allowance :
  forall ceiling used available scalars metadata degree marked balances,
    Budget.before_allocation ceiling used available
      (local_bytes scalars metadata degree marked)
      (local_bytes scalars metadata degree marked) =
      (Some balances, [Budget.AllocatePayload (local_bytes scalars metadata degree marked)]) ->
    local_bytes scalars metadata degree marked <= available.
Proof. intros. eapply Budget.emitted_allocation_is_within_byte_allowance; eauto. Qed.

Example padded_zero_metadata_is_not_canonicalized :
  union_bytes [1%N] [0%N; 0%N; 0%N] = [1%N; 0%N; 0%N].
Proof. reflexivity. Qed.

End ReflectedLocalAssembly.

Print Assumptions ReflectedLocalAssembly.factoring_preserves_every_local_observation.
Print Assumptions ReflectedLocalAssembly.assembly_retains_order_and_multiplicity.
Print Assumptions ReflectedLocalAssembly.both_metadata_vectors_are_exact.
Print Assumptions ReflectedLocalAssembly.bound_free_and_unmarked_policies_are_unchanged.
Print Assumptions ReflectedLocalAssembly.length_observer_counts_actual_metadata_copies.
Print Assumptions ReflectedLocalAssembly.iterative_metadata_plan_matches_reference.
Print Assumptions ReflectedLocalAssembly.local_allocation_requires_the_complete_allowance.
