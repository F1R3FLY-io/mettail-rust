From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Module RewriteFamilyAllocator.

Section Allocator.
Context {Name : Type}.
Variable equal : Name -> Name -> bool.
Hypothesis equal_exact : forall left right, equal left right = true <-> left = right.
Variable encode : nat -> Name.
Hypothesis encode_injective : forall left right, encode left = encode right -> left = right.

Definition reserved_member name reserved := existsb (equal name) reserved.

Lemma reserved_member_exact : forall name reserved,
  reserved_member name reserved = true <-> In name reserved.
Proof.
  intros. unfold reserved_member. rewrite existsb_exists. split.
  - intros [other [Hin Heq]]. apply equal_exact in Heq. now subst.
  - intros Hin. exists name. split; [assumption|apply equal_exact; reflexivity].
Qed.

Fixpoint search fuel reserved next : option (Name * nat) :=
  match fuel with
  | 0 => None
  | S remaining =>
      if reserved_member (encode next) reserved
      then search remaining reserved (S next)
      else Some (encode next, S next)
  end.

Definition allocate capacity reserved next := search (capacity - next) reserved next.

Theorem search_success_contract : forall fuel reserved next name after,
  search fuel reserved next = Some (name, after) ->
  ~ In name reserved /\ next < after /\ after <= next + fuel /\
  name = encode (after - 1).
Proof.
  induction fuel as [|fuel IH]; intros reserved next name after H; simpl in H; [discriminate|].
  destruct (reserved_member (encode next) reserved) eqn:Hmember.
  - specialize (IH reserved (S next) name after H). destruct IH as [Hfresh [Hnext [Hbound Hname]]].
    repeat split; try assumption; lia.
  - inversion H; subst. repeat split; try lia.
    + intros Hin. apply reserved_member_exact in Hin. congruence.
    + f_equal. lia.
Qed.

Theorem search_refusal_is_exact : forall fuel reserved next,
  search fuel reserved next = None <->
  forall index, next <= index < next + fuel -> In (encode index) reserved.
Proof.
  induction fuel as [|fuel IH]; intros reserved next; simpl.
  - split; [intros _ index H; lia|reflexivity].
  - destruct (reserved_member (encode next) reserved) eqn:Hmember.
    + apply reserved_member_exact in Hmember. rewrite IH. split.
      * intros H index Hrange. destruct (Nat.eq_dec index next); [now subst|apply H; lia].
      * intros H index Hrange. apply H. lia.
    + split; [discriminate|]. intros H.
      specialize (H next ltac:(lia)). apply reserved_member_exact in H. congruence.
Qed.

Theorem checked_allocation_preserves_counter_bound : forall capacity reserved next name after,
  allocate capacity reserved next = Some (name, after) ->
  next < after /\ after <= capacity /\ ~ In name reserved.
Proof.
  intros capacity reserved next name after H. unfold allocate in H.
  apply search_success_contract in H. destruct H as [Hfresh [Hnext [Hbound Hname]]].
  repeat split; try assumption. lia.
Qed.

Theorem exhausted_counter_refuses_atomically : forall capacity reserved next,
  capacity <= next -> allocate capacity reserved next = None.
Proof.
  intros. unfold allocate. replace (capacity - next) with 0 by lia. reflexivity.
Qed.

Theorem successful_allocations_with_monotone_counters_are_distinct :
  forall capacity reserved next first after_first later second after_second,
  allocate capacity reserved next = Some (first, after_first) ->
  after_first <= later ->
  allocate capacity reserved later = Some (second, after_second) ->
  first <> second.
Proof.
  intros capacity reserved next first after_first later second after_second Hfirst Horder Hsecond Heq.
  unfold allocate in Hfirst, Hsecond.
  apply search_success_contract in Hfirst. apply search_success_contract in Hsecond.
  destruct Hfirst as [_ [Hfirst [_ Efirst]]]. destruct Hsecond as [_ [Hsecond [_ Esecond]]].
  rewrite Efirst, Esecond in Heq. apply encode_injective in Heq. lia.
Qed.

Theorem one_free_representable_candidate_guarantees_success :
  forall capacity reserved next index,
  next <= index < capacity -> ~ In (encode index) reserved ->
  exists name after, allocate capacity reserved next = Some (name, after).
Proof.
  intros capacity reserved next index Hrange Hfresh.
  unfold allocate. destruct (search (capacity - next) reserved next) as [[name after]|] eqn:Hsearch.
  - now exists name, after.
  - pose proof (proj1 (search_refusal_is_exact (capacity - next) reserved next) Hsearch) as Hall.
    exfalso. apply Hfresh. apply Hall. lia.
Qed.

End Allocator.
End RewriteFamilyAllocator.

Print Assumptions RewriteFamilyAllocator.search_success_contract.
Print Assumptions RewriteFamilyAllocator.search_refusal_is_exact.
Print Assumptions RewriteFamilyAllocator.checked_allocation_preserves_counter_bound.
Print Assumptions RewriteFamilyAllocator.exhausted_counter_refuses_atomically.
Print Assumptions RewriteFamilyAllocator.successful_allocations_with_monotone_counters_are_distinct.
Print Assumptions RewriteFamilyAllocator.one_free_representable_candidate_guarantees_success.
