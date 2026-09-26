(** * Explicit Core precedence observed through the existing byte-sized floors

    Core's production_precedence_valid compares declared u16 powers directly.
    JuxtapositionPrecedence proves that its strict/non-strict child predicate
    is a Pratt floor comparison. The generated WPDA instead carries u8 floors.
    This file proves the finite order representation between those interfaces;
    it does not introduce a recognizer or claim forest completeness.

    The Rust adapter collects the distinct powers of one category in a sorted
    set. Rank below counts strictly smaller entries; on that set it is exactly
    the enumeration index. Entries are 1..N, zero remains unrestricted, and
    255 represents an unranked child. N <= 254 is checked before publication.
    Strict descent uses the original checked successor operation, not wrapping
    arithmetic on the source power. Thus adjacent source levels and 65535 need
    no special case. Unsupported shape observations are explicit refusals.

    Category-leading applicability must be witnessed by the existing exact
    homogeneous binary-juxtaposition classifier and original BinderShape.
    The leading branch checks its own entry against the caller floor, descends
    at its declared left floor, preserves the caller continuation, and supplies
    its right floor to the existing rule_parameter body. All singleton/fork
    and primary/secondary lexical sites must consume the same observation.
    None categories retain the entire original analyzer/transition callback,
    including its state/trace; the default law does not assume callback purity.
    Source correspondence and actual parser tests remain separate obligations.
*)
From Stdlib Require Import List Arith Bool Lia Sorting.Sorted.
From RuntimeGrammar Require Import JuxtapositionPrecedence.
From PrattailWpdaRuntime Require Import BindingPowerAdmission.
Import ListNotations.

Module OwnedExplicitPrattLevels.

Fixpoint rank (levels : list nat) (power : nat) : nat :=
  match levels with
  | [] => 0
  | level :: rest => (if level <? power then 1 else 0) + rank rest power
  end.

Lemma rank_monotone : forall levels p q,
  p <= q -> rank levels p <= rank levels q.
Proof.
  induction levels as [|a rest IH]; intros p q H; simpl; [lia|].
  specialize (IH p q H).
  destruct (a <? p) eqn:A, (a <? q) eqn:B; simpl.
  - lia.
  - apply Nat.ltb_lt in A; apply Nat.ltb_ge in B; lia.
  - lia.
  - lia.
Qed.

Lemma rank_strict_at_member : forall levels p q,
  In p levels -> p < q -> rank levels p < rank levels q.
Proof.
  induction levels as [|a rest IH]; intros p q Member Order;
    simpl in Member; [contradiction|].
  simpl. destruct Member as [Same|Member].
  - subst a. rewrite Nat.ltb_irrefl.
    assert (Step : (p <? q) = true) by (apply Nat.ltb_lt; exact Order).
    rewrite Step; pose proof (rank_monotone rest p q (Nat.lt_le_incl _ _ Order)); lia.
  - specialize (IH p q Member Order).
    destruct (a <? p) eqn:A, (a <? q) eqn:B; simpl.
    + lia.
    + apply Nat.ltb_lt in A; apply Nat.ltb_ge in B; lia.
    + lia.
    + lia.
Qed.

Lemma rank_of_strictly_greater_suffix : forall levels p,
  Forall (fun q => p < q) levels -> rank levels p = 0.
Proof.
  intros levels p Above; induction Above; simpl; [reflexivity|].
  assert (NotBelow : (x <? p) = false) by (apply Nat.ltb_ge; lia).
  now rewrite NotBelow, IHAbove.
Qed.

(** The BTreeSet iteration used by Rust exposes precisely this strictly sorted
    distinct roster. Its zero-based enumerate index equals the model's count;
    no assumption that declaration order already follows precedence is used. *)
Theorem sorted_enumeration_is_count_less_rank : forall levels,
  StronglySorted lt levels -> forall index p,
  nth_error levels index = Some p -> rank levels p = index.
Proof.
  intros levels Sorted; induction Sorted as [|a rest Sorted IH Above];
    intros index p Found.
  - destruct index; discriminate.
  - destruct index as [|index].
    + simpl in Found; inversion Found; subst p.
      simpl; rewrite Nat.ltb_irrefl.
      now apply rank_of_strictly_greater_suffix.
    + simpl in Found.
      assert (Member : In p rest) by (eapply nth_error_In; exact Found).
      pose proof (proj1 (Forall_forall _ _) Above p Member) as Less.
      assert (Below : (a <? p) = true) by (apply Nat.ltb_lt; exact Less).
      simpl; rewrite Below; simpl; f_equal; now apply IH.
Qed.

Theorem rank_reflects_weak_order : forall levels p q,
  In p levels -> In q levels -> (rank levels p <= rank levels q <-> p <= q).
Proof.
  intros levels p q P Q; split; intro H.
  - destruct (Nat.le_gt_cases p q); [assumption|].
    pose proof (rank_strict_at_member levels q p Q H0); lia.
  - now apply rank_monotone.
Qed.

Theorem rank_reflects_strict_order : forall levels p q,
  In p levels -> In q levels -> (rank levels p < rank levels q <-> p < q).
Proof.
  intros levels p q P Q; split; intro H.
  - destruct (Nat.lt_ge_cases p q); [assumption|].
    pose proof (rank_monotone levels q p H0); lia.
  - now apply rank_strict_at_member.
Qed.

Lemma rank_bounded : forall levels p, rank levels p <= length levels.
Proof. induction levels; intros; simpl; [lia|]; specialize (IHlevels p); destruct (a <? p); simpl; lia. Qed.

Lemma member_rank_below_length : forall levels p,
  In p levels -> rank levels p < length levels.
Proof.
  induction levels as [|a rest IH]; intros p Member; simpl in *; [contradiction|].
  destruct Member as [Same|Member].
  - subst a; rewrite Nat.ltb_irrefl; pose proof (rank_bounded rest p); lia.
  - specialize (IH p Member); destruct (a <? p); simpl; lia.
Qed.

Definition entry levels power := S (rank levels power).
Definition floor levels power (allow_equal : bool) :=
  if allow_equal then entry levels power else S (entry levels power).
Definition child_entry levels child :=
  match child with None => 255 | Some power => entry levels power end.
Definition route_admits levels parent allow child :=
  floor levels parent allow <=? child_entry levels child.

Theorem ranked_floor_is_original_core_comparison : forall levels p q allow,
  In p levels -> In q levels ->
  route_admits levels p allow (Some q) = tighter p allow (Some q).
Proof.
  intros levels p q allow P Q.
  unfold route_admits, floor, child_entry, entry, tighter.
  pose proof (rank_reflects_weak_order levels p q P Q) as Weak.
  pose proof (rank_reflects_strict_order levels p q P Q) as Strict.
  apply eq_true_iff_eq.
  rewrite Nat.leb_le, orb_true_iff, andb_true_iff, Nat.ltb_lt, Nat.eqb_eq.
  destruct allow; simpl; lia.
Qed.

Theorem admitted_entry_and_strict_floor_fit : forall levels p,
  length levels <= 254 -> In p levels ->
  1 <= entry levels p /\ entry levels p <= 254 /\ floor levels p false <= 255.
Proof.
  intros levels p Capacity Member.
  pose proof (member_rank_below_length levels p Member).
  unfold floor, entry; simpl; lia.
Qed.

Theorem unranked_child_is_still_unconditionally_admitted : forall levels p allow,
  length levels <= 254 -> In p levels -> route_admits levels p allow None = true.
Proof.
  intros levels p allow Capacity Member.
  pose proof (admitted_entry_and_strict_floor_fit levels p Capacity Member).
  unfold route_admits, floor, child_entry; apply Nat.leb_le; destruct allow; lia.
Qed.

Theorem complete_child_observation_matches_core : forall levels p allow child,
  length levels <= 254 -> In p levels ->
  (match child with Some q => In q levels | None => True end) ->
  route_admits levels p allow child = tighter p allow child.
Proof.
  intros levels p allow [q|] Capacity P Q.
  - now apply ranked_floor_is_original_core_comparison.
  - now apply unranked_child_is_still_unconditionally_admitted.
Qed.

Definition left_equal assoc := match assoc with Left => true | _ => false end.
Definition right_equal assoc := match assoc with Right => true | _ => false end.
Definition binary_route levels assoc p left right :=
  route_admits levels p (left_equal assoc) left &&
  route_admits levels p (right_equal assoc) right.

Theorem both_operand_floors_match_original_associativity : forall levels assoc p left right,
  length levels <= 254 -> In p levels ->
  (match left with Some q => In q levels | None => True end) ->
  (match right with Some q => In q levels | None => True end) ->
  binary_route levels assoc p left right = binary_admission assoc p left right.
Proof.
  intros levels assoc p left right Capacity P L R.
  unfold binary_route.
  rewrite (complete_child_observation_matches_core levels p (left_equal assoc) left Capacity P L).
  rewrite (complete_child_observation_matches_core levels p (right_equal assoc) right Capacity P R).
  destruct assoc; reflexivity.
Qed.

Definition checked_strict_floor levels p :=
  BindingPowerAdmission.add (Some 255) 0 BindingPowerAdmission.InfixSlot (entry levels p) 1.
Theorem strict_floor_reuses_original_checked_successor : forall levels p,
  length levels <= 254 -> In p levels ->
  checked_strict_floor levels p = BindingPowerAdmission.Complete (floor levels p false).
Proof.
  intros levels p Capacity Member.
  pose proof (admitted_entry_and_strict_floor_fit levels p Capacity Member) as Bounds.
  unfold checked_strict_floor, floor; replace (S (entry levels p)) with (entry levels p + 1) by lia.
  apply BindingPowerAdmission.checked_add_fits; simpl in Bounds; lia.
Qed.

Inductive Refusal := CapacityExhausted | UnsupportedShape.
Definition publish (supported : bool) (levels : list nat) :
    (Refusal + list (nat * nat))%type :=
  if supported then
    if length levels <=? 254 then inr (map (fun p => (p, entry levels p)) levels)
    else inl CapacityExhausted
  else inl UnsupportedShape.
Theorem capacity_failure_publishes_no_partial_table : forall levels,
  254 < length levels -> publish true levels = inl CapacityExhausted.
Proof. intros; unfold publish; assert ((length levels <=? 254) = false) by (apply Nat.leb_gt; lia); now rewrite H0. Qed.
Theorem unsupported_shape_is_not_defaulted : forall levels,
  publish false levels = inl UnsupportedShape.
Proof. reflexivity. Qed.
Theorem successful_publication_retains_all_level_identities : forall levels,
  length levels <= 254 ->
  publish true levels = inr (map (fun p => (p, entry levels p)) levels).
Proof. intros; unfold publish; apply Nat.leb_le in H; now rewrite H. Qed.

Section DefaultAndContinuation.
Context {Input Output : Type}.
Variable original : Input -> Output.
Variable explicit : nat -> Input -> Output.
Definition select_mode observation input :=
  match observation with None => original input | Some level => explicit level input end.
Theorem none_retains_complete_original_callback : forall input,
  select_mode None input = original input.
Proof. reflexivity. Qed.
End DefaultAndContinuation.

Definition leading_descent levels assoc p caller :=
  if caller <=? entry levels p
  then Some (floor levels p (left_equal assoc), floor levels p (right_equal assoc), caller)
  else None.
Theorem leading_descent_preserves_caller_continuation : forall levels assoc p caller left right saved,
  leading_descent levels assoc p caller = Some (left, right, saved) -> saved = caller.
Proof. intros; unfold leading_descent in H; destruct (caller <=? entry levels p); inversion H; reflexivity. Qed.
Theorem leading_rule_is_blocked_above_its_own_entry : forall levels assoc p caller,
  entry levels p < caller -> leading_descent levels assoc p caller = None.
Proof. intros; unfold leading_descent; assert ((caller <=? entry levels p) = false) by (apply Nat.leb_gt; lia); now rewrite H0. Qed.

Example adjacent_and_maximum_source_levels_remain_distinct :
  map (entry [10; 11; 65535]) [10; 11; 65535] = [1; 2; 3].
Proof. vm_compute; reflexivity. Qed.
Example top_strict_floor_admits_only_unranked_at_that_boundary :
  route_admits (seq 0 254) 253 false (Some 253) = false /\
  route_admits (seq 0 254) 253 false None = true.
Proof. vm_compute; split; reflexivity. Qed.
Example regex_left_concat_keeps_left_nesting_and_stops_rhs_alt :
  leading_descent [10;20;30] Left 20 0 = Some (2,3,0) /\
  leading_descent [10;20;30] Left 20 2 = Some (2,3,2) /\
  leading_descent [10;20;30] Left 20 3 = None /\
  route_admits [10;20;30] 20 false (Some 10) = false /\
  route_admits [10;20;30] 20 false (Some 30) = true.
Proof. repeat split; reflexivity. Qed.

Print Assumptions rank_reflects_weak_order.
Print Assumptions rank_reflects_strict_order.
Print Assumptions sorted_enumeration_is_count_less_rank.
Print Assumptions ranked_floor_is_original_core_comparison.
Print Assumptions admitted_entry_and_strict_floor_fit.
Print Assumptions unranked_child_is_still_unconditionally_admitted.
Print Assumptions complete_child_observation_matches_core.
Print Assumptions both_operand_floors_match_original_associativity.
Print Assumptions strict_floor_reuses_original_checked_successor.
Print Assumptions capacity_failure_publishes_no_partial_table.
Print Assumptions unsupported_shape_is_not_defaulted.
Print Assumptions successful_publication_retains_all_level_identities.
Print Assumptions none_retains_complete_original_callback.
Print Assumptions leading_descent_preserves_caller_continuation.
Print Assumptions leading_rule_is_blocked_above_its_own_entry.
Print Assumptions adjacent_and_maximum_source_levels_remain_distinct.
Print Assumptions top_strict_floor_admits_only_unranked_at_that_boundary.
Print Assumptions regex_left_concat_keeps_left_nesting_and_stops_rhs_alt.
End OwnedExplicitPrattLevels.
