(** Concrete destination-map refinement for moving owned result records.

    Source algorithm: vinary-requirements/crates/vinary-math-ir/src/canonical.rs,
    reorder_in_place. A checked index permutation first initializes
    destination[order[d]] := d. The movement loop swaps both the whole-record
    array and destination array at i and destination[i], until i is fixed.

    Arrays are finite pointwise views. No equality of functions, functional
    extensionality, record cloning, or equality decision on records is required.
    After the first swap the scratch array is NOT the inverse of order: it is
    the desired destination of the record currently at each position.
    This model establishes that distinction and the movement invariants; it
    does not certify the receipt comparator or the concrete Rust allocator. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Lia.
From RuntimeGrammar Require Import SemanticResultMerge.
Import ListNotations.

Module SemanticResultPermutation.

Definition BoundedInjective count (f : nat -> nat) :=
  (forall p, p < count -> f p < count) /\
  (forall p q, p < count -> q < count -> f p = f q -> p = q).

Theorem index_permutation_is_bijective : forall count indices,
  Permutation (seq 0 count) indices ->
  BoundedInjective count (fun p => nth p indices count) /\
  (forall source, source < count -> exists p,
    p < count /\ nth p indices count = source).
Proof.
  intros count indices P.
  assert (L : length indices = count).
  { pose proof (Permutation_length P). rewrite length_seq in H. lia. }
  assert (N : NoDup indices) by (eapply Permutation_NoDup; [exact P | apply seq_NoDup]).
  split.
  - split.
    + intros p B.
      assert (I : In (nth p indices count) (seq 0 count)).
      { eapply Permutation_in; [apply Permutation_sym; exact P |].
        apply nth_In. now rewrite L. }
      apply in_seq in I. lia.
    + intros p q BP BQ E. apply (proj1 (NoDup_nth indices count) N);
        rewrite ?L; assumption.
  - intros source B.
    assert (I : In source indices).
    { eapply Permutation_in; [exact P | apply in_seq; lia]. }
    destruct (In_nth indices source count I) as [p [BP E]].
    exists p. rewrite L in BP. split; assumption.
Qed.

Definition write_at {A : Type} (values : nat -> A) position value p :=
  if Nat.eq_dec p position then value else values p.

Fixpoint inverse_prefix count length (order : nat -> nat) : nat -> nat :=
  match length with
  | 0 => fun _ => count
  | S previous => write_at (inverse_prefix count previous order) (order previous) previous
  end.

Lemma inverse_prefix_assigned : forall count order,
  BoundedInjective count order -> forall length p,
  length <= count -> p < length -> inverse_prefix count length order (order p) = p.
Proof.
  intros count order [bounded injective] length. induction length as [|length IH];
    intros p L B; [lia |]. cbn [inverse_prefix]. unfold write_at.
  destruct (Nat.eq_dec (order p) (order length)) as [E | E].
  - assert (p = length) by (apply (injective p length); [lia | lia | exact E]). lia.
  - apply IH; [lia |]. assert (p <> length) by congruence. lia.
Qed.

Lemma inverse_prefix_unassigned : forall count order length source,
  (forall p, p < length -> order p <> source) ->
  inverse_prefix count length order source = count.
Proof.
  intros count order length. induction length as [|length IH]; intros source H;
    [reflexivity |]. cbn [inverse_prefix]. unfold write_at.
  destruct (Nat.eq_dec source (order length)) as [E | E].
  - exfalso. apply (H length); [lia | symmetry; exact E].
  - apply IH. intros p B. apply H. lia.
Qed.

Theorem inverse_next_slot_is_unassigned : forall count order length,
  BoundedInjective count order -> length < count ->
  inverse_prefix count length order (order length) = count.
Proof.
  intros count order length [_ injective] L. apply inverse_prefix_unassigned.
  intros p B E. assert (p = length) by (apply (injective p length); [lia | exact L | exact E]). lia.
Qed.

Theorem initialized_inverse_is_two_sided : forall count order,
  BoundedInjective count order ->
  (forall source, source < count -> exists p, p < count /\ order p = source) ->
  (forall p, p < count -> inverse_prefix count count order (order p) = p) /\
  (forall source, source < count ->
    inverse_prefix count count order source < count /\
    order (inverse_prefix count count order source) = source).
Proof.
  intros count order BI onto. split.
  - intros p B. apply inverse_prefix_assigned; auto.
  - intros source B. destruct (onto source B) as [p [BP E]].
    subst source. rewrite inverse_prefix_assigned by auto. split; [exact BP | reflexivity].
Qed.

Theorem initialized_inverse_is_bounded_injective : forall count order,
  BoundedInjective count order ->
  (forall source, source < count -> exists p, p < count /\ order p = source) ->
  BoundedInjective count (inverse_prefix count count order).
Proof.
  intros count order BI onto.
  destruct (initialized_inverse_is_two_sided count order BI onto) as [left right].
  split.
  - intros source B. apply (right source B).
  - intros p q BP BQ E.
    destruct (right p BP) as [_ P]. destruct (right q BQ) as [_ Q].
    rewrite E in P. congruence.
Qed.

Definition exchange_index i j p :=
  if Nat.eq_dec p i then j else if Nat.eq_dec p j then i else p.

Definition exchange {A : Type} (values : nat -> A) i j p := values (exchange_index i j p).

Lemma exchange_index_involutive : forall i j p,
  exchange_index i j (exchange_index i j p) = p.
Proof.
  intros. unfold exchange_index.
  repeat destruct Nat.eq_dec; subst; congruence.
Qed.

Lemma exchange_index_bounded : forall count i j p,
  i < count -> j < count -> p < count -> exchange_index i j p < count.
Proof.
  intros. unfold exchange_index. repeat destruct Nat.eq_dec; assumption.
Qed.

Theorem exchange_preserves_bounded_injectivity : forall count destination i j,
  BoundedInjective count destination -> i < count -> j < count ->
  BoundedInjective count (exchange destination i j).
Proof.
  intros count destination i j [bounded injective] I J. split.
  - intros p P. apply bounded. apply exchange_index_bounded; assumption.
  - intros p q P Q E. unfold exchange in E.
    assert (X : exchange_index i j p = exchange_index i j q).
    { eapply injective; [apply exchange_index_bounded; eauto |
        apply exchange_index_bounded; eauto | exact E]. }
    apply (f_equal (exchange_index i j)) in X.
    now rewrite !exchange_index_involutive in X.
Qed.

Theorem destination_swap_fixes_target : forall destination i,
  destination i <> i ->
  exchange destination i (destination i) (destination i) = destination i.
Proof.
  intros destination i NE. unfold exchange, exchange_index.
  repeat destruct Nat.eq_dec; congruence.
Qed.

Theorem destination_swap_preserves_fixed_positions : forall count destination i p,
  BoundedInjective count destination -> i < count -> p < count ->
  destination i <> i -> destination p = p ->
  exchange destination i (destination i) p = p.
Proof.
  intros count destination i p [bounded injective] I P NE fixed.
  unfold exchange, exchange_index.
  destruct (Nat.eq_dec p i) as [E | E]; [subst; contradiction |].
  destruct (Nat.eq_dec p (destination i)) as [J | J]; [| exact fixed].
  assert (i = p) by (eapply injective; eauto; congruence). congruence.
Qed.

Definition Paired {A : Type} count (original values : nat -> A)
    (order destination : nat -> nat) :=
  forall p, p < count -> values p = original (order (destination p)).

Theorem initialization_pairs_original_records : forall (A : Type) count
  (original : nat -> A) order,
  BoundedInjective count order ->
  (forall source, source < count -> exists p, p < count /\ order p = source) ->
  Paired count original original order (inverse_prefix count count order).
Proof.
  intros A count original order BI onto p P.
  destruct (initialized_inverse_is_two_sided count order BI onto) as [_ right].
  destruct (right p P) as [_ E]. now rewrite E.
Qed.

Theorem simultaneous_swap_preserves_whole_record_pairing : forall (A : Type) count
  (original values : nat -> A) order destination i j,
  Paired count original values order destination -> i < count -> j < count ->
  Paired count original (exchange values i j) order (exchange destination i j).
Proof.
  intros A count original values order destination i j paired I J p P.
  unfold exchange. apply paired. apply exchange_index_bounded; assumption.
Qed.

Theorem fixed_destinations_realize_the_requested_order : forall (A : Type) count
  (original values : nat -> A) order destination,
  Paired count original values order destination ->
  (forall p, p < count -> destination p = p) ->
  forall p, p < count -> values p = original (order p).
Proof.
  intros A count original values order destination paired fixed p P.
  rewrite paired, fixed by exact P. reflexivity.
Qed.

Fixpoint count_true count (predicate : nat -> bool) :=
  match count with
  | 0 => 0
  | S previous => count_true previous predicate + if predicate previous then 1 else 0
  end.

Lemma count_true_monotone : forall count newer older,
  (forall p, p < count -> newer p = true -> older p = true) ->
  count_true count newer <= count_true count older.
Proof.
  induction count as [|count IH]; intros newer older H; [cbn; lia |].
  cbn [count_true]. assert (B : count_true count newer <= count_true count older).
  { apply IH. intros. apply H; auto; lia. }
  specialize (H count ltac:(lia)). destruct (newer count), (older count); cbn in *;
    try lia; specialize (H eq_refl); discriminate.
Qed.

Lemma count_true_strict : forall count newer older witness,
  (forall p, p < count -> newer p = true -> older p = true) ->
  witness < count -> newer witness = false -> older witness = true ->
  count_true count newer < count_true count older.
Proof.
  induction count as [|count IH]; intros newer older witness mono B N O; [lia |].
  cbn [count_true]. destruct (Nat.eq_dec witness count) as [E | E].
  - subst witness. rewrite N, O.
    assert (L : count_true count newer <= count_true count older).
    { apply count_true_monotone. intros. apply mono; auto; lia. } lia.
  - assert (L : count_true count newer < count_true count older).
    { eapply (IH newer older witness); [| lia | exact N | exact O].
      intros. apply mono; auto; lia. }
    specialize (mono count ltac:(lia)). destruct (newer count), (older count); cbn in *;
      try lia; specialize (mono eq_refl); discriminate.
Qed.

Definition nonfixed count destination :=
  count_true count (fun p => negb (Nat.eqb (destination p) p)).

Theorem destination_swap_strictly_decreases_nonfixed : forall count destination i,
  BoundedInjective count destination -> i < count -> destination i <> i ->
  nonfixed count (exchange destination i (destination i)) < nonfixed count destination.
Proof.
  intros count destination i BI I NE. destruct BI as [bounded injective].
  unfold nonfixed. eapply count_true_strict with (witness := destination i).
  - intros p P H.
    destruct (Nat.eqb (destination p) p) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E.
    pose proof (destination_swap_preserves_fixed_positions count destination i p
      (conj bounded injective) I P NE E) as F.
    rewrite F, Nat.eqb_refl in H. discriminate.
  - apply bounded; exact I.
  - rewrite destination_swap_fixes_target by exact NE. now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb (destination (destination i)) (destination i)) eqn:E;
      [| reflexivity].
    apply Nat.eqb_eq in E. exfalso. apply NE.
    eapply injective; [apply bounded; exact I | exact I | exact E].
Qed.

Lemma count_true_bound : forall count predicate, count_true count predicate <= count.
Proof.
  induction count; intros predicate; cbn [count_true]; [lia |].
  specialize (IHcount predicate). destruct (predicate count); lia.
Qed.

Record LoopResult (A : Type) := {
  final_records : nat -> A;
  final_destinations : nat -> nat;
  swap_count : nat
}.
Arguments final_records {A} _ _.
Arguments final_destinations {A} _ _.
Arguments swap_count {A} _.

Definition count_swap {A : Type} (result : LoopResult A) :=
  {| final_records := final_records result;
     final_destinations := final_destinations result;
     swap_count := S (swap_count result) |}.

(** One transition is either an outer-cursor advance or a simultaneous swap.
    Counting swaps here is ghost instrumentation for the prepaid work bound;
    it is not a semantic execution charge or another production counter. *)
Fixpoint reorder {A : Type} fuel count cursor (values : nat -> A) destination
    : option (LoopResult A) :=
  if cursor <? count then
    match fuel with
    | 0 => None
    | S smaller =>
        if Nat.eqb (destination cursor) cursor then
          reorder smaller count (S cursor) values destination
        else
          option_map count_swap (reorder smaller count cursor
            (exchange values cursor (destination cursor))
            (exchange destination cursor (destination cursor)))
    end
  else Some {| final_records := values;
               final_destinations := destination;
               swap_count := 0 |}.

Theorem reorder_completes_with_requested_records : forall (A : Type) fuel count cursor
  (original values : nat -> A) order destination,
  BoundedInjective count destination -> cursor <= count ->
  Paired count original values order destination ->
  (forall p, p < cursor -> destination p = p) ->
  count - cursor + nonfixed count destination <= fuel ->
  exists result,
    reorder fuel count cursor values destination = Some result /\
    (forall p, p < count -> final_records result p = original (order p)) /\
    swap_count result <= nonfixed count destination.
Proof.
  intros A fuel. induction fuel as [|fuel IH];
    intros count cursor original values order destination BI cursor_bound paired prefix potential;
    cbn [reorder]; destruct (cursor <? count) eqn:active.
  - apply Nat.ltb_lt in active. lia.
  - apply Nat.ltb_ge in active.
    exists {| final_records := values; final_destinations := destination; swap_count := 0 |}.
    split; [reflexivity |]. split; [| cbn; lia].
    cbn. apply (fixed_destinations_realize_the_requested_order A count original values
      order destination paired). intros p P. apply prefix. lia.
  - apply Nat.ltb_lt in active.
    destruct (Nat.eqb (destination cursor) cursor) eqn:fixed.
    + apply Nat.eqb_eq in fixed.
      assert (next_prefix : forall p, p < S cursor -> destination p = p).
      { intros p P. destruct (Nat.eq_dec p cursor); [subst; exact fixed | apply prefix; lia]. }
      apply (IH count (S cursor) original values order destination BI ltac:(lia)
        paired next_prefix). lia.
    + apply Nat.eqb_neq in fixed.
      assert (target_bound : destination cursor < count) by (apply BI; exact active).
      assert (next_BI : BoundedInjective count (exchange destination cursor (destination cursor))).
      { apply exchange_preserves_bounded_injectivity; assumption. }
      assert (next_paired : Paired count original
        (exchange values cursor (destination cursor)) order
        (exchange destination cursor (destination cursor))).
      { apply simultaneous_swap_preserves_whole_record_pairing; assumption. }
      assert (next_prefix : forall p, p < cursor ->
        exchange destination cursor (destination cursor) p = p).
      { intros p P. apply (destination_swap_preserves_fixed_positions count destination cursor p
          BI active ltac:(lia) fixed). apply prefix; exact P. }
      pose proof (destination_swap_strictly_decreases_nonfixed count destination cursor
        BI active fixed) as decrease.
      destruct (IH count cursor original (exchange values cursor (destination cursor)) order
        (exchange destination cursor (destination cursor)) next_BI cursor_bound next_paired
        next_prefix ltac:(lia)) as [result [run [records bound]]].
      rewrite run. exists (count_swap result). split; [reflexivity |].
      split; [exact records | cbn [count_swap swap_count]; lia].
  - apply Nat.ltb_ge in active.
    exists {| final_records := values; final_destinations := destination; swap_count := 0 |}.
    split; [reflexivity |]. split; [| cbn; lia].
    cbn. apply (fixed_destinations_realize_the_requested_order A count original values
      order destination paired). intros p P. apply prefix. lia.
Qed.

Theorem checked_index_permutation_moves_whole_records : forall (A : Type) count indices
  (original : nat -> A),
  Permutation (seq 0 count) indices ->
  let order := fun p => nth p indices count in
  exists result,
    reorder (2 * count) count 0 original (inverse_prefix count count order) = Some result /\
    (forall p, p < count -> final_records result p = original (order p)) /\
    swap_count result <= count.
Proof.
  intros A count indices original P order.
  destruct (index_permutation_is_bijective count indices P) as [BI onto].
  assert (inverse_BI : BoundedInjective count (inverse_prefix count count order)).
  { apply initialized_inverse_is_bounded_injective; assumption. }
  assert (paired : Paired count original original order (inverse_prefix count count order)).
  { apply initialization_pairs_original_records; assumption. }
  assert (bound : nonfixed count (inverse_prefix count count order) <= count)
    by apply count_true_bound.
  destruct (reorder_completes_with_requested_records A (2 * count) count 0 original original
    order (inverse_prefix count count order) inverse_BI ltac:(lia) paired
    ltac:(intros; lia) ltac:(lia)) as [result [run [records swaps]]].
  exists result. split; [exact run |]. split; [exact records | lia].
Qed.

Theorem merge_order_moves_whole_records : forall (A State : Type)
  (compare : nat -> nat -> State -> option comparison * State) count state indices final
  (original : nat -> A),
  SemanticResultMerge.SemanticResultMerge.sort compare (seq 0 count) state =
    (Some indices, final) ->
  let order := fun p => nth p indices count in
  exists result,
    reorder (2 * count) count 0 original (inverse_prefix count count order) = Some result /\
    (forall p, p < count -> final_records result p = original (order p)) /\
    swap_count result <= count.
Proof.
  intros A State compare count state indices final original H.
  apply checked_index_permutation_moves_whole_records.
  eapply SemanticResultMerge.SemanticResultMerge.sort_preserves_occurrences; exact H.
Qed.

End SemanticResultPermutation.

Print Assumptions SemanticResultPermutation.index_permutation_is_bijective.
Print Assumptions SemanticResultPermutation.inverse_next_slot_is_unassigned.
Print Assumptions SemanticResultPermutation.initialized_inverse_is_two_sided.
Print Assumptions SemanticResultPermutation.initialized_inverse_is_bounded_injective.
Print Assumptions SemanticResultPermutation.exchange_preserves_bounded_injectivity.
Print Assumptions SemanticResultPermutation.destination_swap_fixes_target.
Print Assumptions SemanticResultPermutation.destination_swap_preserves_fixed_positions.
Print Assumptions SemanticResultPermutation.initialization_pairs_original_records.
Print Assumptions SemanticResultPermutation.simultaneous_swap_preserves_whole_record_pairing.
Print Assumptions SemanticResultPermutation.fixed_destinations_realize_the_requested_order.
Print Assumptions SemanticResultPermutation.destination_swap_strictly_decreases_nonfixed.
Print Assumptions SemanticResultPermutation.reorder_completes_with_requested_records.
Print Assumptions SemanticResultPermutation.checked_index_permutation_moves_whole_records.
Print Assumptions SemanticResultPermutation.merge_order_moves_whole_records.
