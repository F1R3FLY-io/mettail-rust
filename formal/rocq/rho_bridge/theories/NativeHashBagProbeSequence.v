(** Finite triangular residues for the pinned native group probe.
    hashbrown 0.17.1 raw.rs:82 increments stride by Group::WIDTH (16),
    adds that stride to pos, and masks by buckets - 1; raw.rs:2448 starts
    with stride zero and pos = h1(hash) & (buckets - 1).

    This first checkpoint is integer algebra, not an executable replacement
    probe. For B = 16*q and initial position 16*a+r, the mathematical starts
    have the SAME residue r modulo 16. They are shifted unaligned windows,
    not the canonical aligned groups used by the sequential scan model.

    The Rust additions are plain usize additions, not wrapping operations.
    Relating these identities to every actual machine step still requires
    the valid-layout bound and the reached-prefix nonoverflow guards. The
    allocated B=4/8 and singleton cases, mirrored control-window projection,
    EMPTY existence, callback bounds and complete loop accounting remain
    separate obligations. No such source coverage follows from this file.

    Injectivity below is derived, not assumed: an equal triangular residue
    would make 2*q divide the product (i-j)*(i+j+1). The factors have opposite
    parity; Stdlib Gauss and power coprimality cancel the odd factor, leaving
    a positive multiple of 2*q strictly smaller than 2*q. *)
From Stdlib Require Import Lists.List Sorting.Permutation
  ZArith.BinInt ZArith.Znat ZArith.Znumtheory ZArith.Zpow_facts Lia.
Import ListNotations.
Open Scope Z_scope.

Module NativeHashBagProbeSequence.

Fixpoint triangle (step : nat) : Z :=
  match step with
  | O => 0
  | S previous => triangle previous + Z.of_nat (S previous)
  end.

Definition group_modulus (exponent : nat) : Z := 2 ^ Z.of_nat exponent.
Definition triangular_residue (exponent step : nat) : nat :=
  Z.to_nat (triangle step mod group_modulus exponent).

Lemma group_modulus_is_positive : forall exponent,
  0 < group_modulus exponent.
Proof.
  intro exponent. unfold group_modulus.
  apply Z.pow_pos_nonneg; [lia|apply Nat2Z.is_nonneg].
Qed.

Lemma next_group_modulus_is_double : forall exponent,
  group_modulus (S exponent) = 2 * group_modulus exponent.
Proof.
  intro exponent. unfold group_modulus. rewrite Nat2Z.inj_succ.
  apply Z.pow_succ_r. apply Nat2Z.is_nonneg.
Qed.

Theorem twice_triangle_has_its_original_polynomial : forall step,
  2 * triangle step = Z.of_nat step * (Z.of_nat step + 1).
Proof.
  intro step. induction step as [|step IH].
  - reflexivity.
  - cbn [triangle]. rewrite Nat2Z.inj_succ. unfold Z.succ. nia.
Qed.

Lemma group_modulus_is_coprime_to_every_odd_integer : forall exponent value,
  Z.Odd value -> rel_prime (group_modulus exponent) value.
Proof.
  intros exponent value [half ODD]. unfold group_modulus.
  apply rel_prime_sym. apply rel_prime_Zpower_r.
  - apply Nat2Z.is_nonneg.
  - apply rel_prime_sym. apply prime_rel_prime; [apply prime_2|].
    intros [multiple DIVIDES]. lia.
Qed.

Theorem strictly_ordered_triangles_have_distinct_residues :
  forall exponent earlier later,
  (earlier < later)%nat -> Z.of_nat later < group_modulus exponent ->
  triangle earlier mod group_modulus exponent <>
    triangle later mod group_modulus exponent.
Proof.
  intros exponent earlier later ORDER BOUND SAME.
  pose proof (group_modulus_is_positive exponent) as POSITIVE.
  pose proof (Nat2Z.is_nonneg earlier) as EARLIER_NONNEGATIVE.
  apply Nat2Z.inj_lt in ORDER.
  pose proof (Z.div_mod (triangle earlier) (group_modulus exponent)
    ltac:(lia)) as EARLIER_DIVISION.
  pose proof (Z.div_mod (triangle later) (group_modulus exponent)
    ltac:(lia)) as LATER_DIVISION.
  pose proof (twice_triangle_has_its_original_polynomial earlier) as EARLIER_POLYNOMIAL.
  pose proof (twice_triangle_has_its_original_polynomial later) as LATER_POLYNOMIAL.
  assert (PRODUCT : (2 * group_modulus exponent |
    (Z.of_nat later - Z.of_nat earlier) *
    (Z.of_nat later + Z.of_nat earlier + 1))).
  { exists (triangle later / group_modulus exponent -
      triangle earlier / group_modulus exponent). nia. }
  destruct (Z.Even_or_Odd (Z.of_nat later - Z.of_nat earlier))
    as [[half EVEN]|ODD].
  - assert (ODD_SUM : Z.Odd (Z.of_nat later + Z.of_nat earlier + 1)).
    { exists (Z.of_nat earlier + half). lia. }
    assert (COPRIME : rel_prime (2 * group_modulus exponent)
      (Z.of_nat later + Z.of_nat earlier + 1)).
    { rewrite <- next_group_modulus_is_double.
      apply group_modulus_is_coprime_to_every_odd_integer. exact ODD_SUM. }
    assert (DIVIDES : (2 * group_modulus exponent |
      Z.of_nat later - Z.of_nat earlier)).
    { eapply Gauss; [|exact COPRIME].
      rewrite (Z.mul_comm (Z.of_nat later + Z.of_nat earlier + 1)
        (Z.of_nat later - Z.of_nat earlier)). exact PRODUCT. }
    pose proof (Z.divide_pos_le (2 * group_modulus exponent)
      (Z.of_nat later - Z.of_nat earlier) ltac:(lia) DIVIDES). lia.
  - assert (COPRIME : rel_prime (2 * group_modulus exponent)
      (Z.of_nat later - Z.of_nat earlier)).
    { rewrite <- next_group_modulus_is_double.
      apply group_modulus_is_coprime_to_every_odd_integer. exact ODD. }
    assert (DIVIDES : (2 * group_modulus exponent |
      Z.of_nat later + Z.of_nat earlier + 1)).
    { eapply Gauss; [exact PRODUCT|exact COPRIME]. }
    pose proof (Z.divide_pos_le (2 * group_modulus exponent)
      (Z.of_nat later + Z.of_nat earlier + 1) ltac:(lia) DIVIDES). lia.
Qed.

Lemma triangular_residue_is_in_the_finite_range : forall exponent step,
  (triangular_residue exponent step < Z.to_nat (group_modulus exponent))%nat.
Proof.
  intros exponent step. unfold triangular_residue.
  pose proof (group_modulus_is_positive exponent) as POSITIVE.
  pose proof (Z.mod_pos_bound (triangle step) (group_modulus exponent) POSITIVE) as RANGE.
  apply (proj1 (Z2Nat.inj_lt (triangle step mod group_modulus exponent)
    (group_modulus exponent) ltac:(lia) ltac:(lia))). exact (proj2 RANGE).
Qed.

Lemma triangular_residue_is_injective_on_the_finite_range :
  forall exponent left right,
  (left < Z.to_nat (group_modulus exponent))%nat ->
  (right < Z.to_nat (group_modulus exponent))%nat ->
  triangular_residue exponent left = triangular_residue exponent right -> left = right.
Proof.
  intros exponent left right LEFT RIGHT SAME.
  pose proof (group_modulus_is_positive exponent) as POSITIVE.
  apply Nat2Z.inj_lt in LEFT. apply Nat2Z.inj_lt in RIGHT.
  rewrite Z2Nat.id in LEFT, RIGHT by lia.
  unfold triangular_residue in SAME.
  pose proof (Z.mod_pos_bound (triangle left) (group_modulus exponent) POSITIVE) as LEFT_RANGE.
  pose proof (Z.mod_pos_bound (triangle right) (group_modulus exponent) POSITIVE) as RIGHT_RANGE.
  assert (SAME_RESIDUE : triangle left mod group_modulus exponent =
    triangle right mod group_modulus exponent).
  { apply Z2Nat.inj; [lia|lia|exact SAME]. }
  destruct (Nat.lt_trichotomy left right) as [LESS|[EQUAL|GREATER]].
  - exfalso. exact (strictly_ordered_triangles_have_distinct_residues
      exponent left right LESS RIGHT SAME_RESIDUE).
  - exact EQUAL.
  - exfalso. exact (strictly_ordered_triangles_have_distinct_residues
      exponent right left GREATER LEFT (eq_sym SAME_RESIDUE)).
Qed.

Theorem the_first_modulus_many_triangular_residues_have_no_duplicates :
  forall exponent,
  NoDup (map (triangular_residue exponent)
    (seq 0 (Z.to_nat (group_modulus exponent)))).
Proof.
  intro exponent. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros left right LEFT RIGHT SAME.
  apply in_seq in LEFT. apply in_seq in RIGHT.
  apply (triangular_residue_is_injective_on_the_finite_range exponent left right);
    [lia|lia|exact SAME].
Qed.

Theorem triangular_residues_permute_the_complete_power_of_two_range :
  forall exponent,
  Permutation
    (map (triangular_residue exponent) (seq 0 (Z.to_nat (group_modulus exponent))))
    (seq 0 (Z.to_nat (group_modulus exponent))).
Proof.
  intro exponent. apply Permutation_map_same_l.
  - apply the_first_modulus_many_triangular_residues_have_no_duplicates.
  - intros value MEMBER. apply in_map_iff in MEMBER.
    destruct MEMBER as [step [VALUE _]]. subst value.
    apply in_seq. split; [lia|].
    cbn [Nat.add]. apply triangular_residue_is_in_the_finite_range.
Qed.

(** Mathematical source projection only: actual usize addition needs the
    later reached-prefix and layout guards before this recurrence applies. *)
Definition source_probe_position (buckets initial : Z) (step : nat) :=
  (initial + 16 * triangle step) mod buckets.

Theorem source_probe_position_follows_the_incremented_stride :
  forall buckets initial step, buckets <> 0 ->
  source_probe_position buckets initial (S step) =
    (source_probe_position buckets initial step + 16 * Z.of_nat (S step)) mod buckets.
Proof.
  intros buckets initial step NONZERO. unfold source_probe_position.
  rewrite Z.add_mod_idemp_l by exact NONZERO.
  cbn [triangle]. f_equal. lia.
Qed.

Theorem large_table_starts_keep_the_original_unaligned_residue :
  forall groups initial_group residue step,
  0 < groups -> 0 <= residue < 16 ->
  source_probe_position (16 * groups) (16 * initial_group + residue) step =
    16 * ((initial_group + triangle step) mod groups) + residue.
Proof.
  intros groups initial_group residue step POSITIVE RESIDUE.
  unfold source_probe_position.
  pose proof (Z.div_mod (initial_group + triangle step) groups ltac:(lia)) as DIVISION.
  pose proof (Z.mod_pos_bound (initial_group + triangle step) groups POSITIVE) as RANGE.
  symmetry. apply Z.mod_unique_pos with (q := (initial_group + triangle step) / groups).
  - nia.
  - nia.
Qed.

End NativeHashBagProbeSequence.

Print Assumptions NativeHashBagProbeSequence.twice_triangle_has_its_original_polynomial.
Print Assumptions NativeHashBagProbeSequence.strictly_ordered_triangles_have_distinct_residues.
Print Assumptions NativeHashBagProbeSequence.the_first_modulus_many_triangular_residues_have_no_duplicates.
Print Assumptions NativeHashBagProbeSequence.triangular_residues_permute_the_complete_power_of_two_range.
Print Assumptions NativeHashBagProbeSequence.source_probe_position_follows_the_incremented_stride.
Print Assumptions NativeHashBagProbeSequence.large_table_starts_keep_the_original_unaligned_residue.
