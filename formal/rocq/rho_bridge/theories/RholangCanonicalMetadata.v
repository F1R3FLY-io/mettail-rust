(** Canonical metadata maintained by construction, not inferred by reparsing.

    A Boolean represents one 0/1 node byte. Canonical lists are empty or end in
    true. This is a representation invariant of graph-produced values, not a
    restriction on the direct adapter's external Par inputs. In particular the
    existing source helper must still trim arbitrary trailing clear bytes.

    For canonical body metadata, shifting away a binder prefix has an exact
    size computable from the cached length. This permits a preconstruction
    allowance without inspecting a completed subtree or allocating a planner
    copy. Surviving indices are bounded by that size; these lemmas alone do
    not account for helper byte passes, allocation, clone or cleanup workspace. *)
From Stdlib Require Import List Arith Lia Bool.
From RhoBridge Require Import RholangTargetConstruction RholangConstructionFacts.
Import ListNotations.

Fixpoint canonical_bits (bits : list bool) : bool :=
  match bits with
  | [] => true
  | bit :: rest => match rest with [] => bit | _ => canonical_bits rest end
  end.

Lemma canonical_tail : forall bit rest,
  canonical_bits (bit :: rest) = true -> canonical_bits rest = true.
Proof. intros bit [|next rest] H; [reflexivity|exact H]. Qed.

Theorem trimming_produces_canonical_metadata : forall bits,
  canonical_bits (trim_bits bits) = true.
Proof.
  induction bits as [|bit rest IH]; [reflexivity|].
  cbn [trim_bits]. destruct (trim_bits rest) as [|next suffix] eqn:HT;
    destruct bit; cbn in *; auto.
Qed.

Theorem canonical_metadata_is_unchanged_by_trimming : forall bits,
  canonical_bits bits = true -> trim_bits bits = bits.
Proof.
  induction bits as [|bit rest IH]; intro HC; [reflexivity|].
  destruct rest as [|next suffix].
  - destruct bit; cbn in *; congruence.
  - pose proof (canonical_tail bit (next :: suffix) HC) as HT.
    change ((match bit, trim_bits (next :: suffix) with
      | false, [] => [] | _, tail => bit :: tail end) = bit :: next :: suffix).
    rewrite (IH HT). destruct bit; reflexivity.
Qed.

Theorem dropping_a_prefix_preserves_canonical_metadata : forall width bits,
  canonical_bits bits = true -> canonical_bits (skipn width bits) = true.
Proof.
  induction width as [|width IH]; intros [|bit rest] HC; cbn; auto.
  apply IH. now apply (canonical_tail bit).
Qed.

Lemma empty_union_has_empty_operands : forall left right,
  union_bits left right = [] -> left = [] /\ right = [].
Proof. intros [|a left] [|b right] H; cbn in H; try discriminate; auto. Qed.

Theorem union_preserves_canonical_metadata : forall left right,
  canonical_bits left = true -> canonical_bits right = true ->
  canonical_bits (union_bits left right) = true.
Proof.
  induction left as [|a left IH]; intros [|b right] HL HR; cbn [union_bits]; auto.
  pose proof (canonical_tail a left HL) as HTL.
  pose proof (canonical_tail b right HR) as HTR.
  specialize (IH right HTL HTR).
  destruct (union_bits left right) as [|next suffix] eqn:HU.
  - apply empty_union_has_empty_operands in HU as [EL ER]. subst left right.
    cbn in HL, HR. rewrite HL, HR. reflexivity.
  - exact IH.
Qed.

Lemma true_ending_is_canonical : forall prefix,
  canonical_bits (prefix ++ [true]) = true.
Proof. induction prefix as [|bit rest IH]; [reflexivity|]. destruct rest; cbn in *; auto. Qed.

Theorem bound_metadata_is_canonical : forall index,
  canonical_bits (free_bits (bound_summary index)) = true.
Proof. intro index. apply true_ending_is_canonical. Qed.

Theorem shifted_metadata_is_canonical : forall width bits,
  canonical_bits (shift_bits width bits) = true.
Proof. intros. apply trimming_produces_canonical_metadata. Qed.

Theorem canonical_shift_has_exact_saturating_length : forall width bits,
  canonical_bits bits = true ->
  List.length (shift_bits width bits) = List.length bits - width.
Proof.
  intros width bits HC. unfold shift_bits.
  rewrite canonical_metadata_is_unchanged_by_trimming.
  - apply length_skipn.
  - now apply dropping_a_prefix_preserves_canonical_metadata.
Qed.

Fixpoint set_bit_count (bits : list bool) : nat :=
  match bits with [] => 0 | bit :: rest => (if bit then 1 else 0) + set_bit_count rest end.
Theorem set_bit_count_is_bounded_by_metadata_length : forall bits,
  set_bit_count bits <= List.length bits.
Proof. induction bits as [|bit rest IH]; cbn; [lia|]. destruct bit; cbn; lia. Qed.

Theorem surviving_index_count_fits_shifted_allowance : forall width bits,
  set_bit_count (skipn width bits) <= List.length bits - width.
Proof.
  intros. rewrite <- length_skipn. apply set_bit_count_is_bounded_by_metadata_length.
Qed.

Definition canonical_fact (fact : ConstructionFact) : bool :=
  canonical_bits (free_bits (structural_summary fact)).
Theorem append_fact_preserves_canonical_metadata : forall left right,
  canonical_fact left = true -> canonical_fact right = true ->
  canonical_fact (append_fact left right) = true.
Proof. intros. now apply union_preserves_canonical_metadata. Qed.
Theorem fresh_fact_produces_canonical_metadata : forall width body,
  canonical_fact (fresh_fact width body) = true.
Proof. intros. apply shifted_metadata_is_canonical. Qed.

Example trailing_clear_external_metadata_does_not_satisfy_the_length_premise :
  canonical_bits [true; false] = false /\
  List.length (shift_bits 0 [true; false]) = 1 /\
  List.length [true; false] - 0 = 2.
Proof. repeat split; reflexivity. Qed.

Print Assumptions trimming_produces_canonical_metadata.
Print Assumptions canonical_metadata_is_unchanged_by_trimming.
Print Assumptions dropping_a_prefix_preserves_canonical_metadata.
Print Assumptions union_preserves_canonical_metadata.
Print Assumptions bound_metadata_is_canonical.
Print Assumptions shifted_metadata_is_canonical.
Print Assumptions canonical_shift_has_exact_saturating_length.
Print Assumptions set_bit_count_is_bounded_by_metadata_length.
Print Assumptions surviving_index_count_fits_shifted_allowance.
Print Assumptions append_fact_preserves_canonical_metadata.
Print Assumptions fresh_fact_produces_canonical_metadata.
Print Assumptions trailing_clear_external_metadata_does_not_satisfy_the_length_premise.
