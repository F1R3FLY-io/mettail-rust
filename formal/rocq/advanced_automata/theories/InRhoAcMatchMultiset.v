(*
 * InRhoAcMatchMultiset: FV (AC-i) for Stage AC's in-Rho AC matching.
 *
 * The in-Rho AC match (the native `sub_pars` / `MaximumBipartiteMatch` over the reflected bag
 * carrier) is SOUND and COMPLETE with respect to the AC matching RELATION over multisets. The
 * relation is: a selection `S` matches a bag `B` (binding the remainder `rest`) iff `S` is a
 * sub-multiset of `B` and `S ⊎ rest ≡ B`. This theory proves the central correspondence:
 *
 *     sub_multiset S B   <->   exists rest, Permutation (S ++ rest) B
 *
 * i.e. the incremental pick-and-remove the native matcher performs (each pattern slot picks a
 * PRESENT element and recurses on the bag with that occurrence removed — exactly `sub_multiset`)
 * captures EXACTLY the order-independent partitions of the bag. The forward direction is
 * SOUNDNESS (the native selection admits a faithful `rest` = complement, `AcRestReconstruction`);
 * the backward direction is COMPLETENESS (every order-independent partition of the bag into a
 * matched selection + a rest is a reachable native match) — so no valid AC match is missed and
 * none is fabricated. Order-independence is inherent: the witness is a `Permutation`, invariant
 * under the bag's shuffle.
 *
 * Reuses AcRestReconstruction (`sub_multiset`, `complement`, `remove_one_perm`,
 * `selection_rest_partition`) + Stdlib `Permutation`. Zero-admission. Rocq 9.1 compatible.
 *)

From AdvancedAutomata Require Import AcRestReconstruction.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section InRhoAcMatchMultiset.

  (* COMPLETENESS core: an order-independent partition witness makes the selection a sub-multiset.
     Induction on the selection, peeling the head pick off both the partition and the bag. *)
  Lemma partition_sub_multiset : forall selection bag rest,
    Permutation (selection ++ rest) bag -> sub_multiset selection bag.
  Proof.
    induction selection as [| x sel' IH]; intros bag rest Hperm.
    - apply sm_nil.
    - simpl in Hperm.
      assert (Hin : In x bag).
      { apply (Permutation_in x Hperm). left. reflexivity. }
      apply sm_cons; [ exact Hin |].
      apply (IH (remove_one x bag) rest).
      assert (Hcons : Permutation (x :: (sel' ++ rest)) (x :: remove_one x bag)).
      { apply Permutation_trans with bag.
        - exact Hperm.
        - apply Permutation_sym. apply remove_one_perm. exact Hin. }
      exact (Permutation_cons_inv Hcons).
  Qed.

  (* (AC-i) THE MATCH CORRESPONDENCE: the native sub-multiset match holds iff the selection has
     an order-independent complement partitioning the bag — the in-Rho AC match set equals the
     AC matching relation over multisets. *)
  Theorem ac_match_iff_partition : forall selection bag,
    sub_multiset selection bag <-> exists rest, Permutation (selection ++ rest) bag.
  Proof.
    intros selection bag. split.
    - intro Hsub. exists (complement bag selection).
      apply selection_rest_partition. exact Hsub.
    - intros [rest Hperm]. exact (partition_sub_multiset selection bag rest Hperm).
  Qed.

  (* SOUNDNESS: the native selection admits a faithful `rest` = complement that exactly partitions
     the bag (nothing gained or lost) — the in-Rho AC match never fabricates a binding. *)
  Corollary ac_match_sound : forall selection bag,
    sub_multiset selection bag ->
    Permutation (selection ++ complement bag selection) bag.
  Proof. exact selection_rest_partition. Qed.

  (* COMPLETENESS: any order-independent partition of the bag into a matched selection + a rest
     is a reachable native AC match (a sub-multiset) — no valid match is missed. *)
  Corollary ac_match_complete : forall selection rest bag,
    Permutation (selection ++ rest) bag -> sub_multiset selection bag.
  Proof.
    intros selection rest bag H. exact (partition_sub_multiset selection bag rest H).
  Qed.

  (* The rest is DETERMINED up to multiset equality: any two rests witnessing the same selection
     match permute the same complement, so both permute each other — the `rest` binding is
     well-defined regardless of which shuffle the native matcher committed. Proved through the
     canonical complement (selection_rest_partition) to avoid a left-cancellation lemma. *)
  Corollary ac_rest_unique_up_to_perm : forall selection bag rest1 rest2,
    sub_multiset selection bag ->
    Permutation (selection ++ rest1) bag ->
    Permutation (selection ++ rest2) bag ->
    Permutation rest1 rest2.
  Proof.
    intros selection bag rest1 rest2 Hsub H1 H2.
    (* Both rests, appended after selection, permute bag; the canonical complement does too. *)
    assert (Hc : Permutation (selection ++ complement bag selection) bag)
      by (apply selection_rest_partition; exact Hsub).
    (* rest1 ~ complement and rest2 ~ complement via the shared prefix, using only append/trans. *)
    assert (E1 : Permutation (selection ++ rest1) (selection ++ complement bag selection))
      by (apply Permutation_trans with bag; [ exact H1 | apply Permutation_sym; exact Hc ]).
    assert (E2 : Permutation (selection ++ rest2) (selection ++ complement bag selection))
      by (apply Permutation_trans with bag; [ exact H2 | apply Permutation_sym; exact Hc ]).
    apply Permutation_app_inv_l in E1.
    apply Permutation_app_inv_l in E2.
    apply Permutation_trans with (complement bag selection); [ exact E1 | apply Permutation_sym; exact E2 ].
  Qed.

End InRhoAcMatchMultiset.

Print Assumptions ac_match_iff_partition.
Print Assumptions ac_match_sound.
Print Assumptions ac_match_complete.
Print Assumptions ac_rest_unique_up_to_perm.
