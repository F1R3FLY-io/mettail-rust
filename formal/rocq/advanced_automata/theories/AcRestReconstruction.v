(*
 * AcRestReconstruction: FV (AC-rest) for Stage AC's in-Rho AC matching.
 *
 * When an AC (multiset) pattern `op{L_1..L_k, ...rest}` matches a ground bag, the native
 * spatial matcher picks a size-k sub-multiset (the `fixed` selection) and binds `rest` to
 * the COMPLEMENT (bag with one occurrence of each selected element removed). This theory
 * proves the two load-bearing multiset facts the in-Rho AC receiver relies on, independent
 * of the carrier codegen:
 *
 *   (1) PARTITION — `rest = bag ⊖ selection`, i.e. `selection ⊎ rest ≡ bag` (as multisets):
 *       the selection and the reconstructed `rest` partition the whole bag, nothing gained
 *       or lost. This is what makes the AC receiver's `remainder` binding faithful.
 *   (2) FLATTEN — the RHS `⟦R⟧σ` reproduces the host `add_flattened_bag` (dovetail
 *       `rules.rs`): a `fixed` member that is itself a same-op sub-bag SPLICES its elements
 *       inline (associativity), and flattening distributes over append (order- and
 *       multiplicity-preserving). This is the byte-identity spec the RHS reflection meets.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section AcRestReconstruction.

  (* --- The `rest` complement: bag ⊖ selection (multiset, elements as nat identities) --- *)

  Fixpoint remove_one (x : nat) (l : list nat) : list nat :=
    match l with
    | [] => []
    | h :: t => if Nat.eqb h x then t else h :: remove_one x t
    end.

  (* Removing one occurrence of a present element is a permutation-preserving split. *)
  Lemma remove_one_perm : forall x l, In x l -> Permutation (x :: remove_one x l) l.
  Proof.
    intros x l. induction l as [| h t IH]; simpl; [intros [] |].
    destruct (Nat.eqb h x) eqn:He.
    - apply Nat.eqb_eq in He. subst h. intros _. apply Permutation_refl.
    - apply Nat.eqb_neq in He. intros [Heq | Hin].
      + subst h. exfalso. apply He. reflexivity.
      + apply Permutation_trans with (h :: x :: remove_one x t).
        * apply perm_swap.
        * apply perm_skip. apply IH. exact Hin.
  Qed.

  (* A selection is a sub-multiset of the bag: each element is removed in turn. *)
  Inductive sub_multiset : list nat -> list nat -> Prop :=
    | sm_nil : forall bag, sub_multiset [] bag
    | sm_cons : forall x sel bag,
        In x bag ->
        sub_multiset sel (remove_one x bag) ->
        sub_multiset (x :: sel) bag.

  (* The complement `bag ⊖ selection` — remove one occurrence of each selection element. *)
  Definition complement (bag selection : list nat) : list nat :=
    fold_left (fun acc x => remove_one x acc) selection bag.

  (* (1) PARTITION: the selection and its complement together permute the whole bag. *)
  Theorem selection_rest_partition : forall selection bag,
    sub_multiset selection bag ->
    Permutation (selection ++ complement bag selection) bag.
  Proof.
    intros selection bag Hsub.
    induction Hsub as [bag0 | x sel bag0 Hin Hsub IH].
    - unfold complement. simpl. apply Permutation_refl.
    - unfold complement in *. simpl.
      apply Permutation_trans with (x :: remove_one x bag0).
      + apply perm_skip. exact IH.
      + apply remove_one_perm. exact Hin.
  Qed.

  (* --- The flatten (splice same-op sub-bags), the RHS byte-identity spec --- *)

  Inductive member : Type :=
    | Leaf : nat -> member          (* an ordinary element *)
    | Sub : list nat -> member.     (* a same-op sub-bag, to be spliced *)

  Definition splice (m : member) : list nat :=
    match m with
    | Leaf x => [x]
    | Sub xs => xs
    end.

  Definition flatten (ms : list member) : list nat := flat_map splice ms.

  (* (2a) SPLICE: a `fixed` member that is itself a same-op sub-bag contributes its elements
     inline, NOT nested — the `add_flattened_bag` associativity. *)
  Theorem flatten_splices_subbag : forall xs rest,
    flatten (Sub xs :: rest) = xs ++ flatten rest.
  Proof. intros. reflexivity. Qed.

  (* (2b) DISTRIBUTES over append: flattening `fixed ⊎ rest` is the flatten of each,
     concatenated — order- and multiplicity-preserving (the canonical flat bag). *)
  Theorem flatten_app : forall ms1 ms2,
    flatten (ms1 ++ ms2) = flatten ms1 ++ flatten ms2.
  Proof. intros. unfold flatten. apply flat_map_app. Qed.

  (* Corollary: instantiate_ac = flatten(fixedσ ⊎ [Sub rest]) equals the fixed elements
     followed by the reconstructed rest — the exact shape the RHS reflection emits. *)
  Corollary instantiate_ac_shape : forall fixed rest,
    flatten (fixed ++ [Sub rest]) = flatten fixed ++ rest.
  Proof.
    intros fixed rest. rewrite flatten_app. simpl.
    rewrite app_nil_r. reflexivity.
  Qed.

End AcRestReconstruction.

Print Assumptions selection_rest_partition.
Print Assumptions flatten_splices_subbag.
Print Assumptions flatten_app.
Print Assumptions instantiate_ac_shape.
