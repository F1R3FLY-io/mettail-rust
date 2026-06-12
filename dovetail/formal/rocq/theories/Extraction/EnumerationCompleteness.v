(*
 * EnumerationCompleteness: the Dovetail best-first extractor MISSES NO
 * derivation — the hypergraph-recursion completeness (the structural core of
 * Huang & Chiang 2005, Algorithm 3).
 *
 * The extractor enumerates a class's derivations as: for each hyperedge (e-node)
 * of the class, every COMBINATION of child derivations (one rank per child). A
 * derivation is therefore a (hyperedge index, rank-vector) pair, where the
 * rank-vector ranges over the cartesian product of the children's derivation
 * counts. This file proves that enumeration is EXHAUSTIVE:
 *
 *   - enum_vectors_complete : every in-bounds rank-vector of one hyperedge is
 *     enumerated (no product point missed — the lattice the lazy heap traverses).
 *   - enum_vectors_sound    : the enumeration produces only in-bounds vectors.
 *   - class_enum_complete   : for EVERY hyperedge i and EVERY valid rank-vector
 *     v of that edge, (i, v) is enumerated — i.e. NO derivation of the class is
 *     dropped. (Combined with NBestExtraction.v's selection-layer no-prune +
 *     best-first ordering, the extractor's no-miss is closed.)
 *
 * This models the SET enumerated (= the full per-edge cartesian product, unioned
 * over edges); NBestExtraction.v models the order + the 0̄-only removal. Together
 * they back extract.rs's no-miss (the Rust tests T1-T9 are the operational
 * cross-check).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section EnumerationCompleteness.

  (* A rank-vector `v` is in bounds for per-child derivation-counts `bounds`
     when it has the same length and each coordinate is a valid rank
     (0 <= v[i] < bounds[i]). Structured to mirror `enum_vectors`. *)
  Fixpoint in_bounds (bounds v : list nat) : Prop :=
    match bounds, v with
    | [], [] => True
    | b :: bs, x :: xs => x < b /\ in_bounds bs xs
    | _, _ => False
    end.

  (* All rank-vectors of one hyperedge: the cartesian product of the children's
     rank ranges [0, bounds[i]). The lazy heap (Alg.3) traverses exactly these
     points by single-coordinate increments; here we enumerate the full set. *)
  Fixpoint enum_vectors (bounds : list nat) : list (list nat) :=
    match bounds with
    | [] => [ [] ]
    | b :: bs => flat_map (fun r => map (cons r) (enum_vectors bs)) (seq 0 b)
    end.

  (* No product point is missed: every in-bounds rank-vector is enumerated. *)
  Lemma enum_vectors_complete : forall bounds v,
    in_bounds bounds v -> In v (enum_vectors bounds).
  Proof.
    induction bounds as [| b bs IH]; intros v Hib; simpl.
    - destruct v as [| x xs]; simpl in Hib.
      + left. reflexivity.
      + contradiction.
    - destruct v as [| x xs]; simpl in Hib.
      + contradiction.
      + destruct Hib as [Hx Hxs].
        apply in_flat_map. exists x. split.
        * apply in_seq. lia.
        * apply in_map_iff. exists xs. split.
          -- reflexivity.
          -- apply IH. exact Hxs.
  Qed.

  (* Only in-bounds rank-vectors are enumerated (no fabrication). *)
  Lemma enum_vectors_sound : forall bounds v,
    In v (enum_vectors bounds) -> in_bounds bounds v.
  Proof.
    induction bounds as [| b bs IH]; intros v Hin; simpl in *.
    - destruct Hin as [H | H].
      + subst v. exact I.
      + contradiction.
    - apply in_flat_map in Hin. destruct Hin as [r [Hr Hv]].
      apply in_map_iff in Hv. destruct Hv as [xs [Heq Hxs]].
      subst v. simpl. split.
      + apply in_seq in Hr. lia.
      + apply IH. exact Hxs.
  Qed.

  (* A class is its list of hyperedges; each edge is its children's rank-counts. *)
  Definition Class := list (list nat).

  (* The class's enumerated derivations: every (edge index, rank-vector) pair. *)
  Definition class_enum (c : Class) : list (nat * list nat) :=
    flat_map
      (fun p => map (fun v => (fst p, v)) (enum_vectors (snd p)))
      (combine (seq 0 (length c)) c).

  (* Indexing helper: nth_error in a list ⟹ the (index, element) pair is in the
     index-zipped list. *)
  Lemma in_combine_seq :
    forall (A : Type) (l : list A) (start i : nat) (x : A),
      nth_error l i = Some x ->
      In (start + i, x) (combine (seq start (length l)) l).
  Proof.
    induction l as [| h t IH]; intros start i x Hnth; simpl.
    - destruct i; simpl in Hnth; discriminate.
    - destruct i as [| i']; simpl in Hnth.
      + inversion Hnth. left. f_equal. lia.
      + right.
        replace (start + S i') with (S start + i') by lia.
        apply IH. exact Hnth.
  Qed.

  (* THE completeness theorem: for every hyperedge `i` of the class and every
     valid rank-vector `v` of that edge, the derivation (i, v) is ENUMERATED.
     No derivation of a class is ever dropped. *)
  Theorem class_enum_complete : forall c i bounds v,
    nth_error c i = Some bounds -> in_bounds bounds v ->
    In (i, v) (class_enum c).
  Proof.
    intros c i bounds v Hnth Hib.
    unfold class_enum. apply in_flat_map.
    exists (i, bounds). split.
    - replace i with (0 + i) by lia.
      apply in_combine_seq. exact Hnth.
    - simpl. apply in_map_iff. exists v. split.
      + reflexivity.
      + apply enum_vectors_complete. exact Hib.
  Qed.

  (* Soundness companion: every enumerated derivation comes from a real edge with
     an in-bounds rank-vector. *)
  Theorem class_enum_sound : forall c i v,
    In (i, v) (class_enum c) ->
    exists bounds, In (i, bounds) (combine (seq 0 (length c)) c) /\ in_bounds bounds v.
  Proof.
    intros c i v Hin. unfold class_enum in Hin.
    apply in_flat_map in Hin. destruct Hin as [p [Hp Hv]].
    destruct p as [pi pb]. simpl in Hv.
    apply in_map_iff in Hv. destruct Hv as [w [Heq Hw]].
    inversion Heq. subst.
    exists pb. split.
    - exact Hp.
    - apply enum_vectors_sound. exact Hw.
  Qed.

End EnumerationCompleteness.
