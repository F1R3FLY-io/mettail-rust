(*
 * VariantIndexRebuild: Variant-index extraction and rebuild correctness
 * for explicit rewrite congruence (Area 4).
 *
 * In the consolidated congruence rule, each (constructor, field_position)
 * pair is assigned a unique variant index (vi). The extraction match
 * produces (field_value, vi) pairs, and the rebuild match uses vi to
 * reconstruct the correct constructor with the rewritten field.
 *
 * Provides:
 *   V1: variant index injectivity (hypothesis)
 *   V2: extraction-rebuild round-trip (hypothesis)
 *   V3: rebuild correctness (hypothesis)
 *   V4: VARIANT-INDEX CONGRUENCE EQUIVALENCE (Area 4)
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition           | Rust/Ascent Code                     | Location
 *   -------------------------|------------------------------------- |------------
 *   vi_assign                 | Sequential vi in enumerate()         | congruence.rs:414
 *   vi_extract                | for (field_val, vi) in (match lhs ..)| congruence.rs:434
 *   vi_rebuild                | match (lhs, vi) { ... }              | congruence.rs:474
 *   field_positions           | entry.field_idx per constructor      | congruence.rs:418
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.

From RuleConsolidation Require Import Prelude.

Import ListNotations.

(* =====================================================================
 * Variant Index Model
 * =====================================================================
 *
 * A variant index (vi) uniquely identifies a (constructor, field_position)
 * pair. In the Rust codegen, these are assigned sequentially:
 *
 *   Int::Add(x0, x1) => vec![(x0.clone(), 0usize), (x1.clone(), 1usize)],
 *   Int::Neg(x0)     => vec![(x0.clone(), 2usize)],
 *   Int::Sub(x0, x1) => vec![(x0.clone(), 3usize), (x1.clone(), 4usize)],
 *
 * The vi is then used in the rebuild match:
 *   (Int::Add(_, x1), 0usize) => Int::Add(Box::new(t.clone()), x1.clone()),
 *   (Int::Add(x0, _), 1usize) => Int::Add(x0.clone(), Box::new(t.clone())),
 *   ...
 * ===================================================================== *)

Section VariantIndex.

  Variable T : Type.       (* Term type *)
  Variable K : Type.       (* Constructor kind *)
  Variable V : Type.       (* Field value type *)

  Variable classify : T -> option K.
  Variable eqb_K : K -> K -> bool.
  Variable all_kinds : list K.

  Hypothesis eqb_K_spec : forall a b : K, eqb_K a b = true <-> a = b.
  Hypothesis all_kinds_complete : forall k : K, forall t : T,
    classify t = Some k -> In k all_kinds.
  Hypothesis all_kinds_nodup : NoDup all_kinds.

  (* ===================================================================
   * Extraction and rebuild functions (abstract interface)
   * =================================================================== *)

  (** Extract fields with their variant indices from a term.
      Models: match lhs { Cat::A(x0,x1) => vec![(x0,0),(x1,1)], ... } *)
  Variable vi_extract : T -> list (V * nat).

  (** Rebuild a term with a replacement value at the given variant index.
      Models: match (lhs, vi) { (Cat::A(_,x1), 0) => Cat::A(new, x1), ... } *)
  Variable vi_rebuild : T -> nat -> V -> T.

  (** Extract field values for a given kind (without variant indices). *)
  Variable extract_fields : K -> T -> list V.

  (** Variant index assignment: maps (kind, position_in_field_list) to vi. *)
  Variable vi_of : K -> nat -> nat.

  (** Number of fields for each kind. *)
  Variable num_fields : K -> nat.

  (* ===================================================================
   * Preconditions (V1, V2, V3 from the plan)
   * =================================================================== *)

  (** V1: Injectivity of vi_of.
      Different (kind, position) pairs get different variant indices. *)
  Hypothesis vi_of_injective :
    forall k1 k2 i1 i2,
      In k1 all_kinds -> In k2 all_kinds ->
      i1 < num_fields k1 -> i2 < num_fields k2 ->
      vi_of k1 i1 = vi_of k2 i2 ->
      k1 = k2 /\ i1 = i2.

  (** V2: Extraction-rebuild round-trip.
      Rebuilding with the original value at its vi recovers the original term. *)
  Hypothesis rebuild_identity :
    forall (t : T) (k : K) (i : nat) (v : V),
      classify t = Some k ->
      i < num_fields k ->
      nth_error (extract_fields k t) i = Some v ->
      vi_rebuild t (vi_of k i) v = t.

  (** V3: Rebuild correctness.
      Rebuilding preserves the constructor and replaces the target field. *)
  Hypothesis rebuild_replaces :
    forall (t : T) (k : K) (i : nat) (v_new : V),
      classify t = Some k ->
      i < num_fields k ->
      classify (vi_rebuild t (vi_of k i) v_new) = Some k
      /\ nth_error (extract_fields k (vi_rebuild t (vi_of k i) v_new)) i = Some v_new.

  (* ===================================================================
   * vi_extract specification
   * =================================================================== *)

  Hypothesis vi_extract_spec :
    forall (t : T) (k : K),
      classify t = Some k ->
      vi_extract t = combine (extract_fields k t)
                             (map (vi_of k) (seq 0 (num_fields k))).

  Hypothesis vi_extract_none :
    forall (t : T),
      classify t = None ->
      vi_extract t = [].

  Hypothesis extract_fields_length :
    forall (k : K) (t : T),
      classify t = Some k ->
      length (extract_fields k t) = num_fields k.

  (* ===================================================================
   * V4: VARIANT-INDEX CONGRUENCE EQUIVALENCE (Area 4)
   *
   * The original N rules (one per constructor×field) derive the same
   * set of (field_value, variant_index) pairs as the single consolidated
   * rule using vi_extract.
   * =================================================================== *)

  (** Original per-kind extraction with variant indices. *)
  Definition original_vi_extract (t : T) : list (V * nat) :=
    flat_map (fun k =>
      match classify t with
      | Some k' =>
          if eqb_K k' k then
            combine (extract_fields k t)
                    (map (vi_of k) (seq 0 (num_fields k)))
          else []
      | None => []
      end)
      all_kinds.

  (** Helper: per-kind arm produces [] when kind doesn't match. *)
  Lemma vi_arm_miss : forall t k k',
    classify t = Some k' -> k <> k' ->
    (match classify t with
     | Some k'' => if eqb_K k'' k then
                     combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k)))
                   else []
     | None => []
     end) = [].
  Proof.
    intros t k k' Hcl Hne. rewrite Hcl.
    destruct (eqb_K k' k) eqn:E.
    - apply eqb_K_spec in E. subst. contradiction.
    - reflexivity.
  Qed.

  Lemma vi_arm_none : forall t k,
    classify t = None ->
    (match classify t with
     | Some k'' => if eqb_K k'' k then
                     combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k)))
                   else []
     | None => []
     end) = [].
  Proof.
    intros t k Hcl. rewrite Hcl. reflexivity.
  Qed.

  (** Helper: define the per-kind function that the flat_map uses. *)
  Definition vi_per_kind (t : T) (k : K) : list (V * nat) :=
    match classify t with
    | Some k' =>
        if eqb_K k' k then
          combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k)))
        else []
    | None => []
    end.

  Lemma vi_per_kind_hit : forall t k,
    classify t = Some k ->
    vi_per_kind t k = combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k))).
  Proof.
    intros t k Hcl. unfold vi_per_kind. rewrite Hcl.
    assert (H : eqb_K k k = true) by (apply eqb_K_spec; reflexivity).
    rewrite H. reflexivity.
  Qed.

  Lemma vi_per_kind_miss : forall t k k',
    classify t = Some k' -> k <> k' -> vi_per_kind t k = [].
  Proof.
    intros t k k' Hcl Hne. unfold vi_per_kind. rewrite Hcl.
    destruct (eqb_K k' k) eqn:E.
    - apply eqb_K_spec in E. subst. contradiction.
    - reflexivity.
  Qed.

  Lemma vi_per_kind_none : forall t k,
    classify t = None -> vi_per_kind t k = [].
  Proof.
    intros t k Hcl. unfold vi_per_kind. rewrite Hcl. reflexivity.
  Qed.

  (** Restate original_vi_extract in terms of vi_per_kind. *)
  Lemma original_vi_extract_eq : forall t,
    original_vi_extract t = flat_map (vi_per_kind t) all_kinds.
  Proof. reflexivity. Qed.

  Theorem variant_index_extract_equiv :
    forall (t : T),
      original_vi_extract t ≡ₘ vi_extract t.
  Proof.
    intros t.
    rewrite original_vi_extract_eq.
    destruct (classify t) as [k|] eqn:Hcl.
    - (* classify t = Some k *)
      rewrite (vi_extract_spec t k Hcl).
      rewrite <- (vi_per_kind_hit t k Hcl).
      apply flat_map_single_hit with (k0 := k).
      + exact all_kinds_nodup.
      + exact (all_kinds_complete k t Hcl).
      + intros k' Hin Hne. apply vi_per_kind_miss with (k' := k); assumption.
    - (* classify t = None *)
      rewrite (vi_extract_none t Hcl).
      rewrite flat_map_all_nil.
      + apply Permutation_refl.
      + intros k Hk. apply vi_per_kind_none. exact Hcl.
  Qed.

  (** Corollary: The rebuild side is also equivalent, since it only
      depends on the (field_val, vi) pairs and the original term t. *)
  Corollary variant_index_congruence_equiv :
    forall (t : T) (rw : V -> V),
      map (fun '(v, vi) => (t, vi_rebuild t vi (rw v)))
          (original_vi_extract t)
      ≡ₘ
      map (fun '(v, vi) => (t, vi_rebuild t vi (rw v)))
          (vi_extract t).
  Proof.
    intros t rw.
    apply Permutation_map.
    apply variant_index_extract_equiv.
  Qed.

End VariantIndex.
