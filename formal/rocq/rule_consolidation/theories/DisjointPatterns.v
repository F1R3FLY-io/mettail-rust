(*
 * DisjointPatterns: Pattern matching model for constructor-disjoint enum types.
 *
 * Models the core abstraction behind rule consolidation: a type T with
 * disjoint constructors classified by kinds K. Each constructor maps to
 * exactly one kind, and at most one constructor matches any given term.
 *
 * Provides:
 *   D1: classify uniqueness (at most one kind matches)
 *   D2: match_extract = extract k t when classify t = Some k
 *   D3: match_extract = [] when classify t = None
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition   | Rust/Ascent Code                        | Location
 *   ------------------|-----------------------------------------|-----------
 *   classify          | match t { Cat::Ctor(..) => Some(k), ..} | helpers.rs:68
 *   extract           | arm body: vec![f0.clone(), ...]          | helpers.rs:83
 *   match_extract     | (match t { ... }).into_iter()            | helpers.rs:45
 *   all_kinds         | all constructors for a category          | helpers.rs:70
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

From RuleConsolidation Require Import Prelude.

Import ListNotations.

(* =====================================================================
 * Abstract interface for disjoint constructor types
 * =====================================================================
 *
 * We parameterize over:
 *   T — the term type (e.g., Int, Proc)
 *   K — the kind type (constructor tag, e.g., Add, Sub, Neg)
 *   V — the value type extracted from terms (subterms of a target category)
 *
 * The interface consists of:
 *   classify : T → option K    — assigns a constructor kind to each term
 *   extract  : K → T → list V  — extracts values when kind matches
 *   all_kinds : list K          — enumerates all possible kinds
 *   eqb_K   : K → K → bool     — decidable equality on kinds
 *
 * Preconditions:
 *   P1: classify is functional (built into the type — it's a function)
 *   P2: all_kinds enumerates every K that classify can return
 *   P3: eqb_K reflects propositional equality
 *   P4: all_kinds has no duplicates (NoDup)
 * ===================================================================== *)

Section DisjointPatterns.

  Variable T : Type.        (* Term type *)
  Variable K : Type.        (* Constructor kind type *)
  Variable V : Type.        (* Extracted value type *)

  Variable classify : T -> option K.
  Variable extract  : K -> T -> list V.
  Variable all_kinds : list K.
  Variable eqb_K : K -> K -> bool.

  (* Preconditions *)
  Hypothesis eqb_K_spec : forall a b : K, eqb_K a b = true <-> a = b.
  Hypothesis all_kinds_complete : forall k : K, forall t : T,
    classify t = Some k -> In k all_kinds.
  Hypothesis all_kinds_nodup : NoDup all_kinds.

  (* ===================================================================
   * match_extract: the consolidated match expression
   *
   * This models the Rust code:
   *   match t {
   *     Cat::Ctor1(f0, f1) => vec![f0.clone(), f1.clone()],
   *     Cat::Ctor2(f0) => vec![f0.clone()],
   *     ...
   *     _ => vec![],
   *   }
   * =================================================================== *)

  Definition match_extract (t : T) : list V :=
    match classify t with
    | Some k => extract k t
    | None   => []
    end.

  (* ===================================================================
   * D2: match_extract = extract k t when classify t = Some k
   * =================================================================== *)

  Lemma match_extract_some :
    forall (t : T) (k : K),
      classify t = Some k ->
      match_extract t = extract k t.
  Proof.
    intros t k Hcl. unfold match_extract. rewrite Hcl. reflexivity.
  Qed.

  (* ===================================================================
   * D3: match_extract = [] when classify t = None
   * =================================================================== *)

  Lemma match_extract_none :
    forall (t : T),
      classify t = None ->
      match_extract t = [].
  Proof.
    intros t Hcl. unfold match_extract. rewrite Hcl. reflexivity.
  Qed.

  (* ===================================================================
   * D1: classify uniqueness (disjointness)
   *
   * Since classify : T → option K is a function, for any term t
   * there is at most one k such that classify t = Some k.
   * This is trivially true by the determinism of functions, but
   * we state it explicitly for documentation.
   * =================================================================== *)

  Lemma classify_unique :
    forall (t : T) (k1 k2 : K),
      classify t = Some k1 ->
      classify t = Some k2 ->
      k1 = k2.
  Proof.
    intros t k1 k2 H1 H2. rewrite H1 in H2. inversion H2. reflexivity.
  Qed.

  (* ===================================================================
   * Helper: for a given term, only the matching kind contributes
   * to the flat_map over all_kinds.
   * =================================================================== *)

  (** The per-kind conditional extraction function.
      Models: "if let Cat::Ctor(..) = t then extract(..) else []" *)
  Definition per_kind_extract (k : K) (t : T) : list V :=
    cond_extract eqb_K (classify t) k (fun k' => extract k' t).

  Lemma per_kind_extract_hit :
    forall (t : T) (k : K),
      classify t = Some k ->
      per_kind_extract k t = extract k t.
  Proof.
    intros t k Hcl. unfold per_kind_extract, cond_extract.
    rewrite Hcl.
    assert (Hrefl : eqb_K k k = true) by (apply eqb_K_spec; reflexivity).
    rewrite Hrefl. reflexivity.
  Qed.

  Lemma per_kind_extract_miss :
    forall (t : T) (k k' : K),
      classify t = Some k' ->
      k <> k' ->
      per_kind_extract k t = [].
  Proof.
    intros t k k' Hcl Hne. unfold per_kind_extract, cond_extract.
    rewrite Hcl.
    destruct (eqb_K k' k) eqn:E.
    - apply eqb_K_spec in E. symmetry in E. contradiction.
    - reflexivity.
  Qed.

  Lemma per_kind_extract_none :
    forall (t : T) (k : K),
      classify t = None ->
      per_kind_extract k t = [].
  Proof.
    intros t k Hcl. unfold per_kind_extract, cond_extract.
    rewrite Hcl. reflexivity.
  Qed.

  (* ===================================================================
   * The "N separate rules" computation: flat_map over all kinds.
   *
   * Models the original N rules:
   *   Rule_1: tgt(sub) <-- src(t), if let Src::Ctor1(..) = t, ...
   *   Rule_2: tgt(sub) <-- src(t), if let Src::Ctor2(..) = t, ...
   *   ...
   *   Rule_N: tgt(sub) <-- src(t), if let Src::CtorN(..) = t, ...
   *
   * The union of all facts derived = flat_map per_kind_extract all_kinds.
   * =================================================================== *)

  Definition original_rules (t : T) : list V :=
    flat_map (fun k => per_kind_extract k t) all_kinds.

End DisjointPatterns.

