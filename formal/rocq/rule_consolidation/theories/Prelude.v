(*
 * Prelude: Multiset equivalence, list/option utilities for rule consolidation proofs.
 *
 * Provides:
 *   - Multiset equivalence via Permutation
 *   - flat_map and concat_map lemmas
 *   - Decidable equality utilities
 *   - Option/list interaction lemmas
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust/Ascent Code                              | Location
 *   -------------------------|-----------------------------------------------|------------
 *   Permutation (multiset)   | Datalog relation (set semantics, order-free)  | Ascent runtime
 *   flat_map                 | .into_iter().flat_map(...)                     | helpers.rs:45
 *   concat_map               | match t { ... }.into_iter()                   | helpers.rs:33
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import SetoidList.
From Stdlib Require Import FunctionalExtensionality.

Import ListNotations.

(* =====================================================================
 * Multiset equivalence
 * =====================================================================
 *
 * We model Datalog fact sets as lists up to permutation. This is
 * appropriate because:
 *   - Datalog relations are unordered sets
 *   - The order in which match arms appear does not affect the
 *     set of derived facts
 *   - Permutation is an equivalence relation (reflexive, symmetric,
 *     transitive) with congruence under list operations
 * ===================================================================== *)

Notation "l1 '≡ₘ' l2" := (Permutation l1 l2) (at level 70).

(* =====================================================================
 * Basic list lemmas
 * ===================================================================== *)

Lemma flat_map_nil : forall {A B : Type} (f : A -> list B),
  flat_map f [] = [].
Proof. reflexivity. Qed.

Lemma flat_map_cons : forall {A B : Type} (f : A -> list B) (x : A) (xs : list A),
  flat_map f (x :: xs) = f x ++ flat_map f xs.
Proof. reflexivity. Qed.

Lemma flat_map_app : forall {A B : Type} (f : A -> list B) (l1 l2 : list A),
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  induction l1 as [|x xs IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma flat_map_singleton : forall {A B : Type} (f : A -> list B) (x : A),
  flat_map f [x] = f x.
Proof. intros. simpl. rewrite app_nil_r. reflexivity. Qed.

(** flat_map over a list where all elements produce [] yields []. *)
Lemma flat_map_all_nil : forall {A B : Type} (f : A -> list B) (ks : list A),
  (forall k, In k ks -> f k = []) ->
  flat_map f ks = [].
Proof.
  induction ks as [|x xs IH]; intros Hall.
  - reflexivity.
  - simpl. rewrite Hall by (left; reflexivity).
    simpl. apply IH. intros k Hk. apply Hall. right. exact Hk.
Qed.

(** flat_map where exactly one element produces a non-nil result. *)
Lemma flat_map_single_hit :
  forall {A B : Type} (f : A -> list B) (ks : list A) (k0 : A),
    NoDup ks ->
    In k0 ks ->
    (forall k, In k ks -> k <> k0 -> f k = []) ->
    flat_map f ks ≡ₘ f k0.
Proof.
  intros A B f ks k0 Hnd Hin Hothers.
  induction ks as [|x xs IH].
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst x.
      assert (Hrest : flat_map f xs = []).
      { apply flat_map_all_nil.
        intros k Hk.
        inversion Hnd; subst.
        apply Hothers.
        - right. exact Hk.
        - intro Heq. subst k. contradiction.
      }
      rewrite Hrest. rewrite app_nil_r. apply Permutation_refl.
    + inversion Hnd; subst.
      assert (Hxne : x <> k0) by (intro Heq; subst x; contradiction).
      rewrite (Hothers x (or_introl eq_refl) Hxne).
      simpl. apply IH.
      * exact H2.
      * exact Hin.
      * intros k Hk Hne. apply Hothers. right. exact Hk. exact Hne.
Qed.

(* =====================================================================
 * Decidable equality utilities
 * ===================================================================== *)

(** Boolean decidable equality for option types. *)
Definition option_eqb {A : Type} (eqb_A : A -> A -> bool) (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => eqb_A a b
  | _, _ => false
  end.

Lemma option_eqb_spec : forall {A : Type} (eqb_A : A -> A -> bool),
  (forall a b, eqb_A a b = true <-> a = b) ->
  forall x y, option_eqb eqb_A x y = true <-> x = y.
Proof.
  intros A eqb_A Hspec x y.
  destruct x as [a|]; destruct y as [b|]; simpl; split; intros H;
    try discriminate; try reflexivity.
  - apply Hspec in H. subst. reflexivity.
  - inversion H; subst. apply Hspec. reflexivity.
Qed.

(* =====================================================================
 * Conditional list generation
 * =====================================================================
 *
 * Models the pattern:
 *   if classify(t) = Some k then extract(k, t) else []
 * ===================================================================== *)

Definition cond_extract {K V : Type}
  (eqb_K : K -> K -> bool)
  (classify_result : option K)
  (k : K)
  (extract : K -> list V)
  : list V :=
  match classify_result with
  | Some k' => if eqb_K k' k then extract k else []
  | None => []
  end.

Lemma cond_extract_hit :
  forall {K V : Type} (eqb_K : K -> K -> bool) (k : K) (extract : K -> list V),
    (forall a b, eqb_K a b = true <-> a = b) ->
    cond_extract eqb_K (Some k) k extract = extract k.
Proof.
  intros K V eqb_K k extract Hspec.
  unfold cond_extract.
  assert (Hrefl : eqb_K k k = true) by (apply Hspec; reflexivity).
  rewrite Hrefl. reflexivity.
Qed.

Lemma cond_extract_miss_diff :
  forall {K V : Type} (eqb_K : K -> K -> bool) (k k' : K) (extract : K -> list V),
    (forall a b, eqb_K a b = true <-> a = b) ->
    k' <> k ->
    cond_extract eqb_K (Some k') k extract = [].
Proof.
  intros K V eqb_K k k' extract Hspec Hne.
  unfold cond_extract.
  destruct (eqb_K k' k) eqn:E.
  - apply Hspec in E. contradiction.
  - reflexivity.
Qed.

Lemma cond_extract_miss_none :
  forall {K V : Type} (eqb_K : K -> K -> bool) (k : K) (extract : K -> list V),
    cond_extract eqb_K None k extract = [].
Proof. reflexivity. Qed.


