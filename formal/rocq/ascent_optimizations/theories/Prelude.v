(*
 * Prelude: Shared infrastructure for Ascent runtime optimization proofs.
 *
 * Provides:
 *   - Hash function model with injectivity hypothesis (for u32-sized types)
 *   - hash_le ordering derived from hash values
 *   - List utilities (flat_map lemmas, Permutation re-exports)
 *   - Decidable equality helpers
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Ascent Code                | Location
 *   -------------------------|-----------------------------------|--------------------------
 *   hash                     | DefaultHasher::new() + .finish()  | binding.rs:279-283
 *   hash_injective           | u32 UniqueId (no practical colls) | binding.rs:276 (comment)
 *   hash_le                  | .cmp() on hash values             | binding.rs:285
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import SetoidList.

Import ListNotations.

(* ===================================================================== *)
(*  Multiset equivalence notation (same as rule_consolidation/Prelude)    *)
(* ===================================================================== *)

Notation "l1 '≡ₘ' l2" := (Permutation l1 l2) (at level 70, no associativity).

(* ===================================================================== *)
(*  Hash Function Model                                                   *)
(* ===================================================================== *)

Section HashModel.
  Variable A : Type.
  Variable hash : A -> Z.

  (* For u32-sized types, DefaultHasher has no practical collisions.
     This injectivity hypothesis reflects that. *)
  Hypothesis hash_injective : forall a b : A, hash a = hash b -> a = b.

  (* Ordering derived from hash values *)
  Definition hash_le (a b : A) : Prop := (hash a <= hash b)%Z.

  (* hash_le is reflexive *)
  Lemma hash_le_refl : forall a, hash_le a a.
  Proof. intros a. unfold hash_le. lia. Qed.

  (* hash_le is transitive *)
  Lemma hash_le_trans : forall a b c, hash_le a b -> hash_le b c -> hash_le a c.
  Proof. intros a b c Hab Hbc. unfold hash_le in *. lia. Qed.

  (* hash_le is total *)
  Lemma hash_le_total : forall a b, hash_le a b \/ hash_le b a.
  Proof. intros a b. unfold hash_le. lia. Qed.

  (* hash_le is antisymmetric (using injectivity) *)
  Lemma hash_le_antisym : forall a b, hash_le a b -> hash_le b a -> a = b.
  Proof.
    intros a b Hab Hba. unfold hash_le in *.
    apply hash_injective. lia.
  Qed.

End HashModel.

(* ===================================================================== *)
(*  List Utilities                                                        *)
(* ===================================================================== *)

(* flat_map over nil produces nil *)
Lemma flat_map_nil : forall (A B : Type) (f : A -> list B),
  flat_map f [] = [].
Proof. reflexivity. Qed.

(* flat_map distributes over cons *)
Lemma flat_map_cons : forall (A B : Type) (f : A -> list B) (x : A) (xs : list A),
  flat_map f (x :: xs) = f x ++ flat_map f xs.
Proof. reflexivity. Qed.

(* flat_map distributes over app *)
Lemma flat_map_app : forall (A B : Type) (f : A -> list B) (l1 l2 : list A),
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A0 B f l1 l2.
  induction l1 as [| x xs IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(* If every element maps to [], flat_map produces [] *)
Lemma flat_map_all_nil : forall (A B : Type) (f : A -> list B) (l : list A),
  (forall x, In x l -> f x = []) ->
  flat_map f l = [].
Proof.
  intros A0 B f l Hall.
  induction l as [| x xs IH].
  - reflexivity.
  - simpl.
    assert (Hx : f x = []) by (apply Hall; left; reflexivity).
    rewrite Hx. simpl. apply IH.
    intros y Hy. apply Hall. right. exact Hy.
Qed.

(* Specialized: Removing a subset of elements that all map to [] preserves flat_map *)
Lemma flat_map_filter_nil :
  forall (A B : Type) (pred : A -> bool) (f : A -> list B) (l : list A),
    (forall x, In x l -> pred x = false -> f x = []) ->
    flat_map f l = flat_map f (filter pred l).
Proof.
  intros A0 B pred f l Hnil.
  induction l as [| x xs IH].
  - reflexivity.
  - simpl. destruct (pred x) eqn:Hpred.
    + simpl. f_equal. apply IH.
      intros y Hy Hpy. apply Hnil. right. exact Hy. exact Hpy.
    + assert (Hx : f x = []) by (apply Hnil; [left; reflexivity | exact Hpred]).
      rewrite Hx. simpl. apply IH.
      intros y Hy Hpy. apply Hnil. right. exact Hy. exact Hpy.
Qed.

(* Conditional extraction: produces a list or nil based on a boolean *)
Definition cond_extract {V : Type} (b : bool) (vals : list V) : list V :=
  if b then vals else [].

Lemma cond_extract_true : forall (V : Type) (vals : list V),
  cond_extract true vals = vals.
Proof. reflexivity. Qed.

Lemma cond_extract_false : forall (V : Type) (vals : list V),
  cond_extract false vals = [].
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Decidable Equality Helper                                             *)
(* ===================================================================== *)

(* Boolean equality reflection *)
Definition eqb_spec_type (A : Type) (eqb : A -> A -> bool) : Prop :=
  forall x y, eqb x y = true <-> x = y.
