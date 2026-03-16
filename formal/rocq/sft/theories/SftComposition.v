(*
 * SftComposition: Composition properties of Symbolic Finite Transducers.
 *
 * Proves that the composition of SFTs (modeled as list-lifted functions)
 * forms a monoid under the identity transducer:
 *   1. Left identity:   compose(identity, T) = T
 *   2. Right identity:  compose(T, identity) = T
 *   3. Associativity:   compose(compose(T1, T2), T3) = compose(T1, compose(T2, T3))
 *
 * ## Modeling Approach
 *
 * We model an SFT abstractly as a function f : A -> list B, lifted to
 * input words (list A) via flat_map. This captures the essential algebraic
 * structure: each input element is independently transduced to zero or more
 * output elements, and the results are concatenated.
 *
 * Composition of SFTs (A->B) and (B->C) is modeled as:
 *   compose f g := fun a => flat_map g (f a)
 * which lifts to words as flat_map (compose f g) w.
 *
 * ## References
 *
 * - D'Antoni, L. & Veanes, M. (2012). "Symbolic Finite State Transducers:
 *   Algorithms and Applications." POPL 2012.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition       | Rust Code                              | Location
 *   ----------------------|----------------------------------------|------------------
 *   sft_apply             | SymbolicFiniteTransducer::transduce()  | sft.rs:309
 *   sft_compose           | SymbolicFiniteTransducer::compose()    | sft.rs:393
 *   sft_identity          | OutputFunction::Identity               | sft.rs:58
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

(* ===================================================================== *)
(*  Section 1: Core Definitions                                           *)
(* ===================================================================== *)

Section SftComposition.

  Variable A B C D : Type.

  (** An SFT is modeled as a per-element transduction function.
      Given f : A -> list B, the SFT transforms a word w : list A
      by applying f to each element and concatenating the results. *)
  Definition sft_apply {X Y : Type} (f : X -> list Y) (w : list X) : list Y :=
    flat_map f w.

  (** The identity SFT maps each element to itself (singleton list). *)
  Definition sft_identity (x : A) : list A := [x].

  (** Composition of two SFTs: apply f element-wise, then apply g
      element-wise to each intermediate output, and concatenate. *)
  Definition sft_compose {X Y Z : Type}
    (f : X -> list Y) (g : Y -> list Z) : X -> list Z :=
    fun x => flat_map g (f x).

(* ===================================================================== *)
(*  Section 2: Auxiliary Lemmas on flat_map                               *)
(* ===================================================================== *)

  (** flat_map distributes over append. *)
  Lemma flat_map_app :
    forall {X Y : Type} (f : X -> list Y) (l1 l2 : list X),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    intros X Y f l1 l2.
    induction l1 as [| x l1' IH]; simpl.
    - reflexivity.
    - rewrite IH. rewrite app_assoc. reflexivity.
  Qed.

  (** flat_map with singleton is identity. *)
  Lemma flat_map_singleton :
    forall {X : Type} (l : list X),
      flat_map (fun x => [x]) l = l.
  Proof.
    intros X l.
    induction l as [| x l' IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (** flat_map composition: flat_map g (flat_map f l) = flat_map (compose f g) l.
      This is the key lemma for associativity. *)
  Lemma flat_map_flat_map :
    forall {X Y Z : Type} (f : X -> list Y) (g : Y -> list Z) (l : list X),
      flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
  Proof.
    intros X Y Z f g l.
    induction l as [| x l' IH]; simpl.
    - reflexivity.
    - rewrite flat_map_app. rewrite IH. reflexivity.
  Qed.

(* ===================================================================== *)
(*  Section 3: Main Theorems                                              *)
(* ===================================================================== *)

  (** Theorem 1: Left Identity.
      Composing the identity SFT on the left with any SFT g yields g.
      That is, for all words w:
        sft_apply (sft_compose sft_identity g) w = sft_apply g w  *)
  (** Helper: flat_map g [x] = g x. *)
  Lemma flat_map_singleton_apply :
    forall {X Y : Type} (g : X -> list Y) (x : X),
      flat_map g [x] = g x.
  Proof.
    intros X Y g x. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Theorem sft_compose_left_identity :
    forall (g : A -> list B) (w : list A),
      sft_apply (sft_compose sft_identity g) w = sft_apply g w.
  Proof.
    intros g w.
    unfold sft_apply, sft_compose, sft_identity.
    induction w as [| a w' IH].
    - simpl. reflexivity.
    - simpl.
      (* After simpl, LHS is: g a ++ flat_map g [] ++ flat_map ... w'
         which is: g a ++ [] ++ flat_map ... w'
         RHS is: g a ++ flat_map g w' *)
      rewrite app_nil_r.
      f_equal.
      exact IH.
  Qed.

  (** Theorem 2: Right Identity.
      Composing any SFT f on the left with the identity SFT yields f.
      That is, for all words w:
        sft_apply (sft_compose f sft_identity) w = sft_apply f w

      Note: sft_identity here operates on B, so we use a B-typed identity. *)
  Theorem sft_compose_right_identity :
    forall (f : A -> list B) (w : list A),
      sft_apply (sft_compose f (fun x : B => [x])) w = sft_apply f w.
  Proof.
    intros f w.
    unfold sft_apply, sft_compose.
    induction w as [| a w' IH]; simpl.
    - reflexivity.
    - (* flat_map (fun x => [x]) (f a) = f a by flat_map_singleton *)
      rewrite flat_map_singleton.
      rewrite IH.
      reflexivity.
  Qed.

  (** Theorem 3: Associativity.
      Composing (f then g) then h yields the same result as
      composing f then (g then h), for all words w:
        sft_apply (sft_compose (sft_compose f g) h) w
        = sft_apply (sft_compose f (sft_compose g h)) w  *)
  Theorem sft_compose_assoc :
    forall (f : A -> list B) (g : B -> list C) (h : C -> list D) (w : list A),
      sft_apply (sft_compose (sft_compose f g) h) w =
      sft_apply (sft_compose f (sft_compose g h)) w.
  Proof.
    intros f g h w.
    unfold sft_apply, sft_compose.
    induction w as [| a w' IH]; simpl.
    - reflexivity.
    - (* LHS inner: flat_map h (flat_map g (f a))
         RHS inner: flat_map (fun y => flat_map h (g y)) (f a)
         These are equal by flat_map_flat_map. *)
      rewrite flat_map_flat_map.
      rewrite IH.
      reflexivity.
  Qed.

(* ===================================================================== *)
(*  Section 4: Corollaries                                                *)
(* ===================================================================== *)

  (** Corollary: sft_compose with sft_identity is extensionally equal to
      the original function (per-element, not just per-word). *)
  Corollary sft_compose_identity_element_left :
    forall (g : A -> list B) (a : A),
      sft_compose sft_identity g a = g a.
  Proof.
    intros g a.
    unfold sft_compose, sft_identity. simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Corollary sft_compose_identity_element_right :
    forall (f : A -> list B) (a : A),
      sft_compose f (fun x : B => [x]) a = f a.
  Proof.
    intros f a.
    unfold sft_compose.
    rewrite flat_map_singleton.
    reflexivity.
  Qed.

  (** Corollary: Associativity at the element level. *)
  Corollary sft_compose_assoc_element :
    forall (f : A -> list B) (g : B -> list C) (h : C -> list D) (a : A),
      sft_compose (sft_compose f g) h a =
      sft_compose f (sft_compose g h) a.
  Proof.
    intros f g h a.
    unfold sft_compose.
    rewrite flat_map_flat_map.
    reflexivity.
  Qed.

  (** Empty word is a fixed point: any SFT applied to [] yields []. *)
  Lemma sft_apply_nil :
    forall {X Y : Type} (f : X -> list Y),
      sft_apply f [] = [].
  Proof.
    intros X Y f.
    unfold sft_apply. simpl. reflexivity.
  Qed.

  (** SFT application distributes over word concatenation. *)
  Lemma sft_apply_app :
    forall {X Y : Type} (f : X -> list Y) (w1 w2 : list X),
      sft_apply f (w1 ++ w2) = sft_apply f w1 ++ sft_apply f w2.
  Proof.
    intros X Y f w1 w2.
    unfold sft_apply.
    apply flat_map_app.
  Qed.

End SftComposition.
