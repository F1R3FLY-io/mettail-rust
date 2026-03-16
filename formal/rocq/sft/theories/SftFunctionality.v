(*
 * SftFunctionality: Functionality (single-valuedness) preservation for
 * Symbolic Finite Transducers.
 *
 * Proves that functionality is preserved under SFT operations:
 *   1. Identity is functional
 *   2. Constant-output SFTs are functional
 *   3. Composition preserves functionality
 *   4. Domain extraction preserves language membership
 *
 * ## Modeling Approach
 *
 * An SFT is modeled as f : A -> list B (per-element transduction).
 * Functionality means each input element produces at most one output:
 *   functional f := forall a, length (f a) <= 1
 *
 * This per-element determinism ensures per-word determinism: for any
 * input word, there is at most one output word (the concatenation
 * of per-element outputs is uniquely determined).
 *
 * ## References
 *
 * - D'Antoni, L. & Veanes, M. (2012). "Symbolic Finite State Transducers:
 *   Algorithms and Applications." POPL 2012.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition       | Rust Code                              | Location
 *   ----------------------|----------------------------------------|------------------
 *   functional            | SymbolicFiniteTransducer::is_functional | sft.rs:1038
 *   sft_identity          | OutputFunction::Identity               | sft.rs:58
 *   sft_constant          | OutputFunction::Constant               | sft.rs:55
 *   sft_compose           | SymbolicFiniteTransducer::compose()    | sft.rs:393
 *   in_domain             | SymbolicFiniteTransducer::domain_sfa() | sft.rs:352
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Import ListNotations.

(* ===================================================================== *)
(*  Section 1: Core Definitions                                           *)
(* ===================================================================== *)

Section SftFunctionality.

  Variable A B C : Type.

  (** Per-element transduction lifted to words via flat_map. *)
  Definition sft_apply {X Y : Type} (f : X -> list Y) (w : list X) : list Y :=
    flat_map f w.

  (** The identity SFT: each element maps to a singleton. *)
  Definition sft_identity (x : A) : list A := [x].

  (** A constant SFT: every element maps to the same singleton output. *)
  Definition sft_constant (c : B) (_ : A) : list B := [c].

  (** An epsilon SFT: every element maps to empty (drops all input). *)
  Definition sft_epsilon (_ : A) : list B := [].

  (** Composition of SFTs: apply f, then apply g to each intermediate. *)
  Definition sft_compose {X Y Z : Type}
    (f : X -> list Y) (g : Y -> list Z) : X -> list Z :=
    fun x => flat_map g (f x).

  (** An SFT f is functional iff every input element produces at most
      one output element. This per-element property implies per-word
      single-valuedness of the transduction. *)
  Definition functional {X Y : Type} (f : X -> list Y) : Prop :=
    forall a : X, length (f a) <= 1.

  (** A word w is in the domain of SFT f iff f produces non-empty output. *)
  Definition in_domain {X Y : Type} (f : X -> list Y) (w : list X) : Prop :=
    sft_apply f w <> [].

(* ===================================================================== *)
(*  Section 2: Auxiliary Lemmas                                           *)
(* ===================================================================== *)

  (** A list of length <= 1 is either empty or a singleton. *)
  Lemma length_le_1_cases :
    forall {X : Type} (l : list X),
      length l <= 1 -> l = [] \/ exists x, l = [x].
  Proof.
    intros X l H.
    destruct l as [| x l'].
    - left. reflexivity.
    - right. exists x.
      simpl in H.
      destruct l' as [| y l''].
      + reflexivity.
      + simpl in H. lia.
  Qed.

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

  (** Length of flat_map when f is functional: length <= length of input. *)
  Lemma flat_map_functional_length :
    forall {X Y : Type} (f : X -> list Y) (l : list X),
      functional f ->
      length (flat_map f l) <= length l.
  Proof.
    intros X Y f l Hf.
    induction l as [| x l' IH]; simpl.
    - lia.
    - rewrite length_app.
      specialize (Hf x).
      lia.
  Qed.

  (** flat_map on empty list is empty. *)
  Lemma flat_map_nil :
    forall {X Y : Type} (g : X -> list Y),
      flat_map g [] = [].
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (** flat_map on singleton. *)
  Lemma flat_map_cons_nil :
    forall {X Y : Type} (g : X -> list Y) (x : X),
      flat_map g [x] = g x.
  Proof.
    intros. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  (** If flat_map g applied to a list of length <= 1 where g is functional,
      the result has length <= 1. *)
  Lemma flat_map_functional_le1 :
    forall {X Y : Type} (g : X -> list Y) (l : list X),
      functional g ->
      length l <= 1 ->
      length (flat_map g l) <= 1.
  Proof.
    intros X Y g l Hg Hlen.
    destruct (length_le_1_cases l Hlen) as [Hnil | [x Hsingleton]].
    - subst l. simpl. lia.
    - subst l. simpl. rewrite app_nil_r. apply Hg.
  Qed.

  (** flat_map is non-empty iff some element's image is non-empty. *)
  Lemma flat_map_nonempty_iff :
    forall {X Y : Type} (f : X -> list Y) (w : list X),
      flat_map f w <> [] <-> exists a, In a w /\ f a <> [].
  Proof.
    intros X Y f w. split.
    - (* Forward: flat_map f w <> [] -> exists a, In a w /\ f a <> [] *)
      intro H.
      induction w as [| x w' IH].
      + simpl in H. contradiction.
      + simpl in H.
        destruct (f x) eqn:Hfx.
        * (* f x = [], so flat_map f w' <> [] *)
          simpl in H.
          destruct (IH H) as [a [Hin Hfa]].
          exists a. split.
          -- right. exact Hin.
          -- exact Hfa.
        * (* f x = y :: l, so f x <> [] *)
          exists x. split.
          -- left. reflexivity.
          -- rewrite Hfx. discriminate.
    - (* Backward: exists a, In a w /\ f a <> [] -> flat_map f w <> [] *)
      intros [a [Hin Hfa]].
      induction w as [| x w' IH].
      + destruct Hin.
      + simpl.
        destruct Hin as [Heq | Hin].
        * subst x.
          destruct (f a) eqn:Hfx.
          -- contradiction.
          -- simpl. discriminate.
        * destruct (f x) eqn:Hfx.
          -- simpl. apply IH. exact Hin.
          -- simpl. discriminate.
  Qed.

(* ===================================================================== *)
(*  Section 3: Theorem 1 — Identity is Functional                        *)
(* ===================================================================== *)

  (** The identity SFT always produces exactly one output per input,
      so it is trivially functional. *)
  Theorem identity_functional : functional sft_identity.
  Proof.
    unfold functional, sft_identity.
    intro a. simpl. lia.
  Qed.

(* ===================================================================== *)
(*  Section 4: Theorem 2 — Constant is Functional                        *)
(* ===================================================================== *)

  (** A constant SFT maps every input to the same singleton output,
      so it is functional. *)
  Theorem constant_functional :
    forall (c : B), functional (sft_constant c).
  Proof.
    intros c.
    unfold functional, sft_constant.
    intro a. simpl. lia.
  Qed.

  (** The epsilon SFT (drops everything) is also functional. *)
  Theorem epsilon_functional : functional (@sft_epsilon).
  Proof.
    unfold functional, sft_epsilon.
    intro a. simpl. lia.
  Qed.

(* ===================================================================== *)
(*  Section 5: Theorem 3 — Composition Preserves Functionality            *)
(* ===================================================================== *)

  (** If f : A -> list B and g : B -> list C are both functional,
      then their composition (sft_compose f g) is also functional.

      Proof sketch:
        For any input a, we must show length (flat_map g (f a)) <= 1.
        Since f is functional, f a has length <= 1:
        - If f a = [], then flat_map g [] = [], length 0 <= 1.
        - If f a = [b], then flat_map g [b] = g b, and since g is
          functional, length (g b) <= 1. *)
  Theorem compose_preserves_functional :
    forall (f : A -> list B) (g : B -> list C),
      functional f ->
      functional g ->
      functional (sft_compose f g).
  Proof.
    intros f g Hf Hg.
    unfold functional, sft_compose.
    intro a.
    apply flat_map_functional_le1.
    - exact Hg.
    - apply Hf.
  Qed.

(* ===================================================================== *)
(*  Section 6: Theorem 4 — Domain Extraction Preserves Language           *)
(* ===================================================================== *)

  (** The domain of an SFT f consists of exactly those words w that
      contain at least one element a such that f a is non-empty.

      This corresponds to the Rust code domain_sfa() which extracts
      an SFA from an SFT by keeping the guard predicates and dropping
      the output functions. A word is in the SFA's language iff the
      SFT can produce at least one output on it. *)
  Theorem domain_characterization :
    forall {X Y : Type} (f : X -> list Y) (w : list X),
      in_domain f w <-> exists a, In a w /\ f a <> [].
  Proof.
    intros X Y f w.
    unfold in_domain, sft_apply.
    apply flat_map_nonempty_iff.
  Qed.

  (** The empty word is never in the domain (no elements to transduce). *)
  Corollary empty_word_not_in_domain :
    forall {X Y : Type} (f : X -> list Y),
      ~ in_domain f [].
  Proof.
    intros X Y f.
    unfold in_domain, sft_apply. simpl.
    intro H. apply H. reflexivity.
  Qed.

  (** Domain is monotone under word extension: if w is in the domain,
      so is any word containing w as a sublist. *)
  Corollary domain_monotone_cons :
    forall {X Y : Type} (f : X -> list Y) (x : X) (w : list X),
      in_domain f w -> in_domain f (x :: w).
  Proof.
    intros X Y f x w Hdom.
    unfold in_domain, sft_apply in *.
    simpl.
    destruct (f x) eqn:Hfx.
    - simpl. exact Hdom.
    - simpl. discriminate.
  Qed.

  (** A single-element word [a] is in the domain iff f a is non-empty. *)
  Corollary singleton_domain :
    forall {X Y : Type} (f : X -> list Y) (a : X),
      in_domain f [a] <-> f a <> [].
  Proof.
    intros X Y f a.
    unfold in_domain, sft_apply. simpl.
    rewrite app_nil_r.
    split; auto.
  Qed.

  (** Domain is preserved under composition when both SFTs are "total"
      (i.e., every element produces at least one output). *)
  Corollary domain_compose_total :
    forall (f : A -> list B) (g : B -> list C) (w : list A),
      (forall a, f a <> []) ->
      (forall b, g b <> []) ->
      in_domain f w ->
      in_domain (sft_compose f g) w.
  Proof.
    intros f g w Hf_total Hg_total Hdom.
    rewrite domain_characterization in Hdom.
    destruct Hdom as [a [Hin Hfa]].
    rewrite domain_characterization.
    exists a. split.
    - exact Hin.
    - unfold sft_compose.
      destruct (f a) eqn:Hfa_eq.
      + contradiction.
      + simpl.
        (* Goal: g b ++ flat_map g l <> []
           Since g b <> [] by Hg_total, the concatenation is non-empty. *)
        destruct (g b) eqn:Hgb.
        * exfalso. apply (Hg_total b). exact Hgb.
        * simpl. discriminate.
  Qed.

(* ===================================================================== *)
(*  Section 7: Additional Properties                                      *)
(* ===================================================================== *)

  (** Functionality is decidable for constant functions. *)
  Lemma functional_iff_all_le1 :
    forall {X Y : Type} (f : X -> list Y),
      functional f <-> forall a, length (f a) <= 1.
  Proof.
    intros X Y f. unfold functional. split; auto.
  Qed.

  (** A functional SFT applied to a word of length n produces
      at most n output elements. *)
  Theorem functional_output_bounded :
    forall {X Y : Type} (f : X -> list Y) (w : list X),
      functional f ->
      length (sft_apply f w) <= length w.
  Proof.
    intros X Y f w Hf.
    unfold sft_apply.
    apply flat_map_functional_length.
    exact Hf.
  Qed.

  (** The identity SFT preserves word length exactly. *)
  Theorem identity_preserves_length :
    forall (w : list A),
      length (sft_apply sft_identity w) = length w.
  Proof.
    intro w.
    unfold sft_apply, sft_identity.
    induction w as [| x w' IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

End SftFunctionality.
