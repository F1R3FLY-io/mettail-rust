(*
 * StftFunctionality: Functionality (single-valuedness) preservation for
 * Symbolic *Tree* Transducers (the ranked-tree analog of SftFunctionality.v).
 *
 * A forest transducer is modeled as `f : Tree X -> list (Tree Y)`: each input
 * tree produces zero, one, or many output trees. It is *functional*
 * (single-valued) iff every input tree produces at most one output tree:
 *   functional f := forall t, length (f t) <= 1
 *
 * This file proves functionality is preserved/established under the tree
 * transducer operations, mirroring the word file SftFunctionality.v with
 * "word length" replaced by "node count" (`tcount`):
 *   1. The identity transducer is functional.
 *   2. Constant- and epsilon-output transducers are functional.
 *   3. Composition preserves functionality.
 *   4. Domain extraction (drop the outputs, keep the matching structure):
 *      a tree is in the domain iff the transducer produces a non-empty output.
 *   5. Node-count bounds: a deterministic relabeling homomorphism preserves
 *      node count exactly (genuinely tree-recursive, via `tree_ind'`), and a
 *      functional forest transducer yields at most one output tree.
 *
 * ## Modeling Approach
 *
 * Ranked trees `Tree X := tnode : X -> list (Tree X) -> Tree X` with the strong
 * induction principle `tree_ind'` (a plain Fixpoint, hence axiom-free; Coq's
 * auto-generated principle is too weak through the `list (Tree X)` nesting).
 * The forest-level reasoning reuses the same `flat_map` length algebra as the
 * word transducer proofs in SftFunctionality.v.
 *
 * ## References
 *
 * - D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and
 *   Transducers." CAV 2017.
 * - Comon, H. et al. "Tree Automata Techniques and Applications" (TATA), Ch. 6.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition       | Rust Code                                      | Location
 *   ----------------------|------------------------------------------------|--------------------------------
 *   Tree / tnode          | SymTerm { constructor, payload, children }     | prattail/src/sym_tree.rs
 *   functional            | single-valued transduction (≤1 output term)    | prattail/src/sym_tree_transducer.rs
 *   ft_identity           | identity transduction ([t])                    | prattail/src/sym_tree_transducer.rs
 *   ft_constant           | constant OutputBuilder                         | prattail/src/sym_tree_transducer.rs
 *   ft_compose            | compose_transduce()                            | prattail/src/sym_tree_transducer.rs
 *   in_domain             | SymbolicTreeTransducer::domain_sta()           | prattail/src/sym_tree_transducer.rs
 *   thom / tcount         | OutputBuilder::Build relabel / node count      | prattail/src/sym_tree_transducer.rs
 *
 * The shared flat_map length foundation is the same one used by the WORD
 * transducer proofs in formal/rocq/sft/theories/SftFunctionality.v.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.

Import ListNotations.

(* ===================================================================== *)
(*  Section 0: Ranked trees and a strong induction principle             *)
(* ===================================================================== *)

(** A ranked tree: a head label of type [X] with an ordered child list. The
    Rocq model of the Rust [SymTerm]. *)
Inductive Tree (X : Type) : Type :=
  tnode : X -> list (Tree X) -> Tree X.
Arguments tnode {X} _ _.

Section TreeInd.
  Variable X : Type.
  Variable P : Tree X -> Prop.
  Hypothesis Hnode : forall (a : X) (ch : list (Tree X)), Forall P ch -> P (tnode a ch).

  (** Strong induction over [Tree]: builds the [Forall P ch] witness by a nested
      structural recursion over the child list. A plain [Fixpoint] — no axioms. *)
  Fixpoint tree_ind' (t : Tree X) : P t :=
    match t with
    | tnode a ch =>
        Hnode a ch
          ((fix all (l : list (Tree X)) : Forall P l :=
              match l with
              | nil => Forall_nil P
              | cons t' r => Forall_cons t' (tree_ind' t') (all r)
              end) ch)
    end.
End TreeInd.

(** Node count: a node contributes 1 plus the counts of its children. The tree
    analog of word [length]. *)
Fixpoint tcount {X : Type} (t : Tree X) : nat :=
  match t with
  | tnode _ ch => 1 + list_sum (map tcount ch)
  end.

(** The bottom-up relabeling homomorphism (deterministic structural rebuild). *)
Fixpoint thom {X Y : Type} (g : X -> Y) (t : Tree X) : Tree Y :=
  match t with
  | tnode a ch => tnode (g a) (map (thom g) ch)
  end.

(* ===================================================================== *)
(*  Section 1: Core transducer definitions                               *)
(* ===================================================================== *)

Section StftFunctionality.

  Variable A B C : Type.

  (** Apply a forest transducer to a single input tree. *)
  Definition ft_apply {X Y : Type} (f : Tree X -> list (Tree Y)) (t : Tree X)
    : list (Tree Y) := f t.

  (** The identity forest transducer: emit the input tree unchanged. *)
  Definition ft_identity {X : Type} (t : Tree X) : list (Tree X) := [t].

  (** A constant transducer: every input maps to the same singleton output. *)
  Definition ft_constant (c : Tree B) (_ : Tree A) : list (Tree B) := [c].

  (** An epsilon transducer: every input maps to empty (rejects everything). *)
  Definition ft_epsilon (_ : Tree A) : list (Tree B) := [].

  (** Sequential composition of forest transducers. *)
  Definition ft_compose {X Y Z : Type}
    (f : Tree X -> list (Tree Y)) (g : Tree Y -> list (Tree Z))
    : Tree X -> list (Tree Z) :=
    fun t => flat_map g (f t).

  (** A forest transducer is *functional* (single-valued) iff each input tree
      produces at most one output tree. *)
  Definition functional {X Y : Type} (f : Tree X -> list (Tree Y)) : Prop :=
    forall t : Tree X, length (f t) <= 1.

  (** A tree [t] is in the domain of [f] iff [f] produces a non-empty output. *)
  Definition in_domain {X Y : Type} (f : Tree X -> list (Tree Y)) (t : Tree X)
    : Prop := f t <> [].

(* ===================================================================== *)
(*  Section 2: Auxiliary lemmas                                           *)
(* ===================================================================== *)

  (** A list of length <= 1 is empty or a singleton. *)
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

  (** flat_map with a singleton-producing function is the identity. *)
  Lemma flat_map_singleton :
    forall {X : Type} (l : list X),
      flat_map (fun x => [x]) l = l.
  Proof.
    intros X l.
    induction l as [| x l' IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (** If [g] is functional and [l] has length <= 1, then [flat_map g l] has
      length <= 1. The single-step engine of composition preservation. *)
  Lemma flat_map_functional_le1 :
    forall {X Y : Type} (g : Tree X -> list (Tree Y)) (l : list (Tree X)),
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
    forall {X Y : Type} (f : X -> list Y) (l : list X),
      flat_map f l <> [] <-> exists a, In a l /\ f a <> [].
  Proof.
    intros X Y f l. split.
    - intro H.
      induction l as [| x l' IH].
      + simpl in H. contradiction.
      + simpl in H.
        destruct (f x) eqn:Hfx.
        * simpl in H.
          destruct (IH H) as [a [Hin Hfa]].
          exists a. split.
          -- right. exact Hin.
          -- exact Hfa.
        * exists x. split.
          -- left. reflexivity.
          -- rewrite Hfx. discriminate.
    - intros [a [Hin Hfa]].
      induction l as [| x l' IH].
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
(*  Section 3: Theorem 1 — Identity is functional                        *)
(* ===================================================================== *)

  (** The identity transducer emits exactly one output per input. *)
  Theorem identity_functional : functional (@ft_identity A).
  Proof.
    unfold functional, ft_identity.
    intro t. simpl. lia.
  Qed.

(* ===================================================================== *)
(*  Section 4: Theorem 2 — Constant / epsilon are functional             *)
(* ===================================================================== *)

  (** A constant transducer maps every input to the same singleton output. *)
  Theorem constant_functional :
    forall (c : Tree B), functional (ft_constant c).
  Proof.
    intros c.
    unfold functional, ft_constant.
    intro t. simpl. lia.
  Qed.

  (** The epsilon transducer (rejects everything) is functional. *)
  Theorem epsilon_functional : functional (@ft_epsilon).
  Proof.
    unfold functional, ft_epsilon.
    intro t. simpl. lia.
  Qed.

(* ===================================================================== *)
(*  Section 5: Theorem 3 — Composition preserves functionality           *)
(* ===================================================================== *)

  (** If [f] and [g] are both functional, so is [ft_compose f g]. For any input
      [t], [f t] has length <= 1 (f functional); feeding that into [flat_map g]
      with [g] functional keeps the length <= 1. *)
  Theorem compose_preserves_functional :
    forall (f : Tree A -> list (Tree B)) (g : Tree B -> list (Tree C)),
      functional f ->
      functional g ->
      functional (ft_compose f g).
  Proof.
    intros f g Hf Hg.
    unfold functional, ft_compose.
    intro t.
    apply flat_map_functional_le1.
    - exact Hg.
    - apply Hf.
  Qed.

(* ===================================================================== *)
(*  Section 6: Theorem 4 — Domain extraction                             *)
(* ===================================================================== *)

  (** A tree is in the domain of [ft_compose f g] iff [f] produces some
      intermediate tree [s] on which [g] is itself non-empty. This is the tree
      analog of the word domain characterization, lifted to the *image set* of
      the first stage (the Rust [domain_sta] keeps a transition exactly when the
      transducer can produce output at that node). *)
  Theorem domain_characterization :
    forall (f : Tree A -> list (Tree B)) (g : Tree B -> list (Tree C)) (t : Tree A),
      in_domain (ft_compose f g) t <-> exists s, In s (f t) /\ g s <> [].
  Proof.
    intros f g t.
    unfold in_domain, ft_compose.
    apply flat_map_nonempty_iff.
  Qed.

  (** The identity transducer's domain is everything: every tree is in it. *)
  Corollary identity_total_domain :
    forall (t : Tree A), in_domain (@ft_identity A) t.
  Proof.
    intros t.
    unfold in_domain, ft_identity. discriminate.
  Qed.

  (** The epsilon transducer's domain is empty: no tree is in it. *)
  Corollary epsilon_empty_domain :
    forall (t : Tree A), ~ in_domain (@ft_epsilon) t.
  Proof.
    intros t.
    unfold in_domain, ft_epsilon.
    intro H. apply H. reflexivity.
  Qed.

  (** Domain is preserved under composition when both stages are *total* (every
      input produces some output). *)
  Corollary domain_compose_total :
    forall (f : Tree A -> list (Tree B)) (g : Tree B -> list (Tree C)) (t : Tree A),
      (forall u, f u <> []) ->
      (forall v, g v <> []) ->
      in_domain (ft_compose f g) t.
  Proof.
    intros f g t Hf_total Hg_total.
    rewrite domain_characterization.
    (* f t is non-empty, so it has a head s; g s is non-empty by totality. *)
    destruct (f t) as [| s rest] eqn:Hft.
    - exfalso. apply (Hf_total t). exact Hft.
    - exists s. split.
      + left. reflexivity.
      + apply Hg_total.
  Qed.

(* ===================================================================== *)
(*  Section 7: Node-count bounds                                          *)
(* ===================================================================== *)

  (** ---- Theorem 5a (genuinely tree-recursive). ----
      A deterministic relabeling homomorphism preserves node count exactly.
      This is the tree analog of "the identity word map preserves word length",
      and the proof recurses through the tree with [tree_ind']: [map_map] aligns
      the [list_sum (map tcount ...)] terms and the [Forall] IH equates them
      child-by-child. *)
  Theorem thom_preserves_tcount :
    forall {X Y : Type} (g : X -> Y) (t : Tree X),
      tcount (thom g t) = tcount t.
  Proof.
    intros X Y g t.
    induction t using tree_ind'.
    simpl.                          (* both sides: 1 + list_sum (map tcount ...) *)
    f_equal.                        (* goal: list_sum (map tcount (map (thom g) ch)) = list_sum (map tcount ch) *)
    rewrite map_map.                (* map tcount (map (thom g) ch) = map (fun c => tcount (thom g c)) ch *)
    f_equal.                        (* goal: map (fun c => tcount (thom g c)) ch = map tcount ch *)
    apply map_ext_in.
    intros x Hin.
    rewrite Forall_forall in H.
    apply H. exact Hin.
  Qed.

  (** ---- Theorem 5b. ----
      The deterministic relabel, viewed as a forest transducer
      [fun t => [thom g t]], is functional (it yields exactly one output tree). *)
  Theorem thom_singleton_functional :
    forall (g : A -> B), functional (fun t : Tree A => [thom g t]).
  Proof.
    intros g.
    unfold functional.
    intro t. simpl. lia.
  Qed.

  (** ---- Theorem 5c. ----
      A functional forest transducer yields at most one output tree on any
      input (the defining bound, surfaced as a per-input fact). *)
  Theorem functional_output_le1 :
    forall {X Y : Type} (f : Tree X -> list (Tree Y)) (t : Tree X),
      functional f ->
      length (f t) <= 1.
  Proof.
    intros X Y f t Hf.
    apply Hf.
  Qed.

(* ===================================================================== *)
(*  Section 8: Additional properties                                      *)
(* ===================================================================== *)

  (** Functionality unfolds to the per-input length bound (decidability hook). *)
  Lemma functional_iff_all_le1 :
    forall {X Y : Type} (f : Tree X -> list (Tree Y)),
      functional f <-> forall t, length (f t) <= 1.
  Proof.
    intros X Y f. unfold functional. split; auto.
  Qed.

  (** The identity relabel ([thom id]) preserves node count — a direct corollary
      of [thom_preserves_tcount], matching the word file's
      [identity_preserves_length]. *)
  Corollary identity_relabel_preserves_tcount :
    forall {X : Type} (t : Tree X),
      tcount (thom (fun a => a) t) = tcount t.
  Proof.
    intros X t.
    apply thom_preserves_tcount.
  Qed.

End StftFunctionality.

(* ===================================================================== *)
(*  Assumption audit: every main theorem must be closed.                 *)
(* ===================================================================== *)

Print Assumptions identity_functional.
Print Assumptions constant_functional.
Print Assumptions epsilon_functional.
Print Assumptions compose_preserves_functional.
Print Assumptions domain_characterization.
Print Assumptions thom_preserves_tcount.
Print Assumptions thom_singleton_functional.
Print Assumptions functional_output_le1.

(* tree_ind' itself is a plain Fixpoint — confirm it carries no axioms. *)
Print Assumptions tree_ind'.
