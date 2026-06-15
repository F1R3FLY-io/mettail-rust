(*
 * StftComposition: Composition properties of Symbolic *Tree* Transducers
 * (the ranked-tree analog of SftComposition.v).
 *
 * Where the word transducer (SftComposition.v) reads a word `list A` and
 * transduces it element-by-element, the *tree* transducer reads a ranked term
 * `Tree A` bottom-up: each node's constructor/payload/children are matched and
 * an OutputBuilder constructs the output node from the already-transduced
 * children. This file establishes the two algebraic layers of that machine:
 *
 *   (a) The deterministic bottom-up *relabeling homomorphism* `thom g`, which
 *       rebuilds every node with the same shape but relabels the head via `g`
 *       (the `OutputBuilder::Build { children = [0..n) }` case, i.e. a pure
 *       structural rebuild — the tree analog of a length-preserving word map).
 *       We prove it forms a monoid up to the identity relabel and that
 *       relabelings *fuse* ("forest fusion", the tree analog of
 *       `flat_map_flat_map`), preserving node count exactly.
 *
 *   (b) The (nondeterministic) *forest transducer monoid* `ft`, modeling the
 *       full transduction `f : Tree A -> list (Tree B)` (which may produce zero,
 *       one, or many output trees per input). Sequential composition is
 *           ft_compose f g := fun t => flat_map g (f t)
 *       with unit `ft_identity t := [t]`. The monoid laws are *exactly* the
 *       same flat_map algebra proved in SftComposition.v — we re-prove the three
 *       flat_map lemmas locally, as the word file does, so the word and tree
 *       transducer-composition monoids share one foundation.
 *
 * ## Modeling Approach
 *
 * A ranked tree is `Tree X := tnode : X -> list (Tree X) -> Tree X`. Coq's
 * auto-generated induction principle is too weak through the `list (Tree X)`
 * nesting, so we hand-roll a strong principle `tree_ind'` carrying a
 * `Forall P ch` hypothesis on the children (it is a plain Fixpoint, hence
 * axiom-free). All tree-recursive proofs go through `induction t using tree_ind'`.
 *
 * ## References
 *
 * - D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and
 *   Transducers." CAV 2017. (symbolic tree transducers; bottom-up transduction)
 * - Comon, H. et al. "Tree Automata Techniques and Applications" (TATA),
 *   Ch. 6 (tree transducers; homomorphisms; composition).
 * - Engelfriet, J. (1975). "Bottom-up and top-down tree transformations."
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition       | Rust Code                                      | Location
 *   ----------------------|------------------------------------------------|--------------------------------
 *   Tree / tnode          | SymTerm { constructor, payload, children }     | prattail/src/sym_tree.rs
 *   thom g                | OutputBuilder::Build (children = identity sel) | prattail/src/sym_tree_transducer.rs
 *   ft_apply              | SymbolicTreeTransducer::transduce()            | prattail/src/sym_tree_transducer.rs
 *   ft_compose            | compose_transduce()                            | prattail/src/sym_tree_transducer.rs
 *   ft_identity           | identity transduction ([t])                    | prattail/src/sym_tree_transducer.rs
 *   tcount                | node count of SymTerm                          | prattail/src/sym_tree.rs
 *
 * The shared flat_map foundation (flat_map_app / flat_map_singleton /
 * flat_map_flat_map) is the same one used by the WORD transducer proofs in
 * formal/rocq/sft/theories/SftComposition.v.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.

(* ===================================================================== *)
(*  Section 0: Ranked trees and a strong induction principle             *)
(* ===================================================================== *)

(** A ranked tree: a head label of type [X] together with an ordered list of
    child subtrees. This is the Rocq model of the Rust [SymTerm] (its
    [constructor]/[payload] collapse into the single head label [X], and
    [children] is the child list). *)
Inductive Tree (X : Type) : Type :=
  tnode : X -> list (Tree X) -> Tree X.
Arguments tnode {X} _ _.

Section TreeInd.
  Variable X : Type.
  Variable P : Tree X -> Prop.
  Hypothesis Hnode : forall (a : X) (ch : list (Tree X)), Forall P ch -> P (tnode a ch).

  (** Strong induction over [Tree]: the auto-generated principle does not give
      an induction hypothesis for the children (they sit under [list]), so we
      build the [Forall P ch] witness by a nested structural recursion over the
      child list. This is a plain [Fixpoint], so it introduces no axioms. *)
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

(* ===================================================================== *)
(*  Section 1: Layer (a) — bottom-up relabeling homomorphism             *)
(* ===================================================================== *)

Section TreeHomomorphism.

  Variable A B C : Type.

  (** The bottom-up relabeling homomorphism induced by a head map [g]:
      rebuild every node, relabeling its head with [g] and recursing into the
      children. This is the [OutputBuilder::Build] case in which the output node
      reuses the input's shape and selects its children in order — a pure
      structural rebuild (the tree analog of a per-element word map). *)
  Fixpoint thom {X Y : Type} (g : X -> Y) (t : Tree X) : Tree Y :=
    match t with
    | tnode a ch => tnode (g a) (map (thom g) ch)
    end.

  (** Defining equation, stated explicitly for rewriting. *)
  Lemma thom_unfold :
    forall {X Y : Type} (g : X -> Y) (a : X) (ch : list (Tree X)),
      thom g (tnode a ch) = tnode (g a) (map (thom g) ch).
  Proof. intros. reflexivity. Qed.

  (** Node count: a node contributes 1 plus the counts of its children. This is
      the tree analog of word [length]; [thom] preserves it exactly. *)
  Fixpoint tcount {X : Type} (t : Tree X) : nat :=
    match t with
    | tnode _ ch => 1 + list_sum (map tcount ch)
    end.

  (** ---- Theorem (a.1): the identity relabel is the identity. ----
      [thom] with the identity head map returns its input unchanged. Proved by
      strong tree induction: the [Forall] hypothesis rewrites each child, and
      [map_ext_in] + [map_id] collapse the child list. *)
  Theorem thom_id :
    forall {X : Type} (t : Tree X),
      thom (fun a => a) t = t.
  Proof.
    intros X t.
    induction t using tree_ind'.
    rewrite thom_unfold.
    f_equal.
    (* map (thom id) ch = ch : every child is fixed by the IH (Forall). *)
    rewrite <- (map_id ch) at 2.
    apply map_ext_in.
    intros x Hin.
    rewrite Forall_forall in H.
    apply H. exact Hin.
  Qed.

  (** ---- Theorem (a.2): forest fusion. ----
      Two successive relabelings fuse into a single relabel by the composed head
      map. This is the tree analog of [flat_map_flat_map]: the deep rebuild
      commutes through composition. Proved by strong tree induction with
      [map_map] flattening the doubled [map] and the [Forall] IH rewriting each
      child pointwise. *)
  Theorem thom_fusion :
    forall {X Y Z : Type} (g1 : X -> Y) (g2 : Y -> Z) (t : Tree X),
      thom g2 (thom g1 t) = thom (fun a => g2 (g1 a)) t.
  Proof.
    intros X Y Z g1 g2 t.
    induction t using tree_ind'.
    rewrite thom_unfold.            (* thom g1 (tnode a ch) = tnode (g1 a) (map (thom g1) ch) *)
    rewrite thom_unfold.            (* thom g2 (...)        = tnode (g2 (g1 a)) (map (thom g2) ...) *)
    rewrite thom_unfold.            (* RHS unfold *)
    f_equal.
    rewrite map_map.                (* map (thom g2) (map (thom g1) ch) = map (fun c => thom g2 (thom g1 c)) ch *)
    apply map_ext_in.
    intros x Hin.
    rewrite Forall_forall in H.
    apply H. exact Hin.
  Qed.

  (** ---- Theorem (a.3): associativity of homomorphism composition. ----
      A direct corollary of fusion: relabeling by [g1] then [g2] then [g3]
      regroups freely, because each side fuses to the same single relabel
      [fun a => g3 (g2 (g1 a))]. *)
  Theorem thom_compose_assoc :
    forall {W X Y Z : Type} (g1 : W -> X) (g2 : X -> Y) (g3 : Y -> Z) (t : Tree W),
      thom g3 (thom g2 (thom g1 t)) = thom (fun a => g3 (g2 (g1 a))) t.
  Proof.
    intros W X Y Z g1 g2 g3 t.
    rewrite (thom_fusion g1 g2 t).
    (* Now: thom g3 (thom (fun a => g2 (g1 a)) t) = thom (fun a => g3 (g2 (g1 a))) t *)
    rewrite (thom_fusion (fun a => g2 (g1 a)) g3 t).
    reflexivity.
  Qed.

  (** ---- Theorem (a.4): node-count preservation. ----
      Relabeling never changes the shape, so the node count is preserved
      exactly. This is the tree analog of "the identity word map preserves
      length"; here *every* relabel preserves [tcount]. Proved by strong tree
      induction: [map_map] aligns the two [list_sum (map tcount ...)] terms and
      the [Forall] IH equates them child-by-child. *)
  Theorem tcount_thom :
    forall {X Y : Type} (g : X -> Y) (t : Tree X),
      tcount (thom g t) = tcount t.
  Proof.
    intros X Y g t.
    induction t using tree_ind'.
    rewrite thom_unfold.
    simpl.                          (* both sides become 1 + list_sum (map tcount ...) *)
    f_equal.                        (* goal: list_sum (map tcount (map (thom g) ch)) = list_sum (map tcount ch) *)
    rewrite map_map.                (* map tcount (map (thom g) ch) = map (fun c => tcount (thom g c)) ch *)
    f_equal.                        (* goal: map (fun c => tcount (thom g c)) ch = map tcount ch *)
    apply map_ext_in.
    intros x Hin.
    rewrite Forall_forall in H.
    apply H. exact Hin.
  Qed.

End TreeHomomorphism.

(* ===================================================================== *)
(*  Section 2: Layer (b) — forest transducer monoid (flat_map algebra)   *)
(* ===================================================================== *)

(** The full bottom-up tree transduction produces a *set* (list) of output
    trees per input. We re-prove the three flat_map lemmas locally — exactly as
    the word file SftComposition.v does — so the word and tree composition
    monoids rest on the same foundation. *)

Section ForestFlatMap.

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

  (** flat_map composition: the key lemma for associativity. *)
  Lemma flat_map_flat_map :
    forall {X Y Z : Type} (f : X -> list Y) (g : Y -> list Z) (l : list X),
      flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
  Proof.
    intros X Y Z f g l.
    induction l as [| x l' IH]; simpl.
    - reflexivity.
    - rewrite flat_map_app. rewrite IH. reflexivity.
  Qed.

End ForestFlatMap.

Section ForestTransducerMonoid.

  Variable A B C D : Type.

  (** Apply a forest transducer to a single input tree. The transduction is
      itself already the function [f : Tree A -> list (Tree B)]; [ft_apply] is
      the (trivial) application — kept explicit to mirror the word
      [sft_apply]. *)
  Definition ft_apply {X Y : Type} (f : Tree X -> list (Tree Y)) (t : Tree X)
    : list (Tree Y) := f t.

  (** The identity forest transducer: emit the input tree unchanged. *)
  Definition ft_identity {X : Type} (t : Tree X) : list (Tree X) := [t].

  (** Sequential composition: transduce with [f], then transduce each
      intermediate tree with [g] and concatenate. This is exactly
      [compose_transduce] in the Rust:
        t1.transduce(input).iter().flat_map(|mid| t2.transduce(mid)). *)
  Definition ft_compose {X Y Z : Type}
    (f : Tree X -> list (Tree Y)) (g : Tree Y -> list (Tree Z))
    : Tree X -> list (Tree Z) :=
    fun t => flat_map g (f t).

  (** ---- Theorem (b.1): left identity. ----
      Composing the identity transducer on the left with [g] yields [g]. *)
  Theorem ft_compose_left_identity :
    forall (g : Tree A -> list (Tree B)) (t : Tree A),
      ft_apply (ft_compose ft_identity g) t = ft_apply g t.
  Proof.
    intros g t.
    unfold ft_apply, ft_compose, ft_identity.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  (** ---- Theorem (b.2): right identity. ----
      Composing [f] on the left with the identity transducer yields [f]. *)
  Theorem ft_compose_right_identity :
    forall (f : Tree A -> list (Tree B)) (t : Tree A),
      ft_apply (ft_compose f (fun x : Tree B => [x])) t = ft_apply f t.
  Proof.
    intros f t.
    unfold ft_apply, ft_compose.
    rewrite flat_map_singleton.
    reflexivity.
  Qed.

  (** ---- Theorem (b.3): associativity. ----
      [(f ; g) ; h] equals [f ; (g ; h)], by the flat_map composition law. *)
  Theorem ft_compose_assoc :
    forall (f : Tree A -> list (Tree B)) (g : Tree B -> list (Tree C))
           (h : Tree C -> list (Tree D)) (t : Tree A),
      ft_apply (ft_compose (ft_compose f g) h) t =
      ft_apply (ft_compose f (ft_compose g h)) t.
  Proof.
    intros f g h t.
    unfold ft_apply, ft_compose.
    rewrite flat_map_flat_map.
    reflexivity.
  Qed.

(* ===================================================================== *)
(*  Section 3: Corollaries                                                *)
(* ===================================================================== *)

  (** Element-level identity laws (pointwise, not only via [ft_apply]). *)
  Corollary ft_compose_identity_left_pointwise :
    forall (g : Tree A -> list (Tree B)) (t : Tree A),
      ft_compose ft_identity g t = g t.
  Proof.
    intros g t.
    unfold ft_compose, ft_identity. simpl.
    rewrite app_nil_r. reflexivity.
  Qed.

  Corollary ft_compose_identity_right_pointwise :
    forall (f : Tree A -> list (Tree B)) (t : Tree A),
      ft_compose f (fun x : Tree B => [x]) t = f t.
  Proof.
    intros f t.
    unfold ft_compose.
    rewrite flat_map_singleton. reflexivity.
  Qed.

  (** Associativity at the element level. *)
  Corollary ft_compose_assoc_pointwise :
    forall (f : Tree A -> list (Tree B)) (g : Tree B -> list (Tree C))
           (h : Tree C -> list (Tree D)) (t : Tree A),
      ft_compose (ft_compose f g) h t =
      ft_compose f (ft_compose g h) t.
  Proof.
    intros f g h t.
    unfold ft_compose.
    rewrite flat_map_flat_map. reflexivity.
  Qed.

  (** The relabeling homomorphism is a *deterministic* forest transducer:
      the singleton transduction [fun t => [thom g t]] composes with itself by
      fusion. This bridges layer (a) into the layer (b) monoid: deterministic
      relabels are a sub-monoid of the forest transducer monoid, and their
      composition is precisely homomorphism fusion. *)
  Corollary ft_compose_thom_singleton :
    forall (g1 : A -> B) (g2 : B -> C) (t : Tree A),
      ft_compose (fun u => [thom g1 u]) (fun u => [thom g2 u]) t
        = [thom (fun a => g2 (g1 a)) t].
  Proof.
    intros g1 g2 t.
    unfold ft_compose.
    simpl.                          (* flat_map (fun u => [thom g2 u]) [thom g1 t] reduces to [thom g2 (thom g1 t)] *)
    rewrite thom_fusion.
    reflexivity.
  Qed.

End ForestTransducerMonoid.

(* ===================================================================== *)
(*  Assumption audit: every main theorem must be closed.                 *)
(* ===================================================================== *)

(* Layer (a): tree relabeling homomorphism. *)
Print Assumptions thom_id.
Print Assumptions thom_fusion.
Print Assumptions thom_compose_assoc.
Print Assumptions tcount_thom.

(* Layer (b): forest transducer composition monoid. *)
Print Assumptions ft_compose_left_identity.
Print Assumptions ft_compose_right_identity.
Print Assumptions ft_compose_assoc.

(* Bridge corollary: deterministic relabels are a sub-monoid via fusion. *)
Print Assumptions ft_compose_thom_singleton.

(* tree_ind' itself is a plain Fixpoint — confirm it carries no axioms. *)
Print Assumptions tree_ind'.
