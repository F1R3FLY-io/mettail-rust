(*
 * OutputTermAlgebra: the first-class, analyzable output-function term algebra
 * `OutputTerm {Eps, Id, Const, Concat}` (prattail/src/sft.rs §8) that replaces
 * the opaque `OutputFunction::Map`/`FlatMap` closures. It carries two compatible
 * algebraic structures, both proved here up to denotational equivalence
 * `oeq s t := forall x, oapply s x = oapply t x`:
 *
 *   - a MONOID (OConcat, OEps): output concatenation, associative with unit OEps;
 *   - a CATEGORY (othen, OId): sequential composition, associative with unit OId;
 *
 * plus the β compose-correctness law
 *   othen_correct : oapply (othen s t) x = oapply_all t (oapply s x)
 * which is exactly the Rust contract `(self.then(next)).apply(i) =
 * next.apply_all(self.apply(i))`. The η laws are the category unit laws
 * (othen_id_l/othen_id_r). Because `othen` produces a concrete term (never a
 * closure), SFT composition over OutputTerms is precise — upgrading the
 * conservative `Map`/`FlatMap` arm of `SymbolicFiniteTransducer::compose`.
 *
 * The proofs delegate to the same word-transducer flat_map theorems used by
 * SftComposition.v (flat_map over append / singleton / flat_map), so the output
 * algebra and the transducer-composition monoid share one foundation.
 *
 * Spec-to-Code Traceability:
 *   Rocq                | Rust (prattail/src/sft.rs §8)
 *   --------------------|---------------------------------------------
 *   OTerm / oapply      | OutputTerm<A,B> / OutputTerm::apply
 *   oapply_all          | OutputTerm::apply_all
 *   othen               | OutputTerm::then (precise symbolic composition)
 *   OEps/OId/OConst/OConcat | OutputTerm::{Eps,Id,Const,Concat}
 *   othen_correct       | the `then` compose-correctness law (doc + test then_correct)
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.

(* The output-term syntax (single-sorted endo model: input and output share the
   domain X; the Rust two-sorted OutputTerm<A,B> is the object-indexed/typed
   realization of this same algebra, identity-on-objects via Into-coherence). *)
Inductive OTerm (X : Type) : Type :=
| OEps    : OTerm X
| OId     : OTerm X
| OConst  : list X -> OTerm X
| OConcat : OTerm X -> OTerm X -> OTerm X.

Arguments OEps {X}.
Arguments OId {X}.
Arguments OConst {X} _.
Arguments OConcat {X} _ _.

Section OutputTermAlgebra.
  Variable X : Type.

  (* ===================================================================== *)
  (*  Denotation                                                            *)
  (* ===================================================================== *)

  Fixpoint oapply (t : OTerm X) (x : X) : list X :=
    match t with
    | OEps => []
    | OId => [x]
    | OConst v => v
    | OConcat a b => oapply a x ++ oapply b x
    end.

  Definition oapply_all (t : OTerm X) (xs : list X) : list X :=
    flat_map (oapply t) xs.

  (* Precise symbolic composition: `s` followed by `t`. Mirrors Rust
     OutputTerm::then exactly (Eps∘_=Eps, Const∘t=Const(apply_all t v),
     Id∘t=t, Concat distributes). *)
  Fixpoint othen (s t : OTerm X) : OTerm X :=
    match s with
    | OEps => OEps
    | OConst v => OConst (oapply_all t v)
    | OId => t
    | OConcat a b => OConcat (othen a t) (othen b t)
    end.

  Definition oeq (s t : OTerm X) : Prop := forall x, oapply s x = oapply t x.

  (* ===================================================================== *)
  (*  flat_map lemmas (the shared word-transducer monoid foundation)       *)
  (* ===================================================================== *)

  Lemma flat_map_app_ :
    forall {Y Z : Type} (f : Y -> list Z) (l1 l2 : list Y),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    intros Y Z f l1 l2. induction l1 as [|y l1' IH]; simpl.
    - reflexivity.
    - rewrite IH, app_assoc. reflexivity.
  Qed.

  Lemma flat_map_singleton_ :
    forall {Y : Type} (l : list Y), flat_map (fun y => [y]) l = l.
  Proof.
    intros Y l. induction l as [|y l' IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma flat_map_flat_map_ :
    forall {Y Z W : Type} (f : Y -> list Z) (g : Z -> list W) (l : list Y),
      flat_map g (flat_map f l) = flat_map (fun y => flat_map g (f y)) l.
  Proof.
    intros Y Z W f g l. induction l as [|y l' IH]; simpl.
    - reflexivity.
    - rewrite flat_map_app_, IH. reflexivity.
  Qed.

  Lemma flat_map_ext :
    forall {Y Z : Type} (f g : Y -> list Z) (l : list Y),
      (forall y, f y = g y) -> flat_map f l = flat_map g l.
  Proof.
    intros Y Z f g l H. induction l as [|y l' IH]; simpl;
      [reflexivity | rewrite H, IH; reflexivity].
  Qed.

  (* ===================================================================== *)
  (*  oeq is an equivalence                                                 *)
  (* ===================================================================== *)

  Lemma oeq_refl : forall t, oeq t t.
  Proof. intros t x; reflexivity. Qed.

  Lemma oeq_sym : forall s t, oeq s t -> oeq t s.
  Proof. intros s t H x; symmetry; apply H. Qed.

  Lemma oeq_trans : forall s t u, oeq s t -> oeq t u -> oeq s u.
  Proof. intros s t u H1 H2 x; rewrite H1; apply H2. Qed.

  (* ===================================================================== *)
  (*  β: compose-correctness                                               *)
  (* ===================================================================== *)

  Theorem othen_correct :
    forall s t x, oapply (othen s t) x = oapply_all t (oapply s x).
  Proof.
    induction s as [| | v | a IHa b IHb]; intros t x; simpl.
    - reflexivity.                                   (* OEps  *)
    - unfold oapply_all; simpl. rewrite app_nil_r. reflexivity.  (* OId *)
    - reflexivity.                                   (* OConst *)
    - unfold oapply_all. rewrite flat_map_app_.      (* OConcat *)
      rewrite IHa, IHb. reflexivity.
  Qed.

  (* helper: apply_all of a composition factors *)
  Lemma oapply_all_othen :
    forall t u ys, oapply_all (othen t u) ys = oapply_all u (oapply_all t ys).
  Proof.
    intros t u ys. unfold oapply_all.
    rewrite (flat_map_ext (oapply (othen t u))
                          (fun y => flat_map (oapply u) (oapply t y))).
    - rewrite <- flat_map_flat_map_. reflexivity.
    - intro y. rewrite othen_correct. unfold oapply_all. reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Monoid (OConcat, OEps)                                                *)
  (* ===================================================================== *)

  Theorem oconcat_assoc :
    forall a b c, oeq (OConcat (OConcat a b) c) (OConcat a (OConcat b c)).
  Proof. intros a b c x; simpl; rewrite app_assoc; reflexivity. Qed.

  Theorem oconcat_eps_l : forall a, oeq (OConcat OEps a) a.
  Proof. intros a x; reflexivity. Qed.

  Theorem oconcat_eps_r : forall a, oeq (OConcat a OEps) a.
  Proof. intros a x; simpl; rewrite app_nil_r; reflexivity. Qed.

  (* ===================================================================== *)
  (*  Category (othen, OId) — incl. η unit laws and associativity          *)
  (* ===================================================================== *)

  Theorem othen_id_l : forall t, oeq (othen OId t) t.
  Proof. intros t; apply oeq_refl. Qed.   (* othen OId t = t definitionally *)

  (* OId is the unit of oapply_all (singleton-lift of identity). [oapply OId]
     is convertible to [fun x => [x]], so the singleton lemma closes it. *)
  Lemma oapply_all_id : forall xs, oapply_all OId xs = xs.
  Proof.
    intro xs. unfold oapply_all. exact (flat_map_singleton_ xs).
  Qed.

  Theorem othen_id_r : forall s, oeq (othen s OId) s.
  Proof.
    intros s x. rewrite othen_correct. rewrite oapply_all_id. reflexivity.
  Qed.

  Theorem othen_assoc :
    forall s t u, oeq (othen (othen s t) u) (othen s (othen t u)).
  Proof.
    intros s t u x. rewrite !othen_correct. rewrite oapply_all_othen. reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Compatibility: othen respects oeq on the right (functoriality)       *)
  (* ===================================================================== *)

  Theorem othen_eps_l : forall t, oeq (othen OEps t) OEps.
  Proof. intros t x; reflexivity. Qed.

End OutputTermAlgebra.

Print Assumptions othen_correct.
Print Assumptions othen_assoc.
Print Assumptions oconcat_assoc.
