(*
 * TheoryCombination: two decidable constraint theories over a SHARED assignment
 * domain combine into an effective Boolean algebra (EBA), via the *joint-search*
 * decision procedure. This is the sound, possibly-exponential fallback in the
 * Nelson–Oppen story: when the shared domain `D` is enumerable (the convex /
 * finite case), combined satisfiability of `T_A ∪ T_B` reduces to a search over
 * the shared assignments. The crux of the actual Nelson–Oppen theorem is doing
 * this combination WITHOUT enumerating an infinite domain — exchanging only
 * equalities over the shared signature under the stably-infinite +
 * disjoint-signature + convexity hypotheses. That refinement is OUT OF SCOPE
 * here; this file formalizes the exact joint-search base case and names the
 * stronger hypotheses it specializes.
 *
 * Construction. The shared domain `D` is an enumerable type with an exhaustive
 * `enum : list D` (`enum_all`). Two component theories are given purely by their
 * atom syntaxes (`PredA`, `PredB`) and their atom evaluators over the shared
 * domain (`evalA`, `evalB`) — these are the legitimate INPUTS to a theory
 * combination procedure, not hidden proof obligations. The combined predicate
 * syntax `CForm` is the Boolean closure of A-atoms and B-atoms (the shared-
 * variable union `T_A ∪ T_B`); `ceval` interprets it pointwise over a shared
 * assignment `d : D`. SAT is decided by `existsb` over `enum`, and WIT
 * materializes the satisfying assignment with `find` over `enum`. Both are
 * COMPLETE and exact because `enum` is exhaustive.
 *
 * Main result: `combined_eba_laws : EBA_Laws combined_eba`.
 *
 * Spec-to-Code Traceability:
 *   Coq                      | Rust (prattail/src/logict.rs)
 *   -------------------------|-----------------------------------------------
 *   PredA/PredB + evalA/evalB| two `ConstraintTheory` impls (their Constraint
 *                            |   syntaxes + decidable membership over a shared
 *                            |   `Assignment` domain)
 *   CForm / ceval            | `QuantifiedFormula` Boolean closure (And/Or/Not
 *                            |   over the two theories' atoms) / its evaluation
 *   D + enum + enum_all      | the enumerable shared assignment domain (joint
 *                            |   search; `TheoryAlgebra::search_bound` is the
 *                            |   bounded operational analogue of `enum`)
 *   csat (existsb enum)      | combined `BooleanAlgebra::is_satisfiable`
 *                            |   (`TheoryAlgebra<T>` over the union theory)
 *   cwit (find  enum)        | combined `BooleanAlgebra::witness`
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From SymbolicAlgebra Require Import EffectiveBooleanAlgebra.

(* ===================================================================== *)
(*  Generic helper                                                       *)
(* ===================================================================== *)

(* existsb witnesses a satisfying [find]: the standard bridge from a positive
   [existsb] to the concrete element [find] returns. Copied from the closure
   family's [CollectionAlgebraClosure.existsb_find_some]; reused by [cwit_total]. *)
Lemma existsb_find_some {X} (f : X -> bool) (l : list X) :
  existsb f l = true -> exists x, find f l = Some x /\ f x = true.
Proof.
  induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E.
  - intros _. exists a. split; [reflexivity | exact E].
  - simpl. exact IH.
Qed.

(* ===================================================================== *)
(*  The combined EBA over a shared enumerable assignment domain           *)
(* ===================================================================== *)

Section TheoryCombination.
  (* The shared assignment domain (e.g. the valuations of the shared variables),
     together with an exhaustive enumeration — the joint-search fallback. *)
  Variable D : Type.
  Variable enum : list D.
  Variable enum_all : forall d : D, In d enum.

  (* The two component theories, given by their atom syntaxes and their decidable
     atom evaluators over the shared domain. These are the procedure's inputs. *)
  Variable PredA PredB : Type.
  Variable evalA : PredA -> D -> bool.
  Variable evalB : PredB -> D -> bool.

  (* Boolean formulas mixing A-atoms and B-atoms: the shared-variable union
     T_A ∪ T_B. *)
  Inductive CForm : Type :=
  | CTrue  : CForm
  | CFalse : CForm
  | CAtomA : PredA -> CForm
  | CAtomB : PredB -> CForm
  | CAnd   : CForm -> CForm -> CForm
  | COr    : CForm -> CForm -> CForm
  | CNot   : CForm -> CForm.

  (* Evaluate a combined formula at a shared assignment. *)
  Fixpoint ceval (f : CForm) (d : D) : bool :=
    match f with
    | CTrue     => true
    | CFalse    => false
    | CAtomA a  => evalA a d
    | CAtomB b  => evalB b d
    | CAnd x y  => ceval x d && ceval y d
    | COr  x y  => ceval x d || ceval y d
    | CNot x    => negb (ceval x d)
    end.

  (* SAT: search the (exhaustive) shared enumeration. *)
  Definition csat (f : CForm) : bool :=
    existsb (fun d => ceval f d) enum.

  (* WIT: materialize the satisfying shared assignment. *)
  Definition cwit (f : CForm) : option D :=
    find (fun d => ceval f d) enum.

  Definition combined_eba : EBA := {|
    Dom  := D;
    Pred := CForm;
    top  := CTrue;
    bot  := CFalse;
    conj := CAnd;
    disj := COr;
    neg  := CNot;
    eval := ceval;
    sat  := csat;
    wit  := cwit;
  |}.

  (* --------------------------------------------------------------------- *)
  (*  SAT / WIT soundness and completeness                                 *)
  (* --------------------------------------------------------------------- *)

  Lemma csat_sound : forall f, csat f = true -> exists d, ceval f d = true.
  Proof.
    intros f Hsat. unfold csat in Hsat. apply existsb_exists in Hsat.
    destruct Hsat as [d [_ Hd]]. exists d. exact Hd.
  Qed.

  Lemma csat_complete : forall f d, ceval f d = true -> csat f = true.
  Proof.
    intros f d Hev. unfold csat. apply existsb_exists.
    exists d. split; [apply enum_all | exact Hev].
  Qed.

  Lemma cwit_sound : forall f d, cwit f = Some d -> ceval f d = true.
  Proof.
    intros f d Hwit. unfold cwit in Hwit.
    apply find_some in Hwit. destruct Hwit as [_ Hd]. exact Hd.
  Qed.

  Lemma cwit_total : forall f, csat f = true -> exists d, cwit f = Some d.
  Proof.
    intros f Hsat. unfold csat in Hsat. apply existsb_find_some in Hsat.
    destruct Hsat as [d [Hfind _]]. exists d. unfold cwit. exact Hfind.
  Qed.

  (* --------------------------------------------------------------------- *)
  (*  Combination: the union theory is an EBA                              *)
  (* --------------------------------------------------------------------- *)

  Theorem combined_eba_laws : EBA_Laws combined_eba.
  Proof.
    constructor.
    - intros d; reflexivity.
    - intros d; reflexivity.
    - intros p q d; reflexivity.
    - intros p q d; reflexivity.
    - intros p d; reflexivity.
    - intros p. apply csat_sound.
    - intros p d. apply csat_complete.
    - intros p d. apply cwit_sound.
    - intros p. apply cwit_total.
  Qed.

End TheoryCombination.

Print Assumptions combined_eba_laws.
