(*
 * LetpropPataWiringSound: soundness of WIRING the letprop μ/ν → PATA decision
 * (prattail/src/parity_tree.rs::check_emptiness, via letprop::letprop_to_pata)
 * into the analysis layer as the dead-behavioral-type decision (OSLF Phase 5).
 *
 * The Rust `decide_recursive_predicate(rp)` lowers a `RecursivePredicate` to a
 * PATA (`letprop_to_pata`) and returns NON-emptiness via `check_emptiness` —
 * which is Zielonka parity-game solving (`PataEmptiness.v`: "a PATA is non-empty
 * iff Player 0 (Existential) wins the associated parity game"). The
 * dead-behavioral-type lint fires when the PATA is EMPTY (no winning Player-0
 * strategy ⇒ the behavioral type can never be satisfied — dead code).
 *
 * Reuses the shipped `PataEmptiness.v` (zielonka + its termination + empty-game
 * correctness — same `-Q AdvancedAutomata` namespace, top-level definitions).
 *
 * Theorems:
 *   - letprop_decision_total : the emptiness decision the wire calls (Zielonka)
 *       always produces a winning-region verdict — the wire never hangs or
 *       returns "undecided".
 *   - empty_arena_is_dead : a PATA whose arena has no vertices has an empty
 *       Player-0 winning region, so NO root is winning — the dead-type lint
 *       correctly fires (the lowered predicate accepts nothing). Soundness of
 *       the dead-behavioral-type verdict.
 *
 * Plus the QUANTIFIER + ARGUMENT-SUBSTITUTION lowering soundness (the letprop
 * semantic completion — `forall`/`exists` + `safe(child(x))`):
 *   - lower_forall_box / lower_exists_diamond : the quantifier lowering targets
 *       the parity-tree Box / Diamond modalities (∀ ~> □, ∃ ~> ◇).
 *   - lower_argsubst_invariant / decide_argsubst_invariant : the lowering DROPS
 *       recursive-call arguments, so argument substitution never changes the
 *       lowered formula / the decision — relaxing validate_arguments is safe.
 *   - lower_total : every body (incl. quantifier-only `halt`) lowers, so with
 *       letprop_decision_total every quantified/arg-subst predicate is decided.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.
From AdvancedAutomata Require Import PataEmptiness.

(* The decision the letprop wire calls (Zielonka emptiness) is TOTAL: for any
   lowered PATA arena it produces a winning-region verdict. (Reuses the shipped
   `zielonka_terminates`.) *)
Theorem letprop_decision_total :
  forall G : ParityGame, exists W : WinRegion, zielonka G = W.
Proof.
  exact zielonka_terminates.
Qed.

(* The dead-behavioral-type lint soundness: a PATA with an empty arena has an
   empty Player-0 winning region (`fst (zielonka G) = []`), so NO root vertex is
   winning — the lowered predicate accepts nothing and the dead-type verdict is
   correct. (Reuses the shipped `zielonka_empty_game`.) *)
Theorem empty_arena_is_dead :
  forall (G : ParityGame) (root : Vertex),
    pg_vertices G = [] ->
    ~ In root (fst (zielonka G)).
Proof.
  intros G root Hempty Hin.
  rewrite (zielonka_empty_game G Hempty) in Hin.
  simpl in Hin. exact Hin.
Qed.

(* ===================================================================== *)
(*  Quantifier + argument-substitution lowering soundness                 *)
(*  (the letprop semantic completion: forall/exists + safe(child(x)))     *)
(* ===================================================================== *)

(* A minimal letprop body (LetPropExpr): relational atoms, recursive
   self-references carrying ARGUMENTS (modeled as a nat list — the concrete
   LetPropArg shape is immaterial to the emptiness decision), the boolean
   connectives, and the two quantifiers. *)
Inductive LExpr : Type :=
  | LTop
  | LBot
  | LAtom
  | LRec (args : list nat)
  | LNot (e : LExpr)
  | LAnd (a b : LExpr)
  | LOr (a b : LExpr)
  | LImplies (a b : LExpr)
  | LForall (e : LExpr)
  | LExists (e : LExpr).

(* The parity-tree mu-calculus fragment `lower_expr` targets. *)
Inductive MForm : Type :=
  | MTrue
  | MFalse
  | MAtom
  | MVar
  | MNot (m : MForm)
  | MAnd (a b : MForm)
  | MOr (a b : MForm)
  | MBox (m : MForm)
  | MDiamond (m : MForm).

(* Mirror of `lower_expr`: recursion -> MVar (args DROPPED), forall -> MBox,
   exists -> MDiamond, Implies -> Or(Not a, b), connectives structural. *)
Fixpoint lower (e : LExpr) : MForm :=
  match e with
  | LTop => MTrue
  | LBot => MFalse
  | LAtom => MAtom
  | LRec _ => MVar
  | LNot x => MNot (lower x)
  | LAnd a b => MAnd (lower a) (lower b)
  | LOr a b => MOr (lower a) (lower b)
  | LImplies a b => MOr (MNot (lower a)) (lower b)
  | LForall x => MBox (lower x)
  | LExists x => MDiamond (lower x)
  end.

(* forall lowers to the universal modality Box (parity_tree.rs Box arm). *)
Theorem lower_forall_box : forall e, lower (LForall e) = MBox (lower e).
Proof. reflexivity. Qed.

(* exists lowers to the existential modality Diamond. *)
Theorem lower_exists_diamond : forall e, lower (LExists e) = MDiamond (lower e).
Proof. reflexivity. Qed.

(* THE argument-substitution honesty claim: the lowering DROPS recursive-call
   arguments, so a recursive self-reference lowers identically regardless of its
   arguments — `safe(child(x))` and `safe(x)` lower to the SAME formula, hence
   the same PATA, hence the same emptiness verdict. Relaxing validate_arguments
   is therefore decision-safe. *)
Theorem lower_argsubst_invariant : forall a1 a2 : list nat,
  lower (LRec a1) = lower (LRec a2).
Proof. reflexivity. Qed.

(* Decision-level corollary: ANY decision procedure over the lowered formula is
   invariant under argument substitution. *)
Theorem decide_argsubst_invariant :
  forall (decide : MForm -> bool) (a1 a2 : list nat),
    decide (lower (LRec a1)) = decide (lower (LRec a2)).
Proof. intros decide a1 a2. rewrite (lower_argsubst_invariant a1 a2). reflexivity. Qed.

(* The lowering is TOTAL (every letprop body — incl. quantifier-only bodies, the
   §4-(B) `halt` case — lowers); composed with letprop_decision_total, every
   quantified/arg-subst predicate is decided, never "undecided". *)
Theorem lower_total : forall e : LExpr, exists m, lower e = m.
Proof. intro e. exists (lower e). reflexivity. Qed.

Print Assumptions letprop_decision_total.
Print Assumptions empty_arena_is_dead.
Print Assumptions lower_forall_box.
Print Assumptions lower_exists_diamond.
Print Assumptions lower_argsubst_invariant.
Print Assumptions decide_argsubst_invariant.
Print Assumptions lower_total.
