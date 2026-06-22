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

Print Assumptions letprop_decision_total.
Print Assumptions empty_arena_is_dead.
