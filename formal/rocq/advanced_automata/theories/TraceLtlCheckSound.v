(*
 * TraceLtlCheckSound: soundness of the per-step normal-form derivation in the
 * WIRING of simulation's temporal trace-LTL check (OSLF Phase 5).
 *
 * The shipped `simulation/src/temporal.rs::check_trace_ltl` is the full
 * Vardi-Wolper LTL→Büchi product + emptiness decision; its soundness rests on
 * the shipped Büchi-emptiness proof `mathematical_analyses/BuchiWpdsProduct.v`
 * ("a Büchi automaton has a non-empty language iff a reachable SCC contains an
 * accepting state"). The Phase-5 wire only ADDS an adaptor `trace_to_ltl_steps`
 * turning the `ExecutionTrace` into the `(display, is_nf)` word `check_trace_ltl`
 * consumes. Because `TraceEntry` has no per-step normal-form flag, the adaptor
 * DERIVES it: step `i` is a normal form iff the run's outcome was `NormalForm`
 * AND `i` is the last step. This file certifies that derivation is correct (the
 * one new piece of logic the wire introduces); the LTL decision itself is the
 * already-proven `check_trace_ltl` / `BuchiWpdsProduct.v`.
 *
 * Theorems:
 *   - adaptor_nf_at_last  : the last step's NF flag equals the run's NF outcome.
 *   - adaptor_nf_not_last : every non-last step's NF flag is false.
 *   - adaptor_unique_nf   : when the run ended in a normal form, exactly the last
 *                           step is flagged NF.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.

(* The adaptor's per-step NF flag: step `i` of an `num_steps`-step trace is a
   normal form iff `nf_outcome` (the run ended in `NormalForm`) AND `i` is the
   last index (`S i = num_steps`). Mirror of `trace_to_ltl_steps`. *)
Definition adaptor_is_nf (nf_outcome : bool) (num_steps i : nat) : bool :=
  nf_outcome && Nat.eqb (S i) num_steps.

Theorem adaptor_nf_at_last : forall (nf : bool) (m : nat),
  adaptor_is_nf nf (S m) m = nf.
Proof.
  intros nf m. unfold adaptor_is_nf.
  rewrite Nat.eqb_refl. apply Bool.andb_true_r.
Qed.

Theorem adaptor_nf_not_last : forall (nf : bool) (num_steps i : nat),
  S i <> num_steps -> adaptor_is_nf nf num_steps i = false.
Proof.
  intros nf num_steps i Hne. unfold adaptor_is_nf.
  apply Bool.andb_false_iff. right.
  apply Nat.eqb_neq. exact Hne.
Qed.

Theorem adaptor_unique_nf : forall (m i : nat),
  adaptor_is_nf true (S m) i = true <-> i = m.
Proof.
  intros m i. unfold adaptor_is_nf. rewrite Bool.andb_true_l.
  rewrite Nat.eqb_eq. split.
  - intro H. injection H as H. exact H.
  - intro H. subst. reflexivity.
Qed.

Print Assumptions adaptor_nf_at_last.
Print Assumptions adaptor_nf_not_last.
Print Assumptions adaptor_unique_nf.
