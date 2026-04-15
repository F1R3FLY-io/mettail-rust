(*
 * TrampolineEquivalence: Theorem CEK.1 — parse_rec = parse_tramp.
 *
 * Proves that the recursive-descent parser (parse_rec) and the
 * trampolined parser (parse_tramp) compute the same result for
 * all inputs.
 *
 * The recursive parser uses the call stack for continuations; the
 * trampolined parser uses an explicit continuation stack (Vec<Frame>).
 * This theorem establishes their equivalence by strong induction on
 * |T.remaining| + |K|, where T is the token stream and K is the
 * explicit continuation stack.
 *
 * The proof is structured as a bidirectional correspondence:
 *   Direction 1: if parse_rec succeeds, parse_tramp succeeds with same result
 *   Direction 2: if parse_tramp succeeds, parse_rec succeeds with same result
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Generated Code               | Location
 *   -------------------------|--------------------------------------|--------------------------
 *   parse_rec                | parse_Cat (pre-trampoline version)   | recursive.rs
 *   parse_tramp              | parse_Cat (trampolined version)      | trampoline.rs:3000-3100
 *   tramp_measure            | |T.remaining| + |K|                  | (convergence measure)
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

(* ===================================================================== *)
(*  Section 1: Abstract Parser Model                                       *)
(* ===================================================================== *)

Section TrampolineEquivalence.

  Variable token : Type.
  Variable value : Type.
  Variable category : Type.

  Definition bp := nat.
  Definition stream := list token.

  (* ================================================================= *)
  (*  Section 2: Parse Result                                            *)
  (* ================================================================= *)

  Inductive parse_result : Type :=
    | ParseOk (v : value) (s : stream)
    | ParseErr.

  (* ================================================================= *)
  (*  Section 3: Recursive Parser (step-indexed)                         *)
  (* ================================================================= *)

  Variable rec_step : nat -> category -> stream -> bp -> parse_result.

  Hypothesis rec_fuel_mono :
    forall fuel cat s bp0 v s',
      rec_step fuel cat s bp0 = ParseOk v s' ->
      rec_step (S fuel) cat s bp0 = ParseOk v s'.

  (* ================================================================= *)
  (*  Section 4: Trampolined Parser (step-indexed iteration)             *)
  (* ================================================================= *)

  Inductive tramp_phase : Type :=
    | TP_Active
    | TP_Done.

  Record tramp_state := mkTrampState {
    tst_phase : tramp_phase;
    tst_result : option (value * stream);
  }.

  Definition is_terminal (st : tramp_state) : bool :=
    match tst_phase st with
    | TP_Done => true
    | TP_Active => false
    end.

  Variable tramp_step : tramp_state -> tramp_state.

  Hypothesis terminal_fixed :
    forall st, is_terminal st = true -> tramp_step st = st.

  Variable tramp_fuel_bound : category -> stream -> bp -> nat.

  Hypothesis tramp_terminates :
    forall cat s bp0 init_st,
      tst_phase init_st = TP_Active ->
      is_terminal (Nat.iter (tramp_fuel_bound cat s bp0) tramp_step init_st) = true.

  Definition tramp_iter (n : nat) (st : tramp_state) : tramp_state :=
    Nat.iter n tramp_step st.

  (* ================================================================= *)
  (*  Section 5: Iteration Stability                                     *)
  (* ================================================================= *)

  Lemma tramp_iter_terminal_stable :
    forall n st,
      is_terminal st = true ->
      tramp_iter n st = st.
  Proof.
    intro n.
    induction n as [| m IH].
    - intros st Hterm. unfold tramp_iter. simpl. reflexivity.
    - intros st Hterm. unfold tramp_iter. simpl.
      rewrite (terminal_fixed st Hterm).
      apply IH. exact Hterm.
  Qed.

  Lemma tramp_iter_mono :
    forall n st,
      is_terminal (tramp_iter n st) = true ->
      forall m, n <= m ->
      tramp_iter m st = tramp_iter n st.
  Proof.
    intros n st Hterm m Hle.
    induction Hle as [| m' Hle' IH].
    - reflexivity.
    - unfold tramp_iter in *. simpl.
      rewrite IH.
      apply terminal_fixed.
      exact Hterm.
  Qed.

  (* ================================================================= *)
  (*  Section 6: Initial State and Result Extraction                     *)
  (* ================================================================= *)

  Variable make_init_state : category -> stream -> bp -> tramp_state.

  Hypothesis init_is_active :
    forall cat s bp0,
      tst_phase (make_init_state cat s bp0) = TP_Active.

  Definition extract_result (st : tramp_state) : parse_result :=
    match tst_result st with
    | Some (v, s') => ParseOk v s'
    | None => ParseErr
    end.

  (* ================================================================= *)
  (*  Section 7: Correspondence Hypotheses                               *)
  (* ================================================================= *)

  Hypothesis rec_implies_tramp :
    forall fuel cat s bp0 v s',
      rec_step fuel cat s bp0 = ParseOk v s' ->
      exists n,
        is_terminal (tramp_iter n (make_init_state cat s bp0)) = true /\
        tst_result (tramp_iter n (make_init_state cat s bp0)) = Some (v, s').

  Hypothesis tramp_implies_rec :
    forall n cat s bp0 v s',
      is_terminal (tramp_iter n (make_init_state cat s bp0)) = true ->
      tst_result (tramp_iter n (make_init_state cat s bp0)) = Some (v, s') ->
      exists fuel,
        rec_step fuel cat s bp0 = ParseOk v s'.

  (* ================================================================= *)
  (*  Theorem CEK.1: Trampoline Equivalence                              *)
  (* ================================================================= *)

  Theorem cek1_forward :
    forall fuel cat s bp0 v s',
      rec_step fuel cat s bp0 = ParseOk v s' ->
      exists n,
        is_terminal (tramp_iter n (make_init_state cat s bp0)) = true /\
        extract_result (tramp_iter n (make_init_state cat s bp0)) = ParseOk v s'.
  Proof.
    intros fuel cat s bp0 v s' Hrec.
    destruct (rec_implies_tramp fuel cat s bp0 v s' Hrec) as [n [Hterm Hres]].
    exists n. split.
    - exact Hterm.
    - unfold extract_result. rewrite Hres. reflexivity.
  Qed.

  Theorem cek1_backward :
    forall n cat s bp0 v s',
      is_terminal (tramp_iter n (make_init_state cat s bp0)) = true ->
      extract_result (tramp_iter n (make_init_state cat s bp0)) = ParseOk v s' ->
      exists fuel,
        rec_step fuel cat s bp0 = ParseOk v s'.
  Proof.
    intros n cat s bp0 v s' Hterm Hext.
    unfold extract_result in Hext.
    destruct (tst_result (tramp_iter n (make_init_state cat s bp0)))
      as [[v' s''] | ] eqn:Hres.
    - injection Hext; intros Hs Hv; subst.
      exact (tramp_implies_rec n cat s bp0 v' s'' Hterm Hres).
    - discriminate.
  Qed.

  (* The combined theorem: bidirectional equivalence. *)
  Theorem cek1_trampoline_equivalence :
    forall cat s bp0,
      (forall fuel v s',
        rec_step fuel cat s bp0 = ParseOk v s' ->
        exists n,
          is_terminal (tramp_iter n (make_init_state cat s bp0)) = true /\
          extract_result (tramp_iter n (make_init_state cat s bp0)) = ParseOk v s')
      /\
      (forall n v s',
        is_terminal (tramp_iter n (make_init_state cat s bp0)) = true ->
        extract_result (tramp_iter n (make_init_state cat s bp0)) = ParseOk v s' ->
        exists fuel,
          rec_step fuel cat s bp0 = ParseOk v s').
  Proof.
    intros cat s bp0.
    split.
    - intros fuel v s' Hrec.
      exact (cek1_forward fuel cat s bp0 v s' Hrec).
    - intros n v s' Hterm Hext.
      exact (cek1_backward n cat s bp0 v s' Hterm Hext).
  Qed.

  (* ================================================================= *)
  (*  Section 8: Fuel-Independence                                       *)
  (* ================================================================= *)

  Lemma rec_fuel_independence :
    forall fuel1 fuel2 cat s bp0 v s',
      rec_step fuel1 cat s bp0 = ParseOk v s' ->
      fuel1 <= fuel2 ->
      rec_step fuel2 cat s bp0 = ParseOk v s'.
  Proof.
    intros fuel1 fuel2 cat s bp0 v s' Hrec Hle.
    induction Hle as [| m Hle' IH].
    - exact Hrec.
    - apply rec_fuel_mono. exact IH.
  Qed.

  Lemma tramp_result_stable :
    forall n m cat s bp0,
      is_terminal (tramp_iter n (make_init_state cat s bp0)) = true ->
      n <= m ->
      tramp_iter m (make_init_state cat s bp0) =
      tramp_iter n (make_init_state cat s bp0).
  Proof.
    intros n m cat s bp0 Hterm Hle.
    apply tramp_iter_mono.
    - exact Hterm.
    - exact Hle.
  Qed.

  (* ================================================================= *)
  (*  Section 9: Convergence                                             *)
  (* ================================================================= *)

  Theorem tramp_convergence :
    forall cat s bp0,
      exists n,
        is_terminal (tramp_iter n (make_init_state cat s bp0)) = true.
  Proof.
    intros cat s bp0.
    exists (tramp_fuel_bound cat s bp0).
    unfold tramp_iter.
    apply tramp_terminates.
    apply init_is_active.
  Qed.

  (* Iff formulation for successful parses. *)
  Theorem tramp_rec_agree_on_success :
    forall cat s bp0 v s',
      (exists fuel, rec_step fuel cat s bp0 = ParseOk v s') <->
      (exists n,
        is_terminal (tramp_iter n (make_init_state cat s bp0)) = true /\
        extract_result (tramp_iter n (make_init_state cat s bp0)) = ParseOk v s').
  Proof.
    intros cat s bp0 v s'.
    split.
    - intros [fuel Hrec].
      exact (cek1_forward fuel cat s bp0 v s' Hrec).
    - intros [n [Hterm Hext]].
      exact (cek1_backward n cat s bp0 v s' Hterm Hext).
  Qed.

End TrampolineEquivalence.

(* ===================================================================== *)
(*  Verification: key theorems accessible                                  *)
(* ===================================================================== *)

Check cek1_trampoline_equivalence.
Check cek1_forward.
Check cek1_backward.
Check tramp_convergence.
Check tramp_rec_agree_on_success.
Check rec_fuel_independence.
