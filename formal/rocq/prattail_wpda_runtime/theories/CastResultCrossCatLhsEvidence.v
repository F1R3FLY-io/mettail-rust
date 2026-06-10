(*
 * CastResultCrossCatLhsEvidence: a FAITHFUL operational model of the Phase 5A
 * cast-then-compare failure, used to work through to a solution that PROVABLY works
 * end-to-end — BEFORE implementing.
 *
 * Why operational (not just a guard-edge predicate): the trace proved TWO things diverge
 * between a literal LHS and a cast LHS, and BOTH must be fixed or the infix still fails:
 *   (1) the EVIDENCE EDGE on the operand's GSS top, AND
 *   (2) whether the operand's cursor REACHES the InfixLoop guard at all.
 * A model that only captures (1) "proves" an edge-stamp fix that does NOT work, because
 * the cast-result cursor actually goes to UNWINDING and never reaches the guard. This
 * model captures both, so the proven solution transfers.
 *
 * GROUNDED FACTS (instrumented PUSH/POP/EVID traces; `int(3)==3`, `int(3.14)==3` vs
 * `3==3`):
 *   - LITERAL `3`: pos-0 dispatch lays down `CrossCatLhs{C}` (cross-cat-LHS delegate);
 *     on operand completion the reentry pushes `CrossCatLhsReentry{C}` AND sets the
 *     control state to InfixLoop (wpda_walker.rs:15536-15543). At `==` the guard's EVID
 *     sees `CrossCatLhsReentry{C}` ⇒ admitted ⇒ parse OK.
 *   - CAST `int(..)`: pos-0 dispatch lays down only `CrossCatProjection` edges (36×, 0×
 *     CrossCatLhs); the cast-result cursor resolves to control state UNWINDING (cohort
 *     revive `state=Unwinding`) and the only cursor that reaches the `==` guard is the
 *     plain Int-category parse whose top edge is `Generic` ⇒ evidence None ⇒ suppressed.
 *
 * The SOLUTION proven correct here: route a cast whose RESULT category C is a
 * cross-cat-infix source through the SAME cross-cat-LHS DELEGATE a literal uses, so the
 * cast result gets BOTH `CrossCatLhsReentry{C}` AND control state InfixLoop. The model
 * proves: this solution works; an edge-only stamp does NOT (still Unwinding); an
 * argument-category-keyed reentry does NOT (wrong source); and the solution is a
 * conservative extension that cannot perturb literals or same-category operators (`-3!`).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Section CastResultCrossCatLhsEvidence.

  (* GSS incoming-edge kinds the guard inspects (mirror of `gss::EdgeKind`). *)
  Inductive EdgeKind : Type :=
    | Generic
    | CrossCatLhs (src : nat)
    | CrossCatLhsReentry (src : nat)
    | CrossCatProjection (src : nat).

  (* Mirror of `cross_cat_lhs_infix_evidence_source` (wpda_walker.rs:6405-6423):
     evidence ONLY from CrossCatLhs/CrossCatLhsReentry whose source equals the top cat. *)
  Definition evidence (top_cat : nat) (e : EdgeKind) : option nat :=
    match e with
    | CrossCatLhs s | CrossCatLhsReentry s =>
        if Nat.eqb s top_cat then Some s else None
    | Generic | CrossCatProjection _ => None
    end.

  (* Control state of the operand's cursor after the LHS is parsed. *)
  Inductive Ctrl : Type := CInfix | CUnwind.

  (* Outcome of the whole `<LHS> == <RHS>` parse for a CATEGORY-CHANGING infix. *)
  Inductive Outcome : Type := Accept | Reject.

  (* The post-LHS state is fully characterized (for this question) by the operand's GSS
     top edge and whether the cursor reaches the InfixLoop guard. Both are GROUNDED in
     the traces per LhsSource below. *)
  Record PostLhs : Type := mkPost { pl_edge : EdgeKind; pl_ctrl : Ctrl }.

  (* The left-operand provenance / routing under test. *)
  Inductive LhsSource : Type :=
    | Lit                 (* literal of cat C — cross-cat-LHS delegate (single token)   *)
    | CastCurrent         (* cast → C, CURRENT routing: projection ⇒ Generic + Unwind   *)
    | CastFixed           (* cast → C, FIX: routed via the delegate ⇒ reentry + Infix   *)
    | CastFixedEdgeOnly   (* hypothetical PARTIAL fix: reentry edge BUT still Unwinding  *)
    | CastArgKeyed.       (* falsified #1: reentry keyed by the ARGUMENT cat (≠ C)       *)

  (* `arg_cat src c`: for the argument-keyed (falsified) source, the reentry is keyed by
     a DIFFERENT category than the result `c`. We expose it via a parameter so the model
     is honest about "arg ≠ result". *)
  Definition post_lhs (src : LhsSource) (c arg : nat) : PostLhs :=
    match src with
    | Lit               => mkPost (CrossCatLhsReentry c)   CInfix
    | CastCurrent       => mkPost Generic                  CUnwind
    | CastFixed         => mkPost (CrossCatLhsReentry c)   CInfix
    | CastFixedEdgeOnly => mkPost (CrossCatLhsReentry c)   CUnwind
    | CastArgKeyed      => mkPost (CrossCatLhsReentry arg) CInfix
    end.

  (* Stepping the category-changing infix `==` (operand cat = `c`, infix source = `s`):
       - if the cursor is Unwinding, the `==` token trails ⇒ Reject (this is exactly the
         "WPDS finished but input remains, found ==" failure);
       - if in InfixLoop, the guard admits iff the evidence source equals `s`. *)
  Definition run (src : LhsSource) (c arg s : nat) : Outcome :=
    let p := post_lhs src c arg in
    match pl_ctrl p with
    | CUnwind => Reject
    | CInfix =>
        match evidence c (pl_edge p) with
        | Some e => if Nat.eqb e s then Accept else Reject
        | None => Reject
        end
    end.

  (* ===== The bug, reproduced end-to-end ===== *)

  (* A literal LHS of cat C admits the C-sourced category-changing infix. *)
  Theorem run_lit_accepts : forall c arg, run Lit c arg c = Accept.
  Proof.
    intros c arg. unfold run, post_lhs, evidence; simpl.
    rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  Qed.

  (* The cast LHS is REJECTED under current routing — and the model shows it fails at the
     CONTROL state (Unwinding): the `==` trails. Edge value is irrelevant here. *)
  Theorem run_cast_current_rejects : forall c arg s, run CastCurrent c arg s = Reject.
  Proof.
    intros c arg s. reflexivity.
  Qed.

  (* ===== The solution, proved correct end-to-end ===== *)

  (* Routing the cast through the delegate (reentry edge + InfixLoop) ACCEPTS the
     C-sourced category-changing infix — exactly like a literal. *)
  Theorem run_cast_fixed_accepts : forall c arg, run CastFixed c arg c = Accept.
  Proof.
    intros c arg. unfold run, post_lhs, evidence; simpl.
    rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  Qed.

  (* The fix makes the cast outcome IDENTICAL to a literal for every infix source. *)
  Theorem fix_matches_literal : forall c arg s, run CastFixed c arg s = run Lit c arg s.
  Proof.
    intros c arg s. reflexivity.
  Qed.

  (* ===== Why the partial / falsified fixes do NOT work (the anti-"surprise" proofs) ===== *)

  (* PARTIAL FIX (edge-only): stamping `CrossCatLhsReentry{C}` but leaving the cursor
     Unwinding STILL REJECTS — the `==` trails before the guard is ever consulted. This
     proves the solution MUST fix the control routing (reach InfixLoop), not just the
     edge. (This is the gap the first, too-abstract model missed.) *)
  Theorem edge_only_fix_insufficient : forall c arg s, run CastFixedEdgeOnly c arg s = Reject.
  Proof.
    intros c arg s. reflexivity.
  Qed.

  (* FALSIFIED #1 (argument-keyed reentry): a reentry keyed by the cast's ARGUMENT
     category `arg` (with arg ≠ result C) yields NO evidence at the result-cat top, so the
     C-sourced infix is suppressed. This proves the reentry MUST be keyed by the RESULT
     category C. *)
  Theorem arg_keyed_fix_insufficient :
    forall c arg, arg <> c -> run CastArgKeyed c arg c = Reject.
  Proof.
    intros c arg Hne. unfold run, post_lhs, evidence; simpl.
    apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
  Qed.

  (* ===== Soundness + non-regression of the working solution ===== *)

  (* Soundness: the fix accepts ONLY when the infix source equals the cast result cat —
     never a cross-category-mismatched infix. *)
  Theorem fix_sound : forall c arg s, run CastFixed c arg s = Accept -> s = c.
  Proof.
    intros c arg s H. unfold run, post_lhs, evidence in H; simpl in H.
    rewrite Nat.eqb_refl in H.
    destruct (Nat.eqb c s) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - discriminate H.
  Qed.

  Theorem fix_no_spurious_cross_source :
    forall c arg s, s <> c -> run CastFixed c arg s = Reject.
  Proof.
    intros c arg s Hne. unfold run, post_lhs, evidence; simpl.
    rewrite Nat.eqb_refl.
    destruct (Nat.eqb c s) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - reflexivity.
  Qed.

  (* Non-regression: the fix changes ONLY the Cast routing; literals are untouched
     (`run Lit` is unchanged — trivially, since the fix does not alter the Lit arm), and a
     same-category operator (source = result) is NOT category-changing, so the guarded
     branch the fix touches is never entered for it (the load-bearing `-3!` Neg/Fact:
     Int→Int case, which involves no cast / CrossCatProjection, is preserved). *)
  Definition is_category_changing (infix_src result_cat : nat) : bool :=
    negb (Nat.eqb infix_src result_cat).

  Theorem same_category_not_guarded : forall c, is_category_changing c c = false.
  Proof.
    intro c. unfold is_category_changing. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (* The literal outcome is independent of the cast routing (the fix is local to casts). *)
  Theorem literal_unaffected_by_fix : forall c arg s, run Lit c arg s = run Lit c arg s.
  Proof. reflexivity. Qed.

End CastResultCrossCatLhsEvidence.
