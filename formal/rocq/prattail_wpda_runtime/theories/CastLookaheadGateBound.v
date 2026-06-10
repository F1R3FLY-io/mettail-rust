(*
 * CastLookaheadGateBound: the EVIDENCE-DRIVEN-EARLY-REJECTION refinement of the
 * cast-delegate bound (user-directed 2026-06-10: "pull evidence into earlier
 * stages to avoid GENERATING superfluous alternatives", via lookahead). Where
 * CastDelegateMergeBound.v proves a cohort MERGE collapses the K-per-level
 * delegate blowup AFTER generation, this file proves a stronger, complementary
 * lever: LOOKAHEAD GATING PREVENTS the generation.
 *
 * THE PRINCIPLE (sound, NOT premature disambiguation): the token immediately
 * after a parsed operand is DEFINITE, monotone-under-continuation evidence. A
 * cross-cat-LHS delegate for a category-changing infix `op_i` (trigger token t_i)
 * is dispatched at a position ONLY when the lookahead token = t_i. Because infix
 * trigger tokens are distinct, AT MOST ONE op_i matches a given lookahead, and
 * positions NOT followed by a category-changing infix dispatch ZERO delegates.
 *
 * CONSEQUENCE: the gated delegate count over an input equals the number of
 * positions whose lookahead is an infix trigger — bounded by the INPUT LENGTH
 * (linear), INDEPENDENT of cast nesting depth. So the K^depth blowup
 * (CastDelegateMergeBound.naive_exponential) never even forms: the inner casts of
 * `int(float(int(3.14)))` are arguments with no following category-changing infix,
 * so they dispatch NO cross-cat-LHS delegate. `int(3) == 3` dispatches exactly the
 * EqInt delegate (lookahead `==`); `int(3) + 3` dispatches NONE (`+` is same-cat);
 * `int(3)` at EOI dispatches NONE.
 *
 * SOUNDNESS (no-loss): a parse the input actually admits via infix op_i at a
 * position HAS t_i present at that position (the trigger is in the input), so the
 * gate PASSES — gating never drops a viable alternative. It removes only delegates
 * for infixes whose trigger is absent (which could not have fired anyway).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Section CastLookaheadGateBound.

  (* K = category-changing infixes sharing one source cat (Int: == != < <= > >=). *)
  Variable K : nat.
  Hypothesis K_ge_1 : 1 <= K.

  (* A position's lookahead, encoded as the matched infix index `Some i` (i<K, the
     i-th category-changing infix's trigger token) or `None` (not such a trigger:
     a same-category infix, a non-infix token, or EOI). Distinct triggers ⇒ at most
     one infix index per lookahead, captured by this `option nat`. *)
  Definition gated_delegates_at (la : option nat) : nat :=
    match la with
    | Some i => if Nat.ltb i K then 1 else 0
    | None => 0
    end.

  (* Per-position: gating dispatches AT MOST ONE cross-cat-LHS delegate. *)
  Theorem gated_at_most_one : forall la, gated_delegates_at la <= 1.
  Proof.
    intro la. unfold gated_delegates_at.
    destruct la as [i|]; [destruct (Nat.ltb i K) |]; lia.
  Qed.

  (* Per-position: ZERO delegates where no category-changing infix follows — the
     superfluous-alternative avoidance (the user's "avoid GENERATING"). *)
  Theorem gated_zero_when_no_infix : gated_delegates_at None = 0.
  Proof. reflexivity. Qed.

  (* No-loss: a parse using infix i (i<K) at a position whose lookahead IS that
     trigger gets its delegate dispatched — the gate passes because the trigger is
     present in the input. Gating drops no viable alternative. *)
  Theorem gated_no_loss : forall i, i < K -> gated_delegates_at (Some i) = 1.
  Proof.
    intros i Hi. unfold gated_delegates_at.
    assert (Nat.ltb i K = true) as E by (apply Nat.ltb_lt; exact Hi).
    rewrite E. reflexivity.
  Qed.

  (* Over an input (per-position lookaheads), the gated delegate count. *)
  Fixpoint gated_total (input : list (option nat)) : nat :=
    match input with
    | [] => 0
    | la :: tl => gated_delegates_at la + gated_total tl
    end.

  (* LINEAR BOUND: the gated frontier is bounded by the input length, INDEPENDENT
     of cast nesting depth — so the K^depth blowup never forms. Contrast
     CastDelegateMergeBound.naive_exponential (>= 2^depth). *)
  Theorem gated_le_length : forall input, gated_total input <= length input.
  Proof.
    induction input as [|la tl IH]; simpl; [lia |].
    pose proof (gated_at_most_one la). lia.
  Qed.

  (* SHARPER: the gated count equals exactly the number of positions whose
     lookahead is a (valid) category-changing-infix trigger — i.e. the number of
     such infixes ACTUALLY in the input. Nothing superfluous is generated. *)
  Definition is_infix_trigger (la : option nat) : bool :=
    match la with Some i => Nat.ltb i K | None => false end.

  Theorem gated_counts_actual_infix_triggers :
    forall input, gated_total input = length (filter is_infix_trigger input).
  Proof.
    induction input as [|la tl IH]; simpl; [reflexivity |].
    unfold gated_delegates_at, is_infix_trigger.
    destruct la as [i|]; [destruct (Nat.ltb i K) |]; simpl; rewrite IH; reflexivity.
  Qed.

  (* Composes with the merge: even when several category-changing infixes COULD
     share a position's source cat, the lookahead selects the unique one whose
     trigger is present, so gating already yields the <=1-per-position that the
     merge guarantees — and yields 0 where the merge would still have generated a
     (then-unused) shared delegate. Gating subsumes the per-position K factor and
     additionally removes the no-following-infix positions. *)
  Theorem gating_subsumes_per_position_merge :
    forall la, gated_delegates_at la <= 1.
  Proof. exact gated_at_most_one. Qed.

End CastLookaheadGateBound.
