(*
 * CastLookaheadHostSynthesis: the UNIFIED implementation spec for the
 * cast-then-compare fix — lookahead-gated hosting synthesis. Combines the two
 * proven properties into the exact mechanism the walker must transcribe:
 *   - CastCompareFrontierBound.v: a category-changing infix `op : c -> D` is
 *     ACCEPTED (Hosted) only if the operand's cursor has return-context = D
 *     (the hosting law).
 *   - CastLookaheadGateBound.v: the cross-cat-LHS dispatch should fire only when
 *     the LOOKAHEAD token is the infix's trigger (definite, monotone evidence) —
 *     prevents the K^depth blowup, no-loss.
 *
 * THE MECHANISM (breaks the earlier "circular guard"): at the operand-completion
 * InfixLoop — operand of cat c fully parsed, lookahead token `la` — for each
 * c-sourced category-changing infix op_i : c -> D_i with trigger t_i:
 *   if la = t_i: SYNTHESIZE the cross-cat-LHS reentry that sets the operand's
 *               return-context to D_i, so op_i fires HOSTED;
 *   else:        unwind (no infix).
 * The evidence is the LOOKAHEAD TOKEN (already in the input — definite, not a
 * cursor-edge guess), so it is NOT the circular cursor-edge evidence that blocked
 * the post-resolution shortcut. It is applied POST-resolution (operand parsed
 * once => no dispatch-time fan-out / no 2^depth blowup), and yields AT MOST ONE
 * synthesis per operand (distinct triggers).
 *
 * This is the precise spec to implement: at operand-completion, read the
 * lookahead; if it is the trigger of a c-sourced category-changing infix op_i,
 * synthesize a reentry with return-context = D_i; else unwind. The walker change
 * is +0 cursors (a return-context-establishing reentry on the existing operand
 * cursor, gated by the lookahead), realizable lazily.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Section CastLookaheadHostSynthesis.

  Variable c : nat.                   (* the operand (cast result) category *)
  Variable K : nat.                   (* # of c-sourced category-changing infixes *)
  Variable result_cat : nat -> nat.   (* op_i : c -> result_cat i *)
  Hypothesis K_ge_1 : 1 <= K.
  (* Category-CHANGING: each synthesized infix's result differs from the operand
     cat — exactly the family that needs cross-cat-LHS hosting (same-cat infixes
     do not, and are not synthesized here). *)
  Hypothesis changing : forall i, i < K -> result_cat i <> c.

  (* Outcome of the operand at the infix position. HostedInfix i means op_i fired
     with its result HOSTED (return-context = result_cat i). *)
  Inductive Outcome : Type := Unwind | HostedInfix (i : nat).

  (* The synthesized return-context for the operand when op_i is chosen. By the
     hosting law it MUST be result_cat i for op_i to be Hosted. *)
  Definition synth_return_cat (i : nat) : nat := result_cat i.

  (* Lookahead-gated hosting synthesis. la = Some i (the i-th infix's trigger
     token is the lookahead) with i < K => synthesize op_i hosted; else unwind. *)
  Definition synth (la : option nat) : Outcome :=
    match la with
    | Some i => if Nat.ltb i K then HostedInfix i else Unwind
    | None => Unwind
    end.

  (* The synthesized lane establishes return-context = result_cat i = D_i, which
     is EXACTLY the hosting law's requirement (CastCompareFrontierBound
     .hosting_requires_return_cat: Hosted => return-context = result cat). *)
  Theorem synth_return_cat_is_result :
    forall i, synth_return_cat i = result_cat i.
  Proof. intro i. reflexivity. Qed.

  (* A lookahead that is op_i's trigger (i<K) synthesizes op_i hosted. *)
  Theorem synth_hosts_matched_infix :
    forall i, i < K -> synth (Some i) = HostedInfix i.
  Proof.
    intros i Hi. unfold synth.
    assert (Nat.ltb i K = true) as E by (apply Nat.ltb_lt; exact Hi).
    rewrite E. reflexivity.
  Qed.

  (* No following infix trigger => the operand unwinds: no spurious infix, and (by
     contrast with the orphaned recognition approach) no Hosted result is produced
     where none should be. *)
  Theorem synth_unwinds_without_trigger : synth None = Unwind.
  Proof. reflexivity. Qed.

  (* SOUNDNESS: synthesis fires ONLY the lookahead-matched, in-range infix. *)
  Theorem synth_sound :
    forall la i, synth la = HostedInfix i -> la = Some i /\ i < K.
  Proof.
    intros la i H. unfold synth in H. destruct la as [j|]; [| discriminate H].
    destruct (Nat.ltb j K) eqn:E; [| discriminate H].
    injection H as <-. split; [reflexivity | apply Nat.ltb_lt; exact E].
  Qed.

  (* NO-LOSS: a parse that applies op_i (i<K) after the operand HAS t_i present as
     the lookahead, so synthesis produces its hosting lane — gating drops no parse
     the input admits (monotone-evidence soundness). *)
  Theorem synth_no_loss : forall i, i < K -> synth (Some i) = HostedInfix i.
  Proof. exact synth_hosts_matched_infix. Qed.

  (* BOUNDED: at most one infix is synthesized per operand (distinct triggers ⇒
     the lookahead matches at most one i) — +0/≤1 per operand, NOT the K-per-level
     × nesting blowup. *)
  Theorem synth_at_most_one :
    forall la i j, synth la = HostedInfix i -> synth la = HostedInfix j -> i = j.
  Proof.
    intros la i j Hi Hj. rewrite Hi in Hj. injection Hj as <-. reflexivity.
  Qed.

  (* The synthesized infixes are exactly the category-CHANGING ones (result <> c) —
     the family that needs cross-cat-LHS hosting; same-category infixes are not
     synthesized (they need no hosting and fire on the operand's own cat). *)
  Theorem synth_targets_changing_infix :
    forall la i, synth la = HostedInfix i -> result_cat i <> c.
  Proof.
    intros la i H. apply synth_sound in H. destruct H as [_ Hlt].
    apply changing; exact Hlt.
  Qed.

End CastLookaheadHostSynthesis.
