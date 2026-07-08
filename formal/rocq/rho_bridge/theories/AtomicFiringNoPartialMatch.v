(*
 * AtomicFiringNoPartialMatch: FV (iv) for Stage 2's in-Rho matching.
 *
 * The eq:-guarded polyadic join (rholang-codegen `rho_net_automaton.rs`
 * `join_children_receiver`) is ONE atomic guarded consume: no reachable state consumes a
 * proper non-empty subset of the children (no partial match), and the accept output appears
 * IFF the premises are present and the consistency guard holds — the accept fires atomically
 * AFTER the whole structural + consistency verdict. Modeled on the `GuardedCommSoundness`
 * `guarded_attempt` (the single guarded consume): the join is all-or-nothing, which is why the
 * JOIN (not the nested child chain) is required — a nested chain would expose an intermediate
 * committed state (an outer child consumed before the inner guard runs).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From RhoBridge Require Import GuardedCommSoundness.

Import ListNotations.

Section AtomicFiringNoPartialMatch.

  (* ALL-OR-NOTHING: the guarded join consume either adds the output (commit) or leaves the
     facts UNCHANGED (reject) — NO reachable state consumes a proper subset of the children (a
     partial match). Directly from the three `guarded_attempt` constructors. *)
  Theorem partial_consume_unreachable : forall facts r next,
    guarded_attempt facts r next ->
    next = insert_exact (guarded_output r) facts \/ next = facts.
  Proof.
    intros facts r next Hattempt.
    inversion Hattempt; subst.
    - left. reflexivity.
    - right. reflexivity.
    - right. reflexivity.
  Qed.

  (* ACCEPT ATOMIC AFTER VERDICT: the output is added iff the premises are present AND the guard
     holds — the accept send fires only after the whole structural + consistency verdict, never
     before. *)
  Theorem accept_atomic_after_verdict : forall facts r,
    all_present facts (guarded_premises r) ->
    guarded_guard r = true ->
    exists next, guarded_attempt facts r next /\ In (guarded_output r) next.
  Proof.
    intros facts r Hpres Hguard.
    apply (true_guard_enabled_adds_output facts r Hpres Hguard).
  Qed.

  (* NO ACCEPT ON A FAILED VERDICT: a false guard adds NO output and consumes NO data — the
     accept does not fire on inequality (the join is vetoed as a whole). *)
  Theorem no_accept_on_failed_guard : forall facts r next,
    guarded_guard r = false ->
    guarded_attempt facts r next ->
    next = facts.
  Proof.
    intros facts r next Hguard Hattempt.
    apply (failed_guard_no_commit facts r next Hguard Hattempt).
  Qed.

End AtomicFiringNoPartialMatch.

Print Assumptions partial_consume_unreachable.
Print Assumptions accept_atomic_after_verdict.
Print Assumptions no_accept_on_failed_guard.
