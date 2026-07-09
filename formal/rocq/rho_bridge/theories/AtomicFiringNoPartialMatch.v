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
 * STAGE 4 (locate-all + multi-firing) extension: DISTINCT redex SITES fire atomically WITHOUT
 * interference. The locate-all driver co-installs one guarded-join network per redex position
 * over ONE spread; each site's premises are its OWN disjoint-prefix loc:/cap: channels and its
 * accept output is a sigma-receiver send (a DISJOINT channel family from any site's premises).
 * We prove: (a) firing one site NEVER disables another (facts only grow — no-disable,
 * firing_preserves_other_premises); (b) a site's accept output is not confused with a disjoint
 * site's premise (no cross-talk, site_output_does_not_perturb_disjoint_premise); (c) two enabled
 * sites BOTH commit and BOTH outputs appear (distinct_sites_both_commit); and (d) the two firings
 * COMMUTE — the parallel / nondeterministic OUT order the multiset observation relies on
 * (distinct_sites_commute_membership). The disjointness of the premise channels themselves is the
 * O1 symbol-once property (AdvancedAutomata SymbolOnceInjective — position->channel is injective).
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

  (* ===== STAGE 4: distinct redex SITES fire atomically WITHOUT interference ===== *)

  (* A commit only GROWS the facts (`insert_exact` adds, never removes) — the monotonicity a
     co-installed site relies on: no site's firing shrinks the fact base. *)
  Lemma insert_exact_monotone : forall f facts x,
    In x facts -> In x (insert_exact f facts).
  Proof. intros f facts x Hin. apply insert_exact_membership. right. exact Hin. Qed.

  (* NO-DISABLE: firing site r1 (adding its accept output) leaves EVERY premise of a co-installed
     site r2 still present — one located redex firing never disables another. Needs no disjointness
     (facts only grow), the strongest form of non-interference on the enabling side. *)
  Theorem firing_preserves_other_premises : forall facts r1 r2,
    all_present facts (guarded_premises r2) ->
    all_present (insert_exact (guarded_output r1) facts) (guarded_premises r2).
  Proof.
    intros facts r1 r2 Hpres p Hp. apply insert_exact_monotone. apply Hpres. exact Hp.
  Qed.

  (* NO CROSS-TALK: site r1's accept output is a σ-receiver send on a channel family DISJOINT from
     any site's `loc:`/`cap:` premises, so it is never one of r2's premises — hence r1's firing
     neither spuriously ENABLES nor perturbs a premise fact of r2 (membership is unchanged both
     ways). Modeled as: a fact distinct from the output has identical membership before/after. *)
  Theorem site_output_does_not_perturb_disjoint_premise : forall facts r1 p,
    p <> guarded_output r1 ->
    (In p (insert_exact (guarded_output r1) facts) <-> In p facts).
  Proof.
    intros facts r1 p Hne. split.
    - intro Hin. apply insert_exact_membership in Hin. destruct Hin as [Heq | Hin].
      + exfalso. apply Hne. exact Heq.
      + exact Hin.
    - intro Hin. apply insert_exact_monotone. exact Hin.
  Qed.

  (* BOTH SITES FIRE: two enabled, guard-satisfied sites BOTH commit (in sequence, either order by
     the commute lemma below) and BOTH accept outputs are present in the final facts — the
     multi-firing property: every located redex lands its contractum, none excluded. *)
  Theorem distinct_sites_both_commit : forall facts r1 r2,
    all_present facts (guarded_premises r1) -> guarded_guard r1 = true ->
    all_present facts (guarded_premises r2) -> guarded_guard r2 = true ->
    exists f1 f2,
      guarded_attempt facts r1 f1 /\
      guarded_attempt f1 r2 f2 /\
      In (guarded_output r1) f2 /\ In (guarded_output r2) f2.
  Proof.
    intros facts r1 r2 Hp1 Hg1 Hp2 Hg2.
    exists (insert_exact (guarded_output r1) facts).
    exists (insert_exact (guarded_output r2) (insert_exact (guarded_output r1) facts)).
    split; [| split; [| split]].
    - apply guarded_commit; assumption.
    - apply guarded_commit; [ apply firing_preserves_other_premises; exact Hp2 | exact Hg2 ].
    - apply insert_exact_membership. right. apply insert_exact_membership. left. reflexivity.
    - apply insert_exact_membership. left. reflexivity.
  Qed.

  (* ORDER-INDEPENDENT: firing r1 then r2 yields the SAME facts (up to membership) as r2 then r1 —
     the co-installed sites commute, so the nondeterministic order the parallel accepts land on OUT
     does not change the observed multiset of contracta. *)
  Theorem distinct_sites_commute_membership : forall facts r1 r2 x,
    In x (insert_exact (guarded_output r2) (insert_exact (guarded_output r1) facts)) <->
    In x (insert_exact (guarded_output r1) (insert_exact (guarded_output r2) facts)).
  Proof.
    intros facts r1 r2 x. rewrite !insert_exact_membership. tauto.
  Qed.

End AtomicFiringNoPartialMatch.

Print Assumptions partial_consume_unreachable.
Print Assumptions accept_atomic_after_verdict.
Print Assumptions no_accept_on_failed_guard.
Print Assumptions firing_preserves_other_premises.
Print Assumptions site_output_does_not_perturb_disjoint_premise.
Print Assumptions distinct_sites_both_commit.
Print Assumptions distinct_sites_commute_membership.
