(*
 * NonLinearEqConsistency: FV (vi) for Stage 2's in-Rho non-linear eq: consistency join.
 *
 * The eq: consistency join (rholang-codegen `rho_net_automaton.rs` `consistency_guard` /
 * `join_children_receiver`) commits its guarded consume IFF every occurrence of a repeated
 * LHS variable bound the SAME value (name-equal head tags), and is reject-safe otherwise
 * (the reducer's `check_commit` vetoes, consuming NO data — mirroring `merge_substs -> None`).
 * This models the guard as a `GuardedRule` whose `guarded_guard` is `all_equal occ` (the
 * reflected `EEq`/`EAnd` chain over the k occurrences) and proves commit <-> all-equal,
 * reject-safe, and no-fabrication — so the eq: consistency is an INSTANCE of the proven
 * `GuardedCommSoundness` guarded model, not a bespoke re-proof.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import GuardedCommSoundness.

Import ListNotations.

Section NonLinearEqConsistency.

  (* The k occurrence values of a repeated variable (Fact = nat head-tag identities). *)
  Definition Occ := list Fact.

  (* The reflected `EEq`/`EAnd` consistency chain: every occurrence equals the first. *)
  Definition all_equal (occ : Occ) : bool :=
    match occ with
    | [] => true
    | h :: t => forallb (Nat.eqb h) t
    end.

  (* Characterization: `all_equal` is exactly pairwise name-equality (every occurrence equals
     the first) — the "name-equality" of obligation (vi). *)
  Lemma all_equal_iff : forall h t,
    all_equal (h :: t) = true <-> (forall x, In x t -> x = h).
  Proof.
    intros h t. unfold all_equal. rewrite forallb_forall. split.
    - intros H x Hin. symmetry. apply Nat.eqb_eq. apply H. exact Hin.
    - intros H x Hin. apply Nat.eqb_eq. symmetry. apply H. exact Hin.
  Qed.

  (* The eq: consistency rule: fire `output` from `premises` iff the k occurrences agree. *)
  Definition eq_rule (premises : list Fact) (occ : Occ) (output : Fact) : GuardedRule :=
    {| guarded_premises := premises; guarded_guard := all_equal occ; guarded_output := output |}.

  (* COMMIT: all occurrences equal (with the premises present) => the guarded consume adds the
     output. Half of commit <-> name-equality. *)
  Theorem eq_all_equal_commits : forall facts premises occ output,
    all_present facts premises ->
    all_equal occ = true ->
    guarded_attempt facts (eq_rule premises occ output) (insert_exact output facts).
  Proof.
    intros facts premises occ output Hpres Hguard.
    apply guarded_commit; [exact Hpres | exact Hguard].
  Qed.

  (* REJECT-SAFE: if the occurrences disagree, the guard is false, so the guarded consume does
     NOT commit and consumes NO data (next = facts) — the `merge_substs -> None` analogue. The
     other half of commit <-> name-equality. *)
  Theorem eq_unequal_no_commit : forall facts premises occ output next,
    all_equal occ = false ->
    guarded_attempt facts (eq_rule premises occ output) next ->
    next = facts.
  Proof.
    intros facts premises occ output next Hne Hattempt.
    apply (failed_guard_no_commit facts (eq_rule premises occ output) next).
    - exact Hne.
    - exact Hattempt.
  Qed.

  (* NO FABRICATION: every fact after the attempt is the output or was already present. *)
  Theorem eq_no_fabrication : forall facts premises occ output next x,
    guarded_attempt facts (eq_rule premises occ output) next ->
    In x next ->
    x = output \/ In x facts.
  Proof.
    intros facts premises occ output next x Hattempt Hin.
    apply (guarded_attempt_no_fabrication facts (eq_rule premises occ output) next x);
      assumption.
  Qed.

  (* ORACLE AGREEMENT: the in-Rho guard commits iff the host `merge_substs` oracle (a left-fold
     returning None on the first mismatch) accepts — both are `all_equal`. *)
  Definition merge_ok (occ : Occ) : bool := all_equal occ.

  Theorem eq_oracle_agreement : forall premises occ output,
    guarded_guard (eq_rule premises occ output) = merge_ok occ.
  Proof. intros. reflexivity. Qed.

End NonLinearEqConsistency.

Print Assumptions eq_all_equal_commits.
Print Assumptions eq_unequal_no_commit.
Print Assumptions eq_no_fabrication.
Print Assumptions eq_oracle_agreement.
