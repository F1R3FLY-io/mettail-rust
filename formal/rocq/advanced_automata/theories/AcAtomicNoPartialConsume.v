(*
 * AcAtomicNoPartialConsume: FV (AC-atom) for Stage AC's in-Rho AC matching.
 *
 * The native RSpace `consume` over the AC-bag carrier is all-or-nothing. When an AC pattern
 * `op{L_1..L_k, ...rest}` is matched against a ground bag inside ONE atomic locked consume, the
 * transaction either:
 *   - COMMITS (the non-linear guard holds AND the k-element selection is a sub-multiset present
 *     in the bag): it removes the WHOLE selection at once, `bag → complement bag selection`
 *     (`AcRestReconstruction`), binding `rest` to that complement; or
 *   - VETOES (guard false, or the selection is not present): it leaves the bag UNTOUCHED
 *     ("leave the data alone" — the `check_commit` reject-safe veto = host `merge_substs → None`).
 * NO partial removal — a state where only some of the k selected occurrences were consumed — is
 * reachable. This is the REMOVAL-side dual of `AtomicFiringNoPartialMatch` (the firing's
 * addition side) and mirrors `GuardedCommSoundness.guarded_attempt`'s three outcomes
 * (commit / reject-guard / reject-missing) for the consume.
 *
 * Lives in advanced_automata to reuse `AcRestReconstruction`'s `sub_multiset` / `complement` /
 * `selection_rest_partition` directly (same -Q AdvancedAutomata scope).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From AdvancedAutomata Require Import AcRestReconstruction.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

Section AcAtomicConsume.

  (* The AC consume of a matched `selection` from `bag` under a non-linear `guard` verdict.
     `bag`/`selection` are parameters; the resulting bag is the single index. Exactly one of
     the three outcomes fires — the constructors are mutually exclusive on (guard, presence). *)
  Inductive ac_consume (bag selection : list nat) (guard : bool) : list nat -> Prop :=
    | ac_commit :
        guard = true ->
        sub_multiset selection bag ->
        ac_consume bag selection guard (complement bag selection)
    | ac_reject_guard :
        guard = false ->
        ac_consume bag selection guard bag
    | ac_reject_missing :
        ~ sub_multiset selection bag ->
        ac_consume bag selection guard bag.

  (* (AC-atom.1) ALL-OR-NOTHING: the bag after a consume is EITHER the full complement (the
     whole selection removed) OR the untouched bag — never a partial removal. *)
  Theorem ac_consume_all_or_nothing : forall bag selection guard after,
    ac_consume bag selection guard after ->
    after = complement bag selection \/ after = bag.
  Proof.
    intros bag selection guard after H.
    inversion H; subst; [ left | right | right ]; reflexivity.
  Qed.

  (* (AC-atom.2) VETO CONSUMES NOTHING: a false guard leaves the bag untouched (reject-safe;
     the removal-side mirror of GuardedCommSoundness.failed_guard_no_commit). *)
  Theorem ac_veto_consumes_nothing : forall bag selection after,
    ac_consume bag selection false after -> after = bag.
  Proof.
    intros bag selection after H.
    inversion H; subst; [ discriminate | reflexivity | reflexivity ].
  Qed.

  (* (AC-atom.3) A MISSING SELECTION consumes nothing (mirror of missing_premise_no_commit):
     if the selection is not a sub-multiset of the bag, no occurrence is removed. *)
  Theorem ac_missing_selection_consumes_nothing : forall bag selection guard after,
    ~ sub_multiset selection bag ->
    ac_consume bag selection guard after -> after = bag.
  Proof.
    intros bag selection guard after Hmiss H.
    inversion H; subst; [ contradiction | reflexivity | reflexivity ].
  Qed.

  (* (AC-atom.4) A COMMITTED consume removes EXACTLY the selection: `selection ⊎ after ≡ bag`
     as multisets (via AcRestReconstruction.selection_rest_partition) — the removed multiset is
     precisely the matched selection, nothing more, nothing less. With the selection present and
     the guard true, the commit outcome is the only reachable one. *)
  Theorem ac_commit_removes_exactly_the_selection : forall bag selection after,
    sub_multiset selection bag ->
    ac_consume bag selection true after ->
    Permutation (selection ++ after) bag.
  Proof.
    intros bag selection after Hsub H.
    inversion H; subst.
    - apply selection_rest_partition. exact Hsub.
    - discriminate.
    - contradiction.
  Qed.

  (* (AC-atom.5) VETO PRESERVES EVERY element: a rejected consume leaves every bag element in
     place — the "leave the data alone" guarantee the native consume's reject-safe veto gives
     (no element is lost on a non-match, so the persistent receiver can re-fire). *)
  Theorem ac_veto_preserves_all : forall bag selection after x,
    ac_consume bag selection false after -> In x bag -> In x after.
  Proof.
    intros bag selection after x H Hin.
    rewrite (ac_veto_consumes_nothing bag selection after H). exact Hin.
  Qed.

End AcAtomicConsume.

Print Assumptions ac_consume_all_or_nothing.
Print Assumptions ac_veto_consumes_nothing.
Print Assumptions ac_missing_selection_consumes_nothing.
Print Assumptions ac_commit_removes_exactly_the_selection.
Print Assumptions ac_veto_preserves_all.
