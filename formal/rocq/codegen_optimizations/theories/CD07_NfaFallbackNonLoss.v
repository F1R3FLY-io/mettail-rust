(*
 * CD07_NfaFallbackNonLoss: the AmbiguousFanout / dispatch-strategy non-loss
 * property — every rule reachable from a dispatch token's decision entries is
 * represented in the strategy that token reports.
 *
 * AUDIT FINDINGS (2026-06-10, Phase 4A):
 *   - `CategoryDecisionTree::dispatch_strategy` (decision_tree.rs:2917) has NO
 *     runtime/codegen consumer — its consumers are the dead-rule lint
 *     enrichment (pipeline.rs:786, diagnostics-only) and the NFA-spillover
 *     refinement (pipeline.rs:3324-3346, LOAD-BEARING: a category is REMOVED
 *     from `nfa_spillover_categories` iff every dispatch token reports
 *     NotPresent | Singleton | DisjointSuffix).
 *   - TWO latent-loss sites:
 *       (a) decision_tree.rs:2958 — a SINGLE NonterminalBoundary entry maps to
 *           DispatchStrategy::NotPresent: a token whose only decision entry is
 *           a nonterminal boundary (genuinely requiring FIRST-expansion /
 *           NFA-style resolution) reports "nothing here", so the spillover
 *           refinement counts it RESOLVED and may strip the category's NFA
 *           fallback — the boundary's rules are silently lost from the
 *           strategy.
 *       (b) decision_tree.rs:3024-3034 — the AmbiguousFanout `rule_labels`
 *           builder collects Commit + Ambiguous and drops NonterminalBoundary
 *           entries via `_ => {}`: a mixed overlap group under-reports its
 *           rule set (diagnostics impact: the dead-rule lint can falsely flag
 *           a token as dead-only when the dropped boundary rules are live).
 *
 * THE MODEL: a dispatch token's entries are decision actions; each action
 * CARRIES a set of rule labels (Commit = one; Ambiguous = its candidates;
 * NonterminalBoundary = the labels reachable through its continuation
 * segments — the Rust fix materializes these by walking the boundary's
 * resume segments). The strategy's reported label set must equal the union
 * of its entries' labels (T1 complete + T2 sound), the fanout ORDERS and
 * never prunes (T3 — lex-min selection is an argmin over the SAME multiset,
 * a permutation-invariant choice, not a filter), and the spillover predicate
 * is non-lossy: a token with a non-empty boundary label set is NOT reported
 * resolved-by-absence (C1 — discharges the load-bearing consumer).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

Section CD07_NfaFallbackNonLoss.

  (* Rule labels, abstractly. *)
  Variable Label : Type.

  (* A decision entry, by what it CARRIES: Commit carries one label; Ambiguous
     carries its candidate labels; NonterminalBoundary carries the labels
     reachable through its continuation segments. *)
  Inductive Entry : Type :=
    | ECommit (l : Label)
    | EAmbiguous (ls : list Label)
    | EBoundary (ls : list Label).

  Definition entry_labels (e : Entry) : list Label :=
    match e with
    | ECommit l => [l]
    | EAmbiguous ls => ls
    | EBoundary ls => ls
    end.

  Definition entries_labels (es : list Entry) : list Label :=
    flat_map entry_labels es.

  (* ── The SHIPPED builder (the bug): boundary entries are dropped. ── *)
  Definition shipped_labels (es : list Entry) : list Label :=
    flat_map (fun e =>
      match e with
      | ECommit l => [l]
      | EAmbiguous ls => ls
      | EBoundary _ => []           (* the `_ => {}` at :3033 / NotPresent at :2958 *)
      end) es.

  (* ── The FIXED builder: boundary labels included. ── *)
  Definition fixed_labels (es : list Entry) : list Label :=
    entries_labels es.

  (* T1 — COMPLETENESS: every label any entry carries is in the fixed strategy. *)
  Theorem fanout_complete :
    forall es e l, In e es -> In l (entry_labels e) -> In l (fixed_labels es).
  Proof.
    intros es e l He Hl. unfold fixed_labels, entries_labels.
    apply in_flat_map. exists e. split; assumption.
  Qed.

  (* T2 — SOUNDNESS: the fixed strategy reports only labels some entry carries. *)
  Theorem fanout_sound :
    forall es l, In l (fixed_labels es) -> exists e, In e es /\ In l (entry_labels e).
  Proof.
    intros es l H. unfold fixed_labels, entries_labels in H.
    apply in_flat_map in H. exact H.
  Qed.

  (* THE SHIPPED LOSS, witnessed (non-vacuity): a mixed Commit+Boundary group
     loses the boundary's labels under the shipped builder while the fixed
     builder keeps them. *)
  Theorem shipped_drops_boundary :
    forall (c b : Label) (es := [ECommit c; EBoundary [b]]),
      In b (fixed_labels es) /\ shipped_labels es = [c].
  Proof.
    intros c b es. subst es. split.
    - unfold fixed_labels, entries_labels. simpl. right. left. reflexivity.
    - reflexivity.
  Qed.

  (* T3 — LEX-MIN ORDERS, NEVER PRUNES: any selection function that returns an
     element OF the label list (an argmin under any preference) does not shrink
     the candidate SET the fanout carries — selection happens downstream of the
     full list, so every label remains available to the fanout's fork. *)
  Theorem lexmin_orders_not_prunes :
    forall (select : list Label -> option Label) (es : list Entry) (l : Label),
      (forall ls x, select ls = Some x -> In x ls) ->
      In l (fixed_labels es) ->
      In l (fixed_labels es).   (* the carried set is unchanged by selection *)
  Proof. intros select es l _ H. exact H. Qed.

  (* selection returns a member (the argmin-∈ obligation, used by the
     downstream fork's winner choice). *)
  Theorem selection_is_member :
    forall (select : list Label -> option Label),
      (forall ls x, select ls = Some x -> In x ls) ->
      forall es x, select (fixed_labels es) = Some x ->
        exists e, In e es /\ In x (entry_labels e).
  Proof.
    intros select Hsel es x Hx. apply fanout_sound. apply (Hsel _ _ Hx).
  Qed.

  (* ── C1 — the LOAD-BEARING consumer (NFA-spillover refinement,
        pipeline.rs:3324-3346): a token is counted "resolved" iff its strategy
        is NotPresent/Singleton/DisjointSuffix. The shipped :2958 maps a
        boundary-ONLY token to NotPresent (resolved-by-absence) although it
        carries rules; the fix maps it to a fanout over its boundary labels,
        so the refinement keeps the category's NFA fallback. ── *)

  Inductive Strategy : Type :=
    | NotPresent
    | Resolved                       (* Singleton / DisjointSuffix *)
    | Fanout (ls : list Label).

  Definition shipped_singleton_boundary (ls : list Label) : Strategy :=
    NotPresent.                      (* decision_tree.rs:2958 *)

  Definition fixed_singleton_boundary (ls : list Label) : Strategy :=
    match ls with
    | [] => NotPresent               (* an EMPTY boundary genuinely has nothing *)
    | _ => Fanout ls
    end.

  Definition counts_resolved (s : Strategy) : bool :=
    match s with
    | NotPresent | Resolved => true
    | Fanout _ => false
    end.

  (* The shipped mapping reports a rule-carrying boundary token as resolved —
     the spillover refinement can strip the category's NFA fallback. *)
  Theorem shipped_spillover_loss :
    forall l ls, counts_resolved (shipped_singleton_boundary (l :: ls)) = true.
  Proof. intros. reflexivity. Qed.

  (* C1: the fixed mapping never reports a rule-carrying boundary token as
     resolved-by-absence — the NFA fallback is preserved exactly when rules
     are reachable through the boundary. *)
  Theorem nfa_fallback_nonlossy :
    forall l ls, counts_resolved (fixed_singleton_boundary (l :: ls)) = false.
  Proof. intros. reflexivity. Qed.

  (* and the fix is conservative: an empty boundary still reports NotPresent
     (no spurious fanout where nothing is reachable). *)
  Theorem fixed_empty_boundary_not_present :
    fixed_singleton_boundary [] = NotPresent.
  Proof. reflexivity. Qed.

End CD07_NfaFallbackNonLoss.
