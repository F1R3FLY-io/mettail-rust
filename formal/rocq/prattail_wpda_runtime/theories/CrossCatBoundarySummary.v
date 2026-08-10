(*
 * CrossCatBoundarySummary: admission-free correctness model for the
 * incremental target-category lattice used by
 * `WpdaWalker::cgll_pure_crosscat_boundaries`.
 *
 * The production summary is deliberately only a negative-result filter.  It
 * records every explicit target category and every inferred target category
 * reachable before a re-scoping/dead hop.  A positive summary result still
 * executes the exact, cycle-safe GSS walk.  Consequently the optimization's
 * safety obligation is:
 *
 *     summary_may_recognize = false  ->  exact_walk_may_emit = false.
 *
 * This file proves the stronger equality for (1) every finite caller path and
 * (2) the union of every finite caller path in a GSS unfolding.  It also proves
 * semantic idempotence and monotonicity of join, the facts used by the Rust
 * semi-naive fixed-point worklist.  `Summary` uses lists as abstract finite
 * sets; the Rust `[u64; 4]` plus sorted-overflow representation is checked
 * independently by `prattail/tests/crosscat_boundary_summary_oracle.rs`.
 *
 * Rocq 9.1 compatible.  No Admitted, Axiom, or Assumption.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Section CrossCatBoundarySummary.

  Inductive Evidence : Type :=
    | Explicit                         (* same-category target is admissible *)
    | Inferred.                        (* target must differ from the source  *)

  Record Hop : Type := {
    stop_before : bool;                (* dies before this hop's mapping      *)
    target      : option (Evidence * nat);
    stop_after  : bool                 (* mapping runs, then ancestry stops   *)
  }.

  Variable recognizes : nat -> bool.
  Variable source_category : nat.

  Definition target_may_recognize (t : Evidence * nat) : bool :=
    let '(evidence, category) := t in
    match evidence with
    | Explicit => recognizes category
    | Inferred => negb (Nat.eqb category source_category) && recognizes category
    end.

  (* The original exhaustive walk, projected to the existential fact needed
     by the fast reject.  A recognizing target terminates this path; an
     unrecognized target continues unless the hop re-scopes. *)
  Definition exact_step (hop : Hop) (caller_may_emit : bool) : bool :=
    if stop_before hop then false
    else
      let local :=
        match target hop with
        | Some t => target_may_recognize t
        | None => false
        end in
      local || (negb (stop_after hop) && caller_may_emit).

  Fixpoint exact_path_may_emit (hops : list Hop) : bool :=
    match hops with
    | [] => false
    | hop :: callers => exact_step hop (exact_path_may_emit callers)
    end.

  Record Summary : Type := {
    explicit_targets : list nat;
    inferred_targets : list nat;
    inherits_callers : bool
  }.

  Definition empty_summary : Summary :=
    {| explicit_targets := [];
       inferred_targets := [];
       inherits_callers := false |}.

  Definition local_summary (hop : Hop) : Summary :=
    if stop_before hop then empty_summary
    else
      let inherited := negb (stop_after hop) in
      match target hop with
      | Some (Explicit, category) =>
          {| explicit_targets := [category];
             inferred_targets := [];
             inherits_callers := inherited |}
      | Some (Inferred, category) =>
          {| explicit_targets := [];
             inferred_targets := [category];
             inherits_callers := inherited |}
      | None =>
          {| explicit_targets := [];
             inferred_targets := [];
             inherits_callers := inherited |}
      end.

  (* Abstract-set join.  Duplicates do not matter to `summary_may_recognize`;
     the Rust bitset representation removes them physically. *)
  Definition join_summary (left right : Summary) : Summary :=
    {| explicit_targets := explicit_targets left ++ explicit_targets right;
       inferred_targets := inferred_targets left ++ inferred_targets right;
       inherits_callers := inherits_callers left || inherits_callers right |}.

  Definition prepend_summary (hop : Hop) (callers : Summary) : Summary :=
    let local := local_summary hop in
    if inherits_callers local then join_summary local callers else local.

  Fixpoint summarize_path (hops : list Hop) : Summary :=
    match hops with
    | [] => empty_summary
    | hop :: callers => prepend_summary hop (summarize_path callers)
    end.

  Definition summary_may_recognize (summary : Summary) : bool :=
    existsb recognizes (explicit_targets summary)
    || existsb
         (fun category =>
            negb (Nat.eqb category source_category) && recognizes category)
         (inferred_targets summary).

  Lemma empty_summary_rejects :
    summary_may_recognize empty_summary = false.
  Proof. reflexivity. Qed.

  Lemma join_summary_is_disjunction :
    forall left right,
      summary_may_recognize (join_summary left right) =
      (summary_may_recognize left || summary_may_recognize right).
  Proof.
    intros [le li lh] [re ri rh].
    unfold summary_may_recognize, join_summary; simpl.
    repeat rewrite existsb_app.
    btauto.
  Qed.

  (* The join is the monotone, semantically idempotent lattice operation used
     by the semi-naive reverse-dependency worklist. *)
  Theorem join_summary_semantically_idempotent :
    forall summary,
      summary_may_recognize (join_summary summary summary) =
      summary_may_recognize summary.
  Proof.
    intro summary. rewrite join_summary_is_disjunction. apply orb_diag.
  Qed.

  Theorem join_summary_is_monotone_left :
    forall left right,
      summary_may_recognize left = true ->
      summary_may_recognize (join_summary left right) = true.
  Proof.
    intros left right H.
    rewrite join_summary_is_disjunction, H. reflexivity.
  Qed.

  Lemma prepend_summary_matches_exact_step :
    forall hop callers,
      summary_may_recognize (prepend_summary hop callers) =
      exact_step hop (summary_may_recognize callers).
  Proof.
    intros [before target0 after] [explicit0 inferred0 inherits0].
    unfold prepend_summary, local_summary, exact_step,
      summary_may_recognize, empty_summary, join_summary; simpl.
    destruct before; simpl; [reflexivity |].
    destruct target0 as [[evidence category] |].
    - destruct evidence; destruct after; simpl; btauto.
    - destruct after; simpl; btauto.
  Qed.

  (* Strong form of the negative-reject obligation for a single caller path. *)
  Theorem summarize_path_exact :
    forall hops,
      summary_may_recognize (summarize_path hops) = exact_path_may_emit hops.
  Proof.
    induction hops as [| hop callers IH].
    - apply empty_summary_rejects.
    - simpl. rewrite prepend_summary_matches_exact_step, IH. reflexivity.
  Qed.

  Corollary summary_negative_reject_is_sound :
    forall hops,
      summary_may_recognize (summarize_path hops) = false ->
      exact_path_may_emit hops = false.
  Proof.
    intros hops H. rewrite <- summarize_path_exact. exact H.
  Qed.

  (* A GSS node may have several callers.  The exhaustive DFS emits if any
     finite caller path emits; the fixed-point summary joins those paths. *)
  Fixpoint exact_paths_may_emit (paths : list (list Hop)) : bool :=
    match paths with
    | [] => false
    | path :: rest => exact_path_may_emit path || exact_paths_may_emit rest
    end.

  Fixpoint summarize_paths (paths : list (list Hop)) : Summary :=
    match paths with
    | [] => empty_summary
    | path :: rest => join_summary (summarize_path path) (summarize_paths rest)
    end.

  Theorem summarize_all_caller_paths_exact :
    forall paths,
      summary_may_recognize (summarize_paths paths) = exact_paths_may_emit paths.
  Proof.
    induction paths as [| path rest IH].
    - apply empty_summary_rejects.
    - simpl. rewrite join_summary_is_disjunction, summarize_path_exact, IH.
      reflexivity.
  Qed.

  Corollary all_paths_negative_reject_is_sound :
    forall paths,
      summary_may_recognize (summarize_paths paths) = false ->
      exact_paths_may_emit paths = false.
  Proof.
    intros paths H. rewrite <- summarize_all_caller_paths_exact. exact H.
  Qed.

End CrossCatBoundarySummary.

Print Assumptions join_summary_semantically_idempotent.
Print Assumptions join_summary_is_monotone_left.
Print Assumptions summarize_path_exact.
Print Assumptions summary_negative_reject_is_sound.
Print Assumptions summarize_all_caller_paths_exact.
Print Assumptions all_paths_negative_reject_is_sound.
