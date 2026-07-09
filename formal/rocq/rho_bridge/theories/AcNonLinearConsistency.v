(*
 * AcNonLinearConsistency: FV (AC-nl) for Stage AC's in-Rho non-linear AC matching.
 *
 * In an AC match, the native bipartite assignment binds the k pattern slots to k bag elements
 * (the `selection`, in slot order). A repeated LHS variable (e.g. `{x, x, ...rest}`, or the
 * rho-into-rho `x = x'`) occupies a SET of slot positions; its occurrences are the selection
 * values AT those positions. The AC non-linear consistency guard is `all_equal` over those
 * gathered occurrences — i.e. it is exactly the Stage-2 eq: consistency guard
 * (`NonLinearEqConsistency`, vi) COMPOSED WITH the AC selection's slot-gather. So non-linear AC
 * matching is NOT a new proof obligation: it inherits vi's commit <-> name-equality and
 * reject-safety, with the occurrences supplied by the (order-independent) AC selection rather
 * than by fixed positional children.
 *
 * Reuses vi (`all_equal`, `eq_rule`, `eq_all_equal_commits`, `eq_unequal_no_commit`) and
 * `GuardedCommSoundness`. Zero-admission. Rocq 9.1 compatible. No Admitted/Axioms/Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.

Import ListNotations.

Section AcNonLinearConsistency.

  (* Gather the selection values at a repeated variable's slot positions (slot order). *)
  Definition gather (positions : list nat) (selection : list Fact) (default : Fact) : Occ :=
    map (fun p => nth p selection default) positions.

  (* The AC non-linear guard for one repeated variable: its gathered occurrences all agree —
     the reflected EEq/EAnd chain over the selection slots the variable occupies. *)
  Definition ac_nl_guard (positions : list nat) (selection : list Fact) (default : Fact) : bool :=
    all_equal (gather positions selection default).

  (* (AC-nl.1) COMMIT: the AC consistency commits (adds the output) iff the variable's slots,
     gathered from the selection, all bound the same value — vi's commit, with the occurrences
     supplied by the AC bipartite selection. *)
  Theorem ac_nl_commits_iff_slots_agree :
    forall facts premises positions selection default output,
      all_present facts premises ->
      ac_nl_guard positions selection default = true ->
      guarded_attempt facts
        (eq_rule premises (gather positions selection default) output)
        (insert_exact output facts).
  Proof.
    intros facts premises positions selection default output Hpres Hguard.
    apply eq_all_equal_commits; assumption.
  Qed.

  (* (AC-nl.2) REJECT-SAFE: disagreeing slots => the guard is false => no commit, NO data
     consumed (next = facts) — the merge_substs -> None analogue, inherited from vi. *)
  Theorem ac_nl_disagree_no_commit :
    forall facts premises positions selection default output next,
      ac_nl_guard positions selection default = false ->
      guarded_attempt facts (eq_rule premises (gather positions selection default) output) next ->
      next = facts.
  Proof.
    intros facts premises positions selection default output next Hne Hatt.
    apply (eq_unequal_no_commit facts premises (gather positions selection default) output next);
      assumption.
  Qed.

  (* (AC-nl.3) THE TWO-SLOT CHARACTERIZATION: a two-occurrence variable `{x at i, x at j}`
     commits iff the selection agrees at those two slots — regardless of the bag's shuffle
     order, since the guard reads the assignment's OUTPUT (`selection`), not the bag. This is
     the concrete `x = x'` non-linear check the rho-into-rho pattern needs. *)
  Theorem ac_nl_two_slot_agree :
    forall i j selection default,
      ac_nl_guard [i; j] selection default = true <->
      nth i selection default = nth j selection default.
  Proof.
    intros i j selection default.
    unfold ac_nl_guard, gather, all_equal. simpl.
    rewrite Bool.andb_true_r.
    apply Nat.eqb_eq.
  Qed.

  (* (AC-nl.4) ORACLE AGREEMENT: the in-Rho AC guard equals the host's non-linear check on the
     gathered occurrences (both `all_equal`) — the same oracle vi certifies, over the AC
     selection. *)
  Theorem ac_nl_oracle_agreement :
    forall premises positions selection default output,
      guarded_guard (eq_rule premises (gather positions selection default) output)
      = ac_nl_guard positions selection default.
  Proof. intros. reflexivity. Qed.

  (* (AC-nl.5, Stage 4 S-AC / AC3) SPREAD-SOURCED SELECTION: the AC3 non-linear guard
     (`ac_sigma_receiver_par_with_condition`'s `Receive.condition`) reads the SELECTION — the k
     elements the native matcher picked from the SPREAD of the subject bag (`ac_match_call_par`) —
     NOT the report σ. Because EVERY theorem above quantifies over an ARBITRARY `selection`, the
     guard's commit<->agreement (AC-nl.1) and reject-safety (AC-nl.2) hold VERBATIM whether the
     selection was picked from the subject spread (S-AC) or reconstructed from the report σ: the
     guard is carrier-agnostic, so re-sourcing the bag host->spread is compatible. This makes the
     connection explicit for the `{x, x, ...rest}` shape: a spread-picked pair commits iff the two
     SPREAD-sourced elements agree — the guard is enforced ON the reducer over the subject's bag,
     the decisive content of the corrupted-σ probe
     `s_ac_nonlinear_guard_fires_in_rho_from_the_spread_not_the_report`. *)
  Theorem ac_nl_spread_selection_two_slot :
    forall (spread_selection : list Fact) default,
      ac_nl_guard [0; 1] spread_selection default = true <->
      nth 0 spread_selection default = nth 1 spread_selection default.
  Proof. intros. apply ac_nl_two_slot_agree. Qed.

  (* The guard's VALUE is a function of the selection alone, so a selection picked from the subject
     spread and an (equal) selection reconstructed from the report yield the SAME guard verdict —
     the report cannot perturb the reducer-enforced non-linear check when the picked elements match. *)
  Theorem ac_nl_guard_selection_determined :
    forall positions (spread_selection report_selection : list Fact) default,
      spread_selection = report_selection ->
      ac_nl_guard positions spread_selection default
      = ac_nl_guard positions report_selection default.
  Proof. intros positions s r default Heq. rewrite Heq. reflexivity. Qed.

  (* --------------------------------------------------------------------------------------------- *)
  (* (AC-nl.6, Stage 4 S-binder SLICE 3 — Ambient In/Out DEPTH-2 cross-level guard)                  *)
  (*                                                                                                 *)
  (* The Ambient `InRule`/`OutRule` are DEPTH-2 nested structural AC redexes whose non-linear guard   *)
  (* `EEq(M_outer, M_inner)` compares the shared ambient name `M` at TWO different nesting levels:    *)
  (* one occurrence bound at the OUTER level (the sibling `m[R]` for `InRule`, the root wrapper        *)
  (* `m[{…}]` for `OutRule`) and one bound ONE LEVEL DOWN (the inner `in(m,P)`/`out(m,P)`             *)
  (* capability's channel). The reducer flattens EVERY free variable at EVERY nesting depth into ONE   *)
  (* De Bruijn receive frame (`free_map`), so the two `M` occurrences bind DISTINCT flat slots — and   *)
  (* `gather` (AC-nl) reads the selection at SLOT POSITIONS, NOT at depth levels. Hence the cross-      *)
  (* level guard is `ac_nl_guard [i; j]` over the two `M` slots for ARBITRARY positions `i`, `j`,       *)
  (* REGARDLESS of which nesting level bound each: obligation (vi) — and its Stage-AC slot-gather       *)
  (* composition (AC-nl.1/AC-nl.2/AC-nl.3) — applies VERBATIM, with the two occurrences supplied by    *)
  (* the DEPTH-2 selection instead of a flat one. Only the depth-2 MATCH/σ/reduct correspondence        *)
  (* (`advanced_automata/InRhoAcMatchMultiset.v::NestedStructuralAcSpreadMatch`) is genuinely new; the  *)
  (* guard is reused unchanged. These corollaries state that reuse for the two-`M` cross-level shape.   *)

  (* (AC-nl.6a) THE CROSS-LEVEL TWO-SLOT CHARACTERIZATION: the depth-2 In/Out guard commits IFF the
     outer-`M` slot and the inner-`M` slot bound the SAME name — `all_equal` over the two `M` slots
     for ANY positions `i`, `j` (depth-agnostic). Directly `ac_nl_two_slot_agree`, restated to make
     explicit that the two slots may be bound at DIFFERENT nesting levels. *)
  Theorem ac_nl_cross_level_two_slot :
    forall (i j : nat) (selection : list Fact) (default : Fact),
      ac_nl_guard [i; j] selection default = true <->
      nth i selection default = nth j selection default.
  Proof. intros i j selection default. apply ac_nl_two_slot_agree. Qed.

  (* (AC-nl.6b) CROSS-LEVEL COMMIT: with the two structured-element premises present, the depth-2
     In/Out COMM commits (fires, adding the output) IFF the outer-`M` and inner-`M` slots agree — the
     `check_commit` fires. Inherits AC-nl.1 (`ac_nl_commits_iff_slots_agree`) at the two cross-level
     slots. *)
  Theorem ac_nl_cross_level_commits :
    forall facts premises i j selection default output,
      all_present facts premises ->
      nth i selection default = nth j selection default ->
      guarded_attempt facts
        (eq_rule premises (gather [i; j] selection default) output)
        (insert_exact output facts).
  Proof.
    intros facts premises i j selection default output Hpres Hagree.
    apply ac_nl_commits_iff_slots_agree; [ exact Hpres |].
    apply (proj2 (ac_nl_cross_level_two_slot i j selection default)). exact Hagree.
  Qed.

  (* (AC-nl.6c) CROSS-LEVEL REJECT-SAFE (`check_commit` rollback): disagreeing outer/inner `M` slots
     => the guard is false => NO commit and NO data consumed (next = facts) — the mismatched-name
     Ambient soup rests, so `in`/`out` cannot enter/leave a NON-matching ambient. Inherits AC-nl.2
     (`ac_nl_disagree_no_commit`); the depth-2 analogue of `AmbientOpenFiring.open_disagree_no_commit`
     for the cross-LEVEL name check. *)
  Theorem ac_nl_cross_level_reject_safe :
    forall facts premises i j selection default output next,
      nth i selection default <> nth j selection default ->
      guarded_attempt facts (eq_rule premises (gather [i; j] selection default) output) next ->
      next = facts.
  Proof.
    intros facts premises i j selection default output next Hne Hatt.
    apply (ac_nl_disagree_no_commit facts premises [i; j] selection default output next); [| exact Hatt].
    destruct (ac_nl_guard [i; j] selection default) eqn:E; [| reflexivity ].
    exfalso. apply Hne. apply (proj1 (ac_nl_cross_level_two_slot i j selection default)). exact E.
  Qed.

End AcNonLinearConsistency.

Print Assumptions ac_nl_commits_iff_slots_agree.
Print Assumptions ac_nl_disagree_no_commit.
Print Assumptions ac_nl_two_slot_agree.
Print Assumptions ac_nl_oracle_agreement.
Print Assumptions ac_nl_spread_selection_two_slot.
Print Assumptions ac_nl_guard_selection_determined.

(* ---- Stage 4 S-binder (SLICE 3, Ambient In/Out — DEPTH-2 cross-level non-linear guard) ---- *)
Print Assumptions ac_nl_cross_level_two_slot.
Print Assumptions ac_nl_cross_level_commits.
Print Assumptions ac_nl_cross_level_reject_safe.
