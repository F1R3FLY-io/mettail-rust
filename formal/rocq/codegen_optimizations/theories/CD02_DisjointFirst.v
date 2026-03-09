(*
 * CD02_DisjointFirst: Disjoint FIRST sets preserve deterministic dispatch.
 *
 * The dispatch layer uses FIRST sets to determine which RD rule to invoke
 * for a given lookahead token.  When FIRST sets are disjoint, dispatch is
 * deterministic (unique rule for each lookahead).  When they overlap,
 * an NFA fallback is needed.  This file proves:
 *   1. Disjoint FIRST sets => dispatch is deterministic
 *   2. Non-disjoint FIRST sets => dispatch may be ambiguous
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                                | Location
 *   -----------------------------|------------------------------------------|-----------------------------------------
 *   first_set                    | FirstSet / compute_first_sets()          | prattail/src/prediction.rs:218
 *   dispatch                     | write_category_dispatch()                | prattail/src/dispatch.rs
 *   segment_merging              | merge_safe_nt_boundaries()               | prattail/src/decision_tree.rs:782
 *   RuleInfo                     | RuleInfo struct                          | prattail/src/pipeline.rs
 *   Optimization::SegmentMerging | cost_benefit::Optimization::SegmentMerging | prattail/src/cost_benefit.rs:127
 *   first_of_rd_suffix           | first_of_rd_suffix()                     | prattail/src/prediction.rs
 *   NFA fallback                 | NFA try-all alternatives                 | prattail/src/trampoline.rs
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Hammer Require Import Tactics.
From Stdlib Require Import Setoid.

Import ListNotations.

(* ===================================================================== *)
(*  Token and Rule Model                                                   *)
(* ===================================================================== *)

Definition Token := nat.
Definition RuleId := nat.

(* FIRST set: the set of tokens that can begin a derivation of a rule *)
Definition FirstSet := Token -> Prop.

(* Decidable FIRST set membership *)
Definition FirstSetDec := Token -> bool.

(* Rule with its FIRST set.
   This model covers prefix/RD rules only.  Infix rules are dispatched
   by the Pratt binding power layer and are excluded from FIRST-set-based
   prefix dispatch (prediction.rs:237 explicitly skips infix rules).

   Trust boundary: The rwf_first fields are taken as given.  Their
   computation via fixed-point iteration (prediction.rs:218) is outside
   the scope of this proof.  We assume the FIRST sets are correctly
   computed by the Rust implementation. *)
Record RuleWithFirst := mkRWF {
  rwf_id : RuleId;
  rwf_first : FirstSet;
  rwf_first_dec : FirstSetDec;
  rwf_first_correct : forall t, rwf_first t <-> rwf_first_dec t = true
}.

(* A set of rules for a category *)
Definition RuleSet := list RuleWithFirst.

(* ===================================================================== *)
(*  Disjointness                                                           *)
(*                                                                         *)
(*  Two FIRST sets are disjoint if they share no token.                   *)
(* ===================================================================== *)

Definition disjoint (f1 f2 : FirstSet) : Prop :=
  forall t, ~ (f1 t /\ f2 t).

(* Pairwise disjointness of all rules in a set *)
Definition pairwise_disjoint (rules : RuleSet) : Prop :=
  forall i j ri rj,
    nth_error rules i = Some ri ->
    nth_error rules j = Some rj ->
    i <> j ->
    disjoint (rwf_first ri) (rwf_first rj).

(* ===================================================================== *)
(*  Dispatch Function                                                      *)
(*                                                                         *)
(*  Given a lookahead token, find the matching rule(s).                    *)
(* ===================================================================== *)

(* Find all rules whose FIRST set contains the token *)
Definition matching_rules (rules : RuleSet) (tok : Token) : list RuleId :=
  map rwf_id (filter (fun r => rwf_first_dec r tok) rules).

(* Dispatch is deterministic if exactly one rule matches *)
Definition deterministic_dispatch (rules : RuleSet) (tok : Token) : Prop :=
  length (matching_rules rules tok) <= 1.

(* Dispatch is ambiguous if more than one rule matches *)
Definition ambiguous_dispatch (rules : RuleSet) (tok : Token) : Prop :=
  length (matching_rules rules tok) > 1.

(* ===================================================================== *)
(*  Helper Lemmas                                                          *)
(* ===================================================================== *)

Lemma filter_In_iff : forall {A} (f : A -> bool) (l : list A) (x : A),
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. induction l as [| a rest IH].
  - simpl. split; [intro H; destruct H | intros [[] _]].
  - simpl. destruct (f a) eqn:Hfa.
    + simpl. rewrite IH. split.
      * intros [Heq | [Hin Hfx]].
        -- subst. split; [left; reflexivity | exact Hfa].
        -- split; [right; exact Hin | exact Hfx].
      * intros [[Heq | Hin] Hfx].
        -- subst. left. reflexivity.
        -- right. split; assumption.
    + rewrite IH. split.
      * intros [Hin Hfx]. split; [right; exact Hin | exact Hfx].
      * intros [[Heq | Hin] Hfx].
        -- subst. rewrite Hfa in Hfx. discriminate.
        -- split; assumption.
Qed.

Lemma filter_length_le : forall {A} (f : A -> bool) (l : list A),
  length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [| a rest IH].
  - simpl. lia.
  - simpl. destruct (f a); simpl; lia.
Qed.

(* If f returns false for every element, filter returns [] *)
Lemma filter_nil : forall {A} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) ->
  filter f l = [].
Proof.
  intros A f l H. induction l as [| a rest IH].
  - simpl. reflexivity.
  - simpl. rewrite (H a (or_introl eq_refl)).
    apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(* ===================================================================== *)
(*  Theorem 1: Disjoint FIRST sets => deterministic dispatch               *)
(*                                                                         *)
(*  If all FIRST sets are pairwise disjoint, then for any token, at most  *)
(*  one rule matches.                                                      *)
(* ===================================================================== *)

Theorem disjoint_first_deterministic : forall rules tok,
  pairwise_disjoint rules ->
  deterministic_dispatch rules tok.
Proof.
  intros rules tok Hdisj.
  unfold deterministic_dispatch, matching_rules.
  rewrite length_map.
  (* Proof by contradiction: if filter has >= 2 elements, pairwise disjointness is violated *)
  enough (H: length (filter (fun r => rwf_first_dec r tok) rules) <= 1) by exact H.
  (* We prove this by induction on rules *)
  induction rules as [| r rest IH].
  - simpl. lia.
  - simpl. destruct (rwf_first_dec r tok) eqn:Hrdec.
    + (* r matches tok *)
      simpl.
      (* None of the remaining rules can match tok, by disjointness *)
      assert (Hnone : filter (fun r' => rwf_first_dec r' tok) rest = []).
      { apply filter_nil.
        intros r' Hr'_in.
        destruct (rwf_first_dec r' tok) eqn:Hr'dec; try reflexivity.
        (* r' also matches tok: disjointness violated *)
        exfalso.
        apply In_nth_error in Hr'_in as [j Hj].
        assert (Hr_first : rwf_first r tok) by (apply rwf_first_correct; exact Hrdec).
        assert (Hr'_first : rwf_first r' tok) by (apply rwf_first_correct; exact Hr'dec).
        (* r is at index 0 in (r :: rest), r' is at index S j *)
        assert (Hdisj_pair : disjoint (rwf_first r) (rwf_first r')).
        { apply (Hdisj 0 (Datatypes.S j)).
          - simpl. reflexivity.
          - simpl. exact Hj.
          - lia. }
        apply (Hdisj_pair tok). split; assumption. }
      rewrite Hnone. simpl. lia.
    + (* r does not match tok *)
      apply IH.
      intros i j ri rj Hi Hj Hij.
      apply (Hdisj (Datatypes.S i) (Datatypes.S j)).
      * simpl. exact Hi.
      * simpl. exact Hj.
      * lia.
Qed.

(* ===================================================================== *)
(*  Theorem 2: Non-disjoint FIRST sets => possible ambiguity               *)
(*                                                                         *)
(*  If two rules share a token in their FIRST sets, then dispatch for     *)
(*  that token is ambiguous (the NFA fallback is needed).                  *)
(* ===================================================================== *)

Theorem overlapping_first_ambiguous : forall rules i j ri rj tok,
  nth_error rules i = Some ri ->
  nth_error rules j = Some rj ->
  i <> j ->
  rwf_first ri tok ->
  rwf_first rj tok ->
  length (matching_rules rules tok) >= 2.
Proof.
  intros rules i j ri rj tok Hi Hj Hneq Hri_tok Hrj_tok.
  unfold matching_rules. rewrite length_map.
  (* Count occurrences in filter *)
  assert (Hri_in_rules : In ri rules) by (apply nth_error_In with i; exact Hi).
  assert (Hrj_in_rules : In rj rules) by (apply nth_error_In with j; exact Hj).
  assert (Hri_dec : rwf_first_dec ri tok = true) by (apply rwf_first_correct; exact Hri_tok).
  assert (Hrj_dec : rwf_first_dec rj tok = true) by (apply rwf_first_correct; exact Hrj_tok).
  (* We use the fact that filter preserves all matching elements.
     If ri and rj are at different positions in rules, both appear in the filter. *)
  (* Key: nth_error gives us positional information.  We reconstruct the
     filter length from the number of matching positions. *)
  (* Simpler approach: construct two elements in the filter output *)
  clear Hri_in_rules Hrj_in_rules.
  revert i j Hi Hj Hneq.
  induction rules as [| r rest IHrules].
  - intros i j Hi. destruct i; simpl in Hi; discriminate.
  - intros i j Hi Hj Hneq.
    simpl.
    destruct i as [| i'], j as [| j'].
    + (* i = 0, j = 0 *) lia.
    + (* i = 0, j = S j' *)
      simpl in Hi. injection Hi as Hri_eq. subst r.
      simpl in Hj.
      rewrite Hri_dec. simpl.
      assert (Hrj_in_filter : In rj (filter (fun r => rwf_first_dec r tok) rest)).
      { apply filter_In_iff. split.
        - apply nth_error_In with j'. exact Hj.
        - exact Hrj_dec. }
      destruct (filter (fun r => rwf_first_dec r tok) rest) as [| y ys].
      * simpl in Hrj_in_filter. destruct Hrj_in_filter.
      * simpl. lia.
    + (* i = S i', j = 0 *)
      simpl in Hj. injection Hj as Hrj_eq. subst r.
      simpl in Hi.
      rewrite Hrj_dec. simpl.
      assert (Hri_in_filter : In ri (filter (fun r => rwf_first_dec r tok) rest)).
      { apply filter_In_iff. split.
        - apply nth_error_In with i'. exact Hi.
        - exact Hri_dec. }
      destruct (filter (fun r => rwf_first_dec r tok) rest) as [| y ys].
      * simpl in Hri_in_filter. destruct Hri_in_filter.
      * simpl. lia.
    + (* i = S i', j = S j' *)
      simpl in Hi, Hj.
      destruct (rwf_first_dec r tok).
      * simpl.
        enough (length (filter (fun r0 => rwf_first_dec r0 tok) rest) >= 2) by lia.
        apply IHrules with i' j'; try assumption. lia.
      * apply IHrules with i' j'; try assumption. lia.
Qed.

(* ===================================================================== *)
(*  Corollary: Disjoint FIRST sets are necessary and sufficient            *)
(*  for deterministic dispatch                                             *)
(* ===================================================================== *)

Corollary determinism_iff_disjoint : forall rules,
  pairwise_disjoint rules <->
  (forall tok, deterministic_dispatch rules tok).
Proof.
  intros rules. split.
  - (* disjoint -> deterministic *)
    intros Hdisj tok. apply disjoint_first_deterministic. exact Hdisj.
  - (* deterministic -> disjoint (contrapositive) *)
    intros Hdet. unfold pairwise_disjoint.
    intros i j ri rj Hi Hj Hneq tok [Hri_tok Hrj_tok].
    assert (Hoverlap := overlapping_first_ambiguous rules i j ri rj tok Hi Hj Hneq Hri_tok Hrj_tok).
    unfold deterministic_dispatch in Hdet.
    specialize (Hdet tok). lia.
Qed.

(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  T1: disjoint_first_deterministic                                       *)
(*      Pairwise disjoint FIRST sets => deterministic dispatch             *)
(*      (at most one rule matches any token).                              *)
(*                                                                         *)
(*  T2: overlapping_first_ambiguous                                        *)
(*      If two rules share a FIRST token, dispatch has >= 2 matches.      *)
(*                                                                         *)
(*  C1: determinism_iff_disjoint                                           *)
(*      Deterministic dispatch <-> pairwise disjoint FIRST sets.          *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(*                                                                         *)
(*  Abstraction Gaps                                                       *)
(*  1. NFA fallback: When dispatch is ambiguous (overlapping FIRST sets), *)
(*     the Rust uses an NFA try-all alternative (trampoline.rs) to test   *)
(*     all candidate rules.  This is outside the scope of this proof.     *)
(*  2. Segment merging: The decision tree (decision_tree.rs:810) uses     *)
(*     FIRST disjointness for safe merge_nt_boundaries.  We prove the    *)
(*     property but not its application in segment merging.                *)
(*  3. Infix exclusion: Infix rules are excluded from FIRST computation  *)
(*     (prediction.rs:237) and dispatched by the Pratt binding power      *)
(*     layer.  This model only covers prefix/RD rules.                     *)
(*  4. FIRST completeness: The FIRST set computation via fixed-point      *)
(*     iteration is assumed correct; we do not prove the iteration        *)
(*     converges to the true FIRST set.                                    *)
(* ===================================================================== *)
