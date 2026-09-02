(**
  Canonical derivation rank and exact bounded parse cost.

  This theory is the refinement boundary for generated and runtime WPDA
  parsers.  Quantitative path cost and deterministic derivation order are
  deliberately separate:

  - [cost_times] is capped addition.  Instantiating [maximum_cost] with
    [u64::MAX] gives the exact operation used by [ExactParseCost], including
    finite overflow becoming the unique infinity value.
  - [Rank] is indexed by logical input position.  Every bucket has a lexical
    phase followed by a completed-production phase.  Production traces are in
    parse-tree preorder, so a completed parent precedes children that start at
    the same position.
  - child assembly is an iterative left fold over grammatical child slots.
    Runtime completion order is deliberately absent from the result.
  - delayed commits and synthetic factoring states carry no ranking authority.

  Function-valued ranks use pointwise observational equality rather than
  functional extensionality.  Consequently every theorem below is closed
  under Rocq's constructive kernel without an extensionality axiom.
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

(** * Exact bounded min-plus cost *)

Section ExactBoundedCost.

Variable maximum_cost : nat.

(** Every machine [u64] is represented by a natural no greater than the
    chosen maximum.  The maximum itself is the unique infinity value. *)
Definition valid_cost (cost : nat) : Prop := cost <= maximum_cost.

Definition cost_zero : nat := maximum_cost.
Definition cost_one : nat := 0.
Definition cost_plus (left right : nat) : nat := Nat.min left right.
Definition cost_times (left right : nat) : nat :=
  Nat.min maximum_cost (left + right).

Lemma cost_plus_valid :
  forall left right,
    valid_cost left -> valid_cost right -> valid_cost (cost_plus left right).
Proof.
  intros left right Hleft Hright.
  unfold valid_cost, cost_plus in *.
  exact (Nat.le_trans _ _ _ (Nat.le_min_l left right) Hleft).
Qed.

Lemma cost_times_valid :
  forall left right,
    valid_cost (cost_times left right).
Proof.
  intros left right.
  unfold valid_cost, cost_times.
  apply Nat.le_min_l.
Qed.

Lemma cost_plus_left_identity :
  forall cost, valid_cost cost -> cost_plus cost_zero cost = cost.
Proof.
  intros cost Hcost.
  unfold valid_cost, cost_plus, cost_zero in *.
  now apply Nat.min_r.
Qed.

Lemma cost_plus_right_identity :
  forall cost, valid_cost cost -> cost_plus cost cost_zero = cost.
Proof.
  intros cost Hcost.
  unfold valid_cost, cost_plus, cost_zero in *.
  now apply Nat.min_l.
Qed.

Lemma cost_plus_associative :
  forall first second third,
    cost_plus (cost_plus first second) third =
    cost_plus first (cost_plus second third).
Proof.
  intros first second third.
  unfold cost_plus.
  symmetry.
  apply Nat.min_assoc.
Qed.

Lemma cost_plus_commutative :
  forall left right, cost_plus left right = cost_plus right left.
Proof.
  intros left right.
  unfold cost_plus.
  apply Nat.min_comm.
Qed.

Lemma cost_plus_idempotent :
  forall cost, cost_plus cost cost = cost.
Proof.
  intro cost.
  unfold cost_plus.
  apply Nat.min_id.
Qed.

Lemma cost_times_left_identity :
  forall cost, valid_cost cost -> cost_times cost_one cost = cost.
Proof.
  intros cost Hcost.
  unfold valid_cost, cost_times, cost_one in *.
  simpl.
  now apply Nat.min_r.
Qed.

Lemma cost_times_right_identity :
  forall cost, valid_cost cost -> cost_times cost cost_one = cost.
Proof.
  intros cost Hcost.
  unfold valid_cost, cost_times, cost_one in *.
  rewrite Nat.add_0_r.
  now apply Nat.min_r.
Qed.

Lemma cost_times_left_zero :
  forall cost, cost_times cost_zero cost = cost_zero.
Proof.
  intro cost.
  unfold cost_times, cost_zero.
  apply Nat.min_l.
  lia.
Qed.

Lemma cost_times_right_zero :
  forall cost, cost_times cost cost_zero = cost_zero.
Proof.
  intro cost.
  unfold cost_times, cost_zero.
  apply Nat.min_l.
  lia.
Qed.

Lemma cost_times_commutative :
  forall left right, cost_times left right = cost_times right left.
Proof.
  intros left right.
  unfold cost_times.
  now rewrite Nat.add_comm.
Qed.

(** Capped addition remains associative even when either intermediate sum
    crosses the machine boundary.  The four cases are the two possible
    overflow decisions for the adjacent sums; no unbounded numeral is
    normalized by this proof. *)
Lemma cost_times_associative :
  forall first second third,
    cost_times (cost_times first second) third =
    cost_times first (cost_times second third).
Proof.
  intros first second third.
  unfold cost_times.
  destruct (Nat.le_gt_cases (first + second) maximum_cost)
    as [Hfirst_second | Hfirst_second];
  destruct (Nat.le_gt_cases (second + third) maximum_cost)
    as [Hsecond_third | Hsecond_third].
  - rewrite (Nat.min_r maximum_cost (first + second)) by exact Hfirst_second.
    rewrite (Nat.min_r maximum_cost (second + third)) by exact Hsecond_third.
    f_equal.
    lia.
  - rewrite (Nat.min_r maximum_cost (first + second)) by exact Hfirst_second.
    rewrite (Nat.min_l maximum_cost (second + third)) by lia.
    rewrite (Nat.min_l maximum_cost (first + second + third)) by lia.
    rewrite (Nat.min_l maximum_cost (first + maximum_cost)) by lia.
    reflexivity.
  - rewrite (Nat.min_l maximum_cost (first + second)) by lia.
    rewrite (Nat.min_r maximum_cost (second + third)) by exact Hsecond_third.
    rewrite (Nat.min_l maximum_cost (maximum_cost + third)) by lia.
    rewrite (Nat.min_l maximum_cost (first + (second + third))) by lia.
    reflexivity.
  - rewrite (Nat.min_l maximum_cost (first + second)) by lia.
    rewrite (Nat.min_l maximum_cost (second + third)) by lia.
    rewrite (Nat.min_l maximum_cost (maximum_cost + third)) by lia.
    rewrite (Nat.min_l maximum_cost (first + maximum_cost)) by lia.
    reflexivity.
Qed.

Lemma cost_times_monotone_right :
  forall prefix left right,
    left <= right -> cost_times prefix left <= cost_times prefix right.
Proof.
  intros prefix left right Hle.
  unfold cost_times.
  apply Nat.min_le_compat_l.
  lia.
Qed.

Lemma cost_times_distributes_over_plus_left :
  forall prefix left right,
    cost_times prefix (cost_plus left right) =
    cost_plus (cost_times prefix left) (cost_times prefix right).
Proof.
  intros prefix left right.
  destruct (Nat.le_ge_cases left right) as [Hle | Hge].
  - unfold cost_plus at 1.
    rewrite (Nat.min_l left right) by exact Hle.
    change (cost_times prefix left =
      Nat.min (cost_times prefix left) (cost_times prefix right)).
    symmetry.
    apply Nat.min_l.
    now apply cost_times_monotone_right.
  - unfold cost_plus at 1.
    rewrite (Nat.min_r left right) by exact Hge.
    change (cost_times prefix right =
      Nat.min (cost_times prefix left) (cost_times prefix right)).
    symmetry.
    apply Nat.min_r.
    now apply cost_times_monotone_right.
Qed.

Lemma cost_times_distributes_over_plus_right :
  forall suffix left right,
    cost_times (cost_plus left right) suffix =
    cost_plus (cost_times left suffix) (cost_times right suffix).
Proof.
  intros suffix left right.
  rewrite (cost_times_commutative (cost_plus left right) suffix).
  rewrite (cost_times_commutative left suffix).
  rewrite (cost_times_commutative right suffix).
  apply cost_times_distributes_over_plus_left.
Qed.

End ExactBoundedCost.

(** * Position-indexed derivation provenance *)

Record LexicalDecision : Type := {
  lexical_extent : nat;
  lexical_alternative : nat
}.

Record SourceRule : Type := {
  source_category : nat;
  source_declaration : nat
}.

Record PositionBucket : Type := {
  lexical_trace : list LexicalDecision;
  production_trace : list SourceRule
}.

Definition Rank : Type := nat -> PositionBucket.

Definition empty_bucket : PositionBucket :=
  {| lexical_trace := []; production_trace := [] |}.

Definition combine_bucket
    (left right : PositionBucket) : PositionBucket :=
  {| lexical_trace := lexical_trace left ++ lexical_trace right;
     production_trace := production_trace left ++ production_trace right |}.

Definition empty_rank : Rank := fun _ => empty_bucket.

Definition combine_rank (left right : Rank) : Rank :=
  fun position => combine_bucket (left position) (right position).

(** [rank_eq] is the observable equality used by the implementation
    refinement.  It avoids importing functional extensionality. *)
Definition rank_eq (left right : Rank) : Prop :=
  forall position, left position = right position.

Lemma rank_eq_reflexive : forall rank, rank_eq rank rank.
Proof. intros rank position; reflexivity. Qed.

Lemma rank_eq_symmetric :
  forall left right, rank_eq left right -> rank_eq right left.
Proof. intros left right Heq position; symmetry; apply Heq. Qed.

Lemma rank_eq_transitive :
  forall first second third,
    rank_eq first second -> rank_eq second third -> rank_eq first third.
Proof.
  intros first second third Hfirst Hsecond position.
  rewrite (Hfirst position).
  apply Hsecond.
Qed.

Lemma combine_bucket_left_identity :
  forall bucket, combine_bucket empty_bucket bucket = bucket.
Proof. intros [lexical productions]; reflexivity. Qed.

Lemma combine_bucket_right_identity :
  forall bucket, combine_bucket bucket empty_bucket = bucket.
Proof.
  intros [lexical productions].
  unfold combine_bucket, empty_bucket; simpl.
  now rewrite !app_nil_r.
Qed.

Lemma combine_bucket_associative :
  forall first second third,
    combine_bucket (combine_bucket first second) third =
    combine_bucket first (combine_bucket second third).
Proof.
  intros [first_lex first_prod] [second_lex second_prod]
    [third_lex third_prod].
  unfold combine_bucket; simpl.
  now rewrite !app_assoc.
Qed.

Lemma combine_rank_left_identity :
  forall rank, rank_eq (combine_rank empty_rank rank) rank.
Proof.
  intros rank position.
  apply combine_bucket_left_identity.
Qed.

Lemma combine_rank_right_identity :
  forall rank, rank_eq (combine_rank rank empty_rank) rank.
Proof.
  intros rank position.
  apply combine_bucket_right_identity.
Qed.

Lemma combine_rank_associative :
  forall first second third,
    rank_eq (combine_rank (combine_rank first second) third)
      (combine_rank first (combine_rank second third)).
Proof.
  intros first second third position.
  apply combine_bucket_associative.
Qed.

Definition lexical_rank
    (origin : nat) (decision : LexicalDecision) : Rank :=
  fun position =>
    if Nat.eqb position origin
    then {| lexical_trace := [decision]; production_trace := [] |}
    else empty_bucket.

Definition production_rank
    (origin : nat) (rule : SourceRule) : Rank :=
  fun position =>
    if Nat.eqb position origin
    then {| lexical_trace := []; production_trace := [rule] |}
    else empty_bucket.

Definition complete_production
    (origin : nat) (rule : SourceRule) (payload : Rank) : Rank :=
  combine_rank (production_rank origin rule) payload.

(** Child slots are consumed by [fold_left], in grammar order.  This is the
    stack-safe executable presentation intended for the Rust implementation. *)
Definition children_rank_iter (children : list Rank) : Rank :=
  fun position =>
    fold_left combine_bucket (map (fun child => child position) children)
      empty_bucket.

(** The right fold is only a compact denotational specification. *)
Definition children_rank_spec (children : list Rank) : Rank :=
  fun position =>
    fold_right combine_bucket empty_bucket
      (map (fun child => child position) children).

Lemma children_rank_iter_refines_spec :
  forall children, rank_eq (children_rank_iter children) (children_rank_spec children).
Proof.
  intros children position.
  unfold children_rank_iter, children_rank_spec.
  apply fold_symmetric.
  - intros first second third.
    symmetry.
    apply combine_bucket_associative.
  - intro bucket.
    rewrite combine_bucket_left_identity.
    symmetry.
    apply combine_bucket_right_identity.
Qed.

Definition assemble
    (origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Rank :=
  complete_production origin rule
    (combine_rank local_lexical (children_rank_iter children)).

Lemma lexical_phase_precedes_production_phase :
  forall origin decision rule payload,
    lexical_trace
      (complete_production origin rule
        (combine_rank (lexical_rank origin decision) payload) origin) =
      decision :: lexical_trace (payload origin) /\
    production_trace
      (complete_production origin rule
        (combine_rank (lexical_rank origin decision) payload) origin) =
      rule :: production_trace (payload origin).
Proof.
  intros origin decision rule payload.
  unfold complete_production, combine_rank, production_rank, lexical_rank.
  rewrite Nat.eqb_refl.
  simpl.
  split; reflexivity.
Qed.

Lemma outer_production_precedes_child_at_shared_origin :
  forall origin outer inner payload,
    production_trace
      (complete_production origin outer
        (complete_production origin inner payload) origin) =
      outer :: inner :: production_trace (payload origin).
Proof.
  intros origin outer inner payload.
  unfold complete_production, combine_rank, production_rank.
  rewrite Nat.eqb_refl.
  simpl.
  reflexivity.
Qed.

(** Commit timing is an operational fact, not derivation evidence. *)
Inductive CommitTiming : Type := EagerCommit | DelayedCommit.

Definition assemble_with_timing
    (_timing : CommitTiming)
    (origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Rank :=
  assemble origin rule local_lexical children.

Lemma commit_timing_noninterference :
  forall first_timing second_timing origin rule local_lexical children,
    rank_eq
      (assemble_with_timing first_timing origin rule local_lexical children)
      (assemble_with_timing second_timing origin rule local_lexical children).
Proof.
  intros first_timing second_timing origin rule local_lexical children.
  apply rank_eq_reflexive.
Qed.

(** A scheduler trace may record any runtime completion order.  Assembly reads
    the already-indexed grammatical slots, so the trace cannot affect rank. *)
Definition assemble_with_schedule
    (_completion_order : list nat)
    (origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children_by_slot : list Rank) : Rank :=
  assemble origin rule local_lexical children_by_slot.

Lemma scheduler_noninterference :
  forall first_schedule second_schedule origin rule local_lexical children,
    rank_eq
      (assemble_with_schedule first_schedule origin rule local_lexical children)
      (assemble_with_schedule second_schedule origin rule local_lexical children).
Proof.
  intros first_schedule second_schedule origin rule local_lexical children.
  apply rank_eq_reflexive.
Qed.

(** Every synthetic factoring node contributes the identity.  [repeat] and
    [children_rank_iter] make the claim apply to any spine depth, not merely
    to one administrative node. *)
Definition synthetic_spine_rank (depth : nat) : Rank :=
  children_rank_iter (repeat empty_rank depth).

Lemma synthetic_spine_rank_is_empty :
  forall depth, rank_eq (synthetic_spine_rank depth) empty_rank.
Proof.
  intros depth position.
  unfold synthetic_spine_rank, children_rank_iter, empty_rank.
  rewrite map_repeat.
  induction depth as [| depth IH]; simpl.
  - reflexivity.
  - rewrite combine_bucket_left_identity.
    exact IH.
Qed.

Definition unfactored
    (origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Rank :=
  assemble origin rule local_lexical children.

Definition factored
    (spine_depth origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Rank :=
  combine_rank (synthetic_spine_rank spine_depth)
    (assemble origin rule local_lexical children).

Lemma factorization_rank_transparency :
  forall spine_depth origin rule local_lexical children,
    rank_eq (factored spine_depth origin rule local_lexical children)
      (unfactored origin rule local_lexical children).
Proof.
  intros spine_depth origin rule local_lexical children position.
  unfold factored, unfactored, combine_rank.
  rewrite (synthetic_spine_rank_is_empty spine_depth position).
  apply combine_bucket_left_identity.
Qed.

(** * Total local decision order *)

Definition lexical_le (left right : LexicalDecision) : Prop :=
  lexical_extent left > lexical_extent right \/
  (lexical_extent left = lexical_extent right /\
   lexical_alternative left <= lexical_alternative right).

Definition lexical_lt (left right : LexicalDecision) : Prop :=
  lexical_extent left > lexical_extent right \/
  (lexical_extent left = lexical_extent right /\
   lexical_alternative left < lexical_alternative right).

Lemma lexical_le_reflexive : forall decision, lexical_le decision decision.
Proof. intros [extent alternative]; unfold lexical_le; simpl; lia. Qed.

Lemma lexical_le_total :
  forall left right, lexical_le left right \/ lexical_le right left.
Proof.
  intros [left_extent left_alt] [right_extent right_alt].
  unfold lexical_le; simpl; lia.
Qed.

Lemma lexical_le_antisymmetric :
  forall left right,
    lexical_le left right -> lexical_le right left -> left = right.
Proof.
  intros [left_extent left_alt] [right_extent right_alt].
  unfold lexical_le; simpl.
  intros Hleft Hright.
  assert (left_extent = right_extent /\ left_alt = right_alt) by lia.
  destruct H as [-> ->].
  reflexivity.
Qed.

Lemma lexical_le_transitive :
  forall first second third,
    lexical_le first second -> lexical_le second third -> lexical_le first third.
Proof.
  intros [first_extent first_alt] [second_extent second_alt]
    [third_extent third_alt].
  unfold lexical_le; simpl; lia.
Qed.

Lemma lexical_strict_trichotomy :
  forall left right,
    lexical_lt left right \/ left = right \/ lexical_lt right left.
Proof.
  intros [left_extent left_alt] [right_extent right_alt].
  unfold lexical_lt; simpl.
  destruct (Nat.lt_trichotomy right_extent left_extent)
    as [Hextent | [Hextent | Hextent]].
  - left; lia.
  - subst right_extent.
    destruct (Nat.lt_trichotomy left_alt right_alt)
      as [Halt | [Halt | Halt]].
    + left; lia.
    + subst right_alt; right; left; reflexivity.
    + right; right; lia.
  - right; right; lia.
Qed.

Definition production_le (left right : SourceRule) : Prop :=
  source_category left < source_category right \/
  (source_category left = source_category right /\
   source_declaration left <= source_declaration right).

Definition production_lt (left right : SourceRule) : Prop :=
  source_category left < source_category right \/
  (source_category left = source_category right /\
   source_declaration left < source_declaration right).

Lemma production_le_reflexive : forall rule, production_le rule rule.
Proof. intros [category declaration]; unfold production_le; simpl; lia. Qed.

Lemma production_le_total :
  forall left right, production_le left right \/ production_le right left.
Proof.
  intros [left_category left_rule] [right_category right_rule].
  unfold production_le; simpl; lia.
Qed.

Lemma production_le_antisymmetric :
  forall left right,
    production_le left right -> production_le right left -> left = right.
Proof.
  intros [left_category left_rule] [right_category right_rule].
  unfold production_le; simpl.
  intros Hleft Hright.
  assert (left_category = right_category /\ left_rule = right_rule) by lia.
  destruct H as [-> ->].
  reflexivity.
Qed.

Lemma production_le_transitive :
  forall first second third,
    production_le first second -> production_le second third ->
    production_le first third.
Proof.
  intros [first_category first_rule] [second_category second_rule]
    [third_category third_rule].
  unfold production_le; simpl; lia.
Qed.

Lemma production_strict_trichotomy :
  forall left right,
    production_lt left right \/ left = right \/ production_lt right left.
Proof.
  intros [left_category left_rule] [right_category right_rule].
  unfold production_lt; simpl.
  destruct (Nat.lt_trichotomy left_category right_category)
    as [Hcategory | [Hcategory | Hcategory]].
  - left; lia.
  - subst right_category.
    destruct (Nat.lt_trichotomy left_rule right_rule)
      as [Hrule | [Hrule | Hrule]].
    + left; lia.
    + subst right_rule; right; left; reflexivity.
    + right; right; lia.
  - right; right; lia.
Qed.

Fixpoint lexical_trace_le
    (left right : list LexicalDecision) : Prop :=
  match left, right with
  | [], _ => True
  | _ :: _, [] => False
  | left_head :: left_tail, right_head :: right_tail =>
      lexical_lt left_head right_head \/
      (left_head = right_head /\ lexical_trace_le left_tail right_tail)
  end.

Fixpoint production_trace_le
    (left right : list SourceRule) : Prop :=
  match left, right with
  | [], _ => True
  | _ :: _, [] => False
  | left_head :: left_tail, right_head :: right_tail =>
      production_lt left_head right_head \/
      (left_head = right_head /\ production_trace_le left_tail right_tail)
  end.

Lemma lexical_trace_order_total :
  forall left right,
    lexical_trace_le left right \/ lexical_trace_le right left.
Proof.
  induction left as [| left_head left_tail IH]; intros right.
  - left; reflexivity.
  - destruct right as [| right_head right_tail].
    + right; reflexivity.
    + simpl.
      destruct (lexical_strict_trichotomy left_head right_head)
        as [Hlt | [Heq | Hgt]].
      * left; now left.
      * subst right_head.
        destruct (IH right_tail) as [Hleft | Hright].
        -- left; right; split; [reflexivity | exact Hleft].
        -- right; right; split; [reflexivity | exact Hright].
      * right; now left.
Qed.

Lemma production_trace_order_total :
  forall left right,
    production_trace_le left right \/ production_trace_le right left.
Proof.
  induction left as [| left_head left_tail IH]; intros right.
  - left; reflexivity.
  - destruct right as [| right_head right_tail].
    + right; reflexivity.
    + simpl.
      destruct (production_strict_trichotomy left_head right_head)
        as [Hlt | [Heq | Hgt]].
      * left; now left.
      * subst right_head.
        destruct (IH right_tail) as [Hleft | Hright].
        -- left; right; split; [reflexivity | exact Hleft].
        -- right; right; split; [reflexivity | exact Hright].
      * right; now left.
Qed.

Definition bucket_le (left right : PositionBucket) : Prop :=
  lexical_trace_le (lexical_trace left) (lexical_trace right) /\
  (lexical_trace left = lexical_trace right ->
   production_trace_le (production_trace left) (production_trace right)).

Definition lexical_decision_eq_dec :
  forall left right : LexicalDecision, {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Lemma bucket_order_total :
  forall left right, bucket_le left right \/ bucket_le right left.
Proof.
  intros [left_lex left_prod] [right_lex right_prod].
  unfold bucket_le; simpl.
  destruct (lexical_trace_order_total left_lex right_lex)
    as [Hlex | Hlex].
  - destruct (list_eq_dec lexical_decision_eq_dec left_lex right_lex)
      as [Heq | Hneq].
    + subst right_lex.
      destruct (production_trace_order_total left_prod right_prod)
        as [Hprod | Hprod].
      * left; split; [exact Hlex | intros _; exact Hprod].
      * right; split.
        -- exact Hlex.
        -- intros _; exact Hprod.
    + left; split; [exact Hlex |].
      intros Heq; exfalso; now apply Hneq.
  - destruct (list_eq_dec lexical_decision_eq_dec left_lex right_lex)
      as [Heq | Hneq].
    + subst right_lex.
      destruct (production_trace_order_total left_prod right_prod)
        as [Hprod | Hprod].
      * left; split.
        -- exact Hlex.
        -- intros _; exact Hprod.
      * right; split; [exact Hlex | intros _; exact Hprod].
    + right; split; [exact Hlex |].
      intros Heq; exfalso; apply Hneq; now symmetry.
Qed.

(** * Cost/rank product without an unlawful fused semiring *)

Record Candidate : Type := {
  candidate_cost : nat;
  candidate_rank : Rank
}.

Definition candidate_eq (left right : Candidate) : Prop :=
  candidate_cost left = candidate_cost right /\
  rank_eq (candidate_rank left) (candidate_rank right).

Definition identity_candidate (maximum_cost : nat) : Candidate :=
  {| candidate_cost := cost_one;
     candidate_rank := empty_rank |}.

Definition extend_candidate
    (maximum_cost : nat) (left right : Candidate) : Candidate :=
  {| candidate_cost :=
       cost_times maximum_cost (candidate_cost left) (candidate_cost right);
     candidate_rank := combine_rank (candidate_rank left) (candidate_rank right) |}.

Lemma candidate_left_identity :
  forall maximum_cost value,
    valid_cost maximum_cost (candidate_cost value) ->
    candidate_eq (extend_candidate maximum_cost
      (identity_candidate maximum_cost) value) value.
Proof.
  intros maximum_cost [cost rank] Hvalid.
  unfold candidate_eq, extend_candidate, identity_candidate; simpl.
  split.
  - now apply cost_times_left_identity.
  - apply combine_rank_left_identity.
Qed.

Lemma candidate_right_identity :
  forall maximum_cost value,
    valid_cost maximum_cost (candidate_cost value) ->
    candidate_eq (extend_candidate maximum_cost value
      (identity_candidate maximum_cost)) value.
Proof.
  intros maximum_cost [cost rank] Hvalid.
  unfold candidate_eq, extend_candidate, identity_candidate; simpl.
  split.
  - now apply cost_times_right_identity.
  - apply combine_rank_right_identity.
Qed.

Lemma candidate_extend_associative :
  forall maximum_cost first second third,
    candidate_eq
      (extend_candidate maximum_cost
        (extend_candidate maximum_cost first second) third)
      (extend_candidate maximum_cost first
        (extend_candidate maximum_cost second third)).
Proof.
  intros maximum_cost [first_cost first_rank]
    [second_cost second_rank] [third_cost third_rank].
  unfold candidate_eq, extend_candidate; simpl.
  split.
  - apply cost_times_associative.
  - apply combine_rank_associative.
Qed.

Lemma scalar_projection_homomorphism :
  forall maximum_cost left right,
    candidate_cost (extend_candidate maximum_cost left right) =
    cost_times maximum_cost (candidate_cost left) (candidate_cost right).
Proof. reflexivity. Qed.

Definition unfactored_candidate
    (path_cost origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Candidate :=
  {| candidate_cost := path_cost;
     candidate_rank := unfactored origin rule local_lexical children |}.

Definition factored_candidate
    (maximum_cost spine_depth path_cost origin : nat) (rule : SourceRule)
    (local_lexical : Rank) (children : list Rank) : Candidate :=
  extend_candidate maximum_cost (identity_candidate maximum_cost)
    {| candidate_cost := path_cost;
       candidate_rank := factored spine_depth origin rule local_lexical children |}.

Lemma factorization_preserves_cost_and_rank :
  forall maximum_cost spine_depth path_cost origin rule local_lexical children,
    valid_cost maximum_cost path_cost ->
    candidate_eq
      (factored_candidate maximum_cost spine_depth path_cost origin rule
        local_lexical children)
      (unfactored_candidate path_cost origin rule local_lexical children).
Proof.
  intros maximum_cost spine_depth path_cost origin rule local_lexical children
    Hvalid.
  unfold factored_candidate, unfactored_candidate, extend_candidate,
    identity_candidate, candidate_eq; simpl.
  split.
  - now apply cost_times_left_identity.
  - eapply rank_eq_transitive.
    + apply combine_rank_left_identity.
    + apply factorization_rank_transparency.
Qed.

(** * Public compatibility ordering versus rank-aware ordering

    The generated facade uses one iterative realization loop for both public
    surfaces.  The legacy surface keeps the first equal-cost representative
    and performs a stable cost-only sort.  The rank-aware surface additionally
    refines equal-cost choices by complete derivation rank.  [rank_precedes]
    abstracts the already-proved total rank order: the compatibility theorem
    is intentionally independent of its implementation. *)

Definition representative_replaces
    (order_by_rank : bool) (old_cost new_cost : nat)
    (rank_precedes : Prop) : Prop :=
  new_cost < old_cost \/
  (order_by_rank = true /\ new_cost = old_cost /\ rank_precedes).

Definition facade_precedes
    (order_by_rank : bool) (left_cost right_cost : nat)
    (rank_precedes : Prop) : Prop :=
  left_cost < right_cost \/
  (left_cost = right_cost /\ order_by_rank = true /\ rank_precedes).

Lemma compatibility_replaces_iff_strictly_lower_cost :
  forall old_cost new_cost rank_precedes,
    representative_replaces false old_cost new_cost rank_precedes <->
    new_cost < old_cost.
Proof.
  intros old_cost new_cost rank_precedes.
  unfold representative_replaces.
  split.
  - intros [Hlower | [Hdisabled _]].
    + exact Hlower.
    + discriminate Hdisabled.
  - intro Hlower; now left.
Qed.

Lemma compatibility_equal_cost_keeps_first :
  forall cost rank_precedes,
    ~ representative_replaces false cost cost rank_precedes.
Proof.
  intros cost rank_precedes.
  rewrite compatibility_replaces_iff_strictly_lower_cost.
  lia.
Qed.

Lemma compatibility_precedes_iff_strictly_lower_cost :
  forall left_cost right_cost rank_precedes,
    facade_precedes false left_cost right_cost rank_precedes <->
    left_cost < right_cost.
Proof.
  intros left_cost right_cost rank_precedes.
  unfold facade_precedes.
  split.
  - intros [Hlower | [_ [Hdisabled _]]].
    + exact Hlower.
    + discriminate Hdisabled.
  - intro Hlower; now left.
Qed.

Lemma compatibility_equal_cost_is_stable_tie :
  forall cost rank_precedes,
    ~ facade_precedes false cost cost rank_precedes.
Proof.
  intros cost rank_precedes.
  rewrite compatibility_precedes_iff_strictly_lower_cost.
  lia.
Qed.

Lemma ranked_equal_cost_replaces_iff_rank_precedes :
  forall cost rank_precedes,
    representative_replaces true cost cost rank_precedes <-> rank_precedes.
Proof.
  intros cost rank_precedes.
  unfold representative_replaces.
  split.
  - intros [Hlt | [_ [_ Hrank]]].
    + lia.
    + exact Hrank.
  - intro Hrank.
    right; repeat split; assumption || reflexivity.
Qed.

Print Assumptions cost_times_associative.
Print Assumptions cost_times_distributes_over_plus_left.
Print Assumptions children_rank_iter_refines_spec.
Print Assumptions lexical_phase_precedes_production_phase.
Print Assumptions outer_production_precedes_child_at_shared_origin.
Print Assumptions scheduler_noninterference.
Print Assumptions factorization_rank_transparency.
Print Assumptions lexical_trace_order_total.
Print Assumptions production_trace_order_total.
Print Assumptions candidate_extend_associative.
Print Assumptions factorization_preserves_cost_and_rank.
Print Assumptions compatibility_replaces_iff_strictly_lower_cost.
Print Assumptions compatibility_equal_cost_keeps_first.
Print Assumptions compatibility_precedes_iff_strictly_lower_cost.
Print Assumptions compatibility_equal_cost_is_stable_tie.
Print Assumptions ranked_equal_cost_replaces_iff_rank_precedes.
