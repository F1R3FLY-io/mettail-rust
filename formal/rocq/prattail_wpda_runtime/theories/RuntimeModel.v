(*
 * RuntimeModel: abstract model of the active Prattail WPDA runtime.
 *
 * This file intentionally models the runtime walker, not the older offline
 * WPDS saturation algorithm. It captures the proof obligations around
 * ConfigKey, DispatchKey, EquivKey, and cursor merging.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.

Inductive control : Type :=
  | PrefixDispatch
  | InfixChainIterative
  | CrossCatDelegate
  | AmbiguityFanout
  | Unwinding
  | Done
  | Error.

Lemma control_eq_dec : forall x y : control, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Inductive edge_kind : Type :=
  | EdgeGeneric
  | EdgeCrossCatProjection
      (source : nat) (bp : nat) (wrap_cat : nat) (wrap_rule : nat)
  | EdgeCrossCatLhs (source : nat)
  | EdgeCrossCatLhsReentry (source : nat)
  | EdgeOther (tag : nat).

Lemma edge_kind_eq_dec : forall x y : edge_kind, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition edge_kind_equivalent (e1 e2 : edge_kind) : Prop := e1 = e2.

Theorem cross_cat_edge_equiv_preserves_wrap :
  forall s bp wc1 wr1 wc2 wr2,
    edge_kind_equivalent
      (EdgeCrossCatProjection s bp wc1 wr1)
      (EdgeCrossCatProjection s bp wc2 wr2) ->
    wc1 = wc2 /\ wr1 = wr2.
Proof.
  intros s bp wc1 wr1 wc2 wr2 Heq.
  unfold edge_kind_equivalent in Heq.
  inversion Heq.
  split; reflexivity.
Qed.

Theorem cross_cat_lhs_edge_equiv_preserves_source :
  forall s1 s2,
    edge_kind_equivalent (EdgeCrossCatLhs s1) (EdgeCrossCatLhs s2) ->
    s1 = s2.
Proof.
  intros s1 s2 Heq.
  unfold edge_kind_equivalent in Heq.
  now inversion Heq.
Qed.

Theorem cross_cat_lhs_reentry_edge_equiv_preserves_source :
  forall s1 s2,
    edge_kind_equivalent
      (EdgeCrossCatLhsReentry s1)
      (EdgeCrossCatLhsReentry s2) ->
    s1 = s2.
Proof.
  intros s1 s2 Heq.
  unfold edge_kind_equivalent in Heq.
  now inversion Heq.
Qed.

Definition lhs_reentry_after_pop (e : edge_kind) : option edge_kind :=
  match e with
  | EdgeCrossCatLhs source => Some (EdgeCrossCatLhsReentry source)
  | _ => None
  end.

Theorem cross_cat_lhs_pop_reenters_once :
  forall source,
    lhs_reentry_after_pop (EdgeCrossCatLhs source) =
    Some (EdgeCrossCatLhsReentry source).
Proof. reflexivity. Qed.

Theorem cross_cat_lhs_reentry_is_one_shot :
  forall source,
    lhs_reentry_after_pop (EdgeCrossCatLhsReentry source) = None.
Proof. reflexivity. Qed.

Definition cross_cat_lhs_infix_evidence
    (edge : edge_kind)
    (top_cat : nat) : option nat :=
  match edge with
  | EdgeCrossCatLhs source
  | EdgeCrossCatLhsReentry source =>
      if source =? top_cat then Some source else None
  | _ => None
  end.

Definition category_changing_infix
    (source_cat result_cat : nat) : bool :=
  negb (source_cat =? result_cat).

Definition category_changing_infix_allowed
    (edge : edge_kind)
    (top_cat source_cat result_cat : nat) : bool :=
  if category_changing_infix source_cat result_cat then
    match cross_cat_lhs_infix_evidence edge top_cat with
    | Some witnessed_source => witnessed_source =? source_cat
    | None => false
    end
  else true.

Theorem same_category_infix_needs_no_lhs_evidence :
  forall edge top_cat source_cat,
    category_changing_infix_allowed edge top_cat source_cat source_cat = true.
Proof.
  intros edge top_cat source_cat.
  unfold category_changing_infix_allowed, category_changing_infix.
  now rewrite Nat.eqb_refl.
Qed.

Theorem category_changing_infix_requires_lhs_evidence :
  forall edge top_cat source_cat result_cat,
    category_changing_infix source_cat result_cat = true ->
    category_changing_infix_allowed
      edge top_cat source_cat result_cat = true ->
    cross_cat_lhs_infix_evidence edge top_cat = Some source_cat.
Proof.
  intros edge top_cat source_cat result_cat Hchanging Hallowed.
  unfold category_changing_infix_allowed in Hallowed.
  rewrite Hchanging in Hallowed.
  destruct (cross_cat_lhs_infix_evidence edge top_cat) as [witnessed |] eqn:Hev.
  - apply Nat.eqb_eq in Hallowed.
    subst witnessed.
    reflexivity.
  - discriminate Hallowed.
Qed.

Theorem generic_edge_rejects_category_changing_infix :
  forall top_cat source_cat result_cat,
    category_changing_infix source_cat result_cat = true ->
    category_changing_infix_allowed
      EdgeGeneric top_cat source_cat result_cat = false.
Proof.
  intros top_cat source_cat result_cat Hchanging.
  unfold category_changing_infix_allowed.
  now rewrite Hchanging.
Qed.

Record equiv_key : Type := {
  ek_source : nat;
  ek_bp : nat
}.

Lemma equiv_key_eq_dec : forall x y : equiv_key, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Record dispatch_key : Type := {
  dk_pos : nat;
  dk_source : nat;
  dk_bp : nat;
  dk_wrap_cat : nat;
  dk_wrap_rule : nat
}.

Lemma dispatch_key_eq_dec : forall x y : dispatch_key, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition equiv_of_dispatch (d : dispatch_key) : equiv_key :=
  {| ek_source := dk_source d; ek_bp := dk_bp d |}.

Definition edge_kind_of_dispatch (d : dispatch_key) : edge_kind :=
  EdgeCrossCatProjection
    (dk_source d) (dk_bp d) (dk_wrap_cat d) (dk_wrap_rule d).

Lemma equiv_of_dispatch_ignores_pos_and_wrap :
  forall p1 p2 s bp wc1 wr1 wc2 wr2,
    equiv_of_dispatch {| dk_pos := p1;
                         dk_source := s;
                         dk_bp := bp;
                         dk_wrap_cat := wc1;
                         dk_wrap_rule := wr1 |}
    =
    equiv_of_dispatch {| dk_pos := p2;
                         dk_source := s;
                         dk_bp := bp;
                         dk_wrap_cat := wc2;
                         dk_wrap_rule := wr2 |}.
Proof. reflexivity. Qed.

Theorem dispatch_key_equality_preserves_full_position :
  forall d1 d2,
    d1 = d2 -> dk_pos d1 = dk_pos d2.
Proof.
  intros d1 d2 Heq.
  now rewrite Heq.
Qed.

Theorem dispatch_key_distinguishes_distinct_positions :
  forall p1 p2 s bp wc wr,
    p1 <> p2 ->
    {| dk_pos := p1;
       dk_source := s;
       dk_bp := bp;
       dk_wrap_cat := wc;
       dk_wrap_rule := wr |} <>
    {| dk_pos := p2;
       dk_source := s;
       dk_bp := bp;
       dk_wrap_cat := wc;
       dk_wrap_rule := wr |}.
Proof.
  intros p1 p2 s bp wc wr Hneq Heq.
  apply Hneq.
  now inversion Heq.
Qed.

Theorem dispatch_edge_equiv_preserves_wrap :
  forall d1 d2,
    edge_kind_equivalent (edge_kind_of_dispatch d1) (edge_kind_of_dispatch d2) ->
    dk_wrap_cat d1 = dk_wrap_cat d2 /\ dk_wrap_rule d1 = dk_wrap_rule d2.
Proof.
  intros d1 d2 Heq.
  destruct d1 as [p1 s1 bp1 wc1 wr1].
  destruct d2 as [p2 s2 bp2 wc2 wr2].
  simpl in *.
  unfold edge_kind_equivalent in Heq.
  inversion Heq.
  split; reflexivity.
Qed.

Record config_key : Type := {
  ck_control : control;
  ck_node : nat;
  ck_pos : nat;
  ck_incoming_edge : option nat;
  ck_incoming_edge_stack : nat;
  ck_collection_depth : nat;
  ck_origin : option equiv_key;
  ck_sppf_top : option nat;
  ck_lex_alt : nat;
  ck_weight_src : nat;
  ck_weight_rule : nat;
  ck_lex_stamp : option nat
}.

Lemma config_key_eq_dec : forall x y : config_key, {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply control_eq_dec;
    try apply equiv_key_eq_dec;
    try (decide equality; apply Nat.eq_dec);
    try (decide equality; apply equiv_key_eq_dec).
Defined.

Record cursor : Type := {
  cur_config : config_key;
  cur_origin : option dispatch_key;
  cur_weight : nat
}.

Definition config_with_lex_stamp
    (k : config_key)
    (stamp : nat) : config_key :=
  {| ck_control := ck_control k;
     ck_node := ck_node k;
     ck_pos := ck_pos k;
     ck_incoming_edge := ck_incoming_edge k;
     ck_incoming_edge_stack := ck_incoming_edge_stack k;
     ck_collection_depth := ck_collection_depth k;
     ck_origin := ck_origin k;
     ck_sppf_top := ck_sppf_top k;
     ck_lex_alt := ck_lex_alt k;
     ck_weight_src := ck_weight_src k;
     ck_weight_rule := ck_weight_rule k;
     ck_lex_stamp := Some stamp |}.

Record lex_provenance : Type := {
  lp_alt : nat;
  lp_src : nat;
  lp_rule : nat
}.

Definition cohort_shell_lex_from_parent
    (parent_weight : lex_provenance) : lex_provenance :=
  {| lp_alt := lp_alt parent_weight;
     lp_src := lp_src parent_weight;
     lp_rule := lp_rule parent_weight |}.

Theorem cohort_shell_preserves_parent_lex_provenance :
  forall parent_weight,
    cohort_shell_lex_from_parent parent_weight = parent_weight.
Proof.
  intros [alt src rule].
  reflexivity.
Qed.

Definition lex_fork_child_config
    (k : config_key)
    (stamp next_pos : nat) : config_key :=
  {| ck_control := ck_control k;
     ck_node := ck_node k;
     ck_pos := next_pos;
     ck_incoming_edge := ck_incoming_edge k;
     ck_incoming_edge_stack := ck_incoming_edge_stack k;
     ck_collection_depth := ck_collection_depth k;
     ck_origin := ck_origin k;
     ck_sppf_top := ck_sppf_top k;
     ck_lex_alt := ck_lex_alt k;
     ck_weight_src := ck_weight_src k;
     ck_weight_rule := ck_weight_rule k;
     ck_lex_stamp := Some stamp |}.

Inductive lex_alt_operator_action : Type :=
  | LexAltPostfixOperator
  | LexAltInfixOperator
  | LexAltMixfixOperator.

Definition runtime_lex_alt_operator_child
    (_action : lex_alt_operator_action)
    (parent : config_key)
    (stamp next_pos : nat) : config_key :=
  lex_fork_child_config parent stamp next_pos.

Theorem lex_alt_operator_child_advances_to_next_pos :
  forall action parent stamp next_pos,
    ck_pos
      (runtime_lex_alt_operator_child action parent stamp next_pos) =
    next_pos.
Proof. reflexivity. Qed.

Theorem lex_alt_operator_child_records_stamp :
  forall action parent stamp next_pos,
    ck_lex_stamp
      (runtime_lex_alt_operator_child action parent stamp next_pos) =
    Some stamp.
Proof. reflexivity. Qed.

Definition cohort_return_frame_with_lex_stamp
    (parent : config_key)
    (stamp : nat) : config_key :=
  config_with_lex_stamp parent stamp.

Theorem paused_cohort_return_frame_records_lex_stamp :
  forall parent stamp,
    ck_lex_stamp
      (cohort_return_frame_with_lex_stamp parent stamp) =
    Some stamp.
Proof. reflexivity. Qed.

Definition lex_fork_only_secondary_survived
    (branches_nonempty primary_survived : bool) : bool :=
  andb branches_nonempty (negb primary_survived).

Definition lex_fork_fall_through
    (branches_empty primary_only_survived : bool) : bool :=
  orb branches_empty primary_only_survived.

Theorem lex_fork_only_secondary_when_nonempty_without_primary :
  lex_fork_only_secondary_survived true false = true.
Proof. reflexivity. Qed.

Theorem lex_fork_does_not_fall_through_for_only_secondary :
  lex_fork_fall_through false false = false.
Proof. reflexivity. Qed.

Inductive prefix_rule_kind : Type :=
  | PrefixAtomic
  | PrefixBinder
  | PrefixCrossCatProjection.

Record prefix_rule_info : Type := {
  pri_rule : nat;
  pri_kind : prefix_rule_kind
}.

Inductive prefix_branch : Type :=
  | PrefixBranch (info : prefix_rule_info).

Definition emit_prefix_branches
    (infos : list prefix_rule_info) : list prefix_branch :=
  map PrefixBranch infos.

Theorem emit_prefix_branches_preserves_members :
  forall infos info,
    In info infos ->
    In (PrefixBranch info) (emit_prefix_branches infos).
Proof.
  intros infos info Hin.
  unfold emit_prefix_branches.
  now apply in_map.
Qed.

Theorem emit_prefix_branches_preserves_length :
  forall infos,
    length (emit_prefix_branches infos) = length infos.
Proof.
  intros infos.
  unfold emit_prefix_branches.
  apply length_map.
Qed.

Theorem emit_prefix_branches_preserves_two_same_trigger_rules :
  forall first second,
    emit_prefix_branches [first; second] =
    [PrefixBranch first; PrefixBranch second].
Proof. reflexivity. Qed.

Record projection_delegate_key : Type := {
  pdk_rule : nat;
  pdk_source : nat
}.

Lemma projection_delegate_key_eq_dec :
  forall x y : projection_delegate_key, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition insert_projection_delegate
    (d : projection_delegate_key)
    (ds : list projection_delegate_key) : list projection_delegate_key :=
  if in_dec projection_delegate_key_eq_dec d ds then ds else d :: ds.

Fixpoint dedup_projection_delegates
    (ds : list projection_delegate_key) : list projection_delegate_key :=
  match ds with
  | [] => []
  | d :: rest => insert_projection_delegate d (dedup_projection_delegates rest)
  end.

Inductive projection_branch : Type :=
  | ProjectionDelegateBranch (key : projection_delegate_key).

Definition emit_projection_delegate_branches
    (ds : list projection_delegate_key) : list projection_branch :=
  map ProjectionDelegateBranch (dedup_projection_delegates ds).

Theorem emit_projection_delegate_branches_dedups_duplicate :
  forall d,
    emit_projection_delegate_branches [d; d] =
    [ProjectionDelegateBranch d].
Proof.
  intros d.
  unfold emit_projection_delegate_branches.
  simpl.
  unfold insert_projection_delegate.
  destruct (in_dec projection_delegate_key_eq_dec d []) as [Hin_empty | _].
  - inversion Hin_empty.
  - simpl.
    destruct (projection_delegate_key_eq_dec d d) as [_ | Hneq].
    + reflexivity.
    + contradiction.
Qed.

Record transparent_projection : Type := {
  tp_source_cat : nat;
  tp_target_cat : nat;
  tp_wrap_cat : nat;
  tp_wrap_rule : nat
}.

Definition transparent_projection_matches
    (source_cat target_cat : nat)
    (projection : transparent_projection) : bool :=
  (tp_source_cat projection =? source_cat) &&
    (tp_target_cat projection =? target_cat).

Definition guard_projection_evidence
    (projections : list transparent_projection)
    (source_cat target_cat : nat) : bool :=
  existsb (transparent_projection_matches source_cat target_cat) projections.

Inductive guarded_literal_rewrite : Type :=
  | GuardNoRewrite (cat : nat)
  | GuardProjected (projection : transparent_projection).

Definition guarded_literal_rewrite_category
    (rewrite : guarded_literal_rewrite) : nat :=
  match rewrite with
  | GuardNoRewrite cat => cat
  | GuardProjected projection => tp_target_cat projection
  end.

Definition guarded_literal_accepts_top
    (projections : list transparent_projection)
    (required_top_cat : option nat)
    (top_cat : nat) : bool :=
  match required_top_cat with
  | None => true
  | Some required =>
      (top_cat =? required) ||
        guard_projection_evidence projections top_cat required
  end.

Definition guarded_literal_stack_rewrites
    (projections : list transparent_projection)
    (required_top_cat : option nat)
    (top_cat : nat) : list guarded_literal_rewrite :=
  match required_top_cat with
  | None => [GuardNoRewrite top_cat]
  | Some required =>
      if top_cat =? required
      then [GuardNoRewrite top_cat]
      else
        map GuardProjected
          (filter (transparent_projection_matches top_cat required) projections)
  end.

Theorem guarded_literal_accepts_direct_category :
  forall projections required,
    guarded_literal_accepts_top
      projections (Some required) required = true.
Proof.
  intros projections required.
  unfold guarded_literal_accepts_top.
  now rewrite Nat.eqb_refl.
Qed.

Theorem guarded_literal_mismatch_requires_projection_evidence :
  forall projections top_cat required,
    top_cat <> required ->
    guarded_literal_accepts_top
      projections (Some required) top_cat = true ->
    guard_projection_evidence projections top_cat required = true.
Proof.
  intros projections top_cat required Hneq Haccept.
  unfold guarded_literal_accepts_top in Haccept.
  assert (Heq : (top_cat =? required) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heq in Haccept.
  simpl in Haccept.
  exact Haccept.
Qed.

Theorem guarded_literal_rejects_mismatch_without_projection_evidence :
  forall projections top_cat required,
    top_cat <> required ->
    guard_projection_evidence projections top_cat required = false ->
    guarded_literal_accepts_top
      projections (Some required) top_cat = false.
Proof.
  intros projections top_cat required Hneq Hno_evidence.
  unfold guarded_literal_accepts_top.
  assert (Heq : (top_cat =? required) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  now rewrite Heq, Hno_evidence.
Qed.

Theorem guarded_literal_accepts_projection_evidence :
  forall projections top_cat required,
    guard_projection_evidence projections top_cat required = true ->
    guarded_literal_accepts_top
      projections (Some required) top_cat = true.
Proof.
  intros projections top_cat required Hevidence.
  unfold guarded_literal_accepts_top.
  destruct (top_cat =? required); simpl.
  - reflexivity.
  - exact Hevidence.
Qed.

Theorem guarded_literal_rewrite_categories_are_required :
  forall projections top_cat required rewrite,
    In rewrite
      (guarded_literal_stack_rewrites projections (Some required) top_cat) ->
    guarded_literal_rewrite_category rewrite = required.
Proof.
  intros projections top_cat required rewrite Hin.
  unfold guarded_literal_stack_rewrites in Hin.
  destruct (top_cat =? required) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst rewrite. simpl. exact Heq.
    + contradiction.
  - apply in_map_iff in Hin as [projection [Hrewrite Hin_filter]].
    subst rewrite.
    apply filter_In in Hin_filter as [_ Hmatches].
    unfold transparent_projection_matches in Hmatches.
    apply andb_prop in Hmatches as [_ Htarget].
    simpl.
    now apply Nat.eqb_eq.
Qed.

Theorem guarded_literal_enumerates_every_projection :
  forall projections top_cat required projection,
    top_cat <> required ->
    In projection projections ->
    transparent_projection_matches top_cat required projection = true ->
    In (GuardProjected projection)
      (guarded_literal_stack_rewrites projections (Some required) top_cat).
Proof.
  intros projections top_cat required projection Hneq Hin Hmatches.
  unfold guarded_literal_stack_rewrites.
  assert (Heq : (top_cat =? required) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heq.
  apply in_map.
  apply filter_In.
  split; assumption.
Qed.

Theorem guarded_literal_projected_rewrite_has_evidence :
  forall projections top_cat required projection,
    top_cat <> required ->
    In (GuardProjected projection)
      (guarded_literal_stack_rewrites projections (Some required) top_cat) ->
    In projection projections /\
      transparent_projection_matches top_cat required projection = true.
Proof.
  intros projections top_cat required projection Hneq Hin.
  unfold guarded_literal_stack_rewrites in Hin.
  assert (Heq : (top_cat =? required) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heq in Hin.
  apply in_map_iff in Hin as [projection' [Hprojected Hin_filter]].
  inversion Hprojected.
  subst projection'.
  now apply filter_In in Hin_filter.
Qed.

Theorem guarded_literal_projected_rewrite_implies_acceptance :
  forall projections top_cat required projection,
    top_cat <> required ->
    In (GuardProjected projection)
      (guarded_literal_stack_rewrites projections (Some required) top_cat) ->
    guarded_literal_accepts_top
      projections (Some required) top_cat = true.
Proof.
  intros projections top_cat required projection Hneq Hin.
  apply guarded_literal_projected_rewrite_has_evidence in Hin as [Hin_projection Hmatches].
  - apply guarded_literal_accepts_projection_evidence.
    unfold guard_projection_evidence.
    apply existsb_exists.
    exists projection.
    split; assumption.
  - exact Hneq.
Qed.

Definition config_with_incoming_edge_stack
    (k : config_key)
    (stack : nat) : config_key :=
  {| ck_control := ck_control k;
     ck_node := ck_node k;
     ck_pos := ck_pos k;
     ck_incoming_edge := ck_incoming_edge k;
     ck_incoming_edge_stack := stack;
     ck_collection_depth := ck_collection_depth k;
     ck_origin := ck_origin k;
     ck_sppf_top := ck_sppf_top k;
     ck_lex_alt := ck_lex_alt k;
     ck_weight_src := ck_weight_src k;
     ck_weight_rule := ck_weight_rule k;
     ck_lex_stamp := ck_lex_stamp k |}.

Theorem config_with_incoming_edge_stack_sets_stack :
  forall k stack,
    ck_incoming_edge_stack
      (config_with_incoming_edge_stack k stack) =
    stack.
Proof. reflexivity. Qed.

Theorem distinct_incoming_edge_stacks_prevent_config_merge :
  forall k1 k2,
    ck_incoming_edge_stack k1 <> ck_incoming_edge_stack k2 ->
    k1 <> k2.
Proof.
  intros k1 k2 Hdiff Heq.
  apply Hdiff.
  now rewrite Heq.
Qed.

Inductive predecessor_kind : Type :=
  | PredCategoryEntry
  | PredGroupingMarker
  | PredOther
  | PredRoot.

Inductive category_entry_post_pop_state : Type :=
  | PostPopInfixLoop
  | PostPopUnwinding
  | PostPopGroupingClosePreserving.

Definition category_entry_grouping_request
    (close_paren inner_matches : bool) : category_entry_post_pop_state :=
  if close_paren && inner_matches
  then PostPopGroupingClosePreserving
  else PostPopUnwinding.

Definition resolve_category_entry_post_pop
    (exact_pred : predecessor_kind)
    (requested : category_entry_post_pop_state)
    : category_entry_post_pop_state :=
  match exact_pred with
  | PredCategoryEntry => PostPopInfixLoop
  | PredRoot => PostPopInfixLoop
  | PredGroupingMarker =>
      match requested with
      | PostPopGroupingClosePreserving => PostPopGroupingClosePreserving
      | _ => PostPopUnwinding
      end
  | PredOther => PostPopUnwinding
  end.

Definition resolve_category_entry_post_pop_with_ignored_first
    (_first_pred exact_pred : predecessor_kind)
    (requested : category_entry_post_pop_state)
    : category_entry_post_pop_state :=
  resolve_category_entry_post_pop exact_pred requested.

Theorem exact_grouping_predecessor_preserves_grouping_request :
  resolve_category_entry_post_pop
    PredGroupingMarker
    (category_entry_grouping_request true true) =
  PostPopGroupingClosePreserving.
Proof. reflexivity. Qed.

Theorem non_grouping_predecessor_rejects_grouping_request :
  forall exact_pred requested,
    exact_pred <> PredGroupingMarker ->
    resolve_category_entry_post_pop exact_pred requested <>
    PostPopGroupingClosePreserving.
Proof.
  intros exact_pred requested Hnot_grouping Heq.
  destruct exact_pred; simpl in Heq; try discriminate.
  contradiction.
Qed.

Theorem category_entry_post_pop_ignores_first_gss_predecessor :
  forall first_left first_right exact_pred requested,
    resolve_category_entry_post_pop_with_ignored_first
      first_left exact_pred requested =
    resolve_category_entry_post_pop_with_ignored_first
      first_right exact_pred requested.
Proof. reflexivity. Qed.

Theorem first_predecessor_cannot_suppress_exact_grouping :
  forall first_pred,
    resolve_category_entry_post_pop_with_ignored_first
      first_pred
      PredGroupingMarker
      (category_entry_grouping_request true true) =
    PostPopGroupingClosePreserving.
Proof. reflexivity. Qed.

Record parse_alt_key : Type := {
  pak_surface : nat;
  pak_semantic : nat
}.

Definition parse_alt_equivalent (a b : parse_alt_key) : Prop := a = b.

Theorem same_surface_distinct_semantic_prevents_alt_merge :
  forall surface sem1 sem2,
    sem1 <> sem2 ->
    ~ parse_alt_equivalent
        {| pak_surface := surface; pak_semantic := sem1 |}
        {| pak_surface := surface; pak_semantic := sem2 |}.
Proof.
  intros surface sem1 sem2 Hneq Heq.
  unfold parse_alt_equivalent in Heq.
  apply Hneq.
  now inversion Heq.
Qed.

Theorem lex_fork_falls_through_when_no_branches :
  lex_fork_fall_through true false = true.
Proof. reflexivity. Qed.

Theorem lex_fork_falls_through_when_only_primary_survived :
  lex_fork_fall_through false true = true.
Proof. reflexivity. Qed.

Definition observable (c : cursor) : config_key := cur_config c.

Definition origin_consistent (c : cursor) : Prop :=
  match cur_origin c, ck_origin (cur_config c) with
  | None, None => True
  | Some d, Some e => equiv_of_dispatch d = e
  | _, _ => False
  end.

Definition same_observable (c1 c2 : cursor) : Prop :=
  observable c1 = observable c2.

Definition config_deterministic (step : cursor -> list cursor) : Prop :=
  forall c1 c2,
    origin_consistent c1 ->
    origin_consistent c2 ->
    same_observable c1 c2 ->
    map observable (step c1) = map observable (step c2).

Theorem quotient_step_sound :
  forall (step : cursor -> list cursor) c1 c2,
    config_deterministic step ->
    origin_consistent c1 ->
    origin_consistent c2 ->
    same_observable c1 c2 ->
    map observable (step c1) = map observable (step c2).
Proof.
  intros step c1 c2 Hdet Hc1 Hc2 Hsame.
  exact (Hdet c1 c2 Hc1 Hc2 Hsame).
Qed.

Definition insert_config (k : config_key) (ks : list config_key) : list config_key :=
  if in_dec config_key_eq_dec k ks then ks else k :: ks.

Fixpoint config_keys (cs : list cursor) : list config_key :=
  match cs with
  | [] => []
  | c :: rest => insert_config (observable c) (config_keys rest)
  end.

Lemma in_insert_config :
  forall k x xs,
    In k (insert_config x xs) <-> k = x \/ In k xs.
Proof.
  intros k x xs.
  unfold insert_config.
  destruct (in_dec config_key_eq_dec x xs) as [Hin | Hnot].
  - split; intro H.
    + right. exact H.
    + destruct H as [H | H].
      * subst. exact Hin.
      * exact H.
  - simpl. split; intro H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
Qed.

Lemma config_keys_spec :
  forall cs k,
    In k (config_keys cs) <->
    exists c, In c cs /\ observable c = k.
Proof.
  induction cs as [| c rest IH]; intros k.
  - simpl. split; intro H.
    + contradiction.
    + destruct H as [c [Hin _]]. contradiction.
  - simpl. rewrite in_insert_config. rewrite IH.
    split; intro H.
    + destruct H as [H | [c' [Hin Hobs]]].
      * exists c. split.
        -- left. reflexivity.
        -- symmetry. exact H.
      * exists c'. split.
        -- right. exact Hin.
        -- exact Hobs.
    + destruct H as [c' [[Hhead | Hin] Hobs]].
      * rewrite <- Hhead in Hobs. left. symmetry. exact Hobs.
      * right. exists c'. split; assumption.
Qed.

Lemma insert_config_length_le_succ :
  forall k ks,
    length (insert_config k ks) <= S (length ks).
Proof.
  intros k ks.
  unfold insert_config.
  destruct (in_dec config_key_eq_dec k ks); simpl; lia.
Qed.

Lemma config_keys_length_le :
  forall cs,
    length (config_keys cs) <= length cs.
Proof.
  induction cs as [| c rest IH].
  - simpl. lia.
  - simpl.
    eapply Nat.le_trans.
    + apply insert_config_length_le_succ.
    + lia.
Qed.

Inductive cursor_bounding_mode : Type :=
  | CursorUnbounded
  | CursorBeamSize (budget : nat)
  | CursorAmbiguityBudget (budget : nat).

Definition cursor_bound_budget
    (mode : cursor_bounding_mode) : option nat :=
  match mode with
  | CursorUnbounded => None
  | CursorBeamSize budget => Some budget
  | CursorAmbiguityBudget budget => Some budget
  end.

Definition cursor_bound_check
    (mode : cursor_bounding_mode)
    (actual_frontier_len : nat) : option (nat * nat) :=
  match cursor_bound_budget mode with
  | None => None
  | Some budget =>
      if budget <? actual_frontier_len
      then Some (budget, actual_frontier_len)
      else None
  end.

Definition cursor_bound_frontier_len
    (_mode : cursor_bounding_mode)
    (actual_frontier_len : nat) : nat :=
  actual_frontier_len.

Inductive lazy_frontier_frame : Type :=
  | LazyConcrete
  | LazyCohort (members : nat).

Definition frame_logical_cursor_count (frame : lazy_frontier_frame) : nat :=
  match frame with
  | LazyConcrete => 1
  | LazyCohort members => members
  end.

Fixpoint lazy_logical_frontier_len
    (frames : list lazy_frontier_frame) : nat :=
  match frames with
  | [] => 0
  | frame :: rest =>
      frame_logical_cursor_count frame + lazy_logical_frontier_len rest
  end.

Definition frame_materialized_cursor_count
    (frame : lazy_frontier_frame) : list nat :=
  match frame with
  | LazyConcrete => [0]
  | LazyCohort members => repeat 0 members
  end.

Definition materialized_frontier_len
    (frames : list lazy_frontier_frame) : nat :=
  length (flat_map frame_materialized_cursor_count frames).

Definition lazy_cursor_bound_check
    (mode : cursor_bounding_mode)
    (frames : list lazy_frontier_frame) : option (nat * nat) :=
  cursor_bound_check mode (lazy_logical_frontier_len frames).

Definition lazy_bound_physical_frontier_len
    (_mode : cursor_bounding_mode)
    (frames : list lazy_frontier_frame) : nat :=
  length frames.

Lemma lazy_logical_frontier_len_matches_materialized :
  forall frames,
    lazy_logical_frontier_len frames =
    materialized_frontier_len frames.
Proof.
  induction frames as [|frame rest IH].
  - reflexivity.
  - simpl.
    unfold materialized_frontier_len in *.
    simpl.
    rewrite length_app.
    rewrite <- IH.
    destruct frame; simpl.
    + lia.
    + rewrite repeat_length. lia.
Qed.

Theorem lazy_budget_check_matches_eager_materialization :
  forall mode frames,
    lazy_cursor_bound_check mode frames =
    cursor_bound_check mode (materialized_frontier_len frames).
Proof.
  intros mode frames.
  unfold lazy_cursor_bound_check.
  rewrite lazy_logical_frontier_len_matches_materialized.
  reflexivity.
Qed.

Theorem lazy_budget_overflow_preserves_physical_frontier :
  forall budget frames,
    budget < lazy_logical_frontier_len frames ->
    lazy_cursor_bound_check (CursorAmbiguityBudget budget) frames =
      Some (budget, lazy_logical_frontier_len frames) /\
    lazy_bound_physical_frontier_len
      (CursorAmbiguityBudget budget)
      frames =
    length frames.
Proof.
  intros budget frames Hlt.
  split.
  - unfold lazy_cursor_bound_check, cursor_bound_check, cursor_bound_budget.
    assert (Hltb : (budget <? lazy_logical_frontier_len frames) = true).
    { apply Nat.ltb_lt. exact Hlt. }
    now rewrite Hltb.
  - reflexivity.
Qed.

Theorem calculator_cast_frontier_budget_sound :
  (forall actual,
      cursor_bound_check CursorUnbounded actual = None) /\
  (forall budget actual,
      actual <= budget ->
      cursor_bound_check (CursorAmbiguityBudget budget) actual = None) /\
  (forall budget actual,
      budget < actual ->
      cursor_bound_check (CursorAmbiguityBudget budget) actual =
        Some (budget, actual)).
Proof.
  split.
  - intro actual.
    reflexivity.
  - split.
    + intros budget actual Hle.
      unfold cursor_bound_check, cursor_bound_budget.
      assert (Hgeb : (budget <? actual) = false).
      { apply Nat.ltb_ge. exact Hle. }
      now rewrite Hgeb.
    + intros budget actual Hlt.
      unfold cursor_bound_check, cursor_bound_budget.
      assert (Hltb : (budget <? actual) = true).
      { apply Nat.ltb_lt. exact Hlt. }
      now rewrite Hltb.
Qed.

Inductive eoi_cursor_class : Type :=
  | EoiAccepting
  | EoiPrefix
  | EoiPrematureAccepted
  | EoiDead.

Definition eoi_accepting_class (class : eoi_cursor_class) : bool :=
  match class with
  | EoiAccepting => true
  | _ => false
  end.

Definition eoi_prefix_class (class : eoi_cursor_class) : bool :=
  match class with
  | EoiPrefix => true
  | _ => false
  end.

Definition eoi_survives_premature_filter
    (class : eoi_cursor_class) : bool :=
  match class with
  | EoiPrematureAccepted => false
  | _ => true
  end.

Fixpoint count_eoi_classes
    (predicate : eoi_cursor_class -> bool)
    (classes : list eoi_cursor_class) : nat :=
  match classes with
  | [] => 0
  | class :: rest =>
      (if predicate class then 1 else 0) +
      count_eoi_classes predicate rest
  end.

Inductive lazy_eoi_frame : Type :=
  | LazyEoiConcrete (class : eoi_cursor_class)
  | LazyEoiCohort (members : list eoi_cursor_class).

Definition materialized_eoi_frame
    (frame : lazy_eoi_frame) : list eoi_cursor_class :=
  match frame with
  | LazyEoiConcrete class => [class]
  | LazyEoiCohort members => members
  end.

Definition lazy_eoi_frame_count
    (predicate : eoi_cursor_class -> bool)
    (frame : lazy_eoi_frame) : nat :=
  match frame with
  | LazyEoiConcrete class => if predicate class then 1 else 0
  | LazyEoiCohort members => count_eoi_classes predicate members
  end.

Fixpoint lazy_eoi_count
    (predicate : eoi_cursor_class -> bool)
    (frames : list lazy_eoi_frame) : nat :=
  match frames with
  | [] => 0
  | frame :: rest =>
      lazy_eoi_frame_count predicate frame +
      lazy_eoi_count predicate rest
  end.

Definition materialized_eoi_count
    (predicate : eoi_cursor_class -> bool)
    (frames : list lazy_eoi_frame) : nat :=
  count_eoi_classes predicate (flat_map materialized_eoi_frame frames).

Fixpoint first_eoi_class_offset
    (predicate : eoi_cursor_class -> bool)
    (classes : list eoi_cursor_class) : option nat :=
  match classes with
  | [] => None
  | class :: rest =>
      if predicate class then Some 0
      else option_map S (first_eoi_class_offset predicate rest)
  end.

Definition lazy_eoi_frame_first_offset
    (predicate : eoi_cursor_class -> bool)
    (frame : lazy_eoi_frame) : option nat :=
  first_eoi_class_offset predicate (materialized_eoi_frame frame).

Fixpoint lazy_eoi_first_offset
    (predicate : eoi_cursor_class -> bool)
    (frames : list lazy_eoi_frame) : option nat :=
  match frames with
  | [] => None
  | frame :: rest =>
      match lazy_eoi_frame_first_offset predicate frame with
      | Some offset => Some offset
      | None =>
          option_map
            (Nat.add (length (materialized_eoi_frame frame)))
            (lazy_eoi_first_offset predicate rest)
      end
  end.

Definition materialized_eoi_first_offset
    (predicate : eoi_cursor_class -> bool)
    (frames : list lazy_eoi_frame) : option nat :=
  first_eoi_class_offset predicate (flat_map materialized_eoi_frame frames).

Definition lazy_eoi_first_accepting_offset
    (frames : list lazy_eoi_frame) : option nat :=
  lazy_eoi_first_offset eoi_accepting_class frames.

Definition materialized_eoi_first_accepting_offset
    (frames : list lazy_eoi_frame) : option nat :=
  materialized_eoi_first_offset eoi_accepting_class frames.

Definition lazy_eoi_physical_frontier_len
    (frames : list lazy_eoi_frame) : nat :=
  length frames.

Lemma count_eoi_classes_app :
  forall predicate xs ys,
    count_eoi_classes predicate (xs ++ ys) =
    count_eoi_classes predicate xs +
    count_eoi_classes predicate ys.
Proof.
  intros predicate xs ys.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH. now destruct (predicate x).
Qed.

Lemma first_eoi_class_offset_app :
  forall predicate xs ys,
    first_eoi_class_offset predicate (xs ++ ys) =
    match first_eoi_class_offset predicate xs with
    | Some offset => Some offset
    | None =>
        option_map
          (Nat.add (length xs))
          (first_eoi_class_offset predicate ys)
    end.
Proof.
  intros predicate xs ys.
  induction xs as [|x xs IH].
  - simpl.
    destruct (first_eoi_class_offset predicate ys) as [offset |];
      reflexivity.
  - simpl.
    destruct (predicate x) eqn:Hpred.
    + reflexivity.
    + rewrite IH.
      destruct (first_eoi_class_offset predicate xs) as [offset |].
      * reflexivity.
      * destruct (first_eoi_class_offset predicate ys) as [offset |];
          reflexivity.
Qed.

Lemma lazy_eoi_frame_count_matches_materialized :
  forall predicate frame,
    lazy_eoi_frame_count predicate frame =
    count_eoi_classes predicate (materialized_eoi_frame frame).
Proof.
  intros predicate frame.
  destruct frame as [class | members].
  - simpl. now destruct (predicate class).
  - reflexivity.
Qed.

Theorem lazy_eoi_count_matches_eager_materialization :
  forall predicate frames,
    lazy_eoi_count predicate frames =
    materialized_eoi_count predicate frames.
Proof.
  intros predicate frames.
  induction frames as [|frame rest IH].
  - reflexivity.
  - simpl.
    unfold materialized_eoi_count in *.
    simpl.
    rewrite count_eoi_classes_app.
    rewrite <- (lazy_eoi_frame_count_matches_materialized predicate frame).
    rewrite <- IH.
    reflexivity.
Qed.

Theorem lazy_eoi_accepting_count_matches_eager_materialization :
  forall frames,
    lazy_eoi_count eoi_accepting_class frames =
    materialized_eoi_count eoi_accepting_class frames.
Proof.
  apply lazy_eoi_count_matches_eager_materialization.
Qed.

Theorem lazy_eoi_prefix_count_matches_eager_materialization :
  forall frames,
    lazy_eoi_count eoi_prefix_class frames =
    materialized_eoi_count eoi_prefix_class frames.
Proof.
  apply lazy_eoi_count_matches_eager_materialization.
Qed.

Theorem lazy_eoi_survivor_count_matches_eager_materialization :
  forall frames,
    lazy_eoi_count eoi_survives_premature_filter frames =
    materialized_eoi_count eoi_survives_premature_filter frames.
Proof.
  apply lazy_eoi_count_matches_eager_materialization.
Qed.

Theorem lazy_eoi_first_offset_matches_eager_materialization :
  forall predicate frames,
    lazy_eoi_first_offset predicate frames =
    materialized_eoi_first_offset predicate frames.
Proof.
  intros predicate frames.
  unfold materialized_eoi_first_offset.
  induction frames as [|frame rest IH].
  - reflexivity.
  - simpl.
    unfold lazy_eoi_frame_first_offset.
    rewrite first_eoi_class_offset_app.
    destruct
      (first_eoi_class_offset predicate (materialized_eoi_frame frame))
      as [offset |].
    + reflexivity.
    + now rewrite IH.
Qed.

Theorem lazy_eoi_first_accepting_offset_matches_eager_materialization :
  forall frames,
    lazy_eoi_first_accepting_offset frames =
    materialized_eoi_first_accepting_offset frames.
Proof.
  intros frames.
  unfold lazy_eoi_first_accepting_offset,
    materialized_eoi_first_accepting_offset.
  apply lazy_eoi_first_offset_matches_eager_materialization.
Qed.

Theorem lazy_eoi_snapshot_preserves_physical_frontier :
  forall frames,
    lazy_eoi_physical_frontier_len frames = length frames.
Proof. reflexivity. Qed.

Theorem beam_size_matches_ambiguity_budget :
  forall budget actual_frontier_len,
    cursor_bound_check
      (CursorBeamSize budget)
      actual_frontier_len =
    cursor_bound_check
      (CursorAmbiguityBudget budget)
      actual_frontier_len.
Proof. reflexivity. Qed.

Theorem beam_size_overflow_reports_actual :
  forall budget actual_frontier_len,
    budget < actual_frontier_len ->
    cursor_bound_check
      (CursorBeamSize budget)
      actual_frontier_len =
    Some (budget, actual_frontier_len).
Proof.
  intros budget actual_frontier_len Hlt.
  unfold cursor_bound_check, cursor_bound_budget.
  assert (Hltb : (budget <? actual_frontier_len) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  reflexivity.
Qed.

Theorem beam_size_within_budget_reports_no_error :
  forall budget actual_frontier_len,
    actual_frontier_len <= budget ->
    cursor_bound_check
      (CursorBeamSize budget)
      actual_frontier_len =
    None.
Proof.
  intros budget actual_frontier_len Hle.
  unfold cursor_bound_check, cursor_bound_budget.
  assert (Hgeb : (budget <? actual_frontier_len) = false).
  { apply Nat.ltb_ge. exact Hle. }
  rewrite Hgeb.
  reflexivity.
Qed.

Theorem cursor_bound_preserves_frontier_length :
  forall mode actual_frontier_len,
    cursor_bound_frontier_len mode actual_frontier_len =
    actual_frontier_len.
Proof. reflexivity. Qed.

Theorem beam_size_preserves_frontier_length :
  forall budget actual_frontier_len,
    cursor_bound_frontier_len
      (CursorBeamSize budget)
      actual_frontier_len =
    actual_frontier_len.
Proof. reflexivity. Qed.

Theorem beam_size_overflow_preserves_frontier_and_reports_actual :
  forall budget actual_frontier_len,
    budget < actual_frontier_len ->
    cursor_bound_frontier_len
      (CursorBeamSize budget)
      actual_frontier_len =
    actual_frontier_len /\
    cursor_bound_check
      (CursorBeamSize budget)
      actual_frontier_len =
    Some (budget, actual_frontier_len).
Proof.
  intros budget actual_frontier_len Hlt.
  split.
  - apply beam_size_preserves_frontier_length.
  - apply beam_size_overflow_reports_actual.
    exact Hlt.
Qed.

Inductive orphan_revival_result : Type :=
  | OrphanRevivalIdle
  | OrphanRevivalInjected (n : nat)
  | OrphanRevivalBudgetExceeded (budget actual : nat).

Definition bounded_orphan_revival
    (budget actual_orphans : nat) : orphan_revival_result :=
  if budget <? actual_orphans
  then OrphanRevivalBudgetExceeded budget actual_orphans
  else if actual_orphans =? 0
       then OrphanRevivalIdle
       else OrphanRevivalInjected actual_orphans.

Definition old_acceptance_guarded_orphan_revival
    (budget actual_orphans : nat)
    (parse_already_succeeds : bool) : orphan_revival_result :=
  if (budget <? actual_orphans) && parse_already_succeeds
  then OrphanRevivalBudgetExceeded budget actual_orphans
  else if actual_orphans =? 0
       then OrphanRevivalIdle
       else OrphanRevivalInjected actual_orphans.

Definition orphan_revival_accepts
    (_r : orphan_revival_result) : bool :=
  false.

Definition orphan_revival_remaining_evidence
    (actual_orphans : nat)
    (r : orphan_revival_result) : nat :=
  match r with
  | OrphanRevivalBudgetExceeded _ _ => actual_orphans
  | _ => 0
  end.

Theorem orphan_revival_overflow_reports_budget :
  forall budget actual_orphans,
    budget < actual_orphans ->
    bounded_orphan_revival budget actual_orphans =
      OrphanRevivalBudgetExceeded budget actual_orphans.
Proof.
  intros budget actual_orphans Hlt.
  unfold bounded_orphan_revival.
  assert (Hltb : (budget <? actual_orphans) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  reflexivity.
Qed.

Theorem old_acceptance_guarded_orphan_revival_can_inject_over_budget :
  old_acceptance_guarded_orphan_revival 256 257 false =
    OrphanRevivalInjected 257.
Proof. reflexivity. Qed.

Theorem orphan_revival_budget_exceeded_is_not_acceptance :
  forall budget actual_orphans,
    orphan_revival_accepts
      (OrphanRevivalBudgetExceeded budget actual_orphans) = false.
Proof. reflexivity. Qed.

Theorem orphan_revival_budget_exceeded_preserves_unresolved_evidence :
  forall budget actual_orphans,
    orphan_revival_remaining_evidence actual_orphans
      (OrphanRevivalBudgetExceeded budget actual_orphans) =
    actual_orphans.
Proof. reflexivity. Qed.

Inductive cohort_cache_cap_result : Type :=
  | CohortCacheWithinCap
  | CohortCacheBudgetExceeded (budget actual : nat).

Definition bounded_cohort_cache_cap
    (budget attempted : nat) : cohort_cache_cap_result :=
  if budget <? attempted
  then CohortCacheBudgetExceeded budget attempted
  else CohortCacheWithinCap.

Definition cohort_cache_cap_accepts
    (_r : cohort_cache_cap_result) : bool :=
  false.

Definition cohort_cache_unresolved_evidence
    (attempted : nat)
    (r : cohort_cache_cap_result) : nat :=
  match r with
  | CohortCacheBudgetExceeded _ _ => attempted
  | CohortCacheWithinCap => 0
  end.

Theorem cohort_cache_overflow_reports_budget :
  forall budget attempted,
    budget < attempted ->
    bounded_cohort_cache_cap budget attempted =
      CohortCacheBudgetExceeded budget attempted.
Proof.
  intros budget attempted Hlt.
  unfold bounded_cohort_cache_cap.
  assert (Hltb : (budget <? attempted) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  reflexivity.
Qed.

Theorem cohort_cache_overflow_is_not_acceptance :
  forall budget attempted,
    cohort_cache_cap_accepts
      (CohortCacheBudgetExceeded budget attempted) = false.
Proof. reflexivity. Qed.

Theorem cohort_cache_overflow_preserves_unresolved_evidence :
  forall budget attempted,
    cohort_cache_unresolved_evidence attempted
      (CohortCacheBudgetExceeded budget attempted) =
    attempted.
Proof. reflexivity. Qed.

Inductive snapshot_insert_result : Type :=
  | SnapshotAppended
  | SnapshotDuplicate
  | SnapshotOverflow (budget actual : nat).

Definition bounded_snapshot_insert
    (budget : nat)
    (seen_duplicate : bool)
    (current_count : nat) : snapshot_insert_result :=
  if seen_duplicate then SnapshotDuplicate
  else if budget <? S current_count
       then SnapshotOverflow budget (S current_count)
       else SnapshotAppended.

Definition snapshot_count_after_insert
    (budget : nat)
    (seen_duplicate : bool)
    (current_count : nat) : nat :=
  match bounded_snapshot_insert budget seen_duplicate current_count with
  | SnapshotAppended => S current_count
  | SnapshotDuplicate => current_count
  | SnapshotOverflow _ _ => current_count
  end.

Theorem dispatch_snapshot_quotient_sound :
  forall budget current_count,
    bounded_snapshot_insert budget true current_count = SnapshotDuplicate /\
    snapshot_count_after_insert budget true current_count = current_count /\
    (current_count < budget ->
       bounded_snapshot_insert budget false current_count = SnapshotAppended /\
       snapshot_count_after_insert budget false current_count = S current_count) /\
    (budget <= current_count ->
       bounded_snapshot_insert budget false current_count =
         SnapshotOverflow budget (S current_count)).
Proof.
  intros budget current_count.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * intro Hlt.
        split.
        -- unfold bounded_snapshot_insert.
           assert (Hgeb : (budget <? S current_count) = false).
           { apply Nat.ltb_ge. lia. }
           now rewrite Hgeb.
        -- unfold snapshot_count_after_insert.
           assert (Hinsert :
             bounded_snapshot_insert budget false current_count =
               SnapshotAppended).
           {
             unfold bounded_snapshot_insert.
             assert (Hgeb : (budget <? S current_count) = false).
             { apply Nat.ltb_ge. lia. }
             now rewrite Hgeb.
           }
           now rewrite Hinsert.
      * intro Hle.
      unfold bounded_snapshot_insert.
        assert (Hltb : (budget <? S current_count) = true).
        { apply Nat.ltb_lt. lia. }
        now rewrite Hltb.
Qed.

Inductive realization_cap_result : Type :=
  | RealizationWithinCap
  | RealizationBudgetExceeded (budget actual : nat).

Definition bounded_realization_cap
    (budget actual_terms : nat) : realization_cap_result :=
  if budget <? actual_terms
  then RealizationBudgetExceeded budget actual_terms
  else RealizationWithinCap.

Definition realization_cap_accepts
    (_r : realization_cap_result) : bool :=
  false.

Definition realization_unresolved_evidence
    (actual_terms : nat)
    (r : realization_cap_result) : nat :=
  match r with
  | RealizationBudgetExceeded _ _ => actual_terms
  | RealizationWithinCap => 0
  end.

Theorem realization_cap_overflow_reports_budget :
  forall budget actual_terms,
    budget < actual_terms ->
    bounded_realization_cap budget actual_terms =
      RealizationBudgetExceeded budget actual_terms.
Proof.
  intros budget actual_terms Hlt.
  unfold bounded_realization_cap.
  assert (Hltb : (budget <? actual_terms) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  reflexivity.
Qed.

Theorem realization_cap_within_budget_reports_no_error :
  forall budget actual_terms,
    actual_terms <= budget ->
    bounded_realization_cap budget actual_terms =
      RealizationWithinCap.
Proof.
  intros budget actual_terms Hle.
  unfold bounded_realization_cap.
  assert (Hgeb : (budget <? actual_terms) = false).
  { apply Nat.ltb_ge. exact Hle. }
  rewrite Hgeb.
  reflexivity.
Qed.

Theorem realization_cap_probe_reports_overflow :
  forall budget,
    bounded_realization_cap budget (S budget) =
      RealizationBudgetExceeded budget (S budget).
Proof.
  intro budget.
  apply realization_cap_overflow_reports_budget.
  lia.
Qed.

Theorem realization_cap_overflow_is_not_acceptance :
  forall budget actual_terms,
    realization_cap_accepts
      (RealizationBudgetExceeded budget actual_terms) = false.
Proof. reflexivity. Qed.

Theorem realization_cap_overflow_preserves_unresolved_evidence :
  forall budget actual_terms,
    realization_unresolved_evidence actual_terms
      (RealizationBudgetExceeded budget actual_terms) =
    actual_terms.
Proof. reflexivity. Qed.

Inductive semantic_realization_result : Type :=
  | SemanticRealizationWithin (distinct_count raw_count : nat)
  | SemanticRealizationDistinctBudgetExceeded (budget actual : nat)
  | SemanticRealizationRawBudgetExceeded (budget actual : nat).

Definition bounded_semantic_realization_insert
    (distinct_budget raw_budget : nat)
    (seen_duplicate : bool)
    (distinct_count raw_count : nat) : semantic_realization_result :=
  if raw_budget <? S raw_count
  then SemanticRealizationRawBudgetExceeded raw_budget (S raw_count)
  else if seen_duplicate
       then SemanticRealizationWithin distinct_count (S raw_count)
       else if distinct_budget <? S distinct_count
            then SemanticRealizationDistinctBudgetExceeded
                   distinct_budget
                   (S distinct_count)
            else SemanticRealizationWithin
                   (S distinct_count)
                   (S raw_count).

Theorem semantic_realization_budget_sound :
  forall distinct_budget raw_budget distinct_count raw_count,
    raw_count < raw_budget ->
    bounded_semantic_realization_insert
      distinct_budget raw_budget true distinct_count raw_count =
      SemanticRealizationWithin distinct_count (S raw_count) /\
    (distinct_count < distinct_budget ->
       bounded_semantic_realization_insert
         distinct_budget raw_budget false distinct_count raw_count =
         SemanticRealizationWithin (S distinct_count) (S raw_count)) /\
    (distinct_budget <= distinct_count ->
       bounded_semantic_realization_insert
         distinct_budget raw_budget false distinct_count raw_count =
         SemanticRealizationDistinctBudgetExceeded
           distinct_budget
           (S distinct_count)).
Proof.
  intros distinct_budget raw_budget distinct_count raw_count Hraw.
  assert (Hraw_ok : (raw_budget <? S raw_count) = false).
  { apply Nat.ltb_ge. lia. }
  repeat split.
  - unfold bounded_semantic_realization_insert.
    now rewrite Hraw_ok.
  - intro Hdistinct.
    unfold bounded_semantic_realization_insert.
    rewrite Hraw_ok.
    assert (Hdistinct_ok : (distinct_budget <? S distinct_count) = false).
    { apply Nat.ltb_ge. lia. }
    now rewrite Hdistinct_ok.
  - intro Hdistinct.
    unfold bounded_semantic_realization_insert.
    rewrite Hraw_ok.
    assert (Hdistinct_exceeded :
      (distinct_budget <? S distinct_count) = true).
    { apply Nat.ltb_lt. lia. }
    now rewrite Hdistinct_exceeded.
Qed.

Definition realized_terms_for_roots (roots : list nat) : list nat :=
  flat_map (fun count => repeat 0 count) roots.

Definition realized_weights_for_roots (roots : list nat) : list nat :=
  flat_map (fun count => repeat 1 count) roots.

Fixpoint lazy_prefix_realized_terms
    (budget : nat)
    (packing_counts : list nat) : list nat :=
  match budget, packing_counts with
  | 0, _ => []
  | _, [] => []
  | _, count :: rest =>
      let terms := firstn budget (repeat 0 count) in
      terms ++
      lazy_prefix_realized_terms
        (budget - length terms)
        rest
  end.

Theorem lazy_prefix_realization_matches_eager_prefix :
  forall budget packing_counts,
    lazy_prefix_realized_terms budget packing_counts =
    firstn budget (realized_terms_for_roots packing_counts).
Proof.
  intros budget packing_counts.
  revert budget.
  induction packing_counts as [|count rest IH].
  - intro budget. now destruct budget.
  - intro budget. destruct budget as [|budget'].
    + reflexivity.
    + cbn [lazy_prefix_realized_terms].
      change (firstn (S budget') (realized_terms_for_roots (count :: rest))) with
        (firstn (S budget') (repeat 0 count ++ realized_terms_for_roots rest)).
      rewrite (@firstn_app nat (S budget') (repeat 0 count) (realized_terms_for_roots rest)).
      f_equal.
      assert (
        S budget' - length (firstn (S budget') (repeat 0 count)) =
        S budget' - length (repeat 0 count)
      ) as Hremaining.
      {
        rewrite length_firstn.
        lia.
      }
      rewrite Hremaining.
      apply IH.
Qed.

Theorem lazy_prefix_realization_length_bounded :
  forall budget packing_counts,
    length (lazy_prefix_realized_terms budget packing_counts) <= budget.
Proof.
  intros budget packing_counts.
  rewrite lazy_prefix_realization_matches_eager_prefix.
  rewrite length_firstn.
  lia.
Qed.

Theorem lazy_prefix_realization_zero_demand :
  forall packing_counts,
    lazy_prefix_realized_terms 0 packing_counts = [].
Proof.
  intro packing_counts.
  now destruct packing_counts.
Qed.

Theorem lazy_prefix_realization_skips_tail_after_cap_filled :
  forall budget first_count rest,
    budget <= first_count ->
    lazy_prefix_realized_terms budget (first_count :: rest) =
    firstn budget (repeat 0 first_count).
Proof.
  intros budget first_count rest Hfills.
  destruct budget as [|budget'].
  - reflexivity.
  - cbn [lazy_prefix_realized_terms].
    remember (firstn (S budget') (repeat 0 first_count)) as terms.
    assert (Hlen : length terms = S budget').
    {
      subst terms.
      rewrite length_firstn.
      rewrite repeat_length.
      lia.
    }
    rewrite Hlen.
    rewrite Nat.sub_diag.
    rewrite lazy_prefix_realization_zero_demand.
    apply app_nil_r.
Qed.

Inductive weighted_facade_result : Type :=
  | WeightedFacadeAccepted (terms weights : list nat)
  | WeightedFacadeBudgetExceeded (budget actual : nat).

Definition bounded_weighted_facade_realization
    (budget : nat)
    (roots : list nat) : weighted_facade_result :=
  let terms := realized_terms_for_roots roots in
  if budget <? length terms
  then WeightedFacadeBudgetExceeded budget (S budget)
  else WeightedFacadeAccepted terms (realized_weights_for_roots roots).

Lemma realized_terms_weights_for_roots_parallel :
  forall roots,
    length (realized_terms_for_roots roots) =
    length (realized_weights_for_roots roots).
Proof.
  induction roots as [|count rest IH].
  - reflexivity.
  - simpl.
    rewrite !length_app.
    rewrite !repeat_length.
    lia.
Qed.

Theorem weighted_facade_accepted_terms_weights_parallel :
  forall budget roots terms weights,
    bounded_weighted_facade_realization budget roots =
      WeightedFacadeAccepted terms weights ->
    length terms = length weights.
Proof.
  intros budget roots terms weights Haccepted.
  unfold bounded_weighted_facade_realization in Haccepted.
  destruct (budget <? length (realized_terms_for_roots roots)) eqn:Hcap.
  - discriminate Haccepted.
  - inversion Haccepted; subst.
    apply realized_terms_weights_for_roots_parallel.
Qed.

Theorem weighted_facade_probe_reports_structured_overflow :
  forall budget roots,
    budget < length (realized_terms_for_roots roots) ->
    bounded_weighted_facade_realization budget roots =
      WeightedFacadeBudgetExceeded budget (S budget).
Proof.
  intros budget roots Hlt.
  unfold bounded_weighted_facade_realization.
  assert (Hltb : (budget <? length (realized_terms_for_roots roots)) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hltb.
  reflexivity.
Qed.

Definition span_anchored_coercion_jobs
    (direct : bool)
    (coercions : list nat) : list (option nat) :=
  if direct then [None] else map Some coercions.

Definition crosswrap_drain_key : Type :=
  (nat * nat * nat * option nat)%type.

Definition make_crosswrap_drain_key
    (dispatch_key symbol_id member_id : nat)
    (coercion : option nat) : crosswrap_drain_key :=
  (dispatch_key, symbol_id, member_id, coercion).

Theorem span_anchored_coercion_jobs_preserve_count :
  forall coercions,
    length (span_anchored_coercion_jobs false coercions) =
    length coercions.
Proof.
  intros coercions.
  unfold span_anchored_coercion_jobs.
  rewrite length_map.
  reflexivity.
Qed.

Theorem span_anchored_coercion_jobs_preserve_membership :
  forall coercions coercion,
    In coercion coercions ->
    In (Some coercion) (span_anchored_coercion_jobs false coercions).
Proof.
  intros coercions coercion Hin.
  unfold span_anchored_coercion_jobs.
  apply in_map.
  exact Hin.
Qed.

Theorem crosswrap_drain_key_distinguishes_coercions :
  forall dispatch_key symbol_id member_id left right,
    left <> right ->
    make_crosswrap_drain_key dispatch_key symbol_id member_id (Some left) <>
    make_crosswrap_drain_key dispatch_key symbol_id member_id (Some right).
Proof.
  intros dispatch_key symbol_id member_id left right Hneq Hkey.
  inversion Hkey.
  contradiction.
Qed.

Inductive token_class : Type :=
  | OpenDelimiter
  | CloseDelimiter
  | OtherToken.

Definition is_open_delimiter (t : token_class) : bool :=
  match t with
  | OpenDelimiter => true
  | _ => false
  end.

Definition is_close_delimiter (t : token_class) : bool :=
  match t with
  | CloseDelimiter => true
  | _ => false
  end.

Definition token_window
    (tokens : list token_class)
    (start finish : nat) : list token_class :=
  firstn (finish - start) (skipn start tokens).

Definition all_open_prefix (tokens : list token_class) (finish : nat) : bool :=
  (finish <=? length tokens) &&
    forallb is_open_delimiter (firstn finish tokens).

Definition all_close_window
    (tokens : list token_class)
    (start finish : nat) : bool :=
  (finish <=? length tokens) &&
    forallb is_close_delimiter (token_window tokens start finish).

Definition eoi_accepts_semantic_root
    (tokens : list token_class)
    (root_lo root_hi cursor_pos : nat) : bool :=
  (cursor_pos <=? length tokens) &&
    ((root_hi =? cursor_pos) ||
      ((root_hi <? cursor_pos) &&
        (all_open_prefix tokens root_lo &&
         all_close_window tokens root_hi cursor_pos))).

Theorem same_span_accepts_without_delimiter_windows :
  forall tokens root_lo root_hi,
    root_hi <= length tokens ->
    eoi_accepts_semantic_root tokens root_lo root_hi root_hi = true.
Proof.
  intros tokens root_lo root_hi Hlen.
  unfold eoi_accepts_semantic_root.
  assert (Hlenb : (root_hi <=? length tokens) = true).
  { apply Nat.leb_le. exact Hlen. }
  rewrite Hlenb, Nat.eqb_refl.
  reflexivity.
Qed.

Theorem delimiter_suffix_accept_requires_open_prefix :
  forall tokens root_lo root_hi cursor_pos,
    root_hi <> cursor_pos ->
    eoi_accepts_semantic_root tokens root_lo root_hi cursor_pos = true ->
    all_open_prefix tokens root_lo = true.
Proof.
  intros tokens root_lo root_hi cursor_pos Hneq Haccept.
  unfold eoi_accepts_semantic_root in Haccept.
  apply andb_prop in Haccept as [_ Haccept].
  assert (Heq : (root_hi =? cursor_pos) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heq in Haccept.
  simpl in Haccept.
  apply andb_prop in Haccept as [_ Hwindows].
  apply andb_prop in Hwindows as [Hprefix _].
  exact Hprefix.
Qed.

Theorem delimiter_suffix_rejects_non_open_prefix :
  forall tokens root_lo root_hi cursor_pos,
    root_hi < cursor_pos ->
    all_open_prefix tokens root_lo = false ->
    eoi_accepts_semantic_root tokens root_lo root_hi cursor_pos = false.
Proof.
  intros tokens root_lo root_hi cursor_pos Hlt Hprefix.
  unfold eoi_accepts_semantic_root.
  assert (Heq : (root_hi =? cursor_pos) = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hltb : (root_hi <? cursor_pos) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Heq, Hltb, Hprefix.
  destruct (cursor_pos <=? length tokens); reflexivity.
Qed.

Theorem delimiter_wrapped_root_accepts :
  forall tokens root_lo root_hi cursor_pos,
    cursor_pos <= length tokens ->
    root_hi < cursor_pos ->
    all_open_prefix tokens root_lo = true ->
    all_close_window tokens root_hi cursor_pos = true ->
    eoi_accepts_semantic_root tokens root_lo root_hi cursor_pos = true.
Proof.
  intros tokens root_lo root_hi cursor_pos Hpos Hlt Hprefix Hsuffix.
  unfold eoi_accepts_semantic_root.
  assert (Hposb : (cursor_pos <=? length tokens) = true).
  { apply Nat.leb_le. exact Hpos. }
  assert (Heq : (root_hi =? cursor_pos) = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hltb : (root_hi <? cursor_pos) = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hposb, Heq, Hltb, Hprefix, Hsuffix.
  reflexivity.
Qed.

Example malformed_prefix_is_rejected :
  eoi_accepts_semantic_root
    [OpenDelimiter; OtherToken; CloseDelimiter] 2 2 3 = false.
Proof. reflexivity. Qed.

Example past_token_source_is_rejected :
  eoi_accepts_semantic_root
    [OpenDelimiter; OtherToken; CloseDelimiter] 3 4 4 = false.
Proof. reflexivity. Qed.

Example missing_close_suffix_is_rejected :
  eoi_accepts_semantic_root
    [OpenDelimiter; OtherToken] 1 2 3 = false.
Proof. reflexivity. Qed.

Inductive token_position_space : Type :=
  | LinearTokenPositions
  | NonlinearNodePositions.

Definition runtime_eoi_accepts_semantic_root
    (space : token_position_space)
    (tokens : list token_class)
    (root_lo root_hi cursor_pos : nat) : bool :=
  match space with
  | LinearTokenPositions =>
      eoi_accepts_semantic_root tokens root_lo root_hi cursor_pos
  | NonlinearNodePositions =>
      true
  end.

Theorem linear_runtime_eoi_acceptance_is_delimiter_window_acceptance :
  forall tokens root_lo root_hi cursor_pos,
    runtime_eoi_accepts_semantic_root
      LinearTokenPositions tokens root_lo root_hi cursor_pos =
    eoi_accepts_semantic_root tokens root_lo root_hi cursor_pos.
Proof. reflexivity. Qed.

Theorem nonlinear_node_positions_do_not_scan_numeric_token_windows :
  forall tokens root_lo root_hi cursor_pos,
    runtime_eoi_accepts_semantic_root
      NonlinearNodePositions tokens root_lo root_hi cursor_pos = true.
Proof. reflexivity. Qed.

Definition merge_weight (w1 w2 : nat) : nat := w1 + w2.

Lemma merge_weight_zero_l :
  forall w,
    merge_weight 0 w = w.
Proof.
  unfold merge_weight. intros. lia.
Qed.

Lemma merge_weight_zero_r :
  forall w,
    merge_weight w 0 = w.
Proof.
  unfold merge_weight. intros. lia.
Qed.

Lemma merge_weight_comm :
  forall w1 w2,
    merge_weight w1 w2 = merge_weight w2 w1.
Proof.
  unfold merge_weight. intros. lia.
Qed.

Lemma merge_weight_assoc :
  forall w1 w2 w3,
    merge_weight (merge_weight w1 w2) w3 =
    merge_weight w1 (merge_weight w2 w3).
Proof.
  unfold merge_weight. intros. lia.
Qed.

Record weighted_frontier_item : Type := {
  wfi_weight : nat;
  wfi_sequence : nat;
  wfi_node : nat
}.

Definition frontier_minimal
    (picked : weighted_frontier_item)
    (frontier : list weighted_frontier_item) : Prop :=
  In picked frontier /\
  forall item,
    In item frontier ->
    wfi_weight picked <= wfi_weight item.

Definition lazy_force_step
    (frontier forced : list weighted_frontier_item) : Prop :=
  length forced <= 1 /\
  forall item,
    In item forced ->
    In item frontier.

Definition priority_force_step
    (frontier forced : list weighted_frontier_item) : Prop :=
  lazy_force_step frontier forced /\
  forall picked,
    forced = [picked] ->
    frontier_minimal picked frontier.

Theorem singleton_force_is_lazy :
  forall frontier picked,
    In picked frontier ->
    lazy_force_step frontier [picked].
Proof.
  intros frontier picked Hin.
  unfold lazy_force_step.
  split.
  - simpl. lia.
  - intros item Hitem.
    simpl in Hitem.
    destruct Hitem as [Heq | Hnil].
    + now rewrite <- Heq.
    + contradiction.
Qed.

Theorem empty_force_is_lazy :
  forall frontier,
    lazy_force_step frontier [].
Proof.
  intros frontier.
  unfold lazy_force_step.
  split.
  - simpl. lia.
  - intros item Hitem. contradiction.
Qed.

Theorem priority_force_no_better_remaining :
  forall frontier picked item,
    priority_force_step frontier [picked] ->
    In item frontier ->
    wfi_weight picked <= wfi_weight item.
Proof.
  intros frontier picked item Hstep Hin.
  unfold priority_force_step in Hstep.
  destruct Hstep as [_ Hmin].
  specialize (Hmin picked eq_refl).
  unfold frontier_minimal in Hmin.
  destruct Hmin as [_ Hle].
  now apply Hle.
Qed.

Theorem lower_sequence_breaks_equal_weight_tie :
  forall left right,
    wfi_weight left = wfi_weight right ->
    wfi_sequence left <= wfi_sequence right ->
    wfi_weight left <= wfi_weight right /\
    wfi_sequence left <= wfi_sequence right.
Proof.
  intros left right Hweight Hseq.
  split.
  - rewrite Hweight. lia.
  - exact Hseq.
Qed.

Theorem priority_force_preserves_ambiguity_until_demand :
  forall frontier forced item,
    priority_force_step frontier forced ->
    In item forced ->
    In item frontier.
Proof.
  intros frontier forced item Hstep Hin.
  unfold priority_force_step in Hstep.
  destruct Hstep as [Hlazy _].
  unfold lazy_force_step in Hlazy.
  destruct Hlazy as [_ Hmember].
  now apply Hmember.
Qed.

Record lex_dag_node_model : Type := {
  ldn_primary : option nat;
  ldn_secondaries : list nat
}.

Definition eager_secondary_observation
    (nodes : list lex_dag_node_model)
    (pos : nat) : list nat :=
  match nth_error nodes pos with
  | Some node => ldn_secondaries node
  | None => []
  end.

Definition valid_secondary_cache
    (nodes : list lex_dag_node_model)
    (cache : list (option (list nat))) : Prop :=
  forall pos alts,
    nth_error cache pos = Some (Some alts) ->
    alts = eager_secondary_observation nodes pos.

Definition lazy_secondary_observation
    (nodes : list lex_dag_node_model)
    (cache : list (option (list nat)))
    (pos : nat) : list nat :=
  match nth_error cache pos with
  | Some (Some alts) => alts
  | _ => eager_secondary_observation nodes pos
  end.

Theorem lazy_secondary_observation_matches_eager :
  forall nodes cache pos,
    valid_secondary_cache nodes cache ->
    lazy_secondary_observation nodes cache pos =
    eager_secondary_observation nodes pos.
Proof.
  intros nodes cache pos Hvalid.
  unfold lazy_secondary_observation.
  destruct (nth_error cache pos) as [[alts|]|] eqn:Hcache.
  - now apply Hvalid with (pos := pos).
  - reflexivity.
  - reflexivity.
Qed.

Definition primary_observation
    (nodes : list lex_dag_node_model)
    (pos eof_kind : nat) : option nat :=
  match nth_error nodes pos with
  | Some node =>
      Some
        (match ldn_primary node with
         | Some kind => kind
         | None => eof_kind
         end)
  | None => None
  end.

Definition lazy_primary_observation
    (nodes : list lex_dag_node_model)
    (_cache : list (option (list nat)))
    (pos eof_kind : nat) : option nat :=
  primary_observation nodes pos eof_kind.

Theorem lazy_primary_observation_ignores_secondary_cache :
  forall nodes cache_a cache_b pos eof_kind,
    lazy_primary_observation nodes cache_a pos eof_kind =
    lazy_primary_observation nodes cache_b pos eof_kind.
Proof. reflexivity. Qed.

Definition flat_lex_demand_for_dag_facade (dag_has_ambiguity : bool) : nat :=
  if dag_has_ambiguity then 0 else 1.

Theorem ambiguous_dag_facade_does_not_demand_flat_lex :
  flat_lex_demand_for_dag_facade true = 0.
Proof. reflexivity. Qed.

Theorem nonambiguous_dag_facade_falls_back_to_flat_lex :
  flat_lex_demand_for_dag_facade false = 1.
Proof. reflexivity. Qed.

Record parse_alternative_model : Type := {
  pam_semantic_key : nat;
  pam_payload : nat
}.

Definition semantic_key_represented
    (alt : parse_alternative_model)
    (output : list parse_alternative_model) : Prop :=
  exists kept,
    In kept output /\
    pam_semantic_key kept = pam_semantic_key alt.

Definition parser_assembly_preserves_semantic_keys
    (input output : list parse_alternative_model) : Prop :=
  forall alt,
    In alt input ->
    semantic_key_represented alt output.

Theorem parser_assembly_identity_preserves_semantic_keys :
  forall alts,
    parser_assembly_preserves_semantic_keys alts alts.
Proof.
  intros alts alt Hin.
  exists alt.
  split; [exact Hin | reflexivity].
Qed.

Theorem parser_assembly_preserves_distinct_pair_without_evidence :
  forall left right,
    parser_assembly_preserves_semantic_keys [left; right] [left; right].
Proof.
  intros left right.
  apply parser_assembly_identity_preserves_semantic_keys.
Qed.

Definition semantic_key : Type := list nat.

Lemma semantic_key_eq_dec :
  forall x y : semantic_key, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Record exact_parse_alternative_model : Type := {
  epam_semantic_key : semantic_key;
  epam_payload : nat
}.

Definition exact_semantic_key_represented
    (alt : exact_parse_alternative_model)
    (output : list exact_parse_alternative_model) : Prop :=
  exists kept,
    In kept output /\
    epam_semantic_key kept = epam_semantic_key alt.

Definition exact_key_assembly_preserves_semantic_keys
    (input output : list exact_parse_alternative_model) : Prop :=
  forall alt,
    In alt input ->
    exact_semantic_key_represented alt output.

Definition exact_key_pair_dedup
    (left right : exact_parse_alternative_model)
    : list exact_parse_alternative_model :=
  if semantic_key_eq_dec
       (epam_semantic_key left)
       (epam_semantic_key right)
  then [left]
  else [left; right].

Theorem exact_key_pair_dedup_preserves_distinct_keys :
  forall left right,
    epam_semantic_key left <> epam_semantic_key right ->
    exact_key_pair_dedup left right = [left; right].
Proof.
  intros left right Hdistinct.
  unfold exact_key_pair_dedup.
  destruct (semantic_key_eq_dec
              (epam_semantic_key left)
              (epam_semantic_key right)) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem exact_key_assembly_preserves_distinct_pair_without_evidence :
  forall left right,
    epam_semantic_key left <> epam_semantic_key right ->
    exact_key_assembly_preserves_semantic_keys
      [left; right]
      (exact_key_pair_dedup left right).
Proof.
  intros left right Hdistinct alt Hin.
  rewrite exact_key_pair_dedup_preserves_distinct_keys by exact Hdistinct.
  exists alt.
  split; [exact Hin | reflexivity].
Qed.

Theorem parser_preserves_ambiguous_alternatives :
  forall left right,
    epam_semantic_key left <> epam_semantic_key right ->
    exact_semantic_key_represented left (exact_key_pair_dedup left right) /\
    exact_semantic_key_represented right (exact_key_pair_dedup left right).
Proof.
  intros left right Hdistinct.
  pose proof
    (exact_key_assembly_preserves_distinct_pair_without_evidence
       left right Hdistinct) as Hpreserves.
  split.
  - apply Hpreserves.
    simpl; auto.
  - apply Hpreserves.
    simpl; auto.
Qed.

Inductive generated_term_model : Type :=
  | GeneratedSingle (alt : exact_parse_alternative_model)
  | GeneratedAmbiguous (alts : list exact_parse_alternative_model).

Definition generated_all_alts
    (term : generated_term_model)
    : list exact_parse_alternative_model :=
  match term with
  | GeneratedSingle alt => [alt]
  | GeneratedAmbiguous alts => alts
  end.

Fixpoint semantic_key_in
    (key : semantic_key)
    (alts : list exact_parse_alternative_model)
    : bool :=
  match alts with
  | [] => false
  | alt :: rest =>
      if semantic_key_eq_dec key (epam_semantic_key alt)
      then true
      else semantic_key_in key rest
  end.

Fixpoint exact_key_dedup_list
    (alts : list exact_parse_alternative_model)
    : list exact_parse_alternative_model :=
  match alts with
  | [] => []
  | alt :: rest =>
      let deduped_rest := exact_key_dedup_list rest in
      if semantic_key_in (epam_semantic_key alt) deduped_rest
      then deduped_rest
      else alt :: deduped_rest
  end.

Definition generated_seed_keys
    (term : generated_term_model)
    : list semantic_key :=
  map epam_semantic_key
    (exact_key_dedup_list (generated_all_alts term)).

Theorem generated_all_alts_preserves_ambiguous_members :
  forall alts alt,
    In alt alts ->
    In alt (generated_all_alts (GeneratedAmbiguous alts)).
Proof. auto. Qed.

Theorem generated_language_seeds_all_ambiguous_alternatives :
  forall left right,
    epam_semantic_key left <> epam_semantic_key right ->
    generated_seed_keys (GeneratedAmbiguous [left; right]) =
      [epam_semantic_key left; epam_semantic_key right].
Proof.
  intros left right Hdistinct.
  unfold generated_seed_keys, generated_all_alts.
  simpl.
  destruct (semantic_key_eq_dec
              (epam_semantic_key left)
              (epam_semantic_key right)) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Record weighted_parse_alternative_model : Type := {
  wpam_alt : exact_parse_alternative_model;
  wpam_weight : nat;
  wpam_sequence : nat
}.

Definition erase_weighted_parse_alternative
    (alt : weighted_parse_alternative_model)
    : exact_parse_alternative_model :=
  wpam_alt alt.

Definition weighted_exact_key_pair_dedup
    (left right : weighted_parse_alternative_model)
    : list weighted_parse_alternative_model :=
  if semantic_key_eq_dec
       (epam_semantic_key (erase_weighted_parse_alternative left))
       (epam_semantic_key (erase_weighted_parse_alternative right))
  then [left]
  else [left; right].

Definition weighted_exact_semantic_key_represented
    (alt : exact_parse_alternative_model)
    (output : list weighted_parse_alternative_model) : Prop :=
  exists kept,
    In kept output /\
    epam_semantic_key
      (erase_weighted_parse_alternative kept) =
      epam_semantic_key alt.

Definition weighted_parser_assembly_preserves_semantic_keys
    (input : list exact_parse_alternative_model)
    (output : list weighted_parse_alternative_model) : Prop :=
  forall alt,
    In alt input ->
    weighted_exact_semantic_key_represented alt output.

Theorem weighted_exact_key_pair_dedup_preserves_distinct_keys :
  forall left right,
    epam_semantic_key (erase_weighted_parse_alternative left) <>
      epam_semantic_key (erase_weighted_parse_alternative right) ->
    weighted_exact_key_pair_dedup left right = [left; right].
Proof.
  intros left right Hdistinct.
  unfold weighted_exact_key_pair_dedup.
  destruct (semantic_key_eq_dec
              (epam_semantic_key (erase_weighted_parse_alternative left))
              (epam_semantic_key (erase_weighted_parse_alternative right)))
    as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem weighted_parser_alternatives_preserve_unweighted_set :
  forall left right weight_left weight_right seq_left seq_right,
    epam_semantic_key left <> epam_semantic_key right ->
    weighted_parser_assembly_preserves_semantic_keys
      [left; right]
      (weighted_exact_key_pair_dedup
         {| wpam_alt := left;
            wpam_weight := weight_left;
            wpam_sequence := seq_left |}
         {| wpam_alt := right;
            wpam_weight := weight_right;
            wpam_sequence := seq_right |}).
Proof.
  intros left right weight_left weight_right seq_left seq_right Hdistinct.
  unfold weighted_parser_assembly_preserves_semantic_keys.
  intros alt Hin.
  rewrite weighted_exact_key_pair_dedup_preserves_distinct_keys.
  - destruct Hin as [Hleft | [Hright | Hnone]].
    + subst alt.
      exists {| wpam_alt := left;
                wpam_weight := weight_left;
                wpam_sequence := seq_left |}.
      split; [simpl; auto | reflexivity].
    + subst alt.
      exists {| wpam_alt := right;
                wpam_weight := weight_right;
                wpam_sequence := seq_right |}.
      split; [simpl; auto | reflexivity].
    + contradiction.
  - simpl.
    exact Hdistinct.
Qed.

Record substitution_alt_model : Type := {
  sam_before : exact_parse_alternative_model;
  sam_after : exact_parse_alternative_model
}.

Definition substitution_after_alts
    (alts : list substitution_alt_model)
    : list exact_parse_alternative_model :=
  map sam_after alts.

Definition substitution_result_keys
    (alts : list substitution_alt_model)
    : list semantic_key :=
  map epam_semantic_key
    (exact_key_dedup_list (substitution_after_alts alts)).

Theorem ambiguous_substitution_preserves_changed_and_unchanged_siblings :
  forall before_changed after_changed unchanged,
    epam_semantic_key before_changed <> epam_semantic_key after_changed ->
    epam_semantic_key after_changed <> epam_semantic_key unchanged ->
    substitution_result_keys
      [{| sam_before := before_changed; sam_after := after_changed |};
       {| sam_before := unchanged; sam_after := unchanged |}] =
      [epam_semantic_key after_changed; epam_semantic_key unchanged].
Proof.
  intros before_changed after_changed unchanged _ Hdistinct.
  unfold substitution_result_keys, substitution_after_alts.
  simpl.
  destruct (semantic_key_eq_dec
              (epam_semantic_key after_changed)
              (epam_semantic_key unchanged)) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Definition hash_only_pair_dedup
    (hash : semantic_key -> nat)
    (left right : exact_parse_alternative_model)
    : list exact_parse_alternative_model :=
  if Nat.eqb
       (hash (epam_semantic_key left))
       (hash (epam_semantic_key right))
  then [left]
  else [left; right].

Theorem hash_only_pair_dedup_can_drop_distinct_keys :
  exists hash left right,
    epam_semantic_key left <> epam_semantic_key right /\
    hash_only_pair_dedup hash left right = [left].
Proof.
  exists (fun _ => 0).
  exists {| epam_semantic_key := [0]; epam_payload := 10 |}.
  exists {| epam_semantic_key := [1]; epam_payload := 20 |}.
  split.
  - intro Heq.
    now inversion Heq.
  - reflexivity.
Qed.

Record hashbag_order_entry_model : Type := {
  hbo_sort_key : nat;
  hbo_stream_key : nat;
  hbo_count : nat
}.

Definition hashbag_entry_lane (entry : hashbag_order_entry_model) : nat :=
  hbo_stream_key entry + 257 * hbo_count entry.

Fixpoint old_ordered_hashbag_fold
    (entries : list hashbag_order_entry_model) : nat :=
  match entries with
  | [] => 0
  | entry :: rest =>
      131 * old_ordered_hashbag_fold rest + hashbag_entry_lane entry
  end.

Fixpoint commutative_hashbag_summary
    (entries : list hashbag_order_entry_model) : nat :=
  match entries with
  | [] => 0
  | entry :: rest =>
      hashbag_entry_lane entry + commutative_hashbag_summary rest
  end.

Theorem old_ordered_hashbag_fold_can_depend_on_colliding_sort_tie :
  exists left right,
    hbo_sort_key left = hbo_sort_key right /\
    hashbag_entry_lane left <> hashbag_entry_lane right /\
    old_ordered_hashbag_fold [left; right] <>
    old_ordered_hashbag_fold [right; left].
Proof.
  exists {| hbo_sort_key := 0; hbo_stream_key := 1; hbo_count := 0 |}.
  exists {| hbo_sort_key := 0; hbo_stream_key := 2; hbo_count := 0 |}.
  simpl.
  split; [reflexivity |].
  split.
  - intro Heq. inversion Heq.
  - intro Heq. inversion Heq.
Qed.

Theorem commutative_hashbag_summary_permutation :
  forall left right,
    Permutation left right ->
    commutative_hashbag_summary left =
    commutative_hashbag_summary right.
Proof.
  intros left right Hperm.
  induction Hperm.
  - reflexivity.
  - simpl. rewrite IHHperm. reflexivity.
  - simpl. lia.
  - transitivity (commutative_hashbag_summary l'); assumption.
Qed.

Record eval_term_info_model : Type := {
  eti_id : nat;
  eti_normal : bool
}.

Definition eager_normal_forms
    (terms : list eval_term_info_model) : list eval_term_info_model :=
  filter eti_normal terms.

Fixpoint lazy_normal_forms_observation
    (terms : list eval_term_info_model)
    (demand : nat) : list eval_term_info_model :=
  match demand, terms with
  | 0, _ => []
  | Datatypes.S _, [] => []
  | Datatypes.S demand', term :: rest =>
      if eti_normal term
      then term :: lazy_normal_forms_observation rest demand'
      else lazy_normal_forms_observation rest (Datatypes.S demand')
  end.

Theorem lazy_normal_forms_observation_is_eager_prefix :
  forall terms demand,
    lazy_normal_forms_observation terms demand =
    firstn demand (eager_normal_forms terms).
Proof.
  induction terms as [| term rest IH]; intros demand;
    destruct demand as [| demand']; simpl; try reflexivity.
  destruct (eti_normal term); simpl; rewrite IH; reflexivity.
Qed.

Theorem lazy_normal_forms_zero_demand :
  forall terms,
    lazy_normal_forms_observation terms 0 = [].
Proof.
  intros terms.
  destruct terms; reflexivity.
Qed.

Theorem normal_forms_collecting_matches_lazy_all :
  forall terms,
    lazy_normal_forms_observation terms (length (eager_normal_forms terms)) =
    eager_normal_forms terms.
Proof.
  intros terms.
  rewrite lazy_normal_forms_observation_is_eager_prefix.
  apply firstn_all.
Qed.

Record seed_normal_forms_model : Type := {
  snfm_seed : nat;
  snfm_normals : list eval_term_info_model
}.

Definition eager_seed_normal_forms
    (seeds : list seed_normal_forms_model)
    : list eval_term_info_model :=
  flat_map snfm_normals seeds.

Fixpoint lazy_seed_normal_forms_observation
    (seeds : list seed_normal_forms_model)
    (demand : nat) : list eval_term_info_model :=
  match demand, seeds with
  | 0, _ => []
  | Datatypes.S _, [] => []
  | Datatypes.S _, seed :: rest =>
      let observed := firstn demand (snfm_normals seed) in
      observed ++
        lazy_seed_normal_forms_observation
          rest
          (demand - length observed)
  end.

Definition first_seed_normal_form_witness
    (seeds : list seed_normal_forms_model)
    : option eval_term_info_model :=
  hd_error (lazy_seed_normal_forms_observation seeds 1).

Theorem lazy_seed_normal_forms_zero_demand :
  forall seeds,
    lazy_seed_normal_forms_observation seeds 0 = [].
Proof.
  intros seeds.
  destruct seeds; reflexivity.
Qed.

Theorem lazy_seed_normal_forms_preserves_two_singleton_alternatives :
  forall seed_a seed_b nf_a nf_b,
    lazy_seed_normal_forms_observation
      [{| snfm_seed := seed_a; snfm_normals := [nf_a] |};
       {| snfm_seed := seed_b; snfm_normals := [nf_b] |}]
      2 = [nf_a; nf_b].
Proof. reflexivity. Qed.

Theorem first_seed_witness_preserves_seed_order :
  forall seed_a seed_b nf_a nf_b,
    first_seed_normal_form_witness
      [{| snfm_seed := seed_a; snfm_normals := [nf_a] |};
       {| snfm_seed := seed_b; snfm_normals := [nf_b] |}]
      = Some nf_a.
Proof. reflexivity. Qed.

Theorem lazy_seed_normal_forms_skips_later_seed_after_demand_filled :
  forall seed_a seed_b nf_a later,
    lazy_seed_normal_forms_observation
      [{| snfm_seed := seed_a; snfm_normals := [nf_a] |};
       {| snfm_seed := seed_b; snfm_normals := later |}]
      1 = [nf_a].
Proof. reflexivity. Qed.

Theorem lazy_seed_normal_forms_observation_is_eager_prefix :
  forall seeds demand,
    lazy_seed_normal_forms_observation seeds demand =
    firstn demand (eager_seed_normal_forms seeds).
Proof.
  intros seeds.
  induction seeds as [| seed rest IH]; intros demand;
    destruct demand as [| demand'];
    cbn [lazy_seed_normal_forms_observation];
    try reflexivity.
  change (eager_seed_normal_forms (seed :: rest)) with
    (snfm_normals seed ++ eager_seed_normal_forms rest).
  rewrite (@firstn_app eval_term_info_model
             (Datatypes.S demand')
             (snfm_normals seed)
             (eager_seed_normal_forms rest)).
  f_equal.
  assert (
    Datatypes.S demand' -
      length (firstn (Datatypes.S demand') (snfm_normals seed)) =
    Datatypes.S demand' - length (snfm_normals seed)
  ) as Hremaining.
  {
    rewrite length_firstn.
    lia.
  }
  rewrite Hremaining.
  apply IH.
Qed.

Record weighted_seed_normal_forms_model : Type := {
  wsnfm_seed : nat;
  wsnfm_weight : nat;
  wsnfm_sequence : nat;
  wsnfm_normals : list eval_term_info_model
}.

Definition weighted_seed_precedes
    (left right : weighted_seed_normal_forms_model)
    : bool :=
  (wsnfm_weight left <? wsnfm_weight right) ||
  ((wsnfm_weight left =? wsnfm_weight right) &&
   (wsnfm_sequence left <=? wsnfm_sequence right)).

Fixpoint insert_weighted_seed
    (seed : weighted_seed_normal_forms_model)
    (sorted : list weighted_seed_normal_forms_model)
    : list weighted_seed_normal_forms_model :=
  match sorted with
  | [] => [seed]
  | head :: rest =>
      if weighted_seed_precedes seed head
      then seed :: sorted
      else head :: insert_weighted_seed seed rest
  end.

Fixpoint sort_weighted_seeds
    (seeds : list weighted_seed_normal_forms_model)
    : list weighted_seed_normal_forms_model :=
  match seeds with
  | [] => []
  | seed :: rest => insert_weighted_seed seed (sort_weighted_seeds rest)
  end.

Definition erase_weighted_seed
    (seed : weighted_seed_normal_forms_model)
    : seed_normal_forms_model :=
  {| snfm_seed := wsnfm_seed seed;
     snfm_normals := wsnfm_normals seed |}.

Definition eager_weighted_seed_normal_forms
    (seeds : list weighted_seed_normal_forms_model)
    : list eval_term_info_model :=
  eager_seed_normal_forms
    (map erase_weighted_seed (sort_weighted_seeds seeds)).

Definition lazy_weighted_seed_normal_forms_observation
    (seeds : list weighted_seed_normal_forms_model)
    (demand : nat)
    : list eval_term_info_model :=
  lazy_seed_normal_forms_observation
    (map erase_weighted_seed (sort_weighted_seeds seeds))
    demand.

Theorem lazy_weighted_seed_normal_forms_is_eager_prefix :
  forall seeds demand,
    lazy_weighted_seed_normal_forms_observation seeds demand =
    firstn demand (eager_weighted_seed_normal_forms seeds).
Proof.
  intros seeds demand.
  unfold lazy_weighted_seed_normal_forms_observation,
    eager_weighted_seed_normal_forms.
  apply lazy_seed_normal_forms_observation_is_eager_prefix.
Qed.

Theorem weighted_seed_lower_weight_preempts_later_seed :
  forall seed_a seed_b nf_a nf_b weight_a weight_b seq_a seq_b,
    weight_b < weight_a ->
    lazy_weighted_seed_normal_forms_observation
      [{| wsnfm_seed := seed_a;
          wsnfm_weight := weight_a;
          wsnfm_sequence := seq_a;
          wsnfm_normals := [nf_a] |};
       {| wsnfm_seed := seed_b;
          wsnfm_weight := weight_b;
          wsnfm_sequence := seq_b;
          wsnfm_normals := [nf_b] |}]
      1 = [nf_b].
Proof.
  intros seed_a seed_b nf_a nf_b weight_a weight_b seq_a seq_b Hlt.
  destruct (weight_a <? weight_b) eqn:Hweight.
  - apply Nat.ltb_lt in Hweight. lia.
  - destruct (weight_a =? weight_b) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + unfold lazy_weighted_seed_normal_forms_observation.
      cbn [sort_weighted_seeds insert_weighted_seed weighted_seed_precedes
           lazy_seed_normal_forms_observation erase_weighted_seed].
      unfold weighted_seed_precedes.
      cbn [wsnfm_weight wsnfm_sequence].
      rewrite Hweight, Heq.
      reflexivity.
Qed.

Theorem weighted_seed_equal_weight_preserves_lower_sequence :
  forall seed_a seed_b nf_a nf_b weight seq_a seq_b,
    seq_a <= seq_b ->
    lazy_weighted_seed_normal_forms_observation
      [{| wsnfm_seed := seed_a;
          wsnfm_weight := weight;
          wsnfm_sequence := seq_a;
          wsnfm_normals := [nf_a] |};
       {| wsnfm_seed := seed_b;
          wsnfm_weight := weight;
          wsnfm_sequence := seq_b;
          wsnfm_normals := [nf_b] |}]
      1 = [nf_a].
Proof.
  intros seed_a seed_b nf_a nf_b weight seq_a seq_b Hseq.
  destruct (weight <? weight) eqn:Hweight.
  - apply Nat.ltb_lt in Hweight. lia.
  - destruct (seq_a <=? seq_b) eqn:Hle.
    + unfold lazy_weighted_seed_normal_forms_observation.
      cbn [sort_weighted_seeds insert_weighted_seed weighted_seed_precedes
           lazy_seed_normal_forms_observation erase_weighted_seed].
      unfold weighted_seed_precedes.
      cbn [wsnfm_weight wsnfm_sequence].
      rewrite Hweight, Nat.eqb_refl, Hle.
      reflexivity.
    + apply Nat.leb_gt in Hle. lia.
Qed.

Record parse_weighted_seed_model : Type := {
  pwsm_seed : nat;
  pwsm_parse_weight : nat;
  pwsm_parse_sequence : nat;
  pwsm_eval_normals : list eval_term_info_model
}.

Definition parse_seed_to_weighted_eval_seed
    (seed : parse_weighted_seed_model)
    : weighted_seed_normal_forms_model :=
  {| wsnfm_seed := pwsm_seed seed;
     wsnfm_weight := pwsm_parse_weight seed;
     wsnfm_sequence := pwsm_parse_sequence seed;
     wsnfm_normals := pwsm_eval_normals seed |}.

Definition lazy_parse_weighted_evaluation_prefix
    (seeds : list parse_weighted_seed_model)
    (demand : nat)
    : list eval_term_info_model :=
  lazy_weighted_seed_normal_forms_observation
    (map parse_seed_to_weighted_eval_seed seeds)
    demand.

Definition eager_parse_weighted_evaluation_prefix
    (seeds : list parse_weighted_seed_model)
    : list eval_term_info_model :=
  eager_weighted_seed_normal_forms
    (map parse_seed_to_weighted_eval_seed seeds).

Theorem parse_weighted_seed_prefix_matches_evaluation_prefix :
  forall seeds demand,
    lazy_parse_weighted_evaluation_prefix seeds demand =
    firstn demand (eager_parse_weighted_evaluation_prefix seeds).
Proof.
  intros seeds demand.
  unfold lazy_parse_weighted_evaluation_prefix,
    eager_parse_weighted_evaluation_prefix.
  apply lazy_weighted_seed_normal_forms_is_eager_prefix.
Qed.

Inductive cast_normalization_step_result : Type :=
  | CastNormalizationApplied (next_depth : nat)
  | CastNormalizationBudgetExceeded (budget actual : nat)
  | CastNormalizationGuardRejected.

Inductive cast_normalization_bound_source : Type :=
  | BoundBySyntheticInjGuard
  | BoundByGeneratedNormCast.

Definition cast_normalization_bound_applies
    (source : cast_normalization_bound_source)
    (is_auto_injected_norm_cast has_synthetic_guard : bool)
    : Prop :=
  match source with
  | BoundBySyntheticInjGuard => has_synthetic_guard = true
  | BoundByGeneratedNormCast => is_auto_injected_norm_cast = true
  end.

Definition guarded_cast_normalization_step
    (budget depth : nat)
    (guard_allows : bool)
    : cast_normalization_step_result :=
  if guard_allows then
    if depth <? budget
    then CastNormalizationApplied (S depth)
    else CastNormalizationBudgetExceeded budget (S depth)
  else CastNormalizationGuardRejected.

Theorem cast_normalization_budget_sound :
  forall budget depth,
    match guarded_cast_normalization_step budget depth true with
    | CastNormalizationApplied next =>
        depth < budget /\ next = S depth
    | CastNormalizationBudgetExceeded reported_budget actual =>
        budget <= depth /\
        reported_budget = budget /\
        actual = S depth
    | CastNormalizationGuardRejected => False
    end.
Proof.
  intros budget depth.
  unfold guarded_cast_normalization_step.
  destruct (depth <? budget) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    split; [exact Hlt | reflexivity].
  - apply Nat.ltb_ge in Hlt.
    repeat split; try exact Hlt; reflexivity.
Qed.

Theorem cast_normalization_guard_rejection_is_explicit :
  forall budget depth,
    guarded_cast_normalization_step budget depth false =
      CastNormalizationGuardRejected.
Proof. reflexivity. Qed.

Theorem generated_norm_cast_bound_is_independent_of_guard_metadata :
  cast_normalization_bound_applies
    BoundByGeneratedNormCast true false.
Proof. reflexivity. Qed.
