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
    (branches_empty primary_only_survived primary_has_dispatch_rule
      only_secondary_survived : bool) : bool :=
  orb branches_empty
    (orb primary_only_survived
      (andb only_secondary_survived primary_has_dispatch_rule)).

Theorem lex_fork_only_secondary_when_nonempty_without_primary :
  lex_fork_only_secondary_survived true false = true.
Proof. reflexivity. Qed.

Theorem lex_fork_falls_through_when_only_secondary_and_primary_has_dispatch :
  lex_fork_fall_through false false true true = true.
Proof. reflexivity. Qed.

Theorem lex_fork_does_not_fall_through_for_secondary_without_primary_dispatch :
  lex_fork_fall_through false false false true = false.
Proof. reflexivity. Qed.

Theorem lex_fork_fall_through_only_secondary_matches_primary_dispatch :
  forall primary_has_dispatch_rule,
    lex_fork_fall_through false false primary_has_dispatch_rule true =
    primary_has_dispatch_rule.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
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
  lex_fork_fall_through true false false false = true.
Proof. reflexivity. Qed.

Theorem lex_fork_falls_through_when_only_primary_survived :
  lex_fork_fall_through false true false false = true.
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

Record eval_term_info_model : Type := {
  eti_id : nat;
  eti_normal : bool
}.

Definition eager_normal_forms
    (terms : list eval_term_info_model) : list eval_term_info_model :=
  filter eti_normal terms.

Definition lazy_normal_forms_observation
    (terms : list eval_term_info_model)
    (demand : nat) : list eval_term_info_model :=
  firstn demand (eager_normal_forms terms).

Theorem lazy_normal_forms_observation_is_eager_prefix :
  forall terms demand,
    lazy_normal_forms_observation terms demand =
    firstn demand (eager_normal_forms terms).
Proof. reflexivity. Qed.

Theorem lazy_normal_forms_zero_demand :
  forall terms,
    lazy_normal_forms_observation terms 0 = [].
Proof. reflexivity. Qed.

Theorem normal_forms_collecting_matches_lazy_all :
  forall terms,
    lazy_normal_forms_observation terms (length (eager_normal_forms terms)) =
    eager_normal_forms terms.
Proof.
  intros terms.
  unfold lazy_normal_forms_observation.
  apply firstn_all.
Qed.
