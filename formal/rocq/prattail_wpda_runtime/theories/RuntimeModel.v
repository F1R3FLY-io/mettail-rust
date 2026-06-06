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
     ck_collection_depth := ck_collection_depth k;
     ck_origin := ck_origin k;
     ck_sppf_top := ck_sppf_top k;
     ck_lex_alt := ck_lex_alt k;
     ck_weight_src := ck_weight_src k;
     ck_weight_rule := ck_weight_rule k;
     ck_lex_stamp := Some stamp |}.

Definition lex_fork_child_config
    (k : config_key)
    (stamp next_pos : nat) : config_key :=
  {| ck_control := ck_control k;
     ck_node := ck_node k;
     ck_pos := next_pos;
     ck_incoming_edge := ck_incoming_edge k;
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
