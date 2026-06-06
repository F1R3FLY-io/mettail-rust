(*
 * FiniteHarness: Rocq justification for the bounded TLA+ control domain.
 *
 * The executable TLA+ model intentionally keeps only the control states
 * reached by its bounded quotient, chain-absorption, and cross-category
 * scenarios. This file records that reduction against the full runtime
 * control vocabulary from RuntimeModel.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From PrattailWpdaRuntime Require Import RuntimeModel.

Import ListNotations.

Inductive harness_control : Type :=
  | HarnessChain
  | HarnessDelegate
  | HarnessUnwind
  | HarnessDone.

Lemma harness_control_eq_dec :
  forall x y : harness_control, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition embed_harness_control (h : harness_control) : control :=
  match h with
  | HarnessChain => InfixChainIterative
  | HarnessDelegate => CrossCatDelegate
  | HarnessUnwind => Unwinding
  | HarnessDone => Done
  end.

Definition control_in_harness (c : control) : Prop :=
  exists h, embed_harness_control h = c.

Lemma harness_control_cases :
  forall c,
    control_in_harness c <->
      c = InfixChainIterative \/
      c = CrossCatDelegate \/
      c = Unwinding \/
      c = Done.
Proof.
  intros c. split.
  - intros [h H].
    destruct h; simpl in H; subst; tauto.
  - intros [H | [H | [H | H]]]; subst.
    + exists HarnessChain. reflexivity.
    + exists HarnessDelegate. reflexivity.
    + exists HarnessUnwind. reflexivity.
    + exists HarnessDone. reflexivity.
Qed.

Lemma harness_excludes_prefix :
  ~ control_in_harness PrefixDispatch.
Proof.
  intro H.
  apply harness_control_cases in H.
  destruct H as [H | [H | [H | H]]]; discriminate.
Qed.

Lemma harness_excludes_fanout :
  ~ control_in_harness AmbiguityFanout.
Proof.
  intro H.
  apply harness_control_cases in H.
  destruct H as [H | [H | [H | H]]]; discriminate.
Qed.

Lemma harness_excludes_error :
  ~ control_in_harness Error.
Proof.
  intro H.
  apply harness_control_cases in H.
  destruct H as [H | [H | [H | H]]]; discriminate.
Qed.

Record harness_cursor : Type := {
  hc_control : harness_control;
  hc_pos : nat;
  hc_source : nat;
  hc_bp : nat;
  hc_wrap : nat;
  hc_sppf : nat;
  hc_absorbed : bool
}.

Record harness_config : Type := {
  hcfg_control : harness_control;
  hcfg_pos : nat;
  hcfg_source : nat;
  hcfg_bp : nat;
  hcfg_wrap : nat;
  hcfg_sppf : nat;
  hcfg_absorbed : bool
}.

Lemma harness_config_eq_dec :
  forall x y : harness_config, {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply Bool.bool_dec;
    try apply harness_control_eq_dec.
Defined.

Definition harness_wrap_key (wrap_observable : bool) (wrap : nat) : nat :=
  if wrap_observable then wrap else 0.

Definition config_of_harness_cursor
    (wrap_observable : bool)
    (c : harness_cursor) : harness_config :=
  {| hcfg_control := hc_control c;
     hcfg_pos := hc_pos c;
     hcfg_source := hc_source c;
     hcfg_bp := hc_bp c;
     hcfg_wrap := harness_wrap_key wrap_observable (hc_wrap c);
     hcfg_sppf := hc_sppf c;
     hcfg_absorbed := hc_absorbed c |}.

Definition update_harness_cursor
    (c : harness_cursor)
    (st : harness_control)
    (pos : nat)
    (sppf : nat)
    (absorbed : bool) : harness_cursor :=
  {| hc_control := st;
     hc_pos := pos;
     hc_source := hc_source c;
     hc_bp := hc_bp c;
     hc_wrap := hc_wrap c;
     hc_sppf := sppf;
     hc_absorbed := absorbed |}.

Definition update_harness_config
    (k : harness_config)
    (st : harness_control)
    (pos : nat)
    (sppf : nat)
    (absorbed : bool) : harness_config :=
  {| hcfg_control := st;
     hcfg_pos := pos;
     hcfg_source := hcfg_source k;
     hcfg_bp := hcfg_bp k;
     hcfg_wrap := hcfg_wrap k;
     hcfg_sppf := sppf;
     hcfg_absorbed := absorbed |}.

Definition next_harness_cursor (c : harness_cursor) : list harness_cursor :=
  match hc_control c with
  | HarnessChain =>
      [update_harness_cursor c HarnessUnwind 3 (hc_sppf c) true]
  | HarnessDelegate =>
      if hc_absorbed c then
        [update_harness_cursor c HarnessUnwind (hc_pos c) (hc_sppf c) true]
      else if Nat.ltb (hc_pos c) 3 then
        [update_harness_cursor c HarnessUnwind (S (hc_pos c)) 0 false;
         update_harness_cursor c HarnessUnwind (S (hc_pos c)) 1 false]
      else
        [update_harness_cursor c HarnessDone (hc_pos c) (hc_sppf c) false]
  | HarnessUnwind =>
      [update_harness_cursor c HarnessDone (hc_pos c) (hc_sppf c) (hc_absorbed c)]
  | HarnessDone =>
      [c]
  end.

Definition next_harness_config (k : harness_config) : list harness_config :=
  match hcfg_control k with
  | HarnessChain =>
      [update_harness_config k HarnessUnwind 3 (hcfg_sppf k) true]
  | HarnessDelegate =>
      if hcfg_absorbed k then
        [update_harness_config k HarnessUnwind (hcfg_pos k) (hcfg_sppf k) true]
      else if Nat.ltb (hcfg_pos k) 3 then
        [update_harness_config k HarnessUnwind (S (hcfg_pos k)) 0 false;
         update_harness_config k HarnessUnwind (S (hcfg_pos k)) 1 false]
      else
        [update_harness_config k HarnessDone (hcfg_pos k) (hcfg_sppf k) false]
  | HarnessUnwind =>
      [update_harness_config k HarnessDone (hcfg_pos k) (hcfg_sppf k) (hcfg_absorbed k)]
  | HarnessDone =>
      [k]
  end.

Definition insert_harness_config
    (k : harness_config)
    (ks : list harness_config) : list harness_config :=
  if in_dec harness_config_eq_dec k ks then ks else k :: ks.

Fixpoint harness_config_keys (ks : list harness_config) : list harness_config :=
  match ks with
  | [] => []
  | k :: rest => insert_harness_config k (harness_config_keys rest)
  end.

Definition harness_config_set_of_cursors
    (wrap_observable : bool)
    (cs : list harness_cursor) : list harness_config :=
  harness_config_keys (map (config_of_harness_cursor wrap_observable) cs).

Definition no_delegate_inside_absorbed (c : harness_cursor) : Prop :=
  hc_absorbed c = true -> hc_control c <> HarnessDelegate.

Definition delegate_progress (c : harness_cursor) : Prop :=
  hc_control c = HarnessDelegate -> hc_pos c < 3.

Theorem next_harness_controls_embed_in_runtime_subset :
  forall c c',
    In c' (next_harness_cursor c) ->
    control_in_harness (embed_harness_control (hc_control c')).
Proof.
  intros c c' _.
  exists (hc_control c').
  reflexivity.
Qed.

Theorem next_harness_excludes_removed_runtime_controls :
  forall c c',
    In c' (next_harness_cursor c) ->
    embed_harness_control (hc_control c') <> PrefixDispatch /\
    embed_harness_control (hc_control c') <> AmbiguityFanout /\
    embed_harness_control (hc_control c') <> Error.
Proof.
  intros c c' Hin.
  pose proof (next_harness_controls_embed_in_runtime_subset c c' Hin) as Hh.
  split.
  - intro Heq. rewrite Heq in Hh. exact (harness_excludes_prefix Hh).
  - split.
    + intro Heq. rewrite Heq in Hh. exact (harness_excludes_fanout Hh).
    + intro Heq. rewrite Heq in Hh. exact (harness_excludes_error Hh).
Qed.

Theorem next_harness_no_delegate_inside_absorbed_all :
  forall c,
    Forall no_delegate_inside_absorbed (next_harness_cursor c).
Proof.
  intros [st pos source bp wrap sppf absorbed].
  destruct st; cbn.
  - constructor.
    + unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
    + constructor.
  - destruct absorbed; cbn.
    + constructor.
      * unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
      * constructor.
    + destruct (pos <=? 2); cbn.
      * constructor.
        -- unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
        -- constructor.
           ++ unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
           ++ constructor.
      * constructor.
        -- unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
        -- constructor.
  - constructor.
    + unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
    + constructor.
  - constructor.
    + unfold no_delegate_inside_absorbed; simpl; intros _ H; discriminate.
    + constructor.
Qed.

Theorem next_harness_no_delegate_inside_absorbed :
  forall c c',
    In c' (next_harness_cursor c) ->
    no_delegate_inside_absorbed c'.
Proof.
  intros c c' Hin.
  pose proof (next_harness_no_delegate_inside_absorbed_all c) as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c' Hin).
Qed.

Theorem next_harness_delegate_progress_all :
  forall c,
    Forall delegate_progress (next_harness_cursor c).
Proof.
  intros [st pos source bp wrap sppf absorbed].
  destruct st; cbn.
  - constructor.
    + unfold delegate_progress; simpl; intros H; discriminate.
    + constructor.
  - destruct absorbed; cbn.
    + constructor.
      * unfold delegate_progress; simpl; intros H; discriminate.
      * constructor.
    + destruct (pos <=? 2); cbn.
      * constructor.
        -- unfold delegate_progress; simpl; intros H; discriminate.
        -- constructor.
           ++ unfold delegate_progress; simpl; intros H; discriminate.
           ++ constructor.
      * constructor.
        -- unfold delegate_progress; simpl; intros H; discriminate.
        -- constructor.
  - constructor.
    + unfold delegate_progress; simpl; intros H; discriminate.
    + constructor.
  - constructor.
    + unfold delegate_progress; simpl; intros H; discriminate.
    + constructor.
Qed.

Theorem next_harness_delegate_progress :
  forall c c',
    In c' (next_harness_cursor c) ->
    delegate_progress c'.
Proof.
  intros c c' Hin.
  pose proof (next_harness_delegate_progress_all c) as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c' Hin).
Qed.

Theorem next_harness_config_commutes :
  forall wrap_observable c,
    map (config_of_harness_cursor wrap_observable) (next_harness_cursor c) =
    next_harness_config (config_of_harness_cursor wrap_observable c).
Proof.
  intros wrap_observable [st pos source bp wrap sppf absorbed].
  destruct st; cbn.
  - reflexivity.
  - destruct absorbed; cbn.
    + reflexivity.
    + destruct (pos <=? 2); reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint step_harness_full (cs : list harness_cursor) : list harness_cursor :=
  match cs with
  | [] => []
  | c :: rest => next_harness_cursor c ++ step_harness_full rest
  end.

Fixpoint step_harness_configs (ks : list harness_config) : list harness_config :=
  match ks with
  | [] => []
  | k :: rest => next_harness_config k ++ step_harness_configs rest
  end.

Theorem step_harness_config_commutes :
  forall wrap_observable cs,
    map (config_of_harness_cursor wrap_observable) (step_harness_full cs) =
    step_harness_configs
      (map (config_of_harness_cursor wrap_observable) cs).
Proof.
  intros wrap_observable cs.
  induction cs as [| c rest IH].
  - reflexivity.
  - simpl.
    rewrite map_app.
    rewrite next_harness_config_commutes.
    rewrite IH.
    reflexivity.
Qed.

Lemma in_insert_harness_config :
  forall k x xs,
    In k (insert_harness_config x xs) <-> k = x \/ In k xs.
Proof.
  intros k x xs.
  unfold insert_harness_config.
  destruct (in_dec harness_config_eq_dec x xs) as [Hin | Hnot].
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

Lemma harness_config_keys_spec :
  forall ks k,
    In k (harness_config_keys ks) <-> In k ks.
Proof.
  induction ks as [| x rest IH]; intros k.
  - simpl. tauto.
  - simpl. rewrite in_insert_harness_config. rewrite IH.
    split; intro H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
    + destruct H as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
Qed.

Lemma in_step_harness_configs :
  forall ks k,
    In k (step_harness_configs ks) <->
    exists k0, In k0 ks /\ In k (next_harness_config k0).
Proof.
  induction ks as [| k0 rest IH]; intros k.
  - simpl. split; intro H.
    + contradiction.
    + destruct H as [_ [H _]]. contradiction.
  - simpl. rewrite in_app_iff. rewrite IH.
    split; intro H.
    + destruct H as [H | [k1 [Hin Hnext]]].
      * exists k0. split.
        -- left. reflexivity.
        -- exact H.
      * exists k1. split.
        -- right. exact Hin.
        -- exact Hnext.
    + destruct H as [k1 [[Hhead | Hin] Hnext]].
      * subst. left. exact Hnext.
      * right. exists k1. split; assumption.
Qed.

Theorem step_harness_dedup_quotient_sound :
  forall wrap_observable cs k,
    In k
      (harness_config_set_of_cursors
        wrap_observable
        (step_harness_full cs))
    <->
    In k
      (harness_config_keys
        (step_harness_configs
          (harness_config_set_of_cursors wrap_observable cs))).
Proof.
  intros wrap_observable cs k.
  unfold harness_config_set_of_cursors.
  rewrite (harness_config_keys_spec
    (map (config_of_harness_cursor wrap_observable) (step_harness_full cs)) k).
  rewrite (harness_config_keys_spec
    (step_harness_configs
      (harness_config_keys
        (map (config_of_harness_cursor wrap_observable) cs))) k).
  rewrite step_harness_config_commutes.
  rewrite in_step_harness_configs.
  rewrite in_step_harness_configs.
  split; intros [k0 [Hin Hnext]].
  - exists k0. split.
    + rewrite harness_config_keys_spec. exact Hin.
    + exact Hnext.
  - exists k0. split.
    + rewrite <- harness_config_keys_spec. exact Hin.
    + exact Hnext.
Qed.
