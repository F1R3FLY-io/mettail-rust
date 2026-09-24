(** Binder-presence observation through the ORIGINAL parameter worklist.

    Source: ast/src/grammar_shapes.rs::{param,rule,language}_declares_binder
    and prattail/src/wpda_rule_analysis/binder/term_param.rs. The latter is
    relocated, not replaced: reversed child pushes, pop order, original handles,
    optional flags and BOTH reads of a nonoptional parameter remain unchanged.
    TermParamReaderProjection already proves those transition observations.

    The new consumer asks only whether an Abstraction or MultiAbstraction leaf
    occurs. Optional groups are traversed; Simple and GuardBody are false.
    Each reached rule evaluates its context and then its legacy items BEFORE
    combining their booleans. A true context does not skip the item observation.
    The outer rule any stops after the first true rule.

    A finite structural predicate witness below states exactly the original
    recursive equations. It is a theorem premise about the source adapter, not
    an axiom or a claim that arbitrary cyclic readers have a recursive meaning.
    Reader/source simulation and finite successful scans preserve this witness.
    Explicit positive source-site debits bound traversed occurrences, including
    repeated DAG handles; no visited-set deduplication is introduced.

    Event lists are mathematical execution traces ONLY. Rust checks sites inline
    and never allocates a precomputed plan. The public fallible predicate owns
    its iterator and returns no partial bool/state on error; private traversal
    methods are not a public resumable-error API. Existing Iterator callers use
    the same worker with infallible admission. Allocation, reader validation,
    callbacks' internal CPU costs, Rust extraction and all-input parser semantics
    are outside this scoped correspondence claim.
*)
From Stdlib Require Import List Bool Arith Lia.
From PrattailWpdaRuntime Require Import TermParamReaderProjection ReconstructionWorkBudget.
Import ListNotations.
Set Implicit Arguments.

Module BinderPresenceProjection.
Module P := TermParamReaderProjection.TermParamReaderProjection.

Definition leaf_binds (leaf : P.Leaf) := match P.kind leaf with
| P.LAbstraction _ _ _ _ | P.LMultiAbstraction _ _ _ _ => true
| P.LSimple _ _ _ | P.LGuardBody _ _ => false end.

(** These are the five original recursive branches, not a binder classifier. *)
Definition OriginalPredicate store (meaning : nat -> bool) := forall handle,
  meaning handle = match P.source_param store handle with
  | P.SSimple _ _ | P.SGuardBody _ => false
  | P.SAbstraction _ _ _ | P.SMultiAbstraction _ _ _ => true
  | P.SOptional children => existsb meaning (P.source_parameters store children)
  end.
Definition work_binds meaning (work : P.Work) :=
  existsb (fun entry => meaning (fst entry)) work.

Lemma tagged_predicate : forall meaning handles flag,
  work_binds meaning (P.tagged handles flag) = existsb meaning handles.
Proof.
  intros meaning handles flag. induction handles as [|handle rest IH].
  - reflexivity.
  - change (meaning handle || work_binds meaning (P.tagged rest flag) =
      meaning handle || existsb meaning rest).
    now rewrite IH.
Qed.

Theorem original_step_preserves_binder_answer : forall store meaning work,
  OriginalPredicate store meaning ->
  match P.source_step store work with
  | P.Done => work_binds meaning work = false
  | P.Continue remaining _ => work_binds meaning work = work_binds meaning remaining
  | P.Yield leaf remaining _ =>
      work_binds meaning work = orb (leaf_binds leaf) (work_binds meaning remaining)
  | P.InvalidReader => False end.
Proof.
  intros store meaning [|[handle flag] rest] Law; [reflexivity|].
  pose proof (Law handle) as Branch.
  unfold P.source_step. destruct (P.source_param store handle) eqn:Shape;
    cbn [work_binds fst existsb leaf_binds P.kind] in *; try now rewrite Branch.
  unfold work_binds. rewrite existsb_app.
  change (meaning handle || work_binds meaning rest =
    work_binds meaning (P.tagged (P.source_parameters store parameters) true) ||
    work_binds meaning rest).
  rewrite tagged_predicate, Branch. reflexivity.
Qed.

(** Fuel is a finite-execution proof horizon, not a new Rust traversal. *)
Fixpoint scan (step : P.Work -> P.Step) fuel work : option bool := match fuel with
| 0 => None
| S remaining => match step work with
  | P.Done => Some false
  | P.Continue next _ => scan step remaining next
  | P.Yield leaf next _ => if leaf_binds leaf then Some true else scan step remaining next
  | P.InvalidReader => None end end.

Theorem reader_scan_is_original_scan : forall fuel store work,
  scan (P.reader_step (P.view_reader (P.project_store store))) fuel work =
  scan (P.source_step store) fuel work.
Proof.
  induction fuel; intros; cbn [scan]; [reflexivity|].
  rewrite P.original_step_correspondence.
  destruct (P.source_step store work); try reflexivity; [apply IHfuel|].
  destruct (leaf_binds leaf); [reflexivity|apply IHfuel].
Qed.

Theorem successful_scan_is_original_recursive_predicate : forall fuel store meaning work answer,
  OriginalPredicate store meaning -> scan (P.source_step store) fuel work = Some answer ->
  answer = work_binds meaning work.
Proof.
  induction fuel; intros store meaning work answer Law Run; [discriminate|].
  pose proof (@original_step_preserves_binder_answer store meaning work Law) as Step.
  cbn [scan] in Run. destruct (P.source_step store work) as [|next seen|leaf next seen|];
    try discriminate.
  - inversion Run; subst; symmetry; exact Step.
  - rewrite Step. eapply IHfuel; eauto.
  - destruct (leaf_binds leaf) eqn:Bind.
    + inversion Run; subst. rewrite Step. reflexivity.
    + rewrite Step; cbn. eapply IHfuel; eauto.
Qed.

Theorem first_binder_leaf_stops_before_remaining_work : forall fuel step work leaf rest trace,
  step work = P.Yield leaf rest trace -> leaf_binds leaf = true ->
  scan step (S fuel) work = Some true.
Proof. intros; cbn; now rewrite H, H0. Qed.

Inductive Event :=
| ReadLength (sequence : nat) | ReserveFrames (count : nat)
| ReadIndex (sequence index : nat) | PushFrame (handle : nat) (optional : bool)
| PopFrame (handle : nat) | ObserveFirst (handle : nat) | ObserveSecond (handle : nat)
| ReadContext (rule : nat) | ReadItems (rule : nat) | ReadItem (rule index : nat).

(** ReadLength, reserve, then reversed index/read/push pairs. A reservation
    failure precedes ALL corresponding pushes, including an empty expansion. *)
Definition push_events store sequence flag :=
  let handles := P.source_parameters store sequence in
  [ReadLength sequence; ReserveFrames (length handles)] ++
  flat_map (fun index => match nth_error handles index with
    | Some handle => [ReadIndex sequence index; PushFrame handle flag]
    | None => [ReadIndex sequence index] end) (rev (seq 0 (length handles))).
Definition step_events store (work : P.Work) := match work with
| [] => []
| (handle, _) :: _ => [PopFrame handle; ObserveFirst handle] ++
    match P.source_param store handle with
    | P.SOptional children => push_events store children true
    | _ => [ObserveSecond handle] end end.

Theorem optional_expansion_has_one_parameter_read : forall store handle flag rest children,
  P.source_param store handle = P.SOptional children ->
  step_events store ((handle,flag)::rest) =
    [PopFrame handle; ObserveFirst handle] ++ push_events store children true.
Proof. intros; unfold step_events; now rewrite H. Qed.
Theorem nonoptional_has_both_original_reads : forall store handle flag rest,
  (forall children, P.source_param store handle <> P.SOptional children) ->
  step_events store ((handle,flag)::rest) =
    [PopFrame handle; ObserveFirst handle; ObserveSecond handle].
Proof.
  intros; unfold step_events. destruct (P.source_param store handle) eqn:Shape;
    try reflexivity. exfalso; apply (H parameters); reflexivity.
Qed.
Theorem reserve_precedes_reversed_pushes : forall store sequence flag,
  exists pushes, push_events store sequence flag =
    ReadLength sequence :: ReserveFrames (length (P.source_parameters store sequence)) :: pushes.
Proof. intros; eexists; reflexivity. Qed.

Fixpoint scan_schedule store fuel work : option bool * list Event := match fuel with
| 0 => (None, [])
| S remaining =>
  let sites := step_events store work in
  match P.source_step store work with
  | P.Done => (Some false, sites)
  | P.InvalidReader => (None, sites)
  | P.Continue next _ => let '(answer, later) := scan_schedule store remaining next in
      (answer, sites ++ later)
  | P.Yield leaf next _ => if leaf_binds leaf then (Some true, sites)
      else let '(answer, later) := scan_schedule store remaining next in
        (answer, sites ++ later) end end.
Theorem schedule_projects_original_scan : forall fuel store work,
  fst (scan_schedule store fuel work) = scan (P.source_step store) fuel work.
Proof.
  induction fuel; intros; cbn [scan_schedule scan]; [reflexivity|].
  destruct (P.source_step store work); cbn; try reflexivity.
  - specialize (IHfuel store remaining). destruct (scan_schedule store fuel remaining); exact IHfuel.
  - destruct (leaf_binds leaf); [reflexivity|].
    specialize (IHfuel store remaining). destruct (scan_schedule store fuel remaining); exact IHfuel.
Qed.

(** Legacy items are observed in order until the first Binder item. *)
Fixpoint item_schedule rule index (items : list bool) : bool * list Event := match items with
| [] => (false, [])
| true :: _ => (true, [ReadItem rule index])
| false :: rest => let '(answer, later) := item_schedule rule (S index) rest in
    (answer, ReadItem rule index :: later) end.
Lemma item_schedule_is_original_any : forall items rule index,
  fst (item_schedule rule index items) = existsb (fun b => b) items.
Proof.
  induction items as [|head rest IH]; intros; cbn; [reflexivity|].
  destruct head; [reflexivity|]. specialize (IH rule (S index)).
  destruct (item_schedule rule (S index) rest); exact IH.
Qed.
Definition context_schedule store fuel (context : option nat) := match context with
| None => (Some false, [])
| Some params => let '(answer, later) := scan_schedule store fuel (P.source_initial store params false) in
    (answer, push_events store params false ++ later) end.
Definition rule_schedule store fuel rule context items :=
  let '(context_answer, context_sites) := context_schedule store fuel context in
  match context_answer with
  | None => (None, ReadContext rule :: context_sites)
  | Some binds_context =>
      let '(binds_items, item_sites) := item_schedule rule 0 items in
      (Some (binds_context || binds_items),
        ReadContext rule :: context_sites ++ ReadItems rule :: item_sites)
  end.
Theorem true_context_still_observes_items : forall store fuel rule context items sites,
  context_schedule store fuel context = (Some true, sites) ->
  rule_schedule store fuel rule context items =
    (Some true, ReadContext rule :: sites ++ ReadItems rule :: snd (item_schedule rule 0 items)).
Proof.
  intros; unfold rule_schedule; rewrite H. destruct (item_schedule rule 0 items); reflexivity.
Qed.
Theorem rule_combines_both_original_predicates : forall store fuel rule context items answer sites,
  context_schedule store fuel context = (Some answer, sites) ->
  fst (rule_schedule store fuel rule context items) =
    Some (answer || existsb (fun b => b) items).
Proof.
  intros; unfold rule_schedule; rewrite H.
  pose proof (item_schedule_is_original_any items rule 0) as Items.
  destruct (item_schedule rule 0 items); cbn in *; now rewrite Items.
Qed.

Section Language.
Variable observe_rule : nat -> option bool * list Event.
Fixpoint language_schedule rules := match rules with
| [] => (Some false, [])
| rule :: rest => let '(answer, sites) := observe_rule rule in
    match answer with
    | None => (None, sites)
    | Some true => (Some true, sites)
    | Some false => let '(result, later) := language_schedule rest in
        (result, sites ++ later) end end.
Theorem language_first_true_stops : forall rule rest sites,
  observe_rule rule = (Some true, sites) ->
  language_schedule (rule :: rest) = (Some true, sites).
Proof. intros; cbn; now rewrite H. Qed.
Theorem language_first_failure_stops : forall rule rest sites,
  observe_rule rule = (None, sites) ->
  language_schedule (rule :: rest) = (None, sites).
Proof. intros; cbn; now rewrite H. Qed.
Theorem successful_language_is_original_any : forall meaning,
  (forall rule, fst (observe_rule rule) = Some (meaning rule)) -> forall rules,
  fst (language_schedule rules) = Some (existsb meaning rules).
Proof.
  intros meaning Exact rules; induction rules as [|rule rest IH]; [reflexivity|].
  cbn. specialize (Exact rule). destruct (observe_rule rule) as [answer sites]; cbn in Exact.
  rewrite Exact. destruct (meaning rule); [reflexivity|].
  destruct (language_schedule rest); exact IH.
Qed.
End Language.

(** One policy supplies positive logical costs; reserve success is separate.
    Every occurrence is paid, even when several parents refer to one handle. *)
Section Admission.
Variable cost : Event -> nat.
Variable reserved : Event -> bool.
Inductive Payment := Paid (remaining : nat) (visited : list Event)
  | Refused (visited : list Event).
Definition prepend site result := match result with
| Paid remaining sites => Paid remaining (site::sites)
| Refused sites => Refused (site::sites) end.
Fixpoint pay remaining sites := match sites with
| [] => Paid remaining []
| site::rest => match debit remaining (cost site) with
  | None => Refused [site]
  | Some next => if reserved site then prepend site (pay next rest)
      else Refused [site] end end.
Definition visited payment := match payment with Paid _ sites | Refused sites => sites end.
Theorem refused_site_has_no_suffix : forall site rest remaining,
  debit remaining (cost site) = None -> pay remaining (site::rest) = Refused [site].
Proof. intros; cbn; now rewrite H. Qed.
Theorem failed_reservation_prevents_pushes : forall site rest remaining next,
  debit remaining (cost site) = Some next -> reserved site = false ->
  pay remaining (site::rest) = Refused [site].
Proof. intros; cbn; now rewrite H, H0. Qed.
Theorem only_source_prefix_is_visited : forall sites remaining,
  exists suffix, sites = visited (pay remaining sites) ++ suffix.
Proof.
  induction sites as [|site rest IH]; intros; cbn; [exists []; reflexivity|].
  destruct (debit remaining (cost site)) as [next|]; [|exists rest; reflexivity].
  destruct (reserved site); [|exists rest; reflexivity].
  destruct (IH next) as [suffix Prefix]. exists suffix.
  destruct (pay next rest); cbn in *; now rewrite Prefix.
Qed.
Theorem successful_payment_exact : forall sites remaining next trace,
  pay remaining sites = Paid next trace ->
  trace = sites /\ debit_all remaining (map cost sites) = Some next.
Proof.
  induction sites as [|site rest IH]; intros remaining next trace Run; cbn in Run.
  - inversion Run; subst; auto.
  - destruct (debit remaining (cost site)) as [middle|] eqn:Debit; [|discriminate].
    destruct (reserved site); [|discriminate].
    destruct (pay middle rest) as [last seen|seen] eqn:Rest; [|discriminate].
    destruct (IH middle last seen Rest) as [Trace Exact]. inversion Run; subst.
    split; [reflexivity|cbn; now rewrite Debit, Exact].
Qed.
Theorem repeated_occurrences_are_bounded : forall sites remaining next trace,
  Forall (fun site => 0 < cost site) sites -> pay remaining sites = Paid next trace ->
  length sites <= remaining.
Proof.
  intros sites remaining next trace Positive Run.
  destruct (@successful_payment_exact sites remaining next trace Run) as [_ Exact].
  pose proof (positive_control_steps_are_bounded_by_the_initial_budget
    (map cost sites) remaining next) as Bound.
  rewrite length_map in Bound. apply Bound; [now apply Forall_map|exact Exact].
Qed.
Definition publish remaining (schedule : option bool * list Event) : option bool :=
  match pay remaining (snd schedule) with
  | Paid _ _ => fst schedule
  | Refused _ => None end.
Theorem refusal_publishes_no_partial_boolean : forall remaining schedule trace,
  pay remaining (snd schedule) = Refused trace -> publish remaining schedule = None.
Proof. intros; unfold publish; now rewrite H. Qed.
Theorem admitted_scan_uses_existing_worker_answer : forall remaining store fuel work next trace,
  pay remaining (snd (scan_schedule store fuel work)) = Paid next trace ->
  publish remaining (scan_schedule store fuel work) = scan (P.source_step store) fuel work.
Proof. intros; unfold publish; rewrite H; apply schedule_projects_original_scan. Qed.
End Admission.

Print Assumptions original_step_preserves_binder_answer.
Print Assumptions reader_scan_is_original_scan.
Print Assumptions successful_scan_is_original_recursive_predicate.
Print Assumptions first_binder_leaf_stops_before_remaining_work.
Print Assumptions optional_expansion_has_one_parameter_read.
Print Assumptions nonoptional_has_both_original_reads.
Print Assumptions reserve_precedes_reversed_pushes.
Print Assumptions schedule_projects_original_scan.
Print Assumptions item_schedule_is_original_any.
Print Assumptions true_context_still_observes_items.
Print Assumptions rule_combines_both_original_predicates.
Print Assumptions language_first_true_stops.
Print Assumptions language_first_failure_stops.
Print Assumptions successful_language_is_original_any.
Print Assumptions refused_site_has_no_suffix.
Print Assumptions failed_reservation_prevents_pushes.
Print Assumptions only_source_prefix_is_visited.
Print Assumptions successful_payment_exact.
Print Assumptions repeated_occurrences_are_bounded.
Print Assumptions refusal_publishes_no_partial_boolean.
Print Assumptions admitted_scan_uses_existing_worker_answer.

End BinderPresenceProjection.
