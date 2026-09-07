(*
 * Completed-family semantics for the retained reconstruction scheduler.
 *
 * A row is one existing packing/flat alternative after structural preparation.
 * The row list is ghost notation for Bin's packing and flat cursors; it is not
 * a second runtime allocation. Refused rows demand no semantic dependencies.
 * Structural Intermediate packings belong to preparation, not to the semantic
 * action labels. Preparation must report a structural cycle as a fault.
 *
 * Families and accumulators are deliberately distinct: node-specific
 * observation can perform the existing exact deduplication and representative
 * weight selection. It is not silently replaced by list concatenation.
 * All successful relations exclude preparation, assembly and observation
 * faults. Cyclic AST fixed-point completeness is not asserted by this model.
 *)
From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
Set Implicit Arguments.

Section Scheduler.
  Context {Family Accumulator Label Fault : Type}.

  Record row := {
    origin_packing : nat;
    original_flat : list nat;
    admitted : bool;
    dependencies : list nat;
    assembly_label : Label
  }.

  Variable prepare : nat -> Fault + list row.
  Variable initial_accumulator : nat -> Accumulator.
  Variable finish_accumulator : Accumulator -> Family.
  Variable assemble_complete : row -> list Family -> Fault + Family.
  Variable observe : nat -> Accumulator -> Family -> Fault + Accumulator.

  (* These relations specify whole finite successful families, not a chosen
     candidate or a ranked prefix. Each dependency occurrence has a position,
     even when two positions name the same already-completed shared node. *)
  Inductive node_denotes : nat -> Family -> Prop :=
  | NodeDenotes : forall node rows final,
      prepare node = inr rows ->
      rows_denote node rows (initial_accumulator node) final ->
      node_denotes node (finish_accumulator final)
  with rows_denote : nat -> list row -> Accumulator -> Accumulator -> Prop :=
  | RowsDone : forall node acc, rows_denote node [] acc acc
  | RowsRefused : forall node first rest acc final,
      admitted first = false ->
      rows_denote node rest acc final ->
      rows_denote node (first :: rest) acc final
  | RowsAssembled : forall node first rest acc next final inputs family,
      admitted first = true ->
      dependencies_denote (dependencies first) inputs ->
      assemble_complete first inputs = inr family ->
      observe node acc family = inr next ->
      rows_denote node rest next final ->
      rows_denote node (first :: rest) acc final
  with dependencies_denote : list nat -> list Family -> Prop :=
  | DependenciesDone : dependencies_denote [] []
  | DependencyComplete : forall node rest family families,
      node_denotes node family -> dependencies_denote rest families ->
      dependencies_denote (node :: rest) (family :: families).

  Lemma processed_rows_compose_in_order : forall node prefix initial middle,
    rows_denote node prefix initial middle -> forall suffix final,
    rows_denote node suffix middle final ->
    rows_denote node (prefix ++ suffix) initial final.
  Proof.
    intros node prefix initial middle H.
    induction H; intros suffix output Hsuffix; cbn.
    - exact Hsuffix.
    - eapply RowsRefused; eauto.
    - eapply RowsAssembled; eauto.
  Qed.

  (* Logical continuation for a frame's already-processed row prefix. This
     invariant preserves its exact owner/accumulator semantics as the row
     cursor advances, without storing a duplicate prefix in the machine. *)
  Definition frame_context (node : nat) (rows : list row) (acc : Accumulator) : Prop :=
    forall final, rows_denote node rows acc final ->
      node_denotes node (finish_accumulator final).

  Lemma newly_prepared_frame_has_its_exact_context : forall node rows,
    prepare node = inr rows -> frame_context node rows (initial_accumulator node).
  Proof.
    intros node rows Hprepare final Hrows. econstructor; eauto.
  Qed.

  Lemma refusing_a_row_preserves_the_frame_context : forall node first rest acc,
    frame_context node (first :: rest) acc -> admitted first = false ->
    frame_context node rest acc.
  Proof.
    intros node first rest acc Hcontext Hrefused final Hrest.
    apply Hcontext. now apply RowsRefused.
  Qed.

  Lemma observing_a_complete_row_preserves_the_frame_context :
    forall node first rest acc next inputs family,
    frame_context node (first :: rest) acc -> admitted first = true ->
    dependencies_denote (dependencies first) inputs ->
    assemble_complete first inputs = inr family ->
    observe node acc family = inr next -> frame_context node rest next.
  Proof.
    intros node first rest acc next inputs family Hcontext Hadmitted Hinputs Hassemble Hobserve
      final Hrest. apply Hcontext. eapply RowsAssembled; eauto.
  Qed.

  Lemma exhausted_frame_denotes_a_complete_family : forall node acc,
    frame_context node [] acc -> node_denotes node (finish_accumulator acc).
  Proof.
    intros node acc H. apply H. constructor.
  Qed.

  Definition completed_memo := nat -> option Family.

  Definition memo_correct (memo : completed_memo) : Prop :=
    forall node family, memo node = Some family -> node_denotes node family.

  Definition dependencies_ready (memo : completed_memo) (nodes : list nat) : Prop :=
    forall node, In node nodes -> exists family, memo node = Some family.

  Fixpoint read_families (memo : completed_memo) (nodes : list nat) : option (list Family) :=
    match nodes with
    | [] => Some []
    | node :: rest => match memo node, read_families memo rest with
        | Some family, Some families => Some (family :: families)
        | _, _ => None
        end
    end.

  Lemma reading_completed_dependencies_preserves_denotation : forall memo nodes families,
    memo_correct memo -> read_families memo nodes = Some families ->
    dependencies_denote nodes families.
  Proof.
    intros memo nodes. induction nodes as [|node rest IH]; intros families Hmemo Hread; cbn in Hread.
    - inversion Hread; constructor.
    - destruct (memo node) as [family|] eqn:Hnode,
        (read_families memo rest) as [tail|] eqn:Htail; try discriminate.
      inversion Hread; subst. constructor.
      + now apply (Hmemo node).
      + now apply IH.
  Qed.

  Lemma ready_dependencies_have_an_ordered_read : forall memo nodes,
    dependencies_ready memo nodes -> exists families, read_families memo nodes = Some families.
  Proof.
    intros memo nodes. induction nodes as [|node rest IH]; intro Hready.
    - exists []. reflexivity.
    - destruct (Hready node (or_introl eq_refl)) as [family Hnode].
      destruct IH as [families Hrest].
      { intros child Hchild. apply Hready. now right. }
      exists (family :: families). cbn. now rewrite Hnode, Hrest.
  Qed.

  Lemma repeated_dependency_positions_are_not_collapsed : forall memo node family,
    memo node = Some family -> read_families memo [node; node] = Some [family; family].
  Proof. intros; cbn; now rewrite H. Qed.

  Definition publish_complete (memo : completed_memo) (node : nat) (family : Family)
    : completed_memo := fun query => if Nat.eqb query node then Some family else memo query.

  Definition memo_extends (before after : completed_memo) : Prop :=
    forall node family, before node = Some family -> after node = Some family.

  Lemma complete_publication_preserves_memo_correctness : forall memo node family,
    memo_correct memo -> node_denotes node family ->
    memo_correct (publish_complete memo node family).
  Proof.
    intros memo node family Hmemo Hfamily query value Hread.
    unfold publish_complete in Hread. destruct (Nat.eqb query node) eqn:Hequal.
    - apply Nat.eqb_eq in Hequal. subst. inversion Hread; subst. exact Hfamily.
    - now apply (Hmemo query).
  Qed.

  Lemma publication_does_not_overwrite_a_completed_dependency : forall memo node family,
    memo node = None -> memo_extends memo (publish_complete memo node family).
  Proof.
    intros memo node family Habsent query value Hread. unfold publish_complete.
    destruct (Nat.eqb query node) eqn:Hequal; [|exact Hread].
    apply Nat.eqb_eq in Hequal. subst. rewrite Habsent in Hread. discriminate.
  Qed.

  Lemma completed_dependencies_stay_ready : forall before after nodes,
    memo_extends before after -> dependencies_ready before nodes -> dependencies_ready after nodes.
  Proof.
    intros before after nodes Hextends Hready node Hin.
    destruct (Hready node Hin) as [family Hfamily]. exists family. now apply Hextends.
  Qed.

  Inductive enter_decision :=
  | ReuseComplete : Family -> enter_decision
  | UnresolvedCycle : enter_decision
  | PrepareFresh : enter_decision.

  Definition decide_enter (memo : completed_memo) (active : list nat) (node : nat) :=
    match memo node with
    | Some family => ReuseComplete family
    | None => if existsb (Nat.eqb node) active then UnresolvedCycle else PrepareFresh
    end.

  Theorem completed_sharing_reuses_the_family : forall memo active node family,
    memo node = Some family -> decide_enter memo active node = ReuseComplete family.
  Proof. intros; unfold decide_enter; now rewrite H. Qed.

  Theorem active_reentry_is_not_successful_absence : forall memo active node,
    memo node = None -> In node active -> decide_enter memo active node = UnresolvedCycle.
  Proof.
    intros memo active node Hmemo Hin. unfold decide_enter. rewrite Hmemo.
    assert (Hactive : existsb (Nat.eqb node) active = true).
    { apply existsb_exists. exists node. split; [exact Hin|apply Nat.eqb_refl]. }
    now rewrite Hactive.
  Qed.

  (* The frame has one owner and one row cursor. Children/AwaitChild contain
     the source-ordered processed prefix and pending suffix of the current
     row's dependency list. They are ghost views of an integer cursor, not
     two runtime copies of that list. AwaitChild records the suspended call. *)
  Inductive phase :=
  | ScanRows
  | Children : list nat -> list nat -> phase
  | AwaitChild : list nat -> nat -> list nat -> phase
  | LeaveRow.

  Record frame := Frame {
    owner : nat;
    rows_left : list row;
    accumulated : Accumulator;
    frame_phase : phase
  }.

  Definition prepared_suffix (node : nat) (rows : list row) : Prop :=
    exists prefix, prepare node = inr (prefix ++ rows).

  Definition phase_ready (memo : completed_memo) (rows : list row) (at_phase : phase) : Prop :=
    match at_phase with
    | ScanRows => True
    | Children done pending => match rows with
        | [] => False
        | first :: _ => admitted first = true /\
            dependencies first = done ++ pending /\ dependencies_ready memo done
        end
    | AwaitChild done child pending => match rows with
        | [] => False
        | first :: _ => admitted first = true /\
            dependencies first = done ++ child :: pending /\ dependencies_ready memo done
        end
    | LeaveRow => match rows with
        | [] => False
        | first :: _ => admitted first = true /\ dependencies_ready memo (dependencies first)
        end
    end.

  Definition frame_invariant (memo : completed_memo) (current : frame) : Prop :=
    frame_context (owner current) (rows_left current) (accumulated current) /\
    prepared_suffix (owner current) (rows_left current) /\
    phase_ready memo (rows_left current) (frame_phase current).

  Lemma ready_dependencies_append : forall memo first rest,
    dependencies_ready memo first -> dependencies_ready memo rest ->
    dependencies_ready memo (first ++ rest).
  Proof.
    intros memo first rest Hfirst Hrest node Hin. apply in_app_iff in Hin.
    destruct Hin; [now apply Hfirst|now apply Hrest].
  Qed.

  Lemma completed_singleton_is_ready : forall memo node family,
    memo node = Some family -> dependencies_ready memo [node].
  Proof.
    intros memo node family Hmemo query [Hequal|Hfalse]; [|contradiction].
    subst. now exists family.
  Qed.

  Lemma moving_past_a_prepared_row_keeps_a_prepared_suffix : forall node first rest,
    prepared_suffix node (first :: rest) -> prepared_suffix node rest.
  Proof.
    intros node first rest [prefix Hprefix]. exists (prefix ++ [first]).
    now rewrite <- app_assoc.
  Qed.

  Lemma new_frame_satisfies_the_invariant : forall memo node rows,
    prepare node = inr rows -> frame_invariant memo (Frame node rows (initial_accumulator node) ScanRows).
  Proof.
    intros memo node rows Hprepare. repeat split.
    - now apply newly_prepared_frame_has_its_exact_context.
    - exists []. exact Hprepare.
  Qed.

  Lemma extending_completed_memo_preserves_the_frame_invariant : forall before after current,
    memo_extends before after -> frame_invariant before current -> frame_invariant after current.
  Proof.
    intros before after [node rows acc at_phase] Hextends [Hcontext [Hsuffix Hready]].
    split; [exact Hcontext|]. split; [exact Hsuffix|].
    destruct at_phase; cbn in *; [exact I| | |];
      destruct rows; cbn in *; try contradiction.
    - destruct Hready as [Hadmitted [Hdeps Hready]]. repeat split; auto.
      now apply (completed_dependencies_stay_ready Hextends).
    - destruct Hready as [Hadmitted [Hdeps Hready]]. repeat split; auto.
      now apply (completed_dependencies_stay_ready Hextends).
    - destruct Hready as [Hadmitted Hready]. split; [exact Hadmitted|].
      now apply (completed_dependencies_stay_ready Hextends).
  Qed.

  (* Local steps never publish a memo entry. In particular, finishing a row
     is not finishing its owner, which may have further alternatives. *)
  Inductive local_step (memo : completed_memo) : frame -> frame -> Prop :=
  | SkipRefused : forall node first rest acc,
      admitted first = false ->
      local_step memo (Frame node (first :: rest) acc ScanRows) (Frame node rest acc ScanRows)
  | StartAdmitted : forall node first rest acc,
      admitted first = true ->
      local_step memo (Frame node (first :: rest) acc ScanRows)
        (Frame node (first :: rest) acc (Children [] (dependencies first)))
  | ReuseDependency : forall node first rest acc done child pending family,
      memo child = Some family ->
      local_step memo (Frame node (first :: rest) acc (Children done (child :: pending)))
        (Frame node (first :: rest) acc (Children (done ++ [child]) pending))
  | ResumeDependency : forall node first rest acc done child pending family,
      memo child = Some family ->
      local_step memo (Frame node (first :: rest) acc (AwaitChild done child pending))
        (Frame node (first :: rest) acc (Children (done ++ [child]) pending))
  | DependenciesFinished : forall node first rest acc done,
      local_step memo (Frame node (first :: rest) acc (Children done []))
        (Frame node (first :: rest) acc LeaveRow)
  | ApplyCompleteRow : forall node first rest acc next inputs family,
      read_families memo (dependencies first) = Some inputs ->
      assemble_complete first inputs = inr family ->
      observe node acc family = inr next ->
      local_step memo (Frame node (first :: rest) acc LeaveRow) (Frame node rest next ScanRows).

  Lemma local_steps_keep_the_owner : forall memo before after,
    local_step memo before after -> owner before = owner after.
  Proof. intros memo before after H; destruct H; reflexivity. Qed.

  Theorem local_steps_preserve_exact_frame_semantics : forall memo before after,
    memo_correct memo -> local_step memo before after ->
    frame_invariant memo before -> frame_invariant memo after.
  Proof.
    intros memo before after Hmemo Hstep.
    destruct Hstep; intros [Hcontext [Hsuffix Hready]]; cbn in *.
    - split.
      + eapply refusing_a_row_preserves_the_frame_context; eauto.
      + split; [now apply (moving_past_a_prepared_row_keeps_a_prepared_suffix Hsuffix)|exact I].
    - split; [exact Hcontext|]. split; [exact Hsuffix|].
      split; [assumption|]. split; [reflexivity|]. intros dependency Hin. inversion Hin.
    - destruct Hready as [Hadmitted [Hdeps Hdone]].
      split; [exact Hcontext|]. split; [exact Hsuffix|].
      split; [exact Hadmitted|]. split; [now rewrite <- app_assoc|].
      apply ready_dependencies_append; [exact Hdone|]. eapply completed_singleton_is_ready; eauto.
    - destruct Hready as [Hadmitted [Hdeps Hdone]].
      split; [exact Hcontext|]. split; [exact Hsuffix|].
      split; [exact Hadmitted|]. split; [now rewrite <- app_assoc|].
      apply ready_dependencies_append; [exact Hdone|]. eapply completed_singleton_is_ready; eauto.
    - destruct Hready as [Hadmitted [Hdeps Hdone]].
      split; [exact Hcontext|]. split; [exact Hsuffix|].
      split; [exact Hadmitted|]. now rewrite Hdeps, app_nil_r.
    - destruct Hready as [Hadmitted Hdeps]. split.
      + eapply observing_a_complete_row_preserves_the_frame_context; eauto.
        eapply reading_completed_dependencies_preserves_denotation; eauto.
      + split; [now apply (moving_past_a_prepared_row_keeps_a_prepared_suffix Hsuffix)|exact I].
  Qed.

  (* Active owners are precisely the live frame owners. A concrete hash-set
     acceleration must preserve this derived view; memo membership is never
     used as an active marker. No active owner has a reusable memo entry. *)
  Definition machine_invariant (memo : completed_memo) (stack : list frame) : Prop :=
    memo_correct memo /\
    (forall current, In current stack ->
      frame_invariant memo current /\ memo (owner current) = None) /\
    NoDup (map owner stack).

  Inductive scheduler_step : completed_memo -> list frame -> completed_memo -> list frame -> Prop :=
  | StepLocal : forall memo before after tail,
      local_step memo before after ->
      scheduler_step memo (before :: tail) memo (after :: tail)
  | StepEnterChild : forall memo node first rest acc done child pending tail child_rows,
      memo child = None ->
      ~ In child (map owner (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail)) ->
      prepare child = inr child_rows ->
      scheduler_step memo
        (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail) memo
        (Frame child child_rows (initial_accumulator child) ScanRows ::
         Frame node (first :: rest) acc (AwaitChild done child pending) :: tail)
  | StepPublishComplete : forall memo node acc tail,
      scheduler_step memo (Frame node [] acc ScanRows :: tail)
        (publish_complete memo node (finish_accumulator acc)) tail.

  Theorem scheduler_steps_preserve_completed_family_invariants :
    forall before stack after next_stack,
    scheduler_step before stack after next_stack ->
    machine_invariant before stack -> machine_invariant after next_stack.
  Proof.
    intros before stack after next_stack Hstep.
    destruct Hstep as
      [memo first next tail Hlocal
      |memo node first rest acc done child pending tail child_rows Habsent Hfresh Hprepare
      |memo node acc tail]; intros [Hmemo [Hframes Hunique]].
    - pose proof (local_steps_keep_the_owner Hlocal) as Howner.
      destruct (Hframes first (or_introl eq_refl)) as [Hfirst Habsent].
      split; [exact Hmemo|]. split.
      + intros current [Hequal|Hin].
        * subst current. split.
          -- eapply local_steps_preserve_exact_frame_semantics; eauto.
          -- now rewrite <- Howner.
        * apply Hframes. now right.
      + cbn in *. now rewrite <- Howner.
    - assert (Hparent : frame_invariant memo
          (Frame node (first :: rest) acc (AwaitChild done child pending)) /\ memo node = None).
      { destruct (Hframes _ (or_introl eq_refl)) as [Hframe Hnone].
        exact (conj Hframe Hnone). }
      split; [exact Hmemo|]. split.
      + intros current [Hequal|[Hequal|Hin]].
        * subst current. split; [now apply new_frame_satisfies_the_invariant|exact Habsent].
        * now subst current.
        * apply Hframes. now right.
      + cbn in *. constructor; assumption.
    - destruct (Hframes _ (or_introl eq_refl)) as [[Hcontext [Hsuffix Hphase]] Habsent].
      cbn in Hcontext, Habsent.
      assert (Hdenotes : node_denotes node (finish_accumulator acc)).
      { now apply exhausted_frame_denotes_a_complete_family. }
      assert (Hextends : memo_extends memo (publish_complete memo node (finish_accumulator acc))).
      { now apply publication_does_not_overwrite_a_completed_dependency. }
      cbn in Hunique. inversion Hunique as [|head owners Hnotin Htail]; subst.
      split.
      + now apply complete_publication_preserves_memo_correctness.
      + split.
        * intros current Hin. destruct (Hframes current (or_intror Hin)) as [Hframe Hnone].
          split.
          -- eapply extending_completed_memo_preserves_the_frame_invariant; eauto.
          -- unfold publish_complete. destruct (Nat.eqb (owner current) node) eqn:Hequal;
               [|exact Hnone].
             apply Nat.eqb_eq in Hequal. exfalso. apply Hnotin.
             rewrite <- Hequal. now apply in_map.
        * exact Htail.
  Qed.

  Inductive scheduler_run : completed_memo -> list frame -> completed_memo -> list frame -> Prop :=
  | RunRefl : forall memo stack, scheduler_run memo stack memo stack
  | RunStep : forall first stack middle pending last final_stack,
      scheduler_step first stack middle pending ->
      scheduler_run middle pending last final_stack ->
      scheduler_run first stack last final_stack.

  Theorem every_reachable_scheduler_state_preserves_completed_families :
    forall first stack last final_stack,
    scheduler_run first stack last final_stack ->
    machine_invariant first stack -> machine_invariant last final_stack.
  Proof.
    intros first stack last final_stack Hrun. induction Hrun; intro Hinv.
    - exact Hinv.
    - apply IHHrun. eapply scheduler_steps_preserve_completed_family_invariants; eauto.
  Qed.

  Definition empty_memo : completed_memo := fun _ => None.

  Theorem initial_scheduler_state_satisfies_the_invariant : forall root rows,
    prepare root = inr rows ->
    machine_invariant empty_memo [Frame root rows (initial_accumulator root) ScanRows].
  Proof.
    intros root rows Hprepare. split.
    - intros node family Hread. discriminate.
    - split.
      + intros current [Hequal|Hfalse]; [|contradiction]. subst current.
        split; [now apply new_frame_satisfies_the_invariant|reflexivity].
      + repeat constructor. intro Hfalse. inversion Hfalse.
  Qed.

  Theorem finished_root_is_a_complete_family : forall root rows memo family,
    prepare root = inr rows ->
    scheduler_run empty_memo [Frame root rows (initial_accumulator root) ScanRows] memo [] ->
    memo root = Some family -> node_denotes root family.
  Proof.
    intros root rows memo family Hprepare Hrun Hfamily.
    pose proof (initial_scheduler_state_satisfies_the_invariant Hprepare) as Hinitial.
    destruct (every_reachable_scheduler_state_preserves_completed_families Hrun Hinitial)
      as [Hmemo _]. now apply (Hmemo root).
  Qed.

  (* A suspended root retains its whole frame and completed subordinate memo.
     It is a separate result constructor: no fabricated empty/completed root
     is published to make the old Vec-only API appear exhaustive. Faults carry
     no accumulator or output prefix, including faults after successful rows.
     The public result is composed with RealizationFailureBoundary's sticky
     first-failure publication barrier. *)
  Inductive request_failure :=
  | DependencyCycle : nat -> request_failure
  | PreparationFault : nat -> Fault -> request_failure
  | AssemblyFault : nat -> Fault -> request_failure
  | ObservationFault : nat -> Fault -> request_failure
  | SchedulerInvariantFault : nat -> request_failure
  | ResourceFault : request_failure.

  Inductive request_result :=
  | CompleteRoot : Family -> request_result
  | SuspendedRoot : completed_memo -> frame -> request_result
  | FailedRequest : request_failure -> request_result.

  Definition suspend_root (memo : completed_memo) (current : frame) : request_result :=
    SuspendedRoot memo current.

  Theorem root_suspension_has_no_completed_root_entry : forall memo current,
    machine_invariant memo [current] -> memo (owner current) = None.
  Proof.
    intros memo current [_ [Hframes _]]. now apply (Hframes current (or_introl eq_refl)).
  Qed.

  Theorem root_suspension_preserves_the_exact_memo_and_continuation : forall memo current,
    suspend_root memo current = SuspendedRoot memo current.
  Proof. reflexivity. Qed.

  Theorem failed_request_cannot_publish_a_family : forall fault family,
    FailedRequest fault <> CompleteRoot family.
  Proof. discriminate. Qed.

  Definition waiting_for (parent : frame) (child : nat) : Prop :=
    exists done pending, frame_phase parent = AwaitChild done child pending.

  Fixpoint suspended_call_links (stack : list frame) : Prop :=
    match stack with
    | [] => True
    | current :: tail => match tail with
        | [] => True
        | parent :: _ => waiting_for parent (owner current) /\ suspended_call_links tail
        end
    end.

  Definition top_resume_ready (memo : completed_memo) (stack : list frame) : Prop :=
    match stack with
    | [] => True
    | current :: _ => match frame_phase current with
        | AwaitChild _ child _ => exists family, memo child = Some family
        | _ => True
        end
    end.

  Definition control_invariant (memo : completed_memo) (stack : list frame) : Prop :=
    suspended_call_links stack /\ top_resume_ready memo stack.

  Lemma changing_the_top_phase_preserves_suspended_calls : forall first next tail,
    owner first = owner next -> suspended_call_links (first :: tail) ->
    suspended_call_links (next :: tail).
  Proof.
    intros first next [|parent tail] Howner Hlinks; cbn in *; [exact I|].
    now rewrite <- Howner.
  Qed.

  Theorem scheduler_steps_preserve_suspended_call_control : forall before stack after next_stack,
    scheduler_step before stack after next_stack ->
    control_invariant before stack -> control_invariant after next_stack.
  Proof.
    intros before stack after next_stack Hstep.
    destruct Hstep as
      [memo first next tail Hlocal
      |memo node first rest acc done child pending tail child_rows Habsent Hfresh Hprepare
      |memo node acc tail]; intros [Hlinks Hresume].
    - split.
      + eapply changing_the_top_phase_preserves_suspended_calls with (first := first).
        * exact (local_steps_keep_the_owner Hlocal).
        * exact Hlinks.
      + destruct Hlocal; exact I.
    - split; [|exact I]. cbn. split.
      + exists done, pending. reflexivity.
      + exact Hlinks.
    - destruct tail as [|parent tail]; [split; exact I|].
      cbn in Hlinks. destruct Hlinks as [[done [pending Hwaiting]] Hlinks].
      split; [exact Hlinks|]. unfold top_resume_ready. rewrite Hwaiting.
      exists (finish_accumulator acc). unfold publish_complete. cbn. now rewrite Nat.eqb_refl.
  Qed.

  Theorem every_reachable_scheduler_state_has_valid_call_control :
    forall first stack last final_stack,
    scheduler_run first stack last final_stack ->
    control_invariant first stack -> control_invariant last final_stack.
  Proof.
    intros first stack last final_stack Hrun. induction Hrun; intro Hinv.
    - exact Hinv.
    - apply IHHrun. eapply scheduler_steps_preserve_suspended_call_control; eauto.
  Qed.

  (* Only admitted semantic dependencies need a decreasing rank. A refused
     row may contain arbitrary references without introducing evaluation or
     a false cycle. The rank is a proof witness, not a runtime depth limit. *)
  Definition admitted_dependency_rank (rank : nat -> nat) : Prop :=
    forall node rows current child,
    prepare node = inr rows -> In current rows -> admitted current = true ->
    In child (dependencies current) -> rank child < rank node.

  Lemma prepared_admitted_row_decreases_rank : forall rank node first rest child,
    admitted_dependency_rank rank -> prepared_suffix node (first :: rest) ->
    admitted first = true -> In child (dependencies first) -> rank child < rank node.
  Proof.
    intros rank node first rest child Hrank [prefix Hprepare] Hadmitted Hin.
    eapply Hrank; eauto. apply in_app_iff. right. now left.
  Qed.

  Lemma suspended_parent_has_strictly_greater_rank : forall rank memo parent child,
    admitted_dependency_rank rank -> frame_invariant memo parent ->
    waiting_for parent child -> rank child < rank (owner parent).
  Proof.
    intros rank memo [node rows acc at_phase] child Hrank [Hcontext [Hsuffix Hready]]
      [done [pending Hwaiting]]. cbn in Hwaiting. subst at_phase. cbn in *.
    destruct rows as [|first rest]; [contradiction|].
    destruct Hready as [Hadmitted [Hdeps Hdone]].
    eapply prepared_admitted_row_decreases_rank; eauto.
    rewrite Hdeps. apply in_app_iff. right. now left.
  Qed.

  Lemma active_ancestors_have_at_least_the_top_rank : forall rank memo,
    admitted_dependency_rank rank -> forall tail top,
    (forall current, In current (top :: tail) -> frame_invariant memo current) ->
    suspended_call_links (top :: tail) -> forall node,
    In node (map owner (top :: tail)) -> rank (owner top) <= rank node.
  Proof.
    intros rank memo Hrank tail. induction tail as [|parent tail IH];
      intros top Hframes Hlinks node Hin.
    - cbn in Hin. destruct Hin as [Hequal|Hfalse]; [subst; lia|contradiction].
    - cbn in Hlinks. destruct Hlinks as [Hwaiting Hlinks].
      cbn in Hin. destruct Hin as [Hequal|Hin]; [subst; lia|].
      assert (Hedge : rank (owner top) < rank (owner parent)).
      { eapply suspended_parent_has_strictly_greater_rank; eauto. apply Hframes. right. now left. }
      assert (Hancestor : rank (owner parent) <= rank node).
      { apply (IH parent); [|exact Hlinks|exact Hin].
        intros current Hcurrent. apply Hframes. now right. }
      lia.
  Qed.

  Theorem admitted_dag_demand_cannot_reenter_an_active_owner :
    forall rank memo node first rest acc done child pending tail,
    admitted_dependency_rank rank ->
    machine_invariant memo
      (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail) ->
    suspended_call_links
      (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail) ->
    ~ In child (map owner
      (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail)).
  Proof.
    intros rank memo node first rest acc done child pending tail Hrank
      [Hmemo [Hframes Hunique]] Hlinks Hin.
    destruct (Hframes _ (or_introl eq_refl)) as [[Hcontext [Hsuffix Hready]] Hnone].
    cbn in Hready. destruct Hready as [Hadmitted [Hdeps Hdone]].
    assert (Hchild : rank child < rank node).
    { eapply prepared_admitted_row_decreases_rank; eauto.
      rewrite Hdeps. apply in_app_iff. right. now left. }
    assert (Hancestor : rank node <= rank child).
    { eapply active_ancestors_have_at_least_the_top_rank with
        (memo := memo) (tail := tail)
        (top := Frame node (first :: rest) acc (Children done (child :: pending))); eauto.
      intros current Hcurrent. now apply (Hframes current Hcurrent). }
    lia.
  Qed.

  (* Memo-aware progress credit for the prepared-row machine. An unseen
     owner reserves its full local scan cost. Enter transfers that credit to
     its active frame; completion consumes the last unit and the completed
     memo prevents that owner becoming unseen again. This does not unfold a
     shared DAG into an exponential call tree and requires no runtime sum.
     Packing preparation/admin steps and semantic assembly have independent
     termination/resource contracts; these credits are not CPU instructions. *)
  Fixpoint scan_credit (rows : list row) : nat :=
    match rows with
    | [] => 1
    | first :: rest =>
        (if admitted first then 3 + 2 * length (dependencies first) else 1) + scan_credit rest
    end.

  Definition frame_credit (current : frame) : nat :=
    match frame_phase current with
    | ScanRows => scan_credit (rows_left current)
    | Children _ pending => match rows_left current with
        | [] => 1
        | _ :: rest => 2 * length pending + 2 + scan_credit rest
        end
    | AwaitChild _ _ pending => match rows_left current with
        | [] => 1
        | _ :: rest => 2 * length pending + 3 + scan_credit rest
        end
    | LeaveRow => match rows_left current with
        | [] => 1
        | _ :: rest => 1 + scan_credit rest
        end
    end.

  Definition owner_credit (node : nat) : nat :=
    match prepare node with inl _ => 1 | inr rows => scan_credit rows end.

  Definition unseen_credit (memo : completed_memo) (stack : list frame) (node : nat) : nat :=
    match memo node with
    | Some _ => 0
    | None => if existsb (Nat.eqb node) (map owner stack) then 0 else owner_credit node
    end.

  Definition sum_credits {A : Type} (credit : A -> nat) (items : list A) : nat :=
    fold_right (fun item total => credit item + total) 0 items.

  Definition scheduler_credit (universe : list nat) (memo : completed_memo) (stack : list frame) :=
    sum_credits (unseen_credit memo stack) universe + sum_credits frame_credit stack.

  Lemma every_unfinished_scan_has_positive_credit : forall rows, 0 < scan_credit rows.
  Proof.
    induction rows as [|first rest IH]; cbn; [lia|]. destruct (admitted first); lia.
  Qed.

  Lemma every_live_frame_has_positive_credit : forall current, 0 < frame_credit current.
  Proof.
    intros [node rows acc at_phase]. destruct at_phase; cbn.
    - apply every_unfinished_scan_has_positive_credit.
    - destruct rows; cbn; lia.
    - destruct rows; cbn; lia.
    - destruct rows; cbn; lia.
  Qed.

  Theorem local_steps_strictly_decrease_frame_credit : forall memo first next,
    local_step memo first next -> frame_credit next < frame_credit first.
  Proof.
    intros memo first next Hstep. destruct Hstep; cbn [frame_credit scan_credit rows_left frame_phase].
    - rewrite H. lia.
    - rewrite H. lia.
    - cbn. lia.
    - cbn. lia.
    - cbn. lia.
    - lia.
  Qed.

  Lemma active_owners_have_no_unseen_credit : forall memo stack node,
    In node (map owner stack) -> unseen_credit memo stack node = 0.
  Proof.
    intros memo stack node Hin. unfold unseen_credit. destruct (memo node); [reflexivity|].
    assert (Hactive : existsb (Nat.eqb node) (map owner stack) = true).
    { apply existsb_exists. exists node. split; [exact Hin|apply Nat.eqb_refl]. }
    now rewrite Hactive.
  Qed.

  Lemma completed_owners_never_regain_unseen_credit : forall memo stack node family,
    memo node = Some family -> unseen_credit memo stack node = 0.
  Proof. intros; unfold unseen_credit; now rewrite H. Qed.

  Lemma entering_a_prepared_frame_transfers_its_exact_owner_credit : forall node rows,
    prepare node = inr rows ->
    frame_credit (Frame node rows (initial_accumulator node) ScanRows) = owner_credit node.
  Proof. intros; unfold owner_credit; now rewrite H. Qed.

  Lemma equal_credit_entries_have_equal_sums : forall (A : Type) (first next : A -> nat) items,
    (forall item, In item items -> first item = next item) ->
    sum_credits first items = sum_credits next items.
  Proof.
    intros A first next items. induction items as [|item rest IH]; intro Hentries;
      cbn [sum_credits fold_right].
    - reflexivity.
    - rewrite (Hentries item (or_introl eq_refl)). f_equal.
      apply IH. intros other Hin. apply Hentries. now right.
  Qed.

  Lemma zeroing_an_absent_owner_does_not_change_the_sum : forall credit nodes target,
    ~ In target nodes ->
    sum_credits (fun node => if Nat.eqb node target then 0 else credit node) nodes =
      sum_credits credit nodes.
  Proof.
    intros credit nodes. induction nodes as [|node rest IH]; intros target Habsent;
      cbn [sum_credits fold_right].
    - reflexivity.
    - destruct (Nat.eqb node target) eqn:Hequal.
      + apply Nat.eqb_eq in Hequal. subst. exfalso. apply Habsent. now left.
      + f_equal. apply IH. intro Hin. apply Habsent. now right.
  Qed.

  Lemma one_owner_credit_is_removed_exactly_once : forall credit nodes target,
    NoDup nodes -> In target nodes ->
    sum_credits credit nodes = credit target +
      sum_credits (fun node => if Nat.eqb node target then 0 else credit node) nodes.
  Proof.
    intros credit nodes target Hunique. induction Hunique as [|node rest Hnotin Hunique IH];
      intro Hin; [contradiction|].
    change (credit node + sum_credits credit rest = credit target +
      ((if Nat.eqb node target then 0 else credit node) +
        sum_credits (fun query => if Nat.eqb query target then 0 else credit query) rest)).
    destruct (Nat.eqb node target) eqn:Hequal.
    - apply Nat.eqb_eq in Hequal. subst.
      rewrite zeroing_an_absent_owner_does_not_change_the_sum; [lia|exact Hnotin].
    - assert (Hmember : In target rest).
      { destruct Hin as [Hsame|Hin]; [subst; rewrite Nat.eqb_refl in Hequal; discriminate|exact Hin]. }
      specialize (IH Hmember). lia.
  Qed.

  Lemma an_unseen_owner_retains_its_full_credit : forall memo stack node,
    memo node = None -> ~ In node (map owner stack) ->
    unseen_credit memo stack node = owner_credit node.
  Proof.
    intros memo stack node Hmemo Hfresh. unfold unseen_credit. rewrite Hmemo.
    destruct (existsb (Nat.eqb node) (map owner stack)) eqn:Hactive; [|reflexivity].
    apply existsb_exists in Hactive. destruct Hactive as [other [Hin Hequal]].
    apply Nat.eqb_eq in Hequal. subst. contradiction.
  Qed.

  Lemma same_top_owner_preserves_every_unseen_credit : forall memo first next tail node,
    owner first = owner next ->
    unseen_credit memo (first :: tail) node = unseen_credit memo (next :: tail) node.
  Proof.
    intros. unfold unseen_credit. cbn [map existsb]. now rewrite H.
  Qed.

  Lemma entering_an_owner_zeroes_only_its_unseen_credit : forall memo current tail node,
    unseen_credit memo (current :: tail) node =
      if Nat.eqb node (owner current) then 0 else unseen_credit memo tail node.
  Proof.
    intros. unfold unseen_credit. cbn [map existsb].
    destruct (memo node), (Nat.eqb node (owner current)); reflexivity.
  Qed.

  Lemma completion_does_not_restore_any_unseen_credit : forall memo current tail family node,
    unseen_credit (publish_complete memo (owner current) family) tail node =
      unseen_credit memo (current :: tail) node.
  Proof.
    intros. unfold unseen_credit, publish_complete. cbn [map existsb].
    destruct (Nat.eqb node (owner current)), (memo node); reflexivity.
  Qed.

  Definition preparation_dependencies_in_universe (universe : list nat) : Prop :=
    forall node rows current child,
    prepare node = inr rows -> In current rows -> admitted current = true ->
    In child (dependencies current) -> In child universe.

  Theorem scheduler_steps_strictly_decrease_global_credit : forall universe before stack after next_stack,
    NoDup universe -> preparation_dependencies_in_universe universe ->
    machine_invariant before stack -> scheduler_step before stack after next_stack ->
    scheduler_credit universe after next_stack < scheduler_credit universe before stack.
  Proof.
    intros universe before stack after next_stack Hunique Huniverse Hmachine Hstep.
    destruct Hstep as
      [memo first next tail Hlocal
      |memo node first rest acc done child pending tail child_rows Habsent Hfresh Hprepare
      |memo node acc tail].
    - assert (Hunseen : sum_credits (unseen_credit memo (first :: tail)) universe =
          sum_credits (unseen_credit memo (next :: tail)) universe).
      { apply equal_credit_entries_have_equal_sums. intros query Hin.
        apply same_top_owner_preserves_every_unseen_credit. now apply (local_steps_keep_the_owner Hlocal). }
      pose proof (local_steps_strictly_decrease_frame_credit Hlocal) as Hdecrease.
      unfold scheduler_credit. change
        (sum_credits (unseen_credit memo (next :: tail)) universe +
           (frame_credit next + sum_credits frame_credit tail) <
         sum_credits (unseen_credit memo (first :: tail)) universe +
           (frame_credit first + sum_credits frame_credit tail)).
      rewrite Hunseen. lia.
    - set (parent := Frame node (first :: rest) acc (Children done (child :: pending))) in *.
      set (waiting := Frame node (first :: rest) acc (AwaitChild done child pending)).
      set (fresh := Frame child child_rows (initial_accumulator child) ScanRows).
      destruct Hmachine as [Hmemo [Hframes Howners]].
      destruct (Hframes parent (or_introl eq_refl)) as [[Hcontext [[prefix Hprepared] Hready]] Hnone].
      unfold parent in Hprepared, Hready. cbn in Hprepared, Hready.
      destruct Hready as [Hadmitted [Hdeps Hdone]].
      assert (Hmember : In child universe).
      { eapply Huniverse; [exact Hprepared| |exact Hadmitted|].
        - apply in_app_iff. right. now left.
        - rewrite Hdeps. apply in_app_iff. right. now left. }
      assert (Htransfer : sum_credits (unseen_credit memo (parent :: tail)) universe =
          owner_credit child + sum_credits (unseen_credit memo (fresh :: waiting :: tail)) universe).
      { pose proof (one_owner_credit_is_removed_exactly_once
          (unseen_credit memo (parent :: tail)) child Hunique Hmember) as Hremove.
        assert (Hownercredit : unseen_credit memo (parent :: tail) child = owner_credit child).
        { apply an_unseen_owner_retains_its_full_credit; assumption. }
        rewrite Hownercredit in Hremove.
        rewrite Hremove. f_equal. apply equal_credit_entries_have_equal_sums.
        intros query Hin.
        rewrite (entering_an_owner_zeroes_only_its_unseen_credit memo fresh (waiting :: tail) query).
        unfold fresh; cbn [owner]. destruct (Nat.eqb query child); [reflexivity|].
        apply same_top_owner_preserves_every_unseen_credit. reflexivity. }
      assert (Hfreshcredit : frame_credit fresh = owner_credit child).
      { unfold fresh. now apply entering_a_prepared_frame_transfers_its_exact_owner_credit. }
      assert (Hparentcredit : frame_credit parent = S (frame_credit waiting)).
      { unfold parent, waiting. cbn [frame_credit rows_left frame_phase length]. lia. }
      unfold scheduler_credit. change
        (sum_credits (unseen_credit memo (fresh :: waiting :: tail)) universe +
           (frame_credit fresh + (frame_credit waiting + sum_credits frame_credit tail)) <
         sum_credits (unseen_credit memo (parent :: tail)) universe +
           (frame_credit parent + sum_credits frame_credit tail)).
      rewrite Htransfer, Hfreshcredit, Hparentcredit. lia.
    - assert (Hunseen : sum_credits
          (unseen_credit (publish_complete memo node (finish_accumulator acc)) tail) universe =
          sum_credits (unseen_credit memo (Frame node [] acc ScanRows :: tail)) universe).
      { apply equal_credit_entries_have_equal_sums. intros query Hin.
        apply (completion_does_not_restore_any_unseen_credit memo (Frame node [] acc ScanRows)). }
      unfold scheduler_credit. rewrite Hunseen.
      change (sum_credits (unseen_credit memo (Frame node [] acc ScanRows :: tail)) universe +
          sum_credits frame_credit tail <
        sum_credits (unseen_credit memo (Frame node [] acc ScanRows :: tail)) universe +
          (1 + sum_credits frame_credit tail)). lia.
  Qed.

  (* The executable macro-dispatcher below corresponds to the relation above.
     It never uses a missing completed-memo entry as an empty family. An
     invalid phase/read is explicit corruption, not semantic rejection.
     Refused rows are skipped before any dependency can be demanded. *)
  Inductive dispatch_result :=
  | DispatchContinue : completed_memo -> list frame -> dispatch_result
  | DispatchIdle : dispatch_result
  | DispatchFailed : request_failure -> dispatch_result.

  Definition scheduler_dispatch (memo : completed_memo) (stack : list frame) : dispatch_result :=
    match stack with
    | [] => DispatchIdle
    | Frame node rows acc at_phase :: tail =>
      match at_phase, rows with
      | ScanRows, [] =>
          DispatchContinue (publish_complete memo node (finish_accumulator acc)) tail
      | ScanRows, first :: rest =>
          if admitted first then
            DispatchContinue memo (Frame node rows acc (Children [] (dependencies first)) :: tail)
          else DispatchContinue memo (Frame node rest acc ScanRows :: tail)
      | Children done pending, first :: rest =>
          match pending with
          | [] => DispatchContinue memo (Frame node rows acc LeaveRow :: tail)
          | child :: pending => match memo child with
              | Some family => DispatchContinue memo
                  (Frame node rows acc (Children (done ++ [child]) pending) :: tail)
              | None => if existsb (Nat.eqb child) (map owner stack) then
                  DispatchFailed (DependencyCycle child)
                else match prepare child with
                  | inl fault => DispatchFailed (PreparationFault child fault)
                  | inr child_rows => DispatchContinue memo
                      (Frame child child_rows (initial_accumulator child) ScanRows ::
                       Frame node rows acc (AwaitChild done child pending) :: tail)
                  end
              end
          end
      | AwaitChild done child pending, first :: rest => match memo child with
          | Some family => DispatchContinue memo
              (Frame node rows acc (Children (done ++ [child]) pending) :: tail)
          | None => DispatchFailed (SchedulerInvariantFault node)
          end
      | LeaveRow, first :: rest => match read_families memo (dependencies first) with
          | None => DispatchFailed (SchedulerInvariantFault node)
          | Some inputs => match assemble_complete first inputs with
              | inl fault => DispatchFailed (AssemblyFault node fault)
              | inr family => match observe node acc family with
                  | inl fault => DispatchFailed (ObservationFault node fault)
                  | inr next => DispatchContinue memo (Frame node rest next ScanRows :: tail)
                  end
              end
          end
      | _, [] => DispatchFailed (SchedulerInvariantFault node)
      end
    end.

  Lemma active_owner_test_is_exact : forall node active,
    existsb (Nat.eqb node) active = true <-> In node active.
  Proof.
    intros node active. rewrite existsb_exists. split.
    - intros [other [Hin Hequal]]. apply Nat.eqb_eq in Hequal. now subst.
    - intro Hin. exists node. split; [exact Hin|apply Nat.eqb_refl].
  Qed.

  Lemma absent_owner_test_is_exact : forall node active,
    existsb (Nat.eqb node) active = false <-> ~ In node active.
  Proof.
    intros node active. split.
    - intros Htest Hin. apply active_owner_test_is_exact in Hin. congruence.
    - intro Habsent. destruct (existsb (Nat.eqb node) active) eqn:Htest; [|reflexivity].
      apply active_owner_test_is_exact in Htest. contradiction.
  Qed.

  Theorem successful_dispatch_is_exactly_a_scheduler_step : forall memo stack after next_stack,
    scheduler_dispatch memo stack = DispatchContinue after next_stack ->
    scheduler_step memo stack after next_stack.
  Proof.
    intros memo [|[node rows acc at_phase] tail] after next_stack Hdispatch;
      [discriminate|].
    destruct at_phase as [|done pending|done child pending|];
      destruct rows as [|first rest]; cbn [scheduler_dispatch] in Hdispatch; try discriminate.
    - inversion Hdispatch; subst. constructor.
    - destruct (admitted first) eqn:Hadmitted; inversion Hdispatch; subst;
        apply StepLocal; [apply StartAdmitted|apply SkipRefused]; exact Hadmitted.
    - destruct pending as [|child pending].
      + inversion Hdispatch; subst. apply StepLocal. apply DependenciesFinished.
      + destruct (memo child) as [family|] eqn:Hmemo.
        * inversion Hdispatch; subst. apply StepLocal. eapply ReuseDependency; eauto.
        * destruct (existsb (Nat.eqb child)
            (map owner (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail)))
            eqn:Hactive; [discriminate|].
          destruct (prepare child) as [fault|child_rows] eqn:Hprepare; [discriminate|].
          inversion Hdispatch; subst. apply StepEnterChild; auto.
          now apply absent_owner_test_is_exact.
    - destruct (memo child) as [family|] eqn:Hmemo; [|discriminate].
      inversion Hdispatch; subst. apply StepLocal. eapply ResumeDependency; eauto.
    - destruct (read_families memo (dependencies first)) as [inputs|] eqn:Hread;
        [|discriminate].
      destruct (assemble_complete first inputs) as [fault|family] eqn:Hassemble;
        [discriminate|].
      destruct (observe node acc family) as [fault|next] eqn:Hobserve; [discriminate|].
      inversion Hdispatch; subst. apply StepLocal. eapply ApplyCompleteRow; eauto.
  Qed.

  Theorem every_scheduler_step_is_the_dispatchers_actual_transition :
    forall memo stack after next_stack,
    scheduler_step memo stack after next_stack ->
    scheduler_dispatch memo stack = DispatchContinue after next_stack.
  Proof.
    intros memo stack after next_stack Hstep. destruct Hstep as
      [memo first next tail Hlocal
      |memo node first rest acc done child pending tail child_rows Habsent Hfresh Hprepare
      |memo node acc tail].
    - destruct Hlocal; cbn [scheduler_dispatch]; try now rewrite H.
      + reflexivity.
      + now rewrite H, H0, H1.
    - cbn [scheduler_dispatch]. rewrite Habsent.
      apply absent_owner_test_is_exact in Hfresh. now rewrite Hfresh, Hprepare.
    - reflexivity.
  Qed.
  Theorem valid_scheduler_states_never_report_control_corruption : forall memo stack node,
    machine_invariant memo stack -> control_invariant memo stack ->
    scheduler_dispatch memo stack <> DispatchFailed (SchedulerInvariantFault node).
  Proof.
    intros memo [|[owner_node rows acc at_phase] tail] node Hmachine Hcontrol;
      [discriminate|].
    destruct Hmachine as [Hmemo [Hframes Hunique]].
    destruct (Hframes _ (or_introl eq_refl)) as [[Hcontext [Hsuffix Hready]] Habsent].
    destruct Hcontrol as [Hlinks Hresume].
    destruct at_phase as [|done pending|done child pending|];
      destruct rows as [|first rest]; cbn [phase_ready rows_left frame_phase] in Hready;
      try contradiction; cbn [scheduler_dispatch].
    - discriminate.
    - destruct (admitted first); discriminate.
    - destruct pending as [|child pending]; [discriminate|].
      destruct (memo child); [discriminate|].
      destruct (existsb (Nat.eqb child)
        (map owner (Frame owner_node (first :: rest) acc (Children done (child :: pending)) :: tail)));
        [discriminate|]. destruct (prepare child); discriminate.
    - cbn [top_resume_ready frame_phase] in Hresume.
      destruct Hresume as [family Hfamily]. rewrite Hfamily. discriminate.
    - destruct Hready as [Hadmitted Hdependencies].
      destruct (ready_dependencies_have_an_ordered_read Hdependencies) as [inputs Hinputs].
      rewrite Hinputs. destruct (assemble_complete first inputs); [discriminate|].
      destruct (observe owner_node acc f); discriminate.
  Qed.

  Lemma dispatcher_does_not_spend_the_outer_scheduler_budget : forall memo stack,
    scheduler_dispatch memo stack <> DispatchFailed ResourceFault.
  Proof.
    intros memo [|[node rows acc at_phase] tail]; [discriminate|].
    destruct at_phase as [|done pending|done child pending|];
      destruct rows as [|first rest]; cbn [scheduler_dispatch]; try discriminate.
    - destruct (admitted first); discriminate.
    - destruct pending as [|child pending]; [discriminate|].
      destruct (memo child); [discriminate|].
      destruct (existsb (Nat.eqb child)
        (map owner (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail)));
        [discriminate|]. destruct (prepare child); discriminate.
    - destruct (memo child); discriminate.
    - destruct (read_families memo (dependencies first)) as [inputs|]; [|discriminate].
      destruct (assemble_complete first inputs) as [fault|family]; [discriminate|].
      destruct (observe node acc family); discriminate.
  Qed.

  Lemma live_scheduler_never_dispatches_idle : forall memo current tail,
    scheduler_dispatch memo (current :: tail) <> DispatchIdle.
  Proof.
    intros memo [node rows acc at_phase] tail.
    destruct at_phase as [|done pending|done child pending|];
      destruct rows as [|first rest]; cbn [scheduler_dispatch]; try discriminate.
    - destruct (admitted first); discriminate.
    - destruct pending as [|child pending]; [discriminate|].
      destruct (memo child); [discriminate|].
      destruct (existsb (Nat.eqb child)
        (map owner (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail)));
        [discriminate|]. destruct (prepare child); discriminate.
    - destruct (memo child); discriminate.
    - destruct (read_families memo (dependencies first)) as [inputs|]; [|discriminate].
      destruct (assemble_complete first inputs) as [fault|family]; [discriminate|].
      destruct (observe node acc family); discriminate.
  Qed.

  (* One unit of fuel buys one prepared-row dispatch, not the work internal
     to preparation or row assembly. The explicit stack is tail-called;
     Rust realizes this driver as an iterative loop. Failures drop the
     internal memo/accumulators from the public result, even after progress.
     This driver is the uncapped-family mode; root output-quota suspension
     is separate and must never mark a prefix as a completed memo entry. *)
  Fixpoint run_scheduler (fuel : nat) (memo : completed_memo) (stack : list frame)
    : request_failure + completed_memo :=
    match stack with
    | [] => inr memo
    | current :: _ => match fuel with
        | 0 => inl ResourceFault
        | S remaining => match scheduler_dispatch memo stack with
            | DispatchContinue after next_stack => run_scheduler remaining after next_stack
            | DispatchIdle => inl (SchedulerInvariantFault (owner current))
            | DispatchFailed fault => inl fault
            end
        end
    end.

  Theorem successful_bounded_execution_is_a_complete_scheduler_run :
    forall fuel memo stack after,
    run_scheduler fuel memo stack = inr after -> scheduler_run memo stack after [].
  Proof.
    induction fuel as [|fuel IH]; intros memo [|current tail] after Hrun;
      cbn [run_scheduler] in Hrun.
    - inversion Hrun; subst. constructor.
    - discriminate.
    - inversion Hrun; subst. constructor.
    - destruct (scheduler_dispatch memo (current :: tail)) as [next next_stack| |fault]
        eqn:Hdispatch; try discriminate.
      eapply RunStep with (middle := next) (pending := next_stack).
      + apply successful_dispatch_is_exactly_a_scheduler_step. exact Hdispatch.
      + apply IH. exact Hrun.
  Qed.

  Theorem dispatch_failure_is_forwarded_without_any_provisional_memo :
    forall fuel memo stack fault,
    scheduler_dispatch memo stack = DispatchFailed fault ->
    run_scheduler (S fuel) memo stack = inl fault.
  Proof.
    intros fuel memo [|current tail] fault Hdispatch; [discriminate|].
    cbn [run_scheduler]. now rewrite Hdispatch.
  Qed.

  Theorem a_later_failure_is_not_converted_to_a_successful_prefix :
    forall fuel memo stack next next_stack fault,
    scheduler_dispatch memo stack = DispatchContinue next next_stack ->
    run_scheduler fuel next next_stack = inl fault ->
    run_scheduler (S fuel) memo stack = inl fault.
  Proof.
    intros fuel memo [|current tail] next next_stack fault Hdispatch Hfailure;
      [discriminate|]. cbn [run_scheduler]. now rewrite Hdispatch.
  Qed.

  Lemma every_nonempty_scheduler_has_positive_credit : forall universe memo current tail,
    0 < scheduler_credit universe memo (current :: tail).
  Proof.
    intros. pose proof (every_live_frame_has_positive_credit current) as Hpositive.
    unfold scheduler_credit. change (0 <
      sum_credits (unseen_credit memo (current :: tail)) universe +
        (frame_credit current + sum_credits frame_credit tail)). lia.
  Qed.

  Theorem sufficient_credit_rules_out_scheduler_budget_exhaustion :
    forall fuel universe memo stack,
    NoDup universe -> preparation_dependencies_in_universe universe ->
    machine_invariant memo stack -> scheduler_credit universe memo stack <= fuel ->
    run_scheduler fuel memo stack <> inl ResourceFault.
  Proof.
    induction fuel as [|fuel IH]; intros universe memo [|current tail]
      Hunique Huniverse Hmachine Hcredit; cbn [run_scheduler]; try discriminate.
    - pose proof (every_nonempty_scheduler_has_positive_credit universe memo current tail). lia.
    - destruct (scheduler_dispatch memo (current :: tail)) as [next next_stack| |fault]
        eqn:Hdispatch; [|discriminate|].
      + assert (Hstep : scheduler_step memo (current :: tail) next next_stack).
        { now apply successful_dispatch_is_exactly_a_scheduler_step. }
        apply IH with (universe := universe); auto.
        * eapply scheduler_steps_preserve_completed_family_invariants; eauto.
        * assert (Hdecrease : scheduler_credit universe next next_stack <
              scheduler_credit universe memo (current :: tail)).
          { eapply scheduler_steps_strictly_decrease_global_credit; eauto. }
          lia.
      + intro Hequal. inversion Hequal; subst.
        now apply (dispatcher_does_not_spend_the_outer_scheduler_budget memo (current :: tail)).
  Qed.
  (* These are explicit, input-scoped subroutine contracts, not axioms about
     arbitrary grammars. Preparation and semantic callbacks can fail in the
     real implementation; those cases use the exact failure theorem above.
     The no-fault completion theorem applies only when these obligations and
     the admitted-DAG witness hold. In particular, an empty completed family
     is a valid success, while a rejected Cartesian candidate is handled
     inside assemble_complete rather than treated as a scheduler fault. *)
  Definition prepared_row (node : nat) (current : row) : Prop :=
    exists rows, prepare node = inr rows /\ In current rows.

  Definition preparation_defined_on_admitted_dependencies : Prop :=
    forall node current child,
    prepared_row node current -> admitted current = true -> In child (dependencies current) ->
    exists rows, prepare child = inr rows.

  Definition assembly_defined_on_denoting_inputs : Prop :=
    forall node current inputs,
    prepared_row node current -> admitted current = true ->
    dependencies_denote (dependencies current) inputs ->
    exists family, assemble_complete current inputs = inr family.

  Definition observation_defined_on_assembled_rows : Prop :=
    forall node current inputs family acc,
    prepared_row node current -> admitted current = true ->
    dependencies_denote (dependencies current) inputs ->
    assemble_complete current inputs = inr family ->
    exists next, observe node acc family = inr next.

  Lemma first_remaining_row_was_prepared : forall node first rest,
    prepared_suffix node (first :: rest) -> prepared_row node first.
  Proof.
    intros node first rest [prefix Hprepare]. exists (prefix ++ first :: rest).
    split; [exact Hprepare|]. apply in_app_iff. right. now left.
  Qed.

  Theorem no_fault_dag_has_an_actual_next_transition : forall rank memo current tail,
    admitted_dependency_rank rank ->
    preparation_defined_on_admitted_dependencies ->
    assembly_defined_on_denoting_inputs -> observation_defined_on_assembled_rows ->
    machine_invariant memo (current :: tail) -> control_invariant memo (current :: tail) ->
    exists after next_stack, scheduler_dispatch memo (current :: tail) =
      DispatchContinue after next_stack.
  Proof.
    intros rank memo [node rows acc at_phase] tail Hrank Hprepare Hassemble Hobserve Hmachine Hcontrol.
    destruct Hmachine as [Hmemo [Hframes Hunique]] eqn:Hmachine_parts.
    destruct (Hframes _ (or_introl eq_refl)) as [[Hcontext [Hsuffix Hready]] Habsent].
    destruct Hcontrol as [Hlinks Hresume].
    destruct at_phase as [|done pending|done child pending|];
      destruct rows as [|first rest]; cbn [phase_ready rows_left frame_phase] in Hready;
      try contradiction; cbn [scheduler_dispatch].
    - eexists; eexists; reflexivity.
    - destruct (admitted first); eexists; eexists; reflexivity.
    - destruct pending as [|child pending]; [eexists; eexists; reflexivity|].
      destruct (memo child) as [family|] eqn:Hchild; [eexists; eexists; reflexivity|].
      assert (Hfresh : ~ In child (map owner
        (Frame node (first :: rest) acc (Children done (child :: pending)) :: tail))).
      { eapply admitted_dag_demand_cannot_reenter_an_active_owner with (rank := rank); eauto. }
      apply absent_owner_test_is_exact in Hfresh. rewrite Hfresh.
      destruct Hready as [Hadmitted [Hdeps Hdone]].
      assert (Hrow : prepared_row node first).
      { eapply first_remaining_row_was_prepared; exact Hsuffix. }
      assert (Hmember : In child (dependencies first)).
      { rewrite Hdeps. apply in_app_iff. right. now left. }
      destruct (Hprepare node first child Hrow Hadmitted Hmember) as [child_rows Hchild_rows].
      rewrite Hchild_rows. eexists; eexists; reflexivity.
    - cbn [top_resume_ready frame_phase] in Hresume.
      destruct Hresume as [family Hfamily]. rewrite Hfamily. eexists; eexists; reflexivity.
    - destruct Hready as [Hadmitted Hdependencies].
      destruct (ready_dependencies_have_an_ordered_read Hdependencies) as [inputs Hinputs].
      rewrite Hinputs.
      assert (Hrow : prepared_row node first).
      { eapply first_remaining_row_was_prepared; exact Hsuffix. }
      assert (Hdenotes : dependencies_denote (dependencies first) inputs).
      { eapply reading_completed_dependencies_preserves_denotation; eauto. }
      destruct (Hassemble node first inputs Hrow Hadmitted Hdenotes) as [family Hfamily].
      rewrite Hfamily.
      destruct (Hobserve node first inputs family acc Hrow Hadmitted Hdenotes Hfamily)
        as [next Hnext]. rewrite Hnext. eexists; eexists; reflexivity.
  Qed.

  Theorem sufficient_credit_completes_no_fault_dags : forall fuel universe rank memo stack,
    NoDup universe -> preparation_dependencies_in_universe universe ->
    admitted_dependency_rank rank -> preparation_defined_on_admitted_dependencies ->
    assembly_defined_on_denoting_inputs -> observation_defined_on_assembled_rows ->
    machine_invariant memo stack -> control_invariant memo stack ->
    scheduler_credit universe memo stack <= fuel ->
    exists after, run_scheduler fuel memo stack = inr after.
  Proof.
    induction fuel as [|fuel IH]; intros universe rank memo [|current tail]
      Hunique Huniverse Hrank Hprepare Hassemble Hobserve Hmachine Hcontrol Hcredit.
    - exists memo. reflexivity.
    - pose proof (every_nonempty_scheduler_has_positive_credit universe memo current tail). lia.
    - exists memo. reflexivity.
    - destruct (no_fault_dag_has_an_actual_next_transition Hrank Hprepare Hassemble Hobserve
        Hmachine Hcontrol) as [next [next_stack Hdispatch]].
      assert (Hstep : scheduler_step memo (current :: tail) next next_stack).
      { now apply successful_dispatch_is_exactly_a_scheduler_step. }
      assert (Hnext_machine : machine_invariant next next_stack).
      { eapply scheduler_steps_preserve_completed_family_invariants; eauto. }
      assert (Hnext_control : control_invariant next next_stack).
      { eapply scheduler_steps_preserve_suspended_call_control; eauto. }
      assert (Hnext_credit : scheduler_credit universe next next_stack <= fuel).
      { assert (Hdecrease : scheduler_credit universe next next_stack <
            scheduler_credit universe memo (current :: tail)).
        { eapply scheduler_steps_strictly_decrease_global_credit; eauto. } lia. }
      destruct (IH universe rank next next_stack Hunique Huniverse Hrank Hprepare Hassemble
        Hobserve Hnext_machine Hnext_control Hnext_credit) as [after Hafter].
      exists after. cbn [run_scheduler]. now rewrite Hdispatch.
  Qed.

  Definition tracked_owner (node : nat) (memo : completed_memo) (stack : list frame) : Prop :=
    In node (map owner stack) \/ exists family, memo node = Some family.

  Lemma publication_preserves_completed_membership : forall memo node family query,
    (exists value, memo query = Some value) ->
    exists value, publish_complete memo node family query = Some value.
  Proof.
    intros memo node family query [value Hvalue]. unfold publish_complete.
    destruct (Nat.eqb query node); [now exists family|now exists value].
  Qed.

  Theorem scheduler_steps_cannot_lose_an_issued_owner : forall before stack after next_stack node,
    scheduler_step before stack after next_stack ->
    tracked_owner node before stack -> tracked_owner node after next_stack.
  Proof.
    intros before stack after next_stack query Hstep Htracked.
    destruct Hstep as
      [memo first next tail Hlocal
      |memo node first rest acc done child pending tail child_rows Habsent Hfresh Hprepare
      |memo node acc tail]; unfold tracked_owner in *.
    - destruct Htracked as [Hin|Hcomplete]; [left|now right].
      cbn in *. rewrite <- (local_steps_keep_the_owner Hlocal). exact Hin.
    - destruct Htracked as [Hin|Hcomplete]; [left|now right]. cbn in *. now right.
    - destruct Htracked as [[Hequal|Hin]|Hcomplete].
      + cbn in Hequal. subst query. right. exists (finish_accumulator acc).
        unfold publish_complete. now rewrite Nat.eqb_refl.
      + now left.
      + right. eapply publication_preserves_completed_membership; eauto.
  Qed.

  Lemma scheduler_runs_preserve_issued_owners : forall before stack after last_stack node,
    scheduler_run before stack after last_stack ->
    tracked_owner node before stack -> tracked_owner node after last_stack.
  Proof.
    intros before stack after last_stack node Hsteps.
    induction Hsteps; intro Htracked; [exact Htracked|].
    apply IHHsteps. eapply scheduler_steps_cannot_lose_an_issued_owner; eauto.
  Qed.

  Theorem complete_runs_publish_every_issued_owner : forall before stack after node,
    scheduler_run before stack after [] -> tracked_owner node before stack ->
    exists family, after node = Some family.
  Proof.
    intros before stack after node Hrun Htracked.
    destruct (scheduler_runs_preserve_issued_owners Hrun Htracked) as [Himpossible|Hcomplete];
      [contradiction|exact Hcomplete].
  Qed.

  Theorem successful_seeded_execution_returns_the_whole_root_family :
    forall fuel root rows after,
    prepare root = inr rows ->
    run_scheduler fuel empty_memo [Frame root rows (initial_accumulator root) ScanRows] = inr after ->
    exists family, after root = Some family /\ node_denotes root family.
  Proof.
    intros fuel root rows after Hprepare Hrun.
    assert (Hsteps : scheduler_run empty_memo
      [Frame root rows (initial_accumulator root) ScanRows] after []).
    { eapply successful_bounded_execution_is_a_complete_scheduler_run; eauto. }
    assert (Htracked : tracked_owner root empty_memo
      [Frame root rows (initial_accumulator root) ScanRows]).
    { left. now left. }
    destruct (complete_runs_publish_every_issued_owner Hsteps Htracked) as [family Hfamily].
    exists family. split; [exact Hfamily|]. eapply finished_root_is_a_complete_family; eauto.
  Qed.
End Scheduler.

Print Assumptions processed_rows_compose_in_order.
Print Assumptions observing_a_complete_row_preserves_the_frame_context.
Print Assumptions exhausted_frame_denotes_a_complete_family.
Print Assumptions reading_completed_dependencies_preserves_denotation.
Print Assumptions ready_dependencies_have_an_ordered_read.
Print Assumptions complete_publication_preserves_memo_correctness.
Print Assumptions publication_does_not_overwrite_a_completed_dependency.
Print Assumptions completed_sharing_reuses_the_family.
Print Assumptions active_reentry_is_not_successful_absence.
Print Assumptions local_steps_preserve_exact_frame_semantics.
Print Assumptions scheduler_steps_preserve_completed_family_invariants.
Print Assumptions every_reachable_scheduler_state_preserves_completed_families.
Print Assumptions finished_root_is_a_complete_family.
Print Assumptions root_suspension_has_no_completed_root_entry.
Print Assumptions scheduler_steps_preserve_suspended_call_control.
Print Assumptions every_reachable_scheduler_state_has_valid_call_control.
Print Assumptions admitted_dag_demand_cannot_reenter_an_active_owner.
Print Assumptions local_steps_strictly_decrease_frame_credit.
Print Assumptions active_owners_have_no_unseen_credit.
Print Assumptions completed_owners_never_regain_unseen_credit.
Print Assumptions entering_a_prepared_frame_transfers_its_exact_owner_credit.
Print Assumptions scheduler_steps_strictly_decrease_global_credit.
Print Assumptions successful_dispatch_is_exactly_a_scheduler_step.
Print Assumptions every_scheduler_step_is_the_dispatchers_actual_transition.
Print Assumptions valid_scheduler_states_never_report_control_corruption.
Print Assumptions successful_bounded_execution_is_a_complete_scheduler_run.
Print Assumptions dispatch_failure_is_forwarded_without_any_provisional_memo.
Print Assumptions a_later_failure_is_not_converted_to_a_successful_prefix.
Print Assumptions sufficient_credit_rules_out_scheduler_budget_exhaustion.
Print Assumptions no_fault_dag_has_an_actual_next_transition.
Print Assumptions sufficient_credit_completes_no_fault_dags.
Print Assumptions complete_runs_publish_every_issued_owner.
Print Assumptions successful_seeded_execution_returns_the_whole_root_family.
