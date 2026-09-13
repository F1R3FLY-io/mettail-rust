(** Finite child traversal and contextual frame strip/extension.
    Source: iterative_cmp.rs generate_cmp_engine, cmp_arm_stmts and cmp_deliver.
    Pending lists are in pop order. Run/Deliver are the existing control
    paths. A scheduled category return inserts its actual local task prefix;
    it does not assert that the category comparison completed Equal.

    SourceState and the three source-success witness relations below describe
    frame-local arm construction, native-core resume and flat-owner disposal.
    They are operational evidence, not comparator-result equations.
    Instantiation uses exact census recipes/native calls and the source native
    sort/pair/unit-lex witnesses. This file assumes neither their totality nor
    their semantic factorization. It proves the contextual traversal operation
    needed to apply those independently proved source witnesses.

    The saved frame is an untouched suffix. A traversal ends before touching
    it: Run with empty local prefix is an Equal boundary, Deliver r with empty
    local prefix is a decisive boundary. These proof cuts add no runtime
    marker, check, pop, allocation or publication. Root terminal admission and
    nearest-parent Resume handling remain existing source operations.
    Ownership/freshness/valid-pointer premises are carried separately by the
    existing inventory laws; frame replacement here is logical control/trace
    preservation, not a claim that arbitrary physical frames are well formed.
    Observations retain native and callback events; silent control receipts
    remain those of the existing admission/source-group model. *)
From Stdlib Require Import List Arith.PeanoNat.
From RhoBridge Require Import AdmittedGeneratedCollectionScheduling
  AdmittedGeneratedComparisonScheduling AdmittedGeneratedHashScheduling.
Import ListNotations.
Import AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.

Module GeneratedChildTraversal.

Inductive Mode := Run | Deliver (ordering : comparison).
Inductive HandlerExit := Scheduled (local_prefix : list Task) | Signalled (ordering : comparison).
Inductive CoreReply :=
| Requests (role : Role)
    (position : AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position)
| Completes (ordering : comparison).

Definition reply_mode reply := match reply with
  | Requests _ _ => Run
  | Completes Eq => Run
  | Completes Lt => Deliver Lt
  | Completes Gt => Deliver Gt end.
Definition reply_prefix owner callback reply := match reply with
  | Requests _ position =>
      [Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position);
       Resume owner callback]
  | Completes _ => [] end.
Definition reply_observation owner reply := match reply with
  | Requests role position => RequestedChild owner role position
  | Completes ordering => CoreCompleted owner ordering end.
Definition resume_observations owner input internal reply :=
  ResumeEntered owner input :: internal ++ [reply_observation owner reply].

Section SourceExecution.
Context {SourceState : Type}.
Variable arm_source :
  AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position ->
  SourceState -> HandlerExit -> list Observation -> SourceState -> Prop.
Variable core_source : nat -> nat -> option comparison -> SourceState ->
  CoreReply -> list Observation -> SourceState -> Prop.
Variable discard_source : Task -> SourceState -> SourceState -> Prop.

Inductive SourceStep : Mode -> list Task -> SourceState -> list Observation ->
    Mode -> list Task -> SourceState -> Prop :=
| StepEqualVerdict : forall position rest state,
    SourceStep Run
      (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict position Eq) :: rest)
      state [] Run rest state
| StepDecisiveVerdict : forall position ordering rest state,
    ordering <> Eq ->
    SourceStep Run
      (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict position ordering) :: rest)
      state [] (Deliver ordering) rest state
| StepScheduledCategory : forall position rest state prefix events next,
    arm_source position state (Scheduled prefix) events next ->
    SourceStep Run
      (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position) :: rest)
      state events Run (prefix ++ rest) next
| StepSignalledCategory : forall position rest state ordering events next,
    arm_source position state (Signalled ordering) events next -> ordering <> Eq ->
    SourceStep Run
      (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position) :: rest)
      state events (Deliver ordering) rest next
| StepStart : forall owner callback rest state reply events next,
    core_source owner callback None state reply events next ->
    SourceStep Run (Start owner callback :: rest) state
      (resume_observations owner None events reply)
      (reply_mode reply) (reply_prefix owner callback reply ++ rest) next
| StepNormalResume : forall owner callback rest state reply events next,
    core_source owner callback (Some Eq) state reply events next ->
    SourceStep Run (Resume owner callback :: rest) state
      (resume_observations owner (Some Eq) events reply)
      (reply_mode reply) (reply_prefix owner callback reply ++ rest) next
| StepDeliveryResume : forall owner callback rest state ordering reply events next,
    ordering <> Eq -> core_source owner callback (Some ordering) state reply events next ->
    SourceStep (Deliver ordering) (Resume owner callback :: rest) state
      (resume_observations owner (Some ordering) events reply)
      (reply_mode reply) (reply_prefix owner callback reply ++ rest) next
| StepDeliveryDiscard : forall task rest state ordering next,
    ordering <> Eq -> not_resume task = true -> discard_source task state next ->
    SourceStep (Deliver ordering) (task :: rest) state [] (Deliver ordering) rest next.

(** Every reached source branch touches its head and inserts a local prefix.
    No premise says that a whole category/helper/core has a semantic value. *)
Theorem every_source_step_has_an_exact_local_head_replacement :
  forall mode pending state events next_mode after next,
  SourceStep mode pending state events next_mode after next ->
  exists head rest inserted,
    pending = head :: rest /\ after = inserted ++ rest /\
    forall suffix, SourceStep mode (head :: suffix) state events next_mode (inserted ++ suffix) next.
Proof.
  intros mode pending state events next_mode after next HS.
  destruct HS as [position rest state|position ordering rest state NE
    |position rest state prefix events next ARM
    |position rest state ordering events next ARM NE
    |owner callback rest state reply events next CORE
    |owner callback rest state reply events next CORE
    |owner callback rest state ordering reply events next NE CORE
    |task rest state ordering next NE NR DROP].
  - exists (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict position Eq)), rest, [].
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. apply StepEqualVerdict.
  - exists (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict position ordering)), rest, [].
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. now apply StepDecisiveVerdict.
  - exists (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position)), rest, prefix.
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. now apply StepScheduledCategory.
  - exists (Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position)), rest, [].
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. eapply StepSignalledCategory; eassumption.
  - exists (Start owner callback), rest, (reply_prefix owner callback reply).
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. now apply StepStart.
  - exists (Resume owner callback), rest, (reply_prefix owner callback reply).
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. now apply StepNormalResume.
  - exists (Resume owner callback), rest, (reply_prefix owner callback reply).
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. eapply StepDeliveryResume; eassumption.
  - exists task, rest, [].
    split; [reflexivity|]. split; [reflexivity|]. intro suffix. eapply StepDeliveryDiscard; eassumption.
Qed.

Theorem source_step_appends_an_untouched_frame :
  forall frame mode pending state events next_mode after next,
  SourceStep mode pending state events next_mode after next ->
  SourceStep mode (pending ++ frame) state events next_mode (after ++ frame) next.
Proof.
  intros frame mode pending state events next_mode after next HS.
  destruct (every_source_step_has_an_exact_local_head_replacement
    mode pending state events next_mode after next HS)
    as [head [rest [inserted [INPUT [OUTPUT LOCAL]]]]].
  subst pending after. cbn [app]. rewrite <- app_assoc.
  exact (LOCAL (rest ++ frame)).
Qed.

Theorem source_step_strips_an_untouched_frame :
  forall frame mode head rest state events next_mode after next,
  SourceStep mode ((head :: rest) ++ frame) state events next_mode (after ++ frame) next ->
  SourceStep mode (head :: rest) state events next_mode after next.
Proof.
  intros frame mode head rest state events next_mode after next HS.
  destruct (every_source_step_has_an_exact_local_head_replacement
    mode ((head :: rest) ++ frame) state events next_mode (after ++ frame) next HS)
    as [actual_head [actual_rest [inserted [INPUT [OUTPUT LOCAL]]]]].
  cbn [app] in INPUT. injection INPUT as HEAD REST.
  subst actual_head actual_rest.
  assert (AFTER : after = inserted ++ rest).
  { apply (app_inv_tail frame). rewrite <- app_assoc. exact OUTPUT. }
  subst after. exact (LOCAL rest).
Qed.

Theorem no_source_step_pops_an_empty_local_stack :
  forall mode state events next_mode after next,
  ~ SourceStep mode [] state events next_mode after next.
Proof. intros mode state events next_mode after next HS. inversion HS. Qed.

(** Finite source-witness trace. Every nonterminal constructor contains the
    actual SourceStep on the full stack and its next exact stack split. No
    constructor crosses an empty local prefix. Observations/count are retained. *)
Inductive ChildTraversal (frame : list Task) : nat -> Mode -> list Task -> SourceState ->
    list Observation -> comparison -> SourceState -> Prop :=
| TraversalEqualBoundary : forall state,
    ChildTraversal frame 0 Run [] state [] Eq state
| TraversalDecisiveBoundary : forall state ordering,
    ordering <> Eq -> ChildTraversal frame 0 (Deliver ordering) [] state [] ordering state
| TraversalSourceStep : forall count mode head rest state first_events next_mode prefix next
    later_events result last,
    SourceStep mode ((head :: rest) ++ frame) state first_events next_mode (prefix ++ frame) next ->
    ChildTraversal frame count next_mode prefix next later_events result last ->
    ChildTraversal frame (S count) mode (head :: rest) state
      (first_events ++ later_events) result last.

Theorem finite_child_traversal_replaces_its_untouched_frame :
  forall frame replacement count mode prefix state events result last,
  ChildTraversal frame count mode prefix state events result last ->
  ChildTraversal replacement count mode prefix state events result last.
Proof.
  intros frame replacement count mode prefix state events result last HT.
  induction HT as [state|state ordering NE
    |count mode head rest state first_events next_mode prefix next later_events result last STEP TAIL IH].
  - apply TraversalEqualBoundary.
  - now apply TraversalDecisiveBoundary.
  - pose proof (source_step_strips_an_untouched_frame
      frame mode head rest state first_events next_mode prefix next STEP) as LOCAL.
    eapply TraversalSourceStep.
    + exact (source_step_appends_an_untouched_frame
        replacement mode (head :: rest) state first_events next_mode prefix next LOCAL).
    + exact IH.
Qed.

Theorem finite_child_traversal_strips_to_a_genuine_isolated_trace :
  forall frame count mode prefix state events result last,
  ChildTraversal frame count mode prefix state events result last ->
  ChildTraversal [] count mode prefix state events result last.
Proof.
  intros frame count mode prefix state events result last HT.
  exact (finite_child_traversal_replaces_its_untouched_frame
    frame [] count mode prefix state events result last HT).
Qed.

Theorem isolated_child_traversal_extends_to_existing_siblings :
  forall frame count mode prefix state events result last,
  ChildTraversal [] count mode prefix state events result last ->
  ChildTraversal frame count mode prefix state events result last.
Proof.
  intros frame count mode prefix state events result last HT.
  exact (finite_child_traversal_replaces_its_untouched_frame
    [] frame count mode prefix state events result last HT).
Qed.

Theorem source_child_completion_is_contextual_without_a_helper_equal_premise :
  forall frame count mode prefix state events result last,
  ChildTraversal frame count mode prefix state events result last <->
  ChildTraversal [] count mode prefix state events result last.
Proof.
  intros. split.
  - apply finite_child_traversal_strips_to_a_genuine_isolated_trace.
  - apply isolated_child_traversal_extends_to_existing_siblings.
Qed.

Theorem finite_child_traversal_appends_an_outer_frame_without_new_events :
  forall frame outer count mode prefix state events result last,
  ChildTraversal frame count mode prefix state events result last ->
  ChildTraversal (frame ++ outer) count mode prefix state events result last.
Proof.
  intros frame outer count mode prefix state events result last HT.
  exact (finite_child_traversal_replaces_its_untouched_frame
    frame (frame ++ outer) count mode prefix state events result last HT).
Qed.

Definition completion_mode result := reply_mode (Completes result).

(** A generated child starts in Run. Every source step retains a mode with
    an actual empty-prefix boundary; Deliver Eq is not such a boundary.
    This predicate adds no transition or semantic-result assumption. *)
Definition boundary_compatible_mode mode := match mode with
  | Run => True
  | Deliver ordering => ordering <> Eq
  end.

Lemma every_core_reply_has_a_boundary_compatible_mode : forall reply,
  boundary_compatible_mode (reply_mode reply).
Proof.
  intros [role position|ordering]; [exact I|].
  destruct ordering; cbn [reply_mode boundary_compatible_mode];
    [exact I | discriminate | discriminate].
Qed.

Lemma source_step_preserves_boundary_compatible_mode :
  forall mode pending state events next_mode after next,
  boundary_compatible_mode mode ->
  SourceStep mode pending state events next_mode after next ->
  boundary_compatible_mode next_mode.
Proof.
  intros mode pending state events next_mode after next MODE STEP.
  destruct STEP; cbn [boundary_compatible_mode];
    try exact I; try assumption; apply every_core_reply_has_a_boundary_compatible_mode.
Qed.

Lemma a_compatible_mode_completes_the_empty_local_prefix : forall mode frame state,
  boundary_compatible_mode mode ->
  exists result, ChildTraversal frame 0 mode [] state [] result state /\
    completion_mode result = mode.
Proof.
  intros mode frame state MODE. destruct mode as [|ordering].
  - exists Eq. split; [constructor | reflexivity].
  - destruct ordering.
    + exfalso. apply MODE. reflexivity.
    + exists Lt. split; [apply TraversalDecisiveBoundary; discriminate | reflexivity].
    + exists Gt. split; [apply TraversalDecisiveBoundary; discriminate | reflexivity].
Qed.

(** First-hit decomposition of a GIVEN successful source trace. The local
    traversal ends before any frame task is popped. Its remainder is the
    original enclosing trace, with exactly split counts and observations.
    In particular, a callback's child traversal is extracted, not supplied
    as an oracle about the result of the category helper. *)
Theorem finite_source_trace_reaches_its_first_local_boundary :
  forall count mode pending state events result last,
  ChildTraversal [] count mode pending state events result last ->
  boundary_compatible_mode mode -> forall prefix frame,
  pending = prefix ++ frame ->
  exists local_count later_count child_result middle first_events later_events,
    ChildTraversal frame local_count mode prefix state first_events child_result middle /\
    ChildTraversal [] later_count (completion_mode child_result) frame middle
      later_events result last /\
    count = local_count + later_count /\ events = first_events ++ later_events.
Proof.
  intros count mode pending state events result last TRACE.
  induction TRACE as [state|state ordering NE
    |count mode head rest state first next_mode after next later result last STEP TAIL IH];
    intros MODE prefix frame SPLIT; destruct prefix as [|local_head local_rest].
  - cbn [app] in SPLIT. subst frame.
    exists 0, 0, Eq, state, [], []. repeat split; constructor.
  - discriminate SPLIT.
  - cbn [app] in SPLIT. subst frame. destruct ordering; [contradiction| |].
    + exists 0, 0, Lt, state, [], []. repeat split; try reflexivity;
        apply TraversalDecisiveBoundary; discriminate.
    + exists 0, 0, Gt, state, [], []. repeat split; try reflexivity;
        apply TraversalDecisiveBoundary; discriminate.
  - discriminate SPLIT.
  - cbn [app] in SPLIT. subst frame.
    destruct (a_compatible_mode_completes_the_empty_local_prefix
      mode (head :: rest) state MODE) as [child_result [EMPTY COMPLETE_MODE]].
    exists 0, (S count), child_result, state, [], (first ++ later).
    split; [exact EMPTY|]. split.
    + rewrite COMPLETE_MODE. eapply TraversalSourceStep; [exact STEP|exact TAIL].
    + split; reflexivity.
  - cbn [app] in SPLIT. injection SPLIT as HEAD REST.
    subst local_head rest. repeat rewrite app_nil_r in STEP.
    destruct (every_source_step_has_an_exact_local_head_replacement
      mode (head :: (local_rest ++ frame)) state first next_mode after next STEP)
      as [actual_head [actual_rest [inserted [INPUT [OUTPUT LOCAL]]]]].
    injection INPUT as SAME_HEAD SAME_REST. subst actual_head actual_rest.
    assert (NEXT_SPLIT : after = (inserted ++ local_rest) ++ frame).
    { rewrite <- app_assoc. exact OUTPUT. }
    pose proof (source_step_preserves_boundary_compatible_mode
      mode (head :: (local_rest ++ frame)) state first next_mode after next MODE STEP)
      as NEXT_MODE.
    destruct (IH NEXT_MODE (inserted ++ local_rest) frame NEXT_SPLIT)
      as [local_count [later_count [child_result [middle [child_events [later_events
        [CHILD [CONTINUATION [COUNTS EVENTS]]]]]]]]].
    exists (S local_count), later_count, child_result, middle,
      (first ++ child_events), later_events.
    split.
    + eapply TraversalSourceStep with
        (next_mode := next_mode) (prefix := inserted ++ local_rest) (next := next)
        (first_events := first) (later_events := child_events).
      * cbn [app]. rewrite <- app_assoc. exact (LOCAL (local_rest ++ frame)).
      * exact CHILD.
    + split; [exact CONTINUATION|]. split.
      * rewrite COUNTS. reflexivity.
      * rewrite EVENTS, app_assoc. reflexivity.
Qed.

Theorem running_child_trace_splits_before_its_untouched_frame :
  forall count prefix frame state events result last,
  ChildTraversal [] count Run (prefix ++ frame) state events result last ->
  exists local_count later_count child_result middle first_events later_events,
    ChildTraversal frame local_count Run prefix state first_events child_result middle /\
    ChildTraversal [] later_count (completion_mode child_result) frame middle
      later_events result last /\
    count = local_count + later_count /\ events = first_events ++ later_events.
Proof.
  intros count prefix frame state events result last TRACE.
  exact (finite_source_trace_reaches_its_first_local_boundary
    count Run (prefix ++ frame) state events result last TRACE I prefix frame eq_refl).
Qed.

Theorem finite_child_traversal_composes_with_its_actual_continuation :
  forall outer continuation count mode prefix state events result middle,
  ChildTraversal (continuation ++ outer) count mode prefix state events result middle ->
  forall later_count later_events final last,
  ChildTraversal outer later_count (completion_mode result) continuation middle later_events final last ->
  ChildTraversal outer (count + later_count) mode (prefix ++ continuation) state
    (events ++ later_events) final last.
Proof.
  intros outer continuation count mode prefix state events result middle HT.
  induction HT as [state|state ordering NE
    |count mode head rest state first_events next_mode prefix next tail_events result middle STEP TAIL IH];
    intros later_count later_events final last CONT.
  - exact CONT.
  - destruct ordering; [contradiction|exact CONT|exact CONT].
  - cbn [app Nat.add]. rewrite <- app_assoc.
    eapply TraversalSourceStep with
      (next_mode := next_mode) (prefix := prefix ++ continuation) (next := next)
      (first_events := first_events) (later_events := tail_events ++ later_events).
    + cbn [app] in STEP |- *.
      rewrite !app_assoc in STEP. exact STEP.
    + apply IH. exact CONT.
Qed.

(** A genuine finite source traversal supplies the child's boundary result,
    not a category helper's scheduling Equal. The saved core receives this
    result once, and its next traversal supplies the completed field result. *)
Theorem completed_requested_child_traversal_feeds_its_actual_result_to_core :
  forall outer owner callback position count state child_events result middle,
  ChildTraversal [] count Run
    [Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position)]
    state child_events result middle ->
  forall reply core_events next later_count later_events final last,
  core_source owner callback (Some result) middle reply core_events next ->
  ChildTraversal outer later_count (reply_mode reply) (reply_prefix owner callback reply)
    next later_events final last ->
  ChildTraversal outer (count + S later_count) Run
    [Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position);
     Resume owner callback]
    state (child_events ++ (resume_observations owner (Some result) core_events reply ++ later_events)) final last.
Proof.
  intros outer owner callback position count state child_events result middle CHILD
    reply core_events next later_count later_events final last CORE CONT.
  pose proof (isolated_child_traversal_extends_to_existing_siblings
    ([Resume owner callback] ++ outer) count Run
    [Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position)]
    state child_events result middle CHILD) as FRAMED.
  eapply finite_child_traversal_composes_with_its_actual_continuation with
    (continuation := [Resume owner callback])
    (prefix := [Borrowed (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position)])
    (count := count) (result := result) (middle := middle);
    [exact FRAMED|].
  eapply TraversalSourceStep with
    (next_mode := reply_mode reply) (prefix := reply_prefix owner callback reply) (next := next)
    (first_events := resume_observations owner (Some result) core_events reply)
    (later_events := later_events).
  - destruct result; cbn [completion_mode reply_mode].
    + apply StepNormalResume. exact CORE.
    + apply StepDeliveryResume; [discriminate|exact CORE].
    + apply StepDeliveryResume; [discriminate|exact CORE].
  - exact CONT.
Qed.

Theorem start_traversal_uses_the_original_none_input_and_native_core_continuation :
  forall outer owner callback state reply core_events next count events result last,
  core_source owner callback None state reply core_events next ->
  ChildTraversal outer count (reply_mode reply) (reply_prefix owner callback reply) next events result last ->
  ChildTraversal outer (S count) Run [Start owner callback] state
    (resume_observations owner None core_events reply ++ events) result last.
Proof.
  intros outer owner callback state reply core_events next count events result last CORE CONT.
  eapply TraversalSourceStep with
    (next_mode := reply_mode reply) (prefix := reply_prefix owner callback reply) (next := next)
    (first_events := resume_observations owner None core_events reply) (later_events := events).
  - apply StepStart. exact CORE.
  - exact CONT.
Qed.
End SourceExecution.

Print Assumptions every_source_step_has_an_exact_local_head_replacement.
Print Assumptions source_step_appends_an_untouched_frame.
Print Assumptions source_step_strips_an_untouched_frame.
Print Assumptions no_source_step_pops_an_empty_local_stack.
Print Assumptions finite_child_traversal_replaces_its_untouched_frame.
Print Assumptions finite_child_traversal_strips_to_a_genuine_isolated_trace.
Print Assumptions isolated_child_traversal_extends_to_existing_siblings.
Print Assumptions source_child_completion_is_contextual_without_a_helper_equal_premise.
Print Assumptions finite_child_traversal_appends_an_outer_frame_without_new_events.
Print Assumptions every_core_reply_has_a_boundary_compatible_mode.
Print Assumptions source_step_preserves_boundary_compatible_mode.
Print Assumptions a_compatible_mode_completes_the_empty_local_prefix.
Print Assumptions finite_source_trace_reaches_its_first_local_boundary.
Print Assumptions running_child_trace_splits_before_its_untouched_frame.
Print Assumptions finite_child_traversal_composes_with_its_actual_continuation.
Print Assumptions completed_requested_child_traversal_feeds_its_actual_result_to_core.
Print Assumptions start_traversal_uses_the_original_none_input_and_native_core_continuation.
End GeneratedChildTraversal.
