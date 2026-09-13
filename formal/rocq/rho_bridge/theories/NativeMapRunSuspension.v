(** Native Map suspension and saved phase continuations.

    Existing PairProtocol supplies exact Primary/Secondary/alias behavior.
    Existing IndexedRunExecution supplies the actual source cursor, target
    overwrite and remaining run. Cutting does not execute the overwrite;
    plugging the completed pair response restores the SAME indexed run.
    Saved contexts retain earlier native copies/runs/passes and their exact
    suffix witnesses, including physical buffer swaps and saturated widths.

    This is not a new sorter, callback engine, or final-result oracle.
    The concrete source association must identify the yielded owner's phase,
    cursor, buffers and pending role with these saved evidence contexts.
    Logical comparison state is erased, not identified with runtime budget
    state. Successful admission, typed immutable pointer provenance, complete
    paired-unit rosters and concrete child/class instantiation remain their
    existing obligations. No term Eq/Cmp coherence or hash injectivity is used.
    A category helper's scheduling Equal is not a completed child response. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
From RhoBridge Require Import CollectionPairAndUnitLexResults MergeSortPdaNativeRun
  MergeSortPdaCursor AdmittedGeneratedCollectionScheduling
  MergeSortPdaNativePass MergeSortPdaNativeOuter.
From RuntimeGrammar Require Import SemanticComparisonLaws SemanticResultMerge.
Import ListNotations.
Import CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.
Import MergeSortPdaNativeRun.MergeSortPdaNativeRun.
Import MergeSortPdaCursor.MergeSortPdaCursor.
Import MergeSortPdaNativePass.MergeSortPdaNativePass.
Import MergeSortPdaNativeOuter.MergeSortPdaNativeOuter.

Module NativeMapRunSuspension.
Section PairCuts.
Context {Key Value : Type}.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Local Notation PP := (@PairProtocol Key Value key_compare value_compare key_alias value_alias).
Local Notation SP := (@SecondaryProtocol Value value_compare value_alias).

Definition after_primary (lhs rhs : Key * Value) (first : comparison)
    (remaining : list Answer) (result : comparison) := match first with
  | Eq => SP (snd lhs) (snd rhs) remaining result
  | Lt | Gt => remaining = [] /\ result = first end.

Theorem native_primary_request_cut_and_plug : forall lhs rhs answers result,
  key_alias (fst lhs) (fst rhs) = false ->
  (PP lhs rhs answers result <->
    exists first remaining,
      answers = (AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary, first) :: remaining /\
      key_compare (fst lhs) (fst rhs) = first /\ after_primary lhs rhs first remaining result).
Proof.
  intros lhs rhs answers result NONALIAS. split.
  - intro HP. destruct HP as [answers result HA HS|result HA HK HD|answers result HA HK HS].
    + rewrite NONALIAS in HA. discriminate.
    + exists result, []. split; [reflexivity|]. split; [exact HK|].
      destruct result; [contradiction|split; reflexivity|split; reflexivity].
    + exists Eq, answers. split; [reflexivity|]. split; [exact HK|exact HS].
  - intros [first [remaining [ANS [HK CONT]]]]. subst answers.
    destruct first.
    + eapply PairPrimaryEqual; eassumption.
    + destruct CONT as [REST RESULT]. subst remaining result.
      apply PairPrimaryDecisive; try assumption; discriminate.
    + destruct CONT as [REST RESULT]. subst remaining result.
      apply PairPrimaryDecisive; try assumption; discriminate.
Qed.

Theorem native_primary_alias_enters_the_existing_secondary_protocol :
  forall lhs rhs answers result,
  key_alias (fst lhs) (fst rhs) = true ->
  (PP lhs rhs answers result <-> SP (snd lhs) (snd rhs) answers result).
Proof.
  intros lhs rhs answers result ALIAS. split.
  - intro HP. destruct HP as [answers result HA HS|result HA HK HD|answers result HA HK HS].
    + exact HS.
    + rewrite ALIAS in HA. discriminate.
    + rewrite ALIAS in HA. discriminate.
  - intro HS. eapply PairPrimaryAlias; eassumption.
Qed.

Theorem native_secondary_request_forwards_its_one_response :
  forall lhs rhs answers result,
  value_alias lhs rhs = false ->
  (SP lhs rhs answers result <->
    answers = [(AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary, result)] /\
    value_compare lhs rhs = result).
Proof.
  intros lhs rhs answers result NONALIAS. split.
  - intro HS. destruct HS as [HA|result HA HR].
    + rewrite NONALIAS in HA. discriminate.
    + split; [reflexivity|exact HR].
  - intros [ANS RESULT]. subst answers. apply SecondaryAnswered; assumption.
Qed.

Theorem no_external_pair_answer_means_both_native_pointer_shortcuts :
  forall lhs rhs answers result,
  PP lhs rhs answers result -> answers = [] ->
  key_alias (fst lhs) (fst rhs) = true /\
  value_alias (snd lhs) (snd rhs) = true /\ result = Eq.
Proof.
  intros lhs rhs answers result HP.
  destruct HP as [answers result HA HS|result HA HK HD|answers result HA HK HS];
    intro EMPTY; try discriminate.
  destruct HS as [VA|result VA HR]; [|discriminate].
  split; [exact HA|]. split; [exact VA|reflexivity].
Qed.
End PairCuts.

Section IndexedCut.
Context {Entry State : Type}.
Variable compare : Entry -> Entry -> State -> option comparison * State.

Theorem both_live_heads_cut_the_actual_accepted_copy :
  forall source cursor target state next_cursor next next_state,
  NativeCopyStep compare source cursor target state next_cursor next next_state ->
  forall lhs rhs, NativeRequest source cursor lhs rhs ->
  exists decision,
    next_cursor = advance (accept_side decision) cursor /\
    compare lhs rhs state = (Some decision, next_state) /\
    copy_record (accept_side decision) cursor source target =
      Some (advance (accept_side decision) cursor, next).
Proof.
  intros source cursor target state next_cursor next next_state STEP.
  destruct STEP as
    [cursor target next actual_l actual_r state next_state decision HAVE CMP COPY
    |cursor target next state LIVE EX COPY
    |cursor target next state EX LIVE COPY]; intros lhs rhs READY.
  - destruct HAVE as [HL [HR [NL NR]]].
    destruct READY as [HL' [HR' [NL' NR']]].
    rewrite NL in NL'. inversion NL'; subst actual_l.
    rewrite NR in NR'. inversion NR'; subst actual_r.
    exists decision. split; [reflexivity|]. split; assumption.
  - destruct READY as [HL [HR REST]]. unfold can_copy in HR. lia.
  - destruct READY as [HL [HR REST]]. unfold can_copy in HL. lia.
Qed.

Theorem live_run_witness_cuts_before_its_native_copy :
  forall source count cursor target state final_cursor final_target last lhs rhs,
  IndexedRunExecution compare source (S count) cursor target state
    final_cursor final_target last ->
  NativeRequest source cursor lhs rhs ->
  exists decision next next_state,
    compare lhs rhs state = (Some decision, next_state) /\
    copy_record (accept_side decision) cursor source target =
      Some (advance (accept_side decision) cursor, next) /\
    IndexedRunExecution compare source count
      (advance (accept_side decision) cursor) next next_state
      final_cursor final_target last.
Proof.
  intros source count cursor target state final_cursor final_target last lhs rhs RUN READY.
  inversion RUN as
    [|n c t s middle next next_state fc ft finish STEP TAIL]; subst.
  destruct (both_live_heads_cut_the_actual_accepted_copy
    _ _ _ _ _ _ _ STEP lhs rhs READY) as [decision [MID [CMP COPY]]].
  subst middle. exists decision, next, next_state.
  split; [exact CMP|]. split; [exact COPY|exact TAIL].
Qed.

Theorem matched_native_response_plugs_the_same_run_witness :
  forall source count cursor target state final_cursor final_target last
    lhs rhs decision next next_state,
  NativeRequest source cursor lhs rhs ->
  compare lhs rhs state = (Some decision, next_state) ->
  copy_record (accept_side decision) cursor source target =
    Some (advance (accept_side decision) cursor, next) ->
  IndexedRunExecution compare source count
    (advance (accept_side decision) cursor) next next_state
    final_cursor final_target last ->
  IndexedRunExecution compare source (S count) cursor target state
    final_cursor final_target last.
Proof.
  intros source count cursor target state final_cursor final_target last
    lhs rhs decision next next_state READY CMP COPY TAIL.
  eapply IndexedRunMore; [eapply NativeAccepted; eassumption|exact TAIL].
Qed.

Theorem terminal_run_witness_has_no_pending_comparison :
  forall source cursor target state final_cursor final_target last,
  IndexedRunExecution compare source 0 cursor target state
    final_cursor final_target last ->
  final_cursor = cursor /\ final_target = target /\ last = state /\
  left_index cursor = run_middle cursor /\ right_index cursor = run_end cursor.
Proof.
  intros source cursor target state final_cursor final_target last RUN.
  inversion RUN; subst. repeat split; assumption || reflexivity.
Qed.
End IndexedCut.

Section MapPairCut.
Context {Key Value : Type}.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Hypothesis key_alias_sound : forall x y,
  key_alias x y = true -> key_compare x y = Eq.
Hypothesis value_alias_sound : forall x y,
  value_alias x y = true -> value_compare x y = Eq.
Local Notation PC :=
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare).
Local Notation NC :=
  (fun (lhs rhs : Key * Value) (_ : unit) => (Some (PC lhs rhs), tt)).
Local Notation PP :=
  (@PairProtocol Key Value key_compare value_compare key_alias value_alias).

Theorem actual_live_map_run_exposes_its_pair_protocol_and_saved_tail :
  forall source count cursor target final_cursor final_target lhs rhs,
  IndexedRunExecution NC source (S count) cursor target tt
    final_cursor final_target tt ->
  NativeRequest source cursor lhs rhs ->
  exists answers result next,
    PP lhs rhs answers result /\
    copy_record (accept_side result) cursor source target =
      Some (advance (accept_side result) cursor, next) /\
    IndexedRunExecution NC source count
      (advance (accept_side result) cursor) next tt
      final_cursor final_target tt.
Proof.
  intros source count cursor target final_cursor final_target lhs rhs RUN READY.
  destruct (@live_run_witness_cuts_before_its_native_copy
    (Key * Value) unit NC source count cursor target tt final_cursor final_target tt
    lhs rhs RUN READY) as [decision [next [next_state [CMP [COPY TAIL]]]]].
  injection CMP as DEC STATE. subst decision next_state.
  destruct (@original_pair_responses_construct_the_request_protocol
    Key Value key_compare value_compare key_alias value_alias lhs rhs)
    as [answers [result PROTOCOL]].
  pose proof (@pair_request_accept_returns_key_then_value
    Key Value key_compare value_compare key_alias value_alias
    key_alias_sound value_alias_sound lhs rhs answers result PROTOCOL) as RESULT.
  subst result. exists answers, (PC lhs rhs), next.
  split; [exact PROTOCOL|]. split; [exact COPY|exact TAIL].
Qed.

Theorem completed_native_pair_response_restores_the_same_indexed_run :
  forall source count cursor target final_cursor final_target lhs rhs answers result next,
  NativeRequest source cursor lhs rhs ->
  PP lhs rhs answers result ->
  copy_record (accept_side result) cursor source target =
    Some (advance (accept_side result) cursor, next) ->
  IndexedRunExecution NC source count
    (advance (accept_side result) cursor) next tt
    final_cursor final_target tt ->
  IndexedRunExecution NC source (S count) cursor target tt
    final_cursor final_target tt.
Proof.
  intros source count cursor target final_cursor final_target lhs rhs answers result next
    READY PROTOCOL COPY TAIL.
  eapply (@matched_native_response_plugs_the_same_run_witness
    (Key * Value) unit NC source count cursor target tt final_cursor final_target tt
    lhs rhs result next tt); [exact READY| |exact COPY|exact TAIL].
  change ((Some (PC lhs rhs), tt) = (Some result, tt)).
  rewrite (@pair_request_accept_returns_key_then_value
    Key Value key_compare value_compare key_alias value_alias
    key_alias_sound value_alias_sound lhs rhs answers result PROTOCOL).
  reflexivity.
Qed.
End MapPairCut.

Section SavedNativeContexts.
Context {Entry : Type}.
Variable compare : Entry -> Entry -> unit -> option comparison * unit.

(** A hole is exactly one pending NativeAccepted copy. Prior copies remain
    concrete NativeCopySteps; the suffix remains an IndexedRunExecution. *)
Inductive SavedRunContext (source : list Entry)
    (hole_cursor : Cursor) (hole_target : list Entry)
    (after_cursor : Cursor) (after_target : list Entry) :
    nat -> Cursor -> list Entry -> Cursor -> list Entry -> Prop :=
| SavedRunHole : forall count final_cursor final_target,
    IndexedRunExecution compare source count after_cursor after_target tt
      final_cursor final_target tt ->
    SavedRunContext source hole_cursor hole_target after_cursor after_target
      (S count) hole_cursor hole_target final_cursor final_target
| SavedRunBefore : forall count cursor target middle next final_cursor final_target,
    NativeCopyStep compare source cursor target tt middle next tt ->
    SavedRunContext source hole_cursor hole_target after_cursor after_target
      count middle next final_cursor final_target ->
    SavedRunContext source hole_cursor hole_target after_cursor after_target
      (S count) cursor target final_cursor final_target.

Theorem saved_run_context_plugs_the_exact_native_copy :
  forall source hc ht ac after_t count cursor target final_cursor final_target,
  SavedRunContext source hc ht ac after_t count cursor target final_cursor final_target ->
  NativeCopyStep compare source hc ht tt ac after_t tt ->
  IndexedRunExecution compare source count cursor target tt final_cursor final_target tt.
Proof.
  intros source hc ht ac after_t count cursor target final_cursor final_target CONTEXT.
  induction CONTEXT as [count fc ft TAIL|count c t middle next fc ft STEP REST IH];
    intro HOLE.
  - eapply IndexedRunMore; eassumption.
  - eapply IndexedRunMore; [exact STEP|now apply IH].
Qed.

Inductive SavedPassContext (maximum width : nat) (source : list Entry)
    (hole_cursor : Cursor) (hole_target : list Entry)
    (after_cursor : Cursor) (after_target : list Entry) :
    nat -> list Entry -> list Entry -> Prop :=
| SavedPassHole : forall start target count final_cursor next final_target,
    start < length source ->
    SavedRunContext source hole_cursor hole_target after_cursor after_target count
      (reset_cursor maximum (length source) start width) target final_cursor next ->
    IndexedPassExecution compare maximum width source (run_end final_cursor)
      next tt final_target tt ->
    SavedPassContext maximum width source hole_cursor hole_target after_cursor after_target
      start target final_target
| SavedPassBefore : forall start target count final_cursor next final_target,
    start < length source ->
    IndexedRunExecution compare source count
      (reset_cursor maximum (length source) start width) target tt final_cursor next tt ->
    SavedPassContext maximum width source hole_cursor hole_target after_cursor after_target
      (run_end final_cursor) next final_target ->
    SavedPassContext maximum width source hole_cursor hole_target after_cursor after_target
      start target final_target.

Theorem saved_pass_context_plugs_the_exact_native_copy :
  forall maximum width source hc ht ac after_t start target final_target,
  SavedPassContext maximum width source hc ht ac after_t start target final_target ->
  NativeCopyStep compare source hc ht tt ac after_t tt ->
  IndexedPassExecution compare maximum width source start target tt final_target tt.
Proof.
  intros maximum width source hc ht ac after_t start target final_target CONTEXT.
  induction CONTEXT as
    [start target count fc next ft HS RUN TAIL
    |start target count fc next ft HS RUN REST IH]; intro HOLE.
  - eapply IndexedPassMore; [exact HS| |exact TAIL].
    eapply saved_run_context_plugs_the_exact_native_copy; eassumption.
  - eapply IndexedPassMore; [exact HS|exact RUN|now apply IH].
Qed.

(** Earlier passes retain their physical targets, swaps and saturated widths.
    At the hole's pass, source is exactly hole_source, not initial source. *)
Inductive SavedOuterContext (maximum : nat) (hole_source : list Entry)
    (hole_cursor : Cursor) (hole_target : list Entry)
    (after_cursor : Cursor) (after_target : list Entry) :
    nat -> nat -> list Entry -> option (list Entry) ->
    list Entry -> option (list Entry) -> Prop :=
| SavedOuterHole : forall count width scratch completed output final_scratch,
    width < length hole_source ->
    SavedPassContext maximum width hole_source hole_cursor hole_target after_cursor after_target
      0 (scratch_payload hole_source scratch) completed ->
    NativeOuterExecution compare maximum count (saturated_double maximum width)
      completed (Some hole_source) tt output final_scratch tt ->
    SavedOuterContext maximum hole_source hole_cursor hole_target after_cursor after_target
      (S count) width hole_source scratch output final_scratch
| SavedOuterBefore : forall count width source scratch completed output final_scratch,
    width < length source ->
    IndexedPassExecution compare maximum width source 0
      (scratch_payload source scratch) tt completed tt ->
    SavedOuterContext maximum hole_source hole_cursor hole_target after_cursor after_target
      count (saturated_double maximum width) completed (Some source) output final_scratch ->
    SavedOuterContext maximum hole_source hole_cursor hole_target after_cursor after_target
      (S count) width source scratch output final_scratch.

Theorem saved_outer_context_plugs_the_exact_native_copy :
  forall maximum source hc ht ac after_t count width initial scratch output final_scratch,
  SavedOuterContext maximum source hc ht ac after_t count width initial scratch output final_scratch ->
  NativeCopyStep compare source hc ht tt ac after_t tt ->
  NativeOuterExecution compare maximum count width initial scratch tt output final_scratch tt.
Proof.
  intros maximum source hc ht ac after_t count width initial scratch output final_scratch CONTEXT.
  induction CONTEXT as
    [count width scratch completed output final_scratch HW PASS TAIL
    |count width initial scratch completed output final_scratch HW PASS REST IH]; intro HOLE.
  - eapply NativeOuterPass; [exact HW| |exact TAIL].
    eapply saved_pass_context_plugs_the_exact_native_copy; eassumption.
  - eapply NativeOuterPass; [exact HW|exact PASS|now apply IH].
Qed.
End SavedNativeContexts.

Section MapPhaseContinuations.
Context {Key Value : Type}.
Variable key_compare : Key -> Key -> comparison.
Variable value_compare : Value -> Value -> comparison.
Variable key_alias : Key -> Key -> bool.
Variable value_alias : Value -> Value -> bool.
Hypothesis key_alias_sound : forall x y,
  key_alias x y = true -> key_compare x y = Eq.
Hypothesis value_alias_sound : forall x y,
  value_alias x y = true -> value_compare x y = Eq.
Local Notation PC :=
  (SemanticComparisonLaws.SemanticComparisonLaws.pair_compare key_compare value_compare).
Local Notation NC :=
  (fun (lhs rhs : Key * Value) (_ : unit) => (Some (PC lhs rhs), tt)).
Local Notation PP :=
  (@PairProtocol Key Value key_compare value_compare key_alias value_alias).
Local Notation UL :=
  (@UnitLexExecution Key Value key_compare value_compare key_alias value_alias).

(** Source phase order is Lead(Equal), SortLeft, release left scratch,
    SortRight, release right scratch, Lexicographic at unit_cursor 0.
    The final UnitLex witness already includes the decisive Lead/Done route.
    Final scratch values are deliberately not reused after each release. *)
Inductive MapNativeCompletion (maximum : nat)
    (left_input right_input left_output right_output : list (Key * Value))
    (result : comparison) : Prop :=
| MapNativeCompleted : forall left_count left_scratch right_count right_scratch lex_count,
    NativeOuterExecution NC maximum left_count 1 left_input None tt left_output left_scratch tt ->
    NativeOuterExecution NC maximum right_count 1 right_input None tt right_output right_scratch tt ->
    UL left_output right_output 0 lex_count result ->
    MapNativeCompletion maximum left_input right_input left_output right_output result.

Inductive SavedMapSortContinuation (maximum : nat) (hole_source : list (Key * Value))
    (hc : Cursor) (ht : list (Key * Value)) (ac : Cursor) (after_t : list (Key * Value))
    (left_input right_input left_output right_output : list (Key * Value))
    (result : comparison) : Prop :=
| SavedSortLeftDestination : forall left_count left_scratch right_count right_scratch lex_count,
    SavedOuterContext NC maximum hole_source hc ht ac after_t
      left_count 1 left_input None left_output left_scratch ->
    NativeOuterExecution NC maximum right_count 1 right_input None tt right_output right_scratch tt ->
    UL left_output right_output 0 lex_count result ->
    SavedMapSortContinuation maximum hole_source hc ht ac after_t
      left_input right_input left_output right_output result
| SavedSortRightDestination : forall left_count left_scratch right_count right_scratch lex_count,
    NativeOuterExecution NC maximum left_count 1 left_input None tt left_output left_scratch tt ->
    SavedOuterContext NC maximum hole_source hc ht ac after_t
      right_count 1 right_input None right_output right_scratch ->
    UL left_output right_output 0 lex_count result ->
    SavedMapSortContinuation maximum hole_source hc ht ac after_t
      left_input right_input left_output right_output result.

Theorem completed_sort_pair_plugs_its_saved_actual_map_destination :
  forall maximum source hc ht lhs rhs answers decision next
    left_input right_input left_output right_output result,
  NativeRequest source hc lhs rhs -> PP lhs rhs answers decision ->
  copy_record (accept_side decision) hc source ht =
    Some (advance (accept_side decision) hc, next) ->
  SavedMapSortContinuation maximum source hc ht
    (advance (accept_side decision) hc) next
    left_input right_input left_output right_output result ->
  MapNativeCompletion maximum left_input right_input left_output right_output result.
Proof.
  intros maximum source hc ht lhs rhs answers decision next
    left_input right_input left_output right_output result READY PAIR COPY CONTEXT.
  assert (STEP : NativeCopyStep NC source hc ht tt
      (advance (accept_side decision) hc) next tt).
  { eapply NativeAccepted; [exact READY| |exact COPY].
    change ((Some (PC lhs rhs), tt) = (Some decision, tt)).
    rewrite (@pair_request_accept_returns_key_then_value
      Key Value key_compare value_compare key_alias value_alias
      key_alias_sound value_alias_sound lhs rhs answers decision PAIR).
    reflexivity. }
  destruct CONTEXT as [lc ls rc rs n LEFT RIGHT LEX|lc ls rc rs n LEFT RIGHT LEX].
  - eapply MapNativeCompleted; [|exact RIGHT|exact LEX].
    eapply saved_outer_context_plugs_the_exact_native_copy; eassumption.
  - eapply MapNativeCompleted; [exact LEFT| |exact LEX].
    eapply saved_outer_context_plugs_the_exact_native_copy; eassumption.
Qed.

Theorem actual_map_completion_returns_the_sorted_roster_lex_result :
  forall maximum left_input right_input left_output right_output result,
  MapNativeCompletion maximum left_input right_input left_output right_output result ->
  result = list_compare PC left_output right_output.
Proof.
  intros maximum left_input right_input left_output right_output result COMPLETE.
  destruct COMPLETE as [lc ls rc rs n LEFT RIGHT LEX].
  exact (@zero_initialized_map_lex_returns_sorted_pair_list_comparison
    Key Value key_compare value_compare key_alias value_alias
    key_alias_sound value_alias_sound left_output right_output n result LEX).
Qed.

Theorem actual_map_completion_retains_both_original_native_sort_results :
  forall maximum left_input right_input left_output right_output result,
  length left_input <= maximum -> length right_input <= maximum ->
  MapNativeCompletion maximum left_input right_input left_output right_output result ->
  @SemanticResultMerge.SemanticResultMerge.sort (Key * Value) unit NC left_input tt =
    (Some left_output, tt) /\
  @SemanticResultMerge.SemanticResultMerge.sort (Key * Value) unit NC right_input tt =
    (Some right_output, tt).
Proof.
  intros maximum left_input right_input left_output right_output result HL HR COMPLETE.
  destruct COMPLETE as [lc ls rc rs n LEFT RIGHT LEX]. split.
  - eapply actual_native_sort_has_the_existing_sort_result; eassumption.
  - eapply actual_native_sort_has_the_existing_sort_result; eassumption.
Qed.

Local Notation PrimaryRole :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary.
Local Notation SecondaryRole :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary.

(** These are the three actual pending states reachable for pair() records.
    Primary carries both items and destination. Secondary retains destination;
    its proof evidence remembers the same immutable item identities. *)
Inductive SavedPairPending (lhs rhs : Key * Value) :
    AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Role -> Prop :=
| SavedPrimaryPending : key_alias (fst lhs) (fst rhs) = false ->
    SavedPairPending lhs rhs PrimaryRole
| SavedSecondaryAfterAlias :
    key_alias (fst lhs) (fst rhs) = true ->
    value_alias (snd lhs) (snd rhs) = false ->
    SavedPairPending lhs rhs SecondaryRole
| SavedSecondaryAfterEqual :
    key_alias (fst lhs) (fst rhs) = false -> key_compare (fst lhs) (fst rhs) = Eq ->
    value_alias (snd lhs) (snd rhs) = false ->
    SavedPairPending lhs rhs SecondaryRole.

Theorem completed_primary_keeps_the_exact_secondary_continuation :
  forall lhs rhs response remaining result,
  SavedPairPending lhs rhs PrimaryRole ->
  key_compare (fst lhs) (fst rhs) = response ->
  @after_primary Key Value value_compare value_alias lhs rhs response remaining result ->
  PP lhs rhs ((PrimaryRole, response) :: remaining) result.
Proof.
  intros lhs rhs response remaining result PENDING RESPONSE CONT.
  assert (NONALIAS : key_alias (fst lhs) (fst rhs) = false).
  { inversion PENDING; assumption. }
  apply (proj2 (@native_primary_request_cut_and_plug
    Key Value key_compare value_compare key_alias value_alias lhs rhs
    ((PrimaryRole, response) :: remaining) result NONALIAS)).
  exists response, remaining. split; [reflexivity|]. split; assumption.
Qed.

Theorem completed_secondary_forwards_to_the_saved_destination :
  forall lhs rhs response,
  SavedPairPending lhs rhs SecondaryRole ->
  value_compare (snd lhs) (snd rhs) = response ->
  exists answers, PP lhs rhs answers response.
Proof.
  intros lhs rhs response PENDING RESPONSE.
  inversion PENDING as [|HA VA|HA HK VA].
  - exists [(SecondaryRole, response)].
    apply PairPrimaryAlias; [exact HA|]. apply SecondaryAnswered; assumption.
  - exists [(PrimaryRole, Eq); (SecondaryRole, response)].
    apply PairPrimaryEqual; [exact HA|exact HK|]. apply SecondaryAnswered; assumption.
Qed.

(** Exact earlier Lexicographic iterations; each original accepted Equal
    advances unit_cursor index to unit_cursor (S index). This is evidence
    over existing UnitLexExecution, not a second lexicographic procedure. *)
Inductive SavedUnitLexPrefix (lhs rhs : list (Key * Value)) : nat -> Prop :=
| SavedUnitLexZero : SavedUnitLexPrefix lhs rhs 0
| SavedUnitLexEqual : forall index left right answers,
    SavedUnitLexPrefix lhs rhs index ->
    nth_error lhs index = Some left -> nth_error rhs index = Some right ->
    PP left right answers Eq -> SavedUnitLexPrefix lhs rhs (S index).

Theorem saved_unit_prefix_plugs_the_same_native_lex_witness :
  forall lhs rhs index, SavedUnitLexPrefix lhs rhs index ->
  forall count result, UL lhs rhs index count result ->
  exists total, UL lhs rhs 0 total result.
Proof.
  intros lhs rhs index PREFIX.
  induction PREFIX as [|index left right answers PREFIX IH NL NR PAIR];
    intros count result TAIL.
  - exists count. exact TAIL.
  - assert (LOCAL : UL lhs rhs index (S count) result).
    { eapply UnitEqualPair; eassumption. }
    exact (IH (S count) result LOCAL).
Qed.

Inductive SavedUnitLexSuffix (lhs rhs : list (Key * Value)) (index : nat) :
    comparison -> comparison -> Prop :=
| SavedLexEqualSuffix : forall count result,
    UL lhs rhs (S index) count result -> SavedUnitLexSuffix lhs rhs index Eq result
| SavedLexDecisiveSuffix : forall result,
    result <> Eq -> SavedUnitLexSuffix lhs rhs index result result.

Theorem accepted_lex_pair_takes_its_original_equal_or_lead_branch :
  forall lhs rhs index left right answers decision result,
  nth_error lhs index = Some left -> nth_error rhs index = Some right ->
  PP left right answers decision ->
  SavedUnitLexSuffix lhs rhs index decision result ->
  exists count, UL lhs rhs index count result.
Proof.
  intros lhs rhs index left right answers decision result NL NR PAIR SUFFIX.
  destruct SUFFIX as [count result TAIL|result DEC].
  - exists (S count). eapply UnitEqualPair; eassumption.
  - exists 1. eapply UnitDecisivePair; eassumption.
Qed.

Theorem completed_lex_pair_plugs_its_saved_actual_map_destination :
  forall maximum left_input right_input left_output right_output
    left_count left_scratch right_count right_scratch index left right answers decision result,
  NativeOuterExecution NC maximum left_count 1 left_input None tt left_output left_scratch tt ->
  NativeOuterExecution NC maximum right_count 1 right_input None tt right_output right_scratch tt ->
  SavedUnitLexPrefix left_output right_output index ->
  nth_error left_output index = Some left -> nth_error right_output index = Some right ->
  PP left right answers decision ->
  SavedUnitLexSuffix left_output right_output index decision result ->
  MapNativeCompletion maximum left_input right_input left_output right_output result.
Proof.
  intros maximum left_input right_input left_output right_output
    left_count left_scratch right_count right_scratch index left right answers decision result
    LEFT RIGHT PREFIX NL NR PAIR SUFFIX.
  destruct (accepted_lex_pair_takes_its_original_equal_or_lead_branch
    left_output right_output index left right answers decision result NL NR PAIR SUFFIX)
    as [count LEX].
  destruct (saved_unit_prefix_plugs_the_same_native_lex_witness
    left_output right_output index PREFIX count result LEX) as [total COMPLETE].
  eapply MapNativeCompleted; eassumption.
Qed.

(** Finite semantic progress with original pair responses. This does not
    assert that budgets admit all actions or that callers keep resuming. *)
Theorem original_pair_responses_construct_the_complete_map_phase_witness :
  forall maximum left_input right_input,
  length left_input <= maximum -> length right_input <= maximum ->
  exists left_output right_output result,
    MapNativeCompletion maximum left_input right_input left_output right_output result.
Proof.
  intros maximum left_input right_input HL HR.
  assert (TOTAL : forall lhs rhs state, exists decision next,
      NC lhs rhs state = (Some decision, next)).
  { intros lhs rhs state. exists (PC lhs rhs), tt. reflexivity. }
  destruct (@responding_driver_completes_the_actual_native_sort
    (Key * Value) unit NC TOTAL maximum left_input tt HL)
    as [lc [left_output [left_scratch [left_last [LEFT LEFT_REST]]]]].
  destruct left_last.
  destruct (@responding_driver_completes_the_actual_native_sort
    (Key * Value) unit NC TOTAL maximum right_input tt HR)
    as [rc [right_output [right_scratch [right_last [RIGHT RIGHT_REST]]]]].
  destruct right_last.
  destruct (@original_unit_map_responses_construct_a_complete_lex_trace
    Key Value key_compare value_compare key_alias value_alias
    key_alias_sound value_alias_sound left_output right_output)
    as [count [result [LEX REST]]].
  exists left_output, right_output, result.
  eapply MapNativeCompleted; eassumption.
Qed.
End MapPhaseContinuations.
End NativeMapRunSuspension.

Print Assumptions NativeMapRunSuspension.native_primary_request_cut_and_plug.
Print Assumptions NativeMapRunSuspension.native_primary_alias_enters_the_existing_secondary_protocol.
Print Assumptions NativeMapRunSuspension.native_secondary_request_forwards_its_one_response.
Print Assumptions NativeMapRunSuspension.no_external_pair_answer_means_both_native_pointer_shortcuts.
Print Assumptions NativeMapRunSuspension.both_live_heads_cut_the_actual_accepted_copy.
Print Assumptions NativeMapRunSuspension.live_run_witness_cuts_before_its_native_copy.
Print Assumptions NativeMapRunSuspension.matched_native_response_plugs_the_same_run_witness.
Print Assumptions NativeMapRunSuspension.terminal_run_witness_has_no_pending_comparison.
Print Assumptions NativeMapRunSuspension.actual_live_map_run_exposes_its_pair_protocol_and_saved_tail.
Print Assumptions NativeMapRunSuspension.completed_native_pair_response_restores_the_same_indexed_run.
Print Assumptions NativeMapRunSuspension.saved_run_context_plugs_the_exact_native_copy.
Print Assumptions NativeMapRunSuspension.saved_pass_context_plugs_the_exact_native_copy.
Print Assumptions NativeMapRunSuspension.saved_outer_context_plugs_the_exact_native_copy.
Print Assumptions NativeMapRunSuspension.completed_sort_pair_plugs_its_saved_actual_map_destination.
Print Assumptions NativeMapRunSuspension.actual_map_completion_returns_the_sorted_roster_lex_result.
Print Assumptions NativeMapRunSuspension.actual_map_completion_retains_both_original_native_sort_results.
Print Assumptions NativeMapRunSuspension.completed_primary_keeps_the_exact_secondary_continuation.
Print Assumptions NativeMapRunSuspension.completed_secondary_forwards_to_the_saved_destination.
Print Assumptions NativeMapRunSuspension.saved_unit_prefix_plugs_the_same_native_lex_witness.
Print Assumptions NativeMapRunSuspension.accepted_lex_pair_takes_its_original_equal_or_lead_branch.
Print Assumptions NativeMapRunSuspension.completed_lex_pair_plugs_its_saved_actual_map_destination.
Print Assumptions NativeMapRunSuspension.original_pair_responses_construct_the_complete_map_phase_witness.
