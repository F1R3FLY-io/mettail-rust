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

(** A retained physical path, not a new runtime comparator or state machine.
    PairAnswers retains an entire existing PairProtocol block. A resume cut
    advances its answered prefix before advancing any physical event, so a
    Primary Equal followed by Secondary preserves the same native copy hole.
    Run/pass/outer annotations thread the exact existing source/target data.
    RunBoundary records a reset-initialized boundary, not an extra reset call;
    initial new/reset and final non-resetting swap timing stay source-audited.

    The source association must identify the actual owner and pending role
    with the retained path/cut. Compiler checking this annotation is not a
    proof of Rust compilation or admission totality. Refusal and destruction
    retain the existing consuming-owner/prepaid-cleanup contracts. *)
Section AnnotatedResumption.
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
Local Notation Role :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Role.
Local Notation Pending := (@SavedPairPending Key Value key_compare key_alias value_alias).

Inductive SortDestination := InLeftSort | InRightSort.
Inductive AwaitFocus :=
| AtSortPair : SortDestination -> list (Key * Value) -> Cursor ->
    list (Key * Value) -> AwaitFocus
| AtLexPair : list (Key * Value) -> list (Key * Value) -> nat -> AwaitFocus.
Inductive NativeEvent :=
| PairAnswers : AwaitFocus -> (Key * Value) -> (Key * Value) -> list Answer -> NativeEvent
| CopiedRecord : SortDestination -> list (Key * Value) -> Cursor ->
    list (Key * Value) -> Side -> list (Key * Value) -> NativeEvent
| RunBoundary : SortDestination -> nat -> nat -> list (Key * Value) -> nat ->
    list (Key * Value) -> NativeEvent
| ScratchBoundary : SortDestination -> list (Key * Value) -> option (list (Key * Value)) -> NativeEvent
| SwappedBuffers : SortDestination -> nat -> nat -> list (Key * Value) -> list (Key * Value) -> NativeEvent
| ReleasedSort : SortDestination -> list (Key * Value) -> option (list (Key * Value)) -> NativeEvent
| EnterRightSort : NativeEvent
| EnterUnitLex : NativeEvent
| AdvancedUnitLex : list (Key * Value) -> list (Key * Value) -> nat -> NativeEvent
| LexLeadDone : comparison -> NativeEvent
| LexExhausted : comparison -> NativeEvent
| FinishedMap : comparison -> NativeEvent.
Definition pair_events focus lhs rhs (answers : list Answer) :=
  [PairAnswers focus lhs rhs answers].

Inductive CopyEvents (destination : SortDestination) (source : list (Key * Value)) :
    Cursor -> list (Key * Value) -> Cursor -> list (Key * Value) -> list NativeEvent -> Prop :=
| EventsAccepted : forall cursor target next lhs rhs answers decision,
    NativeRequest source cursor lhs rhs -> PP lhs rhs answers decision ->
    copy_record (accept_side decision) cursor source target =
      Some (advance (accept_side decision) cursor, next) ->
    CopyEvents destination source cursor target (advance (accept_side decision) cursor) next
      (pair_events (AtSortPair destination source cursor target) lhs rhs answers ++
       [CopiedRecord destination source cursor target (accept_side decision) next])
| EventsLeftTail : forall cursor target next,
    can_copy FromLeft cursor -> right_index cursor = run_end cursor ->
    copy_record FromLeft cursor source target = Some (advance FromLeft cursor, next) ->
    CopyEvents destination source cursor target (advance FromLeft cursor) next
      [CopiedRecord destination source cursor target FromLeft next]
| EventsRightTail : forall cursor target next,
    left_index cursor = run_middle cursor -> can_copy FromRight cursor ->
    copy_record FromRight cursor source target = Some (advance FromRight cursor, next) ->
    CopyEvents destination source cursor target (advance FromRight cursor) next
      [CopiedRecord destination source cursor target FromRight next].

Inductive RunEvents (destination : SortDestination) (source : list (Key * Value)) :
    nat -> Cursor -> list (Key * Value) -> Cursor -> list (Key * Value) -> list NativeEvent -> Prop :=
| RunEventsDone : forall cursor target,
    left_index cursor = run_middle cursor -> right_index cursor = run_end cursor ->
    RunEvents destination source 0 cursor target cursor target []
| RunEventsMore : forall count cursor target middle next final_cursor final_target first rest,
    CopyEvents destination source cursor target middle next first ->
    RunEvents destination source count middle next final_cursor final_target rest ->
    RunEvents destination source (S count) cursor target final_cursor final_target (first ++ rest).

Inductive PassEvents (destination : SortDestination) (maximum width : nat)
    (source : list (Key * Value)) :
    nat -> list (Key * Value) -> list (Key * Value) -> list NativeEvent -> Prop :=
| PassEventsDone : forall target,
    PassEvents destination maximum width source (length source) target target []
| PassEventsMore : forall start target count final_cursor next final_target first rest,
    start < length source ->
    RunEvents destination source count (reset_cursor maximum (length source) start width)
      target final_cursor next first ->
    PassEvents destination maximum width source (run_end final_cursor) next final_target rest ->
    PassEvents destination maximum width source start target final_target
      (RunBoundary destination maximum width source start target :: first ++ rest).

Inductive OuterEvents (destination : SortDestination) (maximum : nat) :
    nat -> nat -> list (Key * Value) -> option (list (Key * Value)) ->
    list (Key * Value) -> option (list (Key * Value)) -> list NativeEvent -> Prop :=
| OuterEventsDone : forall width source scratch,
    length source <= width -> OuterEvents destination maximum 0 width source scratch source scratch []
| OuterEventsPass : forall count width source scratch completed output final_scratch first rest,
    width < length source ->
    PassEvents destination maximum width source 0 (scratch_payload source scratch) completed first ->
    OuterEvents destination maximum count (saturated_double maximum width)
      completed (Some source) output final_scratch rest ->
    OuterEvents destination maximum (S count) width source scratch output final_scratch
      (ScratchBoundary destination source scratch ::
       first ++ SwappedBuffers destination maximum width source completed :: rest).

Inductive LexEvents (lhs rhs : list (Key * Value)) :
    nat -> nat -> comparison -> list NativeEvent -> Prop :=
| LexEventsLeftEnd : forall index,
    nth_error lhs index = None ->
    LexEvents lhs rhs index 0 (Nat.compare (length lhs) (length rhs))
      [LexExhausted (Nat.compare (length lhs) (length rhs))]
| LexEventsRightEnd : forall index left,
    nth_error lhs index = Some left -> nth_error rhs index = None ->
    LexEvents lhs rhs index 0 (Nat.compare (length lhs) (length rhs))
      [LexExhausted (Nat.compare (length lhs) (length rhs))]
| LexEventsEqual : forall index count left right answers result rest,
    nth_error lhs index = Some left -> nth_error rhs index = Some right ->
    PP left right answers Eq -> LexEvents lhs rhs (S index) count result rest ->
    LexEvents lhs rhs index (S count) result
      (pair_events (AtLexPair lhs rhs index) left right answers ++
       AdvancedUnitLex lhs rhs index :: rest)
| LexEventsDecisive : forall index left right answers result,
    nth_error lhs index = Some left -> nth_error rhs index = Some right ->
    PP left right answers result -> result <> Eq ->
    LexEvents lhs rhs index 1 result
      (pair_events (AtLexPair lhs rhs index) left right answers ++ [LexLeadDone result]).

Inductive MapEvents (maximum : nat)
    (left_input right_input left_output right_output : list (Key * Value))
    (result : comparison) : list NativeEvent -> Prop :=
| MapEventsComplete : forall lc ls rc rs n left_events right_events lex_events,
    OuterEvents InLeftSort maximum lc 1 left_input None left_output ls left_events ->
    OuterEvents InRightSort maximum rc 1 right_input None right_output rs right_events ->
    LexEvents left_output right_output 0 n result lex_events ->
    MapEvents maximum left_input right_input left_output right_output result
      (left_events ++ ReleasedSort InLeftSort left_output ls :: EnterRightSort ::
       right_events ++ ReleasedSort InRightSort right_output rs :: EnterUnitLex ::
       lex_events ++ [FinishedMap result]).

Theorem source_copy_constructs_its_physical_events :
  forall destination source cursor target state after_cursor next next_state,
  NativeCopyStep NC source cursor target state after_cursor next next_state ->
  exists events, CopyEvents destination source cursor target after_cursor next events.
Proof.
  intros destination source cursor target state after_cursor next next_state STEP.
  destruct STEP as
    [cursor target next lhs rhs state next_state decision READY CMP COPY
    |cursor target next state LIVE END COPY
    |cursor target next state END LIVE COPY].
  - assert (DEC : PC lhs rhs = decision).
    { change ((Some (PC lhs rhs), tt) = (Some decision, next_state)) in CMP. congruence. }
    destruct (@original_pair_responses_construct_the_request_protocol
      Key Value key_compare value_compare key_alias value_alias lhs rhs)
      as [answers [result PAIR]].
    pose proof (@pair_request_accept_returns_key_then_value
      Key Value key_compare value_compare key_alias value_alias
      key_alias_sound value_alias_sound lhs rhs answers result PAIR) as RESULT.
    assert (SAME : result = decision) by congruence.
    rewrite SAME in PAIR.
    eexists. eapply EventsAccepted; [exact READY|exact PAIR|exact COPY].
  - eexists. eapply EventsLeftTail; eassumption.
  - eexists. eapply EventsRightTail; eassumption.
Qed.

Theorem physical_copy_events_forget_to_the_same_native_step :
  forall destination source cursor target after_cursor next events,
  CopyEvents destination source cursor target after_cursor next events ->
  NativeCopyStep NC source cursor target tt after_cursor next tt.
Proof.
  intros destination source cursor target after_cursor next events EVENTS.
  destruct EVENTS as
    [cursor target next lhs rhs answers decision READY PAIR COPY
    |cursor target next LIVE END COPY|cursor target next END LIVE COPY].
  - eapply NativeAccepted; [exact READY| |exact COPY].
    change ((Some (PC lhs rhs), tt) = (Some decision, tt)).
    rewrite (@pair_request_accept_returns_key_then_value
      Key Value key_compare value_compare key_alias value_alias
      key_alias_sound value_alias_sound lhs rhs answers decision PAIR). reflexivity.
  - eapply NativeLeftTail; eassumption.
  - eapply NativeRightTail; eassumption.
Qed.

Theorem source_run_constructs_its_sequenced_physical_events :
  forall destination source count cursor target state final_cursor final_target last,
  IndexedRunExecution NC source count cursor target state final_cursor final_target last ->
  exists events, RunEvents destination source count cursor target final_cursor final_target events.
Proof.
  intros destination source count cursor target state final_cursor final_target last RUN.
  induction RUN as [cursor target state EL ER
    |count cursor target state middle next next_state fc ft last STEP TAIL IH].
  - exists []. constructor; assumption.
  - destruct (source_copy_constructs_its_physical_events destination source cursor target
      state middle next next_state STEP) as [first COPY].
    destruct IH as [rest NEXT]. exists (first ++ rest). eapply RunEventsMore; eassumption.
Qed.

Theorem sequenced_run_events_forget_to_the_same_native_run :
  forall destination source count cursor target final_cursor final_target events,
  RunEvents destination source count cursor target final_cursor final_target events ->
  IndexedRunExecution NC source count cursor target tt final_cursor final_target tt.
Proof.
  intros destination source count cursor target final_cursor final_target events EVENTS.
  induction EVENTS as [cursor target EL ER
    |count cursor target middle next fc ft first rest COPY TAIL IH].
  - constructor; assumption.
  - eapply IndexedRunMore; [|exact IH].
    eapply physical_copy_events_forget_to_the_same_native_step; eassumption.
Qed.

Theorem source_pass_constructs_its_sequenced_physical_events :
  forall destination maximum width source start target state final_target last,
  IndexedPassExecution NC maximum width source start target state final_target last ->
  exists events, PassEvents destination maximum width source start target final_target events.
Proof.
  intros destination maximum width source start target state final_target last PASS.
  induction PASS as [target state
    |start target state count fc next next_state ft last HS RUN TAIL IH].
  - exists []. constructor.
  - destruct (source_run_constructs_its_sequenced_physical_events destination source count
      (reset_cursor maximum (length source) start width) target state fc next next_state RUN)
      as [first RUN_EVENTS].
    destruct IH as [rest NEXT].
    exists (RunBoundary destination maximum width source start target :: first ++ rest).
    eapply PassEventsMore; eassumption.
Qed.

Theorem sequenced_pass_events_forget_to_the_same_native_pass :
  forall destination maximum width source start target final_target events,
  PassEvents destination maximum width source start target final_target events ->
  IndexedPassExecution NC maximum width source start target tt final_target tt.
Proof.
  intros destination maximum width source start target final_target events EVENTS.
  induction EVENTS as [target|start target count fc next ft first rest HS RUN TAIL IH].
  - constructor.
  - eapply IndexedPassMore; [exact HS| |exact IH].
    eapply sequenced_run_events_forget_to_the_same_native_run; eassumption.
Qed.

Theorem source_outer_constructs_its_sequenced_physical_events :
  forall destination maximum count width source scratch state output final_scratch last,
  NativeOuterExecution NC maximum count width source scratch state output final_scratch last ->
  exists events, OuterEvents destination maximum count width source scratch output final_scratch events.
Proof.
  intros destination maximum count width source scratch state output final_scratch last OUTER.
  induction OUTER as [width source scratch state DONE
    |count width source scratch state completed next output final_scratch last HW PASS TAIL IH].
  - exists []. now constructor.
  - destruct (source_pass_constructs_its_sequenced_physical_events destination maximum width
      source 0 (scratch_payload source scratch) state completed next PASS) as [first PASS_EVENTS].
    destruct IH as [rest NEXT].
    exists (ScratchBoundary destination source scratch :: first ++
      SwappedBuffers destination maximum width source completed :: rest).
    eapply OuterEventsPass; eassumption.
Qed.

Theorem sequenced_outer_events_forget_to_the_same_native_outer :
  forall destination maximum count width source scratch output final_scratch events,
  OuterEvents destination maximum count width source scratch output final_scratch events ->
  NativeOuterExecution NC maximum count width source scratch tt output final_scratch tt.
Proof.
  intros destination maximum count width source scratch output final_scratch events EVENTS.
  induction EVENTS as [width source scratch DONE
    |count width source scratch completed output final_scratch first rest HW PASS TAIL IH].
  - now constructor.
  - eapply NativeOuterPass; [exact HW| |exact IH].
    eapply sequenced_pass_events_forget_to_the_same_native_pass; eassumption.
Qed.

Theorem source_unit_lex_constructs_its_sequenced_events :
  forall lhs rhs index count result,
  UL lhs rhs index count result -> exists events, LexEvents lhs rhs index count result events.
Proof.
  intros lhs rhs index count result LEX.
  induction LEX as [index END|index left NL END
    |index count left right answers result NL NR PAIR TAIL IH
    |index left right answers result NL NR PAIR DEC].
  - eexists. now apply LexEventsLeftEnd.
  - eexists. eapply LexEventsRightEnd; eassumption.
  - destruct IH as [rest NEXT]. eexists. eapply LexEventsEqual; eassumption.
  - eexists. eapply LexEventsDecisive; eassumption.
Qed.

Theorem sequenced_unit_lex_events_forget_to_the_same_native_lex :
  forall lhs rhs index count result events,
  LexEvents lhs rhs index count result events -> UL lhs rhs index count result.
Proof.
  intros lhs rhs index count result events EVENTS.
  induction EVENTS as [index END|index left NL END
    |index count left right answers result rest NL NR PAIR TAIL IH
    |index left right answers result NL NR PAIR DEC].
  - now apply UnitLeftExhausted.
  - eapply UnitRightExhausted; eassumption.
  - eapply UnitEqualPair; eassumption.
  - eapply UnitDecisivePair; eassumption.
Qed.

Theorem every_native_map_completion_constructs_its_resume_spine :
  forall maximum left_input right_input left_output right_output result,
  MapNativeCompletion key_compare value_compare key_alias value_alias
    maximum left_input right_input left_output right_output result ->
  exists events, MapEvents maximum left_input right_input left_output right_output result events.
Proof.
  intros maximum left_input right_input left_output right_output result COMPLETE.
  destruct COMPLETE as [lc ls rc rs n LEFT RIGHT LEX].
  destruct (source_outer_constructs_its_sequenced_physical_events InLeftSort maximum
    lc 1 left_input None tt left_output ls tt LEFT) as [le LEFT_EVENTS].
  destruct (source_outer_constructs_its_sequenced_physical_events InRightSort maximum
    rc 1 right_input None tt right_output rs tt RIGHT) as [re RIGHT_EVENTS].
  destruct (source_unit_lex_constructs_its_sequenced_events
    left_output right_output 0 n result LEX) as [xe LEX_EVENTS].
  eexists. eapply MapEventsComplete; eassumption.
Qed.

Theorem constructed_resume_spine_retains_the_actual_map_completion :
  forall maximum left_input right_input left_output right_output result events,
  MapEvents maximum left_input right_input left_output right_output result events ->
  MapNativeCompletion key_compare value_compare key_alias value_alias
    maximum left_input right_input left_output right_output result.
Proof.
  intros maximum left_input right_input left_output right_output result events EVENTS.
  destruct EVENTS as [lc ls rc rs n le re xe LEFT RIGHT LEX].
  eapply MapNativeCompleted.
  - eapply sequenced_outer_events_forget_to_the_same_native_outer; exact LEFT.
  - eapply sequenced_outer_events_forget_to_the_same_native_outer; exact RIGHT.
  - eapply sequenced_unit_lex_events_forget_to_the_same_native_lex; exact LEX.
Qed.

Definition focus_has_requested_operands focus lhs rhs := match focus with
| AtSortPair _ source cursor _ => NativeRequest source cursor lhs rhs
| AtLexPair left_items right_items index =>
    nth_error left_items index = Some lhs /\ nth_error right_items index = Some rhs end.
Definition original_answer role lhs rhs response := match role with
| AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Primary =>
    key_compare (fst lhs) (fst rhs) = response
| AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Secondary =>
    value_compare (snd lhs) (snd rhs) = response end.
Definition pair_answer_law lhs rhs (answer : Answer) :=
  Pending lhs rhs (fst answer) /\ original_answer (fst answer) lhs rhs (snd answer).

Lemma existing_pair_protocol_certifies_every_pending_answer :
  forall lhs rhs answers result, PP lhs rhs answers result ->
  Forall (pair_answer_law lhs rhs) answers.
Proof.
  intros lhs rhs answers result PAIR.
  destruct PAIR as [answers result HA SECOND|result HA HK DEC|answers result HA HK SECOND].
  - destruct SECOND as [VA|result VA HR].
    + constructor.
    + constructor; [|constructor]. split; [now apply SavedSecondaryAfterAlias|exact HR].
  - constructor; [|constructor]. split; [now apply SavedPrimaryPending|exact HK].
  - constructor.
    + split; [now apply SavedPrimaryPending|exact HK].
    + destruct SECOND as [VA|result VA HR].
      * constructor.
      * constructor; [|constructor]. split; [eapply SavedSecondaryAfterEqual; eassumption|exact HR].
Qed.

Definition native_body_event_law event := match event with
| PairAnswers focus lhs rhs answers =>
    focus_has_requested_operands focus lhs rhs /\ exists result, PP lhs rhs answers result
| CopiedRecord _ source cursor target side next =>
    copy_record side cursor source target = Some (advance side cursor, next)
| SwappedBuffers _ maximum width source completed =>
    exists target, IndexedPassExecution NC maximum width source 0 target tt completed tt
| FinishedMap _ => False
| _ => True end.

Lemma pair_event_annotation_has_exact_original_operands :
  forall focus lhs rhs answers result,
  focus_has_requested_operands focus lhs rhs -> PP lhs rhs answers result ->
  Forall native_body_event_law (pair_events focus lhs rhs answers).
Proof.
  intros focus lhs rhs answers result FOCUS PAIR.
  constructor; [|constructor]. split; [exact FOCUS|]. exists result. exact PAIR.
Qed.

Lemma physical_copy_event_annotation_is_certified :
  forall destination source cursor target after_cursor next events,
  CopyEvents destination source cursor target after_cursor next events ->
  Forall native_body_event_law events.
Proof.
  intros destination source cursor target after_cursor next events EVENTS.
  destruct EVENTS as [cursor target next lhs rhs answers decision READY PAIR COPY
    |cursor target next LIVE END COPY|cursor target next END LIVE COPY].
  - apply Forall_app. split.
    + eapply pair_event_annotation_has_exact_original_operands; eassumption.
    + constructor; [exact COPY|constructor].
  - constructor; [exact COPY|constructor].
  - constructor; [exact COPY|constructor].
Qed.
Lemma sequenced_run_event_annotation_is_certified :
  forall destination source count cursor target final_cursor final_target events,
  RunEvents destination source count cursor target final_cursor final_target events ->
  Forall native_body_event_law events.
Proof.
  intros destination source count cursor target final_cursor final_target events EVENTS.
  induction EVENTS as [cursor target EL ER|count cursor target middle next fc ft first rest COPY TAIL IH].
  - constructor.
  - apply Forall_app. split; [eapply physical_copy_event_annotation_is_certified; exact COPY|exact IH].
Qed.
Lemma sequenced_pass_event_annotation_is_certified :
  forall destination maximum width source start target final_target events,
  PassEvents destination maximum width source start target final_target events ->
  Forall native_body_event_law events.
Proof.
  intros destination maximum width source start target final_target events EVENTS.
  induction EVENTS as [target|start target count fc next ft first rest HS RUN TAIL IH].
  - constructor.
  - constructor; [exact I|]. apply Forall_app. split;
      [eapply sequenced_run_event_annotation_is_certified; exact RUN|exact IH].
Qed.
Lemma sequenced_outer_event_annotation_is_certified :
  forall destination maximum count width source scratch output final_scratch events,
  OuterEvents destination maximum count width source scratch output final_scratch events ->
  Forall native_body_event_law events.
Proof.
  intros destination maximum count width source scratch output final_scratch events EVENTS.
  induction EVENTS as [width source scratch DONE
    |count width source scratch completed output final_scratch first rest HW PASS TAIL IH].
  - constructor.
  - constructor; [exact I|]. apply Forall_app. split.
    + eapply sequenced_pass_event_annotation_is_certified; exact PASS.
    + constructor; [|exact IH]. exists (scratch_payload source scratch).
      eapply sequenced_pass_events_forget_to_the_same_native_pass; exact PASS.
Qed.
Lemma sequenced_unit_lex_event_annotation_is_certified :
  forall lhs rhs index count result events,
  LexEvents lhs rhs index count result events -> Forall native_body_event_law events.
Proof.
  intros lhs rhs index count result events EVENTS.
  induction EVENTS as [index END|index left NL END
    |index count left right answers result rest NL NR PAIR TAIL IH
    |index left right answers result NL NR PAIR DEC].
  - constructor; [exact I|constructor].
  - constructor; [exact I|constructor].
  - apply Forall_app. split.
    + eapply pair_event_annotation_has_exact_original_operands; [split; eassumption|exact PAIR].
    + constructor; [exact I|exact IH].
  - apply Forall_app. split.
    + eapply pair_event_annotation_has_exact_original_operands; [split; eassumption|exact PAIR].
    + constructor; [exact I|constructor].
Qed.

(** Local block adjacency is exported separately from per-event validity.
    The entire MapEvents certificate is still required for global physical
    sequencing; Forall native_body_event_law alone is not a native path. *)
Definition pair_following_action focus lhs rhs answers next :=
  exists decision, PP lhs rhs answers decision /\
  match focus with
  | AtSortPair destination source cursor target =>
      exists output, next = CopiedRecord destination source cursor target (accept_side decision) output
  | AtLexPair left_items right_items index =>
      next = match decision with
        | Eq => AdvancedUnitLex left_items right_items index
        | Lt | Gt => LexLeadDone decision end
  end.
Fixpoint pair_edges events : Prop := match events with
| [] => True
| PairAnswers focus lhs rhs answers :: rest =>
    (match rest with [] => False | next :: _ => pair_following_action focus lhs rhs answers next end) /\
    pair_edges rest
| _ :: rest => pair_edges rest end.

Lemma pair_edges_app : forall first rest,
  pair_edges first -> pair_edges rest -> pair_edges (first ++ rest).
Proof.
  induction first as [|event first IH]; intros rest FIRST REST; [exact REST|].
  destruct event; cbn [pair_edges app] in FIRST |- *;
    try (exact (IH rest FIRST REST)).
  destruct first as [|next first]; [destruct FIRST as [IMP _]; contradiction|].
  destruct FIRST as [EDGE TAIL]. split; [exact EDGE|]. exact (IH rest TAIL REST).
Qed.
Lemma pair_edges_suffix : forall first rest,
  pair_edges (first ++ rest) -> pair_edges rest.
Proof.
  induction first as [|event first IH]; intros rest PATH; [exact PATH|].
  destruct event; cbn [pair_edges app] in PATH; apply IH;
    exact PATH || exact (proj2 PATH).
Qed.
Lemma own_pair_action_extends_the_certified_path :
  forall focus lhs rhs answers next rest,
  pair_following_action focus lhs rhs answers next -> pair_edges (next :: rest) ->
  pair_edges (pair_events focus lhs rhs answers ++ next :: rest).
Proof. intros. unfold pair_events. cbn [pair_edges app]. split; assumption. Qed.

Lemma copy_events_preserve_their_own_pair_edges :
  forall destination source cursor target after_cursor next events,
  CopyEvents destination source cursor target after_cursor next events -> pair_edges events.
Proof.
  intros destination source cursor target after_cursor next events EVENTS.
  destruct EVENTS as [cursor target next lhs rhs answers decision READY PAIR COPY
    |cursor target next LIVE END COPY|cursor target next END LIVE COPY].
  - apply own_pair_action_extends_the_certified_path; [|exact I].
    exists decision. split; [exact PAIR|]. exists next. reflexivity.
  - exact I.
  - exact I.
Qed.
Lemma run_events_preserve_their_own_pair_edges :
  forall destination source count cursor target final_cursor final_target events,
  RunEvents destination source count cursor target final_cursor final_target events -> pair_edges events.
Proof.
  intros destination source count cursor target final_cursor final_target events EVENTS.
  induction EVENTS as [cursor target EL ER|count cursor target middle next fc ft first rest COPY TAIL IH].
  - exact I.
  - apply pair_edges_app; [eapply copy_events_preserve_their_own_pair_edges; exact COPY|exact IH].
Qed.
Lemma pass_events_preserve_their_own_pair_edges :
  forall destination maximum width source start target final_target events,
  PassEvents destination maximum width source start target final_target events -> pair_edges events.
Proof.
  intros destination maximum width source start target final_target events EVENTS.
  induction EVENTS as [target|start target count fc next ft first rest HS RUN TAIL IH].
  - exact I.
  - cbn [pair_edges]. apply pair_edges_app;
      [eapply run_events_preserve_their_own_pair_edges; exact RUN|exact IH].
Qed.
Lemma outer_events_preserve_their_own_pair_edges :
  forall destination maximum count width source scratch output final_scratch events,
  OuterEvents destination maximum count width source scratch output final_scratch events -> pair_edges events.
Proof.
  intros destination maximum count width source scratch output final_scratch events EVENTS.
  induction EVENTS as [width source scratch DONE
    |count width source scratch completed output final_scratch first rest HW PASS TAIL IH].
  - exact I.
  - cbn [pair_edges]. apply pair_edges_app;
      [eapply pass_events_preserve_their_own_pair_edges; exact PASS|exact IH].
Qed.
Lemma lex_events_preserve_their_own_pair_edges :
  forall lhs rhs index count result events,
  LexEvents lhs rhs index count result events -> pair_edges events.
Proof.
  intros lhs rhs index count result events EVENTS.
  induction EVENTS as [index END|index left NL END
    |index count left right answers result rest NL NR PAIR TAIL IH
    |index left right answers result NL NR PAIR DEC].
  - exact I.
  - exact I.
  - apply own_pair_action_extends_the_certified_path; [|exact IH].
    exists Eq. split; [exact PAIR|reflexivity].
  - apply own_pair_action_extends_the_certified_path; [|exact I].
    exists result. split; [exact PAIR|]. destruct result; [contradiction|reflexivity|reflexivity].
Qed.

Theorem complete_spine_has_one_terminal_after_its_certified_body :
  forall maximum left_input right_input left_output right_output result events,
  MapEvents maximum left_input right_input left_output right_output result events ->
  exists body,
    events = body ++ [FinishedMap result] /\
    Forall native_body_event_law body /\ pair_edges body.
Proof.
  intros maximum left_input right_input left_output right_output result events EVENTS.
  destruct EVENTS as [lc ls rc rs n le re xe LEFT RIGHT LEX].
  pose proof (sequenced_outer_event_annotation_is_certified
    InLeftSort maximum lc 1 left_input None left_output ls le LEFT) as VL.
  pose proof (sequenced_outer_event_annotation_is_certified
    InRightSort maximum rc 1 right_input None right_output rs re RIGHT) as VR.
  pose proof (sequenced_unit_lex_event_annotation_is_certified
    left_output right_output 0 n result xe LEX) as VX.
  pose proof (outer_events_preserve_their_own_pair_edges
    InLeftSort maximum lc 1 left_input None left_output ls le LEFT) as EL.
  pose proof (outer_events_preserve_their_own_pair_edges
    InRightSort maximum rc 1 right_input None right_output rs re RIGHT) as ER.
  pose proof (lex_events_preserve_their_own_pair_edges
    left_output right_output 0 n result xe LEX) as EX.
  exists (le ++ [ReleasedSort InLeftSort left_output ls; EnterRightSort] ++
    re ++ [ReleasedSort InRightSort right_output rs; EnterUnitLex] ++ xe).
  split.
  - repeat rewrite <- app_assoc. reflexivity.
  - split.
    + repeat rewrite Forall_app. repeat split; try assumption; repeat constructor.
    + apply pair_edges_app; [exact EL|]. cbn [pair_edges app].
      apply pair_edges_app; [exact ER|]. cbn [pair_edges app]. exact EX.
Qed.

(** A cut retains arbitrary executed physical events and an arbitrary
    answered prefix in its current pair block. Only the residual suffix is
    searched after the last answer; the initial spine is never replayed. *)
Definition AtAnswer body before focus lhs rhs answered pending remaining after :=
  body = before ++ PairAnswers focus lhs rhs (answered ++ pending :: remaining) :: after.
Definition quiet_event event := match event with
| PairAnswers _ _ _ answers => answers = []
| FinishedMap _ => False
| _ => True end.

Theorem every_retained_answer_cut_has_its_exact_source_pending_state :
  forall body before focus lhs rhs answered pending remaining after,
  Forall native_body_event_law body ->
  AtAnswer body before focus lhs rhs answered pending remaining after ->
  focus_has_requested_operands focus lhs rhs /\
  Pending lhs rhs (fst pending) /\ original_answer (fst pending) lhs rhs (snd pending) /\
  Forall native_body_event_law after.
Proof.
  intros body before focus lhs rhs answered pending remaining after VALID CUT.
  unfold AtAnswer in CUT. rewrite CUT in VALID.
  apply Forall_app in VALID as [PAST CURRENT].
  inversion CURRENT as [|event rest BLOCK FUTURE]; subst.
  destruct BLOCK as [FOCUS [result PAIR]].
  pose proof (existing_pair_protocol_certifies_every_pending_answer
    lhs rhs (answered ++ pending :: remaining) result PAIR) as ANSWERS.
  apply Forall_app in ANSWERS as [DONE NEXT].
  inversion NEXT as [|answer tail CURRENT_ANSWER LATER]; subst.
  destruct CURRENT_ANSWER as [PENDING RESPONSE].
  split; [exact FOCUS|]. split; [exact PENDING|]. split; assumption.
Qed.

Theorem every_retained_pair_cut_exposes_its_own_physical_accept_action :
  forall body before focus lhs rhs answered pending remaining after,
  pair_edges body ->
  AtAnswer body before focus lhs rhs answered pending remaining after ->
  exists next rest,
    after = next :: rest /\
    pair_following_action focus lhs rhs (answered ++ pending :: remaining) next /\
    pair_edges after.
Proof.
  intros body before focus lhs rhs answered pending remaining after EDGES CUT.
  unfold AtAnswer in CUT. rewrite CUT in EDGES.
  pose proof (pair_edges_suffix before
    (PairAnswers focus lhs rhs (answered ++ pending :: remaining) :: after) EDGES) as CURRENT.
  cbn [pair_edges] in CURRENT. destruct CURRENT as [EDGE FUTURE].
  destruct after as [|next rest]; [contradiction|].
  exists next, rest. split; [reflexivity|]. split; assumption.
Qed.

Lemma certified_event_is_quiet_or_a_nonempty_pair_block : forall event,
  native_body_event_law event -> quiet_event event \/
  exists focus lhs rhs pending remaining,
    event = PairAnswers focus lhs rhs (pending :: remaining).
Proof.
  intros event.
  destruct event as [focus lhs rhs answers
    |destination source cursor target side next
    |destination maximum width source start target
    |destination source scratch
    |destination maximum width source completed
    |destination output scratch
    | | |lhs rhs index|decision|decision|decision];
    cbn [native_body_event_law quiet_event]; intro VALID;
    try (left; exact I); try contradiction.
  destruct answers as [|pending remaining].
  - left. reflexivity.
  - right. exists focus, lhs, rhs, pending, remaining. reflexivity.
Qed.

Theorem certified_suffix_exposes_its_next_pair_or_terminal_path : forall body,
  Forall native_body_event_law body ->
  Forall quiet_event body \/
  exists before focus lhs rhs pending remaining after,
    Forall quiet_event before /\ AtAnswer body before focus lhs rhs [] pending remaining after.
Proof.
  intros body VALID. induction VALID as [|event rest HEAD TAIL IH].
  - left. constructor.
  - destruct (certified_event_is_quiet_or_a_nonempty_pair_block event HEAD)
      as [QUIET|[focus [lhs [rhs [pending [remaining EVENT]]]]]].
    + destruct IH as [DONE|[before [focus [lhs [rhs [pending [remaining [after [PREFIX CUT]]]]]]]]].
      * left. constructor; assumption.
      * right. exists (event :: before), focus, lhs, rhs, pending, remaining, after.
        split; [constructor; assumption|]. unfold AtAnswer in *. cbn [app]. now rewrite CUT.
    + right. exists [], focus, lhs, rhs, pending, remaining, rest.
      split; [constructor|]. unfold AtAnswer. cbn [app]. now rewrite EVENT.
Qed.

Lemma two_original_answers_at_the_same_pending_role_are_equal :
  forall role lhs rhs first second,
  original_answer role lhs rhs first -> original_answer role lhs rhs second -> first = second.
Proof. intros role lhs rhs first second H1 H2. destruct role; cbn in *; congruence. Qed.

Theorem matching_response_advances_within_the_same_native_pair_hole :
  forall body before focus lhs rhs answered pending next remaining after response,
  Forall native_body_event_law body ->
  AtAnswer body before focus lhs rhs answered pending (next :: remaining) after ->
  original_answer (fst pending) lhs rhs response ->
  response = snd pending /\
  AtAnswer body before focus lhs rhs (answered ++ [pending]) next remaining after.
Proof.
  intros body before focus lhs rhs answered pending next remaining after response VALID CUT RESPONSE.
  destruct (every_retained_answer_cut_has_its_exact_source_pending_state
    body before focus lhs rhs answered pending (next :: remaining) after VALID CUT)
    as [FOCUS [PENDING [EXPECTED FUTURE]]]. split.
  - eapply two_original_answers_at_the_same_pending_role_are_equal; eassumption.
  - unfold AtAnswer in *. rewrite <- app_assoc. cbn [app]. exact CUT.
Qed.

Theorem matching_last_response_advances_into_the_saved_physical_suffix :
  forall body before focus lhs rhs answered pending after response,
  Forall native_body_event_law body ->
  AtAnswer body before focus lhs rhs answered pending [] after ->
  original_answer (fst pending) lhs rhs response ->
  response = snd pending /\
  body = (before ++ [PairAnswers focus lhs rhs (answered ++ [pending])]) ++ after /\
  Forall native_body_event_law after /\
  (Forall quiet_event after \/
    exists quiet next_focus next_lhs next_rhs next remaining later,
      Forall quiet_event quiet /\
      AtAnswer body
        ((before ++ [PairAnswers focus lhs rhs (answered ++ [pending])]) ++ quiet)
        next_focus next_lhs next_rhs [] next remaining later).
Proof.
  intros body before focus lhs rhs answered pending after response VALID CUT RESPONSE.
  destruct (every_retained_answer_cut_has_its_exact_source_pending_state
    body before focus lhs rhs answered pending [] after VALID CUT)
    as [FOCUS [PENDING [EXPECTED FUTURE]]].
  assert (PATH : body = (before ++ [PairAnswers focus lhs rhs (answered ++ [pending])]) ++ after).
  { unfold AtAnswer in CUT. rewrite <- app_assoc. cbn [app]. exact CUT. }
  split.
  - eapply two_original_answers_at_the_same_pending_role_are_equal; eassumption.
  - split; [exact PATH|]. split; [exact FUTURE|].
    destruct (certified_suffix_exposes_its_next_pair_or_terminal_path after FUTURE)
      as [DONE|[quiet [nf [nl [nr [next [remaining [later [QUIET NEXT]]]]]]]]].
    + left. exact DONE.
    + right. exists quiet, nf, nl, nr, next, remaining, later. split; [exact QUIET|].
      unfold AtAnswer in NEXT |- *. rewrite PATH, NEXT.
      repeat rewrite <- app_assoc. reflexivity.
Qed.

(** Initial extraction and every later cut retain this SAME MapEvents path.
    Arbitrary-prefix advance above supplies the induction over resumed child
    answers. Quiet events are still real admitted work; quiet means only that
    no external child answer is needed, not that executing them is free. *)
Theorem native_completion_constructs_a_certified_initial_resume_frontier :
  forall maximum li ri lo ro result,
  MapNativeCompletion key_compare value_compare key_alias value_alias maximum li ri lo ro result ->
  exists body,
    MapEvents maximum li ri lo ro result (body ++ [FinishedMap result]) /\
    Forall native_body_event_law body /\ pair_edges body /\
    (Forall quiet_event body \/
      exists before focus lhs rhs pending remaining after,
        Forall quiet_event before /\ AtAnswer body before focus lhs rhs [] pending remaining after).
Proof.
  intros maximum li ri lo ro result COMPLETE.
  destruct (every_native_map_completion_constructs_its_resume_spine
    maximum li ri lo ro result COMPLETE) as [events EVENTS].
  destruct (complete_spine_has_one_terminal_after_its_certified_body
    maximum li ri lo ro result events EVENTS) as [body [END [VALID EDGES]]].
  subst events. exists body. split; [exact EVENTS|].
  split; [exact VALID|]. split; [exact EDGES|].
  now apply certified_suffix_exposes_its_next_pair_or_terminal_path.
Qed.
End AnnotatedResumption.
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
Print Assumptions NativeMapRunSuspension.source_copy_constructs_its_physical_events.
Print Assumptions NativeMapRunSuspension.physical_copy_events_forget_to_the_same_native_step.
Print Assumptions NativeMapRunSuspension.source_run_constructs_its_sequenced_physical_events.
Print Assumptions NativeMapRunSuspension.sequenced_run_events_forget_to_the_same_native_run.
Print Assumptions NativeMapRunSuspension.source_pass_constructs_its_sequenced_physical_events.
Print Assumptions NativeMapRunSuspension.sequenced_pass_events_forget_to_the_same_native_pass.
Print Assumptions NativeMapRunSuspension.source_outer_constructs_its_sequenced_physical_events.
Print Assumptions NativeMapRunSuspension.sequenced_outer_events_forget_to_the_same_native_outer.
Print Assumptions NativeMapRunSuspension.source_unit_lex_constructs_its_sequenced_events.
Print Assumptions NativeMapRunSuspension.sequenced_unit_lex_events_forget_to_the_same_native_lex.
Print Assumptions NativeMapRunSuspension.every_native_map_completion_constructs_its_resume_spine.
Print Assumptions NativeMapRunSuspension.constructed_resume_spine_retains_the_actual_map_completion.
Print Assumptions NativeMapRunSuspension.existing_pair_protocol_certifies_every_pending_answer.
Print Assumptions NativeMapRunSuspension.pair_event_annotation_has_exact_original_operands.
Print Assumptions NativeMapRunSuspension.physical_copy_event_annotation_is_certified.
Print Assumptions NativeMapRunSuspension.sequenced_run_event_annotation_is_certified.
Print Assumptions NativeMapRunSuspension.sequenced_pass_event_annotation_is_certified.
Print Assumptions NativeMapRunSuspension.sequenced_outer_event_annotation_is_certified.
Print Assumptions NativeMapRunSuspension.sequenced_unit_lex_event_annotation_is_certified.
Print Assumptions NativeMapRunSuspension.pair_edges_app.
Print Assumptions NativeMapRunSuspension.pair_edges_suffix.
Print Assumptions NativeMapRunSuspension.own_pair_action_extends_the_certified_path.
Print Assumptions NativeMapRunSuspension.copy_events_preserve_their_own_pair_edges.
Print Assumptions NativeMapRunSuspension.run_events_preserve_their_own_pair_edges.
Print Assumptions NativeMapRunSuspension.pass_events_preserve_their_own_pair_edges.
Print Assumptions NativeMapRunSuspension.outer_events_preserve_their_own_pair_edges.
Print Assumptions NativeMapRunSuspension.lex_events_preserve_their_own_pair_edges.
Print Assumptions NativeMapRunSuspension.complete_spine_has_one_terminal_after_its_certified_body.
Print Assumptions NativeMapRunSuspension.every_retained_answer_cut_has_its_exact_source_pending_state.
Print Assumptions NativeMapRunSuspension.every_retained_pair_cut_exposes_its_own_physical_accept_action.
Print Assumptions NativeMapRunSuspension.certified_event_is_quiet_or_a_nonempty_pair_block.
Print Assumptions NativeMapRunSuspension.certified_suffix_exposes_its_next_pair_or_terminal_path.
Print Assumptions NativeMapRunSuspension.two_original_answers_at_the_same_pending_role_are_equal.
Print Assumptions NativeMapRunSuspension.matching_response_advances_within_the_same_native_pair_hole.
Print Assumptions NativeMapRunSuspension.matching_last_response_advances_into_the_saved_physical_suffix.
Print Assumptions NativeMapRunSuspension.native_completion_constructs_a_certified_initial_resume_frontier.
