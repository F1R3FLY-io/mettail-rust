(** Original-write transport and the fixed prefixes of native stable sort.

    Pinned Rust: 2e2b193f8ada105f27608b7be81c293e0d7292cb;
    core/src/slice/sort/shared/smallsort.rs:606-674 and :677-842;
    SHA256 85c75bc93745ff1d4a6d33939d48408c2f7304aa8ffd952b73199ec1f8a175e1.

    A chronological write list is NOT the destination buffer order. The first
    section reuses Stdlib.Permutation_map_inv to transport the already-proved
    destination permutation to the SAME original write pairs. The output at
    each destination is exactly its source occurrence; existence and uniqueness
    are proved, not postulated. This is a ghost description of original writes,
    not a new runtime scatter, sorter, allocation or admission policy.

    sort4 selects original pointers using five actual Boolean replies, then
    copies min/lo/hi/max into destinations 0/1/2/3. It preserves all four
    occurrences even for inconsistent replies. sort8 calls it twice, at source
    and scratch offsets 0 and 4, then calls the EXISTING bidirectional merge on
    that exact destination-ordered scratch roster. Rejection stays rejection;
    no valid returned roster is published after OrdViolation.

    Records are whole original reference pairs (with occurrence identity), not
    reconstructed keys and values. Freeze concerns the copied slots, not an
    assertion that referent internals cannot mutate. Comparator bodies and
    exceptions, raw-pointer/nonaliasing linkage, allocator internals, checked
    numeric receipt projection and panic unwinding remain outside this model.
    Counts measure the named source groups and original calls/copies, not CPU
    instructions. This file does not model general-small-sort half filling,
    its CopyOnDrop wrapper, or driftsort; it imposes no public Map width cap. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia Sorting.Permutation.
From RhoBridge Require Import NativeStableBidirectionalMerge.
Import ListNotations.
Module BM := NativeStableBidirectionalMerge.NativeStableBidirectionalMerge.

Module NativeStableSmallSortPrefixes.

(** Each pair is (destination index, original source index). *)
Fixpoint writes trace := match trace with
  | [] => []
  | BM.Copy source destination :: rest => (destination,source) :: writes rest
  | _ :: rest => writes rest end.
Lemma write_destinations : forall trace,
  map (@fst nat nat) (writes trace) = BM.destinations trace.
Proof. induction trace as [|e rest IH]; [reflexivity|].
  destruct e; cbn; now rewrite IH. Qed.
Lemma write_sources : forall trace,
  map (@snd nat nat) (writes trace) = BM.copied trace.
Proof. induction trace as [|e rest IH]; [reflexivity|].
  destruct e; cbn; now rewrite IH. Qed.
Lemma write_is_original_copy : forall trace destination source,
  In (destination,source) (writes trace) <-> In (BM.Copy source destination) trace.
Proof.
  induction trace as [|e rest IH]; intros destination source; [reflexivity|].
  destruct e; cbn; rewrite IH; split; intros H;
    try (destruct H as [H|H]; [discriminate|assumption]);
    try (right; exact H).
  - destruct H as [H|H]; [inversion H; subst; now left|now right].
  - destruct H as [H|H]; [inversion H; subst; now left|now right].
Qed.

Definition DestinationOrder size trace output := exists ordered,
  Permutation (writes trace) ordered /\
  map (@fst nat nat) ordered = seq 0 size /\
  map (@snd nat nat) ordered = output.

Theorem destination_order_exists_from_native_writes : forall size trace outcome,
  BM.Run size trace outcome -> exists output, DestinationOrder size trace output.
Proof.
  intros size trace outcome RUN.
  pose proof (BM.run_writes_each_destination_once _ _ _ RUN) as D.
  rewrite <- write_destinations in D.
  destruct (@Permutation_map_inv (nat*nat) nat (@fst nat nat)
    (seq 0 size) (writes trace) (Permutation_sym D)) as [ordered [KEYS P]].
  exists (map (@snd nat nat) ordered), ordered. repeat split; auto.
Qed.
Theorem destination_order_has_original_sources : forall size trace output,
  DestinationOrder size trace output -> Permutation (BM.copied trace) output.
Proof. intros size trace output [ordered [P [_ OUT]]].
  rewrite <- write_sources, <- OUT. now apply Permutation_map. Qed.
Theorem destination_order_has_exact_extent : forall size trace output,
  DestinationOrder size trace output -> length output = size.
Proof. intros size trace output [ordered [_ [KEYS OUT]]].
  rewrite <- OUT, length_map. apply (f_equal (@length nat)) in KEYS.
  rewrite length_map, length_seq in KEYS. exact KEYS. Qed.

(** Matching a chronological Copy at destination d determines output[d]. *)
Theorem destination_order_matches_each_original_write : forall size trace output source destination,
  DestinationOrder size trace output -> In (BM.Copy source destination) trace ->
  nth_error output destination = Some source.
Proof.
  intros size trace output source destination [ordered [P [KEYS OUT]]] COPY.
  apply <- write_is_original_copy in COPY.
  pose proof (Permutation_in (destination,source) P COPY) as IN.
  apply In_nth_error in IN. destruct IN as [index AT].
  assert (KEY : nth_error (seq 0 size) index = Some destination).
  { rewrite <- KEYS, nth_error_map, AT. reflexivity. }
  rewrite nth_error_seq in KEY. destruct (index <? size); cbn in KEY; [|discriminate].
  inversion KEY; subst destination. rewrite <- OUT, nth_error_map, AT. reflexivity.
Qed.
Theorem destination_output_cannot_invent_a_write : forall size trace output source destination,
  DestinationOrder size trace output -> nth_error output destination = Some source ->
  In (BM.Copy source destination) trace.
Proof.
  intros size trace output source destination [ordered [P [KEYS OUT]]] AT.
  rewrite <- OUT, nth_error_map in AT.
  destruct (nth_error ordered destination) as [[key value]|] eqn:PAIR;
    cbn in AT; [|discriminate]. inversion AT; subst value.
  assert (KEY : nth_error (seq 0 size) destination = Some key).
  { rewrite <- KEYS, nth_error_map, PAIR. reflexivity. }
  rewrite nth_error_seq in KEY. destruct (destination <? size); cbn in KEY; [|discriminate].
  inversion KEY; subst key. apply write_is_original_copy.
  eapply Permutation_in; [apply Permutation_sym; exact P|].
  now apply nth_error_In in PAIR.
Qed.
Theorem destination_order_is_unique : forall size trace first second,
  DestinationOrder size trace first -> DestinationOrder size trace second -> first = second.
Proof.
  intros size trace first second A B. apply nth_error_ext. intro index.
  destruct (nth_error first index) as [value|] eqn:F.
  - symmetry. eapply destination_order_matches_each_original_write; [exact B|].
    exact (destination_output_cannot_invent_a_write size trace first value index A F).
  - destruct (nth_error second index) as [value|] eqn:S; [|reflexivity].
    assert (COPY : In (BM.Copy value index) trace).
    { exact (destination_output_cannot_invent_a_write size trace second value index B S). }
    pose proof (destination_order_matches_each_original_write _ _ _ _ _ A COPY).
    congruence.
Qed.

Section Records.
Context {Entry : Type}.
Definition read_records (source : list Entry) fallback indices :=
  map (fun index => nth index source fallback) indices.
Theorem accepted_destination_preserves_complete_records : forall source fallback trace indices,
  BM.Run (length source) trace BM.Accepted ->
  DestinationOrder (length source) trace indices ->
  Permutation source (read_records source fallback indices).
Proof.
  intros source fallback trace indices RUN ORDER.
  pose proof (BM.successful_run_preserves_whole_original_records Entry source fallback trace RUN) as P.
  eapply Permutation_trans; [apply Permutation_sym; exact P|].
  unfold read_records. apply Permutation_map.
  now apply destination_order_has_original_sources with (size:=length source).
Qed.
Theorem destination_record_is_the_actual_copy : forall size source fallback trace indices from to,
  DestinationOrder size trace indices -> In (BM.Copy from to) trace ->
  nth_error (read_records source fallback indices) to = Some (nth from source fallback).
Proof. intros. unfold read_records. rewrite nth_error_map.
  erewrite destination_order_matches_each_original_write by eassumption. reflexivity. Qed.
End Records.

Inductive FourGroup := FourEntry | PairPointers | ExtremePointers | MiddlePointers | FourReturn.
Inductive FourEvent := FourControl (group : FourGroup) | FourNative (event : BM.Event).
Definition four_weight counter event := match event with
  | FourControl _ => match counter with BM.Controls => 1 | _ => 0 end
  | FourNative event => BM.weight counter event end.
Definition four_count counter trace :=
  fold_right (fun event total => four_weight counter event + total) 0 trace.
Fixpoint four_native trace := match trace with
  | [] => [] | FourControl _ :: rest => four_native rest
  | FourNative event :: rest => event :: four_native rest end.

(** The local names and conditional pointer choices match source lines
    621-648. No interpretation of a Boolean as a lawful ordering is required. *)
Definition four_script (c1 c2 c3 c4 c5 : bool) :=
  let a := if c1 then 1 else 0 in
  let b := if c1 then 0 else 1 in
  let c := if c2 then 3 else 2 in
  let d := if c2 then 2 else 3 in
  let minimum := if c3 then c else a in
  let maximum := if c4 then b else d in
  let unknown_left := if c3 then a else if c4 then c else b in
  let unknown_right := if c4 then d else if c3 then b else c in
  let low := if c5 then unknown_right else unknown_left in
  let high := if c5 then unknown_left else unknown_right in
  ([FourControl FourEntry;
    FourNative (BM.Compare 1 0 c1); FourNative (BM.Compare 3 2 c2);
    FourControl PairPointers;
    FourNative (BM.Compare c a c3); FourNative (BM.Compare d b c4);
    FourControl ExtremePointers;
    FourNative (BM.Compare unknown_right unknown_left c5); FourControl MiddlePointers;
    FourNative (BM.Copy minimum 0); FourNative (BM.Copy low 1);
    FourNative (BM.Copy high 2); FourNative (BM.Copy maximum 3); FourControl FourReturn],
   [minimum;low;high;maximum]).

Lemma four_script_exact_counts : forall c1 c2 c3 c4 c5,
  let trace := fst (four_script c1 c2 c3 c4 c5) in
  four_count BM.Comparisons trace = 5 /\ four_count BM.Copies trace = 4 /\
  four_count BM.Controls trace = 5.
Proof. intros [] [] [] [] []; cbn [four_script fst four_count four_weight BM.weight];
  repeat split; reflexivity. Qed.
Lemma four_script_exact_writes : forall c1 c2 c3 c4 c5,
  let script := four_script c1 c2 c3 c4 c5 in
  BM.copied (four_native (fst script)) = snd script /\
  BM.destinations (four_native (fst script)) = seq 0 4.
Proof. intros [] [] [] [] []; reflexivity || (split; reflexivity). Qed.
Lemma four_script_accesses_original_slots : forall c1 c2 c3 c4 c5,
  Forall (BM.original_access 4) (four_native (fst (four_script c1 c2 c3 c4 c5))).
Proof. intros [] [] [] [] []; cbn [four_script fst four_native];
  repeat (apply Forall_cons; [cbn [BM.original_access]; repeat split; lia|]);
  apply Forall_nil. Qed.
Lemma four_script_preserves_each_occurrence : forall c1 c2 c3 c4 c5,
  Permutation (snd (four_script c1 c2 c3 c4 c5)) (seq 0 4).
Proof.
  intros [] [] [] [] []; cbn [four_script snd seq].
  all: (apply NoDup_Permutation;
    [repeat constructor; cbn; intuition discriminate
    |repeat constructor; cbn; intuition discriminate
    |intro index; cbn; tauto]).
Qed.
Lemma four_script_is_destination_ordered : forall c1 c2 c3 c4 c5,
  let script := four_script c1 c2 c3 c4 c5 in
  DestinationOrder 4 (four_native (fst script)) (snd script).
Proof.
  intros. exists (writes (four_native (fst (four_script c1 c2 c3 c4 c5)))).
  split; [apply Permutation_refl|]. rewrite write_destinations, write_sources.
  pose proof (four_script_exact_writes c1 c2 c3 c4 c5) as [S D]. split; assumption.
Qed.

Section FixedRecords.
Context {Entry : Type}.
Inductive FourRun : list Entry -> list FourEvent -> list Entry -> Prop :=
| FourFinished : forall a b c d c1 c2 c3 c4 c5,
    FourRun [a;b;c;d] (fst (four_script c1 c2 c3 c4 c5))
      (read_records [a;b;c;d] a (snd (four_script c1 c2 c3 c4 c5))).
Theorem four_run_has_exact_source_cost : forall source trace output,
  FourRun source trace output -> length source = 4 /\
  four_count BM.Comparisons trace = 5 /\ four_count BM.Copies trace = 4 /\
  four_count BM.Controls trace = 5.
Proof. intros source trace output RUN. destruct RUN. split; [reflexivity|].
  apply four_script_exact_counts. Qed.
Theorem four_run_preserves_whole_records : forall source trace output,
  FourRun source trace output -> Permutation source output.
Proof.
  intros source trace output RUN. destruct RUN. unfold read_records.
  pose proof (@Permutation_map nat Entry (fun index => nth index [a;b;c;d] a)
    _ _ (four_script_preserves_each_occurrence c1 c2 c3 c4 c5)) as P.
  change (Permutation
    (map (fun index => nth index [a;b;c;d] a) (snd (four_script c1 c2 c3 c4 c5)))
    (map (fun index => nth index [a;b;c;d] a) (seq 0 (length [a;b;c;d])))) in P.
  rewrite BM.map_nth_original in P. now apply Permutation_sym.
Qed.
Theorem four_run_retains_original_callback_slots : forall source trace output,
  FourRun source trace output -> Forall (BM.original_access (length source)) (four_native trace).
Proof. intros source trace output RUN. destruct RUN. apply four_script_accesses_original_slots. Qed.
Theorem four_callbacks_borrow_complete_original_records :
  forall source trace output rhs lhs reply,
  FourRun source trace output -> In (BM.Compare rhs lhs reply) (four_native trace) ->
  exists right_record left_record,
    nth_error source rhs = Some right_record /\ nth_error source lhs = Some left_record.
Proof.
  intros source trace output rhs lhs reply RUN IN.
  pose proof (four_run_retains_original_callback_slots _ _ _ RUN) as ACCESS.
  rewrite Forall_forall in ACCESS. specialize (ACCESS _ IN).
  cbn [BM.original_access] in ACCESS. destruct ACCESS as [R L].
  destruct (nth_error source rhs) as [rv|] eqn:RN;
    [|apply nth_error_None in RN; lia].
  destruct (nth_error source lhs) as [lv|] eqn:LN;
    [|apply nth_error_None in LN; lia].
  exists rv,lv. auto.
Qed.

Inductive EightGroup := EightEntry | EightReturn.
Inductive EightEvent := EightControl (group : EightGroup)
  | FourBlock (original_base scratch_base : nat) (trace : list FourEvent)
  | MergeBlock (trace : list BM.Event).
Definition eight_weight counter event := match event with
  | EightControl _ => match counter with BM.Controls => 1 | _ => 0 end
  | FourBlock _ _ trace => four_count counter trace
  | MergeBlock trace => BM.count counter trace end.
Definition eight_count counter trace :=
  fold_right (fun event total => eight_weight counter event + total) 0 trace.

Inductive EightRun : list Entry -> list EightEvent -> BM.Outcome -> option (list Entry) -> Prop :=
| EightAccepted : forall left right ltrace rtrace lout rout merge indices fallback,
    FourRun left ltrace lout -> FourRun right rtrace rout ->
    BM.Run 8 merge BM.Accepted -> DestinationOrder 8 merge indices ->
    EightRun (left++right)
      [EightControl EightEntry; FourBlock 0 0 ltrace; FourBlock 4 4 rtrace;
       MergeBlock merge; EightControl EightReturn] BM.Accepted
      (Some (read_records (lout++rout) fallback indices))
| EightRejected : forall left right ltrace rtrace lout rout merge,
    FourRun left ltrace lout -> FourRun right rtrace rout ->
    BM.Run 8 merge BM.OrdViolation ->
    EightRun (left++right)
      [EightControl EightEntry; FourBlock 0 0 ltrace; FourBlock 4 4 rtrace;
       MergeBlock merge] BM.OrdViolation None.

Theorem eight_run_has_exact_source_cost : forall source trace outcome output,
  EightRun source trace outcome output -> length source = 8 /\
  eight_count BM.Comparisons trace = 18 /\ eight_count BM.Copies trace = 16 /\
  eight_count BM.Controls trace = match outcome with BM.Accepted => 38 | BM.OrdViolation => 37 end.
Proof.
  intros source trace outcome output RUN. destruct RUN;
    pose proof (four_run_has_exact_source_cost _ _ _ H) as LC;
    pose proof (four_run_has_exact_source_cost _ _ _ H0) as RC;
    pose proof (BM.source_run_has_exact_counts _ _ _ H1) as MC;
    destruct LC as [LL [LC [LM LG]]]; destruct RC as [RL [RC [RM RG]]];
    destruct MC as [_ [MC [MM MG]]];
    cbn [eight_count eight_weight fold_right]; rewrite length_app;
    cbn in MC, MM, MG; repeat split; lia.
Qed.
Theorem eight_run_success_preserves_original_records : forall source trace output,
  EightRun source trace BM.Accepted (Some output) -> Permutation source output.
Proof.
  intros source trace output RUN.
  remember BM.Accepted as outcome eqn:ACCEPTED.
  remember (Some output) as result eqn:RESULT.
  destruct RUN as [left right ltrace rtrace lout rout merge indices fallback L R M ORDER
    |left right ltrace rtrace lout rout merge L R M].
  - injection RESULT as OUT. subst output.
    pose proof (four_run_preserves_whole_records _ _ _ L) as LP.
    pose proof (four_run_preserves_whole_records _ _ _ R) as RP.
    pose proof (four_run_has_exact_source_cost _ _ _ L) as [LL _].
    pose proof (four_run_has_exact_source_cost _ _ _ R) as [RL _].
    assert (WIDTH : length (lout++rout) = 8).
    { apply Permutation_length in LP. apply Permutation_length in RP.
      rewrite length_app. lia. }
    eapply Permutation_trans; [apply Permutation_app; eassumption|].
    apply accepted_destination_preserves_complete_records with (trace:=merge);
      now rewrite WIDTH.
  - discriminate ACCEPTED.
Qed.
Theorem eight_rejection_publishes_no_roster : forall source trace output,
  EightRun source trace BM.OrdViolation output -> output = None.
Proof. intros source trace output RUN. inversion RUN. reflexivity. Qed.

(** No destination-order premise is left as an unexplained existence oracle. *)
Theorem accepted_eight_calls_have_a_destination_ordered_result :
  forall left right ltrace rtrace lout rout merge (fallback : Entry),
  FourRun left ltrace lout -> FourRun right rtrace rout -> BM.Run 8 merge BM.Accepted ->
  exists trace output, EightRun (left++right) trace BM.Accepted (Some output).
Proof.
  intros. destruct (destination_order_exists_from_native_writes 8 merge BM.Accepted H1)
    as [indices ORDER]. eexists. eexists. eapply EightAccepted with (fallback:=fallback);
    eassumption.
Qed.

(** Every scratch operand is an actual original complete record. This uses
    the two exact prefix outputs, never an arbitrary sorted/permuted roster. *)
Theorem eight_merge_operands_are_original_records :
  forall left right ltrace rtrace lout rout merge outcome rhs lhs reply,
  FourRun left ltrace lout -> FourRun right rtrace rout -> BM.Run 8 merge outcome ->
  In (BM.Compare rhs lhs reply) merge ->
  exists right_record left_record,
    nth_error (lout++rout) rhs = Some right_record /\
    nth_error (lout++rout) lhs = Some left_record /\
    In right_record (left++right) /\ In left_record (left++right).
Proof.
  intros left right ltrace rtrace lout rout merge outcome rhs lhs reply L R M IN.
  pose proof (four_run_preserves_whole_records _ _ _ L) as LP.
  pose proof (four_run_preserves_whole_records _ _ _ R) as RP.
  pose proof (four_run_has_exact_source_cost _ _ _ L) as [LL _].
  pose proof (four_run_has_exact_source_cost _ _ _ R) as [RL _].
  assert (P : Permutation (left++right) (lout++rout)) by (now apply Permutation_app).
  assert (WIDTH : length (lout++rout) = 8).
  { pose proof (Permutation_length P) as LEN. rewrite !length_app in LEN |- *. lia. }
  rewrite <- WIDTH in M.
  destruct (BM.callbacks_borrow_actual_original_records Entry (lout++rout)
    merge outcome rhs lhs reply M IN) as [rv [lv [RN LN]]].
  exists rv,lv. split; [exact RN|]. split; [exact LN|]. split.
  - eapply Permutation_in; [apply Permutation_sym; exact P|].
    now apply nth_error_In in RN.
  - eapply Permutation_in; [apply Permutation_sym; exact P|].
    now apply nth_error_In in LN.
Qed.
End FixedRecords.

(** Literal eight-element traces witness both outcomes of the composition.
    These are proof fixtures, not a second sorting implementation. *)
Definition witness_state i (reverse_left : bool) :=
  BM.cursors i 0 (if reverse_left then i else 0) (if reverse_left then 0 else i).
Definition witness_merge_trace reverse_left :=
  BM.iteration 8 4 0 (witness_state 0 reverse_left) false reverse_left ++
  BM.iteration 8 4 1 (witness_state 1 reverse_left) false reverse_left ++
  BM.iteration 8 4 2 (witness_state 2 reverse_left) false reverse_left ++
  BM.iteration 8 4 3 (witness_state 3 reverse_left) false reverse_left ++ [BM.Control BM.LoopGuard].
Lemma witness_loop_is_the_original_four_iterations : forall reverse_left,
  BM.Loop 8 4 0 BM.initial (witness_merge_trace reverse_left) (witness_state 4 reverse_left).
Proof.
  intros [].
  - unfold witness_merge_trace. repeat (eapply BM.LoopNext with (u:=false) (d:=true); [lia|]).
    apply BM.LoopEnd.
  - unfold witness_merge_trace. repeat (eapply BM.LoopNext with (u:=false) (d:=false); [lia|]).
    apply BM.LoopEnd.
Qed.
Lemma witness_merge_succeeds : exists trace, BM.Run 8 trace BM.Accepted.
Proof. eexists. apply (BM.RunEven 4 (witness_merge_trace false) (witness_state 4 false));
  [lia|apply witness_loop_is_the_original_four_iterations]. Qed.
Lemma witness_merge_rejects : exists trace, BM.Run 8 trace BM.OrdViolation.
Proof. eexists. apply (BM.RunEven 4 (witness_merge_trace true) (witness_state 4 true));
  [lia|apply witness_loop_is_the_original_four_iterations]. Qed.
Example fixed_eight_can_succeed : exists trace output,
  @EightRun nat [0;1;2;3;4;5;6;7] trace BM.Accepted (Some output).
Proof.
  destruct witness_merge_succeeds as [merge M].
  pose proof (@FourFinished nat 0 1 2 3 false false false false false) as L.
  pose proof (@FourFinished nat 4 5 6 7 false false false false false) as R.
  eapply accepted_eight_calls_have_a_destination_ordered_result
    with (left:=[0;1;2;3]) (right:=[4;5;6;7]) (fallback:=0);
    [exact L|exact R|exact M].
Qed.
Example fixed_eight_can_reject : exists trace,
  @EightRun nat [0;1;2;3;4;5;6;7] trace BM.OrdViolation None.
Proof.
  destruct witness_merge_rejects as [merge M].
  pose proof (@FourFinished nat 0 1 2 3 false false false false false) as L.
  pose proof (@FourFinished nat 4 5 6 7 false false false false false) as R.
  eexists. eapply EightRejected with (left:=[0;1;2;3]) (right:=[4;5;6;7]);
    [exact L|exact R|exact M].
Qed.

Print Assumptions destination_order_exists_from_native_writes.
Print Assumptions destination_order_matches_each_original_write.
Print Assumptions destination_order_is_unique.
Print Assumptions accepted_destination_preserves_complete_records.
Print Assumptions four_run_has_exact_source_cost.
Print Assumptions four_run_preserves_whole_records.
Print Assumptions four_callbacks_borrow_complete_original_records.
Print Assumptions eight_run_has_exact_source_cost.
Print Assumptions eight_run_success_preserves_original_records.
Print Assumptions eight_rejection_publishes_no_roster.
Print Assumptions accepted_eight_calls_have_a_destination_ordered_result.
Print Assumptions eight_merge_operands_are_original_records.
End NativeStableSmallSortPrefixes.
