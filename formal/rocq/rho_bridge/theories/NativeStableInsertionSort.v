(** Native standard-sort insertion branch, not CollectionCmpPda.

    Audited compiler: 2e2b193f8ada105f27608b7be81c293e0d7292cb,
    trusted x86_64/64-bit standard library without optimize_for_size.
    Source relative to lib/rustlib/src/rust/library:
      core/src/slice/sort/stable/mod.rs:29-93
      core/src/slice/sort/shared/smallsort.rs:295-309,536-607.
    SHA256 stable/mod.rs:
      3f2b2d8543a1cb91c9352e041bed49949a31cbd4b1030ec1a82cca1304cb22d3
    SHA256 shared/smallsort.rs:
      85c75bc93745ff1d4a6d33939d48408c2f7304aa8ffd952b73199ec1f8a175e1

    Derivations annotate the original pointer loop's successful source blocks.
    Entry denotes a complete original record, including its source occurrence
    if two values are otherwise indistinguishable. It is not a comparison
    class, a copied AST, a runtime trace allocation or a replacement sorter.
    Every callback answer is allowed: finite source bounds need neither
    sortedness nor comparator consistency. The first comparison borrows tail;
    subsequent comparisons borrow its saved ManuallyDrop value. The right
    operand is always an untouched predecessor from that insertion's input.

    Between comparisons the gap guard owns one saved pivot. Copying a
    predecessor and redirecting the guard moves the logical gap one position
    left. Physical bytes temporarily contain duplicates; only initialized
    ownership outside the gap plus the saved pivot forms an inventory.
    CopyOnDrop performs the final copy on NORMAL return too. Intermediate
    arrays are not assumed to be permutations of the original roster.

    Events separate named source-control groups, comparison invocations,
    tail reads and record copies. Callback bodies, allocator internals and
    machine instructions have no assigned unit cost. On this branch there is
    no BufGuard allocation or 4KiB sort scratch; temporary pivot/guard locals
    are distinct from the separately allocated input roster and callback
    storage. Rust pointer validity, concrete source correspondence, checked
    arithmetic/reservation and actual generated-category callback receipts
    remain separate obligations. This file does not cover driftsort, alternate
    standard-library configurations, panic paths or sorting correctness. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia Sorting.Permutation.
Import ListNotations.

Module NativeStableInsertionSort.

Inductive Origin := TailPointer | SavedPointer.
Inductive Group := TailEntry | InitialSift | ReplyGuard | MakeGapGuard
  | RedirectGap | BeginGuard | DecreaseSift | DropGapGuard | TailReturn
  | OuterGuard | AdvanceTail | StableEntry | ZeroSizeGuard | LengthLoad
  | ShortLengthGuard | SmallLengthGuard | InsertionEntry | OffsetZeroGuard
  | OffsetUpperGuard | PointerSetup | StableReturn.
Inductive Counter := Controls | Comparisons | Shifts | Saves | Fills
  | Decrements | InitialComparisons | OuterTests | TailAdvances.

Section Source.
Context {Entry : Type}.

Record Callback := {
  callback_origin : Origin;
  callback_index : nat;
  callback_left : Entry;
  callback_right : Entry;
  callback_reply : bool
}.
Definition callback origin index lhs rhs reply :=
  {| callback_origin := origin; callback_index := index;
     callback_left := lhs; callback_right := rhs; callback_reply := reply |}.
Inductive Event :=
| Control (group : Group)
| Compare (call : Callback)
| ReadPivot (pivot : Entry)
| Shift (source destination : nat) (entry : Entry)
| Fill (destination : nat) (pivot : Entry).

Definition event_weight counter event := match counter, event with
  | Controls, Control _ | Comparisons, Compare _ | Shifts, Shift _ _ _
  | Saves, ReadPivot _ | Fills, Fill _ _ | Decrements, Control DecreaseSift
  | OuterTests, Control OuterGuard | TailAdvances, Control AdvanceTail => 1
  | InitialComparisons, Compare call =>
      match callback_origin call with TailPointer => 1 | SavedPointer => 0 end
  | _, _ => 0
  end.
Fixpoint count counter trace := match trace with
  | [] => 0
  | event :: rest => event_weight counter event + count counter rest
  end.
Lemma count_app : forall counter left right,
  count counter (left ++ right) = count counter left + count counter right.
Proof. intros counter left. induction left; intros; cbn [count app]; [reflexivity|].
  rewrite IHleft. lia. Qed.

Fixpoint callbacks trace := match trace with
  | [] => []
  | Compare call :: rest => call :: callbacks rest
  | _ :: rest => callbacks rest
  end.
Lemma callbacks_app : forall left right,
  callbacks (left ++ right) = callbacks left ++ callbacks right.
Proof. induction left as [|event rest IH]; intro right; [reflexivity|].
  destruct event; cbn [callbacks app]; now rewrite IH. Qed.

(** This is a logical initialized-slot projection, not a byte-array rewrite.
    None names the one location the guard must fill before normal return. *)
Definition gap_slots (remaining shifted suffix : list Entry) :=
  map (@Some Entry) remaining ++ None :: map (@Some Entry) (shifted ++ suffix).
Definition gap_inventory (pivot : Entry) (remaining shifted suffix : list Entry) :=
  remaining ++ pivot :: shifted ++ suffix.

Lemma gap_projection_has_exact_extent : forall remaining shifted suffix,
  length (gap_slots remaining shifted suffix) =
    length remaining + 1 + length shifted + length suffix.
Proof. intros. unfold gap_slots. rewrite length_app, !length_map. cbn [length].
  rewrite length_map, length_app. lia. Qed.

Lemma moving_predecessor_preserves_pivot_inventory : forall prefix current pivot shifted suffix,
  Permutation (gap_inventory pivot (prefix ++ [current]) shifted suffix)
    (gap_inventory pivot prefix (current :: shifted) suffix).
Proof.
  intros. unfold gap_inventory. rewrite <- app_assoc. cbn [app].
  apply Permutation_app_head. apply perm_swap.
Qed.

(** Entry is just after a successful is_less reply, before that predecessor
    is copied. The source's bare loop has no additional loop guard. *)
Inductive ShiftRun (pivot : Entry) :
    list Entry -> list Entry -> list Entry -> list Event -> list Entry -> Prop :=
| ShiftReachesBegin : forall current shifted suffix,
    ShiftRun pivot [current] shifted suffix
      [Shift 0 1 current; Control RedirectGap; Control BeginGuard;
       Control DropGapGuard; Fill 0 pivot; Control TailReturn]
      (pivot :: current :: shifted ++ suffix)
| ShiftFindsPosition : forall prefix previous current shifted suffix,
    ShiftRun pivot (prefix ++ [previous; current]) shifted suffix
      [Shift (S (length prefix)) (S (S (length prefix))) current;
       Control RedirectGap; Control BeginGuard; Control DecreaseSift;
       Compare (callback SavedPointer (length prefix) pivot previous false);
       Control ReplyGuard; Control DropGapGuard;
       Fill (S (length prefix)) pivot; Control TailReturn]
      ((prefix ++ [previous]) ++ pivot :: current :: shifted ++ suffix)
| ShiftContinues : forall prefix previous current shifted suffix trace output,
    ShiftRun pivot (prefix ++ [previous]) (current :: shifted) suffix trace output ->
    ShiftRun pivot (prefix ++ [previous; current]) shifted suffix
      ([Shift (S (length prefix)) (S (S (length prefix))) current;
        Control RedirectGap; Control BeginGuard; Control DecreaseSift;
        Compare (callback SavedPointer (length prefix) pivot previous true);
        Control ReplyGuard] ++ trace) output.

Theorem every_shift_run_has_derived_counts : forall pivot remaining shifted suffix trace output,
  ShiftRun pivot remaining shifted suffix trace output ->
  count Comparisons trace + 1 <= length remaining /\
  count Shifts trace <= length remaining /\
  count Saves trace = 0 /\ count Fills trace = 1 /\
  count Decrements trace = count Comparisons trace /\
  count InitialComparisons trace = 0 /\ count OuterTests trace = 0 /\
  count TailAdvances trace = 0 /\
  count Controls trace = 2 * count Shifts trace + 2 * count Comparisons trace + 2.
Proof.
  intros pivot remaining shifted suffix trace output RUN. induction RUN;
    rewrite ?length_app in *;
    cbn [count event_weight callback callback_origin length app] in *;
    repeat split; lia.
Qed.

Theorem completed_shift_fills_exact_original_inventory :
  forall pivot remaining shifted suffix trace output,
  ShiftRun pivot remaining shifted suffix trace output ->
  Permutation (gap_inventory pivot remaining shifted suffix) output.
Proof.
  intros pivot remaining shifted suffix trace output RUN. induction RUN.
  - unfold gap_inventory. cbn [app]. apply perm_swap.
  - replace (prefix ++ [previous; current]) with ((prefix ++ [previous]) ++ [current])
      by (rewrite <- app_assoc; reflexivity).
    apply moving_predecessor_preserves_pivot_inventory.
  - eapply Permutation_trans; [|exact IHRUN].
    replace (prefix ++ [previous; current]) with ((prefix ++ [previous]) ++ [current])
      by (rewrite <- app_assoc; reflexivity).
    apply moving_predecessor_preserves_pivot_inventory.
Qed.

Lemma nth_error_at_prefix : forall (prefix : list Entry) value rest,
  nth_error (prefix ++ value :: rest) (length prefix) = Some value.
Proof. induction prefix; intros; cbn; [reflexivity|apply IHprefix]. Qed.
Lemma nth_error_survives_append : forall (source : list Entry) rest index value,
  nth_error source index = Some value -> nth_error (source ++ rest) index = Some value.
Proof.
  induction source as [|head source IH]; intros rest [|index] value READ;
    cbn in *; try discriminate; [exact READ|]. now apply IH.
Qed.

Theorem shift_callbacks_borrow_the_original_pivot_and_predecessors :
  forall pivot remaining shifted suffix trace output,
  ShiftRun pivot remaining shifted suffix trace output ->
  Forall (fun call => callback_origin call = SavedPointer /\
    callback_left call = pivot /\
    nth_error remaining (callback_index call) = Some (callback_right call) /\
    callback_index call + 1 < length remaining) (callbacks trace).
Proof.
  intros pivot remaining shifted suffix trace output RUN. induction RUN.
  - constructor.
  - cbn [callbacks]. constructor; [|constructor].
    cbn [callback callback_origin callback_left callback_index callback_right].
    repeat split; try reflexivity.
    + apply nth_error_at_prefix.
    + rewrite length_app. cbn [length]. lia.
  - cbn [callbacks app]. constructor.
    + cbn [callback callback_origin callback_left callback_index callback_right].
      repeat split; try reflexivity.
      * apply nth_error_at_prefix.
      * rewrite length_app. cbn [length]. lia.
    + eapply Forall_impl; [|exact IHRUN]. intros call [ORIGIN [LEFT [READ BOUND]]].
      repeat split; try assumption.
      * replace (prefix ++ [previous; current]) with ((prefix ++ [previous]) ++ [current])
          by (rewrite <- app_assoc; reflexivity).
        now apply nth_error_survives_append.
      * rewrite length_app in BOUND |- *. cbn [length] in *. lia.
Qed.

Inductive TailRun : list Entry -> Entry -> list Entry -> list Event -> list Entry -> Prop :=
| TailAlreadyPlaced : forall prefix previous pivot suffix,
    TailRun (prefix ++ [previous]) pivot suffix
      [Control TailEntry; Control InitialSift;
       Compare (callback TailPointer (length prefix) pivot previous false);
       Control ReplyGuard; Control TailReturn]
      ((prefix ++ [previous]) ++ pivot :: suffix)
| TailMoves : forall prefix previous pivot suffix trace output,
    ShiftRun pivot (prefix ++ [previous]) [] suffix trace output ->
    TailRun (prefix ++ [previous]) pivot suffix
      ([Control TailEntry; Control InitialSift;
        Compare (callback TailPointer (length prefix) pivot previous true);
        Control ReplyGuard; ReadPivot pivot; Control MakeGapGuard] ++ trace) output.

Theorem tail_run_counts_are_derived_from_original_prefix :
  forall prefix pivot suffix trace output, TailRun prefix pivot suffix trace output ->
  count Comparisons trace <= length prefix /\ count Shifts trace <= length prefix /\
  count Saves trace <= 1 /\ count Fills trace = count Saves trace /\
  count InitialComparisons trace = 1 /\
  count Decrements trace + 1 = count Comparisons trace /\
  count OuterTests trace = 0 /\ count TailAdvances trace = 0 /\
  count Controls trace = 4 + 2 * count Shifts trace +
    2 * count Decrements trace + 2 * count Saves trace.
Proof.
  intros prefix pivot suffix trace output RUN. destruct RUN.
  - rewrite length_app. cbn [count event_weight callback callback_origin length].
    repeat split; lia.
  - pose proof (every_shift_run_has_derived_counts _ _ _ _ _ _ H) as COUNTS.
    cbn [count event_weight callback callback_origin app]. repeat split; lia.
Qed.

Theorem completed_tail_preserves_whole_original_records :
  forall prefix pivot suffix trace output, TailRun prefix pivot suffix trace output ->
  Permutation (prefix ++ pivot :: suffix) output.
Proof.
  intros prefix pivot suffix trace output RUN. destruct RUN; [reflexivity|].
  exact (completed_shift_fills_exact_original_inventory _ _ _ _ _ _ H).
Qed.

Theorem tail_callbacks_have_exact_original_operands :
  forall prefix pivot suffix trace output, TailRun prefix pivot suffix trace output ->
  Forall (fun call => callback_left call = pivot /\
    nth_error prefix (callback_index call) = Some (callback_right call) /\
    callback_index call < length prefix) (callbacks trace).
Proof.
  intros prefix pivot suffix trace output RUN. destruct RUN.
  - cbn [callbacks]. constructor; [|constructor].
    cbn [callback callback_left callback_index callback_right].
    repeat split; try reflexivity; [apply nth_error_at_prefix|].
    rewrite length_app. cbn [length]. lia.
  - cbn [callbacks app]. constructor.
    + cbn [callback callback_left callback_index callback_right].
      repeat split; try reflexivity; [apply nth_error_at_prefix|].
      rewrite length_app. cbn [length]. lia.
    + pose proof (shift_callbacks_borrow_the_original_pivot_and_predecessors
        _ _ _ _ _ _ H) as CALLS.
      eapply Forall_impl; [|exact CALLS]. intros call [_ [LEFT [READ BOUND]]].
      repeat split; try assumption; lia.
Qed.

Lemma tail_callback_operands_belong_to_original_records :
  forall prefix pivot suffix trace output, TailRun prefix pivot suffix trace output ->
  Forall (fun call => In (callback_left call) (prefix ++ pivot :: suffix) /\
    In (callback_right call) (prefix ++ pivot :: suffix)) (callbacks trace).
Proof.
  intros prefix pivot suffix trace output RUN.
  pose proof (tail_callbacks_have_exact_original_operands _ _ _ _ _ RUN) as CALLS.
  eapply Forall_impl; [|exact CALLS]. intros call [LEFT [READ _]]. split.
  - rewrite LEFT. apply in_or_app. right. now left.
  - apply in_or_app. left. now apply nth_error_In in READ.
Qed.

(** The outer source index advances once after each complete insert_tail.
    The guard includes its final false test. No number of iterations is an
    input to the relation; it follows from the unchanged original extent. *)
Inductive OuterRun : nat -> list Entry -> list Event -> list Entry -> Prop :=
| OuterDone : forall source,
    OuterRun (length source) source [Control OuterGuard] source
| OuterNext : forall index prefix pivot suffix tail_trace middle trace output,
    length prefix = index -> 0 < index ->
    TailRun prefix pivot suffix tail_trace middle ->
    OuterRun (S index) middle trace output ->
    OuterRun index (prefix ++ pivot :: suffix)
      (Control OuterGuard :: tail_trace ++ Control AdvanceTail :: trace) output.

Fixpoint triangular size := match size with
  | 0 => 0 | S previous => previous + triangular previous end.

Lemma triangular_monotone : forall left right,
  left <= right -> triangular left <= triangular right.
Proof. intros left right LE. induction LE; [reflexivity|].
  cbn [triangular]. lia. Qed.

Theorem triangular_is_the_exact_index_sum : forall size,
  2 * triangular size = size * (size - 1).
Proof.
  induction size as [|size IH]; [reflexivity|].
  destruct size as [|size]; cbn [triangular] in *; nia.
Qed.

Theorem outer_run_preserves_original_records : forall index source trace output,
  OuterRun index source trace output -> Permutation source output.
Proof.
  intros index source trace output RUN. induction RUN; [reflexivity|].
  eapply Permutation_trans; [eapply completed_tail_preserves_whole_original_records; eassumption|].
  exact IHRUN.
Qed.

Theorem outer_counts_follow_the_actual_index : forall index source trace output,
  OuterRun index source trace output ->
  count InitialComparisons trace + index = length source /\
  count Comparisons trace + triangular index <= triangular (length source) /\
  count Shifts trace + triangular index <= triangular (length source) /\
  count Saves trace <= count InitialComparisons trace /\
  count Fills trace = count Saves trace /\
  count Decrements trace + count InitialComparisons trace = count Comparisons trace /\
  count OuterTests trace = S (count InitialComparisons trace) /\
  count TailAdvances trace = count InitialComparisons trace /\
  count Controls trace = 6 * count InitialComparisons trace + 1 +
    2 * count Shifts trace + 2 * count Decrements trace + 2 * count Saves trace.
Proof.
  intros index source trace output RUN. induction RUN.
  - cbn [count event_weight]. repeat split; lia.
  - pose proof (tail_run_counts_are_derived_from_original_prefix _ _ _ _ _ H1) as TC.
    pose proof (completed_tail_preserves_whole_original_records _ _ _ _ _ H1) as PERM.
    apply Permutation_length in PERM. rewrite length_app in PERM |- *.
    cbn [length] in PERM |- *. rewrite <- PERM in IHRUN.
    cbn [count event_weight] in *. rewrite !count_app.
    cbn [count event_weight]. cbn [triangular] in IHRUN.
    repeat split; lia.
Qed.

Theorem outer_callback_operands_are_original_records : forall index source trace output,
  OuterRun index source trace output ->
  Forall (fun call => In (callback_left call) source /\ In (callback_right call) source)
    (callbacks trace).
Proof.
  intros index source trace output RUN. induction RUN; [constructor|].
  cbn [callbacks]. rewrite callbacks_app. cbn [callbacks].
  apply Forall_app. split.
  - eapply tail_callback_operands_belong_to_original_records; eassumption.
  - pose proof (completed_tail_preserves_whole_original_records _ _ _ _ _ H1) as PERM.
    eapply Forall_impl; [|exact IHRUN]. intros call [LEFT RIGHT]. split;
      eapply Permutation_in; try (apply Permutation_sym; exact PERM); assumption.
Qed.

Inductive StableSmallBranch : bool -> list Entry -> list Event -> list Entry -> Prop :=
| StableZeroSized : forall source,
    StableSmallBranch true source
      [Control StableEntry; Control ZeroSizeGuard; Control StableReturn] source
| StableShort : forall source, length source < 2 ->
    StableSmallBranch false source
      [Control StableEntry; Control ZeroSizeGuard; Control LengthLoad;
       Control ShortLengthGuard; Control StableReturn] source
| StableInsertion : forall source trace output,
    2 <= length source <= 20 -> OuterRun 1 source trace output ->
    StableSmallBranch false source
      ([Control StableEntry; Control ZeroSizeGuard; Control LengthLoad;
        Control ShortLengthGuard; Control SmallLengthGuard; Control InsertionEntry;
        Control OffsetZeroGuard; Control OffsetUpperGuard; Control PointerSetup]
        ++ trace ++ [Control StableReturn]) output.

Theorem small_branch_keeps_records_and_bounds_native_callbacks :
  forall zst source trace output, StableSmallBranch zst source trace output ->
  Permutation source output /\ count Comparisons trace <= triangular (length source) /\
  count Shifts trace <= triangular (length source) /\
  count Saves trace <= length source - 1 /\ count Fills trace = count Saves trace.
Proof.
  intros zst source trace output RUN. destruct RUN.
  - cbn [count event_weight]. split; [reflexivity|]. repeat split; lia.
  - cbn [count event_weight]. split; [reflexivity|]. repeat split; lia.
  - split; [eapply outer_run_preserves_original_records; eassumption|].
    pose proof (outer_counts_follow_the_actual_index _ _ _ _ H0) as COUNTS.
    rewrite !count_app. cbn [count event_weight triangular] in *.
    repeat split; lia.
Qed.

Theorem small_branch_has_the_source_threshold_envelope :
  forall zst source trace output, StableSmallBranch zst source trace output ->
  count Comparisons trace <= 190 /\ count Shifts trace <= 190 /\
  count Saves trace <= 19 /\ count Fills trace = count Saves trace /\
  count Controls trace <= 885 /\
  count Saves trace + count Shifts trace + count Fills trace <= 228.
Proof.
  intros zst source trace output RUN. destruct RUN.
  - cbn [count event_weight]. repeat split; lia.
  - cbn [count event_weight]. repeat split; lia.
  - pose proof (outer_counts_follow_the_actual_index _ _ _ _ H0) as COUNTS.
    assert (LIMIT : triangular (length source) <= 190).
    { change (triangular (length source) <= triangular 20).
      apply triangular_monotone. lia. }
    rewrite !count_app. cbn [count event_weight triangular] in COUNTS |- *.
    repeat split; lia.
Qed.

Theorem small_branch_callbacks_keep_original_operand_pairs :
  forall zst source trace output, StableSmallBranch zst source trace output ->
  Forall (fun call => In (callback_left call) source /\ In (callback_right call) source)
    (callbacks trace).
Proof.
  intros zst source trace output RUN. destruct RUN; try constructor.
  rewrite !callbacks_app. cbn [callbacks]. rewrite app_nil_r.
  eapply outer_callback_operands_are_original_records; eassumption.
Qed.

End Source.

Print Assumptions every_shift_run_has_derived_counts.
Print Assumptions completed_shift_fills_exact_original_inventory.
Print Assumptions shift_callbacks_borrow_the_original_pivot_and_predecessors.
Print Assumptions tail_run_counts_are_derived_from_original_prefix.
Print Assumptions completed_tail_preserves_whole_original_records.
Print Assumptions tail_callbacks_have_exact_original_operands.
Print Assumptions outer_counts_follow_the_actual_index.
Print Assumptions triangular_is_the_exact_index_sum.
Print Assumptions outer_callback_operands_are_original_records.
Print Assumptions small_branch_keeps_records_and_bounds_native_callbacks.
Print Assumptions small_branch_has_the_source_threshold_envelope.
Print Assumptions small_branch_callbacks_keep_original_operand_pairs.

End NativeStableInsertionSort.
