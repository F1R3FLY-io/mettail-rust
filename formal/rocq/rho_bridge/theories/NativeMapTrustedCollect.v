(** Actual native Map roster collection, not the paid inspection visitor.

    HashMapLit::iter returns IndexMap 2.14.0 Iter. Its iterator_methods!
    macro OVERRIDES collect: self.iter.map(Bucket::refs).collect(). The
    slice iterator and Map adapter preserve TrustedLen. Consequently Vec
    takes SpecFromIterNested's trusted branch and extend_trusted, NOT the
    generic next/extend_desugared branch. Map's default for_each delegates
    to Map::fold and then slice::Iter::fold's index-based do-while loop.

    Pinned compiler: 2e2b193f8ada105f27608b7be81c293e0d7292cb.
    IndexMap src/macros.rs175-181 SHA256:
    5ff0f20fe33364c705da3cb3a7d0bc6c4afd519df7618b1baf1ed97bb7769bf3.
    IndexMap src/map/iter.rs SHA256:
    a2eab456006765faad980525cd3d3aeab95efdb66adb763ceb9efc11a6e6209d.
    core/src/slice/iter/macros.rs254-283 SHA256:
    8db181ab6087b436dcc4c350efc7283ecc4912e34ca20d8bf7460fca5084c26c.
    alloc/src/vec/spec_from_iter_nested.rs trusted branch SHA256:
    327aeaf0a1f6bb3b537f342f161f549759846a16f0863f154d6ac2c9ca766aa5.
    Remaining source: alloc/src/vec/mod.rs extend_trusted and
    alloc/src/vec/set_len_on_drop.rs; core/src/iter/adapters/map.rs fold.

    Pair labels denote the complete original key/value borrows. Fill tracks
    the ORIGINAL unread suffix, source index, and initialized destination
    length. The two latter counters coincide, initially zero: the mapped
    callback writes local_len, increments it, and only then the slice fold
    increments its index and checks the end. Finish is the successful
    post-body branch, not an invented extra next call. Empty input takes
    the fold's initial empty branch and still commits the zero-length guard.

    The trace is a source projection, not another runtime collector. Control
    labels are named bounded source groups, not processor instructions.
    BufferRequest and ReserveRequest retain their exact requested widths;
    allocator/capacity/layout validity and their implementation costs must
    be composed separately. No theorem equates requests with constant-cost
    allocations or claims complete Map Hash admission. Mathematical lengths
    do not prove machine-word representability. All results concern normal
    completed collection; allocation failure and panic unwinding are outside
    this projection. SelectFoldResult denotes evaluation of the return
    accumulator, not completion of the fold call: the moved closure's
    SetLenOnDrop commits its initialized length before that call returns.
    Helper dispatch and debug checks are grouped at their named boundaries;
    event length counts this projection, not every instruction or branch.
    No native Hash, Eq, Ord or Clone callback is introduced. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Module NativeMapTrustedCollect.
Section OriginalPairs.
Context {Key Value : Type}.
Definition Pair := (Key * Value)%type.

Inductive Group := CollectDispatch | MapSlice | TrustedHint | ExtendHint
  | CheckHint | DestinationPointer | LengthGuard | ForEachDispatch | FoldDispatch
  | EmptyGuard | FoldInitialize | MapContinuation | IncrementLength
  | IncrementIndex | EndGuard | SelectFoldResult | CommitLength | ReturnBuffer.
Inductive Event := Control (group : Group)
  | BufferRequest (width : nat) | ReserveRequest (width : nat)
  | ReadOriginal (index : nat) (pair : Pair)
  | ProjectPair (pair : Pair) | WritePair (index : nat) (pair : Pair).

Definition step index pair :=
  [ReadOriginal index pair; ProjectPair pair; Control MapContinuation;
   WritePair index pair; Control IncrementLength;
   Control IncrementIndex; Control EndGuard].

Inductive Fill (width : nat) : nat -> list Pair -> list Event -> list Pair -> Prop :=
| FillFinished : Fill width width [] [] []
| FillNext : forall index pair rest trace result,
    index < width -> Fill width (S index) rest trace result ->
    Fill width index (pair :: rest) (step index pair ++ trace) (pair :: result).

Fixpoint writes trace := match trace with
  | [] => [] | WritePair index entry :: rest => (index,entry) :: writes rest
  | _ :: rest => writes rest end.
Fixpoint reads trace := match trace with
  | [] => [] | ReadOriginal index entry :: rest => (index,entry) :: reads rest
  | _ :: rest => reads rest end.
Fixpoint requests trace := match trace with
  | [] => [] | BufferRequest width :: rest => width :: requests rest
  | _ :: rest => requests rest end.
Fixpoint reserves trace := match trace with
  | [] => [] | ReserveRequest width :: rest => width :: reserves rest
  | _ :: rest => reserves rest end.

Lemma writes_app : forall a b, writes (a ++ b) = writes a ++ writes b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  destruct event; cbn; now rewrite IH. Qed.
Lemma reads_app : forall a b, reads (a ++ b) = reads a ++ reads b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  destruct event; cbn; now rewrite IH. Qed.
Lemma requests_app : forall a b, requests (a ++ b) = requests a ++ requests b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  destruct event; cbn; now rewrite IH. Qed.
Lemma reserves_app : forall a b, reserves (a ++ b) = reserves a ++ reserves b.
Proof. induction a as [|event rest IH]; intro b; [reflexivity|].
  destruct event; cbn; now rewrite IH. Qed.

Theorem fill_keeps_original_suffix_and_exact_indices :
  forall width index source trace result,
  Fill width index source trace result ->
  result = source /\ width = index + length source /\
  writes trace = combine (seq index (length source)) source /\
  reads trace = writes trace /\ length trace = 7 * length source /\
  requests trace = [] /\ reserves trace = [].
Proof.
  intros width index source trace result RUN. induction RUN.
  - cbn. repeat split; lia.
  - destruct IHRUN as [SAME [WIDTH [WRITES [READS [SIZE [ALLOC RESERVE]]]]]].
    rewrite writes_app, reads_app, length_app, requests_app, reserves_app.
    cbn [step writes reads requests reserves app length seq combine].
    rewrite SAME, READS, WRITES, SIZE, ALLOC, RESERVE.
    repeat split; try reflexivity; lia.
Qed.

Lemma fill_exists : forall source index,
  exists trace, Fill (index + length source) index source trace source.
Proof.
  induction source as [|pair rest IH]; intro index.
  - exists []. rewrite Nat.add_0_r. constructor.
  - destruct (IH (S index)) as [trace RUN].
    exists (step index pair ++ trace).
    replace (index + length (pair :: rest)) with (S index + length rest) by (cbn; lia).
    econstructor; [lia|exact RUN].
Qed.

Definition prefix width :=
  [Control CollectDispatch; Control MapSlice; Control TrustedHint;
   BufferRequest width; Control ExtendHint; Control CheckHint;
   ReserveRequest width; Control DestinationPointer; Control LengthGuard;
   Control ForEachDispatch; Control FoldDispatch; Control EmptyGuard].
Definition suffix := [Control SelectFoldResult; Control CommitLength; Control ReturnBuffer].
Inductive Collect : list Pair -> list Event -> list Pair -> Prop :=
| CollectEmpty : Collect [] (prefix 0 ++ suffix) []
| CollectNonempty : forall pair rest trace result,
    Fill (length (pair :: rest)) 0 (pair :: rest) trace result ->
    Collect (pair :: rest)
      (prefix (length (pair :: rest)) ++ Control FoldInitialize :: trace ++ suffix) result.

Theorem every_source_has_its_original_collect : forall source,
  exists trace, Collect source trace source.
Proof.
  intros [|pair rest]; [eexists; constructor|].
  destruct (fill_exists (pair::rest) 0) as [trace RUN].
  eexists. apply CollectNonempty. exact RUN.
Qed.

Theorem collect_keeps_original_pairs_and_writes_each_slot_once :
  forall source trace result, Collect source trace result ->
  result = source /\
  writes trace = combine (seq 0 (length source)) source /\
  reads trace = writes trace /\
  requests trace = [length source] /\ reserves trace = [length source].
Proof.
  intros source trace result RUN. destruct RUN.
  - cbn [prefix suffix writes reads requests reserves app length seq combine].
    repeat split; reflexivity.
  - pose proof (fill_keeps_original_suffix_and_exact_indices _ _ _ _ _ H)
      as [SAME [_ [WRITES [READS [_ [ALLOC RESERVE]]]]]].
    repeat split.
    + exact SAME.
    + change (writes (trace ++ suffix) =
        combine (seq 0 (length (pair :: rest))) (pair :: rest)).
      rewrite writes_app.
      change (writes trace ++ [] = combine (seq 0 (length (pair :: rest))) (pair :: rest)).
      now rewrite app_nil_r.
    + change (reads (trace ++ suffix) = writes (trace ++ suffix)).
      rewrite reads_app, writes_app.
      change (reads trace ++ [] = writes trace ++ []). now rewrite READS.
    + change (length (pair :: rest) :: requests (trace ++ suffix) = [length (pair :: rest)]).
      rewrite requests_app, ALLOC. reflexivity.
    + change (length (pair :: rest) :: reserves (trace ++ suffix) = [length (pair :: rest)]).
      rewrite reserves_app, RESERVE. reflexivity.
Qed.

Theorem collect_source_group_count : forall source trace result,
  Collect source trace result ->
  length trace = 15 + 7 * length source +
    (match source with [] => 0 | _ :: _ => 1 end).
Proof.
  intros source trace result RUN. destruct RUN.
  - reflexivity.
  - pose proof (fill_keeps_original_suffix_and_exact_indices _ _ _ _ _ H)
      as [_ [_ [_ [_ [SIZE _]]]]].
    rewrite !length_app.
    change (12 + S (length (trace ++ suffix)) =
      15 + 7 * length (pair :: rest) + 1).
    rewrite length_app, SIZE.
    change (12 + S (7 * length (pair :: rest) + 3) =
      15 + 7 * length (pair :: rest) + 1).
    lia.
Qed.

(** Reserve follows successful with_capacity(width). Its requested extra
    width fits the currently empty buffer; this law does not prove a
    successful allocation or give the raw allocator a constant work bound. *)
Theorem collect_reserve_fits_the_allocated_capacity : forall source trace result capacity,
  Collect source trace result -> length source <= capacity ->
  Forall (fun width => 0 + width <= capacity) (reserves trace).
Proof.
  intros source trace result capacity RUN CAPACITY.
  pose proof (collect_keeps_original_pairs_and_writes_each_slot_once _ _ _ RUN)
    as [_ [_ [_ [_ RESERVE]]]].
  rewrite RESERVE. constructor; [exact CAPACITY|constructor].
Qed.

End OriginalPairs.

Print Assumptions fill_keeps_original_suffix_and_exact_indices.
Print Assumptions every_source_has_its_original_collect.
Print Assumptions collect_keeps_original_pairs_and_writes_each_slot_once.
Print Assumptions collect_source_group_count.
Print Assumptions collect_reserve_fits_the_allocated_capacity.
End NativeMapTrustedCollect.
