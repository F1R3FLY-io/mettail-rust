(** Cumulative logical control/storage for the pinned native stable sort.

    Compiler 2e2b193f8ada105f27608b7be81c293e0d7292cb, x86_64 default
    standard library, source directory core/src/slice/sort. This file
    annotates the SAME finite width/flag derivations of
    NativeStableSortRequestBound; it is not a sorter, pointer semantics,
    Rust compiler theorem, comparison oracle or allocator/RSS estimate.
    Callback bodies AND the generated callback adapter remain separate.
    All results concern ordinary normal completion. Existing comparison
    results are unconstrained; no total-order axiom is introduced.

    A work group is a bounded scalar source block or one flat record
    transfer. A record is a cumulative logical local/transfer position,
    NOT a maximum simultaneously live slot. Copies of borrowed pairs have
    no owned bytes. The local profiles below deliberately overpay the
    following reviewed source-group inventories. An occurrence charged in
    a child helper is not also charged in its parent's scalar block.

    * shared/mod.rs20-59, find_existing_run: eight entry/exit groups cover
      length, short input, initial direction and selected loop. Each of at
      most w inspected positions has loop guard, directed operand route,
      result branch and increment (four groups). A selected reverse adds
      at most w/2 swaps; scalar swap routing plus three flat transfers is
      covered by four groups per original position and two record
      positions per original position. Two fixed local positions remain.

    * stable/merge.rs8-66,78-149: 32 fixed groups cover entry guards,
      endpoint/shorter-side setup, gap construction, branch dispatch and
      normal gap cleanup. Each selected output has at most ten groups
      (guard/operand route/result selection/copy/cursor updates), at most
      w iterations. Initial saved shorter width plus remaining-gap copy
      plus selected outputs is at most 2w transfers, NOT just the
      comparator count. Six additional groups per width cover those
      transfers and both directional terminal checks. Four fixed local
      positions and 2w transfer positions suffice.

    * shared/smallsort.rs220-302,536-603,606-685,754-end: threshold32;
      empty/one-element calls still pay fixed entry/exit. sort4 has five
      routed comparisons, four pair-pointer bindings, six min/max/unknown
      selections (including the two nested selections), two final lo/hi
      selections and four transfers:21 groups, plus entry/exit, within24.
      sort8 invokes two sort4 and one eight-element bidirectional merge:
      48+26 control groups+8 transfers+three wrapper groups=85, within96
      work and16 transfers. At most two
      fixed prefixes occur, only at widths >=8 (sort4) or >=16 (sort8).
      Thus 64+16w covers fixed prefixes, two-half setup, per-tail input
      copy, final merge controls and terminal guards. Existing insertion
      counts are 6i+1+2s+2d+2p controls with i<=w, s,d<=triangular(w),
      p<=i, and p+s+p transfers; the two half tails have disjoint index
      sums. The generous 8w^2 term covers these controls AND transfers.
      Final bidirectional output has w transfers; fixed prefixes have at
      most 2w. Hence 8+4w+w^2 cumulative local/transfer positions suffice.
      The stable path uses small_sort_general_with_scratch, not the
      unrelated allocating small_sort_general wrapper. No extra scratch
      is allocated at a small leaf.

    * stable/quicksort.rs15-89,99-244 and shared/pivot.rs15-116:
      one round has choose_pivot, ancestor test and at most TWO partition
      calls; equal partition reverses operands but still decrements depth.
      Each partition scans exactly w records including the pivot's
      comparator-free step, then copies exactly w records back (one
      contiguous prefix and a reverse suffix). Routing, counters, terminal
      probes and two-part scan control fit 16w+16 groups per partition.
      Median nodes contribute at most eight non-body groups each. The
      existing median potential assigns three callbacks per node and
      bounds the pivot potential by w; therefore their cumulative fixed
      local work is <=8w, with <=w local positions. Pivot wrapper/copy,
      ancestor/partition selection, child slicing and entry/exit have at
      most48 fixed groups (within24 in the quick round plus12 in pivot
      dispatch, with12 spare). Under the actual w>32 guard, these fit
      the remaining24w+32 allowance. Thus the round profile64w+64 includes
      both partition profiles AND median groups. Two partitions transfer4w records in all;
      pivot/median/partition locals fit another4w+8. Child calls are paid
      separately, including empty children. The actual round guard w>32
      is essential for their fixed costs; callback-only annotations omit it.

    * stable/drift.rs20-120,147-185,191-280: the shell's192 fixed work
      includes reservation of its two 66-entry local arrays and at most
      60 initialization, scale/threshold, dummy-run and terminal groups.
      Each positive run causes at most one create/scan/depth/stack-push
      route; each earlier run is popped at most once. These bounded
      scalar groups fit32 per original width. Cumulative records separately
      pay132 array slots, six fixed dummy/frame positions, up to five
      positions per real run (next_run, depth, two array writes, prev_run
      transfer), and three per merge (left read, returned run, prev_run
      transfer). Thus138+8n pays BOTH capacity and later transfers; no
      array write is treated as free reuse of its allocation slot. Scan,
      physical-merge and quicksort helper bodies are separate. The same
      shell is paid AGAIN for each eager fallback invocation, not merely
      once at peak nesting. Existing source interval/flag association
      bounds scan/merge counts by width and excludes re-sorting sorted
      intervals. Positive source chunks/runs are retained explicitly here.

    These local loop/group associations are an explicit reviewed pinned
    library dependency. The kernel proves their additive, guarded width
    composition; it does not infer them from a constant table. Exact
    branch/pointer/library refinement is a separate obligation. Top-level
    roster and driftsort_main scratch selection/allocation/cleanup are
    separate: <=20 needs no scratch, >20 uses the fixed 4096-byte stack
    buffer and conditionally the source alloc_len heap buffer. Neither
    physical allocator internals nor panic unwinding is included.

    No sought whole-sort cost is a premise. Source positive progress and
    actual depth guards exclude arbitrary zero-cost nodes that the earlier
    comparator-only abstraction safely permitted. Mathematical arithmetic
    still requires checked machine-word projections and prepayment before
    native execution. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import NativeStableSortRequestBound.
Import ListNotations.

Module NativeStableSortWorkBound.
Module C := NativeStableSortRequestBound.NativeStableSortRequestBound.

Record Charge := charge { work : nat; records : nat }.
Definition add a b := charge (work a+work b) (records a+records b).
Definition zero := charge 0 0.
Definition scan n := charge (8+8*n) (2+2*n).
Definition merge n := charge (32+16*n) (4+2*n).
Definition small n := charge (64+16*n+8*n*n) (8+4*n+n*n).
Definition round n := charge (64+64*n) (8+8*n).
Definition shell n := charge (192+32*n) (138+8*n).
Definition sum (profile : nat -> Charge) (widths : list nat) :=
  fold_right (fun width rest => add (profile width) rest) zero widths.

Lemma local_quick_round_source_groups_fit : forall n,
  32<n -> 2*(16*n+16)+8*n+48<=work(round n).
Proof. intros; cbn [round work]; lia. Qed.

Lemma sum_linear : forall a b ra rb widths,
  work (sum (fun n => charge (a+b*n) (ra+rb*n)) widths)=
    a*length widths+b*C.total widths /\
  records (sum (fun n => charge (a+b*n) (ra+rb*n)) widths)=
    ra*length widths+rb*C.total widths.
Proof.
  intros a b ra rb widths; induction widths as [|n rest [W R]].
  - cbn; lia.
  - change (a+b*n+work (sum (fun n=>charge (a+b*n) (ra+rb*n)) rest)=
      a*S(length rest)+b*(n+C.total rest) /\
      ra+rb*n+records (sum (fun n=>charge (a+b*n) (ra+rb*n)) rest)=
      ra*S(length rest)+rb*(n+C.total rest)).
    rewrite W,R; split; nia.
Qed.

Lemma sum_small : forall widths,
  work (sum small widths)=64*length widths+16*C.total widths+8*C.squares widths /\
  records (sum small widths)=8*length widths+4*C.total widths+C.squares widths.
Proof.
  induction widths as [|n rest [W R]]; [cbn; lia|].
  change (64+16*n+8*n*n+work(sum small rest)=
    64*S(length rest)+16*(n+C.total rest)+8*(n*n+C.squares rest) /\
    8+4*n+n*n+records(sum small rest)=
    8*S(length rest)+4*(n+C.total rest)+(n*n+C.squares rest)).
  rewrite W,R; split; nia.
Qed.

Lemma positive_widths_pay_for_occurrences : forall widths,
  Forall (fun n=>0<n) widths -> length widths<=C.total widths.
Proof. intros widths H; induction H; cbn; lia. Qed.

Definition eager_charge n scans merges chunks :=
  add (shell n) (add (sum scan scans) (add (sum merge merges) (sum small chunks))).

(** The original EagerCalls witness and its exact scan/merge/chunk lists
    remain indices. Only source-positive chunks are restored. *)
Inductive EagerWork : forall n c, C.Eager n c -> Charge -> Prop :=
| EagerSource : forall n scans merges chunks
    (SC : length scans<=n) (SW : Forall (fun w=>w<=n) scans)
    (MC : length merges<=n) (MW : Forall (fun w=>w<=n) merges)
    (CT : C.total chunks<=n) (CW : Forall (fun w=>w<=32) chunks),
    Forall (fun w=>0<w) chunks ->
    EagerWork n _ (C.EagerCalls n scans merges chunks SC SW MC MW CT CW)
      (eager_charge n scans merges chunks).

Theorem eager_work_and_cumulative_records : forall n c (SOURCE:C.Eager n c) fee,
  EagerWork n c SOURCE fee ->
  records fee<=work fee /\ work fee<=32*n*n+512*n+256.
Proof.
  intros n c SOURCE fee COVER; destruct COVER.
  pose proof (C.bounded_widths _ _ SW) as SCANS.
  pose proof (C.bounded_widths _ _ MW) as MERGES.
  pose proof (C.small_widths _ CW) as SMALL.
  pose proof (positive_widths_pay_for_occurrences _ H) as POSITIVE.
  destruct (sum_linear 8 8 2 2 scans) as [SCANW SCANR].
  destruct (sum_linear 32 16 4 2 merges) as [MERGEW MERGER].
  destruct (sum_small chunks) as [SMALLW SMALLR].
  unfold eager_charge,add; cbn [work records shell].
  change (records (sum scan scans)=2*length scans+2*C.total scans) in SCANR.
  change (work (sum scan scans)=8*length scans+8*C.total scans) in SCANW.
  change (records (sum merge merges)=4*length merges+2*C.total merges) in MERGER.
  change (work (sum merge merges)=32*length merges+16*C.total merges) in MERGEW.
  rewrite SCANW,SCANR,MERGEW,MERGER,SMALLW,SMALLR. split; nia.
Qed.

(** Empty small calls retain their fixed cost. A round is reachable only
    above the actual Freeze threshold32. Its two original disjoint child
    widths and decreased depth are inherited from the SAME QuickRound. *)
Inductive QuickWork : forall n d c, C.Quick n d c -> Charge -> Prop :=
| QuickSmallSource : forall n d (WIDTH:n<=32),
    QuickWork n d _ (C.QuickSmall n d WIDTH) (small n)
| QuickEagerSource : forall n c (SOURCE:C.Eager n c) fee,
    EagerWork n c SOURCE fee ->
    QuickWork n 0 c (C.QuickFallback n c SOURCE) (add (charge 4 1) fee)
| QuickRoundSource : forall n d left right lc rc
    (SPLIT:left+right<=n) (LEFT:C.Quick left d lc) (RIGHT:C.Quick right d rc)
    left_fee right_fee,
    32<n -> QuickWork left d lc LEFT left_fee ->
    QuickWork right d rc RIGHT right_fee ->
    QuickWork n (S d) _ (C.QuickRound n d left right lc rc SPLIT LEFT RIGHT)
      (add (round n) (add left_fee right_fee)).

Theorem quick_work_tracks_decreasing_depth : forall n d c (SOURCE:C.Quick n d c) fee,
  QuickWork n d c SOURCE fee ->
  records fee<=work fee /\
  work fee<=128*d*n+32*n*n+512*n+260.
Proof.
  intros n d c SOURCE fee COVER; induction COVER.
  - cbn [small work records]; split; nia.
  - destruct (eager_work_and_cumulative_records _ _ _ _ H) as [R W].
    cbn [add work records]. split; nia.
  - destruct IHCOVER1 as [LR LW], IHCOVER2 as [RR RW].
    cbn [add round work records]. split; nia.
Qed.

Corollary quick_work_with_original_depth_limit : forall n d c
    (SOURCE:C.Quick n d c) fee,
  d<=2*n -> QuickWork n d c SOURCE fee ->
  records fee<=work fee /\ work fee<=288*n*n+512*n+260.
Proof.
  intros n d c SOURCE fee DEPTH COVER.
  destruct (quick_work_tracks_decreasing_depth _ _ _ _ _ COVER) as [R W].
  split; [exact R|nia].
Qed.

(** Positive real runs, excluding the initial/final dummy whose scalar
    source groups already belong to shell. No sorted run is sorted again. *)
Inductive PositiveRun : forall n sorted widths, C.Run n sorted widths -> Prop :=
| PositiveSorted : forall n, 0<n -> PositiveRun n true [] (C.SortedRun n)
| PositiveUnsorted : forall n, 0<n -> PositiveRun n false [] (C.UnsortedRun n)
| PositiveLazy : forall l r ls rs (LEFT:C.Run l false ls) (RIGHT:C.Run r false rs),
    PositiveRun l false ls LEFT -> PositiveRun r false rs RIGHT ->
    PositiveRun (l+r) false (ls++rs) (C.LazyJoin l r ls rs LEFT RIGHT)
| PositivePhysical : forall l r lf rf ls rs
    (LEFT:C.Run l lf ls) (RIGHT:C.Run r rf rs),
    PositiveRun l lf ls LEFT -> PositiveRun r rf rs RIGHT ->
    PositiveRun (l+r) true (ls++rs++C.newly_sorted l lf++C.newly_sorted r rf)
      (C.PhysicalJoin l r lf rf ls rs LEFT RIGHT).

Lemma newly_sorted_positive : forall n sorted,
  0<n -> Forall (fun w=>0<w) (C.newly_sorted n sorted).
Proof. intros n [] H; cbn; repeat constructor; assumption. Qed.

Theorem source_runs_have_positive_sort_inputs : forall n sorted widths
    (SOURCE:C.Run n sorted widths),
  PositiveRun n sorted widths SOURCE ->
  0<n /\ Forall (fun w=>0<w) widths.
Proof.
  intros n sorted widths SOURCE COVER; induction COVER.
  - split; [assumption|constructor].
  - split; [assumption|constructor].
  - destruct IHCOVER1 as [LP LS],IHCOVER2 as [RP RS].
    split; [lia|now apply Forall_app].
  - destruct IHCOVER1 as [LP LS],IHCOVER2 as [RP RS].
    split; [lia|]. rewrite !Forall_app; repeat split; try assumption;
      now apply newly_sorted_positive.
Qed.

Inductive QuickCallsWork : forall widths c, C.QuickCalls widths c -> Charge -> Prop :=
| NoQuickCalls : QuickCallsWork [] 0 C.QuickCallsNil zero
| MoreQuickCalls : forall n rest d c tail (DEPTH:d<=2*n)
    (SOURCE:C.Quick n d c) (REST:C.QuickCalls rest tail) fee tail_fee,
    QuickWork n d c SOURCE fee -> QuickCallsWork rest tail REST tail_fee ->
    QuickCallsWork (n::rest) (c+tail)
      (C.QuickCallsCons n rest d c tail DEPTH SOURCE REST) (add fee tail_fee).

Theorem quick_calls_have_an_occurrence_sensitive_sum : forall widths c
    (SOURCE:C.QuickCalls widths c) fee,
  QuickCallsWork widths c SOURCE fee ->
  records fee<=work fee /\
  work fee<=288*C.squares widths+512*C.total widths+260*length widths.
Proof.
  intros widths c SOURCE fee COVER; induction COVER.
  - cbn [zero work records C.squares C.total length]; split; lia.
  - destruct IHCOVER as [TR TW].
    destruct (quick_work_with_original_depth_limit _ _ _ _ _ DEPTH H) as [R W].
    cbn [add work records C.squares C.total length]. split; nia.
Qed.

Corollary disjoint_positive_quick_inputs_pay_all_calls : forall widths c
    (SOURCE:C.QuickCalls widths c) fee n,
  QuickCallsWork widths c SOURCE fee ->
  Forall (fun w=>0<w) widths -> C.total widths<=n ->
  records fee<=work fee /\ work fee<=288*n*n+772*n.
Proof.
  intros widths c SOURCE fee n COVER POSITIVE WIDTH.
  destruct (quick_calls_have_an_occurrence_sensitive_sum _ _ _ _ COVER) as [R W].
  pose proof (positive_widths_pay_for_occurrences _ POSITIVE).
  pose proof (C.squares_total widths). split; [exact R|nia].
Qed.

Definition drift_charge n scans merges quick_fee :=
  add (shell n) (add (sum scan scans) (add (sum merge merges) quick_fee)).

Inductive DriftWork : forall n c, C.Drift n c -> Charge -> Prop :=
| DriftSource : forall n scans merges sorted widths callbacks
    (SC:length scans<=n) (SW:Forall(fun w=>w<=n) scans)
    (MC:length merges<=n) (MW:Forall(fun w=>w<=n) merges)
    (RUN:C.Run n sorted widths)
    (QUICK:C.QuickCalls (widths++C.newly_sorted n sorted) callbacks) quick_fee,
    PositiveRun n sorted widths RUN ->
    QuickCallsWork _ _ QUICK quick_fee ->
    DriftWork n _ (C.DriftCalls n scans merges sorted widths callbacks SC SW MC MW RUN QUICK)
      (drift_charge n scans merges quick_fee).

Theorem drift_work_and_cumulative_records : forall n c (SOURCE:C.Drift n c) fee,
  DriftWork n c SOURCE fee ->
  records fee<=work fee /\ work fee<=312*n*n+844*n+192.
Proof.
  intros n c SOURCE fee COVER; destruct COVER.
  destruct (source_runs_have_positive_sort_inputs _ _ _ _ H) as [POSITIVE RUNS].
  assert (INPUTS:Forall(fun w=>0<w)(widths++C.newly_sorted n sorted)).
  { apply Forall_app; split; [exact RUNS|now apply newly_sorted_positive]. }
  pose proof (C.final_run_conserves_quicksort_width _ _ _ RUN) as WIDTH.
  destruct (disjoint_positive_quick_inputs_pay_all_calls _ _ _ _ n H0 INPUTS WIDTH)
    as [QR QW].
  pose proof (C.bounded_widths _ _ SW) as SCANS.
  pose proof (C.bounded_widths _ _ MW) as MERGES.
  destruct (sum_linear 8 8 2 2 scans) as [SCANW SCANR].
  destruct (sum_linear 32 16 4 2 merges) as [MERGEW MERGER].
  unfold drift_charge,add; cbn [work records shell].
  change (records(sum scan scans)=2*length scans+2*C.total scans) in SCANR.
  change (work(sum scan scans)=8*length scans+8*C.total scans) in SCANW.
  change (records(sum merge merges)=4*length merges+2*C.total merges) in MERGER.
  change (work(sum merge merges)=32*length merges+16*C.total merges) in MERGEW.
  rewrite SCANW,SCANR,MERGEW,MERGER. split; nia.
Qed.

(** The small top-level dispatch reuses the source's completed insertion
    model, not a fabricated smallsort trace. Its uniform threshold bound
    is intentionally separate from the large-input polynomial. Each saved
    pivot has one separately reserved gap-guard position (the source
    constructs the guard immediately after ReadPivot); one fixed local
    frame is also reserved, including empty calls. These extra positions
    receive work as well as records, rather than borrowing a copy credit.
    Thus the existing885 controls and228 transfers need another19+1
    reservation units, giving the uniform1133 top-level constant. *)
Inductive StableWork : forall n c, C.StableRequests n c -> Charge -> Prop :=
| StableSmallSource : forall Entry (source:list Entry) zst trace output
    (SOURCE:C.I.StableSmallBranch zst source trace output),
    StableWork (length source) _ (C.StableSmallRequests Entry source zst trace output SOURCE)
      (charge (C.I.count C.I.Controls trace+C.I.count C.I.Saves trace+
        C.I.count C.I.Shifts trace+C.I.count C.I.Fills trace+
        C.I.count C.I.Saves trace+1)
        (C.I.count C.I.Saves trace+C.I.count C.I.Shifts trace+C.I.count C.I.Fills trace+
        C.I.count C.I.Saves trace+1))
| StableEagerSource : forall n c (LARGE:20<n) (SOURCE:C.Eager n c) fee,
    EagerWork n c SOURCE fee ->
    StableWork n c (C.StableEagerRequests n c LARGE SOURCE) (add (charge 32 4) fee)
| StableDriftSource : forall n c (LARGE:20<n) (SOURCE:C.Drift n c) fee,
    DriftWork n c SOURCE fee ->
    StableWork n c (C.StableDriftRequests n c LARGE SOURCE) (add (charge 32 4) fee).

Definition core_bound n := 320*n*n+1024*n+1133.

Theorem all_widths_have_cumulative_native_core_allowances :
  forall n c (SOURCE:C.StableRequests n c) fee,
  StableWork n c SOURCE fee ->
  records fee<=work fee /\ work fee<=core_bound n /\ c<=10*n*n+32*n.
Proof.
  intros n c SOURCE fee COVER.
  pose proof (C.all_widths_request_envelope _ _ SOURCE) as CALLBACKS.
  destruct COVER.
  - pose proof (C.I.small_branch_has_the_source_threshold_envelope _ _ _ _ SOURCE)
      as [CMP [SHIFTS [SAVES [FILLS [CONTROL TRANSFERS]]]]].
    cbn [work records]. unfold core_bound. repeat split; nia.
  - destruct (eager_work_and_cumulative_records _ _ _ _ H) as [R W].
    cbn [add work records]. unfold core_bound. repeat split; nia.
  - destruct (drift_work_and_cumulative_records _ _ _ _ H) as [R W].
    cbn [add work records]. unfold core_bound. repeat split; nia.
Qed.

Print Assumptions eager_work_and_cumulative_records.
Print Assumptions quick_work_tracks_decreasing_depth.
Print Assumptions quick_work_with_original_depth_limit.
Print Assumptions source_runs_have_positive_sort_inputs.
Print Assumptions quick_calls_have_an_occurrence_sensitive_sum.
Print Assumptions disjoint_positive_quick_inputs_pay_all_calls.
Print Assumptions drift_work_and_cumulative_records.
Print Assumptions all_widths_have_cumulative_native_core_allowances.
End NativeStableSortWorkBound.
