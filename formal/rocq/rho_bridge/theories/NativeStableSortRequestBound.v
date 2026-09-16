(** Conservative comparator-request potential for the PINNED native stable
    sort, compiler 2e2b193f8ada105f27608b7be81c293e0d7292cb, 64-bit non-size
    optimized profile. This is count composition, NOT another sorter or an
    instruction, pointer, allocator, or sorting-correctness verification.

    Source boundary: stable/mod.rs dispatches <=20 to insertion; drift.rs
    creates positive-width runs, scans suffixes, merges adjacent runs, and
    quicksorts only UNSORTED intervals. quicksort.rs decrements its depth on
    every partition round, uses disjoint child slices, and at depth zero
    falls back to EAGER drift. Eager drift produces sorted runs and cannot
    initiate another nontrivial quicksort. Source associates these original
    widths and flags to the finite annotations below. No sought total count
    is assumed. Local source loop counts and this association are a reviewed
    standard-library dependency, not compiler-checked Rust semantics.

    The pivot recurrence comes from shared/pivot.rs (three recursive eighths,
    then <=3 median comparisons). Partition calls each inspect n-1 nonpivot
    records; at most two calls plus one ancestor test occur in a round.
    smallsort.rs has thresholds16/32. Fixed sort4/sort8 use5/18 requests
    (source-reviewed here); committed insertion and bidirectional-merge
    results supply their existing index/count laws. Complete typed callback
    work/scratch is SEPARATE: one request can compare key and then value.

    All widths are supported. This potential is intentionally conservative;
    it does not impose a width cap or alter ordinary native calls. Arithmetic
    overflow, reservation, actual typed operands and root ownership must be
    checked by the provider before execution. No provider is activated here. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
From RhoBridge Require Import NativeStableInsertionSort NativeStableBidirectionalMerge.
Import ListNotations.

Module NativeStableSortRequestBound.
Module I := NativeStableInsertionSort.NativeStableInsertionSort.
Module B := NativeStableBidirectionalMerge.NativeStableBidirectionalMerge.

Fixpoint total (xs : list nat) : nat :=
  match xs with [] => 0 | x :: rest => x + total rest end.
Fixpoint squares (xs : list nat) : nat :=
  match xs with [] => 0 | x :: rest => x*x + squares rest end.

Lemma total_app : forall a b, total (a++b) = total a + total b.
Proof. induction a; intro b; cbn; [reflexivity|rewrite IHa; lia]. Qed.
Lemma squares_total : forall xs, squares xs <= total xs * total xs.
Proof. induction xs; cbn in *; nia. Qed.
Lemma bounded_widths : forall xs n,
  Forall (fun x => x <= n) xs -> total xs <= length xs * n.
Proof. intros xs n H; induction H; cbn in *; nia. Qed.
Lemma small_widths : forall xs,
  Forall (fun x => x <= 32) xs -> squares xs <= 32 * total xs.
Proof. intros xs H; induction H; cbn in *; nia. Qed.

(** Median recursion is indexed by the ORIGINAL section width, not a
    caller-chosen recursion count. Reply-dependent omission of the third
    comparison can only reduce this upper potential. *)
Inductive Median : nat -> nat -> Prop :=
| MedianBase : forall n, 0 < n -> n < 8 -> Median n 3
| MedianRec : forall n c1 c2 c3,
    8 <= n -> Median (n/8) c1 -> Median (n/8) c2 -> Median (n/8) c3 ->
    Median n (c1+c2+c3+3).

Lemma median_linear : forall n c, Median n c -> c <= 6*n.
Proof.
  intros n c H; induction H.
  - nia.
  - pose proof (Nat.div_mod n 8 ltac:(lia)).
    pose proof (Nat.mod_upper_bound n 8 ltac:(lia)). nia.
Qed.
Inductive Pivot : nat -> nat -> Prop :=
| PivotSmall : forall n, 8 <= n -> n < 64 -> Pivot n 3
| PivotLarge : forall n c, 64 <= n -> Median (n/8) c -> Pivot n c.
Lemma pivot_within_width : forall n c, Pivot n c -> c <= n.
Proof.
  intros n c H; destruct H; [lia|].
  pose proof (median_linear _ _ H0).
  pose proof (Nat.div_mod n 8 ltac:(lia)). nia.
Qed.
Lemma partition_round_within_three_widths : forall n pivot,
  0 < n -> Pivot n pivot -> pivot + 1 + 2*(n-1) <= 3*n.
Proof. intros. pose proof (pivot_within_width _ _ H0). nia. Qed.

(** Two source-reviewed fixed prefixes are cheaper than starting those same
    prefixes with insertion. The insertion tails telescope against their
    initial triangular indices; no arbitrary callback cost is supplied. *)
Example sort4_prefix : 5 <= I.triangular 4. Proof. cbn; lia. Qed.
Example sort8_prefix : 18 <= I.triangular 8. Proof. cbn; lia. Qed.
Lemma triangular_square : forall n, I.triangular n <= n*n.
Proof. intro n. pose proof (I.triangular_is_the_exact_index_sum n). nia. Qed.
Lemma small_halves : forall a b,
  0 < a -> 0 < b ->
  I.triangular a + I.triangular b + (a+b) <= (a+b)*(a+b).
Proof.
  intros a b HA HB.
  pose proof (I.triangular_is_the_exact_index_sum a).
  pose proof (I.triangular_is_the_exact_index_sum b). nia.
Qed.
Lemma original_bidirectional_requests : forall n trace outcome,
  B.Run n trace outcome -> B.count B.Comparisons trace <= n.
Proof.
  intros n trace outcome RUN.
  pose proof (B.source_run_has_exact_counts _ _ _ RUN) as [_ [COUNT _]].
  rewrite COUNT. pose proof (Nat.div_mod n 2 ltac:(lia)). nia.
Qed.

(** A scan call reads an original suffix (<=n requests); a physical merge
    consumes at least one input per request (<=n-1, weakened to n here).
    Positive create-run progress gives <=n scans and <=n-1 merges. Small
    chunks are disjoint, each width <=32. These are local source-loop and
    interval premises, NOT the sought whole-sort count. *)
Inductive Eager : nat -> nat -> Prop :=
| EagerCalls : forall n scans merges chunks,
    length scans <= n -> Forall (fun w => w <= n) scans ->
    length merges <= n -> Forall (fun w => w <= n) merges ->
    total chunks <= n -> Forall (fun w => w <= 32) chunks ->
    Eager n (total scans + total merges + squares chunks).

Theorem eager_requests : forall n c, Eager n c -> c <= 2*n*n+32*n.
Proof.
  intros n c H; destruct H.
  pose proof (bounded_widths _ _ H0).
  pose proof (bounded_widths _ _ H2).
  pose proof (small_widths _ H4). nia.
Qed.

(** Quick's children are the actual disjoint slice widths. The equal-pivot
    branch is covered by one child of width <=n and an empty second child;
    its depth STILL decreases. Thus inconsistent replies cannot reset fuel.
    Eager leaves and small leaves are disjoint by the same width inventory. *)
Inductive Quick : nat -> nat -> nat -> Prop :=
| QuickSmall : forall n d, n <= 32 -> Quick n d (n*n)
| QuickFallback : forall n c, Eager n c -> Quick n 0 c
| QuickRound : forall n d left right lc rc,
    left+right <= n -> Quick left d lc -> Quick right d rc ->
    Quick n (S d) (3*n+lc+rc).

Theorem quick_depth_requests : forall n d c, Quick n d c ->
  c <= 3*d*n + 2*n*n + 32*n.
Proof.
  intros n d c H; induction H.
  - nia.
  - pose proof (eager_requests _ _ H). nia.
  - nia.
Qed.
Corollary quick_requests : forall n d c,
  d <= 2*n -> Quick n d c -> c <= 8*n*n+32*n.
Proof. intros. pose proof (quick_depth_requests _ _ _ H0). nia. Qed.

(** Original drift interval/flag transitions. A sorted interval is NEVER
    passed to quicksort again. Concatenating two unsorted intervals does not
    sort them; a physical merge first sorts only its unsorted children. *)
Definition newly_sorted (width : nat) (sorted : bool) :=
  if sorted then [] else [width].
Inductive Run : nat -> bool -> list nat -> Prop :=
| SortedRun : forall n, Run n true []
| UnsortedRun : forall n, Run n false []
| LazyJoin : forall l r ls rs,
    Run l false ls -> Run r false rs -> Run (l+r) false (ls++rs)
| PhysicalJoin : forall l r lf rf ls rs,
    Run l lf ls -> Run r rf rs ->
    Run (l+r) true (ls++rs++newly_sorted l lf++newly_sorted r rf).

Theorem sorted_flag_conserves_quicksort_width : forall n sorted widths,
  Run n sorted widths -> total widths <= if sorted then n else 0.
Proof.
  intros n sorted widths H; induction H; cbn; try lia.
  - rewrite total_app. lia.
  - rewrite !total_app. destruct lf,rf; cbn in *; lia.
Qed.
Corollary final_run_conserves_quicksort_width : forall n sorted widths,
  Run n sorted widths -> total (widths++newly_sorted n sorted) <= n.
Proof.
  intros. pose proof (sorted_flag_conserves_quicksort_width _ _ _ H).
  rewrite total_app. destruct sorted; cbn in *; lia.
Qed.

Inductive QuickCalls : list nat -> nat -> Prop :=
| QuickCallsNil : QuickCalls [] 0
| QuickCallsCons : forall n rest d c tail,
    d <= 2*n -> Quick n d c -> QuickCalls rest tail ->
    QuickCalls (n::rest) (c+tail).
Lemma disjoint_quick_requests : forall widths c,
  QuickCalls widths c -> c <= 8*squares widths+32*total widths.
Proof.
  intros widths c H; induction H; cbn; [lia|].
  pose proof (quick_requests _ _ _ H H0). nia.
Qed.

Inductive Drift : nat -> nat -> Prop :=
| DriftCalls : forall n scans merges sorted widths callbacks,
    length scans <= n -> Forall (fun w => w <= n) scans ->
    length merges <= n -> Forall (fun w => w <= n) merges ->
    Run n sorted widths ->
    QuickCalls (widths++newly_sorted n sorted) callbacks ->
    Drift n (total scans+total merges+callbacks).

Theorem drift_requests : forall n c, Drift n c -> c <= 10*n*n+32*n.
Proof.
  intros n c H; destruct H.
  pose proof (bounded_widths _ _ H0).
  pose proof (bounded_widths _ _ H2).
  pose proof (final_run_conserves_quicksort_width _ _ _ H3).
  pose proof (disjoint_quick_requests _ _ H4).
  pose proof (squares_total (widths++newly_sorted n sorted)). nia.
Qed.

(** Preserve the actual <=20 dispatch and its committed tighter bound. *)
Theorem original_small_dispatch_requests : forall Entry (source : list Entry) zst trace output,
  I.StableSmallBranch zst source trace output ->
  I.count I.Comparisons trace <= I.triangular (length source).
Proof.
  intros. pose proof (I.small_branch_keeps_records_and_bounds_native_callbacks
    _ _ _ _ H) as [_ [COUNT _]]. exact COUNT.
Qed.

(** The large-input entrypoint itself can select eager drift (up to twice
    the type's small-sort threshold), independently of quicksort fallback.
    Include that entry explicitly; do not drop its small-chunk calls. *)
Inductive StableRequests : nat -> nat -> Prop :=
| StableSmallRequests : forall Entry (source : list Entry) zst trace output,
    I.StableSmallBranch zst source trace output ->
    StableRequests (length source) (I.count I.Comparisons trace)
| StableEagerRequests : forall n c, 20 < n -> Eager n c -> StableRequests n c
| StableDriftRequests : forall n c, 20 < n -> Drift n c -> StableRequests n c.

Theorem all_widths_request_envelope : forall n c,
  StableRequests n c -> c <= 10*n*n+32*n.
Proof.
  intros n c H; destruct H.
  - pose proof (original_small_dispatch_requests _ _ _ _ _ H).
    pose proof (triangular_square (length source)). nia.
  - pose proof (eager_requests _ _ H0). nia.
  - now apply drift_requests.
Qed.

End NativeStableSortRequestBound.
Print Assumptions NativeStableSortRequestBound.pivot_within_width.
Print Assumptions NativeStableSortRequestBound.eager_requests.
Print Assumptions NativeStableSortRequestBound.quick_depth_requests.
Print Assumptions NativeStableSortRequestBound.sorted_flag_conserves_quicksort_width.
Print Assumptions NativeStableSortRequestBound.drift_requests.
Print Assumptions NativeStableSortRequestBound.original_small_dispatch_requests.
Print Assumptions NativeStableSortRequestBound.all_widths_request_envelope.
