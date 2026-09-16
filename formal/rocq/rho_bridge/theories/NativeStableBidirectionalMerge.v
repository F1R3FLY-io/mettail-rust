(** Source-count and occurrence inventory for native bidirectional_merge.

    Pinned Rust compiler: 2e2b193f8ada105f27608b7be81c293e0d7292cb.
    Source: core/src/slice/sort/shared/smallsort.rs:677-842, relative to
    lib/rustlib/src/rust/library; SHA256:
    85c75bc93745ff1d4a6d33939d48408c2f7304aa8ffd952b73199ec1f8a175e1.

    The four counters name advances from the ORIGINAL half-range endpoints.
    They are not a deque algorithm: front and back may temporarily overlap,
    because inconsistent comparator answers are permitted by the source.
    A comparison always borrows the original right pointer THEN left pointer.
    merge_up copies left on false; merge_down copies left on true. The fixed
    loop performs both, then increments its iteration index. The odd tail
    copies without a comparison. Only the source's final two cursor equalities
    justify treating all copied occurrences as a permutation of the input.

    Event indices distinguish source occurrences even when records compare
    equal. The whole-record theorem transports the chronological copy
    inventory to arbitrary COMPLETE records. A separate destination-index
    permutation proves every output slot is written exactly once. No separate
    key/value reconstruction or comparator law is used.
    For Map, a record is the original borrowed key/value reference pair plus
    occurrence identity. This does not assert that referent internals cannot
    mutate: Freeze applies to the copied reference-pair slots.
    Events are proof annotations, not runtime allocations or another sorter.
    Controls count named source groups, not CPU instructions. Callback bodies,
    pointer provenance/non-aliasing, physical allocator costs, checked receipt
    arithmetic, comparator exceptions and other native-sort branches remain
    separate obligations. OrdViolation is retained as a non-success outcome
    at panic dispatch; unwinding costs are not counted.
    This bounded model introduces neither a public width cap nor an admission
    claim for the full Map Hash implementation. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia Sorting.Permutation.
Import ListNotations.

Module NativeStableBidirectionalMerge.

Record Cursors := cursors { lf : nat; rf : nat; lb : nat; rb : nat }.
Definition initial := cursors 0 0 0 0.
Definition up (reply : bool) (s : Cursors) :=
  if reply then cursors (lf s) (S (rf s)) (lb s) (rb s)
  else cursors (S (lf s)) (rf s) (lb s) (rb s).
Definition down (reply : bool) (s : Cursors) :=
  if reply then cursors (lf s) (rf s) (S (lb s)) (rb s)
  else cursors (lf s) (rf s) (lb s) (S (rb s)).
Definition advances (i : nat) (s : Cursors) :=
  lf s + rf s = i /\ lb s + rb s = i.

Inductive Group := Setup | LoopGuard | UpSelect | UpAdvance
  | DownSelect | DownAdvance | EndPointers | OddGuard | OddSelect
  | OddAdvance | FinalGuard | Return | Panic.
Inductive Event := Control (group : Group)
  | Compare (right_index left_index : nat) (reply : bool)
  | Copy (source_index destination_index : nat).
Inductive Counter := Controls | Comparisons | Copies.
Definition weight counter event := match counter, event with
  | Controls, Control _ | Comparisons, Compare _ _ _ | Copies, Copy _ _ => 1
  | _, _ => 0 end.
Definition count counter trace := fold_right (fun e n => weight counter e + n) 0 trace.
Lemma count_cons : forall counter event trace,
  count counter (event::trace) = weight counter event + count counter trace.
Proof. reflexivity. Qed.
Lemma count_app : forall counter a b,
  count counter (a ++ b) = count counter a + count counter b.
Proof. intros counter a. induction a; intros; [reflexivity|].
  change (weight counter a + count counter (a0 ++ b) =
    (weight counter a + count counter a0) + count counter b).
  rewrite IHa. lia. Qed.
Fixpoint copied trace := match trace with
  | [] => [] | Copy source _ :: rest => source :: copied rest
  | _ :: rest => copied rest end.
Lemma copied_app : forall a b, copied (a ++ b) = copied a ++ copied b.
Proof. induction a as [|e rest IH]; intro b; [reflexivity|].
  destruct e; cbn; now rewrite IH. Qed.
Fixpoint destinations trace := match trace with
  | [] => [] | Copy _ destination :: rest => destination :: destinations rest
  | _ :: rest => destinations rest end.
Lemma destinations_app : forall a b,
  destinations (a ++ b) = destinations a ++ destinations b.
Proof. induction a as [|e rest IH]; intro b; [reflexivity|].
  destruct e; cbn; now rewrite IH. Qed.

Definition up_index h (reply : bool) s := if reply then h + rf s else lf s.
Definition down_index n h (reply : bool) s := if reply then h - S (lb s) else n - S (rb s).
Definition iteration n h i s u d :=
  [Control LoopGuard;
   Compare (h + rf s) (lf s) u; Control UpSelect;
   Copy (up_index h u s) i; Control UpAdvance;
   Compare (n - S (rb s)) (h - S (lb s)) d; Control DownSelect;
   Copy (down_index n h d s) (n - S i); Control DownAdvance].

(** i is the original for-loop index, not a caller-supplied trace bound. *)
Inductive Loop (n h : nat) : nat -> Cursors -> list Event -> Cursors -> Prop :=
| LoopEnd : forall s, Loop n h h s [Control LoopGuard] s
| LoopNext : forall i s u d trace final,
    i < h -> Loop n h (S i) (down d (up u s)) trace final ->
    Loop n h i s (iteration n h i s u d ++ trace) final.

Lemma one_iteration_advances : forall i s u d,
  advances i s -> advances (S i) (down d (up u s)).
Proof. intros i s [] []; unfold advances, up, down; cbn; lia. Qed.
Theorem loop_counts_follow_its_source_index : forall n h i s trace final,
  Loop n h i s trace final ->
  i <= h /\ count Comparisons trace = 2 * (h-i) /\
  count Copies trace = 2 * (h-i) /\ count Controls trace = 5 * (h-i) + 1.
Proof. intros n h i s trace final RUN. induction RUN;
  rewrite ?count_app; cbn [iteration count fold_right weight] in *;
  repeat split; lia. Qed.
Theorem loop_preserves_advance_counts : forall n h i s trace final,
  Loop n h i s trace final -> advances i s -> advances h final.
Proof. intros n h i s trace final RUN. induction RUN; intro A; [exact A|].
  apply IHRUN. now apply one_iteration_advances. Qed.

(** Each independent front/back stream contains original occurrence indices.
    Their concatenation may contain duplicates before the terminal check. *)
Definition span first width front back :=
  seq first front ++ seq (first + width - back) back.
Definition inventory n h s :=
  span 0 h (lf s) (lb s) ++ span h (n-h) (rf s) (rb s).

Lemma span_front : forall first width front back,
  Permutation ((first+front) :: span first width front back)
    (span first width (S front) back).
Proof. intros. unfold span. rewrite seq_S, <- app_assoc. cbn [app].
  apply Permutation_middle. Qed.
Lemma span_back : forall first width front back,
  back < width ->
  Permutation ((first+width-S back) :: span first width front back)
    (span first width front (S back)).
Proof. intros. unfold span. cbn [seq].
  replace (S (first+width-S back)) with (first+width-back) by lia.
  apply Permutation_middle. Qed.
Lemma inventory_up : forall n h s reply,
  Permutation (up_index h reply s :: inventory n h s)
    (inventory n h (up reply s)).
Proof.
  intros n h s []; unfold up_index, up, inventory; cbn [lf rf lb rb].
  - eapply Permutation_trans; [apply Permutation_middle|].
    apply Permutation_app_head. apply span_front.
  - exact (@Permutation_app_tail nat _ _ _ (span_front 0 h (lf s) (lb s))).
Qed.
Lemma inventory_down : forall n h s reply,
  h <= n -> lb s < h -> rb s < n-h ->
  Permutation (down_index n h reply s :: inventory n h s)
    (inventory n h (down reply s)).
Proof.
  intros n h s [] H L R; unfold down_index, down, inventory; cbn [lf rf lb rb].
  - exact (@Permutation_app_tail nat _ _ _ (span_back 0 h (lf s) (lb s) L)).
  - eapply Permutation_trans; [apply Permutation_middle|].
    apply Permutation_app_head.
    replace (n-S(rb s)) with (h+(n-h)-S(rb s)) by lia.
    now apply span_back.
Qed.
Lemma iteration_inventory : forall n h i s u d,
  h <= n-h -> advances i s -> i < h ->
  Permutation (copied (iteration n h i s u d) ++ inventory n h s)
    (inventory n h (down d (up u s))).
Proof.
  intros n h i s u d H A I. cbn [iteration copied app].
  eapply Permutation_trans; [apply perm_swap|].
  eapply Permutation_trans; [apply perm_skip; apply inventory_up|].
  replace (down_index n h d s) with (down_index n h d (up u s))
    by (destruct u,d; reflexivity).
  apply inventory_down; unfold advances in A; destruct u; cbn [up lb rb]; lia.
Qed.
Theorem loop_tracks_original_occurrences : forall n h i s trace final,
  Loop n h i s trace final -> h <= n-h -> advances i s ->
  Permutation (copied trace ++ inventory n h s) (inventory n h final).
Proof.
  intros n h i s trace final RUN. induction RUN; intros WIDTH A.
  - cbn [copied app]. apply Permutation_refl.
  - rewrite copied_app. rewrite <- app_assoc.
    eapply Permutation_trans; [apply Permutation_app_swap_app|].
    eapply Permutation_trans.
    + apply Permutation_app_head. apply iteration_inventory with (i:=i); assumption.
    + apply IHRUN; [exact WIDTH|now apply one_iteration_advances].
Qed.

(** Destination writes are independent of comparison replies: the next pair
    is i and n-1-i. This separate invariant is needed to transport the
    chronological source inventory to the completed destination buffer. *)
Theorem loop_writes_exact_destination_ranges : forall n h i s trace final,
  Loop n h i s trace final -> 2*h <= n ->
  Permutation (destinations trace) (seq i (h-i) ++ seq (n-h) (h-i)).
Proof.
  intros n h i s trace final RUN. induction RUN; intro N.
  - rewrite Nat.sub_diag. cbn [destinations seq app]. apply Permutation_refl.
  - rewrite destinations_app. cbn [iteration destinations app].
    eapply Permutation_trans.
    + apply perm_skip. apply perm_skip. apply IHRUN. exact N.
    + replace (h-i) with (S(h-S i)) by lia.
      rewrite (seq_S (h-S i) (n-h)).
      change (Permutation
        (i :: (n-S i) :: seq (S i) (h-S i) ++ seq (n-h) (h-S i))
        (i :: seq (S i) (h-S i) ++ (seq (n-h) (h-S i) ++ [n-h+(h-S i)]) )).
      apply perm_skip. replace (n-S i) with (n-h+(h-S i)) by lia.
      rewrite app_assoc. apply Permutation_cons_append.
Qed.

(** The actual end-pointer equality is front = width-back. Using sums is
    equivalent when each backwards pointer has advanced at most its width. *)
Definition consumed n h s := lf s + lb s = h /\ rf s + rb s = n-h.
Definition consumedb n h s :=
  (lf s + lb s =? h) && (rf s + rb s =? n-h).
Lemma consumedb_spec : forall n h s, consumedb n h s = true <-> consumed n h s.
Proof. intros. unfold consumedb, consumed. rewrite andb_true_iff, !Nat.eqb_eq.
  reflexivity. Qed.
Lemma consumed_is_source_end_check : forall n h s,
  lb s <= h -> rb s <= n-h ->
  (consumed n h s <-> lf s = h-lb s /\ rf s = (n-h)-rb s).
Proof. unfold consumed; intros; lia. Qed.
Lemma span_complete : forall first width front back,
  front + back = width -> span first width front back = seq first width.
Proof. intros. unfold span. replace (first+width-back) with (first+front) by lia.
  rewrite <- seq_app. now rewrite H. Qed.
Lemma consumed_inventory : forall n h s,
  h <= n -> consumed n h s -> inventory n h s = seq 0 n.
Proof. intros n h s H [L R]. unfold inventory.
  rewrite (span_complete _ _ _ _ L), (span_complete _ _ _ _ R).
  replace h with (0+h) at 2 by lia. rewrite <- seq_app.
  f_equal. lia. Qed.

Definition left_nonempty h s := lf s <? h - lb s.
Definition odd_after h s := up (negb (left_nonempty h s)) s.
Definition odd_events (n : nat) h s :=
  [Control OddSelect;
   Copy (up_index h (negb (left_nonempty h s)) s) h;
   Control OddAdvance].
Inductive Outcome := Accepted | OrdViolation.
Definition verdict n h s := if consumedb n h s then Accepted else OrdViolation.
Definition final_event n h s :=
  if consumedb n h s then Control Return else Control Panic.
Definition ending n h (odd : bool) s :=
  [Control EndPointers; Control OddGuard] ++
  (if odd then odd_events n h s else []) ++
  [Control FinalGuard; final_event n h (if odd then odd_after h s else s)].
Inductive Run : nat -> list Event -> Outcome -> Prop :=
| RunEven : forall h trace s,
    0 < h -> Loop (2*h) h 0 initial trace s ->
    Run (2*h) (Control Setup :: trace ++ ending (2*h) h false s)
      (verdict (2*h) h s)
| RunOdd : forall h trace s,
    0 < h -> Loop (S(2*h)) h 0 initial trace s ->
    Run (S(2*h)) (Control Setup :: trace ++ ending (S(2*h)) h true s)
      (verdict (S(2*h)) h (odd_after h s)).

Lemma ending_counts : forall n h odd s,
  count Comparisons (ending n h odd s) = 0 /\
  count Copies (ending n h odd s) = (if odd then 1 else 0) /\
  count Controls (ending n h odd s) = (if odd then 6 else 4).
Proof. intros n h [] s; unfold ending, odd_events, final_event;
  destruct (consumedb n h (odd_after h s)); destruct (consumedb n h s);
  cbn [app count fold_right weight]; repeat split; reflexivity. Qed.
Theorem source_run_has_exact_counts : forall n trace outcome,
  Run n trace outcome ->
  2 <= n /\ count Comparisons trace = 2*(n/2) /\
  count Copies trace = n /\ count Controls trace = 5*(n/2)+6+2*(n mod 2).
Proof.
  intros n trace outcome RUN. destruct RUN;
    pose proof (Nat.div_mod (2*h) 2 ltac:(lia)) as EVEN;
    pose proof (Nat.mod_upper_bound (2*h) 2 ltac:(lia)) as EVEN_BOUND;
    pose proof (Nat.div_mod (S(2*h)) 2 ltac:(lia)) as ODD;
    pose proof (Nat.mod_upper_bound (S(2*h)) 2 ltac:(lia)) as ODD_BOUND;
    pose proof (loop_counts_follow_its_source_index _ _ _ _ _ _ H0) as C;
    pose proof (ending_counts (2*h) h false s) as E;
    pose proof (ending_counts (S(2*h)) h true s) as O;
    rewrite !count_cons, !count_app; cbn [weight]; destruct C as [_ [C [D F]]];
    destruct E as [E1 [E2 E3]]; destruct O as [O1 [O2 O3]];
    rewrite ?C, ?D, ?F, ?E1, ?E2, ?E3, ?O1, ?O2, ?O3;
    repeat split; lia.
Qed.

(** Source read validity follows from the fixed loop index, even when the
    independent front/back regions overlap. Thus no hidden consistency law
    is needed merely to identify the original callback operands. *)
Definition original_access n event := match event with
  | Compare rhs lhs _ => rhs < n /\ lhs < n
  | Copy source destination => source < n /\ destination < n
  | Control _ => True end.
Lemma iteration_accesses_original_records : forall n h i s u d,
  0 < h -> h <= n-h -> i < h -> advances i s ->
  Forall (original_access n) (iteration n h i s u d).
Proof.
  intros n h i s [] [] H N I A; unfold advances in A;
    cbn [iteration up_index down_index];
    repeat (apply Forall_cons; [cbn [original_access up_index down_index]; repeat split; lia|]);
    apply Forall_nil.
Qed.
Theorem loop_accesses_original_records : forall n h i s trace final,
  Loop n h i s trace final -> 0 < h -> h <= n-h -> advances i s ->
  Forall (original_access n) trace.
Proof.
  intros n h i s trace final RUN. induction RUN; intros POS N A.
  - repeat constructor.
  - apply Forall_app. split.
    + apply iteration_accesses_original_records; assumption.
    + apply IHRUN; [exact POS|exact N|now apply one_iteration_advances].
Qed.
Lemma ending_accesses_original_records : forall h (odd : bool) s,
  0 < h -> advances h s ->
  Forall (original_access (if odd then S(2*h) else 2*h))
    (ending (if odd then S(2*h) else 2*h) h odd s).
Proof.
  intros h [] s H A; unfold advances in A;
    unfold ending, final_event, odd_events; cbn [app];
    destruct (consumedb (S(2*h)) h (odd_after h s));
    destruct (consumedb (2*h) h s).
  all: unfold up_index, left_nonempty; destruct (lf s <? h-lb s) eqn:E.
  all: first [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E].
  all: cbn [negb];
    repeat (apply Forall_cons; [cbn [original_access up_index down_index]; repeat split; lia|]);
    apply Forall_nil.
Qed.
Theorem run_accesses_original_records : forall n trace outcome,
  Run n trace outcome -> Forall (original_access n) trace.
Proof.
  intros n trace outcome RUN. destruct RUN; constructor; [exact I| |exact I|];
    apply Forall_app; split.
  - eapply loop_accesses_original_records; [exact H0|exact H|lia|].
    unfold advances, initial; cbn; lia.
  - apply (ending_accesses_original_records h false s); [exact H|].
    eapply loop_preserves_advance_counts; [exact H0|].
    unfold advances, initial; cbn; lia.
  - eapply loop_accesses_original_records; [exact H0|exact H|lia|].
    unfold advances, initial; cbn; lia.
  - apply (ending_accesses_original_records h true s); [exact H|].
    eapply loop_preserves_advance_counts; [exact H0|].
    unfold advances, initial; cbn; lia.
Qed.

Theorem run_writes_each_destination_once : forall n trace outcome,
  Run n trace outcome -> Permutation (destinations trace) (seq 0 n).
Proof.
  intros n trace outcome RUN. destruct RUN.
  - pose proof (loop_writes_exact_destination_ranges _ _ _ _ _ _ H0 ltac:(lia)) as D.
    replace (h-0) with h in D by lia. replace (2*h-h) with h in D by lia.
    cbn [destinations]. rewrite destinations_app. unfold ending, final_event.
    destruct (consumedb (2*h) h s); cbn [destinations app]; rewrite app_nil_r.
    all: (eapply Permutation_trans; [exact D|]).
    all:
      change (Permutation (seq 0 h ++ seq (0+h) h) (seq 0 (2*h)));
      rewrite <- seq_app; replace (h+h) with (2*h) by lia; apply Permutation_refl.
  - pose proof (loop_writes_exact_destination_ranges _ _ _ _ _ _ H0 ltac:(lia)) as D.
    replace (h-0) with h in D by lia. replace (S(2*h)-h) with (S h) in D by lia.
    cbn [destinations]. rewrite destinations_app. unfold ending, final_event, odd_events.
    destruct (consumedb (S(2*h)) h (odd_after h s)); cbn [destinations app].
    all: (eapply Permutation_trans; [apply Permutation_app_tail; exact D|]).
    all: rewrite <- app_assoc.
    all: (eapply Permutation_trans;
        [apply Permutation_app_head; apply Permutation_sym; apply Permutation_cons_append|]).
    all:
      change (Permutation (seq 0 h ++ seq h (S h)) (seq 0 (S(2*h))));
      rewrite <- seq_app; replace (h+S h) with (S(2*h)) by lia; apply Permutation_refl.
Qed.

Lemma initial_inventory : forall n h, inventory n h initial = [].
Proof. reflexivity. Qed.
Lemma accepted_verdict : forall n h s,
  verdict n h s = Accepted -> consumed n h s.
Proof. intros. unfold verdict in H. destruct (consumedb n h s) eqn:E;
  [now apply consumedb_spec|discriminate]. Qed.
Theorem successful_run_preserves_original_occurrence_inventory : forall n trace,
  Run n trace Accepted -> Permutation (copied trace) (seq 0 n).
Proof.
  intros n trace RUN. remember Accepted as result eqn:OK. destruct RUN.
  - pose proof (loop_tracks_original_occurrences _ _ _ _ _ _ H0) as P.
    specialize (P ltac:(lia) ltac:(unfold advances,initial; cbn; lia)).
    rewrite initial_inventory, app_nil_r in P.
    apply accepted_verdict in OK.
    rewrite (consumed_inventory (2*h) h s ltac:(lia) OK) in P.
    cbn [copied]. rewrite copied_app. unfold ending, final_event.
    destruct (consumedb (2*h) h s); cbn [copied app]; now rewrite app_nil_r.
  - pose proof (loop_tracks_original_occurrences _ _ _ _ _ _ H0) as P.
    specialize (P ltac:(lia) ltac:(unfold advances,initial; cbn; lia)).
    rewrite initial_inventory, app_nil_r in P.
    apply accepted_verdict in OK.
    cbn [copied]. rewrite copied_app. unfold ending, final_event, odd_events.
    destruct (consumedb (S(2*h)) h (odd_after h s)); cbn [copied app].
    all: (eapply Permutation_trans; [apply Permutation_app_comm|]); cbn [app].
    all: (eapply Permutation_trans; [apply perm_skip; exact P|]).
    all: (eapply Permutation_trans; [apply inventory_up|]).
    all: change (Permutation (inventory (S(2*h)) h (odd_after h s)) (seq 0 (S(2*h)))).
    all: rewrite (consumed_inventory (S(2*h)) h (odd_after h s) ltac:(lia) OK);
      apply Permutation_refl.
Qed.

Lemma map_nth_original : forall (Entry : Type) (source : list Entry) fallback,
  map (fun index => nth index source fallback) (seq 0 (length source)) = source.
Proof.
  intros Entry source. induction source as [|entry rest IH]; intro fallback; [reflexivity|].
  cbn [length seq map nth]. f_equal.
  rewrite <- (seq_shift (length rest) 0). rewrite map_map.
  cbn [nth]. apply IH.
Qed.
Theorem successful_run_preserves_whole_original_records :
  forall (Entry : Type) (source : list Entry) fallback trace,
  Run (length source) trace Accepted ->
  Permutation (map (fun index => nth index source fallback) (copied trace)) source.
Proof.
  intros Entry source fallback trace RUN.
  pose proof (successful_run_preserves_original_occurrence_inventory
    (length source) trace RUN) as P.
  pose proof (@Permutation_map nat Entry (fun index => nth index source fallback)
    _ _ P) as M.
  rewrite map_nth_original in M. exact M.
Qed.

Theorem callbacks_borrow_actual_original_records :
  forall (Entry : Type) (source : list Entry) trace outcome right left reply,
  Run (length source) trace outcome -> In (Compare right left reply) trace ->
  exists right_record left_record,
    nth_error source right = Some right_record /\
    nth_error source left = Some left_record.
Proof.
  intros Entry source trace outcome right left reply RUN IN.
  pose proof (run_accesses_original_records _ _ _ RUN) as ACCESS.
  rewrite Forall_forall in ACCESS. specialize (ACCESS _ IN).
  cbn [original_access] in ACCESS. destruct ACCESS as [R L].
  destruct (nth_error source right) as [rv|] eqn:ER;
    [|apply nth_error_None in ER; lia].
  destruct (nth_error source left) as [lv|] eqn:EL;
    [|apply nth_error_None in EL; lia].
  exists rv,lv. auto.
Qed.

Example two_record_success : exists trace, Run 2 trace Accepted.
Proof. eexists. apply (RunEven 1
    (iteration 2 1 0 initial false false ++ [Control LoopGuard])
    (cursors 1 0 0 1)); [lia|].
  eapply LoopNext with (u:=false) (d:=false); [lia|]. apply LoopEnd. Qed.
Example inconsistent_replies_are_rejected : exists trace, Run 2 trace OrdViolation.
Proof. eexists. apply (RunEven 1
    (iteration 2 1 0 initial false true ++ [Control LoopGuard])
    (cursors 1 0 1 0)); [lia|].
  eapply LoopNext with (u:=false) (d:=true); [lia|]. apply LoopEnd. Qed.
Example odd_tail_success : exists trace, Run 3 trace Accepted.
Proof. eexists. apply (RunOdd 1
    (iteration 3 1 0 initial false false ++ [Control LoopGuard])
    (cursors 1 0 0 1)); [lia|].
  eapply LoopNext with (u:=false) (d:=false); [lia|]. apply LoopEnd. Qed.

Print Assumptions loop_counts_follow_its_source_index.
Print Assumptions loop_tracks_original_occurrences.
Print Assumptions consumed_is_source_end_check.
Print Assumptions source_run_has_exact_counts.
Print Assumptions run_accesses_original_records.
Print Assumptions run_writes_each_destination_once.
Print Assumptions successful_run_preserves_original_occurrence_inventory.
Print Assumptions successful_run_preserves_whole_original_records.
Print Assumptions callbacks_borrow_actual_original_records.
End NativeStableBidirectionalMerge.
