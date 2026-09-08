(** Occurrence conservation for fallible, fixed-width bottom-up merge passes.

    Algorithm source: vinary-requirements/crates/vinary-math-ir/src/canonical.rs,
    stable_order. Adjacent width-sized runs are merged into a scratch sequence;
    the next pass doubles width. Greater selects the right head; Equal selects
    the left. This model retains an explicit comparison state, including the
    state returned on refusal, so a failed comparison cannot become Equal or
    erase the work already spent. Fuel makes the specification executable; it
    is a termination index, not an additional production resource allowance.

    Conservation/refusal laws hold independently of comparator correctness.
    Sorted-run growth and stable equal-key subsequences additionally require
    the explicitly quantified order/comparison laws. The model does not prove
    concrete receipt comparator field coverage, the in-place inverse-permutation
    implementation, or resource accounting.
    Whole-record permutation is the required transport invariant: terms and
    their complete receipts must never be sorted in separate sequences. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Sorting.Sorted Lia.
Import ListNotations.

Module SemanticResultMerge.

Section Machine.
Context {A State : Type}.
Variable compare : A -> A -> State -> option comparison * State.

Definition prepend (x : A) (result : option (list A) * State) :=
  (option_map (cons x) (fst result), snd result).

Fixpoint merge (fuel : nat) (left right : list A) (state : State)
    : option (list A) * State :=
  match left, right with
  | [], _ => (Some right, state)
  | _, [] => (Some left, state)
  | x :: xs, y :: ys =>
      match fuel with
      | 0 => (None, state)
      | S smaller =>
          let '(decision, next) := compare x y state in
          match decision with
          | None => (None, next)
          | Some Gt => prepend y (merge smaller left ys next)
          | Some _ => prepend x (merge smaller xs right next)
          end
      end
  end.

Lemma merge_preserves_occurrences : forall fuel left right state result final,
  merge fuel left right state = (Some result, final) ->
  Permutation (left ++ right) result.
Proof.
  induction fuel as [|fuel IH]; intros [|x xs] [|y ys] state result final H;
    cbn [merge] in H; try (inversion H; subst; rewrite ?app_nil_r; reflexivity);
    try discriminate.
  destruct (compare x y state) as [[decision|] next] eqn:C; try discriminate.
  destruct decision.
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. apply perm_skip. eapply IH; exact M.
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. apply perm_skip. eapply IH; exact M.
  - destruct (merge fuel (x :: xs) ys next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst.
    eapply Permutation_trans.
    + apply Permutation_sym. apply Permutation_middle.
    + apply perm_skip. eapply IH; exact M.
Qed.

Theorem refused_comparison_keeps_its_state : forall fuel x xs y ys state next,
  compare x y state = (None, next) ->
  merge (S fuel) (x :: xs) (y :: ys) state = (None, next).
Proof. intros. cbn [merge]. now rewrite H. Qed.

Theorem equal_heads_select_left : forall fuel x xs y ys state next,
  compare x y state = (Some Eq, next) ->
  merge (S fuel) (x :: xs) (y :: ys) state =
    prepend x (merge fuel xs (y :: ys) next).
Proof. intros. cbn [merge]. now rewrite H. Qed.

Lemma merge_has_sufficient_fuel :
  (forall x y state, exists decision next, compare x y state = (Some decision, next)) ->
  forall fuel left right state,
  length left + length right <= fuel ->
  exists result final, merge fuel left right state = (Some result, final).
Proof.
  intros total fuel. induction fuel as [|fuel IH];
    intros [|x xs] [|y ys] state B;
    try (eexists; eexists; reflexivity); cbn [length] in B; try lia.
  destruct (total x y state) as [decision [next C]].
  cbn [merge]. rewrite C. destruct decision.
  - destruct (IH xs (y :: ys) next ltac:(cbn [length]; lia)) as [rest [last M]].
    rewrite M. eexists; eexists; reflexivity.
  - destruct (IH xs (y :: ys) next ltac:(cbn [length]; lia)) as [rest [last M]].
    rewrite M. eexists; eexists; reflexivity.
  - destruct (IH (x :: xs) ys next ltac:(cbn [length]; lia)) as [rest [last M]].
    rewrite M. eexists; eexists; reflexivity.
Qed.

Lemma head_bounded_merge : forall (R : A -> A -> Prop)
  fuel x left right state result final,
  Forall (R x) left -> Forall (R x) right ->
  merge fuel left right state = (Some result, final) -> Forall (R x) result.
Proof.
  intros R fuel x left right state result final L B M.
  eapply Permutation_Forall.
  - eapply merge_preserves_occurrences; exact M.
  - apply Forall_app. split; assumption.
Qed.

Theorem merge_sorted_runs : forall (R : A -> A -> Prop),
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => R y x | _ => R x y end) ->
  forall fuel left right state result final,
  StronglySorted R left -> StronglySorted R right ->
  merge fuel left right state = (Some result, final) -> StronglySorted R result.
Proof.
  intros R trans sound fuel. induction fuel as [|fuel IH];
    intros [|x xs] [|y ys] state result final L B H;
    cbn [merge] in H; try (inversion H; subst; assumption); try discriminate.
  destruct (StronglySorted_inv L) as [LX FX].
  destruct (StronglySorted_inv B) as [LY FY].
  destruct (compare x y state) as [[decision|] next] eqn:C; try discriminate.
  pose proof (sound x y state decision next C) as ordered.
  destruct decision; cbn in ordered.
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. constructor.
    + eapply IH; [exact LX | exact B | exact M].
    + eapply head_bounded_merge; [exact FX | | exact M].
      constructor; [exact ordered |]. rewrite Forall_forall in FY |- *.
      intros z Z. eapply trans; [exact ordered | apply FY; exact Z].
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. constructor.
    + eapply IH; [exact LX | exact B | exact M].
    + eapply head_bounded_merge; [exact FX | | exact M].
      constructor; [exact ordered |]. rewrite Forall_forall in FY |- *.
      intros z Z. eapply trans; [exact ordered | apply FY; exact Z].
  - destruct (merge fuel (x :: xs) ys next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. constructor.
    + eapply IH; [exact L | exact LY | exact M].
    + eapply head_bounded_merge; [| exact FY | exact M].
      constructor; [exact ordered |]. rewrite Forall_forall in FX |- *.
      intros z Z. eapply trans; [exact ordered | apply FX; exact Z].
Qed.

Fixpoint pass (fuel width : nat) (values : list A) (state : State)
    : option (list A) * State :=
  match values with
  | [] => (Some [], state)
  | _ => match fuel with
    | 0 => (None, state)
    | S smaller =>
        let left := firstn width values in
        let remaining := skipn width values in
        let right := firstn width remaining in
        let tail := skipn width remaining in
        let '(merged, next) := merge (length left + length right) left right state in
        match merged with
        | None => (None, next)
        | Some run =>
            let '(suffix, final) := pass smaller width tail next in
            (option_map (app run) suffix, final)
        end
    end
  end.

Lemma split_adjacent_runs : forall width (values : list A),
  (firstn width values ++ firstn width (skipn width values)) ++
    skipn width (skipn width values) = values.
Proof.
  intros. rewrite <- app_assoc, firstn_skipn, firstn_skipn. reflexivity.
Qed.

Lemma pass_nil : forall fuel width state, pass fuel width [] state = (Some [], state).
Proof. destruct fuel; reflexivity. Qed.

Theorem pass_preserves_occurrences : forall fuel width values state result final,
  pass fuel width values state = (Some result, final) ->
  Permutation values result.
Proof.
  induction fuel as [|fuel IH]; intros width [|x xs] state result final H;
    cbn [pass] in H; try (inversion H; subst; reflexivity); try discriminate.
  remember (x :: xs) as values in *.
  destruct (merge
    (length (firstn width values) + length (firstn width (skipn width values)))
    (firstn width values) (firstn width (skipn width values)) state)
    as [[run|] next] eqn:M; try discriminate.
  destruct (pass fuel width (skipn width (skipn width values)) next)
    as [[suffix|] last] eqn:P; cbn in H; try discriminate.
  inversion H; subst result final.
  rewrite <- (split_adjacent_runs width values).
  apply Permutation_app.
  - eapply merge_preserves_occurrences; exact M.
  - eapply IH; exact P.
Qed.

Lemma pass_has_sufficient_fuel :
  (forall x y state, exists decision next, compare x y state = (Some decision, next)) ->
  forall fuel width values state,
  0 < width -> length values <= fuel ->
  exists result final, pass fuel width values state = (Some result, final).
Proof.
  intros total fuel. induction fuel as [|fuel IH];
    intros width [|x xs] state W B;
    try (eexists; eexists; reflexivity); cbn [length] in B; try lia.
  cbn [pass]. remember (x :: xs) as values in *.
  destruct (merge_has_sufficient_fuel total
    (length (firstn width values) + length (firstn width (skipn width values)))
    (firstn width values) (firstn width (skipn width values)) state (Nat.le_refl _))
    as [run [next M]]. rewrite M.
  assert (T : length (skipn width (skipn width values)) <= fuel).
  { rewrite !length_skipn, Heqvalues. cbn [length]. lia. }
  destruct (IH width (skipn width (skipn width values)) next W T) as [tail [last P]].
  rewrite P. eexists; eexists; reflexivity.
Qed.

(** Alignment matters: every nonfinal run fills its width. Merely knowing
    that a list is a concatenation of short sorted runs would not justify the
    implementation's fixed firstn/skipn boundaries. *)
Inductive AlignedRuns (R : A -> A -> Prop) (width : nat) : list A -> Prop :=
| final_run : forall values,
    length values <= width -> StronglySorted R values -> AlignedRuns R width values
| complete_run : forall run tail,
    length run = width -> StronglySorted R run -> AlignedRuns R width tail ->
    AlignedRuns R width (run ++ tail).

Lemma take_complete_run : forall width (run tail : list A),
  length run = width -> firstn width (run ++ tail) = run.
Proof.
  intros width run tail L. rewrite <- L, firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma drop_complete_run : forall width (run tail : list A),
  length run = width -> skipn width (run ++ tail) = tail.
Proof.
  intros width run tail L. rewrite <- L, skipn_app, skipn_all, Nat.sub_diag.
  reflexivity.
Qed.

Lemma aligned_head_tail : forall R width values,
  AlignedRuns R width values ->
  StronglySorted R (firstn width values) /\ AlignedRuns R width (skipn width values).
Proof.
  intros R width values H. destruct H as [values B S | run tail L S T].
  - rewrite firstn_all2, skipn_all2 by exact B.
    split; [exact S | apply final_run; [cbn; lia | constructor]].
  - rewrite take_complete_run, drop_complete_run by exact L. split; assumption.
Qed.

Lemma aligned_small_is_sorted : forall R width values,
  AlignedRuns R width values -> length values <= width -> StronglySorted R values.
Proof.
  intros R width values H B. destruct H as [values _ S | run tail L S T].
  - exact S.
  - rewrite length_app, L in B.
    assert (tail = []) by (apply length_zero_iff_nil; lia).
    now rewrite H, app_nil_r.
Qed.

Lemma singleton_runs_are_aligned : forall R values, AlignedRuns R 1 values.
Proof.
  intros R values. induction values as [|x xs IH].
  - apply final_run; [cbn; lia | constructor].
  - change (AlignedRuns R 1 ([x] ++ xs)).
    apply complete_run; [reflexivity | constructor; constructor | exact IH].
Qed.

Theorem pass_doubles_sorted_run_width : forall (R : A -> A -> Prop),
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => R y x | _ => R x y end) ->
  forall fuel width values state result final,
  0 < width -> AlignedRuns R width values ->
  pass fuel width values state = (Some result, final) -> AlignedRuns R (2 * width) result.
Proof.
  intros R trans sound fuel. induction fuel as [|fuel IH];
    intros width [|x xs] state result final W aligned H;
    cbn [pass] in H;
    try (inversion H; subst; apply final_run; [cbn; lia | constructor]);
    try discriminate.
  remember (x :: xs) as values in *.
  destruct (merge
    (length (firstn width values) + length (firstn width (skipn width values)))
    (firstn width values) (firstn width (skipn width values)) state)
    as [[run|] next] eqn:M; try discriminate.
  destruct (pass fuel width (skipn width (skipn width values)) next)
    as [[suffix|] last] eqn:P; cbn in H; try discriminate.
  inversion H; subst result final.
  destruct (aligned_head_tail R width values aligned) as [SL AT].
  destruct (aligned_head_tail R width (skipn width values) AT) as [SR ATT].
  assert (S : StronglySorted R run).
  { eapply merge_sorted_runs; [exact trans | exact sound | exact SL | exact SR | exact M]. }
  assert (L : length (firstn width values) +
    length (firstn width (skipn width values)) = length run).
  { rewrite <- length_app. apply Permutation_length.
    eapply merge_preserves_occurrences; exact M. }
  destruct (Nat.le_gt_cases (length values) (2 * width)) as [short | full].
  - assert (T : skipn width (skipn width values) = []).
    { apply skipn_all2. rewrite length_skipn. lia. }
    rewrite T, pass_nil in P. inversion P; subst suffix last.
    rewrite app_nil_r. apply final_run; [| exact S].
    rewrite !length_firstn in L.
    pose proof (Nat.le_min_l width (length values)).
    pose proof (Nat.le_min_l width (length (skipn width values))). lia.
  - apply complete_run; [| exact S | eapply IH; eauto].
    rewrite !firstn_length_le in L; [lia | rewrite length_skipn; lia | lia].
Qed.

Fixpoint passes (fuel width : nat) (values : list A) (state : State)
    : option (list A) * State :=
  if length values <=? width then (Some values, state)
  else match fuel with
    | 0 => (None, state)
    | S smaller =>
        let '(result, next) := pass (length values) width values state in
        match result with
        | None => (None, next)
        | Some sorted_runs => passes smaller (2 * width) sorted_runs next
        end
    end.

Theorem passes_preserve_occurrences : forall fuel width values state result final,
  passes fuel width values state = (Some result, final) ->
  Permutation values result.
Proof.
  induction fuel as [|fuel IH]; intros width values state result final H;
    cbn [passes] in H; destruct (length values <=? width) eqn:B;
    try (inversion H; subst; reflexivity); try discriminate.
  destruct (pass (length values) width values state) as [[runs|] next] eqn:P;
    try discriminate.
  eapply Permutation_trans.
  - eapply pass_preserves_occurrences; exact P.
  - eapply IH; exact H.
Qed.

Theorem passes_finish_sorted : forall (R : A -> A -> Prop),
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => R y x | _ => R x y end) ->
  forall fuel width values state result final,
  0 < width -> AlignedRuns R width values ->
  passes fuel width values state = (Some result, final) -> StronglySorted R result.
Proof.
  intros R trans sound fuel. induction fuel as [|fuel IH];
    intros width values state result final W aligned H;
    cbn [passes] in H; destruct (length values <=? width) eqn:B;
    try (inversion H; subst; eapply aligned_small_is_sorted;
      [exact aligned | apply Nat.leb_le; exact B]); try discriminate.
  destruct (pass (length values) width values state) as [[runs|] next] eqn:P;
    try discriminate.
  eapply (IH (2 * width) runs next result final); [lia | | exact H].
  eapply pass_doubles_sorted_run_width;
    [exact trans | exact sound | exact W | exact aligned | exact P].
Qed.

Definition sort values state := passes (length values) 1 values state.

Theorem sort_is_sorted : forall (R : A -> A -> Prop),
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall x y state decision next,
    compare x y state = (Some decision, next) ->
    match decision with Gt => R y x | _ => R x y end) ->
  forall values state result final,
  sort values state = (Some result, final) -> StronglySorted R result.
Proof.
  intros R trans sound values state result final H.
  eapply (passes_finish_sorted R trans sound (length values) 1 values state result final);
    [lia | | exact H].
  apply singleton_runs_are_aligned.
Qed.

Lemma passes_have_sufficient_fuel :
  (forall x y state, exists decision next, compare x y state = (Some decision, next)) ->
  forall fuel width values state,
  0 < width -> length values <= width + fuel ->
  exists result final, passes fuel width values state = (Some result, final).
Proof.
  intros total fuel. induction fuel as [|fuel IH]; intros width values state W B;
    cbn [passes]; destruct (length values <=? width) eqn:C;
    try (eexists; eexists; reflexivity).
  - apply Nat.leb_gt in C. lia.
  - destruct (pass_has_sufficient_fuel total (length values) width values state W
      (Nat.le_refl _)) as [runs [next P]]. rewrite P.
    assert (L : length values = length runs).
    { apply Permutation_length. eapply pass_preserves_occurrences; exact P. }
    apply IH; lia.
Qed.

Theorem sort_termination_index_suffices :
  (forall x y state, exists decision next, compare x y state = (Some decision, next)) ->
  forall values state, exists result final, sort values state = (Some result, final).
Proof.
  intros total values state. unfold sort.
  apply passes_have_sufficient_fuel; auto; lia.
Qed.

Theorem sort_preserves_occurrences : forall values state result final,
  sort values state = (Some result, final) -> Permutation values result.
Proof. intros. eapply passes_preserve_occurrences; exact H. Qed.

Theorem sort_preserves_length : forall values state result final,
  sort values state = (Some result, final) -> length values = length result.
Proof. intros. apply Permutation_length. eapply sort_preserves_occurrences; exact H. Qed.

Theorem sort_preserves_each_multiplicity : forall
  (eq_dec : forall a b : A, {a = b} + {a <> b}) values state result final x,
  sort values state = (Some result, final) ->
  count_occ eq_dec values x = count_occ eq_dec result x.
Proof.
  intros. apply (proj1 (Permutation_count_occ eq_dec values result)).
  eapply sort_preserves_occurrences; exact H.
Qed.

Theorem sort_preserves_record_property : forall (bound : A -> Prop)
  values state result final,
  Forall bound values -> sort values state = (Some result, final) -> Forall bound result.
Proof.
  intros bound values state result final B H.
  eapply Permutation_Forall; [| exact B].
  eapply sort_preserves_occurrences; exact H.
Qed.

Theorem sort_preserves_projected_roster : forall (B : Type) (project : A -> B)
  values state result final,
  sort values state = (Some result, final) ->
  Permutation (map project values) (map project result).
Proof.
  intros. apply Permutation_map. eapply sort_preserves_occurrences; exact H.
Qed.

Definition has_key {K : Type} (key : A -> K) (order : K -> K -> comparison)
    (wanted : K) (value : A) :=
  match order (key value) wanted with Eq => true | _ => false end.

Lemma has_key_true : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  forall wanted value, has_key key order wanted value = true -> key value = wanted.
Proof.
  intros K key order eq_iff wanted value H. unfold has_key in H.
  destruct (order (key value) wanted) eqn:E; try discriminate.
  apply eq_iff; exact E.
Qed.

Lemma false_filter_is_empty : forall (predicate : A -> bool) values,
  Forall (fun value => predicate value = false) values -> filter predicate values = [].
Proof.
  intros predicate values H. induction H; [reflexivity |]. cbn. now rewrite H, IHForall.
Qed.

(** A strict right-head choice cannot jump over an equal-key left occurrence.
    This is precisely where sorted input and exact comparator agreement matter;
    the weaker non-strict merge_sorted_runs premise alone cannot prove stability. *)
Lemma strict_head_excludes_key : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  forall x xs y wanted,
  StronglySorted (fun a b => order (key a) (key b) <> Gt) (x :: xs) ->
  order (key x) (key y) = Gt -> has_key key order wanted y = true ->
  filter (has_key key order wanted) (x :: xs) = [].
Proof.
  intros K key order eq_iff x xs y wanted sorted strict matched.
  pose proof (has_key_true K key order eq_iff wanted y matched) as Y.
  destruct (StronglySorted_inv sorted) as [_ all].
  apply false_filter_is_empty. apply Forall_forall. intros z Z.
  destruct (has_key key order wanted z) eqn:M; [| reflexivity].
  pose proof (has_key_true K key order eq_iff wanted z M) as ZE.
  exfalso. destruct Z as [ZX | ZS].
  - subst z. rewrite ZE, Y in strict.
    assert (order wanted wanted = Eq) by (apply eq_iff; reflexivity). congruence.
  - rewrite Forall_forall in all. apply (all z ZS).
    rewrite ZE. now rewrite Y in strict.
Qed.

Theorem merge_preserves_equal_key_subsequence : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (key x) (key y) = decision) ->
  forall fuel left right state result final wanted,
  StronglySorted (fun a b => order (key a) (key b) <> Gt) left ->
  StronglySorted (fun a b => order (key a) (key b) <> Gt) right ->
  merge fuel left right state = (Some result, final) ->
  filter (has_key key order wanted) result =
    filter (has_key key order wanted) left ++ filter (has_key key order wanted) right.
Proof.
  intros K key order eq_iff faithful fuel. induction fuel as [|fuel IH];
    intros [|x xs] [|y ys] state result final wanted L B H;
    cbn [merge] in H;
    try (inversion H; subst; cbn [filter]; rewrite ?app_nil_r; reflexivity);
    try discriminate.
  destruct (StronglySorted_inv L) as [LX FX].
  destruct (StronglySorted_inv B) as [LY FY].
  destruct (compare x y state) as [[decision|] next] eqn:C; try discriminate.
  pose proof (faithful x y state decision next C) as order_heads.
  destruct decision.
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. cbn [filter].
    rewrite (IH xs (y :: ys) next rest _ wanted LX B M).
    cbn [filter]. destruct (has_key key order wanted x); reflexivity.
  - destruct (merge fuel xs (y :: ys) next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. cbn [filter].
    rewrite (IH xs (y :: ys) next rest _ wanted LX B M).
    cbn [filter]. destruct (has_key key order wanted x); reflexivity.
  - destruct (merge fuel (x :: xs) ys next) as [[rest|] last] eqn:M;
      cbn [prepend] in H; try discriminate.
    inversion H; subst. change
      ((if has_key key order wanted y then y :: filter (has_key key order wanted) rest
        else filter (has_key key order wanted) rest) =
       filter (has_key key order wanted) (x :: xs) ++
       (if has_key key order wanted y then y :: filter (has_key key order wanted) ys
        else filter (has_key key order wanted) ys)).
    rewrite (IH (x :: xs) ys next rest _ wanted L LY M).
    destruct (has_key key order wanted y) eqn:Y; [| reflexivity].
    rewrite (strict_head_excludes_key K key order eq_iff x xs y wanted L order_heads Y).
    reflexivity.
Qed.

Theorem pass_preserves_equal_key_subsequence : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (key x) (key y) = decision) ->
  forall fuel width values state result final wanted,
  AlignedRuns (fun a b => order (key a) (key b) <> Gt) width values ->
  pass fuel width values state = (Some result, final) ->
  filter (has_key key order wanted) result = filter (has_key key order wanted) values.
Proof.
  intros K key order eq_iff faithful fuel. induction fuel as [|fuel IH];
    intros width [|x xs] state result final wanted aligned H;
    cbn [pass] in H; try (inversion H; subst; reflexivity); try discriminate.
  remember (x :: xs) as values in *.
  destruct (merge
    (length (firstn width values) + length (firstn width (skipn width values)))
    (firstn width values) (firstn width (skipn width values)) state)
    as [[run|] next] eqn:M; try discriminate.
  destruct (pass fuel width (skipn width (skipn width values)) next)
    as [[suffix|] last] eqn:P; cbn in H; try discriminate.
  inversion H; subst result final.
  destruct (aligned_head_tail _ width values aligned) as [SL AT].
  destruct (aligned_head_tail _ width (skipn width values) AT) as [SR ATT].
  rewrite filter_app,
    (merge_preserves_equal_key_subsequence K key order eq_iff faithful
      _ _ _ state run next wanted SL SR M),
    (IH width _ next suffix _ wanted ATT P).
  rewrite <- !filter_app. f_equal. apply split_adjacent_runs.
Qed.

Lemma exact_key_comparison_is_sound : forall (K : Type) (key : A -> K) order,
  (forall x y, order y x = CompOpp (order x y)) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (key x) (key y) = decision) ->
  forall x y state decision next, compare x y state = (Some decision, next) ->
    match decision with
    | Gt => order (key y) (key x) <> Gt
    | _ => order (key x) (key y) <> Gt
    end.
Proof.
  intros K key order opposite faithful x y state decision next H.
  pose proof (faithful x y state decision next H) as C.
  destruct decision; try (rewrite C; discriminate).
  rewrite opposite, C. discriminate.
Qed.

Theorem passes_preserve_equal_key_subsequence : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y, order y x = CompOpp (order x y)) ->
  (forall x y z, order x y <> Gt -> order y z <> Gt -> order x z <> Gt) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (key x) (key y) = decision) ->
  forall fuel width values state result final wanted,
  0 < width -> AlignedRuns (fun a b => order (key a) (key b) <> Gt) width values ->
  passes fuel width values state = (Some result, final) ->
  filter (has_key key order wanted) result = filter (has_key key order wanted) values.
Proof.
  intros K key order eq_iff opposite trans faithful fuel.
  induction fuel as [|fuel IH];
    intros width values state result final wanted W aligned H;
    cbn [passes] in H; destruct (length values <=? width) eqn:B;
    try (inversion H; subst; reflexivity); try discriminate.
  destruct (pass (length values) width values state) as [[runs|] next] eqn:P;
    try discriminate.
  etransitivity.
  - eapply (IH (2 * width) runs next result final wanted); [lia | | exact H].
    eapply pass_doubles_sorted_run_width.
    + intros a b c. apply trans.
    + apply (exact_key_comparison_is_sound K key order opposite faithful).
    + exact W.
    + exact aligned.
    + exact P.
  - eapply pass_preserves_equal_key_subsequence;
      [exact eq_iff | exact faithful | exact aligned | exact P].
Qed.

Theorem sort_preserves_equal_key_subsequence : forall (K : Type) (key : A -> K) order,
  (forall x y, order x y = Eq <-> x = y) ->
  (forall x y, order y x = CompOpp (order x y)) ->
  (forall x y z, order x y <> Gt -> order y z <> Gt -> order x z <> Gt) ->
  (forall x y state decision next, compare x y state = (Some decision, next) ->
    order (key x) (key y) = decision) ->
  forall values state result final wanted,
  sort values state = (Some result, final) ->
  filter (has_key key order wanted) result = filter (has_key key order wanted) values.
Proof.
  intros K key order eq_iff opposite trans faithful values state result final wanted H.
  eapply (passes_preserve_equal_key_subsequence K key order eq_iff opposite trans faithful
    (length values) 1 values state result final wanted);
    [lia | apply singleton_runs_are_aligned | exact H].
Qed.

End Machine.
End SemanticResultMerge.

Print Assumptions SemanticResultMerge.merge_preserves_occurrences.
Print Assumptions SemanticResultMerge.refused_comparison_keeps_its_state.
Print Assumptions SemanticResultMerge.equal_heads_select_left.
Print Assumptions SemanticResultMerge.merge_has_sufficient_fuel.
Print Assumptions SemanticResultMerge.merge_sorted_runs.
Print Assumptions SemanticResultMerge.pass_preserves_occurrences.
Print Assumptions SemanticResultMerge.pass_has_sufficient_fuel.
Print Assumptions SemanticResultMerge.pass_doubles_sorted_run_width.
Print Assumptions SemanticResultMerge.passes_preserve_occurrences.
Print Assumptions SemanticResultMerge.passes_finish_sorted.
Print Assumptions SemanticResultMerge.sort_is_sorted.
Print Assumptions SemanticResultMerge.passes_have_sufficient_fuel.
Print Assumptions SemanticResultMerge.sort_termination_index_suffices.
Print Assumptions SemanticResultMerge.sort_preserves_occurrences.
Print Assumptions SemanticResultMerge.sort_preserves_length.
Print Assumptions SemanticResultMerge.sort_preserves_each_multiplicity.
Print Assumptions SemanticResultMerge.sort_preserves_record_property.
Print Assumptions SemanticResultMerge.sort_preserves_projected_roster.
Print Assumptions SemanticResultMerge.merge_preserves_equal_key_subsequence.
Print Assumptions SemanticResultMerge.pass_preserves_equal_key_subsequence.
Print Assumptions SemanticResultMerge.passes_preserve_equal_key_subsequence.
Print Assumptions SemanticResultMerge.sort_preserves_equal_key_subsequence.
