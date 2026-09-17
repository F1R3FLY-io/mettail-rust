(** Original occurrence indices for metadata-only comparison inspection.

    The operational state is a row/column cursor, not a Cartesian list. Lists
    below are proof-only suffix witnesses. Both directions and the diagonal
    are retained; neither pointer identity nor Bag repetition counts occur in
    this model. This supplies enumeration, not native callback cost authority.
    Mathematical increments correspond to checked/guarded usize operations
    only when the source dimensions are representable. *)
From Stdlib Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

Module GeneratedComparisonPairCursor.

Definition LocalCursor := option (nat * nat).
Definition local_valid rows cols cursor := match cursor with
  | None => True
  | Some (row, col) => row < rows /\ col < cols end.
Definition local_start rows cols : LocalCursor :=
  if (0 <? rows) && (0 <? cols) then Some (0, 0) else None.
Definition local_next rows cols row col : LocalCursor :=
  if S col <? cols then Some (row, S col)
  else if S row <? rows then Some (S row, 0) else None.
Definition local_word rows cols cursor := match cursor with
  | None => []
  | Some (row, col) =>
      map (pair row) (seq col (cols - col)) ++
      list_prod (seq (S row) (rows - S row)) (seq 0 cols)
  end.

Lemma product_empty_right : forall (rows : list nat), @list_prod nat nat rows [] = [].
Proof. induction rows; cbn; assumption || reflexivity. Qed.

Theorem local_start_is_valid : forall rows cols,
  local_valid rows cols (local_start rows cols).
Proof.
  intros rows cols. unfold local_start.
  destruct (0 <? rows) eqn:R; destruct (0 <? cols) eqn:C; cbn; try exact I.
  apply Nat.ltb_lt in R, C. split; assumption.
Qed.

Theorem local_start_word_is_the_original_cartesian_product : forall rows cols,
  local_word rows cols (local_start rows cols) =
  list_prod (seq 0 rows) (seq 0 cols).
Proof.
  intros rows cols. unfold local_start.
  destruct (0 <? rows) eqn:R; destruct (0 <? cols) eqn:C; cbn [andb].
  - apply Nat.ltb_lt in R, C.
    destruct rows as [|rows]; [lia|]. destruct cols as [|cols]; [lia|].
    unfold local_word. rewrite Nat.sub_0_r.
    replace (S rows - 1) with rows by lia. reflexivity.
  - apply Nat.ltb_ge in C. assert (cols = 0) by lia. subst cols.
    cbn [local_word seq]. symmetry. apply product_empty_right.
  - apply Nat.ltb_ge in R. assert (rows = 0) by lia. now subst rows.
  - apply Nat.ltb_ge in R. assert (rows = 0) by lia. now subst rows.
Qed.

Theorem original_cursor_increments_remain_bounded : forall rows cols row col,
  row < rows -> col < cols ->
  S row <= rows /\ S col <= cols /\
  local_valid rows cols (local_next rows cols row col).
Proof.
  intros rows cols row col R C. split; [lia|]. split; [lia|].
  unfold local_next. destruct (S col <? cols) eqn:COL.
  - apply Nat.ltb_lt in COL. split; assumption.
  - destruct (S row <? rows) eqn:ROW; [|exact I].
    apply Nat.ltb_lt in ROW. split; lia.
Qed.

Theorem local_next_removes_exactly_the_original_head : forall rows cols row col,
  row < rows -> col < cols ->
  local_word rows cols (Some (row, col)) =
  (row, col) :: local_word rows cols (local_next rows cols row col).
Proof.
  intros rows cols row col R C.
  assert (WIDTH : cols - col = S (cols - S col)) by lia.
  unfold local_next. destruct (S col <? cols) eqn:COL.
  - cbn [local_word]. rewrite WIDTH. reflexivity.
  - apply Nat.ltb_ge in COL. assert (ENDCOL : S col = cols) by lia.
    destruct (S row <? rows) eqn:ROW.
    + apply Nat.ltb_lt in ROW.
      assert (HEIGHT : rows - S row = S (rows - S (S row))) by lia.
      cbn [local_word]. rewrite WIDTH, <- ENDCOL, Nat.sub_diag.
      cbn [seq map app]. rewrite HEIGHT. cbn [seq list_prod].
      now rewrite Nat.sub_0_r.
    + apply Nat.ltb_ge in ROW.
      assert (ENDROW : rows - S row = 0) by lia.
      cbn [local_word]. rewrite WIDTH, <- ENDCOL, Nat.sub_diag, ENDROW.
      reflexivity.
Qed.

Inductive LocalRun rows cols : LocalCursor -> list (nat * nat) -> Prop :=
| LocalDone : LocalRun rows cols None []
| LocalEmit : forall row col rest,
    row < rows -> col < cols ->
    LocalRun rows cols (local_next rows cols row col) rest ->
    LocalRun rows cols (Some (row, col)) ((row, col) :: rest).

Theorem every_completed_local_run_has_exact_original_order : forall rows cols cursor output,
  LocalRun rows cols cursor output -> output = local_word rows cols cursor.
Proof.
  intros rows cols cursor output RUN. induction RUN; [reflexivity|].
  rewrite (local_next_removes_exactly_the_original_head rows cols row col H H0).
  now rewrite IHRUN.
Qed.

Lemma local_run_exists_by_remaining_length : forall fuel rows cols cursor,
  local_valid rows cols cursor -> length (local_word rows cols cursor) <= fuel ->
  exists output, LocalRun rows cols cursor output.
Proof.
  induction fuel as [|fuel IH]; intros rows cols [[row col]|] VALID LEN.
  - destruct VALID as [R C].
    rewrite (local_next_removes_exactly_the_original_head rows cols row col R C) in LEN.
    cbn [length] in LEN. lia.
  - exists []. constructor.
  - destruct VALID as [R C].
    pose proof (original_cursor_increments_remain_bounded rows cols row col R C)
      as [_ [_ NEXT]].
    rewrite (local_next_removes_exactly_the_original_head rows cols row col R C) in LEN.
    cbn [length] in LEN.
    destruct (IH rows cols (local_next rows cols row col) NEXT ltac:(lia)) as [rest RUN].
    exists ((row, col) :: rest). now constructor.
  - exists []. constructor.
Qed.

Theorem original_pair_enumeration_finishes : forall rows cols,
  LocalRun rows cols (local_start rows cols)
    (list_prod (seq 0 rows) (seq 0 cols)).
Proof.
  intros rows cols.
  destruct (local_run_exists_by_remaining_length
    (length (local_word rows cols (local_start rows cols))) rows cols
    (local_start rows cols) (local_start_is_valid rows cols) ltac:(lia)) as [output RUN].
  pose proof (every_completed_local_run_has_exact_original_order _ _ _ _ RUN) as SAME.
  rewrite local_start_word_is_the_original_cartesian_product in SAME.
  now subst output.
Qed.

Theorem original_pairs_have_both_directions_and_diagonals : forall rows cols row col,
  In (row, col) (list_prod (seq 0 rows) (seq 0 cols)) <-> row < rows /\ col < cols.
Proof. intros. rewrite in_prod_iff, !in_seq. lia. Qed.

Lemma injective_map_has_no_duplicates : forall (A B : Type) (f : A -> B) values,
  (forall x y, f x = f y -> x = y) -> NoDup values -> NoDup (map f values).
Proof.
  intros A B f values INJECTIVE NODUP. induction NODUP; cbn; constructor.
  - intro MEMBER. apply in_map_iff in MEMBER. destruct MEMBER as [y [SAME MEMBER]].
    apply INJECTIVE in SAME. now subst.
  - assumption.
Qed.

Lemma original_product_has_no_duplicates : forall (rows cols : list nat),
  NoDup rows -> NoDup cols -> NoDup (list_prod rows cols).
Proof.
  intros rows cols ROWS COLS. induction ROWS; cbn; [constructor|].
  apply NoDup_app.
  - apply injective_map_has_no_duplicates; [intros; congruence|exact COLS].
  - exact IHROWS.
  - intros [row col] MEMBER OTHER.
    apply in_map_iff in MEMBER. destruct MEMBER as [value [SAME _]]. inversion SAME; subst.
    apply in_prod_iff in OTHER. apply H. exact (proj1 OTHER).
Qed.

Theorem every_original_index_pair_occurs_once : forall rows cols,
  NoDup (list_prod (seq 0 rows) (seq 0 cols)).
Proof. intros. apply original_product_has_no_duplicates; apply seq_NoDup. Qed.

Inductive Family := LeftSort | RightSort | CrossLex.
Definition dimensions (left right : nat) family := match family with
  | LeftSort => (left, left) | RightSort => (right, right) | CrossLex => (left, right) end.
Definition factor left right family := match family with
  | LeftSort => left * (left - 1)
  | RightSort => right * (right - 1)
  | CrossLex => left + right end.
Definition family_start left right family :=
  let '(rows, cols) := dimensions left right family in
  if factor left right family =? 0 then None else local_start rows cols.

Definition following family := match family with
  | LeftSort => [RightSort; CrossLex]
  | RightSort => [CrossLex]
  | CrossLex => [] end.
Definition families := [LeftSort; RightSort; CrossLex].
Definition Item := (Family * (nat * nat))%type.
Definition Cursor := option Item.
Definition family_word left right family :=
  let '(rows, cols) := dimensions left right family in
  map (pair family) (local_word rows cols (family_start left right family)).
Definition family_words left right phases := flat_map (family_word left right) phases.

(** This recursion is over at most THREE fixed family labels. It describes
    enum transitions; no suffix list is stored or allocated by the source. *)
Fixpoint seek left right phases : Cursor := match phases with
  | [] => None
  | family :: rest => match family_start left right family with
    | Some indices => Some (family, indices)
    | None => seek left right rest end end.
Definition start left right := seek left right families.
Definition next left right family row col : Cursor :=
  let '(rows, cols) := dimensions left right family in
  match local_next rows cols row col with
  | Some indices => Some (family, indices)
  | None => seek left right (following family) end.
Definition valid left right cursor := match cursor with
  | None => True
  | Some (family, (row, col)) =>
      let '(rows, cols) := dimensions left right family in
      0 < factor left right family /\ row < rows /\ col < cols end.
Definition word left right cursor := match cursor with
  | None => []
  | Some (family, indices) =>
      let '(rows, cols) := dimensions left right family in
      map (pair family) (local_word rows cols (Some indices)) ++
      family_words left right (following family) end.

Inductive FamilyChain : list Family -> Prop :=
| ChainDone : FamilyChain []
| ChainMore : forall family rest,
    rest = following family -> FamilyChain rest -> FamilyChain (family :: rest).
Lemma following_is_a_fixed_chain : forall family, FamilyChain (following family).
Proof.
  intros []; cbn [following]; repeat (eapply ChainMore; [reflexivity|]); constructor.
Qed.
Lemma initial_families_are_a_fixed_chain : FamilyChain families.
Proof. apply ChainMore; [reflexivity|exact (following_is_a_fixed_chain LeftSort)]. Qed.

Lemma family_start_is_valid : forall left right family indices,
  family_start left right family = Some indices -> valid left right (Some (family, indices)).
Proof.
  intros left right family [row col] START.
  unfold family_start in START. unfold valid.
  destruct (dimensions left right family) as [rows cols].
  destruct (factor left right family =? 0) eqn:FACTOR; [discriminate|].
  apply Nat.eqb_neq in FACTOR.
  pose proof (local_start_is_valid rows cols) as VALID. rewrite START in VALID.
  cbn [local_valid] in VALID. split; [lia|exact VALID].
Qed.

Lemma seek_is_valid : forall left right phases, valid left right (seek left right phases).
Proof.
  intros left right phases. induction phases as [|family rest IH]; [exact I|].
  cbn [seek]. destruct (family_start left right family) as [indices|] eqn:START;
    [now apply family_start_is_valid|exact IH].
Qed.

Lemma skipped_families_preserve_the_exact_word : forall left right phases,
  FamilyChain phases -> word left right (seek left right phases) = family_words left right phases.
Proof.
  intros left right phases CHAIN. induction CHAIN as [|family rest REST CHAIN IH].
  - reflexivity.
  - cbn [seek family_words flat_map].
    unfold family_word at 1. destruct (dimensions left right family) as [rows cols] eqn:DIM.
    destruct (family_start left right family) as [indices|] eqn:START.
    + cbn [word]. rewrite DIM, REST. reflexivity.
    + cbn [local_word map app]. exact IH.
Qed.

Theorem next_preserves_valid_original_indices : forall left right family row col,
  valid left right (Some (family, (row, col))) ->
  valid left right (next left right family row col).
Proof.
  intros left right family row col VALID. unfold next, valid in *.
  destruct (dimensions left right family) as [rows cols] eqn:DIM.
  destruct VALID as [FACTOR [ROW COL]].
  pose proof (original_cursor_increments_remain_bounded rows cols row col ROW COL)
    as [_ [_ NEXT]].
  destruct (local_next rows cols row col) as [[r c]|] eqn:STEP.
  - rewrite DIM. split; [exact FACTOR|exact NEXT].
  - apply seek_is_valid.
Qed.

Theorem next_consumes_one_original_tagged_occurrence : forall left right family row col,
  valid left right (Some (family, (row, col))) ->
  word left right (Some (family, (row, col))) =
    (family, (row, col)) :: word left right (next left right family row col).
Proof.
  intros left right family row col VALID.
  unfold valid in VALID. destruct (dimensions left right family) as [rows cols] eqn:DIM.
  destruct VALID as [FACTOR [ROW COL]].
  unfold next. rewrite DIM. unfold word at 1. rewrite DIM.
  rewrite (local_next_removes_exactly_the_original_head rows cols row col ROW COL).
  destruct (local_next rows cols row col) as [indices|] eqn:STEP.
  - cbn [map app]. unfold word. now rewrite DIM.
  - cbn [local_word map app]. f_equal. symmetry.
    apply skipped_families_preserve_the_exact_word, following_is_a_fixed_chain.
Qed.

Inductive Run left right : Cursor -> list Item -> Prop :=
| Finished : Run left right None []
| Emitted : forall family row col rest,
    valid left right (Some (family, (row, col))) ->
    Run left right (next left right family row col) rest ->
    Run left right (Some (family, (row, col))) ((family, (row, col)) :: rest).

Theorem completed_cursor_enumerates_its_exact_remaining_word : forall left right cursor output,
  Run left right cursor output -> output = word left right cursor.
Proof.
  intros left right cursor output RUN. induction RUN; [reflexivity|].
  rewrite (next_consumes_one_original_tagged_occurrence _ _ _ _ _ H).
  now rewrite IHRUN.
Qed.

Lemma run_exists_by_remaining_length : forall fuel left right cursor,
  valid left right cursor -> length (word left right cursor) <= fuel ->
  exists output, Run left right cursor output.
Proof.
  induction fuel as [|fuel IH]; intros left right [[family [row col]]|] VALID LEN.
  - rewrite (next_consumes_one_original_tagged_occurrence _ _ _ _ _ VALID) in LEN.
    cbn [length] in LEN. lia.
  - exists []. constructor.
  - rewrite (next_consumes_one_original_tagged_occurrence _ _ _ _ _ VALID) in LEN.
    cbn [length] in LEN.
    destruct (IH left right (next left right family row col)
      (next_preserves_valid_original_indices _ _ _ _ _ VALID) ltac:(lia)) as [rest RUN].
    exists ((family, (row, col)) :: rest). now constructor.
  - exists []. constructor.
Qed.

Theorem all_three_families_finish_in_original_order : forall left right,
  Run left right (start left right) (family_words left right families).
Proof.
  intros left right.
  destruct (run_exists_by_remaining_length (length (word left right (start left right)))
    left right (start left right) (seek_is_valid _ _ _) ltac:(lia)) as [output RUN].
  pose proof (completed_cursor_enumerates_its_exact_remaining_word _ _ _ _ RUN) as SAME.
  unfold start in SAME.
  rewrite skipped_families_preserve_the_exact_word in SAME
    by apply initial_families_are_a_fixed_chain.
  now subst output.
Qed.

Lemma family_word_is_its_unexpanded_product : forall left right family,
  family_word left right family =
  if factor left right family =? 0 then [] else
    let '(rows, cols) := dimensions left right family in
    map (pair family) (list_prod (seq 0 rows) (seq 0 cols)).
Proof.
  intros. unfold family_word, family_start.
  destruct (dimensions left right family) as [rows cols].
  destruct (factor left right family =? 0); [reflexivity|].
  now rewrite local_start_word_is_the_original_cartesian_product.
Qed.

Lemma family_members_keep_their_label : forall left right family item,
  In item (family_word left right family) -> fst item = family.
Proof.
  intros left right family item MEMBER. unfold family_word in MEMBER.
  destruct (dimensions left right family) as [rows cols].
  apply in_map_iff in MEMBER. destruct MEMBER as [indices [SAME _]]. now subst.
Qed.

Lemma each_family_has_no_duplicate_indices : forall left right family,
  NoDup (family_word left right family).
Proof.
  intros. rewrite family_word_is_its_unexpanded_product.
  destruct (factor left right family =? 0); [constructor|].
  destruct (dimensions left right family) as [rows cols].
  apply injective_map_has_no_duplicates; [intros; congruence|].
  apply every_original_index_pair_occurs_once.
Qed.

Lemma family_words_have_no_duplicates : forall left right phases,
  NoDup phases -> NoDup (family_words left right phases).
Proof.
  intros left right phases NODUP. induction NODUP; cbn [family_words flat_map]; [constructor|].
  apply NoDup_app.
  - apply each_family_has_no_duplicate_indices.
  - exact IHNODUP.
  - intros item FIRST OTHER. apply in_flat_map in OTHER.
    destruct OTHER as [family [MEMBER INWORD]].
    pose proof (family_members_keep_their_label _ _ _ _ FIRST) as ONE.
    pose proof (family_members_keep_their_label _ _ _ _ INWORD) as TWO.
    apply H. replace x with family by congruence. exact MEMBER.
Qed.

Theorem all_three_families_have_no_duplicate_index_pairs : forall left right,
  NoDup (family_words left right families).
Proof.
  intros. apply family_words_have_no_duplicates. unfold families.
  repeat constructor; cbn; intuition discriminate.
Qed.

Theorem demanded_family_membership_is_exact : forall left right family row col,
  In (family, (row, col)) (family_words left right families) <->
  0 < factor left right family /\
  let '(rows, cols) := dimensions left right family in row < rows /\ col < cols.
Proof.
  intros left right family row col. unfold family_words. rewrite in_flat_map.
  split.
  - intros [selected [MEMBER PAIR]].
    pose proof (family_members_keep_their_label _ _ _ _ PAIR) as LABEL.
    cbn in LABEL. subst selected. rewrite family_word_is_its_unexpanded_product in PAIR.
    destruct (factor left right family =? 0) eqn:FACTOR; [contradiction|].
    apply Nat.eqb_neq in FACTOR. split; [lia|].
    destruct (dimensions left right family) as [rows cols].
    apply in_map_iff in PAIR. destruct PAIR as [indices [SAME ORIGINAL]].
    inversion SAME; subst. now apply original_pairs_have_both_directions_and_diagonals in ORIGINAL.
  - intros [FACTOR PAIR]. exists family. split.
    + destruct family; unfold families; cbn; auto.
    + rewrite family_word_is_its_unexpanded_product.
      assert (ACTIVE : (factor left right family =? 0) = false) by (apply Nat.eqb_neq; lia).
      rewrite ACTIVE. destruct (dimensions left right family) as [rows cols].
      apply in_map. now apply original_pairs_have_both_directions_and_diagonals.
Qed.

Theorem original_factor_labels_are_exact : forall left right,
  factor left right LeftSort = left * (left - 1) /\
  factor left right RightSort = right * (right - 1) /\
  factor left right CrossLex = left + right.
Proof. intros. repeat split; reflexivity. Qed.

Print Assumptions local_start_is_valid.
Print Assumptions local_start_word_is_the_original_cartesian_product.
Print Assumptions original_cursor_increments_remain_bounded.
Print Assumptions local_next_removes_exactly_the_original_head.
Print Assumptions every_completed_local_run_has_exact_original_order.
Print Assumptions original_pair_enumeration_finishes.
Print Assumptions original_pairs_have_both_directions_and_diagonals.
Print Assumptions every_original_index_pair_occurs_once.
Print Assumptions next_preserves_valid_original_indices.
Print Assumptions next_consumes_one_original_tagged_occurrence.
Print Assumptions completed_cursor_enumerates_its_exact_remaining_word.
Print Assumptions all_three_families_finish_in_original_order.
Print Assumptions all_three_families_have_no_duplicate_index_pairs.
Print Assumptions demanded_family_membership_is_exact.
Print Assumptions original_factor_labels_are_exact.
End GeneratedComparisonPairCursor.
