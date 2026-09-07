(*
 * Streaming Cartesian coordinates for retained semantic families.
 * Bounds and coordinates are in source order; the rightmost index changes
 * fastest. The denotation is an ordered list, not a set: equal values and
 * repeated occurrences must retain their positions. Cardinalities are ghost
 * mathematics only; an implementation need not multiply the row lengths.
 *
 * This file specifies the odometer successor and the exact unexamined suffix.
 * It does not certify forest-family completeness or change parser ranking.
 *)
From Stdlib Require Import List Arith Lia.
From PrattailWpdaRuntime Require Import CollectionItemKBestLifting.
Import ListNotations.
Set Implicit Arguments.

Definition valid_coordinate (bounds indices : list nat) : Prop :=
  Forall2 (fun bound index => index < bound) bounds indices.

Fixpoint successor (bounds indices : list nat) : option (list nat) :=
  match bounds, indices with
  | bound :: bounds, index :: indices =>
      match successor bounds indices with
      | Some next => Some (index :: next)
      | None => if S index <? bound
          then Some (S index :: repeat 0 (length bounds)) else None
      end
  | _, _ => None
  end.

(* Current coordinate followed by every later coordinate in source order. *)
Fixpoint remaining (bounds indices : list nat) : list (list nat) :=
  match bounds, indices with
  | [], [] => [[]]
  | bound :: bounds, index :: indices =>
      map (cons index) (remaining bounds indices) ++
      flat_map (fun next => map (cons next) (coordinate_product bounds))
        (seq (S index) (bound - S index))
  | _, _ => []
  end.

Lemma valid_bounds_positive : forall bounds indices,
  valid_coordinate bounds indices -> Forall (fun bound => 0 < bound) bounds.
Proof.
  intros bounds indices H. induction H; constructor; auto; lia.
Qed.

Lemma zero_coordinate_valid : forall bounds,
  Forall (fun bound => 0 < bound) bounds ->
  valid_coordinate bounds (repeat 0 (length bounds)).
Proof.
  intros bounds H. induction H; cbn; constructor; assumption.
Qed.

Theorem initial_remaining_is_full_product : forall bounds,
  Forall (fun bound => 0 < bound) bounds ->
  remaining bounds (repeat 0 (length bounds)) = coordinate_product bounds.
Proof.
  intros bounds H. induction H as [|bound bounds Hpositive Hbounds IH].
  - reflexivity.
  - destruct bound as [|bound]; [lia |].
    cbn [length repeat remaining coordinate_product].
    rewrite IH. replace (S bound - 1) with bound by lia. reflexivity.
Qed.

(* Initialization distinguishes an empty row (no coordinates) from zero
   rows (one empty coordinate). It scans row lengths without multiplying
   them; the mathematical product below is only a specification. *)
Definition initial_cursor (bounds : list nat) : option (list nat) :=
  if forallb (Nat.ltb 0) bounds
  then Some (repeat 0 (length bounds)) else None.

Lemma positive_bounds_boolean : forall bounds,
  forallb (Nat.ltb 0) bounds = true ->
  Forall (fun bound => 0 < bound) bounds.
Proof.
  intros bounds H. rewrite forallb_forall in H. apply Forall_forall.
  intros bound Hin. apply Nat.ltb_lt. now apply H.
Qed.

Lemma empty_coordinate_tail_annihilates_product : forall bound bounds,
  coordinate_product bounds = [] -> coordinate_product (bound :: bounds) = [].
Proof.
  intros bound bounds H. cbn [coordinate_product]. rewrite H.
  induction (seq 0 bound); cbn; assumption || reflexivity.
Qed.

Lemma empty_row_has_no_coordinates : forall bounds,
  forallb (Nat.ltb 0) bounds = false -> coordinate_product bounds = [].
Proof.
  induction bounds as [|[|bound] bounds IH]; cbn [forallb Nat.ltb].
  - discriminate.
  - reflexivity.
  - intro H. apply empty_coordinate_tail_annihilates_product. now apply IH.
Qed.

Theorem initialization_denotes_the_complete_coordinate_product : forall bounds,
  match initial_cursor bounds with
  | Some indices => valid_coordinate bounds indices /\
      remaining bounds indices = coordinate_product bounds
  | None => coordinate_product bounds = []
  end.
Proof.
  intro bounds. unfold initial_cursor.
  destruct (forallb (Nat.ltb 0) bounds) eqn:H.
  - apply positive_bounds_boolean in H. split.
    + now apply zero_coordinate_valid.
    + now apply initial_remaining_is_full_product.
  - now apply empty_row_has_no_coordinates.
Qed.

Example empty_row_and_zero_rows_are_distinct :
  initial_cursor [2; 0; 2] = None /\ initial_cursor [] = Some [].
Proof. split; reflexivity. Qed.

Theorem successor_keeps_coordinates_in_bounds : forall bounds indices next,
  valid_coordinate bounds indices -> successor bounds indices = Some next ->
  valid_coordinate bounds next.
Proof.
  intros bounds indices next Hvalid. revert next.
  induction Hvalid as [|bound index bounds indices Hindex Htail IH];
    intros next Hnext; cbn [successor] in Hnext; [discriminate |].
  destruct (successor bounds indices) as [tail|] eqn:E.
  - inversion Hnext; subst. constructor; [exact Hindex | now apply IH].
  - destruct (S index <? bound) eqn:Hbound; [|discriminate].
    inversion Hnext; subst. constructor.
    + now apply Nat.ltb_lt.
    + apply zero_coordinate_valid. now apply (valid_bounds_positive Htail).
Qed.

(* This equality is stronger than membership or strict rank increase: no
   intermediate coordinate can be skipped by a carry. *)
Theorem successor_removes_exactly_the_current_coordinate : forall bounds indices,
  valid_coordinate bounds indices ->
  remaining bounds indices = indices ::
    match successor bounds indices with
    | Some next => remaining bounds next
    | None => []
    end.
Proof.
  intros bounds indices Hvalid.
  induction Hvalid as [|bound index bounds indices Hindex Htail IH].
  - reflexivity.
  - cbn [remaining successor]. rewrite IH.
    destruct (successor bounds indices) as [next|] eqn:E.
    + cbn [map app]. reflexivity.
    + cbn [map app]. f_equal.
      destruct (S index <? bound) eqn:Hbound.
      * apply Nat.ltb_lt in Hbound.
        assert (Hcount : bound - S index = S (bound - S (S index))) by lia.
        rewrite Hcount. cbn [seq flat_map].
        change (map (cons (S index)) (coordinate_product bounds) ++
          flat_map (fun n => map (cons n) (coordinate_product bounds))
            (seq (S (S index)) (bound - S (S index))) =
          remaining (bound :: bounds) (S index :: repeat 0 (length bounds))).
        cbn [remaining].
        rewrite initial_remaining_is_full_product.
        -- reflexivity.
        -- now apply (valid_bounds_positive Htail).
      * apply Nat.ltb_ge in Hbound.
        replace (bound - S index) with 0 by lia. reflexivity.
Qed.

Corollary successor_none_means_last_coordinate : forall bounds indices,
  valid_coordinate bounds indices -> successor bounds indices = None ->
  remaining bounds indices = [indices].
Proof.
  intros bounds indices Hvalid Hdone.
  rewrite (successor_removes_exactly_the_current_coordinate Hvalid), Hdone.
  reflexivity.
Qed.

Corollary successor_strictly_decreases_remaining_work : forall bounds indices next,
  valid_coordinate bounds indices -> successor bounds indices = Some next ->
  length (remaining bounds next) < length (remaining bounds indices).
Proof.
  intros bounds indices next Hvalid Hnext.
  rewrite (successor_removes_exactly_the_current_coordinate Hvalid), Hnext.
  cbn. lia.
Qed.

Example two_shared_two_choice_occurrences_have_four_coordinates :
  remaining [2; 2] [0; 0] = [[0; 0]; [0; 1]; [1; 0]; [1; 1]].
Proof. reflexivity. Qed.

Example zero_dimensions_have_one_empty_coordinate :
  remaining [] [] = [[]] /\ successor [] [] = None.
Proof. split; reflexivity. Qed.

(* Operational carry loop. Unvisited pairs are right-to-left; reset_suffix
   represents the digits already set to zero by the in-place Rust loop. A
   carry consumes one pair, so length unvisited is its termination measure.
   rev/map/append specify the resulting vector, not runtime allocation. *)
Fixpoint carry_loop (unvisited : list (nat * nat)) (reset_suffix : list nat)
  : option (list nat) :=
  match unvisited with
  | [] => None
  | (bound, index) :: rest =>
      if S index <? bound then
        Some (rev (map snd rest) ++ S index :: reset_suffix)
      else carry_loop rest (0 :: reset_suffix)
  end.

Lemma zero_suffix_snoc : forall count,
  repeat 0 count ++ [0] = 0 :: repeat 0 count.
Proof. induction count; cbn; [reflexivity|now rewrite IHcount]. Qed.

Lemma carry_loop_append : forall first rest reset_suffix,
  carry_loop (first ++ rest) reset_suffix =
  match carry_loop first reset_suffix with
  | Some digits => Some (rev (map snd rest) ++ digits)
  | None => carry_loop rest (repeat 0 (length first) ++ reset_suffix)
  end.
Proof.
  induction first as [|[bound index] first IH]; intros rest reset_suffix; cbn [app carry_loop length].
  - reflexivity.
  - destruct (S index <? bound).
    + rewrite map_app, rev_app_distr, app_assoc. reflexivity.
    + rewrite IH. destruct (carry_loop first (0 :: reset_suffix)); [reflexivity|].
      replace (repeat 0 (length first) ++ 0 :: reset_suffix) with
        (repeat 0 (S (length first)) ++ reset_suffix).
      * reflexivity.
      * change ((0 :: repeat 0 (length first)) ++ reset_suffix =
          repeat 0 (length first) ++ [0] ++ reset_suffix).
        rewrite app_assoc, zero_suffix_snoc. reflexivity.
Qed.

Lemma valid_coordinate_zip_length : forall bounds indices,
  valid_coordinate bounds indices -> length (combine bounds indices) = length bounds.
Proof.
  intros bounds indices H. induction H; cbn; [reflexivity|now rewrite IHForall2].
Qed.

Theorem iterative_carry_refines_source_order_successor : forall bounds indices,
  valid_coordinate bounds indices ->
  carry_loop (rev (combine bounds indices)) [] = successor bounds indices.
Proof.
  intros bounds indices H.
  induction H as [|bound index bounds indices Hindex Htail IH]; cbn [combine rev successor].
  - reflexivity.
  - rewrite carry_loop_append, IH.
    destruct (successor bounds indices) as [next|] eqn:E.
    + reflexivity.
    + rewrite length_rev, (valid_coordinate_zip_length Htail), app_nil_r.
      cbn [carry_loop map rev app]. destruct (S index <? bound); reflexivity.
Qed.

(* A machine implementation tests before incrementing. In particular, it must
   not compute index + 1 while deciding whether a maximal digit can carry.
   Positive row bounds are established by initialization, not assumed by an
   unchecked runtime subtraction. The finite maximum is left parametric. *)
Theorem guarded_increment_has_the_same_successor_condition : forall bound index,
  0 < bound -> (index <? bound - 1) = (S index <? bound).
Proof.
  intros bound index Hpositive.
  destruct (index <? bound - 1) eqn:Hguard,
    (S index <? bound) eqn:Hsuccessor; try reflexivity;
    apply Nat.ltb_lt in Hguard || apply Nat.ltb_ge in Hguard;
    apply Nat.ltb_lt in Hsuccessor || apply Nat.ltb_ge in Hsuccessor; lia.
Qed.

Theorem guarded_increment_stays_within_the_machine_bound : forall maximum bound index,
  0 < bound -> bound <= maximum -> index < bound - 1 ->
  S index < bound /\ S index <= maximum.
Proof. intros; lia. Qed.

Print Assumptions initial_remaining_is_full_product.
Print Assumptions initialization_denotes_the_complete_coordinate_product.
Print Assumptions successor_keeps_coordinates_in_bounds.
Print Assumptions successor_removes_exactly_the_current_coordinate.
Print Assumptions successor_strictly_decreases_remaining_work.
Print Assumptions iterative_carry_refines_source_order_successor.
Print Assumptions guarded_increment_has_the_same_successor_condition.
Print Assumptions guarded_increment_stays_within_the_machine_bound.

(* Decode coordinates as an ordered list, not merely a membership relation.
   Distinct occurrence coordinates may select equal values; neither order nor
   multiplicity is discarded by this bridge to the retained semantic family. *)
Lemma cursor_flat_map_map : forall (A B C : Type) (f : B -> list C) (g : A -> B) xs,
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof.
  intros. rewrite !flat_map_concat_map, map_map. reflexivity.
Qed.

Lemma cursor_flat_map_flat_map : forall (A B C : Type)
  (f : B -> list C) (g : A -> list B) xs,
  flat_map f (flat_map g xs) = flat_map (fun x => flat_map f (g x)) xs.
Proof.
  intros A B C f g xs. induction xs; cbn; [reflexivity|].
  now rewrite flat_map_app, IHxs.
Qed.

Lemma cursor_map_flat_map : forall (A B C : Type)
  (f : B -> C) (g : A -> list B) xs,
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof.
  intros A B C f g xs. induction xs; cbn; [reflexivity|].
  now rewrite map_app, IHxs.
Qed.

Lemma row_index_flat_map : forall (A B : Type) (row : list A) (f : A -> list B),
  flat_map (fun index => match nth_error row index with
    | Some value => f value | None => [] end) (seq 0 (length row)) = flat_map f row.
Proof.
  intros A B row f. induction row as [|value row IH]; cbn; [reflexivity|].
  rewrite <- seq_shift, cursor_flat_map_map. cbn. now rewrite IH.
Qed.

Section CoordinateDecoding.
  Context {Value : Type}.

  Definition decode_coordinate (families : list (list Value)) (indices : list nat)
    : list (list Value) :=
    match select_coordinate families indices with Some values => [values] | None => [] end.

  Lemma decode_coordinate_cons : forall row rest index suffix,
    decode_coordinate (row :: rest) (index :: suffix) =
      match nth_error row index with
      | Some value => map (cons value) (decode_coordinate rest suffix)
      | None => []
      end.
  Proof.
    intros. unfold decode_coordinate; cbn [select_coordinate].
    destruct (nth_error row index), (select_coordinate rest suffix); reflexivity.
  Qed.

  Lemma decode_prefixed_coordinates : forall row rest index suffixes,
    flat_map (decode_coordinate (row :: rest)) (map (cons index) suffixes) =
      match nth_error row index with
      | Some value => map (cons value) (flat_map (decode_coordinate rest) suffixes)
      | None => []
      end.
  Proof.
    intros row rest index suffixes. rewrite cursor_flat_map_map.
    induction suffixes as [|suffix suffixes IH]; cbn [flat_map]; [destruct (nth_error row index); reflexivity|].
    rewrite decode_coordinate_cons, IH.
    destruct (nth_error row index); cbn; [now rewrite map_app|reflexivity].
  Qed.

  Theorem decoding_coordinates_preserves_the_exact_cartesian_family : forall families,
    flat_map (decode_coordinate families) (coordinates families) = cartesian families.
  Proof.
    induction families as [|row rest IH]; [reflexivity|].
    unfold coordinates in *. cbn [map coordinate_product cartesian].
    rewrite cursor_flat_map_flat_map.
    change (flat_map (fun index => flat_map (decode_coordinate (row :: rest))
      (map (cons index) (coordinate_product (map (@length Value) rest))))
      (seq 0 (length row)) =
      flat_map (fun value => map (cons value) (cartesian rest)) row).
    rewrite <- (row_index_flat_map row (fun value => map (cons value) (cartesian rest))).
    apply flat_map_ext. intro index. rewrite decode_prefixed_coordinates, IH.
    reflexivity.
  Qed.
End CoordinateDecoding.

Example decoding_keeps_duplicate_values_at_distinct_occurrences :
  flat_map (decode_coordinate [[7; 7]; [8; 8]])
    (coordinates [[7; 7]; [8; 8]]) = [[7; 8]; [7; 8]; [7; 8]; [7; 8]].
Proof. reflexivity. Qed.

Print Assumptions decoding_coordinates_preserves_the_exact_cartesian_family.

(* Successful-output limits and computation limits are separate. An undefined
   partial action consumes one coordinate but no output quota. The cursor is
   advanced before testing the next quota, so accepting the final coordinate
   reports Exhausted, not a spurious suspension. WorkLimit contains no prefix;
   the separate RealizationFailureBoundary model covers error publication. *)
Section PartialActionDriver.
  Context {Value : Type}.
  Variable bounds : list nat.
  Variable action : list nat -> option Value.

  Definition cursor_valid (cursor : option (list nat)) : Prop :=
    match cursor with Some indices => valid_coordinate bounds indices | None => True end.

  Definition cursor_remaining (cursor : option (list nat)) : list (list nat) :=
    match cursor with Some indices => remaining bounds indices | None => [] end.

  Definition action_output (indices : list nat) : list Value :=
    match action indices with Some value => [value] | None => [] end.

  Definition cursor_outputs (cursor : option (list nat)) : list Value :=
    flat_map action_output (cursor_remaining cursor).

  Theorem initialized_cursor_is_valid_and_complete :
    cursor_valid (initial_cursor bounds) /\
    cursor_remaining (initial_cursor bounds) = coordinate_product bounds.
  Proof.
    pose proof (initialization_denotes_the_complete_coordinate_product bounds) as H.
    destruct (initial_cursor bounds) as [indices|]; cbn in *.
    - exact H.
    - split; [exact I|symmetry; exact H].
  Qed.

  Inductive stream_result :=
  | Exhausted : list Value -> stream_result
  | Suspended : list Value -> list nat -> stream_result
  | WorkLimit : stream_result.

  Definition prepend_result (value : Value) (result : stream_result) : stream_result :=
    match result with
    | Exhausted output => Exhausted (value :: output)
    | Suspended output cursor => Suspended (value :: output) cursor
    | WorkLimit => WorkLimit
    end.

  Fixpoint drain (fuel quota : nat) (cursor : option (list nat)) : stream_result :=
    match cursor with
    | None => Exhausted []
    | Some indices => match quota with
      | 0 => Suspended [] indices
      | S quota' => match fuel with
        | 0 => WorkLimit
        | S fuel' => match action indices with
          | None => drain fuel' quota (successor bounds indices)
          | Some value => prepend_result value
              (drain fuel' quota' (successor bounds indices))
          end
        end
      end
    end.

  Definition result_refines (expected : list Value) (result : stream_result) : Prop :=
    match result with
    | Exhausted output => expected = output
    | Suspended output indices =>
        valid_coordinate bounds indices /\
        expected = output ++ cursor_outputs (Some indices)
    | WorkLimit => True
    end.

  Lemma next_cursor_valid : forall indices,
    valid_coordinate bounds indices -> cursor_valid (successor bounds indices).
  Proof.
    intros indices H. unfold cursor_valid.
    destruct (successor bounds indices) as [next|] eqn:E; [|exact I].
    now apply (successor_keeps_coordinates_in_bounds H E).
  Qed.

  Lemma cursor_output_step : forall indices,
    valid_coordinate bounds indices ->
    cursor_outputs (Some indices) = action_output indices ++
      cursor_outputs (successor bounds indices).
  Proof.
    intros indices H. unfold cursor_outputs, cursor_remaining.
    rewrite (successor_removes_exactly_the_current_coordinate H).
    destruct (successor bounds indices); reflexivity.
  Qed.

  Lemma prepend_preserves_refinement : forall value expected result,
    result_refines expected result ->
    result_refines (value :: expected) (prepend_result value result).
  Proof.
    intros value expected [output|output indices|]; cbn; intro H.
    - now rewrite H.
    - destruct H as [Hvalid Houtput]. split; [exact Hvalid | now rewrite Houtput].
    - exact I.
  Qed.

  Theorem bounded_driver_preserves_exact_partial_action_order : forall fuel quota cursor,
    cursor_valid cursor ->
    result_refines (cursor_outputs cursor) (drain fuel quota cursor).
  Proof.
    induction fuel as [|fuel IH]; intros quota [indices|] Hvalid.
    - destruct quota; cbn [drain result_refines]; [split; [exact Hvalid|reflexivity]|exact I].
    - reflexivity.
    - destruct quota as [|quota].
      + cbn [drain result_refines]. split; [exact Hvalid|reflexivity].
      + cbn [drain]. rewrite (cursor_output_step Hvalid).
        unfold action_output. destruct (action indices) as [value|] eqn:E; cbn [app].
        * apply prepend_preserves_refinement. apply IH. now apply next_cursor_valid.
        * apply IH. now apply next_cursor_valid.
    - reflexivity.
  Qed.

  Corollary exhausted_driver_evaluated_the_complete_remaining_family :
    forall fuel quota cursor output,
    cursor_valid cursor -> drain fuel quota cursor = Exhausted output ->
    cursor_outputs cursor = output.
  Proof.
    intros fuel quota cursor output Hvalid Hdone.
    pose proof (bounded_driver_preserves_exact_partial_action_order fuel quota cursor Hvalid) as H.
    now rewrite Hdone in H.
  Qed.

  Corollary suspended_driver_keeps_exact_remaining_outputs :
    forall fuel quota cursor output next,
    cursor_valid cursor -> drain fuel quota cursor = Suspended output next ->
    valid_coordinate bounds next /\
    cursor_outputs cursor = output ++ cursor_outputs (Some next).
  Proof.
    intros fuel quota cursor output next Hvalid Hstop.
    pose proof (bounded_driver_preserves_exact_partial_action_order fuel quota cursor Hvalid) as H.
    now rewrite Hstop in H.
  Qed.

  Lemma one_attempt_removes_one_remaining_coordinate : forall indices,
    valid_coordinate bounds indices ->
    length (cursor_remaining (Some indices)) =
      S (length (cursor_remaining (successor bounds indices))).
  Proof.
    intros indices H. unfold cursor_remaining.
    rewrite (successor_removes_exactly_the_current_coordinate H).
    destruct (successor bounds indices); reflexivity.
  Qed.

  (* Fuel counts attempted coordinates, not successful outputs. Width and
     allocation limits belong to the concrete adapter; this theorem does not
     equate one attempt with one instruction of materialization or carry. *)
  Theorem sufficient_attempt_fuel_does_not_report_work_limit : forall fuel quota cursor,
    cursor_valid cursor -> length (cursor_remaining cursor) <= fuel ->
    drain fuel quota cursor <> WorkLimit.
  Proof.
    induction fuel as [|fuel IH]; intros quota [indices|] Hvalid Hfuel.
    - pose proof (one_attempt_removes_one_remaining_coordinate Hvalid). lia.
    - discriminate.
    - destruct quota as [|quota]; [discriminate|]. cbn [drain].
      assert (Hnext : length (cursor_remaining (successor bounds indices)) <= fuel).
      { rewrite (one_attempt_removes_one_remaining_coordinate Hvalid) in Hfuel. lia. }
      pose proof (next_cursor_valid Hvalid) as Hvalid_next.
      destruct (action indices) as [value|].
      + specialize (IH quota _ Hvalid_next Hnext).
        destruct (drain fuel quota (successor bounds indices)); cbn; congruence.
      + now apply IH.
    - discriminate.
  Qed.

  Definition respects_success_quota (quota : nat) (result : stream_result) : Prop :=
    match result with
    | Exhausted output => length output <= quota
    | Suspended output _ => length output = quota
    | WorkLimit => True
    end.

  Lemma prepending_one_success_consumes_one_quota : forall quota value result,
    respects_success_quota quota result ->
    respects_success_quota (S quota) (prepend_result value result).
  Proof.
    intros quota value [output|output next|]; cbn; intro H; (lia || exact I).
  Qed.

  Theorem driver_respects_success_quota : forall fuel quota cursor,
    respects_success_quota quota (drain fuel quota cursor).
  Proof.
    induction fuel as [|fuel IH]; intros quota [indices|].
    - destruct quota; cbn; (reflexivity || exact I).
    - cbn. lia.
    - destruct quota as [|quota]; [reflexivity|]. cbn [drain].
      destruct (action indices).
      + apply prepending_one_success_consumes_one_quota. apply IH.
      + apply IH.
    - cbn. lia.
  Qed.

  (* No output quota does not mean unlimited computation. This mode retains
     the same attempt budget and atomic WorkLimit result as bounded draining.
     The comparison with a larger quota below is ghost reasoning: neither a
     product cardinality nor fuel + 1 is required in the machine algorithm. *)
  Fixpoint drain_unbounded (fuel : nat) (cursor : option (list nat)) : stream_result :=
    match cursor with
    | None => Exhausted []
    | Some indices => match fuel with
      | 0 => WorkLimit
      | S fuel' => match action indices with
        | None => drain_unbounded fuel' (successor bounds indices)
        | Some value => prepend_result value
            (drain_unbounded fuel' (successor bounds indices))
        end
      end
    end.

  Theorem quota_larger_than_attempt_budget_refines_unbounded_mode :
    forall fuel quota cursor,
    fuel < quota -> drain fuel quota cursor = drain_unbounded fuel cursor.
  Proof.
    induction fuel as [|fuel IH]; intros [|quota] [indices|] Hquota;
      try lia; cbn [drain drain_unbounded]; try reflexivity.
    destruct (action indices).
    - f_equal. apply IH. lia.
    - apply IH. lia.
  Qed.

  Theorem unbounded_mode_never_reports_quota_suspension :
    forall fuel cursor output next,
    drain_unbounded fuel cursor <> Suspended output next.
  Proof.
    induction fuel as [|fuel IH]; intros [indices|] output next;
      cbn [drain_unbounded]; try discriminate.
    destruct (action indices) as [value|].
    - specialize (IH (successor bounds indices)).
      destruct (drain_unbounded fuel (successor bounds indices)) as [values|values suffix|];
        cbn [prepend_result]; try discriminate.
      exfalso. now apply (IH values suffix).
    - apply IH.
  Qed.

  Theorem unbounded_driver_preserves_exact_partial_action_order : forall fuel cursor,
    cursor_valid cursor ->
    result_refines (cursor_outputs cursor) (drain_unbounded fuel cursor).
  Proof.
    intros fuel cursor Hvalid.
    rewrite <- (quota_larger_than_attempt_budget_refines_unbounded_mode
      (fuel := fuel) (quota := S fuel) cursor ltac:(lia)).
    now apply bounded_driver_preserves_exact_partial_action_order.
  Qed.

  Theorem sufficient_unbounded_attempt_fuel_exhausts_the_exact_family :
    forall fuel cursor,
    cursor_valid cursor -> length (cursor_remaining cursor) <= fuel ->
    exists output, drain_unbounded fuel cursor = Exhausted output /\
      cursor_outputs cursor = output.
  Proof.
    intros fuel cursor Hvalid Hfuel.
    pose proof (unbounded_driver_preserves_exact_partial_action_order fuel cursor Hvalid) as Hrefines.
    assert (Hwork : drain_unbounded fuel cursor <> WorkLimit).
    { rewrite <- (quota_larger_than_attempt_budget_refines_unbounded_mode
        (fuel := fuel) (quota := S fuel) cursor ltac:(lia)).
      now apply sufficient_attempt_fuel_does_not_report_work_limit. }
    pose proof (unbounded_mode_never_reports_quota_suspension fuel cursor) as Hsuspend.
    destruct (drain_unbounded fuel cursor) as [output|output next|].
    - exists output. split; [reflexivity|exact Hrefines].
    - exfalso. now apply (Hsuspend output next).
    - contradiction.
  Qed.
End PartialActionDriver.

Example rejection_does_not_consume_the_success_quota :
  drain [3] (fun indices => if Nat.eqb (hd 0 indices) 2 then Some 42 else None)
    3 1 (Some [0]) = Exhausted [42].
Proof. reflexivity. Qed.

Example zero_success_quota_preserves_unexamined_zero_dimensional_product :
  drain [] (fun _ => Some 42) 1 0 (Some []) = Suspended [] [].
Proof. reflexivity. Qed.

Example work_exhaustion_does_not_publish_a_successful_prefix :
  drain [3] (fun indices => Some (hd 0 indices)) 1 3 (Some [0]) = WorkLimit.
Proof. reflexivity. Qed.

Example unbounded_output_still_requires_sufficient_attempts :
  drain_unbounded [3] (fun indices => Some (hd 0 indices)) 2 (Some [0]) = WorkLimit /\
  drain_unbounded [3] (fun indices => Some (hd 0 indices)) 3 (Some [0]) =
    Exhausted [0; 1; 2].
Proof. split; reflexivity. Qed.

Print Assumptions bounded_driver_preserves_exact_partial_action_order.
Print Assumptions exhausted_driver_evaluated_the_complete_remaining_family.
Print Assumptions suspended_driver_keeps_exact_remaining_outputs.
Print Assumptions initialized_cursor_is_valid_and_complete.
Print Assumptions sufficient_attempt_fuel_does_not_report_work_limit.
Print Assumptions driver_respects_success_quota.
Print Assumptions quota_larger_than_attempt_budget_refines_unbounded_mode.
Print Assumptions unbounded_mode_never_reports_quota_suspension.
Print Assumptions unbounded_driver_preserves_exact_partial_action_order.
Print Assumptions sufficient_unbounded_attempt_fuel_exhausts_the_exact_family.
