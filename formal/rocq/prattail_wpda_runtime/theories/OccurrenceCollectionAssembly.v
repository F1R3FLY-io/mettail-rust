(*
 * OccurrenceCollectionAssembly specifies the selected-container boundary.
 * A packed symbol identifies a shared family, not a shared choice.  Every
 * position in an action's container plan chooses from that family separately.
 * Selected collections keep their ordered values and weight until an action
 * invocation allocates checked, independently drainable collection slots.
 *
 * The sections prove independent occurrence selection, noncommutative weight
 * preservation, exact category conversion, and the indexed slot operations.
 * They do not assert that the existing Rust implementation refines this model,
 * nor that a bounded candidate prefix is complete.  The operational extraction
 * and caller-completeness obligations remain separate.
 *)

From Stdlib Require Import List Arith Lia Bool.
From PrattailWpdaRuntime Require Import CollectionItemKBestLifting.
Import ListNotations.
Set Implicit Arguments.

Section IndependentOccurrences.
  Context {Symbol Value : Type}.
  Variable family : Symbol -> list Value.

  Definition occurrence_families (occurrences : list Symbol) : list (list Value) :=
    map family occurrences.

  Lemma occurrence_membership :
    forall occurrences values,
      Forall2 (fun value symbol => In value (family symbol)) values occurrences <->
      Forall2 (fun value choices => In value choices)
        values (occurrence_families occurrences).
  Proof.
    induction occurrences as [|symbol rest IH]; intros [|value values];
      unfold occurrence_families in *; cbn; split; intro H;
      inversion H; subst; constructor; auto; now apply IH.
  Qed.

  Theorem occurrence_selection_is_exact :
    forall occurrences values,
      Forall2 (fun value symbol => In value (family symbol)) values occurrences <->
      exists coordinate,
        select_coordinate (occurrence_families occurrences) coordinate = Some values.
  Proof.
    intros occurrences values. split.
    - intro H.
      apply occurrence_membership in H.
      apply cartesian_sound_and_complete in H.
      destruct (@coordinate_selection_complete Value
        (occurrence_families occurrences) values H) as [coordinate [_ Hselect]].
      now exists coordinate.
    - intros [coordinate Hselect].
      destruct (@coordinate_selection_sound Value
        (occurrence_families occurrences) coordinate values Hselect) as [_ Hvalues].
      apply occurrence_membership.
      now apply cartesian_sound_and_complete.
  Qed.
End IndependentOccurrences.

Example repeated_shared_symbol_has_four_independent_readings :
  cartesian (occurrence_families (fun _ : nat => [false; true]) [7; 7]) =
    [[false; false]; [false; true]; [true; false]; [true; true]].
Proof. reflexivity. Qed.

Example node_keyed_singleton_cannot_represent_mixed_occurrences :
  forall choose : nat -> bool,
    map choose [7; 7] <> [false; true].
Proof.
  intros choose H. cbn in H.
  destruct (choose 7); discriminate.
Qed.

Section OrderedWeightAssembly.
  Context {W : Type}.
  Variable one : W.
  Variable times : W -> W -> W.
  Hypothesis times_associative :
    forall a b c, times (times a b) c = times a (times b c).
  Hypothesis one_left : forall a, times one a = a.
  Hypothesis one_right : forall a, times a one = a.

  Definition weight_fold (weights : list W) : W := fold_right times one weights.

  Lemma weight_fold_append : forall first rest,
    weight_fold (first ++ rest) = times (weight_fold first) (weight_fold rest).
  Proof.
    unfold weight_fold.
    induction first as [|weight first IH]; intro rest; cbn.
    - symmetry. apply one_left.
    - rewrite IH. symmetry. apply times_associative.
  Qed.

  Lemma iterative_weight_fold : forall weights initial,
    fold_left times weights initial = times initial (weight_fold weights).
  Proof.
    unfold weight_fold.
    induction weights as [|weight rest IH]; intro initial; cbn.
    - symmetry. apply one_right.
    - rewrite IH. apply times_associative.
  Qed.

  Theorem iterative_and_declarative_weights_agree : forall weights,
    fold_left times weights one = weight_fold weights.
  Proof.
    intro weights. rewrite iterative_weight_fold. apply one_left.
  Qed.

  Theorem container_grouping_preserves_weight_order : forall groups,
    weight_fold (map weight_fold groups) = weight_fold (concat groups).
  Proof.
    induction groups as [|group rest IH].
    - reflexivity.
    - change (times (weight_fold group) (weight_fold (map weight_fold rest)) =
        weight_fold (group ++ concat rest)).
      rewrite weight_fold_append. now rewrite IH.
  Qed.
End OrderedWeightAssembly.

(* A free noncommutative monoid makes the required order directly observable. *)
Example collection_weight_occurs_between_its_neighbors :
  fold_left (@app nat) [[0]; [1; 2]; [3]; [4]] [] = [0; 1; 2; 3; 4].
Proof. reflexivity. Qed.

Section ExactItemConversion.
  Context {A B : Type}.
  Variable convert : A -> option B.

  Fixpoint convert_all (items : list A) : option (list B) :=
    match items with
    | [] => Some []
    | item :: rest =>
        match convert item, convert_all rest with
        | Some value, Some values => Some (value :: values)
        | _, _ => None
        end
    end.

  (* [output ++ [value]] is the abstract sequence operation implemented by
     Vec::push.  The model makes no claim that linked-list append is the
     implementation's allocation strategy. *)
  Fixpoint convert_loop (items : list A) (output : list B) : option (list B) :=
    match items with
    | [] => Some output
    | item :: rest =>
        match convert item with
        | Some value => convert_loop rest (output ++ [value])
        | None => None
        end
    end.

  Theorem conversion_loop_refines_declarative_conversion : forall items output,
    convert_loop items output = option_map (fun values => output ++ values) (convert_all items).
  Proof.
    induction items as [|item rest IH]; intro output; cbn.
    - now rewrite app_nil_r.
    - destruct (convert item) as [value|]; [|reflexivity].
      rewrite IH. destruct (convert_all rest); cbn; [|reflexivity].
      f_equal. now rewrite <- app_assoc.
  Qed.

  Corollary empty_accumulator_loop_is_exact : forall items,
    convert_loop items [] = convert_all items.
  Proof.
    intro items. rewrite conversion_loop_refines_declarative_conversion.
    destruct (convert_all items); reflexivity.
  Qed.

  Theorem conversion_preserves_every_item : forall items values,
    convert_all items = Some values <->
    Forall2 (fun item value => convert item = Some value) items values.
  Proof.
    induction items as [|item rest IH]; intros [|value values]; cbn.
    - split; intro H; constructor.
    - split; intro H; inversion H.
    - destruct (convert item); destruct (convert_all rest);
        split; intro H; inversion H.
    - split.
      + destruct (convert item) as [actual|] eqn:Hitem; [|discriminate].
        destruct (convert_all rest) as [tail|] eqn:Hrest; [|discriminate].
        intro H. inversion H; subst. constructor; [exact Hitem |].
        now apply IH.
      + intro H.
        inversion H as [|item' value' rest' values' Hhead Htail]; subst.
        rewrite Hhead. apply IH in Htail. now rewrite Htail.
  Qed.

  Corollary successful_conversion_keeps_arity : forall items values,
    convert_all items = Some values -> length items = length values.
  Proof.
    intros items values H. apply conversion_preserves_every_item in H.
    induction H; cbn; congruence.
  Qed.

  Theorem invalid_item_rejects_the_whole_collection : forall items item,
    In item items -> convert item = None -> convert_all items = None.
  Proof.
    induction items as [|head rest IH]; intros item Hin Hbad; cbn in *.
    - contradiction.
    - destruct Hin as [<-|Hin].
      + now rewrite Hbad.
      + rewrite (IH item Hin Hbad). now destruct (convert head).
  Qed.
End ExactItemConversion.

Section IndexedActionCollections.
  Context {Payload : Type}.

  (* [None] is a consumed slot.  Draining preserves every slot's index. *)
  Fixpoint take_slot (index : nat) (frame : list (option Payload))
    : option (Payload * list (option Payload)) :=
    match index, frame with
    | 0, Some payload :: rest => Some (payload, None :: rest)
    | S index, head :: rest =>
        match take_slot index rest with
        | Some (payload, remaining) => Some (payload, head :: remaining)
        | None => None
        end
    | _, _ => None
    end.

  Theorem take_slot_exact : forall index frame payload remaining,
    take_slot index frame = Some (payload, remaining) ->
    nth_error frame index = Some (Some payload) /\
    nth_error remaining index = Some None /\
    length remaining = length frame /\
    (forall other, other <> index ->
      nth_error remaining other = nth_error frame other).
  Proof.
    induction index as [|index IH]; intros [|head rest] payload remaining H;
      cbn in H; try discriminate.
    - destruct head as [value|]; [|discriminate].
      inversion H; subst. cbn. repeat split; try reflexivity.
      intros [|other] Hother; [contradiction | reflexivity].
    - destruct (take_slot index rest) as [[value tail]|] eqn:Htake;
        [|discriminate].
      inversion H; subst.
      destruct (IH rest payload tail Htake) as [Hbefore [Hafter [Hlength Hothers]]].
      cbn. repeat split; try assumption; try congruence.
      intros [|other] Hother; [reflexivity |].
      cbn. apply Hothers. congruence.
  Qed.

  Lemma present_slot_can_be_taken : forall index frame payload,
    nth_error frame index = Some (Some payload) ->
    exists remaining, take_slot index frame = Some (payload, remaining).
  Proof.
    induction index as [|index IH]; intros [|head rest] payload H;
      cbn in H; try discriminate.
    - inversion H; subst. eexists. reflexivity.
    - destruct (IH rest payload H) as [remaining Htake].
      exists (head :: remaining). cbn. now rewrite Htake.
  Qed.

  Theorem consumed_slot_cannot_be_taken : forall index frame,
    nth_error frame index = Some None -> take_slot index frame = None.
  Proof.
    induction index as [|index IH]; intros [|head rest] H;
      cbn in H; try discriminate.
    - inversion H; subst. reflexivity.
    - cbn. now rewrite (IH rest H).
  Qed.

  Corollary repeated_drain_is_rejected : forall index frame payload remaining,
    take_slot index frame = Some (payload, remaining) ->
    take_slot index remaining = None.
  Proof.
    intros index frame payload remaining H.
    apply consumed_slot_cannot_be_taken.
    now destruct (@take_slot_exact index frame payload remaining H) as [_ [Hafter _]].
  Qed.

  Theorem draining_one_slot_preserves_every_other_payload :
    forall first second frame payload remaining other_payload,
      first <> second ->
      take_slot first frame = Some (payload, remaining) ->
      nth_error frame second = Some (Some other_payload) ->
      exists final, take_slot second remaining = Some (other_payload, final).
  Proof.
    intros first second frame payload remaining other_payload Hneq Htake Hother.
    apply present_slot_can_be_taken.
    destruct (@take_slot_exact first frame payload remaining Htake)
      as [_ [_ [_ Hpreserve]]].
    rewrite Hpreserve; congruence.
  Qed.

  Definition allocate_slot (limit : nat) (payload : Payload)
    (frame : list (option Payload)) : option (nat * list (option Payload)) :=
    if length frame <? limit
    then Some (length frame, frame ++ [Some payload])
    else None.

  Theorem allocation_is_fresh_and_bounded : forall limit payload frame index after,
    allocate_slot limit payload frame = Some (index, after) ->
    index = length frame /\ index < limit /\
    length after = S (length frame) /\
    nth_error after index = Some (Some payload) /\
    (forall old, old < length frame -> nth_error after old = nth_error frame old).
  Proof.
    intros limit payload frame index after H.
    unfold allocate_slot in H.
    destruct (length frame <? limit) eqn:Hlimit; [|discriminate].
    apply Nat.ltb_lt in Hlimit. inversion H; subst.
    repeat split; try assumption; try reflexivity.
    - rewrite length_app. cbn. lia.
    - rewrite nth_error_app2; [|lia].
      now rewrite Nat.sub_diag.
    - intros old Hbound. now rewrite nth_error_app1.
  Qed.

  Theorem full_frame_rejects_allocation : forall limit payload frame,
    limit <= length frame -> allocate_slot limit payload frame = None.
  Proof.
    intros limit payload frame Hbound. unfold allocate_slot.
    destruct (length frame <? limit) eqn:Htest; [|reflexivity].
    apply Nat.ltb_lt in Htest. lia.
  Qed.

  Definition frame_consumed (frame : list (option Payload)) : bool :=
    forallb (fun slot => match slot with None => true | Some _ => false end) frame.

  Theorem completed_frame_has_no_undrained_payload : forall frame index payload,
    frame_consumed frame = true ->
    nth_error frame index <> Some (Some payload).
  Proof.
    intros frame index payload Hcomplete Hnth.
    unfold frame_consumed in Hcomplete.
    pose proof (proj1 (@forallb_forall (option Payload)
      (fun slot => match slot with None => true | Some _ => false end) frame)
      Hcomplete) as Hall.
    specialize (Hall (Some payload)
      (@nth_error_In (option Payload) frame index (Some payload) Hnth)).
    discriminate.
  Qed.
End IndexedActionCollections.

Section IndexedFrameImplementation.
  Context {Payload : Type}.

  Fixpoint clear_slot (index : nat) (frame : list (option Payload)) :=
    match index, frame with
    | 0, _ :: rest => None :: rest
    | S index, head :: rest => head :: clear_slot index rest
    | _, [] => []
    end.

  (* The vector implementation reads one indexed slot and takes its Option.
     This specification separates that read/write from the recursive model. *)
  Definition indexed_take (index : nat) (frame : list (option Payload)) :=
    match nth_error frame index with
    | Some (Some payload) => Some (payload, clear_slot index frame)
    | _ => None
    end.

  Theorem indexed_take_refines_take_slot : forall index frame,
    indexed_take index frame = take_slot index frame.
  Proof.
    induction index as [|index IH]; intros [|head rest];
      unfold indexed_take in *; cbn; try reflexivity.
    rewrite <- IH.
    destruct (nth_error rest index) as [[payload|]|]; reflexivity.
  Qed.
End IndexedFrameImplementation.

Section CheckedActionProtocol.
  Context {Value : Type}.

  Record action_frame := {
    action_slots : list (option (list Value));
    action_failed : bool
  }.

  (* Existing generated callbacks return unit. A failed drain therefore
     invalidates the entire invocation, even if the callback emits a value
     after receiving an empty item list. Failure is not an empty collection. *)
  Definition checked_drain (index : nat) (frame : action_frame)
    : list Value * action_frame :=
    match indexed_take index (action_slots frame) with
    | Some (payload, remaining) =>
        (payload, {| action_slots := remaining; action_failed := action_failed frame |})
    | None =>
        ([], {| action_slots := action_slots frame; action_failed := true |})
    end.

  Definition action_frame_complete (frame : action_frame) :=
    negb (action_failed frame) && frame_consumed (action_slots frame).

  Theorem checked_drain_keeps_exact_payload : forall index frame payload remaining,
    indexed_take index (action_slots frame) = Some (payload, remaining) ->
    fst (checked_drain index frame) = payload /\
    action_slots (snd (checked_drain index frame)) = remaining.
  Proof.
    intros index frame payload remaining H. unfold checked_drain.
    rewrite H. split; reflexivity.
  Qed.

  Theorem invalid_drain_cannot_publish : forall index frame,
    indexed_take index (action_slots frame) = None ->
    action_frame_complete (snd (checked_drain index frame)) = false.
  Proof.
    intros index frame H. unfold checked_drain. rewrite H. reflexivity.
  Qed.

  Theorem drain_failure_is_sticky : forall index frame,
    action_failed frame = true ->
    action_failed (snd (checked_drain index frame)) = true.
  Proof.
    intros index frame H. unfold checked_drain.
    destruct (indexed_take index (action_slots frame)) as [[payload remaining]|];
      cbn; assumption || reflexivity.
  Qed.

  Definition drain_sequence (indices : list nat) (frame : action_frame) :=
    fold_left (fun state index => snd (checked_drain index state)) indices frame.

  Theorem later_drains_cannot_clear_failure : forall indices frame,
    action_failed frame = true ->
    action_failed (drain_sequence indices frame) = true.
  Proof.
    induction indices as [|index rest IH]; intros frame H; cbn; [exact H |].
    apply IH. now apply drain_failure_is_sticky.
  Qed.

  Theorem completed_action_has_no_missing_drain : forall frame index payload,
    action_frame_complete frame = true ->
    nth_error (action_slots frame) index <> Some (Some payload).
  Proof.
    intros frame index payload H.
    unfold action_frame_complete in H.
    destruct (action_failed frame); cbn in H; [discriminate |].
    now apply completed_frame_has_no_undrained_payload.
  Qed.
End CheckedActionProtocol.

Print Assumptions occurrence_selection_is_exact.
Print Assumptions node_keyed_singleton_cannot_represent_mixed_occurrences.
Print Assumptions iterative_and_declarative_weights_agree.
Print Assumptions container_grouping_preserves_weight_order.
Print Assumptions conversion_preserves_every_item.
Print Assumptions conversion_loop_refines_declarative_conversion.
Print Assumptions empty_accumulator_loop_is_exact.
Print Assumptions successful_conversion_keeps_arity.
Print Assumptions invalid_item_rejects_the_whole_collection.
Print Assumptions take_slot_exact.
Print Assumptions repeated_drain_is_rejected.
Print Assumptions draining_one_slot_preserves_every_other_payload.
Print Assumptions allocation_is_fresh_and_bounded.
Print Assumptions full_frame_rejects_allocation.
Print Assumptions completed_frame_has_no_undrained_payload.
Print Assumptions indexed_take_refines_take_slot.
Print Assumptions checked_drain_keeps_exact_payload.
Print Assumptions invalid_drain_cannot_publish.
Print Assumptions later_drains_cannot_clear_failure.
Print Assumptions completed_action_has_no_missing_drain.
