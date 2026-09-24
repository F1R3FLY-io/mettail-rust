(** Owned infix observations and source-ordered normalized occurrence receipts.

    This is an interface refinement, not another classifier or binding-power
    algorithm. InfixClassifierProjection supplies the unchanged classifier's
    complete source/view observation theorem. AuthoredSynthesisComposition
    supplies source metadata, private-owner, and current-handle replacement
    laws; AuthoredNormalizationMaterialization supplies original normalization.

    Rust boundary: User provenance retains BOTH a caller-roster ordinal and a
    global production index. The original clone callback receives this explicit
    staged pair. The original normalization success boundary writes the returned
    payload into its private ordinal slot. No FIFO, sorting, deduplication,
    rescan of synthetic buckets, or repeated normalization is needed.

    The owner allocates slots only after admission. Each success writes once,
    verifies the expected production identity, and preserves all other slots.
    Finalization requires every slot to be present. These laws cover arbitrary
    normalization visitation order; source order is the original caller roster.

    RetainedData below is a mathematical source-observation record, NOT a Rust
    reconstructed AST. Existing retained-arena reader/capture laws discharge its
    spelling and shallow-field correspondence. Unsupported positions remain
    present; optional empty sequences remain different from absent sequences.
    Runtime NonAssociative cannot be represented by the original right-bool
    classifier interface and is explicitly refused. Prefix precedence is not
    read by infix projection: its later u8 consumer must check the retained u16.

    Interface proof scope: source-view equality, not equality of redundant
    macro clone/normalization traces. The later Rust adapter must actually call
    the existing classifier and binding-power implementation. This file neither
    models nor replaces their decision programs; no parser/physical-RSS claim.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import InfixClassifierProjection
  AuthoredSynthesisComposition AuthoredNormalizationMaterialization.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredInfixProjection.
Module I := InfixClassifierProjection.InfixClassifierProjection.
Module S := AuthoredSynthesisComposition.AuthoredSynthesisComposition.
Module N := AuthoredNormalizationMaterialization.AuthoredNormalizationMaterialization.

Inductive Associativity := Left | Right | NonAssociative.
Record Metadata := {
  associativity : Associativity;
  shares_previous : bool;
  prefix_binding_power : option nat
}.
Record RetainedData := {
  label : string;
  category : string;
  context : option (list I.SourceParam);
  syntax : option (list I.SourceSyntax)
}.
Definition capture_data source :=
  {| label := I.source_label source; category := I.source_category source;
     context := I.source_context source; syntax := I.source_pattern source |}.
Definition capture_metadata source prefix :=
  {| associativity := if I.source_right source then Right else Left;
     shares_previous := I.source_same_level source; prefix_binding_power := prefix |}.
Definition project data metadata : option I.RuleView :=
  match associativity metadata with
  | NonAssociative => None
  | association => Some
      {| I.view_label := label data;
         I.view_category := category data;
         I.view_right := match association with Right => true | _ => false end;
         I.view_same_level := shares_previous metadata;
         I.view_context := option_map (map I.project_param) (context data);
         I.view_pattern := option_map (map I.project_syntax) (syntax data) |}
  end.

Theorem captured_projection_is_original_view : forall source prefix,
  project (capture_data source) (capture_metadata source prefix) =
    Some (I.project_rule source).
Proof.
  intros [l c r s p t] prefix; destruct r; reflexivity.
Qed.
Theorem exact_classifier_observations_reused : forall source prefix view A (query : I.Query A),
  project (capture_data source) (capture_metadata source prefix) = Some view ->
  I.read_view view query = I.read_source source query.
Proof.
  intros source prefix view A query Run.
  rewrite captured_projection_is_original_view in Run; inversion Run; subst.
  apply I.every_classifier_observation_preserved.
Qed.
Theorem exact_unchanged_classifier_program_reused : forall source prefix view R
  (program : I.Decision R),
  project (capture_data source) (capture_metadata source prefix) = Some view ->
  I.run_view view program = I.run_source source program.
Proof.
  intros source prefix view R program Run.
  rewrite captured_projection_is_original_view in Run; inversion Run; subst.
  apply I.unchanged_decision_program_observational_equivalence.
Qed.
Theorem prefix_not_observed_by_infix_projection : forall data association shares a b,
  project data {| associativity := association; shares_previous := shares;
                  prefix_binding_power := a |} =
  project data {| associativity := association; shares_previous := shares;
                  prefix_binding_power := b |}.
Proof. intros; destruct association; reflexivity. Qed.
Theorem nonassociative_is_not_silently_left : forall data shares prefix,
  project data {| associativity := NonAssociative; shares_previous := shares;
                  prefix_binding_power := prefix |} = None.
Proof. reflexivity. Qed.
Theorem projected_context_keeps_all_positions : forall params index,
  List.length (map I.project_param params) = List.length params /\
  nth_error (map I.project_param params) index =
    option_map I.project_param (nth_error params index).
Proof. apply I.context_preserves_length_and_every_position. Qed.
Theorem projected_syntax_keeps_all_positions : forall syntax index,
  List.length (map I.project_syntax syntax) = List.length syntax /\
  nth_error (map I.project_syntax syntax) index =
    option_map I.project_syntax (nth_error syntax index).
Proof. apply I.syntax_preserves_length_and_every_position. Qed.
Theorem unsupported_parameter_not_removed : forall params index opaque,
  nth_error params index = Some (I.SourceOtherParam opaque) ->
  nth_error (map I.project_param params) index = Some I.OtherParam.
Proof. apply I.unsupported_parameter_keeps_its_position. Qed.
Theorem unsupported_syntax_not_removed : forall syntax index opaque,
  nth_error syntax index = Some (I.SourceOtherSyntax opaque) ->
  nth_error (map I.project_syntax syntax) index = Some I.OtherSyntax.
Proof. apply I.unsupported_syntax_keeps_its_position. Qed.
Theorem absent_and_present_empty_remain_distinct :
  option_map (map I.project_param) None <>
  option_map (map I.project_param) (Some []).
Proof. discriminate. Qed.

Inductive Origin := User (roster_index production_index : nat) | Synthetic.
Record Payload := { current_rule : S.RuleId; origin : Origin }.
Definition erase payload : S.Payload :=
  {| S.current_rule := current_rule payload;
     S.origin := match origin payload with
       | User _ production => S.UserOccurrence production
       | Synthetic => S.SyntheticOrigin end |}.
Definition replace_current payload id :=
  {| current_rule := id; origin := origin payload |}.
Theorem replacement_refines_existing_payload : forall payload id,
  erase (replace_current payload id) = S.replace_current (erase payload) id.
Proof. reflexivity. Qed.
Theorem replacement_keeps_both_source_coordinates : forall payload id,
  origin (replace_current payload id) = origin payload.
Proof. reflexivity. Qed.
Theorem original_normalization_is_reused : forall source rule,
  N.L.shared_normalize (fun index => N.L.project_item (source index))
    N.L.original_constructors rule = N.L.source_normalize source rule.
Proof. apply N.shared_normalization_is_reused_not_rederived. Qed.
Theorem duplicate_productions_keep_distinct_occurrences : forall a b production x y,
  origin x = User a production -> origin y = User b production -> a <> b -> x <> y.
Proof. intros a b production x y X Y Different Equal; subst; congruence. Qed.

Definition Slots := list (option Payload).
Fixpoint put slots index payload : option Slots := match slots with
| [] => None
| head :: rest => match index with
  | 0 => match head with None => Some (Some payload :: rest) | Some _ => None end
  | S index => option_map (fun next => head :: next) (put rest index payload)
  end
end.
Definition record expected slots payload := match origin payload with
| Synthetic => None
| User ordinal production => match nth_error expected ordinal with
  | Some target => if Nat.eqb target production then put slots ordinal payload else None
  | None => None end end.

Lemma put_length : forall slots index payload next,
  put slots index payload = Some next -> List.length next = List.length slots.
Proof.
  induction slots as [|head rest IH]; intros [|index] payload next Run; cbn in Run;
    try discriminate.
  - destruct head; [discriminate|]. inversion Run; reflexivity.
  - destruct (put rest index payload) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst; cbn. f_equal. eapply IH; exact Tail.
Qed.
Lemma put_selected : forall slots index payload next,
  put slots index payload = Some next -> nth_error next index = Some (Some payload).
Proof.
  induction slots as [|head rest IH]; intros [|index] payload next Run; cbn in Run;
    try discriminate.
  - destruct head; [discriminate|]. inversion Run; reflexivity.
  - destruct (put rest index payload) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst; cbn. eapply IH; exact Tail.
Qed.
Lemma put_other : forall slots index payload next,
  put slots index payload = Some next -> forall other,
  other <> index -> nth_error next other = nth_error slots other.
Proof.
  induction slots as [|head rest IH]; intros [|index] payload next Run other Different;
    cbn in Run; try discriminate.
  - destruct head; [discriminate|]. inversion Run; subst.
    destruct other; [contradiction|reflexivity].
  - destruct (put rest index payload) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst. destruct other; [reflexivity|].
    cbn. eapply IH; [exact Tail|lia].
Qed.
Lemma occupied_slot_refuses : forall slots index old payload,
  nth_error slots index = Some (Some old) -> put slots index payload = None.
Proof.
  induction slots as [|head rest IH]; intros [|index] old payload At; cbn in *;
    try discriminate.
  - inversion At; subst; reflexivity.
  - now rewrite (IH index old payload At).
Qed.

Definition SlotLaw expected slots := forall index payload,
  nth_error slots index = Some (Some payload) ->
  exists production, nth_error expected index = Some production /\
    origin payload = User index production.
Theorem empty_slots_obey_source_roster : forall expected,
  SlotLaw expected (repeat None (List.length expected)).
Proof.
  intros expected index payload At.
  apply nth_error_In in At. apply repeat_spec in At. discriminate.
Qed.
Theorem checked_record_retains_expected_production : forall expected slots payload next,
  record expected slots payload = Some next ->
  exists ordinal production,
    origin payload = User ordinal production /\
    nth_error expected ordinal = Some production /\
    put slots ordinal payload = Some next.
Proof.
  intros expected slots payload next Run; unfold record in Run.
  destruct (origin payload) as [ordinal production|] eqn:Origin; [|discriminate].
  destruct (nth_error expected ordinal) as [target|] eqn:At; [|discriminate].
  destruct (Nat.eqb target production) eqn:Equal; [|discriminate].
  apply Nat.eqb_eq in Equal; subst target.
  exists ordinal, production; auto.
Qed.
Theorem checked_record_preserves_slot_law : forall expected slots payload next,
  SlotLaw expected slots -> record expected slots payload = Some next ->
  SlotLaw expected next.
Proof.
  intros expected slots payload next Law Run index value At.
  destruct (@checked_record_retains_expected_production expected slots payload next Run)
    as [ordinal [production [Origin [Expected Put]]]].
  destruct (Nat.eq_dec index ordinal) as [Equal|Different].
  - subst index. pose proof (@put_selected slots ordinal payload next Put) as Selected.
    rewrite Selected in At; inversion At; subst value. exists production; auto.
  - apply Law. rewrite <- (@put_other slots ordinal payload next Put index Different).
    exact At.
Qed.
Theorem checked_record_cannot_overwrite : forall expected slots payload next ordinal production,
  record expected slots payload = Some next -> origin payload = User ordinal production ->
  record expected next payload = None.
Proof.
  intros expected slots payload next ordinal production Run Origin.
  destruct (@checked_record_retains_expected_production expected slots payload next Run)
    as [index [source [Kind [At Put]]]].
  rewrite Origin in Kind; inversion Kind; subst.
  unfold record; rewrite Origin, At, Nat.eqb_refl.
  eapply occupied_slot_refuses. eapply put_selected; exact Put.
Qed.

Fixpoint collect slots : option (list Payload) := match slots with
| [] => Some []
| None :: _ => None
| Some payload :: rest => option_map (cons payload) (collect rest)
end.
Theorem collect_exact : forall slots payloads,
  collect slots = Some payloads -> map (@Some Payload) payloads = slots.
Proof.
  induction slots as [|[head|] rest IH]; intros payloads Run; cbn in Run; try discriminate.
  - inversion Run; reflexivity.
  - destruct (collect rest) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst; cbn. f_equal. apply IH; reflexivity.
Qed.
Theorem publication_has_source_order_and_duplicates : forall expected slots payloads index payload,
  SlotLaw expected slots -> collect slots = Some payloads ->
  nth_error payloads index = Some payload ->
  exists production, nth_error expected index = Some production /\
    origin payload = User index production.
Proof.
  intros expected slots payloads index payload Law Run At.
  apply Law. rewrite <- (@collect_exact slots payloads Run), I.map_nth_exact, At.
  reflexivity.
Qed.
Theorem publication_has_no_missing_slots : forall slots payloads index,
  collect slots = Some payloads -> nth_error slots index <> Some None.
Proof.
  intros slots payloads index Run Missing.
  rewrite <- (@collect_exact slots payloads Run), I.map_nth_exact in Missing.
  destruct (nth_error payloads index); discriminate.
Qed.
Theorem publication_keeps_full_roster_length : forall (expected : list nat) slots payloads,
  List.length slots = List.length expected -> collect slots = Some payloads ->
  List.length payloads = List.length expected.
Proof.
  intros expected slots payloads Length Run.
  pose proof (@collect_exact slots payloads Run) as Exact.
  rewrite <- Exact, map_length in Length; exact Length.
Qed.

Section Owner.
Context {Policy : Type}.
Record Owner := { session : N.Session; policy : Policy; slots : Slots }.
Definition normalize_and_record
  (call : N.Session -> S.RuleId -> Policy -> option (N.Session * S.RuleId * Policy))
  expected before payload :=
  match call (session before) (current_rule payload) (policy before) with
  | None => None
  | Some (after, id, next_policy) =>
      let updated := replace_current payload id in
      match record expected (slots before) updated with
      | None => None
      | Some next_slots => Some
          ({| session := after; policy := next_policy; slots := next_slots |}, updated)
      end
  end.
Theorem failed_normalization_has_no_slot_write_or_owner : forall call expected before payload,
  call (session before) (current_rule payload) (policy before) = None ->
  normalize_and_record call expected before payload = None.
Proof. intros; unfold normalize_and_record; now rewrite H. Qed.
Theorem failed_record_exposes_no_updated_owner : forall call expected before payload after id next,
  call (session before) (current_rule payload) (policy before) = Some (after,id,next) ->
  record expected (slots before) (replace_current payload id) = None ->
  normalize_and_record call expected before payload = None.
Proof. intros; unfold normalize_and_record; now rewrite H, H0. Qed.
Theorem success_uses_same_session_and_policy : forall call expected before payload after id next storage,
  call (session before) (current_rule payload) (policy before) = Some (after,id,next) ->
  record expected (slots before) (replace_current payload id) = Some storage ->
  normalize_and_record call expected before payload = Some
    ({| session := after; policy := next; slots := storage |}, replace_current payload id).
Proof. intros; unfold normalize_and_record; now rewrite H, H0. Qed.
End Owner.

(** Checked sequence projection stops at its first failed source occurrence.
    The admitted observation callback owns each source read/copy: no result
    buffer is published on a refusal and no suffix callback is reached. *)
Section ProjectionSequence.
Context {Input Output : Type}.
Variable observe : Input -> option Output.
Fixpoint project_all inputs : option (list Output) * list Input := match inputs with
| [] => (Some [], [])
| item :: rest => match observe item with
  | None => (None, [item])
  | Some output => let '(answer, visited) := project_all rest in
      (option_map (cons output) answer, item :: visited)
  end end.
Theorem projection_first_refusal_has_no_suffix : forall item rest,
  observe item = None -> project_all (item :: rest) = (None, [item]).
Proof. intros; cbn; now rewrite H. Qed.
Theorem projection_visits_only_source_prefix : forall inputs,
  exists suffix, inputs = snd (project_all inputs) ++ suffix.
Proof.
  induction inputs as [|item rest IH]; cbn; [exists []; reflexivity|].
  destruct (observe item); [|exists rest; reflexivity].
  destruct (project_all rest) as [answer visited]; cbn in *.
  destruct IH as [suffix Equal]. exists suffix. now rewrite Equal.
Qed.
Theorem successful_projection_keeps_every_occurrence : forall inputs outputs visited,
  project_all inputs = (Some outputs, visited) ->
  visited = inputs /\ map (@Some Output) outputs = map observe inputs.
Proof.
  induction inputs as [|item rest IH]; intros outputs visited Run; cbn in Run.
  - inversion Run; subst; auto.
  - destruct (observe item) as [output|] eqn:Observed; [|discriminate].
    destruct (project_all rest) as [answer trace] eqn:Tail.
    destruct answer as [later|]; [|discriminate].
    inversion Run; subst. destruct (IH later trace eq_refl) as [Trace Results].
    split; [now rewrite Trace|cbn; now rewrite Observed, Results].
Qed.
End ProjectionSequence.

Print Assumptions captured_projection_is_original_view.
Print Assumptions exact_classifier_observations_reused.
Print Assumptions exact_unchanged_classifier_program_reused.
Print Assumptions prefix_not_observed_by_infix_projection.
Print Assumptions nonassociative_is_not_silently_left.
Print Assumptions projected_context_keeps_all_positions.
Print Assumptions projected_syntax_keeps_all_positions.
Print Assumptions unsupported_parameter_not_removed.
Print Assumptions unsupported_syntax_not_removed.
Print Assumptions absent_and_present_empty_remain_distinct.
Print Assumptions replacement_refines_existing_payload.
Print Assumptions replacement_keeps_both_source_coordinates.
Print Assumptions original_normalization_is_reused.
Print Assumptions duplicate_productions_keep_distinct_occurrences.
Print Assumptions empty_slots_obey_source_roster.
Print Assumptions checked_record_retains_expected_production.
Print Assumptions checked_record_preserves_slot_law.
Print Assumptions checked_record_cannot_overwrite.
Print Assumptions publication_has_source_order_and_duplicates.
Print Assumptions publication_has_no_missing_slots.
Print Assumptions publication_keeps_full_roster_length.
Print Assumptions failed_normalization_has_no_slot_write_or_owner.
Print Assumptions failed_record_exposes_no_updated_owner.
Print Assumptions success_uses_same_session_and_policy.
Print Assumptions projection_first_refusal_has_no_suffix.
Print Assumptions projection_visits_only_source_prefix.
Print Assumptions successful_projection_keeps_every_occurrence.
End AuthoredInfixProjection.
