(** Final-ID binding of immutable captured declarations.

    The header remains source-only. A private builder records compact numeric
    associations at the EXISTING category/mode/token append or coalescing sites.
    Final IDs are not capture IDs, source ordinals, normalized names, or decoder
    guesses. The published table contains only final indices: category and mode
    vectors plus token {direct, optional typed-literal auxiliary} rows.

    Source evidence: macro prattail_bridge token conversion is one row per
    original TokenDef; grammar_core_bridge skips builtin overrides, appends
    by-category Rational/Fixed tokens, and separately appends their custom
    tokens. Thus source rows may share a direct ID and one source row may have
    two distinct routes. The schema frontend has direct tokens without the
    macro auxiliary route. Missing auxiliary is explicit None, not unfinished.

    Source name -> CoreCategory checks reuse AuthoredDeclarationsProjection.
    Token validation checks bounds and mode membership only: original macro
    tokens have category/evaluation None and may have qualified/coalesced names.
    It does NOT prove decoder, pattern, push-transition or native-value parity.
    The original lowering-site provenance and the source-roster partition are
    separate premises; arbitrary structurally valid tables are not asserted to
    have been produced by those source loops. In particular Core validation
    cannot infer a private frontend receipt from serialized numeric IDs.

    write_once is an indexed Vec-slot specification, not a new capture walk.
    finish visits the compact binding rows, never traverses grammar syntax.
    Admission before allocation/checked machine arithmetic remains required;
    this file models logical finite sequences, not allocator capacity or RSS.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import AuthoredRuleStoreProjection
  AuthoredRuleCaptureProjection AuthoredRuleTransportProjection
  AuthoredDeclarationsProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredDeclarationBindingProjection.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.
Module D := AuthoredDeclarationsProjection.AuthoredDeclarationsProjection.

Fixpoint write_once {X} (slots : list (option X)) position value :=
  match slots, position with
  | [], _ => None
  | None :: rest, 0 => Some (Some value :: rest)
  | Some _ :: _, 0 => None
  | slot :: rest, S index =>
      option_map (cons slot) (write_once rest index value)
  end.
Definition finish_slots {X} (slots : list (option X)) :=
  C.map_checked (fun slot => slot) slots.

Theorem write_once_preserves_roster_length : forall X slots position (value : X) result,
  write_once slots position value = Some result -> List.length result = List.length slots.
Proof.
  intros X slots; induction slots as [|slot rest IH]; intros [|position] value result H;
    cbn in H; try discriminate.
  - destruct slot; [discriminate|inversion H; reflexivity].
  - destruct slot; cbn in H;
      destruct (write_once rest position value) as [next|] eqn:E;
      cbn in H; try discriminate; inversion H; subst; cbn; f_equal; eapply IH; eauto.
Qed.
Theorem write_once_assigns_exact_requested_position : forall X slots position (value : X) result,
  write_once slots position value = Some result -> nth_error result position = Some (Some value).
Proof.
  intros X slots; induction slots as [|slot rest IH]; intros [|position] value result H;
    cbn in H; try discriminate.
  - destruct slot; [discriminate|inversion H; reflexivity].
  - destruct slot; cbn in H;
      destruct (write_once rest position value) as [next|] eqn:E;
      cbn in H; try discriminate; inversion H; subst; cbn; eapply IH; eauto.
Qed.
Theorem already_assigned_slot_refuses_even_equal_value : forall X slots position (old value : X),
  nth_error slots position = Some (Some old) -> write_once slots position value = None.
Proof.
  intros X slots; induction slots as [|slot rest IH]; intros [|position] old value H;
    cbn in H |- *; try discriminate.
  - inversion H; reflexivity.
  - destruct slot; cbn; rewrite (IH position old value H); reflexivity.
Qed.
Theorem out_of_range_assignment_refuses : forall X slots position (value : X),
  nth_error slots position = None -> write_once slots position value = None.
Proof.
  intros X slots; induction slots as [|slot rest IH]; intros [|position] value H;
    cbn in H |- *; try reflexivity; try discriminate.
  destruct slot; cbn; rewrite (IH position value H); reflexivity.
Qed.
Theorem write_once_preserves_every_other_position : forall X slots position (value : X) result,
  write_once slots position value = Some result ->
  forall other, other <> position -> nth_error result other = nth_error slots other.
Proof.
  intros X slots; induction slots as [|slot rest IH]; intros [|position] value result H;
    cbn in H; try discriminate.
  - destruct slot; [discriminate|]; inversion H; subst result.
    intros [|other] Different; [contradiction|reflexivity].
  - destruct slot; cbn in H;
      destruct (write_once rest position value) as [next|] eqn:E;
      cbn in H; try discriminate; inversion H; subst result;
      intros [|other] Different; try reflexivity; cbn; eapply IH; first [exact E|lia].
Qed.
Theorem finalized_slots_have_exact_order_and_no_unfinished_entry : forall X slots (values : list X),
  finish_slots slots = Some values ->
  List.length values = List.length slots /\
  forall position value, nth_error values position = Some value ->
    nth_error slots position = Some (Some value).
Proof.
  intros X slots values H; split.
  - eapply C.map_checked_length; exact H.
  - revert values H; induction slots as [|slot rest IH]; intros values H.
    + inversion H; subst values; intros [|position] value Read; discriminate.
    + cbn [finish_slots C.map_checked] in H.
      destruct slot as [head|]; cbn [C.bind] in H; [|discriminate].
      destruct (C.map_checked (fun slot : option X => slot) rest) as [tail|] eqn:E;
        cbn [C.bind] in H; [|discriminate].
      inversion H; subst values; intros [|position] value Read; cbn in Read |- *.
      * inversion Read; reflexivity.
      * eapply IH; eauto.
Qed.

Record TokenBinding := {
  direct : nat;
  typed_literal : option nat
}.
Record Bindings := {
  category_ids : list nat;
  token_ids : list TokenBinding;
  mode_ids : list nat
}.
Record Pending := {
  pending_categories : list (option nat);
  pending_direct : list (option nat);
  pending_auxiliary : list (option (option nat));
  pending_modes : list (option nat)
}.
Definition initial header :=
  {| pending_categories := repeat None (List.length (D.categories header));
     pending_direct := repeat None (List.length (D.tokens header));
     pending_auxiliary := repeat None (List.length (D.tokens header));
     pending_modes := repeat None (List.length (D.modes header)) |}.
Definition make_token (entry : nat * option nat) :=
  {| direct := fst entry; typed_literal := snd entry |}.
Definition cardinalities_match header (categories direct_ids : list nat)
    (auxiliaries : list (option nat)) (modes : list nat) :=
  Nat.eqb (List.length categories) (List.length (D.categories header)) &&
  Nat.eqb (List.length direct_ids) (List.length (D.tokens header)) &&
  Nat.eqb (List.length auxiliaries) (List.length (D.tokens header)) &&
  Nat.eqb (List.length modes) (List.length (D.modes header)).
Definition finish header pending :=
  C.bind (finish_slots (pending_categories pending)) (fun categories =>
  C.bind (finish_slots (pending_direct pending)) (fun direct_ids =>
  C.bind (finish_slots (pending_auxiliary pending)) (fun auxiliaries =>
  C.bind (finish_slots (pending_modes pending)) (fun modes =>
    if cardinalities_match header categories direct_ids auxiliaries modes
    then Some {| category_ids := categories;
                 token_ids := List.map make_token (combine direct_ids auxiliaries);
                 mode_ids := modes |}
    else None)))).
Theorem explicit_absent_auxiliary_is_complete :
  finish_slots [Some (@None nat)] = Some [None].
Proof. reflexivity. Qed.
Theorem unfinished_auxiliary_is_not_absent :
  finish_slots [@None (option nat)] = None.
Proof. reflexivity. Qed.
Theorem finish_has_exact_header_cardinalities : forall header pending bound,
  finish header pending = Some bound ->
  List.length (category_ids bound) = List.length (D.categories header) /\
  List.length (token_ids bound) = List.length (D.tokens header) /\
  List.length (mode_ids bound) = List.length (D.modes header).
Proof.
  intros header pending bound H; unfold finish in H.
  destruct (finish_slots (pending_categories pending)) as [categories|] eqn:Cats;
    cbn [C.bind] in H; [|discriminate].
  destruct (finish_slots (pending_direct pending)) as [direct_ids|] eqn:Direct;
    cbn [C.bind] in H; [|discriminate].
  destruct (finish_slots (pending_auxiliary pending)) as [auxiliaries|] eqn:Aux;
    cbn [C.bind] in H; [|discriminate].
  destruct (finish_slots (pending_modes pending)) as [modes|] eqn:Modes;
    cbn [C.bind] in H; [|discriminate].
  destruct (cardinalities_match header categories direct_ids auxiliaries modes) eqn:Lengths;
    [|discriminate].
  inversion H; subst; cbn.
  unfold cardinalities_match in Lengths; repeat rewrite andb_true_iff in Lengths.
  destruct Lengths as [[[LC LD] LA] LM].
  apply Nat.eqb_eq in LC, LD, LA, LM.
  repeat split; try assumption.
  rewrite length_map, length_combine, LD, LA, Nat.min_id; reflexivity.
Qed.

(** Core projection contains only fields actually read by structural checks. *)
Record CoreView := {
  core_categories : list string;
  core_token_modes : list nat;
  core_mode_members : list (list nat)
}.
Definition token_in_mode core expected token :=
  match nth_error (core_token_modes core) token,
        nth_error (core_mode_members core) expected with
  | Some actual, Some members =>
      Nat.eqb actual expected && existsb (Nat.eqb token) members
  | _, _ => false end.
Definition binding_in_mode core expected binding :=
  token_in_mode core expected (direct binding) &&
  match typed_literal binding with
  | None => true | Some token => token_in_mode core expected token end.
Theorem accepted_token_has_actual_mode_and_membership : forall core mode token,
  token_in_mode core mode token = true ->
  nth_error (core_token_modes core) token = Some mode /\
  exists members, nth_error (core_mode_members core) mode = Some members /\ In token members.
Proof.
  intros core mode token H; unfold token_in_mode in H.
  destruct (nth_error (core_token_modes core) token) as [actual|] eqn:T; [|discriminate].
  destruct (nth_error (core_mode_members core) mode) as [members|] eqn:M; [|discriminate].
  apply andb_true_iff in H; destruct H as [Equal Member].
  apply Nat.eqb_eq in Equal; subst actual; split; [reflexivity|].
  exists members; split; [reflexivity|].
  apply existsb_exists in Member; destruct Member as [found [InFound Equal]].
  apply Nat.eqb_eq in Equal; subst found; exact InFound.
Qed.
Theorem accepted_binding_checks_both_produced_routes : forall core mode direct_id auxiliary,
  binding_in_mode core mode {| direct := direct_id; typed_literal := Some auxiliary |} = true ->
  token_in_mode core mode direct_id = true /\ token_in_mode core mode auxiliary = true.
Proof. intros; apply andb_true_iff; exact H. Qed.
Definition row_in_mode core bindings mode source_index :=
  match nth_error (token_ids bindings) source_index with
  | None => false | Some binding => binding_in_mode core mode binding end.
Definition mode_rows_valid core bindings row core_mode :=
  match nth_error (core_mode_members core) core_mode with
  | None => false
  | Some _ => forallb (row_in_mode core bindings core_mode) (D.mode_source_tokens row)
  end.
Definition validate_bindings arena header core bindings :=
  Nat.eqb (List.length (category_ids bindings)) (List.length (D.categories header)) &&
  Nat.eqb (List.length (token_ids bindings)) (List.length (D.tokens header)) &&
  Nat.eqb (List.length (mode_ids bindings)) (List.length (D.modes header)) &&
  forallb (fun entry => D.category_association arena (core_categories core) (fst entry) (snd entry))
    (combine (D.categories header) (category_ids bindings)) &&
  forallb (row_in_mode core bindings 0) (D.global_source_tokens header) &&
  forallb (fun entry => mode_rows_valid core bindings (fst entry) (snd entry))
    (combine (D.modes header) (mode_ids bindings)).

(** Header reference validity and complete source-roster coverage are store
    obligations, checked independently of final execution IDs. This precise
    partition premise forbids unvisited binding rows. It does not forbid equal
    raw names or equal final TokenIds in distinct source occurrences. *)
Definition source_roster header := D.global_source_tokens header ++
  flat_map D.mode_source_tokens (D.modes header).
Definition SourceRosterPartition header :=
  NoDup (source_roster header) /\
  forall index, In index (source_roster header) <-> index < List.length (D.tokens header).

(** Both source adapters enumerate global rows first, followed by each mode's
    rows in declaration order. Macro globals are the original token_defs
    vector (including its appended literal rows); schema globals are explicit
    tokens followed by literal declarations. Execution-token append order is
    deliberately independent. Therefore the retained source format requires
    exactly seq 0 token_count, stronger than an arbitrary partition.

    The recursive equation specifies an iterator fold: compare the current
    flattened source index to the expected position, then checked-increment.
    Rust need not allocate source_roster or seq. Natural numbers model the
    logical check; checked machine increment is a separate refusal boundary. *)
Fixpoint check_roster_from expected indices :=
  match indices with
  | [] => Some expected
  | index :: rest => if Nat.eqb index expected
      then check_roster_from (S expected) rest else None
  end.
Definition canonical_roster_valid header :=
  match check_roster_from 0 (source_roster header) with
  | None => false
  | Some count => Nat.eqb count (List.length (D.tokens header))
  end.
Lemma checked_roster_is_exact_sequence : forall indices expected final,
  check_roster_from expected indices = Some final ->
  indices = seq expected (List.length indices) /\ final = expected + List.length indices.
Proof.
  induction indices as [|index rest IH]; intros expected final Checked; cbn in Checked.
  - inversion Checked; subst final; cbn; split; [reflexivity|lia].
  - destruct (Nat.eqb index expected) eqn:Equal; [|discriminate].
    apply Nat.eqb_eq in Equal; subst index.
    destruct (IH (S expected) final Checked) as [Sequence Count].
    cbn; split; [f_equal; exact Sequence|lia].
Qed.
Theorem canonical_roster_checker_implies_source_partition : forall header,
  canonical_roster_valid header = true -> SourceRosterPartition header.
Proof.
  intros header Valid; unfold canonical_roster_valid in Valid.
  destruct (check_roster_from 0 (source_roster header)) as [count|] eqn:Checked;
    [|discriminate].
  apply Nat.eqb_eq in Valid.
  destruct (@checked_roster_is_exact_sequence _ _ _ Checked) as [Sequence Count].
  cbn in Count; assert (List.length (source_roster header) = List.length (D.tokens header))
    as Length by lia.
  unfold SourceRosterPartition; rewrite Sequence, Length; split.
  - apply seq_NoDup.
  - intros index; rewrite in_seq; lia.
Qed.

Lemma complete_pairing_contains_each_left_row : forall X Y (left : list X) (right : list Y) row,
  List.length left = List.length right -> In row left ->
  exists target, In (row, target) (combine left right).
Proof.
  intros X Y left; induction left as [|head tail IH]; intros [|target rest] row Length Member;
    cbn in Length, Member |- *; try contradiction; try discriminate.
  destruct Member as [Equal|Member].
  - subst row; exists target; left; reflexivity.
  - destruct (IH rest row ltac:(lia) Member) as [found Found].
    exists found; right; exact Found.
Qed.
Theorem partition_and_validation_check_every_source_token :
  forall arena header core bindings index,
  SourceRosterPartition header -> validate_bindings arena header core bindings = true ->
  index < List.length (D.tokens header) ->
  exists mode binding, nth_error (token_ids bindings) index = Some binding /\
    binding_in_mode core mode binding = true.
Proof.
  intros arena header core bindings index [_ Coverage] Valid Bound.
  apply Coverage in Bound; unfold source_roster in Bound; apply in_app_iff in Bound.
  unfold validate_bindings in Valid; repeat rewrite andb_true_iff in Valid.
  destruct Valid as [[[[[CategoryLength TokenLength] ModeLength] Categories] Globals] Modes].
  assert (exists mode, row_in_mode core bindings mode index = true) as Checked.
  { destruct Bound as [Global|Modal].
    - exists 0; apply forallb_forall with (x := index) in Globals; assumption.
    - apply in_flat_map in Modal; destruct Modal as [row [Member InRow]].
      apply Nat.eqb_eq in ModeLength.
      destruct (@complete_pairing_contains_each_left_row _ _ (D.modes header)
        (mode_ids bindings) row ltac:(lia) Member) as [mode Pair].
      apply forallb_forall with (x := (row, mode)) in Modes; [|exact Pair].
      cbn in Modes; unfold mode_rows_valid in Modes.
      destruct (nth_error (core_mode_members core) mode); [|discriminate].
      exists mode; apply forallb_forall with (x := index) in Modes; assumption. }
  destruct Checked as [mode Checked]; unfold row_in_mode in Checked.
  destruct (nth_error (token_ids bindings) index) as [binding|] eqn:Read; [|discriminate].
  exists mode, binding; auto.
Qed.

(** This is the Core boundary's paired-presence check. The source store's
    validated-header premise is independent of the execution binding checks.
    Neither None means an available empty declaration roster. *)
Definition paired_presence (header : option D.Header) (bindings : option Bindings) :=
  match header, bindings with
  | None, None | Some _, Some _ => true
  | _, _ => false end.
Theorem paired_presence_refuses_half_published_metadata : forall header bindings,
  paired_presence (Some header) None = false /\
  paired_presence None (Some bindings) = false.
Proof. intros; split; reflexivity. Qed.

Definition publish arena header core pending :=
  match finish header pending with
  | None => None
  | Some bindings => if validate_bindings arena header core bindings
      then Some (header, bindings) else None
  end.
Theorem successful_publication_never_mutates_source_header :
  forall arena header core pending result,
  publish arena header core pending = Some result -> fst result = header.
Proof.
  intros arena header core pending result H; unfold publish in H.
  destruct (finish header pending) as [bindings|]; [|discriminate].
  destruct (validate_bindings arena header core bindings); inversion H; reflexivity.
Qed.
Theorem incomplete_bindings_never_publish : forall arena header core pending,
  finish header pending = None -> publish arena header core pending = None.
Proof. intros; unfold publish; rewrite H; reflexivity. Qed.
Theorem invalid_target_table_never_publishes : forall arena header core pending bindings,
  finish header pending = Some bindings -> validate_bindings arena header core bindings = false ->
  publish arena header core pending = None.
Proof. intros; unfold publish; rewrite H, H0; reflexivity. Qed.
Theorem successful_publication_is_complete_and_checked :
  forall arena header core pending published bindings,
  publish arena header core pending = Some (published, bindings) ->
  published = header /\ finish header pending = Some bindings /\
  validate_bindings arena header core bindings = true.
Proof.
  intros arena header core pending published bindings H; unfold publish in H.
  destruct (finish header pending) as [bound|] eqn:F; [|discriminate].
  destruct (validate_bindings arena header core bound) eqn:V; [|discriminate].
  inversion H; subst; auto.
Qed.

(** Exact final append-site ID and coalescing/overwrite provenance laws.
    These describe existing producer operations, not new classifiers. *)
Theorem append_site_returns_the_new_final_id : forall (prior : list nat) mode,
  nth_error (prior ++ [mode]) (List.length prior) = Some mode.
Proof.
  intros; rewrite nth_error_app2 by lia.
  replace (List.length prior - List.length prior) with 0 by lia; reflexivity.
Qed.
Theorem many_source_rows_may_bind_one_existing_token : forall token,
  List.map direct [ {| direct := token; typed_literal := None |};
                    {| direct := token; typed_literal := None |} ] = [token; token].
Proof. reflexivity. Qed.
Theorem one_source_row_retains_both_routes : forall direct_id auxiliary,
  direct {| direct := direct_id; typed_literal := Some auxiliary |} = direct_id /\
  typed_literal {| direct := direct_id; typed_literal := Some auxiliary |} = Some auxiliary.
Proof. intros; split; reflexivity. Qed.
Definition PatternProvenance := string -> option (nat * string).
Definition replace_pattern (table : PatternProvenance) key source_row pattern : PatternProvenance :=
  fun query => if String.eqb query key then Some (source_row, pattern) else table query.
Theorem last_pattern_write_retains_winning_source_provenance :
  forall table key old_row old_pattern new_row new_pattern,
  replace_pattern (replace_pattern table key old_row old_pattern) key new_row new_pattern key =
  Some (new_row, new_pattern).
Proof. intros; unfold replace_pattern; rewrite String.eqb_refl; reflexivity. Qed.

Print Assumptions write_once_preserves_roster_length.
Print Assumptions write_once_assigns_exact_requested_position.
Print Assumptions already_assigned_slot_refuses_even_equal_value.
Print Assumptions out_of_range_assignment_refuses.
Print Assumptions write_once_preserves_every_other_position.
Print Assumptions finalized_slots_have_exact_order_and_no_unfinished_entry.
Print Assumptions explicit_absent_auxiliary_is_complete.
Print Assumptions unfinished_auxiliary_is_not_absent.
Print Assumptions finish_has_exact_header_cardinalities.
Print Assumptions accepted_token_has_actual_mode_and_membership.
Print Assumptions accepted_binding_checks_both_produced_routes.
Print Assumptions canonical_roster_checker_implies_source_partition.
Print Assumptions partition_and_validation_check_every_source_token.
Print Assumptions paired_presence_refuses_half_published_metadata.
Print Assumptions successful_publication_never_mutates_source_header.
Print Assumptions incomplete_bindings_never_publish.
Print Assumptions invalid_target_table_never_publishes.
Print Assumptions successful_publication_is_complete_and_checked.
Print Assumptions append_site_returns_the_new_final_id.
Print Assumptions many_source_rows_may_bind_one_existing_token.
Print Assumptions one_source_row_retains_both_routes.
Print Assumptions last_pattern_write_retains_winning_source_provenance.
End AuthoredDeclarationBindingProjection.
