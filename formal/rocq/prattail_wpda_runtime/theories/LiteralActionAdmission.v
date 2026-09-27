(** * Original literal-row authority at the selected-occurrence boundary

    Source map: wpda_owned/actions/provider.rs::literal and its synthetic
    literal row construction; descriptors.prefixes contains the original
    atomic_prefix::atomic_arm_descriptors HomeCategory rows, not a new literal
    classifier. token_bindings::{resolve,matches_prefix} supply the existing
    retained kind observation and pattern/guard interpretation.

    A Core token's category tag is optional: the macro bridge emits untagged
    builtin tokens. Absence is not authority by itself. Only an original atomic
    home row at the exact action category/rule coordinates can admit that case.
    A present contradictory tag remains an error. The selected TokenId, token
    text, and kind must remain exact; no decoder is chosen by token spelling.

    The finite model composes TerminalOccurrence and TokenKindBindingObservation
    with the existing OwnedActionAdapter decode boundary. It does not prove
    arbitrary source metadata truthful, authorize a host, equate all native
    evaluators, or establish whole-parser equivalence. Those existing source
    projection and host-admission obligations remain unchanged. *)
From Stdlib Require Import List String Bool Arith.PeanoNat.
From PrattailWpdaRuntime Require Import
  TerminalOccurrence TokenKindBindingObservation OwnedActionAdapter.
Import ListNotations.
Local Open Scope type_scope.

Module LiteralActionAdmission.
Module T := TerminalOccurrence.TerminalOccurrence.
Module K := TokenKindBindingObservation.TokenKindBindingObservation.
Module A := OwnedActionAdapter.OwnedActionAdapter.

Definition reused_selected_occurrence_law := @T.selected_decoder_input_is_exact.
Definition reused_token_kind_law := @K.exact_append_site_observation.
Definition reused_decoded_payload_law := @A.successful_decode_is_one_call_and_both_projections.

Record Edge := {
  edge_token : nat;
  edge_text : string;
  edge_category : option nat
}.
Record Argument := {
  occurrence : option nat;
  argument_kind : nat;
  argument_text : string
}.
Record HomeRow := {
  row_category : nat;
  row_rule : nat;
  row_pattern : nat;
  row_guard : option nat
}.

Section Admission.
Variable matches_original : nat -> option nat -> nat -> bool.
Variable true_kind false_kind : nat.

Definition home_witness category rule kind rows :=
  existsb (fun row =>
    Nat.eqb (row_category row) category && Nat.eqb (row_rule row) rule &&
      matches_original (row_pattern row) (row_guard row) kind) rows.

(* Action coordinates and Core category IDs are distinct domains. The adapter's
   authored_action_categories mapping supplies core_category; it is not assumed
   equal to the source category coordinate retained by HomeRow. *)
Definition category_gate action_category core_category rule kind rows tagged :=
  match tagged with
  | Some actual => Nat.eqb actual core_category
  | None => home_witness action_category rule kind rows
  end.

Definition source_kind bindings edge argument :=
  @K.lookup nat true_kind false_kind bindings (edge_token edge) (argument_text argument).

Definition admitted action_category core_category rule rows bindings expected_token edge argument :=
  (match expected_token with
   | Some token => Nat.eqb token (edge_token edge)
   | None => true
   end) &&
  String.eqb (edge_text edge) (argument_text argument) &&
  (match source_kind bindings edge argument with
   | Some kind => Nat.eqb kind (argument_kind argument)
   | None => false
   end) &&
  category_gate action_category core_category rule (argument_kind argument) rows (edge_category edge).

Theorem untagged_requires_original_home_witness : forall action_category core_category rule kind rows,
  category_gate action_category core_category rule kind rows None = true ->
  home_witness action_category rule kind rows = true.
Proof. exact (fun _ _ _ _ _ H => H). Qed.

Theorem matching_tag_retains_original_admission : forall action_category core_category rule kind rows,
  category_gate action_category core_category rule kind rows (Some core_category) = true.
Proof. intros; unfold category_gate; apply Nat.eqb_refl. Qed.

Theorem contradictory_tag_is_not_repaired_by_a_matching_row : forall action_category core_category actual rule kind rows,
  actual <> core_category -> category_gate action_category core_category rule kind rows (Some actual) = false.
Proof. intros; unfold category_gate; now apply Nat.eqb_neq. Qed.

Theorem absent_home_rows_do_not_authorize_an_untagged_token : forall action_category core_category rule kind,
  category_gate action_category core_category rule kind [] None = false.
Proof. reflexivity. Qed.

Theorem retained_source_kind_is_the_original_observation : forall bindings edge argument row,
  nth_error bindings (edge_token edge) = Some (Some row) ->
  source_kind bindings edge argument =
    Some (@K.observe nat true_kind false_kind row (argument_text argument)).
Proof. intros; unfold source_kind; now apply K.exact_append_site_observation. Qed.

Theorem admission_requires_text_kind_and_category : forall action_category core_category rule rows bindings token edge argument,
  admitted action_category core_category rule rows bindings token edge argument = true ->
  edge_text edge = argument_text argument /\
  source_kind bindings edge argument = Some (argument_kind argument) /\
  category_gate action_category core_category rule (argument_kind argument) rows (edge_category edge) = true.
Proof.
  intros action_category core_category rule rows bindings token edge argument H.
  unfold admitted in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[Htoken Htext] Hkind] Hcategory].
  apply String.eqb_eq in Htext. split; [exact Htext|].
  split; [|exact Hcategory].
  destruct (source_kind bindings edge argument) as [kind|] eqn:E; [|discriminate].
  apply Nat.eqb_eq in Hkind. now subst kind.
Qed.

Section Decoder.
Context {Payload Fault State : Type}.
Variable invalid : Fault.
Variable decode : nat -> string -> State -> (Fault + Payload) * State.

(** No callback is performed by any failed observation. The successful call's
    complete result/state pair is retained, including decoder failure. *)
Definition dispatch action_category core_category rule rows bindings expected_token edges argument state
    : ((Fault + Payload) * State) * list nat :=
  match @T.resolve Edge edges (occurrence argument) with
  | None => ((inl invalid, state), [])
  | Some edge =>
    if admitted action_category core_category rule rows bindings expected_token edge argument then
      (decode (edge_token edge) (argument_text argument) state, [edge_token edge])
    else ((inl invalid, state), [])
  end.

Theorem absent_occurrence_invokes_no_decoder : forall action_category core_category rule rows bindings token edges kind text state,
  dispatch action_category core_category rule rows bindings token edges
    {| occurrence := None; argument_kind := kind; argument_text := text |} state =
  ((inl invalid, state), []).
Proof. reflexivity. Qed.

Theorem invalid_occurrence_invokes_no_decoder : forall action_category core_category rule rows bindings token edges argument state,
  @T.resolve Edge edges (occurrence argument) = None ->
  dispatch action_category core_category rule rows bindings token edges argument state = ((inl invalid, state), []).
Proof. intros; unfold dispatch; now rewrite H. Qed.

Theorem failed_admission_invokes_no_decoder : forall action_category core_category rule rows bindings token edges argument state edge,
  @T.resolve Edge edges (occurrence argument) = Some edge ->
  admitted action_category core_category rule rows bindings token edge argument = false ->
  dispatch action_category core_category rule rows bindings token edges argument state = ((inl invalid, state), []).
Proof. intros; unfold dispatch; now rewrite H, H0. Qed.

Theorem successful_admission_calls_exact_selected_decoder_once : forall action_category core_category rule rows bindings token edges argument state edge,
  @T.resolve Edge edges (occurrence argument) = Some edge ->
  admitted action_category core_category rule rows bindings token edge argument = true ->
  dispatch action_category core_category rule rows bindings token edges argument state =
    (decode (edge_token edge) (argument_text argument) state, [edge_token edge]).
Proof. intros; unfold dispatch; now rewrite H, H0. Qed.

Theorem decoder_fault_and_state_are_not_reclassified : forall action_category core_category rule rows bindings token edges argument state edge fault next,
  @T.resolve Edge edges (occurrence argument) = Some edge ->
  admitted action_category core_category rule rows bindings token edge argument = true ->
  decode (edge_token edge) (argument_text argument) state = (inl fault, next) ->
  dispatch action_category core_category rule rows bindings token edges argument state =
    ((inl fault, next), [edge_token edge]).
Proof. intros; unfold dispatch; now rewrite H, H0, H1. Qed.
End Decoder.
End Admission.

Print Assumptions reused_selected_occurrence_law.
Print Assumptions reused_token_kind_law.
Print Assumptions reused_decoded_payload_law.
Print Assumptions untagged_requires_original_home_witness.
Print Assumptions matching_tag_retains_original_admission.
Print Assumptions contradictory_tag_is_not_repaired_by_a_matching_row.
Print Assumptions absent_home_rows_do_not_authorize_an_untagged_token.
Print Assumptions retained_source_kind_is_the_original_observation.
Print Assumptions admission_requires_text_kind_and_category.
Print Assumptions absent_occurrence_invokes_no_decoder.
Print Assumptions invalid_occurrence_invokes_no_decoder.
Print Assumptions failed_admission_invokes_no_decoder.
Print Assumptions successful_admission_calls_exact_selected_decoder_once.
Print Assumptions decoder_fault_and_state_are_not_reclassified.
End LiteralActionAdmission.
