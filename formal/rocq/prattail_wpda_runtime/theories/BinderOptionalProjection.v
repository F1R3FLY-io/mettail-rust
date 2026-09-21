(** Bounded source correspondence for the ORIGINAL optional binder classifier.

    Ledger (macro binder.rs, optional_first_token_set / classify_optional_body):
    - SourceStore is an immutable handle interpretation of borrowed SyntaxExpr
      slices and PatternOp references. project_store is a mathematical relation
      witness; it is NOT a recursively allocated Rust view. Each syntax reader
      observes one list cell, each operation reader one operation constructor.
      Names below are exact Ident::to_string observations. Optional bind and Sep
      source handles, unsupported operation handles, list positions and lengths
      are retained; no filtering, rebuilding source, or eager stringification.
    - Frame has the original items/next/positions/args/group_idx fields; the head
      of frames models Vec::last. step is one iteration of the original loop.
      finish pops first, rejects missing child group or empty child positions,
      then appends OptionalGroup followed by Optional(args). Empty ROOT succeeds.
    - dispatch lists every SyntaxExpr branch. Token defaults are __tok_{kind}.
      Guest invokes its helper once at nested_open_kinds's original field site.
      Param Binder makes the collapsed BinderListLoop with both flags false;
      Body/Simple Ident is inert IdentText, other categories are ordinary terms;
      Guard captures Predicate; unknown, bare BinderList/Collection reject.
    - Opt checks u32 increment BEFORE assignment/push. Sep with None source
      examines/clones next Literal BEFORE advancing and parameter lookup.
      BinderList consumes no collection slot and calls no helper. Collection
      checks/assigns u8 increment BEFORE kv; None kv is accepted. Unsupported and
      source-bearing Sep neither follow source handles nor call helpers.
    - Full ordered position/action forests, both external counters, all frames,
      callback state and invocation trace are in Outcome equality. Rejection
      retains prior effects (and diagnostic local frames); Rust drops those
      frames on return None. N bounds avoid enormous unary u32 computations.
    - Shallow reader laws are PROVED from distinct stores, not supplied as a
      classifier-equality premise. The one-step theorem is lifted to each finite
      execution, including fuel exhaustion. Cursor safety proves the original
      expect/index is safe for valid immutable readers, at every reachable step.

    Explicit limits: callbacks are the SAME state transformers in both runs;
    their implementation is not certified. The name-string observation has no
    effects; Rust review must preserve original conversion/field evaluation
    sites, direct NonTerminalKind::classify, original helper captures, and borrowed
    lifetimes. No Rust extraction, allocator/unwind, model lifecycle, all-input
    termination, or parser completeness theorem is asserted. The existing model
    lifecycle relocation is not certified by this file. This is a transcription
    and reader-substitution proof, not a newly derived parser automaton.
*)
From Stdlib Require Import List String Bool Arith NArith Lia.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module BinderOptionalProjection.

(** Handles need no recursive view data. Opaque payloads remain at their original
    position. Separate source/view constructors make the projection explicit. *)
Inductive SourceSyntax :=
| SLiteral (text : string)
| SParam (name : string)
| STokenKind (name : string) (bind : option string)
| SGuestBody (open close bind : string) (kind : nat)
| SOp (operation : nat).
Inductive SourceOperation :=
| SOpt (child_sequence : nat)
| SSep (name separator : string) (source : option nat)
| SUnsupported (opaque : nat).
Inductive SyntaxObservation :=
| Literal (text : string)
| Param (name : string)
| TokenKind (name : string) (bind : option string)
| GuestBody (open close bind : string) (kind : nat)
| Op (operation : nat).
Inductive OperationObservation :=
| Opt (child_sequence : nat)
| Sep (name separator : string) (source : option nat)
| Other (original_operation : nat).

Definition project_syntax item := match item with
| SLiteral text => Literal text
| SParam name => Param name
| STokenKind name bind => TokenKind name bind
| SGuestBody open close bind kind => GuestBody open close bind kind
| SOp operation => Op operation end.
Definition project_operation handle item := match item with
| SOpt child => Opt child
| SSep name separator source => Sep name separator source
| SUnsupported _ => Other handle end.
Record SourceStore := {
  source_sequences : nat -> list SourceSyntax;
  source_operations : nat -> SourceOperation
}.
Record ViewStore := {
  view_sequences : nat -> list SyntaxObservation;
  view_operations : nat -> OperationObservation
}.
Definition project_store store :=
 {| view_sequences := fun handle => map project_syntax (source_sequences store handle);
    view_operations := fun handle =>
      project_operation handle (source_operations store handle) |}.
Record Reader := {
  sequence_len : nat -> nat;
  syntax_at : nat -> nat -> option SyntaxObservation;
  operation_at : nat -> OperationObservation
}.
Definition source_reader store :=
 {| sequence_len := fun handle => List.length (source_sequences store handle);
    syntax_at := fun handle index =>
      option_map project_syntax (nth_error (source_sequences store handle) index);
    operation_at := fun handle => project_operation handle (source_operations store handle) |}.
Definition view_reader store :=
 {| sequence_len := fun handle => List.length (view_sequences store handle);
    syntax_at := fun handle index => nth_error (view_sequences store handle) index;
    operation_at := view_operations store |}.

Lemma map_nth_exact : forall A B (f : A -> B) xs index,
  nth_error (map f xs) index = option_map f (nth_error xs index).
Proof. intros A B f xs; induction xs; intros [|index]; cbn; auto. Qed.
Theorem sequence_length_correspondence : forall store handle,
  sequence_len (view_reader (project_store store)) handle =
  sequence_len (source_reader store) handle.
Proof. intros; cbn; apply length_map. Qed.
Theorem sequence_nth_correspondence : forall store handle index,
  syntax_at (view_reader (project_store store)) handle index =
  syntax_at (source_reader store) handle index.
Proof. intros; cbn; apply map_nth_exact. Qed.
Theorem operation_correspondence : forall store handle,
  operation_at (view_reader (project_store store)) handle =
  operation_at (source_reader store) handle.
Proof. reflexivity. Qed.
Theorem all_syntax_payloads_preserved : forall text name bind open close guest kind op,
  project_syntax (SLiteral text) = Literal text /\
  project_syntax (SParam name) = Param name /\
  project_syntax (STokenKind name bind) = TokenKind name bind /\
  project_syntax (SGuestBody open close guest kind) = GuestBody open close guest kind /\
  project_syntax (SOp op) = Op op.
Proof. intros; repeat split; reflexivity. Qed.
Theorem optional_and_source_handles_preserved : forall handle child name sep source opaque,
  project_operation handle (SOpt child) = Opt child /\
  project_operation handle (SSep name sep source) = Sep name sep source /\
  project_operation handle (SUnsupported opaque) = Other handle.
Proof. intros; repeat split; reflexivity. Qed.

Definition ReaderValid reader := forall handle index,
  syntax_at reader handle index <> None <-> index < sequence_len reader handle.
Theorem source_reader_valid : forall store, ReaderValid (source_reader store).
Proof.
  intros store handle index; cbn.
  destruct (nth_error (source_sequences store handle) index) eqn:E; cbn.
  - split; [intros _; apply nth_error_Some; rewrite E; discriminate|discriminate].
  - split; [contradiction|intros L; apply nth_error_Some in L; rewrite E in L; contradiction].
Qed.
Theorem view_reader_valid : forall store, ReaderValid (view_reader store).
Proof. intros store handle index; cbn; apply nth_error_Some. Qed.

(** All descriptor fields produced in this slice are explicit. *)
Record CollectionSepInfo := {
  collection_separator : string; collection_close : string;
  collection_element : string; key_val_separator : option string; slot_idx : N
}.
Inductive Position :=
| PLiteral (text : string)
| PToken (kind_name param_name : string)
| PIdentText (param_name : string)
| PGuest (open : string) (nested : list string) (close param_name : string)
| PBinderIdent
| PBinderList (separator close : string) (inner : list Position)
    (collection_param_cat : option string) (allow_empty allow_multi : bool) (slot : N)
| PParam (cat : string) (collection : option CollectionSepInfo)
| PGuard
| POptional (positions : list Position) (group_idx : N) (first_tokens : list string).
Inductive Action :=
| ATokenText (param_name : string)
| AGuest (param_name : string) (kind : nat)
| ABinderName
| AIdentText (param_name : string)
| ATerm (cat : string)
| APredicate
| ABinderList
| ACollection (element : string) (kind : nat)
| AOptional (args : list Action).
Inductive ParamKind :=
| Binder | Body (cat : string) | Simple (cat : string) | Guard
| BinderList | Collection (element : string) (kind : nat).

Definition first_token_set positions := match positions with
| PLiteral text :: _ => [text]
| POptional _ _ tokens :: _ => tokens
| _ => [] end.
Record Frame := {
  items : nat; next : nat; positions : list Position;
  args : list Action; group_idx : option N
}.
Definition empty_frame sequence group :=
 {| items := sequence; next := 0; positions := []; args := []; group_idx := group |}.
Definition advance frame :=
 {| items := items frame; next := S (next frame); positions := positions frame;
    args := args frame; group_idx := group_idx frame |}.
Definition append_outputs frame ps actions :=
 {| items := items frame; next := next frame;
    positions := (positions frame ++ ps)%list;
    args := (args frame ++ actions)%list; group_idx := group_idx frame |}.
Definition u32_max : N := 4294967295%N.
Definition u8_max : N := 255%N.
Definition checked_increment limit value :=
  if N.ltb value limit then Some (N.succ value) else None.
Theorem checked_increment_exact : forall limit value updated,
  checked_increment limit value = Some updated <->
  (value < limit)%N /\ updated = N.succ value.
Proof.
  intros; unfold checked_increment; destruct (N.ltb value limit) eqn:E.
  - apply N.ltb_lt in E; split; [intro H; inversion H; auto|intros [_ ->]; reflexivity].
  - apply N.ltb_ge in E; split; [discriminate|intros [L _]; lia].
Qed.
Corollary checked_increment_never_exceeds_bound : forall limit value updated,
  checked_increment limit value = Some updated -> (updated <= limit)%N.
Proof. intros; apply checked_increment_exact in H; destruct H as [L ->]; lia. Qed.

Inductive Event :=
| GuestCall (open : string) (group_counter slot_counter : N)
| KeyValueCall (kind : nat) (group_counter slot_counter : N).

Section CallbackState.
Context {State : Type}.
Record Effects := {
  next_group : N; collection_slots : N; callback_state : State; trace : list Event
}.
Record Configuration := { frames : list Frame; effects : Effects }.
Inductive Outcome :=
| Continue (configuration : Configuration)
| Accepted (configuration : Configuration) (result_positions : list Position) (result_args : list Action)
| Rejected (configuration : Configuration).
Definition configure stack effect := {| frames := stack; effects := effect |}.
Definition resume frame rest effect := Continue (configure (frame :: rest) effect).
Definition reject frame rest effect := Rejected (configure (frame :: rest) effect).
Definition set_group e counter :=
 {| next_group := counter; collection_slots := collection_slots e;
    callback_state := callback_state e; trace := trace e |}.
Definition set_slots e counter :=
 {| next_group := next_group e; collection_slots := counter;
    callback_state := callback_state e; trace := trace e |}.
Definition after_callback e state event :=
 {| next_group := next_group e; collection_slots := collection_slots e;
    callback_state := state; trace := (trace e ++ [event])%list |}.
Definition outcome_configuration result := match result with
| Continue c | Accepted c _ _ | Rejected c => c end.

Variable parameters : string -> option ParamKind.
Variable guest_openers : string -> State -> list string * State.
Variable key_value : nat -> State -> option string * State.

Definition term_parameter frame rest e name cat :=
  if String.eqb cat "Ident" then
    resume (append_outputs frame [PIdentText name] [AIdentText name]) rest e
  else resume (append_outputs frame [PParam cat None] [ATerm cat]) rest e.
Definition parameter_step frame rest e name :=
  match parameters name with
  | Some Binder => resume (append_outputs frame
      [PBinderList "" "" [PBinderIdent] None false false 0%N] [ABinderName]) rest e
  | Some (Body cat) | Some (Simple cat) => term_parameter frame rest e name cat
  | Some Guard => resume (append_outputs frame [PGuard] [APredicate]) rest e
  | _ => reject frame rest e end.

Definition separator_step reader frame rest e name separator :=
  match syntax_at reader (items frame) (next frame) with
  | Some (Literal close) =>
      let consumed := advance frame in
      match parameters name with
      | Some BinderList => resume (append_outputs consumed
          [PBinderList separator close [PBinderIdent] None true true 0%N]
          [ABinderList]) rest e
      | Some (Collection element kind) =>
          let slot := collection_slots e in
          match checked_increment u8_max slot with
          | None => reject consumed rest e
          | Some updated =>
              let allocated := set_slots e updated in
              let '(pair_value, state) := key_value kind (callback_state allocated) in
              let called := after_callback allocated state
                (KeyValueCall kind (next_group allocated) (collection_slots allocated)) in
              resume (append_outputs consumed
                [PParam element (Some
                  {| collection_separator := separator; collection_close := close;
                     collection_element := element; key_val_separator := pair_value;
                     slot_idx := slot |})] [ACollection element kind]) rest called
          end
      | _ => reject consumed rest e end
  | _ => reject frame rest e end.

Definition operation_step reader frame rest e operation :=
  match operation_at reader operation with
  | Opt child =>
      let group := next_group e in
      match checked_increment u32_max group with
      | None => reject frame rest e
      | Some updated => Continue (configure
          (empty_frame child (Some group) :: frame :: rest) (set_group e updated)) end
  | Sep name separator None => separator_step reader frame rest e name separator
  | _ => reject frame rest e end.

Definition dispatch reader frame rest e item := match item with
  | Literal text => resume (append_outputs frame [PLiteral text] []) rest e
  | Param name => parameter_step frame rest e name
  | TokenKind name bind =>
      let param_name := match bind with Some name => name | None => "__tok_" ++ name end in
      resume (append_outputs frame [PToken name param_name] [ATokenText param_name]) rest e
  | GuestBody open close bind kind =>
      let '(nested, state) := guest_openers open (callback_state e) in
      let called := after_callback e state (GuestCall open (next_group e) (collection_slots e)) in
      resume (append_outputs frame [PGuest open nested close bind] [AGuest bind kind]) rest called
  | Op operation => operation_step reader frame rest e operation end.

Definition finish completed rest e := match rest with
  | [] => Accepted (configure [] e) (positions completed) (args completed)
  | parent :: ancestors => match group_idx completed, positions completed with
      | Some group, (_ :: _) =>
          resume (append_outputs parent
            [POptional (positions completed) group (first_token_set (positions completed))]
            [AOptional (args completed)]) ancestors e
      | _, _ => Rejected (configure rest e) end end.
Definition step reader configuration :=
  let e := effects configuration in
  match frames configuration with
  | [] => Rejected configuration
  | frame :: rest =>
      if Nat.eqb (next frame) (sequence_len reader (items frame))
      then finish frame rest e
      else let consumed := advance frame in
        match syntax_at reader (items frame) (next frame) with
        | Some item => dispatch reader consumed rest e item
        | None => reject consumed rest e (* unreachable for a valid bounded cursor *)
        end end.
Fixpoint execute fuel reader configuration := match fuel with
  | 0 => Continue configuration
  | S remaining => match step reader configuration with
      | Continue next_configuration => execute remaining reader next_configuration
      | other => other end end.
Definition initial root group slots state :=
  configure [empty_frame root None]
    {| next_group := group; collection_slots := slots; callback_state := state; trace := [] |}.

(** A read-only substitution in the ORIGINAL frame loop, not an assumption
    about classifier results. No callback equality premise is needed: the
    callback terms are shared, at the precise sites above, in both interpreters. *)
Theorem original_frame_step_simulation : forall store configuration,
  step (view_reader (project_store store)) configuration =
  step (source_reader store) configuration.
Proof.
  intros store [stack e]; destruct stack as [|frame rest]; [reflexivity|].
  unfold step, dispatch, operation_step, separator_step.
  cbn [frames effects].
  rewrite sequence_length_correspondence.
  destruct (Nat.eqb (next frame) (sequence_len (source_reader store) (items frame)));
    [reflexivity|].
  rewrite sequence_nth_correspondence.
  destruct (syntax_at (source_reader store) (items frame) (next frame)) as [item|];
    [destruct item|]; try reflexivity.
  rewrite operation_correspondence.
  destruct (operation_at (source_reader store) operation) as [child|name sep source|opaque];
    try reflexivity.
  destruct source; [reflexivity|].
  rewrite sequence_nth_correspondence; reflexivity.
Qed.
Theorem finite_execution_preserves_full_result_and_effects : forall fuel store configuration,
  execute fuel (view_reader (project_store store)) configuration =
  execute fuel (source_reader store) configuration.
Proof.
  induction fuel; intros; cbn; [reflexivity|].
  rewrite original_frame_step_simulation.
  destruct (step (source_reader store) configuration); auto.
Qed.

(** Cursor proof covers all outcomes, including retained local cursors at a
    failure. A callback cannot change syntax: its state is a separate field. *)
Definition frame_safe reader frame := next frame <= sequence_len reader (items frame).
Definition stack_safe reader stack := Forall (frame_safe reader) stack.
Definition configuration_safe reader c := stack_safe reader (frames c).
Definition outcome_safe reader result := configuration_safe reader (outcome_configuration result).
Lemma append_safe : forall reader frame ps actions,
  frame_safe reader frame -> frame_safe reader (append_outputs frame ps actions).
Proof. auto. Qed.
Lemma resume_safe : forall reader frame rest e,
  frame_safe reader frame -> stack_safe reader rest -> outcome_safe reader (resume frame rest e).
Proof. intros; unfold outcome_safe, configuration_safe, stack_safe; cbn; constructor; auto. Qed.
Lemma reject_safe : forall reader frame rest e,
  frame_safe reader frame -> stack_safe reader rest -> outcome_safe reader (reject frame rest e).
Proof. intros; unfold outcome_safe, configuration_safe, stack_safe; cbn; constructor; auto. Qed.
#[local] Hint Resolve append_safe resume_safe reject_safe : core.

Lemma parameter_step_safe : forall reader frame rest e name,
  frame_safe reader frame -> stack_safe reader rest ->
  outcome_safe reader (parameter_step frame rest e name).
Proof.
  intros; unfold parameter_step, term_parameter.
  destruct (parameters name) as [[|cat|cat| | |element kind]|]; auto;
    destruct (String.eqb cat "Ident"); auto.
Qed.
Lemma separator_step_safe : forall reader frame rest e name sep,
  ReaderValid reader -> frame_safe reader frame -> stack_safe reader rest ->
  outcome_safe reader (separator_step reader frame rest e name sep).
Proof.
  intros reader frame rest e name sep Valid Safe Rest.
  unfold separator_step.
  destruct (syntax_at reader (items frame) (next frame)) as [item|] eqn:Read; auto.
  destruct item; auto.
  assert (Advanced : frame_safe reader (advance frame)).
  { unfold frame_safe, advance; cbn.
    assert (next frame < sequence_len reader (items frame)).
    { apply Valid. rewrite Read. discriminate. } lia. }
  destruct (parameters name) as [[|cat|cat| | |element kind]|]; auto.
  destruct (checked_increment u8_max (collection_slots e)) as [updated|]; auto.
  destruct (key_value kind (callback_state (set_slots e updated))); auto.
Qed.
Lemma operation_step_safe : forall reader frame rest e operation,
  ReaderValid reader -> frame_safe reader frame -> stack_safe reader rest ->
  outcome_safe reader (operation_step reader frame rest e operation).
Proof.
  intros reader frame rest e operation Valid Safe Rest; unfold operation_step.
  destruct (operation_at reader operation) as [child|name sep source|opaque]; auto.
  - destruct (checked_increment u32_max (next_group e)); auto.
    unfold outcome_safe, configuration_safe, stack_safe; cbn.
    constructor; [unfold frame_safe; cbn; lia|constructor; auto].
  - destruct source; auto. apply separator_step_safe; auto.
Qed.
Lemma dispatch_safe : forall reader frame rest e item,
  ReaderValid reader -> frame_safe reader frame -> stack_safe reader rest ->
  outcome_safe reader (dispatch reader frame rest e item).
Proof.
  intros reader frame rest e item Valid Safe Rest; destruct item; cbn [dispatch]; auto.
  - apply parameter_step_safe; auto.
  - destruct (guest_openers open (callback_state e)); auto.
  - apply operation_step_safe; auto.
Qed.
Lemma finish_safe : forall reader completed rest e,
  stack_safe reader rest -> outcome_safe reader (finish completed rest e).
Proof.
  intros reader completed [|parent ancestors] e Rest; cbn [finish].
  - constructor.
  - inversion Rest; subst.
    destruct (group_idx completed); [destruct (positions completed)|]; auto.
Qed.
Theorem original_frame_step_preserves_cursor_bound : forall reader configuration,
  ReaderValid reader -> configuration_safe reader configuration ->
  outcome_safe reader (step reader configuration).
Proof.
  intros reader [stack e] Valid Safe; unfold step; cbn.
  destruct stack as [|frame rest]; [exact Safe|].
  inversion Safe as [|? ? FrameSafe Rest]; subst.
  destruct (Nat.eqb (next frame) (sequence_len reader (items frame))) eqn:Finished.
  - apply finish_safe; assumption.
  - apply Nat.eqb_neq in Finished.
    assert (Bound : next frame < sequence_len reader (items frame)).
    { unfold frame_safe in FrameSafe; lia. }
    assert (Advanced : frame_safe reader (advance frame)).
    { unfold frame_safe, advance; cbn; lia. }
    destruct (syntax_at reader (items frame) (next frame)) eqn:Read.
    + apply dispatch_safe; auto.
    + exfalso. apply Valid in Bound. apply Bound. exact Read.
Qed.
Theorem finite_execution_preserves_cursor_bound : forall fuel reader configuration,
  ReaderValid reader -> configuration_safe reader configuration ->
  outcome_safe reader (execute fuel reader configuration).
Proof.
  induction fuel; intros reader configuration Valid Safe; cbn; [exact Safe|].
  pose proof (original_frame_step_preserves_cursor_bound Valid Safe) as StepSafe.
  destruct (step reader configuration); auto.
Qed.
Theorem initial_cursor_bound : forall reader root group slots state,
  configuration_safe reader (initial root group slots state).
Proof. intros; constructor; [unfold frame_safe; cbn; lia|constructor]. Qed.
Theorem original_index_expect_is_safe : forall reader frame,
  ReaderValid reader -> frame_safe reader frame ->
  next frame <> sequence_len reader (items frame) ->
  exists item, syntax_at reader (items frame) (next frame) = Some item.
Proof.
  intros reader frame Valid Safe Unfinished.
  assert (Bound : next frame < sequence_len reader (items frame)).
  { unfold frame_safe in Safe; lia. }
  apply Valid in Bound.
  destruct (syntax_at reader (items frame) (next frame)); [eauto|contradiction].
Qed.

(** Small branch laws expose ordering and failure prefixes for source review. *)
Theorem empty_root_succeeds : forall reader root e,
  sequence_len reader root = 0 ->
  step reader (configure [empty_frame root None] e) = Accepted (configure [] e) [] [].
Proof. intros; unfold step; cbn; rewrite H; reflexivity. Qed.
Theorem empty_child_rejects_after_allocated_group : forall reader child parent rest e group,
  sequence_len reader child = 0 ->
  step reader (configure (empty_frame child (Some group) :: parent :: rest) e) =
  Rejected (configure (parent :: rest) e).
Proof. intros; unfold step; cbn; rewrite H; reflexivity. Qed.
Theorem option_overflow_retains_effect_prefix : forall reader frame rest e operation child,
  operation_at reader operation = Opt child -> next_group e = u32_max ->
  operation_step reader frame rest e operation = reject frame rest e.
Proof. intros; unfold operation_step; rewrite H, H0; reflexivity. Qed.
Theorem sourced_sep_does_not_traverse_or_call : forall reader frame rest e operation name sep source,
  operation_at reader operation = Sep name sep (Some source) ->
  operation_step reader frame rest e operation = reject frame rest e.
Proof. intros; unfold operation_step; now rewrite H. Qed.
Theorem unsupported_operation_does_not_call : forall reader frame rest e operation opaque,
  operation_at reader operation = Other opaque ->
  operation_step reader frame rest e operation = reject frame rest e.
Proof. intros; unfold operation_step; now rewrite H. Qed.
Theorem unknown_parameter_retains_prefix : forall frame rest e name,
  parameters name = None -> parameter_step frame rest e name = reject frame rest e.
Proof. intros; unfold parameter_step; now rewrite H. Qed.
Theorem binder_is_collapsed_with_both_flags_false : forall frame rest e name,
  parameters name = Some Binder ->
  parameter_step frame rest e name = resume (append_outputs frame
    [PBinderList "" "" [PBinderIdent] None false false 0%N] [ABinderName]) rest e.
Proof. intros; unfold parameter_step; now rewrite H. Qed.
Theorem binder_list_never_allocates_slot_or_calls : forall reader frame rest e name sep close,
  syntax_at reader (items frame) (next frame) = Some (Literal close) ->
  parameters name = Some BinderList ->
  separator_step reader frame rest e name sep = resume (append_outputs (advance frame)
    [PBinderList sep close [PBinderIdent] None true true 0%N] [ABinderList]) rest e.
Proof. intros; unfold separator_step; now rewrite H, H0. Qed.
Theorem nonempty_child_appends_position_then_action : forall completed parent rest e group first tail,
  group_idx completed = Some group -> positions completed = first :: tail ->
  finish completed (parent :: rest) e = resume (append_outputs parent
    [POptional (positions completed) group (first_token_set (positions completed))]
    [AOptional (args completed)]) rest e.
Proof. intros; unfold finish; rewrite H, H0; reflexivity. Qed.
Theorem invalid_close_does_not_lookup_or_allocate : forall reader frame rest e name sep,
  (forall close, syntax_at reader (items frame) (next frame) <> Some (Literal close)) ->
  separator_step reader frame rest e name sep = reject frame rest e.
Proof.
  intros reader frame rest e name sep Invalid; unfold separator_step.
  destruct (syntax_at reader (items frame) (next frame)) as [item|] eqn:Read; auto.
  destruct item; auto. exfalso. apply (Invalid text); congruence.
Qed.
Theorem collection_overflow_advances_close_but_never_calls : forall reader frame rest e name sep close element kind,
  syntax_at reader (items frame) (next frame) = Some (Literal close) ->
  parameters name = Some (Collection element kind) -> collection_slots e = u8_max ->
  separator_step reader frame rest e name sep = reject (advance frame) rest e.
Proof. intros; unfold separator_step; rewrite H, H0, H1; reflexivity. Qed.
Theorem kv_none_succeeds_after_slot_assignment : forall reader frame rest e name sep close element kind updated state,
  syntax_at reader (items frame) (next frame) = Some (Literal close) ->
  parameters name = Some (Collection element kind) ->
  checked_increment u8_max (collection_slots e) = Some updated ->
  key_value kind (callback_state e) = (None, state) ->
  separator_step reader frame rest e name sep =
    resume (append_outputs (advance frame)
      [PParam element (Some {| collection_separator := sep; collection_close := close;
        collection_element := element; key_val_separator := None; slot_idx := collection_slots e |})]
      [ACollection element kind]) rest
      (after_callback (set_slots e updated) state (KeyValueCall kind (next_group e) updated)).
Proof. intros; unfold separator_step; rewrite H, H0, H1; cbn; rewrite H2; reflexivity. Qed.
Theorem guest_called_once_at_field_site : forall reader frame rest e open close bind kind nested state,
  guest_openers open (callback_state e) = (nested, state) ->
  dispatch reader frame rest e (GuestBody open close bind kind) =
    resume (append_outputs frame [PGuest open nested close bind] [AGuest bind kind]) rest
      (after_callback e state (GuestCall open (next_group e) (collection_slots e))).
Proof. intros; cbn [dispatch]; now rewrite H. Qed.

End CallbackState.

Print Assumptions sequence_length_correspondence.
Print Assumptions sequence_nth_correspondence.
Print Assumptions all_syntax_payloads_preserved.
Print Assumptions optional_and_source_handles_preserved.
Print Assumptions checked_increment_exact.
Print Assumptions original_frame_step_simulation.
Print Assumptions finite_execution_preserves_full_result_and_effects.
Print Assumptions finite_execution_preserves_cursor_bound.
Print Assumptions original_index_expect_is_safe.
Print Assumptions option_overflow_retains_effect_prefix.
Print Assumptions collection_overflow_advances_close_but_never_calls.
Print Assumptions kv_none_succeeds_after_slot_assignment.
Print Assumptions guest_called_once_at_field_site.
Print Assumptions binder_list_never_allocates_slot_or_calls.
Print Assumptions nonempty_child_appends_position_then_action.
End BinderOptionalProjection.
