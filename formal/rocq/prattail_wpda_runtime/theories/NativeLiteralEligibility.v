(** The original classify_literal_patterned eligibility boundary.

    Source: macros/src/gen/runtime/wpda_codegen/prefix.rs, the outer helper
    around lines 298--329. This is NOT native evaluation or a new literal
    classifier. Native kind resolution, family election, generated labels,
    declared-token lookup and evaluation payloads are opaque original callbacks.
    NativeFirstDescriptorProjection already covers the family/token workers.

    Category lookup here uses ORIGINAL NAME IDENTITY, not spelling; family
    lookup uses its separate original spelling-based worker. The first matching
    category without a native type stops the search. A native observation below
    denotes the retained complete source payload, not just a kind enum.

    NativeClone is the original optional native read plus clone. The generic
    adapter returns the cloned source payload at that site; owned adapters may
    retain a borrowed declaration instead. Label generation can explicitly
    fail when a retained source observation is unavailable; that failure is
    not structural refusal. Static labels always succeed. Existing finite
    callback-failure laws cover the corresponding Result propagation.

    Caller/source obligations: callbacks preserve source results, native/name
    identity, spelling, and original default-evaluator selection; captured
    evaluation presence is not evaluation authority. Payload indices below
    abstract opaque original data; they are not runtime IDs or invented
    evaluators. Source-to-Rust correspondence needs actual captured macro
    differential tests. No allocation/RSS, panic, evaluator correctness,
    decoder parity, or installed-parser cutover claim is made.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import NativeFirstDescriptorProjection PrefixCallbackFailure.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module NativeLiteralEligibility.
Module N := NativeFirstDescriptorProjection.NativeFirstDescriptorProjection.
Module F := PrefixCallbackFailure.PrefixCallbackFailure.

Definition reused_family_law := @N.category_family_and_trace_substitution.
Definition reused_token_law := @N.selected_token_and_trace_substitution.
Definition reused_first_error_law := @F.first_error_skips_any_continuation.

Record Category := {
  category_id : nat;
  category_name : nat;
  category_native : option nat
}.
Record Payload := {
  payload_name : string;
  payload_native : nat;
  payload_family : N.Family;
  payload_label : nat;
  payload_evaluation : nat
}.
Inductive Event :=
| Spelling (name : nat)
| NameIdentity (category name : nat)
| NativeClone (category : nat)
| Kind (native : nat)
| Family (name : string)
| Label (native : nat)
| Declared (name : string)
| Evaluation (token : nat)
| DefaultEvaluation (kind : N.NativeKind).

Section Eligibility.
Context (Error : Type).
Record Context := {
  spelling : nat -> string;
  names_equal : nat -> nat -> bool;
  native_kind : nat -> N.NativeKind;
  literal_family : string -> option N.Family;
  literal_label : nat -> nat + Error;
  declared_token : string -> option nat;
  evaluation : nat -> option nat;
  default_evaluation : N.NativeKind -> option nat
}.
Inductive Outcome := Refused | Eligible (payload : Payload) | Failed (error : Error).
Definition Answer := (Outcome * list Event)%type.
Definition prepend events (answer : Answer) : Answer :=
  (fst answer, events ++ snd answer).

(** Find is the source iter().find predicate, preserving duplicates and first
    identity match. Native presence is observed only AFTER that find. *)
Fixpoint source_find context name categories : option Category * list Event :=
  match categories with
  | [] => (None, [])
  | category :: rest =>
    let event := NameIdentity (category_id category) name in
    if names_equal context (category_name category) name
    then (Some category, [event])
    else let '(found, trace) := source_find context name rest in
         (found, event :: trace)
  end.

(** This tail follows the original helper exactly. The declared/evaluation
    callbacks remain separate, including fallback when a selected token has no
    payload. The default evaluator is NOT replaced with a native-kind guess. *)
Definition after_native context name native : Answer :=
  let kind := native_kind context native in
  let before_family := [Kind native; Family name] in
  match literal_family context name with
  | None => (Refused, before_family)
  | Some family =>
    let before_label := before_family ++ [Label native] in
    match literal_label context native with
    | inr error => (Failed error, before_label)
    | inl label =>
      let make eval := Eligible
        {| payload_name := name; payload_native := native;
           payload_family := family; payload_label := label;
           payload_evaluation := eval |} in
      let fallback := fun trace =>
        (match default_evaluation context kind with
         | Some eval => make eval | None => Refused end,
         trace ++ [DefaultEvaluation kind]) in
      let before_declared := before_label ++ [Declared name] in
      match declared_token context name with
      | Some token =>
        let before_eval := before_declared ++ [Evaluation token] in
        match evaluation context token with
        | Some eval => (make eval, before_eval)
        | None => fallback before_eval
        end
      | None => fallback before_declared
      end
    end
  end.

Definition source_tail context name category : Answer :=
  let trace := [NativeClone (category_id category)] in
  match category_native category with
  | None => (Refused, trace)
  | Some native => prepend trace (after_native context name native)
  end.

Definition source_run context name categories : Answer :=
  let text := spelling context name in
  let '(found, trace) := source_find context name categories in
  prepend (Spelling name :: trace)
    (match found with
     | None => (Refused, [])
     | Some category => source_tail context text category
     end).

Record Reader (C : Type) := {
  read_id : C -> nat;
  read_name : C -> nat;
  read_native_clone : C -> option nat
}.
Fixpoint shared_find {C} (reader : Reader C) context name categories :=
  match categories with
  | [] => (None, [])
  | category :: rest =>
    let event := NameIdentity (read_id reader category) name in
    if names_equal context (read_name reader category) name
    then (Some category, [event])
    else let '(found, trace) := shared_find reader context name rest in
         (found, event :: trace)
  end.
Definition shared_tail {C} (reader : Reader C) context name category : Answer :=
  let trace := [NativeClone (read_id reader category)] in
  match read_native_clone reader category with
  | None => (Refused, trace)
  | Some native => prepend trace (after_native context name native)
  end.
Definition shared_run {C} (reader : Reader C) context name categories : Answer :=
  let text := spelling context name in
  let '(found, trace) := shared_find reader context name categories in
  prepend (Spelling name :: trace)
    (match found with
     | None => (Refused, [])
     | Some category => shared_tail reader context text category
     end).
Record ReaderLaw {C} (reader : Reader C) (project : Category -> C) : Prop := {
  id_law : forall category, read_id reader (project category) = category_id category;
  name_law : forall category, read_name reader (project category) = category_name category;
  native_law : forall category,
    read_native_clone reader (project category) = category_native category
}.

Theorem original_identity_lookup_substitution : forall C (reader : Reader C) project,
  ReaderLaw reader project -> forall context name categories,
  shared_find reader context name (map project categories) =
  let '(found, trace) := source_find context name categories in
  (option_map project found, trace).
Proof.
  intros C reader project law context name categories.
  induction categories as [|category rest IH]; cbn; [reflexivity|].
  rewrite (id_law law), (name_law law).
  destruct (names_equal context (category_name category) name); [reflexivity|].
  rewrite IH. destruct (source_find context name rest); reflexivity.
Qed.

Theorem original_tail_substitution : forall C (reader : Reader C) project,
  ReaderLaw reader project -> forall context name category,
  shared_tail reader context name (project category) = source_tail context name category.
Proof.
  intros. unfold shared_tail, source_tail.
  rewrite (id_law H), (native_law H). reflexivity.
Qed.

Theorem complete_eligibility_source_substitution : forall C (reader : Reader C) project,
  ReaderLaw reader project -> forall context name categories,
  shared_run reader context name (map project categories) = source_run context name categories.
Proof.
  intros C reader project law context name categories.
  unfold shared_run, source_run.
  rewrite (original_identity_lookup_substitution law).
  destruct (source_find context name categories) as [[category|] trace]; cbn; [|reflexivity].
  rewrite (original_tail_substitution law). reflexivity.
Qed.

Lemma first_identity_match_stops_lookup : forall context name category rest,
  names_equal context (category_name category) name = true ->
  source_find context name (category :: rest) =
    (Some category, [NameIdentity (category_id category) name]).
Proof. intros. cbn. rewrite H. reflexivity. Qed.

Lemma first_match_missing_native_is_refusal : forall context name category rest,
  names_equal context (category_name category) name = true ->
  category_native category = None ->
  source_run context name (category :: rest) =
    (Refused, [Spelling name; NameIdentity (category_id category) name;
               NativeClone (category_id category)]).
Proof.
  intros. unfold source_run. cbn [source_find]. rewrite H.
  unfold source_tail. rewrite H0. reflexivity.
Qed.

Lemma absent_family_skips_label_and_evaluation : forall context name native,
  literal_family context name = None ->
  after_native context name native = (Refused, [Kind native; Family name]).
Proof. intros. unfold after_native. rewrite H. reflexivity. Qed.

Lemma label_error_is_not_refusal : forall context name native family error,
  literal_family context name = Some family ->
  literal_label context native = inr error ->
  after_native context name native =
    (Failed error, [Kind native; Family name; Label native]).
Proof. intros. unfold after_native. rewrite H, H0. reflexivity. Qed.

Lemma explicit_evaluation_skips_default : forall context name native family label token eval,
  literal_family context name = Some family ->
  literal_label context native = inl label ->
  declared_token context name = Some token ->
  evaluation context token = Some eval ->
  after_native context name native =
    (Eligible {| payload_name := name; payload_native := native;
                 payload_family := family; payload_label := label;
                 payload_evaluation := eval |},
     [Kind native; Family name; Label native; Declared name; Evaluation token]).
Proof. intros. unfold after_native. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma absent_declared_token_uses_original_default : forall context name native family label,
  literal_family context name = Some family ->
  literal_label context native = inl label ->
  declared_token context name = None ->
  snd (after_native context name native) =
    [Kind native; Family name; Label native; Declared name;
     DefaultEvaluation (native_kind context native)].
Proof.
  intros. unfold after_native. rewrite H, H0, H1.
  destruct (default_evaluation context (native_kind context native)); reflexivity.
Qed.

Lemma absent_selected_evaluation_uses_original_default : forall context name native family label token,
  literal_family context name = Some family ->
  literal_label context native = inl label ->
  declared_token context name = Some token ->
  evaluation context token = None ->
  snd (after_native context name native) =
    [Kind native; Family name; Label native; Declared name; Evaluation token;
     DefaultEvaluation (native_kind context native)].
Proof.
  intros. unfold after_native. rewrite H, H0, H1, H2.
  destruct (default_evaluation context (native_kind context native)); reflexivity.
Qed.

Definition published (answer : Answer) :=
  match fst answer with Eligible payload => Some payload | Refused | Failed _ => None end.
Lemma failure_has_no_payload : forall error trace, published (Failed error, trace) = None.
Proof. reflexivity. Qed.

End Eligibility.

Print Assumptions original_identity_lookup_substitution.
Print Assumptions original_tail_substitution.
Print Assumptions complete_eligibility_source_substitution.
Print Assumptions first_identity_match_stops_lookup.
Print Assumptions first_match_missing_native_is_refusal.
Print Assumptions absent_family_skips_label_and_evaluation.
Print Assumptions label_error_is_not_refusal.
Print Assumptions explicit_evaluation_skips_default.
Print Assumptions absent_declared_token_uses_original_default.
Print Assumptions absent_selected_evaluation_uses_original_default.
Print Assumptions failure_has_no_payload.
End NativeLiteralEligibility.
