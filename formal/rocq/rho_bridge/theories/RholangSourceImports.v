(** Exact caller-import transport for direct whole-body preparation.

    An import table is the existing caller map's ordered association list.
    Payloads remain polymorphic here: admission returns the original values,
    without a neutral carrier, synthetic owner slots, decoding or evaluation.
    The supplied Boolean check is an executable parameter, not an assumption
    that every payload is valid. These laws establish what happens for each
    result of that check; they do not prove the concrete Par shape validator,
    host capability ownership, resource precharge or cancellation polling.

    The Rust refinement must establish the ordered-map projection and actual
    validator correspondence. Import keys do not bind bare source variables.
    Every source New retains all admitted entries; generated service-reply
    scopes retain none. Runtime URI lookup still precedes injection fallback.
    Transporting a private name does not grant or re-check an action right;
    the existing provider remains responsible for authorization at use.

    The last section instantiates transport with the existing construction
    algebra only to reuse FreshDescriptor's layout and metadata laws. It does
    not introduce a neutral representation into the direct implementation. *)
From Stdlib Require Import List String Bool.
From RhoBridge Require Import RholangTargetConstruction RholangConstructionProtocol
  RholangFreshDescriptor RholangSourceScope.
Import ListNotations.

Definition ImportEntries (Payload : Type) := list (string * Payload).
Definition import_keys {Payload} (entries : ImportEntries Payload) : list string :=
  map fst entries.
Definition import_values {Payload} (entries : ImportEntries Payload) : list Payload :=
  map snd entries.

Definition admit_imports {Payload} (check : Payload -> bool)
    (entries : ImportEntries Payload) : option (ImportEntries Payload) :=
  if ordered_injection_keys (import_keys entries) &&
      forallb (fun entry => check (snd entry)) entries
  then Some entries else None.

Theorem import_admission_returns_original_entries : forall Payload check entries admitted,
  @admit_imports Payload check entries = Some admitted ->
  admitted = entries /\ ordered_injection_keys (import_keys entries) = true /\
  forallb (fun entry => check (snd entry)) entries = true.
Proof.
  intros Payload check entries admitted H. unfold admit_imports in H.
  destruct (ordered_injection_keys (import_keys entries) &&
    forallb (fun entry => check (snd entry)) entries) eqn:HC; [|discriminate].
  inversion H; subst admitted. apply andb_true_iff in HC. tauto.
Qed.

Theorem successful_import_admission_checks_every_payload :
  forall Payload check entries admitted key value,
  @admit_imports Payload check entries = Some admitted ->
  In (key, value) admitted -> check value = true.
Proof.
  intros Payload check entries admitted key value H Hin.
  apply import_admission_returns_original_entries in H as [HE [_ HC]].
  subst admitted. apply forallb_forall with (x := (key, value)) in HC; assumption.
Qed.

Theorem rejected_payload_prevents_import_admission : forall Payload check entries key value,
  In (key, value) entries -> check value = false ->
  @admit_imports Payload check entries = None.
Proof.
  intros Payload check entries key value Hin HC.
  destruct (admit_imports check entries) as [admitted|] eqn:HA; [|reflexivity].
  pose proof (import_admission_returns_original_entries _ _ _ _ HA) as [HE _].
  subst admitted.
  pose proof (successful_import_admission_checks_every_payload
    _ _ _ _ _ _ HA Hin) as HT. rewrite HC in HT. discriminate.
Qed.

Theorem admitted_keys_are_unique : forall Payload check entries admitted,
  @admit_imports Payload check entries = Some admitted -> NoDup (import_keys admitted).
Proof.
  intros Payload check entries admitted H.
  apply import_admission_returns_original_entries in H as [HE [HO _]].
  subst admitted. now apply injection_key_check_excludes_duplicates.
Qed.

Theorem projecting_and_zipping_preserves_every_association : forall Payload entries,
  combine (@import_keys Payload entries) (import_values entries) = entries.
Proof.
  intros Payload entries. induction entries as [|[key value] rest IH].
  - reflexivity.
  - change ((key, value) :: combine (import_keys rest) (import_values rest) =
      (key, value) :: rest).
    now rewrite IH.
Qed.

Theorem admitted_projection_retains_original_associations : forall Payload check entries admitted,
  @admit_imports Payload check entries = Some admitted ->
  combine (import_keys admitted) (import_values admitted) = entries.
Proof.
  intros Payload check entries admitted H.
  rewrite projecting_and_zipping_preserves_every_association.
  now apply import_admission_returns_original_entries in H as [H _].
Qed.

(** The string-key domain differs from the source URI-declaration domain.
    No used-key filter is part of admission or the New projection. *)
Example an_unused_empty_key_is_admitted : forall Payload (value : Payload),
  admit_imports (fun _ => true) [(EmptyString, value)] =
  Some [(EmptyString, value)].
Proof. reflexivity. Qed.

Inductive ImportScopeKind := SourceNew | GeneratedNew.
Definition scope_imports {Payload} (kind : ImportScopeKind)
    (entries : ImportEntries Payload) : ImportEntries Payload :=
  match kind with SourceNew => entries | GeneratedNew => [] end.

Theorem every_source_scope_retains_all_imports : forall Payload entries,
  @scope_imports Payload SourceNew entries = entries.
Proof. reflexivity. Qed.
Theorem generated_scope_excludes_all_imports : forall Payload entries,
  @scope_imports Payload GeneratedNew entries = [].
Proof. reflexivity. Qed.

(** This read-only lookup is the extensional view of the ordered caller map.
    There is no conversion from the key to a language capability. *)
Fixpoint lookup_import {Payload} (key : string) (entries : ImportEntries Payload)
    : option Payload :=
  match entries with
  | [] => None
  | (candidate, value) :: rest =>
    if String.eqb key candidate then Some value else lookup_import key rest
  end.

Theorem successful_lookup_returns_an_original_payload : forall Payload entries key value,
  @lookup_import Payload key entries = Some value -> In (key, value) entries.
Proof.
  intros Payload entries. induction entries as [|[candidate payload] rest IH];
    intros key value H; [discriminate|].
  cbn [lookup_import] in H. destruct (String.eqb key candidate) eqn:HK.
  - apply String.eqb_eq in HK. inversion H; subst. now left.
  - right. now apply IH.
Qed.

Definition resolve_import_uri {Payload} (runtime : string -> option Payload)
    (entries : ImportEntries Payload) (uri : string) : option Payload :=
  match runtime uri with
  | Some value => Some value
  | None => lookup_import uri entries
  end.

Theorem runtime_uri_binding_has_precedence : forall Payload runtime entries uri value,
  runtime uri = Some value ->
  @resolve_import_uri Payload runtime entries uri = Some value.
Proof. intros. unfold resolve_import_uri. now rewrite H. Qed.

Theorem absent_runtime_uri_uses_exact_injection_lookup : forall Payload runtime entries uri,
  runtime uri = None ->
  @resolve_import_uri Payload runtime entries uri = lookup_import uri entries.
Proof. intros. unfold resolve_import_uri. now rewrite H. Qed.

Theorem absent_runtime_and_import_return_no_value : forall Payload runtime entries uri,
  runtime uri = None -> lookup_import uri entries = None ->
  @resolve_import_uri Payload runtime entries uri = None.
Proof. intros. unfold resolve_import_uri. now rewrite H, H0. Qed.

Section LexicalSeparation.
Context {Options Resolver Payload : Type}.
Definition replace_context_imports
    (context : @SourceContext Options Resolver (ImportEntries Payload))
    (entries : ImportEntries Payload) : @SourceContext Options Resolver (ImportEntries Payload) :=
  {| context_scope := context_scope context;
     context_options := context_options context;
     context_resolver := context_resolver context;
     context_imports := entries;
     context_mode := context_mode context;
     context_pattern := context_pattern context |}.

Theorem replacing_imports_cannot_change_lexical_resolution : forall context entries role identity pretty,
  let replaced := replace_context_imports context entries in
  resolve_free (context_mode replaced) (context_pattern replaced) role
    (context_scope replaced) identity pretty =
  resolve_free (context_mode context) (context_pattern context) role
    (context_scope context) identity pretty.
Proof. reflexivity. Qed.

Theorem import_keys_do_not_resolve_unbound_public_terms : forall context entries role identity pretty,
  lexical_lookup (context_scope context) identity pretty = None ->
  resolve_free PublicSource false role
    (context_scope (replace_context_imports context entries)) identity pretty =
  UnresolvedReference role.
Proof. intros. now apply unresolved_public_terms_reject_by_role. Qed.

Theorem lexical_extension_preserves_the_import_table :
  forall (context : @SourceContext Options Resolver (ImportEntries Payload)) slots,
  context_imports (replace_scope context (extend_scope (context_scope context) slots)) =
  context_imports context.
Proof. reflexivity. Qed.
End LexicalSeparation.

(** A fuelled read-only occurrence walk. The local predicate and child
    enumeration are explicit inputs. Fuel counts visited occurrences, not
    allocator bytes; repeated children are visited repeatedly. The concrete
    implementation must separately justify its local Par classifier, child
    table, precharge before pushing children, and cancellation checks.
    No finite-tree premise is assumed: cyclic child functions cannot acquire
    a successful hereditary derivation merely by exhausting fuel. *)
Section BoundedAdmissionWalk.
Context {Node : Type}.
Variable local_check : Node -> bool.
Variable children : Node -> list Node.

Inductive HereditarilyAdmitted : Node -> Prop :=
| AdmittedNode : forall node,
    local_check node = true ->
    Forall HereditarilyAdmitted (children node) ->
    HereditarilyAdmitted node.

Fixpoint admit_worklist (fuel : nat) (pending : list Node) : bool :=
  match pending with
  | [] => true
  | node :: rest =>
    match fuel with
    | 0 => false
    | S remaining =>
      if local_check node then admit_worklist remaining (children node ++ rest)
      else false
    end
  end.

Theorem successful_worklist_admission_is_hereditary : forall fuel pending,
  admit_worklist fuel pending = true -> Forall HereditarilyAdmitted pending.
Proof.
  induction fuel as [|fuel IH]; intros [|node rest] H.
  - constructor.
  - discriminate.
  - constructor.
  - cbn [admit_worklist] in H. destruct (local_check node) eqn:HL; [|discriminate].
    apply IH in H. apply Forall_app in H as [HC HR].
    constructor; [now constructor|exact HR].
Qed.

Theorem successful_root_admission_checks_every_descendant : forall fuel node,
  admit_worklist fuel [node] = true -> HereditarilyAdmitted node.
Proof.
  intros fuel node H. apply successful_worklist_admission_is_hereditary in H.
  now inversion H.
Qed.

Theorem exhausted_nonempty_worklist_is_not_success : forall node rest,
  admit_worklist 0 (node :: rest) = false.
Proof. reflexivity. Qed.

Theorem rejected_local_shape_cannot_become_success : forall fuel node rest,
  local_check node = false -> admit_worklist fuel (node :: rest) = false.
Proof. intros [|fuel] node rest H; [reflexivity|]. cbn [admit_worklist]. now rewrite H. Qed.

Theorem accepted_step_preserves_every_ordered_child_occurrence : forall fuel node rest,
  local_check node = true ->
  admit_worklist (S fuel) (node :: rest) = admit_worklist fuel (children node ++ rest).
Proof. intros. cbn [admit_worklist]. now rewrite H. Qed.
End BoundedAdmissionWalk.

(** The construction result is retained only on success. This is not a
    protocol for committing node effects; all values here remain private. *)
Definition construct_scope_new (kind : ImportScopeKind) (plan : FreshPlan)
    (entries : ImportEntries Value) (body : Value) : ConstructionResult :=
  let selected := scope_imports kind entries in
  checked_shape_fresh (erase_fresh_roster plan) (import_keys selected)
    (body :: import_values selected).

Definition prepare_source_new (check : Value -> bool) (plan : FreshPlan)
    (entries : ImportEntries Value) (body : Value) : option Value :=
  match admit_imports check entries with
  | None => None
  | Some admitted =>
    match construct_scope_new SourceNew plan admitted body with
    | Constructed value => Some value
    | ConstructionRejected _ => None
    end
  end.

Theorem import_rejection_returns_no_artifact : forall check plan entries body,
  admit_imports check entries = None -> prepare_source_new check plan entries body = None.
Proof. intros. unfold prepare_source_new. now rewrite H. Qed.

Theorem constructor_rejection_returns_no_artifact : forall check plan entries body error,
  construct_scope_new SourceNew plan entries body = ConstructionRejected error ->
  prepare_source_new check plan entries body = None.
Proof.
  intros check plan entries body error HC. unfold prepare_source_new.
  destruct (admit_imports check entries) as [admitted|] eqn:HA; [|reflexivity].
  apply import_admission_returns_original_entries in HA as [HE _].
  subst admitted. now rewrite HC.
Qed.

Theorem prepared_source_new_preserves_complete_layout : forall check plan entries body value,
  prepare_source_new check plan entries body = Some value ->
  ordered_injection_keys (import_keys entries) = true /\
  combine (import_keys entries) (import_values entries) = entries /\
  heads_of value = [MakeHead
    (NewHead (List.length (fresh_binders plan)) (fresh_uris plan) (import_keys entries))
    (body :: import_values entries)] /\
  summary_of value = shifted_summary (List.length (fresh_binders plan)) (summary_of body).
Proof.
  intros check plan entries body value H. unfold prepare_source_new in H.
  destruct (admit_imports check entries) as [admitted|] eqn:HA; [|discriminate].
  apply import_admission_returns_original_entries in HA as [HE [HO _]].
  subst admitted.
  destruct (construct_scope_new SourceNew plan entries body) as [built|error] eqn:HC;
    [|discriminate].
  inversion H; subst built.
  unfold construct_scope_new in HC. cbn [scope_imports] in HC.
  apply erased_success_preserves_keys_children_and_body_only_summary in HC as [_ [HH HS]].
  split; [exact HO|]. split.
  - apply projecting_and_zipping_preserves_every_association.
  - split; assumption.
Qed.

Theorem generated_new_reuses_original_empty_import_constructor : forall plan entries body,
  construct_scope_new GeneratedNew plan entries body = checked_fresh plan body.
Proof.
  intros. unfold construct_scope_new. cbn [scope_imports import_keys import_values].
  apply erased_empty_injections_specialize_original_fresh.
Qed.

Theorem existing_reply_shell_has_no_import_keys : forall channel payloads body,
  heads_of (service_reply channel payloads body) =
  [MakeHead (NewHead 1 [] [])
    [append (send false channel payloads) (service_reply_receive body)]].
Proof. intros. exact (proj1 (service_reply_fixed_scope_and_children channel payloads body)). Qed.

Print Assumptions import_admission_returns_original_entries.
Print Assumptions successful_import_admission_checks_every_payload.
Print Assumptions rejected_payload_prevents_import_admission.
Print Assumptions admitted_keys_are_unique.
Print Assumptions projecting_and_zipping_preserves_every_association.
Print Assumptions admitted_projection_retains_original_associations.
Print Assumptions an_unused_empty_key_is_admitted.
Print Assumptions every_source_scope_retains_all_imports.
Print Assumptions generated_scope_excludes_all_imports.
Print Assumptions successful_lookup_returns_an_original_payload.
Print Assumptions runtime_uri_binding_has_precedence.
Print Assumptions absent_runtime_uri_uses_exact_injection_lookup.
Print Assumptions absent_runtime_and_import_return_no_value.
Print Assumptions replacing_imports_cannot_change_lexical_resolution.
Print Assumptions import_keys_do_not_resolve_unbound_public_terms.
Print Assumptions lexical_extension_preserves_the_import_table.
Print Assumptions successful_worklist_admission_is_hereditary.
Print Assumptions successful_root_admission_checks_every_descendant.
Print Assumptions exhausted_nonempty_worklist_is_not_success.
Print Assumptions rejected_local_shape_cannot_become_success.
Print Assumptions accepted_step_preserves_every_ordered_child_occurrence.
Print Assumptions import_rejection_returns_no_artifact.
Print Assumptions constructor_rejection_returns_no_artifact.
Print Assumptions prepared_source_new_preserves_complete_layout.
Print Assumptions generated_new_reuses_original_empty_import_constructor.
Print Assumptions existing_reply_shell_has_no_import_keys.
