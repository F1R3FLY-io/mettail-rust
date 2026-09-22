(** Authored rule transport and semantic commitment boundary.

    Source correspondence: RuleSpecInput -> RuleSpec in prattail/src/lib.rs,
    compose.rs::merge_rules, grammar_core_bridge.rs::to_grammar_core,
    GrammarCoreV1::validate/fingerprint, and mettail-elab/core_value.rs.

    A store owner below is an opaque allocation identity: equality corresponds
    to Arc::ptr_eq, NOT equality of arena contents. The same immutable owner
    denotes the same store; distinct owners remain distinct even when their
    payloads compare equal. Rule references are forwarded, never reconstructed.

    The arena and typed rule/name lookups reuse AuthoredRuleStoreProjection.
    Store construction, capture, parsing, classifier arithmetic and validation
    of unrelated GrammarCore fields are outside this narrow model. The final
    section models the UNHASHED semantic projection, not postcard correctness,
    BLAKE3 injectivity, allocation, Rust ownership, or cryptographic security.
    It retains the existing exclusions of backend context, documentation,
    global provenance and production provenance, and no authored payload is
    excluded. Opaque unrelated semantic data is preserved literally.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import AuthoredRuleStoreProjection.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module AuthoredRuleTransportProjection.
Module Store := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.

Record AuthoredReference := {
  reference_owner : nat;
  reference_rule : nat
}.
Record Input := {
  input_label : string;
  input_category : string;
  input_authored : option AuthoredReference
}.
Record Spec := {
  spec_label : string;
  spec_category : string;
  spec_authored : option AuthoredReference
}.
Definition forward input :=
  {| spec_label := input_label input;
     spec_category := input_category input;
     spec_authored := input_authored input |}.
Definition reinput spec :=
  {| input_label := spec_label spec;
     input_category := spec_category spec;
     input_authored := spec_authored spec |}.

Theorem transport_preserves_exact_reference : forall input,
  spec_authored (forward input) = input_authored input.
Proof. reflexivity. Qed.
Theorem composition_reforward_is_identity : forall spec,
  forward (reinput spec) = spec.
Proof. intros []; reflexivity. Qed.
Theorem transport_preserves_order_and_multiplicity : forall inputs index,
  nth_error (List.map forward inputs) index =
  option_map forward (nth_error inputs index).
Proof. intros; apply Store.map_nth_exact. Qed.
Theorem absent_is_not_fabricated : forall label category,
  spec_authored (forward {| input_label := label; input_category := category;
                           input_authored := None |}) = None.
Proof. reflexivity. Qed.

(** Outer None is refusal; Some None means no store owner was provided. *)
Definition select_owner (current incoming : option nat) : option (option nat) :=
  match incoming with
  | None => Some current
  | Some owner => match current with
    | None => Some (Some owner)
    | Some prior => if Nat.eqb prior owner then Some current else None
    end
  end.
Fixpoint select_owners (current : option nat) (inputs : list (option nat)) :=
  match inputs with
  | [] => Some current
  | input :: rest => match select_owner current input with
    | None => None
    | Some next => select_owners next rest
    end
  end.
Definition owners inputs := List.map
  (fun input => option_map reference_owner (input_authored input)) inputs.

Theorem absent_reference_does_not_erase_owner : forall current,
  select_owner current None = Some current.
Proof. reflexivity. Qed.
Theorem same_owner_is_accepted : forall owner,
  select_owner (Some owner) (Some owner) = Some (Some owner).
Proof. intros; cbn; now rewrite Nat.eqb_refl. Qed.
Theorem distinct_owners_are_rejected : forall left right,
  left <> right -> select_owner (Some left) (Some right) = None.
Proof. intros left right H; cbn; apply Nat.eqb_neq in H; now rewrite H. Qed.
Lemma selected_owner_cannot_change : forall inputs owner final,
  select_owners (Some owner) inputs = Some final -> final = Some owner.
Proof.
  induction inputs as [|input rest IH]; intros owner final H; cbn in H.
  - now inversion H.
  - destruct input as [incoming|]; cbn in H.
    + destruct (Nat.eqb owner incoming); [eapply IH; exact H|discriminate].
    + eapply IH; exact H.
Qed.
Theorem first_owner_survives_remaining_rows : forall owner rest final,
  select_owners None (Some owner :: rest) = Some final -> final = Some owner.
Proof. intros; cbn in H; eapply selected_owner_cannot_change; exact H. Qed.
Lemma incoming_owner_is_selected : forall current owner next,
  select_owner current (Some owner) = Some next -> next = Some owner.
Proof.
  intros [prior|] owner next H; cbn in H.
  - destruct (Nat.eqb prior owner) eqn:E; [|discriminate].
    apply Nat.eqb_eq in E; subst; now inversion H.
  - now inversion H.
Qed.
Theorem every_present_owner_agrees_on_success : forall inputs current final owner,
  select_owners current inputs = Some final ->
  In (Some owner) inputs -> final = Some owner.
Proof.
  induction inputs as [|input rest IH]; intros current final owner H Hin;
    [contradiction|].
  cbn in H; destruct (select_owner current input) as [next|] eqn:E;
    [|discriminate].
  destruct Hin as [Equal|Hin].
  - subst input. apply incoming_owner_is_selected in E; subst next.
    eapply selected_owner_cannot_change; exact H.
  - eapply IH; eauto.
Qed.
Theorem no_owner_remains_unavailable : forall count,
  select_owners None (List.repeat None count) = Some None.
Proof. induction count; cbn; assumption || reflexivity. Qed.
Theorem equal_payload_does_not_override_distinct_ownership :
  forall (payload : list Store.Node) left right,
  left <> right ->
  select_owners None [Some left; Some right] = None.
Proof.
  intros payload left right H; cbn.
  apply Nat.eqb_neq in H; now rewrite H.
Qed.

(** Actual typed lookups, not a boolean supplied by an unverified adapter. *)
Definition association (arena : list Store.Node) rule_id label category :=
  match nth_error arena rule_id with
  | Some (Store.RuleNode rule) =>
      match Store.name_payload arena (Store.label rule),
            Store.name_payload arena (Store.category rule) with
      | Some stored_label, Some stored_category =>
          String.eqb (Store.spelling stored_label) label &&
          String.eqb (Store.spelling stored_category) category
      | _, _ => false
      end
  | _ => false
  end.

Theorem accepted_association_has_exact_rule_and_names :
  forall arena rule_id label category,
  association arena rule_id label category = true ->
  exists rule stored_label stored_category,
    nth_error arena rule_id = Some (Store.RuleNode rule) /\
    Store.name_payload arena (Store.label rule) = Some stored_label /\
    Store.name_payload arena (Store.category rule) = Some stored_category /\
    Store.spelling stored_label = label /\ Store.spelling stored_category = category.
Proof.
  intros arena rule_id label category H; unfold association in H.
  destruct (nth_error arena rule_id) as [node|] eqn:E; [|discriminate].
  destruct node as [name|names|ty|param|params|syntax|operation|rule]; try discriminate.
  destruct (Store.name_payload arena (Store.label rule)) as [stored_label|] eqn:L;
    [|discriminate].
  destruct (Store.name_payload arena (Store.category rule)) as [stored_category|] eqn:C;
    [|discriminate].
  apply andb_true_iff in H; destruct H as [HL HC].
  apply String.eqb_eq in HL; apply String.eqb_eq in HC.
  exists rule, stored_label, stored_category; repeat split; assumption.
Qed.

Record Production := {
  production_label : string;
  production_category : nat;
  production_authored : option nat;
  production_provenance : nat
}.
Definition validate_association store categories production :=
  match production_authored production with
  | None => true
  | Some rule_id => match store, nth_error categories (production_category production) with
    | Some arena, Some category =>
        association arena rule_id (production_label production) category
    | _, _ => false
    end
  end.
Theorem no_store_with_reference_is_rejected : forall categories label category rule provenance,
  validate_association None categories
    {| production_label := label; production_category := category;
       production_authored := Some rule; production_provenance := provenance |} = false.
Proof. intros; reflexivity. Qed.
Theorem unavailable_reference_stays_unavailable : forall store categories label category provenance,
  validate_association store categories
    {| production_label := label; production_category := category;
       production_authored := None; production_provenance := provenance |} = true.
Proof. reflexivity. Qed.
Theorem undeclared_category_is_not_defaulted : forall store categories production rule,
  production_authored production = Some rule ->
  nth_error categories (production_category production) = None ->
  validate_association store categories production = false.
Proof. intros; unfold validate_association; rewrite H, H0; destruct store; reflexivity. Qed.

Definition current_grammar_abi := 3.
Definition grammar_abi_admitted abi := Nat.eqb abi current_grammar_abi.
Definition current_value_schema := "mettail-language-core-value/5".
Definition value_schema_admitted schema := String.eqb schema current_value_schema.
Theorem current_grammar_abi_is_admitted : grammar_abi_admitted 3 = true.
Proof. reflexivity. Qed.
Theorem both_old_grammar_abis_are_refused :
  grammar_abi_admitted 1 = false /\ grammar_abi_admitted 2 = false.
Proof. split; reflexivity. Qed.
Theorem previous_structural_envelope_is_refused :
  value_schema_admitted "mettail-language-core-value/4" = false.
Proof. reflexivity. Qed.

(** Remaining grammar fields are an opaque exact payload. No function below
    alters or interprets them, including cost-sensitive parser configuration. *)
Record GrammarProjection := {
  grammar_abi : nat;
  semantic_payload : nat;
  retained_store : option (list Store.Node);
  retained_productions : list Production;
  backend_context : option string;
  documentation : option string;
  grammar_provenance : nat
}.
Definition strip_production_diagnostic production :=
  {| production_label := production_label production;
     production_category := production_category production;
     production_authored := production_authored production;
     production_provenance := 0 |}.
Definition semantic_projection grammar :=
  {| grammar_abi := grammar_abi grammar;
     semantic_payload := semantic_payload grammar;
     retained_store := retained_store grammar;
     retained_productions := List.map strip_production_diagnostic (retained_productions grammar);
     backend_context := None; documentation := None; grammar_provenance := 0 |}.
Definition semantic_commitment_input grammar :=
  ("mettail-grammar-core/3", semantic_projection grammar).
Definition full_language_commitment_input grammar (theory_commitment : nat) :=
  (semantic_commitment_input grammar, theory_commitment).

Theorem semantic_projection_preserves_store : forall grammar,
  retained_store (semantic_projection grammar) = retained_store grammar.
Proof. reflexivity. Qed.
Theorem semantic_projection_preserves_rule_references : forall grammar,
  List.map production_authored (retained_productions (semantic_projection grammar)) =
  List.map production_authored (retained_productions grammar).
Proof. intros; cbn; rewrite map_map; apply map_ext; reflexivity. Qed.
Theorem semantic_projection_is_idempotent : forall grammar,
  semantic_projection (semantic_projection grammar) = semantic_projection grammar.
Proof.
  intros []; unfold semantic_projection; cbn; rewrite map_map.
  f_equal.
Qed.
Theorem changed_authored_store_changes_unhashed_projection : forall left right,
  retained_store left <> retained_store right ->
  semantic_commitment_input left <> semantic_commitment_input right.
Proof.
  intros left right H E; apply H.
  exact (f_equal (fun input => retained_store (snd input)) E).
Qed.
Theorem no_store_is_not_present_empty_store : forall left right,
  retained_store left = None -> retained_store right = Some [] ->
  semantic_commitment_input left <> semantic_commitment_input right.
Proof.
  intros left right L R; apply changed_authored_store_changes_unhashed_projection.
  rewrite L, R; discriminate.
Qed.
Theorem full_language_retains_theory_commitment : forall grammar theory,
  snd (full_language_commitment_input grammar theory) = theory.
Proof. reflexivity. Qed.
Theorem full_language_retains_grammar_component : forall grammar theory,
  fst (full_language_commitment_input grammar theory) = semantic_commitment_input grammar.
Proof. reflexivity. Qed.

Print Assumptions transport_preserves_exact_reference.
Print Assumptions composition_reforward_is_identity.
Print Assumptions transport_preserves_order_and_multiplicity.
Print Assumptions distinct_owners_are_rejected.
Print Assumptions selected_owner_cannot_change.
Print Assumptions every_present_owner_agrees_on_success.
Print Assumptions equal_payload_does_not_override_distinct_ownership.
Print Assumptions accepted_association_has_exact_rule_and_names.
Print Assumptions no_store_with_reference_is_rejected.
Print Assumptions undeclared_category_is_not_defaulted.
Print Assumptions both_old_grammar_abis_are_refused.
Print Assumptions previous_structural_envelope_is_refused.
Print Assumptions semantic_projection_preserves_store.
Print Assumptions semantic_projection_preserves_rule_references.
Print Assumptions semantic_projection_is_idempotent.
Print Assumptions changed_authored_store_changes_unhashed_projection.
Print Assumptions no_store_is_not_present_empty_store.
Print Assumptions full_language_retains_theory_commitment.
Print Assumptions full_language_retains_grammar_component.
End AuthoredRuleTransportProjection.
