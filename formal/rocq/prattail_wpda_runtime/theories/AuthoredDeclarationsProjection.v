(** Retained declaration header, extra name roots, and checked transport.

    Proposed Rust layout: AuthoredRuleStore owns one optional flat header.
    Category rows retain NameId, optional NativeKind, optional declared
    collection delimiters. Source
    token rows retain raw NameId, optional category/push NameId, literal/eval
    presence. The global source roster
    and each ordered mode roster contain indices into those rows. Mode rows
    retain raw NameId. A separate compact Core binding table supplies final
    category/token/mode indices to the checks below. No lexer patterns,
    evaluator bodies, token automata or decoder implementation are copied.

    NativeKind and collection kind below are opaque natural-number payloads:
    this file proves their retention, NOT the classifier extraction or a
    canonical carrier/native-value correspondence. Association IDs must be
    recorded at original lowering sites; bounds/membership checks cannot prove
    a fabricated ID refers to the intended source occurrence. Category-name
    association is spelling equality, distinct from source Ident equality.

    Capture uses the EXISTING initial/FiniteRun/Step/ReadyTyped operations.
    No second capture loop is defined. The extra roots and checked ordered
    resolution reuse map_checked. The type extension directly extends the
    store/capture vocabulary; AuthoredExtendedCaptureComposition composes the
    rechecked original finite-run theorem with these declaration-root laws.
    Resource admission is still required before allocating header/name rosters;
    this model does not prove physical Vec capacity, allocation or work bounds.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import
  AuthoredRuleStoreProjection AuthoredRuleCaptureProjection
  AuthoredRuleTransportProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredDeclarationsProjection.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.
Module T := AuthoredRuleTransportProjection.AuthoredRuleTransportProjection.

Record CollectionDeclaration := {
  collection_kind : nat;
  collection_open : option string;
  collection_close : option string;
  collection_separator : option string;
  collection_key_value_separator : option string
}.
Record CategoryDeclaration := {
  category_name : A.Handle A.NameTag;
  category_native : option nat;
  category_collection : option CollectionDeclaration
}.
Record TokenDeclaration := {
  token_name : A.Handle A.NameTag;
  token_category : option (A.Handle A.NameTag);
  token_from_literals : bool;
  token_has_evaluation : bool;
  token_push : option (A.Handle A.NameTag)
}.
Record ModeDeclaration := {
  mode_name : A.Handle A.NameTag;
  mode_source_tokens : list nat
}.
Record Header := {
  categories : list CategoryDeclaration;
  tokens : list TokenDeclaration;
  global_source_tokens : list nat;
  modes : list ModeDeclaration
}.
Definition token_names row :=
  [A.edge (token_name row)] ++ A.optional_edge (token_category row) ++
  A.optional_edge (token_push row).
Definition declaration_names header :=
  List.map (fun row => A.edge (category_name row)) (categories header) ++
  flat_map token_names (tokens header) ++
  List.map (fun row => A.edge (mode_name row)) (modes header).
Definition capture_roots rules header := rules ++ declaration_names header.
Definition header_names_valid arena header :=
  forallb (A.reference_valid arena) (declaration_names header).

Theorem checked_header_names_have_typed_targets : forall arena header reference,
  header_names_valid arena header = true -> In reference (declaration_names header) ->
  exists target, nth_error arena (snd reference) = Some target /\
    A.node_tag target = fst reference /\ snd reference < List.length arena.
Proof.
  intros arena header reference Valid Member; unfold header_names_valid in Valid.
  apply forallb_forall with (x := reference) in Valid; [|exact Member].
  apply A.reference_valid_sound; exact Valid.
Qed.
Theorem declaration_roots_are_retained_without_rules : forall header,
  capture_roots [] header = declaration_names header.
Proof. reflexivity. Qed.
Theorem rule_roots_keep_their_original_positions : forall rules header position edge,
  nth_error rules position = Some edge ->
  nth_error (capture_roots rules header) position = Some edge.
Proof.
  intros rules header position edge Read; unfold capture_roots.
  rewrite nth_error_app1; [exact Read|].
  apply nth_error_Some; rewrite Read; discriminate.
Qed.
Theorem declaration_root_positions_follow_rule_roster : forall rules header position,
  nth_error (capture_roots rules header) (List.length rules + position) =
  nth_error (declaration_names header) position.
Proof.
  intros; unfold capture_roots; rewrite nth_error_app2 by lia.
  replace (List.length rules + position - List.length rules) with position by lia.
  reflexivity.
Qed.

(** The same ordered checked map resolves every root, including repeated
    occurrences. This law is also the new-header remapping boundary. *)
Lemma checked_resolution_app : forall X Y (resolve : X -> option Y) left right,
  C.map_checked resolve (left ++ right) =
  C.bind (C.map_checked resolve left) (fun lhs =>
    C.bind (C.map_checked resolve right) (fun rhs => Some (lhs ++ rhs))).
Proof.
  intros X Y resolve left; induction left as [|head tail IH]; intros right; cbn.
  - destruct (C.map_checked resolve right); reflexivity.
  - destruct (resolve head); cbn; [|reflexivity].
    rewrite IH; destruct (C.map_checked resolve tail); cbn; [|reflexivity].
    destruct (C.map_checked resolve right); reflexivity.
Qed.
Theorem resolved_header_roster_keeps_order_and_duplicates :
  forall (resolve : C.Resolver) header (ids : list nat),
  C.map_checked resolve (declaration_names header) = Some ids ->
  List.length ids = List.length (declaration_names header) /\
  forall position edge, nth_error (declaration_names header) position = Some edge ->
    exists target, nth_error ids position = Some target /\ resolve edge = Some target.
Proof.
  intros resolve header ids H; split.
  - eapply C.map_checked_length; exact H.
  - intros; eapply C.map_checked_index; eauto.
Qed.
Theorem existing_capture_returns_every_declaration_root :
  forall graph admit rules header st nodes ids position edge,
  C.Step graph admit (capture_roots rules header) st (C.Complete nodes ids) ->
  nth_error (declaration_names header) position = Some edge ->
  exists target,
    nth_error ids (List.length rules + position) = Some target /\
    C.memo st edge = Some (C.Ready target).
Proof.
  intros graph admit rules header st nodes ids position edge Done Read.
  destruct (@C.returned_roots_keep_order_and_multiplicity _ _ _ _ _ _ Done)
    as [_ Law].
  apply Law; rewrite declaration_root_positions_follow_rule_roster; exact Read.
Qed.
Theorem extra_name_roots_use_the_same_capture_invariant :
  forall graph admit rules header count after,
  C.FiniteRun graph admit (capture_roots rules header)
    (C.initial (capture_roots rules header)) count after ->
  A.ValidArena (C.arena after) /\
  C.ReadyTyped (C.arena after) (C.memo after).
Proof.
  intros graph admit rules header count after Run.
  destruct (@C.finite_capture_postorder_and_typed_store _ _ _ _ _ Run)
    as [Valid [_ [Ready _]]]; auto.
Qed.

(** Associations are explicit; source rosters are not inferred from execution
    token order or qualified names. Many source rows may share one core token. *)
Definition category_association arena core_names row core_index :=
  match A.name_payload arena (category_name row),
        nth_error core_names core_index with
  | Some authored, Some core_name => String.eqb (A.spelling authored) core_name
  | _, _ => false end.
Theorem accepted_category_association_preserves_spelling : forall arena core_names row core_index,
  category_association arena core_names row core_index = true ->
  exists authored core_name,
    A.name_payload arena (category_name row) = Some authored /\
    nth_error core_names core_index = Some core_name /\
    A.spelling authored = core_name.
Proof.
  intros arena core_names row core_index H; unfold category_association in H.
  destruct (A.name_payload arena (category_name row)) as [authored|] eqn:N;
    [|discriminate].
  destruct (nth_error core_names core_index) as [core_name|] eqn:E;
    [|discriminate].
  apply String.eqb_eq in H; exists authored, core_name; auto.
Qed.
Definition token_association core_count core_index := Nat.ltb core_index core_count.
Theorem token_association_checks_actual_bound : forall core_count core_index,
  token_association core_count core_index = true -> core_index < core_count.
Proof. intros; apply Nat.ltb_lt; exact H. Qed.
Definition roster_valid token_bindings core_members indices := forallb
  (fun source_index => match nth_error token_bindings source_index with
    | None => false
    | Some core_index => existsb (Nat.eqb core_index) core_members
    end) indices.
Theorem checked_mode_roster_has_actual_source_and_core_members :
  forall token_bindings core_members indices source_index,
  roster_valid token_bindings core_members indices = true -> In source_index indices ->
  exists core_index, nth_error token_bindings source_index = Some core_index /\
    In core_index core_members.
Proof.
  intros token_bindings core_members indices source_index H Member.
  unfold roster_valid in H; apply forallb_forall with (x := source_index) in H;
    [|exact Member].
  destruct (nth_error token_bindings source_index) as [core_index|] eqn:E; [|discriminate].
  exists core_index; split; [reflexivity|].
  apply existsb_exists in H; destruct H as [member [Hin Equal]].
  apply Nat.eqb_eq in Equal; subst member; exact Hin.
Qed.
Theorem duplicate_source_rows_are_not_forbidden : forall core_index,
  roster_valid [core_index; core_index] [core_index] [1; 0; 1] = true.
Proof.
  intros core_index.
  change (((Nat.eqb core_index core_index || false) &&
    ((Nat.eqb core_index core_index || false) &&
    ((Nat.eqb core_index core_index || false) && true))) = true).
  rewrite Nat.eqb_refl; reflexivity.
Qed.
Definition mode_association token_bindings core_modes row core_index :=
  match nth_error core_modes core_index with
  | None => false
  | Some members => roster_valid token_bindings members (mode_source_tokens row)
  end.
Theorem missing_core_mode_is_refused : forall token_bindings core_modes row core_index,
  nth_error core_modes core_index = None ->
  mode_association token_bindings core_modes row core_index = false.
Proof. intros; unfold mode_association; rewrite H; reflexivity. Qed.

(** Explicit store ownership seeds the OLD owner selection loop. *)
Definition select_language_owner explicit inputs :=
  T.select_owners explicit (T.owners inputs).
Theorem empty_rule_language_preserves_explicit_owner : forall owner,
  select_language_owner (Some owner) [] = Some (Some owner).
Proof. reflexivity. Qed.
Theorem successful_rule_transport_cannot_replace_header_owner : forall owner inputs final,
  select_language_owner (Some owner) inputs = Some final -> final = Some owner.
Proof. intros; eapply T.selected_owner_cannot_change; exact H. Qed.
Theorem all_present_rule_owners_agree_with_explicit_owner : forall owner inputs final incoming,
  select_language_owner (Some owner) inputs = Some final ->
  In (Some incoming) (T.owners inputs) -> incoming = owner.
Proof.
  intros owner inputs final incoming H Member.
  pose proof (@successful_rule_transport_cannot_replace_header_owner _ _ _ H) as Final.
  pose proof (@T.every_present_owner_agrees_on_success _ _ _ _ H Member) as Incoming.
  congruence.
Qed.
Definition retained_semantic_projection (other : nat) (header : option Header) := (other, header).
Theorem header_is_not_excluded_from_semantic_commitment : forall other left right,
  retained_semantic_projection other left = retained_semantic_projection other right -> left = right.
Proof. intros other left right H; inversion H; reflexivity. Qed.

Print Assumptions checked_header_names_have_typed_targets.
Print Assumptions declaration_roots_are_retained_without_rules.
Print Assumptions rule_roots_keep_their_original_positions.
Print Assumptions declaration_root_positions_follow_rule_roster.
Print Assumptions checked_resolution_app.
Print Assumptions resolved_header_roster_keeps_order_and_duplicates.
Print Assumptions existing_capture_returns_every_declaration_root.
Print Assumptions extra_name_roots_use_the_same_capture_invariant.
Print Assumptions accepted_category_association_preserves_spelling.
Print Assumptions token_association_checks_actual_bound.
Print Assumptions checked_mode_roster_has_actual_source_and_core_members.
Print Assumptions duplicate_source_rows_are_not_forbidden.
Print Assumptions missing_core_mode_is_refused.
Print Assumptions empty_rule_language_preserves_explicit_owner.
Print Assumptions successful_rule_transport_cannot_replace_header_owner.
Print Assumptions all_present_rule_owners_agree_with_explicit_owner.
Print Assumptions header_is_not_excluded_from_semantic_commitment.
End AuthoredDeclarationsProjection.
