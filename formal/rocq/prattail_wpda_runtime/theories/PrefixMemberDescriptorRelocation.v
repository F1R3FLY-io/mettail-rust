(** Exact relocation of five descriptor-only helpers, NOT member discovery or
    prefix binding-power construction:
      binder.rs: lookup_src_idx, first_param_cat_from_positions,
        required_top_cat_after_position, binder_initial_body_cat;
      factoring.rs: binder_items.

    The Rust move changes module/visibility only. BinderOptionalProjection's
    COMPLETE Position descriptors and BinderRuleProjection's COMPLETE BinderShape
    are reused directly. FactoringTreeRelocation supplies the exact SpineItem
    output type. No second grammar classifier or reconstructed AST is present.
    The imported classifier theorems are not claimed to prove these previously
    unmodeled helper loops; their descriptor types are the applicable reuse.

    Source ledger:
    - lookup_src_idx scans category strings in forward order, stops at the FIRST
      equal name, then casts that index to u16 modulo 65536. This is intentionally
      different from synthetic category grouping's last-duplicate map.
    - first_param_cat_from_positions initially reverse-collects root references;
      each pop examines one descriptor. Every ParamParse returns its cat, even
      with collection Some. BinderListLoop with collection_param_cat Some returns
      that field BEFORE inspecting children. Otherwise binder-list/optional
      children are reverse-pushed; remaining root/sibling work stays below them.
      Literals/captures/binder identifiers/guards do not contribute categories.
    - Borrowed names retain owner, occurrence path and field identity, not merely
      string equality. Paths are proof handles for existing references, not Rust
      allocations. Position references retain all original descriptor fields.
    - binder_initial_body_cat returns the explicit body_cat borrow when Some,
      including an empty or undeclared name. Its or_else performs NO nested
      traversal on that path. Category resolution/fallback by discovery is not
      part of this helper and must not be folded into it.
    - required_top_cat_after_position inspects ONLY the supplied immediately
      previous position. Only plain ParamParse (collection None) calls lookup;
      collections and all other forms yield None. Lookup failure here is None,
      not a refusal or a request to inspect an earlier position.
    - binder_items walks the original top-level list in index order. A Literal
      clones its text and asks the previous-position helper (None at index 0).
      A plain ParamParse resolves its category FIRST; unresolved means return
      the already-produced prefix with truncated=true, without a BP lookup.
      Success reads prefix_bp_map at the OWNER (category_src_idx, rule_idx),
      never at the parsed category, and defaults to 0 only if that key is absent.
      Collection parameters and every other original nonmergeable variant stop
      before appending an item, without entering nested positions. Only complete
      exhaustion returns truncated=false. No helper emits a refusal here.

    Name-search and item worklists below are concrete original loop steps.
    Separate original/relocated wrappers execute those unchanged steps. Finite
    runs preserve full items, cur_bp, truncation, borrowed-name identity and
    observation prefixes; fuel exhaustion is explicit, not fabricated None.
    Lookup events are proof instrumentation of helper sites, not new Rust I/O.
    PrefixBpMap represents the existing immutable HashMap lookup only; this file
    does not implement or certify its builder or a dynamic grammar admission.

    Scope: source fields use their original Rust ranges; category/rule keys and
    map values represent u16/u8 values. List lengths/indices must fit usize as
    they do for an existing Rust slice. Index-minus-one is used only at index>0;
    the category cast is modeled exactly, not replaced by a bounds rejection.
    Source transcription, allocation/clone/drop, borrow checking, Rust extraction
    and all-input termination are outside the theorem. No downstream parser,
    unresolved-category diagnostic emitter or new eligibility theorem is claimed.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import BinderOptionalProjection BinderRuleProjection FactoringTreeRelocation.
Import ListNotations.
Set Implicit Arguments.

Module PrefixMemberDescriptorRelocation.
Module O := BinderOptionalProjection.BinderOptionalProjection.
Module B := BinderRuleProjection.BinderRuleProjection.
Module F := FactoringTreeRelocation.FactoringTreeRelocation.

Fixpoint first_category_index name categories := match categories with
| [] => None
| category :: rest => if String.eqb category name then Some 0
    else option_map S (first_category_index name rest) end.
Definition lookup_src_idx name categories :=
  option_map (fun index => index mod 65536) (first_category_index name categories).
Definition required_top_cat_after_position position categories := match position with
| Some (O.PParam cat None) => lookup_src_idx cat categories
| _ => None end.

Record PositionRef := {
  position_owner : nat; position_path : list nat; position_value : O.Position
}.
Fixpoint numbered_positions owner prefix index positions := match positions with
| [] => []
| position :: rest =>
    {| position_owner := owner; position_path := (prefix ++ [index])%list;
       position_value := position |} :: numbered_positions owner prefix (S index) rest end.
Definition root_positions owner positions := numbered_positions owner [] 0 positions.
Definition child_positions parent positions :=
  numbered_positions (position_owner parent) (position_path parent) 0 positions.
Inductive NameField := ExplicitBody | ParamCategory (path : list nat) | ListCollectionCategory (path : list nat).
Record BorrowedName := { name_owner : nat; name_field : NameField; name_text : string }.
Definition borrowed_param ref cat :=
 {| name_owner := position_owner ref; name_field := ParamCategory (position_path ref); name_text := cat |}.
Definition borrowed_collection ref cat :=
 {| name_owner := position_owner ref; name_field := ListCollectionCategory (position_path ref); name_text := cat |}.
Record NameState := { name_work : list PositionRef; name_trace : list PositionRef }.
Definition name_state work trace := {| name_work := work; name_trace := trace |}.

Inductive ItemObservation :=
| InspectPosition (index : nat)
| LookupCategory (name : string)
| LookupPrefixBp (owner_category rule_idx : nat).
Definition previous_position (positions : list O.Position) index := match index with
| 0 => None | S previous => nth_error positions previous end.
Definition required_top_observations position := match position with
| Some (O.PParam cat None) => [LookupCategory cat]
| _ => [] end.
Definition PrefixBpMap := (nat * nat)%type -> option nat.
Record Environment := {
  categories : list string; owner_category : nat; owner_rule : nat; prefix_bp_map : PrefixBpMap
}.
Definition owner_prefix_bp env := match prefix_bp_map env (owner_category env, owner_rule env) with
| Some bp => bp | None => 0 end.
Record ItemState := {
  original_positions : list O.Position; next_position : nat;
  produced_items : list F.SpineItem; item_trace : list ItemObservation
}.
Definition item_state positions index items trace :=
 {| original_positions := positions; next_position := index; produced_items := items; item_trace := trace |}.

Inductive Configuration := Searching (state : NameState) | Collecting (state : ItemState).
Inductive Outcome :=
| Continue (state : Configuration)
| NameResult (name : option BorrowedName) (unvisited : list PositionRef) (trace : list PositionRef)
| ItemResult (items : list F.SpineItem) (truncated : bool) (trace : list ItemObservation).
Definition core_step env configuration := match configuration with
| Searching state => match name_work state with
    | [] => NameResult None [] (name_trace state)
    | ref :: pending =>
        let trace := (name_trace state ++ [ref])%list in
        match position_value ref with
        | O.PParam cat _ => NameResult (Some (borrowed_param ref cat)) pending trace
        | O.PBinderList _ _ _ (Some cat) _ _ _ =>
            NameResult (Some (borrowed_collection ref cat)) pending trace
        | O.PBinderList _ _ children None _ _ _
        | O.POptional children _ _ =>
            Continue (Searching (name_state (child_positions ref children ++ pending)%list trace))
        | O.PLiteral _ | O.PToken _ _ | O.PIdentText _ | O.PGuest _ _ _ _
        | O.PBinderIdent | O.PGuard => Continue (Searching (name_state pending trace))
        end end
| Collecting state =>
    let positions := original_positions state in
    let index := next_position state in
    let items := produced_items state in
    match nth_error positions index with
    | None => ItemResult items false (item_trace state)
    | Some position =>
      let inspected := (item_trace state ++ [InspectPosition index])%list in
      match position with
      | O.PLiteral text =>
          let previous := previous_position positions index in
          Continue (Collecting (item_state positions (S index)
            (items ++ [F.Literal text (required_top_cat_after_position previous (categories env))])%list
            (inspected ++ required_top_observations previous)%list))
      | O.PParam cat None =>
          let looked_up := (inspected ++ [LookupCategory cat])%list in
          match lookup_src_idx cat (categories env) with
          | None => ItemResult items true looked_up
          | Some parsed_cat => Continue (Collecting (item_state positions (S index)
              (items ++ [F.ParamParse parsed_cat (owner_prefix_bp env)])%list
              (looked_up ++ [LookupPrefixBp (owner_category env) (owner_rule env)])%list)) end
      | O.PParam _ (Some _) | O.PToken _ _ | O.PIdentText _ | O.PGuest _ _ _ _
      | O.PBinderIdent | O.PBinderList _ _ _ _ _ _ _ | O.PGuard | O.POptional _ _ _ =>
          ItemResult items true inspected
      end end end.

Record OriginalState := { original_configuration : Configuration }.
Record RelocatedState := { relocated_configuration : Configuration }.
Definition relocate state := {| relocated_configuration := original_configuration state |}.
Definition original_step env state := core_step env (original_configuration state).
Definition relocated_step env state := core_step env (relocated_configuration state).
Fixpoint original_execute fuel env state := match fuel with
| 0 => Continue (original_configuration state)
| S remaining => match original_step env state with
    | Continue next => original_execute remaining env {| original_configuration := next |}
    | terminal => terminal end end.
Fixpoint relocated_execute fuel env state := match fuel with
| 0 => Continue (relocated_configuration state)
| S remaining => match relocated_step env state with
    | Continue next => relocated_execute remaining env {| relocated_configuration := next |}
    | terminal => terminal end end.
Theorem exact_helper_step_relocation : forall env state,
  relocated_step env (relocate state) = original_step env state.
Proof. reflexivity. Qed.
Theorem finite_helpers_preserve_full_results_and_observation_prefix : forall fuel env state,
  relocated_execute fuel env (relocate state) = original_execute fuel env state.
Proof.
  induction fuel; intros; cbn [relocated_execute original_execute]; [reflexivity|].
  rewrite exact_helper_step_relocation.
  destruct (original_step env state) as [next|name pending trace|items truncated trace]; try reflexivity.
  exact (IHfuel env {| original_configuration := next |}).
Qed.

Definition original_first_param fuel env owner positions :=
  original_execute fuel env
    {| original_configuration := Searching (name_state (root_positions owner positions) []) |}.
Definition relocated_first_param fuel env owner positions :=
  relocated_execute fuel env
    {| relocated_configuration := Searching (name_state (root_positions owner positions) []) |}.
Definition original_initial_body fuel env owner shape := match B.shape_body_cat shape with
| Some text => NameResult (Some {| name_owner := owner; name_field := ExplicitBody; name_text := text |}) [] []
| None => original_first_param fuel env owner (B.positions shape) end.
Definition relocated_initial_body fuel env owner shape := match B.shape_body_cat shape with
| Some text => NameResult (Some {| name_owner := owner; name_field := ExplicitBody; name_text := text |}) [] []
| None => relocated_first_param fuel env owner (B.positions shape) end.
Definition original_binder_items fuel env positions :=
  original_execute fuel env {| original_configuration := Collecting (item_state positions 0 [] []) |}.
Definition relocated_binder_items fuel env positions :=
  relocated_execute fuel env {| relocated_configuration := Collecting (item_state positions 0 [] []) |}.
Theorem first_param_entry_relocation : forall fuel env owner positions,
  relocated_first_param fuel env owner positions = original_first_param fuel env owner positions.
Proof.
  intros; exact (finite_helpers_preserve_full_results_and_observation_prefix fuel env
    {| original_configuration := Searching (name_state (root_positions owner positions) []) |}).
Qed.
Theorem initial_body_entry_relocation : forall fuel env owner shape,
  relocated_initial_body fuel env owner shape = original_initial_body fuel env owner shape.
Proof.
  intros; unfold relocated_initial_body, original_initial_body.
  destruct (B.shape_body_cat shape); [reflexivity|apply first_param_entry_relocation].
Qed.
Theorem binder_items_entry_relocation : forall fuel env positions,
  relocated_binder_items fuel env positions = original_binder_items fuel env positions.
Proof.
  intros; exact (finite_helpers_preserve_full_results_and_observation_prefix fuel env
    {| original_configuration := Collecting (item_state positions 0 [] []) |}).
Qed.

(** These two helpers have no loop state or changed representation at all. *)
Definition original_lookup := lookup_src_idx.
Definition relocated_lookup := lookup_src_idx.
Definition original_required_top := required_top_cat_after_position.
Definition relocated_required_top := required_top_cat_after_position.
Theorem lookup_and_previous_guard_relocation :
  (forall name names, relocated_lookup name names = original_lookup name names) /\
  (forall previous names, relocated_required_top previous names = original_required_top previous names).
Proof. split; reflexivity. Qed.

Lemma first_matching_category_index : forall prefix name suffix,
  Forall (fun prior => String.eqb prior name = false) prefix ->
  first_category_index name (prefix ++ name :: suffix)%list = Some (List.length prefix).
Proof.
  induction prefix as [|prior rest IH]; intros name suffix H.
  - change ((if String.eqb name name then Some 0
      else option_map S (first_category_index name suffix)) = Some 0).
    rewrite String.eqb_refl; reflexivity.
  - inversion H as [|entry tail Hprior Hrest]; subst.
    change ((if String.eqb prior name then Some 0
      else option_map S (first_category_index name (rest ++ name :: suffix)%list)) =
      Some (S (List.length rest))).
    rewrite Hprior, IH by assumption; reflexivity.
Qed.
Theorem lookup_keeps_first_duplicate_then_casts : forall prefix name suffix,
  Forall (fun prior => String.eqb prior name = false) prefix ->
  lookup_src_idx name (prefix ++ name :: suffix)%list = Some (List.length prefix mod 65536).
Proof. intros; unfold lookup_src_idx; rewrite first_matching_category_index by assumption; reflexivity. Qed.
(* Keep modulus arithmetic symbolic through equality elimination. Instantiating
   injection directly at 65536 normalizes a large unary modulo term: the timed
   check was interrupted there after 343 seconds. This general lemma retains
   the exact bound while avoiding that proof-construction reduction. *)
Lemma mapped_modulo_result_is_bounded : forall value modulus index,
  modulus <> 0 ->
  option_map (fun source => source mod modulus) value = Some index -> index < modulus.
Proof.
  intros [source|] modulus index Hnonzero H; [|discriminate].
  change (Some (source mod modulus) = Some index) in H.
  injection H as Hindex.
  rewrite <- Hindex.
  apply Nat.mod_upper_bound.
  exact Hnonzero.
Qed.
Theorem lookup_result_is_in_u16_domain : forall name names index,
  lookup_src_idx name names = Some index -> index < 65536.
Proof.
  intros name names index H.
  exact (@mapped_modulo_result_is_bounded (first_category_index name names)
    65536 index (Nat.neq_succ_0 65535) H).
Qed.
Theorem root_reverse_collect_retains_original_pop_order : forall owner positions,
  rev (rev (root_positions owner positions)) = root_positions owner positions.
Proof. intros; apply rev_involutive. Qed.
Theorem child_reverse_push_retains_original_pop_order : forall parent children pending,
  (rev (rev (child_positions parent children)) ++ pending)%list =
  (child_positions parent children ++ pending)%list.
Proof. intros; rewrite rev_involutive; reflexivity. Qed.
Theorem equal_text_at_distinct_positions_has_distinct_borrow_origin : forall owner cat,
  List.map position_path (root_positions owner [O.PParam cat None; O.PParam cat None]) = [[0];[1]].
Proof. reflexivity. Qed.
Theorem parameter_search_keeps_collection_category : forall env ref pending trace cat collection,
  position_value ref = O.PParam cat collection ->
  core_step env (Searching (name_state (ref :: pending) trace)) =
  NameResult (Some (borrowed_param ref cat)) pending (trace ++ [ref])%list.
Proof. intros; cbn [core_step name_state name_work name_trace]; now rewrite H. Qed.
Theorem binder_list_category_short_circuits_children :
  forall env ref pending trace sep close children cat empty multi slot,
  position_value ref = O.PBinderList sep close children (Some cat) empty multi slot ->
  core_step env (Searching (name_state (ref :: pending) trace)) =
  NameResult (Some (borrowed_collection ref cat)) pending (trace ++ [ref])%list.
Proof. intros; cbn [core_step name_state name_work name_trace]; now rewrite H. Qed.
Theorem explicit_body_short_circuits_all_position_reads : forall fuel env owner shape text,
  B.shape_body_cat shape = Some text ->
  original_initial_body fuel env owner shape =
  NameResult (Some {| name_owner := owner; name_field := ExplicitBody; name_text := text |}) [] [].
Proof. intros; unfold original_initial_body; now rewrite H. Qed.
Theorem collection_previous_position_has_no_top_term_guard : forall cat collection names,
  required_top_cat_after_position (Some (O.PParam cat (Some collection))) names = None /\
  required_top_observations (Some (O.PParam cat (Some collection))) = [].
Proof. intros; split; reflexivity. Qed.
Theorem previous_position_is_immediate_not_last_parse : forall cat first second tail,
  previous_position (O.PParam cat None :: O.PLiteral first :: O.PLiteral second :: tail) 2 =
  Some (O.PLiteral first).
Proof. reflexivity. Qed.
Theorem zero_index_never_subtracts_or_reads_previous : forall positions,
  previous_position positions 0 = None.
Proof. reflexivity. Qed.

Theorem unresolved_parameter_preserves_prefix_and_skips_bp : forall env positions index items trace cat,
  nth_error positions index = Some (O.PParam cat None) ->
  lookup_src_idx cat (categories env) = None ->
  core_step env (Collecting (item_state positions index items trace)) =
  ItemResult items true ((trace ++ [InspectPosition index]) ++ [LookupCategory cat])%list.
Proof.
  intros; cbn [core_step item_state original_positions next_position produced_items item_trace].
  now rewrite H,H0.
Qed.
Theorem resolved_parameter_uses_owner_bp_key : forall env positions index items trace cat parsed,
  nth_error positions index = Some (O.PParam cat None) ->
  lookup_src_idx cat (categories env) = Some parsed ->
  core_step env (Collecting (item_state positions index items trace)) =
  Continue (Collecting (item_state positions (S index)
    (items ++ [F.ParamParse parsed (owner_prefix_bp env)])%list
    (((trace ++ [InspectPosition index]) ++ [LookupCategory cat]) ++
      [LookupPrefixBp (owner_category env) (owner_rule env)])%list)).
Proof.
  intros; cbn [core_step item_state original_positions next_position produced_items item_trace].
  now rewrite H,H0.
Qed.
Theorem absent_owner_bp_defaults_to_zero : forall env,
  prefix_bp_map env (owner_category env, owner_rule env) = None -> owner_prefix_bp env = 0.
Proof. intros; unfold owner_prefix_bp; now rewrite H. Qed.
Theorem optional_position_stops_without_visiting_children : forall env positions index items trace children group tokens,
  nth_error positions index = Some (O.POptional children group tokens) ->
  core_step env (Collecting (item_state positions index items trace)) =
  ItemResult items true (trace ++ [InspectPosition index])%list.
Proof.
  intros; cbn [core_step item_state original_positions next_position produced_items item_trace]; now rewrite H.
Qed.
Theorem exhaustion_returns_untruncated_prefix : forall env positions index items trace,
  nth_error positions index = None ->
  core_step env (Collecting (item_state positions index items trace)) = ItemResult items false trace.
Proof.
  intros; cbn [core_step item_state original_positions next_position produced_items item_trace]; now rewrite H.
Qed.

Print Assumptions finite_helpers_preserve_full_results_and_observation_prefix.
Print Assumptions first_param_entry_relocation.
Print Assumptions initial_body_entry_relocation.
Print Assumptions binder_items_entry_relocation.
Print Assumptions lookup_and_previous_guard_relocation.
Print Assumptions lookup_keeps_first_duplicate_then_casts.
Print Assumptions lookup_result_is_in_u16_domain.
Print Assumptions root_reverse_collect_retains_original_pop_order.
Print Assumptions child_reverse_push_retains_original_pop_order.
Print Assumptions equal_text_at_distinct_positions_has_distinct_borrow_origin.
Print Assumptions parameter_search_keeps_collection_category.
Print Assumptions binder_list_category_short_circuits_children.
Print Assumptions explicit_body_short_circuits_all_position_reads.
Print Assumptions collection_previous_position_has_no_top_term_guard.
Print Assumptions previous_position_is_immediate_not_last_parse.
Print Assumptions zero_index_never_subtracts_or_reads_previous.
Print Assumptions unresolved_parameter_preserves_prefix_and_skips_bp.
Print Assumptions resolved_parameter_uses_owner_bp_key.
Print Assumptions absent_owner_bp_defaults_to_zero.
Print Assumptions optional_position_stops_without_visiting_children.
Print Assumptions exhaustion_returns_untruncated_prefix.

End PrefixMemberDescriptorRelocation.
