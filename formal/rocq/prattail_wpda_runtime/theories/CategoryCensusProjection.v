(** Exact source/accessor correspondence for the original category census and
    label-index loops (task 8512), before their Rust relocation.

    Source ledger: wpda_codegen/mod.rs::collect_category_names_with_literals
    has FIVE ordered passes: rule categories, literal types, collection types,
    native types, remaining types. Every type name is read in every type pass;
    an already-seen name suppresses the eligibility callback. Token .any visits
    tokens in order and stops at its first match. from_literals=false suppresses
    the token category read; a missing category is false. There is no data-type
    filter. The final pass inserts every remaining declared type.

    wpda_codegen/infix.rs::build_label_index resolves categories[cat_i] BEFORE
    visiting a row, including an empty row. It reads every label in row order,
    inserts the PAIR (category,label), and truncates both indices to u16. Later
    duplicate keys overwrite earlier values. Missing category is a separate
    indexing fault, not an empty result or a width rejection.

    Source records below are shallow observations, not a reconstructed AST.
    Handles identify original borrowed occurrences; lists retain their order
    and multiplicity. Accessors read those same records lazily at the original
    sites. Events instrument the accessor/field sites, not Rust side effects.
    Distinct recursive source and shared loops are related by induction. The
    shared definition is not used as the source algorithm's implementation.

    The ordered category list represents BOTH the output Vec and membership
    in the source BTreeSet. Only membership/insertion are observed, never set
    traversal; the no-duplicates theorem justifies this abstraction. The label
    map is represented by an insertion history searched newest first: the
    theorem concerns lookup observations, not HashMap storage or iteration.

    Names stand for the exact strings produced by the original to_string.
    Slice lengths/indices are mathematical naturals restricted, at the Rust
    boundary, to existing usize slices. Casts are modeled modulo 65536, with a
    separate in-range theorem; there is no invented bounds refusal. This proves
    the reviewed control-flow transcription and lawful accessor substitution,
    not Rust extraction, arbitrary callback validity, allocation/clone/drop,
    lifetime checking, dynamic grammar admission, or downstream parser behavior.
*)
From Stdlib Require Import List String Bool Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Module CategoryCensusProjection.

Record SourceRule := { source_category : string; source_label : string }.
Record SourceType := {
  source_name : string; source_collection : bool; source_native : bool;
  source_data_marker : bool (* deliberately unobserved by the original loops *)
}.
Record SourceToken := { source_from_literals : bool; source_token_category : option string }.
Record SourceStore := {
  rule_at : nat -> SourceRule;
  type_at : nat -> SourceType;
  token_at : nat -> SourceToken
}.
Record Accessors := {
  rule_category : nat -> string; rule_label : nat -> string;
  type_name : nat -> string; has_collection : nat -> bool;
  has_native : nat -> bool; from_literals : nat -> bool;
  token_category : nat -> option string
}.
Definition project_accessors s :=
 {| rule_category := fun h => source_category (rule_at s h);
    rule_label := fun h => source_label (rule_at s h);
    type_name := fun h => source_name (type_at s h);
    has_collection := fun h => source_collection (type_at s h);
    has_native := fun h => source_native (type_at s h);
    from_literals := fun h => source_from_literals (token_at s h);
    token_category := fun h => source_token_category (token_at s h) |}.

Inductive Pass := LiteralTypes | CollectionTypes | NativeTypes | RemainingTypes.
Inductive Observation :=
| RuleCategory (handle : nat)
| TypeName (pass : Pass) (handle : nat)
| FromLiterals (handle : nat)
| TokenCategory (handle : nat)
| HasCollection (handle : nat)
| HasNative (handle : nat)
| ResolveCategory (index : nat)
| RuleLabel (handle : nat).

Definition seen name categories := existsb (String.eqb name) categories.
Definition insert_first name categories :=
  if seen name categories then categories else (categories ++ [name])%list.
Definition matches_category name category := match category with
| None => false | Some other => String.eqb other name end.

Fixpoint source_any s name tokens : bool * list Observation := match tokens with
| [] => (false, [])
| h :: rest =>
    if source_from_literals (token_at s h) then
      if matches_category name (source_token_category (token_at s h)) then
        (true, [FromLiterals h; TokenCategory h])
      else let '(answer, trace) := source_any s name rest in
        (answer, FromLiterals h :: TokenCategory h :: trace)
    else let '(answer, trace) := source_any s name rest in
      (answer, FromLiterals h :: trace)
end.
Fixpoint shared_any a name tokens : bool * list Observation := match tokens with
| [] => (false, [])
| h :: rest =>
    if from_literals a h then
      if matches_category name (token_category a h) then
        (true, [FromLiterals h; TokenCategory h])
      else let '(answer, trace) := shared_any a name rest in
        (answer, FromLiterals h :: TokenCategory h :: trace)
    else let '(answer, trace) := shared_any a name rest in
      (answer, FromLiterals h :: trace)
end.
Theorem token_scan_accessor_correspondence : forall s name tokens,
  shared_any (project_accessors s) name tokens = source_any s name tokens.
Proof.
  intros s name tokens; induction tokens as [|h rest IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Record Census := { categories : list string; observations : list Observation }.
Definition census cats trace := {| categories := cats; observations := trace |}.
Definition source_rule_step s h state :=
  census (insert_first (source_category (rule_at s h)) (categories state))
    (observations state ++ [RuleCategory h])%list.
Definition shared_rule_step a h state :=
  census (insert_first (rule_category a h) (categories state))
    (observations state ++ [RuleCategory h])%list.

Definition source_type_step s tokens pass h state :=
  let name := source_name (type_at s h) in
  let trace := (observations state ++ [TypeName pass h])%list in
  if seen name (categories state) then census (categories state) trace else
  let '(eligible, extra) := match pass with
    | LiteralTypes => source_any s name tokens
    | CollectionTypes => (source_collection (type_at s h), [HasCollection h])
    | NativeTypes => (source_native (type_at s h), [HasNative h])
    | RemainingTypes => (true, []) end in
  census (if eligible then (categories state ++ [name])%list else categories state)
    (trace ++ extra)%list.
Definition shared_type_step a tokens pass h state :=
  let name := type_name a h in
  let trace := (observations state ++ [TypeName pass h])%list in
  if seen name (categories state) then census (categories state) trace else
  let '(eligible, extra) := match pass with
    | LiteralTypes => shared_any a name tokens
    | CollectionTypes => (has_collection a h, [HasCollection h])
    | NativeTypes => (has_native a h, [HasNative h])
    | RemainingTypes => (true, []) end in
  census (if eligible then (categories state ++ [name])%list else categories state)
    (trace ++ extra)%list.
Theorem type_step_accessor_correspondence : forall s tokens pass h state,
  shared_type_step (project_accessors s) tokens pass h state =
  source_type_step s tokens pass h state.
Proof.
  intros; unfold shared_type_step, source_type_step; cbn.
  destruct (seen (source_name (type_at s h)) (categories state)); [reflexivity|].
  destruct pass; try reflexivity. rewrite token_scan_accessor_correspondence. reflexivity.
Qed.

Fixpoint source_rules s rules state := match rules with
| [] => state | h :: rest => source_rules s rest (source_rule_step s h state) end.
Fixpoint shared_rules a rules state := match rules with
| [] => state | h :: rest => shared_rules a rest (shared_rule_step a h state) end.
Fixpoint source_types s tokens pass types state := match types with
| [] => state
| h :: rest => source_types s tokens pass rest (source_type_step s tokens pass h state) end.
Fixpoint shared_types a tokens pass types state := match types with
| [] => state
| h :: rest => shared_types a tokens pass rest (shared_type_step a tokens pass h state) end.
Theorem rules_accessor_correspondence : forall s rules state,
  shared_rules (project_accessors s) rules state = source_rules s rules state.
Proof.
  intros s rules; induction rules as [|h rest IH]; intros state; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Theorem types_accessor_correspondence : forall s tokens pass types state,
  shared_types (project_accessors s) tokens pass types state =
  source_types s tokens pass types state.
Proof.
  intros s tokens pass types; induction types as [|h rest IH]; intros state; cbn; [reflexivity|].
  rewrite type_step_accessor_correspondence, IH. reflexivity.
Qed.

Definition source_census s rules types tokens :=
  let first := source_rules s rules (census [] []) in
  let second := source_types s tokens LiteralTypes types first in
  let third := source_types s tokens CollectionTypes types second in
  let fourth := source_types s tokens NativeTypes types third in
  source_types s tokens RemainingTypes types fourth.
Definition shared_census a rules types tokens :=
  let first := shared_rules a rules (census [] []) in
  let second := shared_types a tokens LiteralTypes types first in
  let third := shared_types a tokens CollectionTypes types second in
  let fourth := shared_types a tokens NativeTypes types third in
  shared_types a tokens RemainingTypes types fourth.
Theorem five_pass_census_preserves_order_identity_and_observations : forall s rules types tokens,
  shared_census (project_accessors s) rules types tokens = source_census s rules types tokens.
Proof.
  intros; unfold shared_census, source_census.
  rewrite rules_accessor_correspondence. repeat rewrite types_accessor_correspondence.
  reflexivity.
Qed.

Lemma seen_spec : forall name cats, seen name cats = true <-> In name cats.
Proof.
  intros; unfold seen; rewrite existsb_exists; split.
  - intros [other [Hin Heq]]. apply String.eqb_eq in Heq. subst; exact Hin.
  - intros Hin. exists name; split; [exact Hin|apply String.eqb_refl].
Qed.
Lemma unseen_spec : forall name cats, seen name cats = false -> ~ In name cats.
Proof.
  intros name cats Hfalse Hin. apply seen_spec in Hin. congruence.
Qed.
Lemma fresh_append_nodup : forall (cats : list string) (name : string),
  NoDup cats -> ~ In name cats -> NoDup (cats ++ [name])%list.
Proof.
  intros cats name H; induction H as [|head rest Hnot Hdup IH]; intros Hfresh; cbn.
  - constructor; [intro H; inversion H|constructor].
  - constructor.
    + rewrite in_app_iff; cbn; intros [Hin|[Heq|Hbad]].
      * contradiction.
      * subst. apply Hfresh; left; reflexivity.
      * contradiction.
    + apply IH. intro Hin. apply Hfresh; right; exact Hin.
Qed.
Theorem insertion_retains_first_seen_order : forall name cats,
  (seen name cats = true -> insert_first name cats = cats) /\
  (seen name cats = false -> insert_first name cats = (cats ++ [name])%list).
Proof. intros; unfold insert_first; destruct (seen name cats); split; intros; congruence. Qed.
Theorem newly_inserted_index_is_previous_length : forall name cats,
  seen name cats = false -> nth_error (insert_first name cats) (List.length cats) = Some name.
Proof.
  intros name cats H; unfold insert_first; rewrite H, nth_error_app2; [|lia].
  rewrite Nat.sub_diag; reflexivity.
Qed.
Lemma rule_step_nodup : forall s h state,
  NoDup (categories state) -> NoDup (categories (source_rule_step s h state)).
Proof.
  intros; unfold source_rule_step, insert_first; cbn.
  destruct (seen (source_category (rule_at s h)) (categories state)) eqn:E; [assumption|].
  apply fresh_append_nodup; [assumption|apply unseen_spec; exact E].
Qed.
Lemma type_step_nodup : forall s tokens pass h state,
  NoDup (categories state) -> NoDup (categories (source_type_step s tokens pass h state)).
Proof.
  intros; unfold source_type_step.
  destruct (seen (source_name (type_at s h)) (categories state)) eqn:E; [assumption|].
  destruct pass; cbn;
    try (destruct (source_any s (source_name (type_at s h)) tokens) as [eligible trace]);
    try (destruct eligible);
    try (destruct (source_collection (type_at s h)));
    try (destruct (source_native (type_at s h))); cbn; try assumption.
  all: apply fresh_append_nodup; [assumption|apply unseen_spec; exact E].
Qed.
Lemma source_rules_nodup : forall s rules state,
  NoDup (categories state) -> NoDup (categories (source_rules s rules state)).
Proof.
  intros s rules; induction rules; intros state H; cbn; [exact H|].
  apply IHrules, rule_step_nodup; exact H.
Qed.
Lemma source_types_nodup : forall s tokens pass types state,
  NoDup (categories state) -> NoDup (categories (source_types s tokens pass types state)).
Proof.
  intros s tokens pass types; induction types; intros state H; cbn; [exact H|].
  apply IHtypes, type_step_nodup; exact H.
Qed.
Theorem census_has_no_duplicate_categories : forall s rules types tokens,
  NoDup (categories (shared_census (project_accessors s) rules types tokens)).
Proof.
  intros; rewrite five_pass_census_preserves_order_identity_and_observations.
  unfold source_census. repeat apply source_types_nodup.
  apply source_rules_nodup; constructor.
Qed.

Theorem seen_type_skips_eligibility_callbacks : forall a tokens pass h state,
  seen (type_name a h) (categories state) = true ->
  shared_type_step a tokens pass h state =
    census (categories state) (observations state ++ [TypeName pass h])%list.
Proof. intros; unfold shared_type_step; rewrite H; reflexivity. Qed.
Theorem false_from_literals_skips_category_callback : forall a name h rest,
  from_literals a h = false -> shared_any a name (h :: rest) =
  let '(answer, trace) := shared_any a name rest in (answer, FromLiterals h :: trace).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem first_token_match_stops_scan : forall a name h rest,
  from_literals a h = true -> token_category a h = Some name ->
  shared_any a name (h :: rest) = (true, [FromLiterals h; TokenCategory h]).
Proof. intros; cbn; rewrite H, H0; cbn; rewrite String.eqb_refl; reflexivity. Qed.
Theorem missing_token_category_continues_scan : forall a name h rest,
  from_literals a h = true -> token_category a h = None ->
  shared_any a name (h :: rest) =
  let '(answer, trace) := shared_any a name rest in
    (answer, FromLiterals h :: TokenCategory h :: trace).
Proof. intros; cbn; rewrite H, H0; reflexivity. Qed.
Theorem remaining_pass_inserts_without_predicate : forall a tokens h state,
  categories (shared_type_step a tokens RemainingTypes h state) =
  insert_first (type_name a h) (categories state).
Proof. intros; unfold shared_type_step, insert_first; destruct (seen _ _); reflexivity. Qed.

(** Label-index observations retain every category access, even for empty rows.
    The newest-first history implements exactly the observable overwrite rule. *)
Definition Key := (string * string)%type.
Definition Indices := (nat * nat)%type.
Definition History := list (Key * Indices).
Definition key_eqb (left right : Key) :=
  String.eqb (fst left) (fst right) && String.eqb (snd left) (snd right).
Fixpoint lookup key (history : History) : option Indices := match history with
| [] => None | (other, value) :: rest => if key_eqb key other then Some value else lookup key rest end.
Definition cast_u16 index := index mod 65536.
Definition put cat label ci ri (history : History) :=
  ((cat, label), (cast_u16 ci, cast_u16 ri)) :: history.
Record IndexState := { index_history : History; index_observations : list Observation }.
Definition index_state history trace := {| index_history := history; index_observations := trace |}.
Inductive IndexOutcome :=
| IndexComplete (state : IndexState)
| MissingCategory (index : nat) (state : IndexState).

Fixpoint source_row s cat ci ri rules state := match rules with
| [] => state
| h :: rest => source_row s cat ci (S ri) rest
    (index_state (put cat (source_label (rule_at s h)) ci ri (index_history state))
      (index_observations state ++ [RuleLabel h])%list) end.
Fixpoint shared_row a cat ci ri rules state := match rules with
| [] => state
| h :: rest => shared_row a cat ci (S ri) rest
    (index_state (put cat (rule_label a h) ci ri (index_history state))
      (index_observations state ++ [RuleLabel h])%list) end.
Fixpoint source_index s cats ci rows state := match rows with
| [] => IndexComplete state
| rules :: rest =>
    let observed := index_state (index_history state)
      (index_observations state ++ [ResolveCategory ci])%list in
    match nth_error cats ci with
    | None => MissingCategory ci observed
    | Some cat => source_index s cats (S ci) rest (source_row s cat ci 0 rules observed)
    end end.
Fixpoint shared_index a cats ci rows state := match rows with
| [] => IndexComplete state
| rules :: rest =>
    let observed := index_state (index_history state)
      (index_observations state ++ [ResolveCategory ci])%list in
    match nth_error cats ci with
    | None => MissingCategory ci observed
    | Some cat => shared_index a cats (S ci) rest (shared_row a cat ci 0 rules observed)
    end end.
Theorem row_accessor_correspondence : forall s cat ci ri rules state,
  shared_row (project_accessors s) cat ci ri rules state = source_row s cat ci ri rules state.
Proof.
  intros s cat ci ri rules; revert ri; induction rules; intros ri state; cbn; [reflexivity|].
  apply IHrules.
Qed.
Theorem label_index_preserves_casts_collisions_faults_and_observations : forall s cats ci rows state,
  shared_index (project_accessors s) cats ci rows state = source_index s cats ci rows state.
Proof.
  intros s cats ci rows; revert ci; induction rows; intros ci state; cbn; [reflexivity|].
  destruct (nth_error cats ci); [|reflexivity].
  rewrite row_accessor_correspondence. apply IHrows.
Qed.
Theorem last_duplicate_key_wins : forall cat label ci ri history,
  lookup (cat, label) (put cat label ci ri history) = Some (cast_u16 ci, cast_u16 ri).
Proof.
  intros cat label ci ri history.
  change ((if String.eqb cat cat && String.eqb label label
    then Some (cast_u16 ci, cast_u16 ri)
    else lookup (cat, label) history) = Some (cast_u16 ci, cast_u16 ri)).
  rewrite !String.eqb_refl; reflexivity.
Qed.
Theorem distinct_key_survives_insert : forall key cat label ci ri history,
  key_eqb key (cat, label) = false ->
  lookup key (put cat label ci ri history) = lookup key history.
Proof. intros; unfold put; cbn [lookup]; rewrite H; reflexivity. Qed.
Theorem cast_exact_in_u16_domain : forall index,
  index < 65536 -> cast_u16 index = index.
Proof. intros; apply Nat.mod_small; assumption. Qed.
Theorem cast_always_u16 : forall index, cast_u16 index < 65536.
Proof. intros; apply Nat.mod_upper_bound; discriminate. Qed.
Theorem missing_category_fault_even_for_empty_row : forall a cats ci rest state,
  nth_error cats ci = None -> shared_index a cats ci ([] :: rest) state =
    MissingCategory ci (index_state (index_history state)
      (index_observations state ++ [ResolveCategory ci])%list).
Proof. intros; cbn; rewrite H; reflexivity. Qed.

(** Executable witnesses combine all five passes and distinguish loop orders.
    Rule order introduces R before A; type order places unqualified Z first,
    but Z must be last. Tokens include a guarded category, missing category,
    successful match, and unvisited suffix. All types have a data marker, which
    the original algorithm never reads and which does not filter them out. *)
Definition witness_store : SourceStore :=
 {| rule_at := fun h =>
      {| source_category := if Nat.eqb h 0 then "R"%string else "A"%string;
         source_label := "same"%string |};
    type_at := fun h =>
      {| source_name := match h with 0 => "Z"%string | 1 => "N"%string
           | 2 => "C"%string | 3 => "L"%string | _ => "R"%string end;
         source_collection := Nat.eqb h 2; source_native := Nat.eqb h 1;
         source_data_marker := true |};
    token_at := fun h =>
      {| source_from_literals := negb (Nat.eqb h 0);
         source_token_category := match h with 0 => Some "Z"%string
           | 1 => None | _ => Some "L"%string end |} |}.
Example five_ordered_passes_witness :
  categories (shared_census (project_accessors witness_store)
    [0; 1; 0] [0; 1; 2; 3; 4] [0; 1; 2; 3]) =
  ["R"%string; "A"%string; "L"%string; "C"%string; "N"%string; "Z"%string].
Proof. vm_compute; reflexivity. Qed.
Example token_guard_missing_and_early_stop_witness :
  shared_any (project_accessors witness_store) "L"%string [0; 1; 2; 3] =
  (true, [FromLiterals 0; FromLiterals 1; TokenCategory 1;
          FromLiterals 2; TokenCategory 2]).
Proof. vm_compute; reflexivity. Qed.
Example repeated_rule_handle_retains_all_observations :
  observations (shared_rules (project_accessors witness_store) [0; 1; 0] (census [] [])) =
  [RuleCategory 0; RuleCategory 1; RuleCategory 0].
Proof. vm_compute; reflexivity. Qed.
Example duplicate_labels_within_row_last_wins :
  lookup ("R"%string, "same"%string)
    (index_history (shared_row (project_accessors witness_store) "R"%string 0 0
      [0; 1; 0] (index_state [] []))) = Some (0, 2).
Proof. vm_compute; reflexivity. Qed.
Example duplicate_categories_across_rows_last_wins :
  shared_index (project_accessors witness_store) ["R"%string; "R"%string] 0
    [[0; 1]; [0]] (index_state [] []) =
  IndexComplete (index_state
    [(("R"%string, "same"%string), (1, 0));
     (("R"%string, "same"%string), (0, 1));
     (("R"%string, "same"%string), (0, 0))]
    [ResolveCategory 0; RuleLabel 0; RuleLabel 1; ResolveCategory 1; RuleLabel 0]).
Proof. vm_compute; reflexivity. Qed.
Example same_label_distinct_category_keys :
  lookup ("A"%string, "same"%string)
    (put "R"%string "same"%string 1 0
      (put "A"%string "same"%string 0 0 [])) = Some (0, 0).
Proof. vm_compute; reflexivity. Qed.
Example empty_row_still_requires_category :
  shared_index (project_accessors witness_store) [] 0 [[]] (index_state [] []) =
  MissingCategory 0 (index_state [] [ResolveCategory 0]).
Proof. reflexivity. Qed.
Example wrapping_is_not_a_missing_category_fault : cast_u16 65536 = 0.
Proof. unfold cast_u16; apply Nat.mod_same; discriminate. Qed.

Print Assumptions token_scan_accessor_correspondence.
Print Assumptions type_step_accessor_correspondence.
Print Assumptions five_pass_census_preserves_order_identity_and_observations.
Print Assumptions insertion_retains_first_seen_order.
Print Assumptions newly_inserted_index_is_previous_length.
Print Assumptions census_has_no_duplicate_categories.
Print Assumptions seen_type_skips_eligibility_callbacks.
Print Assumptions false_from_literals_skips_category_callback.
Print Assumptions first_token_match_stops_scan.
Print Assumptions missing_token_category_continues_scan.
Print Assumptions remaining_pass_inserts_without_predicate.
Print Assumptions label_index_preserves_casts_collisions_faults_and_observations.
Print Assumptions last_duplicate_key_wins.
Print Assumptions distinct_key_survives_insert.
Print Assumptions cast_exact_in_u16_domain.
Print Assumptions cast_always_u16.
Print Assumptions missing_category_fault_even_for_empty_row.

End CategoryCensusProjection.
