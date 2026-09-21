(** Ordered relocation boundary for synthetic::build_per_category_rules.

    Original source: macros/src/gen/runtime/wpda_codegen/synthetic.rs.
    Source AST constructors below are separate from neutral recipes and their
    materializer. Original user rules are opaque handles: normalization is the
    original operation, not reconstruction from a shallow classifier view.

    The phase driver must preserve: stable user grouping, normalization, native
    literals, collection literals, current-bucket Var suppression, all ordered
    Apply/MApply pairs, THEN a separate ordered Lam pass. Duplicate declarations
    are not deduplicated. Parse-category lookup chooses its last matching slot;
    absent homes are skipped, but domains remain all non-data declarations.

    Label generation, native metadata, lowercase, collection element resolution
    and delimiter trimming are observations of original helpers. In particular
    trimmed_open is the exact trim_end_matches('(') result and split_open is
    raw_open != trimmed_open: the recipe inserts ONE '(' when split_open is true,
    not one per removed character. No new Unicode/native/normalization algorithm
    is justified by this model. Pure observation equalities do not prove that
    eager projection preserves arbitrary helper effects or panics: retaining
    helper gating/order is a separate source-correspondence obligation.

    This is a finite ordered-list/materialization refinement, not a replacement
    scheduler or parser proof. Rust correspondence must also check original
    constructor defaults, exact identifiers/spans and collection mappings.
*)
From Stdlib Require Import List String Bool Arith.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module SyntheticRuleProjection.

Inductive CollectionKind := ListKind | BagKind | MapKind | SetKind | PathmapKind.
Inductive RawType := RBase (name : string) | RCollection (kind : CollectionKind) (element : RawType)
  | RArrow (domain codomain : RawType).
Inductive RecipeType := Base (name : string) | Collection (kind : CollectionKind) (element : string)
  | Arrow (domain codomain : string).
Definition materialize_type ty :=
  match ty with Base n => RBase n | Collection k n => RCollection k (RBase n)
              | Arrow d c => RArrow (RBase d) (RBase c) end.
Inductive RawParam := RSimple (name : string) (ty : RawType)
  | RAbstraction (binder body : string) (ty : RawType).
Inductive RecipeParam := Simple (name : string) (ty : RecipeType)
  | Abstraction (binder body : string) (ty : RecipeType).
Definition materialize_param p :=
  match p with Simple n t => RSimple n (materialize_type t)
             | Abstraction b n t => RAbstraction b n (materialize_type t) end.
Inductive RawSyntax := RLiteral (text : string) | RParam (name : string)
  | RSep (name separator : string) (source : option nat).
Inductive RecipeSyntax := Literal (text : string) | Param (name : string)
  | Sep (name separator : string).
Definition materialize_syntax s :=
  match s with Literal t => RLiteral t | Param n => RParam n | Sep n t => RSep n t None end.
Inductive Legacy := CategoryItem (name : string) | VarItem (name : string).

Record Defaults := {
  bindings : list nat; rust_code : option nat; eval_mode : option nat;
  right_assoc : bool; shares_previous : bool; prefix_bp : option nat;
  tier_directive : option nat; auto_injected : bool;
  doc_comment : option string; canonical_synonym : bool
}.
Definition original_defaults :=
  {| bindings := []; rust_code := None; eval_mode := None;
     right_assoc := false; shares_previous := false; prefix_bp := None;
     tier_directive := None; auto_injected := false;
     doc_comment := None; canonical_synonym := false |}.
Record RawRule := {
  raw_label : string; raw_category : string; raw_items : list Legacy;
  raw_params : option (list RawParam); raw_syntax : option (list RawSyntax);
  raw_defaults : Defaults
}.
Record Recipe := {
  label : string; category : string; items : list Legacy;
  params : option (list RecipeParam); syntax : option (list RecipeSyntax);
  defaults : Defaults
}.
Definition raw_rule l c i p s :=
  {| raw_label := l; raw_category := c; raw_items := i; raw_params := p;
     raw_syntax := s; raw_defaults := original_defaults |}.
Definition recipe l c i p s :=
  {| label := l; category := c; items := i; params := p;
     syntax := s; defaults := original_defaults |}.
Definition materialize_recipe r :=
  {| raw_label := label r; raw_category := category r; raw_items := items r;
     raw_params := option_map (map materialize_param) (params r);
     raw_syntax := option_map (map materialize_syntax) (syntax r);
     raw_defaults := defaults r |}.

Record CollectionObservation := {
  collection_kind : CollectionKind; trimmed_open : string; split_open : bool;
  close_text : string; separator_text : string; element_name : option string
}.
Definition collection_label k := match k with ListKind => "ListLit" | BagKind => "BagLit"
  | MapKind => "MapLit" | SetKind => "SetLit" | PathmapKind => "PathmapLit" end.
Definition element_or_home home o := match element_name o with Some e => e | None => home end.

(** Separate concrete constructors; all ordered parameter/syntax fields and
    fixed defaults are exposed, including Arrow/Abstraction absent from the
    earlier infix view. *)
Definition raw_native home l := raw_rule l home [CategoryItem home] None None.
Definition recipe_native home l := recipe l home [CategoryItem home] None None.
Definition raw_var home l := raw_rule l home [VarItem home] None None.
Definition recipe_var home l := recipe l home [VarItem home] None None.
Definition raw_collection home o :=
  raw_rule (collection_label (collection_kind o)) home []
    (Some [RSimple "elems" (RCollection (collection_kind o) (RBase (element_or_home home o)))])
    (Some (([RLiteral (trimmed_open o)] ++
      (if split_open o then [RLiteral "("] else []) ++
      [RSep "elems" (separator_text o) None; RLiteral (close_text o)])%list)).
Definition recipe_collection home o :=
  recipe (collection_label (collection_kind o)) home []
    (Some [Simple "elems" (Collection (collection_kind o) (element_or_home home o))])
    (Some (([Literal (trimmed_open o)] ++
      (if split_open o then [Literal "("] else []) ++
      [Sep "elems" (separator_text o); Literal (close_text o)])%list)).
Definition raw_apply home dom lower :=
  raw_rule ("Apply" ++ dom) home []
    (Some [RSimple "f" (RBase home); RSimple "x" (RBase dom)])
    (Some [RLiteral ("$" ++ lower); RLiteral "("; RParam "f";
           RLiteral ","; RParam "x"; RLiteral ")"]).
Definition recipe_apply home dom lower :=
  recipe ("Apply" ++ dom) home []
    (Some [Simple "f" (Base home); Simple "x" (Base dom)])
    (Some [Literal ("$" ++ lower); Literal "("; Param "f";
           Literal ","; Param "x"; Literal ")"]).
Definition raw_mapply home dom lower :=
  raw_rule ("MApply" ++ dom) home []
    (Some [RSimple "f" (RBase home); RSimple "xs" (RCollection ListKind (RBase dom))])
    (Some [RLiteral ("$$" ++ lower ++ "("); RParam "f"; RLiteral ",";
           RSep "xs" "," None; RLiteral ")"]).
Definition recipe_mapply home dom lower :=
  recipe ("MApply" ++ dom) home []
    (Some [Simple "f" (Base home); Simple "xs" (Collection ListKind dom)])
    (Some [Literal ("$$" ++ lower ++ "("); Param "f"; Literal ",";
           Sep "xs" ","; Literal ")"]).
Definition raw_lam home :=
  raw_rule ("Lam" ++ home) home []
    (Some [RAbstraction "x" "p" (RArrow (RBase home) (RBase home))])
    (Some [RLiteral "^"; RParam "x"; RLiteral "."; RLiteral "{"; RParam "p"; RLiteral "}"]).
Definition recipe_lam home :=
  recipe ("Lam" ++ home) home []
    (Some [Abstraction "x" "p" (Arrow home home)])
    (Some [Literal "^"; Param "x"; Literal "."; Literal "{"; Param "p"; Literal "}"]).

Theorem all_constructor_fields_materialize_exactly : forall home dom lower l o,
  materialize_recipe (recipe_native home l) = raw_native home l /\
  materialize_recipe (recipe_var home l) = raw_var home l /\
  materialize_recipe (recipe_collection home o) = raw_collection home o /\
  materialize_recipe (recipe_apply home dom lower) = raw_apply home dom lower /\
  materialize_recipe (recipe_mapply home dom lower) = raw_mapply home dom lower /\
  materialize_recipe (recipe_lam home) = raw_lam home.
Proof. intros; destruct o as [k op has_paren cl sep elem]; destruct has_paren; repeat split; reflexivity. Qed.

Lemma materialize_native : forall h l, materialize_recipe (recipe_native h l) = raw_native h l.
Proof. reflexivity. Qed.
Lemma materialize_var : forall h l, materialize_recipe (recipe_var h l) = raw_var h l.
Proof. reflexivity. Qed.
Lemma materialize_collection : forall h o, materialize_recipe (recipe_collection h o) = raw_collection h o.
Proof. intros h [k op has_paren cl sep elem]; destruct has_paren; reflexivity. Qed.

(** Last-write-wins parse-category index, matching collecting the enumerated
    category vector into HashMap. It does not deduplicate the output slots. *)
Fixpoint last_slot name categories : option nat :=
  match categories with
  | [] => None
  | head :: rest => match last_slot name rest with
      | Some index => Some (S index)
      | None => if String.eqb name head then Some 0 else None end
  end.
Theorem later_duplicate_slot_wins : forall name rest index,
  last_slot name rest = Some index -> last_slot name (name :: rest) = Some (S index).
Proof. intros; cbn; now rewrite H. Qed.

Fixpoint push_at {A} index (value : A) rows :=
  match rows, index with
  | [], _ => []
  | row :: rest, 0 => (row ++ [value])%list :: rest
  | row :: rest, S i => row :: push_at i value rest
  end.
Definition map_rows {A B} (f : A -> B) rows := map (map f) rows.
Lemma map_rows_push : forall A B (f : A -> B) rows index value,
  map_rows f (push_at index value rows) = push_at index (f value) (map_rows f rows).
Proof.
  intros A B f rows; induction rows as [|row rest IH]; intros [|i] value; cbn; try reflexivity.
  - now rewrite map_app.
  - change (map f row :: map_rows f (push_at i value rest) =
      map f row :: push_at i (f value) (map_rows f rest)).
    f_equal. apply IH.
Qed.
Lemma map_rows_nth : forall A B (f : A -> B) rows index,
  nth index (map_rows f rows) [] = map f (nth index rows []).
Proof. intros A B f rows; induction rows; intros [|index]; cbn; auto. Qed.

(** Reusable ordered fold law. This proves complete order-sensitive results,
    not only membership/cardinality, and permits state-dependent Var scans. *)
Lemma fold_projection : forall A B S T (project : A -> B) (materialize : T -> S)
    (source_step : S -> A -> S) (view_step : T -> B -> T),
  (forall state input, materialize (view_step state (project input)) =
    source_step (materialize state) input) ->
  forall inputs state,
  materialize (fold_left view_step (map project inputs) state) =
    fold_left source_step inputs (materialize state).
Proof.
  intros A B S T project materialize source_step view_step H inputs.
  induction inputs as [|input rest IH]; intros state; cbn; [reflexivity|].
  rewrite IH, H. reflexivity.
Qed.

Section Pipeline.
Context {Native User Handle : Type}.
Variable literal_label : Native -> string.
Variable var_label lower_name : string -> string.
Variable original_user : Handle -> User.
Variable normalize : User -> User.
Variable user_category : User -> string.
Variable user_first_var : User -> bool.

Record SourceCategory := {
  source_name : string; source_data : bool; source_native : option Native;
  source_collection : option CollectionObservation
}.
Record CategoryView := {
  view_name : string; view_data : bool; view_literal_label : option string;
  view_collection : option CollectionObservation; view_var_label : string
}.
Definition project_category c :=
  {| view_name := source_name c; view_data := source_data c;
     view_literal_label := option_map literal_label (source_native c);
     view_collection := source_collection c; view_var_label := var_label (source_name c) |}.
Inductive SourceStored := Original (user : User) | Generated (rule : RawRule).
Inductive Stored := OriginalHandle (handle : Handle) | Synthetic (rule : Recipe).
Definition materialize stored := match stored with
  | OriginalHandle h => Original (normalize (original_user h))
  | Synthetic r => Generated (materialize_recipe r) end.
Definition raw_first_var r := match raw_items r with VarItem _ :: _ => true | _ => false end.
Definition source_first_var stored := match stored with
  | Original u => user_first_var u | Generated r => raw_first_var r end.
Definition view_first_var stored := match stored with
  | OriginalHandle h => user_first_var (normalize (original_user h))
  | Synthetic r => match items r with VarItem _ :: _ => true | _ => false end end.
Lemma first_var_materialization : forall stored,
  source_first_var (materialize stored) = view_first_var stored.
Proof. intros [h|r]; [reflexivity|]. destruct r; reflexivity. Qed.
Lemma var_scan_materialization : forall row,
  existsb source_first_var (map materialize row) = existsb view_first_var row.
Proof. induction row; cbn; [reflexivity|]. now rewrite first_var_materialization, IHrow. Qed.

Variable categories : list string.
Definition append_source home (value : SourceStored) rows := match last_slot home categories with
  | Some i => push_at i value rows | None => rows end.
Definition append_view home (value : Stored) rows := match last_slot home categories with
  | Some i => push_at i value rows | None => rows end.
Lemma append_materializes : forall rows home value,
  map_rows materialize (append_view home value rows) =
    append_source home (materialize value) (map_rows materialize rows).
Proof. intros; unfold append_view, append_source; destruct (last_slot home categories); [apply map_rows_push|reflexivity]. Qed.

Definition source_user_step rows h :=
  append_source (user_category (original_user h)) (Original (normalize (original_user h))) rows.
Definition view_user_step rows h :=
  append_view (user_category (original_user h)) (OriginalHandle h) rows.
Lemma user_step_materializes : forall rows h,
  map_rows materialize (view_user_step rows h) = source_user_step (map_rows materialize rows) h.
Proof. intros; apply append_materializes. Qed.

(** The original code groups copies BEFORE normalizing in category/bucket
    order. The specification's normalized insertion has equal payloads under
    the same pure operation; this is not equality of effectful call traces. *)
Definition normalize_stored value := match value with
  | Original u => Original (normalize u) | Generated r => Generated r end.
Definition source_raw_user_step rows h :=
  append_source (user_category (original_user h)) (Original (original_user h)) rows.
Lemma normalize_append : forall rows home value,
  map_rows normalize_stored (append_source home value rows) =
    append_source home (normalize_stored value) (map_rows normalize_stored rows).
Proof.
  intros; unfold append_source; destruct (last_slot home categories);
    [apply map_rows_push|reflexivity].
Qed.
Lemma group_then_normalize_payloads : forall users rows,
  map_rows normalize_stored (fold_left source_raw_user_step users rows) =
    fold_left source_user_step users (map_rows normalize_stored rows).
Proof.
  induction users as [|h rest IH]; intros rows; [reflexivity|].
  change (map_rows normalize_stored
      (fold_left source_raw_user_step rest (source_raw_user_step rows h)) =
    fold_left source_user_step rest (source_user_step (map_rows normalize_stored rows) h)).
  rewrite IH. unfold source_raw_user_step, source_user_step.
  now rewrite normalize_append.
Qed.

Definition source_native_step rows c :=
  if source_data c then rows else
  match source_collection c, source_native c with
  | None, Some n => append_source (source_name c) (Generated (raw_native (source_name c) (literal_label n))) rows
  | _, _ => rows end.
Definition view_native_step rows c :=
  if view_data c then rows else
  match view_collection c, view_literal_label c with
  | None, Some l => append_view (view_name c) (Synthetic (recipe_native (view_name c) l)) rows
  | _, _ => rows end.
Lemma native_step_materializes : forall rows c,
  map_rows materialize (view_native_step rows (project_category c)) =
    source_native_step (map_rows materialize rows) c.
Proof.
  intros rows [name data native collection]; unfold view_native_step, source_native_step; cbn.
  destruct data; [reflexivity|]. destruct collection; [reflexivity|].
  destruct native; [apply append_materializes|reflexivity].
Qed.

Definition source_collection_step rows c :=
  if source_data c then rows else match source_collection c with
  | Some o => append_source (source_name c) (Generated (raw_collection (source_name c) o)) rows
  | None => rows end.
Definition view_collection_step rows c :=
  if view_data c then rows else match view_collection c with
  | Some o => append_view (view_name c) (Synthetic (recipe_collection (view_name c) o)) rows
  | None => rows end.
Lemma collection_step_materializes : forall rows c,
  map_rows materialize (view_collection_step rows (project_category c)) =
    source_collection_step (map_rows materialize rows) c.
Proof.
  intros rows [name data native collection]; unfold view_collection_step, source_collection_step; cbn.
  destruct data; [reflexivity|].
  destruct collection as [[k op has_paren cl sep elem]|]; [|reflexivity].
  destruct has_paren; apply append_materializes.
Qed.

Definition source_var_step rows c :=
  if source_data c then rows else match last_slot (source_name c) categories with
  | None => rows
  | Some i => if existsb source_first_var (nth i rows []) then rows
      else push_at i (Generated (raw_var (source_name c) (var_label (source_name c)))) rows end.
Definition view_var_step rows c :=
  if view_data c then rows else match last_slot (view_name c) categories with
  | None => rows
  | Some i => if existsb view_first_var (nth i rows []) then rows
      else push_at i (Synthetic (recipe_var (view_name c) (view_var_label c))) rows end.
Lemma var_step_materializes : forall rows c,
  map_rows materialize (view_var_step rows (project_category c)) =
    source_var_step (map_rows materialize rows) c.
Proof.
  intros rows [name data native collection]; unfold view_var_step, source_var_step; cbn.
  destruct data; [reflexivity|]. destruct (last_slot name categories) as [i|]; [|reflexivity].
  rewrite map_rows_nth, var_scan_materialization.
  destruct (existsb view_first_var (nth i rows [])); [reflexivity|apply map_rows_push].
Qed.

Definition source_pair_step rows pair := let '(home, dom) := pair in
  append_source home (Generated (raw_mapply home dom (lower_name dom)))
    (append_source home (Generated (raw_apply home dom (lower_name dom))) rows).
Definition view_pair_step rows pair := let '(home, dom) := pair in
  append_view home (Synthetic (recipe_mapply home dom (lower_name dom)))
    (append_view home (Synthetic (recipe_apply home dom (lower_name dom))) rows).
Lemma pair_step_materializes : forall rows pair,
  map_rows materialize (view_pair_step rows pair) = source_pair_step (map_rows materialize rows) pair.
Proof. intros rows [home dom]; unfold view_pair_step, source_pair_step. now rewrite !append_materializes. Qed.
Definition source_lam_step rows home := append_source home (Generated (raw_lam home)) rows.
Definition view_lam_step rows home := append_view home (Synthetic (recipe_lam home)) rows.
Lemma lam_step_materializes : forall rows home,
  map_rows materialize (view_lam_step rows home) = source_lam_step (map_rows materialize rows) home.
Proof. intros; apply append_materializes. Qed.

Definition source_names declarations :=
  map source_name (filter (fun c => negb (source_data c)) declarations).
Definition view_names declarations :=
  map view_name (filter (fun c => negb (view_data c)) declarations).
Lemma nondata_names_preserved : forall declarations,
  view_names (map project_category declarations) = source_names declarations.
Proof.
  induction declarations as [|[name data native collection] rest IH]; cbn; [reflexivity|].
  unfold view_names, source_names in *; cbn in *.
  destruct data; cbn; now rewrite IH.
Qed.
Definition pairs (names : list string) := flat_map (fun home => map (fun dom => (home, dom)) names) names.

Definition source_generated_phases declarations (has_binders : bool) grouped :=
  let native := fold_left source_native_step declarations grouped in
  let collections := fold_left source_collection_step declarations native in
  let vars := fold_left source_var_step declarations collections in
  if has_binders then
    let names := source_names declarations in
    let applications := fold_left source_pair_step (pairs names) vars in
    fold_left source_lam_step names applications
  else vars.
Definition source_driver declarations users has_binders initial :=
  source_generated_phases declarations has_binders
    (fold_left source_user_step users initial).
Definition original_source_driver declarations users has_binders initial :=
  source_generated_phases declarations has_binders
    (map_rows normalize_stored (fold_left source_raw_user_step users initial)).
Lemma original_normalization_schedule_payloads : forall declarations users binders initial,
  original_source_driver declarations users binders initial =
    source_driver declarations users binders (map_rows normalize_stored initial).
Proof.
  intros. unfold original_source_driver, source_driver.
  now rewrite group_then_normalize_payloads.
Qed.
Definition view_driver declarations users (has_binders : bool) initial :=
  let grouped := fold_left view_user_step users initial in
  let native := fold_left view_native_step declarations grouped in
  let collections := fold_left view_collection_step declarations native in
  let vars := fold_left view_var_step declarations collections in
  if has_binders then
    let names := view_names declarations in
    let applications := fold_left view_pair_step (pairs names) vars in
    fold_left view_lam_step names applications
  else vars.

(** Identity-input instance of the fold law, used for handles and name pairs. *)
Lemma fold_same_input : forall A (old_step : list (list SourceStored) -> A -> list (list SourceStored))
    (new_step : list (list Stored) -> A -> list (list Stored)),
  (forall rows input, map_rows materialize (new_step rows input) = old_step (map_rows materialize rows) input) ->
  forall inputs rows, map_rows materialize (fold_left new_step inputs rows) =
    fold_left old_step inputs (map_rows materialize rows).
Proof.
  intros A old_step new_step H inputs; induction inputs; intros rows; [reflexivity|].
  change (map_rows materialize (fold_left new_step inputs (new_step rows a)) =
    fold_left old_step inputs (old_step (map_rows materialize rows) a)).
  now rewrite IHinputs, H.
Qed.

Theorem complete_ordered_driver_materialization : forall declarations users has_binders initial,
  map_rows materialize (view_driver (map project_category declarations) users has_binders initial) =
    source_driver declarations users has_binders (map_rows materialize initial).
Proof.
  intros. unfold view_driver, source_driver, source_generated_phases.
  rewrite nondata_names_preserved. destruct has_binders.
  all: repeat rewrite (fold_same_input source_lam_step view_lam_step lam_step_materializes).
  all: repeat rewrite (fold_same_input source_pair_step view_pair_step pair_step_materializes).
  all: rewrite (fold_projection project_category (map_rows materialize) source_var_step view_var_step var_step_materializes).
  all: rewrite (fold_projection project_category (map_rows materialize) source_collection_step view_collection_step collection_step_materializes).
  all: rewrite (fold_projection project_category (map_rows materialize) source_native_step view_native_step native_step_materializes).
  all: now rewrite (fold_same_input source_user_step view_user_step user_step_materializes).
Qed.

Lemma map_empty_rows : forall A B (f : A -> B) count,
  map_rows f (repeat [] count) = repeat [] count.
Proof.
  intros A B f count; induction count; [reflexivity|].
  change ([] :: map_rows f (repeat [] count) = [] :: repeat [] count).
  f_equal. exact IHcount.
Qed.

(** Exact original start: one empty bucket per parse-category entry. No
    idempotence hypothesis about normalize, even on arbitrary user payloads. *)
Theorem original_empty_start_ordered_materialization : forall declarations users binders,
  map_rows materialize
    (view_driver (map project_category declarations) users binders
      (repeat [] (List.length categories))) =
  original_source_driver declarations users binders
    (repeat [] (List.length categories)).
Proof.
  intros. rewrite complete_ordered_driver_materialization.
  rewrite original_normalization_schedule_payloads.
  now rewrite !map_empty_rows.
Qed.

Theorem appended_synthetic_var_is_seen_by_later_visits : forall row home l,
  existsb source_first_var (row ++ [Generated (raw_var home l)])%list = true.
Proof. intros; rewrite existsb_app; cbn. apply orb_true_r. Qed.

Theorem original_payload_identity : forall handle,
  materialize (OriginalHandle handle) = Original (normalize (original_user handle)).
Proof. reflexivity. Qed.

End Pipeline.

(** Eager insertion boundary. Events are admitted pushes in execution order,
    NOT a flattening of the final category buckets. The phase/Var lemmas above
    justify successful ordered outputs; Rust must retain their gates and emit
    each event at the original push site. In particular, current-list Var scans
    use the actual homogeneous payloads, not a deferred recipe side channel. *)
Definition deferred_push (rows : list (list Recipe)) (event : nat * Recipe) :=
  push_at (fst event) (snd event) rows.
Definition eager_push (rows : list (list RawRule)) (event : nat * Recipe) :=
  push_at (fst event) (materialize_recipe (snd event)) rows.

Theorem eager_ordered_output : forall events rows,
  map_rows materialize_recipe (fold_left deferred_push events rows) =
  fold_left eager_push events (map_rows materialize_recipe rows).
Proof.
  induction events as [|[index rule] rest IH]; intros rows; [reflexivity|].
  change (map_rows materialize_recipe
    (fold_left deferred_push rest (push_at index rule rows)) =
    fold_left eager_push rest
      (push_at index (materialize_recipe rule) (map_rows materialize_recipe rows))).
  rewrite IH, map_rows_push. reflexivity.
Qed.

(** A callback error represents an ordered constructor/name-validation failure,
    not allocation failure or Rust unwinding/recovery. A successful callback
    publishes one payload before the next event; a failed callback publishes
    nothing and does not invoke the suffix. The partial rows are a specification
    observation, not a promise that Rust exposes a failed builder's local state.

    Callback correspondence below is an explicit premise. It does NOT assert
    that arbitrary materializers have the original constructor's failure order.
    Static source correspondence retains native/Var helper calls before category
    validation, and checks category/domain identifiers before derived labels.
    proc-macro2 1.0.107 src/fallback.rs:841-875 accepts '_' or XID_Start initially
    and XID_Continue afterwards. The accepted first characters also continue an
    identifier, so fixed ASCII Apply/MApply prefixes preserve a valid nonraw
    domain name; raw r# spellings fail the earlier domain check at '#'. Thus
    moving the already-infallible MApply label check past Apply's push cannot
    change the first invalid-name failure. Unicode tables and allocator behavior
    are not verified here. Exact helper gates and reversed-category failure
    regressions remain mandatory source-correspondence checks. *)
Section PartialInsertion.
Context {Payload Error : Type}.
Inductive EmissionOutcome :=
  | Emitted (rows : list (list Payload)) (attempted : list (nat * RawRule))
  | EmissionFailed (error : Error) (rows : list (list Payload))
      (attempted : list (nat * RawRule)).
Definition prepend_attempt (event : nat * RawRule) (outcome : EmissionOutcome) :=
  match outcome with
  | Emitted rows trace => Emitted rows (event :: trace)
  | EmissionFailed error rows trace => EmissionFailed error rows (event :: trace)
  end.
Fixpoint run_raw_emissions (callback : RawRule -> Payload + Error)
    (events : list (nat * RawRule)) (rows : list (list Payload)) :=
  match events with
  | [] => Emitted rows []
  | (index, rule) :: rest => match callback rule with
      | inl payload => prepend_attempt (index, rule)
          (run_raw_emissions callback rest (push_at index payload rows))
      | inr error => EmissionFailed error rows [(index, rule)]
      end
  end.
Fixpoint run_recipe_emissions (callback : Recipe -> Payload + Error)
    (events : list (nat * Recipe)) (rows : list (list Payload)) :=
  match events with
  | [] => Emitted rows []
  | (index, rule) :: rest => match callback rule with
      | inl payload => prepend_attempt (index, materialize_recipe rule)
          (run_recipe_emissions callback rest (push_at index payload rows))
      | inr error => EmissionFailed error rows [(index, materialize_recipe rule)]
      end
  end.
Definition materialize_event (event : nat * Recipe) :=
  (fst event, materialize_recipe (snd event)).

Theorem ordered_partial_callback_correspondence : forall raw_callback recipe_callback,
  (forall rule, recipe_callback rule = raw_callback (materialize_recipe rule)) ->
  forall events rows,
  run_recipe_emissions recipe_callback events rows =
  run_raw_emissions raw_callback (map materialize_event events) rows.
Proof.
  intros raw_callback recipe_callback H events.
  induction events as [|[index rule] rest IH]; intros rows; [reflexivity|].
  cbn [run_recipe_emissions run_raw_emissions map materialize_event fst snd].
  rewrite H. destruct (raw_callback (materialize_recipe rule)); [now rewrite IH|reflexivity].
Qed.

Theorem first_failed_callback_stops_suffix : forall callback index rule error suffix rows,
  callback rule = inr error ->
  run_recipe_emissions callback ((index, rule) :: suffix) rows =
  EmissionFailed error rows [(index, materialize_recipe rule)].
Proof. intros; cbn [run_recipe_emissions]; now rewrite H. Qed.

(** This prefix law also covers a failure after arbitrarily many successful
    earlier pushes, without inspecting or executing any later event. *)
Theorem successful_prefix_then_first_failure : forall callback prefix rows ready trace,
  run_recipe_emissions callback prefix rows = Emitted ready trace ->
  forall index rule error suffix,
  callback rule = inr error ->
  run_recipe_emissions callback (prefix ++ (index, rule) :: suffix)%list rows =
  EmissionFailed error ready
    (trace ++ [(index, materialize_recipe rule)])%list.
Proof.
  intros callback prefix; induction prefix as [|[i r] rest IH];
    intros rows ready trace H index rule error suffix Herror.
  - cbn [run_recipe_emissions] in H. inversion H; subst.
    apply first_failed_callback_stops_suffix. exact Herror.
  - cbn [run_recipe_emissions] in H.
    destruct (callback r) as [payload|failure] eqn:Hcallback; [|discriminate].
    destruct (run_recipe_emissions callback rest (push_at i payload rows))
      as [rest_rows rest_trace|failure rest_rows rest_trace] eqn:Hrest;
      cbn [prepend_attempt] in H; [|discriminate].
    inversion H; subst.
    cbn [List.app run_recipe_emissions]. rewrite Hcallback.
    rewrite (IH _ _ _ Hrest _ _ _ _ Herror). reflexivity.
Qed.
End PartialInsertion.

Print Assumptions all_constructor_fields_materialize_exactly.
Print Assumptions later_duplicate_slot_wins.
Print Assumptions fold_projection.
Print Assumptions first_var_materialization.
Print Assumptions var_step_materializes.
Print Assumptions complete_ordered_driver_materialization.
Print Assumptions group_then_normalize_payloads.
Print Assumptions original_empty_start_ordered_materialization.
Print Assumptions original_payload_identity.
Print Assumptions eager_ordered_output.
Print Assumptions ordered_partial_callback_correspondence.
Print Assumptions first_failed_callback_stops_suffix.
Print Assumptions successful_prefix_then_first_failure.
End SyntheticRuleProjection.
