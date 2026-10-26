(** Source instantiation and the existing TermConstructionTask machine.

    The four task forms below are the source-level view of Evaluate,
    FinishApply, FinishMapSources, and FinishMapBodies in
    dovetail-runtime/src/semantic_transition_kernel.rs.  Lists of tasks are
    written in POP order; the Rust vector pushes their reverse.  Values are
    the semantic projection of canonical e-class IDs, not e-class addresses.
    Indexed construction environments are related to this view separately.

    This is a correspondence proof, not another production evaluator.  Its
    big-step relation uses AuthoredSourceExecution's rich source arena,
    including exact typed literal payloads, multi-source Map and Product.
    The older erased ExecutableTheoryImage representation is not substituted
    for that arena.  Structural Substitution construction does not perform
    beta reduction; source equations and execution establish those steps.

    The remaining physical contracts are deliberately local: exact-operator
    splice readback, mode-aware collection element readback, product readback,
    canonicalization of a specified child vector, and insertion of one
    specified node.  They take no source root, environment or derivation and
    cannot assert the desired whole-builder theorem.  Their Rust correctness,
    the compiler's exact rich-source projection, and stability of semantic
    e-class projections are not proved here.  AuthoredSourceImage separately
    proves the resolved term-arena check supplies these SourceApply/Slot/Map
    cases; raw-name resolution and physical Rust/model views remain explicit.
    No termination, allocation,
    budget-completeness or whole e-graph refinement claim is made.
*)

From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import AuthoredSourceExecution CollectionComprehension.
Import ListNotations.

Module AuthoredTermConstruction.
Module S := AuthoredSourceExecution.
Module Core := S.Core.
Module K := S.K.
Module Canon := S.Canon.
Module C := CollectionComprehension.

(** A projection of the already checked runtime sort table, retaining exactly
    the distinctions inspected by construction.  OtherSort includes syntax,
    function and opaque sorts; their typing is not rechecked by this model. *)
Inductive ConstructionSort :=
| OtherSort
| CollectionSort (kind : K.RuntimeCollectionKind)
    (key : option Core.SortId) (element : Core.SortId)
| ProductSort (factors : list Core.SortId).
Definition SortTable := list ConstructionSort.

(** Operator identity retains the literal's carrier sort and full payload.
    Substitution also retains the abstraction's function sort. *)
Inductive Operator :=
| ConstructorOperator (constructor : Core.ConstructorId)
| AbstractionOperator (sort : Core.SortId)
| SubstitutionOperator (result function : Core.SortId)
| CollectionOperator (sort element : Core.SortId) (kind : K.RuntimeCollectionKind)
| ProductOperator (sort : Core.SortId)
| LiteralOperator (sort : Core.SortId) (literal : S.Literal).

Record ApplyShape := {
  apply_operator : Operator;
  apply_arguments : list Core.TermId;
  apply_slots : list Core.VariableId;
  apply_remainder : option Core.VariableId;
  apply_mode : option Canon.PathMapMode
}.

Definition shape operator arguments slots remainder mode :=
  {| apply_operator := operator; apply_arguments := arguments;
     apply_slots := slots; apply_remainder := remainder; apply_mode := mode |}.

(** The cases of compile_term_nodes, not a recursively copied compiler.  A
    source node and its resolved table references determine every field. *)
Inductive SourceApply (sorts : SortTable) (arena : S.Arena) :
    Core.TermId -> ApplyShape -> Prop :=
| source_constructor : forall root sort constructor arguments,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceConstructor constructor arguments |} ->
    SourceApply sorts arena root
      (shape (ConstructorOperator constructor) arguments [] None None)
| source_abstraction : forall root sort binder body,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceAbstraction binder body |} ->
    SourceApply sorts arena root
      (shape (AbstractionOperator sort) [body] [binder] None None)
| source_substitution : forall root sort abstraction argument function_node,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceSubstitution abstraction argument |} ->
    nth_error (S.terms arena) abstraction = Some function_node ->
    SourceApply sorts arena root
      (shape (SubstitutionOperator sort (S.node_sort function_node))
        [abstraction; argument] [] None None)
| source_collection : forall root sort kind key element arguments remainder mode,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceCollection arguments remainder mode |} ->
    nth_error sorts sort = Some (CollectionSort kind key element) ->
    SourceApply sorts arena root
      (shape (CollectionOperator sort element kind) arguments [] remainder mode)
| source_product : forall root sort factors,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceProduct factors |} ->
    SourceApply sorts arena root (shape (ProductOperator sort) factors [] None None)
| source_literal : forall root sort literal,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceLiteral literal |} ->
    SourceApply sorts arena root (shape (LiteralOperator sort literal) [] [] None None).

(** Both meanings and observations have this LOCAL signature.  For splice,
    children include physical PathMap mode markers: append_collection_remainder
    copies them, and canonicalize_pathmap_children subsequently reconciles
    them.  Element readback instead returns payload elements and the effective
    element sort (the key sort in PathMap set mode). *)
Record PhysicalOperations := {
  splice_children : Operator -> S.Value -> list S.Value -> Prop;
  collection_elements : Core.SortId -> S.Value -> Core.SortId -> list S.Value -> Prop;
  product_factors : Core.SortId -> S.Value -> list S.Value -> Prop;
  canonical_children : Operator -> option Canon.PathMapMode ->
    list S.Value -> list S.Value -> Prop;
  insert_node : Operator -> list S.Value -> S.Value -> Prop
}.

Record LocalPhysicalRefinement (meaning observed : PhysicalOperations) : Prop := {
  splice_refines : forall operator value children,
    splice_children observed operator value children ->
    splice_children meaning operator value children;
  elements_refine : forall sort value element children,
    collection_elements observed sort value element children ->
    collection_elements meaning sort value element children;
  product_refines : forall sort value children,
    product_factors observed sort value children -> product_factors meaning sort value children;
  canonical_refines : forall operator mode before after,
    canonical_children observed operator mode before after ->
    canonical_children meaning operator mode before after;
  insertion_refines : forall operator children value,
    insert_node observed operator children value -> insert_node meaning operator children value
}.

Definition is_collection operator :=
  match operator with CollectionOperator _ _ _ => true | _ => false end.

Definition is_map_root arena root :=
  match nth_error (S.terms arena) root with
  | Some {| S.node_form := S.SourceMap _ _ _ |} => true
  | _ => false
  end.

Inductive ArgumentSegments (operations : PhysicalOperations) (arena : S.Arena)
    (operator : Operator) : list Core.TermId -> list S.Value ->
      list (C.CollectionSegment S.Value) -> Prop :=
| segments_nil : ArgumentSegments operations arena operator [] [] []
| segments_element : forall root value roots values segments,
    is_collection operator && is_map_root arena root = false ->
    ArgumentSegments operations arena operator roots values segments ->
    ArgumentSegments operations arena operator (root :: roots) (value :: values)
      (C.SegmentElement value :: segments)
| segments_splice : forall root value roots values children segments,
    is_collection operator && is_map_root arena root = true ->
    splice_children operations operator value children ->
    ArgumentSegments operations arena operator roots values segments ->
    ArgumentSegments operations arena operator (root :: roots) (value :: values)
      (C.SegmentSplice children :: segments).

Inductive RemainderChildren (operations : PhysicalOperations) (activation : S.Activation)
    (environment : S.Environment) (operator : Operator) :
      option Core.VariableId -> list S.Value -> Prop :=
| remainder_absent : RemainderChildren operations activation environment operator None []
| remainder_present : forall variable value children,
    S.lookup activation variable environment = Some value ->
    splice_children operations operator value children ->
    RemainderChildren operations activation environment operator (Some variable) children.

Inductive BuildApply (operations : PhysicalOperations) (arena : S.Arena)
    (activation : S.Activation) (environment : S.Environment) (application : ApplyShape) :
      list S.Value -> S.Value -> Prop :=
| build_apply : forall arguments slots segments remainder canonical output,
    S.ReadSlots activation environment (apply_slots application) slots ->
    ArgumentSegments operations arena (apply_operator application)
      (apply_arguments application) arguments segments ->
    RemainderChildren operations activation environment (apply_operator application)
      (apply_remainder application) remainder ->
    canonical_children operations (apply_operator application) (apply_mode application)
      (slots ++ C.flatten_segments segments ++ remainder) canonical ->
    insert_node operations (apply_operator application) canonical output ->
    BuildApply operations arena activation environment application arguments output.

(** Construction has lexical overlays, not fresh-output binding.  The first
    matching row binding shadows its parent; no binding is exported to it. *)
Definition Bindings := list (Core.VariableId * S.Value).
Definition overlay activation (bindings : Bindings) environment : S.Environment :=
  map (fun binding => (S.slot activation (fst binding), snd binding)) bindings ++ environment.

Record ConstructionEnvironment := {
  environment_parent : option nat;
  environment_bindings : Bindings
}.

Inductive EnvironmentAt (activation : S.Activation) (outer : S.Environment)
    (heap : list ConstructionEnvironment) : option nat -> S.Environment -> Prop :=
| environment_outer : EnvironmentAt activation outer heap None outer
| environment_frame : forall index frame parent_environment,
    nth_error heap index = Some frame ->
    (match environment_parent frame with None => True | Some parent => parent < index end) ->
    EnvironmentAt activation outer heap (environment_parent frame) parent_environment ->
    EnvironmentAt activation outer heap (Some index)
      (overlay activation (environment_bindings frame) parent_environment).

Lemma environment_survives_heap_extension : forall activation outer heap pointer environment,
    EnvironmentAt activation outer heap pointer environment -> forall extra,
    EnvironmentAt activation outer (heap ++ extra) pointer environment.
Proof.
  intros activation outer heap pointer environment H. induction H; intros extra.
  - constructor.
  - econstructor; eauto. rewrite nth_error_app1; [exact H|].
    apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma allocated_environment_has_exact_parent : forall activation outer heap pointer environment bindings,
    EnvironmentAt activation outer heap pointer environment ->
    (match pointer with None => True | Some index => index < length heap end) ->
    EnvironmentAt activation outer
      (heap ++ [{| environment_parent := pointer; environment_bindings := bindings |}])
      (Some (length heap)) (overlay activation bindings environment).
Proof.
  intros. eapply environment_frame with
    (frame := {| environment_parent := pointer; environment_bindings := bindings |})
    (parent_environment := environment).
  - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - assumption.
  - now apply environment_survives_heap_extension.
Qed.

Lemma overlay_first_binding : forall activation variable value rest environment,
    S.lookup activation variable (overlay activation ((variable, value) :: rest) environment) = Some value.
Proof.
  intros. change
    ((if K.scoped_variable_eqb (S.slot activation variable) (S.slot activation variable)
      then Some value else S.lookup activation variable (overlay activation rest environment)) = Some value).
  rewrite (proj2 (K.scoped_variable_eqb_spec (S.slot activation variable)
    (S.slot activation variable)) eq_refl). reflexivity.
Qed.

Lemma overlay_unbound_lookup : forall activation bindings environment variable,
    ~ In variable (map fst bindings) ->
    S.lookup activation variable (overlay activation bindings environment) =
    S.lookup activation variable environment.
Proof.
  intros activation bindings. induction bindings as [|[bound value] rest IH];
    intros environment variable Hfresh; [reflexivity|].
  change ((if K.scoped_variable_eqb (S.slot activation variable) (S.slot activation bound)
    then Some value else S.lookup activation variable (overlay activation rest environment)) =
    S.lookup activation variable environment).
  destruct (K.scoped_variable_eqb (S.slot activation variable) (S.slot activation bound)) eqn:Heq.
  - apply K.scoped_variable_eqb_spec in Heq. unfold S.slot in Heq.
    inversion Heq. subst. exfalso. apply Hfresh. now left.
  - apply IH. intro Hin. apply Hfresh. now right.
Qed.

Lemma lookup_scoped_append : forall variable prefix suffix,
    K.lookup_scoped variable (prefix ++ suffix) =
    match K.lookup_scoped variable prefix with
    | Some value => Some value
    | None => K.lookup_scoped variable suffix
    end.
Proof.
  intros variable prefix. induction prefix as [|[bound value] rest IH]; intros suffix.
  - reflexivity.
  - cbn [app K.lookup_scoped]. destruct (K.scoped_variable_eqb variable bound); auto.
Qed.

(** A relational observation of the indexed construction_lookup loop.  The
    local search is the existing scoped lookup on just this frame's bindings;
    no whole term-instantiation fact is hidden in environment resolution. *)
Inductive IndexedLookup (activation : S.Activation) (outer : S.Environment)
    (heap : list ConstructionEnvironment) (variable : Core.VariableId) :
      option nat -> S.Value -> Prop :=
| indexed_outer : forall value,
    S.lookup activation variable outer = Some value ->
    IndexedLookup activation outer heap variable None value
| indexed_hit : forall index frame value,
    nth_error heap index = Some frame ->
    S.lookup activation variable (overlay activation (environment_bindings frame) []) = Some value ->
    IndexedLookup activation outer heap variable (Some index) value
| indexed_parent : forall index frame value,
    nth_error heap index = Some frame ->
    S.lookup activation variable (overlay activation (environment_bindings frame) []) = None ->
    (match environment_parent frame with None => True | Some parent => parent < index end) ->
    IndexedLookup activation outer heap variable (environment_parent frame) value ->
    IndexedLookup activation outer heap variable (Some index) value.

Theorem indexed_lookup_has_exact_overlay_meaning : forall activation outer heap pointer environment,
    EnvironmentAt activation outer heap pointer environment -> forall variable value,
    IndexedLookup activation outer heap variable pointer value ->
    S.lookup activation variable environment = Some value.
Proof.
  intros activation outer heap pointer environment Henv. induction Henv;
    intros variable value Hlookup; inversion Hlookup; subst.
  - assumption.
  - match goal with Hleft : nth_error heap index = Some frame,
                    Hright : nth_error heap index = Some ?other |- _ =>
      assert (frame = other) by congruence; subst other
    end.
    unfold S.lookup, overlay in *. rewrite app_nil_r in *.
    rewrite lookup_scoped_append.
    match goal with Hlocal : K.lookup_scoped ?needle ?bindings = Some value
      |- context [K.lookup_scoped ?needle ?bindings] => now rewrite Hlocal end.
  - match goal with Hleft : nth_error heap index = Some frame,
                    Hright : nth_error heap index = Some ?other |- _ =>
      assert (frame = other) by congruence; subst other
    end.
    unfold S.lookup, overlay in *. rewrite app_nil_r in *.
    rewrite lookup_scoped_append.
    match goal with Hlocal : K.lookup_scoped ?needle ?bindings = None
      |- context [K.lookup_scoped ?needle ?bindings] => rewrite Hlocal end.
    apply IHHenv. assumption.
Qed.

Definition ParameterSorts arena parameters parameter_sorts :=
  Forall2 (fun parameter sort => exists declaration,
    nth_error (S.variables arena) parameter = Some declaration /\
    Core.variable_role declaration = Core.BoundVariable /\
    Core.variable_sort declaration = sort) parameters parameter_sorts.

Definition Column := (Core.SortId * list S.Value)%type.

Inductive SourceColumns (sorts : SortTable) (operations : PhysicalOperations)
    (arena : S.Arena) (multiple : bool) :
      list Core.TermId -> list S.Value -> list Column -> Prop :=
| columns_nil : SourceColumns sorts operations arena multiple [] [] []
| columns_cons : forall root value roots values node kind key declared_element element children columns,
    nth_error (S.terms arena) root = Some node ->
    nth_error sorts (S.node_sort node) = Some (CollectionSort kind key declared_element) ->
    (multiple = true -> kind = K.AdmissionList) ->
    collection_elements operations (S.node_sort node) value element children ->
    SourceColumns sorts operations arena multiple roots values columns ->
    SourceColumns sorts operations arena multiple (root :: roots) (value :: values)
      ((element, children) :: columns).

(** Exact zip is reused from CollectionComprehension.  In particular, neither
    unequal source lengths nor unequal parameter/factor widths are truncated. *)
Inductive RowBindings (sorts : SortTable) (operations : PhysicalOperations)
    (parameters : list Core.VariableId) (parameter_sorts : list Core.SortId)
    (index : nat) : list Column -> Bindings -> Prop :=
| row_scalar : forall parameter element elements value declaration,
    parameters = [parameter] -> parameter_sorts = [element] ->
    nth_error sorts element = Some declaration ->
    (forall factors, declaration <> ProductSort factors) ->
    nth_error elements index = Some value ->
    RowBindings sorts operations parameters parameter_sorts index
      [(element, elements)] [(parameter, value)]
| row_product : forall element elements value factors bindings,
    nth_error sorts element = Some (ProductSort parameter_sorts) ->
    nth_error elements index = Some value ->
    product_factors operations element value factors ->
    C.zip_exact parameters factors = Some bindings ->
    RowBindings sorts operations parameters parameter_sorts index [(element, elements)] bindings
| row_multiple : forall columns values bindings,
    1 < length columns -> map fst columns = parameter_sorts ->
    Forall2 (fun column value => nth_error (snd column) index = Some value) columns values ->
    C.zip_exact parameters values = Some bindings ->
    RowBindings sorts operations parameters parameter_sorts index columns bindings.

Inductive MapRows (sorts : SortTable) (operations : PhysicalOperations) (arena : S.Arena)
    (sources : list Core.TermId) (parameters : list Core.VariableId) :
      list S.Value -> list Bindings -> Prop :=
| map_rows : forall values parameter_sorts first remaining count rows,
    sources <> [] -> parameters <> [] -> ParameterSorts arena parameters parameter_sorts ->
    SourceColumns sorts operations arena (1 <? length sources) sources values (first :: remaining) ->
    length (snd first) = count ->
    Forall (fun column => length (snd column) = count) remaining ->
    Forall2 (fun index bindings =>
      RowBindings sorts operations parameters parameter_sorts index (first :: remaining) bindings)
      (seq 0 count) rows ->
    MapRows sorts operations arena sources parameters values rows.

Definition row_environments activation environment rows :=
  map (fun bindings => overlay activation bindings environment) rows.

Definition construction_mode kind :=
  match kind with K.AdmissionPathMap => Some Canon.PathMapMapMode | _ => None end.

Inductive BuildMap (sorts : SortTable) (operations : PhysicalOperations)
    (target : Core.SortId) : list S.Value -> S.Value -> Prop :=
| build_map : forall kind key element bodies canonical output,
    nth_error sorts target = Some (CollectionSort kind key element) ->
    canonical_children operations (CollectionOperator target element kind)
      (construction_mode kind) bodies canonical ->
    insert_node operations (CollectionOperator target element kind) canonical output ->
    BuildMap sorts operations target bodies output.

Definition Request := (Core.TermId * S.Environment)%type.
Definition requests environment roots : list Request := map (fun root => (root, environment)) roots.
Definition body_requests body environments : list Request := map (fun environment => (body, environment)) environments.

(** Source-level big-step instantiation is independent of task stacks.  All
    child roots are evaluated in the same parent environment.  Only Map bodies
    receive row overlays, each over the SAME saved parent environment. *)
Inductive SourceInstantiation (sorts : SortTable) (operations : PhysicalOperations)
    (arena : S.Arena) (activation : S.Activation) :
      Core.TermId -> S.Environment -> S.Value -> Prop :=
| instantiate_variable : forall root sort variable environment value,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceVariable variable |} ->
    S.lookup activation variable environment = Some value ->
    SourceInstantiation sorts operations arena activation root environment value
| instantiate_apply : forall root environment application arguments output,
    SourceApply sorts arena root application ->
    Forall2 (fun request value => SourceInstantiation sorts operations arena activation
      (fst request) (snd request) value) (requests environment (apply_arguments application)) arguments ->
    BuildApply operations arena activation environment application arguments output ->
    SourceInstantiation sorts operations arena activation root environment output
| instantiate_map : forall root environment target sources parameters body source_values rows body_values output,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := target; S.node_form := S.SourceMap sources parameters body |} ->
    Forall2 (fun request value => SourceInstantiation sorts operations arena activation
      (fst request) (snd request) value) (requests environment sources) source_values ->
    MapRows sorts operations arena sources parameters source_values rows ->
    Forall2 (fun request value => SourceInstantiation sorts operations arena activation
      (fst request) (snd request) value)
      (body_requests body (row_environments activation environment rows)) body_values ->
    BuildMap sorts operations target body_values output ->
    SourceInstantiation sorts operations arena activation root environment output.

Definition InstantiateRequests sorts operations arena activation :=
  Forall2 (fun request value => SourceInstantiation sorts operations arena activation
    (fst request) (snd request) value).

(** The source-level view expands an environment pointer using EnvironmentAt.
    FinishMapBodies intentionally stores neither a source root nor a row
    environment: the continuation invariant remembers their provenance. *)
Inductive Task :=
| Evaluate (root : Core.TermId) (environment : S.Environment)
| FinishApply (application : ApplyShape) (environment : S.Environment) (value_base : nat)
| FinishMapSources (target : Core.SortId) (sources : list Core.TermId)
    (parameters : list Core.VariableId) (body : Core.TermId)
    (environment : S.Environment) (value_base : nat)
| FinishMapBodies (target : Core.SortId) (row_count value_base : nat).

Definition evaluate_requests := map (fun request : Request => Evaluate (fst request) (snd request)).

(** This denotation expresses each pending continuation's stack contract, not
    an executable replay checker.  The exact base and suffix widths are those
    checked by take_construction_values. *)
Inductive TaskMeaning (sorts : SortTable) (operations : PhysicalOperations)
    (arena : S.Arena) (activation : S.Activation) : Task -> list S.Value -> list S.Value -> Prop :=
| meaning_evaluate : forall root environment prefix value,
    SourceInstantiation sorts operations arena activation root environment value ->
    TaskMeaning sorts operations arena activation (Evaluate root environment) prefix (prefix ++ [value])
| meaning_apply : forall application environment base prefix arguments output,
    length prefix = base -> length arguments = length (apply_arguments application) ->
    BuildApply operations arena activation environment application arguments output ->
    TaskMeaning sorts operations arena activation (FinishApply application environment base)
      (prefix ++ arguments) (prefix ++ [output])
| meaning_map_sources : forall target sources parameters body environment base prefix values rows bodies output,
    length prefix = base -> length values = length sources ->
    MapRows sorts operations arena sources parameters values rows ->
    InstantiateRequests sorts operations arena activation
      (body_requests body (row_environments activation environment rows)) bodies ->
    BuildMap sorts operations target bodies output ->
    TaskMeaning sorts operations arena activation
      (FinishMapSources target sources parameters body environment base)
      (prefix ++ values) (prefix ++ [output])
| meaning_map_bodies : forall target count base prefix bodies output,
    length prefix = base -> length bodies = count ->
    BuildMap sorts operations target bodies output ->
    TaskMeaning sorts operations arena activation (FinishMapBodies target count base)
      (prefix ++ bodies) (prefix ++ [output]).

Inductive TasksMeaning (sorts : SortTable) (operations : PhysicalOperations)
    (arena : S.Arena) (activation : S.Activation) : list Task -> list S.Value -> list S.Value -> Prop :=
| meaning_done : forall values, TasksMeaning sorts operations arena activation [] values values
| meaning_next : forall task rest values middle final,
    TaskMeaning sorts operations arena activation task values middle ->
    TasksMeaning sorts operations arena activation rest middle final ->
    TasksMeaning sorts operations arena activation (task :: rest) values final.

Inductive TaskStep (sorts : SortTable) (observed : PhysicalOperations)
    (arena : S.Arena) (activation : S.Activation) :
      list Task -> list S.Value -> list Task -> list S.Value -> Prop :=
| step_variable : forall root sort variable environment rest values value,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := sort; S.node_form := S.SourceVariable variable |} ->
    S.lookup activation variable environment = Some value ->
    TaskStep sorts observed arena activation (Evaluate root environment :: rest) values
      rest (values ++ [value])
| step_expand_apply : forall root environment rest values application,
    SourceApply sorts arena root application ->
    TaskStep sorts observed arena activation (Evaluate root environment :: rest) values
      (evaluate_requests (requests environment (apply_arguments application)) ++
        FinishApply application environment (length values) :: rest) values
| step_expand_map : forall root environment rest values target sources parameters body kind key element,
    nth_error (S.terms arena) root = Some
      {| S.node_sort := target; S.node_form := S.SourceMap sources parameters body |} ->
    sources <> [] -> parameters <> [] ->
    nth_error sorts target = Some (CollectionSort kind key element) ->
    TaskStep sorts observed arena activation (Evaluate root environment :: rest) values
      (evaluate_requests (requests environment sources) ++
        FinishMapSources target sources parameters body environment (length values) :: rest) values
| step_finish_apply : forall application environment base rest prefix arguments output,
    length prefix = base -> length arguments = length (apply_arguments application) ->
    BuildApply observed arena activation environment application arguments output ->
    TaskStep sorts observed arena activation (FinishApply application environment base :: rest)
      (prefix ++ arguments) rest (prefix ++ [output])
| step_map_sources : forall target sources parameters body environment base rest prefix values rows,
    length prefix = base -> length values = length sources ->
    MapRows sorts observed arena sources parameters values rows ->
    TaskStep sorts observed arena activation
      (FinishMapSources target sources parameters body environment base :: rest) (prefix ++ values)
      (evaluate_requests (body_requests body (row_environments activation environment rows)) ++
        FinishMapBodies target (length rows) (length prefix) :: rest) prefix
| step_map_bodies : forall target count base rest prefix bodies output,
    length prefix = base -> length bodies = count ->
    BuildMap sorts observed target bodies output ->
    TaskStep sorts observed arena activation (FinishMapBodies target count base :: rest)
      (prefix ++ bodies) rest (prefix ++ [output]).

Inductive TaskRun sorts observed arena activation :
    list Task -> list S.Value -> list Task -> list S.Value -> Prop :=
| run_refl : forall tasks values, TaskRun sorts observed arena activation tasks values tasks values
| run_step : forall tasks values next next_values final result,
    TaskStep sorts observed arena activation tasks values next next_values ->
    TaskRun sorts observed arena activation next next_values final result ->
    TaskRun sorts observed arena activation tasks values final result.

Section Refinement.
  Context (meaning observed : PhysicalOperations).
  Context (refinement : LocalPhysicalRefinement meaning observed).

  Lemma argument_segments_refine : forall arena operator roots values segments,
      ArgumentSegments observed arena operator roots values segments ->
      ArgumentSegments meaning arena operator roots values segments.
  Proof.
    intros arena operator roots values segments H. induction H.
    - constructor.
    - econstructor; eauto.
    - eapply segments_splice; eauto using splice_refines.
  Qed.

  Lemma remainder_children_refine : forall activation environment operator remainder children,
      RemainderChildren observed activation environment operator remainder children ->
      RemainderChildren meaning activation environment operator remainder children.
  Proof.
    intros activation environment operator remainder children H. destruct H.
    - constructor.
    - econstructor; eauto using splice_refines.
  Qed.

  Lemma build_apply_refines : forall arena activation environment application arguments output,
      BuildApply observed arena activation environment application arguments output ->
      BuildApply meaning arena activation environment application arguments output.
  Proof.
    intros arena activation environment application arguments output H. destruct H.
    econstructor; eauto using argument_segments_refine, remainder_children_refine,
      canonical_refines, insertion_refines.
  Qed.

  Lemma source_columns_refine : forall sorts arena multiple sources values columns,
      SourceColumns sorts observed arena multiple sources values columns ->
      SourceColumns sorts meaning arena multiple sources values columns.
  Proof.
    intros sorts arena multiple sources values columns H. induction H.
    - constructor.
    - econstructor; eauto using elements_refine.
  Qed.

  Lemma row_bindings_refine : forall sorts parameters parameter_sorts index columns bindings,
      RowBindings sorts observed parameters parameter_sorts index columns bindings ->
      RowBindings sorts meaning parameters parameter_sorts index columns bindings.
  Proof.
    intros sorts parameters parameter_sorts index columns bindings H. destruct H.
    - eapply row_scalar; eauto.
    - eapply row_product; eauto using product_refines.
    - eapply row_multiple; eauto.
  Qed.

  Lemma map_rows_refine : forall sorts arena sources parameters values rows,
      MapRows sorts observed arena sources parameters values rows ->
      MapRows sorts meaning arena sources parameters values rows.
  Proof.
    intros sorts arena sources parameters values rows H. destruct H.
    econstructor; eauto using source_columns_refine.
    match goal with Hrows : Forall2 _ _ _ |- Forall2 _ _ _ =>
      induction Hrows; constructor; eauto using row_bindings_refine
    end.
  Qed.

  Lemma build_map_refines : forall sorts target bodies output,
      BuildMap sorts observed target bodies output -> BuildMap sorts meaning target bodies output.
  Proof.
    intros sorts target bodies output H. destruct H.
    econstructor; eauto using canonical_refines, insertion_refines.
  Qed.
End Refinement.

Lemma equal_length_prefixes : forall (A : Type) (prefix other suffix tail : list A),
    length prefix = length other -> prefix ++ suffix = other ++ tail ->
    prefix = other /\ suffix = tail.
Proof.
  intros A prefix. induction prefix as [|head prefix IH];
    intros [|other_head other] suffix tail Hlength Heq; simpl in *; try discriminate.
  - auto.
  - inversion Heq; subst. destruct (IH other suffix tail ltac:(lia) ltac:(assumption)); subst. auto.
Qed.

Lemma evaluated_requests_preserve_order : forall sorts operations arena activation pending prefix rest final,
    TasksMeaning sorts operations arena activation (evaluate_requests pending ++ rest) prefix final ->
    exists results,
      InstantiateRequests sorts operations arena activation pending results /\
      TasksMeaning sorts operations arena activation rest (prefix ++ results) final.
Proof.
  intros sorts operations arena activation pending. induction pending as [|[root environment] pending IH];
    intros prefix rest final Hmeaning.
  - exists []. split; [constructor|]. now rewrite app_nil_r.
  - simpl in Hmeaning. inversion Hmeaning; subst.
    match goal with Htask : TaskMeaning _ _ _ _ (Evaluate _ _) _ _ |- _ => inversion Htask; subst end.
    match goal with Htail : TasksMeaning _ _ _ _ (evaluate_requests pending ++ rest) _ _ |- _ =>
      destruct (IH _ _ _ Htail) as [results [Hresults Hrest]]
    end.
    eexists (_ :: results). split.
    + constructor; eauto.
    + rewrite <- app_assoc in Hrest. exact Hrest.
Qed.

Lemma instantiate_requests_length : forall sorts operations arena activation pending results,
    InstantiateRequests sorts operations arena activation pending results ->
    length pending = length results.
Proof. intros. now apply Forall2_length in H. Qed.

Theorem task_step_preserves_continuation_meaning :
    forall sorts meaning observed arena activation,
    LocalPhysicalRefinement meaning observed ->
    forall tasks values next next_values,
    TaskStep sorts observed arena activation tasks values next next_values ->
    forall final, TasksMeaning sorts meaning arena activation next next_values final ->
    TasksMeaning sorts meaning arena activation tasks values final.
Proof.
  intros sorts meaning observed arena activation Href tasks values next next_values Hstep.
  destruct Hstep; intros final Hnext.
  - econstructor; [constructor; econstructor; eauto|exact Hnext].
  - destruct (evaluated_requests_preserve_order _ _ _ _ _ _ _ _ Hnext)
      as [arguments [Harguments Hfinish]].
    inversion Hfinish; subst.
    match goal with Htask : TaskMeaning _ _ _ _ (FinishApply _ _ _) _ _ |- _ =>
      inversion Htask; subst
    end.
    match goal with Heq : values ++ arguments = ?prefix ++ ?results,
                    Hlen : length ?prefix = length values |- _ =>
      destruct (equal_length_prefixes _ values prefix arguments results (eq_sym Hlen) Heq); subst
    | Heq : ?prefix ++ ?results = values ++ arguments,
      Hlen : length ?prefix = length values |- _ =>
      destruct (equal_length_prefixes _ prefix values results arguments Hlen Heq); subst
    end.
    econstructor; [constructor; eapply instantiate_apply; eauto|eassumption].
  - destruct (evaluated_requests_preserve_order _ _ _ _ _ _ _ _ Hnext)
      as [source_values [Hsources Hfinish]].
    inversion Hfinish; subst.
    match goal with Htask : TaskMeaning _ _ _ _ (FinishMapSources _ _ _ _ _ _) _ _ |- _ =>
      inversion Htask; subst
    end.
    match goal with Heq : values ++ source_values = ?prefix ++ ?results,
                    Hlen : length ?prefix = length values |- _ =>
      destruct (equal_length_prefixes _ values prefix source_values results (eq_sym Hlen) Heq); subst
    | Heq : ?prefix ++ ?results = values ++ source_values,
      Hlen : length ?prefix = length values |- _ =>
      destruct (equal_length_prefixes _ prefix values results source_values Hlen Heq); subst
    end.
    econstructor; [constructor; eapply instantiate_map; eauto|eassumption].
  - econstructor; [econstructor; eauto using build_apply_refines|exact Hnext].
  - destruct (evaluated_requests_preserve_order _ _ _ _ _ _ _ _ Hnext)
      as [body_values [Hbodies Hfinish]].
    inversion Hfinish; subst.
    match goal with Htask : TaskMeaning _ _ _ _ (FinishMapBodies _ _ _) _ _ |- _ =>
      inversion Htask; subst
    end.
    match goal with Heq : prefix ++ body_values = ?other ++ ?results,
                    Hlen : length ?other = length prefix |- _ =>
      destruct (equal_length_prefixes _ prefix other body_values results (eq_sym Hlen) Heq); subst
    | Heq : ?other ++ ?results = prefix ++ body_values,
      Hlen : length ?other = length prefix |- _ =>
      destruct (equal_length_prefixes _ other prefix results body_values Hlen Heq); subst
    end.
    econstructor; [econstructor; eauto using map_rows_refine|eassumption].
  - econstructor; [econstructor; eauto using build_map_refines|exact Hnext].
Qed.

(** A state preserves the exact root AND saved environment when every semantic
    completion of its pending continuations yields that source instantiation.
    It quantifies over the whole task stack and accumulated value stack; it
    does not assert that any particular unfinished state terminates. *)
Definition ConstructionInvariant sorts meaning arena activation root environment tasks values :=
  forall output,
    TasksMeaning sorts meaning arena activation tasks values [output] ->
    SourceInstantiation sorts meaning arena activation root environment output.

Theorem initial_construction_invariant : forall sorts meaning arena activation root environment,
    ConstructionInvariant sorts meaning arena activation root environment [Evaluate root environment] [].
Proof.
  intros sorts meaning arena activation root environment output H.
  inversion H; subst.
  match goal with Htail : TasksMeaning _ _ _ _ [] _ _ |- _ => inversion Htail; subst end.
  match goal with Htask : TaskMeaning _ _ _ _ (Evaluate _ _) [] [_] |- _ => inversion Htask; subst end.
  assumption.
Qed.

Theorem construction_invariant_preserved : forall sorts meaning observed arena activation root environment,
    LocalPhysicalRefinement meaning observed ->
    forall tasks values next next_values,
    ConstructionInvariant sorts meaning arena activation root environment tasks values ->
    TaskStep sorts observed arena activation tasks values next next_values ->
    ConstructionInvariant sorts meaning arena activation root environment next next_values.
Proof.
  intros sorts meaning observed arena activation root environment Href tasks values next next_values Hinv Hstep
    output Hmeaning. apply Hinv.
  eapply task_step_preserves_continuation_meaning; eauto.
Qed.

Theorem finite_run_preserves_construction_invariant :
    forall sorts meaning observed arena activation root environment,
    LocalPhysicalRefinement meaning observed ->
    forall tasks values final result,
    TaskRun sorts observed arena activation tasks values final result ->
    ConstructionInvariant sorts meaning arena activation root environment tasks values ->
    ConstructionInvariant sorts meaning arena activation root environment final result.
Proof.
  intros sorts meaning observed arena activation root environment Href tasks values final result Hrun.
  induction Hrun; intros Hinv; [exact Hinv|]. apply IHHrun.
  eapply construction_invariant_preserved; eauto.
Qed.

Theorem successful_singleton_completion_instantiates_exact_root_environment :
    forall sorts meaning observed arena activation root environment output,
    LocalPhysicalRefinement meaning observed ->
    TaskRun sorts observed arena activation [Evaluate root environment] [] [] [output] ->
    SourceInstantiation sorts meaning arena activation root environment output.
Proof.
  intros sorts meaning observed arena activation root environment output Href Hrun.
  pose proof (finite_run_preserves_construction_invariant sorts meaning observed arena activation
    root environment Href _ _ _ _ Hrun
    (initial_construction_invariant sorts meaning arena activation root environment)) as Hinv.
  apply Hinv. constructor.
Qed.

(** Useful extracted invariants: exact row telescope, no zip truncation, and
    the binder-before-body order of ordinary abstraction construction. *)
Theorem row_bindings_retain_exact_parameters : forall sorts operations parameters parameter_sorts index columns bindings,
    RowBindings sorts operations parameters parameter_sorts index columns bindings ->
    map fst bindings = parameters.
Proof.
  intros sorts operations parameters parameter_sorts index columns bindings H. destruct H.
  - simpl. congruence.
  - now apply C.zip_exact_preserves_both_projections in H2 as [Hparameters _].
  - now apply C.zip_exact_preserves_both_projections in H2 as [Hparameters _].
Qed.

Theorem map_rows_retain_all_source_rows : forall sorts operations arena sources parameters values rows,
    MapRows sorts operations arena sources parameters values rows ->
    exists columns,
      SourceColumns sorts operations arena (1 <? length sources) sources values columns /\
      Forall (fun column => length (snd column) = length rows) columns.
Proof.
  intros sorts operations arena sources parameters values rows H. destruct H.
  match goal with Hr : Forall2 _ (seq 0 ?count) rows |- _ =>
    pose proof (Forall2_length Hr) as Hlength; rewrite seq_length in Hlength
  end.
  eexists. split; [eassumption|]. rewrite <- Hlength. constructor; assumption.
Qed.

Theorem abstraction_slots_precede_body : forall operations arena activation environment sort binder body body_value output,
    BuildApply operations arena activation environment
      (shape (AbstractionOperator sort) [body] [binder] None None) [body_value] output ->
    exists binder_value canonical,
      S.lookup activation binder environment = Some binder_value /\
      canonical_children operations (AbstractionOperator sort) None [binder_value; body_value] canonical /\
      insert_node operations (AbstractionOperator sort) canonical output.
Proof.
  intros operations arena activation environment sort binder body body_value output H.
  inversion H; subst. simpl in *.
  match goal with Hslots : S.ReadSlots _ _ [binder] _ |- _ => inversion Hslots; subst end.
  match goal with Hslots : S.ReadSlots _ _ [] _ |- _ => inversion Hslots; subst end.
  match goal with Hsegments : ArgumentSegments _ _ _ [body] [body_value] _ |- _ =>
    inversion Hsegments; subst; try discriminate
  end.
  match goal with Hsegments : ArgumentSegments _ _ _ [] [] _ |- _ => inversion Hsegments; subst end.
  match goal with Hrem : RemainderChildren _ _ _ _ None _ |- _ => inversion Hrem; subst end.
  simpl in *. eexists. eexists. repeat split; eassumption.
Qed.

Print Assumptions environment_survives_heap_extension.
Print Assumptions allocated_environment_has_exact_parent.
Print Assumptions overlay_first_binding.
Print Assumptions overlay_unbound_lookup.
Print Assumptions indexed_lookup_has_exact_overlay_meaning.
Print Assumptions task_step_preserves_continuation_meaning.
Print Assumptions construction_invariant_preserved.
Print Assumptions finite_run_preserves_construction_invariant.
Print Assumptions successful_singleton_completion_instantiates_exact_root_environment.
Print Assumptions row_bindings_retain_exact_parameters.
Print Assumptions map_rows_retain_all_source_rows.
Print Assumptions abstraction_slots_precede_body.

End AuthoredTermConstruction.
