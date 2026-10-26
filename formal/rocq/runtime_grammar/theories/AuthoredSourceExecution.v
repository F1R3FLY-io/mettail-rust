(** Source derivations for the existing typed rule-frame machine.

    This is not a second evaluator, a receipt replay checker, or a proof of
    the Rust implementation.  It supplies the missing invariant between a
    source match, ordered premise execution, and frame completion.  Primitive
    matching, e-graph construction/readback, intrinsic results, collection
    observations, and guard truth have explicit LOCAL refinement contracts.
    There is no premise asserting that a candidate is a source transition.

    The source view retains fields erased by ExecutableTheoryCore's older
    abstraction: multi-source Map, Product, typed literal payloads, judgment
    identities/arguments, intrinsic opcodes/slots, and guard payloads.  IDs and
    variable declarations are reused from that module.  Producing this view
    from a verified Rust owner, including resolving names to its exact IDs,
    remains a source-refinement obligation; an arbitrary view is not admission.

    RuleDerivation includes either orientation of source equations.  Only a
    RewriteRef may discharge a nested transition; equations have no grade.
    Derivations are finite, but their depth and substitutions are unrestricted.
    No termination or completeness claim for arbitrary recursive theories or
    equation saturation is made.  Native beta and Cost(G) interpretation are
    separate from structural instantiation in this source execution ABI.

    ActionFrame/ActionReturnFrame, ForAllElement/RestoreForAll, and
    CompletedActionBranch in semantic_transition_kernel.rs are the concrete
    refinement sites.  A proof activation namespaces a frame's private locals;
    it need not be an additional runtime field in a stack-owned ActionFrame.
*)

From Stdlib Require Import List Bool PeanoNat ZArith.
From RuntimeGrammar Require Import ExecutableTheoryCore SemanticTransitionKernel
  SemanticIntrinsics CanonicalSemanticTermImage.
Import ListNotations.

Module AuthoredSourceExecution.
Module Core := ExecutableTheoryCore.
Module K := SemanticTransitionKernel.
Module Intr := SemanticIntrinsics.
Module Canon := CanonicalSemanticTermImage.

Definition Value := K.LogicTerm.
Definition Environment := K.ScopedSubstitution.
Definition Activation := nat.
Definition Bytes := list nat.

Inductive Literal :=
| StringLiteral (utf8 : Bytes)
| BytesLiteral (bytes : Bytes)
| IntegerLiteral (integer : Z)
| FloatLiteral (bits : nat)
| BooleanLiteral (boolean : bool)
| UnitLiteral
| BigIntegerLiteral (signed_bytes : Bytes)
| BigRationalLiteral (numerator denominator : Bytes)
| FixedPointLiteral (unscaled : Bytes) (scale : nat).

Inductive TermForm :=
| SourceVariable (id : Core.VariableId)
| SourceConstructor (id : Core.ConstructorId) (arguments : list Core.TermId)
| SourceAbstraction (binder : Core.VariableId) (body : Core.TermId)
| SourceSubstitution (abstraction argument : Core.TermId)
| SourceCollection (elements : list Core.TermId) (remainder : option Core.VariableId)
    (pathmap_mode : option Canon.PathMapMode)
| SourceMap (sources : list Core.TermId) (parameters : list Core.VariableId)
    (body : Core.TermId)
| SourceProduct (factors : list Core.TermId)
| SourceLiteral (literal : Literal).

Record TermNode := {
  node_sort : Core.SortId;
  node_form : TermForm
}.

Record JudgmentAtom := {
  judgment_id : nat;
  judgment_terms : list Core.TermId
}.

Inductive PremiseForm :=
| Freshness (variable target : Core.VariableId) (remainder : bool)
| Transition (source target : Core.VariableId)
| Judgment (atom : JudgmentAtom)
| ForAll (collection parameter : Core.VariableId) (body : Core.PremiseId)
| Intrinsic (invocation : Intr.IntrinsicInvocation)
| Guard (source_payload image_commitment : Bytes).

Record Arena := {
  variables : list Core.VariableDecl;
  terms : list TermNode;
  premises : list PremiseForm;
  premise_roots : list Core.PremiseId
}.

Record SourceRule := {
  rule_arena : Arena;
  rule_left : Core.TermId;
  rule_right : Core.TermId;
  rule_grade : option Core.TermId
}.

Record HornClause := {
  clause_arena : Arena;
  clause_conclusion : JudgmentAtom;
  clause_premises : list JudgmentAtom
}.

Record SourceOwner := {
  owner_language : Bytes;
  owner_theory : Bytes;
  owner_semantic_image : Bytes;
  owner_cost_image : option Bytes
}.

Record SourceTheory := {
  source_owner : SourceOwner;
  source_equations : list SourceRule;
  source_rewrites : list SourceRule;
  source_judgment_clauses : list HornClause
}.

Inductive Orientation := Forward | Reverse.
Inductive RuleReference :=
| EquationRef (index : nat) (direction : Orientation)
| RewriteRef (index : nat).

Definition orient_equation (rule : SourceRule) (direction : Orientation) :=
  {| rule_arena := rule_arena rule;
     rule_left := match direction with Forward => rule_left rule | Reverse => rule_right rule end;
     rule_right := match direction with Forward => rule_right rule | Reverse => rule_left rule end;
     rule_grade := None |}.

Definition lookup_rule theory reference : option SourceRule :=
  match reference with
  | EquationRef index direction =>
      option_map (fun rule => orient_equation rule direction)
        (nth_error (source_equations theory) index)
  | RewriteRef index => nth_error (source_rewrites theory) index
  end.

Definition is_rewrite reference : bool :=
  match reference with RewriteRef _ => true | EquationRef _ _ => false end.

Definition slot activation variable : K.ScopedVariable :=
  {| K.scoped_activation := activation; K.scoped_local := variable |}.

Definition lookup activation variable environment :=
  K.lookup_scoped (slot activation variable) environment.

Definition return_frame activation target environment : K.TransitionResumeFrame :=
  {| K.transition_parent_substitution := environment;
     K.transition_target_variable := slot activation target |}.

Definition element_scope activation parameter element environment : K.ForAllScope :=
  {| K.forall_outer_substitution := environment;
     K.forall_parameter_variable := slot activation parameter;
     K.forall_element_value := element |}.

Inductive ReadSlots (activation : Activation) (environment : Environment) :
    list Core.VariableId -> list Value -> Prop :=
| read_slots_nil : ReadSlots activation environment [] []
| read_slots_cons : forall variable value rest values,
    lookup activation variable environment = Some value ->
    ReadSlots activation environment rest values ->
    ReadSlots activation environment (variable :: rest) (value :: values).

(** Same fresh-output discipline as action_bind_new, not an unrestricted
    replacement environment supplied by an intrinsic. *)
Inductive FreshBindings (activation : Activation) :
    Environment -> list Core.VariableId -> list Value -> Environment -> Prop :=
| fresh_bindings_nil : forall environment,
    FreshBindings activation environment [] [] environment
| fresh_bindings_cons : forall environment variable value rest values final,
    lookup activation variable environment = None ->
    FreshBindings activation
      (K.extend_scoped (slot activation variable) value environment)
      rest values final ->
    FreshBindings activation environment (variable :: rest) (value :: values) final.

(** Meaning is kept separate from an implementation observation.  In
    particular, matching refers to the actual source arena/root and every
    binding, not merely a matching root tag.  Instantiation names the exact
    arena/root/final environment; it is not an assumed transition theorem.
    These interfaces must be instantiated by the existing matcher, builder,
    intrinsic, freshness, collection, and guard contracts.  Their executable
    correctness is not proved just by declaring this record. *)
Record PrimitiveMeaning := {
  term_matches : SourceTheory -> Arena -> Activation -> Core.TermId ->
    Value -> Environment -> Prop;
  term_instantiates : SourceTheory -> Arena -> Activation -> Core.TermId ->
    Environment -> Value -> Prop;
  freshness_true : bool -> Value -> Value -> Prop;
  collection_has_elements : Value -> list Value -> Prop;
  intrinsic_computes : Intr.IntrinsicOpcode -> list Value -> list Value -> Prop;
  guard_true : SourceTheory -> Arena -> Activation -> Bytes -> Bytes ->
    Environment -> Prop
}.

Record PrimitiveObservations := {
  match_observed : SourceTheory -> Arena -> Activation -> Core.TermId ->
    Value -> Environment -> Prop;
  instantiation_observed : SourceTheory -> Arena -> Activation -> Core.TermId ->
    Environment -> Value -> Prop;
  freshness_observed : bool -> Value -> Value -> Prop;
  elements_observed : Value -> list Value -> Prop;
  intrinsic_observed : Intr.IntrinsicOpcode -> list Value -> list Value -> Prop;
  guard_observed : SourceTheory -> Arena -> Activation -> Bytes -> Bytes ->
    Environment -> Prop
}.

Record LocalRefinement (meaning : PrimitiveMeaning) (observations : PrimitiveObservations) : Prop := {
  match_refines : forall theory arena activation root input environment,
    match_observed observations theory arena activation root input environment ->
    term_matches meaning theory arena activation root input environment;
  instantiation_refines : forall theory arena activation root environment output,
    instantiation_observed observations theory arena activation root environment output ->
    term_instantiates meaning theory arena activation root environment output;
  freshness_refines : forall remainder variable target,
    freshness_observed observations remainder variable target ->
    freshness_true meaning remainder variable target;
  elements_refine : forall collection elements,
    elements_observed observations collection elements ->
    collection_has_elements meaning collection elements;
  intrinsic_refines : forall opcode inputs outputs,
    intrinsic_observed observations opcode inputs outputs ->
    intrinsic_computes meaning opcode inputs outputs;
  guard_refines : forall theory arena activation payload commitment environment,
    guard_observed observations theory arena activation payload commitment environment ->
    guard_true meaning theory arena activation payload commitment environment
}.

Definition InstantiateArguments meaning theory arena activation environment roots values :=
  Forall2 (fun root value =>
    term_instantiates meaning theory arena activation root environment value) roots values.

Inductive GradeInstantiation meaning theory arena activation environment :
    option Core.TermId -> option Value -> Prop :=
| grade_absent : GradeInstantiation meaning theory arena activation environment None None
| grade_present : forall root value,
    term_instantiates meaning theory arena activation root environment value ->
    GradeInstantiation meaning theory arena activation environment (Some root) (Some value).

(** A finite, mutually inductive source proof.  Recursive transitions and Horn
    clauses contain finite child proofs; no global termination is assumed.
    ForAllElements starts EACH element from the same saved outer environment. *)
Inductive RuleDerivation (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    RuleReference -> Activation -> Value -> Environment -> Environment ->
    Value -> option Value -> Prop :=
| derive_rule : forall reference activation rule input initial final output grade,
    lookup_rule theory reference = Some rule ->
    term_matches meaning theory (rule_arena rule) activation (rule_left rule) input initial ->
    OrderedPremises meaning theory reference rule activation
      (premise_roots (rule_arena rule)) initial final ->
    term_instantiates meaning theory (rule_arena rule) activation (rule_right rule) final output ->
    GradeInstantiation meaning theory (rule_arena rule) activation final (rule_grade rule) grade ->
    RuleDerivation meaning theory reference activation input initial final output grade
with PremiseDerivation (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    RuleReference -> SourceRule -> Activation -> Core.PremiseId ->
    Environment -> Environment -> Prop :=
| derive_freshness : forall reference rule activation premise environment variable target
    remainder variable_value target_value,
    nth_error (premises (rule_arena rule)) premise = Some (Freshness variable target remainder) ->
    lookup activation variable environment = Some variable_value ->
    lookup activation target environment = Some target_value ->
    freshness_true meaning remainder variable_value target_value ->
    PremiseDerivation meaning theory reference rule activation premise environment environment
| derive_transition : forall reference rule activation premise environment source target input
    child_rule child_activation child_initial child_final output child_grade,
    is_rewrite reference = true ->
    nth_error (premises (rule_arena rule)) premise = Some (Transition source target) ->
    lookup activation source environment = Some input ->
    lookup activation target environment = None ->
    RuleDerivation meaning theory (RewriteRef child_rule) child_activation input
      child_initial child_final output child_grade ->
    PremiseDerivation meaning theory reference rule activation premise environment
      (K.resume_nested_transition (return_frame activation target environment) output child_final)
| derive_judgment : forall reference rule activation premise environment atom arguments,
    nth_error (premises (rule_arena rule)) premise = Some (Judgment atom) ->
    InstantiateArguments meaning theory (rule_arena rule) activation environment
      (judgment_terms atom) arguments ->
    HornDerivation meaning theory (judgment_id atom) arguments ->
    PremiseDerivation meaning theory reference rule activation premise environment environment
| derive_forall : forall reference rule activation premise environment collection parameter body
    collection_value elements,
    nth_error (premises (rule_arena rule)) premise = Some (ForAll collection parameter body) ->
    lookup activation collection environment = Some collection_value ->
    collection_has_elements meaning collection_value elements ->
    ForAllElements meaning theory reference rule activation parameter body environment elements ->
    PremiseDerivation meaning theory reference rule activation premise environment environment
| derive_intrinsic : forall reference rule activation premise initial final invocation inputs outputs,
    nth_error (premises (rule_arena rule)) premise = Some (Intrinsic invocation) ->
    Intr.intrinsic_invocation_well_shaped invocation ->
    ReadSlots activation initial (Intr.invocation_inputs invocation) inputs ->
    intrinsic_computes meaning (Intr.invocation_opcode invocation) inputs outputs ->
    FreshBindings activation initial (Intr.invocation_outputs invocation) outputs final ->
    PremiseDerivation meaning theory reference rule activation premise initial final
| derive_guard : forall reference rule activation premise environment payload commitment,
    nth_error (premises (rule_arena rule)) premise = Some (Guard payload commitment) ->
    guard_true meaning theory (rule_arena rule) activation payload commitment environment ->
    PremiseDerivation meaning theory reference rule activation premise environment environment
with OrderedPremises (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    RuleReference -> SourceRule -> Activation -> list Core.PremiseId ->
    Environment -> Environment -> Prop :=
| premises_nil : forall reference rule activation environment,
    OrderedPremises meaning theory reference rule activation [] environment environment
| premises_cons : forall reference rule activation premise rest initial middle final,
    PremiseDerivation meaning theory reference rule activation premise initial middle ->
    OrderedPremises meaning theory reference rule activation rest middle final ->
    OrderedPremises meaning theory reference rule activation (premise :: rest) initial final
with ForAllElements (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    RuleReference -> SourceRule -> Activation -> Core.VariableId -> Core.PremiseId ->
    Environment -> list Value -> Prop :=
| elements_nil : forall reference rule activation parameter body environment,
    ForAllElements meaning theory reference rule activation parameter body environment []
| elements_cons : forall reference rule activation parameter body environment element rest private,
    PremiseDerivation meaning theory reference rule activation body
      (K.enter_forall_scope (element_scope activation parameter element environment)) private ->
    ForAllElements meaning theory reference rule activation parameter body environment rest ->
    ForAllElements meaning theory reference rule activation parameter body environment (element :: rest)
with HornDerivation (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    nat -> list Value -> Prop :=
| derive_horn : forall index clause activation environment arguments,
    nth_error (source_judgment_clauses theory) index = Some clause ->
    InstantiateArguments meaning theory (clause_arena clause) activation environment
      (judgment_terms (clause_conclusion clause)) arguments ->
    HornGoals meaning theory (clause_arena clause) activation environment (clause_premises clause) ->
    HornDerivation meaning theory (judgment_id (clause_conclusion clause)) arguments
with HornGoals (meaning : PrimitiveMeaning) (theory : SourceTheory) :
    Arena -> Activation -> Environment -> list JudgmentAtom -> Prop :=
| horn_goals_nil : forall arena activation environment,
    HornGoals meaning theory arena activation environment []
| horn_goals_cons : forall arena activation environment atom rest arguments,
    InstantiateArguments meaning theory arena activation environment (judgment_terms atom) arguments ->
    HornDerivation meaning theory (judgment_id atom) arguments ->
    HornGoals meaning theory arena activation environment rest ->
    HornGoals meaning theory arena activation environment (atom :: rest).

Lemma ordered_premises_append : forall meaning theory reference rule activation prefix initial middle,
  OrderedPremises meaning theory reference rule activation prefix initial middle ->
  forall suffix final,
  OrderedPremises meaning theory reference rule activation suffix middle final ->
  OrderedPremises meaning theory reference rule activation (prefix ++ suffix) initial final.
Proof.
  intros meaning theory reference rule activation prefix initial middle Hprefix.
  induction Hprefix; intros suffix last Hsuffix; simpl.
  - exact Hsuffix.
  - eapply premises_cons; eauto.
Qed.

Section FrameExecution.
Context (meaning : PrimitiveMeaning) (observations : PrimitiveObservations).
Context (refinement : LocalRefinement meaning observations).

(** One completed premise operation.  Nested calls carry their finite SOURCE
    child derivation, obtained by the frame-completion theorem below; this is
    not a trusted predicate over child receipt bytes.  A Horn proof likewise
    contains actual source clause instances.  No replay implementation is
    introduced here. *)
Inductive PremiseOperation theory reference rule activation :
    Core.PremiseId -> Environment -> Environment -> Prop :=
| operation_freshness : forall premise environment variable target remainder v t,
    nth_error (premises (rule_arena rule)) premise = Some (Freshness variable target remainder) ->
    lookup activation variable environment = Some v ->
    lookup activation target environment = Some t ->
    freshness_observed observations remainder v t ->
    PremiseOperation theory reference rule activation premise environment environment
| operation_return : forall premise environment source target input child_rule child_activation
    child_initial child_final output child_grade,
    is_rewrite reference = true ->
    nth_error (premises (rule_arena rule)) premise = Some (Transition source target) ->
    lookup activation source environment = Some input ->
    lookup activation target environment = None ->
    RuleDerivation meaning theory (RewriteRef child_rule) child_activation input
      child_initial child_final output child_grade ->
    PremiseOperation theory reference rule activation premise environment
      (K.resume_nested_transition (return_frame activation target environment) output child_final)
| operation_judgment : forall premise environment atom arguments,
    nth_error (premises (rule_arena rule)) premise = Some (Judgment atom) ->
    Forall2 (fun root value => instantiation_observed observations theory (rule_arena rule)
      activation root environment value) (judgment_terms atom) arguments ->
    HornDerivation meaning theory (judgment_id atom) arguments ->
    PremiseOperation theory reference rule activation premise environment environment
| operation_forall : forall premise environment collection parameter body value elements,
    nth_error (premises (rule_arena rule)) premise = Some (ForAll collection parameter body) ->
    lookup activation collection environment = Some value ->
    elements_observed observations value elements ->
    ForAllElements meaning theory reference rule activation parameter body environment elements ->
    PremiseOperation theory reference rule activation premise environment environment
| operation_intrinsic : forall premise initial final invocation inputs outputs,
    nth_error (premises (rule_arena rule)) premise = Some (Intrinsic invocation) ->
    Intr.intrinsic_invocation_well_shaped invocation ->
    ReadSlots activation initial (Intr.invocation_inputs invocation) inputs ->
    intrinsic_observed observations (Intr.invocation_opcode invocation) inputs outputs ->
    FreshBindings activation initial (Intr.invocation_outputs invocation) outputs final ->
    PremiseOperation theory reference rule activation premise initial final
| operation_guard : forall premise environment payload commitment,
    nth_error (premises (rule_arena rule)) premise = Some (Guard payload commitment) ->
    guard_observed observations theory (rule_arena rule) activation payload commitment environment ->
    PremiseOperation theory reference rule activation premise environment environment.

Lemma observed_arguments_refine : forall theory arena activation environment roots values,
  Forall2 (fun root value => instantiation_observed observations theory arena
    activation root environment value) roots values ->
  InstantiateArguments meaning theory arena activation environment roots values.
Proof.
  intros theory arena activation environment roots values H.
  induction H; constructor; auto.
  eapply instantiation_refines; eauto.
Qed.

Theorem completed_premise_operation_has_source_derivation :
  forall theory reference rule activation premise initial final,
    PremiseOperation theory reference rule activation premise initial final ->
    PremiseDerivation meaning theory reference rule activation premise initial final.
Proof.
  intros theory reference rule activation premise initial final H.
  destruct H.
  - eapply derive_freshness; eauto. eapply freshness_refines; eauto.
  - eapply derive_transition; eauto.
  - eapply derive_judgment; eauto using observed_arguments_refine.
  - eapply derive_forall; eauto. eapply elements_refine; eauto.
  - eapply derive_intrinsic; eauto. eapply intrinsic_refines; eauto.
  - eapply derive_guard; eauto. eapply guard_refines; eauto.
Qed.

Record Frame := {
  frame_done : list Core.PremiseId;
  frame_pending : list Core.PremiseId;
  frame_environment : Environment
}.

Definition initial_frame rule environment :=
  {| frame_done := []; frame_pending := premise_roots (rule_arena rule);
     frame_environment := environment |}.

Definition FrameInvariant theory reference rule activation initial frame : Prop :=
  premise_roots (rule_arena rule) = frame_done frame ++ frame_pending frame /\
  OrderedPremises meaning theory reference rule activation (frame_done frame)
    initial (frame_environment frame).

Inductive FrameStep theory reference rule activation : Frame -> Frame -> Prop :=
| frame_advance : forall done premise pending initial final,
    PremiseOperation theory reference rule activation premise initial final ->
    FrameStep theory reference rule activation
      {| frame_done := done; frame_pending := premise :: pending; frame_environment := initial |}
      {| frame_done := done ++ [premise]; frame_pending := pending; frame_environment := final |}.

Inductive FrameRun theory reference rule activation : Frame -> Frame -> Prop :=
| frame_run_refl : forall frame, FrameRun theory reference rule activation frame frame
| frame_run_step : forall first middle final,
    FrameStep theory reference rule activation first middle ->
    FrameRun theory reference rule activation middle final ->
    FrameRun theory reference rule activation first final.

Lemma initial_frame_invariant : forall theory reference rule activation environment,
  FrameInvariant theory reference rule activation environment (initial_frame rule environment).
Proof. intros; split; [reflexivity | constructor]. Qed.

Theorem frame_operation_preserves_exact_source_prefix :
  forall theory reference rule activation initial before after,
    FrameInvariant theory reference rule activation initial before ->
    FrameStep theory reference rule activation before after ->
    FrameInvariant theory reference rule activation initial after.
Proof.
  intros theory reference rule activation initial before after Hinv Hstep.
  destruct Hstep. destruct Hinv as [Horder Hprefix]. split; simpl in *.
  - rewrite <- app_assoc. simpl. exact Horder.
  - eapply ordered_premises_append; [exact Hprefix |].
    eapply premises_cons; [|constructor].
    now apply completed_premise_operation_has_source_derivation.
Qed.

Theorem finite_frame_run_preserves_source_derivation :
  forall theory reference rule activation before after,
    FrameRun theory reference rule activation before after ->
    forall initial, FrameInvariant theory reference rule activation initial before ->
    FrameInvariant theory reference rule activation initial after.
Proof.
  intros theory reference rule activation before after Hrun.
  induction Hrun; intros initial Hinv; [exact Hinv |].
  apply IHHrun. eapply frame_operation_preserves_exact_source_prefix; eauto.
Qed.

(** A nested ForAll body uses the same rule arena but a singleton pending
    list, not the rule's outer root list.  This theorem therefore does not
    assume that a frame starts at the outer rule roots. *)
Theorem finished_frame_derives_its_exact_pending_sequence :
  forall theory reference rule activation before after,
    FrameRun theory reference rule activation before after ->
    frame_pending after = [] ->
    OrderedPremises meaning theory reference rule activation (frame_pending before)
      (frame_environment before) (frame_environment after).
Proof.
  intros theory reference rule activation before after Hrun.
  induction Hrun; intro Hempty.
  - rewrite Hempty. constructor.
  - destruct H. simpl. eapply premises_cons.
    + eapply completed_premise_operation_has_source_derivation; eassumption.
    + apply IHHrun. exact Hempty.
Qed.

Theorem completed_forall_body_supplies_source_element :
  forall theory reference rule activation parameter body environment element final,
    FrameRun theory reference rule activation
      {| frame_done := []; frame_pending := [body]; frame_environment :=
          K.enter_forall_scope (element_scope activation parameter element environment) |} final ->
    frame_pending final = [] ->
    PremiseDerivation meaning theory reference rule activation body
      (K.enter_forall_scope (element_scope activation parameter element environment))
      (frame_environment final) /\
    K.leave_forall_scope (element_scope activation parameter element environment)
      (frame_environment final) = environment.
Proof.
  intros theory reference rule activation parameter body environment element final Hrun Hempty.
  pose proof (finished_frame_derives_its_exact_pending_sequence _ _ _ _ _ _ Hrun Hempty) as Hbody.
  simpl in Hbody. inversion Hbody; subst.
  match goal with
  | Hnil : OrderedPremises _ _ _ _ _ [] _ _ |- _ => inversion Hnil; subst
  end.
  split; [assumption | reflexivity].
Qed.

Record CompletionObservation theory rule activation environment := {
  completed_output : Value;
  completed_grade : option Value;
  completed_rhs_observed : instantiation_observed observations theory (rule_arena rule)
    activation (rule_right rule) environment completed_output;
  completed_grade_observed :
    match rule_grade rule, completed_grade with
    | None, None => True
    | Some root, Some value => instantiation_observed observations theory (rule_arena rule)
        activation root environment value
    | _, _ => False
    end
}.

Lemma completed_grade_refines : forall theory rule activation environment
    (completion : CompletionObservation theory rule activation environment),
  GradeInstantiation meaning theory (rule_arena rule) activation environment
    (rule_grade rule) (completed_grade _ _ _ _ completion).
Proof.
  intros theory rule activation environment [output grade Hr Hg]. simpl in *.
  destruct (rule_grade rule), grade; try contradiction; constructor.
  eapply instantiation_refines; eauto.
Qed.

Theorem successful_finite_completion_is_exact_source_derivation :
  forall theory reference rule activation input initial final
    (completion : CompletionObservation theory rule activation (frame_environment final)),
    lookup_rule theory reference = Some rule ->
    match_observed observations theory (rule_arena rule) activation (rule_left rule) input initial ->
    FrameRun theory reference rule activation (initial_frame rule initial) final ->
    frame_pending final = [] ->
    RuleDerivation meaning theory reference activation input initial (frame_environment final)
      (completed_output _ _ _ _ completion) (completed_grade _ _ _ _ completion).
Proof.
  intros theory reference rule activation input initial final completion Hrule Hmatch Hrun Hempty.
  pose proof (finite_frame_run_preserves_source_derivation _ _ _ _ _ _ Hrun initial
    (initial_frame_invariant theory reference rule activation initial)) as [Horder Hprefix].
  rewrite Hempty, app_nil_r in Horder.
  eapply derive_rule with (rule := rule); eauto.
  - eapply match_refines; eauto.
  - rewrite Horder. exact Hprefix.
  - eapply instantiation_refines; [exact refinement | exact (completed_rhs_observed _ _ _ _ completion)].
  - apply completed_grade_refines.
Qed.

(** Plug a completed child frame into the parent's actual return operation.
    The child's private bindings are used to construct its RHS/grade, but
    resume_nested_transition exports only the returned value. *)
Theorem completed_child_frame_supplies_source_return :
  forall theory reference parent activation premise environment source target input
    child_index child child_activation child_initial child_final
    (completion : CompletionObservation theory child child_activation (frame_environment child_final)),
    is_rewrite reference = true ->
    nth_error (premises (rule_arena parent)) premise = Some (Transition source target) ->
    lookup activation source environment = Some input ->
    lookup activation target environment = None ->
    lookup_rule theory (RewriteRef child_index) = Some child ->
    match_observed observations theory (rule_arena child) child_activation
      (rule_left child) input child_initial ->
    FrameRun theory (RewriteRef child_index) child child_activation
      (initial_frame child child_initial) child_final ->
    frame_pending child_final = [] ->
    PremiseOperation theory reference parent activation premise environment
      (K.resume_nested_transition (return_frame activation target environment)
        (completed_output _ _ _ _ completion) (frame_environment child_final)).
Proof.
  intros theory reference parent activation premise environment source target input
    child_index child child_activation child_initial child_final completion
    Hrewrite Hpremise Hinput Hfresh Hchild Hmatch Hrun Hempty.
  eapply operation_return; eauto.
  eapply successful_finite_completion_is_exact_source_derivation; eauto.
Qed.

Theorem completion_uses_one_final_substitution : forall theory rule activation environment
    (completion : CompletionObservation theory rule activation environment) root value,
  rule_grade rule = Some root -> completed_grade _ _ _ _ completion = Some value ->
  term_instantiates meaning theory (rule_arena rule) activation (rule_right rule) environment
    (completed_output _ _ _ _ completion) /\
  term_instantiates meaning theory (rule_arena rule) activation root environment value.
Proof.
  intros theory rule activation environment [output grade Hr Hg] root value Hroot Hgrade.
  simpl in *. rewrite Hroot, Hgrade in Hg. split; eapply instantiation_refines; eauto.
Qed.

End FrameExecution.

Theorem nested_return_exports_only_declared_target :
  forall activation target environment output child_private other,
    other <> slot activation target ->
    K.lookup_scoped other
      (K.resume_nested_transition (return_frame activation target environment) output child_private) =
    K.lookup_scoped other environment.
Proof.
  intros. unfold K.resume_nested_transition.
  exact (K.resumed_transition_preserves_every_parent_binding
    (return_frame activation target environment) output other H).
Qed.

Theorem nested_return_cannot_export_child_bindings :
  forall activation target environment output child_left child_right,
    K.resume_nested_transition (return_frame activation target environment) output child_left =
    K.resume_nested_transition (return_frame activation target environment) output child_right.
Proof. intros; apply K.child_substitutions_cannot_escape_transition_resume. Qed.

Theorem forall_element_restores_exact_outer_environment :
  forall activation parameter element environment private,
    K.leave_forall_scope (element_scope activation parameter element environment) private = environment.
Proof. intros; apply K.leaving_forall_scope_restores_exact_outer_substitution. Qed.

Theorem equation_lookup_has_no_grade : forall theory index direction rule,
  lookup_rule theory (EquationRef index direction) = Some rule -> rule_grade rule = None.
Proof.
  intros theory index direction rule H. unfold lookup_rule in H.
  destruct (nth_error (source_equations theory) index); simpl in H; try discriminate.
  inversion H; reflexivity.
Qed.

Theorem equation_derivation_is_cost_free : forall meaning theory index direction activation
    input initial final output grade,
  RuleDerivation meaning theory (EquationRef index direction) activation input initial final output grade ->
  grade = None.
Proof.
  intros meaning theory index direction activation input initial final output grade H.
  inversion H; subst.
  match goal with
  | L : lookup_rule _ (EquationRef _ _) = Some ?r,
    G : GradeInstantiation _ _ _ _ _ (rule_grade ?r) _ |- _ =>
      rewrite (equation_lookup_has_no_grade _ _ _ _ L) in G; inversion G; reflexivity
  end.
Qed.

Theorem equations_cannot_discharge_transition_premises :
  forall meaning theory index direction rule activation premise initial final source target,
    nth_error (premises (rule_arena rule)) premise = Some (Transition source target) ->
    ~ PremiseDerivation meaning theory (EquationRef index direction) rule activation premise initial final.
Proof.
  intros meaning theory index direction rule activation premise initial final source target Hnode H.
  inversion H; subst; try congruence; discriminate.
Qed.

Print Assumptions completed_premise_operation_has_source_derivation.
Print Assumptions frame_operation_preserves_exact_source_prefix.
Print Assumptions finite_frame_run_preserves_source_derivation.
Print Assumptions finished_frame_derives_its_exact_pending_sequence.
Print Assumptions completed_forall_body_supplies_source_element.
Print Assumptions successful_finite_completion_is_exact_source_derivation.
Print Assumptions completed_child_frame_supplies_source_return.
Print Assumptions completion_uses_one_final_substitution.
Print Assumptions nested_return_exports_only_declared_target.
Print Assumptions nested_return_cannot_export_child_bindings.
Print Assumptions forall_element_restores_exact_outer_environment.
Print Assumptions equation_lookup_has_no_grade.
Print Assumptions equation_derivation_is_cost_free.
Print Assumptions equations_cannot_discharge_transition_premises.

End AuthoredSourceExecution.
