(**
  ExecutableTheoryCore: admission laws for canonical runtime GSLT rules.

  Runtime-defined equations, directed rewrites, and judgment clauses share a
  flat, typed arena.  Node references point backward; variables have dense
  identifiers and explicit sorts; premise results become available only after
  the premise that produces them.  These choices make admission and later
  execution iterative while ruling out dangling terms, ill-sorted
  substitutions, escaping binders, and RHS variables that no match or premise
  can supply.

  The Rust representation mirrors the records below.  Its validator computes
  these predicates using bounded worklists.  This file establishes the laws
  the executable validator must preserve; it deliberately does not assume
  termination or confluence of a user rewrite system.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Module ExecutableTheoryCore.

Definition SortId := nat.
Definition ConstructorId := nat.
Definition VariableId := nat.
Definition TermId := nat.
Definition PremiseId := nat.

Inductive VariableRole :=
| InputVariable
| DerivedVariable
| BoundVariable
| RemainderVariable
| QuantifiedVariable.

Record VariableDecl := {
  variable_sort : SortId;
  variable_role : VariableRole
}.

Record ConstructorDecl := {
  constructor_domain : list SortId;
  constructor_codomain : SortId
}.

Record Signature := {
  signature_sort_count : nat;
  signature_constructors : list ConstructorDecl;
  (** [(arrow_sort, domain_sort, codomain_sort)]. *)
  signature_arrows : list (SortId * SortId * SortId);
  (** [(collection_sort, element_sort)]. *)
  signature_collections : list (SortId * SortId)
}.

Inductive TermForm :=
| VariableTerm (variable : VariableId)
| ConstructorTerm (constructor : ConstructorId) (arguments : list TermId)
| AbstractionTerm (binder : VariableId) (body : TermId)
| SubstitutionTerm (abstraction argument : TermId)
| CollectionTerm
    (element_sort : SortId)
    (elements : list TermId)
    (remainder : option VariableId)
| MapTerm
    (collection : TermId)
    (parameters : list VariableId)
    (body : TermId)
| ZipTerm (first second : TermId)
| LiteralTerm (canonical_payload : nat).

Record TermNode := {
  term_sort : SortId;
  term_form : TermForm
}.

Definition declared_sort (signature : Signature) (sort : SortId) : Prop :=
  sort < signature_sort_count signature.

Definition earlier (owner target : nat) : Prop := target < owner.

Definition term_has_sort
    (arena : list TermNode) (term : TermId) (sort : SortId) : Prop :=
  exists node, nth_error arena term = Some node /\ term_sort node = sort.

Definition variable_has_sort
    (variables : list VariableDecl) (variable : VariableId) (sort : SortId) : Prop :=
  exists declaration,
    nth_error variables variable = Some declaration /\
    variable_sort declaration = sort.

Definition references_are_earlier (owner : nat) (references : list TermId) : Prop :=
  Forall (earlier owner) references.

Definition node_well_typed
    (signature : Signature)
    (variables : list VariableDecl)
    (arena : list TermNode)
    (owner : nat)
    (node : TermNode) : Prop :=
  declared_sort signature (term_sort node) /\
  match term_form node with
  | VariableTerm variable =>
      variable_has_sort variables variable (term_sort node)
  | ConstructorTerm constructor arguments =>
      exists declaration,
        nth_error (signature_constructors signature) constructor = Some declaration /\
        length arguments = length (constructor_domain declaration) /\
        references_are_earlier owner arguments /\
        Forall2 (term_has_sort arena) arguments (constructor_domain declaration) /\
        term_sort node = constructor_codomain declaration
  | AbstractionTerm binder body =>
      exists domain codomain,
        In (term_sort node, domain, codomain) (signature_arrows signature) /\
        variable_has_sort variables binder domain /\
        earlier owner body /\
        term_has_sort arena body codomain
  | SubstitutionTerm abstraction argument =>
      exists domain codomain arrow,
        In (arrow, domain, codomain) (signature_arrows signature) /\
        earlier owner abstraction /\
        term_has_sort arena abstraction arrow /\
        earlier owner argument /\
        term_has_sort arena argument domain /\
        term_sort node = codomain
  | CollectionTerm element_sort elements remainder =>
      declared_sort signature element_sort /\
      In (term_sort node, element_sort) (signature_collections signature) /\
      references_are_earlier owner elements /\
      Forall (fun element => term_has_sort arena element element_sort) elements /\
      match remainder with
      | None => True
      | Some variable => variable < length variables
      end
  | MapTerm collection parameters body =>
      earlier owner collection /\
      earlier owner body /\
      Forall (fun variable => variable < length variables) parameters
  | ZipTerm first second => earlier owner first /\ earlier owner second
  | LiteralTerm _ => True
  end.

Definition arena_well_typed
    (signature : Signature)
    (variables : list VariableDecl)
    (arena : list TermNode) : Prop :=
  forall owner node,
    nth_error arena owner = Some node ->
    node_well_typed signature variables arena owner node.

Theorem well_typed_constructor_is_arity_and_sort_correct :
  forall signature variables arena owner node constructor arguments declaration,
    arena_well_typed signature variables arena ->
    nth_error arena owner = Some node ->
    term_form node = ConstructorTerm constructor arguments ->
    nth_error (signature_constructors signature) constructor = Some declaration ->
    length arguments = length (constructor_domain declaration) /\
    references_are_earlier owner arguments /\
    Forall2 (term_has_sort arena) arguments (constructor_domain declaration) /\
    term_sort node = constructor_codomain declaration.
Proof.
  intros signature variables arena owner node constructor arguments declaration
         Harena Hnode Hform Hconstructor.
  specialize (Harena owner node Hnode).
  unfold node_well_typed in Harena.
  rewrite Hform in Harena.
  destruct Harena as [_ [actual [Hactual [Harity [Htopology [Hsorts Hresult]]]]]].
  rewrite Hconstructor in Hactual.
  inversion Hactual; subst actual.
  repeat split; assumption.
Qed.

Theorem well_typed_arena_references_only_prior_nodes :
  forall signature variables arena owner node constructor arguments,
    arena_well_typed signature variables arena ->
    nth_error arena owner = Some node ->
    term_form node = ConstructorTerm constructor arguments ->
    Forall (fun target => target < owner) arguments.
Proof.
  intros signature variables arena owner node constructor arguments
         Harena Hnode Hform.
  specialize (Harena owner node Hnode).
  unfold node_well_typed in Harena.
  rewrite Hform in Harena.
  destruct Harena as [_ [declaration [_ [_ [Htopology _]]]]].
  exact Htopology.
Qed.

Theorem well_typed_substitution_is_sort_correct :
  forall signature variables arena owner node abstraction argument,
    arena_well_typed signature variables arena ->
    nth_error arena owner = Some node ->
    term_form node = SubstitutionTerm abstraction argument ->
    exists domain codomain arrow,
      In (arrow, domain, codomain) (signature_arrows signature) /\
      earlier owner abstraction /\
      term_has_sort arena abstraction arrow /\
      earlier owner argument /\
      term_has_sort arena argument domain /\
      term_sort node = codomain.
Proof.
  intros signature variables arena owner node abstraction argument
         Harena Hnode Hform.
  specialize (Harena owner node Hnode).
  unfold node_well_typed in Harena.
  rewrite Hform in Harena.
  exact (proj2 Harena).
Qed.

Inductive PremiseForm :=
| FreshnessPremise (variable target : VariableId) (remainder : bool)
| TransitionPremise (source target : VariableId)
| JudgmentPremise (variables : list VariableId)
| ForAllPremise
    (collection parameter : VariableId)
    (body : PremiseId)
| GuardPremise.

Record PremiseNode := {
  premise_form : PremiseForm
}.

Definition add_if_absent (value : nat) (values : list nat) : list nat :=
  if existsb (Nat.eqb value) values then values else values ++ [value].

Definition available_after_root
    (premises : list PremiseNode)
    (available : list VariableId)
    (root : PremiseId) : list VariableId :=
  match nth_error premises root with
  | Some premise =>
      match premise_form premise with
      | TransitionPremise _ target => add_if_absent target available
      | _ => available
      end
  | None => available
  end.

Theorem forall_root_does_not_extend_later_scope :
  forall premises available root collection parameter body,
    nth_error premises root =
      Some {| premise_form := ForAllPremise collection parameter body |} ->
    available_after_root premises available root = available.
Proof.
  intros premises available root collection parameter body Hroot.
  unfold available_after_root.
  now rewrite Hroot.
Qed.

Theorem transition_root_extends_later_scope :
  forall premises available root source target,
    nth_error premises root =
      Some {| premise_form := TransitionPremise source target |} ->
    available_after_root premises available root =
      add_if_absent target available.
Proof.
  intros premises available root source target Hroot.
  unfold available_after_root.
  now rewrite Hroot.
Qed.

(** Only top-level transition roots extend the scope of later roots.  A
    [ForAllPremise] parameter is absent here because it is visible only while
    its child is checked. *)
Fixpoint available_root_prefix
    (available : list VariableId)
    (premises : list PremiseNode)
    (roots : list PremiseId)
    (count : nat) : list VariableId :=
  match count, roots with
  | O, _ => available
  | S count', [] => available
  | S count', root :: rest =>
      available_root_prefix
        (available_after_root premises available root)
        premises
        rest
        count'
  end.

Definition premise_local_dependencies
    (premises : list PremiseNode)
    (allow_transition : bool)
    (scope : list VariableId)
    (premise : PremiseId) : Prop :=
  match nth_error premises premise with
  | None => False
  | Some node =>
    match premise_form node with
    | FreshnessPremise variable target _ =>
        In variable scope /\ In target scope
    | TransitionPremise source target =>
        allow_transition = true /\ In source scope /\ ~ In target scope
    | JudgmentPremise variables =>
        Forall (fun variable => In variable scope) variables
    | ForAllPremise collection parameter body =>
        In collection scope /\ ~ In parameter scope /\ body < premise
    | GuardPremise => True
    end
  end.

(** The inductive tree relation is the declarative counterpart of the Rust
    validator's explicit worklist.  It adds a quantified parameter only to the
    recursive child scope, never to a later root or to a rule RHS. *)
Inductive premise_tree_scoped
    (premises : list PremiseNode)
    (allow_transition : bool) :
    list VariableId -> PremiseId -> Prop :=
| ScopedFreshness : forall scope premise variable target remainder,
    nth_error premises premise =
      Some {| premise_form := FreshnessPremise variable target remainder |} ->
    premise_local_dependencies premises allow_transition scope premise ->
    premise_tree_scoped premises allow_transition scope premise
| ScopedTransition : forall scope premise source target,
    nth_error premises premise =
      Some {| premise_form := TransitionPremise source target |} ->
    premise_local_dependencies premises allow_transition scope premise ->
    premise_tree_scoped premises allow_transition scope premise
| ScopedJudgment : forall scope premise variables,
    nth_error premises premise =
      Some {| premise_form := JudgmentPremise variables |} ->
    premise_local_dependencies premises allow_transition scope premise ->
    premise_tree_scoped premises allow_transition scope premise
| ScopedForAll : forall scope premise collection parameter body,
    nth_error premises premise =
      Some {| premise_form := ForAllPremise collection parameter body |} ->
    premise_local_dependencies premises allow_transition scope premise ->
    premise_tree_scoped premises allow_transition (parameter :: scope) body ->
    premise_tree_scoped premises allow_transition scope premise
| ScopedGuard : forall scope premise,
    nth_error premises premise = Some {| premise_form := GuardPremise |} ->
    premise_tree_scoped premises allow_transition scope premise.

Definition root_premises_scoped
    (initial : list VariableId)
    (premises : list PremiseNode)
    (roots : list PremiseId)
    (allow_transition : bool) : Prop :=
  forall index root,
    nth_error roots index = Some root ->
    premise_tree_scoped
      premises
      allow_transition
      (available_root_prefix initial premises roots index)
      root.

Inductive premise_reachable_from
    (premises : list PremiseNode) : PremiseId -> PremiseId -> Prop :=
| ReachPremiseSelf : forall root,
    premise_reachable_from premises root root
| ReachPremiseForAll : forall root collection parameter body target,
    nth_error premises root =
      Some {| premise_form := ForAllPremise collection parameter body |} ->
    premise_reachable_from premises body target ->
    premise_reachable_from premises root target.

Definition all_premises_reachable
    (premises : list PremiseNode) (roots : list PremiseId) : Prop :=
  forall premise,
    premise < length premises ->
    exists root,
      In root roots /\ premise_reachable_from premises root premise.

Definition premise_roots_are_disjoint
    (premises : list PremiseNode) (roots : list PremiseId) : Prop :=
  NoDup roots /\
  forall target left right,
    In left roots ->
    In right roots ->
    premise_reachable_from premises left target ->
    premise_reachable_from premises right target ->
    left = right.

Definition variables_in_term_form (form : TermForm) : list VariableId :=
  match form with
  | VariableTerm variable => [variable]
  | AbstractionTerm binder _ => [binder]
  | CollectionTerm _ _ (Some remainder) => [remainder]
  | MapTerm _ parameters _ => parameters
  | ConstructorTerm _ _
  | SubstitutionTerm _ _
  | CollectionTerm _ _ None
  | ZipTerm _ _
  | LiteralTerm _ => []
  end.

Definition term_variables (arena : list TermNode) (root : TermId) : list VariableId :=
  match nth_error arena root with
  | Some node => variables_in_term_form (term_form node)
  | None => []
  end.

Record RuleArena := {
  rule_variables : list VariableDecl;
  rule_terms : list TermNode;
  rule_premises : list PremiseNode;
  rule_premise_roots : list PremiseId;
  rule_allows_transition : bool;
  rule_lhs : TermId;
  rule_rhs : TermId;
  rule_lhs_variables : list VariableId;
  rule_rhs_variables : list VariableId
}.

Record TheoryLimits := {
  max_rule_variables : nat;
  max_term_nodes : nat;
  max_premise_nodes : nat;
  max_output_nodes : nat;
  max_output_bytes : nat
}.

Definition positive_limits (limits : TheoryLimits) : Prop :=
  0 < max_rule_variables limits /\
  0 < max_term_nodes limits /\
  0 < max_premise_nodes limits /\
  0 < max_output_nodes limits /\
  0 < max_output_bytes limits.

Definition within_limits (limits : TheoryLimits) (rule : RuleArena) : Prop :=
  length (rule_variables rule) <= max_rule_variables limits /\
  length (rule_terms rule) <= max_term_nodes limits /\
  length (rule_premises rule) <= max_premise_nodes limits.

Definition initial_variable (rule : RuleArena) (variable : VariableId) : Prop :=
  In variable (rule_lhs_variables rule).

Definition final_available (rule : RuleArena) : list VariableId :=
  available_root_prefix
    (rule_lhs_variables rule)
    (rule_premises rule)
    (rule_premise_roots rule)
    (length (rule_premise_roots rule)).

Definition role_is_linear (role : VariableRole) : bool :=
  match role with
  | BoundVariable | RemainderVariable | DerivedVariable | QuantifiedVariable => true
  | InputVariable => false
  end.

Definition linear_variables_are_unique (rule : RuleArena) : Prop :=
  NoDup
    (filter
      (fun variable =>
         match nth_error (rule_variables rule) variable with
         | Some declaration => role_is_linear (variable_role declaration)
         | None => false
         end)
      (rule_lhs_variables rule ++ final_available rule)).

Definition rule_well_formed
    (signature : Signature) (limits : TheoryLimits) (rule : RuleArena) : Prop :=
  positive_limits limits /\
  within_limits limits rule /\
  arena_well_typed signature (rule_variables rule) (rule_terms rule) /\
  rule_lhs rule < length (rule_terms rule) /\
  rule_rhs rule < length (rule_terms rule) /\
  NoDup (rule_lhs_variables rule) /\
  root_premises_scoped
    (rule_lhs_variables rule)
    (rule_premises rule)
    (rule_premise_roots rule)
    (rule_allows_transition rule) /\
  all_premises_reachable (rule_premises rule) (rule_premise_roots rule) /\
  premise_roots_are_disjoint (rule_premises rule) (rule_premise_roots rule) /\
  Forall (fun variable => In variable (final_available rule)) (rule_rhs_variables rule) /\
  linear_variables_are_unique rule.

Theorem well_formed_rule_rhs_is_closed :
  forall signature limits rule variable,
    rule_well_formed signature limits rule ->
    In variable (rule_rhs_variables rule) ->
    In variable (final_available rule).
Proof.
  intros signature limits rule variable Hrule Hvariable.
  destruct Hrule as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hrhs _]]]]]]]]]].
  now apply Forall_forall with (x := variable) in Hrhs.
Qed.

Theorem scoped_transition_depends_only_on_available_input :
  forall premises allow_transition scope premise source target,
    premise_local_dependencies premises allow_transition scope premise ->
    nth_error premises premise =
      Some {| premise_form := TransitionPremise source target |} ->
    allow_transition = true /\ In source scope /\ ~ In target scope.
Proof.
  intros premises allow_transition scope premise source target
         Hdependencies Hpremise.
  unfold premise_local_dependencies in Hdependencies.
  now rewrite Hpremise in Hdependencies.
Qed.

Theorem well_formed_rule_respects_resource_bounds :
  forall signature limits rule,
    rule_well_formed signature limits rule ->
    length (rule_variables rule) <= max_rule_variables limits /\
    length (rule_terms rule) <= max_term_nodes limits /\
    length (rule_premises rule) <= max_premise_nodes limits.
Proof.
  intros signature limits rule Hrule.
  exact (proj1 (proj2 Hrule)).
Qed.

(** The structural codec has separately named source and wire records, making
    field omission observable rather than relying on definitional equality of
    one type. *)
Record RuleCore := {
  core_variables : list VariableDecl;
  core_terms : list TermNode;
  core_premises : list PremiseNode;
  core_lhs : TermId;
  core_rhs : TermId
}.

Record RuleValue := {
  value_variables : list VariableDecl;
  value_terms : list TermNode;
  value_premises : list PremiseNode;
  value_lhs : TermId;
  value_rhs : TermId
}.

Definition encode_rule (rule : RuleCore) : RuleValue :=
  {| value_variables := core_variables rule;
     value_terms := core_terms rule;
     value_premises := core_premises rule;
     value_lhs := core_lhs rule;
     value_rhs := core_rhs rule |}.

Definition decode_rule (value : RuleValue) : RuleCore :=
  {| core_variables := value_variables value;
     core_terms := value_terms value;
     core_premises := value_premises value;
     core_lhs := value_lhs value;
     core_rhs := value_rhs value |}.

Theorem rule_structural_codec_is_left_inverse :
  forall rule, decode_rule (encode_rule rule) = rule.
Proof.
  intros [variables terms premises lhs rhs].
  reflexivity.
Qed.

Inductive FingerprintPreimage :=
| GrammarFingerprintPreimage (payload : list nat)
| TheoryFingerprintPreimage (payload : list nat)
| LanguageFingerprintPreimage (payload : list nat).

Theorem fingerprint_domains_are_disjoint :
  forall grammar theory language,
    GrammarFingerprintPreimage grammar <> TheoryFingerprintPreimage theory /\
    TheoryFingerprintPreimage theory <> LanguageFingerprintPreimage language /\
    GrammarFingerprintPreimage grammar <> LanguageFingerprintPreimage language.
Proof.
  intros grammar theory language.
  repeat split; discriminate.
Qed.

End ExecutableTheoryCore.
