(**
  ExecutableTheoryImage: sound compilation of admitted GSLT rules to a flat,
  authority-free runtime image.

  The source contract is [ExecutableTheoryCore].  Compilation resolves names
  before this boundary, retains dense numeric sort/constructor/variable
  identities, normalizes every non-variable term to a closed machine operator,
  and preserves the source arena's backward references exactly.  Consequently
  the runtime matcher and RHS builder can be iterative: they never chase a
  forward term edge or depend on the native call stack.

  Premises remain structured data rather than general bytecode.  A finite
  block contains freshness, transition, judgment, forall, or guard operations;
  forall is the only nested continuation and its body already precedes its
  parent in the source arena.  Images carry resource demands and fingerprints,
  but no capabilities or authority grants.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From RuntimeGrammar Require Import ExecutableTheoryCore.

Import ListNotations.

Module ExecutableTheoryImage.

Import ExecutableTheoryCore.

Inductive StructuralOperator :=
| ConstructorOperator (constructor : ConstructorId)
| AbstractionOperator (sort : SortId)
| SubstitutionOperator (sort : SortId)
| CollectionOperator (sort element : SortId)
| MapOperator (sort : SortId)
| ZipOperator (sort : SortId)
| LiteralOperator (sort : SortId) (canonical_payload : nat).

Inductive ImageTermForm :=
| BindSlot (variable : VariableId)
| ApplyOperator
    (operator : StructuralOperator)
    (arguments : list TermId)
    (slots : list VariableId)
    (remainder : option VariableId).

Definition compile_term_form (sort : SortId) (form : TermForm) : ImageTermForm :=
  match form with
  | VariableTerm variable => BindSlot variable
  | ConstructorTerm constructor arguments =>
      ApplyOperator (ConstructorOperator constructor) arguments [] None
  | AbstractionTerm binder body =>
      ApplyOperator (AbstractionOperator sort) [body] [binder] None
  | SubstitutionTerm abstraction argument =>
      ApplyOperator (SubstitutionOperator sort) [abstraction; argument] [] None
  | CollectionTerm element elements remainder =>
      ApplyOperator (CollectionOperator sort element) elements [] remainder
  | MapTerm collection parameters body =>
      ApplyOperator (MapOperator sort) [collection; body] parameters None
  | ZipTerm first second =>
      ApplyOperator (ZipOperator sort) [first; second] [] None
  | LiteralTerm payload =>
      ApplyOperator (LiteralOperator sort payload) [] [] None
  end.

Definition source_term_references (form : TermForm) : list TermId :=
  match form with
  | VariableTerm _ | LiteralTerm _ => []
  | ConstructorTerm _ arguments => arguments
  | AbstractionTerm _ body => [body]
  | SubstitutionTerm abstraction argument => [abstraction; argument]
  | CollectionTerm _ elements _ => elements
  | MapTerm collection _ body => [collection; body]
  | ZipTerm first second => [first; second]
  end.

Definition image_term_references (form : ImageTermForm) : list TermId :=
  match form with
  | BindSlot _ => []
  | ApplyOperator _ arguments _ _ => arguments
  end.

Definition source_term_slots (form : TermForm) : list VariableId :=
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

Definition image_term_slots (form : ImageTermForm) : list VariableId :=
  match form with
  | BindSlot variable => [variable]
  | ApplyOperator _ _ slots (Some remainder) => slots ++ [remainder]
  | ApplyOperator _ _ slots None => slots
  end.

Theorem compile_term_references_exact :
  forall sort form,
    image_term_references (compile_term_form sort form) =
    source_term_references form.
Proof.
  intros sort form.
  destruct form; reflexivity.
Qed.

Theorem compile_term_slots_exact :
  forall sort form,
    image_term_slots (compile_term_form sort form) = source_term_slots form.
Proof.
  intros sort form.
  destruct form; reflexivity.
Qed.

Record ImageTermNode := {
  image_term_sort : SortId;
  image_term_form : ImageTermForm
}.

Definition compile_term_node (node : TermNode) : ImageTermNode :=
  {| image_term_sort := term_sort node;
     image_term_form := compile_term_form (term_sort node) (term_form node) |}.

Definition image_arena (arena : list TermNode) : list ImageTermNode :=
  map compile_term_node arena.

Definition image_arena_references_backward (arena : list ImageTermNode) : Prop :=
  forall owner node,
    nth_error arena owner = Some node ->
    Forall (earlier owner) (image_term_references (image_term_form node)).

Lemma nth_error_image_arena :
  forall arena owner node,
    nth_error arena owner = Some node ->
    nth_error (image_arena arena) owner = Some (compile_term_node node).
Proof.
  intros arena owner node Hnode.
  unfold image_arena.
  rewrite nth_error_map.
  now rewrite Hnode.
Qed.

Lemma nth_error_image_arena_inv :
  forall arena owner image_node,
    nth_error (image_arena arena) owner = Some image_node ->
    exists source_node,
      nth_error arena owner = Some source_node /\
      compile_term_node source_node = image_node.
Proof.
  unfold image_arena.
  induction arena as [|source_node rest IH];
    intros [|owner] image_node Himage; simpl in Himage; try discriminate.
  - inversion Himage; subst image_node.
    exists source_node.
    split; reflexivity.
  - apply IH in Himage.
    destruct Himage as [node [Hnode Hcompile]].
    exists node.
    split; assumption.
Qed.

Theorem well_typed_source_compiles_to_backward_image :
  forall signature variables arena,
    arena_well_typed signature variables arena ->
    image_arena_references_backward (image_arena arena).
Proof.
  intros signature variables arena Htyped owner image_node Himage.
  apply nth_error_image_arena_inv in Himage.
  destruct Himage as [source_node [Hsource Hcompile]].
  subst image_node.
  unfold compile_term_node; simpl.
  rewrite compile_term_references_exact.
  specialize (Htyped owner source_node Hsource).
  unfold node_well_typed in Htyped.
  destruct Htyped as [_ Hform].
  destruct (term_form source_node); simpl in *.
  - constructor.
  - destruct Hform as [declaration [_ [_ [Hreferences _]]]].
    exact Hreferences.
  - destruct Hform as [domain [codomain [_ [_ [Hbody _]]]]].
    constructor; [exact Hbody | constructor].
  - destruct Hform as
        [domain [codomain [arrow [_ [Habstraction [_ [Hargument _]]]]]]].
    constructor; [exact Habstraction | constructor; [exact Hargument | constructor]].
  - destruct Hform as [_ [_ [Hreferences _]]].
    exact Hreferences.
  - destruct Hform as [Hcollection [Hbody _]].
    constructor; [exact Hcollection | constructor; [exact Hbody | constructor]].
  - destruct Hform as [Hfirst Hsecond].
    constructor; [exact Hfirst | constructor; [exact Hsecond | constructor]].
  - constructor.
Qed.

Inductive PremiseOperation :=
| CheckFreshness (variable target : VariableId) (remainder : bool)
| DeriveTransition (source target : VariableId)
| InvokeJudgment (variables : list VariableId)
| IterateForAll
    (collection parameter : VariableId)
    (body : PremiseId)
| CheckGuard.

Definition compile_premise_form (form : PremiseForm) : PremiseOperation :=
  match form with
  | FreshnessPremise variable target remainder =>
      CheckFreshness variable target remainder
  | TransitionPremise source target => DeriveTransition source target
  | JudgmentPremise variables => InvokeJudgment variables
  | ForAllPremise collection parameter body =>
      IterateForAll collection parameter body
  | GuardPremise => CheckGuard
  end.

Definition premise_child (form : PremiseForm) : option PremiseId :=
  match form with
  | ForAllPremise _ _ body => Some body
  | _ => None
  end.

Definition operation_child (operation : PremiseOperation) : option PremiseId :=
  match operation with
  | IterateForAll _ _ body => Some body
  | _ => None
  end.

Theorem compile_premise_continuation_exact :
  forall form,
    operation_child (compile_premise_form form) = premise_child form.
Proof.
  intros form.
  destruct form; reflexivity.
Qed.

Record RuleProgram := {
  program_variables : list VariableDecl;
  program_terms : list ImageTermNode;
  program_premises : list PremiseOperation;
  program_premise_roots : list PremiseId;
  program_lhs : TermId;
  program_rhs : TermId;
  program_lhs_variables : list VariableId;
  program_rhs_variables : list VariableId
}.

Definition compile_rule_program (rule : RuleArena) : RuleProgram :=
  {| program_variables := rule_variables rule;
     program_terms := image_arena (rule_terms rule);
     program_premises := map (fun premise =>
       compile_premise_form (premise_form premise)) (rule_premises rule);
     program_premise_roots := rule_premise_roots rule;
     program_lhs := rule_lhs rule;
     program_rhs := rule_rhs rule;
     program_lhs_variables := rule_lhs_variables rule;
     program_rhs_variables := rule_rhs_variables rule |}.

Definition pair_id_eqb (left right : TermId * TermId) : bool :=
  andb (Nat.eqb (fst left) (fst right)) (Nat.eqb (snd left) (snd right)).

Fixpoint nat_list_eqb (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | left_head :: left_tail, right_head :: right_tail =>
      andb (Nat.eqb left_head right_head) (nat_list_eqb left_tail right_tail)
  | _, _ => false
  end.

Definition nat_option_eqb (left right : option nat) : bool :=
  match left, right with
  | None, None => true
  | Some left_value, Some right_value => Nat.eqb left_value right_value
  | _, _ => false
  end.

(** The executable comparison uses an explicit worklist and a memoized set of
    already-checked term pairs. Equal identifiers are only a fast path:
    distinct arena nodes with the same canonical payload and recursively equal
    children compare equal. Rocq recursion is solely over a numeric transition
    budget; the source term depth never consumes the proof compiler's stack. *)
Fixpoint structural_equal_work
    (fuel : nat)
    (arena : list TermNode)
    (pending seen : list (TermId * TermId)) : bool :=
  match fuel with
  | 0 => false
  | S remaining =>
      match pending with
      | [] => true
      | (left_id, right_id) :: rest =>
          if existsb (pair_id_eqb (left_id, right_id)) seen then
            structural_equal_work remaining arena rest seen
          else
            match nth_error arena left_id, nth_error arena right_id with
            | Some left_node, Some right_node =>
                if Nat.eqb (term_sort left_node) (term_sort right_node) then
                  let next_seen := (left_id, right_id) :: seen in
                  match term_form left_node, term_form right_node with
                  | VariableTerm left_variable, VariableTerm right_variable =>
                      if Nat.eqb left_variable right_variable then
                        structural_equal_work remaining arena rest next_seen
                      else false
                  | ConstructorTerm left_constructor left_arguments,
                    ConstructorTerm right_constructor right_arguments =>
                      if andb (Nat.eqb left_constructor right_constructor)
                         (Nat.eqb (length left_arguments) (length right_arguments))
                      then structural_equal_work remaining arena
                             (combine left_arguments right_arguments ++ rest)
                             next_seen
                      else false
                  | AbstractionTerm left_binder left_body,
                    AbstractionTerm right_binder right_body =>
                      if Nat.eqb left_binder right_binder then
                        structural_equal_work remaining arena
                          ((left_body, right_body) :: rest) next_seen
                      else false
                  | SubstitutionTerm left_abstraction left_argument,
                    SubstitutionTerm right_abstraction right_argument =>
                      structural_equal_work remaining arena
                        ((left_abstraction, right_abstraction) ::
                         (left_argument, right_argument) :: rest) next_seen
                  | CollectionTerm left_element left_elements left_remainder,
                    CollectionTerm right_element right_elements right_remainder =>
                      if andb (Nat.eqb left_element right_element)
                         (andb (nat_option_eqb left_remainder right_remainder)
                           (Nat.eqb (length left_elements) (length right_elements)))
                      then structural_equal_work remaining arena
                             (combine left_elements right_elements ++ rest)
                             next_seen
                      else false
                  | MapTerm left_collection left_parameters left_body,
                    MapTerm right_collection right_parameters right_body =>
                      if nat_list_eqb left_parameters right_parameters then
                        structural_equal_work remaining arena
                          ((left_collection, right_collection) ::
                           (left_body, right_body) :: rest) next_seen
                      else false
                  | ZipTerm left_first left_second,
                    ZipTerm right_first right_second =>
                      structural_equal_work remaining arena
                        ((left_first, right_first) ::
                         (left_second, right_second) :: rest) next_seen
                  | LiteralTerm left_payload, LiteralTerm right_payload =>
                      if Nat.eqb left_payload right_payload then
                        structural_equal_work remaining arena rest next_seen
                      else false
                  | _, _ => false
                  end
                else false
            | _, _ => false
            end
      end
  end.

Definition structural_comparison_budget (arena : list TermNode) : nat :=
  let size := length arena in S (size * size * S size).

Definition structurally_equalb (rule : RuleArena) : bool :=
  structural_equal_work
    (structural_comparison_budget (rule_terms rule))
    (rule_terms rule)
    [(rule_lhs rule, rule_rhs rule)]
    [].

Definition rule_progresses (rule : RuleArena) : Prop :=
  structurally_equalb rule = false.

Definition compile_progressing_rule (rule : RuleArena) : option RuleProgram :=
  if structurally_equalb rule
  then None
  else Some (compile_rule_program rule).

Theorem compiled_rule_progresses :
  forall rule program,
    compile_progressing_rule rule = Some program ->
    rule_progresses rule.
Proof.
  intros rule program Hcompile.
  unfold compile_progressing_rule in Hcompile.
  destruct (structurally_equalb rule) eqn:Hequal;
    try discriminate.
  exact Hequal.
Qed.

Theorem compiled_rule_preserves_bounds :
  forall signature limits rule program,
    rule_well_formed signature limits rule ->
    compile_progressing_rule rule = Some program ->
    length (program_variables program) <= max_rule_variables limits /\
    length (program_terms program) <= max_term_nodes limits /\
    length (program_premises program) <= max_premise_nodes limits.
Proof.
  intros signature limits rule program Hwell Hcompile.
  unfold compile_progressing_rule in Hcompile.
  destruct (structurally_equalb rule); try discriminate.
  inversion Hcompile; subst program; clear Hcompile.
  unfold compile_rule_program, image_arena; simpl.
  repeat rewrite length_map.
  now apply well_formed_rule_respects_resource_bounds with (signature := signature).
Qed.

Theorem compiled_rhs_slots_are_available :
  forall signature limits rule program variable,
    rule_well_formed signature limits rule ->
    compile_progressing_rule rule = Some program ->
    In variable (program_rhs_variables program) ->
    In variable (final_available rule).
Proof.
  intros signature limits rule program variable Hwell Hcompile Hin.
  unfold compile_progressing_rule in Hcompile.
  destruct (structurally_equalb rule); try discriminate.
  inversion Hcompile; subst program; clear Hcompile.
  simpl in Hin.
  now apply well_formed_rule_rhs_is_closed with
    (signature := signature) (limits := limits) (rule := rule).
Qed.

Record ResourceCharge := {
  charged_pattern_nodes : nat;
  charged_template_nodes : nat;
  charged_premise_nodes : nat
}.

Definition compile_charge (rule : RuleArena) : ResourceCharge :=
  {| charged_pattern_nodes := length (rule_terms rule);
     charged_template_nodes := length (rule_terms rule);
     charged_premise_nodes := length (rule_premises rule) |}.

Theorem compile_charge_is_exact :
  forall rule,
    charged_pattern_nodes (compile_charge rule) = length (rule_terms rule) /\
    charged_template_nodes (compile_charge rule) = length (rule_terms rule) /\
    charged_premise_nodes (compile_charge rule) = length (rule_premises rule).
Proof.
  intros rule.
  repeat split; reflexivity.
Qed.

(** An image records demands only.  Authority is supplied independently by an
    installed handle and therefore cannot be reconstructed from image bytes. *)
Record TheoryImage := {
  image_language_fingerprint : list nat;
  image_theory_fingerprint : list nat;
  image_programs : list RuleProgram;
  image_charges : list ResourceCharge
}.

Definition image_authority (_ : TheoryImage) : list nat := [].

Theorem compiled_image_carries_no_authority :
  forall image, image_authority image = [].
Proof.
  reflexivity.
Qed.

Inductive ImageFingerprintPreimage :=
| ParserImageFingerprint (payload : list nat)
| SemanticTermFingerprint (payload : list nat)
| TheoryImageFingerprint (payload : list nat).

Theorem theory_image_fingerprint_domain_is_disjoint :
  forall parser term theory,
    ParserImageFingerprint parser <> TheoryImageFingerprint theory /\
    SemanticTermFingerprint term <> TheoryImageFingerprint theory.
Proof.
  intros parser term theory.
  split; discriminate.
Qed.

End ExecutableTheoryImage.
