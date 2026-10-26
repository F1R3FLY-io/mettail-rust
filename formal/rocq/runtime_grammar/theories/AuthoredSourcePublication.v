(** Composition of completed source frames with the EXISTING collector.

    A frame witness contains source lookup, observed matching, an actual
    finite sequence in the completed-operation model, and RHS/grade
    construction observations. It does not contain the desired source-step
    conclusion. That conclusion is derived by AuthoredSourceExecution.

    The Rust-to-model projection, primitive observation refinement, and
    encoding adequacy remain explicit obligations. This theorem does not
    authenticate arbitrary witness records, assume hash injectivity, replay
    flat runtime receipts, or establish exhaustive successor enumeration.

    The first composition uses the older kernel envelope: its grade field
    retains bytes but has no cost-image fingerprint or grade sort. The second
    composition below reuses CheckedCostImage.publish_grade and exact source
    row admission to retain those fields. Its KernelMatch is constructed from
    the SAME completed frame, including its final environment. Interpreting
    that environment and source grade term in CheckedCostImage's multiset
    representation remains an explicit local refinement, not a coercion from
    arbitrary source values and not a second evaluator. *)

From Stdlib Require Import List.
From RuntimeGrammar Require Import AuthoredSourceExecution
  SemanticTransitionKernel SemanticPublicationProvenance CheckedCostImage
  CostSourceAdmission.
Import ListNotations.

Module AuthoredSourcePublication.
Module S := AuthoredSourceExecution.
Module K := SemanticTransitionKernel.
Module P := SemanticPublicationProvenance.
Module C := CheckedCostImage.
Module A := CostSourceAdmission.

Definition source_program_id (theory : S.SourceTheory) (reference : S.RuleReference) :=
  match reference with
  | S.EquationRef index S.Forward => 2 * index
  | S.EquationRef index S.Reverse => 2 * index + 1
  | S.RewriteRef index => 2 * length (S.source_equations theory) + index
  end.

Section Publication.
Context (meaning : S.PrimitiveMeaning) (observations : S.PrimitiveObservations).
Context (refinement : S.LocalRefinement meaning observations).
Context (encode_value : S.Value -> K.Commitment).

Definition encode_grade (grade : option S.Value) : K.ResourceEvidence :=
  match grade with
  | None => K.NoSemanticGrade
  | Some value => K.CheckedSemanticGrade (encode_value value)
  end.

Record CompletedSourceFrame (theory : S.SourceTheory) := {
  completed_reference : S.RuleReference;
  completed_rule : S.SourceRule;
  completed_activation : S.Activation;
  completed_input : S.Value;
  completed_initial : S.Environment;
  completed_final : S.Frame;
  completed_construction : S.CompletionObservation observations theory
    completed_rule completed_activation (S.frame_environment completed_final);
  completed_lookup : S.lookup_rule theory completed_reference = Some completed_rule;
  completed_match : S.match_observed observations theory
    (S.rule_arena completed_rule) completed_activation (S.rule_left completed_rule)
    completed_input completed_initial;
  completed_run : S.FrameRun meaning observations theory completed_reference
    completed_rule completed_activation
    (S.initial_frame completed_rule completed_initial) completed_final;
  completed_pending_empty : S.frame_pending completed_final = []
}.

Definition frame_output theory (frame : CompletedSourceFrame theory) :=
  S.completed_output observations _ _ _ _ (completed_construction theory frame).

Definition frame_grade theory (frame : CompletedSourceFrame theory) :=
  S.completed_grade observations _ _ _ _ (completed_construction theory frame).

Theorem completed_frame_establishes_source_derivation :
  forall theory (frame : CompletedSourceFrame theory),
    S.RuleDerivation meaning theory
      (completed_reference theory frame) (completed_activation theory frame)
      (completed_input theory frame) (completed_initial theory frame)
      (S.frame_environment (completed_final theory frame))
      (frame_output theory frame) (frame_grade theory frame).
Proof.
  intros theory frame. unfold frame_output, frame_grade.
  eapply S.successful_finite_completion_is_exact_source_derivation;
    eauto using completed_lookup, completed_match, completed_run, completed_pending_empty.
Qed.

Definition candidate_encodes_frame theory (frame : CompletedSourceFrame theory)
    (candidate : K.RuleCandidate) : Prop :=
  let transition := K.candidate_transition candidate in
  let receipt := K.candidate_receipt candidate in
  K.transition_rule transition = source_program_id theory (completed_reference theory frame) /\
  K.transition_input transition = encode_value (completed_input theory frame) /\
  K.transition_output transition = encode_value (frame_output theory frame) /\
  K.transition_grade transition = encode_grade (frame_grade theory frame) /\
  K.receipt_language receipt = S.owner_language (S.source_owner theory) /\
  K.receipt_theory receipt = S.owner_theory (S.source_owner theory) /\
  K.receipt_image receipt = S.owner_semantic_image (S.source_owner theory).

Definition published_source_derivation theory (result : K.ProvenTransition) : Prop :=
  exists reference activation input initial final output grade,
    S.RuleDerivation meaning theory reference activation input initial final output grade /\
    K.transition_rule (K.proven_transition result) = source_program_id theory reference /\
    K.transition_input (K.proven_transition result) = encode_value input /\
    K.transition_output (K.proven_transition result) = encode_value output /\
    K.transition_grade (K.proven_transition result) = encode_grade grade /\
    K.receipt_language (K.proven_receipt result) = S.owner_language (S.source_owner theory) /\
    K.receipt_theory (K.proven_receipt result) = S.owner_theory (S.source_owner theory) /\
    K.receipt_image (K.proven_receipt result) = S.owner_semantic_image (S.source_owner theory).

Theorem completed_frames_publish_only_their_source_derivations :
  forall theory manifest request fuel cancelled candidates results,
    (forall candidate, In candidate candidates ->
      exists frame : CompletedSourceFrame theory, candidate_encodes_frame theory frame candidate) ->
    K.successor_decision manifest request fuel cancelled candidates = K.Proven results ->
    forall result, In result results -> published_source_derivation theory result.
Proof.
  intros theory manifest request fuel cancelled candidates results
    Hframes Hdecision result Hin.
  destruct (P.proven_successor_has_exact_input_candidate manifest request fuel
    cancelled candidates results result Hdecision Hin)
    as [candidate [Hcandidate [Htransition Hreceipt]]].
  destruct (Hframes candidate Hcandidate) as [frame Hframe].
  unfold published_source_derivation.
  exists (completed_reference theory frame), (completed_activation theory frame),
    (completed_input theory frame), (completed_initial theory frame),
    (S.frame_environment (completed_final theory frame)),
    (frame_output theory frame), (frame_grade theory frame).
  split; [apply completed_frame_establishes_source_derivation |].
  rewrite Htransition, Hreceipt. exact Hframe.
Qed.

Theorem verified_completed_frame_has_source_derivation :
  forall theory manifest request fuel cancelled candidates target result,
    (forall candidate, In candidate candidates ->
      exists frame : CompletedSourceFrame theory, candidate_encodes_frame theory frame candidate) ->
    K.verify_transition manifest request fuel cancelled candidates target = K.Proven result ->
    published_source_derivation theory result.
Proof.
  intros theory manifest request fuel cancelled candidates target result Hframes Hverified.
  destruct (P.verified_output_has_exact_input_candidate manifest request fuel
    cancelled candidates target result Hverified)
    as [candidate [Hcandidate [Htransition Hreceipt]]].
  destruct (Hframes candidate Hcandidate) as [frame Hframe].
  unfold published_source_derivation.
  exists (completed_reference theory frame), (completed_activation theory frame),
    (completed_input theory frame), (completed_initial theory frame),
    (S.frame_environment (completed_final theory frame)),
    (frame_output theory frame), (frame_grade theory frame).
  split; [apply completed_frame_establishes_source_derivation |].
  rewrite Htransition, Hreceipt. exact Hframe.
Qed.

(** Only this projection supplies cost bindings. Its arguments are fixed by
    the completed source frame; no independent KernelMatch or substitution
    is accepted by the publication wrapper. The projection's representation
    adequacy is required explicitly below. *)
Section CheckedCostPublication.
Context (project_bindings : S.SourceTheory -> S.Arena -> S.Activation ->
  S.Environment -> list (C.VariableId * C.SignatureKey)).

Definition frame_final_bindings theory (frame : CompletedSourceFrame theory) :=
  project_bindings theory (S.rule_arena (completed_rule theory frame))
    (completed_activation theory frame)
    (S.frame_environment (completed_final theory frame)).

Definition completed_frame_cost_match theory (frame : CompletedSourceFrame theory)
    : option C.KernelMatch :=
  match S.owner_cost_image (S.source_owner theory) with
  | None => None
  | Some installed_cost =>
      Some {| C.match_language := S.owner_language (S.source_owner theory);
              C.match_theory := S.owner_theory (S.source_owner theory);
              C.match_semantic_image := S.owner_semantic_image (S.source_owner theory);
              C.match_installed_cost_image := installed_cost;
              C.match_rule := source_program_id theory (completed_reference theory frame);
              C.match_output := encode_value (frame_output theory frame);
              C.match_bindings := frame_final_bindings theory frame |}
  end.

Definition publish_completed_frame_grade theory (frame : CompletedSourceFrame theory)
    (image : C.CostImage) : option C.GradeReceipt :=
  match completed_frame_cost_match theory frame with
  | None => None
  | Some matched => C.publish_grade image matched
  end.

Definition frame_grade_publication_facts theory (frame : CompletedSourceFrame theory)
    (image : C.CostImage) (receipt : C.GradeReceipt) : Prop :=
  S.owner_cost_image (S.source_owner theory) = Some (C.receipt_cost_image receipt) /\
  C.receipt_language receipt = S.owner_language (S.source_owner theory) /\
  C.receipt_theory receipt = S.owner_theory (S.source_owner theory) /\
  C.receipt_semantic_image receipt = S.owner_semantic_image (S.source_owner theory) /\
  C.receipt_cost_image receipt = C.cost_fingerprint image /\
  C.receipt_rule receipt = source_program_id theory (completed_reference theory frame) /\
  C.receipt_output receipt = encode_value (frame_output theory frame) /\
  C.receipt_sort receipt = C.cost_grade_sort image /\
  S.RuleDerivation meaning theory
    (completed_reference theory frame) (completed_activation theory frame)
    (completed_input theory frame) (completed_initial theory frame)
    (S.frame_environment (completed_final theory frame))
    (frame_output theory frame) (frame_grade theory frame) /\
  exists row,
    C.find_cost_rule (source_program_id theory (completed_reference theory frame))
      (C.cost_rules image) = Some row /\
    C.evaluate_grade (frame_final_bindings theory frame) (C.cost_rule_grade row) =
      Some (C.receipt_grade receipt).

Theorem published_frame_grade_retains_owner_sort_and_final_environment :
  forall theory (frame : CompletedSourceFrame theory) image receipt,
    publish_completed_frame_grade theory frame image = Some receipt ->
    frame_grade_publication_facts theory frame image receipt.
Proof.
  intros theory frame image receipt Hpublish.
  unfold publish_completed_frame_grade, completed_frame_cost_match in Hpublish.
  destruct (S.owner_cost_image (S.source_owner theory)) as [installed_cost|]
    eqn:Hcost; [|discriminate].
  destruct (C.published_grade_is_exactly_the_matched_rule_grade _ _ _ Hpublish)
    as [Hlanguage [Htheory [Hsemantic [Himage
      [Hrlanguage [Hrtheory [Hrsemantic [Hrcost [Houtput [Hsort
        [row [Hrow [Hgrade Hrule]]]]]]]]]]]]].
  change (C.cost_language image = S.owner_language (S.source_owner theory)) in Hlanguage.
  change (C.cost_theory image = S.owner_theory (S.source_owner theory)) in Htheory.
  change (C.cost_semantic_image image = S.owner_semantic_image (S.source_owner theory))
    in Hsemantic.
  change (C.cost_fingerprint image = installed_cost) in Himage.
  change (C.receipt_output receipt = encode_value (frame_output theory frame)) in Houtput.
  change (C.find_cost_rule (source_program_id theory (completed_reference theory frame))
    (C.cost_rules image) = Some row) in Hrow.
  change (C.evaluate_grade (frame_final_bindings theory frame) (C.cost_rule_grade row) =
    Some (C.receipt_grade receipt)) in Hgrade.
  change (C.receipt_rule receipt = source_program_id theory (completed_reference theory frame))
    in Hrule.
  unfold frame_grade_publication_facts.
  split; [rewrite Hrcost, Himage; exact Hcost|].
  split; [rewrite Hrlanguage; exact Hlanguage|].
  split; [rewrite Hrtheory; exact Htheory|].
  split; [rewrite Hrsemantic; exact Hsemantic|].
  split; [exact Hrcost|].
  split; [exact Hrule|].
  split; [exact Houtput|].
  split; [exact Hsort|].
  split; [apply completed_frame_establishes_source_derivation|].
  exists row. split; assumption.
Qed.

(** These two relations distinguish a source arena expression and value from
    the existing multiset grade abstraction. They are NOT defined by copying
    its evaluator. The local refinement says that interpretation commutes
    with an actual source instantiation and the existing grade evaluation at
    the same activation/environment. No global faithfulness is required. *)
Context (source_grade_expression : S.SourceTheory -> S.Arena -> S.Core.TermId ->
  S.Core.SortId -> C.GradeExpr -> Prop).
Context (grade_value_represents : S.Core.SortId -> S.Value -> C.Grade -> Prop).
Context (grade_representation_refines :
  forall theory arena activation root sort environment value expression grade,
    source_grade_expression theory arena root sort expression ->
    S.term_instantiates meaning theory arena activation root environment value ->
    C.evaluate_grade (project_bindings theory arena activation environment) expression =
      Some grade ->
    grade_value_represents sort value grade).

(** This record binds existing row admission to the actual completed source
    rewrite/root. SourceRule has no name field; the source-name component of
    the program view therefore still requires the existing authentic source
    projection. The explicit arena-interpretation premise is confined to the
    selected declared root, not all terms or all possible valuations. *)
Record FrameCostRowAdmission theory (frame : CompletedSourceFrame theory)
    (image : C.CostImage) := {
  frame_cost_source_index : nat;
  frame_cost_source : A.SourceGradeDeclaration;
  frame_cost_program : A.CostProgramView;
  frame_cost_row : A.CostRowReference;
  frame_cost_compiled : C.CostRule;
  frame_cost_reference : completed_reference theory frame =
    S.RewriteRef frame_cost_source_index;
  frame_cost_declared_root : S.rule_grade (completed_rule theory frame) =
    Some (A.source_grade_root frame_cost_source);
  frame_cost_row_admitted : A.admit_source_row (length (S.source_equations theory))
    frame_cost_source_index (C.cost_grade_sort image) frame_cost_source
    frame_cost_program frame_cost_row = Some frame_cost_compiled;
  frame_cost_row_selected : C.find_cost_rule
    (source_program_id theory (completed_reference theory frame)) (C.cost_rules image) =
    Some frame_cost_compiled;
  frame_cost_root_typed : exists node,
    nth_error (S.terms (S.rule_arena (completed_rule theory frame)))
      (A.source_grade_root frame_cost_source) = Some node /\
    S.node_sort node = C.cost_grade_sort image;
  frame_cost_expression_refines : forall expression,
    nth_error (A.program_grade_arena frame_cost_program)
      (A.source_grade_root frame_cost_source) = Some (C.cost_grade_sort image, expression) ->
    source_grade_expression theory (S.rule_arena (completed_rule theory frame))
      (A.source_grade_root frame_cost_source) (C.cost_grade_sort image) expression
}.

Definition frame_grade_interpretation theory (frame : CompletedSourceFrame theory)
    (image : C.CostImage) (receipt : C.GradeReceipt) : Prop :=
  exists root node value expression,
    S.rule_grade (completed_rule theory frame) = Some root /\
    nth_error (S.terms (S.rule_arena (completed_rule theory frame))) root = Some node /\
    S.node_sort node = C.receipt_sort receipt /\
    frame_grade theory frame = Some value /\
    source_grade_expression theory (S.rule_arena (completed_rule theory frame))
      root (C.cost_grade_sort image) expression /\
    S.term_instantiates meaning theory (S.rule_arena (completed_rule theory frame))
      (completed_activation theory frame) root
      (S.frame_environment (completed_final theory frame)) value /\
    C.evaluate_grade (frame_final_bindings theory frame) expression =
      Some (C.receipt_grade receipt) /\
    grade_value_represents (C.receipt_sort receipt) value (C.receipt_grade receipt).

Theorem admitted_frame_grade_has_exact_source_interpretation :
  forall theory (frame : CompletedSourceFrame theory) image
    (admission : FrameCostRowAdmission theory frame image) receipt,
    publish_completed_frame_grade theory frame image = Some receipt ->
    frame_grade_publication_facts theory frame image receipt /\
    frame_grade_interpretation theory frame image receipt.
Proof.
  intros theory frame image admission receipt Hpublish.
  split.
  - now apply published_frame_grade_retains_owner_sort_and_final_environment.
  - destruct admission as [index source program row compiled Hreference Hroot
      Hadmit Hselected [node [Hnode Hnode_sort]] Hexpression].
    unfold publish_completed_frame_grade, completed_frame_cost_match in Hpublish.
    destruct (S.owner_cost_image (S.source_owner theory)) as [installed_cost|]
      eqn:Hcost; [|discriminate].
    destruct (A.admitted_source_row_composes_with_existing_grade_publication
      (length (S.source_equations theory)) index (C.cost_grade_sort image)
      source program row compiled image
      {| C.match_language := S.owner_language (S.source_owner theory);
         C.match_theory := S.owner_theory (S.source_owner theory);
         C.match_semantic_image := S.owner_semantic_image (S.source_owner theory);
         C.match_installed_cost_image := installed_cost;
         C.match_rule := source_program_id theory (completed_reference theory frame);
         C.match_output := encode_value (frame_output theory frame);
         C.match_bindings := frame_final_bindings theory frame |}
      receipt Hadmit Hselected eq_refl Hpublish)
      as [_ [_ [_ [_ [Hsort [expression [Hterm Heval]]]]]]].
    change (C.evaluate_grade (frame_final_bindings theory frame) expression =
      Some (C.receipt_grade receipt)) in Heval.
    pose proof (S.completed_grade_refines meaning observations refinement
      theory (completed_rule theory frame) (completed_activation theory frame)
      (S.frame_environment (completed_final theory frame))
      (completed_construction theory frame)) as Hgrade.
    change (S.GradeInstantiation meaning theory (S.rule_arena (completed_rule theory frame))
      (completed_activation theory frame) (S.frame_environment (completed_final theory frame))
      (S.rule_grade (completed_rule theory frame)) (frame_grade theory frame)) in Hgrade.
    rewrite Hroot in Hgrade.
    destruct (frame_grade theory frame) as [value|] eqn:Hvalue; [|inversion Hgrade].
    pose proof (S.completion_uses_one_final_substitution meaning observations refinement
      theory (completed_rule theory frame) (completed_activation theory frame)
      (S.frame_environment (completed_final theory frame))
      (completed_construction theory frame) (A.source_grade_root source) value Hroot Hvalue)
      as [Hrhs Hinstantiation].
    specialize (Hexpression expression Hterm).
    unfold frame_grade_interpretation.
    exists (A.source_grade_root source), node, value, expression.
    split; [exact Hroot|].
    split; [exact Hnode|].
    split; [rewrite Hsort; exact Hnode_sort|].
    split; [exact Hvalue|].
    split; [exact Hexpression|].
    split; [exact Hinstantiation|].
    split; [exact Heval|].
    rewrite Hsort.
    exact (grade_representation_refines theory (S.rule_arena (completed_rule theory frame))
      (completed_activation theory frame) (A.source_grade_root source) (C.cost_grade_sort image)
      (S.frame_environment (completed_final theory frame)) value expression
      (C.receipt_grade receipt) Hexpression Hinstantiation Heval).
Qed.

(** The grade receipt is not smuggled into the older K.ResourceEvidence.
    This transport retains it alongside the exact source frame and published
    pair, and explicitly links its rule/output and the source grade value.
    The two representations need not have equal byte encodings. *)
Theorem completed_cost_frames_publish_source_and_checked_grade :
  forall theory image manifest request fuel cancelled candidates results,
    (forall candidate, In candidate candidates ->
      exists (frame : CompletedSourceFrame theory)
        (admission : FrameCostRowAdmission theory frame image) receipt,
        candidate_encodes_frame theory frame candidate /\
        publish_completed_frame_grade theory frame image = Some receipt) ->
    K.successor_decision manifest request fuel cancelled candidates = K.Proven results ->
    forall result, In result results ->
      exists (frame : CompletedSourceFrame theory) receipt,
        K.transition_rule (K.proven_transition result) = C.receipt_rule receipt /\
        K.transition_input (K.proven_transition result) =
          encode_value (completed_input theory frame) /\
        K.transition_output (K.proven_transition result) = C.receipt_output receipt /\
        K.transition_grade (K.proven_transition result) = encode_grade (frame_grade theory frame) /\
        K.receipt_language (K.proven_receipt result) = C.receipt_language receipt /\
        K.receipt_theory (K.proven_receipt result) = C.receipt_theory receipt /\
        K.receipt_image (K.proven_receipt result) = C.receipt_semantic_image receipt /\
        frame_grade_publication_facts theory frame image receipt /\
        frame_grade_interpretation theory frame image receipt.
Proof.
  intros theory image manifest request fuel cancelled candidates results
    Hframes Hdecision result Hin.
  destruct (P.proven_successor_has_exact_input_candidate manifest request fuel
    cancelled candidates results result Hdecision Hin)
    as [candidate [Hcandidate [Htransition Hreceipt]]].
  destruct (Hframes candidate Hcandidate) as [frame [admission [receipt [Hframe Hpublish]]]].
  destruct (admitted_frame_grade_has_exact_source_interpretation
    theory frame image admission receipt Hpublish) as [Hfacts Hinterpretation].
  pose proof Hfacts as [_ [Hlanguage [Htheory [Hsemantic [_ [Hrule [Houtput _]]]]]]].
  unfold candidate_encodes_frame in Hframe.
  destruct Hframe as [Hcandidate_rule [Hcandidate_input [Hcandidate_output [Hcandidate_grade
    [Hcandidate_language [Hcandidate_theory Hcandidate_image]]]]]].
  exists frame, receipt. rewrite Htransition, Hreceipt.
  split; [rewrite Hcandidate_rule; symmetry; exact Hrule|].
  split; [exact Hcandidate_input|].
  split; [rewrite Hcandidate_output; symmetry; exact Houtput|].
  split; [exact Hcandidate_grade|].
  split; [rewrite Hcandidate_language; symmetry; exact Hlanguage|].
  split; [rewrite Hcandidate_theory; symmetry; exact Htheory|].
  split; [rewrite Hcandidate_image; symmetry; exact Hsemantic|].
  split; assumption.
Qed.

End CheckedCostPublication.

End Publication.

Print Assumptions completed_frame_establishes_source_derivation.
Print Assumptions completed_frames_publish_only_their_source_derivations.
Print Assumptions verified_completed_frame_has_source_derivation.
Print Assumptions published_frame_grade_retains_owner_sort_and_final_environment.
Print Assumptions admitted_frame_grade_has_exact_source_interpretation.
Print Assumptions completed_cost_frames_publish_source_and_checked_grade.

End AuthoredSourcePublication.
