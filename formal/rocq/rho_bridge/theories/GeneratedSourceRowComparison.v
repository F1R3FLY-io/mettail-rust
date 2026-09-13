(** Original row construction and consultation of its borrowed task batches.

    Source: iterative_cmp.rs cmp_arm_stmts, cmp_collection_push_stmts,
    generate_cmp_binder_arm and generate_cmp_multi_binder_arm; the paired Vec
    iterator is left.iter().zip(right.iter()).rev() in collection_walk.rs.
    Native results are computed at their ORIGINAL construction sites. Eager
    leaves stop immediately on a decisive result. Otherwise the scope group
    is constructed first, then the remaining fields in reverse order. The
    resulting task words are popped in forward field order. A scope pushes
    body then pattern verdict; a Vec pushes length then reversed common-prefix
    pairs. None/None has no task. A Map Box is created before its Start task,
    but no Map comparison is performed by construction.

    Term is the existing immutable typed source borrow, not a new source AST.
    The source telescope comes from GeneratedConstructorSourceProjection.
    lookup interprets an original generated task's typed pointer pair; it
    contains no comparison result and does not change during execution.
    State interprets the original Box payloads. make_map_box is the concrete
    constructor/typed-roster association boundary, NOT a Map result premise.
    No owner registry or new allocation representation is defined here.

    The current file constructs the actual source arm/group witnesses and
    proves consultation for non-Map borrowed batches using actual child
    traversals and the lower-height induction hypothesis. The latter ranges
    over arbitrary original operand pairs, not just opposite root rosters.
    Native Map raw-resume/Box association and its proved whole segment must be
    supplied by GeneratedMapCoreSource before extending the batch theorem to
    Start/Resume. There is deliberately no assumed MapResult or root factor.
    The actual census/enum projection must also bind these typed telescopes,
    source positions and scope boundaries to the original match arms. This
    is not claimed merely from having an abstract observer.

    Admission/cleanup erasure remains in the existing checked source models.
    In particular an untouched task frame does not itself prove arbitrary
    State preservation: the original Box-in-task move discipline must retain
    parked owners during child execution. No native call or allocation cost
    is inferred from the mathematical task/result lists below. *)
From Stdlib Require Import List Arith.PeanoNat Bool.
From RhoBridge Require Import GeneratedConstructorComparisonClasses
  GeneratedConstructorSourceProjection GeneratedChildTraversal
  GeneratedComparisonFieldResults AdmittedGeneratedComparisonScheduling
  AdmittedGeneratedCollectionScheduling AdmittedGeneratedHashScheduling.
Import ListNotations.
Import GeneratedConstructorComparisonClasses.GeneratedConstructorComparisonClasses.
Import GeneratedConstructorSourceProjection.GeneratedConstructorSourceProjection.
Import GeneratedChildTraversal.GeneratedChildTraversal.
Import GeneratedComparisonFieldResults.GeneratedComparisonFieldResults.

Module GeneratedSourceRowComparison.

Local Notation Task := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Task.
Local Notation Observation := AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Observation.
Local Notation Position := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.Position.

Definition child_task position : Task :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Borrowed
    (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.CategoryPair position).
Definition verdict_task position result : Task :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Borrowed
    (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.PrecomputedVerdict position result).
Definition native_cmp_observation position result : Observation :=
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Native
    (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.NativeCmp position result).
Definition native_cmp_results events := flat_map (fun event => match event with
  | AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Native
      (AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.NativeCmp _ result) => [result]
  | _ => [] end) events.

Definition plain_field {Cat : Type} (base : @BaseField Cat) : @Field Cat :=
  {| field_base := base; field_optional := false |}.
Definition optional_field {Cat : Type} (base : @BaseField Cat) : @Field Cat :=
  {| field_base := base; field_optional := true |}.
Definition stack_expressible {Cat : Type} (field : @Field Cat) :=
  match field_base field with Native _ => false | _ => true end.
Definition optional_base_admitted {Cat : Type} (base : @BaseField Cat) : Prop :=
  match base with Native _ => False | _ => True end.
Definition pattern_atom (multi : bool) := if multi then MultiPattern else SinglePattern.

Section OriginalConstruction.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable State : Type.
Variables uid_digest binder_digest : nat -> nat.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Definition pair_at category position left right :=
  lookup position = Some (existT _ category (left, right)).

(** The created Box owns only the original paid rosters and native machine.
    This interface describes creation/move, never a comparison outcome. *)
Variable make_map_box : forall category,
  list (Term category * Term category) -> list (Term category * Term category) ->
  State -> nat -> nat -> State -> Prop.
Variable field_position : nat -> Position.

Inductive BaseConstruction : forall base : @BaseField Cat,
    source_base_type Term base -> source_base_type Term base ->
    Position -> State -> list Task -> list Observation -> State -> Prop :=
| ConstructNative : forall atom left right position state,
    BaseConstruction (Native atom) left right position state
      [verdict_task position (atom_source_compare uid_digest binder_digest atom left right)]
      [native_cmp_observation position (atom_source_compare uid_digest binder_digest atom left right)] state
| ConstructChild : forall category left right position state,
    pair_at category position left right ->
    BaseConstruction (Child category) left right position state [child_task position] [] state
| ConstructVector : forall category left right position state positions,
    Forall2 (fun pair child_position => pair_at category child_position (fst pair) (snd pair))
      (combine left right) positions ->
    BaseConstruction (Vector category) left right position state
      (verdict_task position (Nat.compare (length left) (length right)) :: rev (map child_task positions))
      [native_cmp_observation position (Nat.compare (length left) (length right))] state
| ConstructMapBox : forall category left right position before owner callback after,
    make_map_box category left right before owner callback after ->
    BaseConstruction (MapPairs category) left right position before
      [AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.Start owner callback] [] after.

Inductive FieldConstruction : forall field : @Field Cat,
    source_field_type Term field -> source_field_type Term field ->
    Position -> State -> list Task -> list Observation -> State -> Prop :=
| ConstructPlain : forall base left right position before word events after,
    BaseConstruction base left right position before word events after ->
    FieldConstruction (plain_field base) left right position before word events after
| ConstructNoneNone : forall base position state,
    optional_base_admitted base ->
    FieldConstruction (optional_field base) None None position state [] [] state
| ConstructNoneSome : forall base right position state,
    optional_base_admitted base ->
    FieldConstruction (optional_field base) None (Some right) position state
      [verdict_task position Lt] [] state
| ConstructSomeNone : forall base left position state,
    optional_base_admitted base ->
    FieldConstruction (optional_field base) (Some left) None position state
      [verdict_task position Gt] [] state
| ConstructSomeSome : forall base left right position before word events after,
    optional_base_admitted base ->
    BaseConstruction base left right position before word events after ->
    FieldConstruction (optional_field base) (Some left) (Some right) position before word events after.

(** Native append/push order is retained separately from forward drain groups.
    State and observations thread through the REST construction first. *)
Inductive ReverseFieldsConstruction : forall fields : list (@Field Cat),
    source_fields_type Term fields -> source_fields_type Term fields -> nat ->
    State -> list Task -> list (list Task) -> list Observation -> State -> Prop :=
| ConstructReverseNil : forall index state,
    ReverseFieldsConstruction [] tt tt index state [] [] [] state
| ConstructReverseCons : forall field rest left right left_rest right_rest index
    before tail_word tail_groups tail_events middle head_word head_events after,
    ReverseFieldsConstruction rest left_rest right_rest (S index)
      before tail_word tail_groups tail_events middle ->
    FieldConstruction field left right (field_position index) middle head_word head_events after ->
    ReverseFieldsConstruction (field :: rest) (left, left_rest) (right, right_rest) index
      before (tail_word ++ head_word) (rev head_word :: tail_groups)
      (tail_events ++ head_events) after.

Theorem reverse_field_construction_drains_in_forward_groups :
  forall fields left right index before word groups events after,
  ReverseFieldsConstruction fields left right index before word groups events after ->
  rev word = concat groups.
Proof.
  intros fields left right index before word groups events after CONSTRUCTION.
  induction CONSTRUCTION; [reflexivity|].
  rewrite rev_app_distr, IHCONSTRUCTION. reflexivity.
Qed.

(** A scope remains one ORIGINAL construction group, although its class-key
    telescope has the two positions pattern then body. *)
Inductive TrailerConstruction : forall fields : list (@Field Cat),
    source_fields_type Term fields -> source_fields_type Term fields ->
    State -> list Task -> list Observation -> State -> Prop :=
| ConstructNoScope : forall state,
    TrailerConstruction [] tt tt state [] [] state
| ConstructScope : forall multi category
    (left_pattern right_pattern : atom_source_type (pattern_atom multi))
    left_body right_body pattern_position body_position state,
    pair_at category body_position left_body right_body ->
    TrailerConstruction
      [plain_field (Native (pattern_atom multi)); plain_field (Child category)]
      (left_pattern, (left_body, tt)) (right_pattern, (right_body, tt)) state
      [child_task body_position;
       verdict_task pattern_position
         (atom_source_compare uid_digest binder_digest (pattern_atom multi) left_pattern right_pattern)]
      [native_cmp_observation pattern_position
         (atom_source_compare uid_digest binder_digest (pattern_atom multi) left_pattern right_pattern)] state.

Section OneOriginalRow.
Variable trailer_fields : list (@Field Cat).
Variables trailer_left trailer_right : source_fields_type Term trailer_fields.

Inductive ArmConstruction : forall fields : list (@Field Cat),
    source_fields_type Term fields -> source_fields_type Term fields -> nat ->
    State -> HandlerExit -> list Observation -> State -> Prop :=
| ConstructEagerDecisive : forall atom rest left right left_rest right_rest index state,
    atom_source_compare uid_digest binder_digest atom left right <> Eq ->
    ArmConstruction (plain_field (Native atom) :: rest) (left, left_rest) (right, right_rest)
      index state (Signalled (atom_source_compare uid_digest binder_digest atom left right))
      [native_cmp_observation (field_position index)
        (atom_source_compare uid_digest binder_digest atom left right)] state
| ConstructEagerEqual : forall atom rest left right left_rest right_rest index before exit events after,
    atom_source_compare uid_digest binder_digest atom left right = Eq ->
    ArmConstruction rest left_rest right_rest (S index) before exit events after ->
    ArmConstruction (plain_field (Native atom) :: rest) (left, left_rest) (right, right_rest)
      index before exit
      (native_cmp_observation (field_position index)
        (atom_source_compare uid_digest binder_digest atom left right) :: events) after
| ConstructDeferredSuffix : forall field rest left right index before
    scope_word scope_events middle field_word groups field_events after,
    stack_expressible field = true ->
    TrailerConstruction trailer_fields trailer_left trailer_right
      before scope_word scope_events middle ->
    ReverseFieldsConstruction (field :: rest) left right index
      middle field_word groups field_events after ->
    ArmConstruction (field :: rest) left right index before
      (Scheduled (rev (scope_word ++ field_word))) (scope_events ++ field_events) after
| ConstructAfterLastEager : forall index before word events after,
    TrailerConstruction trailer_fields trailer_left trailer_right before word events after ->
    ArmConstruction [] tt tt index before (Scheduled (rev word)) events after.

Theorem a_signalled_arm_constructs_its_decisive_eager_consultation :
  forall fields left right index before exit events after,
  ArmConstruction fields left right index before exit events after -> forall result suffix,
  exit = Signalled result -> Consultation (native_cmp_results events ++ suffix) result.
Proof.
  intros fields left right index before exit events after CONSTRUCTION.
  induction CONSTRUCTION; intros result suffix EXIT.
  - inversion EXIT; subst result.
    cbn [native_cmp_results native_cmp_observation flat_map app].
    apply ConsultDecisive. assumption.
  - cbn [native_cmp_results native_cmp_observation flat_map app].
    rewrite H. apply ConsultEqual. now apply IHCONSTRUCTION.
  - discriminate EXIT.
  - discriminate EXIT.
Qed.

Theorem a_deferred_row_drains_prefields_before_its_scope :
  forall fields left right index before field_word groups field_events middle
    scope_word,
  ReverseFieldsConstruction fields left right index before field_word groups field_events middle ->
  rev (scope_word ++ field_word) = concat groups ++ rev scope_word.
Proof.
  intros. rewrite rev_app_distr.
  now rewrite (reverse_field_construction_drains_in_forward_groups _ _ _ _ _ _ _ _ _ H).
Qed.
End OneOriginalRow.
End OriginalConstruction.

(** Exact algebra needed by the concrete Vec group, not another list order. *)
Definition common_prefix_decisions {A : Type} (compare : A -> A -> comparison) left right :=
  map (fun pair => compare (fst pair) (snd pair)) (combine left right).
Theorem list_comparison_is_common_prefix_then_length :
  forall (A : Type) (compare : A -> A -> comparison) left right,
  list_compare compare left right =
    fold_decisions (common_prefix_decisions compare left right ++
      [Nat.compare (length left) (length right)]).
Proof.
  intros A compare left. induction left as [|head tail IH]; intros [|other rest];
    try reflexivity.
  cbn [list_compare common_prefix_decisions combine map fst snd app length
    fold_decisions fold_right].
  destruct (compare head other); cbn [SemanticComparisonLaws.SemanticComparisonLaws.lex];
    try reflexivity.
  exact (IH rest).
Qed.

Fixpoint projected_field_decisions {Cat : Type} (children : Cat -> Ordered)
    (fields : list (@Field Cat)) :
    carrier (fields_order children fields) -> carrier (fields_order children fields) -> list comparison :=
  match fields as selected_fields return
    carrier (fields_order children selected_fields) ->
    carrier (fields_order children selected_fields) -> list comparison with
  | [] => fun _ _ => []
  | field :: rest => fun left right =>
      comparison_function (field_order children field) (fst left) (fst right) ::
      projected_field_decisions children rest (snd left) (snd right)
  end.
Theorem projected_field_fold_is_the_existing_product_comparison :
  forall (Cat : Type) (children : Cat -> Ordered) fields left right,
  fold_decisions (projected_field_decisions children fields left right) =
    comparison_function (fields_order children fields) left right.
Proof.
  intros Cat children fields. induction fields as [|field rest IH]; intros left right.
  - reflexivity.
  - change (SemanticComparisonLaws.SemanticComparisonLaws.lex
      (comparison_function (field_order children field) (fst left) (fst right))
      (fold_decisions (projected_field_decisions children rest (snd left) (snd right))) =
    SemanticComparisonLaws.SemanticComparisonLaws.lex
      (comparison_function (field_order children field) (fst left) (fst right))
      (comparison_function (fields_order children rest) (snd left) (snd right))).
    now rewrite IH.
Qed.

Section ActualBorrowedExecution.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable State : Type.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Variable children : Cat -> Ordered.
Variable next : forall category, Term category -> option (carrier (children category)).
Variable arm_source : Position -> State -> HandlerExit -> list Observation -> State -> Prop.
Variable core_source : nat -> nat -> option comparison -> State -> CoreReply -> list Observation -> State -> Prop.
Variable discard_source : Task -> State -> State -> Prop.
Local Notation Trace := (@ChildTraversal State arm_source core_source discard_source).

(** This is precisely the LOWER-HEIGHT actual-traversal induction hypothesis.
    It is not a callback giving an arbitrary comparison result. *)
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  next category left = Some left_key -> next category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = comparison_function (children category) left_key right_key.

(** A nonrecursive proof binding over the EXISTING task, not a replacement
    instruction. Native outcomes are already stored; child keys refer only to
    projected original operands. Map Start/Resume have no constructor here. *)
Inductive ProjectedBorrowed : Task -> comparison -> Prop :=
| StoredVerdict : forall position result,
    ProjectedBorrowed (verdict_task position result) result
| ProjectedChild : forall category position left right left_key right_key,
    pair_at Term lookup category position left right ->
    next category left = Some left_key -> next category right = Some right_key ->
    ProjectedBorrowed (child_task position)
      (comparison_function (children category) left_key right_key).

Lemma a_projected_borrowed_task_has_no_owner_continuation : forall task decision,
  ProjectedBorrowed task decision ->
  AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.not_resume task = true.
Proof. intros task decision BOUND. destruct BOUND; reflexivity. Qed.
Lemma a_projected_borrowed_batch_has_no_owner_continuation : forall tasks decisions,
  Forall2 ProjectedBorrowed tasks decisions ->
  Forall (fun task =>
    AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.not_resume task = true) tasks.
Proof.
  intros tasks decisions BOUND. induction BOUND; constructor; auto.
  eapply a_projected_borrowed_task_has_no_owner_continuation. exact H.
Qed.

Lemma a_completed_stored_verdict_returns_its_stored_ordering :
  forall position decision count state events result last,
  Trace [] count Run [verdict_task position decision] state events result last -> result = decision.
Proof.
  intros position decision count state events result last TRAVERSAL.
  unfold verdict_task in TRAVERSAL.
  inversion TRAVERSAL as [| |n mode head rest before first next_mode prefix middle later final ending STEP TAIL]; subst.
  repeat rewrite app_nil_r in STEP.
  inversion STEP; subst; inversion TAIL; subst; reflexivity.
Qed.

Lemma an_actual_borrowed_child_returns_its_projected_comparison :
  forall task decision, ProjectedBorrowed task decision ->
  forall count state events result last,
  Trace [] count Run [task] state events result last -> result = decision.
Proof.
  intros task decision BOUND. destruct BOUND; intros count state events final_result last TRAVERSAL.
  - eapply a_completed_stored_verdict_returns_its_stored_ordering. exact TRAVERSAL.
  - eapply lower_height_completed_child; eassumption.
Qed.

Lemma delivery_over_nonresume_tasks_cannot_change_the_decision :
  forall count mode tasks state events result last,
  Trace [] count mode tasks state events result last -> forall decision,
  mode = Deliver decision ->
  Forall (fun task =>
    AdmittedGeneratedCollectionScheduling.AdmittedGeneratedCollectionScheduling.not_resume task = true) tasks ->
  result = decision.
Proof.
  intros count mode tasks state events result last TRAVERSAL.
  induction TRAVERSAL as [state|state ordering NE
    |count mode head rest state first next_mode prefix middle later result last STEP TAIL IH];
    intros decision MODE NONRESUME.
  - discriminate MODE.
  - now injection MODE.
  - subst mode. inversion NONRESUME as [|task tail HEAD REST]; subst task tail.
    repeat rewrite app_nil_r in STEP.
    inversion STEP; subst.
    + discriminate HEAD.
    + apply IH; [reflexivity|assumption].
Qed.

Theorem actual_nonmap_task_batch_constructs_consultation : forall tasks decisions,
  Forall2 ProjectedBorrowed tasks decisions -> forall count state events result last,
  Trace [] count Run tasks state events result last -> Consultation decisions result.
Proof.
  intros tasks decisions BOUND.
  induction BOUND as [|task decision tasks decisions HEAD TAIL IH];
    intros count state events result last TRAVERSAL.
  - inversion TRAVERSAL; subst. constructor.
  - destruct (@running_child_trace_splits_before_its_untouched_frame
      State arm_source core_source discard_source count [task] tasks state events result last TRAVERSAL)
      as [child_count [later_count [child_result [middle [child_events [later_events
        [CHILD [CONTINUATION [COUNTS EVENTS]]]]]]]]].
    pose proof (@finite_child_traversal_strips_to_a_genuine_isolated_trace
      State arm_source core_source discard_source tasks child_count Run [task]
      state child_events child_result middle CHILD) as ISOLATED.
    pose proof (an_actual_borrowed_child_returns_its_projected_comparison
      task decision HEAD child_count state child_events child_result middle ISOLATED) as ANSWER.
    subst child_result. destruct decision.
    + apply ConsultEqual. eapply IH. exact CONTINUATION.
    + assert (RESULT : result = Lt).
      { eapply delivery_over_nonresume_tasks_cannot_change_the_decision;
          [exact CONTINUATION|reflexivity|].
        eapply a_projected_borrowed_batch_has_no_owner_continuation. exact TAIL. }
      subst result. apply ConsultDecisive. discriminate.
    + assert (RESULT : result = Gt).
      { eapply delivery_over_nonresume_tasks_cannot_change_the_decision;
          [exact CONTINUATION|reflexivity|].
        eapply a_projected_borrowed_batch_has_no_owner_continuation. exact TAIL. }
      subst result. apply ConsultDecisive. discriminate.
Qed.

Theorem actual_nonmap_task_batch_returns_its_projected_fold : forall tasks decisions,
  Forall2 ProjectedBorrowed tasks decisions -> forall count state events result last,
  Trace [] count Run tasks state events result last -> result = fold_decisions decisions.
Proof.
  intros tasks decisions BOUND count state events result last TRAVERSAL.
  apply completed_consultation_returns_the_lexicographic_result.
  eapply actual_nonmap_task_batch_constructs_consultation; eassumption.
Qed.
End ActualBorrowedExecution.

Print Assumptions reverse_field_construction_drains_in_forward_groups.
Print Assumptions a_signalled_arm_constructs_its_decisive_eager_consultation.
Print Assumptions a_deferred_row_drains_prefields_before_its_scope.
Print Assumptions list_comparison_is_common_prefix_then_length.
Print Assumptions projected_field_fold_is_the_existing_product_comparison.
Print Assumptions a_completed_stored_verdict_returns_its_stored_ordering.
Print Assumptions an_actual_borrowed_child_returns_its_projected_comparison.
Print Assumptions delivery_over_nonresume_tasks_cannot_change_the_decision.
Print Assumptions actual_nonmap_task_batch_constructs_consultation.
Print Assumptions actual_nonmap_task_batch_returns_its_projected_fold.
End GeneratedSourceRowComparison.
