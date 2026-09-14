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

(** This bridge binds the construction witnesses above to successful ORIGINAL
    operand projections. Its restriction is only the missing Map segment:
    optional opaque leaves remain impossible by FieldConstruction itself.
    No result of a recursive operation occurs in the construction premises. *)
Definition nonmap_base {Cat : Type} (base : @BaseField Cat) : Prop :=
  match base with MapPairs _ => False | _ => True end.

Section ConstructionProjection.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable State : Type.
Variables uid_digest binder_digest : nat -> nat.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Variable make_map_box : forall category,
  list (Term category * Term category) -> list (Term category * Term category) ->
  State -> nat -> nat -> State -> Prop.
Variable field_position : nat -> Position.
Variable children : Cat -> Ordered.
Variable next : forall category, Term category -> option (carrier (children category)).

Local Notation PB := (@ProjectedBorrowed Cat Term lookup children next).
Local Notation BC := (@BaseConstruction Cat Term State uid_digest binder_digest lookup make_map_box).
Local Notation FC := (@FieldConstruction Cat Term State uid_digest binder_digest lookup make_map_box).
Local Notation RC := (@ReverseFieldsConstruction Cat Term State uid_digest binder_digest lookup make_map_box field_position).
Local Notation TC := (@TrailerConstruction Cat Term State uid_digest binder_digest lookup).
Local Notation ProjectBase := (project_base Term uid_digest binder_digest children next).
Local Notation ProjectField := (project_field Term uid_digest binder_digest children next).
Local Notation ProjectFields := (project_fields Term uid_digest binder_digest children next).
Local Notation lex := SemanticComparisonLaws.SemanticComparisonLaws.lex.

Definition ProjectedBatch tasks decision : Prop :=
  exists decisions, Forall2 PB tasks decisions /\ fold_decisions decisions = decision.

Lemma projected_bindings_append : forall tasks decisions,
  Forall2 PB tasks decisions -> forall suffix results,
  Forall2 PB suffix results -> Forall2 PB (tasks ++ suffix) (decisions ++ results).
Proof.
  intros tasks decisions BOUND. induction BOUND; intros suffix results TAIL;
    cbn [app]; [exact TAIL|constructor; auto].
Qed.

Lemma projected_batch_empty : ProjectedBatch [] Eq.
Proof. exists []. split; constructor. Qed.

Lemma projected_batch_verdict : forall position decision,
  ProjectedBatch [verdict_task position decision] decision.
Proof.
  intros position decision. exists [decision]. split.
  - constructor; [constructor|constructor].
  - destruct decision; reflexivity.
Qed.

Lemma projected_batch_append : forall first a rest b,
  ProjectedBatch first a -> ProjectedBatch rest b ->
  ProjectedBatch (first ++ rest) (lex a b).
Proof.
  intros first a rest b [xs [FIRST A]] [ys [REST B]].
  exists (xs ++ ys). split.
  - now apply projected_bindings_append.
  - now rewrite fold_decisions_app, A, B.
Qed.

Lemma paired_child_projection_preserves_length : forall category values keys,
  Forall2 (fun value key => next category value = Some key) values keys ->
  length values = length keys.
Proof. intros category values keys PROJECTION. induction PROJECTION; cbn; congruence. Qed.

(** The three Forall2 witnesses share the ORIGINAL common-prefix pairs.
    This proves the typed pointer association, not just list lengths. *)
Lemma projected_common_prefix_binds_original_positions :
  forall category left left_keys,
  Forall2 (fun value key => next category value = Some key) left left_keys ->
  forall right right_keys,
  Forall2 (fun value key => next category value = Some key) right right_keys ->
  forall positions,
  Forall2 (fun pair position => pair_at Term lookup category position (fst pair) (snd pair))
    (combine left right) positions ->
  Forall2 PB (map child_task positions)
    (common_prefix_decisions (comparison_function (children category)) left_keys right_keys).
Proof.
  intros category left left_keys LEFT.
  induction LEFT as [|left left_key lefts left_keys LEFT_HEAD LEFT_TAIL IH];
    intros right right_keys RIGHT positions POSITIONS.
  - cbn [combine] in POSITIONS. inversion POSITIONS; subst. constructor.
  - inversion RIGHT as [|right_head right_key rights rest_keys RIGHT_HEAD RIGHT_TAIL]; subst.
    + cbn [combine] in POSITIONS. inversion POSITIONS; subst. constructor.
    + cbn [combine] in POSITIONS.
      inversion POSITIONS as [|pair position pairs rest_positions POSITION REMAINING]; subst.
      cbn [map common_prefix_decisions combine fst snd]. constructor.
      * eapply ProjectedChild; [exact POSITION|exact LEFT_HEAD|exact RIGHT_HEAD].
      * eapply IH; [exact RIGHT_TAIL|exact REMAINING].
Qed.

Theorem constructed_nonmap_base_binds_its_successful_projection :
  forall base left right position before word events after,
  BC base left right position before word events after -> nonmap_base base ->
  forall left_key right_key,
  ProjectBase base left = Some left_key -> ProjectBase base right = Some right_key ->
  ProjectedBatch (rev word) (comparison_function (base_order children base) left_key right_key).
Proof.
  intros base left right position before word events after CONSTRUCTION.
  destruct CONSTRUCTION; intros NONMAP left_key right_key LEFT RIGHT.
  - pose proof (successful_native_field_projection_has_the_original_leaf_result
      Term uid_digest binder_digest children next atom left right left_key right_key LEFT RIGHT) as FACTOR.
    cbn [rev app base_order]. rewrite <- FACTOR. apply projected_batch_verdict.
  - exists [comparison_function (children category) left_key right_key]. split.
    + cbn [rev app]. constructor; [eapply ProjectedChild; eassumption|constructor].
    + cbn [base_order].
      destruct (comparison_function (children category) left_key right_key); reflexivity.
  - pose proof (successful_vector_projection_keeps_every_child_view
      Term uid_digest binder_digest children next category left left_key LEFT) as LEFT_PAIRS.
    pose proof (successful_vector_projection_keeps_every_child_view
      Term uid_digest binder_digest children next category right right_key RIGHT) as RIGHT_PAIRS.
    pose proof (paired_child_projection_preserves_length _ _ _ LEFT_PAIRS) as LEFT_LENGTH.
    pose proof (paired_child_projection_preserves_length _ _ _ RIGHT_PAIRS) as RIGHT_LENGTH.
    exists (common_prefix_decisions (comparison_function (children category)) left_key right_key ++
      [Nat.compare (length left) (length right)]). split.
    + cbn [rev]. rewrite rev_involutive. apply projected_bindings_append.
      * eapply projected_common_prefix_binds_original_positions; eassumption.
      * constructor; [constructor|constructor].
    + rewrite LEFT_LENGTH, RIGHT_LENGTH.
      symmetry. apply list_comparison_is_common_prefix_then_length.
  - contradiction.
Qed.

Theorem constructed_nonmap_field_binds_its_successful_projection :
  forall field left right position before word events after,
  FC field left right position before word events after -> nonmap_base (field_base field) ->
  forall left_key right_key,
  ProjectField field left = Some left_key -> ProjectField field right = Some right_key ->
  ProjectedBatch (rev word) (comparison_function (field_order children field) left_key right_key).
Proof.
  intros field left right position before word events after CONSTRUCTION.
  destruct CONSTRUCTION; intros NONMAP left_key right_key LEFT RIGHT.
  - eapply constructed_nonmap_base_binds_its_successful_projection; eassumption.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    inversion LEFT; inversion RIGHT; subst. apply projected_batch_empty.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base right) as [key|] eqn:KEY; try discriminate.
    inversion LEFT; inversion RIGHT; subst. apply projected_batch_verdict.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base left) as [key|] eqn:KEY; try discriminate.
    inversion LEFT; inversion RIGHT; subst. apply projected_batch_verdict.
  - cbn [project_field optional_field] in LEFT, RIGHT.
    destruct (ProjectBase base left) as [lk|] eqn:LK; try discriminate.
    destruct (ProjectBase base right) as [rk|] eqn:RK; try discriminate.
    inversion LEFT; inversion RIGHT; subst.
    eapply constructed_nonmap_base_binds_its_successful_projection; eassumption.
Qed.

Theorem constructed_nonmap_reverse_fields_bind_their_successful_projection :
  forall fields left right index before word groups events after,
  RC fields left right index before word groups events after ->
  Forall (fun field => nonmap_base (field_base field)) fields ->
  forall left_key right_key,
  ProjectFields fields left = Some left_key -> ProjectFields fields right = Some right_key ->
  ProjectedBatch (rev word) (comparison_function (fields_order children fields) left_key right_key).
Proof.
  intros fields left right index before word groups events after CONSTRUCTION.
  induction CONSTRUCTION; intros NONMAP left_key right_key LEFT RIGHT.
  - destruct left_key, right_key. apply projected_batch_empty.
  - inversion NONMAP as [|f fs HEAD TAIL]; subst.
    destruct left_key as [lk lks], right_key as [rk rks].
    apply successful_pair_projection_keeps_both_original_positions in LEFT as [LEFT_HEAD LEFT_TAIL].
    apply successful_pair_projection_keeps_both_original_positions in RIGHT as [RIGHT_HEAD RIGHT_TAIL].
    rewrite rev_app_distr. apply projected_batch_append.
    + eapply constructed_nonmap_field_binds_its_successful_projection; eassumption.
    + eapply IHCONSTRUCTION; eassumption.
Qed.

Theorem constructed_scope_binds_its_successful_projection :
  forall fields left right before word events after,
  TC fields left right before word events after -> forall left_key right_key,
  ProjectFields fields left = Some left_key -> ProjectFields fields right = Some right_key ->
  ProjectedBatch (rev word) (comparison_function (fields_order children fields) left_key right_key).
Proof.
  intros fields left right before word events after CONSTRUCTION.
  destruct CONSTRUCTION; intros left_key right_key LEFT RIGHT.
  - destruct left_key, right_key. apply projected_batch_empty.
  - destruct left_key as [lp [lb []]], right_key as [rp [rb []]].
    apply successful_pair_projection_keeps_both_original_positions in LEFT as [LP LB].
    apply successful_pair_projection_keeps_both_original_positions in RIGHT as [RP RB].
    apply successful_pair_projection_keeps_both_original_positions in LB as [LB _].
    apply successful_pair_projection_keeps_both_original_positions in RB as [RB _].
    pose proof (successful_native_field_projection_has_the_original_leaf_result
      Term uid_digest binder_digest children next (pattern_atom multi)
      left_pattern right_pattern lp rp LP RP) as PATTERN.
    exists [atom_source_compare uid_digest binder_digest (pattern_atom multi) left_pattern right_pattern;
      comparison_function (children category) lb rb]. split.
    + cbn [rev app]. constructor; [constructor|].
      constructor; [eapply ProjectedChild; eassumption|constructor].
    + rewrite PATTERN. reflexivity.
Qed.

(** This is a proof property of the EXISTING HandlerExit. In particular it
    does not replace an arm_source step or assign a result to a Map owner. *)
Definition ProjectedHandler exit decision : Prop := match exit with
  | Signalled result => result = decision
  | Scheduled tasks => ProjectedBatch tasks decision
  end.

Section OriginalRowProjection.
Variable trailer_fields : list (@Field Cat).
Variables trailer_left trailer_right : source_fields_type Term trailer_fields.
Local Notation AC := (@ArmConstruction Cat Term State uid_digest binder_digest lookup
  make_map_box field_position trailer_fields trailer_left trailer_right).

Theorem constructed_nonmap_arm_binds_its_successful_row_projection :
  forall fields left right index before exit events after,
  AC fields left right index before exit events after ->
  Forall (fun field => nonmap_base (field_base field)) fields ->
  forall left_key right_key trailer_left_key trailer_right_key,
  ProjectFields fields left = Some left_key -> ProjectFields fields right = Some right_key ->
  ProjectFields trailer_fields trailer_left = Some trailer_left_key ->
  ProjectFields trailer_fields trailer_right = Some trailer_right_key ->
  ProjectedHandler exit
    (lex (comparison_function (fields_order children fields) left_key right_key)
      (comparison_function (fields_order children trailer_fields) trailer_left_key trailer_right_key)).
Proof.
  intros fields left right index before exit events after CONSTRUCTION.
  induction CONSTRUCTION; intros NONMAP left_key right_key tlk trk LEFT RIGHT TRAILER_LEFT TRAILER_RIGHT.
  - destruct left_key as [lk lks], right_key as [rk rks].
    apply successful_pair_projection_keeps_both_original_positions in LEFT as [LP LR].
    apply successful_pair_projection_keeps_both_original_positions in RIGHT as [RP RR].
    pose proof (successful_native_field_projection_has_the_original_leaf_result
      Term uid_digest binder_digest children next atom left right lk rk LP RP) as NATIVE.
    change (atom_source_compare uid_digest binder_digest atom left right =
      lex (lex (comparison_function (atom_order atom) lk rk)
        (comparison_function (fields_order children rest) lks rks))
        (comparison_function (fields_order children trailer_fields) tlk trk)).
    rewrite <- NATIVE. destruct (atom_source_compare uid_digest binder_digest atom left right);
      [contradiction|reflexivity|reflexivity].
  - inversion NONMAP as [|f fs HEAD TAIL]; subst.
    destruct left_key as [lk lks], right_key as [rk rks].
    apply successful_pair_projection_keeps_both_original_positions in LEFT as [LP LR].
    apply successful_pair_projection_keeps_both_original_positions in RIGHT as [RP RR].
    pose proof (successful_native_field_projection_has_the_original_leaf_result
      Term uid_digest binder_digest children next atom left right lk rk LP RP) as NATIVE.
    change (ProjectedHandler exit
      (lex (lex (comparison_function (atom_order atom) lk rk)
        (comparison_function (fields_order children rest) lks rks))
        (comparison_function (fields_order children trailer_fields) tlk trk))).
    rewrite <- NATIVE, H. eapply IHCONSTRUCTION; eassumption.
  - unfold ProjectedHandler. rewrite rev_app_distr. apply projected_batch_append.
    + eapply constructed_nonmap_reverse_fields_bind_their_successful_projection; eassumption.
    + eapply constructed_scope_binds_its_successful_projection; eassumption.
  - destruct left_key, right_key. cbn [ProjectedHandler fields_order comparison_function].
    eapply constructed_scope_binds_its_successful_projection; eassumption.
Qed.

Section ActualSuffix.
Variable arm_source : Position -> State -> HandlerExit -> list Observation -> State -> Prop.
Variable core_source : nat -> nat -> option comparison -> State -> CoreReply -> list Observation -> State -> Prop.
Variable discard_source : Task -> State -> State -> Prop.
Local Notation Trace := (@ChildTraversal State arm_source core_source discard_source).
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  next category left = Some left_key -> next category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = comparison_function (children category) left_key right_key.

Lemma every_projected_row_fold_has_its_consultation : forall decisions,
  Consultation decisions (fold_decisions decisions).
Proof.
  intro decisions. induction decisions as [|decision rest IH]; [constructor|].
  destruct decision; [now apply ConsultEqual|apply ConsultDecisive; discriminate|apply ConsultDecisive; discriminate].
Qed.

(** The Scheduled case consumes the actual isolated suffix traversal. The
    Signalled case uses its already proved eager source construction, never a
    supplied comparator result. This is still a HANDLER theorem: the census
    RowPath/selector/VariantKind association and enclosing CategoryPair source
    step are not inferred from it. Map-containing rows remain outside it. *)
Theorem constructed_nonmap_arm_and_actual_suffix_consult_the_projected_row :
  forall fields left right index before exit events after,
  AC fields left right index before exit events after ->
  Forall (fun field => nonmap_base (field_base field)) fields ->
  forall left_key right_key trailer_left_key trailer_right_key,
  ProjectFields fields left = Some left_key -> ProjectFields fields right = Some right_key ->
  ProjectFields trailer_fields trailer_left = Some trailer_left_key ->
  ProjectFields trailer_fields trailer_right = Some trailer_right_key ->
  let decisions := projected_field_decisions children fields left_key right_key ++
    projected_field_decisions children trailer_fields trailer_left_key trailer_right_key in
  match exit with
  | Signalled result => Consultation decisions result
  | Scheduled tasks => forall count suffix_events result last,
      Trace [] count Run tasks after suffix_events result last -> Consultation decisions result
  end.
Proof.
  intros fields left right index before exit events after CONSTRUCTION NONMAP
    left_key right_key tlk trk LEFT RIGHT TRAILER_LEFT TRAILER_RIGHT decisions.
  pose proof (constructed_nonmap_arm_binds_its_successful_row_projection
    fields left right index before exit events after CONSTRUCTION NONMAP
    left_key right_key tlk trk LEFT RIGHT TRAILER_LEFT TRAILER_RIGHT) as BOUND.
  assert (ROW_FOLD : fold_decisions decisions =
    lex (comparison_function (fields_order children fields) left_key right_key)
      (comparison_function (fields_order children trailer_fields) tlk trk)).
  { unfold decisions. rewrite fold_decisions_app.
    now rewrite !projected_field_fold_is_the_existing_product_comparison. }
  destruct exit as [tasks|decision].
  - intros count suffix_events result last TRAVERSAL.
    destruct BOUND as [task_decisions [TASKS RESULT]].
    assert (ACTUAL : result = fold_decisions task_decisions).
    { eapply actual_nonmap_task_batch_returns_its_projected_fold;
        [exact lower_height_completed_child|exact TASKS|exact TRAVERSAL]. }
    rewrite ACTUAL, RESULT, <- ROW_FOLD. apply every_projected_row_fold_has_its_consultation.
  - unfold ProjectedHandler in BOUND. rewrite BOUND, <- ROW_FOLD.
    apply every_projected_row_fold_has_its_consultation.
Qed.
End ActualSuffix.
End OriginalRowProjection.
End ConstructionProjection.

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
Print Assumptions projected_common_prefix_binds_original_positions.
Print Assumptions constructed_nonmap_base_binds_its_successful_projection.
Print Assumptions constructed_nonmap_field_binds_its_successful_projection.
Print Assumptions constructed_nonmap_reverse_fields_bind_their_successful_projection.
Print Assumptions constructed_scope_binds_its_successful_projection.
Print Assumptions constructed_nonmap_arm_binds_its_successful_row_projection.
Print Assumptions constructed_nonmap_arm_and_actual_suffix_consult_the_projected_row.
(** The scope split is a split of the existing finite field telescope, not a
    second row datatype. These joins retain the terminal unit exactly. *)
Local Notation lex := SemanticComparisonLaws.SemanticComparisonLaws.lex.
Section TelescopeAppend.
Context {Cat : Type}.
Variable Term : Cat -> Type.
Variable children : Cat -> Ordered.

Fixpoint append_source_fields (first rest : list (@Field Cat)) :
    source_fields_type Term first -> source_fields_type Term rest ->
    source_fields_type Term (first ++ rest) :=
  match first as selected return source_fields_type Term selected ->
    source_fields_type Term rest -> source_fields_type Term (selected ++ rest) with
  | [] => fun _ tail => tail
  | field :: fields => fun head tail =>
      (fst head, append_source_fields fields rest (snd head) tail)
  end.
Fixpoint append_field_keys (first rest : list (@Field Cat)) :
    carrier (fields_order children first) -> carrier (fields_order children rest) ->
    carrier (fields_order children (first ++ rest)) :=
  match first as selected return carrier (fields_order children selected) ->
    carrier (fields_order children rest) -> carrier (fields_order children (selected ++ rest)) with
  | [] => fun _ tail => tail
  | field :: fields => fun head tail =>
      (fst head, append_field_keys fields rest (snd head) tail)
  end.

Theorem appended_field_keys_keep_original_lexicographic_priority :
  forall first rest left right tail_left tail_right,
  comparison_function (fields_order children (first ++ rest))
    (append_field_keys first rest left tail_left)
    (append_field_keys first rest right tail_right) =
  lex (comparison_function (fields_order children first) left right)
    (comparison_function (fields_order children rest) tail_left tail_right).
Proof.
  intro first. induction first as [|field fields IH]; intros rest left right tail_left tail_right.
  - reflexivity.
  - destruct left as [left left_rest], right as [right right_rest].
    change (lex (comparison_function (field_order children field) left right)
      (comparison_function (fields_order children (fields ++ rest))
        (append_field_keys fields rest left_rest tail_left)
        (append_field_keys fields rest right_rest tail_right)) =
      lex (lex (comparison_function (field_order children field) left right)
        (comparison_function (fields_order children fields) left_rest right_rest))
        (comparison_function (fields_order children rest) tail_left tail_right)).
    rewrite IH. destruct (comparison_function (field_order children field) left right); reflexivity.
Qed.

Variables uid_digest binder_digest : nat -> nat.
Variable next : forall category, Term category -> option (carrier (children category)).
Local Notation ProjectFields := (project_fields Term uid_digest binder_digest children next).

Theorem appended_source_projection_is_exactly_the_two_original_projections :
  forall first rest left tail,
  ProjectFields (first ++ rest) (append_source_fields first rest left tail) =
  match ProjectFields first left, ProjectFields rest tail with
  | Some head, Some last => Some (append_field_keys first rest head last)
  | _, _ => None end.
Proof.
  intro first. induction first as [|field fields IH]; intros rest left tail.
  - destruct left. cbn [append_source_fields append_field_keys project_fields app].
    destruct (ProjectFields rest tail); reflexivity.
  - destruct left as [head remaining].
    cbn [append_source_fields project_fields fst snd app]. rewrite IH.
    destruct (project_field Term uid_digest binder_digest children next field head),
      (ProjectFields fields remaining), (ProjectFields rest tail); reflexivity.
Qed.

Theorem successful_appended_projection_splits_at_the_original_scope_boundary :
  forall first rest left tail key,
  ProjectFields (first ++ rest) (append_source_fields first rest left tail) = Some key ->
  exists head last,
    ProjectFields first left = Some head /\ ProjectFields rest tail = Some last /\
    key = append_field_keys first rest head last.
Proof.
  intros first rest left tail key RESULT.
  rewrite appended_source_projection_is_exactly_the_two_original_projections in RESULT.
  destruct (ProjectFields first left) as [head|] eqn:HEAD,
    (ProjectFields rest tail) as [last|] eqn:TAIL; try discriminate.
  inversion RESULT; subst key. exists head, last. repeat split; reflexivity.
Qed.
End TelescopeAppend.

(** Original CategoryPair handler association. It records only constructor
    selection, original field selectors, scope boundary, and actual arm
    construction. There is no whole-row comparison-result premise. Binding
    this relation to Rust is the explicitly audited census/emitter boundary;
    the comparison indices are not Rust enum discriminants. *)
Section EnclosingCategorySource.
Context {Cat : Type}.
Variable signature : Cat -> list (@Row Cat).
Variable Term : Cat -> Type.
Variable State : Type.
Variables uid_digest binder_digest : nat -> nat.
Variable observe : forall category, Term category -> SourceObservation signature Term category.
Variable lookup : Position -> option { category : Cat & (Term category * Term category)%type }.
Variable make_map_box : forall category,
  list (Term category * Term category) -> list (Term category * Term category) ->
  State -> nat -> nat -> State -> Prop.
Definition admitted_source_row ordinal fields : @Row Cat :=
  {| row_ordinal := ordinal; row_admitted := true; row_fields := fields |}.

Inductive CategoryArmBinding category position (left right : Term category) :
    State -> HandlerExit -> list Observation -> State -> Prop :=
| BindOriginalOrdinalMismatch : forall state events,
    pair_at Term lookup category position left right ->
    observed_ordinal signature Term observe category left <>
      observed_ordinal signature Term observe category right ->
    CategoryArmBinding category position left right state
      (Signalled (Nat.compare (observed_ordinal signature Term observe category left)
        (observed_ordinal signature Term observe category right))) events state
| BindOriginalSameRow : forall ordinal fields trailer_fields (positions : nat -> Position)
    (path : RowPath (signature category) (admitted_source_row ordinal (fields ++ trailer_fields)))
    left_fields right_fields left_trailer right_trailer before exit events after,
    pair_at Term lookup category position left right ->
    observe category left = existT _ (admitted_source_row ordinal (fields ++ trailer_fields))
      (path, append_source_fields Term fields trailer_fields left_fields left_trailer) ->
    observe category right = existT _ (admitted_source_row ordinal (fields ++ trailer_fields))
      (path, append_source_fields Term fields trailer_fields right_fields right_trailer) ->
    ArmConstruction Term State uid_digest binder_digest lookup make_map_box positions
      trailer_fields left_trailer right_trailer fields left_fields right_fields 0 before exit events after ->
    CategoryArmBinding category position left right before exit events after.

Definition observed_row_is_nonmap category (term : Term category) :=
  match observe category term with existT _ row _ =>
    Forall (fun field => nonmap_base (field_base field)) (row_fields row) end.

Variable arm_source : Position -> State -> HandlerExit -> list Observation -> State -> Prop.
Variable core_source : nat -> nat -> option comparison -> State -> CoreReply -> list Observation -> State -> Prop.
Variable discard_source : Task -> State -> State -> Prop.
Local Notation Trace := (@ChildTraversal State arm_source core_source discard_source).
Local Notation View := (source_view signature Term uid_digest binder_digest observe).
Hypothesis ORDINALS : signature_ordinals_ordered signature.
Variable height : nat.
Local Notation children := (category_order signature height).
Local Notation next := (fun category child => View height category child).

(** This is the eventual height-induction hypothesis, not an assumed ArmResult.
    It quantifies over arbitrary original pairs, including same-roster pairs. *)
Hypothesis lower_height_completed_child : forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  next category left = Some left_key -> next category right = Some right_key ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = comparison_function (children category) left_key right_key.

Theorem original_bound_nonmap_handler_factors_at_the_enclosing_category :
  forall category position left right before exit events after,
  CategoryArmBinding category position left right before exit events after ->
  (observed_ordinal signature Term observe category left <>
    observed_ordinal signature Term observe category right \/ observed_row_is_nonmap category left) ->
  forall left_key right_key,
  View (S height) category left = Some left_key -> View (S height) category right = Some right_key ->
  match exit with
  | Signalled result => result = key_compare signature (S height) category left_key right_key
  | Scheduled tasks => forall count suffix_events result last,
      Trace [] count Run tasks after suffix_events result last ->
      result = key_compare signature (S height) category left_key right_key
  end.
Proof.
  intros category position left right before exit events after BINDING.
  destruct BINDING as [state events PAIR DIFFERENT
    |ordinal fields trailer_fields positions path left_fields right_fields left_trailer right_trailer
      before exit events after PAIR OBSERVED_LEFT OBSERVED_RIGHT CONSTRUCTION];
    intros CHECK left_key right_key LEFT RIGHT.
  - symmetry. eapply source_constructor_mismatch_factors_without_an_arm_result_premise; eassumption.
  - assert (SAME : observed_ordinal signature Term observe category left =
        observed_ordinal signature Term observe category right).
    { unfold observed_ordinal. rewrite OBSERVED_LEFT, OBSERVED_RIGHT. reflexivity. }
    destruct CHECK as [DIFFERENT|NONMAP]; [contradiction|].
    unfold observed_row_is_nonmap in NONMAP. rewrite OBSERVED_LEFT in NONMAP.
    cbn [admitted_source_row row_fields] in NONMAP.
    apply Forall_app in NONMAP as [PREFIELDS_NONMAP TRAILER_NONMAP].
    cbn [source_view] in LEFT, RIGHT.
    rewrite OBSERVED_LEFT in LEFT. rewrite OBSERVED_RIGHT in RIGHT.
    change (option_map (inject_row children path)
      (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
        (append_source_fields Term fields trailer_fields left_fields left_trailer)) = Some left_key) in LEFT.
    change (option_map (inject_row children path)
      (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
        (append_source_fields Term fields trailer_fields right_fields right_trailer)) = Some right_key) in RIGHT.
    destruct (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
      (append_source_fields Term fields trailer_fields left_fields left_trailer)) as [left_payload|] eqn:PL;
      cbn [option_map] in LEFT; try discriminate.
    destruct (project_fields Term uid_digest binder_digest children next (fields ++ trailer_fields)
      (append_source_fields Term fields trailer_fields right_fields right_trailer)) as [right_payload|] eqn:PR;
      cbn [option_map] in RIGHT; try discriminate.
    injection LEFT as LEFT_KEY. injection RIGHT as RIGHT_KEY. subst left_key right_key.
    destruct (successful_appended_projection_splits_at_the_original_scope_boundary
      Term children uid_digest binder_digest next fields trailer_fields left_fields left_trailer left_payload PL)
      as [lk [tlk [LP [TL LEFT_PAYLOAD]]]].
    destruct (successful_appended_projection_splits_at_the_original_scope_boundary
      Term children uid_digest binder_digest next fields trailer_fields right_fields right_trailer right_payload PR)
      as [rk [trk [RP [TR RIGHT_PAYLOAD]]]].
    subst left_payload right_payload.
    assert (KEY_RESULT : key_compare signature (S height) category
        (inject_row children path (append_field_keys children fields trailer_fields lk tlk))
        (inject_row children path (append_field_keys children fields trailer_fields rk trk)) =
      lex (comparison_function (fields_order children fields) lk rk)
        (comparison_function (fields_order children trailer_fields) tlk trk)).
    { unfold key_compare. cbn [category_order].
      rewrite same_row_injection_preserves_field_comparison.
      apply appended_field_keys_keep_original_lexicographic_priority. }
    rewrite KEY_RESULT.
    pose proof (@constructed_nonmap_arm_and_actual_suffix_consult_the_projected_row
      Cat Term State uid_digest binder_digest lookup make_map_box positions children next
      trailer_fields left_trailer right_trailer arm_source core_source discard_source
      lower_height_completed_child fields left_fields right_fields 0 before exit events after
      CONSTRUCTION PREFIELDS_NONMAP lk rk tlk trk LP RP TL TR) as RESULT.
    assert (FOLD : fold_decisions
        (projected_field_decisions children fields lk rk ++
         projected_field_decisions children trailer_fields tlk trk) =
      lex (comparison_function (fields_order children fields) lk rk)
        (comparison_function (fields_order children trailer_fields) tlk trk)).
    { rewrite fold_decisions_app.
      now rewrite !projected_field_fold_is_the_existing_product_comparison. }
    destruct exit as [tasks|decision].
    + intros count suffix_events result last TRAVERSAL.
      specialize (RESULT count suffix_events result last TRAVERSAL).
      apply completed_consultation_returns_the_lexicographic_result in RESULT.
      now rewrite FOLD in RESULT.
    + apply completed_consultation_returns_the_lexicographic_result in RESULT.
      now rewrite FOLD in RESULT.
Qed.

(** This explicit SOURCE ASSOCIATION premise is operational: the census must
    bind the real enum pair and field selectors to CategoryArmBinding. It is
    not implied by successful projection and does not assume a row result. *)
Hypothesis source_arm_has_its_original_constructor_binding :
  forall category position left right before exit events after,
  pair_at Term lookup category position left right ->
  arm_source position before exit events after ->
  CategoryArmBinding category position left right before exit events after.

Theorem actual_enclosing_nonmap_category_traversal_factors_from_lower_height_children :
  forall category position left right left_key right_key,
  pair_at Term lookup category position left right ->
  View (S height) category left = Some left_key -> View (S height) category right = Some right_key ->
  (observed_ordinal signature Term observe category left <>
    observed_ordinal signature Term observe category right \/ observed_row_is_nonmap category left) ->
  forall count state events result last,
  Trace [] count Run [child_task position] state events result last ->
  result = key_compare signature (S height) category left_key right_key.
Proof.
  intros category position left right left_key right_key PAIR LEFT RIGHT CHECK
    count state events result last TRAVERSAL.
  unfold child_task in TRAVERSAL.
  inversion TRAVERSAL as [| |n mode head rest before first next_mode prefix middle later final ending STEP TAIL]; subst.
  repeat rewrite app_nil_r in STEP. inversion STEP; subst.
  - match goal with ARM : arm_source position state (Scheduled _) _ _ |- _ =>
      pose proof (source_arm_has_its_original_constructor_binding
        category position left right _ _ _ _ PAIR ARM) as BOUND
    end.
    pose proof (original_bound_nonmap_handler_factors_at_the_enclosing_category
      category position left right _ _ _ _ BOUND CHECK left_key right_key LEFT RIGHT) as FACTOR.
    repeat rewrite app_nil_r in TAIL. exact (FACTOR _ _ _ _ TAIL).
  - match goal with ARM : arm_source position state (Signalled _) _ _ |- _ =>
      pose proof (source_arm_has_its_original_constructor_binding
        category position left right _ _ _ _ PAIR ARM) as BOUND
    end.
    pose proof (original_bound_nonmap_handler_factors_at_the_enclosing_category
      category position left right _ _ _ _ BOUND CHECK left_key right_key LEFT RIGHT) as FACTOR.
    inversion TAIL; subst. exact FACTOR.
Qed.
End EnclosingCategorySource.

Print Assumptions appended_field_keys_keep_original_lexicographic_priority.
Print Assumptions appended_source_projection_is_exactly_the_two_original_projections.
Print Assumptions successful_appended_projection_splits_at_the_original_scope_boundary.
Print Assumptions original_bound_nonmap_handler_factors_at_the_enclosing_category.
Print Assumptions actual_enclosing_nonmap_category_traversal_factors_from_lower_height_children.
End GeneratedSourceRowComparison.
