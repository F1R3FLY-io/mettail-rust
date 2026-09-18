(** Completed-frame refinement for the application driver declared in Regex.
    This composes the existing nullable and derivative small-step machines;
    it does not replace them with native regex operations. A derivation records
    completed child frames in their source order. The concrete DDL lifts one
    child transition at a time; that source correspondence is tested separately.
    Text here counts Unicode scalars. RegexGsltApplication and SemanticIntrinsics
    supply the separate scalar-position/UTF-8-byte correspondence.
    No theorem here claims allocator bounds or that a finite host budget suffices. *)
From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import RegexGsltMatch RegexGsltSearch RegexGsltReplace
  RegexGsltNullableMachine RegexGsltDerivativeMachine.
Import ListNotations.

Module RegexGsltApplicationMachine.

Definition NullableResult (p : RegexPattern) (b : bool) : Prop :=
  exists fuel, run_nullable_machine fuel (EvaluateNullable p []) = Some b.
Definition DerivativeResult (c : Scalar) (p q : RegexPattern) : Prop :=
  DerivativeSteps (EvaluateDerivative c p []) (DonePattern q).

Lemma nullable_result_exact : forall p b, NullableResult p b -> b = nullable p.
Proof.
  intros p b [fuel H].
  exact (bounded_nullable_machine_is_sound fuel (EvaluateNullable p []) b H).
Qed.
Lemma nullable_result_exists : forall p, NullableResult p (nullable p).
Proof. intro p. exists (nullable_evaluation_steps p + 1).
  apply declared_nullable_machine_computes_reference. Qed.
Lemma derivative_result_exact : forall c p q,
  DerivativeResult c p q -> q = derivative c p.
Proof. exact completed_derivative_cannot_misreport. Qed.
Lemma derivative_result_exists : forall c p,
  DerivativeResult c p (derivative c p).
Proof. exact derivative_core_completes. Qed.

Inductive FullScan : RegexPattern -> Text -> bool -> Prop :=
| FullScanEnd : forall p b, NullableResult p b -> FullScan p [] b
| FullScanNext : forall p c rest q b,
    DerivativeResult c p q -> FullScan q rest b -> FullScan p (c :: rest) b.

Theorem full_scan_exact : forall p text b,
  FullScan p text b -> b = full_match p text.
Proof.
  intros p text b H; induction H.
  - exact (nullable_result_exact _ _ H).
  - rewrite derivative_step_sound. rewrite <- (derivative_result_exact _ _ _ H).
    exact IHFullScan.
Qed.
Theorem full_scan_exists : forall text p, FullScan p text (full_match p text).
Proof.
  induction text as [|c rest IH]; intro p.
  - apply FullScanEnd. apply nullable_result_exists.
  - rewrite derivative_step_sound. eapply FullScanNext.
    + apply derivative_result_exists.
    + apply IH.
Qed.

(** Prefix frames inspect the later result before the current nullable result:
    a later success is longer, irrespective of alternative syntax order. *)
Inductive PrefixScan : RegexPattern -> Text -> option nat -> Prop :=
| PrefixEnd : forall p b,
    NullableResult p b -> PrefixScan p [] (if b then Some 0 else None)
| PrefixLonger : forall p c rest q n,
    DerivativeResult c p q -> PrefixScan q rest (Some n) ->
    PrefixScan p (c :: rest) (Some (S n))
| PrefixFallback : forall p c rest q b,
    DerivativeResult c p q -> PrefixScan q rest None -> NullableResult p b ->
    PrefixScan p (c :: rest) (if b then Some 0 else None).

Theorem prefix_scan_exact : forall p text result,
  PrefixScan p text result -> result = longest_prefix p text.
Proof.
  intros p text result H; induction H; cbn [longest_prefix].
  - now rewrite <- (nullable_result_exact _ _ H).
  - rewrite <- (derivative_result_exact _ _ _ H), <- IHPrefixScan. reflexivity.
  - rewrite <- (derivative_result_exact _ _ _ H), <- IHPrefixScan.
    now rewrite <- (nullable_result_exact _ _ H1).
Qed.
Theorem prefix_scan_exists : forall text p, PrefixScan p text (longest_prefix p text).
Proof.
  induction text as [|c rest IH]; intro p; cbn [longest_prefix].
  - apply PrefixEnd. apply nullable_result_exists.
  - specialize (IH (derivative c p)).
    destruct (longest_prefix (derivative c p) rest) as [n|] eqn:E.
    + eapply PrefixLonger; [apply derivative_result_exists|exact IH].
    + eapply PrefixFallback; [apply derivative_result_exists|exact IH|].
      apply nullable_result_exists.
Qed.

Definition later (result : option (nat * nat)) :=
  option_map (fun pair => (S (fst pair), snd pair)) result.
Inductive SearchScan (p : RegexPattern) : Text -> option (nat * nat) -> Prop :=
| SearchHere : forall text n,
    PrefixScan p text (Some n) -> SearchScan p text (Some (0,n))
| SearchEnd : PrefixScan p [] None -> SearchScan p [] None
| SearchLater : forall c rest result,
    PrefixScan p (c :: rest) None -> SearchScan p rest result ->
    SearchScan p (c :: rest) (later result).

Theorem search_scan_exact : forall p text result,
  SearchScan p text result -> result = search_raw p text.
Proof.
  intros p text result H; induction H.
  - destruct text; cbn [search_raw];
      rewrite <- (prefix_scan_exact _ _ _ H); reflexivity.
  - cbn [search_raw]. now rewrite <- (prefix_scan_exact _ _ _ H).
  - cbn [search_raw]. rewrite <- (prefix_scan_exact _ _ _ H), <- IHSearchScan.
    destruct result as [[start n]|]; reflexivity.
Qed.
Theorem search_scan_exists : forall text p, SearchScan p text (search_raw p text).
Proof.
  induction text as [|c rest IH]; intro p.
  - cbn [search_raw].
    pose proof (prefix_scan_exists [] p) as HP.
    destruct (longest_prefix p []) as [n|]; [apply SearchHere|apply SearchEnd];
      exact HP.
  - cbn [search_raw].
    pose proof (prefix_scan_exists (c :: rest) p) as HP.
    destruct (longest_prefix p (c :: rest)) as [n|].
    + apply SearchHere; exact HP.
    + specialize (IH p).
      destruct (search_raw p rest) as [[start n]|] eqn:E.
      * change (SearchScan p (c :: rest) (later (Some (start,n)))).
        now apply SearchLater.
      * change (SearchScan p (c :: rest) (later None)).
        now apply SearchLater.
Qed.
Theorem search_scan_leftmost_longest : forall p text start count,
  SearchScan p text (Some (start,count)) ->
  forall candidate_start candidate_count,
    SearchCandidate p text candidate_start candidate_count ->
    start <= candidate_start /\
      (start = candidate_start -> candidate_count <= count).
Proof.
  intros p text start count H.
  apply search_raw_is_leftmost_longest. symmetry. now apply search_scan_exact.
Qed.

Inductive Render : ReplacementTemplateValue -> Text -> Text -> Prop :=
| RenderEmpty : forall matched, Render ReplacementEmptyValue matched []
| RenderLiteral : forall matched text,
    Render (ReplacementLiteralValue text) matched text
| RenderWhole : forall matched, Render ReplacementWholeValue matched matched
| RenderAppend : forall left right matched lhs rhs,
    Render left matched lhs -> Render right matched rhs ->
    Render (ReplacementAppendValue left right) matched (lhs ++ rhs).
Theorem render_exact : forall template matched output,
  Render template matched output -> output = render_replacement template matched.
Proof. intros template matched output H; induction H; cbn [render_replacement];
  congruence. Qed.
Theorem render_exists : forall template matched,
  Render template matched (render_replacement template matched).
Proof. induction template; intro matched; cbn [render_replacement];
  constructor; auto. Qed.

Inductive ReplaceFirst (p : RegexPattern) (r : ReplacementTemplateValue)
    (text : Text) : Text -> Prop :=
| ReplaceFirstMiss : SearchScan p text None -> ReplaceFirst p r text text
| ReplaceFirstHit : forall start count output,
    SearchScan p text (Some (start,count)) ->
    Render r (matched_segment text start count) output ->
    ReplaceFirst p r text (firstn start text ++ output ++ skipn (start+count) text).
Theorem replace_first_exact : forall p r text output,
  ReplaceFirst p r text output -> output = replace_first p r text.
Proof.
  intros p r text output H; destruct H.
  - symmetry. apply replace_first_miss_is_identity. symmetry.
    now apply search_scan_exact.
  - rewrite (render_exact _ _ _ H0). symmetry.
    apply replace_first_hit_has_the_specified_output. symmetry.
    now apply search_scan_exact.
Qed.

Inductive ReplaceAll (p : RegexPattern) (r : ReplacementTemplateValue)
    : Text -> nat -> Text -> list MatchSpan -> Prop :=
| ReplaceAllMiss : forall text offset,
    SearchScan p text None -> ReplaceAll p r text offset text []
| ReplaceAllPositive : forall text offset start n inserted output spans,
    SearchScan p text (Some (start,S n)) ->
    Render r (matched_segment text start (S n)) inserted ->
    ReplaceAll p r (skipn (start+S n) text) (offset+start+S n) output spans ->
    ReplaceAll p r text offset (firstn start text ++ inserted ++ output)
      (absolute_span offset start (S n) :: spans)
| ReplaceAllFinalEmpty : forall text offset start inserted,
    SearchScan p text (Some (start,0)) -> skipn start text = [] ->
    Render r [] inserted ->
    ReplaceAll p r text offset (firstn start text ++ inserted)
      [absolute_span offset start 0]
| ReplaceAllAdvanceEmpty : forall text offset start c rest inserted output spans,
    SearchScan p text (Some (start,0)) -> skipn start text = c :: rest ->
    Render r [] inserted ->
    ReplaceAll p r rest (offset+start+1) output spans ->
    ReplaceAll p r text offset (firstn start text ++ inserted ++ c :: output)
      (absolute_span offset start 0 :: spans).

Theorem replace_all_refines_reference : forall p r text offset output spans,
  ReplaceAll p r text offset output spans ->
  ReplaceAllPlanSpec p r text offset output spans.
Proof.
  intros p r text offset output spans H; induction H.
  - apply ReplaceAllNoMatch. symmetry. now apply search_scan_exact.
  - rewrite (render_exact _ _ _ H0).
    apply ReplaceAllNonEmpty; [symmetry; now apply search_scan_exact|assumption].
  - rewrite (render_exact _ _ _ H1).
    apply ReplaceAllEmptyAtEnd; [symmetry; now apply search_scan_exact|assumption].
  - rewrite (render_exact _ _ _ H1).
    eapply ReplaceAllEmptyWithProgress with (rest := rest).
    + symmetry. exact (search_scan_exact _ _ _ H).
    + exact H0.
    + exact IHReplaceAll.
Qed.

Theorem replace_all_reference_realized : forall p r text offset output spans,
  ReplaceAllPlanSpec p r text offset output spans ->
  ReplaceAll p r text offset output spans.
Proof.
  intros p r text offset output spans H; induction H.
  - apply ReplaceAllMiss. pose proof (search_scan_exists text p) as HS.
    now rewrite H in HS.
  - eapply ReplaceAllPositive.
    + pose proof (search_scan_exists text p) as HS. now rewrite H in HS.
    + apply render_exists.
    + exact IHReplaceAllPlanSpec.
  - eapply ReplaceAllFinalEmpty.
    + pose proof (search_scan_exists text p) as HS. now rewrite H in HS.
    + exact H0.
    + apply render_exists.
  - eapply ReplaceAllAdvanceEmpty.
    + pose proof (search_scan_exists text p) as HS. now rewrite H in HS.
    + exact H0.
    + apply render_exists.
    + exact IHReplaceAllPlanSpec.
Qed.

Theorem replace_all_frames_complete : forall p r text offset,
  exists output spans, ReplaceAll p r text offset output spans.
Proof.
  intros p r text offset.
  destruct (replace_all_plan_terminates_with_sufficient_fuel
    (S (length text)) p r text offset (Nat.lt_succ_diag_r _))
    as [output [spans H]].
  exists output, spans. apply replace_all_reference_realized.
  now apply replace_all_plan_is_sound in H.
Qed.

Theorem empty_replacement_frame_strictly_progresses : forall p text start,
  SearchScan p text (Some (start,0)) ->
  match skipn start text with
  | [] => start = length text
  | _ :: rest => length rest < length text
  end.
Proof.
  intros p text start H.
  apply (empty_match_either_finishes_or_consumes_a_scalar p text start).
  symmetry. now apply search_scan_exact.
Qed.

Print Assumptions full_scan_exact.
Print Assumptions full_scan_exists.
Print Assumptions prefix_scan_exact.
Print Assumptions prefix_scan_exists.
Print Assumptions search_scan_exact.
Print Assumptions search_scan_exists.
Print Assumptions search_scan_leftmost_longest.
Print Assumptions render_exact.
Print Assumptions render_exists.
Print Assumptions replace_first_exact.
Print Assumptions replace_all_refines_reference.
Print Assumptions replace_all_reference_realized.
Print Assumptions replace_all_frames_complete.
Print Assumptions empty_replacement_frame_strictly_progresses.
End RegexGsltApplicationMachine.
