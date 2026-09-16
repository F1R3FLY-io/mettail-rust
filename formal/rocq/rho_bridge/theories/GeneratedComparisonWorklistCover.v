(** Finite, reply-free expansion of the existing generated comparison jobs.

    Source: iterative_cmp.rs's same-handler inspection interpretation. Jobs
    retain Eq versus Ord, category, and directed original operands. A recipe
    contains native demands, child pushes, virtual deferred Verdict pushes,
    and the existing fixed logical source groups. It is selected by actual
    metadata, not native answers. No production tree or event tape is added.

    PrefixTrace refines the existing leaf-prefix model only by retaining the
    deferred-Verdict marker. Its erasure is that existing SourcePrefix.
    Known deferred Verdict occurrences (Option tags, Vec length, scope
    pattern) contribute a marker too; the scope-pattern RESULT is unknown.
    Unlike eager guards these markers do not stop construction. Known
    Eq shape exits select/truncate that handler's recipe, not the outer stack.

    InspectRun always expands the full recipe and drains its typed jobs.
    ActualPrefix is a COST projection: it permits any local prefix and any
    global early stop, thus includes more traces than native execution. It
    does not return a boolean/Ordering, assert semantic continuation, or feed
    invented replies to the comparison PDA. Previously queued children stay
    in pending; source early exit can discard them without visiting them.

    A completed InspectRun derives finite expansion certificates. Splitting
    those certificates at each actual prefix proves additive coverage for
    every nonnegative coordinate. The final bound is therefore computed from
    inspection, not assumed as a child allowance or an arbitrary polynomial.
    Repeated equal/aliased jobs remain separate list occurrences.

    Instantiate visit_cost with handler contributions, atom_cost with native
    work or child/virtual push counts, one coordinate at a time. A child push
    and its later visit are distinct sites. LocalControl then consumes the
    proved push cover. The caller must associate the recipe with the shared
    emitter and pay inspection before reads/retention; only successful checked
    accumulation may publish an allowance. Overflow/cancellation are not
    erased by these natural-number inequalities. Unordered collection demand
    families, native body bounds, panic unwinding and termination of native
    callbacks are outside this local law. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import GeneratedComparisonInspectionCover
  AdmittedGeneratedComparisonScheduling.
Import ListNotations.

Module GeneratedComparisonWorklistCover.
Module I := GeneratedComparisonInspectionCover.GeneratedComparisonInspectionCover.
Module C := AdmittedGeneratedComparisonScheduling.AdmittedGeneratedComparisonScheduling.

Section TypedJobs.
Context {Category : Type} (Operand : Category -> Type).
Definition Job := (I.Mode * I.Pair Operand)%type.
Inductive Atom :=
| Required (demand : I.Demand Operand)
| VirtualVerdict
| LocalGroup (group : C.SourceGroup).

Definition event_atoms (event : I.Event Operand) :=
  Required (I.demand Operand event) ::
  match event with I.DeferredCmp _ _ _ => [VirtualVerdict] | _ => [] end.
Definition source_atoms := flat_map event_atoms.

Inductive PrefixTrace : list (I.Event Operand) -> list (I.Event Operand) -> Prop :=
| TraceDone : PrefixTrace [] []
| TraceRefused : forall pending, PrefixTrace pending []
| TraceGuard : forall event rest,
    I.stops Operand event = true -> PrefixTrace (event :: rest) [event]
| TraceNext : forall event rest observed,
    I.stops Operand event = false -> PrefixTrace rest observed ->
    PrefixTrace (event :: rest) (event :: observed).

Theorem refined_prefix_erases_to_existing_leaf_prefix : forall events observed,
  PrefixTrace events observed ->
  I.SourcePrefix Operand events (I.inspect Operand observed).
Proof.
  intros events observed PREFIX. induction PREFIX.
  - apply I.PrefixDone.
  - apply I.PrefixRefused.
  - now apply I.PrefixGuardExit.
  - now apply I.PrefixContinues.
Qed.

Theorem refined_prefix_retains_exact_virtual_occurrences : forall events observed,
  PrefixTrace events observed ->
  exists rest, source_atoms events = source_atoms observed ++ rest.
Proof.
  intros events observed PREFIX. induction PREFIX.
  - exists []. reflexivity.
  - exists (source_atoms pending). reflexivity.
  - exists (source_atoms rest).
    change (event_atoms event ++ source_atoms rest =
      (event_atoms event ++ []) ++ source_atoms rest). now rewrite app_nil_r.
  - destruct IHPREFIX as [suffix SAME]. exists suffix.
    change (event_atoms event ++ source_atoms rest =
      (event_atoms event ++ source_atoms observed) ++ suffix).
    rewrite SAME, app_assoc. reflexivity.
Qed.

Theorem deferred_native_construction_keeps_one_virtual_verdict : forall pair reply,
  event_atoms (I.DeferredCmp Operand pair reply) =
    [Required (I.NativeCmp Operand pair); VirtualVerdict].
Proof. reflexivity. Qed.

Definition atom_children atom : list Job := match atom with
  | Required (I.ChildPair _ mode operands) => [(mode, operands)]
  | _ => [] end.
Definition children := flat_map atom_children.
Lemma children_app : forall first second,
  children (first ++ second) = children first ++ children second.
Proof. intros. apply flat_map_app. Qed.

Variable recipe : Job -> list Atom.
Variable visit_cost : Job -> nat.
Variable atom_cost : Atom -> nat.
Definition local_cost atoms := fold_right (fun atom total => atom_cost atom + total) 0 atoms.
Lemma local_cost_app : forall first second,
  local_cost (first ++ second) = local_cost first + local_cost second.
Proof.
  induction first as [|atom first IH]; intro second; [reflexivity|].
  change (atom_cost atom + local_cost (first ++ second) =
    (atom_cost atom + local_cost first) + local_cost second).
  rewrite IH. lia.
Qed.

(** Certificates are finite derivations, not additional runtime syntax.
    Their numerical totals are determined solely by the original recipes. *)
Inductive FullJob : Job -> nat -> Prop :=
| ExpandJob : forall job descendants,
    FullForest (children (recipe job)) descendants ->
    FullJob job (visit_cost job + local_cost (recipe job) + descendants)
with FullForest : list Job -> nat -> Prop :=
| ForestEmpty : FullForest [] 0
| ForestNext : forall job pending own rest,
    FullJob job own -> FullForest pending rest ->
    FullForest (job :: pending) (own + rest).

Lemma forest_append : forall first own,
  FullForest first own -> forall second rest,
  FullForest second rest -> FullForest (first ++ second) (own + rest).
Proof.
  intros first own FOREST. induction FOREST; intros second extra NEXT.
  - exact NEXT.
  - change (FullForest (job :: (pending ++ second)) ((own + rest) + extra)).
    replace ((own + rest) + extra) with (own + (rest + extra)) by lia.
    apply ForestNext; [assumption|]. now apply IHFOREST.
Qed.

Lemma forest_split : forall first second total,
  FullForest (first ++ second) total ->
  exists own rest, FullForest first own /\ FullForest second rest /\ total = own + rest.
Proof.
  induction first as [|job first IH]; intros second total FOREST.
  - exists 0, total. repeat split; try constructor; assumption.
  - inversion FOREST as [|head tail own rest JOB TAIL]; subst.
    destruct (IH second rest TAIL) as [front [back [FRONT [BACK SUM]]]].
    exists (own + front), back. split.
    + now apply ForestNext.
    + split; [exact BACK|lia].
Qed.

Lemma forest_reverse : forall jobs total,
  FullForest jobs total -> FullForest (rev jobs) total.
Proof.
  intros jobs total FOREST. induction FOREST.
  - constructor.
  - cbn [rev]. replace (own + rest) with (rest + own) by lia.
    apply forest_append; [exact IHFOREST|].
    replace own with (own + 0) by lia. apply ForestNext; [assumption|constructor].
Qed.

Inductive InspectRun : list Job -> nat -> Prop :=
| InspectDone : InspectRun [] 0
| InspectNext : forall job pending rest,
    InspectRun (rev (children (recipe job)) ++ pending) rest ->
    InspectRun (job :: pending) (visit_cost job + local_cost (recipe job) + rest).

Theorem completed_inspection_derives_its_finite_expansion : forall pending total,
  InspectRun pending total -> FullForest pending total.
Proof.
  intros pending total RUN. induction RUN.
  - constructor.
  - destruct (forest_split _ _ _ IHRUN) as [descendants [tail [CHILDREN [TAIL SUM]]]].
    apply forest_reverse in CHILDREN. rewrite rev_involutive in CHILDREN.
    rewrite SUM. replace (visit_cost job + local_cost (recipe job) + (descendants + tail))
      with ((visit_cost job + local_cost (recipe job) + descendants) + tail) by lia.
    apply ForestNext; [now apply ExpandJob|exact TAIL].
Qed.

Inductive ActualPrefix : list Job -> nat -> Prop :=
| ActualStop : forall pending, ActualPrefix pending 0
| ActualNext : forall job pending observed suffix rest,
    recipe job = observed ++ suffix ->
    ActualPrefix (rev (children observed) ++ pending) rest ->
    ActualPrefix (job :: pending) (visit_cost job + local_cost observed + rest).

Theorem finite_expansion_covers_every_actual_prefix : forall pending actual,
  ActualPrefix pending actual -> forall inspected,
  FullForest pending inspected -> actual <= inspected.
Proof.
  intros pending actual RUN. induction RUN; intros inspected FOREST.
  - lia.
  - inversion FOREST as [|head tail own remaining JOB TAIL]; subst.
    inversion JOB as [original descendants CHILDREN]; subst.
    rewrite H, children_app in CHILDREN.
    destruct (forest_split _ _ _ CHILDREN) as [first [second [FIRST [SECOND SUM]]]].
    pose proof (forest_reverse _ _ FIRST) as REVERSE.
    pose proof (forest_append _ _ REVERSE _ _ TAIL) as PENDING.
    specialize (IHRUN _ PENDING).
    rewrite H, local_cost_app. lia.
Qed.

Theorem completed_inspection_covers_original_local_worklist :
  forall pending actual inspected,
  ActualPrefix pending actual -> InspectRun pending inspected -> actual <= inspected.
Proof.
  intros pending actual inspected ACTUAL INSPECT.
  eapply finite_expansion_covers_every_actual_prefix; [exact ACTUAL|].
  now apply completed_inspection_derives_its_finite_expansion.
Qed.

(** With a cost of one on child pushes and virtual Verdicts, and zero on
    visits/native calls, the previous theorem is exactly the missing later
    push-count cover used by GeneratedComparisonLocalControl. Native costs
    and fixed visit/field groups use the SAME theorem, not new traces. *)
Definition push_occurrence atom := match atom with
  | Required (I.ChildPair _ _ _) | VirtualVerdict => 1
  | _ => 0 end.
Theorem known_deferred_verdict_is_one_push_not_a_child :
  push_occurrence VirtualVerdict = 1 /\ atom_children VirtualVerdict = [].
Proof. split; reflexivity. Qed.
Theorem duplicate_child_occurrences_are_not_deduplicated : forall mode pair,
  children [Required (I.ChildPair Operand mode pair); Required (I.ChildPair Operand mode pair)] =
    [(mode, pair); (mode, pair)].
Proof. reflexivity. Qed.

End TypedJobs.

Theorem completed_inspection_covers_later_push_count :
  forall Category (Operand : Category -> Type) recipe pending actual inspected,
  @ActualPrefix Category Operand recipe (fun _ => 0) (push_occurrence Operand) pending actual ->
  @InspectRun Category Operand recipe (fun _ => 0) (push_occurrence Operand) pending inspected ->
  actual <= inspected.
Proof. intros. eapply completed_inspection_covers_original_local_worklist; eassumption. Qed.

(** Ordinary handler base, using the established logical groups only.
    ShallowOperand belongs to CHECKED support prechecks and is absent here.
    Entry/return routing is included in these groups, not charged again.
    Field/scope/iterator and native payload work remain separate. *)
Inductive HandlerBranch := EqAlias | EqIndexMismatch | EqMatched | OrdIndexMismatch | OrdMatched.
Definition handler_groups branch := match branch with
  | EqAlias => [C.EqPointerCheck]
  | EqIndexMismatch => [C.EqPointerCheck; C.IndexProjections; C.IndexNe]
  | EqMatched => [C.EqPointerCheck; C.IndexProjections; C.IndexNe; C.VariantRoute]
  | OrdIndexMismatch => [C.IndexProjections; C.IndexNe; C.IndexCmp]
  | OrdMatched => [C.IndexProjections; C.IndexNe; C.VariantRoute] end.
Definition fixed_work groups := fold_right (fun group total => C.group_work group + total) 0 groups.
Theorem ordinary_handler_base_is_at_most_six : forall branch,
  fixed_work (handler_groups branch) <= 6.
Proof. destruct branch; cbn [fixed_work handler_groups fold_right C.group_work]; lia. Qed.
Theorem ordinary_handler_base_has_no_checked_support_projection : forall branch,
  ~ In C.ShallowOperand (handler_groups branch).
Proof. destruct branch; cbn [handler_groups In]; intuition discriminate. Qed.

Print Assumptions refined_prefix_erases_to_existing_leaf_prefix.
Print Assumptions refined_prefix_retains_exact_virtual_occurrences.
Print Assumptions deferred_native_construction_keeps_one_virtual_verdict.
Print Assumptions completed_inspection_derives_its_finite_expansion.
Print Assumptions finite_expansion_covers_every_actual_prefix.
Print Assumptions completed_inspection_covers_original_local_worklist.
Print Assumptions completed_inspection_covers_later_push_count.
Print Assumptions duplicate_child_occurrences_are_not_deduplicated.
Print Assumptions ordinary_handler_base_is_at_most_six.
Print Assumptions ordinary_handler_base_has_no_checked_support_projection.
End GeneratedComparisonWorklistCover.
