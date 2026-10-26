(** Completion of the existing binder-sensitive freshness worklist.

    Reuses SemanticTransitionKernel.FreeOccurrence and freshness_step.  The
    worklist is a proof view of freshness_holds in semantic_transition_kernel.rs,
    not another production evaluator.  Its head is the next pop; reverse pushes
    of plain children therefore become children ++ pending.  The visited list
    models set membership, not iteration order.  Equality with the needle is
    tested before visited membership, just as in Rust.

    SuccessfulRun contains only completed Boolean outcomes.  Allocation,
    cancellation and work-exhaustion refusals do not manufacture a verdict.
    A popped, previously unvisited non-needle vertex requiring malformed graph
    decoding has no Boolean verdict.  Equality with the needle needs no node
    decoding, and shielded bodies need not be inspected.  No totality claim is
    made for an infinite graph or an
    insufficient budget.  Graph vertices denote canonical e-class IDs; the
    concrete graph decoder and its source-value interpretation remain separate
    representation obligations.  The graph is immutable during freshness.

    Two invariants suffice even with sharing and cycles: every scheduled or
    visited vertex is reachable by binder-sensitive edges from the target; and
    every visited vertex has been inspected, is not the needle, and has all its
    traversable children covered by visited or pending vertices.  Exhaustion
    closes that set.  Induction on a finite FreeOccurrence derivation then
    proves that no closed visited vertex contains a free occurrence.
*)
From Stdlib Require Import List Bool PeanoNat.
From RuntimeGrammar Require Import SemanticTransitionKernel.
Import ListNotations.

Module FreshnessWorklist.
Module K := SemanticTransitionKernel.

Section Graph.
Context (graph : K.RuntimeFreshnessGraph) (needle : nat).

Lemma continue_excludes_needle : forall root children,
  K.freshness_step graph needle root = K.FreshnessContinue children ->
  root <> needle.
Proof.
  intros root children Hstep. unfold K.freshness_step in Hstep.
  destruct (Nat.eqb root needle) eqn:Heq; try discriminate.
  now apply Nat.eqb_neq.
Qed.

Lemma continue_occurrence_iff : forall root children,
  K.freshness_step graph needle root = K.FreshnessContinue children ->
  (K.FreeOccurrence graph needle root <->
   exists child, In child children /\ K.FreeOccurrence graph needle child).
Proof.
  intros root children Hstep.
  pose proof (continue_excludes_needle _ _ Hstep) as Hneq.
  unfold K.freshness_step in Hstep.
  destruct (Nat.eqb root needle) eqn:Heq; try discriminate.
  destruct (graph root) as [node|] eqn:Hgraph; try discriminate.
  destruct node as [plain|binder body].
  - inversion Hstep; subst children. split.
    + intro Hocc. inversion Hocc; subst; try contradiction.
      * rewrite Hgraph in H. inversion H; subst. eauto.
      * rewrite Hgraph in H. discriminate.
    + intros [child [Hin Hocc]]. eapply K.FreeOccurrencePlain; eauto.
  - destruct (Nat.eqb binder needle) eqn:Hbinder.
    + apply Nat.eqb_eq in Hbinder. subst binder.
      inversion Hstep; subst children. split.
      * intro Hocc. exfalso.
        eapply K.matching_abstraction_binder_shields_every_body_occurrence;
          eauto.
      * intros [child [Hin _]]. contradiction.
    + apply Nat.eqb_neq in Hbinder. inversion Hstep; subst children.
      split.
      * intro Hocc. exists body. split; [now left|].
        apply (proj2 (K.different_abstraction_binder_preserves_body_freedom
          graph root needle binder body Hneq Hbinder Hgraph)). exact Hocc.
      * intros [child [Hin Hocc]]. destruct Hin as [<-|Hin];
          [|contradiction].
        eapply K.FreeOccurrenceAbstraction; eauto.
Qed.

Inductive Reachable (target : nat) : nat -> Prop :=
| reachable_target : Reachable target target
| reachable_child : forall root children child,
    Reachable target root ->
    K.freshness_step graph needle root = K.FreshnessContinue children ->
    In child children -> Reachable target child.

Lemma reachable_occurrence_lifts : forall target vertex,
  Reachable target vertex ->
  K.FreeOccurrence graph needle vertex ->
  K.FreeOccurrence graph needle target.
Proof.
  intros target vertex Hreach. induction Hreach; intro Hocc; auto.
  apply IHHreach. apply (proj2 (continue_occurrence_iff _ _ H)). eauto.
Qed.

Definition Covered (visited pending : list nat) (vertex : nat) :=
  In vertex visited \/ In vertex pending.

Record Invariant (target : nat) (visited pending : list nat) : Prop := {
  target_covered : Covered visited pending target;
  all_reachable : forall vertex, Covered visited pending vertex ->
    Reachable target vertex;
  visited_closed : forall vertex, In vertex visited ->
    exists children,
      K.freshness_step graph needle vertex = K.FreshnessContinue children /\
      forall child, In child children -> Covered visited pending child
}.

Lemma initial_invariant : forall target, Invariant target [] [target].
Proof.
  intro target. constructor.
  - right. now left.
  - intros vertex [H|[H|H]]; try contradiction. subst. constructor.
  - intros vertex H. contradiction.
Qed.

Lemma skip_coverage : forall visited pending vertex item,
  In vertex visited -> Covered visited (vertex :: pending) item ->
  Covered visited pending item.
Proof.
  intros visited pending vertex item Hin [H|[H|H]];
    unfold Covered; auto. subst. auto.
Qed.

Lemma skip_preserves_invariant : forall target visited pending vertex,
  Invariant target visited (vertex :: pending) -> In vertex visited ->
  Invariant target visited pending.
Proof.
  intros target visited pending vertex Hinv Hin.
  destruct Hinv as [Htarget Hreach Hclosed]. constructor.
  - apply (skip_coverage visited pending vertex target Hin Htarget).
  - intros item Hitem. apply Hreach.
    destruct Hitem as [Hitem|Hitem]; [now left|right; now right].
  - intros item Hitem. destruct (Hclosed item Hitem) as [children [Hstep Hall]].
    exists children. split; [exact Hstep|]. intros child Hchild.
    apply (skip_coverage visited pending vertex child Hin).
    now apply Hall.
Qed.

Lemma expand_coverage : forall visited pending vertex children item,
  Covered visited (vertex :: pending) item ->
  Covered (vertex :: visited) (children ++ pending) item.
Proof.
  intros visited pending vertex children item [H|[H|H]];
    unfold Covered.
  - left. now right.
  - left. now left.
  - right. apply in_or_app. now right.
Qed.

Lemma expand_preserves_invariant : forall target visited pending vertex children,
  Invariant target visited (vertex :: pending) ->
  K.freshness_step graph needle vertex = K.FreshnessContinue children ->
  Invariant target (vertex :: visited) (children ++ pending).
Proof.
  intros target visited pending vertex children Hinv Hstep.
  destruct Hinv as [Htarget Hreach Hclosed]. constructor.
  - now apply expand_coverage.
  - intros item [[Hitem|Hitem]|Hitem].
    + subst item. apply Hreach. right. now left.
    + apply Hreach. now left.
    + apply in_app_or in Hitem. destruct Hitem as [Hitem|Hitem].
      * eapply reachable_child with (root := vertex) (children := children).
        -- apply Hreach. right. now left.
        -- exact Hstep.
        -- exact Hitem.
      * apply Hreach. right. now right.
  - intros item [Hitem|Hitem].
    + subst item. exists children. split; [exact Hstep|].
      intros child Hchild. right. apply in_or_app. now left.
    + destruct (Hclosed item Hitem) as [next [Hnext Hall]].
      exists next. split; [exact Hnext|]. intros child Hchild.
      apply expand_coverage. now apply Hall.
Qed.

(** No acyclicity premise: the occurrence derivation, not the graph, is the
    well-founded induction argument. *)
Lemma closed_vertices_are_fresh : forall visited,
  (forall vertex, In vertex visited ->
    exists children,
      K.freshness_step graph needle vertex = K.FreshnessContinue children /\
      forall child, In child children -> In child visited) ->
  forall vertex, K.FreeOccurrence graph needle vertex -> ~ In vertex visited.
Proof.
  intros visited Hclosed vertex Hocc. induction Hocc; intro Hin.
  - destruct (Hclosed needle Hin) as [next [Hstep _]].
    exact (continue_excludes_needle _ _ Hstep eq_refl).
  - destruct (Hclosed root Hin) as [next [Hstep Hall]].
    unfold K.freshness_step in Hstep.
    destruct (Nat.eqb root needle); try discriminate.
    rewrite H in Hstep. inversion Hstep; subst next.
    apply IHHocc. now apply Hall.
  - destruct (Hclosed root Hin) as [next [Hstep Hall]].
    unfold K.freshness_step in Hstep.
    destruct (Nat.eqb root needle); try discriminate.
    rewrite H in Hstep.
    destruct (Nat.eqb binder needle) eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + inversion Hstep; subst next. apply IHHocc. apply Hall. now left.
Qed.

Lemma exhausted_invariant_is_fresh : forall target visited,
  Invariant target visited [] -> K.freshness_holds graph needle target.
Proof.
  intros target visited [Htarget Hreach Hclosed].
  destruct Htarget as [Hin|Hin]; [|contradiction].
  unfold K.freshness_holds. intro Hocc.
  eapply closed_vertices_are_fresh; [|exact Hocc|exact Hin].
  intros vertex Hvertex. destruct (Hclosed vertex Hvertex) as [next [Hstep Hall]].
  exists next. split; [exact Hstep|]. intros child Hchild.
  destruct (Hall child Hchild); [assumption|contradiction].
Qed.

Inductive SuccessfulRun : list nat -> list nat -> bool -> Prop :=
| run_exhausted : forall visited, SuccessfulRun visited [] true
| run_found : forall visited pending,
    SuccessfulRun visited (needle :: pending) false
| run_skip : forall visited pending vertex result,
    vertex <> needle -> In vertex visited ->
    SuccessfulRun visited pending result ->
    SuccessfulRun visited (vertex :: pending) result
| run_expand : forall visited pending vertex children result,
    ~ In vertex visited ->
    K.freshness_step graph needle vertex = K.FreshnessContinue children ->
    SuccessfulRun (vertex :: visited) (children ++ pending) result ->
    SuccessfulRun visited (vertex :: pending) result.

Definition Verdict (target : nat) (result : bool) :=
  if result then K.freshness_holds graph needle target
  else K.FreeOccurrence graph needle target.

Theorem completed_worklist_verdict : forall visited pending result,
  SuccessfulRun visited pending result ->
  forall target, Invariant target visited pending -> Verdict target result.
Proof.
  intros visited pending result Hrun. induction Hrun;
    intros target Hinv.
  - simpl. now apply exhausted_invariant_is_fresh with (visited := visited).
  - simpl. eapply reachable_occurrence_lifts; [|constructor].
    apply (all_reachable _ _ _ Hinv). right. now left.
  - apply IHHrun. eapply skip_preserves_invariant; eauto.
  - apply IHHrun. eapply expand_preserves_invariant; eauto.
Qed.

Theorem successful_freshness_is_exact : forall target result,
  SuccessfulRun [] [target] result ->
  ((result = true <-> K.freshness_holds graph needle target) /\
   (result = false <-> K.FreeOccurrence graph needle target)).
Proof.
  intros target result Hrun.
  pose proof (completed_worklist_verdict _ _ _ Hrun target
    (initial_invariant target)) as Hverdict.
  destruct result; simpl in Hverdict; unfold K.freshness_holds in *;
    split; split; intros; try reflexivity; try assumption;
    try discriminate; contradiction.
Qed.

Theorem success_never_has_opposite_verdicts : forall target,
  SuccessfulRun [] [target] true ->
  SuccessfulRun [] [target] false -> False.
Proof.
  intros target Htrue Hfalse.
  pose proof (completed_worklist_verdict _ _ _ Htrue target
    (initial_invariant target)) as Hfresh.
  pose proof (completed_worklist_verdict _ _ _ Hfalse target
    (initial_invariant target)) as Hocc.
  exact (Hfresh Hocc).
Qed.

Theorem malformed_unvisited_vertex_has_no_boolean_verdict :
  forall visited pending vertex result,
    vertex <> needle -> ~ In vertex visited -> graph vertex = None ->
    ~ SuccessfulRun visited (vertex :: pending) result.
Proof.
  intros visited pending vertex result Hneq Hnew Hmissing Hrun.
  inversion Hrun; subst; try contradiction.
  match goal with
  | Hstep : K.freshness_step graph needle vertex = _ |- _ =>
      unfold K.freshness_step in Hstep;
      rewrite Hmissing in Hstep;
      destruct (Nat.eqb vertex needle); discriminate
  end.
Qed.

End Graph.

(** A finite cyclic graph needs no recursive descent or acyclicity premise.
    This is a graph-model control, not a claim that the public e-graph API
    admits a singleton cyclic e-class. *)
Example self_cycle_without_needle_finishes_fresh :
  SuccessfulRun (fun _ => Some (K.RuntimePlainNode [1])) 0 [] [1] true.
Proof.
  eapply run_expand with (children := [1]).
  - simpl. tauto.
  - reflexivity.
  - apply run_skip; [discriminate|now left|constructor].
Qed.

Example matching_binder_hides_an_invalid_body :
  SuccessfulRun
    (fun root => if Nat.eqb root 1
      then Some (K.RuntimeAbstractionNode 0 2) else None)
    0 [] [1] true.
Proof.
  eapply run_expand with (children := []).
  - simpl. tauto.
  - reflexivity.
  - constructor.
Qed.

Print Assumptions completed_worklist_verdict.
Print Assumptions successful_freshness_is_exact.
Print Assumptions success_never_has_opposite_verdicts.
Print Assumptions malformed_unvisited_vertex_has_no_boolean_verdict.
End FreshnessWorklist.
