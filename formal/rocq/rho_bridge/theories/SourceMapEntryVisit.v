(** Paid original-pair visitation for HashMapLit.

    Source: runtime/src/hashmap_lit.rs, the iterator body shared by
    try_comparison_roster and try_for_each_entry. IndexMap 2.14.0 Iter::next
    advances its contiguous slice and projects Bucket::refs; unlike HashBag,
    no hidden table scan is present. The existing roster model already uses
    this source association. This refinement preserves its setup/next charges
    while making the consumer explicit, without allocating another roster.

    Walk constructors are the actual next/visitor branches: they retain the
    original head pair, the exact remaining suffix, and the same allowance.
    Every visitor attempt follows a successful next reservation. No arbitrary
    trace or supplied loop bound can create an extra or reordered visit.
    A visitor can fail or have separately paid effects; no bound or rollback
    law for those effects is assumed here. Walk counts successful next
    reservations; EntryVisit additionally counts successful iterator setup.
    Neither includes failed reservations or the visitor's own charges.

    The pair labels denote original immutable borrows, not cloned terms.
    Rust retains their types/lifetimes and moves the original error payload.
    Profile refusal and the wrapper's length/roster allocation charges are
    outside this shared loop; public visitation checks the profile first. *)
From Stdlib Require Import List Arith.PeanoNat Lia Sorting.Permutation.
From RhoBridge Require Import RholangInitialGraphResources.
Import ListNotations.

Module SourceMapEntryVisit.
Section OriginalPairs.
Context {Key Value State : Type}.
Definition Pair := (Key * Value)%type.
Variable visit : Pair -> State -> Allowance -> State * ActionResult unit.

Inductive Walk : list Pair -> State -> Allowance -> State -> ActionResult unit ->
    nat -> list Pair -> Prop :=
| NextRefused : forall pairs state available,
    reserve available 1 0 = None ->
    Walk pairs state available state (Refused available) 0 []
| EndReached : forall state available paid,
    reserve available 1 0 = Some paid ->
    Walk [] state available state (Accepted paid tt) 1 []
| VisitorRefused : forall pair rest state available paid final remaining,
    reserve available 1 0 = Some paid ->
    visit pair state paid = (final, Refused remaining) ->
    Walk (pair :: rest) state available final (Refused remaining) 1 [pair]
| VisitorAccepted : forall pair rest state available paid middle after_visit final result
    steps observed,
    reserve available 1 0 = Some paid ->
    visit pair state paid = (middle, Accepted after_visit tt) ->
    Walk rest middle after_visit final result steps observed ->
    Walk (pair :: rest) state available final result (S steps) (pair :: observed).

Theorem visits_are_an_exact_original_prefix : forall pairs state available final result steps observed,
  Walk pairs state available final result steps observed ->
  exists suffix, pairs = observed ++ suffix.
Proof.
  intros pairs state available final result steps observed RUN. induction RUN.
  - exists pairs. reflexivity.
  - exists []. reflexivity.
  - exists rest. reflexivity.
  - destruct IHRUN as [suffix SAME]. exists suffix. cbn. now rewrite SAME.
Qed.

Theorem successful_visitation_keeps_every_pair_and_terminal_next :
  forall pairs state available final remaining steps observed,
  Walk pairs state available final (Accepted remaining tt) steps observed ->
  observed = pairs /\ steps = S (length pairs).
Proof.
  intros pairs state available final remaining steps observed RUN.
  remember (Accepted remaining tt) as result eqn:RESULT.
  induction RUN; try discriminate.
  - cbn. auto.
  - specialize (IHRUN RESULT). cbn. intuition congruence.
Qed.

Theorem every_attempt_has_a_paid_next_and_only_terminal_next_is_extra :
  forall pairs state available final result steps observed,
  Walk pairs state available final result steps observed ->
  length observed <= steps <= S (length observed).
Proof. intros pairs state available final result steps observed RUN.
  induction RUN; cbn in *; lia. Qed.

Theorem refusal_before_next_cannot_visit :
  forall pairs state available final result steps observed,
  reserve available 1 0 = None -> Walk pairs state available final result steps observed ->
  final = state /\ result = Refused available /\ steps = 0 /\ observed = [].
Proof. intros pairs state available final result steps observed REFUSAL RUN.
  inversion RUN; subst; try congruence. auto. Qed.

Theorem visitor_refusal_cannot_visit_the_suffix :
  forall pair rest state available paid stopped remaining final result steps observed,
  reserve available 1 0 = Some paid -> visit pair state paid = (stopped, Refused remaining) ->
  Walk (pair :: rest) state available final result steps observed ->
  final = stopped /\ result = Refused remaining /\ steps = 1 /\ observed = [pair].
Proof. intros pair rest state available paid stopped remaining final result steps observed
    NEXT VISIT RUN.
  inversion RUN; subst; try congruence.
  assert (paid0 = paid) by congruence. subst paid0. intuition congruence.
Qed.

(** The mathematical callback describes completed normal returns. This is
    finite iteration, not a termination or panic proof for arbitrary Rust code. *)
Theorem finite_source_has_a_result_without_fuel : forall pairs state available,
  exists final result steps observed, Walk pairs state available final result steps observed.
Proof.
  induction pairs as [|pair rest IH]; intros state available;
    destruct (reserve available 1 0) as [paid|] eqn:NEXT.
  - exists state, (Accepted paid tt), 1, []. now constructor.
  - exists state, (Refused available), 0, []. now constructor.
  - destruct (visit pair state paid) as [middle result] eqn:VISIT.
    destruct result as [remaining|remaining []].
    + exists middle, (Refused remaining), 1, [pair]. eapply VisitorRefused; eassumption.
    + destruct (IH middle remaining) as [final [result [steps [observed RUN]]]].
      exists final, result, (S steps), (pair :: observed).
      eapply VisitorAccepted; eassumption.
  - exists state, (Refused available), 0, []. now constructor.
Qed.

Inductive EntryVisit : list Pair -> State -> Allowance -> State -> ActionResult unit ->
    nat -> list Pair -> Prop :=
| SetupRefused : forall pairs state available,
    reserve available 1 0 = None ->
    EntryVisit pairs state available state (Refused available) 0 []
| SetupAccepted : forall pairs state available paid final result steps observed,
    reserve available 1 0 = Some paid ->
    Walk pairs state paid final result steps observed ->
    EntryVisit pairs state available final result (S steps) observed.

Theorem successful_helper_pays_setup_and_every_next :
  forall pairs state available final remaining steps observed,
  EntryVisit pairs state available final (Accepted remaining tt) steps observed ->
  observed = pairs /\ steps = 2 + length pairs.
Proof.
  intros pairs state available final remaining steps observed RUN. inversion RUN; subst.
  apply successful_visitation_keeps_every_pair_and_terminal_next in H0. lia || intuition lia.
Qed.

Theorem setup_refusal_preserves_visitor_state_and_has_no_visits :
  forall pairs state available final result steps observed,
  reserve available 1 0 = None ->
  EntryVisit pairs state available final result steps observed ->
  final = state /\ result = Refused available /\ steps = 0 /\ observed = [].
Proof.
  intros pairs state available final result steps observed REFUSAL RUN.
  inversion RUN; subst; try congruence. auto.
Qed.

(** No semantic equality, key hashing or sorting is used to obtain this sum.
    Its use as a native allowance still requires source-specific leaf costs
    and an independent proof that the actual native sort permutes whole pairs.
    This algebra alone does not cover sorting or generated traversal work. *)
Definition leaf_sum (key_work : Key -> nat) (value_work : Value -> nat) pairs :=
  fold_right (fun pair total => key_work (fst pair) + value_work (snd pair) + total) 0 pairs.

Theorem whole_pair_permutation_preserves_leaf_sum :
  forall key_work value_work original reordered,
  Permutation original reordered ->
  leaf_sum key_work value_work original = leaf_sum key_work value_work reordered.
Proof.
  intros key_work value_work original reordered ORDER. induction ORDER.
  - reflexivity.
  - unfold leaf_sum in *. cbn [fold_right]. now rewrite IHORDER.
  - cbn [leaf_sum fold_right]. lia.
  - now rewrite IHORDER1, IHORDER2.
Qed.
End OriginalPairs.
End SourceMapEntryVisit.

Print Assumptions SourceMapEntryVisit.visits_are_an_exact_original_prefix.
Print Assumptions SourceMapEntryVisit.successful_visitation_keeps_every_pair_and_terminal_next.
Print Assumptions SourceMapEntryVisit.every_attempt_has_a_paid_next_and_only_terminal_next_is_extra.
Print Assumptions SourceMapEntryVisit.refusal_before_next_cannot_visit.
Print Assumptions SourceMapEntryVisit.visitor_refusal_cannot_visit_the_suffix.
Print Assumptions SourceMapEntryVisit.finite_source_has_a_result_without_fuel.
Print Assumptions SourceMapEntryVisit.successful_helper_pays_setup_and_every_next.
Print Assumptions SourceMapEntryVisit.setup_refusal_preserves_visitor_state_and_has_no_visits.
Print Assumptions SourceMapEntryVisit.whole_pair_permutation_preserves_leaf_sum.
