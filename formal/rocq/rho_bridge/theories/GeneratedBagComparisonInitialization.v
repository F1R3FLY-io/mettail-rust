(** Initialization correspondence for the existing generated Bag comparison.
    Original immutable source pairs retain native iteration order and counts.
    The adapter below uses the existing checked roster operation; it does not
    implement a Bag sort, a counts-map equality algorithm, or another executor.
    Successful construction excludes zero repetitions and checked-sum overflow.
    Source totals used as the comparison lead are separate from these sums.

    Source bindings: HashBag::try_comparison_roster uses the paid next-based
    native scan. Ordinary map/collect and its possible native fold specialization
    enumerate the same ordered FULL positions; only the checked next path has
    the borrowed-scan cost proof. Both convert each original borrowed key/count
    into CollectionCmpItem with absent secondary and unchanged repetitions. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RhoBridge Require Import AdmittedCollectionComparisonOwnership.
Import ListNotations.

Module GeneratedBagComparisonInitialization.
Import AdmittedCollectionComparisonOwnership.AdmittedCollectionComparisonOwnership.

Section RepeatedSource.
Context {Primary Secondary : Type}.

Definition repeated_entry (pair : Primary * nat) : @Entry Primary Secondary :=
  {| primary := fst pair; secondary := None; repetitions := snd pair |}.
Definition source_count (source : list (Primary * nat)) :=
  fold_right (fun pair total => snd pair + total) 0 source.
Fixpoint append_repeated maximum source (roster : @Roster Primary Secondary) :=
  match source with
  | [] => Built roster
  | entry_pair :: rest => match try_push maximum roster (repeated_entry entry_pair) with
      | Built next => append_repeated maximum rest next
      | Rejected reason => Rejected reason
      end
  end.

Lemma repeated_entries_have_the_original_sum : forall source,
  repetition_sum (map repeated_entry source) = source_count source.
Proof.
  intro source. induction source as [|pair rest IH];
    cbn [repetition_sum source_count fold_right map repeated_entry repetitions];
    [reflexivity|now rewrite IH].
Qed.

Theorem successful_repeated_walk_preserves_original_counts :
  forall maximum source roster final,
    valid_roster roster -> running_total roster <= maximum ->
    append_repeated maximum source roster = Built final ->
    valid_roster final /\ reserved_width final = reserved_width roster /\
    entries final = entries roster ++ map repeated_entry source /\
    running_total final = running_total roster + source_count source /\
    running_total final <= maximum.
Proof.
  intros maximum source. induction source as [|pair rest IH];
    intros roster final VALID BOUND BUILT.
  - cbn [append_repeated] in BUILT. inversion BUILT; subst final.
    cbn [source_count fold_right map]. rewrite app_nil_r.
    split; [exact VALID|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|exact BOUND].
  - cbn [append_repeated] in BUILT.
    destruct (try_push maximum roster (repeated_entry pair)) as [next|reason]
      eqn:PUSH; [|discriminate].
    destruct (successful_push_preserves_prefix_width_and_total
      maximum roster (repeated_entry pair) next VALID PUSH)
      as [VN [WIDTH [ENTRIES [TOTAL BN]]]].
    destruct (IH next final VN BN BUILT) as [VF [WF [EF [TF BF]]]].
    split; [exact VF|]. split; [now rewrite WF, WIDTH|]. split.
    + rewrite EF, ENTRIES. cbn [map]. now rewrite <- app_assoc.
    + split; [|exact BF]. rewrite TF, TOTAL.
      change (running_total roster + snd pair + source_count rest =
        running_total roster + (snd pair + source_count rest)). lia.
Qed.

Theorem complete_repeated_roster_matches_ordinary : forall maximum source final,
  append_repeated maximum source (empty_roster (length source)) = Built final ->
  valid_roster final /\ entries final = map repeated_entry source /\
  reserved_width final = length source /\
  running_total final = source_count source /\ running_total final <= maximum.
Proof.
  intros maximum source final BUILT.
  destruct (successful_repeated_walk_preserves_original_counts maximum source
    (empty_roster (length source)) final (empty_roster_is_valid _) ltac:(cbn; lia) BUILT)
    as [VALID [WIDTH [ENTRIES [TOTAL BOUND]]]].
  cbn [empty_roster entries reserved_width running_total app] in *.
  exact (conj VALID (conj ENTRIES (conj WIDTH (conj TOTAL BOUND)))).
Qed.

(** The five arguments below are exactly those of the shared from_parts
    initializer: supplied stored-total lead, original left/right item vectors,
    and their repetition sums. [initialize] is constructor congruence, not a
    comparison-result oracle. Its source instantiation is the successful
    payload of that SAME initializer under either unit-returning policy.
    Source field audit: phase Lead, pending None, supplied lead and sums,
    indices and remaining counters zero. Each merge starts with source intact,
    target None, width one, start/left/output zero, waiting false, done from
    source length; reset_run sets middle=min(1,length), end=min(2,length), and
    right=middle. No field depends on successful policy unit values.
    Subsequent request preservation uses the existing shared-source policy
    erasure theorem with actual source events and identical typed answers;
    neither a new Bag canonical result nor Map-only factorization is proved. *)
Theorem successful_repeated_rosters_supply_identical_constructor_arguments :
  forall (Core : Type)
    (initialize : comparison -> list (@Entry Primary Secondary) ->
      list (@Entry Primary Secondary) -> nat -> nat -> Core)
    maximum lead left_source right_source left_roster right_roster,
  append_repeated maximum left_source (empty_roster (length left_source)) =
    Built left_roster ->
  append_repeated maximum right_source (empty_roster (length right_source)) =
    Built right_roster ->
  initialize lead (entries left_roster) (entries right_roster)
    (running_total left_roster) (running_total right_roster) =
  initialize lead (map repeated_entry left_source) (map repeated_entry right_source)
    (repetition_sum (map repeated_entry left_source))
    (repetition_sum (map repeated_entry right_source)).
Proof.
  intros Core initialize maximum lead left_source right_source left_roster right_roster
    LEFT RIGHT.
  destruct (complete_repeated_roster_matches_ordinary maximum left_source left_roster LEFT)
    as [_ [LE [_ [LT _]]]].
  destruct (complete_repeated_roster_matches_ordinary maximum right_source right_roster RIGHT)
    as [_ [RE [_ [RT _]]]].
  rewrite LE, RE, LT, RT, !repeated_entries_have_the_original_sum. reflexivity.
Qed.

End RepeatedSource.
End GeneratedBagComparisonInitialization.

Print Assumptions GeneratedBagComparisonInitialization.repeated_entries_have_the_original_sum.
Print Assumptions GeneratedBagComparisonInitialization.successful_repeated_walk_preserves_original_counts.
Print Assumptions GeneratedBagComparisonInitialization.complete_repeated_roster_matches_ordinary.
Print Assumptions GeneratedBagComparisonInitialization.successful_repeated_rosters_supply_identical_constructor_arguments.
