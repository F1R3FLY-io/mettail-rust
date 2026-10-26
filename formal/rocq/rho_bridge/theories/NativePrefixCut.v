From Stdlib Require Import List PeanoNat Bool Lia Sorting.Permutation.
From CostAccountedRho Require Import AuthorityPresentation LocatedStackConsumption
  OrderedStackMaterialization NativeOperationJournal CausalStackOrder.
Import ListNotations.

Module OS := OrderedStackMaterialization.
Module LS := LocatedStackConsumption.

Definition completed_before (lookup : nat -> option nat) (boundary event : nat) : Prop :=
  exists position, lookup event = Some position /\ position < boundary.

Theorem birth_readiness_depends_on_completed_cut :
  forall left_lookup right_lookup left_boundary right_boundary required,
    (forall event, In event required ->
      (completed_before left_lookup left_boundary event <->
       completed_before right_lookup right_boundary event)) ->
    OS.birth_ready_at left_boundary left_lookup required =
    OS.birth_ready_at right_boundary right_lookup required.
Proof.
  intros left_lookup right_lookup left_boundary right_boundary required Hequiv.
  assert (Hready : OS.birth_ready_at left_boundary left_lookup required = true <->
                  OS.birth_ready_at right_boundary right_lookup required = true).
  { rewrite !OS.readiness_iff_all_required_events_precede.
    split; intros [Hnonempty Hall]; split; [exact Hnonempty | | exact Hnonempty |].
    - intros event Hin. apply (proj1 (Hequiv event Hin)). now apply Hall.
    - intros event Hin. apply (proj2 (Hequiv event Hin)). now apply Hall. }
  destruct (OS.birth_ready_at left_boundary left_lookup required),
    (OS.birth_ready_at right_boundary right_lookup required); intuition discriminate.
Qed.

Definition cut_lookup (boundary : nat) (lookup : nat -> option nat) event :=
  match lookup event with
  | Some position => if position <? boundary then Some position else None
  | None => None
  end.

Theorem local_readiness_can_use_cut_lookup : forall boundary lookup required,
  OS.birth_ready_at boundary (cut_lookup boundary lookup) required =
  OS.birth_ready_at boundary lookup required.
Proof.
  intros boundary lookup required. apply birth_readiness_depends_on_completed_cut.
  intros event _. unfold completed_before, cut_lookup.
  destruct (lookup event) as [position|] eqn:Hlookup.
  - destruct (position <? boundary) eqn:Hbefore.
    + reflexivity.
    + apply Nat.ltb_ge in Hbefore. split; intros [actual [Heq Hprior]];
        inversion Heq; lia.
  - reflexivity.
Qed.

Section Prefixes.

Context {atom : Type}.

Theorem causal_history_splits_without_changing_birth_lookup :
  forall prefix suffix lookup births index before after,
    @OS.causal_stack_history atom lookup births index (prefix ++ suffix) before after ->
    exists middle,
      OS.causal_stack_history lookup births index prefix before middle /\
      OS.causal_stack_history lookup births (index + length prefix) suffix middle after.
Proof.
  induction prefix as [|ids rest IH]; intros suffix lookup births index before after Hhistory.
  - exists before. split; [constructor |]. simpl in *. now rewrite Nat.add_0_r.
  - simpl in Hhistory. inversion Hhistory; subst.
    match goal with
    | Htail : OS.causal_stack_history _ _ _ (rest ++ suffix) _ _ |- _ =>
        destruct (IH _ _ _ _ _ _ Htail) as [cut [Hprefix Hsuffix]]
    end.
    exists cut. split.
    + econstructor; eauto.
    + replace (index + length (ids :: rest)) with (S index + length rest) by (simpl; lia).
      exact Hsuffix.
Qed.

Theorem checked_history_has_exact_prefix_residual :
  forall events boundary lookup births before after,
    boundary <= length events ->
    @OS.validated_causal_history atom lookup births 0 events before after ->
    exists middle,
      OS.birth_metadata_well_formed lookup births before /\
      OS.causal_stack_history lookup births 0 (firstn boundary events) before middle /\
      OS.causal_stack_history lookup births boundary (skipn boundary events) middle after /\
      forall id cells, before id = Some cells ->
        middle id = Some (skipn (selected_uses id (firstn boundary events)) cells) /\
        selected_uses id (firstn boundary events) <= length cells.
Proof.
  intros events boundary lookup births before after Hbound [Hmetadata Hhistory].
  rewrite <- (firstn_skipn boundary events) in Hhistory.
  destruct (causal_history_splits_without_changing_birth_lookup
    (firstn boundary events) (skipn boundary events) lookup births 0 before after Hhistory)
    as [middle [Hprefix Hsuffix]].
  exists middle. split; [exact Hmetadata |]. split; [exact Hprefix |]. split.
  - simpl in Hsuffix. rewrite length_firstn, Nat.min_l in Hsuffix by exact Hbound.
    exact Hsuffix.
  - intros id cells Hcells.
    eapply OS.causal_histories_preserve_exact_suffix; eauto.
Qed.

Context {location surface : Type}.
Context (near : surface -> location -> Prop).

Theorem located_history_splits_without_changing_access :
  forall prefix suffix before after,
    @LS.located_history atom location surface near (prefix ++ suffix) before after ->
    exists middle,
      LS.located_history near prefix before middle /\
      LS.located_history near suffix middle after.
Proof.
  induction prefix as [|request rest IH]; intros suffix before after Hhistory.
  - exists before. split; [constructor | exact Hhistory].
  - simpl in Hhistory. inversion Hhistory; subst.
    match goal with
    | Htail : LS.located_history _ (rest ++ suffix) _ _ |- _ =>
        destruct (IH _ _ _ Htail) as [cut [Hprefix Hsuffix]]
    end.
    exists cut. split; [econstructor; eauto | exact Hsuffix].
Qed.

Theorem located_prefix_retains_location_and_exact_suffix :
  forall requests boundary before after,
    @LS.located_history atom location surface near requests before after ->
    exists middle,
      LS.located_history near (firstn boundary requests) before middle /\
      LS.located_history near (skipn boundary requests) middle after /\
      forall id place cells, before id = Some (place, cells) ->
        middle id = Some (place, skipn
          (selected_uses id (map LS.request_stacks (firstn boundary requests))) cells) /\
        selected_uses id (map LS.request_stacks (firstn boundary requests)) <= length cells.
Proof.
  intros requests boundary before after Hhistory.
  rewrite <- (firstn_skipn boundary requests) in Hhistory.
  destruct (located_history_splits_without_changing_access
    (firstn boundary requests) (skipn boundary requests) before after Hhistory)
    as [middle [Hprefix Hsuffix]].
  exists middle. split; [exact Hprefix |]. split; [exact Hsuffix |].
  intros id place cells Hcells.
  eapply LS.located_histories_preserve_exact_suffix; eauto.
Qed.

Theorem located_and_causal_prefixes_have_the_same_cells :
  forall requests boundary lookup births before located_after causal_after,
    @LS.located_history atom location surface near
      (firstn boundary requests) before located_after ->
    OS.causal_stack_history lookup births 0
      (firstn boundary (map LS.request_stacks requests))
      (LS.forget_locations before) causal_after ->
    forall id, LS.forget_locations located_after id = causal_after id.
Proof.
  intros requests boundary lookup births before located_after causal_after Hlocated Hcausal.
  eapply admitted_interleavings_preserve_stack_suffixes.
  - exact (LS.located_histories_refine_selected_consumption near _ _ _ Hlocated).
  - exact (OS.causal_histories_refine_ordered_consumption _ _ _ _ _ _ Hcausal).
  - rewrite firstn_map. apply Permutation_refl.
Qed.

End Prefixes.

Theorem native_dependency_excludes_equal_or_reversed_fresh_positions :
  forall lo hi next_lo next_hi first second,
    journal_contains lo hi (JournalFresh first) = true ->
    journal_contains next_lo next_hi (JournalFresh second) = true ->
    hi <= next_lo -> ~ second <= first.
Proof.
  intros lo hi next_lo next_hi first second Hfirst Hsecond Hdep.
  pose proof (journal_dependency_orders_fresh _ _ _ _ _ _ Hfirst Hsecond Hdep). lia.
Qed.

Example equal_event_sets_do_not_preserve_stack_execution :
  Permutation [true; false] [false; true] /\
  consumes_in_order [true; false] [true; false] [] /\
  ~ exists after, consumes_in_order [false; true] [true; false] after.
Proof.
  split; [apply perm_swap |]. split; [repeat constructor |].
  intros [after Hrun].
  exact (reversed_pair_cannot_consume_causal_stack true false [] after
    ltac:(discriminate) Hrun).
Qed.

Definition example_birth_lookup event := if Nat.eqb event 9 then Some 2 else None.
Definition example_births id := if Nat.eqb id 7 then Some [9] else None.
Definition example_inventory id : option (@authority_stack bool) :=
  if Nat.eqb id 7 then Some [[false]] else None.

Example full_metadata_validates_an_unused_future_birth :
  OS.birth_metadata_well_formed example_birth_lookup example_births example_inventory.
Proof.
  intros id required Hbirth. unfold example_births in Hbirth.
  destruct (Nat.eqb id 7) eqn:Hid; [| discriminate].
  inversion Hbirth; subst required.
  exists [[false]], 2. unfold example_inventory. rewrite Hid. repeat split; reflexivity.
Qed.

Example future_birth_cannot_supply_this_cut :
  OS.birth_ready_at 2 example_birth_lookup [9] = false.
Proof. reflexivity. Qed.

Example slicing_lookup_invalidates_global_metadata :
  ~ OS.birth_metadata_well_formed
      (cut_lookup 2 example_birth_lookup) example_births example_inventory.
Proof.
  eapply OS.global_precheck_rejects_missing_unused_birth_event with (id := 7)
    (required := [9]) (event := 9); simpl; auto.
Qed.

Print Assumptions birth_readiness_depends_on_completed_cut.
Print Assumptions local_readiness_can_use_cut_lookup.
Print Assumptions causal_history_splits_without_changing_birth_lookup.
Print Assumptions checked_history_has_exact_prefix_residual.
Print Assumptions located_history_splits_without_changing_access.
Print Assumptions located_prefix_retains_location_and_exact_suffix.
Print Assumptions located_and_causal_prefixes_have_the_same_cells.
Print Assumptions native_dependency_excludes_equal_or_reversed_fresh_positions.
Print Assumptions equal_event_sets_do_not_preserve_stack_execution.
Print Assumptions full_metadata_validates_an_unused_future_birth.
Print Assumptions future_birth_cannot_supply_this_cut.
Print Assumptions slicing_lookup_invalidates_global_metadata.
