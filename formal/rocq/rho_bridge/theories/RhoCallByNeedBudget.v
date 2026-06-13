(*
 * RhoCallByNeedBudget: bounded force admission for the generic call-by-need
 * lowering.
 *
 * A successful force consumes one lookahead step.  A memo hit uses no heap; a
 * memo miss must allocate exactly one memo cell and therefore consumes one heap
 * cell.  Failed admission preserves the incoming budget and produces no public
 * observation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From RhoBridge Require Import RhoCallByNeedObservation.

Import ListNotations.

Section RhoCallByNeedBudget.

  Record NeedBudget : Type := {
    lookahead_remaining : nat;
    heap_remaining : nat
  }.

  Inductive ForceKind : Type :=
    | MemoHit
    | MemoMiss.

  Inductive NeedBudgetBlocker : Type :=
    | LookaheadExceeded
    | HeapBudgetExceeded.

  Record NeedAdmission : Type := {
    admission_budget_after : NeedBudget;
    admission_blocker : option NeedBudgetBlocker
  }.

  Definition admission_allowed (a : NeedAdmission) : bool :=
    match admission_blocker a with
    | None => true
    | Some _ => false
    end.

  Definition allow (budget_after : NeedBudget) : NeedAdmission :=
    {| admission_budget_after := budget_after;
       admission_blocker := None |}.

  Definition block
      (reason : NeedBudgetBlocker)
      (budget_after : NeedBudget) : NeedAdmission :=
    {| admission_budget_after := budget_after;
       admission_blocker := Some reason |}.

  Definition admit_force_kind
      (kind : ForceKind)
      (budget : NeedBudget) : NeedAdmission :=
    match lookahead_remaining budget with
    | 0 => block LookaheadExceeded budget
    | S lookahead_after =>
        match kind with
        | MemoHit =>
            allow
              {| lookahead_remaining := lookahead_after;
                 heap_remaining := heap_remaining budget |}
        | MemoMiss =>
            match heap_remaining budget with
            | 0 => block HeapBudgetExceeded budget
            | S heap_after =>
                allow
                  {| lookahead_remaining := lookahead_after;
                     heap_remaining := heap_after |}
            end
        end
    end.

  Definition force_kind (e : Expr) (memo : Memo) : ForceKind :=
    match lookup (expr_thunk e) memo with
    | Some _ => MemoHit
    | None => MemoMiss
    end.

  Definition admit_force
      (e : Expr)
      (memo : Memo)
      (budget : NeedBudget) : NeedAdmission :=
    admit_force_kind (force_kind e memo) budget.

  Inductive BoundedForceOutcome : Type :=
    | NeedObserved : Value -> Memo -> NeedBudget -> BoundedForceOutcome
    | NeedBlocked : NeedBudgetBlocker -> NeedBudget -> BoundedForceOutcome.

  Definition bounded_force
      (e : Expr)
      (memo : Memo)
      (budget : NeedBudget) : BoundedForceOutcome :=
    let admission := admit_force e memo budget in
    match admission_blocker admission with
    | Some blocker => NeedBlocked blocker (admission_budget_after admission)
    | None =>
        let result := force e memo in
        NeedObserved (fst result) (snd result) (admission_budget_after admission)
    end.

  Theorem zero_lookahead_blocks_admission : forall kind heap,
    admit_force_kind kind
      {| lookahead_remaining := 0; heap_remaining := heap |}
    =
    block LookaheadExceeded
      {| lookahead_remaining := 0; heap_remaining := heap |}.
  Proof.
    intros kind heap. destruct kind; reflexivity.
  Qed.

  Theorem memo_hit_consumes_only_lookahead : forall lookahead heap,
    admit_force_kind MemoHit
      {| lookahead_remaining := S lookahead; heap_remaining := heap |}
    =
    allow
      {| lookahead_remaining := lookahead; heap_remaining := heap |}.
  Proof. intros lookahead heap. reflexivity. Qed.

  Theorem memo_miss_consumes_lookahead_and_heap : forall lookahead heap,
    admit_force_kind MemoMiss
      {| lookahead_remaining := S lookahead; heap_remaining := S heap |}
    =
    allow
      {| lookahead_remaining := lookahead; heap_remaining := heap |}.
  Proof. intros lookahead heap. reflexivity. Qed.

  Theorem memo_miss_without_heap_blocks_admission : forall lookahead,
    admit_force_kind MemoMiss
      {| lookahead_remaining := S lookahead; heap_remaining := 0 |}
    =
    block HeapBudgetExceeded
      {| lookahead_remaining := S lookahead; heap_remaining := 0 |}.
  Proof. intros lookahead. reflexivity. Qed.

  Theorem zero_lookahead_blocks_bounded_force : forall e memo heap,
    bounded_force e memo
      {| lookahead_remaining := 0; heap_remaining := heap |}
    =
    NeedBlocked LookaheadExceeded
      {| lookahead_remaining := 0; heap_remaining := heap |}.
  Proof.
    intros e memo heap. unfold bounded_force, admit_force, force_kind.
    destruct (lookup (expr_thunk e) memo); reflexivity.
  Qed.

  Theorem force_miss_without_heap_blocks_bounded_force : forall e memo lookahead,
    lookup (expr_thunk e) memo = None ->
    bounded_force e memo
      {| lookahead_remaining := S lookahead; heap_remaining := 0 |}
    =
    NeedBlocked HeapBudgetExceeded
      {| lookahead_remaining := S lookahead; heap_remaining := 0 |}.
  Proof.
    intros e memo lookahead Hmiss.
    unfold bounded_force, admit_force, force_kind. rewrite Hmiss. reflexivity.
  Qed.

  Theorem force_hit_preserves_memo_and_heap_budget :
    forall e memo lookahead heap value,
      lookup (expr_thunk e) memo = Some value ->
      bounded_force e memo
        {| lookahead_remaining := S lookahead; heap_remaining := heap |}
      =
      NeedObserved value memo
        {| lookahead_remaining := lookahead; heap_remaining := heap |}.
  Proof.
    intros e memo lookahead heap value Hhit.
    unfold bounded_force, admit_force, force_kind, force.
    rewrite Hhit. reflexivity.
  Qed.

  Theorem force_miss_consumes_one_heap_cell_and_memoizes :
    forall e memo lookahead heap,
      lookup (expr_thunk e) memo = None ->
      bounded_force e memo
        {| lookahead_remaining := S lookahead; heap_remaining := S heap |}
      =
      NeedObserved (source_eval e) ((expr_thunk e, expr_value e) :: memo)
        {| lookahead_remaining := lookahead; heap_remaining := heap |}.
  Proof.
    intros e memo lookahead heap Hmiss.
    unfold bounded_force, admit_force, force_kind, force, source_eval.
    rewrite Hmiss. reflexivity.
  Qed.

  Theorem bounded_force_success_requires_admission :
    forall e memo budget value memo_after budget_after,
      bounded_force e memo budget = NeedObserved value memo_after budget_after ->
      admission_allowed (admit_force e memo budget) = true.
  Proof.
    intros e memo budget value memo_after budget_after Hsuccess.
    unfold bounded_force in Hsuccess.
    destruct (admit_force e memo budget) as [after blocker] eqn:Hadmit.
    destruct blocker as [blocker |]; simpl in *.
    - discriminate Hsuccess.
    - reflexivity.
  Qed.

  Theorem bounded_force_success_observes_source :
    forall e memo budget value memo_after budget_after,
      memo_sound_for e memo ->
      bounded_force e memo budget = NeedObserved value memo_after budget_after ->
      value = source_eval e.
  Proof.
    intros e memo budget value memo_after budget_after Hsound Hsuccess.
    unfold bounded_force in Hsuccess.
    destruct (admit_force e memo budget) as [after blocker] eqn:Hadmit.
    destruct blocker as [blocker |]; simpl in Hsuccess.
    - discriminate Hsuccess.
    - destruct (force e memo) as [forced_value forced_memo] eqn:Hforce.
      inversion Hsuccess. subst value.
      pose proof (force_observes_source e memo Hsound) as Hobserve.
      rewrite Hforce in Hobserve. simpl in Hobserve. exact Hobserve.
  Qed.

  Theorem bounded_force_success_preserves_memo_sound :
    forall e memo budget value memo_after budget_after,
      memo_sound_for e memo ->
      bounded_force e memo budget = NeedObserved value memo_after budget_after ->
      memo_sound_for e memo_after.
  Proof.
    intros e memo budget value memo_after budget_after Hsound Hsuccess.
    unfold bounded_force in Hsuccess.
    destruct (admit_force e memo budget) as [after blocker] eqn:Hadmit.
    destruct blocker as [blocker |]; simpl in Hsuccess.
    - discriminate Hsuccess.
    - destruct (force e memo) as [forced_value forced_memo] eqn:Hforce.
      inversion Hsuccess. subst memo_after.
      pose proof (force_preserves_memo_sound_for e memo Hsound) as Hpreserved.
      rewrite Hforce in Hpreserved. simpl in Hpreserved. exact Hpreserved.
  Qed.

  Theorem blocked_force_preserves_budget :
    forall e memo budget blocker budget_after,
      bounded_force e memo budget = NeedBlocked blocker budget_after ->
      budget_after = budget.
  Proof.
    intros e memo [lookahead heap] blocker budget_after Hblocked.
    unfold bounded_force, admit_force, admit_force_kind, force_kind in Hblocked.
    destruct lookahead as [| lookahead']; destruct (lookup (expr_thunk e) memo) as [value |];
      destruct heap as [| heap']; simpl in Hblocked; try discriminate Hblocked;
      inversion Hblocked; reflexivity.
  Qed.

End RhoCallByNeedBudget.
