(** Storage refinement for the existing Rholang Job/Kont worklist.

    This model isolates stack representation, incremental debt accounting,
    checked value suffix extraction and carrier changes. It does not introduce
    another tree traversal. Work is top-first; values are oldest-first, exactly
    the logical order of the Rust value Vec. Payloads are not interpreted here.

    WorklistFoldEquivalence separately supplies fixed-tree fold equivalence.
    Staged receive producers, concrete constructors, allocation/cancellation and
    Rust source correspondence remain separate obligations. In particular the
    debt equation alone is NOT a proof of local continuation arity safety. *)
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Inductive Work (J : Type) := Enter (payload : J) | Combine (arity : nat) (payload : J).
Arguments Enter {J} _.
Arguments Combine {J} _ _.

Definition entered {J} (job : Work J) :=
  match job with Enter _ => 1 | Combine _ _ => 0 end.
Definition continued {J} (job : Work J) :=
  match job with Enter _ => 0 | Combine _ _ => 1 end.
Definition owed {J} (job : Work J) :=
  match job with Enter _ => 0 | Combine arity _ => arity end.
Definition total {J} (measure : Work J -> nat) (work : list (Work J)) :=
  fold_right (fun job rest => measure job + rest) 0 work.

Record Counts := { enters : nat; konts : nat; kont_arity : nat }.
Definition count_work {J} (work : list (Work J)) : Counts :=
  {| enters := total entered work; konts := total continued work;
     kont_arity := total owed work |}.
Definition push_count {J} (job : Work J) (counts : Counts) : Counts :=
  {| enters := entered job + enters counts;
     konts := continued job + konts counts;
     kont_arity := owed job + kont_arity counts |}.
Definition pop_count {J} (job : Work J) (counts : Counts) : Counts :=
  {| enters := enters counts - entered job;
     konts := konts counts - continued job;
     kont_arity := kont_arity counts - owed job |}.

Theorem push_counts_exact : forall J (job : Work J) work,
  push_count job (count_work work) = count_work (job :: work).
Proof. reflexivity. Qed.

Theorem pop_counts_exact : forall J (job : Work J) work,
  pop_count job (count_work (job :: work)) = count_work work.
Proof.
  intros. unfold pop_count, count_work, total; simpl.
  repeat rewrite Nat.add_sub_swap by lia.
  repeat rewrite Nat.sub_diag. repeat rewrite Nat.add_0_r. reflexivity.
Qed.

(** A machine word ceiling is a parameter, not an enormous reduced Peano
    numeral. All new counters must be checked before any state mutation. *)
Definition counts_fit (ceiling : nat) (counts : Counts) : bool :=
  (enters counts <=? ceiling) && (konts counts <=? ceiling) &&
  (kont_arity counts <=? ceiling).
Definition checked_push_count {J} ceiling (job : Work J) counts :=
  let next := push_count job counts in
  if counts_fit ceiling next then Some next else None.

Theorem checked_push_success_exact : forall J ceiling (job : Work J) counts next,
  checked_push_count ceiling job counts = Some next ->
  next = push_count job counts /\ counts_fit ceiling next = true.
Proof.
  intros J ceiling job counts next H. unfold checked_push_count in H.
  destruct (counts_fit ceiling (push_count job counts)) eqn:E;
    inversion H; subst; auto.
Qed.

Definition checked_suffix {V} (count : nat) (values : list V)
    : option (list V * list V) :=
  if count <=? length values then
    Some (firstn (length values - count) values,
          skipn (length values - count) values)
  else None.

Theorem suffix_underflow_rejects : forall V count (values : list V),
  length values < count -> checked_suffix count values = None.
Proof.
  intros. unfold checked_suffix. apply Nat.leb_gt in H. rewrite H. reflexivity.
Qed.

Theorem suffix_success_exact : forall V count (values prefix suffix : list V),
  checked_suffix count values = Some (prefix, suffix) ->
  values = prefix ++ suffix /\ length suffix = count.
Proof.
  intros V count values prefix suffix H. unfold checked_suffix in H.
  destruct (count <=? length values) eqn:E; inversion H; subst.
  apply Nat.leb_le in E. split.
  - symmetry. apply firstn_skipn.
  - rewrite length_skipn. lia.
Qed.

Theorem suffix_source_order : forall V (prefix children : list V),
  checked_suffix (length children) (prefix ++ children) = Some (prefix, children).
Proof.
  intros. unfold checked_suffix. rewrite length_app.
  replace (length children <=? length prefix + length children) with true
    by (symmetry; apply Nat.leb_le; lia).
  replace (length prefix + length children - length children) with (length prefix) by lia.
  rewrite firstn_app, skipn_app, firstn_all, skipn_all, Nat.sub_diag.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem suffix_zero : forall V (values : list V),
  checked_suffix 0 values = Some (values, []).
Proof.
  intros. replace values with (values ++ []) at 1 by apply app_nil_r.
  exact (suffix_source_order V values []).
Qed.

Definition debt (values : nat) (counts : Counts) : Prop :=
  values + enters counts + konts counts = 1 + kont_arity counts.

Theorem initial_debt : forall J (root : J), debt 0 (count_work [Enter root]).
Proof. reflexivity. Qed.

Theorem leaf_preserves_debt : forall v e c a,
  debt v {| enters := S e; konts := c; kont_arity := a |} ->
  debt (S v) {| enters := e; konts := c; kont_arity := a |}.
Proof. unfold debt; simpl; intros; lia. Qed.

Theorem expansion_preserves_debt : forall v e c a n,
  debt v {| enters := S e; konts := c; kont_arity := a |} ->
  debt v {| enters := e + n; konts := S c; kont_arity := a + n |}.
Proof. unfold debt; simpl; intros; lia. Qed.

Theorem combine_preserves_debt : forall v e c a n,
  n <= v ->
  debt v {| enters := e; konts := S c; kont_arity := a + n |} ->
  debt (v - n + 1) {| enters := e; konts := c; kont_arity := a |}.
Proof. unfold debt; simpl; intros; lia. Qed.

Theorem staged_combine_preserves_debt : forall v e c a n m,
  n <= v ->
  debt v {| enters := e; konts := S c; kont_arity := a + n |} ->
  debt (v - n) {| enters := e + m; konts := S c; kont_arity := a + m |}.
Proof. unfold debt; simpl; intros; lia. Qed.

Theorem halted_debt_has_one_value : forall J v,
  debt v (count_work (@nil (Work J))) -> v = 1.
Proof. unfold debt, count_work, total; simpl; intros; lia. Qed.

(** Counterexample: global debt alone cannot justify popping an operand.
    The child Enter is incorrectly BELOW a Combine on the work stack. *)
Example debt_does_not_prove_ready_arity :
  debt 0 (count_work [Combine 1 0; Enter 0]) /\
  checked_suffix 1 (@nil nat) = None.
Proof. split; reflexivity. Qed.

Definition retype_job {J K} (f : J -> K) (job : Work J) : Work K :=
  match job with Enter x => Enter (f x) | Combine n x => Combine n (f x) end.

Theorem retype_preserves_counts : forall J K (f : J -> K) work,
  count_work (map (retype_job f) work) = count_work work.
Proof.
  intros J K f work. induction work as [|job rest IH]; simpl; auto.
  change (push_count (retype_job f job) (count_work (map (retype_job f) rest)) =
          push_count job (count_work rest)).
  rewrite IH. destruct job; reflexivity.
Qed.

Theorem mapped_suffix_commutes : forall V W (f : V -> W) n values,
  checked_suffix n (map f values) =
  option_map (fun '(prefix, suffix) => (map f prefix, map f suffix))
    (checked_suffix n values).
Proof.
  intros. unfold checked_suffix. rewrite length_map.
  destruct (n <=? length values); simpl; auto.
  rewrite firstn_map, skipn_map. reflexivity.
Qed.

(** Erasing diagnostic origins is a concrete instance, not an assumption
    that arbitrary semantic transformations preserve evaluation. *)
Corollary erase_origins_preserves_suffix : forall V O n (values : list (V * O)),
  checked_suffix n (map fst values) =
  option_map (fun '(prefix, suffix) => (map fst prefix, map fst suffix))
    (checked_suffix n values).
Proof. intros. apply mapped_suffix_commutes. Qed.

Definition finish {V} (work_empty : bool) (values : list V) : option V :=
  match work_empty, values with true, [root] => Some root | _, _ => None end.

Theorem finish_exact : forall V empty (values : list V) root,
  finish empty values = Some root -> empty = true /\ values = [root].
Proof.
  intros V empty values root H. destruct empty; try discriminate.
  destruct values as [|v [|v' rest]]; inversion H; subst; auto.
Qed.

Print Assumptions push_counts_exact.
Print Assumptions pop_counts_exact.
Print Assumptions checked_push_success_exact.
Print Assumptions suffix_underflow_rejects.
Print Assumptions suffix_success_exact.
Print Assumptions suffix_source_order.
Print Assumptions suffix_zero.
Print Assumptions initial_debt.
Print Assumptions leaf_preserves_debt.
Print Assumptions expansion_preserves_debt.
Print Assumptions combine_preserves_debt.
Print Assumptions staged_combine_preserves_debt.
Print Assumptions halted_debt_has_one_value.
Print Assumptions debt_does_not_prove_ready_arity.
Print Assumptions retype_preserves_counts.
Print Assumptions mapped_suffix_commutes.
Print Assumptions erase_origins_preserves_suffix.
Print Assumptions finish_exact.
