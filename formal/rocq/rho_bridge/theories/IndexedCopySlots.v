(** Logical indexed result storage for the shared structural copy machine.
    This models executable checked writes/takes and ordered range collection.
    Generated scheduling, raw-pointer validity, allocator behavior and Rust
    panic behavior remain separate obligations. The mathematical ceiling
    corresponds to checked machine-word addition, not allocator capacity. *)
From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

Module IndexedCopySlots.
Section Slots.
Context {A : Type}.
Definition Cell := option (nat * A).
Definition Slots := list Cell.

Definition allocate (ceiling count : nat) (slots : Slots) : option Slots :=
  if length slots + count <=? ceiling
  then Some (slots ++ repeat None count)
  else None.

Theorem allocation_exact : forall ceiling count slots next,
  allocate ceiling count slots = Some next ->
  next = slots ++ repeat None count /\
  length next = length slots + count /\
  length next <= ceiling.
Proof.
  intros ceiling count slots next H.
  unfold allocate in H.
  destruct (length slots + count <=? ceiling) eqn:E; try discriminate.
  inversion H; subst. apply Nat.leb_le in E.
  rewrite length_app, repeat_length. auto.
Qed.

Theorem allocation_preserves_prefix : forall ceiling count slots next,
  allocate ceiling count slots = Some next ->
  firstn (length slots) next = slots.
Proof.
  intros ceiling count slots next H.
  apply allocation_exact in H as [-> _].
  rewrite firstn_app, firstn_all, Nat.sub_diag.
  simpl. now rewrite app_nil_r.
Qed.

Theorem allocation_overflow_refuses : forall ceiling count slots,
  ceiling < length slots + count -> allocate ceiling count slots = None.
Proof.
  intros. unfold allocate.
  apply Nat.leb_gt in H. now rewrite H.
Qed.

Theorem adjacent_allocations_disjoint :
  forall ceiling first_count second_count slots middle final i j,
  allocate ceiling first_count slots = Some middle ->
  allocate ceiling second_count middle = Some final ->
  length slots <= i < length slots + first_count ->
  length middle <= j < length middle + second_count ->
  i <> j /\ j < length final.
Proof.
  intros ceiling first_count second_count slots middle final i j H1 H2 HI HJ.
  apply allocation_exact in H1 as [_ [L1 _]].
  apply allocation_exact in H2 as [_ [L2 _]]. lia.
Qed.

(** Only an empty existing slot can be filled. *)
Fixpoint fill (index : nat) (entry : nat * A) (slots : Slots) : option Slots :=
  match index, slots with
  | 0, None :: rest => Some (Some entry :: rest)
  | S index, head :: rest =>
      match fill index entry rest with
      | Some next => Some (head :: next)
      | None => None
      end
  | _, _ => None
  end.

Definition write_slot expected actual value index slots : option Slots :=
  if expected =? actual then fill index (actual, value) slots else None.

Definition after_write expected actual value index slots : Slots :=
  match write_slot expected actual value index slots with
  | Some next => next
  | None => slots
  end.

Theorem wrong_write_category_keeps_slots :
  forall expected actual value index slots,
  expected <> actual ->
  write_slot expected actual value index slots = None /\
  after_write expected actual value index slots = slots.
Proof.
  intros expected actual value index slots H. apply Nat.eqb_neq in H.
  unfold after_write, write_slot. rewrite H. auto.
Qed.

Theorem fill_once : forall index entry slots next,
  fill index entry slots = Some next ->
  forall other, fill index other next = None.
Proof.
  induction index as [|index IH]; intros entry slots next H other;
    destruct slots as [|head rest]; cbn in H; try discriminate.
  - destruct head; try discriminate.
    inversion H; subst. reflexivity.
  - destruct (fill index entry rest) as [updated|] eqn:E; try discriminate.
    inversion H; subst. cbn.
    now rewrite (IH entry rest updated E other).
Qed.

Theorem fill_bounds : forall index entry slots next,
  fill index entry slots = Some next ->
  index < length slots /\ length next = length slots.
Proof.
  induction index as [|index IH]; intros entry slots next H;
    destruct slots as [|head rest]; cbn in H; try discriminate.
  - destruct head; try discriminate.
    inversion H; subst. cbn. lia.
  - destruct (fill index entry rest) as [updated|] eqn:E; try discriminate.
    inversion H; subst.
    specialize (IH entry rest updated E). cbn. lia.
Qed.

Theorem write_once : forall expected actual value index slots next other,
  write_slot expected actual value index slots = Some next ->
  write_slot expected actual other index next = None /\
  after_write expected actual other index next = next.
Proof.
  intros expected actual value index slots next other H.
  unfold write_slot in H.
  destruct (expected =? actual) eqn:E; try discriminate.
  pose proof (fill_once index (actual, value) slots next H (actual, other)) as F.
  unfold after_write, write_slot. rewrite E, F. auto.
Qed.

(** Taking validates the category and replaces exactly that cell by None. *)
Fixpoint take_slot (index expected : nat) (slots : Slots) : option (A * Slots) :=
  match index, slots with
  | 0, Some (actual, value) :: rest =>
      if expected =? actual then Some (value, None :: rest) else None
  | S index, head :: rest =>
      match take_slot index expected rest with
      | Some (value, next) => Some (value, head :: next)
      | None => None
      end
  | _, _ => None
  end.

Definition after_take index expected slots : Slots :=
  match take_slot index expected slots with
  | Some (_, next) => next
  | None => slots
  end.

Theorem take_once : forall index expected slots value next,
  take_slot index expected slots = Some (value, next) ->
  take_slot index expected next = None /\ after_take index expected next = next.
Proof.
  induction index as [|index IH]; intros expected slots value next H;
    destruct slots as [|head rest]; cbn in H; try discriminate.
  - destruct head as [[actual found]|]; try discriminate.
    destruct (expected =? actual); try discriminate.
    inversion H; subst. split; reflexivity.
  - destruct (take_slot index expected rest) as [[found updated]|] eqn:E;
      try discriminate.
    destruct (IH expected rest found updated E) as [F _].
    inversion H; subst.
    unfold after_take. cbn. rewrite F. auto.
Qed.

Lemma take_at_prefix : forall prefix expected cell rest,
  take_slot (length prefix) expected (prefix ++ cell :: rest) =
  option_map (fun '(value, next) => (value, prefix ++ next))
    (take_slot 0 expected (cell :: rest)).
Proof.
  induction prefix as [|head prefix IH]; intros.
  - destruct cell as [[actual value]|]; cbn; [|reflexivity].
    destruct (expected =? actual); reflexivity.
  - cbn [length app take_slot]. rewrite IH.
    destruct cell as [[actual value]|]; cbn; [|reflexivity].
    destruct (expected =? actual); reflexivity.
Qed.

Theorem empty_take_keeps_slots : forall prefix expected rest,
  take_slot (length prefix) expected (prefix ++ None :: rest) = None /\
  after_take (length prefix) expected (prefix ++ None :: rest) =
    prefix ++ None :: rest.
Proof.
  intros. unfold after_take. rewrite take_at_prefix. cbn. auto.
Qed.

Theorem wrong_take_category_keeps_slots :
  forall prefix expected actual value rest,
  expected <> actual ->
  take_slot (length prefix) expected
    (prefix ++ Some (actual, value) :: rest) = None /\
  after_take (length prefix) expected
    (prefix ++ Some (actual, value) :: rest) =
    prefix ++ Some (actual, value) :: rest.
Proof.
  intros prefix expected actual value rest H. apply Nat.eqb_neq in H.
  unfold after_take. rewrite take_at_prefix. cbn. rewrite H. auto.
Qed.

(** Indexed takes advance in source order. Failure returns no collected
    result; this operation does not claim rollback of earlier taken values. *)
Fixpoint take_many (count start expected : nat) (slots : Slots)
    : option (list A * Slots) :=
  match count with
  | 0 => Some ([], slots)
  | S count =>
      match take_slot start expected slots with
      | None => None
      | Some (value, next) =>
          match take_many count (S start) expected next with
          | None => None
          | Some (values, final) => Some (value :: values, final)
          end
      end
  end.

Lemma take_many_cons : forall count start expected head slots,
  take_many count (S start) expected (head :: slots) =
  option_map (fun '(values, next) => (values, head :: next))
    (take_many count start expected slots).
Proof.
  induction count as [|count IH]; intros; cbn; [reflexivity|].
  destruct (take_slot start expected slots) as [[value next]|]; cbn; [|reflexivity].
  rewrite IH.
  destruct (take_many count (S start) expected next) as [[values final]|]; reflexivity.
Qed.

Lemma prepared_front_ready : forall expected values suffix,
  take_many (length values) 0 expected
    (map (fun value => Some (expected, value)) values ++ suffix) =
  Some (values, repeat None (length values) ++ suffix).
Proof.
  intros expected values.
  induction values as [|value values IH]; intros suffix; cbn; [reflexivity|].
  rewrite Nat.eqb_refl. cbn.
  rewrite take_many_cons, IH. reflexivity.
Qed.

Theorem prepared_range_ready : forall prefix expected values suffix,
  take_many (length values) (length prefix) expected
    (prefix ++ map (fun value => Some (expected, value)) values ++ suffix) =
  Some (values, prefix ++ repeat None (length values) ++ suffix).
Proof.
  induction prefix as [|head prefix IH]; intros; cbn.
  - apply prepared_front_ready.
  - rewrite take_many_cons, IH. reflexivity.
Qed.

(** The ordinary list [values] preserves source order and repetitions.
    The generator still owes field coverage, category-correct writes and
    scheduling correspondence establishing readiness before assembly. *)
End Slots.

Print Assumptions allocation_exact.
Print Assumptions allocation_preserves_prefix.
Print Assumptions allocation_overflow_refuses.
Print Assumptions adjacent_allocations_disjoint.
Print Assumptions wrong_write_category_keeps_slots.
Print Assumptions fill_once.
Print Assumptions fill_bounds.
Print Assumptions write_once.
Print Assumptions take_once.
Print Assumptions empty_take_keeps_slots.
Print Assumptions wrong_take_category_keeps_slots.
Print Assumptions prepared_range_ready.
End IndexedCopySlots.
