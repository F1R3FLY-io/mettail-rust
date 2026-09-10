(** Two paid phases around the existing environment helper.

    [lengths] describes the owned key-byte lengths of old binder/hole entries
    and every added slot occurrence, including overwritten duplicates. It is a
    specification of a borrowed iteration, NOT a Rust vector to materialize.
    Its length comes from the existing map/slice lengths before inspection.
    Inspection reads lengths and checked-sums them without constructing keys.

    Schedule: inspection (n work, zero units), then an atomic reservation of
    (1+n+s+b work, 4*(1+n)+b units). Here s counts old entries shifted, b is
    aggregate owned key bytes. The one record includes retained EnvArena
    storage/append; it must not be charged a second time by its caller.
    Pattern cloning has s=0; empty-context creation has n=s=b=0.

    These are logical entry/shift/byte charges, NOT allocator capacity, RSS,
    collision counts, arbitrary Hash callback work, or CPU-time bounds.
    Rust correspondence must check immutable borrowing, no inspection
    allocation, polling sites, checked arithmetic and private result cleanup.
    The functional model cannot prove effects of arbitrary Rust callbacks.
    Lexical meaning is imported from SourceScope, never reimplemented here. *)
From Stdlib Require Import List Arith Lia Permutation.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget.
From RhoBridge Require Import RholangInitialGraphResources
  RholangPreparationReservation RholangSourceScope.
Import ListNotations.

(** Remaining ceiling is checked subtraction, equivalent to accumulating a
    checked nonnegative byte sum. Poll before each read and once at the end.
    This local arithmetic does not debit the caller's meter per key: the
    complete inspection count was reserved before this function is reached. *)
Fixpoint inspect_remaining (ceiling : nat) (lengths : list nat)
    (cancelled : nat -> bool) : option nat :=
  if cancelled 0 then None else
  match lengths with
  | [] => Some ceiling
  | bytes :: rest =>
    match debit ceiling bytes with
    | None => None
    | Some next => inspect_remaining next rest (fun i => cancelled (S i))
    end
  end.

Theorem inspected_sum_is_exact : forall lengths ceiling cancelled remaining,
  inspect_remaining ceiling lengths cancelled = Some remaining ->
  remaining + total_charge lengths = ceiling.
Proof.
  induction lengths as [|bytes rest IH]; intros ceiling cancelled remaining H;
    cbn in H; destruct (cancelled 0); try discriminate.
  - inversion H; subst. cbn. lia.
  - destruct (debit ceiling bytes) as [next|] eqn:HD; [|discriminate].
    pose proof (successful_debit_is_exact _ _ _ HD).
    pose proof (IH _ _ _ H). cbn. lia.
Qed.

Theorem inspection_without_cancellation_reuses_debit_all : forall lengths ceiling,
  inspect_remaining ceiling lengths (fun _ => false) = debit_all ceiling lengths.
Proof.
  induction lengths as [|bytes rest IH]; intros; cbn; [reflexivity|].
  destruct (debit ceiling bytes); [apply IH|reflexivity].
Qed.

Theorem inspection_poll_refuses_before_read : forall ceiling lengths cancelled,
  cancelled 0 = true -> inspect_remaining ceiling lengths cancelled = None.
Proof. intros ceiling [|bytes rest] cancelled H; cbn; now rewrite H. Qed.

Lemma total_charge_permutation : forall lhs rhs,
  Permutation lhs rhs -> total_charge lhs = total_charge rhs.
Proof. intros lhs rhs H; induction H; cbn; lia. Qed.

Lemma debit_all_depends_only_on_total : forall lengths ceiling,
  debit_all ceiling lengths =
  if total_charge lengths <=? ceiling
  then Some (ceiling - total_charge lengths) else None.
Proof.
  intros lengths ceiling. destruct (total_charge lengths <=? ceiling) eqn:HF.
  - apply Nat.leb_le in HF. now apply every_affordable_sequence_succeeds.
  - apply Nat.leb_gt in HF.
    destruct (debit_all ceiling lengths) as [next|] eqn:HD; [|reflexivity].
    pose proof (successful_sequence_has_exact_total_cost _ _ _ HD). lia.
Qed.

Definition inspected_bytes ceiling lengths cancelled : option nat :=
  match inspect_remaining ceiling lengths cancelled with
  | Some remaining => Some (ceiling - remaining)
  | None => None
  end.

Theorem inspected_bytes_success_exact : forall ceiling lengths cancelled bytes,
  inspected_bytes ceiling lengths cancelled = Some bytes ->
  bytes = total_charge lengths /\ bytes <= ceiling.
Proof.
  intros ceiling lengths cancelled bytes H. unfold inspected_bytes in H.
  destruct (inspect_remaining ceiling lengths cancelled) as [remaining|] eqn:HI;
    [|discriminate].
  inversion H; subst. apply inspected_sum_is_exact in HI. lia.
Qed.

Definition paid_inspection cancelled ceiling available lengths polls :=
  preparation_action cancelled ceiling available [List.length lengths] []
    (fun _ => inspected_bytes ceiling lengths polls).

Definition environment_action {A} cancel_inspection cancel_copy ceiling available
    lengths shifted polls (helper : unit -> option A) : ActionResult A :=
  match paid_inspection cancel_inspection ceiling available lengths polls with
  | Refused remaining => Refused remaining
  | Accepted remaining bytes =>
    preparation_action cancel_copy ceiling remaining
      [1; List.length lengths; shifted; bytes]
      [4; List.length lengths; List.length lengths; List.length lengths;
          List.length lengths; bytes] helper
  end.

Theorem successful_inspection_is_paid_and_exact :
  forall cancelled ceiling available lengths polls paid bytes,
  paid_inspection cancelled ceiling available lengths polls = Accepted paid bytes ->
  bytes = total_charge lengths /\ bytes <= ceiling /\
  work_left paid + List.length lengths = work_left available /\
  units_left paid = units_left available.
Proof.
  intros cancelled ceiling available lengths polls paid bytes H.
  unfold paid_inspection in H.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct H as [_ [HB [_ [_ [HW HU]]]]].
  apply inspected_bytes_success_exact in HB. cbn in HW, HU. intuition lia.
Qed.

Theorem successful_environment_action_is_exact :
  forall A ci cc ceiling available lengths shifted polls
    (helper : unit -> option A) paid value,
  environment_action ci cc ceiling available lengths shifted polls helper = Accepted paid value ->
  helper tt = Some value /\
  work_left paid + List.length lengths +
    (1 + List.length lengths + shifted + total_charge lengths) = work_left available /\
  units_left paid + (4 * (1 + List.length lengths) + total_charge lengths) =
    units_left available.
Proof.
  intros A ci cc ceiling available lengths shifted polls helper paid value H.
  unfold environment_action in H.
  destruct (paid_inspection ci ceiling available lengths polls) as [remaining|remaining bytes]
    eqn:HI; [discriminate|].
  apply successful_inspection_is_paid_and_exact in HI.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct HI as [HB [Hbound [HW HU]]].
  destruct H as [_ [HH [_ [_ [HW2 HU2]]]]].
  cbn in HW2, HU2. subst bytes. split; [exact HH|]. split; lia.
Qed.

Theorem initial_cancellation_has_no_environment :
  forall A cc ceiling available lengths shifted polls (helper : unit -> option A),
  environment_action true cc ceiling available lengths shifted polls helper = Refused available.
Proof. reflexivity. Qed.

Theorem inspection_refusal_never_invokes_copy :
  forall A ci cc ceiling available lengths shifted polls paid (helper : unit -> option A),
  paid_inspection ci ceiling available lengths polls = Refused paid ->
  environment_action ci cc ceiling available lengths shifted polls helper = Refused paid.
Proof. intros; unfold environment_action; now rewrite H. Qed.

Theorem later_cancellation_retains_inspection_charge :
  forall A ci ceiling available lengths shifted polls paid bytes (helper : unit -> option A),
  paid_inspection ci ceiling available lengths polls = Accepted paid bytes ->
  environment_action ci true ceiling available lengths shifted polls helper = Refused paid /\
  work_left paid + List.length lengths = work_left available.
Proof.
  intros A ci ceiling available lengths shifted polls paid bytes helper H.
  split.
  - unfold environment_action. rewrite H. reflexivity.
  - apply successful_inspection_is_paid_and_exact in H. tauto.
Qed.

Theorem copy_overdraw_retains_inspection_charge :
  forall A ci ceiling available lengths shifted polls paid bytes (helper : unit -> option A),
  paid_inspection ci ceiling available lengths polls = Accepted paid bytes ->
  reserve paid (1 + List.length lengths + shifted + bytes)
    (4 * (1 + List.length lengths) + bytes) = None ->
  environment_action ci false ceiling available lengths shifted polls helper = Refused paid.
Proof.
  intros A ci ceiling available lengths shifted polls paid bytes helper HI HR.
  unfold environment_action. rewrite HI.
  apply preparation_overdraw_has_no_result.
  replace (total_charge [1; List.length lengths; shifted; bytes]) with
    (1 + List.length lengths + shifted + bytes) by (cbn; lia).
  replace (total_charge [4; List.length lengths; List.length lengths;
    List.length lengths; List.length lengths; bytes]) with
    (4 * (1 + List.length lengths) + bytes) by (cbn; lia).
  exact HR.
Qed.

Theorem environment_charge_is_iteration_order_independent :
  forall A lhs rhs ci cc ceiling available shifted (helper : unit -> option A),
  Permutation lhs rhs ->
  environment_action ci cc ceiling available lhs shifted (fun _ => false) helper =
  environment_action ci cc ceiling available rhs shifted (fun _ => false) helper.
Proof.
  intros A lhs rhs ci cc ceiling available shifted helper HP.
  pose proof (Permutation_length HP) as HL.
  pose proof (total_charge_permutation _ _ HP) as HT.
  unfold environment_action, paid_inspection, inspected_bytes.
  rewrite !inspection_without_cancellation_reuses_debit_all.
  rewrite !debit_all_depends_only_on_total. now rewrite HL, HT.
Qed.

(** Instantiate the callback with the ALREADY PROVED lexical operation.
    The length schedule models concrete Rust key ownership separately from
    ScopeKey: MonikerKey does not contain its optional pretty-name payload. *)
Definition paid_environment_extension ci cc ceiling available lengths polls env slots :=
  environment_action ci cc ceiling available lengths
    (List.length (lexical_bindings env)) polls
    (fun _ => checked_extend_environment ceiling env slots).

Theorem paid_extension_preserves_existing_lexical_semantics :
  forall ci cc ceiling available lengths polls env slots paid extended,
  paid_environment_extension ci cc ceiling available lengths polls env slots =
    Accepted paid extended ->
  extended = extend_lexical_environment env slots /\ lexical_width extended <= ceiling.
Proof.
  intros ci cc ceiling available lengths polls env slots paid extended H.
  unfold paid_environment_extension in H.
  apply successful_environment_action_is_exact in H. destruct H as [HH _].
  now apply checked_environment_extension_preserves_exact_width_and_bindings in HH.
Qed.

(** Publication retains the old immutable value on failure; construction and
    arena insertion are private until success. This is not heap separation. *)
Definition publish_environment {A} (original : A) (result : ActionResult A) : A :=
  match result with Refused _ => original | Accepted _ value => value end.
Theorem refusal_preserves_published_input : forall A (original : A) paid,
  publish_environment original (Refused paid) = original.
Proof. reflexivity. Qed.

Example exact_two_phase_environment_allowance :
  environment_action false false 30 {| work_left := 11; units_left := 17 |}
    [2; 3] 1 (fun _ => false) (fun _ => Some 7) =
  Accepted {| work_left := 0; units_left := 0 |} 7.
Proof. reflexivity. Qed.

Example one_under_copy_units_keeps_paid_inspection :
  environment_action false false 30 {| work_left := 11; units_left := 16 |}
    [2; 3] 1 (fun _ => false) (fun _ => Some 7) =
  Refused {| work_left := 9; units_left := 16 |}.
Proof. reflexivity. Qed.

Example cancelled_length_scan_keeps_paid_inspection :
  environment_action false false 30 {| work_left := 11; units_left := 17 |}
    [2; 3] 1 (fun i => Nat.eqb i 1) (fun _ => Some 7) =
  Refused {| work_left := 9; units_left := 17 |}.
Proof. reflexivity. Qed.

Example empty_context_still_reserves_its_record :
  environment_action false false 4 {| work_left := 1; units_left := 4 |}
    [] 0 (fun _ => false) (fun _ => Some 7) =
  Accepted {| work_left := 0; units_left := 0 |} 7.
Proof. reflexivity. Qed.

Print Assumptions inspected_sum_is_exact.
Print Assumptions inspection_without_cancellation_reuses_debit_all.
Print Assumptions inspection_poll_refuses_before_read.
Print Assumptions inspected_bytes_success_exact.
Print Assumptions successful_inspection_is_paid_and_exact.
Print Assumptions successful_environment_action_is_exact.
Print Assumptions initial_cancellation_has_no_environment.
Print Assumptions inspection_refusal_never_invokes_copy.
Print Assumptions later_cancellation_retains_inspection_charge.
Print Assumptions copy_overdraw_retains_inspection_charge.
Print Assumptions environment_charge_is_iteration_order_independent.
Print Assumptions paid_extension_preserves_existing_lexical_semantics.
Print Assumptions refusal_preserves_published_input.
Print Assumptions exact_two_phase_environment_allowance.
Print Assumptions one_under_copy_units_keeps_paid_inspection.
Print Assumptions cancelled_length_scan_keeps_paid_inspection.
Print Assumptions empty_context_still_reserves_its_record.
