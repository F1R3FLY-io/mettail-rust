(** Resource interpretation of the initial scalar/append construction machine.

    A footprint counts expression entries and UTF-8 payload bytes. Rocq strings
    here represent byte strings, not Unicode scalar sequences. Four logical
    units per entry follow the existing reflected-codec convention; they are
    not native sizeof, allocator capacity, protobuf size, semantic gas or RSS.

    The existing Par append clones the left sequence, then concat clones both
    temporary sequences. Thus its copy footprint is twice left plus right,
    although its output footprint is just left plus right. These equations
    require correspondence checks against those actual constructor bodies.

    This module reuses the checked-debit laws. It proves exact cached payload
    measures and atomic, non-refunding precharge composition. The concrete
    graph machine and every intermediate stack bound are proved separately in
    RholangInitialGraphMachine. No recursive implementation is prescribed. *)
From Stdlib Require Import List Arith Lia String Bool.
From RhoBridge Require Import RholangInitialGraphInterpretation
  RholangInitialGraphMachine RholangTargetConstruction.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget.
Import ListNotations.

Record Footprint := { entry_count : nat; text_bytes : nat }.
Definition plus (lhs rhs : Footprint) : Footprint :=
  {| entry_count := entry_count lhs + entry_count rhs;
     text_bytes := text_bytes lhs + text_bytes rhs |}.
Definition head_bytes (head : Head) : nat :=
  match head with MakeHead (TextHead payload) _ => String.length payload | _ => 0 end.
Fixpoint sequence_bytes (heads : list Head) : nat :=
  match heads with [] => 0 | head :: rest => head_bytes head + sequence_bytes rest end.
Definition footprint (value : Value) : Footprint :=
  {| entry_count := List.length (heads_of value);
     text_bytes := sequence_bytes (heads_of value) |}.
Definition scalar_footprint (scalar : InitialScalar) : Footprint :=
  match scalar with
  | EmptyScalar => {| entry_count := 0; text_bytes := 0 |}
  | TextScalar payload => {| entry_count := 1; text_bytes := String.length payload |}
  | _ => {| entry_count := 1; text_bytes := 0 |}
  end.
Fixpoint tree_footprint (tree : InitialTree) : Footprint :=
  match tree with
  | ScalarTree scalar => scalar_footprint scalar
  | AppendTree lhs rhs => plus (tree_footprint lhs) (tree_footprint rhs)
  end.

Lemma sequence_bytes_app : forall lhs rhs,
  sequence_bytes (lhs ++ rhs) = sequence_bytes lhs + sequence_bytes rhs.
Proof. induction lhs; intros; cbn; [reflexivity|rewrite IHlhs; lia]. Qed.

Theorem scalar_footprint_is_exact : forall scalar,
  scalar_footprint scalar = footprint (scalar_denotation scalar).
Proof.
  destruct scalar; unfold scalar_footprint, scalar_denotation, footprint,
    empty, singleton, boolean, text; cbn; try reflexivity.
  now rewrite Nat.add_0_r.
Qed.

Theorem append_footprint_is_exact : forall lhs rhs,
  footprint (append lhs rhs) = plus (footprint lhs) (footprint rhs).
Proof.
  intros. unfold footprint, append, plus; cbn [heads_of].
  now rewrite length_app, sequence_bytes_app.
Qed.

Theorem cached_tree_footprint_is_exact : forall tree,
  tree_footprint tree = footprint (tree_denotation tree).
Proof.
  induction tree; cbn [tree_footprint tree_denotation].
  - apply scalar_footprint_is_exact.
  - now rewrite append_footprint_is_exact, IHtree1, IHtree2.
Qed.

Definition initial_head (head : Head) : Prop :=
  match head with
  | MakeHead (IntegerHead _) [] | MakeHead (BooleanHead _) []
  | MakeHead (TextHead _) [] => True
  | _ => False
  end.

(** The old closed-head result has a concrete syntax-domain premise. Bound and
    wildcard leaves are flat too, but their metadata is not generally closed. *)
Fixpoint original_scalar_tree (tree : InitialTree) : bool :=
  match tree with
  | ScalarTree (BoundScalar _ _) | ScalarTree (WildcardScalar _) => false
  | ScalarTree _ => true
  | AppendTree lhs rhs => original_scalar_tree lhs && original_scalar_tree rhs
  end.

Theorem initial_outputs_have_only_flat_closed_scalar_heads : forall tree,
  original_scalar_tree tree = true ->
  Forall initial_head (heads_of (tree_denotation tree)) /\
  summary_of (tree_denotation tree) = closed_summary.
Proof.
  induction tree as [scalar|lhs IHleft rhs IHright]; intro Hdomain.
  - destruct scalar; cbn in Hdomain; try discriminate; cbn; split; repeat constructor.
  - apply andb_true_iff in Hdomain. destruct Hdomain as [HLdomain HRdomain].
    destruct (IHleft HLdomain) as [HL SL], (IHright HRdomain) as [HR SR].
    cbn [tree_denotation]. split.
    + change (Forall initial_head
        (heads_of (tree_denotation lhs) ++ heads_of (tree_denotation rhs))).
      apply Forall_app; auto.
    + change (join_summary (summary_of (tree_denotation lhs))
        (summary_of (tree_denotation rhs)) = closed_summary).
      now rewrite SL, SR.
Qed.

Definition flat_reference_head (head : Head) : Prop :=
  match head with
  | MakeHead (BoundHead _) [] | MakeHead WildcardHead [] => True
  | _ => initial_head head
  end.
Theorem extended_outputs_have_only_flat_heads : forall tree,
  Forall flat_reference_head (heads_of (tree_denotation tree)).
Proof.
  induction tree as [scalar|lhs HL rhs HR].
  - destruct scalar; cbn; repeat constructor.
  - change (Forall flat_reference_head
      (heads_of (tree_denotation lhs) ++ heads_of (tree_denotation rhs))).
    apply Forall_app; auto.
Qed.

Definition append_copy_footprint (lhs rhs : Footprint) := plus lhs (plus lhs rhs).
Definition payload_work (size : Footprint) := entry_count size + text_bytes size.
Definition payload_units (size : Footprint) := 4 * entry_count size + text_bytes size.

Theorem append_charge_covers_the_actual_three_copies : forall lhs rhs,
  let copies := append_copy_footprint (footprint lhs) (footprint rhs) in
  entry_count copies = 2 * List.length (heads_of lhs) + List.length (heads_of rhs) /\
  text_bytes copies = 2 * sequence_bytes (heads_of lhs) + sequence_bytes (heads_of rhs) /\
  entry_count (footprint (append lhs rhs)) <= entry_count copies /\
  text_bytes (footprint (append lhs rhs)) <= text_bytes copies.
Proof.
  intros. rewrite append_footprint_is_exact.
  unfold append_copy_footprint, plus, footprint; cbn; lia.
Qed.

(** A successful reservation updates both dimensions together. Failure leaves
    both unchanged; a later callback failure retains the already paid meter.
    Remaining work is work_limit minus the cumulative incoming counter, whose
    representability/overdraw checks remain explicit in the Rust adapter. *)
Record Allowance := { work_left : nat; units_left : nat }.
Definition reserve (available : Allowance) (work units : nat) : option Allowance :=
  match debit (work_left available) work, debit (units_left available) units with
  | Some next_work, Some next_units =>
    Some {| work_left := next_work; units_left := next_units |}
  | _, _ => None
  end.

Theorem successful_reservation_is_exact : forall available work units next,
  reserve available work units = Some next ->
  work_left next + work = work_left available /\
  units_left next + units = units_left available.
Proof.
  intros available work units next H. unfold reserve in H.
  destruct (debit (work_left available) work) eqn:HW; [|discriminate].
  destruct (debit (units_left available) units) eqn:HU; [|discriminate].
  inversion H; subst. cbn. split; eapply successful_debit_is_exact; eassumption.
Qed.

Theorem reservation_succeeds_exactly_when_both_dimensions_fit : forall available work units,
  (exists next, reserve available work units = Some next) <->
  work <= work_left available /\ units <= units_left available.
Proof.
  intros. split.
  - intros [next H]. apply successful_reservation_is_exact in H. lia.
  - intros [HW HU]. unfold reserve, debit.
    apply Nat.leb_le in HW. apply Nat.leb_le in HU. rewrite HW, HU. eauto.
Qed.

Inductive ActionResult (A : Type) :=
| Refused (remaining : Allowance)
| Accepted (remaining : Allowance) (result : A).
Arguments Refused {A}.
Arguments Accepted {A}.

Definition precharged_action {A} (cancelled : bool) (available : Allowance)
    (work units : nat) (build : unit -> option A) : ActionResult A :=
  if cancelled then Refused available else
  match reserve available work units with
  | None => Refused available
  | Some next => match build tt with
    | None => Refused next
    | Some value => Accepted next value
    end
  end.

Theorem cancellation_prevents_construction : forall A available work units (build : unit -> option A),
  precharged_action true available work units build = Refused available.
Proof. reflexivity. Qed.

Theorem failed_precharge_is_independent_of_constructor :
  forall A available work units (build : unit -> option A),
  reserve available work units = None ->
  precharged_action false available work units build = Refused available.
Proof. intros; unfold precharged_action; now rewrite H. Qed.

Theorem callback_failure_does_not_refund :
  forall A available work units next (build : unit -> option A),
  reserve available work units = Some next -> build tt = None ->
  precharged_action false available work units build = Refused next.
Proof. intros; unfold precharged_action; now rewrite H, H0. Qed.

Theorem successful_action_constructs_only_the_paid_result :
  forall A cancelled available work units (build : unit -> option A) next value,
  precharged_action cancelled available work units build = Accepted next value ->
  cancelled = false /\ build tt = Some value /\
  work_left next + work = work_left available /\
  units_left next + units = units_left available.
Proof.
  intros A cancelled available work units build next value H.
  destruct cancelled; [discriminate|]. unfold precharged_action in H.
  destruct (reserve available work units) as [paid|] eqn:HP; [|discriminate].
  destruct (build tt) eqn:HB; [|discriminate]. inversion H; subst.
  apply successful_reservation_is_exact in HP. auto.
Qed.

(** Separate control and payload reservations preserve an already paid control
    step if payload admission fails. This matters even for empty payloads. *)
Theorem control_then_payload_success_is_exact : forall available after_control final size,
  reserve available 1 0 = Some after_control ->
  reserve after_control (payload_work size) (payload_units size) = Some final ->
  work_left final + 1 + payload_work size = work_left available /\
  units_left final + payload_units size = units_left available.
Proof. intros. apply successful_reservation_is_exact in H, H0. lia. Qed.

Theorem successful_job_count_is_bounded : forall costs work next,
  debit_all work (map (fun payload => 1 + payload) costs) = Some next ->
  List.length costs <= work.
Proof.
  intros costs work next H.
  rewrite <- (length_map (fun payload => 1 + payload) costs).
  eapply positive_control_steps_are_bounded_by_the_initial_budget; [|exact H].
  apply Forall_forall. intros amount Hmember. apply in_map_iff in Hmember.
  destruct Hmember as [payload [<- _]]. lia.
Qed.

Print Assumptions scalar_footprint_is_exact.
Print Assumptions append_footprint_is_exact.
Print Assumptions cached_tree_footprint_is_exact.
Print Assumptions initial_outputs_have_only_flat_closed_scalar_heads.
Print Assumptions extended_outputs_have_only_flat_heads.
Print Assumptions append_charge_covers_the_actual_three_copies.
Print Assumptions successful_reservation_is_exact.
Print Assumptions reservation_succeeds_exactly_when_both_dimensions_fit.
Print Assumptions cancellation_prevents_construction.
Print Assumptions failed_precharge_is_independent_of_constructor.
Print Assumptions callback_failure_does_not_refund.
Print Assumptions successful_action_constructs_only_the_paid_result.
Print Assumptions control_then_payload_success_is_exact.
Print Assumptions successful_job_count_is_bounded.
