(** Finite semantic-reply metadata and a one-shot prepaid completion permit.

    The wire ABI is numeric version 1. Fixed status/domain/code/option tags
    are bounded host constants; caller quantities use the existing full-width
    unsigned scalar codec. The success body is separately charged and remains
    opaque here: receipt preservation and result permutation have their own
    checked models. No semantic execution or authority is supplied by a permit.

    Scalar width is an abstract Boolean oracle, instantiated by the already
    checked unsigned codec. Its maximum charge is valid for either width, so
    no unary expansion of 64-bit endpoints is needed. Logical payload is not
    physical RSS. Local encoding debits already prepaid credit; it never
    changes the cumulative counters reported in the shell. *)
From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import SemanticReceiptWire InstalledSemanticService InstalledFltJudgments.
Import ListNotations.

Module SemanticReplyCompletion.
Module W := SemanticReceiptWire.SemanticReceiptWire.
Module S := InstalledSemanticService.InstalledSemanticService.
Module J := InstalledFltJudgments.InstalledFltJudgments.

Definition limit_words limits :=
  let e := S.execution limits in
  [S.work e; S.normalization_steps e; S.outputs e; S.frontier e;
   S.proofs e; S.proof_nodes e; S.term_nodes e; S.term_bytes e;
   S.output_nodes e; S.output_bytes e; S.boundary_payload limits].
Definition encode_limits limits := W.Tuple (map W.UInt (limit_words limits)).
Definition decode_limits value := match value with
  | W.Tuple [W.UInt w; W.UInt n; W.UInt o; W.UInt f; W.UInt p; W.UInt pn;
             W.UInt tn; W.UInt tb; W.UInt onodes; W.UInt ob; W.UInt boundary] =>
      Some (S.service_limits (S.execution_limits w n o f p pn tn tb onodes ob) boundary)
  | _ => None end.

Theorem limits_inverse : forall limits, decode_limits (encode_limits limits) = Some limits.
Proof. intros [[a b c d e f g h i j] k]; reflexivity. Qed.

Definition encode_option {A} (encode : A -> W.Value) value := match value with
  | None => W.Tuple [W.UInt 0]
  | Some value => W.Tuple [W.UInt 1; encode value] end.
Definition decode_option {A} (decode : W.Value -> option A) value := match value with
  | W.Tuple [W.UInt 0] => Some None
  | W.Tuple [W.UInt 1; value] =>
      match decode value with Some value => Some (Some value) | None => None end
  | _ => None end.
Definition decode_uint value := match value with W.UInt n => Some n | _ => None end.

Lemma option_inverse : forall A (encode : A -> W.Value) decode,
  (forall value, decode (encode value) = Some value) ->
  forall value, decode_option decode (encode_option encode value) = Some value.
Proof. intros A encode decode H [value|]; cbn; [now rewrite H | reflexivity]. Qed.

Record Usage := usage {
  total_work : nat;
  kernel_work : option nat;
  effective_limits : option S.ServiceLimits;
  remaining_payload : nat
}.
Definition encode_usage u := W.Tuple
  [W.UInt (total_work u); encode_option W.UInt (kernel_work u);
   encode_option encode_limits (effective_limits u); W.UInt (remaining_payload u)].
Definition decode_usage value := match value with
  | W.Tuple [W.UInt work; kernel; limits; W.UInt remaining] =>
      match decode_option decode_uint kernel, decode_option decode_limits limits with
      | Some kernel, Some limits => Some (usage work kernel limits remaining)
      | _, _ => None end
  | _ => None end.

Theorem usage_inverse : forall u, decode_usage (encode_usage u) = Some u.
Proof.
  intros [work kernel limits remaining]. unfold encode_usage, decode_usage; cbn.
  rewrite (option_inverse nat W.UInt decode_uint); [| reflexivity].
  rewrite (option_inverse S.ServiceLimits encode_limits decode_limits limits_inverse).
  reflexivity.
Qed.

Theorem usage_encoding_retains_every_field : forall a b,
  encode_usage a = encode_usage b -> a = b.
Proof.
  intros a b H. pose proof (f_equal decode_usage H) as E.
  rewrite !usage_inverse in E. now inversion E.
Qed.

Inductive Event := Tag | Word (n : nat) | Slots (length : nat).
Definition option_events {A} (events : A -> list Event) value := match value with
  | None => [Slots 1; Tag]
  | Some value => [Slots 2; Tag] ++ events value end.
Definition limits_events limits := Slots 11 :: map Word (limit_words limits).
Definition usage_events u :=
  [Slots 4; Word (total_work u)] ++
  option_events (fun n => [Word n]) (kernel_work u) ++
  option_events limits_events (effective_limits u) ++ [Word (remaining_payload u)].
Definition completion_events (negative : bool) u :=
  [Slots 4; Tag; Tag] ++
  (if negative then [Slots 2; Tag; Tag] else []) ++ usage_events u.

Definition event_work (wide : nat -> bool) event := match event with
  | Tag | Slots _ => 1
  | Word n => if wide n then 10 else 1 end.
Definition event_payload (wide : nat -> bool) event := match event with
  | Tag => 16 | Slots length => 16 + 8 * length
  | Word n => if wide n then 25 else 16 end.
Definition sum (charge : Event -> nat) events := fold_right (fun e n => charge e + n) 0 events.

Lemma sum_app : forall charge a b, sum charge (a ++ b) = sum charge a + sum charge b.
Proof. intros charge a b. unfold sum. induction a; cbn; [reflexivity | now rewrite IHa, Nat.add_assoc]. Qed.

Lemma sum_cons : forall charge e rest, sum charge (e :: rest) = charge e + sum charge rest.
Proof. reflexivity. Qed.
Lemma sum_nil : forall charge, sum charge [] = 0.
Proof. reflexivity. Qed.

Lemma words_bound : forall charge cap words,
  (forall n, charge (Word n) <= cap) ->
  sum charge (map Word words) <= length words * cap.
Proof. intros charge cap words H. unfold sum. induction words; cbn; [lia | specialize (H a); lia]. Qed.

Lemma scalar_work_bound : forall wide n, event_work wide (Word n) <= 10.
Proof. intros; cbn; destruct (wide n); lia. Qed.
Lemma scalar_payload_bound : forall wide n, event_payload wide (Word n) <= 25.
Proof. intros; cbn; destruct (wide n); lia. Qed.

Lemma limits_work_bound : forall wide limits, sum (event_work wide) (limits_events limits) <= 111.
Proof.
  intros wide limits. pose proof (words_bound (event_work wide) 10 (limit_words limits) (scalar_work_bound wide)) as H.
  assert (L : length (limit_words limits) = 11) by (destruct limits as [[a b c d e f g h i j] k]; reflexivity).
  rewrite L in H. unfold limits_events. rewrite sum_cons. cbn [event_work]. lia.
Qed.
Lemma limits_payload_bound : forall wide limits, sum (event_payload wide) (limits_events limits) <= 379.
Proof.
  intros wide limits. pose proof (words_bound (event_payload wide) 25 (limit_words limits) (scalar_payload_bound wide)) as H.
  assert (L : length (limit_words limits) = 11) by (destruct limits as [[a b c d e f g h i j] k]; reflexivity).
  rewrite L in H. unfold limits_events. rewrite sum_cons. cbn [event_payload]. lia.
Qed.

Lemma usage_work_bound : forall wide u, sum (event_work wide) (usage_events u) <= 146.
Proof.
  intros wide [work kernel limits remaining].
  pose proof (scalar_work_bound wide work); pose proof (scalar_work_bound wide remaining).
  unfold usage_events; cbn [total_work kernel_work effective_limits remaining_payload].
  repeat rewrite sum_app.
  destruct kernel as [k|], limits as [l|]; cbn [option_events]; repeat rewrite sum_app;
    repeat rewrite sum_cons; repeat rewrite sum_nil;
    try pose proof (scalar_work_bound wide k);
    try pose proof (limits_work_bound wide l); cbn [event_work] in *; lia.
Qed.
Lemma usage_payload_bound : forall wide u, sum (event_payload wide) (usage_events u) <= 598.
Proof.
  intros wide [work kernel limits remaining].
  pose proof (scalar_payload_bound wide work); pose proof (scalar_payload_bound wide remaining).
  unfold usage_events; cbn [total_work kernel_work effective_limits remaining_payload].
  repeat rewrite sum_app.
  destruct kernel as [k|], limits as [l|]; cbn [option_events]; repeat rewrite sum_app;
    repeat rewrite sum_cons; repeat rewrite sum_nil;
    try pose proof (scalar_payload_bound wide k);
    try pose proof (limits_payload_bound wide l); cbn [event_payload] in *; lia.
Qed.

Definition reserved_work := 152.
Definition reserved_payload := 742.

Theorem exact_completion_shell_is_bounded : forall wide negative u,
  sum (event_work wide) (completion_events negative u) <= reserved_work /\
  sum (event_payload wide) (completion_events negative u) <= reserved_payload.
Proof.
  intros. pose proof (usage_work_bound wide u). pose proof (usage_payload_bound wide u).
  unfold completion_events; repeat rewrite sum_app.
  destruct negative; repeat rewrite sum_cons; repeat rewrite sum_nil;
    cbn [event_work event_payload].
  all: unfold reserved_work, reserved_payload; lia.
Qed.

Record State := state {
  spent_work : nat;
  spent_payload : nat;
  permit_live : bool;
  cancelled : bool
}.
Definition reserve work_limit payload_limit s :=
  if permit_live s || cancelled s then None else
  match J.charge_work work_limit (spent_work s) reserved_work,
        J.charge_work payload_limit (spent_payload s) reserved_payload with
  | Some work, Some bytes => Some (state work bytes true false)
  | _, _ => None end.

Theorem permit_reservation_keeps_prefixes_and_ceilings : forall wl bl before after,
  reserve wl bl before = Some after ->
  spent_work after = spent_work before + reserved_work /\
  spent_payload after = spent_payload before + reserved_payload /\
  spent_work after <= wl /\ spent_payload after <= bl /\ permit_live after = true.
Proof.
  intros wl bl before after H. unfold reserve in H.
  destruct (permit_live before || cancelled before); try discriminate.
  destruct (J.charge_work wl (spent_work before) reserved_work) as [w|] eqn:W; try discriminate.
  destruct (J.charge_work bl (spent_payload before) reserved_payload) as [b|] eqn:B; try discriminate.
  apply J.successful_charge_preserves_prefix_and_ceiling in W.
  apply J.successful_charge_preserves_prefix_and_ceiling in B.
  inversion H; subst; cbn; tauto.
Qed.

Definition observe_cancellation s := state (spent_work s) (spent_payload s) (permit_live s) true.
Definition finish s (proven : bool) local_work local_payload :=
  if permit_live s && negb (cancelled s && proven) &&
     Nat.leb local_work reserved_work && Nat.leb local_payload reserved_payload
  then Some (state (spent_work s) (spent_payload s) false (cancelled s))
  else None.

Theorem completion_does_not_recharge_or_refund : forall before proven w b after,
  finish before proven w b = Some after ->
  spent_work after = spent_work before /\ spent_payload after = spent_payload before /\
  permit_live after = false /\ cancelled after = cancelled before.
Proof.
  intros before proven w b after H. unfold finish in H.
  destruct (permit_live before && negb (cancelled before && proven) &&
    (w <=? reserved_work) && (b <=? reserved_payload)); inversion H; subst; auto.
Qed.

Theorem completion_cannot_spend_a_permit_twice : forall before proven w b after p w2 b2,
  finish before proven w b = Some after -> finish after p w2 b2 = None.
Proof.
  intros. apply completion_does_not_recharge_or_refund in H.
  destruct H as [_ [_ [H _]]]. unfold finish. now rewrite H.
Qed.

Theorem cancellation_forbids_proven_completion : forall s w b,
  finish (observe_cancellation s) true w b = None.
Proof. intros. unfold finish, observe_cancellation; cbn. now destruct (permit_live s). Qed.

Definition snapshot s kernel limits payload_limit :=
  usage (spent_work s) kernel limits (payload_limit - spent_payload s).

Theorem reported_usage_is_the_final_cumulative_usage :
  forall before proven w b after kernel limits payload_limit,
  finish before proven w b = Some after ->
  snapshot before kernel limits payload_limit = snapshot after kernel limits payload_limit.
Proof.
  intros. apply completion_does_not_recharge_or_refund in H.
  destruct H as [W [B _]]. unfold snapshot. now rewrite W, B.
Qed.

(** The concrete shell derives its status and success permission from the same
    constructor. Neither a separate caller Boolean nor arbitrary encoded
    status can bypass the cancellation check. The negative body has exactly
    two fixed host tag slots; their finite code policy is a Rust refinement. *)
Inductive Body :=
| ProvenBody (payload : W.Value)
| RefutedBody (domain code : nat)
| UndeterminedBody (domain code : nat)
| ErrorBody (domain code : nat).

Definition status body := match body with
  | ProvenBody _ => 0 | RefutedBody _ _ => 1
  | UndeterminedBody _ _ => 2 | ErrorBody _ _ => 3 end.
Definition is_proven body := match body with ProvenBody _ => true | _ => false end.
Definition encode_body body := match body with
  | ProvenBody payload => payload
  | RefutedBody domain code | UndeterminedBody domain code | ErrorBody domain code =>
      W.Tuple [W.UInt domain; W.UInt code] end.
Definition encode_reply body u :=
  W.Tuple [W.UInt 1; W.UInt (status body); encode_body body; encode_usage u].

Definition complete wide s body kernel limits work_limit payload_limit :=
  let u := snapshot s kernel limits payload_limit in
  let events := completion_events (negb (is_proven body)) u in
  if Nat.leb (spent_work s) work_limit && Nat.leb (spent_payload s) payload_limit then
    match finish s (is_proven body) (sum (event_work wide) events)
            (sum (event_payload wide) events) with
    | Some after => Some (encode_reply body u, after)
    | None => None end
  else None.

Theorem successful_completion_retains_its_exact_shell_and_counters :
  forall wide s body kernel limits wl bl reply after,
  complete wide s body kernel limits wl bl = Some (reply, after) ->
  reply = encode_reply body (snapshot after kernel limits bl) /\
  spent_work after = spent_work s /\ spent_payload after = spent_payload s /\
  spent_work after <= wl /\ spent_payload after <= bl /\ permit_live after = false.
Proof.
  intros wide s body kernel limits wl bl reply after H. unfold complete in H.
  destruct ((spent_work s <=? wl) && (spent_payload s <=? bl)) eqn:B; try discriminate.
  apply andb_true_iff in B. destruct B as [BW BB].
  apply Nat.leb_le in BW, BB.
  destruct (finish s (is_proven body)
    (sum (event_work wide) (completion_events (negb (is_proven body)) (snapshot s kernel limits bl)))
    (sum (event_payload wide) (completion_events (negb (is_proven body)) (snapshot s kernel limits bl))))
    as [next|] eqn:F; try discriminate.
  inversion H; subst. pose proof (reported_usage_is_the_final_cumulative_usage _ _ _ _ _ kernel limits bl F) as U.
  apply completion_does_not_recharge_or_refund in F. destruct F as [W [P [L C]]].
  rewrite U. repeat split; try assumption; congruence.
Qed.

Theorem cancelled_completion_cannot_encode_proven :
  forall wide s body kernel limits wl bl reply after,
  complete wide (observe_cancellation s) body kernel limits wl bl = Some (reply, after) ->
  match reply with W.Tuple [W.UInt 1; W.UInt 0; _; _] => False | _ => True end.
Proof.
  intros wide s body kernel limits wl bl reply after H.
  destruct body.
  - unfold complete in H. cbn [is_proven] in H.
    rewrite cancellation_forbids_proven_completion in H.
    destruct ((spent_work (observe_cancellation s) <=? wl) &&
              (spent_payload (observe_cancellation s) <=? bl)); discriminate.
  - apply successful_completion_retains_its_exact_shell_and_counters in H.
    destruct H as [-> _]. exact I.
  - apply successful_completion_retains_its_exact_shell_and_counters in H.
    destruct H as [-> _]. exact I.
  - apply successful_completion_retains_its_exact_shell_and_counters in H.
    destruct H as [-> _]. exact I.
Qed.

Theorem final_overdraw_has_no_completion : forall wide s body kernel limits wl bl,
  wl < spent_work s \/ bl < spent_payload s ->
  complete wide s body kernel limits wl bl = None.
Proof.
  intros wide s body kernel limits wl bl H. unfold complete.
  destruct (spent_work s <=? wl) eqn:W, (spent_payload s <=? bl) eqn:B;
    try reflexivity.
  apply Nat.leb_le in W, B. lia.
Qed.

End SemanticReplyCompletion.

Print Assumptions SemanticReplyCompletion.limits_inverse.
Print Assumptions SemanticReplyCompletion.usage_inverse.
Print Assumptions SemanticReplyCompletion.usage_encoding_retains_every_field.
Print Assumptions SemanticReplyCompletion.exact_completion_shell_is_bounded.
Print Assumptions SemanticReplyCompletion.permit_reservation_keeps_prefixes_and_ceilings.
Print Assumptions SemanticReplyCompletion.completion_does_not_recharge_or_refund.
Print Assumptions SemanticReplyCompletion.completion_cannot_spend_a_permit_twice.
Print Assumptions SemanticReplyCompletion.cancellation_forbids_proven_completion.
Print Assumptions SemanticReplyCompletion.reported_usage_is_the_final_cumulative_usage.
Print Assumptions SemanticReplyCompletion.successful_completion_retains_its_exact_shell_and_counters.
Print Assumptions SemanticReplyCompletion.cancelled_completion_cannot_encode_proven.
Print Assumptions SemanticReplyCompletion.final_overdraw_has_no_completion.
