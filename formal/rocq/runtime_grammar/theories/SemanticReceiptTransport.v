(** * Complete concrete receipt transport, without another semantic evaluator

    This finite record/sum mirrors every field of the runtime transition,
    normalization-hop, normalization-proof, and six premise receipt variants.
    Identifiers and scalar values are mathematical naturals; byte strings model
    ordered bytes, not strings to parse. Resource reservations use fixed logical
    widths, not Rust layout, physical memory or the future public wire format.

    The service consumes its own fresh, unmodified kernel result. The existing
    kernel supplies output-key provenance and semantic proof validity. The
    envelope projection below reuses its receipt-bound predicate; it does NOT
    certify arbitrary external/mutated Rust bundles or re-prove the evaluator.
    Whole-record pairing preserves all additional fields, including nested
    premise rule IDs and every exhaustive normalization proof. A first hop starts
    after the entry rewrite, so no first-hop/original-input equality is assumed.

    The schedule denotes the events of a borrowed flat traversal; Rust need not
    allocate this list. Successful checked traversal preserves both prior
    counters. Cancellation and rejected reservations abort without publication;
    this module makes no physical-resource or cancellation-latency claim. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From RuntimeGrammar Require Import InstalledFltJudgments.
Import ListNotations.

Module SemanticReceiptTransport.
Module J := InstalledFltJudgments.InstalledFltJudgments.
Module K := J.Kernel.
Definition Bytes := list nat.

Inductive Opcode := ExactTermEq | Utf8AtEnd | Utf8ScalarAt | Utf8Slice
  | CheckedNatAdd | Utf8ConcatMany.

Inductive Premise :=
| Freshness (rule premise : nat)
| Transition (rule premise child_rule : nat)
| Judgment (rule premise judgment proofs proof_steps : nat)
| ForAll (rule premise elements : nat)
| Intrinsic (rule premise : nat) (opcode : Opcode)
    (inputs outputs : list Bytes) (work : nat)
| Guard (rule premise : nat) (guard_commitment evidence_commitment : Bytes).

Record Step := step {
  step_rule : nat;
  step_before : Bytes;
  step_after : Bytes;
  step_premises : list Premise
}.

Record Hop := hop {
  hop_before : Bytes;
  hop_after : Bytes;
  hop_proofs : list Step;
  hop_work : nat
}.

Inductive Resource := NoGrade | CheckedGrade (sort : nat) (grade cost_image : Bytes).
Inductive EffectClass := Pure | Structural | Behavioral | ResourceEffect | External.

Record Receipt := receipt {
  language : Bytes; theory : Bytes; image : Bytes;
  action : nat; rule : nat;
  input : Bytes; output : Bytes;
  effect : nat; effect_class : EffectClass;
  resource : Resource;
  premises : list Premise;
  hops : list Hop;
  work : nat
}.

Definition abstract_resource r :=
  match r with
  | NoGrade => K.NoSemanticGrade
  | CheckedGrade _ grade _ => K.CheckedSemanticGrade grade
  end.

Definition abstract_receipt r : K.TransitionReceipt :=
  {| K.receipt_language := language r; K.receipt_theory := theory r;
     K.receipt_image := image r; K.receipt_action := action r;
     K.receipt_rule := rule r; K.receipt_input := input r;
     K.receipt_output := output r; K.receipt_grade := abstract_resource (resource r);
     K.receipt_effects := [effect r]; K.receipt_work := work r |}.

Definition envelope_bound manifest request fresh receipt :=
  K.receipt_bound manifest request fresh (abstract_receipt receipt).

Theorem envelope_projection_reuses_the_existing_binding_contract :
  forall manifest request fresh receipt,
    envelope_bound manifest request fresh receipt = true ->
    K.receipt_bound manifest request fresh (abstract_receipt receipt) = true.
Proof. intros; exact H. Qed.

(** Schedule v1: event = logical work and logical payload bytes. Fixed fields
    use a one-unit visit; each variable payload additionally visits its bytes.
    Values of receipt.work and intrinsic/hop.work are scalar DATA here, never
    additional execution charges. Commitments occupy fixed 32-byte fields in
    Rust; parameterized Bytes retain their complete mathematical content. *)
Definition Event := (nat * nat)%type.
Definition fixed (bytes : nat) : Event := (1, bytes).
Definition payload (bytes : Bytes) : Event := (S (length bytes), 8 + length bytes).
Definition key_list_events (keys : list Bytes) := fixed 8 :: map payload keys.

Definition premise_events p : list Event :=
  fixed 9 :: (* tag + rule + premise *)
  match p with
  | Freshness _ _ => []
  | Transition _ _ _ => [fixed 4]
  | Judgment _ _ _ _ _ => [fixed 12]
  | ForAll _ _ _ => [fixed 4]
  | Intrinsic _ _ _ inputs outputs _ =>
      fixed 9 :: key_list_events inputs ++ key_list_events outputs
  | Guard _ _ _ _ => [fixed 64]
  end.

Definition premise_list_events ps := fixed 8 :: flat_map premise_events ps.
Definition step_events s :=
  [fixed 4; payload (step_before s); payload (step_after s)] ++
  premise_list_events (step_premises s).
Definition hop_events h :=
  [fixed 8; payload (hop_before h); payload (hop_after h); fixed 8] ++
  flat_map step_events (hop_proofs h).
Definition resource_events r :=
  match r with
  | NoGrade => [fixed 1]
  | CheckedGrade _ grade _ => [fixed 37; payload grade]
  end.
Definition receipt_events r :=
  (* Three commitments, action/rule/effect, class tag, aggregate work. *)
  [fixed 117; payload (input r); payload (output r)] ++
  resource_events (resource r) ++ premise_list_events (premises r) ++
  fixed 8 :: flat_map hop_events (hops r).

Definition work_sum (events : list Event) := fold_right (fun event n => fst event + n) 0 events.
Definition payload_sum (events : list Event) := fold_right (fun event n => snd event + n) 0 events.

Fixpoint charge_events events work_limit payload_limit used_work used_payload
    : option (nat * nat) :=
  match events with
  | [] =>
      match J.charge_work work_limit used_work 0,
            J.charge_work payload_limit used_payload 0 with
      | Some w, Some b => Some (w, b)
      | _, _ => None
      end
  | event :: rest =>
      match J.charge_work work_limit used_work (fst event),
            J.charge_work payload_limit used_payload (snd event) with
      | Some w, Some b => charge_events rest work_limit payload_limit w b
      | _, _ => None
      end
  end.

Theorem successful_walk_preserves_both_prefixes_and_ceilings :
  forall events wl bl w b final_w final_b,
    charge_events events wl bl w b = Some (final_w, final_b) ->
    final_w = w + work_sum events /\ final_b = b + payload_sum events /\
    final_w <= wl /\ final_b <= bl.
Proof.
  induction events as [|event rest IH]; intros wl bl w b fw fb H; cbn in H.
  - destruct (J.charge_work wl w 0) as [next_w|] eqn:W; try discriminate.
    destruct (J.charge_work bl b 0) as [next_b|] eqn:B; try discriminate.
    inversion H; subst. apply J.successful_charge_preserves_prefix_and_ceiling in W.
    apply J.successful_charge_preserves_prefix_and_ceiling in B.
    unfold work_sum, payload_sum; cbn; lia.
  - destruct (J.charge_work wl w (fst event)) as [next_w|] eqn:W; try discriminate.
    destruct (J.charge_work bl b (snd event)) as [next_b|] eqn:B; try discriminate.
    apply J.successful_charge_preserves_prefix_and_ceiling in W.
    apply J.successful_charge_preserves_prefix_and_ceiling in B.
    specialize (IH wl bl next_w next_b fw fb H).
    unfold work_sum, payload_sum in *; cbn; lia.
Qed.

Theorem aggregate_scalar_is_not_recharged :
  forall lang thy img act rl inp out eff cls res ps hs first second,
    receipt_events (receipt lang thy img act rl inp out eff cls res ps hs first) =
    receipt_events (receipt lang thy img act rl inp out eff cls res ps hs second).
Proof. reflexivity. Qed.

Section Pairing.
  Context {Term : Type}.
  Record Export := export { exported_term : Term; exported_receipt : Receipt }.

  Fixpoint pair_pending (receipts : list Receipt) (terms : list Term)
      (private : list Export) : option (list Export) :=
    match receipts, terms with
    | [], [] => Some (rev private)
    | r :: rs, t :: ts => pair_pending rs ts (export t r :: private)
    | _, _ => None
    end.

  Theorem pairing_keeps_the_complete_ordered_lists :
    forall receipts terms private exports,
      pair_pending receipts terms private = Some exports ->
      map exported_receipt exports = rev (map exported_receipt private) ++ receipts /\
      map exported_term exports = rev (map exported_term private) ++ terms.
  Proof.
    induction receipts as [|r rs IH]; intros terms private exports H;
      destruct terms as [|t ts]; cbn in H; try discriminate.
    - inversion H; subst. split; rewrite map_rev; now rewrite app_nil_r.
    - apply IH in H. destruct H as [Hr Ht]. split; [rewrite Hr | rewrite Ht];
        cbn; now rewrite <- app_assoc.
  Qed.

  Definition pair_results receipts terms := pair_pending receipts terms [].

  Corollary successful_pairing_keeps_every_receipt_field :
    forall (A : Type) (field : Receipt -> A) receipts terms exports,
      pair_results receipts terms = Some exports ->
      map (fun e => field (exported_receipt e)) exports = map field receipts.
  Proof.
    intros A field receipts terms exports H.
    apply pairing_keeps_the_complete_ordered_lists in H.
    destruct H as [Hr _]. cbn in Hr. rewrite <- map_map. now rewrite Hr.
  Qed.

  Theorem mismatched_lengths_cannot_publish_a_prefix :
    forall receipts terms,
      length receipts <> length terms -> pair_results receipts terms = None.
  Proof.
    intros receipts terms Hlength.
    destruct (pair_results receipts terms) as [exports|] eqn:H; [|reflexivity].
    apply pairing_keeps_the_complete_ordered_lists in H.
    destruct H as [Hr Ht]. cbn in Hr, Ht.
    apply (f_equal (@length Receipt)) in Hr.
    apply (f_equal (@length Term)) in Ht.
    rewrite length_map in Hr, Ht. exfalso. lia.
  Qed.
End Pairing.

End SemanticReceiptTransport.

Print Assumptions SemanticReceiptTransport.envelope_projection_reuses_the_existing_binding_contract.
Print Assumptions SemanticReceiptTransport.successful_walk_preserves_both_prefixes_and_ceilings.
Print Assumptions SemanticReceiptTransport.aggregate_scalar_is_not_recharged.
Print Assumptions SemanticReceiptTransport.pairing_keeps_the_complete_ordered_lists.
Print Assumptions SemanticReceiptTransport.successful_pairing_keeps_every_receipt_field.
Print Assumptions SemanticReceiptTransport.mismatched_lengths_cannot_publish_a_prefix.
