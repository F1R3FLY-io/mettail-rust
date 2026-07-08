(*
 * NativeSystemProcessBoundary: the Stage 3e native-system-process dispatch is
 * TOTAL-OR-REJECT, and the emitted COMM payload is EXACTLY the trusted native
 * handler's value — the encoder DELEGATES, it never fabricates.
 *
 * The Rust lowering (`rholang-codegen/src/rho_net_lower.rs`,
 * `lower_native_system_process` / `native_rule_shape`) compiles a native system
 * process `NativeProc(a0..a_{k-1}) ~> <native value>` — a `![…] fold` HOL term the
 * Rho scalar-contract path rejects (BigInt/large-int arithmetic, `PowInt`,
 * factorial) — to a persistent flat DISPATCH RECEIVER
 * `for (result, out <- c) { out!(result) }` (the one-slot `sigma_receiver_par`).
 * The native σ-injection (`macros/src/gen/runtime/rho_invocation.rs`) reflects the
 * firing's CONTRACTUM — the value the host's TRUSTED native handler computed inside
 * Dovetail saturation (model-b), carried on
 * `RuntimeRewriteJustification::contractum` (Stage 3c) — and sends it as the single
 * dispatch argument on `c`; the receiver forwards that slot on `@out`.
 *
 * Two pieces carry correctness, modeled and proved here:
 *
 *   (1) TOTAL-OR-REJECT (`lower_native_system_process`). Every native process either
 *       MATERIALIZES a dispatch receiver or is REJECTED with a PRECISE reason — never
 *       a silent no-op. It materializes iff its evaluation mode is `fold` (so the host
 *       produces a funded-best contractum the receiver can forward — `native_rule_shape`)
 *       AND its dispatch channel resolves. A `step` (or annotation-less) native process
 *       is rejected `NotFold`; an unresolvable channel is rejected `ChannelUnresolved`.
 *       Modeled as [lower]; proved [lower_total], [lower_materialized_iff_fold_and_channel],
 *       [lower_rejected_has_precise_reason].
 *
 *   (2) DELEGATION, NO FABRICATION (the dispatch receiver + native σ-injection). The
 *       receiver forwards ONLY its single bound slot ([receiver_emit] = the head of the
 *       injected argument list), and the injection fills that slot with the REFLECTED
 *       contractum ([inject] = [reflect handler_value]). So the emitted payload is
 *       EXACTLY [reflect handler_value] ([emitted_is_reflected_handler_value]): the
 *       encoder introduces no value of its own — the structural rendezvous (the COMM on
 *       the dispatch channel) is real, and the PAYLOAD is delegated to the trusted
 *       handler. And the payload TRACKS the handler value: distinct handler values yield
 *       distinct payloads ([emitted_tracks_handler_value], under [reflect] injective —
 *       which the constructor reflection guarantees), so the encoder cannot fabricate a
 *       constant unrelated to the handler's computation.
 *
 * A native system process is dispatched by a real COMM on the rule's dedicated channel;
 * ONLY the value is host-computed, under the trusted-handler obligation modeled by
 * RhoHostObligationBoundary.v (a `NativeHandler` host disposition). It inherits the
 * flat-receiver COMM correspondence (LinearCommCorrespondence.v) and the install boundary
 * (RhoLoweringTotalOrRejects.v); this file discharges the ADDED native-dispatch
 * total-or-reject + payload-delegation obligation.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (Section
 * Variable/Hypothesis only, discharged when the section closes).
 *)

From Stdlib Require Import List.

Import ListNotations.

Section NativeSystemProcessBoundary.

  (* ---------------------------------------------------------------------------
     (1) TOTAL-OR-REJECT dispatch.
     --------------------------------------------------------------------------- *)

  (* The evaluation mode of a native system process HOL term (`ast/src/types.rs`
     `EvalMode`). Only [Fold] reduces to a host-computed value INSIDE Dovetail
     saturation (producing a rewrite justification whose contractum the dispatch
     receiver forwards); [Step] reduces on a different path (partial / routing to an
     `Err` normal form) and exposes no funded-best contractum. *)
  Inductive EvalMode : Type := Fold | Step.

  (* A native system process term: its evaluation mode plus its category/label ids
     (`GrammarRule` category + label — the op-variant firing identity the report
     producer bare-ifies the native firing to, e.g. [Int_PowInt]). *)
  Record NativeTerm : Type := {
    nt_eval  : EvalMode;
    nt_cat   : nat;
    nt_label : nat
  }.

  (* [native_rule_shape] (`rho_net_lower.rs`): the op-variant firing label a native
     process's Dovetail firing carries — [Some (cat, label)] iff its mode is [Fold],
     else [None] (a `step` native process has no host-computed contractum). *)
  Definition native_rule_shape (t : NativeTerm) : option (nat * nat) :=
    match nt_eval t with
    | Fold => Some (nt_cat t, nt_label t)
    | Step => None
    end.

  (* The precise, enumerated fail-closed reason (`UnsupportedFamily` /
     `RhoNetLoweringError`): a non-`fold` native process ([NotFold],
     `NativeSystemProcessNotFold`), or an unresolvable dispatch channel
     ([ChannelUnresolved], `RuleSourceDrift` / `ChannelResolution`). *)
  Inductive RejectReason : Type := NotFold | ChannelUnresolved.

  (* The lowering outcome (`RhoNetLoweredRule`): a MATERIALIZED dispatch receiver
     ([Materialized]) or a fail-closed REJECTION ([Rejected]) carrying its precise
     reason. There is NO third "silently dropped" outcome — the whole point of the
     install boundary. *)
  Inductive LowerOutcome : Type :=
    | Materialized : LowerOutcome
    | Rejected     : RejectReason -> LowerOutcome.

  (* Whether the native process's mode is [Fold]. *)
  Definition is_fold (t : NativeTerm) : bool :=
    match nt_eval t with Fold => true | Step => false end.

  (* [lower_native_system_process] modeled: route on [native_rule_shape]. A non-`fold`
     native process fails closed with the precise [NotFold] reason; a `fold` native
     process materializes its dispatch receiver iff its channel resolves
     ([channel_ok]), otherwise fails closed [ChannelUnresolved]. *)
  Definition lower (t : NativeTerm) (channel_ok : bool) : LowerOutcome :=
    match native_rule_shape t with
    | None => Rejected NotFold
    | Some _ => if channel_ok then Materialized else Rejected ChannelUnresolved
    end.

  (* TOTAL-OR-REJECT: every native process either materializes or is rejected — never
     a silent no-op (the install boundary can drop nothing). *)
  Theorem lower_total : forall t channel_ok,
    lower t channel_ok = Materialized
    \/ (exists r, lower t channel_ok = Rejected r).
  Proof.
    intros t channel_ok. unfold lower.
    destruct (native_rule_shape t) as [p|].
    - destruct channel_ok.
      + left. reflexivity.
      + right. exists ChannelUnresolved. reflexivity.
    - right. exists NotFold. reflexivity.
  Qed.

  (* MATERIALIZES iff `fold` AND the channel resolves — exactly the two conditions
     `lower_native_system_process` requires before building the dispatch receiver. *)
  Theorem lower_materialized_iff_fold_and_channel : forall t channel_ok,
    lower t channel_ok = Materialized <-> (is_fold t = true /\ channel_ok = true).
  Proof.
    intros t channel_ok. unfold lower, is_fold, native_rule_shape.
    destruct (nt_eval t); simpl.
    - destruct channel_ok; simpl; split.
      + intro. split; reflexivity.
      + intro. reflexivity.
      + intro H. discriminate H.
      + intros [_ H]. discriminate H.
    - split.
      + intro H. discriminate H.
      + intros [H _]. discriminate H.
  Qed.

  (* Every REJECTION carries a PRECISE, determined reason: [NotFold] for a `step`
     native process, [ChannelUnresolved] for a `fold` native process with an
     unresolvable channel. No rejection is unexplained. *)
  Theorem lower_rejected_has_precise_reason : forall t channel_ok r,
    lower t channel_ok = Rejected r ->
      (r = NotFold /\ nt_eval t = Step)
      \/ (r = ChannelUnresolved /\ nt_eval t = Fold /\ channel_ok = false).
  Proof.
    intros t channel_ok r H. unfold lower, native_rule_shape in H.
    destruct (nt_eval t) eqn:Emode.
    - destruct channel_ok eqn:Echan.
      + discriminate H.
      + right. injection H as H'. subst r. repeat split; (reflexivity || assumption).
    - left. injection H as H'. subst r. repeat split; (reflexivity || assumption).
  Qed.

  (* ---------------------------------------------------------------------------
     (2) PAYLOAD DELEGATION — the encoder delegates, never fabricates.
     --------------------------------------------------------------------------- *)

  (* The domain of values: a native handler's computed value, and its reflected Rho
     image (a `Par`). Abstract — the theory is parametric in the value/reflection
     representation (discharged when the section closes; no axiom). *)
  Variable Val : Type.

  (* The constructor reflection encoder (`reflect_ground_term_par`): reflect a
     host-computed contractum to its ground Rho `Par`. *)
  Variable reflect : Val -> Val.

  (* The installed dispatch receiver `for (result, out <- c) { out!(result) }` forwards
     ONLY its single bound slot — modeled as the HEAD of the delivered argument list. It
     introduces no value of its own; whatever it emits, it received. *)
  Definition receiver_emit (args : list Val) : option Val := hd_error args.

  (* The native σ-injection sends EXACTLY the reflected contractum as the single dispatch
     argument (`term_contract_call(c, vec![reflect(contractum)], out)`). The contractum
     IS the trusted handler's value (the Stage 3c contractum mechanism: the host computes
     the native value and carries it on the firing's justification). *)
  Definition inject (handler_value : Val) : list Val := [reflect handler_value].

  (* MAIN (delegation): the emitted COMM payload is EXACTLY the reflection of the trusted
     handler's value. The receiver forwards the single injected slot, and the injection
     put there is [reflect handler_value] and nothing else — the encoder delegates the
     payload to the handler, fabricating no value of its own. *)
  Theorem emitted_is_reflected_handler_value : forall handler_value,
    receiver_emit (inject handler_value) = Some (reflect handler_value).
  Proof.
    intro handler_value. unfold receiver_emit, inject. reflexivity.
  Qed.

  (* NO FABRICATION (weak form, hypothesis-free): the emitted payload DETERMINES the
     reflected handler value — two firings emit the same payload only if they reflect the
     same handler value. The payload carries the handler's computation, not a constant. *)
  Theorem emitted_determines_reflected_value : forall v1 v2,
    receiver_emit (inject v1) = receiver_emit (inject v2) -> reflect v1 = reflect v2.
  Proof.
    intros v1 v2 H.
    rewrite !emitted_is_reflected_handler_value in H.
    injection H as H'. exact H'.
  Qed.

  (* The constructor reflection is injective (the ground-term reflector tags each
     constructor distinctly — the same NoDup-order injectivity BinderReflectionTotalOrReject
     establishes for the reflected σ image). A Section Hypothesis: discharged into the
     theorem below when the section closes (no axiom). *)
  Hypothesis reflect_inj : forall v1 v2, reflect v1 = reflect v2 -> v1 = v2.

  (* NO FABRICATION (strong form): the emitted payload TRACKS the handler value — distinct
     handler values yield distinct payloads. The encoder cannot collapse the handler's
     computation to a fabricated constant: the payload is a faithful, injective image of
     exactly what the trusted handler computed. *)
  Theorem emitted_tracks_handler_value : forall v1 v2,
    receiver_emit (inject v1) = receiver_emit (inject v2) -> v1 = v2.
  Proof.
    intros v1 v2 H.
    apply reflect_inj, emitted_determines_reflected_value. exact H.
  Qed.

  (* END-TO-END: a `fold` native process with a resolvable dispatch channel MATERIALIZES
     its receiver, and driving that receiver with the trusted handler's value [v] (the
     firing's contractum) emits EXACTLY [reflect v] — the whole Stage 3e claim: the native
     system process fires as a COMM whose delegated payload is the handler's value. *)
  Theorem fold_native_process_fires_handler_value : forall t channel_ok v,
    nt_eval t = Fold ->
    channel_ok = true ->
    lower t channel_ok = Materialized
    /\ receiver_emit (inject v) = Some (reflect v).
  Proof.
    intros t channel_ok v Hfold Hchan. split.
    - apply lower_materialized_iff_fold_and_channel.
      unfold is_fold. rewrite Hfold. split; [ reflexivity | exact Hchan ].
    - apply emitted_is_reflected_handler_value.
  Qed.

End NativeSystemProcessBoundary.

Print Assumptions lower_total.
Print Assumptions lower_materialized_iff_fold_and_channel.
Print Assumptions lower_rejected_has_precise_reason.
Print Assumptions emitted_is_reflected_handler_value.
Print Assumptions emitted_determines_reflected_value.
Print Assumptions emitted_tracks_handler_value.
Print Assumptions fold_native_process_fires_handler_value.
