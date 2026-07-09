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

  (* ---------------------------------------------------------------------------
     (3) IN-RHO DISPATCH + LOCATION↔VALUE SEPARATION (Stage 4 S-native, commit
     445bf013).

     Stage 4 moved the native DISPATCH — LOCATE `NativeProc(a0..a_{k-1})` by its head
     tag + arity and CAPTURE the structural args — INTO Rho: the reflected subject is
     spread and the positional set-automaton LOCATES the App-rooted native node
     (AdvancedAutomata `InRhoMatchPositional.locate_all_dispatched` /
     `whole_term_located`) and captures its structural args, RETIRING the host-σ
     location. The native VALUE stays the trusted handler's payload: it is
     [reflect handler_value] on the AUTOMATON-captured args, and is INDEPENDENT of
     where — or of any REPORT field claiming where — the redex was located.

     We model the two directions of the SEPARATION the corrupted-σ probe
     `s_native_location_is_produced_by_the_automaton_not_the_report`
     (`rholang-runtime/tests/rho_net_native_firing.rs`) exercises:

       (a) a corrupted REPORT LOCATION cannot change the emitted VALUE — the payload
           reads the handler value, never the report's location field
           ([corrupt_location_preserves_value]); and, contrastively, a design that DID
           read the location from the (corruptible) report WOULD be perturbable
           ([buggy_report_location_is_corruptible]);
       (b) the native VALUE cannot perturb the located POSITION — the true location is
           the AUTOMATON's, computed from the subject alone, never from the report
           ([location_from_automaton_not_report]).

     [native_dispatch_separation] packages both as the formal analogue of the probe.
     --------------------------------------------------------------------------- *)

  (* The located position of the redex (a Dewey / StateId address). Historically the
     host-σ carried it; the corrupted-σ probe overwrites it with garbage. Abstract —
     the separation holds for ANY location representation (a Section Variable,
     discharged when the section closes; no Axiom). *)
  Variable Loc : Type.

  (* The reflected subject the in-Rho automaton scans. The automaton LOCATES the
     App-rooted `NativeProc` node in it ([automaton_locate]) and CAPTURES its
     structural args, from which the trusted handler computes the native value
     ([handler_of]) — BOTH functions of the SUBJECT, never of any report field. *)
  Variable Subject          : Type.
  Variable automaton_locate : Subject -> Loc.  (* where the automaton locates the redex *)
  Variable handler_of       : Subject -> Val.  (* the trusted handler value on the captured args *)

  (* A firing REPORT: it carries a LOCATION field (the redex position — historically
     the host-σ, now automaton-produced) and the handler VALUE payload. The
     corrupted-σ probe overwrites the location field with an arbitrary value. *)
  Record Report : Type := { rep_loc : Loc ; rep_value : Val }.

  (* The emitted COMM payload reads the report's VALUE field and reflects it — the
     one-slot dispatch receiver forwards exactly the injected reflected value
     ([receiver_emit (inject (rep_value r))]). It never reads the location field. *)
  Definition report_emit (r : Report) : option Val := receiver_emit (inject (rep_value r)).

  (* The TRUE located position is the AUTOMATON's, computed from the subject — NOT the
     report's (corruptible) location field. This is the claim the probe name asserts:
     the location is "produced by the automaton, not the report". *)
  Definition true_location (s : Subject) (r : Report) : Loc := automaton_locate s.

  (* The BUGGY alternative the probe rules out: reading the located position from the
     REPORT's location field. *)
  Definition report_location (r : Report) : Loc := rep_loc r.

  (* The emitted payload is EXACTLY the reflection of the report's VALUE field — a
     function of the value field ALONE (never the location). *)
  Theorem report_emit_is_reflected_value : forall r,
    report_emit r = Some (reflect (rep_value r)).
  Proof. intro r. unfold report_emit. apply emitted_is_reflected_handler_value. Qed.

  (* SEPARATION (a): a corrupted report LOCATION cannot change the emitted VALUE — the
     payload is [reflect (rep_value r)], independent of the location field. Overwriting
     the location with garbage leaves the payload byte-identical. The formal analogue
     of the corrupted-σ probe's VALUE invariance. *)
  Theorem corrupt_location_preserves_value : forall loc1 loc2 v,
    report_emit {| rep_loc := loc1 ; rep_value := v |}
    = report_emit {| rep_loc := loc2 ; rep_value := v |}.
  Proof. intros loc1 loc2 v. rewrite !report_emit_is_reflected_value. reflexivity. Qed.

  (* CONTRAST (reachability of the bug): a design that read the located position from
     the REPORT's location field IS corruptible — distinct (corrupted) location fields
     give distinct positions. This is exactly the failure the automaton-produced
     [true_location] avoids; it makes [location_from_automaton_not_report] non-vacuous.
     (The corruptible-report dual of InRhoMatchPositional's
     `buggy_head_tag_wrong_for_nonnullary`.) *)
  Theorem buggy_report_location_is_corruptible : forall loc1 loc2 v,
    loc1 <> loc2 ->
    report_location {| rep_loc := loc1 ; rep_value := v |}
    <> report_location {| rep_loc := loc2 ; rep_value := v |}.
  Proof. intros loc1 loc2 v Hne. unfold report_location. cbn. exact Hne. Qed.

  (* SEPARATION (b): the native VALUE cannot perturb the located POSITION — the true
     location is [automaton_locate s], a function of the SUBJECT alone. Two reports
     with ANY (differing) value or location fields yield the SAME true location. The
     dual direction of (a): value ⇏ location, as (corrupted) location ⇏ value. *)
  Theorem location_from_automaton_not_report : forall s r1 r2,
    true_location s r1 = true_location s r2.
  Proof. intros s r1 r2. unfold true_location. reflexivity. Qed.

  (* In an HONEST firing the report's value field IS the trusted handler's value on the
     automaton-captured args ([rep_value r = handler_of s]); then the emitted payload is
     [reflect (handler_of s)] — computed from the SUBJECT's captured args, wholly
     independent of the report's location field. *)
  Theorem emitted_is_handler_on_captured_args : forall s r,
    rep_value r = handler_of s ->
    report_emit r = Some (reflect (handler_of s)).
  Proof.
    intros s r Hval. rewrite report_emit_is_reflected_value, Hval. reflexivity.
  Qed.

  (* MAIN (the corrupted-σ probe, formal analogue): take an HONEST report and a
     LOCATION-CORRUPTED report carrying the SAME handler value [v]. BOTH (i) the true
     located position (the automaton's) and (ii) the emitted value (the handler's) are
     UNCHANGED by the corruption — the location↔value separation is sound. *)
  Theorem native_dispatch_separation : forall s loc_true loc_corrupt v,
    true_location s {| rep_loc := loc_true ; rep_value := v |}
      = true_location s {| rep_loc := loc_corrupt ; rep_value := v |}
    /\ report_emit {| rep_loc := loc_true ; rep_value := v |}
      = report_emit {| rep_loc := loc_corrupt ; rep_value := v |}.
  Proof.
    intros s loc_true loc_corrupt v. split.
    - apply location_from_automaton_not_report.
    - apply corrupt_location_preserves_value.
  Qed.

End NativeSystemProcessBoundary.

Print Assumptions lower_total.
Print Assumptions lower_materialized_iff_fold_and_channel.
Print Assumptions lower_rejected_has_precise_reason.
Print Assumptions emitted_is_reflected_handler_value.
Print Assumptions emitted_determines_reflected_value.
Print Assumptions emitted_tracks_handler_value.
Print Assumptions fold_native_process_fires_handler_value.

(* ---- Stage 4 S-native (in-Rho dispatch + location↔value separation) ---- *)
Print Assumptions report_emit_is_reflected_value.
Print Assumptions corrupt_location_preserves_value.
Print Assumptions buggy_report_location_is_corruptible.
Print Assumptions location_from_automaton_not_report.
Print Assumptions emitted_is_handler_on_captured_args.
Print Assumptions native_dispatch_separation.
