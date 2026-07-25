(*
 * GuardDischargeSoundness: soundness of COMPILE-TIME GUARD DISCHARGE (S-D0).
 *
 * ── What is being modeled ───────────────────────────────────────────────────
 *
 * A Rholang `for(… <- …) where φ { … }` lowers φ into `Receive.condition`, which
 * f1r3node's matcher evaluates at COMM time:
 *
 *     Matcher::check_commit (rholang/…/matcher/match.rs)
 *       | k.guard = None            => true                (the SHORT-CIRCUIT)
 *       | k.guard = Some φ          => guard_passes φ σ
 *     guard_passes φ σ
 *       = match rho_pure_eval::eval_with(φ, env(σ), SpatialMatcherOracle) with
 *         | Ok r => extract_bool r = Some true
 *         | _    => false                                   (the guard-fail COLLAPSE)
 *
 * COMPILE-TIME DISCHARGE is the observation that when φ mentions no variable, the
 * compiler can run THAT SAME FUNCTION on THAT SAME INPUT, and if it answers `true`
 * it may record the answer by simply NOT POPULATING `Receive.condition` — because an
 * absent guard makes `check_commit` answer `true` by short-circuit. No new runtime
 * code, no f1r3node change, and it holds identically on play (`rspace.rs`) and on
 * replay (`replay_rspace.rs`, which reaches `check_commit` through
 * `extract_first_match`).
 *
 * ── The one fact everything rests on ────────────────────────────────────────
 *
 * `rho_pure_eval` reads its environment at EXACTLY ONE place: `resolve_var`, reached
 * only from the `ExprInstance::EVarBody` arm. Every other constructor is
 * env-independent, and the spatial-match oracle's published contract makes
 * `EMatchesBody` env-independent too (`SpatialMatch::matches` is a pure function of
 * `(target, pattern)`). Hence a condition with no `EVar` anywhere evaluates
 * IDENTICALLY under every environment — [T-GD-5], the workhorse induction below.
 *
 * The model reproduces exactly that structure: [CVar] is the sole constructor whose
 * [eval] clause consults [env], and the oracle is a `Variable` of type
 * `Value -> Pattern -> bool` — env-free BY TYPING, so the contract cannot be
 * quietly violated inside this development.
 *
 * ── Main results (all zero-admission) ───────────────────────────────────────
 *
 *   T-GD-1  discharged_guard_would_have_held
 *             a discharged guard evaluates `true` under EVERY environment — the
 *             hypothesis that keeps `RhoGuardedCommSoundness.comm_fires_implies_true_guard`
 *             true after the elision.
 *   T-GD-2  discharge_preserves_the_fired_set
 *             `check_commit` answers identically before and after discharge, at every
 *             environment. THE money theorem: discharge is behaviour-preserving.
 *   T-GD-3  refutation_changes_nothing
 *             a statically-FALSE guard is emitted verbatim; the artifact and the fired
 *             set are untouched. Refutation is a diagnostic, not a transformation.
 *   T-GD-4  discharge_is_one_sided
 *             only a `true` guard is ever elided; a guard that could fail at any
 *             environment is always emitted.
 *   T-GD-5  env_independence_of_closed_conditions
 *             the workhorse induction.
 *   T-GD-6  discharge_is_replay_stable
 *             REPLACES the unprovable `T-R-2 replay_does_not_re-evaluate_guards`
 *             (§18.6) and `T-D-5` (wiring plan §7), both DELETED. Replay *does*
 *             re-evaluate — `replay_rspace.rs:1328` reaches `check_commit` through
 *             `extract_first_match` — and that is fine: after discharge every node
 *             reaches the same verdict `true`, at ZERO evaluation cost, whatever its
 *             local environment. The true obligation is DETERMINISM, and for a
 *             discharged guard determinism is unconditional.
 *   T-GD-7  only_exact_may_discharge
 *             `ExactDecidable` quality + machine routing + a binder-closed, ground
 *             condition are each NECESSARY. Bounded, reject-safe, trusted-native,
 *             machine-checked-model and runtime-observation qualities never discharge.
 *
 * plus the composition `discharged_comm_still_implies_true_guard`, which EXTENDS
 * (does not duplicate) `RhoGuardedCommSoundness.comm_fires_implies_true_guard`.
 *
 * ── Modeling choices, and why they are faithful ─────────────────────────────
 *
 * · Integers are `nat`. Sign plays no role in either the closedness walk or the
 *   env-independence induction; what the model needs is an ordered carrier with
 *   decidable equality, so `nat` is the house-style choice (no `ZArith` in this
 *   project) and loses nothing.
 * · `COpaque` stands for every `ExprInstance` the evaluator refuses
 *   (`EMethodBody`, `EPercentPercentBody`, `EPathmapBody`, `EZipperBody`, …). It
 *   evaluates to `None` and is NOT closed — fail-closed, exactly as the Rust walk's
 *   named-refusal arms are.
 * · `CProcess` stands for a PROCESS embedded in a condition (a send/receive of
 *   literals). `rho_pure_eval` copies process slots through unevaluated, so such a
 *   condition can never extract to a boolean. It is CLOSED (it mentions no variable)
 *   yet not a settled OPERAND — which is precisely why `classify` conjoins
 *   [operands_ground] as an INDEPENDENT requirement instead of inheriting it from
 *   closedness. `closedness_and_groundness_are_independent` exhibits the separation.
 * · The HOST leg of the anti-divergence fence is an arbitrary `option bool` supplied
 *   per call. Nothing is assumed about it — which is the point: soundness must not
 *   depend on the second evaluator being right, only on the two AGREEING.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import RhoGuardedCommSoundness.

Section GuardDischargeSoundness.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* The condition language                                                   *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* A fully evaluated guard operand. `extract_bool` accepts only the boolean
     shape; every other value is "not a verdict". *)
  Inductive Value : Type :=
    | VBool : bool -> Value
    | VInt  : nat -> Value.

  (* Patterns are OPAQUE, and the spatial-match oracle is a `Variable` of type
     `Value -> Pattern -> bool`. Its env-independence — the published
     `rho_pure_eval::SpatialMatch` contract, "same input Par + same Env produce the
     same output Par byte-for-byte on every node" — is thus enforced BY TYPING here:
     there is no environment for the oracle to read. *)
  Variable Pattern : Type.
  Variable oracle : Value -> Pattern -> bool.
  (* Whether a pattern mentions no binder. The pattern side of `is_binder_closed`;
     opaque because the walk over patterns is structurally the same argument and adds
     nothing to the theorem. *)
  Variable pattern_closed : Pattern -> bool.

  Inductive Cond : Type :=
    | CBool    : bool -> Cond
    | CInt     : nat -> Cond
    (* ★ THE ONLY CONSTRUCTOR THAT READS THE ENVIRONMENT (models `EVarBody`). *)
    | CVar     : nat -> Cond
    | CNot     : Cond -> Cond
    | CAnd     : Cond -> Cond -> Cond
    | COr      : Cond -> Cond -> Cond
    | CEq      : Cond -> Cond -> Cond
    | CGt      : Cond -> Cond -> Cond
    (* `EMatchesBody`: the target is evaluated, the pattern is passed verbatim. *)
    | CMatches : Cond -> Pattern -> Cond
    (* A PROCESS embedded in the condition: copied through unevaluated. *)
    | CProcess : Cond -> Cond
    (* Any construct the evaluator refuses. *)
    | COpaque  : Cond.

  Definition Env : Type := nat -> option Value.

  (* The environment the COMPILER has: no bindings at all. *)
  Definition empty_env : Env := fun _ => None.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* The evaluator (models `rho_pure_eval::eval_with`)                        *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  Fixpoint eval (c : Cond) (env : Env) : option Value :=
    match c with
    | CBool b => Some (VBool b)
    | CInt n  => Some (VInt n)
    (* ★ the sole `env` read, mirroring `resolve_var` *)
    | CVar i  => env i
    | CNot p =>
        match eval p env with
        | Some (VBool b) => Some (VBool (negb b))
        | _ => None
        end
    | CAnd a b =>
        match eval a env, eval b env with
        | Some (VBool x), Some (VBool y) => Some (VBool (x && y))
        | _, _ => None
        end
    | COr a b =>
        match eval a env, eval b env with
        | Some (VBool x), Some (VBool y) => Some (VBool (x || y))
        | _, _ => None
        end
    | CEq a b =>
        match eval a env, eval b env with
        | Some (VBool x), Some (VBool y) => Some (VBool (Bool.eqb x y))
        | Some (VInt x), Some (VInt y)   => Some (VBool (Nat.eqb x y))
        (* a HETEROGENEOUS comparison is refused, exactly as `cmp_binop` refuses it *)
        | _, _ => None
        end
    | CGt a b =>
        match eval a env, eval b env with
        | Some (VInt x), Some (VInt y) => Some (VBool (Nat.ltb y x))
        | _, _ => None
        end
    | CMatches t p =>
        match eval t env with
        | Some v => Some (VBool (oracle v p))
        | None => None
        end
    (* A process slot is copied through unevaluated, so it never yields a value the
       boolean extractor accepts. *)
    | CProcess _ => None
    | COpaque => None
    end.

  (* `extract_bool` (private in both `matcher/match.rs` and `reduce.rs`, reproduced
     in `guard_discharge.rs` and pinned there against the real `check_commit`). *)
  Definition verdict (c : Cond) (env : Env) : option bool :=
    match eval c env with
    | Some (VBool b) => Some b
    | _ => None
    end.

  (* `Matcher::check_commit`: the short-circuit on an absent guard, and the collapse
     of false / not-a-boolean / evaluation-error into one "do not commit". *)
  Definition check_commit (g : option Cond) (env : Env) : bool :=
    match g with
    | None => true
    | Some c =>
        match verdict c env with
        | Some true => true
        | _ => false
        end
    end.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* The two structural predicates (`rholang-codegen::guard_closure`)         *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* D0 — "does this condition mention any variable at all?" No wildcard-true arm:
     every constructor is decided explicitly, and the ones with no closedness
     decision answer `false`. *)
  Fixpoint closed (c : Cond) : bool :=
    match c with
    | CBool _ => true
    | CInt _ => true
    | CVar _ => false                                  (* ★ *)
    | CNot p => closed p
    | CAnd a b => closed a && closed b
    | COr a b => closed a && closed b
    | CEq a b => closed a && closed b
    | CGt a b => closed a && closed b
    | CMatches t p => closed t && pattern_closed p
    | CProcess p => closed p     (* a literal-only process mentions no variable *)
    | COpaque => false           (* fail CLOSED *)
    end.

  (* The substrate-routing boundary — "is every operand a value already settled at
     lowering time?" A process is not an operand, however literal its contents. *)
  Fixpoint operands_ground (c : Cond) : bool :=
    match c with
    | CBool _ => true
    | CInt _ => true
    | CVar _ => false
    | CNot p => operands_ground p
    | CAnd a b => operands_ground a && operands_ground b
    | COr a b => operands_ground a && operands_ground b
    | CEq a b => operands_ground a && operands_ground b
    | CGt a b => operands_ground a && operands_ground b
    | CMatches t p => operands_ground t && pattern_closed p
    | CProcess _ => false        (* ★ closed, but NOT a settled operand *)
    | COpaque => false
    end.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-5 — the workhorse induction                                         *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* A binder-closed condition evaluates IDENTICALLY under every environment.
     The induction is uniform: every constructor except [CVar] either ignores [env]
     outright or passes it unchanged to sub-evaluations covered by the induction
     hypotheses, and [CVar] is excluded because [closed (CVar i) = false]. *)
  Theorem env_independence_of_closed_conditions :
    forall c, closed c = true -> forall e1 e2, eval c e1 = eval c e2.
  Proof.
    induction c; intros Hclosed e1 e2; simpl in *.
    - reflexivity.                                        (* CBool *)
    - reflexivity.                                        (* CInt *)
    - discriminate Hclosed.                               (* CVar — excluded by D0 *)
    - rewrite (IHc Hclosed e1 e2). reflexivity.           (* CNot *)
    - apply andb_true_iff in Hclosed. destruct Hclosed as [H1 H2].
      rewrite (IHc1 H1 e1 e2), (IHc2 H2 e1 e2). reflexivity.   (* CAnd *)
    - apply andb_true_iff in Hclosed. destruct Hclosed as [H1 H2].
      rewrite (IHc1 H1 e1 e2), (IHc2 H2 e1 e2). reflexivity.   (* COr *)
    - apply andb_true_iff in Hclosed. destruct Hclosed as [H1 H2].
      rewrite (IHc1 H1 e1 e2), (IHc2 H2 e1 e2). reflexivity.   (* CEq *)
    - apply andb_true_iff in Hclosed. destruct Hclosed as [H1 H2].
      rewrite (IHc1 H1 e1 e2), (IHc2 H2 e1 e2). reflexivity.   (* CGt *)
    - apply andb_true_iff in Hclosed. destruct Hclosed as [H1 _].
      rewrite (IHc H1 e1 e2). reflexivity.                     (* CMatches *)
    - reflexivity.                                        (* CProcess — always None *)
    - reflexivity.                                        (* COpaque — always None *)
  Qed.

  (* The verdict form of T-GD-5, which is what every later theorem consumes. *)
  Corollary verdict_independent_of_env :
    forall c, closed c = true -> forall e1 e2, verdict c e1 = verdict c e2.
  Proof.
    intros c Hclosed e1 e2. unfold verdict.
    rewrite (env_independence_of_closed_conditions c Hclosed e1 e2). reflexivity.
  Qed.

  (* Closedness and groundness are genuinely INDEPENDENT questions, which is why
     `classify` conjoins them instead of deriving one from the other: a literal-only
     process mentions no variable yet is not a settled operand. *)
  Lemma closedness_and_groundness_are_independent :
    exists c, closed c = true /\ operands_ground c = false.
  Proof.
    exists (CProcess (CBool true)). simpl. split; reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* Quality, routing, and the classifier                                     *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* The documented 7-value guard-quality vocabulary (`guard_quality.rs`). *)
  Inductive Quality : Type :=
    | ExactDecidable
    | BoundedDecidable
    | RejectSafeApprox
    | TrustedNativeGuard
    | MachineCheckedModel
    | RuntimeObservation
    | UnknownQuality.

  (* Only EXACT decidability may license a compile-time decision.
     · Bounded (T3) — discharge would delete the artifact point carrying the
       recorded bound, so the bound would stop being consensus-visible.
     · Reject-safe — reject-safety licenses RETAINING a guard, never DISCHARGING
       one; and a three-valued `DontKnow` has no `true` to discharge on.
     · Machine-checked-model — discharging on a proof would make the proof
       RUNTIME-LOAD-BEARING, which is exactly what proof attribution must not become.
     · Trusted-native / runtime-observation — the deciding authority is not this
       evaluator, so folding here would be deciding someone else's question.
     · Unknown — fail-closed. *)
  Definition may_discharge (q : Quality) : bool :=
    match q with
    | ExactDecidable => true
    | BoundedDecidable => false
    | RejectSafeApprox => false
    | TrustedNativeGuard => false
    | MachineCheckedModel => false
    | RuntimeObservation => false
    | UnknownQuality => false
    end.

  (* ★ THE ROUTE-SITE INVARIANT. The route is an INPUT to the classifier, never
     derived inside it: one routing decision per guard, computed once at lowering,
     consulted by every decider. *)
  Inductive Routing : Type :=
    | MachineEvaluated                                (* rides as `Receive.condition` *)
    | OtherSubstrate.                                 (* a Dovetail fold / EBA / SFT / native *)

  Definition permits_compile_time_decision (r : Routing) : bool :=
    match r with
    | MachineEvaluated => true
    | OtherSubstrate => false
    end.

  Inductive Discharge : Type := Discharged | Refuted | Residual.

  (* `guard_discharge::classify`, including the ANTI-DIVERGENCE FENCE: the machine
     leg (`verdict … empty_env`) is the authority, and the host leg must AGREE. *)
  Definition classify (q : Quality) (r : Routing) (host : option bool) (c : Cond)
    : Discharge :=
    if may_discharge q then
      if permits_compile_time_decision r then
        if closed c then
          if operands_ground c then
            match verdict c empty_env, host with
            | Some true, Some true => Discharged
            | Some false, Some false => Refuted
            | _, _ => Residual
            end
          else Residual
        else Residual
      else Residual
    else Residual.

  (* The emitted guard. `None` IS the discharge — `check_commit` short-circuits it. *)
  Definition lower (q : Quality) (r : Routing) (host : option bool) (c : Cond)
    : option Cond :=
    match classify q r host c with
    | Discharged => None
    | Refuted => Some c
    | Residual => Some c
    end.

  (* Inverting `classify`: a `Discharged` verdict forces every conjunct. Used by
     T-GD-1, T-GD-4 and T-GD-7, so the case analysis is done ONCE. *)
  Lemma discharged_inversion : forall q r host c,
    classify q r host c = Discharged ->
    q = ExactDecidable
    /\ r = MachineEvaluated
    /\ closed c = true
    /\ operands_ground c = true
    /\ verdict c empty_env = Some true
    /\ host = Some true.
  Proof.
    intros q r host c H. unfold classify in H.
    destruct q; simpl in H; try discriminate H.
    destruct r; simpl in H; try discriminate H.
    destruct (closed c) eqn:Hclosed; [| discriminate H].
    destruct (operands_ground c) eqn:Hground; [| discriminate H].
    destruct (verdict c empty_env) as [[|]|] eqn:Hverdict;
      destruct host as [[|]|]; try discriminate H;
      repeat split; reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-1 — a discharged guard would have held                              *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* The elided check would have SUCCEEDED — at every environment, not merely at the
     empty one the compiler used. This is the hypothesis that keeps
     `RhoGuardedCommSoundness.comm_fires_implies_true_guard` true after the elision:
     the fired COMM still satisfies its guard, the guard is simply not re-checked. *)
  Theorem discharged_guard_would_have_held : forall q r host c,
    classify q r host c = Discharged ->
    forall env, verdict c env = Some true.
  Proof.
    intros q r host c H env.
    apply discharged_inversion in H.
    destruct H as [_ [_ [Hclosed [_ [Hverdict _]]]]].
    rewrite (verdict_independent_of_env c Hclosed env empty_env). exact Hverdict.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-2 — discharge preserves the fired set                               *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* THE money theorem. At EVERY environment, `check_commit` answers identically on
     the discharged artifact and on the original one: discharge changes no COMM's
     fate. Both directions of the elision are covered — when the guard is elided the
     short-circuit returns `true` and T-GD-1 says the check would have returned
     `true` too; when it is not elided the artifact is literally unchanged. *)
  Theorem discharge_preserves_the_fired_set : forall q r host c env,
    check_commit (lower q r host c) env = check_commit (Some c) env.
  Proof.
    intros q r host c env. unfold lower.
    destruct (classify q r host c) eqn:Hclass.
    - (* Discharged: the short-circuit answers `true`, and so would the check. *)
      simpl.
      rewrite (discharged_guard_would_have_held q r host c Hclass env).
      reflexivity.
    - reflexivity.                                        (* Refuted: unchanged *)
    - reflexivity.                                        (* Residual: unchanged *)
  Qed.

  (* The same statement read as a bisimulation on the COMMIT decision: the two
     artifacts are indistinguishable to every observer of firing. *)
  Corollary discharge_is_unobservable : forall q r host c,
    (forall env, check_commit (lower q r host c) env = check_commit (Some c) env).
  Proof.
    intros q r host c env. apply discharge_preserves_the_fired_set.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-3 — refutation changes nothing                                      *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* A guard decided statically FALSE is emitted VERBATIM. The receive stays in the
     artifact — it is a resting, observable continuation: it appears in the normal
     form, in the state hash, and in tuplespace storage, and the datum it would have
     consumed stays put. Refutation is therefore a DIAGNOSTIC (`W1
     GuardStaticallyFalse`), never a transformation. *)
  Theorem refutation_changes_nothing : forall q r host c,
    classify q r host c = Refuted -> lower q r host c = Some c.
  Proof.
    intros q r host c H. unfold lower. rewrite H. reflexivity.
  Qed.

  (* …and therefore no COMM's fate changes either — the artifact IS the behaviour. *)
  Corollary refutation_preserves_every_verdict : forall q r host c,
    classify q r host c = Refuted ->
    forall env, check_commit (lower q r host c) env = check_commit (Some c) env.
  Proof.
    intros q r host c H env. rewrite (refutation_changes_nothing q r host c H).
    reflexivity.
  Qed.

  (* A refuted guard genuinely never fires — the receive rests forever. This is the
     observable the corpus tests assert, and the reason folding it away would be
     unsound: the resting receive and its unconsumed datum are part of the state. *)
  Theorem a_refuted_guard_never_commits : forall q r host c,
    classify q r host c = Refuted -> check_commit (lower q r host c) empty_env = false.
  Proof.
    intros q r host c H.
    assert (Hv : verdict c empty_env = Some false).
    { unfold classify in H.
      destruct q; simpl in H; try discriminate H.
      destruct r; simpl in H; try discriminate H.
      destruct (closed c); [| discriminate H].
      destruct (operands_ground c); [| discriminate H].
      destruct (verdict c empty_env) as [[|]|] eqn:Hverdict;
        destruct host as [[|]|]; try discriminate H; reflexivity. }
    rewrite (refutation_changes_nothing q r host c H). simpl. rewrite Hv. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-4 — discharge is one-sided                                          *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* Elision happens ONLY for a guard that holds. There is no environment at which a
     discharged guard could have failed. *)
  Theorem discharge_is_one_sided : forall q r host c,
    lower q r host c = None -> forall env, verdict c env = Some true.
  Proof.
    intros q r host c H env. unfold lower in H.
    destruct (classify q r host c) eqn:Hclass; try discriminate H.
    exact (discharged_guard_would_have_held q r host c Hclass env).
  Qed.

  (* The contrapositive, which is the form a reviewer wants: if the guard could fail
     ANYWHERE, it is emitted. (Closedness is required because for an OPEN guard the
     empty-environment verdict says nothing about the runtime one — which is exactly
     why D0 is the sound class.) *)
  Theorem a_guard_that_can_fail_is_never_elided : forall q r host c env,
    closed c = true ->
    verdict c env <> Some true ->
    lower q r host c = Some c.
  Proof.
    intros q r host c env Hclosed Hfail. unfold lower.
    destruct (classify q r host c) eqn:Hclass; [| reflexivity | reflexivity].
    exfalso. apply Hfail.
    exact (discharged_guard_would_have_held q r host c Hclass env).
  Qed.

  (* An OPEN guard is never elided at all, whatever it evaluates to. D0's fence
     stated positively. *)
  Theorem an_open_guard_is_never_discharged : forall q r host c,
    closed c = false -> lower q r host c = Some c.
  Proof.
    intros q r host c Hopen. unfold lower.
    destruct (classify q r host c) eqn:Hclass; [| reflexivity | reflexivity].
    apply discharged_inversion in Hclass.
    destruct Hclass as [_ [_ [Hclosed _]]]. rewrite Hopen in Hclosed. discriminate.
  Qed.

  (* ★ THE ANTI-DIVERGENCE FENCE. If the two evaluators disagree, nothing is
     discharged. Soundness does not depend on the host leg being RIGHT — only on the
     two AGREEING — so a divergence surfaces as a refusal (and, in the
     implementation, a `WARN`), never as an unsound elision. *)
  Theorem evaluator_disagreement_never_discharges : forall q r c m h,
    verdict c empty_env = Some m ->
    h <> m ->
    classify q r (Some h) c <> Discharged.
  Proof.
    intros q r c m h Hmachine Hdiffer Hclass.
    apply discharged_inversion in Hclass.
    destruct Hclass as [_ [_ [_ [_ [Hverdict Hhost]]]]].
    rewrite Hmachine in Hverdict. injection Hverdict as Hm.
    injection Hhost as Hh. apply Hdiffer. rewrite Hh, Hm. reflexivity.
  Qed.

  (* A host leg that DECLINED can never license discharge either. *)
  Theorem a_declining_host_leg_never_discharges : forall q r c,
    classify q r None c <> Discharged.
  Proof.
    intros q r c Hclass. apply discharged_inversion in Hclass.
    destruct Hclass as [_ [_ [_ [_ [_ Hhost]]]]]. discriminate Hhost.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-6 — discharge is replay-stable                                      *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* The cost a node pays to decide a guard: the size of the expression it must
     evaluate, and ZERO when there is no guard to evaluate. *)
  Fixpoint eval_cost (c : Cond) : nat :=
    match c with
    | CBool _ => 1
    | CInt _ => 1
    | CVar _ => 1
    | CNot p => S (eval_cost p)
    | CAnd a b => S (eval_cost a + eval_cost b)
    | COr a b => S (eval_cost a + eval_cost b)
    | CEq a b => S (eval_cost a + eval_cost b)
    | CGt a b => S (eval_cost a + eval_cost b)
    | CMatches t _ => S (eval_cost t)
    | CProcess p => S (eval_cost p)
    | COpaque => 1
    end.

  Definition guard_cost (g : option Cond) : nat :=
    match g with
    | None => 0
    | Some c => eval_cost c
    end.

  (* ★ REPLACES the DELETED `T-R-2 replay_does_not_re-evaluate_guards` (§18.6) and
     `T-D-5` (wiring plan §7). Both were UNPROVABLE AS STATED: replay DOES
     re-evaluate guards — `replay_rspace.rs:1328` reaches `check_commit` through
     `extract_first_match` — so "replay does not re-evaluate" is simply false.
     The true obligation is DETERMINISM, and for a discharged guard it is
     unconditional and free:
       (i)   every node reaches the SAME verdict, whatever its local environment;
       (ii)  that verdict is `true`;
       (iii) it costs ZERO evaluation steps (the `check_commit` short-circuit) —
             the O(1) claim, in a checkable form.
     Nothing here assumes two nodes share an environment; the result holds even if
     they did not. *)
  Theorem discharge_is_replay_stable : forall q r host c,
    classify q r host c = Discharged ->
    (forall env1 env2,
        check_commit (lower q r host c) env1 = check_commit (lower q r host c) env2)
    /\ (forall env, check_commit (lower q r host c) env = true)
    /\ guard_cost (lower q r host c) = 0.
  Proof.
    intros q r host c Hclass.
    assert (Hnone : lower q r host c = None).
    { unfold lower. rewrite Hclass. reflexivity. }
    rewrite Hnone. simpl. repeat split; reflexivity.
  Qed.

  (* The companion fact for the guards that are NOT discharged: replay re-evaluates
     them, and determinism there is LOAD-BEARING rather than inherited. For a
     binder-closed residual guard (one the fence refused, e.g. because the host leg
     declined) determinism still holds unconditionally, by T-GD-5. *)
  Theorem a_closed_residual_guard_is_still_deterministic : forall q r host c,
    closed c = true ->
    classify q r host c <> Discharged ->
    lower q r host c = Some c
    /\ forall env1 env2, check_commit (Some c) env1 = check_commit (Some c) env2.
  Proof.
    intros q r host c Hclosed Hnot. split.
    - unfold lower. destruct (classify q r host c); [contradiction | reflexivity | reflexivity].
    - intros env1 env2. simpl.
      rewrite (verdict_independent_of_env c Hclosed env1 env2). reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* T-GD-7 — only exact may discharge                                        *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* Every conjunct of the licence is NECESSARY: the quality must be
     `ExactDecidable`, the route must be the machine's own guard evaluator, and the
     condition must be both binder-closed and made of ground operands. *)
  Theorem only_exact_may_discharge : forall q r host c,
    classify q r host c = Discharged ->
    q = ExactDecidable
    /\ r = MachineEvaluated
    /\ closed c = true
    /\ operands_ground c = true.
  Proof.
    intros q r host c H. apply discharged_inversion in H.
    destruct H as [Hq [Hr [Hclosed [Hground _]]]].
    repeat split; assumption.
  Qed.

  (* The six refused qualities, enumerated rather than left implicit — each with the
     reason recorded at [may_discharge]. *)
  Theorem no_other_quality_ever_discharges : forall q r host c,
    q <> ExactDecidable -> classify q r host c = Residual.
  Proof.
    intros q r host c Hq. unfold classify.
    destruct q; simpl; try reflexivity. exfalso. apply Hq. reflexivity.
  Qed.

  (* A guard routed to another substrate is never decided here, even when it is a
     closed constant this evaluator could trivially fold. Folding it would BE the
     route-site violation: this module deciding a routing question it does not own. *)
  Theorem a_substrate_routed_guard_is_never_discharged : forall q host c,
    classify q OtherSubstrate host c = Residual.
  Proof.
    intros q host c. unfold classify. destruct q; simpl; reflexivity.
  Qed.

  (* A guard whose operands are not settled at lowering time is never folded, even
     when it mentions no variable — the substrate boundary, CHECKED rather than
     inherited from D0's definition. *)
  Theorem an_unsettled_operand_is_never_folded : forall q r host c,
    operands_ground c = false -> classify q r host c = Residual.
  Proof.
    intros q r host c Hground. unfold classify.
    destruct q; simpl; try reflexivity.
    destruct r; simpl; try reflexivity.
    destruct (closed c); [| reflexivity].
    rewrite Hground. reflexivity.
  Qed.

End GuardDischargeSoundness.

(* ══════════════════════════════════════════════════════════════════════════ *)
(* Composition with M7 (`RhoGuardedCommSoundness`) — EXTEND, do not duplicate  *)
(* ══════════════════════════════════════════════════════════════════════════ *)

Section DischargeComposedWithM7.

  (* The M7 setting, verbatim. *)
  Variable Subst : Type.
  Variable name_match structural_eval behavioral_eval behavioral_true : Subst -> bool.
  Hypothesis behavioral_sound :
    forall s, behavioral_eval s = true -> behavioral_true s = true.

  (* The discharge setting. *)
  Variable Pattern : Type.
  Variable oracle : Value -> Pattern -> bool.
  Variable pattern_closed : Pattern -> bool.

  (* How a matched substitution presents itself to the guard evaluator. *)
  Variable env_of : Subst -> Env.

  (* ★ THE COMPOSITION. `RhoGuardedCommSoundness.comm_fires_implies_true_guard` says
     a fired guarded COMM satisfies the TRUE guard. Eliding a discharged `where`
     clause does not weaken that conclusion, because T-GD-1 supplies exactly the
     missing premise: the elided check would have SUCCEEDED at this very
     substitution. So after discharge the fired COMM still satisfies both the M7
     product guard and the elided `where` guard — the latter now as a THEOREM about
     the artifact rather than as a runtime check.

     M7's theorem is INSTANTIATED here, never re-proved. *)
  Theorem discharged_comm_still_implies_true_guard :
    forall (q : Quality) (r : Routing) (host : option bool)
           (c : Cond Pattern) (s : Subst),
      classify Pattern oracle pattern_closed q r host c = Discharged ->
      RhoGuardedCommSoundness.comm_fires Subst name_match structural_eval
        behavioral_eval s = true ->
      name_match s = true
      /\ RhoGuardedCommSoundness.product_true Subst structural_eval behavioral_true s
         = true
      /\ verdict Pattern oracle c (env_of s) = Some true
      /\ check_commit Pattern oracle
           (lower Pattern oracle pattern_closed q r host c) (env_of s) = true.
  Proof.
    intros q r host c s Hdischarged Hfires.
    (* M7, instantiated — not rederived. *)
    destruct (RhoGuardedCommSoundness.comm_fires_implies_true_guard
                Subst name_match structural_eval behavioral_eval behavioral_true
                behavioral_sound s Hfires) as [Hname Hproduct].
    (* T-GD-1: the elided check would have held at THIS substitution's environment. *)
    assert (Hheld : verdict Pattern oracle c (env_of s) = Some true).
    { exact (discharged_guard_would_have_held Pattern oracle pattern_closed
               q r host c Hdischarged (env_of s)). }
    repeat split; try assumption.
    (* …and the emitted (guard-free) artifact commits, by the short-circuit. *)
    assert (Hnone : lower Pattern oracle pattern_closed q r host c = None).
    { unfold lower. rewrite Hdischarged. reflexivity. }
    rewrite Hnone. reflexivity.
  Qed.

End DischargeComposedWithM7.

(* ── Zero-admission audit (house style: one per theorem) ─────────────────── *)

Print Assumptions env_independence_of_closed_conditions.
Print Assumptions verdict_independent_of_env.
Print Assumptions closedness_and_groundness_are_independent.
Print Assumptions discharged_inversion.
Print Assumptions discharged_guard_would_have_held.
Print Assumptions discharge_preserves_the_fired_set.
Print Assumptions discharge_is_unobservable.
Print Assumptions refutation_changes_nothing.
Print Assumptions refutation_preserves_every_verdict.
Print Assumptions a_refuted_guard_never_commits.
Print Assumptions discharge_is_one_sided.
Print Assumptions a_guard_that_can_fail_is_never_elided.
Print Assumptions an_open_guard_is_never_discharged.
Print Assumptions evaluator_disagreement_never_discharges.
Print Assumptions a_declining_host_leg_never_discharges.
Print Assumptions discharge_is_replay_stable.
Print Assumptions a_closed_residual_guard_is_still_deterministic.
Print Assumptions only_exact_may_discharge.
Print Assumptions no_other_quality_ever_discharges.
Print Assumptions a_substrate_routed_guard_is_never_discharged.
Print Assumptions an_unsettled_operand_is_never_folded.
Print Assumptions discharged_comm_still_implies_true_guard.
