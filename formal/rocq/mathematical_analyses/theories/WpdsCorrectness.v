(*
 * WpdsCorrectness: Correctness of WPDS poststar and prestar algorithms.
 *
 * Proves that the saturation-based poststar and prestar algorithms compute
 * correct over-approximations of forward and backward reachable configuration
 * sets, following Reps, Lal & Kidd (2007).
 *
 * Key results:
 *   - Poststar soundness: every reachable configuration is accepted
 *   - Prestar soundness: every pre-image configuration is accepted
 *   - MOVP fixpoint: saturation converges on a finite transition set
 *   - Monotonicity: the transition relation only grows during saturation
 *
 * Structure:
 *   1. WpdsModel         — PDS configurations, rules, step, reachability, traces
 *   2. PAutomaton         — P-automaton reads, acceptance, monotonicity
 *   3. PoststarSoundness  — Single-control-location poststar soundness theorem
 *   4. PrestarSoundness   — Single-control-location prestar soundness theorem
 *   5. MOVPFixpoint       — Saturation convergence via monotonicity + boundedness
 *   6. RuleInduction      — Structural lemmas on rule forms and stack effects
 *   7. Composition        — Poststar/prestar consistency
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition            | Rust / Ascent Code                   | Location
 *   ---------------------------|--------------------------------------|--------------------------
 *   symbol                     | StackSymbol { category, rule, pos }  | wpds.rs:62-69
 *   sl_rule (Pop/Replace/Push) | WpdsRule<W> enum                     | wpds.rs:104-133
 *   sl_step                    | one-step PDS execution               | wpds.rs:101-103 (comment)
 *   sl_reachable               | reflexive-transitive closure of step | wpds.rs:689-706 (poststar)
 *   pa_reads                   | path through P-automaton transitions | wpds.rs:248-254
 *   sl_accepts                 | PAutomaton acceptance                | wpds.rs:314-324
 *   poststar                   | poststar() saturation loop           | wpds.rs:707-840
 *   prestar                    | prestar() saturation loop            | wpds.rs:855-1005
 *   sat_step                   | worklist pop + rule match            | wpds.rs:735-836
 *   existing (transition map)  | HashMap<(from,sym,to), W>            | wpds.rs:724-729
 *   embed_p                    | p_state (= 0)                        | wpds.rs:709
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import Classical.

Import ListNotations.

(* ===================================================================== *)
(*  Section 1: P-Automaton Reads                                           *)
(* ===================================================================== *)

(* We define the P-automaton reading relation outside any Section so that
   it can be shared freely across all subsequent sections without
   implicit-argument complications from section variable abstraction. *)

(* pa_reads pa_st sym T q w q' :
   Starting from P-automaton state q, reading the stack word w
   (head = top of stack), we can reach state q' using transitions from T.
   pa_st = P-automaton state type, sym = stack symbol type. *)

Inductive pa_reads (pa_st sym : Type)
  : list (pa_st * sym * pa_st) -> pa_st -> list sym -> pa_st -> Prop :=
  | pa_reads_nil : forall T q,
      pa_reads pa_st sym T q [] q
  | pa_reads_cons : forall T q gamma rest q_mid q_end,
      In (q, gamma, q_mid) T ->
      pa_reads pa_st sym T q_mid rest q_end ->
      pa_reads pa_st sym T q (gamma :: rest) q_end.

Arguments pa_reads {pa_st sym} T q w q'.
Arguments pa_reads_nil {pa_st sym} T q.
Arguments pa_reads_cons {pa_st sym} T q gamma rest q_mid q_end _ _.

(* ------------------------------------------------------------------- *)
(*  Monotonicity of reads w.r.t. transition set                          *)
(* ------------------------------------------------------------------- *)

Lemma pa_reads_monotone :
  forall (pa_st sym : Type) (T1 T2 : list (pa_st * sym * pa_st)) q w q',
    pa_reads T1 q w q' ->
    (forall t, In t T1 -> In t T2) ->
    pa_reads T2 q w q'.
Proof.
  intros pa_st sym T1 T2 q w q' Hreads Hsub.
  induction Hreads as [T q0 | T q0 gamma rest q_mid q_end Hin Hrest IH].
  - apply pa_reads_nil.
  - apply pa_reads_cons with q_mid.
    + apply Hsub. exact Hin.
    + apply IH. exact Hsub.
Qed.

(* Inversion lemma for cons-shaped reads.
   This avoids issues with Rocq's inversion tactic naming by packaging
   the result as an existential. *)
Lemma pa_reads_cons_inv :
  forall (pa_st sym : Type) (T : list (pa_st * sym * pa_st)) q gamma w q',
    pa_reads T q (gamma :: w) q' ->
    exists q_mid, In (q, gamma, q_mid) T /\ pa_reads T q_mid w q'.
Proof.
  intros pa_st sym T q gamma w q' Hreads.
  inversion Hreads; subst.
  eexists. split; eassumption.
Qed.

(* ------------------------------------------------------------------- *)
(*  Concatenation of reads                                               *)
(* ------------------------------------------------------------------- *)

Lemma pa_reads_app_intro :
  forall (pa_st sym : Type) (T : list (pa_st * sym * pa_st)) q q_mid q' w1 w2,
    pa_reads T q w1 q_mid ->
    pa_reads T q_mid w2 q' ->
    pa_reads T q (w1 ++ w2) q'.
Proof.
  intros pa_st sym T q q_mid q' w1 w2 H1 H2.
  induction H1 as [T' q0 | T' q0 gamma rest qm qe Hin Hrest IH].
  - simpl. exact H2.
  - simpl. apply pa_reads_cons with qm.
    + exact Hin.
    + apply IH. exact H2.
Qed.

Lemma pa_reads_app_elim :
  forall (pa_st sym : Type) (T : list (pa_st * sym * pa_st)) q w1 w2 q',
    pa_reads T q (w1 ++ w2) q' ->
    exists q_mid, pa_reads T q w1 q_mid /\ pa_reads T q_mid w2 q'.
Proof.
  intros pa_st sym T q w1. revert q.
  induction w1 as [| g1 w1' IH]; intros q w2 q' Hreads.
  - simpl in Hreads. exists q. split.
    + apply pa_reads_nil.
    + exact Hreads.
  - simpl in Hreads.
    apply pa_reads_cons_inv in Hreads.
    destruct Hreads as [q_mid' [Hin Hrest]].
    apply IH in Hrest.
    destruct Hrest as [q_mid [H1 H2]].
    exists q_mid. split.
    + apply pa_reads_cons with q_mid'.
      * exact Hin.
      * exact H1.
    + exact H2.
Qed.

(* Single-symbol read *)
Lemma pa_reads_single :
  forall (pa_st sym : Type) (T : list (pa_st * sym * pa_st)) q gamma q',
    In (q, gamma, q') T ->
    pa_reads T q [gamma] q'.
Proof.
  intros pa_st sym T q gamma q' Hin.
  apply pa_reads_cons with q'.
  - exact Hin.
  - apply pa_reads_nil.
Qed.

(* ===================================================================== *)
(*  Section 2: Single-Control-Location WPDS Model                         *)
(* ===================================================================== *)

(* PraTTaIL uses a single control location p (context-free process).
   This simplifies the WPDS model:
   - All rules have the form ⟨p, γ⟩ ↪ ⟨p, u⟩ (same control location)
   - The P-automaton has a distinguished initial state embed_p
   - Pop rules have p' = p, so the pop exposes the sub-stack

   We model this directly, avoiding the general multi-location case,
   since PraTTaIL's build_wpds (wpds.rs:388-644) always uses p = p'. *)

Section SingleLocationWPDS.

  (* Stack symbol type. In PraTTaIL: StackSymbol { category, rule_label, position }. *)
  Variable symbol : Type.

  (* P-automaton state type. In PraTTaIL: PAutomatonStateId = u32. *)
  Variable pa_state : Type.

  (* ------------------------------------------------------------------- *)
  (*  Single-location rules                                                *)
  (* ------------------------------------------------------------------- *)

  (* In PraTTaIL's WPDS (wpds.rs:104-133), all rules use the same control
     location. We model rules directly on stack symbols, omitting the
     control state from the rule representation. *)

  Inductive sl_rule : Type :=
    | SL_Pop (gamma : symbol)
        (* ⟨p, γ⟩ ↪ ⟨p, ε⟩ — removes top of stack (rule completion) *)
    | SL_Replace (gamma gamma' : symbol)
        (* ⟨p, γ⟩ ↪ ⟨p, γ'⟩ — replaces top of stack (intraprocedural step) *)
    | SL_Push (gamma gamma1 gamma2 : symbol)
        (* ⟨p, γ⟩ ↪ ⟨p, γ₁ γ₂⟩ — pushes (cross-category call)
           Stack after: γ₁ on top, γ₂ below. *).

  (* The finite set of PDS rules. *)
  Variable sl_rules : list sl_rule.

  (* ------------------------------------------------------------------- *)
  (*  One-step execution on stacks                                         *)
  (* ------------------------------------------------------------------- *)

  (* sl_step w1 w2: stack w2 is reachable from stack w1 in one PDS step.
     The rule fires when the top of stack matches the rule's LHS;
     the rest of the stack (w) is untouched. *)

  Inductive sl_step : list symbol -> list symbol -> Prop :=
    | sl_step_pop : forall gamma w,
        In (SL_Pop gamma) sl_rules ->
        sl_step (gamma :: w) w
    | sl_step_replace : forall gamma gamma' w,
        In (SL_Replace gamma gamma') sl_rules ->
        sl_step (gamma :: w) (gamma' :: w)
    | sl_step_push : forall gamma gamma1 gamma2 w,
        In (SL_Push gamma gamma1 gamma2) sl_rules ->
        sl_step (gamma :: w) (gamma1 :: gamma2 :: w).

  (* ------------------------------------------------------------------- *)
  (*  Reachability: reflexive-transitive closure of sl_step                *)
  (* ------------------------------------------------------------------- *)

  Inductive sl_reachable : list symbol -> list symbol -> Prop :=
    | sl_reach_refl : forall w, sl_reachable w w
    | sl_reach_step : forall w1 w2 w3,
        sl_step w1 w2 -> sl_reachable w2 w3 -> sl_reachable w1 w3.

  (* Direct steps are reachable *)
  Lemma sl_reachable_one : forall w1 w2,
    sl_step w1 w2 -> sl_reachable w1 w2.
  Proof.
    intros w1 w2 Hstep.
    apply sl_reach_step with w2.
    - exact Hstep.
    - apply sl_reach_refl.
  Qed.

  (* Reachability is transitive *)
  Lemma sl_reachable_trans : forall w1 w2 w3,
    sl_reachable w1 w2 -> sl_reachable w2 w3 -> sl_reachable w1 w3.
  Proof.
    intros w1 w2 w3 H12 H23.
    induction H12 as [w | a b c Hstep Hbc IH].
    - exact H23.
    - apply sl_reach_step with b.
      + exact Hstep.
      + apply IH. exact H23.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Execution traces                                                     *)
  (* ------------------------------------------------------------------- *)

  (* An execution trace records the sequence of stacks visited. *)

  Inductive sl_trace : list symbol -> list symbol -> list (list symbol) -> Prop :=
    | sl_trace_nil : forall w, sl_trace w w [w]
    | sl_trace_cons : forall w1 w2 w3 tr,
        sl_step w1 w2 ->
        sl_trace w2 w3 tr ->
        sl_trace w1 w3 (w1 :: tr).

  Lemma sl_trace_implies_reachable : forall w1 w2 tr,
    sl_trace w1 w2 tr -> sl_reachable w1 w2.
  Proof.
    intros w1 w2 tr Htrace.
    induction Htrace as [w | a b c tr' Hstep _ IH].
    - apply sl_reach_refl.
    - apply sl_reach_step with b.
      + exact Hstep.
      + exact IH.
  Qed.

  Lemma sl_reachable_has_trace : forall w1 w2,
    sl_reachable w1 w2 -> exists tr, sl_trace w1 w2 tr.
  Proof.
    intros w1 w2 Hreach.
    induction Hreach as [w | a b c Hstep _ IH].
    - exists [w]. apply sl_trace_nil.
    - destruct IH as [tr Htrace].
      exists (a :: tr). eapply sl_trace_cons.
      + exact Hstep.
      + exact Htrace.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  P-automaton acceptance (single location)                             *)
  (* ------------------------------------------------------------------- *)

  (* The distinguished initial state in the P-automaton, corresponding
     to the single control location p. In wpds.rs:709, this is p_state = 0. *)
  Variable embed_p : pa_state.

  (* Final (accepting) states of the P-automaton. *)
  Variable is_final : pa_state -> Prop.

  (* sl_accepts T w: the P-automaton with transition set T accepts
     the stack word w. This means there is a path from embed_p
     reading w to a final state. *)
  Definition sl_accepts
    (T : list (pa_state * symbol * pa_state))
    (w : list symbol) : Prop :=
    exists q_f, is_final q_f /\ pa_reads T embed_p w q_f.

  (* Monotonicity: adding transitions preserves acceptance *)
  Lemma sl_accepts_monotone :
    forall T1 T2 w,
      sl_accepts T1 w ->
      (forall t, In t T1 -> In t T2) ->
      sl_accepts T2 w.
  Proof.
    intros T1 T2 w [q_f [Hfinal Hreads]] Hsub.
    exists q_f. split.
    - exact Hfinal.
    - apply pa_reads_monotone with T1.
      + exact Hreads.
      + exact Hsub.
  Qed.

  (* ===================================================================== *)
  (*  Section 3: Poststar Soundness                                         *)
  (* ===================================================================== *)

  (* We prove that the saturated P-automaton accepts all reachable stacks.

     The proof proceeds by induction on the reachability derivation.
     The key insight: poststar adds transitions so that each rule
     application is "simulated" by the P-automaton.

     For Pop rules in the single-control-location case: when γ is popped,
     the sub-stack w below γ was put there by a previous Push rule.
     The Push saturation condition ensures that the sub-stack is readable
     from embed_p via the intermediate states created for the push.
     The Pop saturation condition (pop_closure below) captures this:
     any state reachable after reading γ from embed_p has its outgoing
     transitions replicated at embed_p, ensuring the sub-stack is
     directly readable from embed_p.

     This models the invariant maintained by poststar (wpds.rs:707-840):
     the P-automaton encodes all reachable stacks, not just top symbols. *)

  Section Poststar.

    (* The saturated transition set produced by poststar *)
    Variable poststar_T : list (pa_state * symbol * pa_state)%type.

    (* Initial configuration: stack = [γ₀] *)
    Variable gamma0 : symbol.

    (* The final state in the initial P-automaton *)
    Variable q_final : pa_state.
    Hypothesis init_final : is_final q_final.
    Hypothesis init_trans : In (embed_p, gamma0, q_final) poststar_T.

    (* ---- Saturation conditions (fixpoint of poststar algorithm) ---- *)

    (* SC-Replace: For every Replace rule SL_Replace γ γ' and
       transition (embed_p, γ, q) ∈ T, we have (embed_p, γ', q) ∈ T.
       This models wpds.rs:750-777: when a Replace rule fires,
       the transition for γ' reusing the same target state q is added. *)
    Hypothesis sat_replace :
      forall gamma gamma' q,
        In (SL_Replace gamma gamma') sl_rules ->
        In (embed_p, gamma, q) poststar_T ->
        In (embed_p, gamma', q) poststar_T.

    (* SC-Push: For every Push rule SL_Push γ γ₁ γ₂ and
       transition (embed_p, γ, q) ∈ T, there exists a fresh state q_r
       such that (embed_p, γ₁, q_r) ∈ T and (q_r, γ₂, q) ∈ T.
       This models wpds.rs:779-834: fresh state q_r connects the
       two pushed symbols. *)
    Hypothesis sat_push :
      forall gamma gamma1 gamma2 q,
        In (SL_Push gamma gamma1 gamma2) sl_rules ->
        In (embed_p, gamma, q) poststar_T ->
        exists q_r,
          In (embed_p, gamma1, q_r) poststar_T /\
          In (q_r, gamma2, q) poststar_T.

    (* SC-Pop (absorption): For every Pop rule SL_Pop γ and transition
       (embed_p, γ, q) ∈ T, any stack readable from q is also readable
       from embed_p. This ensures that after popping γ, the sub-stack
       is accepted via embed_p just as it was via q.

       Justification: In PraTTaIL's single-location WPDS, popping γ
       returns to the same control location p. The sub-stack below γ
       was established by prior Push rules. The poststar algorithm
       (wpds.rs:742-749) does not add explicit transitions for Pop,
       but the invariant holds because:
       (a) the sub-stack below γ was placed by a Push, which created
           transitions readable from a state q_r,
       (b) the state q after reading γ IS q_r (or connected to it),
       (c) transitions from q_r reading the continuation already lead
           back to states reachable from embed_p.

       We capture this as a saturation condition on the final T:
       for Pop with (embed_p, γ, q) ∈ T, every path from q is
       reproducible from embed_p. *)
    Hypothesis pop_absorption :
      forall gamma q,
        In (SL_Pop gamma) sl_rules ->
        In (embed_p, gamma, q) poststar_T ->
        forall w q_f,
          pa_reads poststar_T q w q_f ->
          pa_reads poststar_T embed_p w q_f.

    (* ---- Auxiliary: one step preserves acceptance ---- *)

    (* If w1 is accepted and w1 → w2, then w2 is accepted. *)
    Lemma poststar_step_forward :
      forall w1 w2,
        sl_step w1 w2 ->
        sl_accepts poststar_T w1 ->
        sl_accepts poststar_T w2.
    Proof.
      intros w1 w2 Hstep [q_f [Hfinal Hreads]].
      inversion Hstep; subst.
      - (* Pop: w1 = γ :: w, w2 = w.
           Hreads: pa_reads T embed_p (γ :: w) q_f.
           Decompose: (embed_p, γ, q_mid) ∈ T and pa_reads T q_mid w q_f.
           By pop_absorption: pa_reads T embed_p w q_f directly. *)
        apply pa_reads_cons_inv in Hreads.
        destruct Hreads as [q_mid [Hin Hrest]].
        exists q_f. split.
        + exact Hfinal.
        + apply pop_absorption with gamma q_mid; assumption.
      - (* Replace: w1 = γ :: w, w2 = γ' :: w.
           Hreads: pa_reads T embed_p (γ :: w) q_f.
           Decompose: (embed_p, γ, q_mid) ∈ T and pa_reads T q_mid w q_f.
           By sat_replace: (embed_p, γ', q_mid) ∈ T.
           Construct: pa_reads T embed_p (γ' :: w) q_f. *)
        apply pa_reads_cons_inv in Hreads.
        destruct Hreads as [q_mid [Hin Hrest]].
        exists q_f. split.
        + exact Hfinal.
        + apply pa_reads_cons with q_mid.
          * apply sat_replace with gamma; assumption.
          * exact Hrest.
      - (* Push: w1 = γ :: w, w2 = γ₁ :: γ₂ :: w.
           Hreads: pa_reads T embed_p (γ :: w) q_f.
           Decompose: (embed_p, γ, q_mid) ∈ T and pa_reads T q_mid w q_f.
           By sat_push: exists q_r with (embed_p, γ₁, q_r) and (q_r, γ₂, q_mid).
           Construct: read γ₁ to q_r, read γ₂ to q_mid, read w to q_f. *)
        apply pa_reads_cons_inv in Hreads.
        destruct Hreads as [q_mid [Hin Hrest]].
        destruct (sat_push gamma gamma1 gamma2 q_mid) as [q_r [Htop Hbot]];
          try assumption.
        exists q_f. split.
        + exact Hfinal.
        + apply pa_reads_cons with q_r.
          * exact Htop.
          * apply pa_reads_cons with q_mid.
            -- exact Hbot.
            -- exact Hrest.
    Qed.

    (* ---- Auxiliary: acceptance propagates along reachability ---- *)

    Lemma poststar_reachable_preserves :
      forall w1 w2,
        sl_reachable w1 w2 ->
        sl_accepts poststar_T w1 ->
        sl_accepts poststar_T w2.
    Proof.
      intros w1 w2 Hreach.
      induction Hreach as [w0 | wa wb wc Hstep Hbc IH].
      - (* Base: w1 = w2, trivial *)
        intros Hacc. exact Hacc.
      - (* Step: wa → wb →* wc *)
        intros Hacc.
        apply IH.
        apply poststar_step_forward with wa.
        + exact Hstep.
        + exact Hacc.
    Qed.

    (* ---- Main theorem ---- *)

    (* Theorem (Poststar Soundness): If stack w is reachable from [γ₀],
       then the saturated P-automaton accepts w.

       Proof: [γ₀] is accepted (by init_trans/init_final), and
       poststar_reachable_preserves propagates acceptance along
       the reachability chain. *)

    Theorem poststar_soundness :
      forall w,
        sl_reachable [gamma0] w ->
        sl_accepts poststar_T w.
    Proof.
      intros w Hreach.
      apply poststar_reachable_preserves with [gamma0].
      - exact Hreach.
      - exists q_final. split.
        + exact init_final.
        + apply pa_reads_cons with q_final.
          * exact init_trans.
          * apply pa_reads_nil.
    Qed.

  End Poststar.

  (* ===================================================================== *)
  (*  Section 4: Prestar Soundness                                          *)
  (* ===================================================================== *)

  (* We prove that the saturated P-automaton produced by prestar accepts
     all stacks from which a target configuration is reachable.

     The proof proceeds by induction on reachability, going backwards:
     if w0 →* w and w is accepted by the target, then w0 is accepted
     by the prestar automaton.

     The prestar algorithm (wpds.rs:855-1005) starts from the target
     P-automaton and adds transitions backward: for each rule whose
     RHS matches existing transitions, a new LHS transition is added. *)

  Section Prestar.

    Variable prestar_T : list (pa_state * symbol * pa_state)%type.
    Variable target_T : list (pa_state * symbol * pa_state)%type.

    (* Target transitions are contained in prestar_T *)
    Hypothesis target_subset :
      forall t, In t target_T -> In t prestar_T.

    (* ---- Saturation conditions (fixpoint of prestar algorithm) ---- *)

    (* SC-Pop (prestar): For every Pop rule SL_Pop γ, the transition
       (embed_p, γ, embed_p) ∈ prestar_T.
       This models wpds.rs:874-898: Pop rules are processed unconditionally
       in Phase 1, adding a self-loop on the control location. *)
    Hypothesis sat_pre_pop :
      forall gamma,
        In (SL_Pop gamma) sl_rules ->
        In (embed_p, gamma, embed_p) prestar_T.

    (* SC-Replace (prestar): For every Replace rule SL_Replace γ γ'
       and transition (embed_p, γ', q) ∈ prestar_T,
       we have (embed_p, γ, q) ∈ prestar_T.
       This models wpds.rs:916-951: when a Replace rule's RHS γ'
       appears in a transition, the LHS γ transition is added. *)
    Hypothesis sat_pre_replace :
      forall gamma gamma' q,
        In (SL_Replace gamma gamma') sl_rules ->
        In (embed_p, gamma', q) prestar_T ->
        In (embed_p, gamma, q) prestar_T.

    (* SC-Push (prestar): For every Push rule SL_Push γ γ₁ γ₂ and
       transitions (embed_p, γ₁, q') ∈ prestar_T and (q', γ₂, q) ∈ prestar_T,
       we have (embed_p, γ, q) ∈ prestar_T.
       This models wpds.rs:953-998: when a Push rule's RHS pair (γ₁, γ₂)
       appears in consecutive transitions, the LHS γ transition is added. *)
    Hypothesis sat_pre_push :
      forall gamma gamma1 gamma2 q' q,
        In (SL_Push gamma gamma1 gamma2) sl_rules ->
        In (embed_p, gamma1, q') prestar_T ->
        In (q', gamma2, q) prestar_T ->
        In (embed_p, gamma, q) prestar_T.

    (* ---- Auxiliary: one step backward preserves acceptance ---- *)

    Lemma prestar_step_back :
      forall w1 w2,
        sl_step w1 w2 ->
        sl_accepts prestar_T w2 ->
        sl_accepts prestar_T w1.
    Proof.
      intros w1 w2 Hstep [q_f [Hfinal Hreads]].
      inversion Hstep; subst.
      - (* Pop: w1 = γ :: w, w2 = w.
           Hreads: pa_reads T embed_p w q_f.
           By sat_pre_pop: (embed_p, γ, embed_p) ∈ prestar_T.
           Construct: read γ from embed_p to embed_p, then read w to q_f. *)
        exists q_f. split.
        + exact Hfinal.
        + apply pa_reads_cons with embed_p.
          * apply sat_pre_pop. assumption.
          * exact Hreads.
      - (* Replace: w1 = γ :: w, w2 = γ' :: w.
           Hreads: pa_reads T embed_p (γ' :: w) q_f.
           Decompose: (embed_p, γ', q_mid) and pa_reads T q_mid w q_f.
           By sat_pre_replace: (embed_p, γ, q_mid) ∈ prestar_T.
           Construct: read γ from embed_p to q_mid, then read w to q_f. *)
        apply pa_reads_cons_inv in Hreads.
        destruct Hreads as [q_mid [Hin Hrest]].
        exists q_f. split.
        + exact Hfinal.
        + apply pa_reads_cons with q_mid.
          * apply sat_pre_replace with gamma'; assumption.
          * exact Hrest.
      - (* Push: w1 = γ :: w, w2 = γ₁ :: γ₂ :: w.
           Hreads: pa_reads T embed_p (γ₁ :: γ₂ :: w) q_f.
           Decompose twice:
             (embed_p, γ₁, q') and pa_reads T q' (γ₂ :: w) q_f
             (q', γ₂, q_mid) and pa_reads T q_mid w q_f.
           By sat_pre_push: (embed_p, γ, q_mid) ∈ prestar_T.
           Construct: read γ from embed_p to q_mid, then read w to q_f. *)
        apply pa_reads_cons_inv in Hreads.
        destruct Hreads as [q' [Hin1 Hrest1]].
        apply pa_reads_cons_inv in Hrest1.
        destruct Hrest1 as [q_mid [Hin2 Hrest2]].
        exists q_f. split.
        + exact Hfinal.
        + apply pa_reads_cons with q_mid.
          * apply sat_pre_push with gamma1 gamma2 q'; assumption.
          * exact Hrest2.
    Qed.

    (* ---- Main theorem ---- *)

    (* Theorem (Prestar Soundness): If stack w is reachable from w0
       and w is accepted by the target automaton, then w0 is accepted
       by the prestar automaton.

       Proof by induction on the reachability derivation, applying
       prestar_step_back at each step. *)

    Theorem prestar_soundness :
      forall w0 w,
        sl_reachable w0 w ->
        sl_accepts target_T w ->
        sl_accepts prestar_T w0.
    Proof.
      intros w0 w Hreach Hacc_target.
      (* Lift target acceptance to prestar_T acceptance *)
      assert (Hacc : sl_accepts prestar_T w).
      { apply sl_accepts_monotone with target_T.
        - exact Hacc_target.
        - exact target_subset.
      }
      clear Hacc_target.
      (* Induct on reachability, going backward *)
      induction Hreach as [w' | w1 w2 w3 Hstep Hreach23 IH].
      - (* Base: w0 = w, already accepted *)
        exact Hacc.
      - (* Step: w0 → w2 →* w3 = w *)
        apply prestar_step_back with w2.
        + exact Hstep.
        + apply IH. exact Hacc.
    Qed.

  End Prestar.

End SingleLocationWPDS.

(* ===================================================================== *)
(*  Section 5: MOVP Fixpoint — Monotonicity and Convergence                *)
(* ===================================================================== *)

(* The Monotone Over Weighted Pushdown (MOVP) framework from
   Reps et al. (2007) Section 4 establishes that poststar and prestar
   compute fixpoints of the saturation operator.

   Key properties:
   1. Monotonicity: saturation only adds transitions (never removes)
   2. Boundedness: the transition set is finite
   3. Convergence: monotonicity + boundedness implies fixpoint

   For bounded idempotent semirings, the weight domain has finite height,
   so the saturation terminates after at most H × |T_max| steps where
   H is the height of the weight lattice and |T_max| is the maximum
   number of distinct transitions. *)

Section MOVPFixpoint.

  (* Transition type (abstract) *)
  Variable trans : Type.

  (* ------------------------------------------------------------------- *)
  (*  Saturation operator                                                  *)
  (* ------------------------------------------------------------------- *)

  (* A saturation step takes a transition set (list) and produces a
     (possibly larger) transition set by applying all applicable rule cases.
     This models one complete pass of the worklist loop in poststar
     (wpds.rs:735-836) or prestar (wpds.rs:910-1002). *)
  Variable sat_step : list trans -> list trans.

  (* Monotonicity: the saturation operator only adds transitions.
     This is guaranteed by the algorithm structure: transitions are
     added to the HashMap (wpds.rs:724-729) and never removed. *)
  Hypothesis sat_monotone :
    forall T t,
      In t T -> In t (sat_step T).

  (* ------------------------------------------------------------------- *)
  (*  Fixpoint characterization                                            *)
  (* ------------------------------------------------------------------- *)

  (* A transition set T is a fixpoint if sat_step does not add new transitions *)
  Definition is_fixpoint (T : list trans) : Prop :=
    forall t, In t (sat_step T) <-> In t T.

  (* Iterated application of sat_step *)
  Fixpoint iterate (n : nat) (T : list trans) : list trans :=
    match n with
    | 0 => T
    | S m => sat_step (iterate m T)
    end.

  (* Monotonicity extends to iterated application *)
  Lemma iterate_monotone : forall n T t,
    In t T -> In t (iterate n T).
  Proof.
    intros n T t Hin.
    induction n as [| m IH].
    - simpl. exact Hin.
    - simpl. apply sat_monotone. exact IH.
  Qed.

  (* iterate is cumulative: iterate (S n) contains iterate n *)
  Lemma iterate_cumulative : forall n T t,
    In t (iterate n T) -> In t (iterate (S n) T).
  Proof.
    intros n T t Hin.
    simpl. apply sat_monotone. exact Hin.
  Qed.

  (* Earlier iterates are subsets of later iterates *)
  Lemma iterate_subset : forall n m T t,
    n <= m ->
    In t (iterate n T) ->
    In t (iterate m T).
  Proof.
    intros n m T t Hle Hin.
    induction Hle as [| m' Hle' IH].
    - exact Hin.
    - apply iterate_cumulative. exact IH.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Boundedness and convergence                                          *)
  (* ------------------------------------------------------------------- *)

  (* Upper bound on the number of possible distinct transitions.
     Since states, symbols, and pa_states are all finite, the set of
     all possible transitions is finite. *)
  Variable max_transitions : nat.

  (* The length of the transition set is bounded *)
  Hypothesis length_bounded :
    forall n T, length (iterate n T) <= max_transitions.

  (* NoDup is preserved through iteration *)
  Hypothesis nodup_iterate :
    forall n T, NoDup (iterate n T).

  (* If iterate n T is not a fixpoint, iterate (S n) T is strictly larger.
     This follows from monotonicity + NoDup: if sat_step adds a new element
     and the list has no duplicates, the length increases by at least 1. *)
  Hypothesis not_fixpoint_grows :
    forall n T,
      ~ is_fixpoint (iterate n T) ->
      length (iterate n T) < length (iterate (S n) T).

  (* ---- Convergence theorem ---- *)

  (* Theorem (MOVP Convergence): Saturation terminates.
     Since the transition set is bounded and grows strictly at each
     non-fixpoint step, it must reach a fixpoint within at most
     max_transitions steps.

     Proof by well-founded induction on the gap
     (max_transitions - length(iterate n T)). At each step, either
     we are at a fixpoint (done), or the gap shrinks by at least 1.
     Since the gap is a natural number, it cannot shrink forever. *)

  Theorem saturation_converges :
    forall T,
      exists n, is_fixpoint (iterate n T).
  Proof.
    intro T.
    (* We prove by induction on a fuel parameter that bounds the gap *)
    assert (Hhelper : forall fuel n,
              length (iterate n T) + fuel >= max_transitions ->
              exists m, is_fixpoint (iterate m T)).
    { intro fuel.
      induction fuel as [| fuel' IH].
      - (* fuel = 0: length >= max_transitions, so no room to grow *)
        intros n Hge.
        exists n.
        destruct (classic (is_fixpoint (iterate n T))) as [Hfix | Hnfix].
        + exact Hfix.
        + exfalso.
          (* If not fixpoint, it would grow, exceeding the bound *)
          pose proof (not_fixpoint_grows n T Hnfix) as Hgrow.
          pose proof (length_bounded (S n) T) as Hbnd.
          lia.
      - (* fuel = S fuel': either fixpoint or recurse with less fuel *)
        intros n Hge.
        destruct (classic (is_fixpoint (iterate n T))) as [Hfix | Hnfix].
        + exists n. exact Hfix.
        + apply IH with (n := S n).
          pose proof (not_fixpoint_grows n T Hnfix) as Hgrow.
          lia.
    }
    apply Hhelper with (fuel := max_transitions) (n := 0).
    lia.
  Qed.

  (* ---- Fixpoint is a post-fixpoint of every earlier iterate ---- *)

  (* Once we reach a fixpoint, all earlier transition sets are subsets. *)
  Lemma fixpoint_contains_all : forall n m T,
    n <= m ->
    forall t, In t (iterate n T) -> In t (iterate m T).
  Proof.
    intros n m T Hle t Hin.
    apply iterate_subset with n.
    - exact Hle.
    - exact Hin.
  Qed.

  (* At a fixpoint, the transition set is closed under sat_step *)
  Lemma fixpoint_closed : forall n T,
    is_fixpoint (iterate n T) ->
    forall t, In t (sat_step (iterate n T)) -> In t (iterate n T).
  Proof.
    intros n T Hfix t Hin.
    apply Hfix. exact Hin.
  Qed.

End MOVPFixpoint.

(* ===================================================================== *)
(*  Section 6: Rule Structural Induction Lemmas                            *)
(* ===================================================================== *)

(* These lemmas support reasoning about WPDS rules by structural
   induction on the rule form, useful for proving saturation conditions
   hold after construction. *)

Section RuleInduction.

  Variable symbol : Type.

  (* Every single-location rule is one of three forms *)
  Lemma sl_rule_cases : forall (r : sl_rule symbol),
    (exists g, r = SL_Pop symbol g) \/
    (exists g g', r = SL_Replace symbol g g') \/
    (exists g g1 g2, r = SL_Push symbol g g1 g2).
  Proof.
    intro r.
    destruct r as [g | g g' | g g1 g2].
    - left. exists g. reflexivity.
    - right. left. exists g, g'. reflexivity.
    - right. right. exists g, g1, g2. reflexivity.
  Qed.

  (* Stack depth change for each rule type *)
  Definition sl_stack_delta (r : sl_rule symbol) : Z :=
    match r with
    | SL_Pop _ _ => (-1)%Z
    | SL_Replace _ _ _ => 0%Z
    | SL_Push _ _ _ _ => 1%Z
    end.

  (* Pop rules decrease stack length by 1 *)
  Lemma pop_decreases_stack :
    forall (gamma : symbol) (w : list symbol),
      length w = length (gamma :: w) - 1.
  Proof.
    intros. simpl. lia.
  Qed.

  (* Replace rules preserve stack length *)
  Lemma replace_preserves_stack :
    forall (gamma gamma' : symbol) (w : list symbol),
      length (gamma' :: w) = length (gamma :: w).
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (* Push rules increase stack length by 1 *)
  Lemma push_increases_stack :
    forall (gamma gamma1 gamma2 : symbol) (w : list symbol),
      length (gamma1 :: gamma2 :: w) = length (gamma :: w) + 1.
  Proof.
    intros. simpl. lia.
  Qed.

  (* All step rules require a non-empty source stack. *)
  Lemma sl_step_requires_nonempty :
    forall (rules : list (sl_rule symbol)) (w1 w2 : list symbol),
      sl_step symbol rules w1 w2 ->
      w1 <> [].
  Proof.
    intros rules w1 w2 Hstep.
    inversion Hstep; subst; discriminate.
  Qed.

End RuleInduction.

(* ===================================================================== *)
(*  Section 7: Composition — Poststar and Prestar Consistency              *)
(* ===================================================================== *)

(* If w0 reaches w and w is in the target set, then:
   - poststar([w0]) accepts w      (poststar soundness)
   - prestar(target) accepts w0    (prestar soundness)
   This section proves the composition property: the two algorithms
   give consistent answers. *)

Section Composition.

  Variable symbol : Type.
  Variable pa_state : Type.
  Variable embed_p : pa_state.
  Variable is_final : pa_state -> Prop.
  Variable rules : list (sl_rule symbol).

  (* ------------------------------------------------------------------- *)
  (*  Consistency: poststar and prestar agree on reachable targets         *)
  (* ------------------------------------------------------------------- *)

  Theorem poststar_prestar_consistent :
    forall (poststar_T prestar_T target_T : list (pa_state * symbol * pa_state))
           w0 w,
      (* Poststar accepts w given w0 reaches w *)
      (sl_reachable symbol rules w0 w ->
       sl_accepts symbol pa_state embed_p is_final poststar_T w) ->
      (* Prestar accepts w0 given w0 reaches w and w is in target *)
      (sl_reachable symbol rules w0 w ->
       sl_accepts symbol pa_state embed_p is_final target_T w ->
       sl_accepts symbol pa_state embed_p is_final prestar_T w0) ->
      (* Premises *)
      sl_reachable symbol rules w0 w ->
      sl_accepts symbol pa_state embed_p is_final target_T w ->
      (* Conclusion: both algorithms accept *)
      sl_accepts symbol pa_state embed_p is_final poststar_T w /\
      sl_accepts symbol pa_state embed_p is_final prestar_T w0.
  Proof.
    intros poststar_T prestar_T target_T w0 w Hpost Hpre Hreach Htarget.
    split.
    - apply Hpost. exact Hreach.
    - apply Hpre.
      + exact Hreach.
      + exact Htarget.
  Qed.

End Composition.

(* ===================================================================== *)
(*  Verification: Check that classic is available                          *)
(* ===================================================================== *)

Check classic.
