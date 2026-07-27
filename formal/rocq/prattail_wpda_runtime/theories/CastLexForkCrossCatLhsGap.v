(*
 * CastLexForkCrossCatLhsGap: the RE-GROUNDED model for the cast-then-compare
 * fix, written after the red-team refuted the prior dispatch design's mechanism
 * and the ground-truth trace re-investigation pinned the real gap
 * (docs/design/parser-fv/cast-compare-ground-truth.md).
 *
 * GROUND TRUTH (trace-proven, `int(3) == 3`):
 *   - The root ALREADY fans `int` into the ProcBool projection (the lex-alt
 *     table supports CrossCatProjection, kind_dispatch.rs:471-501), so a
 *     Bool-seeking context EXISTS. In it, `int` is keyword/ident lex-ambiguous;
 *     the lex-fork takes over (forks.rs:174); its table has NO
 *     LexAltRuleKind::CrossCatLhs variant, so the Pass-0 CrossCatLhs{Int} arm
 *     (prefix.rs:1301-1323 — which EXISTS for (Bool, "int")) is unrepresentable;
 *     the 51d57c91 fall-through does not fire because
 *     prefix_primary_has_dispatch_rule(Bool,"int") covers only the state cat's
 *     OWN leading-literal rules (kind_dispatch.rs:172-199) and Bool owns none.
 *     ⇒ only the Ident->Var branch survives (trace F1: VarBool[0,1]) — the
 *     keyword interpretation that would make this cursor a dispatch-time
 *     d-WORKER is DROPPED. Same gap class as 51d57c91 (an interpretation the
 *     lex-alt table cannot represent), one context over.
 *
 * THE MODEL: classify the state category of a dispatch of keyword token kw
 * (owned by category c — kw heads leading-literal rules only in c):
 *   - OwnerCtx : state = c. prefix_primary_has_dispatch_rule = true (the
 *     NonAtomic/TerminalKeyword leading-literal arms) ⇒ 51d57c91 fall-through ⇒
 *     the cast/keyword arm fires. (Transcribed: kind_dispatch.rs:172-199.)
 *   - SourceCtx: state = d ≠ c with c ∈ cross_cat_infix_sources(d) and
 *     kw ∈ FIRST(c) ⇒ the normal dispatch owns a Pass-0 CrossCatLhs{c} arm
 *     (transcribed: prefix.rs Pass-0 :944-976 + emit arm :1301-1323), but the
 *     LEX-FORK cannot represent it — the gap.
 *   - OtherCtx : neither (no keyword rule, no Pass-0 bucket).
 *
 * Interpretations of the kw token at a dispatch: IVar (the Ident->Var lex-alt),
 * ICast (the owner cat's leading-literal/cast arm), IDelegate (the Pass-0
 * CrossCatLhs delegate — the dispatch-time d-worker).
 *
 * The hosting fact (imported conclusion, proven in CastRehostOutputProjection +
 * observed live in trace F5): a category-changing infix result d is hosted IFF
 * the operand worker is a dispatch-time d-context worker = IDelegate in
 * SourceCtx. ICast in OwnerCtx yields the c-worker whose continuation injects
 * c, never d (trace F5: Bool[0,6] rejected by every Int frame, expected=2).
 *
 * THEOREMS: the CURRENT branch sets have NO d-hosting interpretation anywhere
 * (the completeness gap = the observed failure cluster); both fix shapes (d1
 * fall-through extension / d2 new lex-alt variant) restore it; d2 is a
 * monotone superset of current (no-loss); the fall-through predicate extension
 * preserves the 51d57c91 (189-fix) behavior verbatim and never fires at
 * multi-length ties (the -3! guard); and the cursor fan-out is DERIVED from
 * one counting function over the context classification: constant for the fix
 * (inner cast levels are OwnerCtx — the cast body's param cats own their
 * keywords), exponential 2^(S d) for the falsified per-level routing (every
 * level SourceCtx) — deriving BOTH the falsified experiment's blowup and the
 * fix's bound from the same function, instead of asserting either.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section CastLexForkCrossCatLhsGap.

  (* ── Context classification of a keyword dispatch (transcribed premises) ── *)
  Inductive CtxKind : Type :=
    | OwnerCtx    (* state cat owns a kw-leading rule: primary-dispatch true *)
    | SourceCtx   (* state cat has a Pass-0 CrossCatLhs bucket for kw *)
    | OtherCtx.   (* neither *)

  (* ── Interpretations of the kw token ── *)
  Inductive Interp : Type :=
    | IVar        (* Ident -> auto-injected Var (the lex-alt Atomic branch) *)
    | ICast       (* the owner cat's leading-literal (cast/keyword) arm *)
    | IDelegate.  (* the Pass-0 CrossCatLhs delegate = dispatch-time d-worker *)

  Definition interp_eqb (a b : Interp) : bool :=
    match a, b with
    | IVar, IVar | ICast, ICast | IDelegate, IDelegate => true
    | _, _ => false
    end.

  (* ── The hosting fact (imported from CastRehostOutputProjection +
        trace F5): only the dispatch-time delegate worker hosts the
        category-changing result d. ── *)
  Definition hosts_d (i : Interp) (k : CtxKind) : bool :=
    match i, k with
    | IDelegate, SourceCtx => true
    | _, _ => false
    end.

  (* ── Branch sets per context ── *)

  (* CURRENT system (trace-proven): OwnerCtx falls through to the cast arm
     (51d57c91); SourceCtx forks ONLY the Ident->Var lex-alt (the CrossCatLhs
     arm is unrepresentable in the table and the fall-through predicate is
     false); OtherCtx likewise Var-only. *)
  Definition branches_current (k : CtxKind) : list Interp :=
    match k with
    | OwnerCtx => [ICast]
    | SourceCtx => [IVar]
    | OtherCtx => [IVar]
    end.

  (* FIX d1 — fall-through extension (the 51d57c91 pattern): in SourceCtx the
     fork is skipped and the normal dispatch's Pass-0 arm fires (singleton
     CrossCatLhs). The Var alt is dropped at the same-length tie — keyword
     reservation, the documented 51d57c91 policy. *)
  Definition branches_d1 (k : CtxKind) : list Interp :=
    match k with
    | OwnerCtx => [ICast]
    | SourceCtx => [IDelegate]
    | OtherCtx => [IVar]
    end.

  (* FIX d2 — new lex-alt variant (LexAltRuleKind::CrossCatLhs): the fork keeps
     BOTH the Var branch AND the delegate branch (ambiguity-preserving;
     evidence — the premature filter at EOI — rejects the loser). *)
  Definition branches_d2 (k : CtxKind) : list Interp :=
    match k with
    | OwnerCtx => [ICast]
    | SourceCtx => [IVar; IDelegate]
    | OtherCtx => [IVar]
    end.

  (* ── THE COMPLETENESS GAP (current system): no interpretation anywhere
        hosts d — the observed failure cluster (12 comparison_after_cast +
        2 operator_chains + 2 string + 6 casterrfixed + 1 rholang). ── *)
  Theorem current_completeness_gap :
    forall k i, In i (branches_current k) -> hosts_d i k = false.
  Proof.
    intros k i H. destruct k; simpl in H;
      destruct H as [<- | H]; try contradiction; reflexivity.
  Qed.

  (* ── BOTH FIXES RESTORE the d-hosting derivation in SourceCtx. ── *)
  Theorem d1_restores_hosting :
    exists i, In i (branches_d1 SourceCtx) /\ hosts_d i SourceCtx = true.
  Proof. exists IDelegate. split; [left; reflexivity | reflexivity]. Qed.

  Theorem d2_restores_hosting :
    exists i, In i (branches_d2 SourceCtx) /\ hosts_d i SourceCtx = true.
  Proof. exists IDelegate. split; [right; left; reflexivity | reflexivity]. Qed.

  (* ── d2 is a MONOTONE EXTENSION of current (no interpretation is lost —
        feedback_preserve_disambiguation). ── *)
  Theorem d2_monotone :
    forall k i, In i (branches_current k) -> In i (branches_d2 k).
  Proof.
    intros k i H. destruct k; simpl in *;
      destruct H as [<- | H]; try contradiction;
      [ left; reflexivity | left; reflexivity | left; reflexivity ].
  Qed.

  (* d1 ⊆ d2: every d1 parse is a d2 parse (d1 = d2 minus the reserved Var at
     the SourceCtx same-length tie). *)
  Theorem d1_subset_d2 :
    forall k i, In i (branches_d1 k) -> In i (branches_d2 k).
  Proof.
    intros k i H. destruct k; simpl in *;
      destruct H as [<- | H]; try contradiction.
    - left; reflexivity.
    - right; left; reflexivity.
    - left; reflexivity.
  Qed.

  (* The d1-vs-d2 delta is EXACTLY the Var interpretation at SourceCtx (the
     keyword-reservation drop) — nothing else differs. *)
  Theorem d1_d2_delta :
    forall k i, In i (branches_d2 k) -> ~ In i (branches_d1 k) ->
      k = SourceCtx /\ i = IVar.
  Proof.
    intros k i H Hn. destruct k; simpl in *.
    - destruct H as [<- | H]; [exfalso; apply Hn; left; reflexivity | contradiction].
    - destruct H as [<- | [<- | H]]; try contradiction.
      + split; reflexivity.
      + exfalso; apply Hn; left; reflexivity.
    - destruct H as [<- | H]; [exfalso; apply Hn; left; reflexivity | contradiction].
  Qed.

  (* ── FALL-THROUGH PREDICATE ALGEBRA (d1's transcription target,
        forks.rs:427-430): old = primary_has && same_len;
        new = (primary_has || crosscat_lhs_has) && same_len. ── *)
  Definition fall_through_old (primary_has same_len : bool) : bool :=
    primary_has && same_len.
  Definition fall_through_new (primary_has crosscat_has same_len : bool) : bool :=
    (primary_has || crosscat_has) && same_len.

  (* 189-fix NON-INTERFERENCE: wherever the old predicate held (every 189-fix
     token fires in its OWNER context, primary_has = true), the new predicate
     is byte-identical. *)
  Theorem extension_preserves_189_behavior :
    forall ch sl, fall_through_new true ch sl = fall_through_old true sl.
  Proof. intros ch sl. reflexivity. Qed.

  (* The extension only ADDS fall-through cases (never removes one). *)
  Theorem extension_only_adds :
    forall ph ch sl, fall_through_old ph sl = true -> fall_through_new ph ch sl = true.
  Proof.
    intros ph ch sl H. unfold fall_through_old in H. unfold fall_through_new.
    apply andb_prop in H. destruct H as [Hp Hs].
    rewrite Hp. rewrite Hs. reflexivity.
  Qed.

  (* -3! GUARD: at a multi-length lexical tie (same_len = false) the new
     predicate NEVER fires — multi-length ambiguities (Minus@1 vs Integer@2)
     keep forking, exactly as before. *)
  Theorem multilength_unaffected :
    forall ph ch, fall_through_new ph ch false = false.
  Proof. intros ph ch. unfold fall_through_new. apply andb_false_r. Qed.

  (* ── THE DERIVED BOUND: one counting function over context classifications
        derives BOTH the fix's constant fan-out AND the falsified experiment's
        exponential blowup. ── *)

  (* Cursor-path multiplier of a dispatch chain: the product over levels of the
     number of branches emitted at that level's context. *)
  Fixpoint path_multiplier (levels : list CtxKind) (b : CtxKind -> nat) : nat :=
    match levels with
    | [] => 1
    | k :: rest => b k * path_multiplier rest b
    end.

  Definition branch_count_current (k : CtxKind) : nat := length (branches_current k).
  Definition branch_count_d1 (k : CtxKind) : nat := length (branches_d1 k).
  Definition branch_count_d2 (k : CtxKind) : nat := length (branches_d2 k).

  (* THE FIX'S DISPATCH CHAIN for a depth-n nested cast at a comparison LHS:
     ONE SourceCtx dispatch (the comparison-LHS position, entered via the
     existing ProcD projection), then n OwnerCtx dispatches — the cast body's
     param cats own their keywords (FloatToInt's body parses in Float context,
     where `float` has a same-cat leading-literal rule, etc.; transcribed from
     calculator.rs:233-242 + kind_dispatch.rs NonAtomic arm). *)
  Definition fix_levels (n : nat) : list CtxKind :=
    SourceCtx :: repeat OwnerCtx n.

  (* THE FALSIFIED EXPERIMENT'S CHAIN: keyword routed into delegates at EVERY
     level (no owner-context fall-through) — every level SourceCtx. *)
  Definition falsified_levels (n : nat) : list CtxKind :=
    repeat SourceCtx (S n).

  Lemma path_multiplier_repeat_one :
    forall b k n, b k = 1 -> path_multiplier (repeat k n) b = 1.
  Proof.
    intros b k n Hb. induction n as [| n IH]; simpl.
    - reflexivity.
    - rewrite Hb, IH. reflexivity.
  Qed.

  (* d1: SourceCtx is a fall-through SINGLETON (no fork at all) — multiplier 1,
     identical to the unambiguous-literal path. *)
  Theorem d1_fanout_constant :
    forall n, path_multiplier (fix_levels n) branch_count_d1 = 1.
  Proof.
    intro n. simpl. rewrite path_multiplier_repeat_one; reflexivity.
  Qed.

  (* d2: ONE binary fork at the comparison-LHS position, inner levels singleton
     — multiplier 2, CONSTANT in nesting depth n. *)
  Theorem d2_fanout_constant :
    forall n, path_multiplier (fix_levels n) branch_count_d2 = 2.
  Proof.
    intro n. simpl. rewrite path_multiplier_repeat_one; reflexivity.
  Qed.

  (* The falsified per-level routing under the SAME counting function:
     2^(S n) — exponential in depth. This DERIVES the observed 327-cursor /
     nested-cast blowup shape from the classification, rather than asserting
     it: the danger was never the delegate itself, it was routing at every
     level instead of only at SourceCtx positions. *)
  Theorem falsified_fanout_exponential :
    forall n, path_multiplier (falsified_levels n) branch_count_d2 = 2 ^ (S n).
  Proof.
    intro n. unfold falsified_levels.
    induction n as [| n IH]; simpl in *.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma pow2_ge_2 : forall n, 1 <= n -> 2 <= 2 ^ n.
  Proof.
    intros n Hn. destruct n as [| n]; [lia |].
    simpl. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
  Qed.

  (* The contrast: for any nesting depth >= 1, the fix's fan-out is STRICTLY
     below the falsified shape's. *)
  Theorem fix_strictly_below_falsified :
    forall n, 1 <= n ->
      path_multiplier (fix_levels n) branch_count_d2
        < path_multiplier (falsified_levels n) branch_count_d2.
  Proof.
    intros n Hn.
    rewrite d2_fanout_constant, falsified_fanout_exponential.
    simpl. pose proof (pow2_ge_2 n Hn). lia.
  Qed.

  (* ── Completeness of the classification premise: the current system's
        SourceCtx Var-only branch is what produces the trace's short parse
        (VarBool[0,1] -> Proc[0,1] premature) — i.e. current SourceCtx admits
        IVar and ONLY IVar; the model is faithful to F1, not vacuous. ── *)
  Theorem current_sourcectx_is_var_only :
    branches_current SourceCtx = [IVar].
  Proof. reflexivity. Qed.

  (* ════════════════════════════════════════════════════════════════════════
     SCIENTIFIC LEDGER (2026-06-10d): the `fix_levels` premise — "inner cast
     levels are OwnerCtx" — was FALSIFIED empirically. The cast arm forks over
     its BODY categories (FloatToInt/BoolToInt/StrToInt/IntId), and the
     Bool-body branch is a SourceCtx at EVERY nesting level. Moreover the
     blowup is WORK-per-branch, not branch-count: the d1 SourceCtx branch is a
     fall-through SINGLETON (count 1 — `d1_fanout_constant` is true but about
     the wrong measure), yet the delegate it dispatches RE-PARSES its whole
     suffix, so an n-deep cast tower costs T(n) = T_owner(n-1) + T_delegate(n-1)
     ≈ 2^n WORK at constant cursor count (observed: 18 s / 30 s / >120 s-timeout
     on the depth-3/3/4 nested-cast tests). The fix below GATES the delegate on
     TRIGGER-PRESENCE in the remaining input — definite, monotone evidence (an
     infix fires only by CONSUMING its trigger token from the remaining input,
     so absence refutes every future firing): the no-comparison towers collapse
     to owner-only work, while every genuinely d-hosting input keeps its
     delegate (no-loss).
     ════════════════════════════════════════════════════════════════════════ *)

  Section TriggerPresenceGate.

    (* present = some d-resulting cross-cat infix TRIGGER token occurs in the
       remaining input (a whole-suffix scan — position-independent, monotone:
       consuming tokens never makes an absent trigger present). *)
    Variable present : bool.

    (* d1 GATED branch sets: the fall-through's crosscat disjunct additionally
       requires `present`; when absent, the lex fork behaves exactly as the
       CURRENT system (Var-only in SourceCtx). *)
    Definition branches_d1g (k : CtxKind) : list Interp :=
      match k with
      | OwnerCtx => [ICast]
      | SourceCtx => if present then [IDelegate] else [IVar]
      | OtherCtx => [IVar]
      end.

    (* NO-LOSS: the premise (transcribed from the InfixLoop dispatch — an infix
       fires only via ConsumeAndPush of its trigger) means a d-hosting
       derivation EXISTS only if its trigger is in the remaining input, i.e.
       present = true — and then the gated branches still host d. *)
    Theorem gate_no_loss :
      present = true ->
      exists i, In i (branches_d1g SourceCtx) /\ hosts_d i SourceCtx = true.
    Proof.
      intro Hp. exists IDelegate. unfold branches_d1g. rewrite Hp.
      split; [left; reflexivity | reflexivity].
    Qed.

    (* ZERO OVERHEAD when absent: the gated system is BRANCH-IDENTICAL to the
       current system in every context — the timed-out no-comparison towers
       return to baseline behavior. *)
    Theorem gate_zero_overhead_when_absent :
      present = false -> forall k, branches_d1g k = branches_current k.
    Proof.
      intros Hp k. destruct k; unfold branches_d1g, branches_current;
        [reflexivity | rewrite Hp; reflexivity | reflexivity].
    Qed.

    (* ── THE WORK MEASURE (the falsified premise corrected): an n-deep cast
          tower where EVERY level carries a Bool-body SourceCtx branch. ── *)

    (* ungated d1: at each level the delegate re-parses the suffix — the
       owner's work plus an equal delegate's work: 2^n. *)
    Fixpoint work_ungated (n : nat) : nat :=
      match n with
      | 0 => 1
      | S k => work_ungated k + work_ungated k
      end.

    (* gated d1 with the trigger ABSENT: the delegate never dispatches —
       owner-only work at every level. *)
    Fixpoint work_gated_absent (n : nat) : nat :=
      match n with
      | 0 => 1
      | S k => work_gated_absent k + 0
      end.

    Theorem ungated_work_exponential : forall n, work_ungated n = 2 ^ n.
    Proof.
      induction n as [| n IH]; simpl.
      - reflexivity.
      - rewrite IH. lia.
    Qed.

    Theorem gated_absent_work_constant : forall n, work_gated_absent n = 1.
    Proof.
      induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
    Qed.

    (* The contrast — the gate eliminates the tower blowup (the observed
       18 s / 30 s / >120 s growth) on trigger-free inputs. *)
    Theorem gate_kills_tower_blowup :
      forall n, 1 <= n -> work_gated_absent n < work_ungated n.
    Proof.
      intros n Hn. rewrite gated_absent_work_constant, ungated_work_exponential.
      destruct n as [| n]; [lia |].
      simpl. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia.
    Qed.

  End TriggerPresenceGate.

End CastLexForkCrossCatLhsGap.
