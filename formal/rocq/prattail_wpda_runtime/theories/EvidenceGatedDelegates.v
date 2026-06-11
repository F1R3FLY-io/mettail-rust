(*
 * EvidenceGatedDelegates: the P1 spec of the evidence-driven early-
 * pruning program (docs/design/evidence-pruning/02-staged-implementation-
 * plan.md, converged v3 @ 194a1d5c) — the cross-cat-LHS delegate fan is
 * bounded by suffix-trigger EVIDENCE, and the only admissible merge is
 * the exact-duplicate (EquivKey) collapse.
 *
 * COMPOSES (cited, not re-proven): CastLookaheadGateBound.v (the gated
 * frontier is linear in actual trigger occurrences, depth-independent;
 * gating_subsumes_per_position_merge), CastDelegateMergeBound.v
 * (K^d → linear), CastDispatchHostResolution.v (dispatch_sound /
 * dispatch_no_loss), CastLexForkCrossCatLhsGap.v (d1_subset_d2 /
 * d1_d2_delta — the keyword-reserved Var interpretation at a
 * same-length lex-fork tie is the exact d2−d1 residue).
 *
 * THIS FILE's new obligations (the P1 commit-1 deliverables):
 *   T1 gated_delegates_no_loss — any parse that consumes a trigger in
 *      the remaining suffix passes the (d2-complete) presence gate;
 *   T2 d1_gate_can_miss_d2_parse — the d1 trigger set being a strict
 *      subset can refute a d2-admitted parse (non-vacuous: the gate
 *      must ship with the FULL trigger alphabet);
 *   T3 gate_zero_when_absent — no trigger anywhere in the suffix ⇒ the
 *      gate licenses NO delegate at ANY position (the tower-blowup
 *      kill: depth-independent zero);
 *   T4 repair_blind_gate_over_refutes / repair_aware_gate_no_loss —
 *      the I8 v3 obligation: a trigger class synthesizable by repair
 *      must count as present (the presence gate may only refute when
 *      the trigger is BOTH absent and non-synthesizable);
 *   T5 equiv_dedup_identity_when_singleton + equiv_dedup_preserves_set
 *      — the EquivKey merge is coverage-preserving in general and the
 *      IDENTITY when the gate already yields ≤1 delegate per key
 *      (share_iff_duplicate: why the cohort-share half of P1 is
 *      conditional on measured duplicates; wrap_rule/wrap_cat REMAIN
 *      key discriminators — the M4 tombstone).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

(* ════════════════════════════════════════════════════════════════════
   Part 1 — the presence gate over a lattice suffix (T1-T4).
   The suffix is a list of per-position alternative-class SETS (the
   lattice form: a position may carry several lex alternatives; the
   gate's presence test is the union over alternatives — the sound
   over-approximation direction).
   ════════════════════════════════════════════════════════════════════ *)

Section PresenceGate.

  (* Per-position alternative class sets (as predicates). *)
  Variable suffix : list (nat -> Prop).
  (* The trigger alphabet the gate scans for. *)
  Variable triggers : nat -> Prop.
  (* Classes a repair can synthesize (INSERT/SUBSTITUTE/CategorySwitch;
     ∅ when recovery is disabled). *)
  Variable repair_synthesizable : nat -> Prop.

  (* A class is present in the suffix at-or-after position i. *)
  Definition present_from (i : nat) (c : nat) : Prop :=
    exists j P, i <= j /\ nth_error suffix j = Some P /\ P c.

  (* The PRESENCE GATE (repair-aware, the I8 v3 form): license the
     delegate at position i iff some trigger is present from i OR some
     trigger is repair-synthesizable. *)
  Definition gate_licenses (i : nat) : Prop :=
    exists c, triggers c
      /\ (present_from i c \/ repair_synthesizable c).

  (* A parse that USES a trigger: it consumes class c (a trigger) at
     some position j ≥ i, where c is either on the lattice or supplied
     by a repair. *)
  Definition parse_uses_trigger_from (i : nat) : Prop :=
    exists c j, triggers c /\ i <= j
      /\ ((exists P, nth_error suffix j = Some P /\ P c)
          \/ repair_synthesizable c).

  (* ── T1 — NO-LOSS: every parse that consumes a trigger from i is
        licensed by the gate at i. ── *)
  Theorem gated_delegates_no_loss :
    forall i, parse_uses_trigger_from i -> gate_licenses i.
  Proof.
    intros i [c [j [Htrig [Hle [HP | Hr]]]]].
    - destruct HP as [P [Hnth HPc]].
      exists c. split; [exact Htrig |].
      left. exists j, P. repeat split; assumption.
    - exists c. split; [exact Htrig |]. right. exact Hr.
  Qed.

  (* ── T3 — ZERO-WHEN-ABSENT: if no trigger is anywhere in the suffix
        and none is synthesizable, the gate licenses NOTHING at any
        position — the depth-independent tower kill. ── *)
  Theorem gate_zero_when_absent :
    (forall c j P, triggers c -> nth_error suffix j = Some P -> ~ P c) ->
    (forall c, triggers c -> ~ repair_synthesizable c) ->
    forall i, ~ gate_licenses i.
  Proof.
    intros Habsent Hnosynth i [c [Htrig [Hpres | Hr]]].
    - destruct Hpres as [j [P [_ [Hnth HPc]]]].
      exact (Habsent c j P Htrig Hnth HPc).
    - exact (Hnosynth c Htrig Hr).
  Qed.

End PresenceGate.

(* ── T2 — the d1 gate (strict trigger SUBSET) can refute a parse the
      d2 gate admits: with d2 = {5, 9} and d1 = {5} only, a parse using
      trigger 9 passes d2 but fails d1. The gate must ship with the
      FULL (d2) trigger alphabet. ── *)

Section D1MissesD2.

  Definition d2_triggers (c : nat) : Prop := c = 5 \/ c = 9.
  Definition d1_triggers (c : nat) : Prop := c = 5.
  Definition w_suffix : list (nat -> Prop) := [fun c => c = 9].
  Definition no_synth (_ : nat) : Prop := False.

  Theorem d1_gate_can_miss_d2_parse :
    parse_uses_trigger_from w_suffix d2_triggers no_synth 0
    /\ gate_licenses w_suffix d2_triggers no_synth 0
    /\ ~ gate_licenses w_suffix d1_triggers no_synth 0.
  Proof.
    split; [| split].
    - exists 9, 0. split; [right; reflexivity |].
      split; [apply Nat.le_refl |].
      left. exists (fun c => c = 9). split; reflexivity.
    - exists 9. split; [right; reflexivity |].
      left. exists 0, (fun c => c = 9).
      repeat split. apply Nat.le_refl.
    - intros [c [Hc [Hpres | Hr]]].
      + unfold d1_triggers in Hc. subst c.
        destruct Hpres as [j [P [_ [Hnth HPc]]]].
        destruct j as [| j'].
        * simpl in Hnth. injection Hnth as <-. discriminate HPc.
        * simpl in Hnth. destruct j'; discriminate Hnth.
      + exact Hr.
  Qed.

End D1MissesD2.

(* ── T4 — the repair-blind presence gate over-refutes: a trigger
      absent from the raw suffix but repair-synthesizable admits a
      repaired parse; the blind gate refuses it, the aware gate
      licenses it. ── *)

Section RepairAwareness.

  Definition rb_triggers (c : nat) : Prop := c = 7.
  Definition rb_suffix : list (nat -> Prop) := [fun _ => False].
  Definition rb_synth (c : nat) : Prop := c = 7.

  (* The repair-blind gate: presence only. *)
  Definition blind_gate_licenses (i : nat) : Prop :=
    exists c, rb_triggers c /\ present_from rb_suffix i c.

  Theorem repair_blind_gate_over_refutes :
    parse_uses_trigger_from rb_suffix rb_triggers rb_synth 0
    /\ gate_licenses rb_suffix rb_triggers rb_synth 0
    /\ ~ blind_gate_licenses 0.
  Proof.
    split; [| split].
    - exists 7, 0. split; [reflexivity |].
      split; [apply Nat.le_refl |]. right. reflexivity.
    - exists 7. split; [reflexivity |]. right. reflexivity.
    - intros [c [Hc Hpres]].
      unfold rb_triggers in Hc. subst c.
      destruct Hpres as [j [P [_ [Hnth HPc]]]].
      destruct j as [| j'].
      + simpl in Hnth. injection Hnth as <-. exact HPc.
      + simpl in Hnth. destruct j'; discriminate Hnth.
  Qed.

End RepairAwareness.

(* ════════════════════════════════════════════════════════════════════
   Part 2 — the EquivKey merge (T5): exact-duplicate collapse only.
   Delegates are keyed records; the merge collapses members with EQUAL
   keys (the EquivKey = (source_src_idx, inner_cur_bp) in the runtime;
   wrap_cat/wrap_rule REMAIN cache-key discriminators — collapsing
   across them was the M4 cast-family root cause and is NOT modeled as
   admissible here).
   ════════════════════════════════════════════════════════════════════ *)

Section EquivMerge.

  (* Keys are nats; a frontier is a list of keyed delegates. *)
  Definition dedup_keys (l : list nat) : list nat :=
    fold_right (fun k acc => if existsb (Nat.eqb k) acc then acc
                             else k :: acc) [] l.

  Lemma dedup_keys_sound :
    forall l k, In k (dedup_keys l) -> In k l.
  Proof.
    induction l as [| k0 l' IH]; simpl; intros k H.
    - exact H.
    - destruct (existsb (Nat.eqb k0) (dedup_keys l')) eqn:E.
      + right. exact (IH k H).
      + destruct H as [-> | H].
        * left. reflexivity.
        * right. exact (IH k H).
  Qed.

  Lemma dedup_keys_complete :
    forall l k, In k l -> In k (dedup_keys l).
  Proof.
    induction l as [| k0 l' IH]; simpl; intros k H.
    - exact H.
    - destruct H as [-> | H].
      + destruct (existsb (Nat.eqb k) (dedup_keys l')) eqn:E.
        * apply existsb_exists in E.
          destruct E as [k' [Hin Heq]].
          apply Nat.eqb_eq in Heq. subst k'. exact Hin.
        * left. reflexivity.
      + destruct (existsb (Nat.eqb k0) (dedup_keys l')) eqn:E.
        * exact (IH k H).
        * right. exact (IH k H).
  Qed.

  (* ── T5a — the EquivKey merge is COVERAGE-PRESERVING: the merged
        frontier carries exactly the same key SET (no delegate class is
        lost; only exact duplicates collapse). ── *)
  Theorem equiv_dedup_preserves_set :
    forall l k, In k (dedup_keys l) <-> In k l.
  Proof.
    intros l k. split;
      [apply dedup_keys_sound | apply dedup_keys_complete].
  Qed.

  (* ── T5b — share_iff_duplicate: when the frontier is already
        duplicate-free (the gate yields ≤1 delegate per key — the
        CastLookaheadGateBound regime), the merge is the IDENTITY:
        building the cohort-share machinery buys nothing. This is the
        formal statement of why P1's cohort-share half is CONDITIONAL
        on the measured duplicate counter. ── *)
  Theorem equiv_dedup_identity_when_singleton :
    forall l, NoDup l -> dedup_keys l = l.
  Proof.
    induction l as [| k l' IH]; simpl; intros Hnd.
    - reflexivity.
    - inversion Hnd; subst.
      rewrite (IH ltac:(assumption)).
      destruct (existsb (Nat.eqb k) l') eqn:E.
      + apply existsb_exists in E.
        destruct E as [k' [Hin Heq]].
        apply Nat.eqb_eq in Heq. subst k'. contradiction.
      + reflexivity.
  Qed.

End EquivMerge.
