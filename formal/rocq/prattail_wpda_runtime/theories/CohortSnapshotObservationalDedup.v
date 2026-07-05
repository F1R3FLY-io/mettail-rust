(*
 * CohortSnapshotObservationalDedup: soundness of narrowing the cohort
 * WorkerSnapshot dedup key to the CONSUMER-OBSERVED fields.
 *
 * CONTEXT (Phase 5A d1, 2026-06-10): the d1 lex-fork fall-through makes a
 * cross-cat-source context parse the cast operand via the CrossCatLhs delegate
 * (the d-worker fix, CastLexForkCrossCatLhsGap). The delegate's pops resolve
 * the SAME cohort keys as the owner-category parse, appending additional
 * WorkerSnapshots. The shipped dedup predicate
 * (`worker_snapshot_observationally_eq`, dispatch_cohort.rs) compares ALL
 * fields, INCLUDING `worker_weight` and `worker_pre_dispatch_weight` — but the
 * revive consumer (`revive_cohort_member_with_snapshot`, wpda_walker.rs:15150+)
 * reads ONLY {worker_inner_state, worker_last_action_output_cat,
 * worker_pending_packing_weight}: `worker_pre_dispatch_weight` is explicitly
 * discarded (`let _ = ...`, :15184 — the falsified Stage-1.5.3 tropical-delta
 * scheme) and `worker_weight` is never read (revive computes cursor.weight =
 * member.weight_at_dispatch ⊗ symbol_weight_sum). So two snapshots differing
 * ONLY in the dead weight fields produce BYTE-IDENTICAL revived cursors, yet
 * occupy two cap slots (MAX_WORKER_SNAPSHOTS_PER_KEY = 16) — the d1 delegates
 * tip saturated keys to 17 and the parse fails with a spurious
 * AmbiguityBudget overflow.
 *
 * THE FIX: narrow the dedup key to the consumed fields. This theory proves it
 * SOUND under the no-drop mandate:
 *   - `dedup_revival_no_loss`: consumed-equal snapshots revive identically
 *     (revive factors through the consumed projection) — collapsing them is
 *     EXACT observational-equivalence dedup, not weight-pruning.
 *   - `dedup_preserves_revived_set`: the revive-image of the consumed-dedup'd
 *     list equals the revive-image of the original list (no revived cursor is
 *     lost or invented).
 *   - `dedup_included` / `dedup_covers`: the dedup keeps a representative of
 *     every consumed-class and introduces nothing.
 *   - `narrow_key_fits_where_full_key_overflows`: the non-vacuous d1 contrast
 *     — two snapshots equal on consumed fields but different in dead weights
 *     occupy 2 slots under the full key (overflowing a cap of 1) and 1 slot
 *     under the consumed key, with IDENTICAL revived sets.
 *
 * The `-3!` per-packing distinction is PRESERVED: `worker_pending_packing_weight`
 * (the field that carries it, per the Stage-1.5.2 lesson) stays IN the key —
 * the model's `Op` type includes it by construction.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section CohortSnapshotObservationalDedup.

  (* Op = the consumer-observed fields {inner_state, last_action_output_cat,
     pending_packing_weight}; Dead = the unread fields {worker_weight,
     worker_pre_dispatch_weight}. A snapshot is their pair. *)
  Variable Op Dead Cursor : Type.
  Variable revive : Op -> Cursor.

  (* Decidable equality on the consumed fields (the new dedup key). *)
  Variable op_eqb : Op -> Op -> bool.
  Hypothesis op_eqb_eq : forall a b, op_eqb a b = true <-> a = b.

  Definition Snapshot : Type := (Op * Dead)%type.

  (* The TRANSCRIBED consumer: revive reads ONLY the Op component
     (wpda_walker.rs:15150-15238 — inner_state/output_cat/pending_packing_weight
     are copied to the cursor; worker_pre_dispatch_weight is `let _`-discarded;
     worker_weight is never read). *)
  Definition revive_snap (s : Snapshot) : Cursor := revive (fst s).

  Definition consumed_eqb (a b : Snapshot) : bool := op_eqb (fst a) (fst b).

  (* ── SOUNDNESS CRUX: consumed-equal snapshots revive IDENTICALLY — the
        dedup collapses only observationally-equal alternatives (Invariant 1:
        exact-key dedup, never weight-pruning). ── *)
  Theorem dedup_revival_no_loss :
    forall a b, consumed_eqb a b = true -> revive_snap a = revive_snap b.
  Proof.
    intros a b H. unfold consumed_eqb in H. apply op_eqb_eq in H.
    unfold revive_snap. rewrite H. reflexivity.
  Qed.

  (* Right-fold first-representative dedup (the append-side shape:
     append_snapshot_bounded keeps the FIRST snapshot of each class and marks
     later ones Duplicate). *)
  Fixpoint dedup_by (l : list Snapshot) : list Snapshot :=
    match l with
    | [] => []
    | x :: r =>
        if existsb (consumed_eqb x) (dedup_by r) then dedup_by r else x :: dedup_by r
    end.

  (* The dedup introduces nothing: dedup ⊆ original. *)
  Lemma dedup_included : forall l s, In s (dedup_by l) -> In s l.
  Proof.
    induction l as [| x r IH]; simpl; intros s H.
    - exact H.
    - destruct (existsb (consumed_eqb x) (dedup_by r)) eqn:E.
      + right. apply IH. exact H.
      + destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H].
  Qed.

  (* The dedup keeps a representative of every consumed-class. *)
  Lemma dedup_covers :
    forall l s, In s l -> exists s', In s' (dedup_by l) /\ consumed_eqb s' s = true.
  Proof.
    induction l as [| x r IH]; simpl; intros s H.
    - contradiction.
    - destruct H as [-> | H].
      + destruct (existsb (consumed_eqb s) (dedup_by r)) eqn:E.
        * apply existsb_exists in E. destruct E as [s' [Hin Heq]].
          exists s'. split; [exact Hin |].
          unfold consumed_eqb in *. apply op_eqb_eq in Heq.
          apply op_eqb_eq. symmetry. exact Heq.
        * exists s. split; [left; reflexivity |].
          unfold consumed_eqb. apply op_eqb_eq. reflexivity.
      + destruct (IH s H) as [s' [Hin Heq]].
        destruct (existsb (consumed_eqb x) (dedup_by r)) eqn:E.
        * exists s'. split; [exact Hin | exact Heq].
        * exists s'. split; [right; exact Hin | exact Heq].
  Qed.

  (* ── NO-LOSS AT THE SET LEVEL: the revived-cursor set of the dedup'd list
        equals that of the original list. ── *)
  Theorem dedup_preserves_revived_set :
    forall l c,
      (exists s, In s l /\ revive_snap s = c)
      <-> (exists s, In s (dedup_by l) /\ revive_snap s = c).
  Proof.
    intros l c. split.
    - intros [s [Hin Hrev]].
      destruct (dedup_covers l s Hin) as [s' [Hin' Heq]].
      exists s'. split; [exact Hin' |].
      rewrite (dedup_revival_no_loss s' s Heq). exact Hrev.
    - intros [s [Hin Hrev]].
      exists s. split; [apply dedup_included; exact Hin | exact Hrev].
  Qed.

  (* ── THE d1 CONTRAST (non-vacuity): two snapshots equal on Op, different in
        Dead. Under the FULL key (which distinguishes Dead) they occupy 2 cap
        slots — overflowing a cap of 1; under the consumed key they occupy 1 —
        no overflow — and the revived sets are IDENTICAL. ── *)
  Section Contrast.
    Variable o : Op.
    Variable d1 d2 : Dead.
    Hypothesis dead_differ : d1 <> d2.

    Definition full_eqb (a b : Snapshot) : bool := consumed_eqb a b.
    (* (the full key ALSO compares Dead; we model only what we need: the two
       contrast snapshots are full-DISTINCT because their Dead parts differ) *)

    Definition snap1 : Snapshot := (o, d1).
    Definition snap2 : Snapshot := (o, d2).

    Theorem full_key_two_slots : snap1 <> snap2.
    Proof.
      intro H. apply dead_differ. inversion H. reflexivity.
    Qed.

    Theorem narrow_key_one_slot : dedup_by [snap1; snap2] = [snap2].
    Proof.
      simpl. unfold consumed_eqb. simpl.
      assert (op_eqb o o = true) as E by (apply op_eqb_eq; reflexivity).
      rewrite E. simpl. reflexivity.
    Qed.

    (* the collapsed list revives the SAME cursor set as the two-slot list *)
    Theorem narrow_key_fits_where_full_key_overflows :
      (forall c,
        (exists s, In s [snap1; snap2] /\ revive_snap s = c)
        <-> (exists s, In s (dedup_by [snap1; snap2]) /\ revive_snap s = c))
      /\ length (dedup_by [snap1; snap2]) = 1
      /\ snap1 <> snap2.
    Proof.
      split; [| split].
      - intro c. apply dedup_preserves_revived_set.
      - rewrite narrow_key_one_slot. reflexivity.
      - exact full_key_two_slots.
    Qed.
  End Contrast.

  (* ── CAP RELIEF IS MONOTONE: the dedup'd list is never longer than the
        original, so narrowing the key can only DECREASE the per-key slot
        count (fewer spurious overflows; a genuine 17-distinct-revival
        overflow still overflows — the cap's protective role is intact). ── *)
  Theorem dedup_never_longer : forall l, length (dedup_by l) <= length l.
  Proof.
    induction l as [| x r IH]; simpl.
    - lia.
    - destruct (existsb (consumed_eqb x) (dedup_by r)); simpl; lia.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
     ROOT-B (2026-06-27): the source-committed delegate collection dispatch.
     The ROOT-B fix routes a multi-length lex-ambiguous collection open (`{|`)
     INSIDE its CrossCatDelegate to the SINGLE source-collection arm (one
     consumed-Op snapshot stream) instead of re-projecting across ~6 numeric
     cats (the SnapshotDuplicate storm that tipped saturated keys past
     MAX_WORKER_SNAPSHOTS_PER_KEY). When every snapshot of the dispatch shares
     the consumed Op (one arm), the consumed-key dedup collapses them to ≤ 1,
     hence ≤ cap for any cap ≥ 1 — no snapshot explosion.
     ════════════════════════════════════════════════════════════════════════ *)

  (* Every snapshot of a single source-collection dispatch shares the consumed
     observation (the same inner_state/output_cat/pending_packing_weight of the
     one cat-14 arm). *)
  Definition all_same_consumed (l : list Snapshot) : Prop :=
    forall a b, In a l -> In b l -> consumed_eqb a b = true.

  (* A consumed-uniform snapshot stream dedups to AT MOST ONE slot. *)
  Lemma dedup_all_same_consumed_le_one :
    forall l, all_same_consumed l -> length (dedup_by l) <= 1.
  Proof.
    induction l as [| x r IH]; intro Hall; simpl.
    - lia.
    - destruct (existsb (consumed_eqb x) (dedup_by r)) eqn:E.
      + apply IH. unfold all_same_consumed in *. intros a b Ha Hb.
        apply Hall; right; assumption.
      + (* x is kept; show dedup_by r = [] so the result has length 1. *)
        assert (Hr : dedup_by r = []).
        { destruct (dedup_by r) as [| y r'] eqn:Edr; [reflexivity |].
          exfalso.
          assert (Hyd : In y (dedup_by r)). { rewrite Edr. left. reflexivity. }
          assert (Hyr : In y r). { apply dedup_included. exact Hyd. }
          assert (Hxy : consumed_eqb x y = true).
          { apply Hall; [left; reflexivity | right; exact Hyr]. }
          assert (Hex : existsb (consumed_eqb x) (dedup_by r) = true).
          { apply existsb_exists. exists y. split; [exact Hyd | exact Hxy]. }
          (* `destruct (dedup_by r) eqn:Edr` rewrote E to the `y :: r'` form;
             Edr bridges Hex (dedup_by r form) and E for congruence. *)
          congruence. }
        rewrite Hr. simpl. lia.
  Qed.

  (* The cap obligation: a source-committed delegate collection dispatch never
     exceeds the per-key snapshot cap (cap ≥ 1). Bounded — no explosion. *)
  Theorem delegate_collection_dispatch_snapshots_le_cap :
    forall l cap,
      all_same_consumed l -> 1 <= cap -> length (dedup_by l) <= cap.
  Proof.
    intros l cap Hall Hcap.
    apply Nat.le_trans with (m := 1).
    - apply dedup_all_same_consumed_le_one. exact Hall.
    - exact Hcap.
  Qed.

End CohortSnapshotObservationalDedup.

(* ═════════════════ Assumption audit (ROOT-B extension) — must print
   "Closed under the global context" ═════════════════ *)
Print Assumptions delegate_collection_dispatch_snapshots_le_cap.
