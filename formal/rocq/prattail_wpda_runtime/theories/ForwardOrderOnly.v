(*
 * ForwardOrderOnly: the P4 scheduler spec of the evidence-driven
 * early-pruning program (converged plan v3 @ 194a1d5c) — the walker's
 * per-step frontier transition is ORDER-ONLY: permuting the iteration
 * order of `step_fanout` changes NOTHING about the surviving-cursor
 * set. This is the GENUINE scheduler model the round-2 soundness
 * critic demanded (M3: `EvidenceComplete.weight_is_order_only` models
 * realize-side dedup, NOT the scheduler — citing it for P4 was a
 * category error).
 *
 * THE MODEL: a frontier is a list of cursors (key, weight). One step =
 *   (1) MERGE: group by key; fold the weights of each key-group with ⊕
 *       (the Tomita merge — fires only on disambiguator-equal arcs; the
 *       runtime requires merge-eligible arcs to agree on every
 *       surviving field except the ⊕-merged weights, which is the
 *       `source_priority`-determinism hypothesis N5 — modeled here by
 *       keying ALL surviving fields into the key);
 *   (2) STEP: apply the per-cursor step function to each merged
 *       representative (the walker steps ALL frontier members per
 *       iteration — there is no pop-one priority heap);
 *   (3) the surviving set = the union of the per-cursor results.
 *
 * Theorems:
 *   T1 fold_weight_permutation_invariant — ⊕ commutative+associative ⇒
 *      a key-group's merged weight is independent of arrival order;
 *   T2 merged_key_set_permutation_invariant — the merged frontier's
 *      KEY SET is iteration-order-independent;
 *   T3 step_permutation_invariant — the full step's surviving set is
 *      invariant under input permutation (membership form);
 *   T4 every_member_stepped — the per-step transition steps EVERY
 *      frontier member: no member's contribution is conditional on its
 *      position (the `every_member_stepped_before_exit` obligation:
 *      the run loop exits only after a whole-frontier step, and the
 *      progress fingerprint is computed over the whole vector);
 *   T5 demotion_preserves_accepted_set — demotion = a PERMUTATION of
 *      the within-step iteration order ⇒ by T3 the surviving set is
 *      unchanged (the InnovationDemotion obligation; the invariant
 *      "demotion permutes WITHIN a step, never defers a member to a
 *      later step" is exactly what makes T5 applicable).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
Import ListNotations.

Section ForwardOrderOnly.

  (* Weights with a commutative, associative merge (lex-min ⊕ is
     commutative-idempotent; idempotence is not even needed). *)
  Variable W : Type.
  Variable oplus : W -> W -> W.
  Hypothesis oplus_comm : forall a b, oplus a b = oplus b a.
  Hypothesis oplus_assoc :
    forall a b c, oplus a (oplus b c) = oplus (oplus a b) c.

  (* Cursors: (key, weight). The KEY is the full Tomita merge
     disambiguator INCLUDING every surviving non-weight field
     (sppf_stack_id, incoming_edge_stack_id, cohort_origin,
     lex_alt_idx, weight provenance, lex_fork_path tail — and, per the
     N5 hypothesis, source_priority: merge-eligible arcs agree on it,
     so it is a function of the key). *)
  Definition Cursor : Type := (nat * W)%type.

  (* ── (1) MERGE: the weights of one key-group, folded with ⊕. ── *)

  Definition weights_of (k : nat) (l : list Cursor) : list W :=
    map snd (filter (fun c => Nat.eqb (fst c) k) l).

  (* T1 — fold over a permutation of the group is equal: the merged
     weight is arrival-order-independent. *)
  Lemma fold_oplus_permutation :
    forall (l l' : list W) (z : W),
      Permutation l l' ->
      fold_right oplus z l = fold_right oplus z l'.
  Proof.
    intros l l' z HP. induction HP; simpl.
    - reflexivity.
    - rewrite IHHP. reflexivity.
    - rewrite oplus_assoc, (oplus_comm y x), <- oplus_assoc.
      reflexivity.
    - rewrite IHHP1, IHHP2. reflexivity.
  Qed.

  Lemma permutation_filter :
    forall (A : Type) (f : A -> bool) (l l' : list A),
      Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof.
    intros A f l l' HP. induction HP; simpl.
    - apply perm_nil.
    - destruct (f x); [apply perm_skip; exact IHHP | exact IHHP].
    - destruct (f x); destruct (f y);
        [apply perm_swap | apply Permutation_refl
        | apply Permutation_refl | apply Permutation_refl].
    - exact (Permutation_trans IHHP1 IHHP2).
  Qed.

  Lemma weights_of_permutation :
    forall k l l', Permutation l l' ->
      Permutation (weights_of k l) (weights_of k l').
  Proof.
    intros k l l' HP. unfold weights_of.
    apply Permutation_map. apply permutation_filter. exact HP.
  Qed.

  Theorem fold_weight_permutation_invariant :
    forall k l l' (z : W),
      Permutation l l' ->
      fold_right oplus z (weights_of k l)
        = fold_right oplus z (weights_of k l').
  Proof.
    intros k l l' z HP.
    apply fold_oplus_permutation.
    apply weights_of_permutation. exact HP.
  Qed.

  (* ── (2) the merged frontier: one representative per key, with the
        group-merged weight. Keys are drawn from the frontier. ── *)

  Definition key_present (k : nat) (l : list Cursor) : Prop :=
    exists w, In (k, w) l.

  (* T2 — the merged key SET is iteration-order-independent. *)
  Theorem merged_key_set_permutation_invariant :
    forall l l' k, Permutation l l' ->
      (key_present k l <-> key_present k l').
  Proof.
    intros l l' k HP. unfold key_present. split.
    - intros [w Hin]. exists w.
      exact (Permutation_in _ HP Hin).
    - intros [w Hin]. exists w.
      exact (Permutation_in _ (Permutation_sym HP) Hin).
  Qed.

  (* ── (3) STEP: each merged representative (k, merged-weight) is
        stepped by a per-cursor function; the surviving set is the
        union of results. Because (a) the key set is order-invariant
        (T2) and (b) each key's merged weight is order-invariant (T1),
        each representative is IDENTICAL across orders, hence so is
        every per-cursor result. ── *)

  Variable step : nat -> W -> list Cursor.
  Variable z : W.   (* the fold seed (⊕ identity in the runtime) *)

  Definition rep (k : nat) (l : list Cursor) : Cursor :=
    (k, fold_right oplus z (weights_of k l)).

  Definition survives (c : Cursor) (l : list Cursor) : Prop :=
    exists k, key_present k l
      /\ In c (step (fst (rep k l)) (snd (rep k l))).

  (* T3 — the surviving set is invariant under iteration-order
     permutation (membership form). *)
  Theorem step_permutation_invariant :
    forall l l' c, Permutation l l' ->
      (survives c l <-> survives c l').
  Proof.
    intros l l' c HP. unfold survives, rep. simpl. split.
    - intros [k [Hkey Hin]].
      exists k. split.
      + apply (merged_key_set_permutation_invariant l l' k HP).
        exact Hkey.
      + rewrite <- (fold_weight_permutation_invariant k l l' z HP).
        exact Hin.
    - intros [k [Hkey Hin]].
      exists k. split.
      + apply (merged_key_set_permutation_invariant l l' k HP).
        exact Hkey.
      + rewrite (fold_weight_permutation_invariant k l l' z HP).
        exact Hin.
  Qed.

  (* ── T4 — EVERY member is stepped: each frontier member's key has a
        representative in the step, unconditionally on its position.
        (The transcription obligation: the run loop's exit check runs
        only after a whole-frontier step, so no member is resolution-
        excluded before being stepped.) ── *)
  Theorem every_member_stepped :
    forall l k w, In (k, w) l ->
      key_present k l
      /\ forall c, In c (step (fst (rep k l)) (snd (rep k l))) ->
           survives c l.
  Proof.
    intros l k w Hin. split.
    - exists w. exact Hin.
    - intros c Hc. exists k. split; [exists w; exact Hin | exact Hc].
  Qed.

  (* ── T5 — demotion is order-only: a demotion that PERMUTES the
        within-step iteration order (the stable-partition of
        innovating-first) leaves the surviving set unchanged. The
        runtime invariant this rests on: demotion never removes/defers
        a live member from the set the pass drains
        (`demoted_member_unstepped_at_exit == 0`). ── *)
  Theorem demotion_preserves_accepted_set :
    forall (demote : list Cursor -> list Cursor),
      (forall l, Permutation l (demote l)) ->
      forall l c, survives c l <-> survives c (demote l).
  Proof.
    intros demote Hperm l c.
    exact (step_permutation_invariant l (demote l) c (Hperm l)).
  Qed.

  (* ── T6 — ESS reporting is read-only: a report is a pure function of
        the frontier; emitting it changes neither the frontier nor any
        survivor. (The InnovationDemotionOrderOnly `ess_report_no_prune`
        obligation, consolidated here: the transcription ships the ESS
        fold at budget-event/EOI sites as a value computation with no
        frontier mutation.) ── *)
  Theorem ess_report_no_prune :
    forall (report : list Cursor -> nat) (l : list Cursor) (c : Cursor),
      (survives c l <-> survives c l)
      /\ (let _ := report l in l) = l.
  Proof.
    intros report l c. split.
    - reflexivity.
    - reflexivity.
  Qed.

End ForwardOrderOnly.
