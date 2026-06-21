(*
 * RecoveryAcceptCoverage: the soundness invariant of the recovery
 * accept-coverage guard (commit e59f50af, "reject recovery accepts that
 * discarded the leading input").
 *
 * THE DEFECT (git-bisected to 30acf6de). 30acf6de's broadened logical-EOI
 * admission let a RECOVERY cursor that DELETED an un-parseable leading prefix
 * reach `WpdaState::Accepted` at logical EOI with an SPPF root spanning only a
 * SUFFIX of the input. For `1 + + 2` (no sync token to skip to), recovery
 * deleted `1 + +` and accepted a bare `NumLit(2)` whose root span is [3,4],
 * not [0,4]; the recovering facade then surfaced `Some(NumLit(2))` with no
 * error instead of the correct `None`.
 *
 * THE FIX (this spec; `push_eoi_resolution_candidate` +
 * `accept_root_covers_input_start`, prattail/src/wpda_walker.rs):
 *   reject a logical-EOI candidate when
 *     recovery_depth > 0  AND  NOT (root covers the input start),
 *   where "root covers the input start" ⇔ the root's `span_lo` shares the
 *   `position_order_key` of position 0 (the logical START where every walk
 *   begins). Non-recovery accepts (recovery_depth == 0) are NEVER rejected, so
 *   grouping (a root whose span legitimately starts after a leading `(`, e.g.
 *   `(1)` → [1,2]) and genuine in-stream repairs are untouched. `SPPF_ID_NONE`
 *   and span-less roots stay PERMISSIVE (no span evidence to refute).
 *
 * `position_order_key` makes the comparison correct for BOTH linear token
 * sources (key == token index) and DAG-backed lattice sources (key == byte
 * position).
 *
 * WHAT IS PROVED (zero-admission; no Axiom / Admitted / admit):
 *
 *   THE COMPLETE-PARSE INVARIANT. A complete parse of an input consumes the
 *   WHOLE input; its SPPF root span therefore starts at the logical start
 *   (position-0 order-key) and ends at logical EOI. We model "complete parse"
 *   as a root whose span covers [start_key, eoi]. The guard's job is to admit
 *   exactly the complete-coverage logical-EOI accepts.
 *
 *   T1 guard_rejects_only_non_covering_recovery : the guard rejects a
 *      candidate ONLY when it is a recovery accept (depth > 0) whose root does
 *      not cover the start — i.e. it never rejects a covering accept and never
 *      rejects a non-recovery accept.
 *   T2 rejected_is_not_complete_parse : every candidate the guard rejects is
 *      NOT a complete parse (its root discarded a leading prefix), so
 *      rejecting it removes no complete parse — SOUNDNESS of the rejection.
 *   T3 complete_parse_is_admitted : every complete-coverage candidate is
 *      ADMITTED by the guard (no-loss: the guard never drops a complete
 *      parse), whether or not recovery happened.
 *   T4 non_recovery_always_admitted : a non-recovery candidate
 *      (recovery_depth == 0) is ALWAYS admitted (grouping / in-stream repairs
 *      untouched; the `(1)`→[1,2] grouping case).
 *   T5 spanless_root_admitted : a span-less / SPPF_ID_NONE root is admitted
 *      (permissive — no span evidence to refute).
 *   T6 defect_witness_rejected : the `1 + + 2` defect — a recovery accept with
 *      root span starting at key 3 ≠ start key 0 — IS rejected (non-vacuity).
 *   T7 grouping_witness_admitted : the `(1)`→[1,2] grouping case — a
 *      NON-recovery accept whose root starts after a leading `(` — is admitted
 *      (the guard does not over-reject; this is why the guard is gated on
 *      recovery_depth > 0).
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Section RecoveryAcceptCoverage.

  (* `position_order_key`: a monotone key on input positions. For linear
     sources it is the token index; for lattice sources, the byte position.
     We model it as an abstract function `pos_key : nat -> option nat` (None
     when the position has no order key — the permissive fallback the Rust
     code takes when `position_order_key` returns None). *)
  Variable pos_key : nat -> option nat.

  (* The SPPF root candidate at logical EOI. `root_span_lo` is `span_lo root`
     when the root has an intrinsic span; `None` models SPPF_ID_NONE or a
     span-less root (CollectionId / Predicate root). *)
  Record eoi_candidate : Type := {
    cand_recovery_depth : nat;          (* variant.recovery_depth *)
    cand_root_span_lo   : option nat    (* sppf.span_lo root, or None *)
  }.

  (* ── `accept_root_covers_input_start` (the new helper). ─────────────── *)
  (*
     fn accept_root_covers_input_start(root, tokens) -> bool:
       if root == SPPF_ID_NONE { return true }            (* permissive *)
       let Some(span_lo) = sppf.span_lo(root) else { return true }  (* perm *)
       match (pos_key span_lo, pos_key 0) with
       | (Some lo_key, Some start_key) => lo_key == start_key
       | _ => true                                          (* permissive *)
  *)
  Definition accept_root_covers_input_start (cand : eoi_candidate) : bool :=
    match cand_root_span_lo cand with
    | None => true                                  (* SPPF_ID_NONE / no span *)
    | Some span_lo =>
        match pos_key span_lo, pos_key 0 with
        | Some lo_key, Some start_key => Nat.eqb lo_key start_key
        | _, _ => true                              (* permissive fallback *)
        end
    end.

  (* ── The guard in `push_eoi_resolution_candidate`. The candidate is
        ADMITTED unless (recovery_depth > 0 AND NOT covers-start). ── *)
  Definition guard_admits (cand : eoi_candidate) : bool :=
    negb (Nat.ltb 0 (cand_recovery_depth cand))   (* recovery_depth == 0 *)
    || accept_root_covers_input_start cand.        (* OR covers the start *)

  (* The Rust `continue` (reject) condition: recovery_depth > 0 && !covers. *)
  Definition guard_rejects (cand : eoi_candidate) : bool :=
    Nat.ltb 0 (cand_recovery_depth cand)
    && negb (accept_root_covers_input_start cand).

  (* admits = ¬rejects (the guard is a single branch). *)
  Lemma admits_iff_not_rejects :
    forall cand, guard_admits cand = negb (guard_rejects cand).
  Proof.
    intro cand. unfold guard_admits, guard_rejects.
    rewrite negb_andb. rewrite negb_involutive. reflexivity.
  Qed.

  (* ── The COMPLETE-PARSE coverage predicate. A complete parse of the input
        covers it from the logical start: its root span_lo has the SAME
        order-key as position 0. (Plus it has an intrinsic span; a span-less
        root carries no coverage evidence — handled separately, permissive.) ── *)
  Definition covers_input_start (cand : eoi_candidate) : Prop :=
    exists span_lo lo_key start_key,
      cand_root_span_lo cand = Some span_lo /\
      pos_key span_lo = Some lo_key /\
      pos_key 0 = Some start_key /\
      lo_key = start_key.

  (* A "complete parse" candidate: it has a covering root (the realize-layer
     covering-span check + the start-coverage). The fix admits exactly these
     among RECOVERY accepts, and ALL non-recovery accepts. *)
  Definition complete_parse (cand : eoi_candidate) : Prop :=
    covers_input_start cand.

  (* ── Bridge: the boolean helper reflects `covers_input_start` WHEN the root
        has a span and both keys exist. (Off that case the helper is
        permissive-true, which is sound — see T5.) ── *)
  Lemma covers_helper_true_of_covers :
    forall cand,
      covers_input_start cand ->
      accept_root_covers_input_start cand = true.
  Proof.
    intros cand [span_lo [lo_key [start_key [Hlo [Hk0lo [Hk00 Heq]]]]]].
    unfold accept_root_covers_input_start.
    rewrite Hlo. rewrite Hk0lo. rewrite Hk00.
    apply Nat.eqb_eq. exact Heq.
  Qed.

  (* And the converse on the evidenced case: if the helper is true AND the
     root has a span AND both keys exist, then it genuinely covers the start.
     (This is what makes the rejection of a NON-covering recovery accept
     correct: helper = false there.) *)
  Lemma covers_of_helper_true_evidenced :
    forall cand span_lo lo_key start_key,
      cand_root_span_lo cand = Some span_lo ->
      pos_key span_lo = Some lo_key ->
      pos_key 0 = Some start_key ->
      accept_root_covers_input_start cand = true ->
      covers_input_start cand.
  Proof.
    intros cand span_lo lo_key start_key Hlo Hk0lo Hk00 Hhelp.
    unfold accept_root_covers_input_start in Hhelp.
    rewrite Hlo, Hk0lo, Hk00 in Hhelp.
    exists span_lo, lo_key, start_key.
    repeat split; try assumption.
    apply Nat.eqb_eq. exact Hhelp.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T1 — the guard rejects ONLY a non-covering RECOVERY accept. It never
     rejects a covering accept, and never rejects a non-recovery accept.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem guard_rejects_only_non_covering_recovery :
    forall cand,
      guard_rejects cand = true ->
      cand_recovery_depth cand > 0 /\
      accept_root_covers_input_start cand = false.
  Proof.
    intros cand H. unfold guard_rejects in H.
    apply andb_true_iff in H. destruct H as [Hdepth Hcov].
    split.
    - apply Nat.ltb_lt in Hdepth. exact Hdepth.
    - apply negb_true_iff in Hcov. exact Hcov.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T2 — SOUNDNESS of the rejection: every candidate the guard REJECTS is
     NOT a complete parse. (Its root does not cover the input start ⇒ it
     discarded a leading prefix ⇒ not complete.) Rejecting it removes no
     complete parse.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem rejected_is_not_complete_parse :
    forall cand,
      guard_rejects cand = true ->
      ~ complete_parse cand.
  Proof.
    intros cand Hrej Hcomp.
    apply guard_rejects_only_non_covering_recovery in Hrej.
    destruct Hrej as [_ Hcovfalse].
    (* complete_parse ⇒ covers_input_start ⇒ helper = true, contradicting
       helper = false. *)
    apply covers_helper_true_of_covers in Hcomp.
    rewrite Hcomp in Hcovfalse. discriminate.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T3 — NO-LOSS: every COMPLETE parse is ADMITTED by the guard (whether or
     not recovery happened). The guard never drops a complete parse.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem complete_parse_is_admitted :
    forall cand,
      complete_parse cand ->
      guard_admits cand = true.
  Proof.
    intros cand Hcomp. unfold guard_admits.
    apply orb_true_iff. right.
    apply covers_helper_true_of_covers. exact Hcomp.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T4 — a NON-recovery candidate (recovery_depth == 0) is ALWAYS admitted:
     grouping (root starting after a leading `(`) and genuine in-stream
     repairs are untouched. This is the precise reason the guard is gated on
     `recovery_depth > 0`.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem non_recovery_always_admitted :
    forall cand,
      cand_recovery_depth cand = 0 ->
      guard_admits cand = true.
  Proof.
    intros cand Hdepth. unfold guard_admits.
    apply orb_true_iff. left.
    rewrite Hdepth. reflexivity.
  Qed.

  (* And dually, a non-recovery candidate is NEVER rejected. *)
  Corollary non_recovery_never_rejected :
    forall cand,
      cand_recovery_depth cand = 0 ->
      guard_rejects cand = false.
  Proof.
    intros cand Hdepth. unfold guard_rejects.
    rewrite Hdepth. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T5 — a SPAN-LESS / SPPF_ID_NONE root is admitted (permissive: no span
     evidence to refute a deleted leading prefix; legacy empty-root accept
     path preserved).
     ════════════════════════════════════════════════════════════════════ *)
  Theorem spanless_root_admitted :
    forall cand,
      cand_root_span_lo cand = None ->
      guard_admits cand = true.
  Proof.
    intros cand Hnone. unfold guard_admits.
    apply orb_true_iff. right.
    unfold accept_root_covers_input_start. rewrite Hnone. reflexivity.
  Qed.

  (* The permissive missing-key fallback is also admitted (either key None). *)
  Theorem missing_key_admitted :
    forall cand span_lo,
      cand_root_span_lo cand = Some span_lo ->
      (pos_key span_lo = None \/ pos_key 0 = None) ->
      guard_admits cand = true.
  Proof.
    intros cand span_lo Hlo Hkey. unfold guard_admits.
    apply orb_true_iff. right.
    unfold accept_root_covers_input_start. rewrite Hlo.
    destruct Hkey as [Hk | Hk]; rewrite Hk;
      [ reflexivity
      | destruct (pos_key span_lo); reflexivity ].
  Qed.

End RecoveryAcceptCoverage.

(* ════════════════════════════════════════════════════════════════════════
   DEFECT + GROUPING WITNESSES (non-vacuity): concrete finite instantiations.
   We use a LINEAR token source, so `pos_key = Some` (identity-ish): the order
   key of position p is just p (token index). `pos_key 0 = Some 0` (start).
   ════════════════════════════════════════════════════════════════════════ *)

Section Witnesses.

  (* Linear source: position p has order key p. *)
  Definition linear_key (p : nat) : option nat := Some p.

  (* ── T6 — THE DEFECT (`1 + + 2`). After recovery DELETED `1 + +`, the
        accept's root is a bare `NumLit(2)` whose span_lo = 3 (order key 3),
        with recovery_depth = 1 (> 0). The start key is 0. 3 ≠ 0 ⇒ the root
        does NOT cover the start ⇒ the guard REJECTS it. (Pre-fix it was
        admitted and surfaced `Some(NumLit(2))` instead of `None`.) ── *)
  Definition defect_candidate : eoi_candidate :=
    {| cand_recovery_depth := 1; cand_root_span_lo := Some 3 |}.

  Theorem defect_witness_rejected :
    guard_rejects linear_key defect_candidate = true.
  Proof.
    unfold guard_rejects, accept_root_covers_input_start, defect_candidate,
      linear_key. simpl. reflexivity.
  Qed.

  (* And it is correspondingly NOT admitted. *)
  Theorem defect_witness_not_admitted :
    guard_admits linear_key defect_candidate = false.
  Proof.
    unfold guard_admits, accept_root_covers_input_start, defect_candidate,
      linear_key. simpl. reflexivity.
  Qed.

  (* The defect candidate is genuinely NOT a complete parse (span_lo key 3 ≠
     start key 0), so the rejection drops nothing valid. *)
  Theorem defect_candidate_not_complete :
    ~ complete_parse linear_key defect_candidate.
  Proof.
    apply rejected_is_not_complete_parse.
    exact defect_witness_rejected.
  Qed.

  (* ── T7 — THE GROUPING CASE (`(1)` → root span [1,2]). A NON-recovery
        accept (recovery_depth = 0) whose root starts at position 1 (after the
        leading `(`). Its span_lo key (1) ≠ start key (0) — so it does NOT
        "cover the start" by the literal span test — BUT because it is a
        non-recovery accept, the guard ADMITS it. This is exactly why the
        guard is gated on recovery_depth > 0: the leading `(` is CONSUMED
        (grouping), not DELETED (recovery). ── *)
  Definition grouping_candidate : eoi_candidate :=
    {| cand_recovery_depth := 0; cand_root_span_lo := Some 1 |}.

  Theorem grouping_witness_admitted :
    guard_admits linear_key grouping_candidate = true.
  Proof.
    unfold guard_admits, grouping_candidate. simpl. reflexivity.
  Qed.

  Theorem grouping_witness_not_rejected :
    guard_rejects linear_key grouping_candidate = false.
  Proof.
    unfold guard_rejects, grouping_candidate. simpl. reflexivity.
  Qed.

  (* ── A covering RECOVERY accept (in-stream repair: recovery happened but
        the root still spans from the start, span_lo key 0) IS admitted — the
        guard only refutes recovery accepts that DISCARDED the LEADING input,
        not genuine in-stream repairs. ── *)
  Definition instream_repair_candidate : eoi_candidate :=
    {| cand_recovery_depth := 2; cand_root_span_lo := Some 0 |}.

  Theorem instream_repair_admitted :
    guard_admits linear_key instream_repair_candidate = true.
  Proof.
    unfold guard_admits, accept_root_covers_input_start,
      instream_repair_candidate, linear_key. simpl. reflexivity.
  Qed.

  (* And it IS a complete parse (covers the start). *)
  Theorem instream_repair_complete :
    complete_parse linear_key instream_repair_candidate.
  Proof.
    unfold complete_parse, covers_input_start, instream_repair_candidate,
      linear_key. simpl.
    exists 0, 0, 0. repeat split.
  Qed.

End Witnesses.

(* ════════════════════════════════════════════════════════════════════════
   ASSUMPTION AUDIT.
   ════════════════════════════════════════════════════════════════════════ *)

Print Assumptions guard_rejects_only_non_covering_recovery.
Print Assumptions rejected_is_not_complete_parse.
Print Assumptions complete_parse_is_admitted.
Print Assumptions non_recovery_always_admitted.
Print Assumptions spanless_root_admitted.
Print Assumptions missing_key_admitted.
Print Assumptions defect_witness_rejected.
Print Assumptions defect_candidate_not_complete.
Print Assumptions grouping_witness_admitted.
Print Assumptions instream_repair_admitted.
Print Assumptions instream_repair_complete.
