(*
 * CastCompareFrontierBound: a FAITHFUL operational model of the Phase 5A
 * cast-then-compare problem, ENRICHED with the dimension an earlier, too-abstract
 * model missed — a lane's RETURN CONTEXT (the category its continuation/return
 * frame can HOST as a result). Working backwards from THIS model rules out the
 * wrong fix at design time and characterizes the correct one.
 *
 * THE BUG (PROVEN via instrumented PRATTAIL_TRACE=actions of `3==3` vs `int(3)==3`):
 *   A category-changing infix `op : C -> D` (e.g. EqInt: source Int=C, result
 *   Bool=D) is admitted by the InfixLoop guard only when the operand cursor
 *   carries cross-cat-LHS evidence Some(C). When it fires, it produces a value of
 *   the RESULT category D. That value is ACCEPTED (wrappable to a root) ONLY if
 *   the firing cursor's return frame can host a D — i.e. its RETURN CONTEXT is D.
 *   - LITERAL `3 == 3`: the Int LHS is parsed by the Bool-EqInt cross-cat-LHS
 *     DELEGATE — a cursor DISPATCHED BY Bool, so its return context is Bool=D.
 *     EqInt fires ⇒ Bool, hosted by the Bool context ⇒ wrapped to a Proc root
 *     (`ProcBool`) ⇒ accepted. (Trace: `Symbol(nt=0, span=[0,3])` ×4 — the Proc
 *     root EXISTS.)
 *   - CAST `int(3) == 3`: the cast result `int(3)` (an Int) reaches the same `==`
 *     guard, but on the TOP-LEVEL Int-parse cursor, whose return context is
 *     Int=C, NOT Bool=D. If EqInt is admitted there, it fires ⇒ Bool, but the
 *     Int return context CANNOT host a Bool ⇒ the Bool is ORPHANED ⇒ NO Proc root
 *     ⇒ EOI-acceptance empty ⇒ longest-prefix salvage. (Trace: `Symbol(nt=7,
 *     span=[0,6])` ×25 — the Bool EXISTS — but NO `Symbol(nt=0, span=[0,6])` —
 *     the root wrap FAILS.)
 *
 * WHY THE "RECOGNIZE THE INT-PARSE CAST CURSOR" FIX (approach A) IS UNSOUND:
 *   Admitting EqInt on the Int-context cast cursor produces an ORPHANED Bool
 *   (return context Int <> result Bool). The model below PROVES this (Orphaned,
 *   frontier does NOT accept), reproducing the empirical col-4 failure — so the
 *   model now rejects the design that the abstract model wrongly endorsed.
 *
 * THE CORRECT REQUIREMENT (derived, to be implemented next):
 *   The cast result must be produced by a cursor whose RETURN CONTEXT is the
 *   infix RESULT category D — i.e. the cast must be parsed AS the Int LHS of the
 *   Bool-EqInt delegate (return context Bool), exactly as the literal is. The
 *   model PROVES such a delegate lane is Hosted (accepted), and that acceptance
 *   NECESSARILY requires a lane with return context D. The remaining engineering
 *   problem — making the Bool-EqInt delegate parse the cast `int(3)` as its Int
 *   LHS WITHOUT the dispatch-time fan-out (2^depth, falsified) — is bounded by
 *   the same frontier-size argument retained below.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *
 * ★ DIVERGENCE-I RE-CHECK (2026-07-25). Closing divergence I partitioned
 * RhoCalc's/Calculator's integer LITERAL domains (`BigInt`'s eval was a
 * universal acceptor of every integer spelling). That STRICTLY SHRINKS the
 * literal cohort at every token shape — proved, not assumed, as
 * `LiteralCarrierContextIndependence.T_CohortShrinks`, with the a-fortiori step
 * for any cohort-size-monotone bound as `T_CohortBoundsHoldAFortiori`. The
 * bounds below are cohort-size monotone, so they hold A FORTIORI; nothing in
 * this file needed to change. ⚠ Note what does NOT hold and is deliberately not
 * claimed: per-CATEGORY containment. The new `Int` domain accepts `5u32`, which
 * the old one refused outright (`parse_int_lit(text, Some(I64))` rejects a
 * mismatched fixed suffix); it is the cohort's SIZE that is non-increasing.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Section CastCompareFrontierBound.

  Inductive EdgeKind : Type :=
    | Generic
    | CrossCatLhs (src : nat)
    | CrossCatLhsReentry (src : nat)
    | CrossCatProjection (src : nat).

  Inductive Ctrl : Type := CInfix | CUnwind.

  (* A LANE = one cursor at the infix position. ln_return_cat is the category its
     continuation / return frame can HOST as a result (the dimension the earlier
     model lacked). *)
  Record Lane : Type := mkLane {
    ln_cat : nat;          (* the operand category on the lane's GSS top *)
    ln_edge : EdgeKind;    (* incoming GSS edge *)
    ln_ctrl : Ctrl;        (* reaches the InfixLoop guard? *)
    ln_cast_origin : bool; (* SPPF top is a cast/cross-category-prefix result *)
    ln_return_cat : nat    (* category the return frame can HOST *)
  }.

  (* cross-cat-LHS evidence: edge (delegate) OR cast-origin (a complete C value). *)
  Definition evidence (l : Lane) : option nat :=
    match ln_edge l with
    | CrossCatLhs s | CrossCatLhsReentry s =>
        if Nat.eqb s (ln_cat l) then Some s else None
    | Generic => if ln_cast_origin l then Some (ln_cat l) else None
    | CrossCatProjection _ => None
    end.

  (* Firing a category-changing infix (source s, RESULT d) on a lane has three
     outcomes — the KEY enrichment:
       Suppressed : the guard rejects (no evidence, or not in InfixLoop, or source
                    mismatch) — the infix never fires;
       Orphaned   : the infix FIRES (evidence + source match) but the lane's RETURN
                    CONTEXT <> d, so the produced result cannot be hosted/wrapped
                    to a root (the `int(3)==3` Bool-with-no-Proc-root failure);
       Hosted     : the infix fires AND the return context = d, so the result is
                    accepted. *)
  Inductive FireOutcome : Type := Suppressed | Orphaned | Hosted.

  Definition fire_infix (s d : nat) (l : Lane) : FireOutcome :=
    match ln_ctrl l with
    | CUnwind => Suppressed
    | CInfix =>
        match evidence l with
        | Some e =>
            if Nat.eqb e s
            then (if Nat.eqb (ln_return_cat l) d then Hosted else Orphaned)
            else Suppressed
        | None => Suppressed
        end
    end.

  (* A lane ACCEPTS the infix iff firing it is Hosted (Orphaned does NOT accept —
     this is what the abstract model got wrong). *)
  Definition lane_hosts (s d : nat) (l : Lane) : bool :=
    match fire_infix s d l with Hosted => true | _ => false end.

  Definition frontier_accepts (s d : nat) (f : list Lane) : bool :=
    existsb (lane_hosts s d) f.

  (* ===== THE HOSTING LAW (the enrichment, the crux) ===== *)

  (* A fired infix is ACCEPTED only if the firing lane's return context equals the
     infix RESULT category. This is the law the earlier model omitted. *)
  Theorem hosting_requires_return_cat :
    forall s d l, fire_infix s d l = Hosted -> ln_return_cat l = d.
  Proof.
    intros s d l H. unfold fire_infix in H.
    destruct (ln_ctrl l); [| discriminate H].
    destruct (evidence l) as [e|]; [| discriminate H].
    destruct (Nat.eqb e s); [| discriminate H].
    destruct (Nat.eqb (ln_return_cat l) d) eqn:E; [| discriminate H].
    apply Nat.eqb_eq in E. exact E.
  Qed.

  (* Acceptance of the frontier NECESSARILY exhibits a lane whose return context is
     the result category d — so NO frontier all of whose lanes return <> d can ever
     accept a category-changing infix into d. *)
  Theorem accept_requires_result_context :
    forall s d f, frontier_accepts s d f = true -> exists l, In l f /\ ln_return_cat l = d.
  Proof.
    intros s d f H. unfold frontier_accepts in H.
    apply existsb_exists in H. destruct H as [l [Hin Hh]].
    exists l. split; [exact Hin |].
    unfold lane_hosts in Hh.
    destruct (fire_infix s d l) eqn:E; try discriminate Hh.
    apply (hosting_requires_return_cat s d l E).
  Qed.

  (* ===== the cast operand's lanes, GROUNDED in the trace ===== *)
  (* cast result cat c (Int); infix source = c, infix RESULT d (Bool), d <> c. *)

  (* APPROACH A (falsified): recognize the TOP-LEVEL Int-parse cast cursor. Its
     return context is c (Int) — it was parsing an Int. cast_origin=true ⇒ evidence
     Some(c). *)
  Definition cast_recognized_lane (c : nat) : Lane := mkLane c Generic CInfix true c.
  (* The catch-all Proc-injection lane: unwinds. *)
  Definition proc_inject_lane (c proc : nat) : Lane :=
    mkLane proc (CrossCatProjection c) CUnwind false proc.
  (* THE CORRECT lane: the cast parsed AS the Bool-EqInt delegate's Int LHS — a
     cursor dispatched BY Bool, so return context d (Bool); evidence via the
     delegate reentry edge. This is also exactly the LITERAL's admitting lane. *)
  Definition delegate_lane (c d : nat) : Lane := mkLane c (CrossCatLhsReentry c) CInfix false d.

  Definition frontier_approach_a (c proc : nat) : list Lane :=
    [ cast_recognized_lane c ; proc_inject_lane c proc ].
  Definition frontier_delegate (c d proc : nat) : list Lane :=
    [ delegate_lane c d ; proc_inject_lane c proc ].

  (* ===== approach A is UNSOUND: it ORPHANS the result ===== *)

  (* The recognized Int-context cast lane FIRES EqInt but is ORPHANED (return cat
     c=Int cannot host the result d=Bool). *)
  Theorem approach_a_orphaned :
    forall c d, d <> c -> fire_infix c d (cast_recognized_lane c) = Orphaned.
  Proof.
    intros c d Hne. unfold fire_infix, cast_recognized_lane, evidence; cbn.
    rewrite Nat.eqb_refl.
    destruct (Nat.eqb c d) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - reflexivity.
  Qed.

  (* Therefore the approach-A frontier does NOT accept — modeling the empirical
     `int(3)==3` failure (Bool produced, but no Proc root, so EOI-accept empty). *)
  Theorem approach_a_rejects :
    forall c d proc, d <> c -> frontier_accepts c d (frontier_approach_a c proc) = false.
  Proof.
    intros c d proc Hne.
    assert (Ha : lane_hosts c d (cast_recognized_lane c) = false).
    { unfold lane_hosts. rewrite (approach_a_orphaned c d Hne). reflexivity. }
    assert (Hb : lane_hosts c d (proc_inject_lane c proc) = false).
    { unfold lane_hosts, fire_infix, proc_inject_lane; cbn. reflexivity. }
    unfold frontier_accepts, frontier_approach_a, existsb.
    rewrite Ha, Hb. reflexivity.
  Qed.

  (* ===== the CORRECT requirement: a result-context (delegate) lane HOSTS ===== *)

  Theorem delegate_hosted : forall c d, fire_infix c d (delegate_lane c d) = Hosted.
  Proof.
    intros c d. unfold fire_infix, delegate_lane, evidence; cbn.
    repeat (rewrite Nat.eqb_refl; cbn). reflexivity.
  Qed.

  Theorem frontier_delegate_accepts :
    forall c d proc, frontier_accepts c d (frontier_delegate c d proc) = true.
  Proof.
    intros c d proc. unfold frontier_accepts. rewrite existsb_exists.
    exists (delegate_lane c d). split.
    - unfold frontier_delegate. simpl. left. reflexivity.
    - unfold lane_hosts. rewrite (delegate_hosted c d). reflexivity.
  Qed.

  (* The literal's admitting lane IS the delegate lane (return context = result
     cat), so `3==3` works for the same reason the correct cast fix must. *)
  Theorem literal_accepts : forall c d proc, frontier_accepts c d (frontier_delegate c d proc) = true.
  Proof. exact frontier_delegate_accepts. Qed.

  (* SOUNDNESS: the delegate frontier accepts ONLY the result cat's own infix
     source — i.e. accepting source s forces s = c (the cast/operand cat). *)
  Theorem delegate_sound :
    forall s d c proc, frontier_accepts s d (frontier_delegate c d proc) = true -> s = c.
  Proof.
    intros s d c proc H.
    unfold frontier_accepts, frontier_delegate, existsb,
           lane_hosts, fire_infix, delegate_lane, proc_inject_lane, evidence in H.
    cbn in H. rewrite Nat.eqb_refl in H. cbn in H.
    destruct (Nat.eqb c s) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - cbn in H. discriminate H.
  Qed.

  (* ===== boundedness: the correct fix must add lanes LINEARLY, not 2^depth ===== *)
  (* The delegate fix adds one delegate lane per cast result (post-resolution, no
     re-dispatch of inner content) — LINEAR. The falsified dispatch-time
     fall-through routes each cast TOKEN through the delegate before resolution,
     re-dispatching inner content multiplicatively (>= 2^depth). *)

  Definition size_delegate (d : nat) : nat := 2 * d + d.  (* base + 1 delegate per level *)
  Fixpoint size_fallthrough (n : nat) : nat :=
    match n with O => 1 | S n' => 2 * size_fallthrough n' end.

  Theorem delegate_linear : forall n, size_delegate n <= 3 * n.
  Proof. intro n. unfold size_delegate. lia. Qed.

  Theorem fallthrough_exponential : forall n, size_fallthrough n = 2 ^ n.
  Proof.
    induction n as [|n IH]; simpl.
    - reflexivity.
    - rewrite IH. lia.
  Qed.

  Lemma pow2_pos : forall n, 1 <= 2 ^ n.
  Proof. induction n; simpl; lia. Qed.

  Lemma n_lt_2pow : forall n, n < 2 ^ n.
  Proof. induction n as [|n IH]; simpl; [lia |]. pose proof (pow2_pos n). lia. Qed.

  Theorem fallthrough_unbounded : forall B, exists n, B < size_fallthrough n.
  Proof.
    intro B. exists (S B). rewrite fallthrough_exponential.
    pose proof (n_lt_2pow (S B)). lia.
  Qed.

  Lemma three_d_lt_pow2 : forall n, 4 <= n -> 3 * n < 2 ^ n.
  Proof.
    induction n as [|n IH]; intro H.
    - lia.
    - destruct (Nat.le_gt_cases 4 n) as [Hle|Hgt].
      + specialize (IH Hle). replace (2 ^ S n) with (2 * 2 ^ n) by (simpl; lia). lia.
      + assert (n = 3) by lia. subst. simpl. lia.
  Qed.

  Theorem fix_bounded_fallthrough_explodes :
    forall n, 4 <= n -> size_delegate n < size_fallthrough n.
  Proof.
    intros n Hn. rewrite fallthrough_exponential. unfold size_delegate.
    replace (2 * n + n) with (3 * n) by lia.
    apply three_d_lt_pow2; exact Hn.
  Qed.

  (* Ambiguity preservation: the Proc-injection lane survives in the delegate
     frontier (the fix only ADDS the delegate lane). *)
  Theorem delegate_preserves_proc_lane :
    forall c d proc, In (proc_inject_lane c proc) (frontier_delegate c d proc).
  Proof.
    intros c d proc. unfold frontier_delegate. simpl. right. left. reflexivity.
  Qed.

End CastCompareFrontierBound.
