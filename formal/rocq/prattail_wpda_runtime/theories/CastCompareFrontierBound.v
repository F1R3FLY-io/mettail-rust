(*
 * CastCompareFrontierBound: the FRONTIER + BOUNDEDNESS refinement of
 * CastResultCrossCatLhsEvidence.v. Together they form the FV derivation of the
 * Phase 5A cast-then-compare fix — worked through in the model BEFORE implementing.
 *
 * WHY THIS FILE EXISTS (the dimension the earlier model missed):
 *   CastResultCrossCatLhsEvidence.v proved that giving a cast LHS a
 *   `CrossCatLhsReentry{C}` edge + InfixLoop control (as a literal gets via the
 *   cross-cat-LHS delegate) makes the C-sourced category-changing infix fire.
 *   But it modeled ONE lane in isolation. When that conclusion was implemented as
 *   "route the cast TOKEN through the delegate at DISPATCH," it was empirically
 *   UNBOUNDED: nested casts `int(float(int(..)))` exploded the cursor frontier
 *   (327 cursors / 10 regressions). The earlier model could not see this because
 *   it did not model the FRONTIER (the SET of cursors the cast produces) nor its
 *   SIZE as a function of nesting depth.
 *
 * GROUNDED FACTS (instrumented PUSH/POP/EVID traces of `int(3)==3` etc.):
 *   At the `==` position the cast operand contributes a SET of lanes (cursors):
 *     - an Int-category parse lane:  (cat=C,    edge=Generic,                 InfixLoop)
 *         reaches the guard but Generic ⇒ evidence None ⇒ EqInt SUPPRESSED;
 *     - a catch-all Proc-injection lane: (cat=Proc, edge=CrossCatProjection{C}, Unwinding)
 *         injects to the catch-all Proc category and UNWINDS ⇒ `==` trails.
 *   A LITERAL of cat C instead contributes a delegate-reentry lane
 *     (cat=C, edge=CrossCatLhsReentry{C}, InfixLoop) ⇒ guard ADMITS ⇒ `3==3` OK.
 *
 * THE FIX THIS MODEL DERIVES AND PROVES (accepting AND bounded):
 *   APPEND ONE cross-cat-LHS-reentry lane (cat=C, CrossCatLhsReentry{C}, InfixLoop)
 *   AT THE CAST RESULT (post-resolution — where the parser already knows the
 *   operand is a cast of result cat C and the inner content is ALREADY parsed),
 *   ALONGSIDE the existing lanes. Post-resolution the inner content is NOT
 *   re-dispatched, so this is +1 lane per cast RESULT (LINEAR in nesting depth),
 *   NOT the K^depth multiplication of the dispatch-time fall-through.
 *
 * The model proves, at the FRONTIER level:
 *   - current_rejects                  : the current frontier does NOT accept;
 *   - literal_accepts                  : the literal frontier DOES accept;
 *   - resultreentry_accepts            : the FIXED frontier accepts (the appended lane fires);
 *   - resultreentry_adds_one_lane      : the fix appends EXACTLY ONE lane;
 *   - resultreentry_linear             : the fix's frontier is LINEAR (<= 3*d) in depth d;
 *   - fallthrough_exponential/_unbounded: the dispatch-time fall-through is 2^d, unbounded;
 *   - fix_bounded_fallthrough_explodes : past depth 4 the fall-through strictly exceeds the fix;
 *   - resultreentry_preserves_proc_lane: the Proc-injection lane SURVIVES (ambiguity end-to-end);
 *   - fix_is_conservative              : the fix is purely additive — it removes NO existing
 *                                        acceptance (literals, same-category ops, `-3!` untouched);
 *   - resultreentry_sound              : the fix accepts ONLY the C-sourced infix (no spurious cross-cat).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Section CastCompareFrontierBound.

  (* ===== guard-relevant GSS edge kinds + evidence (mirror of wpda_walker.rs) ===== *)

  Inductive EdgeKind : Type :=
    | Generic
    | CrossCatLhs (src : nat)
    | CrossCatLhsReentry (src : nat)
    | CrossCatProjection (src : nat).

  (* Mirror of `cross_cat_lhs_infix_evidence_source`: evidence ONLY from
     CrossCatLhs/CrossCatLhsReentry whose recorded source equals the top cat. *)
  Definition evidence (top_cat : nat) (e : EdgeKind) : option nat :=
    match e with
    | CrossCatLhs s | CrossCatLhsReentry s =>
        if Nat.eqb s top_cat then Some s else None
    | Generic | CrossCatProjection _ => None
    end.

  (* Control state of a lane's cursor at the infix position. *)
  Inductive Ctrl : Type := CInfix | CUnwind.

  (* A LANE = one cursor at the infix position: its category, its GSS-top edge,
     and whether it reaches the InfixLoop guard. *)
  Record Lane : Type := mkLane { ln_cat : nat; ln_edge : EdgeKind; ln_ctrl : Ctrl }.

  (* A lane FIRES a category-changing infix of source `s` iff it reaches the guard
     (InfixLoop) and the evidence keyed by its own category equals `s`. *)
  Definition lane_fires (s : nat) (l : Lane) : bool :=
    match ln_ctrl l with
    | CUnwind => false
    | CInfix =>
        match evidence (ln_cat l) (ln_edge l) with
        | Some e => Nat.eqb e s
        | None => false
        end
    end.

  (* A FRONTIER accepts the category-changing infix iff SOME lane fires it. *)
  Definition frontier_accepts (s : nat) (f : list Lane) : bool :=
    existsb (lane_fires s) f.

  (* ===== the cast operand's frontier at `==`, GROUNDED in the trace ===== *)
  (* result cat = c; the comparison infix source is also c (e.g. EqInt: Int->Bool). *)
  (* proc = the catch-all wrapper category the projection injects into (proc <> c). *)

  Definition int_parse_lane (c : nat) : Lane := mkLane c Generic CInfix.
  Definition proc_inject_lane (c proc : nat) : Lane :=
    mkLane proc (CrossCatProjection c) CUnwind.
  Definition reentry_lane (c : nat) : Lane := mkLane c (CrossCatLhsReentry c) CInfix.

  (* The lanes the cast ALWAYS produces today (trace). *)
  Definition base_lanes (c proc : nat) : list Lane :=
    [ int_parse_lane c ; proc_inject_lane c proc ].

  (* CURRENT routing: just the base lanes. *)
  Definition frontier_current (c proc : nat) : list Lane := base_lanes c proc.

  (* THE FIX: base lanes + ONE cross-cat-LHS-reentry lane appended at the cast RESULT. *)
  Definition frontier_resultreentry (c proc : nat) : list Lane :=
    base_lanes c proc ++ [ reentry_lane c ].

  (* A literal's frontier (for the non-regression comparison): the delegate reentry
     lane plus the plain category parse lane. *)
  Definition frontier_literal (c : nat) : list Lane :=
    [ reentry_lane c ; int_parse_lane c ].

  (* The reentry lane fires the C-sourced infix. *)
  Lemma reentry_lane_fires : forall c, lane_fires c (reentry_lane c) = true.
  Proof.
    intro c. unfold lane_fires, reentry_lane, evidence; cbn.
    rewrite Nat.eqb_refl. cbn. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (* ===== the bug + the fix, at the FRONTIER level ===== *)

  (* CURRENT cast frontier does NOT accept: the Int-parse lane has no evidence
     (Generic) and the Proc-injection lane unwinds. This is the
     "WPDS finished but input remains, found ==" failure. *)
  Theorem current_rejects : forall c proc, frontier_accepts c (frontier_current c proc) = false.
  Proof.
    intros c proc.
    unfold frontier_accepts, frontier_current, base_lanes,
           int_parse_lane, proc_inject_lane, lane_fires, evidence; cbn.
    reflexivity.
  Qed.

  (* A LITERAL frontier accepts (it has the delegate reentry lane) — `3 == 3` works. *)
  Theorem literal_accepts : forall c, frontier_accepts c (frontier_literal c) = true.
  Proof.
    intro c. unfold frontier_accepts. rewrite existsb_exists.
    exists (reentry_lane c). split.
    - unfold frontier_literal. simpl. left. reflexivity.
    - apply reentry_lane_fires.
  Qed.

  (* THE FIX: the appended reentry lane fires ⇒ the fixed frontier accepts. *)
  Theorem resultreentry_accepts : forall c proc, frontier_accepts c (frontier_resultreentry c proc) = true.
  Proof.
    intros c proc. unfold frontier_accepts. rewrite existsb_exists.
    exists (reentry_lane c). split.
    - unfold frontier_resultreentry. apply in_or_app. right. simpl. left. reflexivity.
    - apply reentry_lane_fires.
  Qed.

  (* ===== boundedness: the fix is LINEAR; the dispatch-time fall-through is EXPONENTIAL ===== *)

  (* Concrete lane-count: the fix appends EXACTLY ONE lane to the frontier. *)
  Theorem resultreentry_adds_one_lane :
    forall c proc, length (frontier_resultreentry c proc) = S (length (frontier_current c proc)).
  Proof.
    intros c proc. unfold frontier_resultreentry, frontier_current, base_lanes. simpl. reflexivity.
  Qed.

  (* Depth-parameterized frontier sizes. A cast RESULT is post-resolution: its
     already-parsed inner content is NOT re-dispatched, so CURRENT and the FIX add
     a CONSTANT number of lanes per cast level (base = 2; the fix's reentry = +1),
     hence both are LINEAR in nesting depth d. *)
  Definition size_current (d : nat) : nat := 2 * d.
  Definition size_resultreentry (d : nat) : nat := 2 * d + d.   (* base + 1 reentry per level *)

  (* The FALSIFIED dispatch-time fall-through routes each cast TOKEN through the
     delegate BEFORE its operand is resolved; each level's delegate re-dispatches
     the inner content, MULTIPLYING the branch count (factor >= 2 ⇒ >= 2^d). *)
  Fixpoint size_fallthrough (d : nat) : nat :=
    match d with
    | O => 1
    | S d' => 2 * size_fallthrough d'
    end.

  (* The fix adds exactly d lanes over current — additive (1 per level), not multiplicative. *)
  Theorem resultreentry_additive : forall d, size_resultreentry d = size_current d + d.
  Proof. intro d. unfold size_resultreentry, size_current. lia. Qed.

  (* The fix's frontier is linearly bounded. *)
  Theorem resultreentry_linear : forall d, size_resultreentry d <= 3 * d.
  Proof. intro d. unfold size_resultreentry. lia. Qed.

  (* The fall-through frontier is exactly 2^d. *)
  Theorem fallthrough_exponential : forall d, size_fallthrough d = 2 ^ d.
  Proof.
    induction d as [|d IH]; simpl.
    - reflexivity.
    - rewrite IH. lia.
  Qed.

  Lemma pow2_pos : forall n, 1 <= 2 ^ n.
  Proof. induction n; simpl; lia. Qed.

  Lemma n_lt_2pow : forall n, n < 2 ^ n.
  Proof.
    induction n as [|n IH]; simpl.
    - lia.
    - pose proof (pow2_pos n). lia.
  Qed.

  (* The fall-through frontier grows without bound (exceeds any fixed budget B). *)
  Theorem fallthrough_unbounded : forall B, exists d, B < size_fallthrough d.
  Proof.
    intro B. exists (S B). rewrite fallthrough_exponential.
    pose proof (n_lt_2pow (S B)). lia.
  Qed.

  Lemma three_d_lt_pow2 : forall d, 4 <= d -> 3 * d < 2 ^ d.
  Proof.
    induction d as [|d IH]; intro H.
    - lia.
    - destruct (Nat.le_gt_cases 4 d) as [Hle|Hgt].
      + specialize (IH Hle).
        replace (2 ^ S d) with (2 * 2 ^ d) by (simpl; lia).
        lia.
      + assert (d = 3) by lia. subst. simpl. lia.
  Qed.

  (* Past depth 4 the dispatch-time fall-through STRICTLY exceeds the fix — the
     formal statement of "the fix stays bounded while the fall-through explodes,"
     with the gap = 2^d - 3*d growing without bound. *)
  Theorem fix_bounded_fallthrough_explodes :
    forall d, 4 <= d -> size_resultreentry d < size_fallthrough d.
  Proof.
    intros d Hd. rewrite fallthrough_exponential. unfold size_resultreentry.
    replace (2 * d + d) with (3 * d) by lia.
    apply three_d_lt_pow2; exact Hd.
  Qed.

  (* ===== ambiguity preservation + non-regression + soundness ===== *)

  (* The Proc-injection lane SURVIVES in the fixed frontier — the fix only APPENDS,
     so every prior interpretation is preserved (ambiguity end-to-end). *)
  Theorem resultreentry_preserves_proc_lane :
    forall c proc, In (proc_inject_lane c proc) (frontier_resultreentry c proc).
  Proof.
    intros c proc. unfold frontier_resultreentry, base_lanes.
    apply in_or_app. left. simpl. right. left. reflexivity.
  Qed.

  Theorem resultreentry_preserves_int_parse_lane :
    forall c proc, In (int_parse_lane c) (frontier_resultreentry c proc).
  Proof.
    intros c proc. unfold frontier_resultreentry, base_lanes.
    apply in_or_app. left. simpl. left. reflexivity.
  Qed.

  (* The fix is PURELY ADDITIVE — it APPENDS a lane. Appending a lane never removes
     an acceptance: any frontier that accepts `s` still accepts `s` afterwards. This
     is non-vacuous (instantiate f := frontier_literal c, s := c, which accepts by
     literal_accepts) and is exactly why the fix cannot regress literals,
     same-category operators, or the load-bearing `-3!` — those frontiers are
     untouched by, or only grown by, the appended cast-result lane. *)
  Theorem append_lane_monotone :
    forall s f l, frontier_accepts s f = true -> frontier_accepts s (f ++ [l]) = true.
  Proof.
    intros s f l H. unfold frontier_accepts in *.
    rewrite existsb_app. rewrite H. reflexivity.
  Qed.

  (* Corollary: literals still accept after the fix appends the cast-result lane. *)
  Corollary literal_accepts_after_fix :
    forall c l, frontier_accepts c (frontier_literal c ++ [l]) = true.
  Proof.
    intros c l. apply append_lane_monotone. apply literal_accepts.
  Qed.

  (* The appended reentry lane can ONLY introduce acceptance of the c-sourced infix:
     if the augmented frontier accepts `s`, then either the original already did, or
     s = c. So the fix never fabricates a spurious cross-category acceptance. *)
  Theorem append_reentry_only_adds_c :
    forall s f c,
      frontier_accepts s (f ++ [reentry_lane c]) = true ->
      frontier_accepts s f = true \/ s = c.
  Proof.
    intros s f c H. unfold frontier_accepts in H.
    rewrite existsb_app in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
    - left. exact H.
    - right. simpl in H. rewrite Bool.orb_false_r in H.
      unfold lane_fires, reentry_lane, evidence in H. simpl in H.
      rewrite Nat.eqb_refl in H. simpl in H. apply Nat.eqb_eq in H. lia.
  Qed.

  (* SOUNDNESS at the frontier level: the fixed frontier accepts ONLY when the infix
     source equals the cast result cat — no spurious cross-category infix slips in. *)
  Theorem resultreentry_sound :
    forall s c proc, frontier_accepts s (frontier_resultreentry c proc) = true -> s = c.
  Proof.
    intros s c proc H.
    unfold frontier_accepts, frontier_resultreentry, base_lanes,
           int_parse_lane, proc_inject_lane, reentry_lane, lane_fires, evidence in H.
    simpl in H. rewrite Nat.eqb_refl in H. simpl in H.
    rewrite Bool.orb_false_r in H. apply Nat.eqb_eq in H. lia.
  Qed.

End CastCompareFrontierBound.
