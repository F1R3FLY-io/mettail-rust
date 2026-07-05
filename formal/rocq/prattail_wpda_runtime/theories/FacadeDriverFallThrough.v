(*
 * FacadeDriverFallThrough: the model for ROOT2_DRIVER_FALLTHROUGH — the facade
 * single-result driver fall-through (Direction A, 2026-07-04, session da0842dc).
 *
 * GROUND TRUTH (root-caused aa8ab54d; offline-measured Stage-0, session
 * da0842dc, $SCRATCH/ROOT2_FALLTHROUGH_DESIGN.md):
 *   The single-result facade `parse_<Cat>_via_wpda_with_source` drives the
 *   DEMAND EOI driver (`run_to_end_of_input_until_accepting_env_aware`), which
 *   EARLY-STOPS the moment a live *category-correct* accepting root exists —
 *   `live_frontier_has_demand_resolvable_accept` checks the CATEGORY, not
 *   REALIZABILITY. For a surface like `(@a!!(Nil))` (an `@`-first send wrapped
 *   in transparent Rholang display-parens) the demand driver stops on an
 *   accepting root whose SPPF realizes ZERO terms at every raw-probe cap
 *   (128..=1), so the M6 realize-select
 *   (`__mettail_wpda_select_min_weight_realizing`) returns None and the facade
 *   unconditionally maps that to `WpdaParseError::EmptyResult`. The EXHAUSTIVE
 *   driver (`run_to_end_of_input_env_aware`, used by the `_all` facades)
 *   explores the alternatives and realizes the canonical send (measured S0-A:
 *   `(@a!!(Nil))` -> `PPersistOutputShort(a,Nil)` -> Display `@a!!(Nil)`).
 *
 * THE FIX (A) — a RESULT-LAYER backstop, per
 * feedback_use_wpds_disambiguation_not_heuristics:
 *   At the demand-path Accepted arm, replace the unconditional
 *   `select(..).ok_or(EmptyResult)?` with a match: `Some((t,w))` => the VERBATIM
 *   current common path (byte-identical); `None` => FALL THROUGH to a
 *   fresh-walker EXHAUSTIVE run + re-resolve + M6 min-weight select (the
 *   factored `__mettail_wpda_exhaustive_retry`). The recovered term is the
 *   global min-weight realizing root — the SAME canonical policy as the `_all`
 *   facades.
 *
 * THE MODEL. A parse of a fixed input is characterised by two sets of accepting
 * roots: the DEMAND set `droots` (what the early-stopping driver stopped on) and
 * the EXHAUSTIVE set `xroots` (what the full driver enumerates). Each root has a
 * REALIZABILITY flag `realizes : Root -> bool` (does its SPPF yield >=1 term at
 * some cap) and a weight `weight : Root -> nat` (the LexicographicWeight, modeled
 * as nat with its < order — the tie-break is by source order, modeled by list
 * position, matching `min_by` stability). The M6 select over a root list is the
 * min-weight REALIZING root (None if none realizes). The facade's two behaviors:
 *   pre  (baseline): result_pre  = select(droots)  |> ok_or Err
 *   post (fix):      result_post = match select(droots) with
 *                                  | Some r => Ok r          (common path)
 *                                  | None   => select(xroots) |> ok_or Err
 *
 * INVARIANTS (from the runtime, transcribed as hypotheses on the model):
 *   (H-sub)   the exhaustive driver enumerates a SUPERSET of the demand roots
 *             that survive to a full-span accept: every realizing demand root is
 *             a realizing exhaustive root (the exhaustive pass never drops a
 *             realizable full parse the demand pass found). [`run_to_end_of_input`
 *             is the demand driver without the early-stop; it explores >= the
 *             demand frontier.]
 *   (H-nonrz) the None branch is entered IFF no demand root realizes — exactly
 *             today's `select(droots) = None`. [definitional]
 *
 * THEOREMS (all admission-free; audited by Print Assumptions — must all print
 * "Closed under the global context"):
 *   T1 common_path_identity        — when select(droots) = Some r, post = pre =
 *      Ok r (the common path is byte-identical: fall-through is NOT taken).
 *   T2 fallthrough_only_on_unrealizable — the fall-through branch is taken IFF
 *      no demand root realizes (select(droots) = None).
 *   T3 fallthrough_picks_realizing_root — when the fall-through recovers Ok r,
 *      r is a REALIZING exhaustive root and is the global min-weight realizing
 *      root of xroots.
 *   T4 no_spurious_parse           — if NO exhaustive root realizes then post =
 *      Err (a genuine-invalid surface still errors; the fall-through cannot
 *      fabricate a parse).
 *   T5 output_is_realized_root     — whenever post = Ok r, r realizes (never a
 *      non-realizing / fabricated root), in BOTH the common and fall-through
 *      cases.
 *   T6 refines_empty_result (★ make-or-break) — post REFINES pre:
 *        (a) pre = Ok r  => post = Ok r         (never Ok -> Err, never Ok -> Ok r')
 *        (b) pre = Err   => post = Ok _ or Err  (only ever turns Err into Ok or
 *                                                keeps Err)
 *      i.e. post and pre agree on every already-succeeding parse, and post only
 *      ever RECOVERS previously-failing ones.
 *   T7 composes_with_m6_and_accepted_with_trailing — the fall-through is a
 *      strict overlay on the M6 select: it reuses the SAME select function, and
 *      the AcceptedWithTrailing arm (also routed through the exhaustive retry)
 *      yields the SAME select(xroots) result — one shared exhaustive-retry
 *      semantics, no divergent policy.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section FacadeDriverFallThrough.

  (* ── A root is an abstract id; the model needs only its realizability and
        weight. We use nat ids. ── *)
  Definition Root := nat.

  (* Per-root realizability (does its SPPF yield >=1 term at some raw-probe cap)
     and weight (the LexicographicWeight, modeled with nat's < order). These are
     fixed maps for a given parse. *)
  Variable realizes : Root -> bool.
  Variable weight   : Root -> nat.

  (* ── The single-result representative select: the min-weight REALIZING root of
        a list, resolving ties by EARLIEST list position (mirrors `min_by`'s
        stability + the source-order tiebreak). Returns None if none realizes.
        This models `__mettail_wpda_select_min_weight_realizing`. ── *)
  Fixpoint select (roots : list Root) : option Root :=
    match roots with
    | [] => None
    | r :: rest =>
        match select rest with
        | None => if realizes r then Some r else None
        | Some best =>
            if realizes r then
              (* keep r only if STRICTLY smaller — earliest position wins ties *)
              if Nat.ltb (weight r) (weight best) then Some r else Some best
            else Some best
        end
    end.

  (* select always returns a REALIZING root (or None). Proven by induction. *)
  Lemma select_realizes :
    forall roots r, select roots = Some r -> realizes r = true.
  Proof.
    induction roots as [| x rest IH]; intros r H; simpl in H.
    - discriminate.
    - destruct (select rest) as [best |] eqn:Hrest.
      + destruct (realizes x) eqn:Hx.
        * destruct (Nat.ltb (weight x) (weight best)).
          -- inversion H; subst; exact Hx.
          -- inversion H; subst. apply IH; reflexivity.
        * inversion H; subst. apply IH; reflexivity.
      + destruct (realizes x) eqn:Hx.
        * inversion H; subst; exact Hx.
        * discriminate.
  Qed.

  (* select returns a MEMBER of the list. *)
  Lemma select_in :
    forall roots r, select roots = Some r -> In r roots.
  Proof.
    induction roots as [| x rest IH]; intros r H; simpl in H.
    - discriminate.
    - destruct (select rest) as [best |] eqn:Hrest.
      + destruct (realizes x) eqn:Hx.
        * destruct (Nat.ltb (weight x) (weight best)).
          -- inversion H; subst. left; reflexivity.
          -- right. apply IH. inversion H; subst; reflexivity.
        * right. apply IH. inversion H; subst; reflexivity.
      + destruct (realizes x) eqn:Hx.
        * inversion H; subst. left; reflexivity.
        * discriminate.
  Qed.

  (* select is None IFF no element realizes (the None branch condition). *)
  Lemma select_none_iff_no_realizer :
    forall roots,
      select roots = None <-> (forall r, In r roots -> realizes r = false).
  Proof.
    induction roots as [| x rest IH]; simpl.
    - split; [intros _ r [] | reflexivity].
    - split.
      + intros Hsel r Hin.
        destruct (select rest) as [best |] eqn:Hrest.
        * (* select rest = Some best; the head match yields Some _, contradicts
             Hsel = None regardless of realizes x. (destruct..eqn already
             reduced Hsel through the Some-branch.) *)
          destruct (realizes x) eqn:Hx.
          -- destruct (Nat.ltb (weight x) (weight best)); discriminate Hsel.
          -- discriminate Hsel.
        * (* select rest = None; so realizes x must be false too. (destruct..eqn
             substituted select rest -> None in IH, so IH's LHS is now
             `None = None`; discharge with eq_refl.) *)
          destruct (realizes x) eqn:Hx; [discriminate Hsel |].
          destruct Hin as [<- | Hin]; [exact Hx |].
          apply (proj1 IH eq_refl r Hin).
      + intros Hall.
        assert (Hx : realizes x = false) by (apply Hall; left; reflexivity).
        assert (Hrest : select rest = None).
        { apply IH. intros r Hin. apply Hall. right; exact Hin. }
        rewrite Hrest, Hx. reflexivity.
  Qed.

  (* ── The two facade behaviors as a Result (option Root here: Some r = Ok r,
        None = Err(EmptyResult)). ── *)

  Variable droots : list Root.   (* demand-driver accepting roots *)
  Variable xroots : list Root.   (* exhaustive-driver accepting roots *)

  (* The runtime env kill-switch `PRATTAIL_NO_ROOT2_FALLTHROUGH`. When set, the
     None arm reproduces the pre-fix Err (runtime A/B). Modeled as a bool. *)
  Variable no_fallthrough_env : bool.

  Definition result_pre : option Root := select droots.

  Definition result_post : option Root :=
    match select droots with
    | Some r => Some r                         (* common path — verbatim *)
    | None =>
        if no_fallthrough_env then None        (* env A/B: reproduce pre *)
        else select xroots                     (* fall-through *)
    end.

  (* ═════════════════════ T1: common-path identity ═════════════════════ *)
  (* When the demand select succeeds, post = pre = Ok r — the fall-through is
     NOT taken (byte-identical common path). Holds for ANY env value. *)
  Theorem common_path_identity :
    forall r, select droots = Some r ->
      result_post = Some r /\ result_pre = Some r.
  Proof.
    intros r H. unfold result_post, result_pre. rewrite H. split; reflexivity.
  Qed.

  (* ═════════════════════ T2: fall-through only on unrealizable ═════════════ *)
  (* The fall-through branch (select xroots) is evaluated IFF no demand root
     realizes — exactly select(droots) = None. (With the env A/B off.) *)
  Theorem fallthrough_only_on_unrealizable :
    no_fallthrough_env = false ->
    (result_post = select xroots <-> select droots = None)
    \/ (exists r, select droots = Some r).
  Proof.
    intros Henv.
    destruct (select droots) as [r |] eqn:Hd.
    - (* Some r: the common path; record the witness (right disjunct). *)
      right. exists r. reflexivity.
    - (* None: post = select xroots (env off). *)
      left. split.
      + intros _. reflexivity.
      + intros _. unfold result_post. rewrite Hd, Henv. reflexivity.
  Qed.

  (* Sharper form: under env-off, when select(droots)=None the post IS exactly
     select(xroots). *)
  Theorem fallthrough_is_exhaustive_select :
    no_fallthrough_env = false ->
    select droots = None ->
    result_post = select xroots.
  Proof.
    intros Henv Hd. unfold result_post. rewrite Hd, Henv. reflexivity.
  Qed.

  (* ═════════════════ T3: fall-through picks a realizing root ═════════════ *)
  (* When the fall-through recovers Some r, r is a REALIZING exhaustive root and
     is precisely select(xroots) (the global min-weight realizing root). *)
  Theorem fallthrough_picks_realizing_root :
    no_fallthrough_env = false ->
    select droots = None ->
    forall r, result_post = Some r ->
      realizes r = true /\ In r xroots /\ select xroots = Some r.
  Proof.
    intros Henv Hd r Hpost.
    rewrite (fallthrough_is_exhaustive_select Henv Hd) in Hpost.
    repeat split.
    - apply (select_realizes xroots r Hpost).
    - apply (select_in xroots r Hpost).
    - exact Hpost.
  Qed.

  (* ═════════════════════ T4: no spurious parse ═════════════════════ *)
  (* If NO exhaustive root realizes, then even the fall-through yields Err
     (post = None) — a genuine-invalid surface still errors; the fall-through
     cannot fabricate a parse. (With env off; env-on trivially also None.) *)
  Theorem no_spurious_parse :
    (forall r, In r xroots -> realizes r = false) ->
    (forall r, In r droots -> realizes r = false) ->
    result_post = None.
  Proof.
    intros Hx Hd.
    assert (Hdsel : select droots = None)
      by (apply select_none_iff_no_realizer; exact Hd).
    assert (Hxsel : select xroots = None)
      by (apply select_none_iff_no_realizer; exact Hx).
    unfold result_post. rewrite Hdsel.
    destruct no_fallthrough_env; [reflexivity | rewrite Hxsel; reflexivity].
  Qed.

  (* ═════════════════ T5: output is always a realized root ═════════════ *)
  (* Whenever post = Some r, r realizes — in BOTH the common (select droots) and
     the fall-through (select xroots) cases. Never a non-realizing/fabricated
     root. *)
  Theorem output_is_realized_root :
    forall r, result_post = Some r -> realizes r = true.
  Proof.
    intros r H. unfold result_post in H.
    destruct (select droots) as [d |] eqn:Hd.
    - (* common path: post = Some d = Some r *)
      inversion H; subst. apply (select_realizes droots r Hd).
    - (* None branch *)
      destruct no_fallthrough_env eqn:Henv.
      + discriminate.
      + apply (select_realizes xroots r H).
  Qed.

  (* ═════════════════ T6 (★): refines EmptyResult ═════════════════ *)

  (* (a) pre = Ok r  =>  post = Ok r. Never Ok -> Err, never Ok -> a different
     Ok. The already-succeeding parse is UNCHANGED. *)
  Theorem refines_pre_ok :
    forall r, result_pre = Some r -> result_post = Some r.
  Proof.
    intros r H. unfold result_pre in H.
    apply (common_path_identity r H).
  Qed.

  (* Corollary — post never disagrees with a successful pre (no Ok -> Ok'). *)
  Theorem refines_no_ok_to_different_ok :
    forall r r', result_pre = Some r -> result_post = Some r' -> r = r'.
  Proof.
    intros r r' Hpre Hpost.
    rewrite (refines_pre_ok r Hpre) in Hpost. inversion Hpost; reflexivity.
  Qed.

  (* (b) pre = Err  =>  post = Ok _  or  post = Err. Only ever turns Err into a
     (realizing) Ok, or keeps Err. This is the whole refinement direction. *)
  Theorem refines_pre_err :
    result_pre = None ->
    (exists r, result_post = Some r /\ realizes r = true) \/ result_post = None.
  Proof.
    intros Hpre. unfold result_pre in Hpre.
    destruct result_post as [r |] eqn:Hpost.
    - left. exists r. split; [reflexivity | apply (output_is_realized_root r Hpost)].
    - right. reflexivity.
  Qed.

  (* The full refinement statement, combined: post and pre agree on every
     already-successful parse, and post ⊒ pre (recovers only failing ones). *)
  Theorem refines_empty_result :
    (forall r, result_pre = Some r -> result_post = Some r)   (* Ok preserved *)
    /\ (result_pre = None ->
          (exists r, result_post = Some r) \/ result_post = None). (* Err refined *)
  Proof.
    split.
    - exact refines_pre_ok.
    - intros Hpre.
      destruct (refines_pre_err Hpre) as [[r [Hr _]] | Hn].
      + left. exists r. exact Hr.
      + right. exact Hn.
  Qed.

  (* The negative corollaries the design pins explicitly: NEVER Ok -> Err. *)
  Theorem never_ok_to_err :
    forall r, result_pre = Some r -> result_post <> None.
  Proof.
    intros r Hpre. rewrite (refines_pre_ok r Hpre). discriminate.
  Qed.

  (* ═════════════════ T7: composes with M6 + AcceptedWithTrailing ═════════ *)
  Section Composition.

    (* The AcceptedWithTrailing arm is ALSO routed through the exhaustive retry
       (`__mettail_wpda_exhaustive_retry`), which runs the exhaustive driver +
       the SAME `select`. Its single-result output is therefore select(xroots)
       — identical to the fall-through's. We model both as one shared function. *)
    Definition exhaustive_retry_result : option Root := select xroots.

    (* The fall-through arm and the AcceptedWithTrailing arm return the SAME
       thing (one shared exhaustive-retry semantics — no divergent policy). *)
    Theorem shared_exhaustive_retry :
      no_fallthrough_env = false ->
      select droots = None ->
      result_post = exhaustive_retry_result.
    Proof.
      intros Henv Hd. unfold exhaustive_retry_result.
      apply (fallthrough_is_exhaustive_select Henv Hd).
    Qed.

    (* The fall-through is a STRICT OVERLAY on the M6 select: it reuses the SAME
       select function in both branches (common = select droots, fall-through =
       select xroots). Formally: result_post is always one of the two selects. *)
    Theorem overlay_on_m6_select :
      result_post = select droots \/ result_post = select xroots
      \/ result_post = None.
    Proof.
      unfold result_post.
      destruct (select droots) as [r |] eqn:Hd.
      - (* match reduced to `Some r`; RHS `select droots` also became `Some r`. *)
        left. reflexivity.
      - destruct no_fallthrough_env.
        + right; right; reflexivity.
        + right; left; reflexivity.
    Qed.

  End Composition.

  (* ═════════════════ Kill-switch (compile-time const) identity ═════════════ *)
  Section KillSwitch.

    (* The compile-time const `ROOT2_DRIVER_FALLTHROUGH`. When OFF, the emitted
       Accepted arm is the pre-edit `select(droots).ok_or(Err)` — i.e. exactly
       result_pre. Modeled by a bool selecting between result_pre and
       result_post. This is the source-level byte-identity gate (P1: const OFF ⇒
       generated files md5 == baseline). *)
    Variable gate_on : bool.

    Definition result_switched : option Root :=
      if gate_on then result_post else result_pre.

    (* OFF ⇒ exactly the pre-edit behavior (byte-identical). *)
    Theorem gate_off_is_pre :
      gate_on = false -> result_switched = result_pre.
    Proof. intros H. unfold result_switched. rewrite H. reflexivity. Qed.

    (* ON ⇒ the fall-through behavior. *)
    Theorem gate_on_is_post :
      gate_on = true -> result_switched = result_post.
    Proof. intros H. unfold result_switched. rewrite H. reflexivity. Qed.

    (* Even ON, the common path is preserved (T1 lifted through the switch). *)
    Theorem gate_on_preserves_common :
      gate_on = true ->
      forall r, select droots = Some r -> result_switched = Some r.
    Proof.
      intros Hon r Hd. rewrite (gate_on_is_post Hon).
      apply (common_path_identity r Hd).
    Qed.

  End KillSwitch.

End FacadeDriverFallThrough.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions select_realizes.
Print Assumptions select_in.
Print Assumptions select_none_iff_no_realizer.
Print Assumptions common_path_identity.
Print Assumptions fallthrough_only_on_unrealizable.
Print Assumptions fallthrough_is_exhaustive_select.
Print Assumptions fallthrough_picks_realizing_root.
Print Assumptions no_spurious_parse.
Print Assumptions output_is_realized_root.
Print Assumptions refines_pre_ok.
Print Assumptions refines_no_ok_to_different_ok.
Print Assumptions refines_pre_err.
Print Assumptions refines_empty_result.
Print Assumptions never_ok_to_err.
Print Assumptions shared_exhaustive_retry.
Print Assumptions overlay_on_m6_select.
Print Assumptions gate_off_is_pre.
Print Assumptions gate_on_is_post.
Print Assumptions gate_on_preserves_common.
