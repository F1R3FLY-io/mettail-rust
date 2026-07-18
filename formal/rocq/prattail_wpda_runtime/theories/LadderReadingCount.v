(*
 * LadderReadingCount: Theorem D of the S2 descriptor-pure canonical-GLL
 * campaign — the analytic attribution-ladder reading count, formalized as the
 * self-contained two-generator doubling recurrence of ledger §D.1
 * (scratchpad/zz_probes/s2_stageA_ledger.md, "Stage D — formal go/no-go",
 * Lemmas D-B / D-W / D-U + Theorem D).
 *
 * WHAT THIS PROVES. The ladder family T(d) = `@Nil!(A_d)` with
 * A_1 = `@(@Nil)!()`, A_k = `@(A_{k-1})!()` has reading counts
 *
 *     R(1) = 2      and      R(d) = 2^(d-1)  for d >= 2,
 *
 * i.e. the measured/predicted sequence 2, 2, 4, 8, 16 at d = 1..5 — the
 * beyond-oracle validation of the pure arm's grp_d5 = 16 result (the classic
 * E1 ground-truth route is machine-infeasible at d5: >300 GB; ledger §"E1-classic
 * GT for grp_d4/d5"). The recurrence is a two-generator doubling system:
 *   - the WRAPPED level (Lemma D-W): w(k) = { S(x), E(x) : x in w(k-1) },
 *     |w(k)| = 2·|w(k-1)|, where S = POutputShortEmpty and
 *     E = POutputEmpty ∘ NQuote are injective constructors with disjoint
 *     images (distinct head constructors);
 *   - the BASE (Lemma D-B): |w(1)| = 2 — the two readings
 *     QE(NParen(NQS(PZero))) and QE(NQS(PZero)) of `@(@Nil)!()` at a wrapped
 *     Proc slot (QE = POutputQuotedEmpty, NQS = NQuoteShort; the NParen-kept
 *     vs transparent-projection pair at the Name slot);
 *   - the S-ONLY OUTER level (Lemma D-U): u(1) = w(1) and, for d >= 2,
 *     u(d) = { S(x) : x in w(d-1) } — the E (channel-first) branch is
 *     excluded at POutputNil's unwrapped argument slot.
 *
 * MODEL CORRESPONDENCE (grammar: languages/src/rhocalc.rs — rule heads
 * PZero @120, POutputEmpty @143, POutputNil @186, POutputQuotedEmpty @281,
 * POutputShortEmpty @288, NQuote @538, NQuoteShort @566, NParen @572;
 * measured multisets: logs_s2b0/ast_pure_grp_d{1..5}.log, cross-check
 * generator scratchpad/zz_probes/stageD_derivation_check.py,
 * EXACT-MULTISET-MATCH d1..d5):
 *   - `LadderReading` is the constructor skeleton of the reading ASTs:
 *     `BaseParenKept`/`BaseTransparent` = the two D-B base readings;
 *     `WrapShort` = the S generator; `WrapChannel` = the E generator;
 *     `OuterShell` = the fixed POutputNil shell of T(d).
 *   - `wrapped k` models the ledger's w(k+1) (index shift so the fixpoint
 *     recursion is structural); `unwrapped d` models u(d); `ladder_readings d`
 *     models the complete reading set of T(d).
 *   - The D-U exclusion (no E at the outer unwrapped slot) and the D-N Name
 *     floor (no full-span Name reading; prefix(220) l_bp floor) enter this
 *     model as DEFINITIONS of `unwrapped`, exactly as ledger §D.1 takes them:
 *     they are oracle-established premises (exhaustive E1-classic GT at d4 =
 *     8/8 all-outer-S; classic/pure MSET-EQ at d1..d3; budget-complete pure
 *     saturation at d5). Their TABLE-LEVEL mechanism (the generated-WPDA l_bp
 *     extraction) is a named residual OUTSIDE this file's scope — this file
 *     is the mandated "Theorem D as a corollary": the recurrence combinatorics,
 *     fully self-contained, no parser model.
 *   - Byte-identical twin families (footnotes F1/F2/F3 of §D.1 — NQuoteNil vs
 *     NQuoteShort(PZero), POutputShort(PZero,·) vs POutputNil,
 *     POutputEmpty(NQuoteShort(x)) vs POutputShortEmpty(x)) are dedup-elected
 *     uniformly by both engines and therefore do not appear as separate
 *     constructors: each `LadderReading` value is one MATERIALIZED (dedup'd)
 *     AST, matching the `{t:?}` AST-dump comparator the gates used.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, each must
 * print "Closed under the global context"):
 *   T1 wrapped_level_doubles      — |w(k+1)| = 2·|w(k)| (Lemma D-W's count).
 *   T2 wrapped_level_length       — |w(k)| = 2^k for k >= 1 (closed form).
 *   T3 wrapped_level_distinct     — w(k) is duplicate-free: S/E are injective
 *                                   with disjoint images, so the doubling
 *                                   never collides (the multiset IS a set —
 *                                   16 DISTINCT ASTs at d5).
 *   T4 theorem_D_base             — R(1) = 2.
 *   T5 theorem_D_closed_form      — R(d) = 2^(d-1) for d >= 2.
 *   T6 ladder_readings_distinct   — the T(d) reading list is duplicate-free.
 *   T7 ladder_counts_d1_to_d5     — the concrete instance 2,2,4,8,16 at
 *                                   d = 1..5 (computes; the d5 = 16 receipt).
 *   T8 deep_readings_all_outer_S  — for d >= 2 every reading's outermost
 *                                   generator under the shell is S (the D-U
 *                                   exclusion, now structural in the model).
 *
 * FAILED STRATEGIES (documented so they are not re-attempted):
 *   - Defining `wrapped` at the ledger's own index (w : k >= 1) with a
 *     `match k with 0 => [] | 1 => base | S (S k') => ...` fixpoint makes the
 *     recursive call `wrapped (S k')` non-structural in the `S (S k')` branch
 *     without a nested match; the index shift (`wrapped k` models w(k+1))
 *     keeps the recursion structural and every proof by plain induction.
 *   - Proving T3 via stdlib `Injective_map_NoDup` pulls in `FinFun`; a local
 *     two-line `nodup_map_injective` avoids the extra import surface.
 *
 * Rocq 9.1 compatible. No Admitted, no Axiom, no Parameter.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section LadderReadingCount.

  (* ── The reading-AST constructor skeleton (see the correspondence block). ── *)
  Inductive LadderReading : Type :=
    | BaseParenKept                          (* QE(NParen(NQS(PZero)))  — D-B *)
    | BaseTransparent                        (* QE(NQS(PZero))          — D-B *)
    | WrapShort   : LadderReading -> LadderReading   (* S = POutputShortEmpty *)
    | WrapChannel : LadderReading -> LadderReading   (* E = POutputEmpty∘NQuote *)
    | OuterShell  : LadderReading -> LadderReading.  (* POutputNil(·) shell   *)

  (* Lemma D-B: the two base readings of A_1 at a wrapped Proc slot. *)
  Definition base_readings : list LadderReading := [BaseParenKept; BaseTransparent].

  (* Lemma D-W as a recurrence: `wrapped k` = the ledger's w(k+1)
     (readings of A_{k+1} at a parenthesized/wrapped Proc position). *)
  Fixpoint wrapped (k : nat) : list LadderReading :=
    match k with
    | 0 => base_readings
    | S k' => map WrapShort (wrapped k') ++ map WrapChannel (wrapped k')
    end.

  (* Lemma D-U: u(d) — readings of A_d at POutputNil's UNWRAPPED argument
     slot. u(1) = w(1); u(d) = { S(x) : x in w(d-1) } for d >= 2 (the E branch
     is excluded at the unwrapped slot — the oracle-established premise). *)
  Definition unwrapped (d : nat) : list LadderReading :=
    match d with
    | 0 => []                                   (* no level-0 term in the family *)
    | 1 => base_readings                        (* u(1) = w(1) *)
    | S (S d'') => map WrapShort (wrapped d'')  (* u(d) = S(w(d-1)), w(d-1) = wrapped (d-2) *)
    end.

  (* The complete reading set of T(d) = `@Nil!(A_d)`: the injective
     POutputNil shell over u(d). R(d) := length (ladder_readings d). *)
  Definition ladder_readings (d : nat) : list LadderReading :=
    map OuterShell (unwrapped d).

  (* ═══════════════════════════════════════════════════════════════════════════
     T1/T2 — the doubling recurrence and its closed form (Lemma D-W count).
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem wrapped_level_doubles :
    forall k, length (wrapped (S k)) = 2 * length (wrapped k).
  Proof.
    intro k. cbn [wrapped].
    rewrite length_app, !length_map. lia.
  Qed.

  (* |w(k)| = 2^k for the ledger index k >= 1; at this file's shifted index:
     |wrapped k| = 2^(k+1). *)
  Theorem wrapped_level_length :
    forall k, length (wrapped k) = 2 ^ (S k).
  Proof.
    induction k as [|k IHk].
    - reflexivity.
    - rewrite wrapped_level_doubles, IHk.
      rewrite (Nat.pow_succ_r' 2 (S k)). reflexivity.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T3 — distinctness: the doubling never collides (S/E injective, images
     disjoint by head constructor), so counts are counts of DISTINCT readings.
     ═══════════════════════════════════════════════════════════════════════════ *)

  (* Local helper: an injective map preserves NoDup. *)
  Lemma nodup_map_injective :
    forall (f : LadderReading -> LadderReading) (l : list LadderReading),
      (forall x y, f x = f y -> x = y) ->
      NoDup l -> NoDup (map f l).
  Proof.
    intros f l Hinj Hnd. induction Hnd as [|x l Hnin Hnd IH].
    - constructor.
    - cbn [map]. constructor.
      + intro Hin. apply in_map_iff in Hin.
        destruct Hin as [y [Heq Hy]].
        apply Hinj in Heq. subst y. exact (Hnin Hy).
      + exact IH.
  Qed.

  (* Local helper: appending disjoint NoDup lists yields a NoDup list. *)
  Lemma nodup_app_disjoint :
    forall l1 l2 : list LadderReading,
      NoDup l1 -> NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) ->
      NoDup (l1 ++ l2).
  Proof.
    induction l1 as [|a l1 IH]; intros l2 Hnd1 Hnd2 Hdisj.
    - exact Hnd2.
    - cbn [app]. inversion Hnd1 as [|? ? Hnin Hnd1']; subst.
      constructor.
      + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
        * exact (Hnin Hin).
        * exact (Hdisj a (or_introl eq_refl) Hin).
      + apply IH; [exact Hnd1' | exact Hnd2 |].
        intros x Hx1 Hx2. exact (Hdisj x (or_intror Hx1) Hx2).
  Qed.

  Theorem wrapped_level_distinct :
    forall k, NoDup (wrapped k).
  Proof.
    induction k as [|k IHk].
    - (* base: the two D-B readings are distinct constants *)
      cbn [wrapped]. unfold base_readings.
      constructor.
      + intro Hin. cbn in Hin.
        destruct Hin as [Hin | Hin]; [discriminate Hin | exact Hin].
      + constructor; [intro Hin; exact Hin | constructor].
    - cbn [wrapped]. apply nodup_app_disjoint.
      + apply nodup_map_injective; [| exact IHk].
        intros x y Heq. injection Heq. tauto.
      + apply nodup_map_injective; [| exact IHk].
        intros x y Heq. injection Heq. tauto.
      + (* disjoint images: WrapShort _ never equals WrapChannel _ *)
        intros x HinS HinE.
        apply in_map_iff in HinS. destruct HinS as [xs [HeqS _]].
        apply in_map_iff in HinE. destruct HinE as [xe [HeqE _]].
        subst x. discriminate HeqE.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T4/T5 — Theorem D: R(1) = 2 and R(d) = 2^(d-1) for d >= 2.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem theorem_D_base :
    length (ladder_readings 1) = 2.
  Proof. reflexivity. Qed.

  Theorem theorem_D_closed_form :
    forall d, 2 <= d -> length (ladder_readings d) = 2 ^ (d - 1).
  Proof.
    intros d Hd.
    destruct d as [|[|d'']]; [lia | lia |].
    (* d = S (S d''), so d - 1 = S d''. *)
    unfold ladder_readings. cbn [unwrapped].
    rewrite !length_map, wrapped_level_length.
    (* `S (S d'') - 1` reduces to `S d''`, so f_equal closes by computation
       (a trailing `lia` here would face zero goals; `; lia` stays vacuous). *)
    f_equal; lia.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T6 — the T(d) reading lists are duplicate-free at every depth: the
     measured multisets are SETS (16 distinct ASTs at d5, matching the
     `EXACT-MULTISET-MATCH distinct=16` receipt).
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem ladder_readings_distinct :
    forall d, NoDup (ladder_readings d).
  Proof.
    intro d. unfold ladder_readings.
    apply nodup_map_injective.
    { intros x y Heq. injection Heq. tauto. }
    destruct d as [|[|d'']].
    - constructor.
    - (* unwrapped 1 = base_readings *)
      cbn [unwrapped]. unfold base_readings.
      constructor.
      + intro Hin. cbn in Hin.
        destruct Hin as [Hin | Hin]; [discriminate Hin | exact Hin].
      + constructor; [intro Hin; exact Hin | constructor].
    - cbn [unwrapped]. apply nodup_map_injective.
      + intros x y Heq. injection Heq. tauto.
      + apply wrapped_level_distinct.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T7 — the concrete gate instance: R(1..5) = 2, 2, 4, 8, 16 by computation.
     This is the analytic d5 = 16 the Stage-D gate rests on (classic E1 GT
     machine-infeasible at d5), plus the measured 2/2/4/8 at d1..d4.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem ladder_counts_d1_to_d5 :
    map (fun d => length (ladder_readings d)) [1; 2; 3; 4; 5]
    = [2; 2; 4; 8; 16].
  Proof. reflexivity. Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T8 — the D-U exclusion, structurally: for d >= 2 every reading of T(d)
     opens with the S generator directly under the POutputNil shell (reading
     shape POutputNil ∘ S ∘ {S,E}^(d-2) ∘ QE ∘ {NParen∘NQS, NQS} (PZero)).
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem deep_readings_all_outer_S :
    forall d r, 2 <= d -> In r (ladder_readings d) ->
      exists r', r = OuterShell (WrapShort r').
  Proof.
    intros d r Hd Hin.
    destruct d as [|[|d'']]; [lia | lia |].
    unfold ladder_readings in Hin. cbn [unwrapped] in Hin.
    apply in_map_iff in Hin. destruct Hin as [u [Hu Hin']].
    apply in_map_iff in Hin'. destruct Hin' as [x [Hx _]].
    subst u. subst r. eauto.
  Qed.

End LadderReadingCount.

(* ── ADMISSION AUDIT — every theorem must print "Closed under the global context". *)
Print Assumptions wrapped_level_doubles.
Print Assumptions wrapped_level_length.
Print Assumptions wrapped_level_distinct.
Print Assumptions theorem_D_base.
Print Assumptions theorem_D_closed_form.
Print Assumptions ladder_readings_distinct.
Print Assumptions ladder_counts_d1_to_d5.
Print Assumptions deep_readings_all_outer_S.
