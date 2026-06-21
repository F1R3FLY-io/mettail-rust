(*
 * SingleResultDominanceSubsumption: the soundness invariant of the
 * single-result demand-mode weight-dominance subsumption pass
 * (`subsume_weight_dominated_when_single_result`, commit c45bdea2).
 *
 * Design source of truth:
 *   docs/design/calculator-map-crosscat-fanout.md
 *     §4.1   the ConfigKey + the dominance predicate
 *     §4.2   L1 (dominance invariant under common continuation) + L2
 *            (SPPF weight_sum invariant under dropping a dominated cursor)
 *     §8.1   the red-team refinement: the order is preserved as `≤`, NOT
 *            strict `<`. A `Less` may DEGRADE to `Equal` (never invert to
 *            `Greater`) through `LexicographicWeight::times`'s `is_one`
 *            short-circuit; left-projection holds for non-identity cursors;
 *            the triple is frozen (monotone-sticky) once `primary > 0`.
 *
 * WHAT IS PROVED (zero-admission, no Axiom / Admitted / admit):
 *
 *   The `LexicographicWeight` is modelled as the lexicographic product of
 *   (a) a tropical/min-plus PRIMARY and (b) a left-projected PROVENANCE
 *   TRIPLE, with the idempotent semiring add `⊕` = lex-min and the multiply
 *   `⊗` = (primary: tropical-sum `+`; triple: left-projection with the
 *   `is_one`/identity short-circuit). The model reproduces the Rust
 *   `lex_cmp` / `plus` / `times` of `rigail/src/lex_weight.rs` EXACTLY on the
 *   relevant fragment (see the fidelity note below).
 *
 *   L1 dominance_monotone_under_common_continuation : for weights s, c with
 *      `lex_cmp s c ∈ {Lt, Eq}` and ANY continuation w,
 *      `lex_cmp (s ⊗ w) (c ⊗ w) ∈ {Lt, Eq}`.
 *      (Monotone `≤`, NOT strict-preserving — the `is_one` short-circuit is
 *      encoded faithfully so the proof is honest that `Lt` may degrade to
 *      `Eq`.)
 *
 *   L2 lex_min_invariant_under_dropping_dominated : for a finite list M and
 *      a dominated element c (∃ s ∈ M, s ≠ c, `lex_cmp s c ∈ {Lt, Eq}`),
 *      `lex_min M = lex_min (remove c M)`. Hence dropping a dominated cursor
 *      preserves the single-result `min_by(weight)` selection.
 *
 *   TOP-LEVEL single_result_subsumption_preserves_selection : the connection
 *      to the parser — subsuming a same-config dominated cursor leaves the
 *      single-result realized winner (the lex-min of the accept frontier)
 *      unchanged.
 *
 * ── FIDELITY NOTE (the model ↔ the Rust) ────────────────────────────────
 *
 *   primary.  Rust `TropicalWeight(f64)` accumulates NON-NEGATIVE costs by
 *   real addition (`times = +`, `plus = min`), with multiplicative identity
 *   `one() = 0.0` and `is_one() ⇔ primary == 0.0` (lex_weight.rs:439,
 *   lib.rs:696,716). We model `primary : nat` with `0` = the identity and
 *   `+`/`min`/`≤` the tropical product/sum/order. This is faithful to the
 *   live fragment: every accumulated primary cost is a non-negative finite
 *   real, `total_cmp` agrees with `≤` there, and the ONLY structural fact
 *   the soundness argument uses is "the identity is `0`, product is additive,
 *   the order is total and translation-monotone" — all exactly `nat`.
 *
 *   triple.  The provenance triple `(lex_alt_idx, src_idx, rule_idx)` is
 *   compared lexicographically AFTER primary and is `Eq`-decidable; we model
 *   it as a single opaque `triple : T` with a total order `tri_cmp`. (Folding
 *   the three u16s into one totally-ordered value is sound: lexicographic
 *   product of total orders is a total order, and the proof never inspects
 *   the components — only that the whole-triple order is total and that
 *   `times` left-projects it.)
 *
 *   lex_cmp.  `lex_cmp a b = compare a.primary b.primary` then, on `Eq`,
 *   `tri_cmp a.triple b.triple` — exactly lex_weight.rs:344-352.
 *
 *   times (⊗) — the load-bearing short-circuit.  lex_weight.rs:418-431:
 *       if self.is_one()  then *other            (* primary self = 0 *)
 *       else if other.is_one() then *self        (* primary other = 0 *)
 *       else { primary := self.primary + other.primary; triple := self.triple }
 *   i.e. left-projection of the triple fires ONLY in the `else` arm, where
 *   BOTH primaries are > 0. This is the §8.1 degradation channel and is
 *   reproduced verbatim by `wtimes` below.
 *
 *   plus (⊕).  lex_weight.rs:405-410: lex-min, returning `*self` on `Eq`.
 *   Idempotent, commutative-on-value, associative — the SPPF Goodman fold.
 *
 *   Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Import ListNotations.

(* ════════════════════════════════════════════════════════════════════════
   PART I — the LexicographicWeight algebra (a faithful model of
   rigail/src/lex_weight.rs).
   ════════════════════════════════════════════════════════════════════════ *)

Section LexWeightAlgebra.

  (* The provenance-triple carrier and its total order. We keep it opaque:
     the soundness argument inspects only the order's totality and the fact
     that `times` left-projects it. `T` and `tri_cmp` are parameters of the
     section (NOT axioms — they are universally quantified over below and the
     theorems hold for EVERY such instance). *)
  Variable T : Type.
  Variable tri_cmp : T -> T -> comparison.

  (* The total-order laws tri_cmp must satisfy (these mirror the standard
     `comparison` contract for a lexicographic product of `u16` orders; they
     are HYPOTHESES on the parameter, discharged by `nat`-style instances —
     see the InstantiationSanity section, which gives a concrete T = nat with
     these laws PROVED, so the section is non-vacuous). *)
  Hypothesis tri_cmp_refl  : forall x, tri_cmp x x = Eq.
  Hypothesis tri_cmp_eq    : forall x y, tri_cmp x y = Eq -> x = y.
  Hypothesis tri_cmp_sym   : forall x y, tri_cmp x y = CompOpp (tri_cmp y x).
  Hypothesis tri_cmp_trans :
    forall c x y z, tri_cmp x y = c -> tri_cmp y z = c -> tri_cmp x z = c.

  (* A LexicographicWeight: tropical primary (nat, 0 = multiplicative
     identity) + provenance triple. *)
  Record lex_weight : Type := {
    lw_primary : nat;
    lw_triple  : T
  }.

  (* is_one ⇔ primary == 0.0  (lex_weight.rs:439 → lib.rs:716). *)
  Definition is_one (w : lex_weight) : bool := Nat.eqb (lw_primary w) 0.

  (* lex_cmp: primary (Nat.compare) then, on Eq, tri_cmp.
     (lex_weight.rs:344-352; Nat.compare is the `nat` image of `total_cmp`
     on non-negative finite reals.) *)
  Definition lex_cmp (a b : lex_weight) : comparison :=
    match Nat.compare (lw_primary a) (lw_primary b) with
    | Eq => tri_cmp (lw_triple a) (lw_triple b)
    | c  => c
    end.

  (* ⊗ (times): the EXACT lex_weight.rs:418-431 short-circuit. *)
  Definition wtimes (a b : lex_weight) : lex_weight :=
    if is_one a then b
    else if is_one b then a
    else {| lw_primary := lw_primary a + lw_primary b;
            lw_triple  := lw_triple a |}.

  (* ⊕ (plus): lex-min, returning the left operand on Eq
     (lex_weight.rs:405-410). *)
  Definition wplus (a b : lex_weight) : lex_weight :=
    match lex_cmp a b with
    | Lt | Eq => a
    | Gt      => b
    end.

  (* "a dominates / is at-least-as-good-as b" — the design `≤`:
     `lex_cmp a b ∈ {Lt, Eq}`. *)
  Definition lex_le (a b : lex_weight) : Prop :=
    lex_cmp a b = Lt \/ lex_cmp a b = Eq.

  (* ── Basic order facts derived from the tri_cmp contract. ───────────── *)

  Lemma lex_cmp_refl : forall a, lex_cmp a a = Eq.
  Proof.
    intro a. unfold lex_cmp.
    rewrite Nat.compare_refl. apply tri_cmp_refl.
  Qed.

  Lemma lex_cmp_eq_primary :
    forall a b, lex_cmp a b = Eq -> lw_primary a = lw_primary b.
  Proof.
    intros a b H. unfold lex_cmp in H.
    destruct (Nat.compare (lw_primary a) (lw_primary b)) eqn:E;
      try discriminate.
    apply Nat.compare_eq in E. exact E.
  Qed.

  Lemma lex_cmp_eq :
    forall a b, lex_cmp a b = Eq -> a = b.
  Proof.
    intros a b H.
    pose proof (lex_cmp_eq_primary a b H) as Hp.
    unfold lex_cmp in H. rewrite Hp in H.
    rewrite Nat.compare_refl in H.
    apply tri_cmp_eq in H.
    destruct a as [pa ta]; destruct b as [pb tb].
    simpl in *. subst. reflexivity.
  Qed.

  (* lex_cmp is antisymmetric in the CompOpp sense (a total preorder that is
     a total order on values). *)
  Lemma lex_cmp_sym :
    forall a b, lex_cmp a b = CompOpp (lex_cmp b a).
  Proof.
    intros a b. unfold lex_cmp.
    (* Case on `compare (primary a) (primary b)`; the reverse comparison is
       its CompOpp by Nat.compare_antisym. *)
    destruct (Nat.compare (lw_primary a) (lw_primary b)) eqn:Eab.
    - (* primaries equal ⇒ reverse also Eq ⇒ both branches chase triple. *)
      apply Nat.compare_eq in Eab. rewrite Eab.
      rewrite Nat.compare_refl. apply tri_cmp_sym.
    - (* primary a < primary b ⇒ reverse is Gt ⇒ CompOpp Gt = Lt. *)
      rewrite (Nat.compare_antisym (lw_primary a) (lw_primary b)).
      rewrite Eab. reflexivity.
    - (* primary a > primary b ⇒ reverse is Lt ⇒ CompOpp Lt = Gt. *)
      rewrite (Nat.compare_antisym (lw_primary a) (lw_primary b)).
      rewrite Eab. reflexivity.
  Qed.

  Lemma lex_cmp_lt_gt :
    forall a b, lex_cmp a b = Lt -> lex_cmp b a = Gt.
  Proof.
    intros a b H.
    rewrite (lex_cmp_sym b a). rewrite H. reflexivity.
  Qed.

  Lemma lex_cmp_gt_lt :
    forall a b, lex_cmp a b = Gt -> lex_cmp b a = Lt.
  Proof.
    intros a b H.
    rewrite (lex_cmp_sym b a). rewrite H. reflexivity.
  Qed.

  (* Transitivity of `≤` (Lt/Eq), needed for the min-fold reasoning. *)
  (* NOTE (failed strategy, recorded per CLAUDE.md so it is not re-attempted):
     `destruct ...; subst c; try discriminate` is WRONG here. `subst c`
     substitutes `c` with `tri_cmp (lw_triple a) (lw_triple b)` (taken from
     the hypothesis `Hab : ... = c`), NOT with the constructor `Eq` — so the
     goal RHS becomes a `tri_cmp` term and the chaining breaks. The correct
     idiom keeps `Hab`/`Hbd` as `... = c` and applies `tri_cmp_trans` / uses
     `c` symbolically per primary-comparison case. *)
  Lemma lex_cmp_trans :
    forall c a b d, lex_cmp a b = c -> lex_cmp b d = c -> lex_cmp a d = c.
  Proof.
    intros c a b d Hab Hbd. unfold lex_cmp in *.
    (* Nine primary-comparison cases. `destruct ... eqn:E` substitutes the
       match scrutinee in Hab/Hbd, so Hab/Hbd are `Lt = c` / `Gt = c` (off
       the diagonal) or the triple comparison `= c` (on the Eq diagonal).
       The two cross cases (Lt/Gt, Gt/Lt) are impossible: Hab and Hbd then
       force `Lt = c` and `Gt = c` ⇒ congruence. *)
    destruct (Nat.compare (lw_primary a) (lw_primary b)) eqn:Eab;
    destruct (Nat.compare (lw_primary b) (lw_primary d)) eqn:Ebd.
    - (* Eq / Eq: chase the triple via tri_cmp_trans. *)
      apply Nat.compare_eq in Eab. apply Nat.compare_eq in Ebd.
      rewrite Eab, Ebd. rewrite Nat.compare_refl.
      apply (tri_cmp_trans c (lw_triple a) (lw_triple b) (lw_triple d));
        assumption.
    - (* Eq / Lt ⇒ a<d primary; Hbd : Lt = c. *)
      apply Nat.compare_eq in Eab. rewrite Eab. rewrite Ebd. exact Hbd.
    - (* Eq / Gt ⇒ a>d primary; Hbd : Gt = c. *)
      apply Nat.compare_eq in Eab. rewrite Eab. rewrite Ebd. exact Hbd.
    - (* Lt / Eq ⇒ a<d primary; Hab : Lt = c. *)
      apply Nat.compare_eq in Ebd. rewrite <- Ebd. rewrite Eab. exact Hab.
    - (* Lt / Lt ⇒ a<d primary; Hab : Lt = c. *)
      apply Nat.compare_lt_iff in Eab. apply Nat.compare_lt_iff in Ebd.
      rewrite (proj2 (Nat.compare_lt_iff _ _) (Nat.lt_trans _ _ _ Eab Ebd)).
      exact Hab.
    - (* Lt / Gt: impossible — Hab : Lt = c, Hbd : Gt = c. *)
      congruence.
    - (* Gt / Eq ⇒ a>d primary; Hab : Gt = c. *)
      apply Nat.compare_eq in Ebd. rewrite <- Ebd. rewrite Eab. exact Hab.
    - (* Gt / Lt: impossible — Hab : Gt = c, Hbd : Lt = c. *)
      congruence.
    - (* Gt / Gt ⇒ a>d primary; Hab : Gt = c. *)
      apply Nat.compare_gt_iff in Eab. apply Nat.compare_gt_iff in Ebd.
      rewrite (proj2 (Nat.compare_gt_iff _ _) (Nat.lt_trans _ _ _ Ebd Eab)).
      exact Hab.
  Qed.

  (* lex_le is reflexive and transitive (a preorder), and total. *)
  Lemma lex_le_refl : forall a, lex_le a a.
  Proof. intro a. right. apply lex_cmp_refl. Qed.

  Lemma lex_le_trans : forall a b d, lex_le a b -> lex_le b d -> lex_le a d.
  Proof.
    intros a b d [Hab | Hab] [Hbd | Hbd].
    - left. eapply lex_cmp_trans; eassumption.
    - apply lex_cmp_eq in Hbd. subst d. left. exact Hab.
    - apply lex_cmp_eq in Hab. subst b. left. exact Hbd.
    - apply lex_cmp_eq in Hab. subst b. right. exact Hbd.
  Qed.

  Lemma lex_le_total : forall a b, lex_le a b \/ lex_le b a.
  Proof.
    intros a b. unfold lex_le.
    destruct (lex_cmp a b) eqn:E.
    - left. right. reflexivity.
    - left. left. reflexivity.
    - right. left. apply lex_cmp_gt_lt. exact E.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     L1 — DOMINANCE MONOTONE UNDER COMMON CONTINUATION.

     For weights s, c with `lex_le s c` and ANY continuation w,
     `lex_le (wtimes s w) (wtimes c w)`.

     This is the §4.2/§8.1 core lemma, encoding the `is_one` short-circuit
     FAITHFULLY: the proof case-splits on `is_one s`, `is_one c`, `is_one w`
     exactly as `wtimes` does, and is honest that a `Lt` may DEGRADE to `Eq`
     (it proves the `≤` relation `lex_le`, never the strict `<`).
     ════════════════════════════════════════════════════════════════════ *)

  (* The continuation w is applied to BOTH s and c (the §4.2 "common
     continuation": s and c share a ConfigKey, so the engine's pure step
     function produces the SAME next weight increment w for both). *)
  Theorem dominance_monotone_under_common_continuation :
    forall s c w,
      lex_le s c ->
      lex_le (wtimes s w) (wtimes c w).
  Proof.
    intros s c w Hsc.
    unfold wtimes.
    (* Case on the three short-circuit conditions, mirroring wtimes. *)
    destruct (is_one s) eqn:His; destruct (is_one c) eqn:Hic.
    - (* s,c both identity (primary 0). wtimes s w = w = wtimes c w. *)
      apply lex_le_refl.
    - (* s identity, c not. wtimes s w = w; wtimes c w = (case on w). *)
      (* From lex_le s c with s.primary = 0: c.primary >= 0; but Hic says
         c not identity ⇒ c.primary > 0. We must show lex_le w (wtimes c w).
         wtimes c w: if is_one w then c else (c.primary + w.primary, c.triple).
         We show w ≤ that result via the primary order. *)
      unfold is_one in His. apply Nat.eqb_eq in His.
      unfold is_one in Hic. apply Nat.eqb_neq in Hic.
      destruct (is_one w) eqn:Hiw.
      + (* wtimes c w = c. Show lex_le w c.
           w identity ⇒ w.primary = 0 = s.primary; and lex_le s c.
           Since s.primary = 0 = w.primary, and c.primary > 0,
           primary w (=0) < primary c ⇒ lex_cmp w c = Lt. *)
        unfold is_one in Hiw. apply Nat.eqb_eq in Hiw.
        left. unfold lex_cmp. rewrite Hiw.
        assert (Hlt : 0 < lw_primary c) by lia.
        rewrite (proj2 (Nat.compare_lt_iff 0 (lw_primary c)) Hlt).
        reflexivity.
      + (* wtimes c w = (c.primary + w.primary, c.triple). Show
           lex_le w (that). w not identity ⇒ w.primary > 0; result primary
           = c.primary + w.primary > w.primary (c.primary > 0). *)
        unfold is_one in Hiw. apply Nat.eqb_neq in Hiw.
        left. unfold lex_cmp. simpl.
        assert (Hlt : lw_primary w < lw_primary c + lw_primary w) by lia.
        rewrite (proj2 (Nat.compare_lt_iff _ _) Hlt). reflexivity.
    - (* c identity, s not. wtimes c w = w; wtimes s w = (case on w).
         From lex_le s c with c.primary = 0: lex_cmp s c ∈ {Lt,Eq}.
         lex_cmp s c primary part = compare s.primary 0. If s.primary > 0
         that is Gt, contradicting lex_le. So s.primary = 0 — but His says s
         not identity ⇒ s.primary > 0. CONTRADICTION: this case is vacuous. *)
      exfalso.
      unfold is_one in His. apply Nat.eqb_neq in His.
      unfold is_one in Hic. apply Nat.eqb_eq in Hic.
      destruct Hsc as [H | H]; unfold lex_cmp in H; rewrite Hic in H.
      + (* lex_cmp = Lt: compare s.primary 0 — s.primary>0 ⇒ Gt, not Lt *)
        assert (Hgt : 0 < lw_primary s) by lia.
        rewrite (proj2 (Nat.compare_gt_iff _ _) Hgt) in H. discriminate.
      + assert (Hgt : 0 < lw_primary s) by lia.
        rewrite (proj2 (Nat.compare_gt_iff _ _) Hgt) in H. discriminate.
    - (* s,c both NON-identity. wtimes left-projects each triple and adds
         the SAME w.primary (if w non-identity) or returns each whole (if w
         identity). This is the §8.1 "frozen triple" arm. *)
      unfold is_one in His. apply Nat.eqb_neq in His.
      unfold is_one in Hic. apply Nat.eqb_neq in Hic.
      destruct (is_one w) eqn:Hiw.
      + (* w identity ⇒ wtimes s w = s, wtimes c w = c. Order = lex_le s c. *)
        exact Hsc.
      + (* w non-identity. wtimes s w = (s.primary+w.primary, s.triple);
           wtimes c w = (c.primary+w.primary, c.triple). The primaries get
           the SAME +w.primary increment, triples are each left-projected
           UNCHANGED (frozen). So the order is preserved EXACTLY. *)
        destruct Hsc as [Hlt | Heq].
        * (* lex_cmp s c = Lt. Decompose: either primary s < primary c, or
             primaries equal and triple s < triple c. Both ⇒ Lt after +w. *)
          left. unfold lex_cmp in *. simpl.
          destruct (Nat.compare (lw_primary s) (lw_primary c)) eqn:Ep;
            try discriminate.
          -- (* primaries equal ⇒ adding w keeps them equal; triple part
                identical to the pre-times lex_cmp ⇒ still Lt. *)
             apply Nat.compare_eq in Ep. rewrite Ep.
             rewrite Nat.compare_refl. exact Hlt.
          -- (* primary s < primary c ⇒ s.primary+w < c.primary+w *)
             apply Nat.compare_lt_iff in Ep.
             assert (Hlt' : lw_primary s + lw_primary w
                            < lw_primary c + lw_primary w) by lia.
             rewrite (proj2 (Nat.compare_lt_iff _ _) Hlt'). reflexivity.
        * (* lex_cmp s c = Eq ⇒ s = c ⇒ wtimes equal ⇒ Eq. *)
          apply lex_cmp_eq in Heq. subst c. apply lex_le_refl.
  Qed.

  (* The headline corollary in the design's `∈ {Lt, Eq}` phrasing. *)
  Corollary dominance_cmp_in_lt_eq :
    forall s c w,
      (lex_cmp s c = Lt \/ lex_cmp s c = Eq) ->
      (lex_cmp (wtimes s w) (wtimes c w) = Lt \/
       lex_cmp (wtimes s w) (wtimes c w) = Eq).
  Proof.
    intros s c w H.
    apply (dominance_monotone_under_common_continuation s c w H).
  Qed.

  (* §8.1 honesty witness (NON-VACUITY of the degradation): there EXIST s, c,
     w with `lex_cmp s c = Lt` (strict) but `lex_cmp (s⊗w) (c⊗w) = Eq`. This
     is the "Less degrades to Equal" channel: s is at identity (primary 0),
     c differs from s only in the TRIPLE (same primary 0 is impossible since
     then s=c; so c has primary 0 too but a larger triple — then is_one c is
     true and c ⊗ w = w = s ⊗ w). Concretely with the nat instance below. *)
  (* (The concrete witness is discharged in InstantiationSanity, where T is
     instantiated, so it is a closed theorem, not a parametric claim.) *)

End LexWeightAlgebra.

(* ════════════════════════════════════════════════════════════════════════
   PART II — L2: lex_min invariant under dropping a dominated element.

   We work over an explicit decidable element type with a lex_cmp-style total
   order, fold the list with `wplus` (= lex-min), and prove that removing a
   dominated element does not change the fold. The triple order is again a
   parameter with the same total-order contract.
   ════════════════════════════════════════════════════════════════════════ *)

Section LexMinDropDominated.

  Variable T : Type.
  Variable tri_cmp : T -> T -> comparison.
  Hypothesis tri_cmp_refl  : forall x, tri_cmp x x = Eq.
  Hypothesis tri_cmp_eq    : forall x y, tri_cmp x y = Eq -> x = y.
  Hypothesis tri_cmp_sym   : forall x y, tri_cmp x y = CompOpp (tri_cmp y x).
  Hypothesis tri_cmp_trans :
    forall c x y z, tri_cmp x y = c -> tri_cmp y z = c -> tri_cmp x z = c.
  (* Decidable equality on weights — needed to `remove` an element. It is
     derivable from tri_cmp_eq + nat eq, but we take it as a (discharged)
     parameter to keep the fold reasoning crisp; the nat instance proves it. *)
  Variable weq_dec :
    forall x y : lex_weight T, {x = y} + {x <> y}.

  Notation lw := (lex_weight T).
  Notation cmp := (lex_cmp T tri_cmp).
  Notation le := (lex_le T tri_cmp).
  Notation plus := (wplus T tri_cmp).

  (* Re-export the order facts under this section's parameters. *)
  Local Lemma cmp_refl : forall a, cmp a a = Eq.
  Proof. exact (lex_cmp_refl T tri_cmp tri_cmp_refl). Qed.
  Local Lemma cmp_eq : forall a b, cmp a b = Eq -> a = b.
  Proof. exact (lex_cmp_eq T tri_cmp tri_cmp_eq). Qed.
  Local Lemma le_refl : forall a, le a a.
  Proof. exact (lex_le_refl T tri_cmp tri_cmp_refl). Qed.
  Local Lemma le_trans : forall a b d, le a b -> le b d -> le a d.
  Proof. exact (lex_le_trans T tri_cmp tri_cmp_eq tri_cmp_trans). Qed.
  Local Lemma le_total : forall a b, le a b \/ le b a.
  Proof. exact (lex_le_total T tri_cmp tri_cmp_sym). Qed.

  (* wplus is the lex-min: it returns whichever operand is `le` the other,
     biased to the left on ties. The two facts the fold needs: *)
  Lemma wplus_le_left : forall a b, le a b -> plus a b = a.
  Proof.
    intros a b [H | H]; unfold wplus; rewrite H; reflexivity.
  Qed.

  Lemma wplus_result_le_both :
    forall a b, le (plus a b) a /\ le (plus a b) b.
  Proof.
    intros a b. unfold wplus.
    destruct (cmp a b) eqn:E.
    - (* Eq: plus = a. a ≤ a, and a ≤ b since cmp a b = Eq. *)
      split.
      + apply le_refl.
      + right. exact E.
    - (* Lt: plus = a. a ≤ a, a ≤ b. *)
      split.
      + apply le_refl.
      + left. exact E.
    - (* Gt: plus = b. b ≤ a (from cmp a b = Gt ⇒ cmp b a = Lt), b ≤ b. *)
      split.
      + left. apply (lex_cmp_gt_lt T tri_cmp tri_cmp_sym). exact E.
      + apply le_refl.
  Qed.

  Lemma wplus_chooses_one :
    forall a b, plus a b = a \/ plus a b = b.
  Proof.
    intros a b. unfold wplus. destruct (cmp a b); auto.
  Qed.

  (* lex_min of a NON-EMPTY list: fold wplus over the tail starting from the
     head. (`min_by(weight)` over the accept frontier — facade.rs:142-149.) *)
  Fixpoint lex_min (seed : lw) (rest : list lw) : lw :=
    match rest with
    | [] => seed
    | x :: xs => lex_min (plus seed x) xs
    end.

  (* The fold's result is `le` the seed and `le` every element. *)
  Lemma lex_min_le_seed : forall rest seed, le (lex_min seed rest) seed.
  Proof.
    induction rest as [| x xs IH]; intro seed; simpl.
    - apply le_refl.
    - eapply le_trans.
      + apply IH.
      + apply (proj1 (wplus_result_le_both seed x)).
  Qed.

  Lemma lex_min_le_elem :
    forall rest seed x, In x rest -> le (lex_min seed rest) x.
  Proof.
    induction rest as [| y ys IH]; intros seed x Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst y. eapply le_trans.
        * apply lex_min_le_seed.
        * apply (proj2 (wplus_result_le_both seed x)).
      + apply IH. exact Hin.
  Qed.

  (* Adding an element x that is dominated by the current accumulator does not
     change the fold from that accumulator: plus seed x = seed when seed ≤ x. *)
  Lemma lex_min_absorb_dominated_head :
    forall xs seed x,
      le seed x ->
      lex_min seed (x :: xs) = lex_min seed xs.
  Proof.
    intros xs seed x Hle. simpl. rewrite (wplus_le_left seed x Hle).
    reflexivity.
  Qed.

  (* The fold is INSENSITIVE to the seed beyond the lex-min value: two seeds
     that are `≤`-equivalent (each ≤ the other ⇒ equal, by antisymmetry)
     give the same result. More usefully, the fold value equals the global
     lex-min of (seed :: rest). We capture exactly what L2 needs:
     the fold is invariant under inserting/removing a dominated element. *)

  (* The KEY structural lemma: if x is dominated by SOME element already in
     the fold input (seed or a member of rest), then folding with x present
     equals folding with x absent. We prove the head/seed-anchored version
     and the in-rest version, then assemble L2. *)

  (* Helper: wplus is "commutative up to the result value" — folding seed
     then x equals the lex-min of {seed, x} regardless of order, and that
     lex-min is order-independent on VALUE. We need: plus (plus a x) y has
     the same VALUE as plus (plus a y) x when reasoning about reordering. We
     avoid full AC by instead proving the targeted invariance via the global
     characterization below. *)

  (* Global characterization: lex_min seed rest is the UNIQUE element m of
     (seed :: rest) with m ≤ every element of (seed :: rest) AND m is the
     left-most such (tie-break). For L2 we only need the ≤-extremal value, so
     we characterize the RESULT as a least element of the multiset. *)

  Definition is_in_all (m : lw) (seed : lw) (rest : list lw) : Prop :=
    le m seed /\ forall y, In y rest -> le m y.

  Lemma lex_min_is_least :
    forall rest seed, is_in_all (lex_min seed rest) seed rest.
  Proof.
    intros rest seed. unfold is_in_all. split.
    - apply lex_min_le_seed.
    - intros y Hin. apply lex_min_le_elem. exact Hin.
  Qed.

  Lemma lex_min_is_member :
    forall rest seed, lex_min seed rest = seed \/ In (lex_min seed rest) rest.
  Proof.
    induction rest as [| x xs IH]; intro seed; simpl.
    - left. reflexivity.
    - destruct (IH (plus seed x)) as [Heq | Hin].
      + (* lex_min (plus seed x) xs = plus seed x; that is seed or x *)
        rewrite Heq. destruct (wplus_chooses_one seed x) as [H | H].
        * left. exact H.
        * right. left. symmetry. exact H.
      + right. right. exact Hin.
  Qed.

  (* Antisymmetry: le a b and le b a ⇒ a = b. *)
  Lemma le_antisym : forall a b, le a b -> le b a -> a = b.
  Proof.
    intros a b [Hab | Hab] [Hba | Hba].
    - (* both strict: cmp a b = Lt and cmp b a = Lt — impossible since
         cmp a b = Lt ⇒ cmp b a = Gt (lex_cmp_lt_gt), contradicting Hba. *)
      exfalso. pose proof (lex_cmp_lt_gt T tri_cmp tri_cmp_sym a b Hab) as Hgt.
      rewrite Hba in Hgt. discriminate.
    - apply cmp_eq in Hba. symmetry. exact Hba.
    - apply cmp_eq in Hab. exact Hab.
    - apply cmp_eq in Hab. exact Hab.
  Qed.

  (* A least element of a multiset is unique up to VALUE: any two elements
     each ≤ everything (and members) are equal. We use this to show the fold
     value is stable when we drop a dominated (non-least) element. *)
  Lemma least_unique :
    forall seed rest m1 m2,
      is_in_all m1 seed rest -> (m1 = seed \/ In m1 rest) ->
      is_in_all m2 seed rest -> (m2 = seed \/ In m2 rest) ->
      m1 = m2.
  Proof.
    intros seed rest m1 m2 [H1s H1r] H1mem [H2s H2r] H2mem.
    apply le_antisym.
    - (* m1 ≤ m2: m2 is seed or in rest, m1 ≤ both. *)
      destruct H2mem as [He | Hin].
      + subst m2. exact H1s.
      + apply H1r. exact Hin.
    - destruct H1mem as [He | Hin].
      + subst m1. exact H2s.
      + apply H2r. exact Hin.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     L2 — lex_min invariant under dropping a DOMINATED element.

     If c ∈ (seed :: rest) and some s ∈ (seed :: rest) with s ≠ c and
     `le s c` (s dominates c, kept), then the fold value is unchanged when c
     is removed. We phrase it on the WHOLE multiset M = seed :: rest and use
     `remove` (decidable on weights).
     ════════════════════════════════════════════════════════════════════ *)

  (* `remove` one occurrence-set of c from a list (Coq's List.remove removes
     ALL occurrences; for a multiset min that is fine — every copy of c is
     dominated by s, so dropping all copies is still covered by s). *)

  (* The fold over a permutation/sublist is characterized by its least
     element. We prove: lex_min over M and lex_min over (M minus all c) have
     the same is_in_all witness when c is dominated by a surviving s, hence
     are equal by least_unique. We reformulate the fold over a single list
     argument to apply the characterization uniformly. *)

  (* fold over a non-empty list given as its element list (head-anchored). *)
  Definition lex_min_list (M : list lw) : option lw :=
    match M with
    | [] => None
    | x :: xs => Some (lex_min x xs)
    end.

  Lemma lex_min_list_is_least :
    forall M m, lex_min_list M = Some m ->
      (forall y, In y M -> le m y) /\ In m M.
  Proof.
    intros [| x xs] m H; simpl in H; [discriminate |].
    inversion H; subst m. split.
    - intros y [Hhd | Hin].
      + subst y. apply lex_min_le_seed.
      + apply lex_min_le_elem. exact Hin.
    - destruct (lex_min_is_member xs x) as [He | Hin].
      + left. symmetry. exact He.
      + right. exact Hin.
  Qed.

  (* The substantive theorem. Removing every copy of a dominated c (covered
     by a surviving s ≠ c, s ∈ M) leaves the lex_min value unchanged. *)
  Theorem lex_min_invariant_under_dropping_dominated :
    forall M s c,
      In s M -> In c M -> s <> c -> le s c ->
      lex_min_list M = lex_min_list (remove weq_dec c M).
  Proof.
    intros M s c Hs Hc Hsc Hle.
    (* M is non-empty (contains s). The reduced list still contains s
       (s ≠ c ⇒ s survives the remove). So both folds are Some. *)
    assert (HsR : In s (remove weq_dec c M)).
    { apply in_in_remove; [exact Hsc | exact Hs]. }
    destruct M as [| x xs] eqn:EM; [destruct Hs |].
    (* both lex_min_list are Some _ ; name them. *)
    remember (x :: xs) as M0 eqn:HM0.
    assert (HM0ne : M0 <> []) by (subst M0; discriminate).
    assert (HRne : remove weq_dec c M0 <> []).
    { intro Hnil. rewrite Hnil in HsR. destruct HsR. }
    destruct (lex_min_list M0) as [m |] eqn:Em.
    2:{ subst M0. simpl in Em. discriminate. }
    destruct (lex_min_list (remove weq_dec c M0)) as [mR |] eqn:EmR.
    2:{ destruct (remove weq_dec c M0) eqn:Erm.
        - contradiction.
        - simpl in EmR. discriminate. }
    f_equal.
    (* Show m = mR by least_unique-style antisymmetry over the two lists. *)
    pose proof (lex_min_list_is_least M0 m Em) as [HmAll HmIn].
    pose proof (lex_min_list_is_least (remove weq_dec c M0) mR EmR)
      as [HmRAll HmRIn].
    apply le_antisym.
    - (* m ≤ mR: mR ∈ remove _ c M0 ⊆ M0, and m ≤ everything in M0. *)
      apply HmAll. apply in_remove in HmRIn. destruct HmRIn as [HmRin _].
      exact HmRin.
    - (* mR ≤ m: m ∈ M0. Two cases: m = c or m ≠ c.
         If m ≠ c, m survives the remove ⇒ m ∈ remove _ c M0 ⇒ mR ≤ m.
         If m = c, then s ≤ c = m, and s ∈ remove _ c M0 ⇒ mR ≤ s ≤ m. *)
      destruct (weq_dec m c) as [Hmc | Hmc].
      + (* m = c: chase through s. *)
        subst m. eapply le_trans.
        * apply HmRAll. exact HsR.
        * exact Hle.
      + (* m ≠ c: m survives. *)
        apply HmRAll. apply in_in_remove; [exact Hmc | exact HmIn].
  Qed.

  (* Direct corollary in the design's phrasing: dropping a dominated cursor
     preserves the single-result min_by(weight) selection. The single-result
     facade returns `Some (lex_min_list frontier)`; the theorem says that
     value is identical with c removed. *)
  Corollary single_result_min_unchanged_by_dropping_dominated :
    forall frontier s c,
      In s frontier -> In c frontier -> s <> c -> le s c ->
      lex_min_list frontier = lex_min_list (remove weq_dec c frontier).
  Proof.
    intros frontier s c Hs Hc Hsc Hle.
    apply (lex_min_invariant_under_dropping_dominated frontier s c);
      assumption.
  Qed.

End LexMinDropDominated.

(* ════════════════════════════════════════════════════════════════════════
   PART III — INSTANTIATION SANITY (non-vacuity).

   We instantiate T = nat with tri_cmp = Nat.compare, PROVING the four
   total-order hypotheses and weq_dec. This shows the parametric sections are
   non-vacuous (there is a real model) and discharges the §8.1 NON-VACUITY
   witness (a strict Lt that degrades to Eq under ⊗) as a CLOSED theorem.
   ════════════════════════════════════════════════════════════════════════ *)

Section InstantiationSanity.

  (* The triple modelled as a single nat (a faithful fold of the three u16
     tiebreaks into one totally-ordered value; see the fidelity note). *)
  Definition nat_tri_cmp := Nat.compare.

  Lemma nat_tri_cmp_refl : forall x, nat_tri_cmp x x = Eq.
  Proof. intro x. apply Nat.compare_refl. Qed.

  Lemma nat_tri_cmp_eq : forall x y, nat_tri_cmp x y = Eq -> x = y.
  Proof. intros x y H. apply Nat.compare_eq. exact H. Qed.

  Lemma nat_tri_cmp_sym :
    forall x y, nat_tri_cmp x y = CompOpp (nat_tri_cmp y x).
  Proof. intros x y. apply Nat.compare_antisym. Qed.

  Lemma nat_tri_cmp_trans :
    forall c x y z,
      nat_tri_cmp x y = c -> nat_tri_cmp y z = c -> nat_tri_cmp x z = c.
  Proof.
    intros c x y z Hxy Hyz. unfold nat_tri_cmp in *.
    destruct c.
    - apply Nat.compare_eq in Hxy. apply Nat.compare_eq in Hyz.
      subst. apply Nat.compare_refl.
    - apply Nat.compare_lt_iff in Hxy. apply Nat.compare_lt_iff in Hyz.
      apply Nat.compare_lt_iff. lia.
    - apply Nat.compare_gt_iff in Hxy. apply Nat.compare_gt_iff in Hyz.
      apply Nat.compare_gt_iff. lia.
  Qed.

  Lemma nat_lw_eq_dec :
    forall x y : lex_weight nat, {x = y} + {x <> y}.
  Proof.
    intros [pa ta] [pb tb].
    destruct (Nat.eq_dec pa pb) as [Hp | Hp];
    destruct (Nat.eq_dec ta tb) as [Ht | Ht];
      subst; auto;
      right; intro H; inversion H; contradiction.
  Defined.

  Notation NW := (lex_weight nat).
  Notation Ncmp := (lex_cmp nat nat_tri_cmp).
  Notation Ntimes := (wtimes nat).
  Notation Nle := (lex_le nat nat_tri_cmp).

  (* The instantiated L1 — a CLOSED theorem (no free hypotheses). *)
  Theorem nat_L1_dominance_monotone :
    forall s c w, Nle s c -> Nle (Ntimes s w) (Ntimes c w).
  Proof.
    apply (dominance_monotone_under_common_continuation
             nat nat_tri_cmp nat_tri_cmp_refl nat_tri_cmp_eq).
  Qed.

  (* The instantiated L2 — a CLOSED theorem. *)
  Theorem nat_L2_min_invariant :
    forall M s c,
      In s M -> In c M -> s <> c -> Nle s c ->
      lex_min_list nat nat_tri_cmp M
      = lex_min_list nat nat_tri_cmp (remove nat_lw_eq_dec c M).
  Proof.
    intros M s c Hs Hc Hsc Hle.
    apply (lex_min_invariant_under_dropping_dominated
             nat nat_tri_cmp nat_tri_cmp_refl nat_tri_cmp_eq nat_tri_cmp_sym
             nat_tri_cmp_trans nat_lw_eq_dec M s c);
      assumption.
  Qed.

  (* §8.1 NON-VACUITY of the "Less degrades to Equal" channel, as a closed
     theorem. Take s with primary 0, triple 0; c with primary 0, triple 1;
     w with primary 0 (identity). Then:
       Ncmp s c = Lt          (same primary 0, triple 0 < 1)
       Ntimes s w = s (is_one s) ... actually is_one s true ⇒ Ntimes s w = w,
       Ntimes c w = w (is_one c true) ⇒ both = w ⇒ Ncmp (s⊗w)(c⊗w) = Eq.
     The strict Lt collapsed to Eq — exactly the design's degradation, and it
     is HARMLESS (both map to the same continuation value, so min_by keeps a
     valid winner). *)
  Definition s_lt : NW := {| lw_primary := 0; lw_triple := 0 |}.
  Definition c_lt : NW := {| lw_primary := 0; lw_triple := 1 |}.
  Definition w_id : NW := {| lw_primary := 0; lw_triple := 7 |}.

  Theorem nat_less_degrades_to_equal_under_times :
    Ncmp s_lt c_lt = Lt /\
    Ncmp (Ntimes s_lt w_id) (Ntimes c_lt w_id) = Eq.
  Proof.
    split.
    - unfold lex_cmp, s_lt, c_lt, nat_tri_cmp. simpl. reflexivity.
    - unfold wtimes, is_one, s_lt, c_lt, w_id. simpl.
      (* is_one s_lt = (0 =? 0) = true ⇒ both ⊗ collapse to w_id *)
      unfold lex_cmp, nat_tri_cmp. simpl. reflexivity.
  Qed.

  (* And the order is NEVER inverted (the safety direction), as a closed
     instance of L1: from Lt we get Lt ∨ Eq, never Gt. *)
  Theorem nat_strict_never_inverts :
    forall s c w,
      Ncmp s c = Lt ->
      Ncmp (Ntimes s w) (Ntimes c w) <> Gt.
  Proof.
    intros s c w Hlt Hgt.
    assert (Hle : Nle s c) by (left; exact Hlt).
    pose proof (nat_L1_dominance_monotone s c w Hle) as [H | H];
      rewrite Hgt in H; discriminate.
  Qed.

End InstantiationSanity.

(* ════════════════════════════════════════════════════════════════════════
   PART IV — TOP-LEVEL: connection to the parser.

   The single-result facade (`Cat::parse`, facade.rs:142-149) realizes
   `min_by(weight)` over the accept frontier. The subsumption pass
   (`subsume_weight_dominated_when_single_result`, c45bdea2) drops a cursor c
   that shares a ConfigKey (SubsumeConfigKey, §8.3) with a surviving cursor s
   and is dominated by it (`le s c`). We model the realized-winner selection
   as the lex_min over the accept-weight frontier, and conclude the winner is
   unchanged by the subsumption (L2), provided the dropped weight still has a
   surviving dominator in the frontier (the pass's invariant: it KEEPS the
   lex-min representative per config, so any dropped cursor's weight is
   dominated by the kept one — and the kept one's accept-weight is in the
   frontier by L1, since s reaches at least as good an accept as c).
   ════════════════════════════════════════════════════════════════════════ *)

Section ParserConnection.

  (* Accept-frontier weights are nat-triple LexicographicWeights (the live
     model). The realized single-result winner is their lex-min. *)
  Notation NW := (lex_weight nat).
  Notation Nle := (lex_le nat nat_tri_cmp).

  Definition realized_winner (frontier : list NW) : option NW :=
    lex_min_list nat nat_tri_cmp frontier.

  (* THE TOP-LEVEL SOUNDNESS THEOREM. Dropping a dominated same-config cursor
     weight c (covered by a surviving s ≠ c in the frontier) leaves the
     single-result realized winner unchanged.

     This is the machine-checked form of §4.2's "Single-result min_by(weight)
     is invariant under the subsumption" and §6.5's requested lemma
     `single_result_dominance_preserves_min`. *)
  Theorem single_result_subsumption_preserves_selection :
    forall frontier s c,
      In s frontier ->        (* the surviving lex-min representative *)
      In c frontier ->        (* the dropped dominated cursor's accept weight *)
      s <> c ->
      Nle s c ->              (* s dominates c (the §4.1 dominance predicate) *)
      realized_winner frontier
      = realized_winner (remove nat_lw_eq_dec c frontier).
  Proof.
    intros frontier s c Hs Hc Hsc Hle.
    unfold realized_winner.
    apply (nat_L2_min_invariant frontier s c); assumption.
  Qed.

  (* Multi-element corollary by induction: dropping a whole SET of dominated
     cursors (each covered by a surviving dominator) preserves the winner.
     Modelled as repeated single-element drops; each drop preserves the
     winner AND keeps the surviving dominator s present (s ≠ each dropped
     c). *)
  Fixpoint drop_all (cs : list NW) (frontier : list NW) : list NW :=
    match cs with
    | [] => frontier
    | c :: rest => drop_all rest (remove nat_lw_eq_dec c frontier)
    end.

  (* If every dropped weight equals a single fixed s? No — too strong. The
     realistic invariant the PASS guarantees is: there is ONE surviving
     representative s (the lex-min of the whole config-class) that dominates
     every dropped cursor of that class, and s is itself never dropped. We
     prove the iterated preservation under exactly that hypothesis. *)
  Theorem single_result_subsumption_preserves_selection_iterated :
    forall cs s frontier,
      In s frontier ->
      (forall c, In c cs -> s <> c /\ Nle s c) ->
      realized_winner frontier = realized_winner (drop_all cs frontier).
  Proof.
    induction cs as [| c rest IH]; intros s frontier Hs Hdom; simpl.
    - reflexivity.
    - (* Drop c first (dominated by s, s ≠ c), then recurse: s still present
         in the reduced frontier (s ≠ c ⇒ survives remove). *)
      destruct (Hdom c (or_introl eq_refl)) as [Hsc Hle].
      (* c may or may not be in frontier; split cleanly. If c ∉ frontier the
         remove is a no-op and the winner is trivially unchanged for this
         step. If c ∈ frontier, apply the single-element theorem. *)
      destruct (In_dec nat_lw_eq_dec c frontier) as [Hin | Hnin].
      + rewrite (single_result_subsumption_preserves_selection
                   frontier s c Hs Hin Hsc Hle).
        apply (IH s).
        * apply in_in_remove; [exact Hsc | exact Hs].
        * intros c' Hc'. apply Hdom. right. exact Hc'.
      + (* c ∉ frontier ⇒ remove _ c frontier = frontier. *)
        rewrite notin_remove; [| exact Hnin].
        apply (IH s).
        * exact Hs.
        * intros c' Hc'. apply Hdom. right. exact Hc'.
  Qed.

End ParserConnection.

(* ════════════════════════════════════════════════════════════════════════
   ASSUMPTION AUDIT — every theorem closed under the global context.
   ════════════════════════════════════════════════════════════════════════ *)

(* PART I/II are parametric (the tri_cmp total-order contract is a section
   HYPOTHESIS, discharged by the nat instance in PART III); these prints
   confirm no Axiom/Admitted leaked into the parametric proofs themselves. *)
Print Assumptions dominance_monotone_under_common_continuation.
Print Assumptions lex_min_invariant_under_dropping_dominated.

(* PART III/IV are CLOSED theorems (instantiated / parser-facing). *)
Print Assumptions nat_L1_dominance_monotone.
Print Assumptions nat_L2_min_invariant.
Print Assumptions nat_less_degrades_to_equal_under_times.
Print Assumptions nat_strict_never_inverts.
Print Assumptions single_result_subsumption_preserves_selection.
Print Assumptions single_result_subsumption_preserves_selection_iterated.
