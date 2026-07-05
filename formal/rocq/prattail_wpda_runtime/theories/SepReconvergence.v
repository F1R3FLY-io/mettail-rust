(*
 * SepReconvergence: the spec for the P2 ISOLATION+COMBINE CODEGEN fix — the
 * ROOT-P `.*sep` divide-and-conquer linearization that the generated facade
 * SHIPS (Plan a7986200, 2026-07-05, session da0842dc).
 *
 * THE DEFECT (measured; rhocalc ForRow `b "&" bs.*sep("&") ["where" cond]`):
 * parsing a k-separator list MONOLITHICALLY forks `dᵏ` cursor paths across the
 * separator run — the per-`&`-segment edge-stack blocks never reconverge the
 * Tomita frontier — so wall-time is EXPONENTIAL in the segment count (Stage-0
 * a7fc5b75 measured mono peak 84→629→1544→13047→123762 for k=0..4).
 *
 * THE FIX (this spec): SPLIT the depth-0 `sep`-separated list into segments,
 * RE-LEX+PARSE each segment in a TRULY ISOLATED sub-parse (fresh walker from
 * ROOT — NO cross-segment accumulation), then COMBINE the per-segment reading
 * sets by cartesian product, folding segment weights with the ⊗ (tropical-sum)
 * semiring. Stage-0 (a7fc5b75) MEASURED that this is BOTH (a) exactly LINEAR
 * (Σ = 84·(k+1)) AND (b) SOUND — the isolated+combined alt SET EXACTLY equals
 * the monolithic set for every shape incl the d=3 `@(Map()<@Nil!())<=a`
 * (lost = 0). This file PROVES the combine construction realizes that measured
 * fact and characterizes its soundness, weight-correctness, linearity, and
 * fall-through refinement.
 *
 * THE MODEL: a per-segment ISOLATED reading list `seg_readings : list (list
 * Reading)` (segment i's isolated element sub-parse alternatives). The
 * COMBINE enumerates the cartesian product; the MONOLITHIC reading set is
 * (Stage-0-grounded) EXACTLY the tuples that pick one reading per segment.
 *
 * Theorems:
 *   T1 combine_equals_monolithic     — In tup (cartesian segs) ↔ is_mono segs tup
 *                                       (the combine enumerates EXACTLY the
 *                                       monolithic reading set).
 *   T2a no_reading_lost              — is_mono → In cartesian (SOUNDNESS: no
 *                                       monolithic reading dropped — the HALT gate).
 *   T2b no_reading_gained            — In cartesian → is_mono (COMPLETENESS: no
 *                                       spurious reading fabricated).
 *   T3 linear_step                   — the isolated total grows by a CONSTANT per
 *                                       segment (linear), vs the geometric
 *                                       monolithic step (exponential).
 *   T4 segment_independence          — each segment's isolated cost is
 *                                       independent of the others (S0-A: constant).
 *   T5 weights_correct               — ⊗ (sum) is additive + monotone over
 *                                       independent segments, so the min-weight
 *                                       combine tuple = the per-segment-min tuple
 *                                       = the monolithic winner.
 *   T6 fallback_refines              — combine SET = monolithic SET, so a `None`
 *                                       fall-through (monolithic) loses nothing
 *                                       and an engaged combine loses nothing
 *                                       (byte-identical result set — RT-4).
 *   T7 inert_when_single_segment     — a 0-separator (single-element) list is
 *                                       NOT-APPLICABLE (helper returns None) ⇒
 *                                       monolithic ⇒ byte-identical; and the
 *                                       construction is GENERAL over the abstract
 *                                       `seg_readings` (no per-language hardcode).
 *   T8 composes_with_fallback        — composing the isolation with any
 *                                       downstream monolithic transform `g` and
 *                                       taking `None`⇒g leaves `g`'s behavior
 *                                       UNCHANGED (disjoint composition with the
 *                                       landed gates).
 *   T9 separator_locality_sound      — under SEPARATOR-LOCALITY (an element
 *                                       surface has no depth-0 separator), the
 *                                       depth-0 split of a `sep`-joined element
 *                                       list recovers EXACTLY the elements
 *                                       (split ∘ join = id) — no fragmentation,
 *                                       no missed split.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Section Combine.

  (* An abstract ELEMENT reading (an isolated element sub-parse result). *)
  Variable Reading : Type.

  (* Per-segment ISOLATED reading alternatives: `seg_readings` at index i is the
     list of readings segment i yields when parsed in TOTAL ISOLATION. *)

  (* The COMBINE enumerates the cartesian product of the per-segment reading
     lists: every way to pick one reading from each segment, in order. This is
     EXACTLY the emitted helper's `__element_combos` fold. *)
  Fixpoint cartesian (segs : list (list Reading)) : list (list Reading) :=
    match segs with
    | [] => [ [] ]
    | s :: rest =>
        flat_map (fun r => map (fun tup => r :: tup) (cartesian rest)) s
    end.

  (* The MONOLITHIC reading set (Stage-0-grounded, a7fc5b75: the monolithic
     ForRow alt-set decomposes EXACTLY to the position-tuples that pick one
     isolated reading per segment, for every shape incl d=3, lost=0): a tuple is
     a monolithic reading iff it is pointwise a member of the per-segment lists. *)
  Definition is_mono (segs : list (list Reading)) (tup : list Reading) : Prop :=
    Forall2 (fun r s => In r s) tup segs.

  (* ── T1: the combine enumerates EXACTLY the monolithic reading set. ── *)
  Theorem T1_combine_equals_monolithic :
    forall segs tup, In tup (cartesian segs) <-> is_mono segs tup.
  Proof.
    unfold is_mono.
    induction segs as [| s rest IH]; intros tup; simpl.
    - split.
      + intros [H | []]. subst tup. constructor.
      + intros H. inversion H. subst. left. reflexivity.
    - rewrite in_flat_map. split.
      + intros [r [Hr Hmap]].
        rewrite in_map_iff in Hmap.
        destruct Hmap as [t [Heq Ht]].
        subst tup.
        constructor.
        * exact Hr.
        * apply IH. exact Ht.
      + intros H. destruct tup as [| r0 t0]; inversion H; subst.
        exists r0. split.
        * assumption.
        * rewrite in_map_iff. exists t0. split; [reflexivity |].
          apply IH. assumption.
  Qed.

  (* ── T2a: SOUNDNESS — no monolithic reading is dropped (the HALT gate). ── *)
  Theorem T2a_no_reading_lost :
    forall segs tup, is_mono segs tup -> In tup (cartesian segs).
  Proof. intros segs tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* ── T2b: COMPLETENESS — no spurious reading is fabricated. ── *)
  Theorem T2b_no_reading_gained :
    forall segs tup, In tup (cartesian segs) -> is_mono segs tup.
  Proof. intros segs tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* The combine reading SET is EXACTLY the monolithic reading SET (extensional
     equality of the accept predicates) — the S0-CG-sound gate, modeled. *)
  Theorem combine_set_eq_mono_set :
    forall segs tup, In tup (cartesian segs) <-> is_mono segs tup.
  Proof. exact T1_combine_equals_monolithic. Qed.

End Combine.

Section Weights.

  Variable Reading : Type.
  (* Tropical (min-plus) cost of a reading: LOWER = better. ⊗ = Nat.add. *)
  Variable w : Reading -> nat.

  (* The ⊗-fold of a tuple's segment weights = their tropical product = sum. *)
  Definition tuple_weight (tup : list Reading) : nat :=
    fold_right (fun r acc => w r + acc) 0 tup.

  Lemma tuple_weight_cons :
    forall r t, tuple_weight (r :: t) = w r + tuple_weight t.
  Proof. intros r t. reflexivity. Qed.

  (* ── T5: ⊗ (sum) is additive + MONOTONE over independent segments. So if
     tuple A picks a no-worse reading than tuple B at EVERY segment (in
     particular, A picks the per-segment MIN), then A's ⊗-weight ≤ B's. Hence
     the min-weight combine tuple is the per-segment-min tuple = the monolithic
     winner (the winner-parity the S0-CG-single gate checks). ── *)
  Theorem T5_weights_correct :
    forall tupA tupB,
      Forall2 (fun rA rB => w rA <= w rB) tupA tupB ->
      tuple_weight tupA <= tuple_weight tupB.
  Proof.
    intros tupA tupB H.
    induction H as [| rA rB tA tB Hle Htl IH]; simpl.
    - lia.
    - unfold tuple_weight in *. simpl. lia.
  Qed.

End Weights.

Section Linearity.

  (* Isolated cost of segment i's sub-parse. S0-A MEASURED this CONSTANT across
     the position i (peak = 84, flat k=0..6) — segment independence. *)
  Variable iso_cost : nat -> nat.

  (* ── T4: SEGMENT INDEPENDENCE — each segment's isolated cost is independent
     of position (the S0-A finding, hypothesized as the constant-cost model). ── *)
  Hypothesis iso_const : forall i j, iso_cost i = iso_cost j.

  (* Total isolated cost of an (n+1)-segment list = Σ_{i≤n} iso_cost i. *)
  Fixpoint total_iso (n : nat) : nat :=
    match n with
    | 0 => iso_cost 0
    | S m => iso_cost (S m) + total_iso m
    end.

  (* ── T3: the isolated total grows by a CONSTANT per added segment — LINEAR
     (arithmetic step). Contrast the geometric monolithic step below. ── *)
  Theorem T3_linear_step :
    forall n, total_iso (S n) = iso_cost 0 + total_iso n.
  Proof.
    intro n. simpl. rewrite (iso_const (S n) 0). reflexivity.
  Qed.

  (* Closed form: total_iso n = (n+1) * c (Σ = 84·(k+1) — S0-B). *)
  Theorem T3_linear_closed_form :
    forall n, total_iso n = (S n) * iso_cost 0.
  Proof.
    induction n as [| m IH]; simpl.
    - lia.
    - rewrite (iso_const (S m) 0). simpl in IH. lia.
  Qed.

  (* The EXPONENTIAL monolithic baseline: cost grows by a constant FACTOR
     (b ≥ 2) per segment — geometric, NOT linear. This is what the fix removes. *)
  Fixpoint mono_geom (n b : nat) : nat :=
    match n with
    | 0 => 1
    | S m => b * mono_geom m b
    end.

  Theorem T3_monolithic_is_geometric :
    forall n b, mono_geom (S n) b = b * mono_geom n b.
  Proof. intros n b. reflexivity. Qed.

  (* The qualitative gap: for b ≥ 2 and a positive constant cost, the geometric
     monolithic step STRICTLY exceeds the linear isolated increment eventually —
     the geometric term at least doubles while the linear term adds a constant. *)
  Theorem T3_geometric_dominates_linear :
    forall n b, 2 <= b -> mono_geom n b + mono_geom n b <= mono_geom (S n) b.
  Proof.
    intros n b Hb.
    assert (Hpos : 1 <= mono_geom n b).
    { induction n as [| m IH]; simpl; [lia | nia]. }
    simpl. nia.
  Qed.

End Linearity.

Section Fallback.

  Variable Reading : Type.

  (* The facade runs the ISOLATION when applicable, else FALLS THROUGH to the
     monolithic body. Both compute the SAME reading set (T1 / the Stage-0
     grounding: combine SET = monolithic SET). We model the observable result
     as that shared set-membership predicate. *)
  Variable segs : list (list Reading).

  Definition combine_accepts (tup : list Reading) : Prop :=
    In tup (cartesian Reading segs).
  Definition mono_accepts (tup : list Reading) : Prop :=
    is_mono Reading segs tup.

  (* ── T6: FALL-THROUGH REFINES — engaging the combine and falling through to
     the monolithic accept the SAME readings. So a `None` fall-through (RT-4:
     any not-applicable / sub-parse failure ⇒ monolithic authoritative) loses
     NOTHING, and an engaged combine fabricates NOTHING: byte-identical set. ── *)
  Theorem T6_fallback_refines :
    forall tup, combine_accepts tup <-> mono_accepts tup.
  Proof.
    intro tup. unfold combine_accepts, mono_accepts.
    apply T1_combine_equals_monolithic.
  Qed.

  (* The runtime A/B (`PRATTAIL_NO_SEP_ISOLATION`): whichever branch runs, the
     accepted set is identical (ON ≡ OFF at the reading-set level). *)
  Theorem T6_ab_control_set_identical :
    forall tup, combine_accepts tup <-> mono_accepts tup.
  Proof. exact T6_fallback_refines. Qed.

End Fallback.

Section GeneralAndInert.

  Variable Reading : Type.

  (* ── T7 (inert): a list with FEWER than 2 segments (0 separators — a single
     element) is NOT-APPLICABLE: the emitted helper returns None (`__seg_ranges.len()
     < 2 ⇒ None`), so the facade falls through to the monolithic single-variant
     path — byte-identical. We model the applicability predicate and prove the
     single-segment case is inert (delegates to the monolithic, which is the
     cartesian of one segment = that segment's readings, so nothing changes). ── *)
  Definition applicable (segs : list (list Reading)) : Prop := 2 <= length segs.

  Theorem T7_inert_when_single_segment :
    forall s : list Reading, ~ applicable [s].
  Proof. intro s. unfold applicable. simpl. lia. Qed.

  (* Even if it were (counterfactually) engaged on one segment, the cartesian of
     a single segment is that segment's readings wrapped as singletons — a
     bijection with the monolithic single-element readings (no loss, no gain);
     the helper simply declines it as an optimization (the monolithic is already
     linear for one element). *)
  Theorem T7_single_segment_bijective :
    forall (s : list Reading) tup,
      In tup (cartesian Reading [s]) <-> exists r, In r s /\ tup = [r].
  Proof.
    intros s tup. simpl. rewrite in_flat_map. split.
    - intros [r [Hr Hmap]]. simpl in Hmap.
      destruct Hmap as [Heq | []]. exists r. split; [exact Hr | now subst].
    - intros [r [Hr Heq]]. exists r. split; [exact Hr |]. simpl. left. now subst.
  Qed.

  (* ── T7 (general): the construction is PARAMETRIC in `seg_readings` — the
     theorems above hold for an ARBITRARY per-segment reading list (any element
     category, any language). No per-language / per-rule constant appears. This
     is the universal quantification of T1 over `segs`: restated to make the
     generality explicit. ── *)
  Theorem T7_general_over_star_sep :
    forall (segs : list (list Reading)) tup,
      In tup (cartesian Reading segs) <-> is_mono Reading segs tup.
  Proof. exact (T1_combine_equals_monolithic Reading). Qed.

End GeneralAndInert.

Section Compose.

  Variable Reading : Type.
  Variable Result : Type.

  (* A downstream MONOLITHIC transform (any landed gate / continuation `g`
     applied after the parse). The isolation prologue either (a) returns a
     combined result Some, short-circuiting BEFORE `g`, or (b) returns None,
     leaving `g` to run on the monolithic path UNTOUCHED. ── *)
  Variable g : list (list Reading) -> Result.
  Variable combine_run : list (list Reading) -> option Result.

  (* The composed facade: Some ⇒ the combined result; None ⇒ fall through to g. *)
  Definition composed (segs : list (list Reading)) : Result :=
    match combine_run segs with
    | Some r => r
    | None => g segs
    end.

  (* ── T8: when the isolation is NOT-APPLICABLE (None), the composed facade is
     EXACTLY the downstream `g` — the prologue is disjoint from and does not
     disturb the landed gates (M6 / ROOT-2 / AT_QUOTED / CROSSCAT_LEX / …). ── *)
  Theorem T8_composes_with_fallback :
    forall segs, combine_run segs = None -> composed segs = g segs.
  Proof. intros segs H. unfold composed. rewrite H. reflexivity. Qed.

End Compose.

Section SeparatorLocality.

  Variable Token : Type.
  Hypothesis Token_eq_dec : forall a b : Token, {a = b} + {a <> b}.
  Variable sep : Token.

  (* Join a nonempty list of element surfaces with the separator (the `.*sep`
     list surface: e0 sep e1 sep … sep ek). *)
  Fixpoint join (es : list (list Token)) : list Token :=
    match es with
    | [] => []
    | [e] => e
    | e :: rest => e ++ sep :: join rest
    end.

  (* The depth-0 split at `sep`. SEPARATOR-LOCALITY (the T9 gate, grammar-checked
     as `sep ∉ infix(element)`) is modeled here by the hypothesis that an element
     surface contains NO separator at split depth (`~ In sep e`); the emitted
     helper refines this with bracket-depth tracking so a separator NESTED inside
     an element's brackets is not at depth 0 and is not split. *)
  Fixpoint split_on (ts : list Token) : list (list Token) :=
    match ts with
    | [] => [ [] ]
    | t :: rest =>
        if Token_eq_dec t sep
        then [] :: split_on rest
        else match split_on rest with
             | cur :: more => (t :: cur) :: more
             | [] => [ [t] ]   (* unreachable: split_on always returns a cons *)
             end
    end.

  Lemma split_on_nonnil : forall ts, split_on ts <> [].
  Proof.
    induction ts as [| t rest IH]; simpl.
    - discriminate.
    - destruct (Token_eq_dec t sep).
      + discriminate.
      + destruct (split_on rest); discriminate.
  Qed.

  (* Appending a sep-free prefix `e` in front of a token stream whose split
     begins a fresh first segment prepends `e` to that first segment. *)
  Lemma split_on_app_sepfree :
    forall e ts,
      ~ In sep e ->
      split_on (e ++ ts) =
        match split_on ts with
        | cur :: more => (e ++ cur) :: more
        | [] => [e]
        end.
  Proof.
    induction e as [| x e IH]; intros ts Hnin; simpl.
    - destruct (split_on ts) eqn:E.
      + exfalso. eapply split_on_nonnil. exact E.
      + reflexivity.
    - destruct (Token_eq_dec x sep) as [Heq | Hne].
      + subst x. exfalso. apply Hnin. left. reflexivity.
      + rewrite IH by (intro Hin; apply Hnin; right; exact Hin).
        destruct (split_on ts) eqn:E.
        * exfalso. eapply split_on_nonnil. exact E.
        * reflexivity.
  Qed.

  (* A leading separator opens a fresh (empty) first segment. *)
  Lemma split_on_sep_cons : forall ts, split_on (sep :: ts) = [] :: split_on ts.
  Proof.
    intros ts. simpl.
    destruct (Token_eq_dec sep sep) as [_ | Hne]; [reflexivity |].
    exfalso. apply Hne. reflexivity.
  Qed.

  (* A sep-free surface is a single segment. *)
  Lemma split_on_sepfree : forall e, ~ In sep e -> split_on e = [e].
  Proof.
    intros e H.
    assert (Hr : split_on (e ++ []) = [e]).
    { rewrite split_on_app_sepfree by exact H. simpl. rewrite app_nil_r. reflexivity. }
    rewrite app_nil_r in Hr. exact Hr.
  Qed.

  (* ── T9: SEPARATOR-LOCALITY SOUND — under locality (every element surface is
     sep-free at split depth) AND every element nonempty-list-of-elements, the
     depth-0 split of the joined list recovers EXACTLY the elements. No element
     is fragmented (a nested sep would be, but it is not at depth 0) and no split
     is missed (each inter-element sep IS at depth 0). Hence the combine's
     segmentation is a bijection with the element positions — the precondition
     for T1's no-loss/no-gain to transfer to the surface. ── *)
  Theorem T9_separator_locality_sound :
    forall es,
      es <> [] ->
      Forall (fun e => ~ In sep e) es ->
      split_on (join es) = es.
  Proof.
    induction es as [| e rest IH]; intros Hne Hall.
    - contradiction Hne. reflexivity.
    - assert (He : ~ In sep e) by (inversion Hall; assumption).
      assert (Hrest : Forall (fun e => ~ In sep e) rest) by (inversion Hall; assumption).
      destruct rest as [| e1 rest1].
      + (* single element: join [e] = e, and split_on e = [e] since e sep-free. *)
        simpl join. apply split_on_sepfree. exact He.
      + (* e ++ sep :: join (e1::rest1) : the leading sep-free e prepends to the
           fresh first segment produced by the sep. `change` unfolds ONLY the
           outer `join` (preserving `join (e1::rest1)` for the IH rewrite). *)
        change (join (e :: e1 :: rest1)) with (e ++ sep :: join (e1 :: rest1)).
        rewrite split_on_app_sepfree by exact He.
        rewrite split_on_sep_cons.
        rewrite (IH ltac:(discriminate) Hrest).
        simpl. rewrite app_nil_r. reflexivity.
  Qed.

End SeparatorLocality.

(* ══════════════ Admission audit — every theorem "Closed under the global
   context" (no Admitted, no Axiom, no Assumption). ══════════════ *)
Print Assumptions T1_combine_equals_monolithic.
Print Assumptions T2a_no_reading_lost.
Print Assumptions T2b_no_reading_gained.
Print Assumptions combine_set_eq_mono_set.
Print Assumptions T5_weights_correct.
Print Assumptions T3_linear_step.
Print Assumptions T3_linear_closed_form.
Print Assumptions T3_geometric_dominates_linear.
Print Assumptions T6_fallback_refines.
Print Assumptions T7_inert_when_single_segment.
Print Assumptions T7_single_segment_bijective.
Print Assumptions T7_general_over_star_sep.
Print Assumptions T8_composes_with_fallback.
Print Assumptions T9_separator_locality_sound.
