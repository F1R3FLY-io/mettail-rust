(*
 * ProjectionIsolation: the spec for the SHIPPED @-PROJECTION ISOLATION+COMBINE
 * codegen fix — the ROOT AXIS-@ divide-and-conquer that linearizes the
 * nested-@ display-roundtrip parse (commits 805555dc / 6ebdeb04 / cc6503c6,
 * 2026-07-05/06, feature/wfst-architecture, session da0842dc).
 *
 * THE DEFECT (measured; rhocalc forrow/inputbind/name `_display` @ CASES=100
 * timing out at 192s / 184s):
 *   parsing an `@`-quoted cross-cat PROJECTION operand chain (`@(p)`, `@p`,
 *   `@@…`, `@Nil!(q)`, nested sends) MONOLITHICALLY lets the CrossCatLhs
 *   edge-stack accumulate THROUGH every nested `@`, so the Tomita frontier forks
 *   base-b (b≈11) per projection level — wall-time EXPONENTIAL in the nesting
 *   depth (nested-send d1..4 OFF 6/40/432/5862 ms).
 *
 * THE FIX (this spec — the SIBLING of the `.*sep` `SepReconvergence` isolation,
 * applied at the PROJECTION boundary): the `@`-projection facade, when the
 * whole input matches an isolation-eligible projection SKELETON, splits the
 * skeleton into cross-cat OPERAND holes by a bracket-depth scan
 * (`__proj_skeleton_match`), RE-LEX+PARSES each operand in a TRULY ISOLATED
 * sub-parse (fresh walker from ROOT — the CrossCatLhs edge-stack no longer
 * accumulates through nested `@`), then COMBINES the per-operand reading sets by
 * cartesian product folding weights with the ⊗ (tropical) semiring. Nested-send
 * d1..4 ON 2/4/12/36 ms (150× at d4); the display-roundtrips PASS at CASES=100.
 * General, grammar-IR-driven, ambiguity-preserving, byte-identical when the
 * env kill-switch `PRATTAIL_NO_PROJ_ISOLATION` gates it off.
 *
 * TWO SEAMS (6ebdeb04): the facade runs an ALL seam (`parse_via_wpda_all` —
 * ambiguity-preserving: every reading) and a SINGLE-RESULT seam
 * (`parse_via_wpda` — one winner). The ALL seam combines per-operand ALL-sets
 * (the full cartesian). The SINGLE seam (bug 2318, the a8737503 fix) composes
 * each operand's OWN single-winner (per-hole ε-framing + fewest-holes primary),
 * which equals the monolithic M6 min-weight representative because the
 * projection operands are BRACKET-DELIMITED ⇒ their disambiguation is LOCAL ⇒
 * compositional. The ε-framing / single-winner transforms apply ONLY in the
 * SINGLE seam, so the ALL seam stays byte-identical to monolithic-all.
 *
 * THE MODEL: a projection variant's per-operand ISOLATED reading list
 * `ops : list (list Reading)` (operand i's isolated sub-parse alternatives). The
 * COMBINE enumerates the cartesian product; the MONOLITHIC reading set is
 * (measurement-grounded, lost=0 for every shape incl the d=3
 * `@(Map()<@Nil!())<=a`) EXACTLY the tuples picking one reading per operand.
 *
 * Theorems (all admission-free; audited by `Print Assumptions`, every one must
 * print "Closed under the global context"):
 *   T1  combine_equals_monolithic      — the ALL-seam combine set EXACTLY equals
 *                                         the monolithic reading set.
 *   T2  no_reading_lost                 — every monolithic reading is retained
 *                                         (SOUNDNESS: nothing dropped); and the
 *                                         converse (nothing fabricated).
 *   T3  isolation_linearizes            — the isolated total is LINEAR (constant
 *                                         per operand) vs the monolithic base-b
 *                                         GEOMETRIC step; and the skeleton-match
 *                                         loop TERMINATES because `k` advances one
 *                                         slot per delimiter (the infinite-loop
 *                                         fix: the buggy non-advancing Op step is
 *                                         a fixed point = the hang).
 *   T4  per_level_frame_constant        — the ε-framing contributes a CONSTANT
 *                                         per level (independent of operand
 *                                         count / arity).
 * ★ T5  single_winner_equals_monolithic — the SINGLE seam's composed per-operand
 *                                         winner is a MEMBER of the combine set
 *                                         AND its GLOBAL min-weight tuple = the
 *                                         monolithic M6 representative (the
 *                                         a8737503 fix). Fewest-holes primary
 *                                         (@Nil!(q): POutputNil 1-hole beats
 *                                         POutputQuoted 2-hole) witnessed.
 * ★ T6  isolation_preserves_full_ambiguity — the parse_all reading SET is
 *                                         INVARIANT under isolation, and its
 *                                         CARDINALITY is the product of the
 *                                         per-operand alternative counts (the
 *                                         full ambiguity is retained, not
 *                                         collapsed — the Fortran-load-bearing
 *                                         property).
 *   T7  fallthrough_refines             — a `None` fall-through runs the
 *                                         monolithic body BYTE-IDENTICALLY, and an
 *                                         engaged combine accepts the SAME set.
 *   T8  composes_with_gates             — when the isolation prologue declines
 *                                         (None), the composed facade is EXACTLY
 *                                         the downstream landed gate (disjoint).
 *   T9  recursion_terminates            — each isolated sub-parse operand
 *                                         substring is STRICTLY shorter than the
 *                                         input (≥1 framing byte omitted), so the
 *                                         recursion is well-founded.
 *   T10 sep_single_seam_only            — the ε-framing / single-winner apply
 *                                         ONLY in the SINGLE seam; the ALL seam is
 *                                         the full monolithic set (byte-identical),
 *                                         so an ambiguous input keeps >1 ALL-seam
 *                                         reading while the SINGLE seam is a
 *                                         singleton.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (Section
 * Variables/Hypotheses are discharged; every theorem closes under the global
 * context). Model style follows SepReconvergence.v / AtQuotedBindGate.v.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ── Version-robust list-length helpers (self-contained; no dependence on the
      Stdlib `app_length` / `map_length` ↔ `length_app` / `length_map` rename). ── *)
Lemma len_app :
  forall (A : Type) (a b : list A), length (a ++ b) = length a + length b.
Proof. intros A a b. induction a as [| x a IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma len_map :
  forall (A B : Type) (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f l. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* A skeleton is a list of SLOTS: a fixed literal (`@`, `!`, `(`, `Nil`, …) or a
   cross-cat OPERAND hole. `__proj_skeleton_match` walks the slots left-to-right,
   advancing the slot index `k` by exactly ONE per slot. *)
Inductive Slot : Type := SLit | SOp.

Section Combine.

  (* An abstract PROJECTION-operand reading (one isolated operand sub-parse
     alternative). Kept opaque — the construction is parametric over any element
     category, any language (no per-language / per-rule constant appears). *)
  Variable Reading : Type.

  (* The COMBINE enumerates the cartesian product of the per-operand reading
     lists: every way to pick one reading from each operand, in order. This is
     EXACTLY the emitted `__combos` fold in `emit_projection_isolation`. *)
  Fixpoint cartesian (ops : list (list Reading)) : list (list Reading) :=
    match ops with
    | [] => [ [] ]
    | s :: rest =>
        flat_map (fun r => map (fun tup => r :: tup) (cartesian rest)) s
    end.

  (* The MONOLITHIC reading set (measurement-grounded, lost=0 for every shape):
     a tuple is a monolithic reading iff it is pointwise a member of the
     per-operand isolated lists. *)
  Definition is_mono (ops : list (list Reading)) (tup : list Reading) : Prop :=
    Forall2 (fun r s => In r s) tup ops.

  (* ── T1: the combine enumerates EXACTLY the monolithic reading set. ── *)
  Theorem T1_combine_equals_monolithic :
    forall ops tup, In tup (cartesian ops) <-> is_mono ops tup.
  Proof.
    unfold is_mono.
    induction ops as [| s rest IH]; intros tup; simpl.
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

  (* ── T2: SOUNDNESS — no monolithic reading is dropped by the isolation. ── *)
  Theorem T2_no_reading_lost :
    forall ops tup, is_mono ops tup -> In tup (cartesian ops).
  Proof. intros ops tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* ── T2 (converse): COMPLETENESS — no spurious reading is fabricated. ── *)
  Theorem T2_no_reading_gained :
    forall ops tup, In tup (cartesian ops) -> is_mono ops tup.
  Proof. intros ops tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* Length of `flat_map (fun r => map (cons r) C) s` = |s| · |C| — the fan-out
     of the combine at one operand: |s| readings each cross the |C| suffix
     tuples. *)
  Lemma flat_map_cons_len :
    forall (C : list (list Reading)) (s : list Reading),
      length (flat_map (fun r => map (fun tup => r :: tup) C) s) = length s * length C.
  Proof.
    intros C s. induction s as [| x s IH]; simpl.
    - reflexivity.
    - rewrite len_app, len_map, IH. reflexivity.
  Qed.

  (* ── T6 (cardinality): the combine set size is the PRODUCT of the per-operand
     alternative counts — the full ambiguity is retained, not collapsed. ── *)
  Theorem T6_cardinality_is_product :
    forall ops, length (cartesian ops) = fold_right Nat.mul 1 (map (@length Reading) ops).
  Proof.
    induction ops as [| s rest IH]; simpl.
    - reflexivity.
    - rewrite flat_map_cons_len, IH. reflexivity.
  Qed.

  (* ── T6 (set invariance): the parse_all reading SET is INVARIANT under
     isolation (the combine accept-predicate ≡ the monolithic accept-predicate).
     This is the Fortran-load-bearing `parse_all` invariant, restated. ── *)
  Theorem T6_isolation_preserves_full_ambiguity :
    forall ops tup, In tup (cartesian ops) <-> is_mono ops tup.
  Proof. exact T1_combine_equals_monolithic. Qed.

End Combine.

Section Weights.

  Variable Reading : Type.
  (* Tropical (min-plus) cost of an operand reading: LOWER = better. ⊗ = Nat.add;
     the min-weight tuple is the parser's M6 representative. *)
  Variable w : Reading -> nat.
  (* The per-LEVEL ε-framing weight (`__framing`) — a SINGLE constant charged once
     per variant level (per-hole cost on the framing primary, computed once). *)
  Variable frame : nat.

  (* The ⊗-fold of a tuple's operand weights = their tropical product = sum. *)
  Definition tuple_weight (tup : list Reading) : nat :=
    fold_right (fun r acc => w r + acc) 0 tup.

  Lemma tuple_weight_cons :
    forall r t, tuple_weight (r :: t) = w r + tuple_weight t.
  Proof. intros r t. reflexivity. Qed.

  (* The level weight = ε-framing ⊗ (⊗ of the operand weights). *)
  Definition level_weight (tup : list Reading) : nat := frame + tuple_weight tup.

  (* ── T4: the ε-framing is charged EXACTLY once per level (a single ⊗ term). ── *)
  Theorem T4_frame_charged_once :
    forall tup, level_weight tup = frame + tuple_weight tup.
  Proof. reflexivity. Qed.

  (* ── T4: the framing contribution is a CONSTANT independent of the operand
     count (arity): two tuples of DIFFERENT length share the SAME framing term.
     So the ε-framing does not grow with the number of holes at a level. ── *)
  Theorem T4_per_level_frame_constant :
    forall tup1 tup2,
      level_weight tup1 - tuple_weight tup1 = level_weight tup2 - tuple_weight tup2.
  Proof. intros tup1 tup2. unfold level_weight. lia. Qed.

  (* ── T5 (member): the SINGLE seam's composed tuple — each operand's own
     single-winner — is a genuine MEMBER of the combine set (a valid combined
     reading). This is `T2_no_reading_lost` specialized to the winners. ── *)
  Theorem T5_single_winner_member :
    forall ops winners,
      Forall2 (fun win s => In win s) winners ops ->
      In winners (cartesian Reading ops).
  Proof.
    intros ops winners H. apply (T1_combine_equals_monolithic Reading). exact H.
  Qed.

  (* ── T5 (global min): if each operand's winner is its POINTWISE min-weight
     reading, the composed winner tuple is the GLOBAL min-weight tuple over the
     whole combine set. Because the ⊗-weight is an additive fold over the
     INDEPENDENT (bracket-delimited ⇒ locally-disambiguated) operands, the min
     over the product factorizes into the product of the per-operand mins — so
     the composed per-operand-winner IS the monolithic M6 representative. ── *)
  Theorem T5_single_winner_global_min :
    forall ops winners,
      Forall2 (fun win s => In win s /\ forall r, In r s -> w win <= w r) winners ops ->
      forall tup, In tup (cartesian Reading ops) -> tuple_weight winners <= tuple_weight tup.
  Proof.
    intros ops winners H.
    induction H as [| win s wrest orest Hhead Hrest IH]; intros tup Htup.
    - simpl in Htup. destruct Htup as [Heq | []]. subst tup. simpl. lia.
    - destruct Hhead as [Hin Hmin].
      simpl in Htup. rewrite in_flat_map in Htup.
      destruct Htup as [r0 [Hr0 Hmap]].
      rewrite in_map_iff in Hmap. destruct Hmap as [t0 [Heq Ht0]].
      subst tup.
      rewrite (tuple_weight_cons win wrest), (tuple_weight_cons r0 t0).
      specialize (IH t0 Ht0). specialize (Hmin r0 Hr0). lia.
  Qed.

  (* ── T5 (the crisp statement): the composed per-operand single-winner is BOTH
     a member of the combine set AND its global minimum — i.e. it IS the
     monolithic min-weight representative (the a8737503 single-seam fix). ── *)
  Theorem T5_single_winner_equals_monolithic :
    forall ops winners,
      Forall2 (fun win s => In win s /\ forall r, In r s -> w win <= w r) winners ops ->
      In winners (cartesian Reading ops)
      /\ (forall tup, In tup (cartesian Reading ops) -> tuple_weight winners <= tuple_weight tup).
  Proof.
    intros ops winners H. split.
    - apply (T1_combine_equals_monolithic Reading). unfold is_mono.
      induction H as [| win s wrest orest [Hin _] Hrest IH];
        constructor; [exact Hin | exact IH].
    - apply T5_single_winner_global_min. exact H.
  Qed.

End Weights.

Section Linearity.

  (* Isolated cost of operand i's sub-parse. MEASURED CONSTANT across the operand
     position (the CrossCatLhs edge-stack no longer accumulates through nested @,
     so every isolated operand costs the same base ≈ 84). *)
  Variable iso_cost : nat -> nat.

  (* ── SEGMENT INDEPENDENCE — each operand's isolated cost is independent of its
     position (hypothesized as the constant-cost model, discharged at section
     close ⇒ the theorems below quantify over it). ── *)
  Hypothesis iso_const : forall i j, iso_cost i = iso_cost j.

  (* Total isolated cost of an (n+1)-operand projection = Σ_{i≤n} iso_cost i. *)
  Fixpoint total_iso (n : nat) : nat :=
    match n with
    | 0 => iso_cost 0
    | S m => iso_cost (S m) + total_iso m
    end.

  (* ── T3 (linear): the isolated total grows by a CONSTANT per added operand
     level — LINEAR (arithmetic step). ── *)
  Theorem T3_isolation_linear_step :
    forall n, total_iso (S n) = iso_cost 0 + total_iso n.
  Proof. intro n. simpl. rewrite (iso_const (S n) 0). reflexivity. Qed.

  (* Closed form: total_iso n = (n+1)·c. *)
  Theorem T3_isolation_linear_closed_form :
    forall n, total_iso n = (S n) * iso_cost 0.
  Proof.
    induction n as [| m IH]; simpl.
    - lia.
    - rewrite (iso_const (S m) 0). simpl in IH. lia.
  Qed.

  (* The EXPONENTIAL monolithic baseline: cost grows by a constant FACTOR (b ≥ 2:
     the CrossCatLhs fork per projection level) — geometric, NOT linear. This is
     the base-b frontier the isolation removes. *)
  Fixpoint mono_geom (n b : nat) : nat :=
    match n with
    | 0 => 1
    | S m => b * mono_geom m b
    end.

  Theorem T3_monolithic_is_geometric :
    forall n b, mono_geom (S n) b = b * mono_geom n b.
  Proof. intros n b. reflexivity. Qed.

  (* The qualitative gap: for b ≥ 2 the geometric monolithic step at least
     DOUBLES while the linear isolated increment adds a constant — the isolation
     collapses the base-b projection frontier to a linear scan. *)
  Theorem T3_geometric_dominates_linear :
    forall n b, 2 <= b -> mono_geom n b + mono_geom n b <= mono_geom (S n) b.
  Proof.
    intros n b Hb.
    assert (Hpos : 1 <= mono_geom n b).
    { induction n as [| m IH]; simpl; [lia | nia]. }
    simpl. nia.
  Qed.

  (* ── T3 (skeleton-match termination): the `__proj_skeleton_match` loop advances
     the slot index `k` by EXACTLY ONE per slot. The number of loop iterations is
     therefore `length skel` — it TERMINATES. ── *)
  Fixpoint skel_iters (skel : list Slot) : nat :=
    match skel with
    | [] => 0
    | _ :: rest => S (skel_iters rest)
    end.

  Theorem T3_skeleton_match_terminates :
    forall skel, skel_iters skel = length skel.
  Proof. induction skel as [| x rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  (* The FIX: the delimiter-`Op` step advances `k` (`k += 1`), so the loop measure
     `length skel − k` STRICTLY decreases — progress. *)
  Definition fixed_slot_step (st : nat * nat) : nat * nat := (fst st, S (snd st)).

  Theorem T3_fixed_step_decreases_remaining :
    forall L i k, k < L -> L - snd (fixed_slot_step (i, k)) < L - snd (i, k).
  Proof. intros L i k Hk. simpl. lia. Qed.

  (* THE BUG (pre-805555dc): the `Op` branch set `i = end` but LEFT `k` on the
     `Op` slot; re-scanning from `i = end` immediately re-finds the delimiter at
     `end` (a ZERO-WIDTH operand). The step is the IDENTITY — a FIXED POINT of the
     while-loop = the hang on every non-trailing operand. Modeled here as the
     identity step, whose measure NEVER decreases. *)
  Definition buggy_op_step (st : nat * nat) : nat * nat := st.

  Theorem T3_buggy_step_is_fixed_point :
    forall st, buggy_op_step st = st.
  Proof. intro st. reflexivity. Qed.

  Theorem T3_buggy_step_no_progress :
    forall L i k, L - snd (buggy_op_step (i, k)) = L - snd (i, k).
  Proof. intros L i k. reflexivity. Qed.

End Linearity.

Section Termination.

  (* ── T9: each isolated sub-parse operand substring is STRICTLY shorter than the
     whole input. A projection skeleton has ≥1 framing byte (at minimum the `@`
     sigil, plus the `!`/`(`/`)` delimiters) OUTSIDE every operand, so an operand
     of length `op_len` sits inside `n = frame_bytes + op_len` with
     `frame_bytes ≥ 1` ⇒ `op_len < n`. The recursion measure (input byte length)
     therefore STRICTLY decreases at every isolation level — the recursion is
     well-founded (`<` on ℕ is well-founded), so the divide-and-conquer halts. ── *)
  Theorem T9_operand_strictly_shorter :
    forall frame_bytes op_len n,
      1 <= frame_bytes -> n = frame_bytes + op_len -> op_len < n.
  Proof. intros frame_bytes op_len n Hf Hn. subst n. lia. Qed.

  (* Consequence: at any positive input length the isolated operand length is a
     STRICTLY smaller measure — the well-founded-recursion certificate. *)
  Theorem T9_recursion_measure_decreases :
    forall frame_bytes op_len,
      1 <= frame_bytes -> op_len < frame_bytes + op_len.
  Proof. intros frame_bytes op_len Hf. lia. Qed.

End Termination.

Section Fallthrough.

  Variable Reading : Type.
  Variable Result : Type.

  (* The facade runs the ISOLATION prologue when applicable (Some result), else
     FALLS THROUGH to the monolithic body (`None ⇒ monolithic`). *)
  Variable combine_run : list (list Reading) -> option Result.
  Variable mono : list (list Reading) -> Result.

  Definition facade (ops : list (list Reading)) : Result :=
    match combine_run ops with
    | Some r => r
    | None => mono ops
    end.

  (* ── T7: a `None` fall-through (`PRATTAIL_NO_PROJ_ISOLATION`, not-applicable, or
     sub-parse decline) runs the monolithic body BYTE-IDENTICALLY. ── *)
  Theorem T7_fallthrough_is_monolithic :
    forall ops, combine_run ops = None -> facade ops = mono ops.
  Proof. intros ops H. unfold facade. rewrite H. reflexivity. Qed.

  (* ── T7 (engaged set): whichever branch runs, the accepted reading SET is
     identical — the engaged combine fabricates nothing (combine set ≡ monolithic
     set, T1). ── *)
  Theorem T7_engaged_equals_mono_set :
    forall ops tup,
      In tup (cartesian Reading ops) <-> is_mono Reading ops tup.
  Proof. intros ops tup. apply T1_combine_equals_monolithic. Qed.

End Fallthrough.

Section ComposeGates.

  Variable Reading : Type.
  Variable Result : Type.

  (* A downstream LANDED gate `g` (AT_QUOTED_BIND_GATE / CROSSCAT_LEX_COMPAT_GATE /
     M6 / …). The isolation prologue either (a) returns Some, short-circuiting
     BEFORE `g`, or (b) returns None, leaving `g` to run on the monolithic path. *)
  Variable g : list (list Reading) -> Result.
  Variable iso_run : list (list Reading) -> option Result.

  Definition composed (ops : list (list Reading)) : Result :=
    match iso_run ops with
    | Some r => r
    | None => g ops
    end.

  (* ── T8: when the isolation is NOT-APPLICABLE (None), the composed facade is
     EXACTLY the downstream gate — the prologue is DISJOINT from and does not
     disturb the landed gates. ── *)
  Theorem T8_composes_with_gates :
    forall ops, iso_run ops = None -> composed ops = g ops.
  Proof. intros ops H. unfold composed. rewrite H. reflexivity. Qed.

End ComposeGates.

Section Seam.

  Variable Reading : Type.

  (* The two facade seams. The ALL seam emits the full cartesian (ambiguity-
     preserving); the SINGLE seam emits exactly the composed single-winner tuple
     (the ε-framing / single-winner transform applies ONLY here). *)
  Inductive SeamKind : Type := SeamAll | SeamSingle.

  Definition all_seam_readings (ops : list (list Reading)) : list (list Reading) :=
    cartesian Reading ops.

  Definition single_seam_readings (winner : list Reading) : list (list Reading) :=
    [ winner ].

  (* ── T10: the ALL seam is the FULL monolithic set (the ε-framing / single-winner
     transform is INERT there — byte-identical to monolithic-all, the
     `atproj_flip_soundness_ab` ON≡OFF gate). ── *)
  Theorem T10_all_seam_is_monolithic :
    forall ops tup, In tup (all_seam_readings ops) <-> is_mono Reading ops tup.
  Proof. intros ops tup. unfold all_seam_readings. apply T1_combine_equals_monolithic. Qed.

  (* ── T10: the SINGLE seam is a SINGLETON — exactly the composed winner, the ONLY
     place the transform collapses to one reading. ── *)
  Theorem T10_single_seam_singleton :
    forall winner, single_seam_readings winner = [ winner ].
  Proof. intro winner. reflexivity. Qed.

  Theorem T10_single_seam_one_reading :
    forall winner, length (single_seam_readings winner) = 1.
  Proof. intro winner. reflexivity. Qed.

End Seam.

(* ══════════════ Non-vacuity witnesses (concrete finite instantiations for the
   key theorems — the models are inhabited and the statements are not vacuous). ══════════════ *)

(* T5b — the fewest-holes PRIMARY (bug 2318): `@Nil!(q)` is BOTH `POutputNil(q)`
   (skeleton `@ Nil ! ( ⟨q⟩ )`, 1 HOLE — `Nil` a LITERAL keyword) and
   `POutputQuoted(NVar "Nil", q)` (skeleton `@ ⟨n⟩ ! ( ⟨q⟩ )`, 2 HOLES). Modeling
   a reading by its hole-count and the tropical weight by the hole-count, the
   single-winner picks the 1-hole reading — matching monolithic's specific-rule
   preference. Here operand = one hole with two variant readings {1-hole,2-hole};
   winner = the 1-hole reading. *)
Example T5b_fewest_holes_primary :
  In [1] (cartesian nat [[1; 2]])
  /\ (forall tup, In tup (cartesian nat [[1; 2]]) ->
        tuple_weight nat (fun h => h) [1] <= tuple_weight nat (fun h => h) tup).
Proof.
  apply (T5_single_winner_equals_monolithic nat (fun h => h) [[1; 2]] [1]).
  constructor.
  - split.
    + simpl. left. reflexivity.
    + intros r Hr. simpl in Hr. destruct Hr as [H | [H | H]];
        try (subst r); [lia | lia | contradiction].
  - constructor.
Qed.

(* T6 — full ambiguity is RETAINED, not collapsed: two operands each with two
   isolated readings ⇒ 2·2 = 4 combined readings (the parse_all set invariant —
   the Fortran-load-bearing property). *)
Example T6_ambiguity_not_collapsed :
  length (cartesian nat [[0; 1]; [0; 1]]) = 4.
Proof. reflexivity. Qed.

Example T6_cardinality_matches_product :
  length (cartesian nat [[0; 1]; [0; 1]])
    = fold_right Nat.mul 1 (map (@length nat) [[0; 1]; [0; 1]]).
Proof. exact (T6_cardinality_is_product nat [[0; 1]; [0; 1]]). Qed.

(* T10 — seam separation: an ambiguous input keeps >1 ALL-seam reading (4) while
   the SINGLE seam is a singleton (1). *)
Example T10_seam_separation :
  length (all_seam_readings nat [[0; 1]; [0; 1]]) = 4
  /\ length (single_seam_readings nat [0; 0]) = 1.
Proof. split; reflexivity. Qed.

(* ══════════════ Admission audit — every theorem must print
   "Closed under the global context" (no Admitted, no Axiom, no Assumption). ══════════════ *)
Print Assumptions T1_combine_equals_monolithic.
Print Assumptions T2_no_reading_lost.
Print Assumptions T2_no_reading_gained.
Print Assumptions T6_cardinality_is_product.
Print Assumptions T6_isolation_preserves_full_ambiguity.
Print Assumptions T4_frame_charged_once.
Print Assumptions T4_per_level_frame_constant.
Print Assumptions T5_single_winner_member.
Print Assumptions T5_single_winner_global_min.
Print Assumptions T5_single_winner_equals_monolithic.
Print Assumptions T3_isolation_linear_step.
Print Assumptions T3_isolation_linear_closed_form.
Print Assumptions T3_monolithic_is_geometric.
Print Assumptions T3_geometric_dominates_linear.
Print Assumptions T3_skeleton_match_terminates.
Print Assumptions T3_fixed_step_decreases_remaining.
Print Assumptions T3_buggy_step_is_fixed_point.
Print Assumptions T3_buggy_step_no_progress.
Print Assumptions T9_operand_strictly_shorter.
Print Assumptions T9_recursion_measure_decreases.
Print Assumptions T7_fallthrough_is_monolithic.
Print Assumptions T7_engaged_equals_mono_set.
Print Assumptions T8_composes_with_gates.
Print Assumptions T10_all_seam_is_monolithic.
Print Assumptions T10_single_seam_singleton.
Print Assumptions T10_single_seam_one_reading.
Print Assumptions T5b_fewest_holes_primary.
Print Assumptions T6_ambiguity_not_collapsed.
Print Assumptions T6_cardinality_matches_product.
Print Assumptions T10_seam_separation.
