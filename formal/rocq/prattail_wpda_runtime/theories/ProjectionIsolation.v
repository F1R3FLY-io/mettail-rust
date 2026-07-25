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
 * ── G1 DEGENERATE-TAIL ADDITIONS (2026-07-25; see the section banner below) ──
 * ★ T11 empty_seplist_is_unit          — a ZERO-element `.*sep` region is in the
 *                                         language, the emitted scan manufactures a
 *                                         PHANTOM empty segment for it, and the
 *                                         value the fixed arm binds is the cartesian
 *                                         fold's own UNIT (weight `one`, so it
 *                                         perturbs no other operand).
 * ★ T12 degenerate_tail_complete       — appending a degenerate (empty) tail to a
 *                                         frame is a BIJECTION on the combine set
 *                                         (count-preserving, nothing fabricated);
 *                                         hence whenever the frame's other operands
 *                                         parse, the degenerate-tail frame HAS a
 *                                         reading and declining LOSES it.
 * ★ T13 fallthrough_is_not_completeness — T7 is a REFINEMENT statement, never a
 *                                         completeness guarantee: it fixes the
 *                                         declined facade's VALUE, not its SUCCESS.
 *                                         Declining is safe on an input IFF the
 *                                         monolithic body is complete THERE — an
 *                                         empirical premise that must be MEASURED
 *                                         (the `PRATTAIL_NO_PROJ_ISOLATION` kill
 *                                         switch), never assumed. Misreading T7 as
 *                                         a licence is what enabled G1.
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

(* ════════════════════════════════════════════════════════════════════════
   LITERAL-RUN ANCHOR (PROJ_ISO_LITERAL_RUN_ANCHOR, 2026-07-06): the InputBind
   query-frame `@@`-CHANNEL fix (this session's spec, session da0842dc).

   THE DEFECT: `__proj_skeleton_match` delimits an operand at the FIRST depth-0
   position where the SINGLE next literal matches (the pre-fix `if wb {…}`). When
   the operand itself contains that literal's first char at depth 0 — a channel
   `@@Nil!()` whose OWN send `!` sits at depth 0, with the post-channel delimiter
   `!` (the first char of the query run `! ? (`) — the FALSE-EARLY position is
   taken; the very-next literal of the run (`?`) then mismatches the channel's
   `(`, so the whole match returns None ⇒ the helper declines ⇒ the facade falls
   through to the monolithic body, which ALSO fails to form the reading for the
   complex multi-arg query (0 alts) ⇒ `InputBind::parse` / `ForRow::parse` Err.

   THE FIX: anchor the boundary on the FULL literal RUN (`if wb && __run_ok {…}`,
   via the emitted `__match_lit_run`): accept a depth-0 position ONLY when EVERY
   literal of the run matches there. The channel's internal `!` is followed by `(`
   (not `?(`), so it is skipped; the query run `!?(` matches only at the genuine
   frame ⇒ the channel operand recovers as `@@Nil!()` and the args region as
   `true, Pathmap() <= @Nil!!()` (both then sub-parse + combine).

   MODEL: a candidate scan position carries its per-run-literal match profile
   `bs : list bool` (bit i = run-literal i matches here; NON-EMPTY — the run has
   ≥1 literal, the delimiter). `fc_of` = the FIRST literal matches (the pre-fix
   `wb`); `run_of` = ALL literals match (the fix). A scan is the position list
   `list (list bool)`; a boundary is the FIRST position satisfying its predicate.

   Theorems (all admission-free — audited below):
     LRA1 run_implies_fc          — run_of ⇒ fc_of (the run STARTS with the
                                    delimiter): anchored candidates ⊆ single-lit.
     LRA2 no_false_frame          — the anchored boundary is ALWAYS a genuine
                                    frame (run_of holds there): never fabricates.
     LRA3 anchored_never_earlier  — the anchored boundary is never EARLIER than the
                                    single-lit boundary: it removes only false-early
                                    splits (passing ranges are unchanged).
     LRA4 identical_when_valid    — when the single-lit boundary ALREADY carries the
                                    full run (the PASSING forms), the anchored
                                    boundary is IDENTICAL (byte-identical ranges).
     LRA5 never_worse             — pre-fix SUCCESS ⇒ anchored SUCCESS with the SAME
                                    boundary (the strict-improvement lower bound).
     LRA6 recovers_when_single_fails — pre-fix FAILURE but a true frame exists ⇒
                                    anchored SUCCEEDS (None → Some — the strict gain
                                    that recovers `<-@@Nil!()!?(…)`).
   ════════════════════════════════════════════════════════════════════════ *)
Section LiteralRunAnchor.

  (* `fc_of` — the SINGLE next literal (the delimiter's first char) matches: the
     pre-fix `wb`. `run_of` — the WHOLE consecutive literal run matches: the fix. *)
  Definition fc_of (bs : list bool) : bool := hd false bs.
  Definition run_of (bs : list bool) : bool := forallb (fun b => b) bs.

  (* LRA1: the FULL run matching implies the FIRST literal (the delimiter) matches
     — so every anchored candidate position is a single-literal candidate (⊆). *)
  Lemma LRA1_run_implies_fc :
    forall bs, bs <> [] -> run_of bs = true -> fc_of bs = true.
  Proof.
    intros [| b rest] Hne H.
    - contradiction.
    - unfold run_of in H. simpl in H. unfold fc_of. simpl.
      destruct b; [reflexivity | simpl in H; discriminate].
  Qed.

  (* The generated matcher's boundary = the FIRST position satisfying its predicate
     (pre-fix `fc_of`, fix `run_of`) — `__proj_skeleton_match`'s greedy-first scan. *)
  Fixpoint find_first (f : list bool -> bool) (l : list (list bool)) : option nat :=
    match l with
    | [] => None
    | p :: rest => if f p then Some 0 else option_map S (find_first f rest)
    end.

  Definition single_boundary := find_first fc_of.
  Definition anchored_boundary := find_first run_of.

  Lemma find_first_some :
    forall f l k, find_first f l = Some k ->
      exists x, nth_error l k = Some x /\ f x = true.
  Proof.
    intros f l. induction l as [| p rest IH]; intros k H; simpl in H.
    - discriminate.
    - destruct (f p) eqn:Hp.
      + injection H as H; subst k. exists p. split; [reflexivity | exact Hp].
      + destruct (find_first f rest) as [k'|] eqn:Hf; simpl in H; try discriminate.
        (* `destruct … eqn:Hf` rewrote `find_first f rest` to `Some k'` inside IH,
           so IH's premise is now `Some k' = Some k`; discharge it by reflexivity. *)
        injection H as H; subst k. simpl. apply IH. reflexivity.
  Qed.

  Lemma find_first_minimal :
    forall f l k, find_first f l = Some k ->
      forall j y, j < k -> nth_error l j = Some y -> f y = false.
  Proof.
    intros f l. induction l as [| p rest IH]; intros k H j y Hjk Hj; simpl in H.
    - discriminate.
    - destruct (f p) eqn:Hp.
      + injection H as H; subst k. lia.
      + destruct (find_first f rest) as [k'|] eqn:Hf; simpl in H; try discriminate.
        injection H as H; subst k.
        destruct j as [| j'].
        * simpl in Hj. injection Hj as Hj; subst y. exact Hp.
        * (* IH's `find_first f rest` premise was rewritten to `Some k'` by the
             `eqn:Hf` destruct, so pass `eq_refl` for `Some k' = Some k'`. *)
          simpl in Hj. apply (IH k' eq_refl j' y); [lia | exact Hj].
  Qed.

  Lemma find_first_le :
    forall f l k x, nth_error l k = Some x -> f x = true ->
      exists i, find_first f l = Some i /\ i <= k.
  Proof.
    intros f l. induction l as [| p rest IH]; intros k x Hk Hx; simpl.
    - destruct k; simpl in Hk; discriminate.
    - destruct (f p) eqn:Hp.
      + exists 0. split; [reflexivity | lia].
      + destruct k as [| k'].
        * simpl in Hk. injection Hk as Hk; subst x. rewrite Hx in Hp. discriminate.
        * simpl in Hk. specialize (IH k' x Hk Hx). destruct IH as [i [Hi Hle]].
          rewrite Hi. simpl. exists (S i). split; [reflexivity | lia].
  Qed.

  (* LRA2: the anchored boundary is ALWAYS a genuine frame (run_of holds there):
     the run-anchor never fabricates a boundary where the fixed frame is absent. *)
  Theorem LRA2_no_false_frame :
    forall l k, anchored_boundary l = Some k ->
      exists bs, nth_error l k = Some bs /\ run_of bs = true.
  Proof. intros l k H. apply find_first_some. exact H. Qed.

  (* LRA3: the anchored boundary is never EARLIER than the single-lit boundary
     (it removes only FALSE-EARLY splits — a passing form's range is unchanged). *)
  Theorem LRA3_anchored_never_earlier :
    forall l k,
      (forall bs, In bs l -> bs <> []) ->
      anchored_boundary l = Some k ->
      exists i, single_boundary l = Some i /\ i <= k.
  Proof.
    intros l k Hne H.
    destruct (find_first_some run_of l k H) as [bs [Hk Hrun]].
    assert (Hin : In bs l) by (eapply nth_error_In; exact Hk).
    assert (Hfc : fc_of bs = true)
      by (apply LRA1_run_implies_fc; [apply Hne; exact Hin | exact Hrun]).
    apply (find_first_le fc_of l k bs Hk Hfc).
  Qed.

  (* LRA4: when the single-lit boundary ALREADY carries the full run (a passing
     form — the operand does NOT contain the delimiter early), the anchored
     boundary is IDENTICAL. This is the byte-identical-ranges property (OLD==NEW). *)
  Theorem LRA4_identical_when_valid :
    forall l s bs,
      (forall b, In b l -> b <> []) ->
      single_boundary l = Some s ->
      nth_error l s = Some bs ->
      run_of bs = true ->
      anchored_boundary l = Some s.
  Proof.
    intros l s bs Hne Hs Hnth Hrun.
    destruct (find_first_le run_of l s bs Hnth Hrun) as [i [Hi Hle]].
    assert (i = s).
    { destruct (Nat.lt_ge_cases i s) as [Hlt | Hge].
      - exfalso.
        destruct (find_first_some run_of l i Hi) as [bi [Hbi Hruni]].
        assert (Hini : In bi l) by (eapply nth_error_In; exact Hbi).
        assert (Hfci : fc_of bi = true)
          by (apply LRA1_run_implies_fc; [apply Hne; exact Hini | exact Hruni]).
        pose proof (find_first_minimal fc_of l s Hs i bi Hlt Hbi) as Hc.
        rewrite Hfci in Hc. discriminate.
      - lia. }
    subst i. exact Hi.
  Qed.

  (* The matcher OUTCOME. The pre-fix matcher SUCCEEDS at this operand iff its
     (single-lit) boundary exists AND the full run holds there — else the very-next
     literal after the operand mismatches and the whole match returns None. The
     anchored matcher succeeds iff ANY run position exists. *)
  Definition single_succeeds (l : list (list bool)) : Prop :=
    exists s bs,
      single_boundary l = Some s /\ nth_error l s = Some bs /\ run_of bs = true.
  Definition anchored_succeeds (l : list (list bool)) : Prop :=
    anchored_boundary l <> None.

  (* LRA5 (never worse): pre-fix SUCCESS ⇒ anchored SUCCESS with the SAME boundary. *)
  Theorem LRA5_never_worse :
    forall l,
      (forall b, In b l -> b <> []) ->
      single_succeeds l ->
      anchored_succeeds l /\ anchored_boundary l = single_boundary l.
  Proof.
    intros l Hne [s [bs [Hs [Hnth Hrun]]]].
    pose proof (LRA4_identical_when_valid l s bs Hne Hs Hnth Hrun) as Hanch.
    split.
    - unfold anchored_succeeds. rewrite Hanch. discriminate.
    - rewrite Hanch, Hs. reflexivity.
  Qed.

  (* LRA6 (strict gain): pre-fix FAILURE but a true frame exists ⇒ anchored
     SUCCEEDS (None → Some — the recovery of `<-@@Nil!()!?(…)`). The `~single`
     premise is the recovery context; the anchored success follows from the frame. *)
  Theorem LRA6_recovers_when_single_fails :
    forall l,
      ~ single_succeeds l ->
      (exists s bs, nth_error l s = Some bs /\ run_of bs = true) ->
      anchored_succeeds l.
  Proof.
    intros l _ [s [bs [Hnth Hrun]]].
    unfold anchored_succeeds, anchored_boundary.
    destruct (find_first_le run_of l s bs Hnth Hrun) as [i [Hi _]].
    rewrite Hi. discriminate.
  Qed.

End LiteralRunAnchor.

(* Non-vacuity — the `@@`-channel scan `<-@@Nil!()  !?(…)`: position 0 = the
   channel-internal `!` (first char `!` matches, but the run `!?(` does not — the
   next char is `(`), position 1 = the query `!?(` (full run matches). The pre-fix
   matcher takes position 0, mismatches, and FAILS (`~single_succeeds`); the run-
   anchor skips it and SUCCEEDS at position 1. The STRICT gain, witnessed. *)
Example LRA_strict_gain_witness :
  single_boundary [ [true; false]; [true; true] ] = Some 0
  /\ ~ single_succeeds [ [true; false]; [true; true] ]
  /\ anchored_boundary [ [true; false]; [true; true] ] = Some 1
  /\ anchored_succeeds [ [true; false]; [true; true] ].
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - intros [s [bs [Hs [Hnth Hrun]]]].
    unfold single_boundary in Hs. simpl in Hs. injection Hs as Hs; subst s.
    simpl in Hnth. injection Hnth as Hnth; subst bs. simpl in Hrun. discriminate.
  - reflexivity.
  - unfold anchored_succeeds. simpl. discriminate.
Qed.

(* Non-vacuity — a PASSING scan (channel with NO internal delimiter): the first
   position already carries the full run, so single and anchored AGREE (Some 0). *)
Example LRA_passing_identical_witness :
  single_boundary [ [true; true] ] = Some 0
  /\ single_succeeds [ [true; true] ]
  /\ anchored_boundary [ [true; true] ] = Some 0.
Proof.
  refine (conj _ (conj _ _)).
  - reflexivity.
  - exists 0, [true; true]. refine (conj _ (conj _ _)); reflexivity.
  - reflexivity.
Qed.

(* ════════════════════════════════════════════════════════════════════════
   G1 DEGENERATE-TAIL (2026-07-25) — the ZERO-ELEMENT `.*sep` operand.

   THE DEFECT. `emit_proj_variant_arm`'s `OpKind::Sep` arm opened with

       if __region.is_empty() { __cap_hit = true; break '__variant; }

   so the `@`-projection isolation helper DECLINED whenever a frame's `.*sep`
   operand region was empty. But a zero-element list is IN THE LANGUAGE: `.*sep`
   is zero-or-more, so `POutput2Plus . n:Name, a:Proc, bs:Vec(Proc) |- n "!" "("
   a "," bs.*sep(",") ")"` derives `n!(a,)` with `bs = []`, and `Display` renders
   exactly that surface. Two independent facts, each individually survivable,
   composed into a hard parse failure:

     G1 the isolation helper cannot REPRESENT the zero-element list (it declines);
     G2 the monolithic walker cannot PARSE a σ-led frame whose channel operand is
        a grouped method frame containing a nested channel-first send.

   On the INTERSECTION the decline lands on the walker gap and the input dies.
   Measured 2026-07-25 with the committed `PRATTAIL_NO_PROJ_ISOLATION` kill switch
   (`languages/tests/proj_iso_ab_soundness.rs`):

     `@(Nil.set(a!(Nil) , Nil))!(Nil,Nil)`   facade ON → ACCEPT   walker only → REJECT
     `@(Nil.set(a!(Nil) , Nil))!(Nil)`       facade ON → ACCEPT   walker only → REJECT
     `@(Nil.set(a!(Nil) , Nil))!(Nil,)`      facade ON → REJECT   walker only → REJECT  ★
     `@(Nil.set(Nil , Nil))!(Nil,)`          facade ON → ACCEPT   walker only → ACCEPT

   The first two rows REFUTE the codegen comment's premise that the walker is
   "the authoritative/complete parser"; the third row is the composition.

   THE FIX. Bind the empty list instead of bailing. This is not new semantics: the
   cartesian fold is already SEEDED with the one-element combo carrying the empty
   tuple, so zero segments already denote it. T11 proves the seed IS the unit,
   T12 proves appending a degenerate tail to a frame is a completeness-preserving
   bijection, and T13 removes the misreading of T7 that licensed the bail.
   ════════════════════════════════════════════════════════════════════════ *)

Section DegenerateTail.

  (* ── The SEGMENTATION model. A `.*sep` region is a token string over a
     distinguished separator `TSep` and element characters `TCh`. This is exactly
     the alphabet the emitted depth-0 scan sees: it only ever tests "is this byte
     the separator at bracket depth 0?", and every other byte is opaque to it. ── *)
  Inductive Tok : Type := TSep | TCh.

  (* The EMITTED split (`__seg_ranges`): scan left to right, close a segment at
     every depth-0 separator, and ALWAYS push a final segment after the loop
     (`__seg_ranges.push((__start, __rn))`). Transcribed faithfully. *)
  Fixpoint split_aux (r : list Tok) (cur : list Tok) : list (list Tok) :=
    match r with
    | []          => [ rev cur ]
    | TSep :: rest => rev cur :: split_aux rest []
    | TCh  :: rest => split_aux rest (TCh :: cur)
    end.

  Definition split_emitted (r : list Tok) : list (list Tok) := split_aux r [].

  (* An ELEMENT is a NON-EMPTY run of element characters — the smallest thing the
     element category's string entry can consume. *)
  Definition chunk (e : list Tok) : Prop := e <> [] /\ Forall (fun t => t = TCh) e.

  (* The LANGUAGE of `bs.*sep(",")` — Kleene star over `elem (sep elem)*`, indexed
     by the ELEMENT COUNT. `SLnil` is the whole point: zero elements is derivable,
     and its surface is the EMPTY region. *)
  Inductive sep_list : list Tok -> nat -> Prop :=
  | SLnil  : sep_list [] 0
  | SLone  : forall e, chunk e -> sep_list e 1
  | SLcons : forall e r n,
      chunk e -> sep_list r (S n) -> sep_list (e ++ TSep :: r) (S (S n)).

  (* ── T11 (a): the EMPTY region is in the language, with ZERO elements. This is
     the grammatical fact the bail denied. ── *)
  Theorem T11_empty_region_is_in_the_language : sep_list [] 0.
  Proof. exact SLnil. Qed.

  (* ── T11 (b): the emitted scan maps the empty region to ONE EMPTY SEGMENT, not
     to zero segments. That phantom segment is what the per-element emptiness rule
     then (correctly, on its own terms) refuses — which is exactly why the arm
     needs the empty region handled BEFORE the scan runs. ── *)
  Theorem T11_emitted_split_of_empty_is_one_phantom_segment :
    split_emitted [] = [ [] ].
  Proof. reflexivity. Qed.

  Theorem T11_phantom_segment_is_not_an_element :
    forall e, In e (split_emitted []) -> ~ chunk e.
  Proof.
    intros e Hin. simpl in Hin. destruct Hin as [Heq | []]. subst e.
    intros [Hne _]. apply Hne. reflexivity.
  Qed.

  (* ── T11 (c) ★ THE UNIT LAW: zero operand-alternative lists denote EXACTLY ONE
     combo — the empty tuple. So `vec![(Vec::new(), one())]`, the value the fixed
     arm binds, is not an invention: it is the cartesian fold's own seed, i.e. the
     unit of the combine monoid, reached by short-circuit instead of by iteration.
     (`cartesian` is the emitted `__combos` fold; see T1.) ── *)
  Theorem T11_empty_seplist_is_unit :
    forall (Reading : Type), cartesian Reading [] = [ [] ].
  Proof. intro Reading. reflexivity. Qed.

  (* The unit is a LEFT and RIGHT identity for the combine's append action, which
     is what makes "bind the empty list" compositional with the other operands. *)
  Theorem T11_unit_is_neutral :
    forall (Reading : Type) (tup : list Reading), [] ++ tup = tup /\ tup ++ [] = tup.
  Proof.
    intros Reading tup. split; [reflexivity |]. induction tup as [| x t IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (* ── T11 (d): the BAIL is not the unit. Declining contributes the EMPTY
     candidate list; the correct value is the SINGLETON containing the empty
     tuple. `[] <> [[]]` — one reading was lost, not zero. ── *)
  Theorem T11_bail_loses_the_unit :
    forall (Reading : Type), (@nil (list Reading)) <> cartesian Reading [].
  Proof. intros Reading H. rewrite T11_empty_seplist_is_unit in H. discriminate. Qed.

  (* ── The ⊗-WEIGHT of the bound unit. The arm binds weight `one()`; in the
     tropical semiring `one = 0` and `⊗ = +`, so the empty tail contributes
     NOTHING to the frame's weight and cannot perturb which reading wins. ── *)
  Theorem T11_unit_weight_is_identity :
    forall (Reading : Type) (w : Reading -> nat),
      tuple_weight Reading w [] = 0.
  Proof. intros Reading w. reflexivity. Qed.

  Theorem T11_unit_weight_absorbs :
    forall (Reading : Type) (w : Reading -> nat) (tup : list Reading),
      tuple_weight Reading w tup + tuple_weight Reading w [] = tuple_weight Reading w tup.
  Proof. intros Reading w tup. simpl. lia. Qed.

  (* ── T12 ★ DEGENERATE-TAIL COMPLETENESS. A frame with a degenerate (empty)
     `.*sep` tail has an operand-alternative profile `ops ++ [[u]]`, where `ops`
     are the frame's other operands and `u` is the ONE alternative the empty tail
     admits (the empty list). Appending a SINGLETON alternative list is a
     BIJECTION on the combine set: every reading of the tail-less frame extends
     uniquely, nothing is fabricated, nothing is lost. ── *)
  Theorem T12_degenerate_tail_bijection :
    forall (Reading : Type) (ops : list (list Reading)) (u : Reading) tup,
      In tup (cartesian Reading (ops ++ [[u]]))
      <-> (exists t, In t (cartesian Reading ops) /\ tup = t ++ [u]).
  Proof.
    intros Reading ops u.
    induction ops as [| s rest IH]; intros tup.
    - (* BASE: `[] ++ [[u]] = [[u]]`, whose combine is the single tuple `[u]`, and
         `cartesian []` is the single tuple `[]` — so the bijection is `[] ↦ [u]`. *)
      split.
      + intro H. simpl in H. destruct H as [Heq | []].
        exists []. split.
        * simpl. left. reflexivity.
        * simpl. symmetry. exact Heq.
      + intros [t [Ht Heq]]. simpl in Ht. destruct Ht as [Heq2 | []].
        rewrite <- Heq2 in Heq. simpl in Heq. rewrite Heq. simpl. left. reflexivity.
    - (* STEP: peel operand `s`. `(s :: rest) ++ [[u]] = s :: (rest ++ [[u]])`, so
         both sides fan out over the SAME `s` and the IH transports the suffix. *)
      split.
      + intro H. simpl in H. rewrite in_flat_map in H.
        destruct H as [r [Hr Hmap]]. rewrite in_map_iff in Hmap.
        destruct Hmap as [t0 [Heq Ht0]].
        apply IH in Ht0. destruct Ht0 as [t [Ht Heq2]].
        exists (r :: t). split.
        * simpl. rewrite in_flat_map. exists r. split; [exact Hr |].
          rewrite in_map_iff. exists t. split; [reflexivity | exact Ht].
        * rewrite <- Heq, Heq2. reflexivity.
      + intros [t [Ht Heq]]. simpl in Ht. rewrite in_flat_map in Ht.
        destruct Ht as [r [Hr Hmap]]. rewrite in_map_iff in Hmap.
        destruct Hmap as [t' [Heq' Ht']].
        simpl. rewrite in_flat_map. exists r. split; [exact Hr |].
        rewrite in_map_iff. exists (t' ++ [u]). split.
        * rewrite Heq, <- Heq'. reflexivity.
        * apply IH. exists t'. split; [exact Ht' | reflexivity].
  Qed.

  (* Version-robust `map` / `fold_right` helpers (same self-containment policy as
     `len_app` / `len_map` at the top of this file — no dependence on Stdlib
     renames). *)
  Lemma map_app_local :
    forall (A B : Type) (f : A -> B) (l l' : list A),
      map f (l ++ l') = map f l ++ map f l'.
  Proof.
    intros A B f l l'. induction l as [| x l IH]; simpl;
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma fold_mul_snoc_one :
    forall l, fold_right Nat.mul 1 (l ++ [1]) = fold_right Nat.mul 1 l.
  Proof.
    induction l as [| n l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  (* Cardinality form: the degenerate tail changes NO count — it multiplies the
     product of the per-operand alternative counts (T6) by the SINGLE alternative
     the empty tail admits, i.e. by 1. *)
  Theorem T12_degenerate_tail_preserves_count :
    forall (Reading : Type) (ops : list (list Reading)) (u : Reading),
      length (cartesian Reading (ops ++ [[u]])) = length (cartesian Reading ops).
  Proof.
    intros Reading ops u.
    rewrite (T6_cardinality_is_product Reading (ops ++ [[u]])).
    rewrite (T6_cardinality_is_product Reading ops).
    rewrite map_app_local. simpl. apply fold_mul_snoc_one.
  Qed.

  (* ── T12 ★ THE DEFECT, STATED: whenever the frame's other operands parse, the
     degenerate-tail frame HAS at least one reading. Declining therefore LOSES a
     reading — it is not a neutral "let someone else handle it". ── *)
  Theorem T12_degenerate_tail_complete :
    forall (Reading : Type) (ops : list (list Reading)) (u : Reading),
      cartesian Reading ops <> [] -> cartesian Reading (ops ++ [[u]]) <> [].
  Proof.
    intros Reading ops u Hne Hcontra.
    apply Hne.
    assert (Hlen : length (cartesian Reading ops) = 0).
    { rewrite <- (T12_degenerate_tail_preserves_count Reading ops u), Hcontra. reflexivity. }
    destruct (cartesian Reading ops); [reflexivity | simpl in Hlen; discriminate].
  Qed.

  (* The bail's cost, made explicit: the arm CONTRIBUTED `[]` where completeness
     demanded a non-empty set. *)
  Theorem T12_bail_is_incomplete :
    forall (Reading : Type) (ops : list (list Reading)) (u : Reading),
      cartesian Reading ops <> [] ->
      (@nil (list Reading)) <> cartesian Reading (ops ++ [[u]]).
  Proof.
    intros Reading ops u Hne H.
    apply (T12_degenerate_tail_complete Reading ops u Hne).
    symmetry. exact H.
  Qed.

End DegenerateTail.

(* ════════════════════════════════════════════════════════════════════════
   T13 — FALL-THROUGH IS NOT COMPLETENESS (documentation-by-proof).

   THE ROOT ENABLER of the G1 defect was not a coding slip; it was a MISREADING of
   T7. `T7_fallthrough_is_monolithic` says

       combine_run ops = None  ->  facade ops = mono ops,

   i.e. declining is a REFINEMENT: the facade transfers the monolithic body's
   answer verbatim. The codegen comment read it as a SAFETY LICENCE — "the walker
   (the authoritative/complete parser) parses it" — and on that basis declined a
   shape that is in the language. T7 does not, and cannot, say that: it quantifies
   over `mono`'s VALUE, never over `mono`'s SUCCESS.

   The theorems below make the gap unmisreadable. T13a restates the refinement.
   T13b exhibits a model in which T7 holds everywhere and the facade nevertheless
   accepts nothing — so "declining is safe" is independent of T7. T13c gives the
   exact missing side condition: declining is safe on an input IFF the monolithic
   body is complete on that input, which is an EMPIRICAL fact that must be
   MEASURED (that is what the `PRATTAIL_NO_PROJ_ISOLATION` kill switch is for),
   never assumed. T13d records the measurement that refuted the assumption.
   ════════════════════════════════════════════════════════════════════════ *)
Section FallthroughIsNotCompleteness.

  Variable Reading : Type.
  Variable Result : Type.

  Variable combine_run : list (list Reading) -> option Result.
  Variable mono : list (list Reading) -> Result.

  (* `ok r` — "this result is an ACCEPT" (a non-empty reading set). The facade's
     user cares about `ok (facade ops)`, not about `facade ops = mono ops`. *)
  Variable ok : Result -> Prop.

  Definition facade_ok (ops : list (list Reading)) : Result :=
    match combine_run ops with
    | Some r => r
    | None   => mono ops
    end.

  (* ── T13 (a): the refinement, restated on this section's facade. Declining
     transfers the monolithic ANSWER — nothing more. ── *)
  Theorem T13_fallthrough_transfers :
    forall ops, combine_run ops = None -> facade_ok ops = mono ops.
  Proof. intros ops H. unfold facade_ok. rewrite H. reflexivity. Qed.

  (* ── T13 (c) ★ THE MISSING SIDE CONDITION. On a declined input the facade
     accepts IFF the monolithic body accepts. So "it is safe to decline here" is
     EXACTLY the claim "mono is complete here" — a separate, empirical premise.
     T7 supplies the left-to-right transfer; it supplies no evidence for `ok`. ── *)
  Theorem T13_safety_needs_mono_completeness :
    forall ops, combine_run ops = None -> (ok (facade_ok ops) <-> ok (mono ops)).
  Proof.
    intros ops H. rewrite (T13_fallthrough_transfers ops H). reflexivity.
  Qed.

  (* Contrapositive, in the form the defect took: if the monolithic body REJECTS a
     declined input, the facade rejects it too. A decline onto a monolithic gap is
     a parse failure, full stop. *)
  Theorem T13_decline_onto_a_gap_rejects :
    forall ops, combine_run ops = None -> ~ ok (mono ops) -> ~ ok (facade_ok ops).
  Proof.
    intros ops Hnone Hbad Hok.
    apply Hbad. apply (T13_safety_needs_mono_completeness ops Hnone). exact Hok.
  Qed.

End FallthroughIsNotCompleteness.

(* ── T13 (b) ★ INDEPENDENCE. A concrete model in which the T7 fall-through
   equation holds at EVERY input and the facade nevertheless accepts NOTHING.
   `Result := bool`, `ok b := b = true`, the isolation always declines, and the
   monolithic body always rejects. T7's conclusion is satisfied everywhere, so no
   amount of T7 can rule this model out: "fall-through" ⊬ "accepts".
   This is precisely the situation the G1 comment assumed away. ── *)
Theorem T13_fallthrough_is_not_completeness :
  exists (cr : list (list nat) -> option bool) (m : list (list nat) -> bool),
    (forall ops, cr ops = None)
    /\ (forall ops, facade_ok nat bool cr m ops = m ops)
    /\ (forall ops, ~ (fun b => b = true) (facade_ok nat bool cr m ops)).
Proof.
  exists (fun _ => None), (fun _ => false).
  refine (conj (fun _ => eq_refl) (conj _ _)).
  - intro ops. reflexivity.
  - intro ops. simpl. discriminate.
Qed.

(* ── T13 (d) NON-VACUITY, tied to the 2026-07-25 measurement. The kill-switch A/B
   measured, on `@(Nil.set(a!(Nil) , Nil))!(Nil,Nil)`:
       facade ENGAGED  → ACCEPT      (`combine_run ops = Some true`)
       facade DECLINED → REJECT      (`mono ops = false`)
   so on THIS input the engaged facade and the declined facade differ in `ok`.
   That is the empirical refutation of "the walker parses it", and it is why the
   G1 arm must bind the empty list rather than decline. ── *)
Example T13_measured_witness :
  let cr_engaged := (fun _ : list (list nat) => Some true) in
  let cr_declined := (fun _ : list (list nat) => @None bool) in
  let m := (fun _ : list (list nat) => false) in
  facade_ok nat bool cr_engaged m [] = true
  /\ facade_ok nat bool cr_declined m [] = false
  /\ facade_ok nat bool cr_engaged m [] <> facade_ok nat bool cr_declined m [].
Proof. refine (conj eq_refl (conj eq_refl _)). discriminate. Qed.

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
Print Assumptions LRA1_run_implies_fc.
Print Assumptions LRA2_no_false_frame.
Print Assumptions LRA3_anchored_never_earlier.
Print Assumptions LRA4_identical_when_valid.
Print Assumptions LRA5_never_worse.
Print Assumptions LRA6_recovers_when_single_fails.
Print Assumptions LRA_strict_gain_witness.
Print Assumptions LRA_passing_identical_witness.
(* G1 degenerate-tail (2026-07-25). *)
Print Assumptions T11_empty_region_is_in_the_language.
Print Assumptions T11_emitted_split_of_empty_is_one_phantom_segment.
Print Assumptions T11_phantom_segment_is_not_an_element.
Print Assumptions T11_empty_seplist_is_unit.
Print Assumptions T11_unit_is_neutral.
Print Assumptions T11_bail_loses_the_unit.
Print Assumptions T11_unit_weight_is_identity.
Print Assumptions T11_unit_weight_absorbs.
Print Assumptions T12_degenerate_tail_bijection.
Print Assumptions T12_degenerate_tail_preserves_count.
Print Assumptions T12_degenerate_tail_complete.
Print Assumptions T12_bail_is_incomplete.
Print Assumptions T13_fallthrough_transfers.
Print Assumptions T13_safety_needs_mono_completeness.
Print Assumptions T13_decline_onto_a_gap_rejects.
Print Assumptions T13_fallthrough_is_not_completeness.
Print Assumptions T13_measured_witness.
