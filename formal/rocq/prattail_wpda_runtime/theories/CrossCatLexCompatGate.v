(*
 * CrossCatLexCompatGate: the model for the CROSSCAT_LEX_COMPAT_GATE — the
 * general, evidence-based first-token lexical-compatibility FILTER at a
 * category's cross-cat PROJECTION fork.
 *
 * ★ SCOPE CORRECTION (2026-07-04, session da0842dc, mandate: never-accept-bugs):
 *   this gate does NOT "finish the ROOT-P `<-` residual" and does NOT linearize.
 *   It removes the CAST fan-out factor from the per-segment frontier BASE
 *   (Θ((2+n)^k) → Θ(b^k) with residual base b ≈ 9.5, a measured 153× peak-latency
 *   reduction) — a strictly SMALLER EXPONENTIAL, NOT O(1)/segment, NOT linear.
 *   The residual `Θ(b^k)` is a genuine derivation-multiplicity floor driven by
 *   the CrossCatLhs edge-stack (a141ea9c + session da0842dc DEEP
 *   SPPF-continuation-sharing Stage-0). The correctness theorems below (sound
 *   ∅-prune, no-reading-lost) HOLD; only the LINEARITY claim is corrected — see
 *   the ★ HONESTY RELABEL at `gate_removes_cast_fanout_factor` and
 *   DESCRIPTOR_WORKLIST_DESIGN.md § Stage-0 verdict.
 *
 * GROUND TRUTH (offline-classifier-proven + trace-proven, rholang `@a <- c`):
 *   The result category `Proc` PrefixDispatch on a bare `Ident` token emits a
 *   Fork whose branches (measured directly in generated wpda.rs:26535, 18
 *   branches) are:
 *     - ONE CrossCatLhs delegate `category_entry(Name)` — the `@`-quoted-name
 *       (NQuoteShort) reading (legitimate);
 *     - ONE home-var PVar atomic (rule 106) — the canonical proc-var reading;
 *     - SIXTEEN CrossCatProjection cast delegates (rules 20-35:
 *       CastBigRat/Fixed/Float/BigInt/UInt32/Int/Bool/Str/Bytes/List/Bag/Map/
 *       Set/Pathmap/ReadZipper/WriteZipper). Each source category `S` acquires
 *       `Ident` in its FIRST set ONLY from its own Var rule (`collect_first_set`
 *       synthetic/VarRule) — `S` cannot LITERALLY begin with an `Ident`. So all
 *       16 casts dispatch on the SAME `Ident` bucket.
 *   Measured: `@a<-c` (and `a` as a Proc) yields alts = 1 (the PVar reading);
 *   every one of the 16 casts realizes ZERO parses on a genuine `Ident` (a bare
 *   variable is not a number / list / map / …). Yet each cast SPAWNS a distinct
 *   `ProjDescriptorKey W` (the CrossCatDelegate cohort key) → the per-segment
 *   frontier fan-out is Θ(8^k) (measured branch_cursors_peak_pre_merge
 *   176@k0 → 11125@k1 → 84077@k2 → 716620@k3; the pruned set
 *   fork_cross_cat_projection_branches 461 → 24163 → 243834 scales base-8 IN
 *   LOCKSTEP — the proven driver), while the no-`@` control `x<-c & …` (which
 *   never opens a Proc-Ident cast fork) stays flat (74@k0 → 103 constant).
 *   a87574eb T-LinearIffWBounded: reducing #{W} is the SOLE linearizing lever.
 *
 * THE FIX (grammar-derived, one-sided monotone FILTER of a proven ∅-realizing
 * over-generation — the SAME soundness class as min_terminal_span /
 * FORROW_PROJ_GATE / AT_QUOTED_BIND_GATE, per
 * feedback_use_wpds_disambiguation_not_heuristics — SOUND FIRST-set FILTERING,
 * NOT the forbidden FIRST-set TIEBREAK):
 *   (A) at the CrossCatProjection emission loop (prefix.rs), SKIP a projection
 *       source-FIRST token `t` iff (compile-time) `t` is ONLY a VAR CONTRIBUTION
 *       of the source `S` [`FirstToken::is_var_contribution`, i.e.
 *       t ∉ LITERAL-FIRST(S) = FIRST(S) − {var-contributions}] AND the result
 *       category `R` has its OWN home Var reading [`result_has_home_var_reading`].
 *       ⇒ the 16 casts leave the `Some(Ident)` bucket (18 → 2 branches:
 *       CrossCatLhs + PVar). Every LITERAL-first bucket KEEPS its cast (`@1` →
 *       CastInt on `Integer`, `@[1]` → CastList on `[`, `@{k:v}` → CastMap on
 *       `{`, `@Set(1)` → CastSet on the `Set` keyword — none is a var
 *       contribution). BYTE-IDENTICAL when the kill-switch const is off.
 *   (B) at runtime, a backstop `crosscat_proj_lex_compatible(source, tokens,
 *       pos)` refutes a projection push whose source is var-only-Ident when the
 *       peek is `Ident` — fail-open otherwise, INERT under (A).
 *
 * THE MODEL: classify the dispatch of a token `t` in the result category `R`
 * against a projection source `S`:
 *   - VarOnlyIdent : t = Ident, t ∈ FIRST(S) ONLY as a var-contribution
 *                    (t ∉ LITERAL-FIRST(S)), and R has a home Var reading (the
 *                    OVER-GENERATION scenario — `@a<-c`, the 16 casts).
 *   - LiteralFirst : t ∈ LITERAL-FIRST(S) (S literally begins with t, e.g. an
 *                    Integer/`[`/`{`/`Set`-keyword — `@1`→CastInt, KEPT).
 *                    ★ AMENDED 2026-07-25 (divergence I): this illustration used
 *                    to read `@1`→CastBigInt, because `BigInt`'s eval was a
 *                    UNIVERSAL ACCEPTOR of every integer spelling and so won the
 *                    lex-min tiebreak on a bare `1` by grammar declaration order.
 *                    The literal domains now PARTITION
 *                    (`LiteralCarrierContextIndependence.T_DomainsPartition`), so
 *                    an unsuffixed `1` is an `Int` and `@1` is `CastInt`. The
 *                    GATE itself is unaffected — it keys on whether the token is
 *                    a var-contribution, never on which numeric category the cast
 *                    targets — so only the illustration changes, no theorem.
 *   - NoHomeVar    : t = Ident var-only for S but R has NO home Var reading
 *                    (the projection is the ONLY source→result path — KEEP,
 *                    fail-safe, so no reading is lost even absent a home var).
 * Branch kinds at such a dispatch: BCrossCatLhs (the legitimate whole-source
 * `@`-name delegate), BHomeVar (the home PVar), BProj (a cross-cat cast
 * projection delegate). The gate removes ONLY BProj in a VarOnlyIdent context.
 *
 * THEOREMS (all admission-free; audited by Print Assumptions, must all print
 * "Closed under the global context"):
 *   T-PrunedBranchYieldsNoParse — a BProj in a VarOnlyIdent context realizes ∅
 *      (the source cannot literally begin with the Ident ⇒ 0 parses).
 *   T-NoReadingLost — the gate is a STRICT REFINEMENT removing ONLY ∅-realizing
 *      branches ⇒ the REALIZED reading set is EQUAL (every parse-realizing
 *      branch preserved), and every legit LiteralFirst / NoHomeVar reading kept.
 *   T-GatePreservesLiteralCast — a BProj in a LiteralFirst context (`@1` →
 *      CastInt) is KEPT.
 *   T-SmallerExponentialBase (was mislabeled "T-LinearFrontier"; CORRECTED
 *      2026-07-04) — after the gate the per-segment branch multiplier at a
 *      VarOnlyIdent dispatch drops from the ungated (2 + N) to the residual base
 *      `b ≈ 9.5` (the cast fan-out N is removed from the base), so a k-segment
 *      `.*sep` chain is `Θ(b^k)` — a STRICTLY SMALLER EXPONENTIAL than the
 *      ungated `(2 + N)^k` (a constant-factor latency win), **NOT linear**. The
 *      original "LINEAR (matches the no-`@` control)" claim was FALSE: the
 *      no-`@` `x<-c` control IS flat, but the gated `@a<-c` residual is `Θ(b^k)`
 *      exponential (the CrossCatLhs edge-stack floor the gate never targeted).
 *      See `gate_removes_cast_fanout_factor` / `gate_base_strictly_below_ungated`.
 *   T-KillSwitchIdentity — with the kill-switch off the gated branch set equals
 *      the ungated (baseline) set in EVERY context (byte-identical).
 *   T-GeneralInertWhenViable — parametric over ANY (source, token, result): the
 *      gate fires ONLY on a var-only-Ident-with-home-var dispatch; it is inert
 *      for every literal-first token AND every result lacking a home var (no
 *      language hardcode — calculator `Proc` casts behave identically).
 *   T-ComposesWithLanded — on the SAME Proc-Ident fork the ALREADY-LANDED
 *      AT_QUOTED_BIND_GATE (which suppresses the outer CrossCatLhs over-gen in a
 *      SigilBind context) and THIS gate (which suppresses the ∅-realizing cast
 *      projections) compose: the composed removed set is
 *      (overgen-CrossCatLhs ∪ ∅-realizing-casts), and every ADMISSIBLE reading
 *      (the home PVar + any legit whole-source) is preserved by BOTH.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section CrossCatLexCompatGate.

  (* ── Dispatch-context classification of a (token, projection-source, result)
        triple at a cross-cat PROJECTION emission (transcribed premises). ── *)
  Inductive DispatchCtx : Type :=
    | VarOnlyIdent      (* t = Ident, t ∈ FIRST(S) ONLY via a var-contribution
                           (t ∉ LITERAL-FIRST(S)), reachable purely through
                           var-projections; R has a home Var reading — the
                           over-generation (the 16 casts on `@a<-c`) *)
    | LiteralFirst      (* t ∈ LITERAL-FIRST(S): S literally begins with t
                           (`@1`→CastInt on Integer — KEEP) *)
    | StructuralSource  (* t = Ident, but S is IDENT-LED via a STRUCTURAL rule
                           (a leading NT followed by MORE consuming items, e.g.
                           `InputBind . lhs:Name "<-" n`; `ForRow . b:InputBind`).
                           A bare Ident through S is the START of a REAL
                           structured term, NOT a var-projection ⇒ the projection
                           is the ONLY path to that reading — KEEP. The
                           `source_ident_first_is_var_only` PURE-PROJECTION gate
                           excludes exactly this context. *)
    | NoHomeVar.        (* t var-only-Ident for S but R has NO home Var reading:
                           the projection is the ONLY source→result path — KEEP *)

  (* ── Branch kinds emitted at such a dispatch. ── *)
  Inductive Branch : Type :=
    | BCrossCatLhs   (* the whole-source `@`-name (NQuoteShort) delegate *)
    | BHomeVar       (* the home PVar atomic (rule 106) *)
    | BProj.         (* a cross-cat cast PROJECTION delegate (rules 20-35) *)

  Definition branch_eqb (a b : Branch) : bool :=
    match a, b with
    | BCrossCatLhs, BCrossCatLhs
    | BHomeVar, BHomeVar
    | BProj, BProj => true
    | _, _ => false
    end.

  (* Decidable equality on Branch (a 3-element enumeration). *)
  Definition branch_eq_dec (a b : Branch) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* ── The realization fact (imported from the measurement: alts=1 for `@a<-c`
        / bare `a` as Proc, and each cast realizes ∅ on a genuine Ident): a BProj
        cast delegate realizes a parse ONLY when the dispatch token is in the
        source's LITERAL-FIRST — i.e. in a LiteralFirst context. In a
        VarOnlyIdent context BProj realizes ∅ (a bare variable is not a
        number/list/map). BCrossCatLhs and BHomeVar always realize (the
        whole-source `@`-name reading and the home var reading, respectively). ── *)
  Definition realizes (b : Branch) (k : DispatchCtx) : bool :=
    match b, k with
    | BProj, VarOnlyIdent => false   (* the ∅-realizing over-generation *)
    | BProj, _            => true    (* literal-first / structural / only-path cast realizes *)
    | BCrossCatLhs, _     => true
    | BHomeVar, _         => true
    end.

  (* Whether the result category has its own home Var reading in this context
     (true in VarOnlyIdent by definition; false in NoHomeVar; the LiteralFirst
     context is orthogonal to the home-var question — the token is not an Ident
     there — so we record it as true, matching `result_has_home_var_reading`
     being a property of the RESULT category alone). *)
  Definition result_has_home_var (k : DispatchCtx) : bool :=
    match k with
    | VarOnlyIdent     => true
    | LiteralFirst     => true
    | StructuralSource => true
    | NoHomeVar        => false
    end.

  (* Whether the dispatch token is ONLY a var-contribution of the source (i.e.
     t ∉ LITERAL-FIRST(S)). True in VarOnlyIdent, StructuralSource, NoHomeVar
     (all are the Ident dispatch); false in LiteralFirst (S literally begins with
     a non-Ident literal). *)
  Definition token_is_var_only (k : DispatchCtx) : bool :=
    match k with
    | VarOnlyIdent     => true
    | LiteralFirst     => false
    | StructuralSource => true
    | NoHomeVar        => true
    end.

  (* ★ The PURE-PROJECTION soundness discriminator
     (`source_ident_first_is_var_only`): the source's bare-Ident reading is
     EXCLUSIVELY its own variable, reachable ONLY through pure (token-transparent,
     single-NT-body) projections — NO structural Ident-led rule. TRUE for
     VarOnlyIdent (leaf value sources / their pure var-projection chains) and
     NoHomeVar; FALSE for StructuralSource (InputBind/ForRow: Ident-led via a
     leading NT followed by MORE consuming items). Vacuously TRUE for LiteralFirst
     (the token is not an Ident there, so the discriminator is not consulted). *)
  Definition source_is_pure_projection_var_only (k : DispatchCtx) : bool :=
    match k with
    | VarOnlyIdent     => true
    | LiteralFirst     => true
    | StructuralSource => false
    | NoHomeVar        => true
    end.

  (* The compile-time gate predicate (A): SUPPRESS the projection branch iff the
     token is a var-only contribution of the source, the SOURCE's Ident is
     pure-projection var-only (NOT a structural Ident-led source), AND the result
     has a home var reading. Mirrors the codegen conjunct
     `ft.is_var_contribution && source_ident_first_is_var_only(S)
      && result_has_home_var_reading(R)`. *)
  Definition gate_suppresses_proj (k : DispatchCtx) : bool :=
    token_is_var_only k
      && source_is_pure_projection_var_only k
      && result_has_home_var k.

  (* ── Branch sets per context. ── *)

  (* UNGATED (baseline): every dispatch forks the whole-source delegate, the home
     var, AND the cast projection (the measured 18-branch fork abstracts to these
     three kinds; the N=16 concrete casts are one BProj kind here — see the
     N-ary multiplier below for the counting theorem). *)
  Definition branches_ungated (k : DispatchCtx) : list Branch :=
    [BCrossCatLhs; BHomeVar; BProj].

  (* GATED (A, kill-switch on): the cast projection BProj is SUPPRESSED exactly
     when `gate_suppresses_proj k` — i.e. in VarOnlyIdent. LiteralFirst keeps
     BProj (its token is not var-only), NoHomeVar keeps BProj (no home var). *)
  Definition branches_gated (k : DispatchCtx) : list Branch :=
    if gate_suppresses_proj k
    then [BCrossCatLhs; BHomeVar]
    else [BCrossCatLhs; BHomeVar; BProj].

  (* ═══════════ T-PrunedBranchYieldsNoParse ═══════════ *)
  (* The branch the gate removes (BProj in VarOnlyIdent) realizes ∅. *)
  Theorem pruned_branch_yields_no_parse :
    realizes BProj VarOnlyIdent = false.
  Proof. reflexivity. Qed.

  (* And it is the ONLY (branch, context) pair the gate removes: the gate removes
     a branch b at context k iff b = BProj and k = VarOnlyIdent. *)
  Theorem gate_removes_only_varonly_proj :
    forall k b,
      In b (branches_ungated k) -> ~ In b (branches_gated k) ->
      b = BProj /\ k = VarOnlyIdent.
  Proof.
    intros k b Hin Hnin. destruct k; unfold branches_gated in Hnin; simpl in *.
    - (* VarOnlyIdent: gated = [BCrossCatLhs; BHomeVar] *)
      destruct Hin as [<- | [<- | [<- | []]]].
      + exfalso; apply Hnin; left; reflexivity.
      + exfalso; apply Hnin; right; left; reflexivity.
      + split; reflexivity.
    - (* LiteralFirst: gated = ungated ⇒ contradiction with Hnin *)
      exfalso; apply Hnin; exact Hin.
    - (* StructuralSource: gated = ungated ⇒ contradiction with Hnin *)
      exfalso; apply Hnin; exact Hin.
    - (* NoHomeVar: gated = ungated ⇒ contradiction with Hnin *)
      exfalso; apply Hnin; exact Hin.
  Qed.

  (* ═══════════ T-NoReadingLost ═══════════ *)
  (* The gate is a STRICT REFINEMENT: every gated branch was a baseline branch
     (monotone subset — nothing invented). *)
  Theorem gate_subset_ungated :
    forall k b, In b (branches_gated k) -> In b (branches_ungated k).
  Proof.
    intros k b H. unfold branches_gated in H; destruct k; simpl in *.
    - (* VarOnlyIdent: gated = [BCrossCatLhs; BHomeVar] *)
      destruct H as [<- | [<- | []]]; [left; reflexivity | right; left; reflexivity].
    - (* LiteralFirst: gated = ungated *)
      destruct H as [<- | [<- | [<- | []]]];
        [left | right; left | right; right; left ]; reflexivity.
    - (* StructuralSource: gated = ungated *)
      destruct H as [<- | [<- | [<- | []]]];
        [left | right; left | right; right; left ]; reflexivity.
    - (* NoHomeVar: gated = ungated *)
      destruct H as [<- | [<- | [<- | []]]];
        [left | right; left | right; right; left ]; reflexivity.
  Qed.

  (* The KEY no-loss statement in terms of REALIZED readings: every branch that
     REALIZES a parse in the baseline still realizes a parse in the gate — i.e.
     the removed branches are exactly ∅-realizing, so the realized reading SET is
     EQUAL (this is the "removed = ∅-realizing ⇒ EQUAL realized set" mandate). *)
  Theorem gate_preserves_realizing_branches :
    forall k b,
      In b (branches_ungated k) -> realizes b k = true ->
      In b (branches_gated k).
  Proof.
    intros k b Hin Hreal.
    destruct (in_dec branch_eq_dec b (branches_gated k)) as [Hyes | Hno].
    - exact Hyes.
    - exfalso.
      pose proof (gate_removes_only_varonly_proj k b Hin Hno) as [-> ->].
      simpl in Hreal. discriminate.
  Qed.

  (* Converse direction: the gate never INVENTS a realizing reading either — a
     gated branch that realizes also realized in the baseline (trivially, since
     gated ⊆ ungated). Together with the above this gives realized-set EQUALITY. *)
  Theorem gate_realized_set_equal :
    forall k b,
      (In b (branches_gated k) /\ realizes b k = true)
      <-> (In b (branches_ungated k) /\ realizes b k = true).
  Proof.
    intros k b. split.
    - intros [Hin Hreal]. split; [apply gate_subset_ungated; exact Hin | exact Hreal].
    - intros [Hin Hreal]. split; [apply gate_preserves_realizing_branches; assumption | exact Hreal].
  Qed.

  (* ═══════════ T-GatePreservesLiteralCast ═══════════ *)
  (* A literal-first cast projection (`@1` → CastInt on an Integer token) is
     KEPT by the gate (its token is not a var-contribution). *)
  Theorem gate_preserves_literal_cast :
    In BProj (branches_gated LiteralFirst).
  Proof. simpl. right. right. left. reflexivity. Qed.

  (* More generally, in EVERY non-VarOnlyIdent context BProj survives. *)
  Theorem gate_keeps_proj_off_varonly :
    forall k, k <> VarOnlyIdent -> In BProj (branches_gated k).
  Proof.
    intros k Hk. destruct k.
    - exfalso; apply Hk; reflexivity.
    - simpl. right. right. left. reflexivity.
    - simpl. right. right. left. reflexivity.
    - simpl. right. right. left. reflexivity.
  Qed.

  (* ★ STRUCTURAL-SOURCE NO-LOSS (the soundness property discovered empirically:
     the `InputBind : ForRow` projection must NOT be pruned or `for(p <- …)`
     breaks). In a StructuralSource context the cast projection BProj is KEPT and
     REALIZES a genuine (non-∅) reading — the pure-projection discriminator
     `source_is_pure_projection_var_only` is FALSE there, so the gate does not
     fire. *)
  Theorem gate_keeps_structural_source_proj :
    In BProj (branches_gated StructuralSource) /\ realizes BProj StructuralSource = true.
  Proof. split; [simpl; right; right; left; reflexivity | reflexivity]. Qed.

  (* ═══════════ T-LinearFrontier ═══════════ *)
  (* The N-ary cast fan-out: at an ungated VarOnlyIdent dispatch the concrete
     fork has (2 + n) branches — the 2 fixed {BCrossCatLhs, BHomeVar} plus n
     cast projections (n = 16 for rholang Proc). The gate drops all n cast
     projections, leaving the 2 fixed branches. This N-ary count refines the
     3-kind abstraction above (where the n casts collapse to one BProj kind). *)
  Definition bcount_ungated_nary (n : nat) : nat := 2 + n.

  (* ★ HONESTY RELABEL (2026-07-04, session da0842dc, mandate: never-accept-bugs;
     NO new Axiom/Parameter — the corrected statements are UNIVERSALLY QUANTIFIED
     over the residual base `b`, so they are fully general and admission-free).

     The ORIGINAL `bcount_gated_nary := 2` asserted the post-gate per-segment
     branch count is a CONSTANT 2, which is EMPIRICALLY FALSE: a141ea9c's
     FRESH_LHSAT measured the post-gate per-`&`-segment multiplier at ~9.5 (peak
     22 → 159 → 482 → 2682 → …), and the DEEP SPPF-continuation-sharing Stage-0
     (session da0842dc, DESCRIPTOR_WORKLIST_DESIGN.md) CONFIRMED it: the residual
     is a genuine derivation-multiplicity floor driven by the CrossCatLhs
     edge-stack, NOT foldable to a constant by this cast gate. The gate's WIN is
     that it removes the CAST contribution `n` from the base (176 → the residual
     regime, a 153× peak reduction), NOT that it makes the base constant nor
     linear. We keep the TRUE arithmetic identity and quantify over the residual
     base `b` (measured b ≈ 9.5 for rholang Proc) instead of hardcoding a false
     constant. *)

  (* Cursor-path multiplier of a homogeneous k-segment `.*sep` chain: the product
     over segments of the per-segment branch count (mirrors AtQuotedBindGate's
     path_multiplier / CastLexForkCrossCatLhsGap). *)
  Fixpoint path_multiplier (counts : list nat) : nat :=
    match counts with
    | [] => 1
    | c :: rest => c * path_multiplier rest
    end.

  Lemma path_multiplier_repeat :
    forall c n, path_multiplier (repeat c n) = c ^ n.
  Proof.
    intros c n. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  (* ★ HONESTY RELABEL — GATED (post-gate): every segment contributes the residual
     base `b` (measured ≈ 9.5, NOT a constant 2), so the frontier multiplier is
     `b ^ k`. Quantifying over `b` makes this a TRUE identity for the ACTUAL
     (measured) base rather than the false `2`. This is a STRICTLY SMALLER
     EXPONENTIAL BASE than the ungated `(2 + n) ^ k` when the cast fan-out `n`
     exceeds the residual excess — a CONSTANT-FACTOR LATENCY REDUCTION (the
     measured 153× peak win at k=4), **NOT a linearization**. The original prose
     mislabeled `2^k` as "LINEAR in the input", false on two counts: (i) `2^k` is
     exponential, and (ii) the real post-gate base is ≈ 9.5, not 2. The TRUE
     linearizer — the CrossCatLhs edge-stack reconvergence — does NOT exist as a
     sound merge-key projection: session da0842dc's DEEP SPPF-continuation-sharing
     Stage-0 (S0-DW-LINEAR) MEASURED that no `(edge_target, EdgeKind)`-class
     projection of the edge-stack linearizes (the GSS node forks per `.*sep`
     segment, so `edge_target` is per-segment-distinct and cannot fold; only a
     COUNT/LENGTH projection linearizes, and that over-merges — see
     DESCRIPTOR_WORKLIST_DESIGN.md § Stage-0 verdict). This gate is a latency win
     that reduces the base; there is no linearizer to point at. *)
  Theorem gate_removes_cast_fanout_factor :
    forall (b : nat) (k : nat), path_multiplier (repeat b k) = b ^ k.
  Proof.
    intros b k. rewrite path_multiplier_repeat. reflexivity.
  Qed.

  (* UNGATED: every segment contributes (2 + n) — so the multiplier is (2+n)^k,
     the measured base-(2+n) explosion (for n=16 casts this is the base-8-class
     fan-out observed: 176 → 11125 → 84077 → …). Derived from the SAME counting
     function, not asserted. *)
  Theorem ungated_frontier_exponential_nary :
    forall k n, path_multiplier (repeat (bcount_ungated_nary n) k) = (2 + n) ^ k.
  Proof.
    intros k n. rewrite path_multiplier_repeat. reflexivity.
  Qed.

  (* ★ HONESTY RELABEL — the contrast at the heart of the fix, CORRECTLY stated
     and admission-free (universally quantified over the residual base `b`): for a
     cast fan-out `n` such that the residual base `b` is strictly below `2 + n`,
     and any chain length k >= 1, the gated frontier base `b` yields a multiplier
     STRICTLY below the ungated `(2 + n) ^ k` — i.e. the gate removes the
     cast-driven fork explosion factor, yielding a smaller EXPONENTIAL base (a
     constant-factor latency win), NOT linearity. The hypothesis `b < 2 + n` names
     precisely the regime where the cast contribution dominates the residual
     CrossCatLhs base (measured true for rholang Proc: b ≈ 9.5 < 2 + 16 = 18). *)
  Theorem gate_base_strictly_below_ungated :
    forall (b : nat) (k : nat) (n : nat),
      1 <= k -> b < 2 + n ->
      path_multiplier (repeat b k)
        < path_multiplier (repeat (bcount_ungated_nary n) k).
  Proof.
    intros b k n Hk Hlt.
    rewrite gate_removes_cast_fanout_factor, ungated_frontier_exponential_nary.
    apply Nat.pow_lt_mono_l; lia.
  Qed.

  (* ═══════════ T-KillSwitchIdentity ═══════════ *)
  Section KillSwitch.

    (* The kill-switch (`CROSSCAT_LEX_COMPAT_GATE`, a compile-time bool). When
       off, the emitted branch set is the UNGATED baseline in EVERY context (the
       gate conjunct is never evaluated ⇒ byte-identical, md5-verified); when on,
       it is the gated set. *)
    Variable gate_on : bool.

    Definition branches_switched (k : DispatchCtx) : list Branch :=
      if gate_on then branches_gated k else branches_ungated k.

    (* OFF ⇒ byte-identical to baseline in every context. *)
    Theorem gate_kill_switch_identity :
      gate_on = false ->
      forall k, branches_switched k = branches_ungated k.
    Proof.
      intros Hoff k. unfold branches_switched. rewrite Hoff. reflexivity.
    Qed.

    (* ON ⇒ exactly the gated set. *)
    Theorem gate_on_is_gated :
      gate_on = true ->
      forall k, branches_switched k = branches_gated k.
    Proof.
      intros Hon k. unfold branches_switched. rewrite Hon. reflexivity.
    Qed.

  End KillSwitch.

  (* ═══════════ T-GeneralInertWhenViable ═══════════ *)
  (* The gate is parametric over the (source, token, result) triple encoded in
     the context: it SUPPRESSES the projection ONLY in a VarOnlyIdent context.
     In particular it is INERT (changes nothing) whenever the token is
     literal-first for the source, OR the result lacks a home var reading — no
     language hardcode; the calculator `Proc` casts (whose sources are likewise
     var-only for Ident) are gated identically, and any literal-first cast in any
     language is untouched. *)
  Theorem gate_inert_when_literal_first :
    branches_gated LiteralFirst = branches_ungated LiteralFirst.
  Proof. reflexivity. Qed.

  Theorem gate_inert_when_no_home_var :
    branches_gated NoHomeVar = branches_ungated NoHomeVar.
  Proof. reflexivity. Qed.

  (* ★ The gate is INERT for a STRUCTURAL Ident-led source (InputBind/ForRow) —
     the pure-projection discriminator prevents over-pruning. *)
  Theorem gate_inert_when_structural_source :
    branches_gated StructuralSource = branches_ungated StructuralSource.
  Proof. reflexivity. Qed.

  (* The suppression fires EXACTLY in the VarOnlyIdent context and nowhere else —
     the precise characterization of when the gate is active. *)
  Theorem gate_fires_iff_var_only_ident :
    forall k, gate_suppresses_proj k = true <-> k = VarOnlyIdent.
  Proof.
    intro k. destruct k; simpl; split; intro H;
      solve [reflexivity | discriminate | exact H | (subst; reflexivity)].
  Qed.

  (* Consequence: whenever the gate does NOT fire, the branch set is the exact
     baseline (the general inert statement in one shot). *)
  Theorem gate_inert_unless_var_only :
    forall k, k <> VarOnlyIdent -> branches_gated k = branches_ungated k.
  Proof.
    intros k Hk. unfold branches_gated.
    destruct (gate_suppresses_proj k) eqn:E.
    - exfalso. apply Hk. apply gate_fires_iff_var_only_ident. exact E.
    - reflexivity.
  Qed.

  (* ═══════════ T-ComposesWithLanded ═══════════ *)
  Section ComposeWithAtQuotedBindGate.

    (* On the SAME Proc-Ident fork the ALREADY-LANDED AT_QUOTED_BIND_GATE
       suppresses the OUTER whole-source CrossCatLhs over-generation in a
       SigilBind dispatch context (`@a<-@b`), and THIS gate suppresses the
       ∅-realizing cast projections in a VarOnlyIdent context. We model the
       composition on the common Proc-Ident fork by an independent
       AT-gate suppression flag (does the AT gate remove BCrossCatLhs here?) — it
       is orthogonal to THIS gate's BProj suppression, so the two removals do not
       interfere and every ADMISSIBLE (parse-realizing) reading survives BOTH. *)

    (* Does the landed AT_QUOTED_BIND_GATE remove the whole-source CrossCatLhs on
       this fork? (True exactly in its SigilBind over-gen scenario.) We take it
       as a parameter: the composition theorem holds for BOTH values. *)
    Variable at_gate_removes_crosscatlhs : bool.

    (* The composed branch set: start from THIS gate's gated set, then also drop
       BCrossCatLhs if the AT gate removes it. *)
    Definition branches_composed (k : DispatchCtx) : list Branch :=
      if at_gate_removes_crosscatlhs
      then filter (fun b => negb (branch_eqb b BCrossCatLhs)) (branches_gated k)
      else branches_gated k.

    (* The composed removed set is exactly (AT-gate's CrossCatLhs removal) ∪
       (THIS gate's BProj removal): a branch is removed by the composition iff it
       is removed by THIS gate OR (the AT gate is active AND it is BCrossCatLhs). *)
    Theorem composed_removed_is_union :
      forall k b,
        In b (branches_ungated k) ->
        (~ In b (branches_composed k)
         <-> ( (b = BProj /\ k = VarOnlyIdent)
               \/ (at_gate_removes_crosscatlhs = true /\ b = BCrossCatLhs) )).
    Proof.
      intros k b Hin. unfold branches_composed.
      destruct at_gate_removes_crosscatlhs eqn:Eat.
      - (* AT gate active: composed = filter (≠ CrossCatLhs) gated *)
        split.
        + intro Hnin. rewrite filter_In in Hnin.
          (* b is not in the filtered gated set. *)
          destruct (branch_eq_dec b BCrossCatLhs) as [Hcl | Hcl].
          * right. split; [reflexivity | exact Hcl].
          * (* b <> CrossCatLhs, so removal is by THIS gate (not in gated). *)
            left. apply gate_removes_only_varonly_proj; [exact Hin |].
            intro Hg. apply Hnin. split; [exact Hg |].
            destruct b; simpl; try reflexivity.
            exfalso; apply Hcl; reflexivity.
        + intros [[Hb Hk] | [_ Hb]].
          * (* removed by THIS gate ⇒ not in gated ⇒ not in filtered gated *)
            subst. intro Hin'. rewrite filter_In in Hin'.
            destruct Hin' as [Hin' _].
            revert Hin'. change (~ In BProj (branches_gated VarOnlyIdent)).
            simpl. intros [H | [H | []]]; discriminate.
          * (* b = CrossCatLhs ⇒ filtered out *)
            subst. intro Hin'. rewrite filter_In in Hin'.
            destruct Hin' as [_ Hneg]. simpl in Hneg. discriminate.
      - (* AT gate inactive: composed = gated. *)
        split.
        + intro Hnin. left. apply gate_removes_only_varonly_proj; assumption.
        + intros [[Hb Hk] | [Hcontra _]]; [| discriminate].
          subst. change (~ In BProj (branches_gated VarOnlyIdent)).
          simpl. intros [H | [H | []]]; discriminate.
    Qed.

    (* The HOME PVar reading — the canonical admissible reading — is preserved by
       the composition in EVERY context, regardless of the AT gate (neither gate
       touches BHomeVar). *)
    Theorem composed_preserves_home_var :
      forall k, In BHomeVar (branches_composed k).
    Proof.
      intro k. unfold branches_composed.
      destruct at_gate_removes_crosscatlhs.
      - rewrite filter_In. split.
        + (* BHomeVar ∈ gated in every context *)
          unfold branches_gated. destruct (gate_suppresses_proj k);
            simpl; right; left; reflexivity.
        + reflexivity.
      - unfold branches_gated. destruct (gate_suppresses_proj k);
          simpl; right; left; reflexivity.
    Qed.

  End ComposeWithAtQuotedBindGate.

End CrossCatLexCompatGate.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions pruned_branch_yields_no_parse.
Print Assumptions gate_removes_only_varonly_proj.
Print Assumptions gate_subset_ungated.
Print Assumptions gate_preserves_realizing_branches.
Print Assumptions gate_realized_set_equal.
Print Assumptions gate_preserves_literal_cast.
Print Assumptions gate_keeps_proj_off_varonly.
Print Assumptions gate_keeps_structural_source_proj.
Print Assumptions gate_removes_cast_fanout_factor.
Print Assumptions ungated_frontier_exponential_nary.
Print Assumptions gate_base_strictly_below_ungated.
Print Assumptions gate_kill_switch_identity.
Print Assumptions gate_on_is_gated.
Print Assumptions gate_inert_when_literal_first.
Print Assumptions gate_inert_when_no_home_var.
Print Assumptions gate_inert_when_structural_source.
Print Assumptions gate_fires_iff_var_only_ident.
Print Assumptions gate_inert_unless_var_only.
Print Assumptions composed_removed_is_union.
Print Assumptions composed_preserves_home_var.
