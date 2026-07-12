//! Unified Fork-emission framework — Stage 3.16/3.17/3.18 (Commit 2,
//! 2026-05-05).
//!
//! Replaces deterministic peek-and-decide patterns in WPDS codegen with
//! `WpdaStepAction::Fork` over multiple branches, letting lex-min disambiguate
//! per `feedback_use_wpds_disambiguation_not_heuristics.md`. Branches are
//! emitted unconditionally; branches whose per-branch guards or subsequent
//! steps fail naturally transition to Error/Idle and are discarded as failed
//! derivations. The walker never drops a live cursor solely to satisfy a
//! cursor-count bound.
//!
//! Three already-shipped Forks prove the pattern works:
//! - F7 multi-rule binder (`binder.rs:556-596`)
//! - F8 cross-cat projection (`prefix.rs:932-971`)
//! - A.i Opt-Group sub_pos:0 (`binder.rs:992-1046`)
//!
//! This module unifies the 11 remaining fork sites (Cluster 1: 5 sites; Cluster 2:
//! 2 sites; Cluster 3: 3 sites — Cluster 4 #18/#19 is Commit 3, Cluster 5 is
//! Commit 4) under a small helper API.
//!
//! ## Design notes
//!
//! - **Source-order tiebreak via rule_idx.** Load-bearing per Class A.i
//!   precedent. All Forks must use rule_idx for deterministic disambiguation.
//! - **Lex-min weighting.**
//!   `lex_w(bias, src, rule)` is the standard weight
//!   constructor for new Fork branches; per-tier bias offsets enforce
//!   inter-tier ordering on weight ties.
//! - **Cursor explosion mitigation.** Each Fork emission grows the cursor
//!   count by N; nested call sites multiply. Cursor-count bounds are explicit
//!   opt-in overflow checks (`CursorBoundingMode::BeamSize` compatibility
//!   mode or `AmbiguityBudget`) that report structured ambiguity-budget
//!   overflow instead of silently truncating the frontier.
//! - **Unconditional branch emission.** Following the F7/F8/A.i pattern,
//!   branches are pushed into the Fork unconditionally; per-branch runtime
//!   correctness is enforced when the cursor's subsequent step against the
//!   token stream either matches or transitions to Error. This is simpler
//!   than codegen-time guard evaluation and matches the WPDS principle of
//!   "emit all valid branches, let lex-min pick the survivor."

#![allow(dead_code)]

use proc_macro2::TokenStream;
use quote::quote;

// ─────── Per-cluster constants ───────────────────────────────────────────

/// Cluster 1 SKIP-branch weight bias. Reused from `EPSILON_OPT_SKIP` for
/// consistency with the canonical Opt-Group A.i Fork.
pub(crate) const SKIP_BIAS: f64 = 0.5;

/// Cluster 5 (Commit 4) base offset for recovery branches.
pub(crate) const RECOVERY_BASE: u16 = 0xFE00;

/// Cluster 3 BP-tier biases. Lower wins on lex-min; tier 0 (infix) is
/// preferred over postfix/mixfix when l_bp ties.
pub(crate) const BP_TIER_INFIX: f64 = 0.00;
pub(crate) const BP_TIER_CROSSCAT_LHS: f64 = 0.05;
pub(crate) const BP_TIER_POSTFIX: f64 = 0.10;
pub(crate) const BP_TIER_MIXFIX: f64 = 0.20;

/// ForRow F3 symmetric projection-suppression gate kill switch (2026-06-28).
///
/// Compile-time `const` resolved at macro expansion (the
/// [`crate::gen::runtime::wpda_codegen::infix::GEN1_MAX_SLICE`] kill-switch
/// convention — NOT a runtime env var). When `true`, the transparent
/// cross-cat PROJECTION delegate emitted in the prefix lex-fork
/// ([`emit_lex_fork_at_prefix_dispatch`], both `CrossCatProjection` arms) is
/// SUPPRESSED at a dispatch where a row-scoped EXTENSION trigger binds the
/// same LHS AND a transparent projection `source → result` fallback exists —
/// the exact DUAL of the F0 extension push-gate (the `CrossCatLhs` arms in the
/// same fn). This yields EXACTLY ONE delegate per dispatch (extension when
/// triggered, projection otherwise), collapsing the F2 multiplicative
/// (`2^N`) `&`-join cursor-frontier explosion that the futile projection
/// sibling caused.
///
/// When `false`, the gate is inert: the generated guard folds to
/// `!(false && …) == true`, so the projection push is kept unconditionally —
/// behaviorally byte-identical to the pre-F3 (F2) emission. Flip to `false`
/// to A/B the gate off without reverting; full revert = restore the pre-F3
/// snapshot.
pub(crate) const FORROW_PROJ_GATE: bool = true;

/// KWAMBIG_PROJ_EXEMPT_GATE — the ROOT-A fix (keyword/ident-ambiguous bare
/// cross-cat PROJECTION exemption from the F3 row-scoped-trigger suppression;
/// 2026-07-07). Compile-time `const` resolved at macro expansion (the
/// [`FORROW_PROJ_GATE`] / [`AT_QUOTED_BIND_GATE`] kill-switch convention).
///
/// ## The defect it ships the fix for (ROOT A — the display-roundtrip blocker)
/// A comma-separated `Proc`-operand sequence FAILS to parse when one operand is a
/// keyword/ident-ambiguous bare cross-cat projection (`CastBool` of `true`/`false`
/// — the ONLY such trigger in rhocalc: `true`/`false` lex as BOTH a `Bool` literal
/// keyword AND an `Ident`) AND a LATER comma-operand carries a top-level send
/// (`!(`/`!!(`). Minimal: `fraction(false, a!(0))` FAILS; `fraction(0, a!(0))`,
/// `fraction(Nil, a!(0))`, `fraction((false), a!(0))`, `fraction(false, (a!(0)))`
/// all PASS. Generalizes to `[false, a!(0)]`. The grammar ADMITS the derivation
/// `FractionProc(CastBool(false), POutput(a,0))`; the parser wrongly cannot build
/// it (BOTH the demand `parse` and the exhaustive `parse_via_wpda_all` fail).
///
/// ## Root cause (measured, impl-step-0 2026-07-07)
/// When the ambiguous `false` operand is dispatched, its `Bool→Proc` projection
/// (`CastBool`, `LexAltRuleKind::CrossCatProjection`) is emitted through the F3
/// [`FORROW_PROJ_GATE`] suppression in [`emit_lex_fork_at_prefix_dispatch`] (both
/// `CrossCatProjection` arms). That gate suppresses the projection when
/// `prefix_crosscat_lhs_trigger_ahead_scoped(primary_src, …)` sees a cross-cat-LHS
/// trigger AT DEPTH 0 ahead AND a transparent `source→result` projection fallback
/// exists. The scoped scan starts at depth 0 from the operand position and — the
/// operand separator `,` is NOT a bracket opener and NOT a `row_sep` — it walks
/// PAST the comma and sees the NEXT operand's send `!` at depth 0, concluding a
/// send trigger "binds" the `false` LHS. It does not: `!` binds a `Name` send
/// channel (a metavariable LHS), while `false` is a self-contained `Bool` literal
/// belonging to a different comma-operand. So the `Bool→Proc` projection is
/// wrongly suppressed, `false` never reads as `Bool`, `CastBool` never forms, and
/// no `FractionProc` derivation exists. (`(a!(0))` PASSES because its `!` sits at
/// depth 1 inside parens — never counted; `(false)` PASSES because a parenthesized
/// operand is not the ambiguous-token lex-fork path — F3 never applies.)
///
/// ## The fix — ADD the missing reading (ambiguity-preserving, one-sided monotone)
/// EXEMPT from the F3 suppression any projection whose lex-fork trigger token is a
/// KEYWORD reading (`kind ≠ Ident`) of an IDENT-AMBIGUOUS position (some reading at
/// `*pos` IS `Ident`). Such a projection reads a self-contained keyword LITERAL of
/// the source category (`true`/`false` ⇒ a complete `Bool`); a keyword literal can
/// NEVER be the metavariable LHS the pending cross-cat-LHS extension trigger binds,
/// so the F3 futility premise never holds for it. This is GRAMMAR-DERIVED (keys on
/// the token being a keyword-of-an-ambiguous-position, NOT on `fraction`/`Bool`
/// names) and STRICTLY ADDITIVE: it can only flip `__proj_keep` from `false` to
/// `true` (keep a projection F3 removed), never the reverse — the REALIZED reading
/// set only GROWS, restoring the admitted `CastBool` derivation. It is NOT an
/// early-disambiguation tiebreak (it selects no winner; the added branch competes
/// on evidence exactly like every other). The `@a<-a & @a<-a` ForRow `&`-join that
/// F3 protects is UNAFFECTED: its `InputBind→ForRow` projection is triggered by
/// `@`/`Ident` (not a non-Ident keyword of an ident-ambiguous position — `@` is not
/// even lexically ambiguous), so the exemption never matches it and the F2 `2^N`
/// suppression stays intact.
///
/// ## Kill-switch / A-B
/// `false` ⇒ the exemption conjunct + the `__pos_has_ident_reading` decl are
/// OMITTED ENTIRELY from the emission (the [`AT_QUOTED_BIND_GATE`] convention) ⇒
/// the generated `wpda.rs` is TEXTUALLY BYTE-IDENTICAL (md5-verified) to the pre-fix
/// baseline. `true` (SHIP DEFAULT — this IS the fix) ⇒ the exemption is folded into
/// both `CrossCatProjection` arms' `__proj_keep`. FV: `KwAmbigProjExempt.v` (mirror
/// `AtQuotedBindGate.v`: exempt_no_loss one-sided monotone — the gated keep-set is a
/// strict SUPERSET of the F3 keep-set and every added branch is a keyword-literal
/// projection whose F3 futility premise is false, so no reading is lost and the
/// realized set only grows).
pub(crate) const KWAMBIG_PROJ_EXEMPT_GATE: bool = true;

/// AT_QUOTED_BIND_GATE — parse-time evidence gate for the `@`-quoted bind
/// over-generation (2026-07-03). Kill-switch `const` (compile-time, folded into
/// the generated CrossCatLhs push guard as a literal `true`/`false`, the same
/// convention as [`FORROW_PROJ_GATE`]).
///
/// ## What over-generation
/// A grammar with BOTH (i) a generic cross-category-LHS bind rule
/// `result ::= source <bind-trigger> …` whose `source` FIRST-set contains a
/// SIGIL `σ` (e.g. rhocalc `InputBind ::= Name "<-" Name`, `Name`'s FIRST
/// includes `@` via `NQuoteShort "@" p`), AND (ii) a SIBLING rule
/// `result ::= σ operand <same-bind-trigger> …` that begins with the SAME
/// sigil (e.g. `InputBindQuoted ::= "@" pat "<-" n`) admits TWO readings of
/// `σx <bind> …`: the whole-`source` reading `result(source=σx, …)` (parse `σx`
/// as one `source` atom, then project `source → result`) and the direct
/// sigil-triggered reading `result_quoted(operand=x, …)`. The whole-`source`
/// reading is a GRAMMAR OVER-GENERATION with no canonical counterpart (proven
/// for rhocalc against tree-sitter grammar.js + the interpreter + 100% corpus;
/// `@a` in a bind LHS is UNAMBIGUOUSLY a quoted pattern = the scalar
/// `InputBindQuoted`). Keeping it makes every such bind ≥2-way ambiguous, which
/// under a `.*sep` repetition (`@a<-@b & …`) compounds multiplicatively (the
/// measured ROOT-P `674@k0 → 146011@k1` fork explosion), while the no-sigil
/// control (`x<-c & …`) stays flat.
///
/// ## The gate
/// At the RESULT-category PrefixDispatch fork on `σ`, the whole-`source` reading
/// is carried by exactly one branch: the `PushCrossCatLhs` delegate
/// `category_entry(source)` (parse `σ…` as a `source` atom). When `AT_QUOTED_BIND_GATE`
/// is `true`, that branch is SUPPRESSED iff BOTH: (a) `σ` (this bucket's
/// leading structural literal) is ALSO the leading literal of a sibling rule in
/// the result category [compile-time, grammar-derived — the direct
/// sigil-triggered rule that subsumes the whole-`source` reading exists]; AND
/// (b) a bind-trigger is scoped-ahead in this row
/// (`prefix_crosscat_lhs_trigger_ahead_scoped`, runtime — positive evidence a
/// bind is being formed). The direct sigil-triggered rules (InputBindQuoted
/// family) are UNTOUCHED, so `alts` collapses `2 → 1` to the scalar reading.
///
/// ## Soundness (one-sided monotone refutation, per
/// `feedback_use_wpds_disambiguation_not_heuristics`)
/// This is EVIDENCE rule-out of a PROVEN over-generation, NOT a weight-pick of
/// a genuine ambiguity — the `σ`-quoting discriminator is STATIC + DEFINITIONAL
/// (same class as `min_terminal_span` / `FORROW_PROJ_GATE`). Condition (a) is a
/// strict grammar refinement: the delegate is dropped ONLY where a direct
/// sigil-sibling provides the reading, so NO admitting parse is lost (`x<-c`
/// dispatches on `Ident`, not a rule-leading sigil ⇒ inert; `a,b<-c` is a
/// distinct polyadic rule ⇒ inert; a language with no sigil-sibling ⇒ inert =
/// baseline). Gate-miss only fails to suppress (fail-open). FV:
/// `AtQuotedBindGate.v` (T1 over-gen/non-Rholang, T2 no-legit-parse-lost,
/// T3 single-valued+scalar-arity, T4 linear-frontier, T5 kill-switch-identity,
/// T6 realize-backstop-inert-under-parse-gate).
///
/// When `false`, the gate folds to a literal `false` inside the suppression
/// conjunct, so the CrossCatLhs push guard is byte-identical to the pre-gate
/// emission (the `!(false && …) == true` fold). Flip to `false` to A/B off
/// without reverting.
///
/// ★ 2026-07-03 EMPIRICAL STATUS (session da0842dc): the parse-time (C) gate is
/// CORRECTNESS-COMPLETE and FV-backed (AtQuotedBindGate.v, zero-admission) —
/// flipping this to `true` collapses `@a<-@b`/`@a<=@b`/`@a<-@b!?(c)` from
/// alts=2 (over-generation) to alts=1 (the canonical scalar InputBindQuoted
/// family), provably inert for every legit bind (x<-c / (x)<-c / polyadic
/// a,b<-c all preserved), roundtrip-idempotent, ZERO regression (prattail
/// 3604/0, gen_rhocalc_unit 157/0, rhocalc_tests 383/0). BUT the design's
/// S0-G-LINEAR premise — that the `@` over-generation is the SOLE fork source,
/// so removing it linearizes the `@a<-@b & …` frontier — was REFUTED live:
/// gate-ON `branch_cursors_peak_pre_merge` still grows super-linearly
/// (k0=516, k1=44869, k2=485589 — vs ungated k0=674, k1=146011; a ~3.3×
/// constant-factor improvement but NOT linear; the flat control `x<-c` is
/// 74→103). Decomposition proved the residual is the `@`-NQuoteShort CROSS-CAT
/// PROJECTION frontier (`@a<-c` alone still explodes 63×/segment at alts=1) —
/// the pre-existing OPEN-ENDED ROOT-P sppf-continuation / visited_proj_descriptors
/// non-reconvergence (memory root-p-phase1-content-distinct: 100%
/// content-distinct derivations). The ~14 ROOT-P `<-` timeouts DO NOT clear
/// from this fix alone. Left OFF (byte-identical baseline) pending the user's
/// decision on whether the correctness-only win (evidence-based disambiguation
/// of `@a<-@b`, aligning RhoCalc with canonical Rholang) justifies enabling it
/// independently of the perf residual. Flip THIS + the walker-side
/// `AT_QUOTED_BIND_REALIZE_GATE` consts + `super::forks::AT_QUOTED_BIND_REALIZE_GATE`
/// together to enable.
pub(crate) const AT_QUOTED_BIND_GATE: bool = true;

/// AT_QUOTED_BIND_GATE realize-backstop (option B) codegen kill-switch
/// (2026-07-03). Gates emission of the two grammar-derived engine-impl helper
/// methods (`sigil_quoted_bind_overgen_rule` / `sigil_quoted_source_atom_rule`,
/// engine_impl.rs) that the walker's realize-time backstop consumes. MUST be
/// flipped in lock-step with the walker-side `AT_QUOTED_BIND_REALIZE_GATE`
/// const (wpda_walker.rs, in the realize loop): the walker const gates the
/// DROP; this const gates the METADATA the drop reads. When BOTH are `false`
/// (baseline) the generated engine impl is byte-identical (the trait defaults —
/// `false` — apply) and the walker never calls the helpers. Defense-in-depth,
/// INERT under the parse-time (C) gate. FV: `AtQuotedBindGate.{drop_set_sound,
/// realize_inert_under_parse_gate}`.
pub(crate) const AT_QUOTED_BIND_REALIZE_GATE: bool = true;

/// ROOT2_DRIVER_FALLTHROUGH — the facade single-result driver fall-through
/// (Direction A, 2026-07-04, session da0842dc). Kill-switch `const`
/// (compile-time, folds into the generated `parse_<Cat>_via_wpda_with_source`
/// body — the same convention as [`AT_QUOTED_BIND_GATE`] / [`FORROW_PROJ_GATE`]).
///
/// ## The defect it backstops (ROOT aa8ab54d)
/// The single-result facade `parse_<Cat>_via_wpda_with_source`
/// (wpda_codegen/facade.rs) drives the DEMAND EOI driver
/// (`run_to_end_of_input_until_accepting_env_aware`), which EARLY-STOPS the
/// moment a live *category-correct* accepting root exists
/// (`live_frontier_has_demand_resolvable_accept` checks category, NOT
/// realizability). For a surface like `(@a!!(Nil))` (an `@`-first send wrapped in
/// transparent Rholang display-parens `_parenthesized`) the demand driver stops
/// on a root whose SPPF realizes ZERO terms (all raw-probe caps `128..=1`), so
/// the M6 realize-select (`__mettail_wpda_select_min_weight_realizing`) returns
/// `None` and the facade unconditionally maps that to
/// `WpdaParseError::EmptyResult` ("WPDS produced no result"). The EXHAUSTIVE
/// driver (`run_to_end_of_input_env_aware`, used by the `_all` facades) explores
/// the alternatives and realizes the canonical send
/// (`PPersistOutputShort(a, Nil)` → Display `@a!!(Nil)`, parens transparent).
///
/// ## The fix
/// At the demand-path `Accepted` arm, replace the unconditional
/// `__mettail_wpda_select_min_weight_realizing(..).ok_or(EmptyResult)?` with a
/// `match`: `Some((term, dw))` ⇒ the VERBATIM current common path
/// (byte-identical); `None` ⇒ FALL THROUGH to a fresh-walker EXHAUSTIVE run +
/// re-resolve + M6 min-weight select (the factored helper
/// `__mettail_wpda_exhaustive_retry`, whose body is the EXACT
/// `AcceptedWithTrailing` retry — both arms call it). The common path is
/// BYTE-IDENTICAL: the `None` arm is reached IFF the demand M6-select returns
/// `None`, which is EXACTLY today's unconditional `EmptyResult`. The recovered
/// term is the global min-weight realizing root — the SAME canonical policy the
/// `_all` facades use (grounded concretely by Stage-0 S0-B roundtrip-idempotence,
/// not by the FV — the honest term-correctness split, like the M6 precedent).
///
/// ## Soundness (per feedback_use_wpds_disambiguation_not_heuristics)
/// This is a RESULT-LAYER backstop that BACKSTOPS (does not mask) the demand
/// driver's early-stop defect. It relaxes NO acceptance criterion: the
/// exhaustive re-run's realizable-root set ⊇ the demand run's, and a
/// genuine-invalid surface still yields `Err` (the exhaustive pass produces no
/// realizing root → `EmptyResult`, measured S0-A `(@a)` → still Err). It cannot
/// fabricate a parse for a non-parseable surface (T4). FV:
/// `FacadeDriverFallThrough.v` (T1 common_path_identity, T2
/// fallthrough_only_on_unrealizable, T3 fallthrough_picks_realizing_root, T4
/// no_spurious_parse, T5 output_is_realized_root, T6 refines_empty_result — the
/// make-or-break: pre=Ok ⟹ post=same Ok; pre=Err ⟹ post ∈ {Ok-realized | Err};
/// NEVER Ok→Err or Ok→different, T7 composes_with_m6_and_accepted_with_trailing).
///
/// ## Kill-switch
/// When `false`, the `Accepted` arm emits the PRE-EDIT
/// `.ok_or(WpdaParseError::EmptyResult)?` shape — byte-identical OFF (the
/// generated `parser.rs`/facade md5 == baseline). Runtime A/B: the env var
/// `PRATTAIL_NO_ROOT2_FALLTHROUGH` (mirrors `PRATTAIL_NO_M6_SELECT`) forces the
/// `None` arm to reproduce the `EmptyResult` error even when the const is `true`,
/// re-exposing the demand-driver defect for study without a rebuild.
///
/// ★ 2026-07-04 STAGE-0 (offline, session da0842dc): S0-A recovers
/// (`(@a!!(Nil))`→`@a!!(Nil)`, `(@a!(Nil))`→`@a!(Nil)`, full-ctx), S0-B
/// roundtrip-idempotent, S0-C leverage = 16 roundtrip-correct recoveries / 0
/// mishandled over the ROOT-2 corpus, S0-D 0 common-path fall-through entries.
/// Enabled (`true`).
pub(crate) const ROOT2_DRIVER_FALLTHROUGH: bool = true;

/// GRAMMAR_DERIVED_ISOLATION_CATEGORIES — increment P0 of the ROOT-P
/// generalization (2026-07-07). Master compile-time kill-switch selecting HOW the
/// three isolation families choose their result categories at the gates
/// [`super::facade::sep_isolation_shape`] / [`super::facade::projection_iso_shape`]
/// / [`super::facade::infix_iso_shape`]:
///
///   - `true` (SHIP DEFAULT, the ACTIVE generalization): use the GRAMMAR-DERIVED
///     eligibility predicate (`facade::eligible_family`) — a prefix-cohort /
///     list-element / infix-operand REACHABILITY analysis over the grammar IR,
///     with NO hardcoded category names. This is the real "not coupled to `@`"
///     selection: it isolates EXACTLY the categories that fork-explode (a ≥2
///     shared-prefix cohort whose operands nest back into the category), in ANY
///     language, present or future.
///   - `false` (kill-switch fallback): use the HARDCODED include lists
///     [`SEP_ISOLATION_CATEGORIES`] / [`PROJ_ISOLATION_CATEGORIES`] /
///     [`INFIX_ISOLATION_CATEGORIES`] — the pre-P0, rhocalc-name-coupled behavior.
///     Retained as a byte-identical-to-pre-P0 escape hatch.
///
/// ## Behavior-preserving refinement (NOT byte-identical — validated 2026-07-07)
/// The derived predicate is a PRINCIPLED REFINEMENT, not a byte-for-byte
/// reproduction, of the hardcoded lists. The hardcoded PROJ list is name-global
/// (`Name`/`Proc`/`InputBind`), so it incidentally isolated 5 non-rhocalc
/// languages' categories (Ambient/Class2Smoke `Proc`, Class3Multi/Class3Opt
/// `Name`, GuardedRho `Name`+`Proc`) whose shapes are SINGLETON-sigil / framed-list
/// / method-frame — i.e. do NOT fork-explode. The derived predicate correctly
/// EXCLUDES them (no ≥2 cohort), so it emits FEWER (redundant) isolation helpers
/// than the hardcoded lists for those 5 languages. This is EMPIRICALLY VALIDATED
/// BEHAVIOR-PRESERVING: the full test suites of all 5 languages + every control
/// (rhocalc 386/0, prattail 3606/0, gen_* , cross-lang roundtrips) pass IDENTICALLY
/// with the derived path ON vs OFF (422/0 affected, byte-diff of per-suite counts
/// empty). Isolation is a pure early-return fast-path; for a non-fork-exploding
/// shape the monolithic path already yields the same term, so dropping the helper
/// changes the ROUTE, not the RESULT. The behavioral gate is therefore the full
/// test suite (it runs against this default-ON path), NOT a codegen set-equality
/// assert — the earlier `debug_assert_eq!(derived, effective)` enforced a false
/// (byte-identity) invariant and was retired. `PRATTAIL_ISOLATION_ORACLE_DEBUG`
/// still prints the per-language derived-vs-effective sets for inspection.
///
/// ## Kill-switch / A-B
/// The codegen-time env override `PRATTAIL_GRAMMAR_DERIVED_ISOLATION=1|0` (read by
/// `facade::grammar_derived_isolation_enabled`) flips the path WITHOUT a source
/// edit; unset ⇒ this const. `0` restores the pre-P0 hardcoded-list emission.
pub(crate) const GRAMMAR_DERIVED_ISOLATION_CATEGORIES: bool = true;

/// SEP_ISOLATION_COMBINE — the ROOT-P `.*sep` DIVIDE-AND-CONQUER isolation+combine
/// facade fast-path (Plan a7986200, 2026-07-05, session da0842dc). Master
/// compile-time kill-switch (same convention as [`ROOT2_DRIVER_FALLTHROUGH`] /
/// [`AT_QUOTED_BIND_GATE`]): folds a guarded PROLOGUE into the generated
/// `parse_<Cat>_via_wpda_with_source` and
/// `parse_<Cat>_via_wpda_all_with_source_and_bounding_mode` facade bodies for
/// every category named in [`SEP_ISOLATION_CATEGORIES`].
///
/// ## The defect it ships the fix for (ROOT P)
/// A `.*sep` category (e.g. `ForRow` = `b "&" bs.*sep("&") ["where" cond]`) parsed
/// monolithically forks `dᵏ` cursor paths across the `k`-segment separator run —
/// the per-`&`-segment edge-stack blocks never reconverge the Tomita frontier, so
/// wall-time explodes EXPONENTIALLY in the segment count (Stage-0 measured mono
/// peak 84→629→1544→13047→123762 for k=0..4; the `forrow_display` roundtrip test
/// times out). Stage-0 (a7fc5b75) PROVED that parsing each `&`-separated segment in
/// a TRULY ISOLATED sub-parse (its own walker from ROOT) then COMBINING the
/// per-segment readings (cartesian product) is BOTH (a) exactly LINEAR
/// (Σ = 84·(k+1)) and (b) SOUND — the isolated+combined alt SET EXACTLY equals the
/// monolithic set for every shape incl the d=3 `@(Map()<@Nil!())<=a` (lost=0).
///
/// ## The fix (this feature)
/// Before each facade's `WpdaWalker::new_for_category`, a guarded prologue calls
/// the emitted per-category helper `__mettail_wpda_sep_isolate_all_<Cat>`. The
/// helper (i) engages ONLY on a LINEAR / lex-unambiguous token source (else falls
/// through), (ii) locates the list DOMAIN + optional suffix (`where cond`) via a
/// grammar-derived bracket-depth scan, (iii) splits the domain at depth-0
/// separators, (iv) sub-parses each element span through the ELEMENT category's
/// own `_all_with_source` facade (fresh `new_for_category`, edge-stack from ROOT —
/// NO cross-segment accumulation), (v) cartesian-combines the per-segment readings
/// into `Cat` terms via `__mettail_wpda_sep_ctor_<Cat>`, folding segment weights
/// with the ⊗ semiring product, and (vi) dedups by semantic key + ⊕-min-selects +
/// weight-sorts (mirroring the monolithic `_all` finalize). It returns
/// `Some((terms, weights))` on success, `None` for NOT-APPLICABLE or ANY sub-parse
/// failure — in which case the facade falls through to the UNMODIFIED monolithic
/// body (byte-identical; the monolithic path stays authoritative — RT-4).
///
/// ## Generality (no per-language / per-rule hardcode)
/// The shape is derived from the grammar IR (`GrammarRule.syntax_pattern`'s
/// `PatternOp::Sep` ⇔ the classifier's `MixfixRep`; the same classification the
/// walker uses — RT-1/7) and the SEPARATOR-LOCALITY soundness gate
/// (`separator ∉ infix-operators(element_category)`) is grammar-checked. Bracket
/// delimiters come from the language's collection delimiters + structural parens.
///
/// ## Kill-switch / A-B
/// When `false`, NO prologue and NO helper/ctor are emitted for ANY category —
/// byte-identical (every generated `wpda.rs` md5 == baseline). The per-category
/// include set [`SEP_ISOLATION_CATEGORIES`] gates WHICH categories opt in (EMPTY =
/// byte-identical even with the master switch `true`). The runtime env
/// `PRATTAIL_NO_SEP_ISOLATION` forces the emitted prologue to return early
/// (reproduces the monolithic path) WITHOUT a rebuild — the causal A/B control.
///
/// FV: `formal/rocq/prattail_wpda_runtime/theories/SepReconvergence.v` (T1
/// combine_equals_monolithic … T9 separator_locality_sound; model
/// `CollectionForkEvidence.v`; zero-admission).
pub(crate) const SEP_ISOLATION_COMBINE: bool = true;

/// Per-result-category INCLUDE set for [`SEP_ISOLATION_COMBINE`] (mirrors the
/// [`GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES`](super::infix) include/exclude
/// convention). A `.*sep` category is given the isolation+combine prologue +
/// helper + ctor ONLY when its name appears here AND [`SEP_ISOLATION_COMBINE`] is
/// `true` AND a `SepCombineShape` is derivable for it. EMPTY ⇒ byte-identical
/// (P1 plumbing checkpoint). `{"ForRow"}` at P3 (the DECISIVE `&`-join flip).
/// Expanded to every `.*sep` category at P4.
pub(crate) const SEP_ISOLATION_CATEGORIES: &[&str] = &["ForRow"];

/// SEP_ISOLATION_SINGLE_BARE — GROUP-A `<-@Nil!?(…)` fix (2026-07-06, session
/// da0842dc). Extends the bug-2318 single-element isolation from SUFFIX variants
/// (`ForRowWhere`→`ForRowSingleWhere`) to the BARE list variant
/// (`ForRowNoWhere`→`ForRowSingleNoWhere`), in the SINGLE-RESULT seam only.
///
/// ## The defect it ships the fix for
/// The MONOLITHIC ForRow WPDA parse FAILS to form the `InputBindEmptyQuery`
/// reading when the `!?`-query `args.*sep(",")` list holds an AMBIGUOUS
/// keyword-collection (`Set`/`Bag`/`List` — which ALSO lex as a bare `PVar`,
/// unlike the reserved `Map`/`Pathmap`) in a NON-LAST position FOLLOWED by a
/// SEND element, under the `ForRow`→`InputBind` `CrossCatProjection` frame: the
/// args collection-element dispatch grabs the bare-`PVar` reading of the keyword
/// and drops the `CastSet` reading, so the whole `InputBindEmptyQuery` cursor
/// dies and only `InputBindEmpty` (`<-n`) survives → the `!?` tail is stranded
/// (`TrailingTokens` at `!`). `InputBind::parse` (NO ForRow frame) forms both
/// readings correctly. Because `ForRowSingleNoWhere . b:InputBind |- b` is a
/// DEFINITIONAL projection, isolating the single `InputBind` and wrapping it is
/// == the monolithic result for every PASSING single-bind (Stage-0 S0-SOUND
/// 32/0, S0-ALL 32/0) and RECOVERS the failing ones. The single-result seam
/// engages it (line 709 `__single_winner &&`), so the ambiguity-preserving
/// `_all` alt-set stays byte-identical (declines single-element, unchanged).
///
/// ## Kill-switch / A-B
/// `false` ⇒ the bare variant is EXCLUDED from `single_allowed_vis` → a
/// single-element bare domain declines to the walker → generated code
/// byte-identical to the pre-fix (suffix-only) helper. Runtime env
/// `PRATTAIL_NO_SEP_SINGLE_BARE` forces the bare single-element path to decline
/// WITHOUT a rebuild (causal A/B), while keeping the suffix single-element
/// (bug-2318) path intact.
pub(crate) const SEP_ISOLATION_SINGLE_BARE: bool = true;

/// PROJ_ISOLATION_COMBINE — the `@`-PROJECTION DIVIDE-AND-CONQUER isolation+combine
/// facade fast-path (Plan a8b32275, 2026-07-05, session da0842dc). Master
/// compile-time kill-switch (same convention as [`SEP_ISOLATION_COMBINE`]): folds a
/// guarded PROLOGUE into the generated `Cat::parse_via_wpda` and
/// `Cat::parse_via_wpda_all_with_weights` string parse entries for every category
/// named in [`PROJ_ISOLATION_CATEGORIES`], BEFORE the sep-isolation prologue
/// (mutually-exclusive by input shape: a leading sigil `σ` vs a depth-0 separator
/// list).
///
/// ## The defect it ships the fix for (AXIS-@ — the exponential-killer)
/// An `@`-projection category (rules `σ [open] p:D [close] [tail] : C`, σ a
/// non-ident sigil, `p:D` a NESTED cross-cat operand — rhocalc `NQuote @(p)`,
/// `NQuoteShort @p`, `POutputShort @p!(q)`, `POutputNil @Nil!(q)`) parsed
/// MONOLITHICALLY re-enters the SAME walker for the inner `p` while the `@`-prefix
/// CrossCatLhs/Projection cohort accumulates on the edge-stack, so the frontier
/// forks `base-11` per nesting level — nested `@Nil!(@Nil!(…))` explodes
/// EXPONENTIALLY (Stage-0 measured mono peak 20→197→2241→26061 for d=1..4, base~11;
/// `proc_display` roundtrip times out). Stage-0 (a15ec630, re-confirmed this
/// session) PROVED that extracting the inner operand and parsing it in a TRULY
/// ISOLATED sub-parse (fresh `new_for_category(D)` from ROOT — NO CrossCatLhs
/// accumulation, inner base-2 not base-11) then WRAPPING each inner reading × the
/// matching frame-variant is BOTH (a) exactly LINEAR (Σ = leaf + d·frame, ratios
/// →1.0, 283× at d=4) AND (b) SOUND — the isolated+combined alt SET EXACTLY equals
/// the monolithic set incl the genuine `2^d` keyword-vs-freevar floor (raw==distinct
/// per level, combine peak BOUNDED at the constant frame, NOT the `11^d` frontier).
///
/// ## The fix (this feature)
/// Before each facade's `WpdaWalker::new_for_category`, a guarded prologue calls the
/// emitted per-category helper `__mettail_wpda_proj_isolate_all_<Cat>`. The helper
/// (i) matches each `σ`-led frame-variant's grammar-derived Literal/Param skeleton
/// against the RAW input via a bracket-depth scan, (ii) extracts each cross-cat
/// operand substring, (iii) sub-parses each through its OWN category's
/// `parse_via_wpda_all_with_weights` string entry (fresh walker from ROOT — which
/// RECURSES through this same prologue for deeper levels), (iv) cartesian-combines
/// the per-operand readings into `Cat` terms via the surface enum ctor, folding
/// operand weights with the ⊗ semiring product, and (v) dedups by semantic key +
/// ⊕-min-selects + weight-sorts (mirroring the monolithic `_all` finalize). It
/// returns `Some((terms, weights))` on success, `None` for NOT-APPLICABLE (no
/// leading sigil / no variant matches) or ANY sub-parse failure — in which case the
/// facade falls through to the UNMODIFIED monolithic body (byte-identical; the
/// monolithic path stays authoritative — RT-4).
///
/// ## Generality (no per-language / per-rule hardcode)
/// The shape is derived from the grammar IR (`GrammarRule.syntax_pattern`: a leading
/// `Literal(σ)` with `σ` NON-ident, plus `Param(p)` slots with `TypeExpr::Base(D)`) —
/// the SAME classification the walker uses. Bracket delimiters come from structural
/// parens + the language's collection delimiters.
///
/// ## Kill-switch / A-B
/// When `false`, NO prologue and NO helper is emitted for ANY category —
/// byte-identical (every generated `wpda.rs` md5 == baseline). The per-category
/// include set [`PROJ_ISOLATION_CATEGORIES`] gates WHICH categories opt in (EMPTY =
/// byte-identical even with the master switch `true` — the P1 plumbing checkpoint).
/// The runtime env `PRATTAIL_NO_PROJ_ISOLATION` forces the emitted prologue to
/// return early (reproduces the monolithic path) WITHOUT a rebuild — the causal A/B
/// control.
///
/// FV: `formal/rocq/prattail_wpda_runtime/theories/ProjectionIsolation.v` (T1
/// combine_equals_monolithic … T8 isolation_preserves_full_ambiguity … T10 composes;
/// model `SepReconvergence.v`; zero-admission).
pub(crate) const PROJ_ISOLATION_COMBINE: bool = true;

/// Per-result-category INCLUDE set for [`PROJ_ISOLATION_COMBINE`] (mirrors the
/// [`SEP_ISOLATION_CATEGORIES`] convention). An `@`-projection category is given the
/// isolation+combine prologue + helper ONLY when its name appears here AND
/// [`PROJ_ISOLATION_COMBINE`] is `true` AND a `ProjIsoShape` is derivable for it.
/// EMPTY ⇒ byte-identical (P1 plumbing checkpoint). `{"Name","Proc","InputBind"}`
/// at P4 (the DECISIVE `@`-nesting flip).
///
/// P0 (2026-07-07): dropped the inert `"ForRow"` entry — `ForRow` has NO
/// sigil-led projection rule and its `.*sep` list is owned by the dedicated sep
/// helper (`sep_owned`), so `derive_projection_iso_shape(ForRow)` is `None`;
/// listing it never emitted a projection helper. The drop is a behavioral no-op
/// (byte-identical) and makes this list equal the EFFECTIVE set the P0 oracle
/// compares the GRAMMAR-DERIVED predicate against.
pub(crate) const PROJ_ISOLATION_CATEGORIES: &[&str] = &["Name", "Proc", "InputBind"];

/// METHOD_FRAME_ISOLATION — extend the `@`-PROJECTION isolation (above) to the
/// RECEIVER-LED POSTFIX (method-call) frames (ROOT-D, session da0842dc,
/// 2026-07-06). Compile-time kill-switch (sibling of [`PROJ_ISOLATION_COMBINE`]);
/// OFF ⇒ [`derive_projection_iso_shape`] does NOT admit method frames ⇒ the
/// generated facade is BYTE-IDENTICAL to the pre-ROOT-D baseline.
///
/// ## The defect it ships the fix for (ROOT D)
/// A method rule (`m:Proc "." "get" "(" k:Proc ")"`, …) begins with an OPERAND
/// (the `m:Proc` receiver), not a sigil, and has NO `.*sep` list, so the proj-iso
/// eligibility (sigil-led ∨ framed-list) DECLINES it. A deep-`@` operand inside a
/// method-call arg (`Nil.concat(@Nil!(@Nil!(…)))`) then parses MONOLITHICALLY —
/// EXPONENTIAL (Stage-0 measured `Nil.concat(@^d Nil)` = 23→55→269→1568→7546→
/// 34666 ms for d=1..6, base~5), while the SAME `@`-nest parsed as an ISOLATED arg
/// is the linear proj-iso base-2 floor (2→5→10→21→45→86 ms). `proc_display` times
/// out at CASES=100.
///
/// ## The fix (this feature)
/// Admit a "receiver-led postfix frame" (slot 0 = Param, LAST slot = closing-
/// bracket Literal — excludes binary-infix which ends in a Param) as a projection
/// variant. Its LEADING receiver operand is matched GREEDY-LAST (the method `.` is
/// the unique rightmost depth-0 `.`; args are bracketed) so left-assoc method
/// CHAINS (`a.b().c()`) recover; its receiver is soundness-gated (a depth-0-
/// whitespace STRING pre-filter + an AST decline of binary-infix / prefix top-
/// ctors) so a low-precedence receiver (`Map() % @X` → `Mod`, `-Nil` → `NegProc`)
/// DECLINES the frame (falls to the monolithic body — sound; the method `.` binds
/// tighter than every infix and than `-`, so those are NOT the whole receiver).
/// Args + receiver are sub-parsed through the operand facade (RECURSES through the
/// proj-iso prologue ⇒ deep-`@` args linearize) and wrapped in the method ctor.
///
/// ## Generality
/// GRAMMAR-DERIVED, no per-language/per-rule hardcode: eligibility is the
/// slot-shape; the greedy-last flag is "slot0.category is left-recursive via the
/// slot1 literal" (∃ `cat <delim> … : cat`); the decline-set is "rules producing
/// the receiver category with syntax `[Param,Lit,Param]` or `[Lit,Param]`".
/// Calculator has no method rules ⇒ no method frames ⇒ byte-identical.
///
/// ## Kill-switch / A-B
/// `false` ⇒ no method variants for ANY category ⇒ byte-identical. The runtime env
/// `PRATTAIL_NO_METHOD_ISOLATION` makes the emitted method-variant arms return
/// early WITHOUT a rebuild — the causal A/B control.
///
/// FV: `formal/rocq/prattail_wpda_runtime/theories/MethodFrameIsolation.v`
/// (combine_equals_monolithic … receiver_gate_declines_nonprimary; zero-admission).
pub(crate) const METHOD_FRAME_ISOLATION: bool = true;

/// PROJ_ISO_LITERAL_RUN_ANCHOR — the InputBind query-frame `@@`-CHANNEL fix
/// (session da0842dc, 2026-07-06). Compile-time kill-switch (sibling of
/// [`METHOD_FRAME_ISOLATION`] / [`PROJ_ISOLATION_COMBINE`]); OFF ⇒ the emitted
/// `__proj_skeleton_match` matcher ([`super::facade::emit_projection_isolation`])
/// is BYTE-IDENTICAL to the pre-fix single-next-literal boundary.
///
/// ## The defect it ships the fix for (the last on-path `forrow_display` residual)
/// The `@`-PROJECTION / framed-list isolation matcher delimits each cross-cat
/// OPERAND by the FIRST depth-0 occurrence of the SINGLE next fixed literal. For a
/// query bind whose CHANNEL is itself a quoted SEND — the rule
/// `InputBindEmptyQuery . n:Name, args:Vec(Proc) |- "<-" n "!" "?" "(" args.*sep(",") ")"`
/// on the surface `<-@@Nil!()!?(true, Pathmap() <= @Nil!!())` — the channel operand
/// `@@Nil!()` (a VALID Name = `NQuoteShort(POutputNilEmpty)`) CONTAINS a depth-0 `!`
/// from its OWN send `!()`. The post-channel delimiter literal is `!` (the first
/// char of the query run `! ? (`), so the greedy-first depth-0 scan matches the
/// channel-INTERNAL `!` (pos 7) BEFORE the query `!` (pos 10); the very-next literal
/// `?` then mismatches the channel's `(` ⇒ the matcher returns `None` ⇒ the helper
/// declines ⇒ the facade falls through to the monolithic body, which ALSO cannot
/// form the reading for the complex multi-arg query (0 alts) ⇒ `InputBind::parse` /
/// `ForRow::parse` return `Err`. Each piece parses in isolation
/// (`Name::parse("@@Nil!()")` OK, each `Proc::parse(arg)` OK); ONLY the frame match
/// at the InputBind level fails. This is the SAME divide-and-conquer isolation locus
/// as the polyadic-send / method-arg framing, applied to the InputBind query rules;
/// the gap is the MATCHER, not the shape (the three query variants are already
/// derived + emitted as framed-list projection variants — verified in the emitted
/// helper).
///
/// ## The fix (this feature)
/// Anchor each operand's RIGHT boundary on the MAXIMAL consecutive LITERAL RUN after
/// its `Op` slot (all `Lit` slots up to the next `Op`), not just the single next
/// literal: accept a depth-0 delimiter position ONLY when the WHOLE run
/// (whitespace-flexible, same word-boundary rule as the main Lit arm — via the
/// emitted `__match_lit_run`) matches there. The channel's internal `!` is followed
/// by `(`, not the query run `! ? (`, so it is skipped; the run `!?(` matches only
/// at the genuine query frame ⇒ the channel operand recovers as `@@Nil!()` and the
/// args region as `true, Pathmap() <= @Nil!!()` (both then sub-parse + combine).
///
/// ## Soundness (strict monotone improvement — measured, pure-logic Stage-0a)
/// The run is GRAMMAR-DERIVED (the skeleton's fixed literals, which the grammar
/// REQUIRES consecutively after the operand), so the TRUE operand boundary ALWAYS
/// has the full run matching there — anchoring on it never SKIPS the true boundary.
/// It only removes SPURIOUS early splits (a position where the first literal matches
/// but the rest of the run does not — where the pre-fix matcher then mismatched the
/// next literal and returned `None`). So per operand the anchored scan is a strict
/// refinement of the boundary set: where the pre-fix matcher returned `Some(ranges)`
/// it returns the IDENTICAL ranges (the true boundary has the full run; any earlier
/// full-run match would have been taken by BOTH — greedy-first); where it returned
/// `None` from a false-early split it now returns the correct `Some`. Pure-logic
/// Stage-0a confirmed: OLD `None` / NEW correct for every `@@`-channel query surface;
/// OLD == NEW (byte-identical ranges) for every passing form (`<-a!?(x)`,
/// `<-@Nil!?(Set(),@Nil!!())`, method frames `.get(`/`.keys(`). The query run `!?(`
/// is UNIQUE to the query at the Name/Proc level (no `!?(` production), so no false
/// frame match. FV:
/// `formal/rocq/prattail_wpda_runtime/theories/ProjectionIsolation.v`
/// (`literal_run_anchor_*`: anchored-boundary ⊆ single-literal boundary set,
/// true-boundary preserved, none→some-only; zero-admission).
///
/// ## Kill-switch / A-B
/// `false` ⇒ NO `__match_lit_run` helper, NO env read, the pre-fix `if wb { … }`
/// single-literal boundary ⇒ BYTE-IDENTICAL (every generated `wpda.rs` md5 ==
/// baseline). Runtime env `PRATTAIL_NO_PROJ_RUN_ANCHOR` reproduces the single-
/// literal boundary WITHOUT a rebuild (causal A/B — reproduces the pre-fix decline).
pub(crate) const PROJ_ISO_LITERAL_RUN_ANCHOR: bool = true;

/// PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM — the ROOT-P nested-send fix (Fix A, P1,
/// 2026-07-07). The `__proj_skeleton_match` matcher delimits each cross-cat operand
/// at the NEXT depth-0 occurrence of the following literal δ, committed GREEDY-FIRST.
/// That is WRONG when the operand's OWN category can itself PRODUCE δ at depth 0:
/// e.g. the send-sugar receiver `p` in `@ p ! ( … )` (rhocalc `POutputShort2Plus`),
/// where δ = `!` and `p : Proc` is ITSELF a send (`@Nil!(…)`) carrying its own
/// depth-0 `!(`. Greedy-first splits `p = @Nil`, strands the outer `!(args)`, the
/// whole-input check fails, EVERY `@`-send variant declines, the helper falls to the
/// monolithic path — which fork-explodes on nested `@` (the ROOT-P residual:
/// `@@@Nil!(…)!(…) <- a` timed the display roundtrip out at ~8.5 s / "no accepting
/// branch"). The parser is full-GLR (monolithic ⊇ any operand tiling), so the fix is
/// DIVIDE-AND-CONQUER ENUMERATION: at an AMBIGUOUS-δ operand slot (k ≥ 1) enumerate
/// ALL run-anchor-passing depth-0 δ boundaries, sub-parse each candidate assignment
/// in isolation, and keep those that consume the whole input and parse — the
/// ambiguity-preserving union (ALL seam) / min-weight (SINGLE seam). GRAMMAR-DERIVED,
/// NOT `@`-coupled: a slot's δ is "ambiguous" iff δ is producible at depth 0 in the
/// operand category (`category_produces_delim_at_depth0` — transitive over depth-0
/// operands); δ = `<-`/`!?(`/`where` are NOT depth-0-producible in a Proc so those
/// slots keep the single greedy boundary. Generalizes the ROOT-D method greedy-last
/// (k == 0, NOT enumerated — retains greedy-last; sigil-send receivers sit at k = 1,
/// method receivers at k = 0, disjoint).
///
/// ## Kill-switch / A-B
/// `false` ⇒ the codegen emits the pre-P1 single-assignment matcher + variant arm
/// VERBATIM ⇒ BYTE-IDENTICAL (every generated `wpda.rs` md5 == the pre-P1 baseline).
/// `true` (SHIP DEFAULT — this IS the fix) ⇒ the enumerating matcher + per-assignment
/// arm loop. Runtime env `PRATTAIL_NO_PROJ_BOUNDARY_ENUM` forces the single-boundary
/// behavior WITHOUT a rebuild (causal A/B — reproduces the pre-fix decline/explosion).
/// Requires `PROJ_ISO_LITERAL_RUN_ANCHOR` ON (enumeration ranges only over
/// run-anchor-passing positions, so a `!` inside a `!!`-persistent send is never a
/// candidate).
pub(crate) const PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM: bool = true;

/// PROJ_ISO_BESTPARSE_MEMO — the ROOT-P MEMOIZED BEST-PARSE fix (design af7680e2,
/// "3A LIGHT"), layered ON TOP of the [`PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM`]
/// enumerating matcher (P1). Compile-time kill-switch (same convention as
/// [`PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM`] / [`PROJ_ISOLATION_COMBINE`]).
///
/// ## The defect it ships the fix for (the P1 seed-timeout residual)
/// P1's enumerating matcher greens the ROOT-P nested-send counterexample and the
/// inputbind/proc/forrow display roundtrips at CASES=100, but
/// `name_display_parse_roundtrip` TIMES OUT on some proptest seeds. Root cause:
/// enumerate-all's recursive sub-parses re-parse OVERLAPPING `(category, span)`
/// subproblems. At each `@`-projection / framed-list level the matcher enumerates
/// every run-anchor-passing depth-0 boundary assignment (O(n) tilings — a send has
/// ≤1 ambiguous operand slot, so the per-LEVEL enum is linear), sub-parses each
/// candidate operand span IN ISOLATION, and keeps the whole-input-consuming ones.
/// Because a nested operand of depth `d` is re-visited by every enclosing tiling,
/// the recursion is an exponential TREE — `O(n^{m·d})`, `m` = operands/level, `d` =
/// nesting depth. The per-level tiling is fine; it is the un-shared RE-descent that
/// explodes.
///
/// ## The fix
/// MEMOIZE the per-category STRING entry `Cat::parse_via_wpda(input) ->
/// Result<Cat, ParseError>` on the key = TRIMMED span CONTENT (`String`), in a
/// per-category thread-local map, EPOCH-SCOPED to the OUTERMOST parse (the RAII
/// `__ProjMemoGuard`; see [`super::facade::emit_proj_memo_preamble`]). Every operand
/// is parsed from a freshly-trimmed ISOLATED substring taken from ROOT (the bug-2318
/// locality), so `parse_via_wpda(cat, trimmed-content)` is a PURE function of
/// `(cat, trimmed-content)` — memoizing returns the IDENTICAL value; only WHEN
/// sub-parses run changes, never WHAT. This collapses the recursion TREE into a
/// polynomial DAG (each distinct `(category, trimmed-span)` sub-parse runs once per
/// outermost parse), so the SELECTED single winner is BYTE-IDENTICAL to the pre-memo
/// (P1) enumerate-all winner while depth scaling becomes polynomial. Failure (`Err`)
/// results are memoized too (required for polynomiality — a non-parsing span fails
/// identically every visit). Mirrors `runtime/src/binding.rs` BCG05_EPOCH /
/// clear_var_cache.
///
/// ## Scope — ONLY the single-winner seam
/// The memo wraps ONLY the single-result `parse_via_wpda`. The ambiguity-preserving
/// `parse_via_wpda_all` / `parse_via_wpda_all_with_weights` (a genuine `2^d` SET, off
/// the roundtrip path) are NOT memoized — they stay byte-identical and disjoint from
/// the memo. Only ISOLATION-ELIGIBLE categories (`projection_iso_shape` ∨
/// `sep_isolation_shape` ∨ `infix_iso_shape` is `Some` — the categories whose
/// `parse_via_wpda` recurses through the divide-and-conquer prologues) get the memo
/// wrapper; every other category keeps the plain body (byte-identical).
///
/// ## Kill-switch / A-B
/// `false` ⇒ NO memo preamble, NO per-category memo map, and the `parse_via_wpda`
/// body is emitted VERBATIM (no `parse_via_wpda_uncached` split) ⇒ BYTE-IDENTICAL
/// (every generated `wpda.rs`/`parser.rs` md5 == the pre-memo baseline). `true`
/// (SHIP DEFAULT — this IS the fix) ⇒ the memo wrapper + `parse_via_wpda_uncached`
/// for iso-eligible categories + the shared thread-local preamble. The runtime env
/// `PRATTAIL_NO_PROJ_MEMO` (read once per OUTERMOST parse, at `__ProjMemoGuard::enter`
/// when depth 0 → 1 — the isolation path is non-hot) BYPASSES the memo WITHOUT a
/// rebuild (causal A/B — reproduces the pre-memo exponential recursion for
/// study / drift verification).
pub(crate) const PROJ_ISO_BESTPARSE_MEMO: bool = true;

/// PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT — the ROOT-1 deep-`@` polynomiality fix
/// (design a9fbeefe, 2026-07-07). Layered ON TOP of the P1 enumerating matcher
/// ([`PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM`]) + the memo ([`PROJ_ISO_BESTPARSE_MEMO`]).
/// Compile-time kill-switch (same convention as its two predecessors).
///
/// ## The defect it ships the fix for (the ROOT-1 exponential residual)
/// The receiver-nested send ladder `@^d Nil (!(0))^d` parses EXPONENTIALLY
/// (measured d4≈856 ms, d5≈8 s, d6≈67 s, base≈8), even with P1 + memo ON. The
/// chain IS already correctly tiled by P1; the blow-up is the GLR WALKER running
/// on genuinely-UNPARSEABLE, UNBALANCED `@`-led send spans reached via the
/// `POutputQuoted` (`@ n ! ( q )`, `n : Name`) → `NQuoteShort` (`@ Op`, peels one
/// `@`) name-receiver detour: the receiver sub-parse of a nested send strands an
/// unbalanced span (e.g. `@@Nil!(0)!(0)!(0)` — 2 `@`, 3 sends) that is NOT a Proc.
/// The proj helper CORRECTLY declines it (every tiling's operand sub-parse `Err`s
/// ⇒ `__candidates` empty), but the bare `return None` at the decline falls to
/// `parse_via_wpda_uncached`'s WPDA walker, which fork-explodes ≈`8^d` PROVING the
/// span non-parseable. perf: ≈100 % walker, helper/matcher/memo ≈0 %. The memo
/// cannot help — the expensive walker call is a single atomic unit and the spans
/// are unique. GROUND TRUTH (measured): a bare `@`-led string can ONLY be a send
/// (`POutput*`) or an infix-combination of sends — there is NO `Name → Proc`
/// coercion (the only `@`-adjacent Name reading is `PDrop . "*" n : Proc`, which is
/// STAR-led, not `@`-led), so an `@`-led span whose every send-tiling fails is
/// provably not a Proc.
///
/// ## The fix
/// Make the projection helper AUTHORITATIVE for sigil-led send frames. When the
/// helper MATCHED a whole-input sigil-led send skeleton (a `sigil_led` variant's
/// `__proj_skeleton_match_all` returned a non-empty tiling set — `__sigil_frame_matched`)
/// but EVERY tiling's operand sub-parse failed (`__candidates` empty) AND no
/// materialization cap fired (`!__cap_hit` — enumeration was COMPLETE) AND the
/// (trimmed, non-empty) input starts with a projection sigil, SIGNAL A DEFINITIVE
/// REJECT (a thread-local `__PROJ_SIGIL_REJECT` the prologue reads → `Err`) instead
/// of the bare `return None` that falls to the fork-exploding walker. SOUND because
/// an `@`-led string is a send or an infix-combination of sends, and the infix
/// isolation prologue runs AFTER proj in `parse_via_wpda_uncached` — so the reject
/// fires ONLY when BOTH proj AND infix decline (`@Nil!(0) or @Nil!(0)`, an
/// infix-of-sends, is recovered by the infix prologue and never reaches the reject).
/// Combined with P1 + memo, the recursion now bottoms out at the small non-`@`-led
/// leaf `Nil!(0)` (the walker never runs on a span whose size grows with `d`) ⇒
/// the ladder is O(d³) POLYNOMIAL.
///
/// ## Scope — ONLY the single-winner seam
/// The reject is signalled ONLY when the helper is called with `__single_winner`
/// (the `parse_via_wpda` / `parse_via_wpda_uncached` seam). The ambiguity-preserving
/// `parse_via_wpda_all` / `parse_via_wpda_all_with_weights` (ALL seam, g3 alt-counts)
/// are left UNTOUCHED — byte-identical. The cap-hit path stays `None` → walker
/// (never `Err`): a cap means enumeration was INCOMPLETE, so a valid parse might be
/// hidden and rejecting would be unsound.
///
/// ## Kill-switch / A-B
/// `false` ⇒ NO `__sigil_frame_matched` / `__cap_hit` locals, NO reject preamble,
/// NO prologue capture/fire, and the decline site + cap sites are emitted VERBATIM
/// (bare `return None` / `break '__variant`) ⇒ BYTE-IDENTICAL (every generated
/// `wpda.rs` md5 == the pre-fix baseline). `true` (SHIP DEFAULT — this IS the fix)
/// ⇒ the authoritative-reject machinery. The runtime env
/// `PRATTAIL_NO_PROJ_AUTHORITATIVE_REJECT` (read at the decline site) suppresses the
/// reject WITHOUT a rebuild (causal A/B — reproduces the pre-fix `None` → walker
/// explosion for study / drift verification). Requires
/// [`PROJ_ISO_AMBIGUOUS_BOUNDARY_ENUM`] ON (`__sigil_frame_matched` is set from the
/// enumerating matcher's `__assignments`).
// ## Completeness fix (2026-07-07, ENABLED) — reject fires ONLY on complete-
// enumeration-all-genuinely-failed
// The reject's soundness precondition is "the helper declined ⟹ the span is
// genuinely unparseable". A helper decline for a STRUCTURAL / INCOMPLETENESS reason
// (an empty operand/region/element segment, a receiver ws/AST gate, a materialization
// cap, a debug A/B knob) VIOLATES that precondition — the walker/grammar may still
// accept the span. Canonical break: an `@`-led send with a TRAILING COMMA in its args
// (`@Nil!(0,)`) — the grammar's `args.*sep(",")` ACCEPTS a trailing separator, but the
// SepList element split of `"0,"` yields `["0",""]` and the empty trailing segment
// declined (`break '__variant`), which the pre-fix reject wrongly escalated to `Err`
// (an Ok→Err FLIP; proptest `proc`/`inputbind` `_display_parse_roundtrip` regress).
// FIX: every STRUCTURAL decline site in `emit_proj_variant_arm` now sets `__cap_hit`
// (the same "enumeration incomplete" flag the materialization caps use), so the reject
// (`!__cap_hit`) never fires on a structural bail — it falls to the walker (the
// authoritative/complete parser, which handles trailing commas etc.). The ONLY decline
// that permits the reject is a σ-led send skeleton that matched every tiling and whose
// every operand's `parse_via_wpda` sub-parse returned a genuine `Err` (the walker's own
// verdict). Fail-safe: when in doubt, mark incomplete (don't reject ⇒ fall to walker ⇒
// correct-but-slow, never a false `Err`). Gate A (polynomiality) is preserved — the
// pathological `@^d Nil (!(0))^d` spans have NO trailing comma / empty segment, so
// every tiling routes through the genuine-`Err` operand decline (UNMARKED) and the
// reject still fires. Verified: Gate B′ (no Ok→Err drift incl. trailing-comma) + the
// `proc_/inputbind_/name_/forrow_display_parse_roundtrip` completeness fuzz
// (PROPTEST_CASES=300 × ≥5 seeds, all PASS).
pub(crate) const PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT: bool = true;

/// RECOGNIZER_PREFILTER — the ROOT-P structural-decline fast-reject FALLBACK
/// (non-parseability recognizer oracle a166789b, wired 2026-07-07). The SIBLING
/// fail-safe of [`PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT`]. Compile-time kill-switch
/// (same convention as its predecessors).
///
/// ## The defect it ships the fix for (the ROOT-P structural-decline residual)
/// The authoritative-reject fast-rejects the CLEAN σ-led-send residual (a σ-frame
/// skeleton matched the whole input, enumeration was COMPLETE, and EVERY tiling's
/// operand sub-parse genuinely `Err`ed) in poly time — Gate A. But it FAILS SAFE:
/// on a STRUCTURAL decline (`__cap_hit` — a trailing separator like `@Nil!(0,)`,
/// an empty segment, or a materialization cap marked the enumeration INCOMPLETE,
/// so the reject cannot SOUNDLY fire) it falls through to the walker. When such a
/// residual σ-led span is GENUINELY non-parseable, the GLR walker still explores
/// ≈`8^d` before failing. The display proptests
/// `{proc,name,inputbind,forrow}_display_parse_roundtrip` TIME OUT at high
/// `PROPTEST_CASES` because a VALID top-level term's receiver-detour sub-parse
/// (`@ n ! ( q )` → `NQuoteShort`) strands exactly such a span.
///
/// ## The fix
/// Wire the already-VALIDATED non-parseability RECOGNIZER
/// (`WpdaWalker::recognize_reachable`, a166789b — a one-sided REJECT-only oracle:
/// coarse GLL-Slot cursor merge + Tomita pop fan-out ⇒ a SOUND over-approximation
/// of the real walker's reachability whose frontier stays POLYNOMIAL even where
/// the full parse is exponential) as that fail-safe's FALLBACK. At the STRING-entry
/// `parse_via_wpda` fall-through point — AFTER the proj/sep/infix isolation
/// prologues AND the authoritative-reject have all DECLINED to reject, i.e. exactly
/// where a known-hard σ-led span is about to hit the walker — run the recognizer on
/// the SAME token source the guarded walker path uses (`LatticeTokenSource` when
/// `lex_dag(input)` is ambiguous, else the `SliceTokenSource` kinds/texts shape).
/// `false` ⇒ the span is DEFINITIVELY non-parseable ⇒ return the parse `Err` in
/// poly time (the exponential walker is never reached). `true` / inconclusive
/// (max-steps) ⇒ proceed to the existing walker path UNCHANGED.
///
/// ## Scope — the σ-led hard cases only (NOT every parse; no ~2× on easy parses)
/// Emitted ONLY for a category with a derivable `@`-projection shape
/// (`projection_iso_shape(..).is_some()`) that admits ≥1 σ-led variant, and gated
/// at RUNTIME on the trimmed input starting with one of that category's
/// grammar-derived projection sigils (`sigil_lead_bytes` — `@`/`*`/`-`/`(` … — the
/// SAME set the authoritative-reject's `starts_with_sigil` uses). Non-σ-led inputs
/// (the common easy parse: `Nil`, `x!(5)`, a number, `for(..)`) SKIP the recognizer
/// entirely. σ-led spans that were PARSEABLE are handled by the isolation prologues
/// and return BEFORE the fall-through, so only σ-led spans that ALREADY FAILED
/// isolation (all genuinely hard) reach the recognizer — where the walker was about
/// to explode, so the poly recognizer is a strict win, not a 2× tax.
///
/// ## Soundness — REJECT-only, never a parse-reading heuristic
/// The recognizer NEVER drops or elects a parse reading. It acts ONLY on a
/// DEFINITIVE `Unreachable` (`false`); ANY doubt — `true`, max-steps inconclusive,
/// a `lex`/`lex_dag` failure, or the env A/B being set — falls through to the
/// walker (correct-but-slow, never a false `Err`). Because isolation has already
/// declined at the hook, the ONLY remaining acceptance path IS the walker, and the
/// recognizer soundly over-approximates the walker ⇒ `false` ⇒ the walker would
/// also reject (just exponentially slower).
///
/// ## Kill-switch / A-B
/// `false` (SHIP DEFAULT until STAGE 2 confirms the win) ⇒ NO
/// `recognize_<Cat>_reachable_ws` facade fn, NO pre-pass fragment in the
/// `parse_via_wpda` body ⇒ every generated `wpda.rs` is BYTE-IDENTICAL to the
/// pre-wiring baseline. `true` ⇒ the recognizer pre-pass machinery. The runtime env
/// `PRATTAIL_NO_RECOGNIZER_PREFILTER` (read at the fall-through hook) suppresses the
/// pre-pass WITHOUT a rebuild (causal A/B — reproduces the pre-fix walker explosion
/// for study). Independent of [`PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT`] (they cover
/// DISJOINT σ-led subsets: the reject the clean-all-fail set, the recognizer the
/// structural-decline residual) but shares its `projection_iso_shape` /
/// `sigil_lead_bytes` grammar-derived gates.
///
/// ## STAGE-2 RESULT (2026-07-08) — SHIPS OFF pending a narrow-gate refinement
/// The wiring is COMPLETE and CORRECT (verified: emits nothing OFF ⇒ generated
/// `wpda.rs` byte-identical; ON emits the `recognize_<Cat>_reachable_ws` facade fn
/// + the `parse_via_wpda` fall-through fragment for `Proc`/`Name`/`InputBind`), and
/// the recognizer DOES deliver its intended win where it applies:
///   • `proc_display_parse_roundtrip` @ PROPTEST_CASES=64: baseline STACK OVERFLOW
///     (9.8 s) → PASS (13.3 s) — the exploding σ-led spans fast-reject (`false` in
///     ≈10 ms) before the walker recurses to overflow.
///   • `name_display_parse_roundtrip`: 22.2 s → 9.4 s.
/// BUT the current SHIP-DEFAULT wiring (this const ON + the BROAD σ-led gate + the
/// natural `max_steps` = 1M) REGRESSES badly, because `recognize_reachable`'s coarse
/// frontier does NOT converge on some SMALL, PARSEABLE σ-led spans (empirically: a
/// 4-token rhocalc `Proc`): it neither empties nor accepts, and grinds to `max_steps`
/// (≈0.4 ms/step ⇒ tens of seconds at 1M). The broad gate invokes the recognizer on
/// EVERY σ-led fall-through — including those non-convergent parseable spans — so a
/// single one hangs the parse (proc @ CASES=1: 2.4 s → >90 s). A bounded budget
/// (`PRATTAIL_RECOGNIZER_MAX_STEPS=300`) makes the non-convergent calls bail fast and
/// restores the win (proc→PASS 13.3 s), but 300 is a GRAMMAR-TUNED magic number that
/// trades reject-completeness against latency — a band-aid, not a principled fix.
/// (`inputbind_display_parse_roundtrip` STACK-OVERFLOWS in BOTH baseline and ON with
/// 0 recognizer rejects — the separate cast-tower recursion the recognizer does not
/// target; out-of-scope, pre-existing, NOT a regression.)
///
/// ROOT CAUSE = a recognizer-MECHANISM non-convergence (`prattail/src/wpda_walker.rs`
/// `recognizer_mode`, OUT OF SCOPE here — actively under FV development, HEAD "recognizer
/// pop fan-out soundness"). The PRINCIPLED WIRING FIX is a NARROW gate: invoke the
/// recognizer ONLY on the structural-decline residual (the σ-frame-matched-but-not-
/// authoritatively-rejected spans where the walker actually explodes), NOT every σ-led
/// fall-through — that decouples latency from `max_steps` (few calls ⇒ a large,
/// reject-complete budget is affordable) and skips the non-convergent parseable spans
/// entirely. That needs a Plan-agent design + empirical confirmation it selects the
/// exploding spans, and coordination with the in-flight recognizer convergence work.
/// Until then this ships OFF (byte-identical, zero-regression); flip ON only WITH the
/// narrow gate (and/or once the frontier converges).
pub(crate) const RECOGNIZER_PREFILTER: bool = false;

/// RECOGNIZER_REJECT_GATE — the SOUND GATE on the authoritative-reject
/// (non-parseability recognizer oracle a166789b, wired 2026-07-08). This is the
/// PRINCIPLED narrow-gate refinement the STAGE-2 result of [`RECOGNIZER_PREFILTER`]
/// called for — but applied at a DIFFERENT (and inherently narrow) hook: the
/// authoritative-reject FIRE site, not the every-σ-led fall-through.
///
/// ## The defect it ships the fix for (the auth-reject FALSE-REJECT)
/// [`PROJ_ISO_SIGIL_AUTHORITATIVE_REJECT`] fires whenever a σ-led send skeleton
/// matched the WHOLE input, enumeration was COMPLETE (`!__cap_hit`), the trimmed
/// input starts with a projection sigil, and NO tiling parsed — the module
/// thread-local `__proj_sigil_reject` flag is set, and the `parse_via_wpda`
/// prologue turns it into `Err`. That heuristic is UNSOUND: a valid NON-send
/// `@`-quoted bind whose subject looks like a send frame is FALSE-REJECTED. Proven
/// counterexamples (with `PRATTAIL_NO_PROJ_AUTHORITATIVE_REJECT=1` both parse):
///   • `@([]) <= @(Map())` → the valid `InputBind` `@[] <= @(Map())`
///   • `@([]) <- x`        → the valid `InputBind` `@[] <- x`
/// `@([])` is a valid quoted-list `Name`, not a malformed send. The reject fires
/// because the σ-frame matcher matches `@( … )` over the whole input, every tiling
/// declines (it is not a send), and the crude heuristic concludes "unparseable".
///
/// ## The fix — GATE the reject with the SOUND recognizer
/// At the `proj_reject_fire` site (the SINGLE place `__proj_sigil_reject` becomes
/// `Err`), fire the authoritative-reject ONLY IF the non-parseability recognizer
/// (`WpdaWalker::recognize_reachable`, a166789b — a one-sided REJECT-only oracle:
/// coarse GLL-Slot cursor merge + Tomita pop fan-out ⇒ a SOUND over-approximation
/// of the real walker whose frontier stays POLYNOMIAL even where the full parse is
/// exponential) CONFIRMS the span is `Unreachable` (returns `false`). If the
/// recognizer says `Reachable` (`true`), grinds to the step budget (`true`), or the
/// input fails to lex (inconclusive), SUPPRESS the reject and fall through to the
/// full walker UNCHANGED. This makes the crude auth-reject SOUND: it now rejects
/// ONLY recognizer-confirmed-`Unreachable` spans.
///   • Parseable `@([])` bind ⇒ recognizer `Reachable` (or budget ⇒ `true`) ⇒
///     reject SUPPRESSED ⇒ the walker parses it correctly. FIXES the false-reject.
///   • Genuinely-unparseable deep-`@` (`@Nil!(true false)`, `@@@Nil!(0`) ⇒
///     recognizer converges `Unreachable` FAST (poly) ⇒ reject FIRES ⇒ fast reject.
///     Delivers the ROOT-P perf (never reaches the exponential fail-safe walker).
///
/// ## Why the narrow gate is inherently safe (vs the broad prefilter)
/// The recognizer runs ONLY when `__proj_sigil_reject` is already set — the σ-frame-
/// matched clean-decline set, a NARROW residual (NOT every σ-led parse). So the
/// STAGE-2 non-convergence (coarse frontier grinding to `max_steps` on some SMALL
/// PARSEABLE σ-led spans) costs at most a BOUNDED latency (`RECOGNIZER_GATE_MAX_STEPS`)
/// on those rare reject-candidate spans — which fall through to the full walker
/// ANYWAY. That bounded budget IS the natural one-sided-oracle semantics (budget ⇒
/// inconclusive ⇒ `true` ⇒ suppress), not a band-aid. All non-reject-candidate
/// parses NEVER touch the recognizer ⇒ no ~2× regression.
///
/// ## Soundness — REJECT-only, never a parse-reading heuristic
/// The recognizer NEVER drops or elects a reading. The reject fires ONLY on a
/// DEFINITIVE `Unreachable` (`false`); ANY doubt (`true`, max-steps, a lex failure,
/// or the env A/B set) SUPPRESSES the reject and falls through to the walker
/// (correct-but-slow, never a false `Err`). Because the walker soundly under-lies
/// the recognizer (fan-out ⊇ SlotEdge ⊇ true-parser), a recognizer `false` means the
/// walker would ALSO reject (just exponentially slower) ⇒ the reject is SOUND.
///
/// ## Kill-switch / A-B
/// `true` (SHIP DEFAULT — it FIXES a correctness bug, so on-by-default is warranted,
/// unlike the perf-only [`RECOGNIZER_PREFILTER`]) ⇒ the `proj_reject_fire` site emits
/// the recognizer-gated fire + the `recognize_<Cat>_reachable_ws` facade fn is emitted
/// (shared with the prefilter's emission gate). `false` ⇒ the `proj_reject_fire` site
/// emits the VERBATIM unconditional reject + (with [`RECOGNIZER_PREFILTER`] also OFF)
/// NO facade fn ⇒ every generated `wpda.rs`/`parser.rs` is BYTE-IDENTICAL to the
/// pre-gate baseline. The runtime env `PRATTAIL_NO_RECOGNIZER_REJECT_GATE` (read at
/// the fire site) reverts to the unconditional reject WITHOUT a rebuild (causal A/B —
/// reproduces the pre-fix false-reject for study).
///
/// ⚠ SHIPPED OFF (2026-07-08, reverted from `true`): although the gate fixes the
/// `@([])` false-reject (a real correctness win), a CASES=64 A/B proved it
/// SEVERELY regresses perf — `gen_rhocalc_prop::proc_display_parse_roundtrip`
/// (7.2s→TIMEOUT) and `sim_rhocalc_proptest_campaign` (52.6s→TIMEOUT) — because
/// the coarse recognizer is NON-CONVERGENT on genuinely-unparseable deep-`@`
/// (d≥2), so every malformed `@`-led reject span these generator-heavy tests
/// produce grinds to `RECOGNIZER_GATE_MAX_STEPS` then (soundly) SUPPRESSES the
/// previously-fast auth-reject → slow walker → timeout. A sound gate MUST
/// suppress-on-budget (never false-reject), so the regression is intrinsic to
/// gating on a non-convergent recognizer. The `@([])` false-reject is instead
/// addressed by a TARGETED auth-reject-matcher narrowing (no per-span recognizer
/// cost). The gate machinery stays for if/when the recognizer's deep-`@`
/// non-convergence is fixed. OFF ⇒ byte-identical to the pre-gate baseline.
pub(crate) const RECOGNIZER_REJECT_GATE: bool = false;

/// RECOGNIZER_GATE_MAX_STEPS — the coarse-walker step budget for the
/// [`RECOGNIZER_REJECT_GATE`] recognizer call. Modest (NOT the prefilter's 1M).
///
/// ## Empirically calibrated (2026-07-08 measurement, rhocalc)
/// The gate's recognizer is invoked ONLY on `__proj_sigil_reject` candidates. Three
/// regimes were measured (coarse walker ≈ 0.38 ms/step):
///   • CONVERGENT-Reachable (the parseable false-reject candidates, e.g.
///     `@([]) <= @(Map())`): the recognizer converges to `Reachable` in < 300 steps
///     REGARDLESS of budget (parse latency is budget-invariant at ~490 ms — that is
///     the WALKER parsing the now-un-rejected span, not the recognizer). ⇒ suppress
///     fires fast, the false-reject FIX is preserved at ANY budget ≥ ~300.
///   • CONVERGENT-Unreachable (shallow genuine rejects, e.g. `@Nil!(true false)`):
///     converge to `Unreachable` in ~100 steps ⇒ the reject fires (≈38 ms).
///   • NON-CONVERGENT (genuinely-unparseable DEEP-`@`, e.g. `@@Nil!(true false)`):
///     the coarse frontier NEVER converges — it grinds to `max_steps` at EVERY budget
///     (500 → 19 s at budget 50 000). Nothing converges in the (500, 50 000) range, so
///     a larger budget buys ZERO extra fast-rejects and only inflates the grind that
///     precedes the safe suppress → the full walker (which was going to run anyway;
///     the deep-`@` explosion is PRE-EXISTING — present identically with the gate
///     OFF). ⇒ a SMALL budget is strictly better here.
///
/// 500 sits above the convergent ceiling (< 300) with margin AND bounds the
/// non-convergent grind to ≈190 ms (vs ≈760 ms at the initially-suggested 2000).
/// Correctness is BUDGET-INDEPENDENT (suppress-on-budget is always sound); the budget
/// is purely an error-path latency knob. Env `PRATTAIL_RECOGNIZER_MAX_STEPS` overrides
/// at runtime for tuning without a rebuild.
pub(crate) const RECOGNIZER_GATE_MAX_STEPS: usize = 500;

/// INFIX_ISOLATION_COMBINE — the PRECEDENCE-AWARE BINARY-INFIX operand
/// DIVIDE-AND-CONQUER isolation+combine facade fast-path (ROOT-2 `or`/PParInfix
/// locus, 2026-07-06). Master compile-time kill-switch (same convention as
/// [`SEP_ISOLATION_COMBINE`] / [`PROJ_ISOLATION_COMBINE`]): folds a guarded
/// PROLOGUE into the generated `parse_<Cat>_via_wpda*` string entries for every
/// category named in [`INFIX_ISOLATION_CATEGORIES`]. It is the THIRD sibling of
/// the `.*sep` (P2) and `@`-projection (P1) isolators — those linearize LIST /
/// FRAME operands; THIS linearizes the two operands of a top-level BINARY INFIX.
///
/// ## The defect it ships the fix for (ROOT 2, `or` locus)
/// A binary-infix composition whose LEFT operand is a POLYADIC persistent send
/// carrying a division-containing arg — `@Nil!!(true, @Nil!() / @Nil!()) or X` —
/// parsed MONOLITHICALLY dies with "no accepting branch reached end of input": the
/// GLR frontier does not RECONVERGE across the infix-operand boundary (the same
/// edge-stack / cross-cat non-reconvergence as the `.*sep` / `@`-projection loci,
/// but at the binary-infix-operand level). Each operand parses in ISOLATION
/// (`@Nil!!(true,@Nil!() / @Nil!())` → Ok in ~6 ms via proj-iso; the RHS send → Ok)
/// and simpler `or`s parse; only the composition of a complex LEFT send with a
/// second send explodes. `proc_display_parse_roundtrip` @CASES=100 fails on it.
///
/// ## The fix (this feature)
/// Before each facade's monolithic body, a guarded prologue calls the emitted
/// per-category helper `__mettail_wpda_infix_isolate_all_<Cat>`. The helper (i)
/// scans the raw input at bracket-depth 0 for the category's binary-infix operator
/// terminals (grammar-derived from the SAME binding-power table the walker uses —
/// [`build_bp_table`](super::infix::build_bp_table)), (ii) elects the ROOT split:
/// the LOOSEST-precedence (min `left_bp.min(right_bp)`) depth-0 operator; among its
/// occurrences the RIGHTMOST for left-assoc (`left_bp < right_bp`) / LEFTMOST for
/// right-assoc — the exact Pratt root, so `a or b / c` splits at `or` and
/// `a or b or c` at the rightmost `or`, (iii) sub-parses the LEFT and RIGHT operand
/// spans through the OPERAND category's own string entry (fresh walker from ROOT —
/// RECURSES through ALL prologues incl proj/sep/infix, so nested infix + framed
/// sends both linearize), (iv) combines via the operator's binary ctor
/// `Cat::Label(Arc(l), Arc(r))`, ⊗-folding operand weights, (v) dedups by semantic
/// key + ⊕-min + weight-sort (the monolithic `_all` finalize). It returns
/// `Some((terms, weights))` on success, `None` for NOT-APPLICABLE (no depth-0
/// binary infix — a pure frame/atom, handled by proj/sep/monolithic) or ANY
/// sub-parse failure ⇒ the facade falls through to the UNMODIFIED monolithic body
/// (byte-identical — the monolithic path stays authoritative). Wired AFTER the
/// proj + sep prologues (mutually-exclusive by shape: proj/sep consume a WHOLE
/// frame/list; infix needs a depth-0 operator with BOTH operands present).
///
/// ## Generality (no per-language / per-rule hardcode)
/// The operator set, precedence, and associativity are read from the binding-power
/// table (`InfixOperator{terminal,left_bp,right_bp,label,category,result_category}`)
/// — the SAME classification the walker's InfixLoop consumes. Only HOMOGENEOUS
/// same-category binary infix (`category == result_category == cat`, `!postfix`,
/// `!mixfix`) is admitted; cross-category comparisons (`Int×Int→Bool`) are NOT
/// chainable at one category and fall to the monolithic path (sound). Maximal-munch
/// (`>=` beats `>`) + word-boundary (alpha `or`/`and`/`bitor`) + a leading-operand
/// guard (the char before the operator is an operand terminal, not another operator
/// / open bracket) exclude unary `-`/`*` in operator position.
///
/// ## Kill-switch / A-B
/// When `false`, NO prologue and NO helper are emitted for ANY category —
/// byte-identical (every generated `wpda.rs` md5 == baseline). The per-category
/// include set [`INFIX_ISOLATION_CATEGORIES`] gates WHICH categories opt in (EMPTY
/// = byte-identical even with the master switch `true`). The runtime env
/// `PRATTAIL_NO_INFIX_ISOLATION` forces the emitted prologue to return early
/// (reproduces the monolithic path) WITHOUT a rebuild — the causal A/B control.
///
/// FV: `formal/rocq/prattail_wpda_runtime/theories/InfixReconvergence.v`
/// (precedence-root split == monolithic Pratt parse, combine set-eq, linearity,
/// fallback refinement; zero-admission).
///
/// Byte-identical-OFF VERIFIED (2026-07-06): with this `false`, the generated
/// rhocalc `parser.rs`/`wpda.rs` differ from the `true` build by EXACTLY the infix
/// helper + the two prologues (0 OFF-only non-whitespace lines); calculator (not in
/// the include set) is md5-unchanged.
pub(crate) const INFIX_ISOLATION_COMBINE: bool = true;

/// Per-result-category INCLUDE set for [`INFIX_ISOLATION_COMBINE`] (mirrors the
/// [`SEP_ISOLATION_CATEGORIES`] / [`PROJ_ISOLATION_CATEGORIES`] convention). A
/// category is given the binary-infix isolation prologue + helper ONLY when its
/// name appears here AND [`INFIX_ISOLATION_COMBINE`] is `true` AND an
/// `InfixIsoShape` is derivable for it (≥1 homogeneous binary-infix operator).
/// EMPTY ⇒ byte-identical (plumbing checkpoint). `{"Proc"}` ships the `or` locus
/// (rhocalc's 16 `Proc×Proc→Proc` operators).
pub(crate) const INFIX_ISOLATION_CATEGORIES: &[&str] = &["Proc"];

/// CROSSCAT_LEX_COMPAT_GATE (option A — PRIMARY, emission-side bucket split;
/// 2026-07-03). The general, evidence-based first-token lexical-compatibility
/// FILTER at the cross-cat `Proc` (and any category's) PROJECTION fork.
///
/// ROOT it finishes (the `<-` residual / ROOT-P): `@`-NQuoteShort dispatching a
/// bare-Ident inner `p:Proc` forks 16 CrossCatDelegate cast branches (rules
/// 20-35 CastBigRat..CastWriteZipper) that ALL bucket into `Some(Ident)` — each
/// source category contributes `Ident` to its FIRST via its own Var rule
/// (`collect_first_set`), so all 16 casts share the Ident dispatch. ONLY PVar
/// (rule 106) + the CrossCatLhs→Name delegate are canonical; the 15/16 casts
/// realize ZERO parses on a genuine Ident (measured alts=1,
/// zz_inner_proc_w_enum) yet each spawns a distinct ProjDescriptorKey `W` →
/// Θ(8^k) frontier fan-out per `&`-segment (branch_cursors_peak_pre_merge
/// 176→11125→84077 base-8; fork_cross_cat_projection_branches scales base-8 in
/// lockstep — the proven driver). AT_QUOTED_BIND_GATE removed the OUTER `@a<-@b`
/// over-generation (alts 2→1) but NOT this INNER cross-cat cast fan-out; this
/// gate finishes it.
///
/// FIX: at the CrossCatProjection emission loop (`prefix.rs`, gate (A)), when a
/// projection's source-FIRST token is ONLY a var-contribution (`Ident`
/// from the source's Var rule — `FirstToken::is_var_contribution`) AND the
/// result category has its own home Var reading (`result_has_home_var_reading`),
/// skip that token — so the 16 casts leave the `Some(Ident)` bucket (18→2
/// branches: CrossCatLhs + PVar). Every LITERAL-first bucket (`Some(Integer)`,
/// `Some("[")`, `Some("{")`, `Set` keyword, …) KEEPS its cast (`@1`→CastBigInt,
/// `@[1]`→CastList, `@{k:v}`→CastMap, `@Set(1)`→CastSet all intact).
///
/// This is SOUND FIRST-set FILTERING per `feedback_use_wpds_disambiguation_not_heuristics`
/// (prune branches that realize ∅, measured alts=1) — NOT the forbidden FIRST-set
/// TIEBREAK (pick a winner among viable branches): (1) MEASURED alts=1 before
/// the gate (no genuine ambiguity to break); (2) the discriminator is
/// STATIC/DEFINITIONAL (`Ident ∈ var-contributions ∧ home-var-exists`, no
/// weight/rule-order); (3) one-sided monotone fail-safe — the gated dispatch set
/// is a strict SUBSET of the ungated set and every removed branch is
/// ∅-realizing ⇒ the REALIZED reading set is EQUAL. It removes never-real
/// branches at Fork CREATION (before any cursor/edge-stack/`W` forms), which
/// linearizes where downstream MERGE could not (the 8 refuted ROOT-P
/// merge-relaxations all operate on already-forked co-diverging cursors — there
/// was nothing to soundly merge; this stops the fork from happening).
///
/// KILL-SWITCH: `false` (baseline) ⇒ the gate conjunct is never evaluated, NO
/// token is skipped ⇒ generated `wpda.rs` is BYTE-IDENTICAL (md5-verified). FV:
/// `CrossCatLexCompatGate.v` (mirror `AtQuotedBindGate.v`, zero-admission).
pub(crate) const CROSSCAT_LEX_COMPAT_GATE: bool = true;

/// CROSSCAT_LEX_COMPAT_RUNTIME_GATE (option B — BACKSTOP runtime guard, INERT
/// under A; 2026-07-03). Defense-in-depth. Gates (1) emission of the
/// grammar-derived engine method `crosscat_proj_lex_compatible`
/// (`kind_dispatch.rs`, sibling `crosscat_lhs_has_projection_fallback`) that
/// returns true iff the peek'd token ∈ LITERAL-FIRST(source), and (2) the
/// `if crosscat_proj_lex_compatible(...)` wrap around the CrossCatProjection
/// push in the singleton + multi-branch prefix arms (`emit_unified_arm`). It is
/// fail-OPEN (a projection whose source LITERALLY begins with the token is
/// unaffected) and INERT under gate (A) (A already removes the var-only-Ident
/// projection at codegen — so at runtime there is no such branch to guard, 0
/// additional prunes). Kept for the multi-token-source path + future overlap.
/// When `false` (baseline) the engine method is not emitted (trait default
/// `true` applies → the wrap is a no-op) and the push is byte-identical.
pub(crate) const CROSSCAT_LEX_COMPAT_RUNTIME_GATE: bool = true;

/// S1_FACTORING — master kill-switch for the generic FGLL-style shared-prefix
/// factoring of the PrefixDispatch fan (Stage F0, 2026-07-11). Compile-time
/// `const` resolved at macro expansion (the [`FORROW_PROJ_GATE`] /
/// [`AT_QUOTED_BIND_GATE`] kill-switch convention — NOT a runtime env var).
///
/// Plan of record: `scratchpad/zz_probes/s1_factoring_plan.md` (§0-§5 plus the
/// red-team amendments A1-A10). Literature anchor: Scott & Johnstone,
/// *Structuring the GLL parsing algorithm for performance*, SCP 125 (2016).
/// The fan: at `PrefixDispatch` on `@` in RhoCalc `Proc` the generated engine
/// forks 15 per-rule branches (rules 10-24) that mirror the SAME `@` token
/// into the SPPF 15 times and run the inner `Name`/`Proc` sub-parse once per
/// RULE per nesting level; the factored emission runs it once per GROUP
/// (`@`-cohort: 16 branches → 4).
///
/// When `false` (F0 ships OFF): the factoring model
/// ([`super::factoring`]) is a PURE data-structure computation exercised only
/// by its unit tests and by the grammar-generality INV-8 prefix-surface
/// no-loss invariant — NO emitter consults it, and the generated
/// `target/generated/<lang>/wpda.rs` files are BYTE-IDENTICAL to the pre-F0
/// output for every bundled language (receipt:
/// `scratchpad/zz_probes/logs_s1f0/`).
///
/// When `true` (F1+): `factoring::emission_partition` drives the
/// unified-bucket Fork emission in `prefix.rs` (one spine branch per eligible
/// group, commit at trie divergence leaves), the `binder.rs` BinderRule key
/// space gains `(cat, SPINE_ID, spine_pos)` arms, and the lex-alt surface
/// (`kind_dispatch.rs` + [`emit_lex_fork_at_prefix_dispatch`]) emits GROUP
/// entries instead of per-member `PrefixOp` entries (red-team AV5 — without
/// that the lex-fork path re-creates the per-rule fan). Flip criteria: plan
/// §5 (the F4 gate — d4-under-cap + depth-uniformity primary, ≥5× d3 wall
/// secondary).
pub(crate) const S1_FACTORING: bool = false;

// ─────── Branch descriptors ──────────────────────────────────────────────

/// A single Fork branch in a Cluster 1 emission. Stringly-typed via
/// TokenStream so callers retain full control of the symbol/state/action
/// expressions.
pub(crate) struct FirstSetBranch {
    /// Branch identifier for diagnostics (e.g., "close", "sep", "ident").
    pub name: &'static str,
    /// Weight bias offset (0.0 = preferred; SKIP_BIAS = deprioritized).
    pub weight_bias: f64,
    /// `result_src_idx` for the branch's weight (lex-min tiebreak component).
    pub result_src_idx: u16,
    /// `rule_idx` for the branch's weight (source-order tiebreak — load-bearing).
    pub rule_idx: u16,
    /// `StackSymbolV2` expression to push onto the GSS for this branch.
    pub symbol: TokenStream,
    /// `WpdaState` expression for the branch's `new_state`.
    pub new_state: TokenStream,
    /// `ForkActionKind` expression. Default for most Cluster 1 branches:
    /// `ForkActionKind::Push`.
    pub action_kind: TokenStream,
}

// ─────── Cluster 1 helper ────────────────────────────────────────────────

/// Cluster 1 helper. Emits a `WpdaStepAction::Fork` over the given branches
/// with `consume_trigger` semantics specified by the caller. Following the
/// F7/F8/A.i pattern, branches are emitted unconditionally — the walker
/// discards only branches whose own guard/subsequent step fails.
///
/// Source-order tiebreak: branches are emitted in the same order as
/// `branches` parameter; per-branch `rule_idx` weight component gives
/// lower-index branches lex-min preference on tier-bias ties (see
/// `wpda_walker.rs::ForkBranch.weight`).
///
/// **Cursor-explosion mitigation.** When `branches.len() >= 2`, the emit
/// site grows the cursor count by N; nested call sites multiply. If a caller
/// installs a cursor-count bound, the walker reports structured
/// ambiguity-budget overflow when the live frontier exceeds it; it does not
/// silently prune by branch weight.
pub(crate) fn emit_first_set_fork(
    branches: &[FirstSetBranch],
    consume_trigger: bool,
) -> TokenStream {
    let branch_exprs: Vec<TokenStream> = branches
        .iter()
        .map(|b| {
            let bias = b.weight_bias;
            let src = b.result_src_idx;
            let rule = b.rule_idx;
            let symbol = &b.symbol;
            let new_state = &b.new_state;
            let action_kind = &b.action_kind;
            let _name = b.name;
            quote! {
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: #symbol,
                    weight: lex_w(#bias, #src, #rule),
                    new_state: #new_state,
                    action_kind: #action_kind,
                }
            }
        })
        .collect();

    quote! {
        WpdaStepAction::Fork {
            branches: vec![ #( #branch_exprs ),* ],
            consume_trigger: #consume_trigger,
        }
    }
}

// ─────── Cluster 2 #12 helper (lex-fork) ─────────────────────────────────

/// Cluster 2 #12 — emit a lex-Fork at PrefixDispatch top.
///
/// Wires `WpdaTokenSource::peek_alternatives(*pos)` into a Fork whose
/// branches each commit one lex alternative. Each branch's weight is
/// `from_cost_with_lex(0.0, src, rule, alt_idx)` so lex-min over alt_idx
/// preserves source-order tiebreak. Walker's existing
/// `MutableMultiTokenSource::commit_alternative` is invoked at commit_winner
/// time via `BuilderDelta::CommitLexAlternative`.
///
/// **Production semantics.** The default `SliceTokenSource::peek_alternatives`
/// returns `&[]`, so the lex-fork is dispatched only when a multi-alt token
/// source is in use (e.g., `MutableMultiTokenSource` after Stage 3.20 recovery
/// edge work in Commit 4). For default lexers, this emission is inert.
pub(crate) fn emit_lex_fork_at_prefix_dispatch(
    primary_src_idx: u16,
    // S1-FACTORING F1 amendment AV5 (2026-07-12): when the language has ≥1
    // factored group, a lex-alt `PrefixOp` entry may carry `rule_idx =
    // SPINE_ID` (the A3 group entry) — its WEIGHT identity stamp must be the
    // group's MIN member rule, NEVER the SPINE_ID (lex_w_alt identity fields
    // join `plus()` elections; a synthetic stamp would flip lattice-only
    // elected terms). The wrap routes through the generated
    // `__s1_spine_weight_rule` free fn (identity for real ids). `false` ⇒
    // the fn is not emitted and the weight expressions below are
    // byte-identical to the pre-F1 output.
    s1_any_groups: bool,
) -> TokenStream {
    // S1-FACTORING AV5: the two PrefixOp weight identity-stamp expressions
    // (primary alt_idx = 0u16; secondary alt_idx = the runtime `alt_idx`).
    let __s1_prefixop_weight_primary: TokenStream = if s1_any_groups {
        quote! {
            lex_w_alt_with_len(
                __open_len, 0.0, primary_src,
                __s1_spine_weight_rule(primary_src, info.rule_idx), 0u16,
            )
        }
    } else {
        quote! {
            lex_w_alt_with_len(
                __open_len, 0.0, primary_src, info.rule_idx, 0u16,
            )
        }
    };
    let __s1_prefixop_weight_secondary: TokenStream = if s1_any_groups {
        quote! {
            lex_w_alt_with_len(
                __open_len, 0.0, primary_src,
                __s1_spine_weight_rule(primary_src, info.rule_idx), alt_idx,
            )
        }
    } else {
        quote! {
            lex_w_alt_with_len(
                __open_len, 0.0, primary_src, info.rule_idx, alt_idx,
            )
        }
    };
    // ForRow F3 (2026-06-28): the kill-switch value, folded into the
    // projection-suppression guard below as a literal `true`/`false`
    // (`bool: ToTokens`). `false` ⇒ `!(false && …) == true` ⇒ projection
    // always kept ⇒ behaviorally byte-identical to the pre-F3 (F2) emission.
    let __forrow_proj_gate_lit = FORROW_PROJ_GATE;
    // KWAMBIG_PROJ_EXEMPT_GATE (ROOT-A, 2026-07-07): three codegen fragments,
    // EMPTY when the gate is off (⇒ every interpolation site below is textually
    // byte-identical to the pre-fix emission — the AT_QUOTED_BIND_GATE
    // convention). When on: (1) `__kwambig_pos_ident_decl` binds a once-per-fork
    // runtime bool `__pos_has_ident_reading` (some reading at `*pos` IS `Ident`);
    // (2)/(3) the primary/secondary `&& !( … )` conjuncts fold the exemption into
    // each `CrossCatProjection` arm's `__proj_keep`, keying on the projection
    // trigger being a KEYWORD (`kind ≠ Ident`) reading of that ident-ambiguous
    // position. `!( keyword ∧ ident-ambiguous )` is appended so a matched
    // exemption drives the inner `__proj_keep` conjunction false ⇒ `!( … )` ⇒
    // the projection is KEPT (strictly additive over F3).
    let __kwambig_pos_ident_decl: TokenStream = if KWAMBIG_PROJ_EXEMPT_GATE {
        quote! {
            let __pos_has_ident_reading: bool =
                matches!(
                    tokens.peek_kind(*pos),
                    Some(mettail_prattail::automata::TokenKind::Ident)
                ) || tokens.peek_alternatives(*pos).iter().any(|__a| {
                    matches!(__a.kind, mettail_prattail::automata::TokenKind::Ident)
                });
        }
    } else {
        TokenStream::new()
    };
    let __kwambig_exempt_primary: TokenStream = if KWAMBIG_PROJ_EXEMPT_GATE {
        quote! {
            && !(
                !matches!(
                    primary_kind,
                    mettail_prattail::automata::TokenKind::Ident
                ) && __pos_has_ident_reading
            )
        }
    } else {
        TokenStream::new()
    };
    let __kwambig_exempt_secondary: TokenStream = if KWAMBIG_PROJ_EXEMPT_GATE {
        quote! {
            && !(
                !matches!(
                    alt.kind,
                    mettail_prattail::automata::TokenKind::Ident
                ) && __pos_has_ident_reading
            )
        }
    } else {
        TokenStream::new()
    };
    quote! {
        // M6c.3 (2026-05-14): lex-Fork emits ALL alternatives — primary
        // (branch[0]) + each secondary that has a literal rule in the
        // requesting cat. Each branch is bound to its categorical
        // literal rule(s) via `lex_alt_rules_for_prefix(state_cat, kind)`; the
        // walker's LexAlt apply arm uses the rule's Return marker
        // symbol to flow the token through FireAction and produce an
        // AST term.
        //
        // Mandate compliance: pure rule-out by evidence. A branch is
        // dropped iff `lex_alt_rules_for_prefix` returns an empty Vec (no rule in the
        // requesting cat for that kind). No weight-based pre-filter.
        //
        // Primary cursor preserved: pre-M6c the Fork emitted only
        // secondaries and `return`ed, replacing the primary cursor.
        // Now branch[0] IS the primary alt (`alt_idx=0`,
        // `lex_alt_idx=0`); secondaries are `alt_idx=1..` with
        // `lex_alt_idx>=1`.
        //
        // Fast path: when `__branches.len() < 2` (no actual ambiguity
        // surviving the rule-out filter, or only the primary has a
        // rule), the function FALLS THROUGH to the normal per-cat
        // PrefixDispatch arms — byte-identical to non-ambiguous lex.
        if tokens.is_ambiguous_at(*pos) {
            let alts = tokens.peek_alternatives(*pos);
            let primary_src_for_fork: u16 = #primary_src_idx;
            // GEN-2 cross-cat collection-element lex-fork category fix
            // (2026-07-02): the dispatch category for this lex-fork is
            // normally the frontier-top symbol's category. BUT when the
            // frontier top is a `CollectionMarker` whose CollectionSpec
            // declares a cross-category element (`element_src_idx != result
            // (owning) category`), the token at `*pos` is a COLLECTION
            // ELEMENT that must be dispatched in the ELEMENT category, NOT
            // the owning-rule category. This mirrors the non-ambiguous
            // CollectionMarker cross-cat redirect in the `PrefixDispatch`
            // arm (engine_impl.rs: `category_entry_goal(element_src_idx)`),
            // which the lex-fork otherwise PRE-EMPTS: without this, a
            // lex-ambiguous keyword-led element (e.g. rhocalc `Nil`/`Map`/
            // `Set`/`Pathmap`/`str`/`bigrat`, each `Fixed(kw) | Ident`) in a
            // cross-cat collection slot (InputBindQuery `args:Vec(Proc)`
            // owned by `InputBind`) is looked up in the OWNING category, so
            // only the `Ident` secondary (a metavariable rule) survives and
            // the keyword's element-category rule (Proc `PZero`/`MapEmpty`/
            // `CastSet`/…) is never dispatched — the fork returns a lone
            // wrong-category branch and never falls through to the redirect.
            // A same-category collection element (`element == owning`, e.g. a
            // Proc send's `bs:Vec(Proc)` rest) has `element_src_idx == rs` so
            // this override is inert (byte-identical). Grammar-derived from
            // CollectionSpec — no per-rule/per-language hardcode. The
            // `COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED` const is the LIFO
            // kill-switch (flip to `false` to restore pre-fix behavior).
            const COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED: bool = true;
            let primary_src = {
                let __ft_cat = frontier_top
                    .map(|n| n.symbol.category_src_idx)
                    .unwrap_or(primary_src_for_fork);
                if COLL_ELEMENT_LEXFORK_REDIRECT_ENABLED {
                    match frontier_top {
                        Some(__ft)
                            if __ft.symbol.kind
                                == mettail_prattail::wpda_runtime::SymbolKind::CollectionMarker =>
                        {
                            let __rs = __ft.symbol.category_src_idx;
                            let __ri = __ft.symbol.rule_index_in_category;
                            let __slot = __ft.symbol.bp.unwrap_or(0u8);
                            match self
                                .collection_spec(__rs, __ri, __slot)
                                .and_then(|__s| __s.element_src_idx)
                            {
                                Some(__e) if __e != __rs => __e,
                                _ => __ft_cat,
                            }
                        }
                        _ => __ft_cat,
                    }
                } else {
                    __ft_cat
                }
            };
            let mut __branches: Vec<mettail_prattail::wpda_walker::ForkBranch<
                __DwW,
            >> = Vec::with_capacity(alts.len() + 1);
            // GEN-2 longest-open-token (2026-06-29): the byte length of the
            // PRIMARY open token at this dispatch. Each primary fork branch
            // carries it as `open_len` so a longer matched open (e.g. Pathmap
            // `{|`, len 2) wins over a shorter one (PPar `{`, len 1) above the
            // BP-tier biases. The SECONDARY loop shadows `__open_len` with each
            // alt's own `alt.text` length, so every branch's weight constructor
            // can uniformly reference `__open_len`.
            let __open_len: u16 =
                tokens.peek_text(*pos).map(|__t| __t.len() as u16).unwrap_or(0);
            // M6c.8.5 (2026-05-14): track whether the primary alt
            // survived the `lex_alt_rules_for_prefix` evidence filter. The
            // fall-through optimization (skip Fork when only the
            // primary survives → defer to standard PrefixDispatch
            // arms) is ONLY safe when the survivor IS the primary —
            // standard PrefixDispatch dispatches on `peek_kind` which
            // returns the primary's kind. When only a SECONDARY
            // survives, fall-through would silently dispatch the
            // primary kind (wrong rule), violating "never
            // disambiguate early". In that case we MUST Fork (even
            // for a single branch).
            let mut __primary_survived: bool = false;
            let mut __secondary_survived: bool = false;
            // Cross-category projection does not consume a lexical edge at
            // this site. It delegates to the source category, whose own
            // PrefixDispatch/lex-fork will consume the primary or secondary
            // edge by evidence. Emitting one projection branch per matching
            // lex alternative duplicates the same delegate and encodes a
            // false early alt choice in the branch weight, inflating the
            // frontier without adding evidence.
            let mut __crosscat_projection_seen: std::collections::BTreeSet<(u16, u16)> =
                std::collections::BTreeSet::new();
            let mut __crosscat_lhs_seen: std::collections::BTreeSet<u16> =
                std::collections::BTreeSet::new();

            // ForRow Part-1 push-gate (F0, 2026-06-28): row-scoped trigger
            // lookahead for the cross-cat-LHS EXTENSION delegates pushed below.
            // Computed ONCE (depends only on `primary_src` + `*pos`, not on the
            // per-alt rule info). Each `CrossCatLhs` arm keeps its push iff
            // `__ccl_trigger_scoped OR NOT crosscat_lhs_has_projection_fallback`
            // (H1) — i.e. it is suppressed ONLY when both (a) no scoped trigger
            // binds this LHS in-row AND (b) a transparent projection
            // source→result exists to carry the triggerless derivation. So a
            // triggerless in-row bind WITH a projection (`@[1]<-c` → ForRow via
            // `ForRowSingleNoWhere`) drops to projection-only, a genuine in-row
            // `&`/`where`/`<=` trigger still forks the extension, and a cross-cat
            // pair with NO projection fallback (LedTest `Num→Pred` via `==`)
            // keeps the delegate unconditionally — byte-identical to baseline.
            // The EOF fall-through predicate below
            // (`prefix_crosscat_lhs_trigger_ahead`) is UNCHANGED — this gates
            // only the PUSH sites. FV: CastLexForkCrossCatLhsGap.gate_no_loss
            // extended to the push site, conditioned on the projection fallback
            // (one-sided monotone refutation: when a projection carries the
            // triggerless case, scoped-absence ⇒ the delegate dies by evidence
            // anyway, so dropping it removes no admitting parse).
            let __ccl_trigger_scoped: bool =
                prefix_crosscat_lhs_trigger_ahead_scoped(primary_src, tokens, *pos);
            #__kwambig_pos_ident_decl

            // Branch[0] — PRIMARY (lex_alt_idx = 0).
            // M6c.6.4.d (2026-05-14): activated PrefixOp branch — same-cat
            // unary prefix rules (e.g., `Neg`) now emit lex-Fork branches
            // with `LexAltPrefixOp` action_kind, mirroring the standard
            // `Fixed(trigger) → ConsumeAndPush(BinderRule)` arm shape.
            if let Some(primary_kind) = tokens.peek_kind(*pos) {
                for info in lex_alt_rules_for_prefix(primary_src, &primary_kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic => {
                            let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                            let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                            ).with_kind_return();
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt_with_len(
                                    __open_len, 0.0, primary_src, info.rule_idx, 0u16,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: mettail_prattail::wpda_walker::ForkActionKind::LexAlt {
                                    alt_idx: 0u16,
                                    kind: primary_kind.clone(),
                                    text: primary_text,
                                    next_pos: primary_next_pos,
                                    rule_idx: info.rule_idx,
                                },
                            });
                            __primary_survived = true;
                        }
                        // GAP-3 route (a) (2026-06-28): the PRIMARY lattice
                        // reading is the Fixed(trigger) of a nullary
                        // multi-literal keyword rule (e.g. `Map`/`Pathmap`).
                        // Push the mixfix marker + enter MixfixLiteralRun(kind=2)
                        // — the trigger is mirrored as a TriggerTerminal by the
                        // LexAltNullaryRun apply (modelled on LexAltPrefixOp).
                        mettail_prattail::wpda_runtime::LexAltRuleKind::NullaryPrefixRun => {
                            let primary_text =
                                tokens.peek_text(*pos).unwrap_or("").to_string();
                            let primary_next_pos =
                                tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::mixfix_marker(
                                primary_src, info.rule_idx, 0u8,
                            );
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt_with_len(
                                    __open_len, 0.0, primary_src, info.rule_idx, 0u16,
                                ),
                                new_state: WpdaState::MixfixLiteralRun {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    completed_idx: 0u8,
                                    kind: 2u8,
                                    sub_pos: 0u8,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltNullaryRun {
                                        alt_idx: 0u16,
                                        trigger: primary_text,
                                        rule_idx: info.rule_idx,
                                        next_pos: primary_next_pos,
                                    },
                            });
                            __primary_survived = true;
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                            body_src_idx,
                        } => {
                            let primary_text = tokens.peek_text(*pos).unwrap_or("").to_string();
                            let primary_next_pos = tokens.next_pos(*pos, 0).unwrap_or(*pos + 1);
                            // Symbol shape: rule_at(cat, rule_idx, slot=1,
                            // Some(*cur_bp)) — NO with_kind_return. Mirror
                            // of standard `Fixed("-")` ConsumeAndPush arm.
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 1u8, Some(*cur_bp),
                            );
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: #__s1_prefixop_weight_primary,
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    body_src_idx,
                                    outer_bp: *cur_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                        alt_idx: 0u16,
                                        trigger: primary_text,
                                        rule_idx: info.rule_idx,
                                        body_src_idx,
                                        next_pos: primary_next_pos,
                                        outer_bp: *cur_bp,
                                    },
                            });
                            __primary_survived = true;
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatProjection {
                            source_src_idx,
                        } => {
                            // ForRow F3 (2026-06-28): symmetric projection-
                            // suppression gate — the exact DUAL of the F0
                            // extension push-gate (the `CrossCatLhs` arm below).
                            // Keep the transparent PROJECTION delegate UNLESS a
                            // row-scoped EXTENSION trigger (`&`/`where`/`<=`)
                            // binds this LHS AND a transparent projection
                            // source→result fallback exists. Under a trigger the
                            // projection is FUTILE: its ForRow result leaves the
                            // trigger unconsumable before the row delimiter, so it
                            // never reaches an accepting root, yet keeping it
                            // re-parses `b` in a 2nd GSS lineage the merge/subsume
                            // key rightly cannot fold (distinct sppf_stack) = the
                            // F2 `2^N` `&`-join frontier leak. Suppressing it
                            // leaves EXACTLY ONE delegate per dispatch (extension
                            // when triggered, projection otherwise), the logical
                            // complement of F0 (extension kept iff
                            // `trigger ∨ ¬proj`; projection kept iff
                            // `¬trigger ∨ ¬proj`). NON-ForRow projections (Pathmap
                            // `{|`, casts) carry no `&`/`where`/`<=` trigger ⇒
                            // `__ccl_trigger_scoped` false ⇒ guard folds to
                            // `__proj_keep == true` ⇒ BYTE-IDENTICAL. Behind
                            // `FORROW_PROJ_GATE` (this module) for A/B. FV:
                            // CastLexForkCrossCatLhsGap proj_gate_no_loss (dual of
                            // gate_no_loss; one-sided monotone refutation).
                            let __proj_keep = !(#__forrow_proj_gate_lit
                                && __ccl_trigger_scoped
                                && crosscat_lhs_has_projection_fallback(
                                    primary_src, source_src_idx,
                                )
                                #__kwambig_exempt_primary);
                            if __proj_keep
                                && __crosscat_projection_seen
                                    .insert((info.rule_idx, source_src_idx))
                            {
                                let sym = StackSymbolV2::rule_at(
                                    primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                                ).with_kind_return();
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: sym,
                                    weight: lex_w_with_len(
                                        __open_len,
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                        primary_src,
                                        info.rule_idx,
                                    ),
                                    new_state: WpdaState::CrossCatDelegate {
                                        source_src_idx,
                                        inner_cur_bp: *cur_bp,
                                    },
                                    // Stage 4 (Lever-1 emit-both supersedes Fix A,
                                    // 2026-06-27): route the cross-cat projection
                                    // delegate (e.g. Pathmap `{|`) through the NORMAL
                                    // cohort fork-push (`Push`), NOT Fix A's singleton
                                    // `PushProjectionInline`. The Pathmap `{|…|}`
                                    // close residual is closed by the InfixLoop
                                    // emit-both delimiter yield (frame_ctx); with that
                                    // close fix in place the OPEN-side projection
                                    // resolves the KV literals (`{|1:2|}`,
                                    // `{|["k"]:1|}`, `*@{|1:2|}`) through the ordinary
                                    // cohort push (empirically verified 2026-06-27), so
                                    // the singleton hack is no longer needed. FV:
                                    // ForkSurvivorBinderPop.v +
                                    // CollectionDelegateDispatch.v.
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                                });
                                // GEN-1 GAP-4 (2026-06-28): survival flag set INSIDE
                                // the `if __proj_keep` gate — symmetric with the
                                // secondary projection arm and the F0 `CrossCatLhs`
                                // arm. Previously this was a sibling statement AFTER
                                // the gate, so a SUPPRESSED primary projection still
                                // flipped `__primary_survived`, which could force the
                                // `__branches.len() == 1 && __primary_survived`
                                // fall-through (line ~709) into the normal dispatch —
                                // whose un-suppressed projection arm re-introduced the
                                // futile branch F3 had removed. Audit §GAP-4.
                                __primary_survived = true;
                            }
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatLhs {
                            source_src_idx,
                        } => {
                            // F0 push-gate (H1): suppress the EXTENSION delegate
                            // only when (a) no row-scoped trigger binds this LHS
                            // AND (b) a transparent projection source→result
                            // exists to carry the triggerless derivation. Where
                            // NO projection fallback exists (e.g. LedTest
                            // Num→Pred via `==`), the delegate is the ONLY
                            // source→result path, so it MUST stay — keep
                            // unconditionally (byte-identical to baseline).
                            let __ccl_keep = __ccl_trigger_scoped
                                || !crosscat_lhs_has_projection_fallback(
                                    primary_src, source_src_idx,
                                );
                            if __ccl_keep
                                && __crosscat_lhs_seen.insert(source_src_idx)
                            {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(source_src_idx),
                                    weight: lex_w_with_len(
                                        __open_len,
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                        primary_src,
                                        source_src_idx,
                                    ),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: *pos,
                                        cur_bp: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs,
                                });
                                __primary_survived = true;
                            }
                        }
                        // Other variants are InfixLoop-site only;
                        // shouldn't appear here.
                        _ => {}
                    }
                }
            }

            // Branches[1..] — SECONDARIES (lex_alt_idx = 1..).
            for (sec_idx, alt) in alts.iter().enumerate() {
                let alt_idx = (sec_idx + 1) as u16;
                // GEN-2 longest-open-token: shadow `__open_len` with THIS
                // secondary alt's matched open-token byte length (e.g. Pathmap
                // `{|` ⇒ 2). Every weight constructor below references
                // `__open_len`, which now resolves to this alt's length.
                let __open_len: u16 = alt.text.len() as u16;
                for info in lex_alt_rules_for_prefix(primary_src, &alt.kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::Atomic => {
                            let alt_next_pos = tokens
                                .next_pos(*pos, sec_idx + 1)
                                .unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                            ).with_kind_return();
                            __secondary_survived = true;
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt_with_len(
                                    __open_len, 0.0, primary_src, info.rule_idx, alt_idx,
                                ),
                                new_state: WpdaState::Unwinding,
                                action_kind: mettail_prattail::wpda_walker::ForkActionKind::LexAlt {
                                    alt_idx,
                                    kind: alt.kind.clone(),
                                    text: alt.text.to_string(),
                                    next_pos: alt_next_pos,
                                    rule_idx: info.rule_idx,
                                },
                            });
                        }
                        // GAP-3 route (a) (2026-06-28): the CRITICAL path —
                        // `Map`/`Pathmap` lex with `Ident` as PRIMARY and
                        // `Fixed(trigger)` as a SECONDARY. This arm keeps the
                        // Fixed reading alive (pushes the mixfix marker + enters
                        // MixfixLiteralRun(kind=2)) so it competes with the
                        // `Ident → Var` primary; for `Map()` the marker run
                        // consumes `( )` (longer parse) and wins by lex-min,
                        // while bare `Map` still parses as a Var.
                        mettail_prattail::wpda_runtime::LexAltRuleKind::NullaryPrefixRun => {
                            let alt_next_pos = tokens
                                .next_pos(*pos, sec_idx + 1)
                                .unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::mixfix_marker(
                                primary_src, info.rule_idx, 0u8,
                            );
                            __secondary_survived = true;
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: lex_w_alt_with_len(
                                    __open_len, 0.0, primary_src, info.rule_idx, alt_idx,
                                ),
                                new_state: WpdaState::MixfixLiteralRun {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    completed_idx: 0u8,
                                    kind: 2u8,
                                    sub_pos: 0u8,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltNullaryRun {
                                        alt_idx,
                                        trigger: alt.text.to_string(),
                                        rule_idx: info.rule_idx,
                                        next_pos: alt_next_pos,
                                    },
                            });
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PrefixOp {
                            body_src_idx,
                        } => {
                            let alt_next_pos = tokens
                                .next_pos(*pos, sec_idx + 1)
                                .unwrap_or(*pos + 1);
                            let sym = StackSymbolV2::rule_at(
                                primary_src, info.rule_idx, 1u8, Some(*cur_bp),
                            );
                            __secondary_survived = true;
                            __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: sym,
                                weight: #__s1_prefixop_weight_secondary,
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: primary_src,
                                    rule_idx: info.rule_idx,
                                    body_src_idx,
                                    outer_bp: *cur_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::LexAltPrefixOp {
                                        alt_idx,
                                        trigger: alt.text.to_string(),
                                        rule_idx: info.rule_idx,
                                        body_src_idx,
                                        next_pos: alt_next_pos,
                                        outer_bp: *cur_bp,
                                    },
                            });
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatProjection {
                            source_src_idx,
                        } => {
                            // ForRow F3 (2026-06-28): symmetric projection-
                            // suppression gate (secondary arm; same DUAL of the F0
                            // extension push-gate as the primary arm above — see
                            // that comment). Suppression here also withholds
                            // `__secondary_survived` (it sits inside the gated
                            // `if`, mirroring the F0 `CrossCatLhs` survival flag),
                            // so a suppressed projection cannot keep a fork alive.
                            let __proj_keep = !(#__forrow_proj_gate_lit
                                && __ccl_trigger_scoped
                                && crosscat_lhs_has_projection_fallback(
                                    primary_src, source_src_idx,
                                )
                                #__kwambig_exempt_secondary);
                            if __proj_keep
                                && __crosscat_projection_seen
                                    .insert((info.rule_idx, source_src_idx))
                            {
                                __secondary_survived = true;
                                let sym = StackSymbolV2::rule_at(
                                    primary_src, info.rule_idx, 0u8, Some(*cur_bp),
                                ).with_kind_return();
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: sym,
                                    weight: lex_w_with_len(
                                        __open_len,
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                        primary_src,
                                        info.rule_idx,
                                    ),
                                    new_state: WpdaState::CrossCatDelegate {
                                        source_src_idx,
                                        inner_cur_bp: *cur_bp,
                                    },
                                    // Stage 4 (Lever-1 emit-both supersedes Fix A,
                                    // 2026-06-27): route the cross-cat projection
                                    // delegate (e.g. Pathmap `{|`) through the NORMAL
                                    // cohort fork-push (`Push`), NOT Fix A's singleton
                                    // `PushProjectionInline`. The Pathmap `{|…|}`
                                    // close residual is closed by the InfixLoop
                                    // emit-both delimiter yield (frame_ctx); with that
                                    // close fix in place the OPEN-side projection
                                    // resolves the KV literals (`{|1:2|}`,
                                    // `{|["k"]:1|}`, `*@{|1:2|}`) through the ordinary
                                    // cohort push (empirically verified 2026-06-27), so
                                    // the singleton hack is no longer needed. FV:
                                    // ForkSurvivorBinderPop.v +
                                    // CollectionDelegateDispatch.v.
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                                });
                            }
                        }
                        mettail_prattail::wpda_runtime::LexAltRuleKind::CrossCatLhs {
                            source_src_idx,
                        } => {
                            // F0 push-gate (secondary, H1): same combined guard
                            // as the primary arm — suppress only when no scoped
                            // trigger AND a projection fallback exists.
                            let __ccl_keep = __ccl_trigger_scoped
                                || !crosscat_lhs_has_projection_fallback(
                                    primary_src, source_src_idx,
                                );
                            if __ccl_keep
                                && __crosscat_lhs_seen.insert(source_src_idx)
                            {
                                __secondary_survived = true;
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(source_src_idx),
                                    weight: lex_w_with_len(
                                        __open_len,
                                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                        primary_src,
                                        source_src_idx,
                                    ),
                                    new_state: WpdaState::PrefixDispatch {
                                        pos: *pos,
                                        cur_bp: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs,
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }

            // Stage 4 (Lever-1 emit-both) — prefix-dispatch site (mirrors the
            // InfixLoop emit-both): when a peeked lattice alternative's text
            // equals a required structural delimiter of the INNERMOST enclosing
            // collection frame (`frame_ctx`), ensure the category_entry
            // `Advance(Unwinding)` yield is present ALONGSIDE the operator/atomic
            // branches so an element sub-parse dispatched directly at a delimiter
            // (an absent/closing element) yields to its `CollectionMarker` rather
            // than being lost. When this fires it forces a `Fork` (the
            // `!__delim_yield` guard on `__fall_through` below) so the yield is
            // never swallowed by the keyword-reservation / crosscat-lhs
            // fall-throughs. Byte-identical on existing inputs: the prefix lex-
            // fork runs only at lattice-ambiguous positions, and a collection
            // delimiter appears at an element-START only in absent-element cases
            // that the corpus does not currently exercise.
            let __delim_yield = frame_ctx.has_structural_frame()
                && (frame_ctx.matches_delim(tokens.peek_text(*pos).unwrap_or(""))
                    || alts.iter().any(|__a| frame_ctx.matches_delim(&__a.text)));
            if __delim_yield {
                let __dy_sym = StackSymbolV2::category_entry(primary_src);
                let __dy_present = __branches.iter().any(|b| {
                    b.symbol == __dy_sym
                        && matches!(b.new_state, WpdaState::Unwinding)
                        && matches!(
                            b.action_kind,
                            mettail_prattail::wpda_walker::ForkActionKind::Advance
                        )
                });
                if !__dy_present {
                    __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                        symbol: __dy_sym,
                        weight: lex_one(),
                        new_state: WpdaState::Unwinding,
                        action_kind: mettail_prattail::wpda_walker::ForkActionKind::Advance,
                    });
                }
            }

            // Phase 5A keyword-reservation fix (2026-06-10): wire the
            // long-generated-but-never-called `prefix_primary_has_dispatch_rule`
            // into the fall-through decision. `lex_alt_rules_for_prefix` only
            // represents `Atomic | PrefixOp | CrossCatProjection`; it DROPS
            // collection-literal rules (ListLit/BagLit/MapLit) and multi-token
            // keyword-prefix rules (ElemList `at(...)`, DeleteList `delete(...)`,
            // …). For a keyword that ALSO matches the ident regex
            // (`list`/`at`/`error`/`int`/…) the lattice surfaces a SAME-LENGTH
            // `{Fixed("kw"), Ident}` ambiguity, so the lex-fork would Fork into
            // only the secondary `Ident -> Var` branch — making the keyword parse
            // as a bare variable (collections/keyword-prefix ops fail with
            // trailing `(`; `error op error` blows the cursor budget via the
            // 11-way cross-cat Var fan-out). When the PRIMARY token has a real
            // PrefixDispatch arm (`prefix_primary_has_dispatch_rule`) AND every
            // lexical alternative is the SAME LENGTH as the primary, fall through
            // to the normal `match peek` dispatch: it owns the collection/
            // keyword-prefix/terminal arms and dispatches the explicitly-declared
            // keyword. The same-length guard preserves genuine MULTI-length
            // disambiguation (e.g. `-3` = `{Minus@1, Integer@2}` must keep
            // forking both). Keyword-reservation at a same-length lexical tie: a
            // grammar-declared keyword beats the auto-injected `Var` fallback —
            // evidence-based (the grammar declares the literal), not a heuristic.
            let __primary_has_dispatch = tokens
                .peek_kind(*pos)
                .map(|pk| prefix_primary_has_dispatch_rule(primary_src, &pk))
                .unwrap_or(false);
            // Phase 5A cast-then-compare d1 (2026-06-10; FV:
            // CastLexForkCrossCatLhsGap — d1_restores_hosting +
            // extension_preserves_189_behavior + multilength_unaffected +
            // d1_fanout_constant, all zero-admission): the SECOND fall-through
            // evidence source. A keyword/ident-ambiguous token whose keyword
            // heads rules in a SOURCE category of a category-changing infix
            // RESULTING in the current state cat (e.g. `int` — cat-Int casts —
            // in a Bool-seeking context entered via the ProcBool projection;
            // Bool's Pass-0 owns a CrossCatLhs{Int} arm for it) may fall
            // through to the normal dispatch when the primary token carries
            // that evidence. Secondary keyword alternatives are represented
            // directly above by LexAltRuleKind::CrossCatLhs, because normal
            // dispatch can only inspect the primary token kind.
            // A surviving secondary branch is also evidence. Normal dispatch
            // can only inspect the primary token, so cross-cat fall-through is
            // valid only when it does not erase a secondary lexical path. This
            // preserves inputs such as a keyword/Ident tie where the keyword
            // can host a cross-cat operand and the Ident can satisfy the
            // requested category directly.
            // Same-length keyword reservation applies, identically to the
            // primary-rule fall-through above; inner cast levels are
            // owner-context (same-cat primaries), so the fan-out stays
            // depth-independent (the falsified per-level routing is the
            // 2^depth shape fenced by fix_strictly_below_falsified).
            // TRIGGER-PRESENCE GATE (FV: gate_no_loss /
            // gate_zero_overhead_when_absent / gate_kills_tower_blowup): the
            // delegate can host a result ONLY via an infix that CONSUMES its
            // trigger from the remaining input, so absence is definite,
            // monotone refutation — gate the fall-through on presence. This
            // collapses trigger-free nested-cast towers (str(float(int(...)))
            // — the cast arm's Bool-body branch is a SourceCtx at EVERY level,
            // each delegate re-parsing its suffix = 2^depth WORK, observed as
            // 18s/30s/>120s-timeout) back to owner-only work, while every
            // input that can actually host a category-changing infix keeps
            // its delegate.
            // EP-P1 Step-0 (2026-06-11, plan §P1 commit 2): the kind
            // predicate and the trigger gate are bound SEPARATELY so the
            // diagnostic hook below can distinguish "gated off by
            // trigger absence" from "kind miss" — the `&&` chain is
            // semantically identical to the original single binding
            // (short-circuit preserved).
            let __ccl_kind_hit = tokens
                .peek_kind(*pos)
                .map(|pk| prefix_crosscat_lhs_has_dispatch_rule(primary_src, &pk))
                .unwrap_or(false);
            let __primary_has_crosscat_lhs = __ccl_kind_hit
                && prefix_crosscat_lhs_trigger_ahead(primary_src, tokens, *pos);
            let __primary_next_pos = tokens.next_pos(*pos, 0);
            let __all_alts_same_length = alts
                .iter()
                .enumerate()
                .all(|(__i, _)| tokens.next_pos(*pos, __i + 1) == __primary_next_pos);
            // M6c.8.5 (2026-05-14): Fork when ≥2 branches survive OR
            // when the sole survivor is a SECONDARY (not the primary).
            // Fall-through only when 0 branches survived (standard
            // arm handles dispatch / fails naturally) OR when exactly
            // the primary survived (standard PrefixDispatch dispatches
            // on `peek_kind = primary` — byte-identical to non-
            // ambiguous lex, optimization preserved) OR when the primary
            // keyword owns a normal dispatch arm that the lex-alt table
            // cannot represent and all alternatives are same-length
            // (Phase 5A keyword-reservation above).
            let __fall_through = !__delim_yield
                && (__branches.is_empty()
                    || (__branches.len() == 1 && __primary_survived)
                    || (__primary_has_dispatch && __all_alts_same_length)
                    || (__primary_has_crosscat_lhs
                        && __all_alts_same_length
                        && !__secondary_survived));
            // EP-P1 Step-0 diagnostic hook (no-op without the
            // `walker-stats` feature). `crosscat_load_bearing` = the
            // fall-through decided true, would have been FALSE without
            // the crosscat disjunct, and ≥ 1 lex-alt branch was
            // bypassed — the runtime witness of the FV `d1_d2_delta`
            // (CastLexForkCrossCatLhsGap), counted as
            // `crosscat_lhs_d2_only_hits`.
            mettail_prattail::walker_stats::ep_p1::note_crosscat_lhs_fallthrough(
                __ccl_kind_hit,
                __primary_has_crosscat_lhs,
                __fall_through
                    && (__primary_has_crosscat_lhs
                        && __all_alts_same_length
                        && !__secondary_survived)
                    && !(__branches.is_empty()
                        || (__branches.len() == 1 && __primary_survived)
                        || (__primary_has_dispatch && __all_alts_same_length)),
            );
            if !__fall_through {
                return WpdaStepAction::Fork {
                    branches: __branches,
                    consume_trigger: false,
                };
            }
        }
    }
}

/// Emit a lex-Fork at InfixLoop top.
///
/// This mirrors the normal InfixLoop candidate construction, but runs it for
/// every surviving lexical alternative at the current token position. Each
/// branch carries the alternative-specific `next_pos`, so lattice token
/// sources advance along the chosen DAG edge.
pub(crate) fn emit_lex_fork_at_infix_loop(_primary_src_idx: u16) -> TokenStream {
    quote! {
        if tokens.is_ambiguous_at(_pos) {
            let alts = tokens.peek_alternatives(_pos);
            let primary_src = state_cat_src_idx;
            let mut __branches: Vec<mettail_prattail::wpda_walker::ForkBranch<
                __DwW,
            >> = Vec::with_capacity(alts.len() + 1);
            let mut __primary_survived: bool = false;
            let mut __primary_floor_blocked: bool = false;

            if let Some(primary_kind) = tokens.peek_kind(_pos) {
                let primary_text = tokens.peek_text(_pos).unwrap_or("").to_string();
                let primary_next_pos = tokens.next_pos(_pos, 0).unwrap_or(_pos + 1);
                for info in lex_alt_rules_for_infix(primary_src, &primary_kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PostfixOp {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    new_state: WpdaState::Unwinding,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltPostfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::InfixOp {
                            l_bp,
                            r_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                let new_state =
                                    if result_src_idx != primary_src {
                                        WpdaState::CrossCatDelegate {
                                            source_src_idx: primary_src,
                                            inner_cur_bp: r_bp,
                                        }
                                    } else {
                                        WpdaState::PrefixDispatch {
                                            pos: primary_next_pos,
                                            cur_bp: r_bp,
                                        }
                                    };
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    new_state,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltInfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            r_bp,
                                            result_src_idx,
                                            source_cat_src_idx: primary_src,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::mixfix_marker(
                                        result_src_idx, info.rule_idx, 0,
                                    ),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        0u16,
                                    ),
                                    // #307 ROOT-A D2: enter the pre-operand
                                    // literal run (kind=2) — this lex-fork site
                                    // previously jumped straight to the operand
                                    // (PrefixDispatch), resurrecting the part-0
                                    // skip on lattice-ambiguous triggers. The
                                    // child is allocated at the action_kind's
                                    // next_pos, so the pos-less state reads the
                                    // post-trigger position.
                                    new_state: WpdaState::MixfixLiteralRun {
                                        result_src_idx,
                                        rule_idx: info.rule_idx,
                                        completed_idx: 0,
                                        kind: 2,
                                        sub_pos: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                            alt_idx: 0u16,
                                            trigger: primary_text.clone(),
                                            rule_idx: info.rule_idx,
                                            next_pos: primary_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                                __primary_survived = true;
                            } else {
                                __primary_floor_blocked = true;
                            }
                        },
                        _ => {},
                    }
                }
            }

            // Stage 4 (Lever-1 emit-both): emit the category_entry
            // `Advance(Unwinding)` yield branch when EITHER the Pratt floor
            // blocked every primary operator (the original max-munch boundary)
            // OR a peeked lattice alternative's text equals a required structural
            // delimiter of the INNERMOST enclosing collection frame
            // (`frame_ctx`). The second trigger restores the no-candidate
            // fall-through that this lex-fork otherwise PRE-EMPTS on a
            // lattice-ambiguous multi-char close (e.g. the Pathmap `|}` close,
            // whose leading `|` collides with the `PParInfix` operator): the
            // element/value sub-parse never yields back to its `CollectionMarker`
            // and the close never resumes. The yield is ADDED ALONGSIDE the
            // operator branches (never instead) — the doomed operator fork dies
            // under the runtime ambiguity budget while the yield pops the element
            // to its `CollectionMarker`, which resumes its close. The match
            // ranges over primary ∪ peek_alternatives. A single push DEDUPs the
            // two triggers by `(symbol, new_state, action_kind)` — both produce
            // the identical `category_entry(primary_src)` + `Advance` +
            // `Unwinding` branch. Byte-identical on every existing passing input:
            // single-char seps are non-ambiguous (lex-fork never runs at them);
            // marker-framed elements are pre-empted by the CollectionMarker
            // reroute BEFORE this lex-fork; the only ambiguous category_entry
            // close with an operator secondary in the corpus is the Pathmap
            // `|}` residual.
            let __delim_yield = frame_ctx.has_structural_frame()
                && (frame_ctx.matches_delim(tokens.peek_text(_pos).unwrap_or(""))
                    || alts.iter().any(|__a| frame_ctx.matches_delim(&__a.text)));
            if (__primary_floor_blocked && !__primary_survived) || __delim_yield {
                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::category_entry(primary_src),
                    weight: lex_one(),
                    new_state: WpdaState::Unwinding,
                    action_kind: mettail_prattail::wpda_walker::ForkActionKind::Advance,
                });
            }

            for (sec_idx, alt) in alts.iter().enumerate() {
                let alt_idx = (sec_idx + 1) as u16;
                let alt_next_pos = tokens
                    .next_pos(_pos, sec_idx + 1)
                    .unwrap_or(_pos + 1);
                for info in lex_alt_rules_for_infix(primary_src, &alt.kind) {
                    match info.kind {
                        mettail_prattail::wpda_runtime::LexAltRuleKind::PostfixOp {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_POSTFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    new_state: WpdaState::Unwinding,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltPostfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::InfixOp {
                            l_bp,
                            r_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                let new_state =
                                    if result_src_idx != primary_src {
                                        WpdaState::CrossCatDelegate {
                                            source_src_idx: primary_src,
                                            inner_cur_bp: r_bp,
                                        }
                                    } else {
                                        WpdaState::PrefixDispatch {
                                            pos: alt_next_pos,
                                            cur_bp: r_bp,
                                        }
                                    };
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        result_src_idx, info.rule_idx, 0, Some(*cur_bp),
                                    ).with_kind_return(),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_INFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    new_state,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltInfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            r_bp,
                                            result_src_idx,
                                            source_cat_src_idx: primary_src,
                                        },
                                });
                            }
                        },
                        mettail_prattail::wpda_runtime::LexAltRuleKind::MixfixFirstTrigger {
                            l_bp,
                            result_src_idx,
                        } => {
                            if l_bp >= *cur_bp {
                                __branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::mixfix_marker(
                                        result_src_idx, info.rule_idx, 0,
                                    ),
                                    weight: lex_w_alt(
                                        mettail_prattail::automata::lex_weight::BP_TIER_MIXFIX,
                                        result_src_idx,
                                        info.rule_idx,
                                        alt_idx,
                                    ),
                                    // #307 ROOT-A D2: enter the pre-operand
                                    // literal run (kind=2) — see the primary
                                    // MixfixFirstTrigger site above; the child
                                    // is allocated at the action_kind's
                                    // next_pos (alt_next_pos).
                                    new_state: WpdaState::MixfixLiteralRun {
                                        result_src_idx,
                                        rule_idx: info.rule_idx,
                                        completed_idx: 0,
                                        kind: 2,
                                        sub_pos: 0,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::LexAltMixfixOp {
                                            alt_idx,
                                            trigger: alt.text.to_string(),
                                            rule_idx: info.rule_idx,
                                            next_pos: alt_next_pos,
                                            l_bp,
                                            result_src_idx,
                                        },
                                });
                            }
                        },
                        _ => {},
                    }
                }
            }

            let __fall_through =
                __branches.is_empty()
                    || (__branches.len() == 1 && __primary_survived);
            if !__fall_through {
                return WpdaStepAction::Fork {
                    branches: __branches,
                    consume_trigger: false,
                };
            }
        }
    }
}

// ─────── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emit_first_set_fork_three_branches_yields_fork_arm() {
        let branches = vec![
            FirstSetBranch {
                name: "close",
                weight_bias: 0.0,
                result_src_idx: 1,
                rule_idx: 0,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdaState::Unwinding },
                action_kind: quote! {
                    mettail_prattail::wpda_walker::ForkActionKind::CollectionClose
                },
            },
            FirstSetBranch {
                name: "sep",
                weight_bias: 0.0,
                result_src_idx: 1,
                rule_idx: 1,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdaState::PrefixDispatch { pos: *pos + 1, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
            },
            FirstSetBranch {
                name: "ident",
                weight_bias: SKIP_BIAS,
                result_src_idx: 1,
                rule_idx: 2,
                symbol: quote! { StackSymbolV2::category_entry(1) },
                new_state: quote! { WpdaState::PrefixDispatch { pos: *pos, cur_bp: 0 } },
                action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
            },
        ];
        let ts = emit_first_set_fork(&branches, true);
        let s = ts.to_string();
        assert!(s.contains("WpdaStepAction :: Fork"), "missing Fork arm: {}", s);
        assert!(s.contains("CollectionClose"), "missing CollectionClose: {}", s);
        // Phase C (2026-05-17) drift fix: emit_first_set_fork now produces
        // `lex_w(...)` per-branch weights (the canonical
        // LexicographicWeight constructor for Fork branches). The
        // previous assertion checked for `from_cost`, the older constructor
        // name; the underlying generator changed to `lex_w` without
        // updating this assertion. Test was a pre-existing failure unrelated
        // to Phase C — fixed here as part of the Phase C gauntlet sweep.
        assert!(s.contains("lex_w"), "missing lex_w weight: {}", s);
        // 3 branches => 3 ForkBranch literals.
        assert_eq!(s.matches("ForkBranch").count(), 3);
    }

    #[test]
    fn emit_first_set_fork_single_branch_ok() {
        let branches = vec![FirstSetBranch {
            name: "only",
            weight_bias: 0.0,
            result_src_idx: 0,
            rule_idx: 0,
            symbol: quote! { StackSymbolV2::category_entry(0) },
            new_state: quote! { WpdaState::Accepted },
            action_kind: quote! { mettail_prattail::wpda_walker::ForkActionKind::Push },
        }];
        let ts = emit_first_set_fork(&branches, false);
        let s = ts.to_string();
        assert!(s.contains("WpdaStepAction :: Fork"));
        assert_eq!(s.matches("ForkBranch").count(), 1);
        assert!(s.contains("consume_trigger : false"));
    }

    #[test]
    fn emit_lex_fork_emits_peek_alternatives_check() {
        let ts = emit_lex_fork_at_prefix_dispatch(0, false);
        let s = ts.to_string();
        assert!(s.contains("is_ambiguous_at"), "missing is_ambiguous_at: {}", s);
        assert!(s.contains("LexAlt"), "missing LexAlt action_kind: {}", s);
        assert!(
            s.contains("LexAltRuleKind :: CrossCatLhs"),
            "missing cross-cat LHS lex-alt kind: {}",
            s
        );
        assert!(
            s.contains("ForkActionKind :: PushCrossCatLhs"),
            "missing cross-cat LHS lex-alt action: {}",
            s
        );
        assert!(s.contains("peek_alternatives"), "missing peek_alternatives: {}", s);
    }

    #[test]
    fn emit_infix_lex_fork_emits_operator_action_variants() {
        let ts = emit_lex_fork_at_infix_loop(0);
        let s = ts.to_string();
        assert!(s.contains("lex_alt_rules_for_infix"), "missing infix lookup: {}", s);
        assert!(s.contains("LexAltPostfixOp"), "missing postfix action: {}", s);
        assert!(s.contains("LexAltInfixOp"), "missing infix action: {}", s);
        assert!(s.contains("LexAltMixfixOp"), "missing mixfix action: {}", s);
        assert!(
            s.contains("__primary_floor_blocked") && s.contains("ForkActionKind :: Advance"),
            "missing max-munch Pratt-floor boundary branch: {}",
            s
        );
        assert!(
            s.contains("consume_trigger : false"),
            "lex-alt operator actions consume intrinsically: {}",
            s
        );
    }

    #[test]
    fn cluster3_bp_tier_constants_are_strictly_increasing() {
        // Tier biases must be strictly increasing so lex-min picks lower
        // tiers on weight ties (infix < cross-cat-LHS < postfix < mixfix).
        assert!(BP_TIER_INFIX < BP_TIER_CROSSCAT_LHS);
        assert!(BP_TIER_CROSSCAT_LHS < BP_TIER_POSTFIX);
        assert!(BP_TIER_POSTFIX < BP_TIER_MIXFIX);
    }
}
