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
pub(crate) const S1_FACTORING: bool = true;

/// S1F5_ACCEPT_CONTINUE — kill-switch for F5-1 accept+continue groups
/// (interior accept-nodes admitted as SIBLING LEAVES, 2026-07-13).
/// Compile-time `const` resolved at macro expansion (the [`S1_FACTORING`]
/// kill-switch convention — NOT a runtime env var). Effective ONLY while
/// [`S1_FACTORING`] is also `true`: `factoring::emission_partition`
/// short-circuits to the identity partition otherwise, and the model
/// (`factoring::build_prefix_factoring`) is consulted by no emitter.
///
/// Plan of record: `scratchpad/zz_probes/f5_accept_continue_plan.md` (§0-§9
/// plus the §RED-TEAM amendments A1-A4). The cohort being admitted: a
/// proper-prefix member — one whose post-trigger item list is a proper
/// prefix of a sibling's, e.g. RhoCalc `InputBindQuoted` (`@ pat <- n`)
/// inside `InputBindQuotedQuery` (`@ pat <- n ! ? ( args… )`) — marks its
/// whole group `IneligibleReason::InteriorAccept` under F0/F1, so the bucket
/// emits unfactored per-rule branches. The F5-1 design REJECTS an ε-branch
/// at the accept node (no non-consuming marker-replace `ForkActionKind`
/// exists — plan §9-FS1) and instead HOISTS the accept one edge earlier as
/// an ORDINARY LEAF sharing its edge item with the continuation subtree: the
/// fork at the arm consuming that edge emits the member's typed commit
/// branch AND the spine-continue branch. Every emitted construct is an
/// F1-emitted construct (action-identical replace/push/state species) —
/// ZERO walker changes, zero prefix/binder/kind_dispatch/engine_impl
/// changes; the entire delta is the `factoring.rs` model (forest-shaped
/// tries), its tests, and the INV-8 ON-branch census.
///
/// When `false`: `factoring::build_tree` routes exhausted members to
/// `interior_accepts` exactly as F0 shipped — the model, the emission, and
/// every generated `target/generated/<lang>/wpda.rs` are byte-identical to
/// the F4 flip state (receipts: `scratchpad/zz_probes/logs_s1f5_1/`).
///
/// When `true`: exhausted members finalize as sibling accept leaves
/// (`factoring::build_tree`, normative forest order `remainder ++ accepts`
/// per amendment A1) and the group proceeds to ordinary eligibility.
/// Exactly ONE bundled cohort changes: rhocalc `(InputBind, "@")`
/// {QuotedQuery=2, Quoted=3, QuotedPersistent=6} — rhocalc groups 3 → 4,
/// ineligible 1 → 0, InputBind@ dispatch rule-fan 3 → 1; every other
/// engine byte-invariant (amendment A2; census + hash gates in
/// `run_s1f5_1_*.sh`).
pub(crate) const S1F5_ACCEPT_CONTINUE: bool = true;

/// S1F5_MIXFIX_COHORTS — kill-switch for F5-2 mixfix send cohorts (the
/// InfixLoop Name-led send fan, 2026-07-13). Compile-time `const` resolved
/// at macro expansion (the [`S1_FACTORING`] kill-switch convention — NOT a
/// runtime env var). Effective ONLY while [`S1_FACTORING`] is also `true`:
/// `factoring::mixfix_emission_partition` short-circuits to the identity
/// partition otherwise, and the mixfix model
/// (`factoring::build_mixfix_factoring`) is consulted by no emitter.
///
/// Plan of record: `scratchpad/zz_probes/f5_mixfix_cohorts_plan.md` (§1-§8
/// plus the §RED-TEAM amendments A-M1..A-M5). The fan being factored: at
/// `InfixLoop` on `!` (resp. `!!`) in RhoCalc `Name` the generated engine
/// forks 3 per-rule `mixfix_marker` + `MixfixLiteralRun{kind: 2}` branches
/// — rules {4 POutput, 6 POutputEmpty, 8 POutput2Plus} (resp. {5, 7, 9}) —
/// so rules 4 and 8 EACH descend the payload sub-parse (×2 per send, and
/// the distinct marker symbols duplicate the whole payload subtree in the
/// pure descriptor space). The factored emission pushes ONE spine branch
/// per cohort (D-1 full-admission-only: admitted iff `min_l_bp >= cur_bp`
/// with the goal/method-name gates member-uniform; any partial-admission
/// window falls back to the verbatim per-member loop), runs ONE kind-2 run
/// and ONE payload walk, and commits to the member rule at the trie
/// divergence leaves INSIDE a spliced `MixfixLiteralRun` prelude (kind-2
/// exit for the nullary member; kind-0 step 1 for the operand members —
/// every commit rides a consuming edge, FS1). D-2 forces the width-1 trigger
/// Fork (`Fork{ct: true, n: 1}` — the M6c.8.5 precedent) so the action
/// family at send sites never changes; D-4 keeps every `mixfix_bp_<cat>`
/// table per-rule (the Arm G reset triple + iter-absorb `.first()` oracles);
/// D-6 stamps the spine trigger `lex_w(BP_TIER_MIXFIX, result, MIN member)`
/// (AV5-analog) with commit edges `lex_one()` — the C8-mixfix channel is
/// pre-classified (member-tail min-member substitution on NULLARY rows
/// only; payload rows byte-equal).
///
/// When `false`: the loop-v2 match, the MLR spine prelude, the
/// `mixfix_parts_len` poison rows, the lex-alt group entries, and every
/// mixfix engine-table row are ABSENT — the generated
/// `target/generated/<lang>/wpda.rs` files are byte-identical to the F5-1
/// flip state (receipts: `scratchpad/zz_probes/logs_s1f5_2/`).
///
/// When `true`: exactly ONE bundled engine changes (rhocalc — the only
/// language with factorable mixfix cohorts: Name `!` {4,6,8} spine 0xF803
/// and `!!` {5,7,9} spine 0xF804, per-RESULT-category ordinals continuing
/// after the Proc `@`-cohort prefix groups); calculator + fortranmodel are
/// hash-identical controls (census + hash gates in `run_s1f5_2_*.sh`).
/// The ONE prattail walker change riding this leg (A-M1, D-3 two-arm): the
/// fork-branch `ConsumeAtAndReplace` arms in BOTH engines honor
/// `branch.symbol` (pure sets `cur_sym`; classic conditionally
/// GSS-replaces on symbol inequality) — a no-op for every pre-F5-2 emitter
/// (`__checked_literal_consume!` is the sole fork-CAR emitter and is always
/// same-marker) and load-bearing for spine commits.
pub(crate) const S1F5_MIXFIX_COHORTS: bool = true;

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
///
/// S1-FACTORING F5-2 (A3-analog, red-team A-M5): `mixfix_spine_entries` is
/// `true` iff THIS language's `lex_alt_rules_for_infix` table carries
/// factored mixfix GROUP entries (`info.rule_idx` = a SPINE id). The two
/// `MixfixFirstTrigger` sites then route the `lex_w_alt` weight identity AND
/// the `LexAltMixfixOp.rule_idx` ACTION-KIND field through
/// `__s1_spine_weight_rule(result, rule)` — MIN member for spine ids
/// (AV5-mirrored; a SPINE id in either channel would leak into lex-min
/// elections / the classic `LexForkStamp` conversion), identity for real
/// ids. The branch `symbol`/`new_state` keep `info.rule_idx` (the spine
/// coordinates). Admission stays the site's own floor-only predicate
/// (`l_bp >= *cur_bp`; the group entry carries the cohort MIN l_bp = the
/// D-1 full-admission gate at this site). `false` ⇒ byte-identical
/// emission.
pub(crate) fn emit_lex_fork_at_infix_loop(
    _primary_src_idx: u16,
    mixfix_spine_entries: bool,
) -> TokenStream {
    // The two identity channels per MixfixFirstTrigger branch (weight rule +
    // action-kind rule_idx) — redirected only for grouped languages.
    let mixfix_identity_rule = if mixfix_spine_entries {
        quote! { __s1_spine_weight_rule(result_src_idx, info.rule_idx) }
    } else {
        quote! { info.rule_idx }
    };
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
                                        #mixfix_identity_rule,
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
                                            rule_idx: #mixfix_identity_rule,
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
                                        #mixfix_identity_rule,
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
                                            rule_idx: #mixfix_identity_rule,
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
        let ts = emit_lex_fork_at_infix_loop(0, false);
        let s = ts.to_string();
        assert!(s.contains("lex_alt_rules_for_infix"), "missing infix lookup: {}", s);
        assert!(s.contains("LexAltPostfixOp"), "missing postfix action: {}", s);
        assert!(s.contains("LexAltInfixOp"), "missing infix action: {}", s);
        assert!(s.contains("LexAltMixfixOp"), "missing mixfix action: {}", s);
        // F5-2 A-M5: without mixfix group entries the identity channels stay
        // the plain `info.rule_idx` (byte-identity); with them BOTH the
        // weight rule and the action-kind rule_idx route through
        // `__s1_spine_weight_rule`.
        assert!(
            !s.contains("__s1_spine_weight_rule"),
            "no-groups emission must not reference the redirect: {}",
            s
        );
        let grouped = emit_lex_fork_at_infix_loop(0, true).to_string();
        assert_eq!(
            grouped.matches("__s1_spine_weight_rule").count(),
            4,
            "two MixfixFirstTrigger sites × (weight + action-kind) redirects: {}",
            grouped
        );
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
