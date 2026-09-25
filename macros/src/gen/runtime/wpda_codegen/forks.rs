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

use proc_macro2::TokenStream;
use quote::quote;

// ─────── Per-cluster constants ───────────────────────────────────────────

/// Cluster 1 SKIP-branch weight bias. Reused from `EPSILON_OPT_SKIP` for
/// consistency with the canonical Opt-Group A.i Fork.
// dead_code: codegen-side reference value used only by the `#[cfg(test)]` ordering asserts;
// production emit strings reference `mettail_prattail::automata::lex_weight::*` directly.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const SKIP_BIAS: f64 = 0.5;

/// Cluster 5 (Commit 4) base offset for recovery branches.
pub(crate) const RECOVERY_BASE: u16 = 0xFE00;

/// Cluster 3 BP-tier biases. Lower wins on lex-min; tier 0 (infix) is
/// preferred over postfix/mixfix when l_bp ties.
// dead_code: codegen-side reference values used only by the `#[cfg(test)]` ordering asserts;
// production emit strings reference `mettail_prattail::automata::lex_weight::*` directly.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const BP_TIER_INFIX: f64 = 0.00;
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const BP_TIER_CROSSCAT_LHS: f64 = 0.05;
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) const BP_TIER_POSTFIX: f64 = 0.10;
#[cfg_attr(not(test), allow(dead_code))]
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
/// — the ONLY such trigger in rholang: `true`/`false` lex as BOTH a `Bool` literal
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
/// SIGIL `σ` (e.g. rholang `InputBind ::= Name "<-" Name`, `Name`'s FIRST
/// includes `@` via `NQuoteShort "@" p`), AND (ii) a SIBLING rule
/// `result ::= σ operand <same-bind-trigger> …` that begins with the SAME
/// sigil (e.g. `InputBindQuoted ::= "@" pat "<-" n`) admits TWO readings of
/// `σx <bind> …`: the whole-`source` reading `result(source=σx, …)` (parse `σx`
/// as one `source` atom, then project `source → result`) and the direct
/// sigil-triggered reading `result_quoted(operand=x, …)`. The whole-`source`
/// reading is a GRAMMAR OVER-GENERATION with no canonical counterpart (proven
/// for rholang against tree-sitter grammar.js + the interpreter + 100% corpus;
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
/// 3604/0, gen_rholang_unit 157/0, rholang_tests 383/0). BUT the design's
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
/// of `@a<-@b`, aligning Rholang with canonical Rholang) justifies enabling it
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
/// The fan: at `PrefixDispatch` on `@` in Rholang `Proc` the generated engine
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
/// prefix of a sibling's, e.g. Rholang `InputBindQuoted` (`@ pat <- n`)
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
/// Exactly ONE bundled cohort changes: rholang `(InputBind, "@")`
/// {QuotedQuery=2, Quoted=3, QuotedPersistent=6} — rholang groups 3 → 4,
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
/// `InfixLoop` on `!` (resp. `!!`) in Rholang `Name` the generated engine
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
/// When `true`: exactly ONE bundled engine changes (rholang — the only
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
// dead_code: constructed only by the `#[cfg(test)]` `emit_first_set_fork` shape test; not wired into the emit path.
#[cfg_attr(not(test), allow(dead_code))]
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
// dead_code: exercised only by the same-file `#[cfg(test)]` shape test; not wired into the emit path.
#[cfg_attr(not(test), allow(dead_code))]
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
    let branch_count = branch_exprs.len();
    let branch_pushes = branch_exprs.iter().map(|branch| {
        quote! {
            __first_set_branches.push(#branch);
        }
    });

    quote! {
        {
            let mut __first_set_branches = ::std::vec::Vec::with_capacity(#branch_count);
            #( #branch_pushes )*
            WpdaStepAction::Fork {
                branches: __first_set_branches,
                consume_trigger: #consume_trigger,
            }
        }
    }
}

// ─────── Cluster 2 #12 helper (lex-fork) ─────────────────────────────────

/// Cluster 2 #12 — emit a lex-Fork at PrefixDispatch top.
///
/// Wires `WpdaTokenSource::peek_alternatives(*pos)` into a Fork whose
/// branches each commit one lex alternative. Each branch's weight preserves
/// lexical extent, alternative ordinal, and declaration priority. Walker's existing
/// `MutableMultiTokenSource::commit_alternative` is invoked at commit_winner
/// time via `BuilderDelta::CommitLexAlternative`.
///
/// **Production semantics.** The default `SliceTokenSource::peek_alternatives`
/// returns `&[]`, so the lex-fork is dispatched only when a multi-alt token
/// source is in use (e.g., `MutableMultiTokenSource` after Stage 3.20 recovery
/// edge work in Commit 4). For default lexers, this emission is inert.
pub(crate) fn emit_lex_fork_at_prefix_dispatch(
    primary_src_idx: u16,
    contextual_keywords: &[String],
    s1_any_groups: bool,
) -> TokenStream {
    let contextual_keyword_literals = contextual_keywords.iter();
    let primary_is_contextual_keyword = if contextual_keywords.is_empty() {
        quote! { false }
    } else {
        quote! {
            matches!(
                tokens.peek_text(*pos),
                Some(#(#contextual_keyword_literals)|*)
            )
        }
    };
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
    let kwambig_observation = if KWAMBIG_PROJ_EXEMPT_GATE {
        quote! { #__kwambig_pos_ident_decl __pos_has_ident_reading }
    } else {
        quote! { () }
    };
    quote! {
        if let Some(__action) = mettail_prattail::wpda_transitions::lexical_fork::prefix(
            #primary_src_idx, pos, cur_bp, frontier_top, tokens, frame_ctx,
            |result_src_idx, rule_idx, slot_idx| self.collection_spec(result_src_idx, rule_idx, slot_idx),
            lex_alt_rules_for_prefix,
            prefix_crosscat_lhs_trigger_ahead_scoped,
            || { #kwambig_observation },
            |__ccl_trigger_scoped, primary_src, source_src_idx, primary_kind, __pos_has_ident_reading| {
                !(#__forrow_proj_gate_lit
                    && __ccl_trigger_scoped
                    && crosscat_lhs_has_projection_fallback(primary_src, source_src_idx)
                    #__kwambig_exempt_primary)
            },
            |__ccl_trigger_scoped, primary_src, source_src_idx, alt, __pos_has_ident_reading| {
                !(#__forrow_proj_gate_lit
                    && __ccl_trigger_scoped
                    && crosscat_lhs_has_projection_fallback(primary_src, source_src_idx)
                    #__kwambig_exempt_secondary)
            },
            crosscat_lhs_has_projection_fallback,
            prefix_primary_has_dispatch_rule,
            || { #primary_is_contextual_keyword },
            prefix_crosscat_lhs_has_dispatch_rule,
            prefix_crosscat_lhs_trigger_ahead,
            lex_one, lex_w, lex_w_with_len, lex_w_alt_with_len,
            |__open_len, primary_src, info| { #__s1_prefixop_weight_primary },
            |__open_len, primary_src, info, alt_idx| { #__s1_prefixop_weight_secondary },
        ) {
            return Some(__action);
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
/// `MixfixFirstTrigger` sites then route the scalar-cost trigger identity and
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
        mettail_prattail::wpda_transitions::lexical_fork::infix(
            state_cat_src_idx, cur_bp, _pos, tokens, frame_ctx,
            lex_alt_rules_for_infix,
            |result_src_idx, info| { #mixfix_identity_rule },
            lex_w_alt, lex_one,
        )
    }
}

// ─────── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn shared_lexical_fork_body(name: &str) -> String {
        let module = syn::parse_file(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../prattail/src/wpda_transitions/lexical_fork.rs",
        )))
        .expect("shared lexical fork source parses");
        let body = module
            .items
            .into_iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == name => Some(function.block),
                _ => None,
            })
            .expect("original shared lexical fork body exists");
        quote! { #body }.to_string()
    }

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
        // updating this assertion.
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
        let ts = emit_lex_fork_at_prefix_dispatch(0, &[], false);
        let forwarding = ts.to_string();
        let expected = quote! {
            mettail_prattail::wpda_transitions::lexical_fork::prefix
        };
        assert!(forwarding.contains(&expected.to_string()));
        assert!(forwarding.contains("lex_alt_rules_for_prefix"));
        assert!(forwarding.contains("prefix_crosscat_lhs_trigger_ahead_scoped"));
        assert!(forwarding.contains("return Some (__action)"));
        let s = shared_lexical_fork_body("prefix");
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
        assert!(
            s.contains("LexAltRuleKind :: CrossCatPrefixUnary"),
            "missing cross-category prefix-unary lex-alt kind: {}",
            s
        );
        assert!(
            s.contains("ForkActionKind :: LexAltCrossCatPrefixUnary"),
            "missing cross-category prefix-unary lex-alt action: {}",
            s
        );
        assert!(s.contains("peek_alternatives"), "missing peek_alternatives: {}", s);
    }

    #[test]
    fn contextual_keyword_retains_fork_only_when_primary_is_represented() {
        let ts = emit_lex_fork_at_prefix_dispatch(
            0,
            &["Module".to_string(), "Theory".to_string()],
            false,
        );
        let forwarding = ts.to_string();
        let keyword_policy = quote! {
            || { matches!(tokens.peek_text(*pos), Some("Module" | "Theory")) }
        };
        assert!(
            forwarding.contains(&keyword_policy.to_string()),
            "contextual policy must stay lazy: {forwarding}"
        );
        let s = format!("{} {}", forwarding, shared_lexical_fork_body("prefix"));
        assert!(s.contains("Module"), "missing Module policy: {s}");
        assert!(s.contains("Theory"), "missing Theory policy: {s}");
        assert!(
            s.contains("! __primary_is_contextual_keyword"),
            "contextual reservation guard is absent: {s}",
        );
        assert!(
            s.contains("! __primary_survived"),
            "unrepresented-primary completeness guard is absent: {s}",
        );
        assert!(
            s.contains("(! __primary_is_contextual_keyword || ! __primary_survived)"),
            "contextual dispatch does not encode the proved C/P disjunction: {s}",
        );
    }

    #[test]
    fn emit_infix_lex_fork_emits_operator_action_variants() {
        let ts = emit_lex_fork_at_infix_loop(0, false);
        let forwarding = ts.to_string();
        let expected = quote! {
            mettail_prattail::wpda_transitions::lexical_fork::infix(
                state_cat_src_idx, cur_bp, _pos, tokens, frame_ctx,
                lex_alt_rules_for_infix,
                |result_src_idx, info| { info.rule_idx },
                lex_w_alt, lex_one,
            )
        };
        assert!(
            forwarding.contains(&expected.to_string()),
            "infix must forward original observations and plain identity: {forwarding}"
        );
        assert_eq!(forwarding, expected.to_string(), "the shared InfixLoop owns early return");
        let s = shared_lexical_fork_body("infix");
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
            1,
            "grouped emission supplies the original identity callback: {}",
            grouped
        );
        let grouped_identity = quote! {
            |result_src_idx, info| { __s1_spine_weight_rule(result_src_idx, info.rule_idx) }
        };
        assert!(grouped.contains(&grouped_identity.to_string()));
        assert_eq!(
            s.matches("mixfix_identity_rule (result_src_idx , & info)").count(),
            4,
            "two MixfixFirstTrigger sites must each observe identity separately for weight and action-kind",
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
