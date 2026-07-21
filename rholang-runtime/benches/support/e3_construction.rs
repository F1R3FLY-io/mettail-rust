//! E-3 (lazy/incremental set-automaton construction) — Stage-0 phase-split + first-touch
//! cell support, shared (by `#[path]` inclusion) with the JSON-lines driver bin
//! `src/bin/bench_e3_construction.rs`. Deliberately SEPARATE from the Track-B
//! `workloads.rs` (the E-3 design forbids growing the shared module).
//!
//! # What this module measures
//!
//! The in-Rho FIRST-COMPILE pipeline of a `definition_source` — the exact call sequence
//! `CompiledInRhoArtifacts` memoizes (`rho_net_cache.rs`):
//!
//! ```text
//! reconstruct_language_def → lower_language_def → compile_in_rho_matching_ruleset
//!                          → from_language_def → lower_to_par → installed_program_par
//! ```
//!
//! Phase attribution uses the E-3 Stage-0 SELF-time spans
//! (`mettail_rholang_codegen::pipeline_spans`): the phases RE-ENTER each other
//! (`compile_in_rho_matching_ruleset` re-runs the full lowering through
//! `rho_net_injection_sites`; `DRIVE_OPT_IN` languages nest a second ruleset compile
//! inside `drive_lowering`), so per-phase wall timers would double-count — SELF time is
//! the partition (red-team amendment EM-4a).
//!
//! # Workloads
//!
//! * **W-C real anchors** — the production `language!` bodies of RhoCalc / Calculator /
//!   Lambda / Ambient, extracted verbatim from `languages/src/*.rs` exactly as the
//!   production-language gate tests do (`extract_language_body`). RhoCalc is the largest
//!   committed full-pipeline datapoint; Ambient is pinned POST-A-S5.4b (EM-9: the
//!   Cardelli–Gordon premise fix changed Ambient's fingerprint and flipped it
//!   installing).
//! * **W-A `rules_ladder(r)`** — GENERATED definition sources (and, for the direct entry
//!   mode, the same pattern sets handed straight to `SetAutomaton::compile_structural`),
//!   deterministic pure functions of `(r, shape, alphabet)`:
//!
//!   | shape | rule `i`'s LHS pattern | notes |
//!   |---|---|---|
//!   | `multi1` / `multi3` | `Rᵢ(Sˢ(x))`, `s ∈ {1, 3}` | the Track-B `multi_rule_shared` shape: pairwise-distinct roots over ONE shared `Sˢ(x)` sub-chain |
//!   | `mixed` | `i % 5 ∈ {0,1}`: flat `Rᵢ(x)` · `{2,3}`: nested-2 `Rᵢ(S(S(x)))` · `{4}`: shared-root `Shared(Tᵢ(x))` | the design's ~40/40/20 flat / nested-2 / shared-root mix |
//!
//!   Every rewrite is `Mᵢ . |- (…LHS…) ~> (Wrap x) ;` — a unary-wrap contractum (the
//!   `AcDemo` precedent), kept constant across shapes so construction cost varies with
//!   the LHS pattern set only.
//!
//!   **Alphabet axis (`multi*` shapes only; the thesis-'maa' 708-symbol analogue at
//!   r = 750):** `distinct` gives every rule its own root op `Rᵢ` (r + 2 constructors);
//!   `shared16` folds the roots to 16 ops `R₍ᵢ mod 16₎` and keeps the r rules'
//!   patterns pairwise distinct by growing the chain depth to `s + ⌊i/16⌋`
//!   (all-var-leaf, same matching class as `distinct`). REALIZATION NOTE (recorded for
//!   the coordinator, design leaves the mechanism open): rule distinctness under shared
//!   roots comes from DEPTH, not from ground leaves, so both alphabet arms stay in the
//!   variable-leaf class and the regressor (total pattern nodes) remains comparable.
//!
//! EM-11 harness note (BINDING, recorded): the per-CALL receiver-network emitter's
//! `groups.iter_mut().find` scan is `O(entries × distinct-ops)` on the EXEC-time network
//! path — it does NOT sit in the derivation pipeline measured here, but any future
//! exec-time cell at the r = 750 `distinct` axis inherits it.
//!
//! # The H2v2 first-touch arms (T-LAZY; red-team amendment EM-1)
//!
//! EM-1 re-scoped H2 as DEAD-WEIGHT ELIMINATION: the cache's eager installed-par
//! emission had ZERO consumers, so deferring it wins its Stage-0 SELF-time share on
//! every first touch. Three arms, one per invocation, so BOTH cell states are measured:
//!
//! | arm | what one rep times (fresh thread each) | validated cell state |
//! |---|---|---|
//! | `eager-control` | the full pure pipeline sequence — exactly the pre-T-LAZY `derive` body ("today's eager memoized pipeline") | n/a (no cells) |
//! | `lazy-gate-only` | `cached_in_rho_artifacts` + `ruleset()` — the exec/gate forcing set | `ruleset` forced; `lowered`/`installed_par` UNFORCED |
//! | `lazy-force-installed` | `cached_in_rho_artifacts` + `ruleset()` + `installed_par()` — THE named forcing consumer (bench-only; production accessor adoption is a D3 question) | all three forced |
//!
//! The H2v2 win claim compares `lazy-gate-only` against `eager-control` (expected ≥ the
//! Stage-0 SELF-time share of the deferred phases); `lazy-force-installed` against
//! `eager-control` is the ≤ 2% full-path regression guard. A rep whose cell-state
//! validation fails is emitted as a DNF, never silently kept.
//!
//! # Cell discipline
//!
//! Every cell rep runs on a FRESH thread ([`in_fresh_thread`]): the artifact cache is
//! `thread_local!`, so a fresh thread is a true first-touch by construction, and the
//! `!Send` artifacts (`LanguageDef` holds `proc-macro2` data) never cross threads — only
//! `Send`-safe numbers return. Thread spawn/join sit OUTSIDE the timed region. The timed
//! region INCLUDES the `source.to_string()` copy (derivation fidelity: `derive` stores
//! the source as its collision-verification key) and EXCLUDES the memo-map hash/insert
//! of `cached_in_rho_artifacts` on the pure-pipeline arms (sub-µs against multi-ms
//! cells; the asymmetry DISFAVORS the treatment arms, i.e. it is conservative for every
//! win claim).

use std::time::Instant;

use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};
use mettail_rholang_codegen::pipeline_spans::{
    begin_phase_span_collection, take_phase_span_report, PhaseSpanReport,
};
use mettail_rholang_codegen::rho_net::RhoNetProgram;
use mettail_rholang_codegen::rho_net_ruleset::compile_in_rho_matching_ruleset;
use mettail_rholang_codegen::{lower::lower_language_def, reconstruct_language_def};

// ─────────────────────────────────────────────────────────────────────────────────────
// W-C anchors: the production language bodies, extracted verbatim.
// ─────────────────────────────────────────────────────────────────────────────────────

/// The four W-C anchor languages (design §3), in size order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnchorLanguage {
    /// `languages/src/lambda.rs` — production Lambda (β + congruences, drive-admitted).
    Lambda,
    /// `languages/src/ambient.rs` — production Ambient POST-A-S5.4b (the EM-9 pin).
    Ambient,
    /// `languages/src/calculator.rs` — production Calculator (the scalar-heavy anchor).
    Calculator,
    /// `languages/src/rhocalc.rs` — production RhoCalc: the largest committed
    /// full-pipeline datapoint (117 entries / 124 states / 314 raw automaton nodes).
    RhoCalc,
}

/// Every anchor, in the order cells are reported.
pub const ALL_ANCHORS: [AnchorLanguage; 4] = [
    AnchorLanguage::Lambda,
    AnchorLanguage::Ambient,
    AnchorLanguage::Calculator,
    AnchorLanguage::RhoCalc,
];

impl AnchorLanguage {
    /// The stable CLI / JSON name of this anchor.
    pub fn name(self) -> &'static str {
        match self {
            AnchorLanguage::Lambda => "lambda",
            AnchorLanguage::Ambient => "ambient",
            AnchorLanguage::Calculator => "calculator",
            AnchorLanguage::RhoCalc => "rhocalc",
        }
    }

    /// Parse a CLI anchor name.
    pub fn from_name(name: &str) -> Option<Self> {
        ALL_ANCHORS.iter().copied().find(|anchor| anchor.name() == name)
    }

    /// The verbatim `language! { … }` body of this anchor's production source file.
    pub fn definition_source(self) -> &'static str {
        match self {
            AnchorLanguage::Lambda => {
                extract_language_body(include_str!("../../../languages/src/lambda.rs"))
            },
            AnchorLanguage::Ambient => {
                extract_language_body(include_str!("../../../languages/src/ambient.rs"))
            },
            AnchorLanguage::Calculator => {
                extract_language_body(include_str!("../../../languages/src/calculator.rs"))
            },
            AnchorLanguage::RhoCalc => {
                extract_language_body(include_str!("../../../languages/src/rhocalc.rs"))
            },
        }
    }
}

/// Extract the verbatim `language! { … }` body from a production language source file —
/// the same extraction `rho_net_cache.rs`'s tests and
/// `rholang-codegen/tests/a_s5c_production_language_gates.rs` use: everything between
/// the macro invocation's opening `{` and the LAST `}` in the file (each anchor file
/// ends at the macro's own closing brace — verified for all four anchors).
pub fn extract_language_body(source: &str) -> &str {
    let macro_at =
        source.find("language!").expect("the production language file must invoke language!");
    let open = source[macro_at..]
        .find('{')
        .map(|offset| macro_at + offset)
        .expect("the language! invocation must open a brace");
    let close = source.rfind('}').expect("the language! invocation must close its brace");
    &source[open + 1..close]
}

// ─────────────────────────────────────────────────────────────────────────────────────
// W-A rules_ladder: generated definition sources + the direct pattern sets.
// ─────────────────────────────────────────────────────────────────────────────────────

/// The ladder pattern shapes (module docs table).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LadderShape {
    /// `Rᵢ(S¹(x))` — the shared-chain shape at depth 1.
    Multi1,
    /// `Rᵢ(S³(x))` — the shared-chain shape at depth 3.
    Multi3,
    /// ~40/40/20 flat / nested-2 / shared-root (deterministic by `i % 5`).
    Mixed,
}

impl LadderShape {
    /// The stable CLI / JSON name of this shape.
    pub fn name(self) -> &'static str {
        match self {
            LadderShape::Multi1 => "multi1",
            LadderShape::Multi3 => "multi3",
            LadderShape::Mixed => "mixed",
        }
    }

    /// Parse a CLI shape name.
    pub fn from_name(name: &str) -> Option<Self> {
        [LadderShape::Multi1, LadderShape::Multi3, LadderShape::Mixed]
            .into_iter()
            .find(|shape| shape.name() == name)
    }

    /// The shared `S`-chain depth of the `multi*` shapes (`None` for `mixed`).
    fn shared_depth(self) -> Option<usize> {
        match self {
            LadderShape::Multi1 => Some(1),
            LadderShape::Multi3 => Some(3),
            LadderShape::Mixed => None,
        }
    }
}

/// The root-op alphabet axis (`multi*` shapes only; module docs).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LadderAlphabet {
    /// One root op `Rᵢ` per rule.
    Distinct,
    /// 16 shared root ops `R₍ᵢ mod 16₎`; per-rule distinctness via chain depth
    /// `s + ⌊i/16⌋` (all-var-leaf — see the module-docs realization note).
    Shared16,
}

impl LadderAlphabet {
    /// The stable CLI / JSON name of this alphabet.
    pub fn name(self) -> &'static str {
        match self {
            LadderAlphabet::Distinct => "distinct",
            LadderAlphabet::Shared16 => "shared16",
        }
    }

    /// Parse a CLI alphabet name.
    pub fn from_name(name: &str) -> Option<Self> {
        [LadderAlphabet::Distinct, LadderAlphabet::Shared16]
            .into_iter()
            .find(|alphabet| alphabet.name() == name)
    }
}

/// The harness's DEFAULT 9-point r ladder (log-spaced through the thesis §4.7 regime;
/// includes the r = 750 alphabet-axis anchor and the r = 1000 endpoint). The
/// pre-registration locks the actual values at `experiment_open`; cells can override
/// per-invocation via `--r`.
pub const DEFAULT_LADDER_R: [usize; 9] = [8, 16, 32, 64, 125, 250, 500, 750, 1000];

/// One ladder rule's structural description: its root op, the ops of the unary spine
/// UNDER the root (outermost first), all over a variable leaf `x`.
///
/// Single source of truth for BOTH entry modes: [`ladder_source`] renders it as a
/// `rewrites { … }` line and [`ladder_patterns`] builds the identical
/// [`Pattern`] — so the generated-source arm and the direct-construction arm compile
/// the SAME pattern set by construction.
fn ladder_rule_spine(
    rule: usize,
    shape: LadderShape,
    alphabet: LadderAlphabet,
) -> (String, Vec<String>) {
    match shape {
        LadderShape::Multi1 | LadderShape::Multi3 => {
            let base_depth =
                shape.shared_depth().expect("multi* shapes carry a shared depth");
            let (root, depth) = match alphabet {
                LadderAlphabet::Distinct => (format!("R{rule}"), base_depth),
                LadderAlphabet::Shared16 => (format!("R{}", rule % 16), base_depth + rule / 16),
            };
            (root, vec!["S".to_string(); depth])
        },
        LadderShape::Mixed => match rule % 5 {
            // ~40%: flat `Rᵢ(x)`.
            0 | 1 => (format!("R{rule}"), Vec::new()),
            // ~40%: nested-2 `Rᵢ(S(S(x)))`.
            2 | 3 => (format!("R{rule}"), vec!["S".to_string(); 2]),
            // ~20%: shared-root `Shared(Tᵢ(x))`.
            _ => ("Shared".to_string(), vec![format!("T{rule}")]),
        },
    }
}

/// Validate a ladder cell's parameters (the `mixed` shape has no alphabet axis — reject
/// the meaningless combination loudly instead of silently ignoring it).
pub fn validate_ladder_cell(
    r: usize,
    shape: LadderShape,
    alphabet: LadderAlphabet,
) -> Result<(), String> {
    if r == 0 {
        return Err("the rules ladder needs r >= 1".to_string());
    }
    if shape == LadderShape::Mixed && alphabet == LadderAlphabet::Shared16 {
        return Err(
            "the shared16 alphabet axis is defined for the multi* shapes only (design §3: \
             the r = 750 alphabet axis rides the multi_rule family)"
                .to_string(),
        );
    }
    Ok(())
}

/// Generate the W-A `rules_ladder(r)` DEFINITION SOURCE — a complete `language!` body
/// (the same surface the anchors and every generated language feed through
/// `reconstruct_language_def`).
pub fn ladder_source(r: usize, shape: LadderShape, alphabet: LadderAlphabet) -> String {
    validate_ladder_cell(r, shape, alphabet).expect("ladder cell parameters validate");
    // Collect the distinct constructor ops the r rules mention (declaration order:
    // Wrap, S, then roots/second-level ops in first-use order).
    let mut ops: Vec<String> = vec!["Wrap".to_string(), "S".to_string()];
    let mut spines: Vec<(String, Vec<String>)> = Vec::with_capacity(r);
    for rule in 0..r {
        let (root, spine) = ladder_rule_spine(rule, shape, alphabet);
        for op in std::iter::once(&root).chain(spine.iter()) {
            if !ops.iter().any(|seen| seen == op) {
                ops.push(op.clone());
            }
        }
        spines.push((root, spine));
    }

    // Preallocate: ~64 B per term line, ~48 B per rewrite line + the fixed skeleton.
    let mut source = String::with_capacity(128 + ops.len() * 64 + r * 48);
    source.push_str(&format!(
        "\n        name: E3Ladder{}{}R{r},\n        types {{ Proc }}\n        terms {{\n",
        capitalized(shape.name()),
        capitalized(alphabet.name()),
    ));
    for op in &ops {
        // Every constructor is unary over Proc with its own lowercase display keyword.
        source.push_str(&format!(
            "            {op} . x:Proc |- \"{}\" \"(\" x \")\" : Proc ;\n",
            op.to_lowercase()
        ));
    }
    source.push_str("        }\n        equations {}\n        rewrites {\n");
    for (rule, (root, spine)) in spines.iter().enumerate() {
        // Rule i's LHS: root over its unary spine over the variable leaf.
        let mut lhs = String::from("x");
        for op in spine.iter().rev() {
            lhs = format!("({op} {lhs})");
        }
        lhs = format!("({root} {lhs})");
        source.push_str(&format!("            M{rule} . |- {lhs} ~> (Wrap x) ;\n"));
    }
    source.push_str("        }\n    ");
    source
}

/// Build the SAME r-rule pattern set as [`ladder_source`]'s rewrites, as direct
/// [`Pattern`] values for the `compile_structural` entry mode (W-A(b)).
pub fn ladder_patterns(
    r: usize,
    shape: LadderShape,
    alphabet: LadderAlphabet,
) -> Vec<(PatternId, Pattern<String>)> {
    validate_ladder_cell(r, shape, alphabet).expect("ladder cell parameters validate");
    (0..r)
        .map(|rule| {
            let (root, spine) = ladder_rule_spine(rule, shape, alphabet);
            let mut pattern = Pattern::var("x");
            for op in spine.iter().rev() {
                pattern = Pattern::app(op.clone(), vec![pattern]);
            }
            (PatternId(rule), Pattern::app(root, vec![pattern]))
        })
        .collect()
}

/// Total pattern nodes of a pattern set — H1's pre-registered regressor (EM-7b:
/// `log(total pattern nodes)`, per shape). Counts every application node and every
/// variable leaf.
pub fn pattern_node_count(patterns: &[(PatternId, Pattern<String>)]) -> usize {
    fn nodes(pattern: &Pattern<String>) -> usize {
        match pattern {
            Pattern::Var(_) => 1,
            Pattern::App { args, .. } => 1 + args.iter().map(nodes).sum::<usize>(),
            Pattern::AcApp { .. } => {
                unreachable!("the ladder generates no AC patterns (compile_structural rejects AC)")
            },
        }
    }
    patterns.iter().map(|(_, pattern)| nodes(pattern)).sum()
}

// ─────────────────────────────────────────────────────────────────────────────────────
// Cell runners.
// ─────────────────────────────────────────────────────────────────────────────────────

/// One Stage-0 phase-split cell: the full eager pipeline under SELF-time span
/// collection.
#[derive(Clone, Debug)]
pub struct SpanCell {
    /// Wall nanoseconds of the whole pipeline sequence (source copy included).
    pub wall_ns: u64,
    /// The per-phase SELF/total span report of the sequence.
    pub report: PhaseSpanReport,
    /// Whether `installed_program_par` produced `Ok` (a fail-closed install is a VALID
    /// cell state — the emission work still ran — recorded, never a DNF).
    pub installed_ok: bool,
}

/// One direct-construction cell (`SetAutomaton::compile_structural` on a ladder pattern
/// set — the W-A(b) entry mode isolating the automaton from the full pipeline).
#[derive(Clone, Copy, Debug)]
pub struct DirectCell {
    /// Wall nanoseconds of `compile_structural` alone (pattern-set construction is
    /// outside the timed region).
    pub wall_ns: u64,
    /// Automaton entries (must equal r — every ladder pattern is AC-free).
    pub entry_count: usize,
    /// Interned automaton states (the sharing observable; reported for the
    /// direct-vs-source parity inspection).
    pub state_count: usize,
    /// Total pattern nodes (H1's regressor).
    pub pattern_nodes: usize,
}

/// The full EAGER pipeline sequence — exactly `CompiledInRhoArtifacts::derive`'s body
/// (source copy, reconstruct, scalar lowering, ruleset compile, planning + emission +
/// install fold), called through the SAME pub pipeline functions. This is the H2
/// CONTROL arm ("today's eager memoized pipeline") and the spans-mode subject; it never
/// consults the artifact cache, so it is invariant to the T-LAZY cache representation.
///
/// Returns `Err` only for a reconstruction failure (the one fallible phase for a
/// well-formed source; the bin records it as a DNF).
fn run_full_pipeline(source: &str) -> Result<(u64, bool), String> {
    let started = Instant::now();
    // Derivation fidelity: `derive` stores the source as its collision-verification
    // key; the copy belongs to the measured first-touch.
    let stored = std::hint::black_box(source.to_string());
    let def = reconstruct_language_def(&stored)
        .map_err(|err| format!("ladder/anchor source did not reconstruct: {err}"))?;
    let lowered = lower_language_def(&def);
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let installed = RhoNetProgram::from_language_def(&def, &lowered)
        .lower_to_par(&def, &lowered)
        .installed_program_par();
    let installed_ok = installed.is_ok();
    // Keep every artifact alive to the clock read (nothing is dropped early or
    // optimized away before the measurement closes).
    std::hint::black_box((&def, &lowered, &ruleset, &installed));
    let wall_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    Ok((wall_ns, installed_ok))
}

/// Run one spans-mode rep on the CALLING thread: the eager pipeline under span
/// collection. The caller wraps this in [`in_fresh_thread`] for cell isolation.
pub fn run_spans_once(source: &str) -> Result<SpanCell, String> {
    begin_phase_span_collection();
    let outcome = run_full_pipeline(source);
    let report = take_phase_span_report()
        .expect("the collection window begun by this rep is still active");
    let (wall_ns, installed_ok) = outcome?;
    Ok(SpanCell { wall_ns, report, installed_ok })
}

/// One eager-control first-touch cell (no spans — the H2v2 control arm's wall clock).
#[derive(Clone, Copy, Debug)]
pub struct EagerCell {
    /// Wall nanoseconds of the whole pipeline sequence.
    pub wall_ns: u64,
    /// Whether `installed_program_par` produced `Ok`.
    pub installed_ok: bool,
}

/// One lazy first-touch cell (a T-LAZY treatment arm's wall clock + its validated cell
/// states).
#[derive(Clone, Copy, Debug)]
pub struct LazyCell {
    /// Wall nanoseconds of the arm's forcing sequence (cache first-touch + accessors).
    pub wall_ns: u64,
    /// The post-arm cell states (`lowered`, `ruleset`, `installed_par`) — the bench-side
    /// witness that BOTH cell states are measured (EM-1).
    pub forced_lowered: bool,
    pub forced_ruleset: bool,
    pub forced_installed_par: bool,
    /// `Some(install outcome)` when the arm forced the installed program, `None` on the
    /// gate-only arm.
    pub installed_ok: Option<bool>,
}

/// Run one eager-control rep on the CALLING thread (no spans): the H2v2 control arm.
pub fn run_eager_control_once(source: &str) -> Result<EagerCell, String> {
    let (wall_ns, installed_ok) = run_full_pipeline(source)?;
    Ok(EagerCell { wall_ns, installed_ok })
}

/// Run one `lazy-gate-only` rep on the CALLING thread: the exec/gate forcing set —
/// cache first touch (reconstruct only, T-LAZY) + `ruleset()`.
pub fn run_lazy_gate_only_once(source: &str) -> Result<LazyCell, String> {
    let started = Instant::now();
    let artifacts = mettail_rholang_codegen::cached_in_rho_artifacts(source)?;
    let ruleset = artifacts.ruleset();
    std::hint::black_box(ruleset);
    let wall_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    Ok(LazyCell {
        wall_ns,
        forced_lowered: artifacts.lowered_forced(),
        forced_ruleset: artifacts.ruleset_forced(),
        forced_installed_par: artifacts.installed_par_forced(),
        installed_ok: None,
    })
}

/// Run one `lazy-force-installed` rep on the CALLING thread: the named forcing arm —
/// the gate-only sequence PLUS `installed_par()` (which forces `lowered()` first,
/// mirroring the old eager derivation).
pub fn run_lazy_force_installed_once(source: &str) -> Result<LazyCell, String> {
    let started = Instant::now();
    let artifacts = mettail_rholang_codegen::cached_in_rho_artifacts(source)?;
    let ruleset = artifacts.ruleset();
    std::hint::black_box(ruleset);
    let installed_ok = artifacts.installed_par().is_ok();
    let wall_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    Ok(LazyCell {
        wall_ns,
        forced_lowered: artifacts.lowered_forced(),
        forced_ruleset: artifacts.ruleset_forced(),
        forced_installed_par: artifacts.installed_par_forced(),
        installed_ok: Some(installed_ok),
    })
}

/// Run one direct-construction rep on the CALLING thread: `compile_structural` on the
/// pre-built pattern set (the set's construction is setup, not measurement).
pub fn run_direct_compile_once(patterns: Vec<(PatternId, Pattern<String>)>) -> DirectCell {
    let pattern_nodes = pattern_node_count(&patterns);
    let started = Instant::now();
    let automaton = SetAutomaton::compile_structural(patterns)
        .expect("the ladder pattern set is AC-free and compiles structurally");
    let wall_ns = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    let entry_count = automaton.view().entry_count();
    let state_count = automaton.view().state_count();
    std::hint::black_box(&automaton);
    DirectCell { wall_ns, entry_count, state_count, pattern_nodes }
}

/// Run `f` on a FRESH thread (fresh `thread_local!` artifact cache ⇒ a true first
/// touch) with a stack of at least 8 MiB (the workspace's `RUST_MIN_STACK` floor;
/// a larger env value is honored), returning its `Send`-safe result.
pub fn in_fresh_thread<T, F>(f: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let stack_bytes = std::env::var("RUST_MIN_STACK")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(0)
        .max(8 * 1024 * 1024);
    std::thread::Builder::new()
        .name("e3-cell".to_string())
        .stack_size(stack_bytes)
        .spawn(f)
        .expect("the E-3 cell thread spawns")
        .join()
        .expect("the E-3 cell thread completes without panicking")
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_rholang_codegen::pipeline_spans::PipelinePhase;

    #[test]
    fn anchors_extract_nonempty_language_bodies() {
        for anchor in ALL_ANCHORS {
            let body = anchor.definition_source();
            assert!(
                body.contains("rewrites"),
                "{} extraction must reach the rewrites block",
                anchor.name()
            );
            // The extraction must land INSIDE the invocation: the body's first
            // non-whitespace content is the language header, not the macro name.
            // (The body may still MENTION `language!` in comments — Calculator does.)
            assert!(
                body.trim_start().starts_with("name:")
                    || body.trim_start().starts_with("//"),
                "{} extraction must start at the language body, got: {:.60}",
                anchor.name(),
                body.trim_start()
            );
        }
    }

    #[test]
    fn lambda_anchor_runs_the_full_pipeline_with_balanced_spans() {
        // The production Lambda body through the spans runner: balanced spans, every
        // phase active, and the re-entrancy signature visible (the ruleset compile
        // re-enters the lowering, so LowerToPar closes MORE than once).
        let cell = in_fresh_thread(|| {
            run_spans_once(AnchorLanguage::Lambda.definition_source())
                .expect("the production Lambda body derives")
        });
        assert_eq!(cell.report.mismatched_spans, 0, "the rep brackets whole derivations");
        for (phase, stats) in cell.report.phases() {
            assert!(stats.activations >= 1, "phase {} must activate", phase.name());
        }
        let lower_to_par = cell.report.stats(PipelinePhase::LowerToPar);
        assert!(
            lower_to_par.activations >= 2,
            "EM-4: the ruleset compile re-enters lower_to_par via rho_net_injection_sites \
             (observed {} activations)",
            lower_to_par.activations
        );
        // The SELF-time partition stays inside the measured wall.
        assert!(cell.report.self_ns_sum() <= cell.wall_ns);
        assert!(cell.installed_ok, "A-S5.1: Lambda's σ-receiver program installs");
    }

    #[test]
    fn ladder_sources_derive_with_one_automaton_entry_per_rule() {
        // Every (shape, alphabet) cell at r = 8: the generated source reconstructs,
        // the ruleset admits ALL r rewrites as automaton entries (no deferrals), and
        // the direct pattern set compiles to the same entry count.
        let cells = [
            (LadderShape::Multi1, LadderAlphabet::Distinct),
            (LadderShape::Multi1, LadderAlphabet::Shared16),
            (LadderShape::Multi3, LadderAlphabet::Distinct),
            (LadderShape::Multi3, LadderAlphabet::Shared16),
            (LadderShape::Mixed, LadderAlphabet::Distinct),
        ];
        for (shape, alphabet) in cells {
            let r = 8;
            let source = ladder_source(r, shape, alphabet);
            let (ruleset, deferred_len) = in_fresh_thread(move || {
                let def = mettail_rholang_codegen::reconstruct_language_def(&source)
                    .expect("the generated ladder source reconstructs");
                let ruleset = compile_in_rho_matching_ruleset(&def);
                let counts =
                    (ruleset.automaton.view().entry_count(), ruleset.automaton.view().state_count());
                (counts, ruleset.deferred.len())
            });
            assert_eq!(
                deferred_len,
                0,
                "{}/{}: every ladder rewrite is an automaton entry",
                shape.name(),
                alphabet.name()
            );
            assert_eq!(
                ruleset.0,
                r,
                "{}/{}: one entry per rule",
                shape.name(),
                alphabet.name()
            );
            let direct = run_direct_compile_once(ladder_patterns(r, shape, alphabet));
            assert_eq!(direct.entry_count, r);
            assert_eq!(
                direct.state_count,
                ruleset.1,
                "{}/{}: the direct pattern set and the source-derived automaton intern \
                 the same state set (the two entry modes compile the SAME patterns)",
                shape.name(),
                alphabet.name()
            );
        }
    }

    #[test]
    fn multi_shape_state_sharing_matches_the_track_b_formula() {
        // The multi_rule sharing law (workloads.rs §(vii)): state_count = r + s + 1 for
        // r distinct roots over one shared Sˢ(x) chain.
        for (shape, s) in [(LadderShape::Multi1, 1), (LadderShape::Multi3, 3)] {
            let r = 8;
            let direct = run_direct_compile_once(ladder_patterns(r, shape, LadderAlphabet::Distinct));
            assert_eq!(direct.entry_count, r);
            assert_eq!(
                direct.state_count,
                r + s + 1,
                "{}: the Sˢ chain interns to ONE shared state set",
                shape.name()
            );
            // Regressor sanity: r rules × (1 root + s chain + 1 var) nodes.
            assert_eq!(direct.pattern_nodes, r * (s + 2));
        }
    }

    #[test]
    fn shared16_keeps_rules_pairwise_distinct() {
        // r > 16 under the shared alphabet: entries stay one-per-rule (depth
        // distinguishes same-root rules).
        let r = 40;
        let direct =
            run_direct_compile_once(ladder_patterns(r, LadderShape::Multi1, LadderAlphabet::Shared16));
        assert_eq!(direct.entry_count, r);
    }

    #[test]
    fn mixed_shape_rejects_the_alphabet_axis() {
        assert!(validate_ladder_cell(8, LadderShape::Mixed, LadderAlphabet::Shared16).is_err());
    }

    #[test]
    fn h2_arms_pin_their_cell_states() {
        // EM-1: BOTH cell states are measured — the gate-only arm leaves the emission
        // cells unforced; the forcing arm forces everything (installed_par forces the
        // lowering first). Small ladder source so the pin is cheap.
        let source = ladder_source(8, LadderShape::Multi1, LadderAlphabet::Distinct);
        let gate_source = source.clone();
        let gate = in_fresh_thread(move || {
            run_lazy_gate_only_once(&gate_source).expect("the ladder source derives")
        });
        assert!(gate.forced_ruleset, "the gate arm forces the ruleset");
        assert!(!gate.forced_lowered, "the gate arm must not force the lowering (EM-10)");
        assert!(!gate.forced_installed_par, "the gate arm must not force the emission");
        assert!(gate.installed_ok.is_none());

        let force = in_fresh_thread(move || {
            run_lazy_force_installed_once(&source).expect("the ladder source derives")
        });
        assert!(force.forced_ruleset && force.forced_lowered && force.forced_installed_par);
        assert_eq!(
            force.installed_ok,
            Some(true),
            "the all-base-rewrite ladder language installs"
        );
    }
}

/// Capitalize the first ASCII letter of a CLI name (for the generated language name).
fn capitalized(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
        None => String::new(),
    }
}
