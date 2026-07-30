use super::*;

pub(crate) fn collect_refinement_downcast_rule_labels(spec: &LanguageSpec) -> HashSet<String> {
    let refinement_base_by_name: HashMap<&str, &str> = spec
        .refinement_types
        .iter()
        .map(|r| (r.name.as_str(), r.base_category.as_str()))
        .collect();

    spec.rules
        .iter()
        .filter_map(|rule| {
            let base_category = refinement_base_by_name.get(rule.category.as_str())?;
            if !rule.is_cast
                || rule.cast_source_category.as_deref() != Some(*base_category)
                || rule.syntax.len() != 1
            {
                return None;
            }

            match &rule.syntax[0] {
                SyntaxItemSpec::NonTerminal { category, .. }
                    if category.as_str() == *base_category =>
                {
                    Some(rule.label.clone())
                },
                _ => None,
            }
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// DB03: Parallel analysis phase execution
// ══════════════════════════════════════════════════════════════════════════════

/// Result of compile-time refinement type analysis.
#[derive(Debug, Clone, Default)]
pub struct RefinementAnalysisResult {
    /// Refinement types whose predicate is unsatisfiable (RT01).
    pub unsatisfiable: Vec<(String, String)>, // (type_name, reason)
    /// Refinement types whose predicate is tautological (RT02).
    pub tautological: Vec<(String, String)>, // (type_name, reason)
    /// Pairs of refinement types with empty intersection (RT03).
    pub empty_intersections: Vec<(String, String, String)>, // (type_a, type_b, reason)
    /// Subtype relationships detected between refinement types (RT04).
    pub subtype_pairs: Vec<(String, String)>, // (sub, super)
    /// Decidability tier for each refinement type's predicate (RT05).
    pub decidability_tiers: Vec<(String, String)>, // (type_name, tier_description)
    /// Refinement types that shadow a base type name (RT06).
    pub name_shadows: Vec<(String, String)>, // (refinement_name, base_type_name)
    /// SFA dispatch analysis: disjointness, subsumption, overlap (RT10).
    pub dispatch_analysis: Option<crate::type_system::RefinementDispatchAnalysis>,
    /// Per-category structural inhabitation witnesses, surfaced as RT-note hints
    /// (`(category, witness_term_repr)`). Populated from
    /// `structural_types::structural_verdict().witnesses` (a minimal inhabiting
    /// term per inhabited category, rendered to a string).
    pub structural_witnesses: Vec<(String, String)>,
    /// Casts `r : src → tgt` whose pre-image ∩ source-category is empty — the
    /// cast can never fire (OSLF transducer dead-cast detection). Each entry is
    /// `(cast_rule_label, reason)`. Populated from
    /// [`crate::sym_tree_transducer::analyze_from_bundle`]'s `dead_casts`.
    pub dead_casts: Vec<(String, String)>,
}

/// Collected results from the mathematical analysis phase.
///
/// All fields correspond to the individual analysis results that the lint
/// layer and downstream pipeline stages consume. Feature-gated analyses
/// are behind `#[cfg]` attributes matching the analysis module gates.
///
/// This struct allows returning all results from both the parallel and
/// sequential execution paths without needing uninitialized variable
/// assignments inside closures.
///
/// `Debug` is derived so that #164's equivalence guard can compare the parallel
/// and sequential paths **as whole values**. Comparing the struct rather than a
/// hand-written list of its fields is what makes the guard total: a field added
/// here is compared automatically, with nothing to remember to extend.
#[derive(Debug)]
pub(crate) struct MathAnalysisResults {
    /// Number of analysis phases that were executed (for I19 diagnostic).
    pub phase_count: u32,

    // ── Always-on analyses ──
    pub safety_result:
        Option<crate::verify::SafetyResult<crate::automata::semiring::BooleanWeight>>,
    pub cegar_result: Option<crate::cegar::CegarLog>,
    pub algebraic_result: Option<crate::algebraic::AlgebraicSummary>,

    // ── Feature-gated analyses ──
    pub confluence_result: Option<crate::confluence::ConfluenceAnalysis>,
    pub termination_result: Option<crate::termination::TerminationResult>,
    pub vpa_result: Option<crate::vpa::VpaAnalysis>,
    pub wta_result: Option<crate::tree_automaton::WtaAnalysis>,
    pub ewpds_result: Option<crate::ewpds::EwpdsAnalysis>,
    pub ara_result: Option<crate::ara::AraAnalysis>,
    pub petri_result: Option<crate::petri::PetriAnalysis>,
    pub nominal_result: Option<crate::nominal::NominalAnalysis>,
    pub alternating_result: Option<crate::alternating::AlternatingAnalysis>,
    /// OSLF Phase-4 `.1`: bisimulation partition computed by
    /// [`crate::bisimulation::analyze_from_bundle`] (Kanellakis–Smolka /
    /// Paige–Tarjan refinement over one LTS). Drop-in for `alternating_result`
    /// at the N06-ISO / A3 codegen seams — the agreement gate proves parity.
    pub bisimulation_result: Option<crate::bisimulation::BisimulationAnalysis>,
    /// OSLF Phase-6 `.1`: Hindley-Milner base-sort consistency over the grammar's
    /// constructor arrow types, computed by
    /// [`crate::hindley_milner::analyze_from_bundle`]. Feeds the HM01 lint only
    /// (no codegen seam). On every well-formed grammar its `sort_mismatches` is
    /// empty (inert).
    pub hindley_result: Option<crate::hindley_milner::HmInferenceAnalysis>,
    pub ltl_results: Option<Vec<crate::ltl::LtlCheckResult>>,
    pub provenance_result: Option<crate::provenance::ProvenanceAnalysis>,
    pub cra_result: Option<crate::cra::CraAnalysis>,
    pub morphism_result: Option<crate::morphism::MorphismCheck>,
    pub kat_result: Option<crate::kat::KatCheck>,
    // ── Advanced automata analyses ──
    pub symbolic_result: Option<crate::symbolic::SymbolicAnalysis>,
    pub buchi_result: Option<crate::buchi::BuchiAnalysis>,
    pub mso_result: Option<crate::weighted_mso::MsoAnalysis>,
    pub probabilistic_result: Option<crate::probabilistic::ProbabilisticAnalysis>,
    pub register_result: Option<crate::register_automata::RegisterAnalysis>,
    pub parity_tree_result: Option<crate::parity_tree::ParityTreeAnalysis>,
    pub multi_tape_result: Option<crate::multi_tape::MultiTapeAnalysis>,
    pub multiset_result: Option<crate::multiset_automata::MultisetAnalysisResult>,
    pub two_way_result: Option<crate::two_way_transducer::TwoWayAnalysis>,
    pub sft_result: Option<crate::sft::SftAnalysis>,

    // ── E-graph equality saturation ──
    pub egraph_result: Option<crate::egraph::EGraphAnalysis>,

    // ── Constraint theory analyses ──
    pub presburger_result: Option<crate::presburger::PresburgerAnalysis>,
    pub unification_result: Option<crate::unification::UnificationAnalysis>,
    pub lattice_result: Option<crate::lattice_theory::LatticeAnalysis>,

    // ── Refinement type analysis ──
    pub refinement_analysis: Option<RefinementAnalysisResult>,
}

/// Count the number of analysis phases based on enabled features.
///
/// Always-on: safety, cegar, algebraic (3). Each feature-gated
/// analysis adds 1 (trs-analysis adds 2 for confluence + termination).
pub(crate) fn count_analysis_phases() -> u32 {
    #[allow(unused_mut)] // mut needed when feature flags add to count
    let mut count = 3u32; // safety, cegar, algebraic
    {
        count += 2;
    } // confluence, termination
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    } // buchi analysis (separate from LTL)
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    {
        count += 1;
    }
    count
}

// ══════════════════════════════════════════════════════════════════════════════
// DB03: recovering an analysis thread's panic payload  (#141 Stage 4)
// ══════════════════════════════════════════════════════════════════════════════

/// The text of a panic payload, for the two payload types `panic!` can produce.
///
/// `panic!("literal")` boxes a `&'static str`; `panic!("{fmt}", …)` boxes a
/// `String`. Anything else — `std::panic::panic_any` with a custom type — has no
/// text, and saying so is more honest than pretending the panic was silent.
///
/// Written as a `match` chain rather than `if let` so the discrimination is on
/// the payload's *type*, which is what `downcast_ref` actually decides.
pub(super) fn panic_payload_text(payload: &(dyn std::any::Any + Send)) -> &str {
    match payload.downcast_ref::<&'static str>() {
        Some(literal) => literal,
        None => match payload.downcast_ref::<String>() {
            Some(formatted) => formatted.as_str(),
            None => "<panic payload is neither `&str` nor `String`>",
        },
    }
}

/// Join one scoped analysis thread, recovering the **original** panic payload
/// into the pipeline's own diagnostic channel before letting the unwind
/// continue.
///
/// # Why this exists — the defect it replaces
///
/// Every one of the 32 analyses below used to be joined with
///
/// ```text
/// h_symbolic.join().expect("DB03: symbolic analysis thread panicked")
/// ```
///
/// [`std::thread::ScopedJoinHandle::join`] returns
/// `Err(Box<dyn Any + Send>)` **carrying the original panic message**, and
/// [`Result::expect`] throws that box away and panics with its own string
/// instead. The analysis modules behind these handles contain ~114 authored
/// refusals between them; the payload is the *only* value that says which one
/// fired. `expect` discarded exactly the discriminating information and kept
/// only the module name, which the handle already encodes.
///
/// # Two measured facts that bound what this can and cannot do
///
/// 1. ⚠ **On this workspace's `dev` profile the join is never reached.**
///    `[profile.dev] codegen-backend = "cranelift"` (root `Cargo.toml`), and
///    cg_clif emits no catch pads, so the unwind out of a scoped thread cannot
///    become an `Err`: the process dies with `fatal runtime error: failed to
///    initiate panic, error 5`. This was measured directly on 2026-07-29 — a
///    probe printed its outcome marker in *neither* the `Ok` nor the `Err` arm.
///    The 32 `.expect` strings this replaces were therefore **dead text**, and
///    so, on `dev`, is the `Err` arm below. It is live on any LLVM-backed
///    profile — `[profile.release]`, and CI's release jobs.
/// 2. **The panic is not silent even when this code never runs.** With no hook
///    installed, `std`'s default handler still prints
///    `thread '<unnamed>' panicked at <file>:<line>: <payload>` from the
///    panicking thread. What the recovery below adds is not audibility; it is
///    turning that stderr line into a **value inside the pipeline's diagnostic
///    stream**, tagged with the grammar being expanded and the analysis that
///    failed, in the same channel and format as every other pipeline
///    diagnostic. Interleaved stderr from 32 concurrent threads does not say
///    *which grammar* was being compiled; `I22` does.
///
/// # Why it re-raises rather than substituting a value
///
/// A panicked analysis produced no result. Returning `T::default()` would put a
/// fabricated answer into [`MathAnalysisResults`] and let codegen proceed on it
/// — the same defect as `BpLookup::empty()`, fixed in `9911d27d`: *a wrong
/// answer, not a degraded one*. [`std::panic::resume_unwind`] continues the
/// original unwind with the original payload, adding no second message to
/// stderr; the diagnostic already carries the text. This is not a
/// `catch_unwind` — it installs no landing pad and asserts no panic, so it is
/// outside the scope of `dovetail/tests/panic_expectation_gate.rs`.
fn join_analysis<T>(
    handle: std::thread::ScopedJoinHandle<'_, T>,
    analysis: &'static str,
    grammar_name: &str,
) -> T {
    match handle.join() {
        Ok(value) => value,
        Err(payload) => {
            crate::lint::emit_diagnostic(&analysis_panic_diagnostic(
                analysis,
                grammar_name,
                panic_payload_text(&*payload),
            ));
            std::panic::resume_unwind(payload)
        },
    }
}

/// Build the `I22` diagnostic for a recovered analysis-thread panic.
///
/// Split out of [`join_analysis`] so that the *message* — the only part of this
/// repair that carries information — can be asserted without a panicking
/// thread. Under `[profile.dev]`'s cranelift backend a scoped thread's panic
/// never becomes a joinable `Err` at all (see [`join_analysis`]'s note 1), so a
/// test that spawned one would abort the whole test binary rather than exercise
/// this code. Constructing the diagnostic directly asserts exactly the part that
/// `Result::expect` used to throw away.
///
/// ⚠ The severity is [`LintSeverity::Error`] and that is load-bearing:
/// [`crate::lint::emit_diagnostic`] silently drops anything below
/// `PRATTAIL_LINT_LEVEL`, whose default is `Warning`. A `Note` here would
/// re-create the defect being repaired — the payload recovered and then
/// discarded, one channel further along.
pub(super) fn analysis_panic_diagnostic(
    analysis: &str,
    grammar_name: &str,
    payload_text: &str,
) -> crate::lint::LintDiagnostic {
    crate::lint::LintDiagnostic {
        id: DiagnosticId::I22,
        name: "analysis-thread-panicked",
        severity: crate::lint::LintSeverity::Error,
        category: None,
        rule: None,
        message: format!("DB03: the {analysis} thread panicked: {payload_text}"),
        hint: Some(format!(
            "the text after the colon is the panic's own payload, recovered from the join; it \
             names the site inside the {analysis} that refused"
        )),
        grammar_name: Some(grammar_name.to_string()),
        source_location: None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// #164: the ANALYSIS SPAWN LEDGER — making the spawn decision observable
// ══════════════════════════════════════════════════════════════════════════════

/// Number of dispatch modules [`crate::predicate_dispatch`] can distinguish.
///
/// Indexes both arrays in [`AnalysisSpawnLedger`]. Read from
/// [`crate::predicate_dispatch::PredicateSignature::NUM_MODULES`] rather than
/// written down, so adding a module cannot leave the ledger short a slot.
const DISPATCH_MODULE_SLOTS: usize =
    crate::predicate_dispatch::PredicateSignature::NUM_MODULES as usize;

/// What [`run_math_analyses_parallel`] did with its analyses on **this thread's
/// most recent call**: how many became OS threads, how many were refused before
/// becoming one, and — per dispatch module — how many gated sites asked the
/// plan versus how many of those questions were answered "yes".
///
/// # Why a ledger rather than a comment
///
/// The claim this type exists to make checkable is *"an analysis the dispatch
/// plan does not want is never created"*. That claim is about a **thread that
/// does not exist**, which no assertion on [`MathAnalysisResults`] can see: a
/// skipped analysis and a ran-and-declined analysis leave the same `None` in the
/// same field. The ledger is the only place where the difference is a value.
///
/// # Why per-module arrays, and not just two totals
///
/// A total says *how many* were skipped; it cannot say the **right ones** were.
/// `consulted[m]` and `created[m]` let a test re-derive the whole spawn decision
/// from [`crate::predicate_dispatch::GrammarDispatchPlan::requires`] and compare,
/// with no hand-maintained list of which analysis is gated on which module — the
/// mechanism reports what it actually asked. `u8` per slot is ample: the largest
/// entry is 2 (`Awa` gates both `alternating` and `bisimulation`).
///
/// # Why thread-local and not atomic
///
/// Every increment happens on the thread that owns the `std::thread::Scope` —
/// i.e. the caller — because `Scope::spawn` is called from there. A thread-local
/// is therefore *exact per call* and immune to the interference a process-wide
/// counter would suffer under `cargo test`'s concurrent harness, where several
/// tests call this function at once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnalysisSpawnLedger {
    /// Analyses handed to `std::thread::Scope::spawn` — one OS thread each.
    pub spawned: u32,
    /// Dispatch-gated analyses whose module the plan does not require, and which
    /// therefore never became a thread. Was `0` before #164, when the gate sat
    /// *inside* the closure and every refusal still cost a thread.
    pub elided: u32,
    /// `consulted[m as usize]` — gated spawn sites that asked the plan about
    /// module `m`. Summed over `m`, the number of gated sites (16).
    pub consulted: [u8; DISPATCH_MODULE_SLOTS],
    /// `created[m as usize]` — of those consultations, how many spawned. Equals
    /// `consulted[m]` when the plan requires `m`, and `0` when it does not;
    /// nothing else is a correct hoist.
    pub created: [u8; DISPATCH_MODULE_SLOTS],
}

impl AnalysisSpawnLedger {
    /// The ledger before any analysis has been considered.
    pub const EMPTY: Self = Self {
        spawned: 0,
        elided: 0,
        consulted: [0; DISPATCH_MODULE_SLOTS],
        created: [0; DISPATCH_MODULE_SLOTS],
    };

    /// Total analyses considered — spawned plus elided.
    ///
    /// Invariant, and the non-vacuity floor for #164: this is the **constant**
    /// number of analyses (32) whatever the grammar. A "fix" that dropped an
    /// analysis outright, rather than declining to thread it, would lower this.
    pub fn considered(&self) -> u32 {
        self.spawned + self.elided
    }

    /// Number of dispatch-gated spawn sites evaluated, `Σ_m consulted[m]`.
    pub fn gated_sites(&self) -> u32 {
        self.consulted.iter().copied().map(u32::from).sum()
    }
}

thread_local! {
    /// The calling thread's ledger, reset at the top of every
    /// [`run_math_analyses_parallel`] so it always describes the **latest**
    /// grammar analysed on this thread. One `Cell` write per spawn decision.
    static SPAWN_LEDGER: std::cell::Cell<AnalysisSpawnLedger> =
        const { std::cell::Cell::new(AnalysisSpawnLedger::EMPTY) };
}

/// The spawn ledger for the most recent [`run_math_analyses_parallel`] on the
/// calling thread. [`AnalysisSpawnLedger::EMPTY`] if there has not been one.
///
/// ⚠ "Most recent" is load-bearing, and reading it without
/// [`reset_analysis_spawn_ledger`] is a trap: a grammar with fewer than three
/// categories takes [`run_math_analyses_sequential`] instead, spawns nothing, and
/// leaves the *previous* grammar's ledger in place. An observer that walks a list
/// of grammars will then attribute one grammar's threads to another. Reset before
/// each observation and an empty ledger means "this grammar spawned nothing",
/// which is the answer you wanted.
pub fn analysis_spawn_ledger() -> AnalysisSpawnLedger {
    SPAWN_LEDGER.with(std::cell::Cell::get)
}

/// Clear the calling thread's spawn ledger.
///
/// For observers that read [`analysis_spawn_ledger`] once per grammar: it is the
/// only way to tell "spawned nothing" from "did not run the parallel path at
/// all", because both leave `spawned` unchanged. [`run_math_analyses_parallel`]
/// resets on entry itself, so production code never needs this.
pub fn reset_analysis_spawn_ledger() {
    SPAWN_LEDGER.with(|cell| cell.set(AnalysisSpawnLedger::EMPTY));
}

/// Record that an analysis became a thread. `module` is `Some` for a
/// dispatch-gated analysis and `None` for one that always runs.
fn record_analysis_spawn(module: Option<crate::predicate_dispatch::ModuleId>) {
    SPAWN_LEDGER.with(|cell| {
        let mut ledger = cell.get();
        ledger.spawned += 1;
        if let Some(module) = module {
            let slot = module as usize;
            ledger.consulted[slot] += 1;
            ledger.created[slot] += 1;
        }
        cell.set(ledger);
    });
}

/// Record that a dispatch-gated analysis was refused **before** any thread
/// existed — the whole point of #164.
fn record_analysis_elision(module: crate::predicate_dispatch::ModuleId) {
    SPAWN_LEDGER.with(|cell| {
        let mut ledger = cell.get();
        ledger.elided += 1;
        ledger.consulted[module as usize] += 1;
        cell.set(ledger);
    });
}

/// Spawn an analysis that runs for **every** grammar, tallying it.
///
/// A thin wrapper over `std::thread::Scope::spawn` with the same signature, so
/// the ledger's `spawned` count is derived from the mechanism rather than
/// maintained beside it: there is no way to add an unconditional analysis that
/// the ledger does not see, short of calling `s.spawn` directly.
fn spawn_analysis<'scope, 'env, F, T>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    body: F,
) -> std::thread::ScopedJoinHandle<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    record_analysis_spawn(None);
    scope.spawn(body)
}

/// Spawn a dispatch-gated analysis **only if the plan requires its module**.
///
/// # The defect this replaces (#164)
///
/// Sixteen of the 32 analyses used to be written
///
/// ```text
/// let h_vpa = s.spawn(|| {
///     if !dispatch_plan.requires(ModuleId::Vpa) { return None; }
///     crate::vpa::analyze_from_bundle(categories, all_syntax)
/// });
/// ```
///
/// — the gate on the *wrong side of the spawn*. When the answer was "no" the
/// thread was still created, scheduled, entered, and joined, all to produce the
/// `None` the caller could have had for free. `dispatch_plan` is built **before**
/// the `std::thread::scope` (it must be, for the closures to borrow it), so the
/// answer was already in hand at the spawn site; nothing forced the question
/// inside.
///
/// # Why the return type is `Option<ScopedJoinHandle<'_, Option<T>>>`
///
/// "Never spawned" is `None` at the handle, and [`join_analysis_if_spawned`]
/// maps that to `None` at the result — the *same value* the closure used to
/// return. The equivalence is therefore a property of the types, not of a test:
/// there is no way for a consumer to distinguish *never-ran* from
/// *ran-and-returned-`None`*, because by the time a consumer sees anything, both
/// are the identical `Option<T>`.
fn spawn_analysis_if_required<'scope, 'env, F, T>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    plan: &crate::predicate_dispatch::GrammarDispatchPlan,
    module: crate::predicate_dispatch::ModuleId,
    body: F,
) -> Option<std::thread::ScopedJoinHandle<'scope, Option<T>>>
where
    F: FnOnce() -> Option<T> + Send + 'scope,
    T: Send + 'scope,
{
    match plan.requires(module) {
        true => {
            record_analysis_spawn(Some(module));
            Some(scope.spawn(body))
        },
        false => {
            record_analysis_elision(module);
            None
        },
    }
}

/// Join a handle from [`spawn_analysis_if_required`], collapsing "was never
/// spawned" to the `None` that the in-closure gate used to return.
fn join_analysis_if_spawned<T>(
    handle: Option<std::thread::ScopedJoinHandle<'_, Option<T>>>,
    analysis: &'static str,
    grammar_name: &str,
) -> Option<T> {
    match handle {
        Some(handle) => join_analysis(handle, analysis, grammar_name),
        None => None,
    }
}

/// Environment variable that prints one ledger line per grammar to stderr.
///
/// Off by default; a single `var_os` read per grammar expansion (54 per full
/// workspace build) is the entire cost. It is what turns the #164 claim into a
/// measurement over the *real* 54 grammars rather than over test fixtures:
///
/// ```text
/// PRATTAIL_ANALYSIS_SPAWN_LEDGER=1 cargo check -p languages --all-targets 2>&1 \
///   | grep analysis-spawn-ledger
/// ```
pub const SPAWN_LEDGER_ENV: &str = "PRATTAIL_ANALYSIS_SPAWN_LEDGER";

/// Emit the per-grammar ledger line when [`SPAWN_LEDGER_ENV`] is set.
///
/// One space-separated `key=value` line, so a build log can be reduced with
/// `grep`/`awk` and totalled without a parser.
fn report_spawn_ledger(
    grammar_name: &str,
    plan: &crate::predicate_dispatch::GrammarDispatchPlan,
    ledger: AnalysisSpawnLedger,
) {
    if std::env::var_os(SPAWN_LEDGER_ENV).is_none() {
        return;
    }
    let required: Vec<String> = crate::predicate_dispatch::ModuleId::ALL
        .iter()
        .filter(|module| plan.requires(**module))
        .map(|module| format!("{module:?}"))
        .collect();
    eprintln!(
        "prattail: analysis-spawn-ledger grammar={grammar_name} considered={} spawned={} \
         elided={} gated={} signature=0x{:04X} required={}",
        ledger.considered(),
        ledger.spawned,
        ledger.elided,
        ledger.gated_sites(),
        plan.aggregate_signature.raw(),
        required.join(","),
    );
}

/// Run all mathematical analyses in parallel using `std::thread::scope`.
///
/// All inputs are borrowed references that are `Send + Sync`, allowing
/// scoped threads to share them without cloning. Each analysis runs in
/// its own thread; results are joined when the scope exits.
///
/// # Panics
///
/// Propagates panics from any analysis thread via [`join_analysis`], which
/// first records the recovered payload as an `I22` diagnostic naming the
/// grammar and the analysis.
///
/// # #164: the dispatch gate is at the spawn site, not inside the closure
///
/// There are 32 analyses. Sixteen run for every grammar; the other sixteen are
/// **dispatch-gated** and go through [`spawn_analysis_if_required`], which asks
/// `dispatch_plan.requires(…)` *before* `s.spawn` and returns no handle at all
/// when the answer is "no". Until #164 all sixteen asked the same question
/// *inside* the spawned closure and returned `None`, so a refusal still cost a
/// thread creation, a schedule, an entry and a join.
///
/// Every spawn decision is tallied in [`AnalysisSpawnLedger`], readable through
/// [`analysis_spawn_ledger`] and printable per grammar with
/// [`SPAWN_LEDGER_ENV`]; `prattail/src/pipeline/analysis.rs`'s
/// `spawn_ledger_guards` tests re-derive the whole decision from the plan and
/// compare.
///
/// ⚠ Two of the sixteen gates can never refuse.
/// [`crate::predicate_dispatch::PredicateSignature::new`] seeds every signature
/// with `BASE = M1_SYMBOLIC | M10_MSO`, so `requires(Symbolic)` and
/// `requires(Mso)` are true for *every* grammar. The floor on the spawn count is
/// therefore **18** (16 ungated + `symbolic` + `mso`), not 16.
pub(crate) fn run_math_analyses_parallel(
    bundle: &ParserBundle,
    wpds_analysis: Option<&crate::wpds::WpdsAnalysis>,
) -> MathAnalysisResults {
    let all_syntax = &bundle.all_syntax;
    let categories = &bundle.categories;
    let wpds_ref = wpds_analysis;
    // Carried into every `join_analysis` so a recovered payload names the
    // grammar it belongs to: 54 languages expand in one `cargo build`, and 32
    // threads interleave their stderr within each one.
    let grammar_name = bundle.grammar_name.as_str();

    // Pre-build petri category info outside the thread scope.
    let petri_cats: Vec<crate::wpds::WpdsCategoryInfo> = categories
        .iter()
        .map(|c| crate::wpds::WpdsCategoryInfo {
            name: c.name.clone(),
            is_primary: c.is_primary,
        })
        .collect();

    let phase_count = count_analysis_phases();

    // Phase 7A: Predicate dispatch classification. Before the thread scope both
    // because the spawned closures borrow it AND — #164 — because the spawn
    // decisions below read it.
    let dispatch_plan = crate::predicate_dispatch::classify_grammar(all_syntax, categories);

    // #164: the ledger describes ONE call, so start from zero. Reset here rather
    // than in the caller so no caller can forget.
    reset_analysis_spawn_ledger();
    let plan = &dispatch_plan;
    use crate::predicate_dispatch::ModuleId;

    #[allow(unused_mut)] // mut needed when egraph feature adds post-scope mutation
    let mut results = std::thread::scope(|s| {
        // Phase 1: TRS (no dependencies)
        let h_confluence =
            spawn_analysis(s, || crate::confluence::analyze_from_bundle(all_syntax, 100));
        let h_termination =
            spawn_analysis(s, || crate::termination::analyze_from_bundle(all_syntax));

        // Phase 2: Automata (no dependencies)
        let h_vpa = spawn_analysis_if_required(s, plan, ModuleId::Vpa, || {
            crate::vpa::analyze_from_bundle(categories, all_syntax)
        });
        let h_wta = spawn_analysis(s, || {
            crate::tree_automaton::analyze_from_bundle(categories, all_syntax)
        });

        // Phase 3: WPDS-dependent
        let h_safety = spawn_analysis(s, || {
            wpds_ref.and_then(|wa| crate::verify::verify_from_bundle(wa, categories, all_syntax))
        });
        let h_cegar =
            spawn_analysis(s, || wpds_ref.and_then(|wa| crate::cegar::cegar_from_bundle(wa)));
        let h_algebraic =
            spawn_analysis(s, || wpds_ref.map(|wa| crate::algebraic::analyze_from_bundle(wa)));

        let h_ewpds = spawn_analysis(s, || {
            wpds_ref.and_then(|wa| crate::ewpds::extend_from_bundle(wa, all_syntax))
        });
        let h_ara = spawn_analysis(s, || {
            wpds_ref.map(|wa| crate::ara::analyze_from_bundle(wa, all_syntax))
        });

        // Phase 4: Concurrency (no dependencies)
        let h_petri =
            spawn_analysis(s, || Some(crate::petri::analyze_from_bundle(all_syntax, &petri_cats)));
        let h_nominal = spawn_analysis(s, || Some(crate::nominal::analyze_from_bundle(all_syntax)));
        // Phase 5: Temporal
        let h_ltl = spawn_analysis(s, || wpds_ref.map(|wa| crate::ltl::check_from_bundle(wa)));
        let h_provenance =
            spawn_analysis(s, || crate::provenance::track_from_bundle(all_syntax, categories));
        let h_cra = spawn_analysis(s, || crate::cra::analyze_from_bundle(all_syntax));

        // Phase 6: Meta
        let h_morphism =
            spawn_analysis(s, || crate::morphism::check_from_bundle(all_syntax, categories));
        let h_kat = spawn_analysis(s, || {
            wpds_ref.and_then(|wa| crate::kat::check_from_bundle(wa, all_syntax))
        });

        // Phase 7B: Advanced automata — #164: the dispatch gate is evaluated HERE,
        // at the spawn site, so an analysis the plan does not require never
        // becomes a thread. `Symbolic` and `Mso` are `PredicateSignature::BASE`
        // and so are required by every grammar; the other gates can refuse.
        let h_symbolic = spawn_analysis_if_required(s, plan, ModuleId::Symbolic, || {
            Some(crate::symbolic::analyze_from_bundle(all_syntax, categories))
        });
        let h_buchi = spawn_analysis_if_required(s, plan, ModuleId::Buchi, || {
            Some(crate::buchi::analyze_from_bundle(all_syntax, categories))
        });
        let h_mso = spawn_analysis_if_required(s, plan, ModuleId::Mso, || {
            Some(crate::weighted_mso::analyze_from_bundle(all_syntax, categories))
        });
        let h_probabilistic = spawn_analysis_if_required(s, plan, ModuleId::Probabilistic, || {
            Some(crate::probabilistic::analyze_from_bundle(all_syntax, categories))
        });
        let h_register = spawn_analysis_if_required(s, plan, ModuleId::Register, || {
            Some(crate::register_automata::analyze_from_bundle(all_syntax, categories))
        });
        // OSLF Phase 5 `.1`: routes to the live recursive-predicate decision path
        // (which lowers each `letprop` predicate through
        // `letprop::letprop_to_pata` + `check_emptiness`). The `ParityTree` gate
        // needs recursion AND ≥3-child branching, so on most grammars this
        // analysis is now not even spawned.
        let h_parity_tree = spawn_analysis_if_required(s, plan, ModuleId::ParityTree, || {
            Some(crate::parity_tree::analyze_recursive_predicates(all_syntax, categories))
        });
        let h_multi_tape = spawn_analysis_if_required(s, plan, ModuleId::MultiTape, || {
            Some(crate::multi_tape::analyze_from_bundle(all_syntax, categories))
        });
        let h_multiset = spawn_analysis_if_required(s, plan, ModuleId::Multiset, || {
            Some(crate::multiset_automata::analyze_from_bundle(all_syntax, categories))
        });
        let h_two_way = spawn_analysis_if_required(s, plan, ModuleId::TwoWay, || {
            Some(crate::two_way_transducer::analyze_from_bundle(all_syntax, categories))
        });
        let h_sft = spawn_analysis_if_required(s, plan, ModuleId::Sft, || {
            Some(crate::sft::analyze_from_bundle(all_syntax, categories))
        });
        let h_alternating = spawn_analysis_if_required(s, plan, ModuleId::Awa, || {
            Some(crate::alternating::analyze_from_bundle(all_syntax, categories))
        });
        // OSLF Phase-4 `.1`: parallel bisimulation pass gated by the SAME `Awa`
        // dispatch predicate `alternating` uses — the live supersede at the
        // N06-ISO / A3 seams reads this. `Awa` is therefore the one module
        // consulted TWICE per grammar, which is why the ledger counts
        // consultations per module rather than storing a set.
        let h_bisimulation = spawn_analysis_if_required(s, plan, ModuleId::Awa, || {
            Some(crate::bisimulation::analyze_from_bundle(all_syntax, categories))
        });
        // OSLF Phase-6 `.1`: Hindley-Milner base-sort consistency. UNCONDITIONAL
        // within the cfg — HM applies to ALL grammars (no `dispatch_plan` gate),
        // mirroring the unconditional refinement-sync block rather than the
        // dispatch-gated automata spawns. Inert on every well-formed grammar
        // (empty `sort_mismatches`).
        let h_hindley = spawn_analysis(s, || {
            Some(crate::hindley_milner::analyze_from_bundle(all_syntax, categories))
        });

        // Phase 8: Constraint theory analyses
        let h_presburger = spawn_analysis_if_required(s, plan, ModuleId::LinearArithmetic, || {
            Some(crate::presburger::analyze_from_bundle(all_syntax))
        });
        let h_unification = spawn_analysis_if_required(s, plan, ModuleId::Unification, || {
            Some(crate::unification::analyze_from_bundle(all_syntax))
        });
        let h_lattice = spawn_analysis_if_required(s, plan, ModuleId::SubtypeLattice, || {
            Some(crate::lattice_theory::analyze_from_bundle(all_syntax, categories))
        });

        // Phase 8B: Refinement type analysis (synchronous — lightweight syntactic checks)
        let refinement_analysis_result: Option<RefinementAnalysisResult> = {
            if bundle.refinement_types.is_empty() {
                None
            } else {
                Some(analyze_refinement_types(bundle))
            }
        };

        // ── Collect results ──────────────────────────────────────────────
        MathAnalysisResults {
            phase_count,
            safety_result: join_analysis(h_safety, "safety verification", grammar_name),
            cegar_result: join_analysis(h_cegar, "CEGAR refinement", grammar_name),
            algebraic_result: join_analysis(h_algebraic, "algebraic analysis", grammar_name),
            confluence_result: join_analysis(h_confluence, "confluence analysis", grammar_name),
            termination_result: join_analysis(h_termination, "termination analysis", grammar_name),
            vpa_result: join_analysis_if_spawned(h_vpa, "VPA analysis", grammar_name),
            wta_result: join_analysis(h_wta, "WTA analysis", grammar_name),
            ewpds_result: join_analysis(h_ewpds, "EWPDS analysis", grammar_name),
            ara_result: join_analysis(h_ara, "ARA analysis", grammar_name),
            petri_result: join_analysis(h_petri, "Petri net analysis", grammar_name),
            nominal_result: join_analysis(h_nominal, "nominal analysis", grammar_name),
            alternating_result: join_analysis_if_spawned(
                h_alternating,
                "alternating analysis",
                grammar_name,
            ),
            bisimulation_result: join_analysis_if_spawned(
                h_bisimulation,
                "bisimulation analysis",
                grammar_name,
            ),
            hindley_result: join_analysis(h_hindley, "Hindley-Milner analysis", grammar_name),
            ltl_results: join_analysis(h_ltl, "LTL check", grammar_name),
            provenance_result: join_analysis(h_provenance, "provenance tracking", grammar_name),
            cra_result: join_analysis(h_cra, "CRA analysis", grammar_name),
            morphism_result: join_analysis(h_morphism, "morphism check", grammar_name),
            kat_result: join_analysis(h_kat, "KAT check", grammar_name),
            symbolic_result: join_analysis_if_spawned(
                h_symbolic,
                "symbolic analysis",
                grammar_name,
            ),
            buchi_result: join_analysis_if_spawned(h_buchi, "Büchi analysis", grammar_name),
            mso_result: join_analysis_if_spawned(h_mso, "MSO analysis", grammar_name),
            probabilistic_result: join_analysis_if_spawned(
                h_probabilistic,
                "probabilistic analysis",
                grammar_name,
            ),
            register_result: join_analysis_if_spawned(
                h_register,
                "register analysis",
                grammar_name,
            ),
            parity_tree_result: join_analysis_if_spawned(
                h_parity_tree,
                "parity tree analysis",
                grammar_name,
            ),
            multi_tape_result: join_analysis_if_spawned(
                h_multi_tape,
                "multi-tape analysis",
                grammar_name,
            ),
            multiset_result: join_analysis_if_spawned(
                h_multiset,
                "multiset analysis",
                grammar_name,
            ),
            two_way_result: join_analysis_if_spawned(
                h_two_way,
                "two-way transducer analysis",
                grammar_name,
            ),
            sft_result: join_analysis_if_spawned(h_sft, "SFT analysis", grammar_name),
            // ── E-graph equality saturation; populated after confluence joins ──
            egraph_result: None,
            // ── Constraint theory analyses ──
            presburger_result: join_analysis_if_spawned(
                h_presburger,
                "Presburger analysis",
                grammar_name,
            ),
            unification_result: join_analysis_if_spawned(
                h_unification,
                "Unification analysis",
                grammar_name,
            ),
            lattice_result: join_analysis_if_spawned(h_lattice, "Lattice analysis", grammar_name),
            // ── Refinement type analysis ──
            refinement_analysis: refinement_analysis_result,
        }
    });

    // #164: one greppable line per grammar when SPAWN_LEDGER_ENV is set. Emitted
    // after the scope so the ledger is complete.
    report_spawn_ledger(grammar_name, &dispatch_plan, analysis_spawn_ledger());

    // Phase 8C: E-graph equality saturation (sequential — depends on confluence result)
    {
        // egraph feature implies trs-analysis, so confluence_result is available
        let confluence_ref = results.confluence_result.as_ref();
        let egraph_result = crate::egraph::analyze_from_bundle(
            &bundle.all_syntax,
            confluence_ref,
            &crate::egraph::EGraphConfig::default(),
        );
        results.egraph_result = egraph_result;
    }

    results
}

/// Run all mathematical analyses sequentially (fallback when DB03 gate is off
/// or grammar is not eligible).
pub(crate) fn run_math_analyses_sequential(
    bundle: &ParserBundle,
    wpds_analysis: Option<&crate::wpds::WpdsAnalysis>,
    eligible: bool,
) -> MathAnalysisResults {
    // Build dispatch plan for sequential path so dispatch gates are respected.
    let dispatch_plan =
        crate::predicate_dispatch::classify_grammar(&bundle.all_syntax, &bundle.categories);

    /// Helper macro: returns `None` when dispatch says module is not needed.
    /// The inner `#[cfg]` gate ensures this compiles when `predicate-dispatch` is off.
    #[allow(unused_macros)]
    macro_rules! dispatch_gate {
        ($module:ident) => {{
            if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::$module) {
                return None;
            }
        }};
    }

    MathAnalysisResults {
        phase_count: 0,

        // Always-on analyses
        safety_result: if eligible {
            wpds_analysis.and_then(|wa| {
                crate::verify::verify_from_bundle(wa, &bundle.categories, &bundle.all_syntax)
            })
        } else {
            None
        },
        cegar_result: if eligible {
            wpds_analysis.and_then(|wa| crate::cegar::cegar_from_bundle(wa))
        } else {
            None
        },
        algebraic_result: if eligible {
            wpds_analysis.map(|wa| crate::algebraic::analyze_from_bundle(wa))
        } else {
            None
        },

        // Feature-gated analyses
        confluence_result: if eligible {
            crate::confluence::analyze_from_bundle(&bundle.all_syntax, 100)
        } else {
            None
        },
        termination_result: if eligible {
            crate::termination::analyze_from_bundle(&bundle.all_syntax)
        } else {
            None
        },
        vpa_result: if eligible {
            (|| {
                dispatch_gate!(Vpa);
                crate::vpa::analyze_from_bundle(&bundle.categories, &bundle.all_syntax)
            })()
        } else {
            None
        },
        wta_result: if eligible {
            crate::tree_automaton::analyze_from_bundle(&bundle.categories, &bundle.all_syntax)
        } else {
            None
        },
        ewpds_result: if eligible {
            wpds_analysis.and_then(|wa| crate::ewpds::extend_from_bundle(wa, &bundle.all_syntax))
        } else {
            None
        },
        ara_result: if eligible {
            wpds_analysis.map(|wa| crate::ara::analyze_from_bundle(wa, &bundle.all_syntax))
        } else {
            None
        },
        petri_result: if eligible {
            let petri_cats: Vec<crate::wpds::WpdsCategoryInfo> = bundle
                .categories
                .iter()
                .map(|c| crate::wpds::WpdsCategoryInfo {
                    name: c.name.clone(),
                    is_primary: c.is_primary,
                })
                .collect();
            Some(crate::petri::analyze_from_bundle(&bundle.all_syntax, &petri_cats))
        } else {
            None
        },
        nominal_result: if eligible {
            Some(crate::nominal::analyze_from_bundle(&bundle.all_syntax))
        } else {
            None
        },
        alternating_result: if eligible {
            (|| {
                dispatch_gate!(Awa);
                Some(crate::alternating::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        // OSLF Phase-4 `.1`: same `Awa` dispatch gate as the alternating pass.
        bisimulation_result: if eligible {
            (|| {
                dispatch_gate!(Awa);
                Some(crate::bisimulation::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        // OSLF Phase-6 `.1`: UNCONDITIONAL (no `eligible`/dispatch gate) — HM
        // applies to ALL grammars, mirroring the unconditional refinement-sync
        // block below rather than the eligibility-gated automata passes above.
        hindley_result: Some(crate::hindley_milner::analyze_from_bundle(
            &bundle.all_syntax,
            &bundle.categories,
        )),
        ltl_results: if eligible {
            wpds_analysis.map(|wa| crate::ltl::check_from_bundle(wa))
        } else {
            None
        },
        provenance_result: if eligible {
            crate::provenance::track_from_bundle(&bundle.all_syntax, &bundle.categories)
        } else {
            None
        },
        cra_result: if eligible {
            crate::cra::analyze_from_bundle(&bundle.all_syntax)
        } else {
            None
        },
        morphism_result: if eligible {
            crate::morphism::check_from_bundle(&bundle.all_syntax, &bundle.categories)
        } else {
            None
        },
        kat_result: if eligible {
            wpds_analysis.and_then(|wa| crate::kat::check_from_bundle(wa, &bundle.all_syntax))
        } else {
            None
        },
        symbolic_result: if eligible {
            (|| {
                dispatch_gate!(Symbolic);
                Some(crate::symbolic::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
            })()
        } else {
            None
        },
        buchi_result: if eligible {
            (|| {
                dispatch_gate!(Buchi);
                Some(crate::buchi::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
            })()
        } else {
            None
        },
        mso_result: if eligible {
            (|| {
                dispatch_gate!(Mso);
                Some(crate::weighted_mso::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        probabilistic_result: if eligible {
            (|| {
                dispatch_gate!(Probabilistic);
                Some(crate::probabilistic::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        register_result: if eligible {
            (|| {
                dispatch_gate!(Register);
                Some(crate::register_automata::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        parity_tree_result: if eligible {
            (|| {
                dispatch_gate!(ParityTree);
                // OSLF Phase 5 `.1`: same live routing as the parallel path.
                Some(crate::parity_tree::analyze_recursive_predicates(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        multi_tape_result: if eligible {
            (|| {
                dispatch_gate!(MultiTape);
                Some(crate::multi_tape::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
            })()
        } else {
            None
        },
        multiset_result: if eligible {
            (|| {
                dispatch_gate!(Multiset);
                Some(crate::multiset_automata::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        two_way_result: if eligible {
            (|| {
                dispatch_gate!(TwoWay);
                Some(crate::two_way_transducer::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        sft_result: if eligible {
            (|| {
                dispatch_gate!(Sft);
                Some(crate::sft::analyze_from_bundle(&bundle.all_syntax, &bundle.categories))
            })()
        } else {
            None
        },
        // ── E-graph equality saturation; populated by the pipeline caller ──
        egraph_result: None,
        // ── Constraint theory analyses ──
        presburger_result: if eligible {
            (|| {
                dispatch_gate!(LinearArithmetic);
                Some(crate::presburger::analyze_from_bundle(&bundle.all_syntax))
            })()
        } else {
            None
        },
        unification_result: if eligible {
            (|| {
                dispatch_gate!(Unification);
                Some(crate::unification::analyze_from_bundle(&bundle.all_syntax))
            })()
        } else {
            None
        },
        lattice_result: if eligible {
            (|| {
                dispatch_gate!(SubtypeLattice);
                Some(crate::lattice_theory::analyze_from_bundle(
                    &bundle.all_syntax,
                    &bundle.categories,
                ))
            })()
        } else {
            None
        },
        // ── Refinement type analysis ──
        refinement_analysis: if !bundle.refinement_types.is_empty() {
            Some(analyze_refinement_types(bundle))
        } else {
            None
        },
    }
}

/// Analyze refinement type definitions from the language specification.
///
/// This runs at compile time during `language!` macro expansion. It checks:
/// - RT01: predicate unsatisfiability (dead refinement type)
/// - RT02: predicate tautology (refinement equivalent to base type)
/// - RT03: pairwise empty intersection
/// - RT04: pairwise subtype detection
/// - RT05: decidability tier classification
/// - RT06: name shadowing of base types
pub(crate) fn analyze_refinement_types(bundle: &ParserBundle) -> RefinementAnalysisResult {
    use crate::RefinementPredKind;

    let mut result = RefinementAnalysisResult::default();
    let spec = &bundle.refinement_types;

    // Refinement declarations also introduce a same-named category so the
    // parser can construct refined terms. RT06 should ignore that expected
    // category and report only an independent base-category collision.
    let mut category_name_counts: HashMap<String, usize> = HashMap::new();
    for category in &bundle.categories {
        *category_name_counts
            .entry(category.name.to_ascii_lowercase())
            .or_default() += 1;
    }
    let mut refinement_name_counts: HashMap<String, usize> = HashMap::new();
    for rt in spec {
        *refinement_name_counts
            .entry(rt.name.to_ascii_lowercase())
            .or_default() += 1;
    }

    for rt in spec {
        // RT05: Classify decidability tier based on predicate kind
        let tier = match rt.predicate_kind {
            RefinementPredKind::Presburger => "T2 (decidable, automata-based)".to_string(),
            RefinementPredKind::Structural => "T2 (decidable, unification-based)".to_string(),
            RefinementPredKind::Behavioral => "T3 (bounded, quantified)".to_string(),
            RefinementPredKind::Mixed => "T3 (bounded, mixed constraint domains)".to_string(),
        };
        result.decidability_tiers.push((rt.name.clone(), tier));

        // RT06: Check if the refinement name shadows a base category name.
        let refinement_key = rt.name.to_ascii_lowercase();
        let base_key = rt.base_category.to_ascii_lowercase();
        let category_count = category_name_counts
            .get(&refinement_key)
            .copied()
            .unwrap_or(0);
        let refinement_count = refinement_name_counts
            .get(&refinement_key)
            .copied()
            .unwrap_or(0);
        if refinement_key == base_key || category_count > refinement_count {
            let shadowed_name = if refinement_key == base_key {
                rt.base_category.clone()
            } else {
                rt.name.clone()
            };
            result.name_shadows.push((rt.name.clone(), shadowed_name));
        }

        // RT01/RT02: Predicate analysis
        // For now, mark predicates that are syntactically trivial.
        // Full satisfiability checking requires the actual ConstraintTheory
        // instances (Presburger NFA, etc.) which are only available when
        // the corresponding features are enabled. The per-predicate analysis
        // is deferred to the feature-gated analysis modules.
        if rt.predicate_repr == "true" || rt.predicate_repr.is_empty() {
            result
                .tautological
                .push((rt.name.clone(), "predicate is trivially true".to_string()));
        } else if rt.predicate_repr == "false" {
            result
                .unsatisfiable
                .push((rt.name.clone(), "predicate is trivially false".to_string()));
        }
    }

    // RT03/RT04/RT10: SFA dispatch analysis + pairwise overlap/subsumption
    // Uses the RefinementDispatchAnalysis from type_system.rs for predicate-aware
    // disjointness and subsumption checking.
    //
    // STRUCTURAL refinement pairs are decided precisely by the sym_tree recognizer
    // (over the grammar's ranked alphabet) instead of the string heuristic;
    // Presburger / Behavioral / Mixed pairs stay on the internal
    // `classify_predicate_overlap` heuristic, so this is never worse than the
    // heuristic-only path.
    let dispatch = crate::type_system::analyze_refinement_dispatch_structural(
        spec,
        &bundle.all_syntax,
        &bundle.categories,
    );

    // Merge dispatch results into the RT03/RT04 lints
    for (sub, sup) in &dispatch.subtype_pairs {
        if !result
            .subtype_pairs
            .iter()
            .any(|(s, p)| s == sub && p == sup)
        {
            result.subtype_pairs.push((sub.clone(), sup.clone()));
        }
    }

    // RT03 (empty intersection). On the HEURISTIC path, disjoint pairs are NOT an
    // RT03 finding — for Presburger refinements (e.g. PosInt vs NegInt) an empty
    // intersection is expected, not a warning. On the STRUCTURAL `.1` path the
    // recognizer has *proven* (via tree-automaton emptiness) that two structural
    // refinement patterns can never co-inhabit; that genuinely-empty intersection
    // is the RT03 finding the lint was written for, so we populate
    // `empty_intersections` from the structural disjoint pairs (firing the
    // previously-dead RT03 lint).
    {
        // Identify which disjoint pairs are STRUCTURAL (both sides Structural and
        // both predicates parse) — only those are precise emptiness findings.
        let alpha =
            crate::structural_types::ranked_alphabet(&bundle.all_syntax, &bundle.categories);
        let kind_by_name: std::collections::HashMap<&str, &crate::RefinementPredKind> = spec
            .iter()
            .map(|s| (s.name.as_str(), &s.predicate_kind))
            .collect();
        let repr_by_name: std::collections::HashMap<&str, &str> = spec
            .iter()
            .map(|s| (s.name.as_str(), s.predicate_repr.as_str()))
            .collect();
        for (a, b) in &dispatch.disjoint_pairs {
            let both_structural = kind_by_name.get(a.as_str())
                == Some(&&crate::RefinementPredKind::Structural)
                && kind_by_name.get(b.as_str()) == Some(&&crate::RefinementPredKind::Structural);
            let both_parse = repr_by_name
                .get(a.as_str())
                .and_then(|r| crate::structural_types::parse_structural_predicate(r, &alpha))
                .is_some()
                && repr_by_name
                    .get(b.as_str())
                    .and_then(|r| crate::structural_types::parse_structural_predicate(r, &alpha))
                    .is_some();
            if both_structural && both_parse {
                result.empty_intersections.push((
                    a.clone(),
                    b.clone(),
                    "structural refinement patterns are disjoint (proven by the \
                     symbolic tree-automaton recognizer)"
                        .to_string(),
                ));
            }
        }

        // RT structural witnesses: a minimal inhabiting term per inhabited base
        // category that a refinement refines, surfaced as a hint.
        let verdict =
            crate::structural_types::structural_verdict(&bundle.all_syntax, &bundle.categories);
        let refined_bases: std::collections::HashSet<&str> =
            spec.iter().map(|s| s.base_category.as_str()).collect();
        for (cat, witness) in &verdict.witnesses {
            if refined_bases.contains(cat.as_str()) {
                result
                    .structural_witnesses
                    .push((cat.clone(), render_sym_term(witness)));
            }
        }
    }

    // OSLF Phase-4 `.1`: dead-cast detection via bottom-up symbolic tree
    // transduction. A cast `r : src → tgt` whose pre-image (over the ranked
    // alphabet) has empty intersection with the source category's term
    // automaton can never fire — the transducer reports its rule label in
    // `dead_casts`. `non_total_casts` is intentionally NOT surfaced: every
    // refinement downcast is non-total by nature, so it is noise; `dead_casts`
    // is the genuine unreachability defect signal.
    {
        let analysis = crate::sym_tree_transducer::analyze_from_bundle(
            &bundle.all_syntax,
            &bundle.categories,
            spec,
        );
        result.dead_casts = analysis
            .dead_casts
            .into_iter()
            .map(|label| (label, "pre-image empty — cast unreachable".to_string()))
            .collect();
    }

    for (a, b) in &dispatch.overlapping_pairs {
        // Overlapping predicates: potential dispatch ambiguity.
        // This feeds into future lint for dispatch safety.
        let _ = (a, b);
    }

    result.dispatch_analysis = Some(dispatch);

    result
}

/// Render a structural witness term ([`SymTerm<AnyDomain>`](crate::any_algebra))
/// to a compact `c(child, …)` string for an RT-note hint. Scalar payload leaves
/// render their constructor only (the structural shape is what matters for the
/// hint; a concrete payload value is an arbitrary inhabitant).
fn render_sym_term(t: &crate::sym_tree::SymTerm<crate::any_algebra::AnyDomain>) -> String {
    if t.children.is_empty() {
        t.constructor.clone()
    } else {
        let kids: Vec<String> = t.children.iter().map(render_sym_term).collect();
        format!("{}({})", t.constructor, kids.join(", "))
    }
}

/// Bundle of advanced automata analysis results for codegen promotion.
///
/// Passed to [`build_pipeline_analysis()`] to integrate feature-gated analysis
/// data into the pipeline. Each field is `Option<&AnalysisType>` — `None` when
/// the corresponding analysis was not run (e.g., no grammar features triggered it).
pub(crate) struct AdvancedAnalysisBundle<'a> {
    pub(crate) symbolic: Option<&'a crate::symbolic::SymbolicAnalysis>,
    pub(crate) alternating: Option<&'a crate::alternating::AlternatingAnalysis>,
    /// OSLF Phase-4 `.1`: bisimulation partition that supersedes `alternating`
    /// at the N06-ISO / A3 seams (falls back to `alternating` when this is
    /// `None`).
    pub(crate) bisimulation: Option<&'a crate::bisimulation::BisimulationAnalysis>,
    pub(crate) vpa: Option<&'a crate::vpa::VpaAnalysis>,
    pub(crate) register: Option<&'a crate::register_automata::RegisterAnalysis>,
    pub(crate) probabilistic: Option<&'a crate::probabilistic::ProbabilisticAnalysis>,
    pub(crate) multi_tape: Option<&'a crate::multi_tape::MultiTapeAnalysis>,
    pub(crate) buchi: Option<&'a crate::buchi::BuchiAnalysis>,
    /// PhantomData to bind the lifetime when no advanced features are enabled.
    pub(crate) _phantom: std::marker::PhantomData<&'a ()>,
}

/// Build a [`PipelineAnalysis`] from the data computed during parser code generation.
///
/// Extracts constructor weights from prediction WFSTs, computes category-level
/// averages, identifies fully unreachable categories, and integrates advanced
/// automata analysis results for codegen optimization promotion.
///
/// # Advanced Automata Integration (Sprints 1-7, A3)
///
/// When feature-gated analysis results are available, this function:
/// - **SYM01-DCE**: Extends `dead_rule_labels` with unsatisfiable symbolic guards
///   (an UNSAT guard is a proof over the whole input domain — see the body)
/// - **PR01-WEIGHT**: Blends probabilistic selectivity into `constructor_weights`
///
/// ⚠ **PR01-DCE is gone** (#112/D4). It extended `dead_rule_labels` with
/// `low_selectivity_rules`, i.e. with a FREQUENCY statistic. `dead_rule_labels` is
/// consumed as a reachability claim, so "rare" was being published as "unreachable";
/// the rationale is recorded at the deletion site in the body.
/// - **N06-ISO**: Extends `isomorphic_groups` with bisimulation-equivalent category pairs
/// - **A3**: Adds +0.5 tropical weight penalty to constructors of bisimilar categories'
///   lexicographically second member, reducing redundant NFA try-all work
/// - **RA01-SKIP**: Populates `dead_binder_categories` from dead register analysis
/// - **V05-INFO**: Sets `bracket_deterministic` flag from VPA analysis
/// - **MT01-INFO**: Populates `independent_categories` from disconnected tape analysis
pub(crate) fn build_pipeline_analysis(
    dead_rules: &HashSet<String>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    categories: &[CategoryInfo],
    rule_infos: &[RuleInfo],
    decision_trees: HashMap<String, crate::decision_tree::CategoryDecisionTree>,
    _advanced: &AdvancedAnalysisBundle<'_>,
) -> crate::PipelineAnalysis {
    let mut constructor_weights = HashMap::new();
    let mut category_weights = HashMap::new();

    // Extract per-constructor weights from each category's PredictionWfst.
    // Each WeightedAction in the WFST's action table maps a dispatch decision
    // (constructor rule label) to a tropical weight (lower = more frequent).
    for (cat_name, wfst) in prediction_wfsts {
        let mut cat_total_weight = 0.0_f64;
        let mut cat_action_count = 0_usize;

        for action in &wfst.actions {
            let label = action.action.rule_label();
            let weight = action.weight.value();
            // Use the minimum weight if a constructor appears in multiple categories.
            // Minimum weight = highest frequency = most useful for ordering.
            let entry = constructor_weights.entry(label).or_insert(f64::INFINITY);
            if weight < *entry {
                *entry = weight;
            }
            cat_total_weight += weight;
            cat_action_count += 1;
        }

        if cat_action_count > 0 {
            category_weights.insert(cat_name.clone(), cat_total_weight / cat_action_count as f64);
        }
    }

    // ── Sprint 3 (PR01-WEIGHT): Blend probabilistic selectivity into constructor weights ──
    if let Some(prob) = _advanced.probabilistic {
        if prob.is_normalized {
            for (label, selectivity) in &prob.rule_selectivities {
                if *selectivity > 0.0 {
                    let prob_weight = -selectivity.ln(); // tropical: lower = more frequent
                    let existing = constructor_weights
                        .get(label.as_str())
                        .copied()
                        .unwrap_or(f64::INFINITY);
                    // Geometric mean blend: (WFST_weight + prob_weight) / 2
                    constructor_weights.insert(label.clone(), (existing + prob_weight) / 2.0);
                }
            }
        }
    }

    // ── Dead rule extension from advanced automata analyses ───────────────
    // mut needed when the symbolic-automata feature extends the set.
    #[allow(unused_mut)]
    let mut dead_rules_extended = dead_rules.clone();

    // Sprint 1 (SYM01-DCE): Unsatisfiable symbolic guards → dead rules.
    //
    // This one IS a reachability proof and belongs here: `unsatisfiable_rule_labels`
    // names rules whose guard is UNSAT over the symbolic algebra, so no input
    // whatsoever can satisfy it. "There is no model" is a statement about the whole
    // input domain, not about a sample of it.
    if let Some(sym) = _advanced.symbolic {
        for label in &sym.unsatisfiable_rule_labels {
            dead_rules_extended.insert(label.clone());
        }
    }

    // ── ★★ #112/D4 — Sprint 2 (PR01-DCE) DELETED: "low selectivity" is not "dead" ──
    //
    // This block used to read
    //
    // ```text
    //     if prob.is_normalized && !prob.low_selectivity_rules.is_empty() {
    //         for label in &prob.low_selectivity_rules {
    //             dead_rules_extended.insert(label.clone());
    //         }
    //     }
    // ```
    //
    // `ProbabilisticAnalysis::low_selectivity_rules` is produced by
    // `probabilistic.rs`'s threshold sweep: it names every state whose outgoing
    // probability MASS falls below a cut-off. That is a FREQUENCY statistic. A rule
    // that fires on one input in ten thousand is rare; it is not unreachable, and
    // `dead_rule_labels` is consumed as a reachability claim — it is published in
    // every generated `tests_unit.rs`, it derives `unreachable_categories` below,
    // and (behind `enhanced_dce`) it suppresses parser codegen. Feeding a frequency
    // statistic into it is the same category error Tier 3 committed one file over,
    // with a worse failure mode: the rules it silences are by construction the
    // rarely-exercised ones, i.e. exactly those whose loss a corpus would not show.
    //
    // The `is_normalized` guard did not make it sound, only quieter — it gates
    // whether the probabilities are meaningful, not whether "improbable" means
    // "impossible". There is no gate under which this is admissible, so there is no
    // gate here; the statistic itself remains available on
    // `AdvancedAnalysisBundle::probabilistic` for weighting (PR01-WEIGHT above still
    // blends it into `constructor_weights`, which is precisely where a frequency
    // belongs — it reorders candidates, it does not delete them).

    // Determine unreachable categories: categories where ALL rules are dead.
    let mut unreachable_categories = HashSet::new();
    for cat in categories {
        let all_dead = rule_infos
            .iter()
            .filter(|r| r.category == cat.name)
            .all(|r| dead_rules_extended.contains(&r.label));
        // Only mark as unreachable if the category actually has rules
        let has_rules = rule_infos.iter().any(|r| r.category == cat.name);
        if has_rules && all_dead {
            unreachable_categories.insert(cat.name.clone());
        }
    }

    // Sprint 8: Detect isomorphic WFST groups using De Bruijn canonicalization.
    // mut needed when feature = "alternating" extends groups with bisimulation equivalences.
    #[allow(unused_mut)]
    let mut isomorphic_groups = group_isomorphic_wfsts(prediction_wfsts);

    // ── OSLF Phase-4 `.1`: select the non-bisimilar-pair source for N06-ISO/A3 ──
    // Both seams below consume `&Vec<(String, String)>` of non-bisimilar category
    // pairs. The bisimulation pass supersedes `alternating` (falling back to it
    // when the bisimulation result is absent). The two analyses carry the *same*
    // `non_bisimilar_pairs` shape (parity proven by the agreement gate), so the
    // seam bodies are unchanged.
    let equiv_pairs: Option<&Vec<(String, String)>> = _advanced
        .bisimulation
        .map(|b| &b.non_bisimilar_pairs)
        .or_else(|| _advanced.alternating.map(|a| &a.non_bisimilar_pairs));

    // ── Sprint 4 (N06-ISO): Extend isomorphic groups with bisimulation equivalences ──
    if let Some(equiv_pairs) = equiv_pairs {
        // Collect new bisimulation groups into a separate vec to avoid borrow conflict.
        let new_groups = {
            // Categories already in De Bruijn groups
            let already_grouped: HashSet<&str> = isomorphic_groups
                .iter()
                .flatten()
                .map(|s| s.as_str())
                .collect();

            // Build set of non-bisimilar pairs for fast lookup
            let non_bisimilar: HashSet<(&str, &str)> = equiv_pairs
                .iter()
                .flat_map(|(a, b)| vec![(a.as_str(), b.as_str()), (b.as_str(), a.as_str())])
                .collect();

            // Find bisimilar pairs not already grouped
            let cat_names: Vec<&str> = categories.iter().map(|c| c.name.as_str()).collect();
            let mut groups = Vec::new();
            for i in 0..cat_names.len() {
                for j in (i + 1)..cat_names.len() {
                    let a = cat_names[i];
                    let b = cat_names[j];
                    if !already_grouped.contains(a)
                        && !already_grouped.contains(b)
                        && !non_bisimilar.contains(&(a, b))
                    {
                        groups.push(vec![a.to_string(), b.to_string()]);
                    }
                }
            }
            groups
        };
        isomorphic_groups.extend(new_groups);
    }

    // ── Sprint A3: Bisimilar weight discount ──
    // Deprioritize the lexicographically second category in each bisimilar pair
    // by adding 0.5 to its constructor weights. This reduces redundant NFA try-all
    // work when two categories accept the same language (bisimilar).
    if let Some(equiv_pairs) = equiv_pairs {
        let cat_names: Vec<&str> = categories.iter().map(|c| c.name.as_str()).collect();
        let non_bisimilar: HashSet<(&str, &str)> = equiv_pairs
            .iter()
            .flat_map(|(a, b)| vec![(a.as_str(), b.as_str()), (b.as_str(), a.as_str())])
            .collect();

        // Build rule-label → category mapping for weight lookup
        let rule_to_cat: HashMap<&str, &str> = rule_infos
            .iter()
            .map(|r| (r.label.as_str(), r.category.as_str()))
            .collect();

        // Collect all deprioritized categories
        let mut deprioritized_cats: HashSet<&str> = HashSet::new();
        for i in 0..cat_names.len() {
            for j in (i + 1)..cat_names.len() {
                let a = cat_names[i];
                let b = cat_names[j];
                if !non_bisimilar.contains(&(a, b)) {
                    // Bisimilar pair — deprioritize the lexicographically second
                    let deprioritized = if a > b { a } else { b };
                    deprioritized_cats.insert(deprioritized);
                }
            }
        }

        // Apply +0.5 tropical weight penalty to all rules in deprioritized categories
        for (label, weight) in constructor_weights.iter_mut() {
            if let Some(&cat) = rule_to_cat.get(label.as_str()) {
                if deprioritized_cats.contains(cat) {
                    *weight += 0.5;
                }
            }
        }
    }

    // Build action maps after bisimulation extension so they reflect all groups.
    let isomorphic_action_maps = build_isomorphic_action_maps(prediction_wfsts, &isomorphic_groups);

    // ── Sprint 5 (RA01-SKIP): Dead registers → skip binder alpha-equivalence ──
    let dead_binder_categories = if let Some(reg) = _advanced.register {
        // Map dead register indices to category names.
        // In register automata analysis, register index i corresponds to
        // the i-th category. A dead register means the binder associated
        // with that category's scope is stored but never tested.
        reg.dead_registers
            .iter()
            .filter_map(|&idx| categories.get(idx).map(|c| c.name.clone()))
            .collect()
    } else {
        HashSet::new()
    };

    // ── Sprint 6 (V05-INFO): VPA bracket deterministic flag ──
    let bracket_deterministic = _advanced
        .vpa
        .map_or(false, |v| v.is_determinizable && v.alphabet_mismatches.is_empty());

    // ── Sprint A1: VPA nesting depth bound ──
    let vpa_max_nesting_bound = _advanced.vpa.map(|v| v.max_nesting_bound);

    // ── Sprint A2: VPA bracket mismatch tokens ──
    let bracket_mismatch_tokens: HashSet<String> = _advanced
        .vpa
        .map_or_else(HashSet::new, |v| v.alphabet_mismatches.iter().cloned().collect());

    // ── Sprint 7 (MT01-INFO): Independent categories from multi-tape analysis ──
    let independent_categories = if let Some(mt) = _advanced.multi_tape {
        mt.disconnected_tapes
            .iter()
            .filter_map(|&idx| categories.get(idx).map(|c| c.name.clone()))
            .collect()
    } else {
        HashSet::new()
    };

    // ── Sprint C1: Guard-disambiguated tokens ──
    // Tokens where one category's guard subsumes another's can be dispatched
    // without backtracking. A subsumed guard pair (A, B) means guard A ⊂ guard B,
    // so the subsuming category can be tried first deterministically.
    let guard_disambiguated_tokens: HashSet<String> = if let Some(sym) = _advanced.symbolic {
        sym.subsumed_guards
            .iter()
            .map(|(subsumed, _subsumer)| subsumed.clone())
            .collect()
    } else {
        HashSet::new()
    };

    // ── Sprint C3: Per-category entropy from probabilistic analysis ──
    // Compute Shannon entropy per category from rule selectivities.
    // High entropy → more ambiguous alternatives → wider beam needed.
    // Categories with a single dominant rule have entropy near zero.
    let per_category_entropy: HashMap<String, f64> = if let Some(prob) = _advanced.probabilistic {
        // Group rule selectivities by category and compute per-category entropy.
        let mut cat_probs: HashMap<String, Vec<f64>> = HashMap::new();
        for (qualified_label, &selectivity) in &prob.rule_selectivities {
            // qualified_label format is "Category::Rule"
            if let Some(cat) = qualified_label.split("::").next() {
                cat_probs
                    .entry(cat.to_string())
                    .or_default()
                    .push(selectivity);
            }
        }

        let mut entropy_map = HashMap::new();
        for (cat, probs) in &cat_probs {
            let sum: f64 = probs.iter().sum();
            if sum > 0.0 {
                let mut entropy = 0.0_f64;
                for &p in probs {
                    let normalized = p / sum;
                    if normalized > 0.0 {
                        entropy -= normalized * normalized.ln();
                    }
                }
                entropy_map.insert(cat.clone(), entropy);
            }
        }
        entropy_map
    } else {
        HashMap::new()
    };

    // ── Recursive SCC categories from Buchi analysis ──
    // Categories participating in accepting SCCs (recursive grammar loops).
    // Recovery prefers InsertToken in these categories to maintain the loop.
    let recursive_scc_categories: HashSet<String> = if let Some(buchi) = _advanced.buchi {
        buchi.accepting_sccs.iter().flatten().cloned().collect()
    } else {
        HashSet::new()
    };

    crate::PipelineAnalysis {
        dead_rule_labels: dead_rules_extended,
        unreachable_categories,
        constructor_weights,
        category_weights,
        isomorphic_groups,
        isomorphic_action_maps,
        decision_trees,
        dead_binder_categories,
        bracket_deterministic,
        vpa_max_nesting_bound,
        bracket_mismatch_tokens,
        independent_categories,
        guard_disambiguated_tokens,
        per_category_entropy,
        recursive_scc_categories,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 8: Isomorphic WFST detection
// ══════════════════════════════════════════════════════════════════════════════

/// Group categories whose PredictionWFSTs are alpha-equivalent (isomorphic).
///
/// Two WFSTs are alpha-equivalent if they have identical De Bruijn-canonicalized
/// structure: same states, same transitions, same weights, same action shapes —
/// but potentially different action labels (rule names, category names).
///
/// Only returns groups with ≥2 members. Categories within each group are sorted
/// alphabetically for deterministic output.
fn group_isomorphic_wfsts(prediction_wfsts: &HashMap<String, PredictionWfst>) -> Vec<Vec<String>> {
    use crate::wfst::CanonicalWfstStructure;

    // Compute canonical structure for each category's WFST
    let mut canonical_groups: HashMap<CanonicalWfstStructure, Vec<String>> = HashMap::new();

    for (cat_name, wfst) in prediction_wfsts {
        let canonical = wfst.canonical_structure();
        canonical_groups
            .entry(canonical)
            .or_default()
            .push(cat_name.clone());
    }

    // Keep only groups with ≥2 members, sort members for deterministic output
    let mut groups: Vec<Vec<String>> = canonical_groups
        .into_values()
        .filter(|group| group.len() >= 2)
        .map(|mut group| {
            group.sort();
            group
        })
        .collect();

    // Sort groups by first member for deterministic ordering
    groups.sort_by(|a, b| a[0].cmp(&b[0]));
    groups
}

/// Build per-group De Bruijn action maps.
///
/// For each isomorphic group, maps De Bruijn action index → `Vec<(category, rule_label)>`.
/// This records which concrete action label in each category corresponds to each
/// De Bruijn position, enabling template instantiation to substitute the correct names.
fn build_isomorphic_action_maps(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    isomorphic_groups: &[Vec<String>],
) -> Vec<HashMap<u32, Vec<(String, String)>>> {
    isomorphic_groups
        .iter()
        .map(|group| {
            let mut action_map: HashMap<u32, Vec<(String, String)>> = HashMap::new();

            for cat_name in group {
                if let Some(wfst) = prediction_wfsts.get(cat_name) {
                    // Re-compute the De Bruijn mapping for this WFST
                    let mut action_debruijn: HashMap<u32, u32> = HashMap::new();
                    let mut next_debruijn: u32 = 0;

                    for state in &wfst.states {
                        let mut sorted_trans: Vec<_> = state.transitions.iter().collect();
                        sorted_trans.sort_by_key(|t| (t.input, t.action_idx));

                        for t in sorted_trans {
                            let db_idx =
                                *action_debruijn.entry(t.action_idx).or_insert_with(|| {
                                    let idx = next_debruijn;
                                    next_debruijn += 1;
                                    idx
                                });

                            // Record this category's concrete label at this De Bruijn position
                            if let Some(wa) = wfst.actions.get(t.action_idx as usize) {
                                let label = wa.action.rule_label();
                                action_map
                                    .entry(db_idx)
                                    .or_default()
                                    .push((cat_name.clone(), label));
                            }
                        }
                    }
                }
            }

            // Deduplicate: each (category, label) pair should appear only once per De Bruijn index
            for entries in action_map.values_mut() {
                entries.sort();
                entries.dedup();
            }

            action_map
        })
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// #164: guards for the hoisted dispatch gate
// ══════════════════════════════════════════════════════════════════════════════

/// Guards that the dispatch gate stays on the **spawn side** of `s.spawn`.
///
/// # What is being guarded, and why it needs three guards rather than one
///
/// The repair is one sentence — *ask `dispatch_plan.requires(m)` before
/// `Scope::spawn`, not inside the closure* — but it has three independent failure
/// modes, and each needs its own witness:
///
/// | failure mode                                   | guard                                | what goes red                                        |
/// |------------------------------------------------|--------------------------------------|------------------------------------------------------|
/// | the gate drifts back **inside** a closure       | [`gate_is_never_inside_a_closure`]   | a `.requires(` found in the function body            |
/// | a **wanted** analysis stops being spawned       | [`spawn_decision_matches_the_plan`]  | `created[m] != consulted[m]` for a required `m`      |
/// | the hoist degenerates to "spawn (almost) nothing" | [`rich_grammar_still_spawns_its_analyses`] | the spawn count on a maximal grammar          |
///
/// # Why the expected counts are read out of the source text
///
/// "32 analyses, 16 of them gated" is a fact about *this file*, and a constant
/// spelling it out would be a hand-maintained mirror of a computable domain — the
/// exact shape that has failed open repeatedly in this workspace. So
/// [`SpawnSiteCensus`] **counts the call sites in `analysis.rs`'s own source**,
/// via `include_str!`, and reads each gated site's `ModuleId` out of its argument
/// list. Add an analysis and the census moves with it; there is nothing to
/// forget to update.
///
/// ⚠ No test here expects a panic: under `[profile.dev]`'s cranelift backend a
/// `panic!` inside a proc-macro or a scoped thread aborts without unwinding, so
/// a panic-expecting test would kill the harness rather than assert anything.
/// Every guard below is a plain value comparison.
#[cfg(test)]
mod spawn_ledger_guards {
    use super::*;
    use crate::predicate_dispatch::{classify_grammar, GrammarDispatchPlan, ModuleId};

    /// This file's own source, read at compile time. The census below is derived
    /// from it, so the guards cannot drift from the code they guard.
    const ANALYSIS_SOURCE: &str = include_str!("analysis.rs");

    /// A tally of the analyses and dispatch modules named in [`ANALYSIS_SOURCE`].
    ///
    /// ★ Every field is **invariant under reverting the hoist**, and that is the
    /// whole design. If the census were "count the `spawn_analysis_if_required`
    /// sites", then burying a gate back inside its closure would remove the site
    /// *and* the elision together, and every count would still agree with itself —
    /// the guard would pass on the defect it exists to catch. So instead:
    ///
    /// - `analyses` counts calls to **either** spawn helper, which a revert does
    ///   not change (a reverted site is still a spawn);
    /// - `gated_modules` counts `ModuleId::` mentions **anywhere** inside
    ///   [`run_math_analyses_parallel`], which a revert does not change either (the
    ///   module is still named, just one line lower).
    ///
    /// A revert therefore leaves the *expected* numbers alone and moves only the
    /// *observed* ones, which is exactly what makes the assertions fire.
    #[derive(Debug, PartialEq, Eq)]
    struct SpawnSiteCensus {
        /// Calls to `spawn_analysis` or `spawn_analysis_if_required` inside
        /// [`run_math_analyses_parallel`] — one per analysis. 32 of them.
        analyses: u32,
        /// `ModuleId::M` mentions inside [`run_math_analyses_parallel`], in source
        /// order — one per dispatch-gated analysis. 16 of them, with `Awa` twice
        /// (it gates both `alternating` and `bisimulation`).
        gated_modules: Vec<ModuleId>,
        /// `Scope::spawn` calls in the production region. Exactly 2 — one per
        /// spawn helper. A third would be an analysis invisible to the ledger.
        helper_spawn_calls: u32,
        /// `s.spawn(` calls in [`run_math_analyses_parallel`] — spawns that skip
        /// the helpers, and so the ledger. Must be 0.
        unledgered_spawns: u32,
        /// `.requires(` calls inside [`run_math_analyses_parallel`] — dispatch
        /// gates that did **not** get hoisted, since the hoisted form passes a
        /// `ModuleId` to a helper instead of calling the plan itself. Must be 0.
        gates_inside_closures: u32,
    }

    /// Count the analyses, dispatch modules and stray gates in this file's source.
    ///
    /// # Scope of the scan
    ///
    /// Only the **production region** — everything above this guard module — is
    /// scanned, and the per-function counters fire only inside
    /// [`run_math_analyses_parallel`]. Both restrictions are load-bearing:
    ///
    /// - the guard module itself calls `plan.requires(…)` and names `ModuleId::`
    ///   legitimately (that is how it re-derives the expected decision), and must
    ///   not be mistaken for a relapse;
    /// - [`run_math_analyses_sequential`] gates *inside* a closure via its
    ///   `dispatch_gate!` macro, and that is correct there — it spawns no threads
    ///   at all, so there is no thread to waste.
    ///
    /// # Why the needles are assembled with `concat!`
    ///
    /// A scanner that looks for `"spawn_analysis("` in a file containing its own
    /// source would otherwise match the *literal that defines the needle*. Each
    /// needle is therefore split across a `concat!` so no single line of this
    /// function contains a complete needle. Same for the marker that ends the
    /// production region.
    fn census() -> SpawnSiteCensus {
        const SPAWN_CALL: &str = concat!("spawn_analysis", "(s,");
        const GATED_SPAWN_CALL: &str = concat!("spawn_analysis_if_", "required(s,");
        const MODULE: &str = concat!("Module", "Id::");
        const HELPER_SPAWN: &str = concat!("scope.", "spawn(");
        const UNLEDGERED_SPAWN: &str = concat!("s.", "spawn(");
        const GATE_CALL: &str = concat!(".requi", "res(");
        const GUARD_MODULE: &str = concat!("mod spawn_ledger", "_guards {");
        const PARALLEL_FN: &str = concat!("fn run_math_analyses", "_parallel(");

        let production = match ANALYSIS_SOURCE.split_once(GUARD_MODULE) {
            Some((above, _)) => above,
            None => ANALYSIS_SOURCE,
        };

        let mut census = SpawnSiteCensus {
            analyses: 0,
            gated_modules: Vec::with_capacity(16),
            helper_spawn_calls: 0,
            unledgered_spawns: 0,
            gates_inside_closures: 0,
        };
        let mut in_parallel_fn = false;

        for line in production.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("//") {
                continue;
            }
            // Item boundaries, for rustfmt-formatted source: the signature line
            // opens the region and the column-0 `}` closes it. Matching on
            // "any column-0 line" would fail on the multi-line signature, whose
            // `) -> MathAnalysisResults {` also starts at column 0.
            if line.contains(PARALLEL_FN) {
                in_parallel_fn = true;
            } else if line.starts_with('}') {
                in_parallel_fn = false;
            }
            census.helper_spawn_calls += trimmed.matches(HELPER_SPAWN).count() as u32;
            if !in_parallel_fn {
                continue;
            }
            census.unledgered_spawns += trimmed.matches(UNLEDGERED_SPAWN).count() as u32;
            census.gates_inside_closures += trimmed.matches(GATE_CALL).count() as u32;
            census.analyses += trimmed.matches(SPAWN_CALL).count() as u32;
            census.analyses += trimmed.matches(GATED_SPAWN_CALL).count() as u32;
            for mention in trimmed.split(MODULE).skip(1) {
                let name: String = mention
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect();
                let module = ModuleId::ALL
                    .iter()
                    .copied()
                    .find(|m| format!("{m:?}") == name)
                    .unwrap_or_else(|| {
                        panic!("a dispatch gate names an unknown ModuleId: `{name}`")
                    });
                census.gated_modules.push(module);
            }
        }

        census
    }

    // ── Fixtures ──────────────────────────────────────────────────────────────

    fn category(name: &str, is_primary: bool) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: None,
            is_primary,
            has_var: true,
        }
    }

    fn nt(category: &str, param: &str) -> SyntaxItemSpec {
        SyntaxItemSpec::NonTerminal {
            category: category.to_string(),
            param_name: param.to_string(),
        }
    }

    fn term(text: &str) -> SyntaxItemSpec {
        SyntaxItemSpec::Terminal(text.to_string())
    }

    /// A `ParserBundle` carrying `all_syntax`/`categories` and nothing else —
    /// every other field is what the pipeline's own tests use. The analyses under
    /// guard read only these two.
    fn bundle(
        name: &str,
        categories: Vec<CategoryInfo>,
        all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
    ) -> ParserBundle {
        ParserBundle {
            grammar_name: name.to_string(),
            categories,
            bp_table: crate::binding_power::BindingPowerTable { operators: Vec::new() },
            rule_infos: Vec::new(),
            follow_inputs: Vec::new(),
            rd_rules: Vec::new(),
            cross_rules: Vec::new(),
            cast_rules: Vec::new(),
            has_binders: false,
            beam_width: crate::BeamWidthConfig::default(),
            recovery_config: crate::recovery::RecoveryConfig::default(),
            all_syntax,
            rule_locations: HashMap::new(),
            dead_rule_ignore_labels: HashSet::new(),
            semantic_dependency_groups: Vec::new(),
            custom_tokens: Vec::new(),
            refinement_types: Vec::new(),
        }
    }

    /// The **thinnest** grammar the parallel path will accept: three categories,
    /// one flat rule each, no brackets, no binders, no recursion, no collection,
    /// no arithmetic. Its plan requires only `PredicateSignature::BASE`, so it
    /// maximises elision and is the lower bound on the spawn count.
    fn sparse_bundle() -> ParserBundle {
        bundle(
            "SparseGuard",
            vec![category("Alpha", true), category("Beta", false), category("Gamma", false)],
            vec![
                ("AOne".to_string(), "Alpha".to_string(), vec![term("alpha")]),
                ("BOne".to_string(), "Beta".to_string(), vec![term("beta")]),
                ("COne".to_string(), "Gamma".to_string(), vec![term("gamma")]),
            ],
        )
    }

    /// A grammar built to trip **every** heuristic in
    /// [`crate::predicate_dispatch::classify_grammar`]: `{`/`}` brackets (M4),
    /// direct category self-reference (M2), a rule with ≥3 non-terminal children
    /// (M3, and with recursion M5), a binder (M6), ≥3 rules in one category (M7),
    /// cross-category references (M8, M11, and with recursion M15), a collection
    /// (M9), `+` (M12), `match` (M13) and `:` (M14). With `BASE` (M1, M10) that
    /// is all 15 modules — the non-vacuity floor.
    fn rich_bundle() -> ParserBundle {
        bundle(
            "RichGuard",
            vec![category("Proc", true), category("Name", false), category("Int", false)],
            vec![
                (
                    "PBranch".to_string(),
                    "Proc".to_string(),
                    vec![
                        term("{"),
                        nt("Proc", "p"),
                        term("match"),
                        nt("Proc", "q"),
                        term(":"),
                        nt("Int", "n"),
                        term("}"),
                    ],
                ),
                (
                    "PBind".to_string(),
                    "Proc".to_string(),
                    vec![
                        term("for"),
                        SyntaxItemSpec::Binder {
                            param_name: "x".to_string(),
                            category: "Name".to_string(),
                            is_multi: false,
                        },
                        nt("Proc", "body"),
                    ],
                ),
                (
                    "PList".to_string(),
                    "Proc".to_string(),
                    vec![
                        term("["),
                        SyntaxItemSpec::Collection {
                            param_name: "elems".to_string(),
                            element_category: "Name".to_string(),
                            separator: ",".to_string(),
                            key_val_separator: None,
                            kind: crate::grammar::ir::CollectionKind::Vec,
                        },
                        term("]"),
                    ],
                ),
                ("NQuote".to_string(), "Name".to_string(), vec![term("@"), nt("Proc", "p")]),
                (
                    "Add".to_string(),
                    "Int".to_string(),
                    vec![nt("Int", "a"), term("+"), nt("Int", "b")],
                ),
            ],
        )
    }

    fn plan_for(bundle: &ParserBundle) -> GrammarDispatchPlan {
        classify_grammar(&bundle.all_syntax, &bundle.categories)
    }

    /// Analyses the plan does not want, counted over the source's gated sites.
    fn expected_elisions(census: &SpawnSiteCensus, plan: &GrammarDispatchPlan) -> u32 {
        census
            .gated_modules
            .iter()
            .filter(|module| !plan.requires(**module))
            .count() as u32
    }

    // ── Guard 1: no dispatch gate may sit inside a spawned closure ────────────

    /// The #164 defect itself, stated as a source-shape property.
    ///
    /// Goes red if any `.requires(` reappears outside the spawn helpers — which is
    /// exactly what reverting the hoist does, and the only failure the ledger
    /// cannot see (a re-buried gate still produces the right `Option`, it just
    /// pays a thread for it).
    #[test]
    fn gate_is_never_inside_a_closure() {
        let census = census();
        assert_eq!(
            census.gates_inside_closures, 0,
            "#164: `run_math_analyses_parallel` contains {} dispatch gate(s) spelled \
             `.requires(`; expected 0. The hoisted form names its `ModuleId` and lets \
             `spawn_analysis_if_required` ask the plan, so a `.requires(` here is a gate that \
             went back INSIDE a spawned closure — creating a thread only to discard it.",
            census.gates_inside_closures
        );
        assert_eq!(
            census.helper_spawn_calls, 2,
            "#164: found {} `Scope::spawn` call(s) in the production region; expected exactly \
             2 (one in `spawn_analysis`, one in `spawn_analysis_if_required`). A third \
             bypasses the spawn ledger, so its thread would be invisible to every guard here.",
            census.helper_spawn_calls
        );
        assert_eq!(
            census.unledgered_spawns, 0,
            "#164: `run_math_analyses_parallel` spawns {} thread(s) directly through `s.spawn(`; \
             expected 0. Every analysis must go through `spawn_analysis` or \
             `spawn_analysis_if_required` so the ledger — and therefore every guard here — \
             can see it.",
            census.unledgered_spawns
        );
    }

    // ── Guard 2: the ledger's decision is exactly the plan's ──────────────────

    /// Every gated analysis is spawned **iff** the plan requires its module, on
    /// both a sparse and a rich grammar, with the expected counts derived from
    /// the source census and the plan rather than written down.
    #[test]
    fn spawn_decision_matches_the_plan() {
        let census = census();
        for bundle in [sparse_bundle(), rich_bundle()] {
            let plan = plan_for(&bundle);
            let _results = run_math_analyses_parallel(&bundle, None);
            let ledger = analysis_spawn_ledger();
            let name = &bundle.grammar_name;

            assert_eq!(
                ledger.considered(),
                census.analyses,
                "{name}: the ledger saw {} analyses but `run_math_analyses_parallel` calls a \
                 spawn helper {} times; an analysis is escaping the ledger",
                ledger.considered(),
                census.analyses,
            );
            assert_eq!(
                ledger.gated_sites(),
                census.gated_modules.len() as u32,
                "{name}: {} spawn site(s) consulted the dispatch plan, but \
                 `run_math_analyses_parallel` names {} dispatch module(s). A named module that \
                 no spawn site consulted is a gate buried back inside its closure.",
                ledger.gated_sites(),
                census.gated_modules.len(),
            );

            let expected_elided = expected_elisions(&census, &plan);
            assert_eq!(
                ledger.elided,
                expected_elided,
                "{name}: elided {} of {} gated analyses; the plan (signature 0x{:04X}) does \
                 not require {} of them, so exactly that many must never be spawned",
                ledger.elided,
                census.gated_modules.len(),
                plan.aggregate_signature.raw(),
                expected_elided,
            );
            assert_eq!(
                ledger.spawned,
                census.analyses - expected_elided,
                "{name}: spawned {} threads; expected {} = {} analyses − {} elisions",
                ledger.spawned,
                census.analyses - expected_elided,
                census.analyses,
                expected_elided,
            );

            // Per module: a required module spawns every site that consults it,
            // an unrequired module spawns none. Nothing else is a correct hoist.
            for module in ModuleId::ALL {
                let slot = module as usize;
                let expected_created = match plan.requires(module) {
                    true => ledger.consulted[slot],
                    false => 0,
                };
                assert_eq!(
                    ledger.created[slot],
                    expected_created,
                    "{name}: module {module:?} is {}required by the plan, was consulted by {} \
                     spawn site(s), and spawned {}; expected {expected_created}",
                    match plan.requires(module) {
                        true => "",
                        false => "NOT ",
                    },
                    ledger.consulted[slot],
                    ledger.created[slot],
                );
            }
        }
    }

    /// `Symbolic` (M1) and `Mso` (M10) are
    /// [`crate::predicate_dispatch::PredicateSignature::BASE`], so
    /// [`crate::predicate_dispatch::classify_grammar`] seeds them for *every*
    /// grammar and their two gates can never refuse. The spawn count therefore has
    /// a floor of `ungated + 2`, and the "32 → 16" reading of #164 is unreachable.
    #[test]
    fn base_modules_are_required_by_every_grammar() {
        let census = census();
        let sparse = sparse_bundle();
        let plan = plan_for(&sparse);
        for module in [ModuleId::Symbolic, ModuleId::Mso] {
            assert!(
                plan.requires(module),
                "{module:?} is in PredicateSignature::BASE, so even the sparsest grammar must \
                 require it (signature 0x{:04X})",
                plan.aggregate_signature.raw(),
            );
        }
        let _results = run_math_analyses_parallel(&sparse, None);
        let ledger = analysis_spawn_ledger();
        let ungated = census.analyses - census.gated_modules.len() as u32;
        let floor = ungated + 2;
        assert_eq!(
            ledger.spawned, floor,
            "the sparsest grammar spawned {} analyses; the floor is {floor} = {ungated} \
             ungated + symbolic + mso",
            ledger.spawned,
        );
    }

    // ── Guard 3: non-vacuity — a grammar that wants everything gets everything ─

    /// A grammar that trips every dispatch heuristic must still spawn **all** 32
    /// analyses. Without this the hoist could degenerate into "spawn nothing" and
    /// every count above would still agree with itself.
    #[test]
    fn rich_grammar_still_spawns_its_analyses() {
        let census = census();
        let rich = rich_bundle();
        let plan = plan_for(&rich);

        assert_eq!(
            plan.aggregate_signature.count(),
            crate::predicate_dispatch::PredicateSignature::NUM_MODULES,
            "the rich fixture must activate all {} modules, not {} (signature 0x{:04X}); \
             otherwise this floor tests nothing",
            crate::predicate_dispatch::PredicateSignature::NUM_MODULES,
            plan.aggregate_signature.count(),
            plan.aggregate_signature.raw(),
        );

        let _results = run_math_analyses_parallel(&rich, None);
        let ledger = analysis_spawn_ledger();
        assert_eq!(
            ledger.elided, 0,
            "a grammar requiring every module must elide nothing, but {} analyses were elided",
            ledger.elided,
        );
        assert_eq!(
            ledger.spawned, census.analyses,
            "a grammar requiring every module must spawn all {} analyses, not {}",
            census.analyses, ledger.spawned,
        );
    }

    // ── Guard 4: equivalence — the wanted analyses produce identical results ───

    /// Render one analysis run as pretty-`Debug` lines, with the two fields that
    /// are *defined* to differ between the paths normalised away.
    ///
    /// Neither normalisation is a convenience:
    ///
    /// - `phase_count` — the sequential path reports `0` by design (it runs no
    ///   parallel phases), documented at its own definition;
    /// - `egraph_result` — the parallel path fills it in *after* the thread scope
    ///   from `confluence_result`, while the sequential path leaves it for its
    ///   caller. `confluence_result`, the input to e-graph saturation, is still
    ///   compared.
    ///
    /// Everything else is compared as the whole struct's rendering rather than as
    /// a list of fields, so the guard cannot fall behind
    /// [`MathAnalysisResults`]: a field added there is compared automatically.
    fn render(mut results: MathAnalysisResults) -> Vec<String> {
        results.phase_count = 0;
        results.egraph_result = None;
        format!("{results:#?}")
            .lines()
            .map(str::to_string)
            .collect()
    }

    /// The parallel path must agree with the sequential path on every analysis
    /// result, everywhere the result is *reproducible at all*.
    ///
    /// # The oracle
    ///
    /// [`run_math_analyses_sequential`] applies the same dispatch gate to the same
    /// analysis functions with no threads whatsoever, so it is an independent
    /// oracle for both halves of the equivalence: the analyses the plan wants
    /// produce identical values, and the ones it does not are `None` on both paths
    /// — which is exactly the claim that *absent* and *ran-and-returned-`None`*
    /// are indistinguishable downstream.
    ///
    /// # ⚠ Why a repeated run is part of the method
    ///
    /// Some analysis results are **not reproducible from one call to the next**:
    /// `PetriAnalysis::unbounded_places`, for one, is rendered in `HashSet`
    /// iteration order, so two runs of the *same* path on the *same* grammar can
    /// print `["Gamma", "Alpha", "Beta"]` and `["Alpha", "Beta", "Gamma"]`. That
    /// is a determinism defect in the analysis, not in this hoist — `petri` is
    /// **ungated**, so #164 cannot have touched it — but it makes a naive
    /// path-to-path diff fail for the wrong reason.
    ///
    /// Rather than exclude the unstable fields by name — a list that would rot
    /// silently, and would hide a *newly* unstable field — each path is run
    /// [`EQUIVALENCE_REPEATS`] times and the unstable lines are **derived**: a line
    /// that a path cannot reproduce against itself is not evidence about anything,
    /// on either path, and is skipped.
    ///
    /// The guard then asserts that every line both paths *can* reproduce is
    /// identical between them, and — the canary — that irreproducibility has not
    /// grown to the point where that says nothing.
    #[test]
    fn parallel_and_sequential_agree_wherever_results_are_reproducible() {
        /// Runs per path. Enough that a two-element `HashSet` rendering does not
        /// look stable by coincidence: with `k` equally likely orders, `n` runs
        /// miss the instability with probability `k^{1-n}`.
        const EQUIVALENCE_REPEATS: usize = 6;
        /// Ceiling on the share of rendered lines that may be irreproducible
        /// before this guard stops being evidence. Not a semantic claim — a canary
        /// on the analyses' own determinism, which is a defect elsewhere (see
        /// `PetriAnalysis::unbounded_places` above).
        const IRREPRODUCIBLE_LINE_BUDGET: usize = 10; // percent

        for bundle in [sparse_bundle(), rich_bundle()] {
            let name = &bundle.grammar_name;
            let parallel: Vec<Vec<String>> = (0..EQUIVALENCE_REPEATS)
                .map(|_| render(run_math_analyses_parallel(&bundle, None)))
                .collect();
            let sequential: Vec<Vec<String>> = (0..EQUIVALENCE_REPEATS)
                .map(|_| render(run_math_analyses_sequential(&bundle, None, true)))
                .collect();

            let line_count = parallel[0].len();
            assert_eq!(
                line_count,
                sequential[0].len(),
                "{name}: the parallel path rendered {line_count} lines of results and the \
                 sequential path {} — the two paths do not even produce the same shape, so one \
                 of them is missing or inventing an analysis",
                sequential[0].len(),
            );

            // A line is irreproducible if ANY run of EITHER path disagrees with
            // that path's first run at that position.
            let irreproducible = |index: usize| {
                parallel.iter().any(|run| run[index] != parallel[0][index])
                    || sequential
                        .iter()
                        .any(|run| run[index] != sequential[0][index])
            };

            let mut compared = 0usize;
            let mut skipped = Vec::new();
            for index in 0..line_count {
                if irreproducible(index) {
                    skipped.push(index);
                    continue;
                }
                assert_eq!(
                    parallel[0][index], sequential[0][index],
                    "{name}: analysis results differ at line {index} between the parallel and \
                     sequential paths — hoisting the dispatch gate to the spawn site must not \
                     change any result"
                );
                compared += 1;
            }

            assert!(
                skipped.len() * 100 <= line_count * IRREPRODUCIBLE_LINE_BUDGET,
                "{name}: {} of {line_count} rendered result lines are irreproducible across \
                 {EQUIVALENCE_REPEATS} runs (lines {skipped:?}), over the \
                 {IRREPRODUCIBLE_LINE_BUDGET}% budget. {compared} lines were compared. \
                 Irreproducible analysis output is a determinism defect in the analyses \
                 themselves, and past this point this equivalence guard is no longer evidence.",
                skipped.len(),
            );
        }
    }
}
