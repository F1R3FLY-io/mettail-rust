//! D1: Cost-Benefit Optimization Framework
//!
//! Uses `ProductWeight<TropicalWeight, TropicalWeight>` (lexicographic ordering)
//! to rank optimization candidates by (speedup, compile_cost). Among equally
//! beneficial optimizations, the cheaper one is preferred.
//!
//! The framework evaluates grammar properties (shared prefix ratio, cold dispatch
//! fraction, ambiguous token fraction, etc.) and produces a ranked list of
//! optimizations that should be applied. Each optimization has:
//!
//! - **Speedup estimate** (lower = more beneficial, in tropical semiring)
//! - **Compile cost estimate** (lower = cheaper, in tropical semiring)
//! - **Applicability predicate** (gated on grammar analysis results)
//!
//! This module is purely analytical — it does not apply optimizations itself.
//! The pipeline consults `evaluate_optimizations()` to decide which passes to run.

use std::collections::HashMap;
use std::fmt;

use crate::automata::semiring::{ProductWeight, TropicalWeight};
use crate::prediction::FirstSet;
use crate::wfst::PredictionWfst;

/// An optimization that the framework can recommend.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Optimization {
    /// A1: Grammar left-factoring via prefix sharing.
    /// Subsumed by the decision tree for the DisjointSuffix path, but this
    /// gate still controls the recovery parser's legacy fallback.
    LeftFactoring,
    /// A2: Hot/cold dispatch path splitting
    HotColdSplitting,
    /// A4: Enhanced dead-code elimination via full dispatch graph
    EnhancedDeadCodeElimination,
    /// A5: CountingWeight-guided ambiguity targeting
    AmbiguityTargeting,
    /// B1: Multi-token lookahead via extended PredictionWfst.
    /// Used by both DT-driven NfaTryAll path and legacy fallback path.
    MultiTokenLookahead,
    /// B2: Adaptive recovery via runtime weight accumulation
    AdaptiveRecovery,
    /// B3: PredictionWfst minimization
    WfstMinimization,
    /// F1: Weight-based spillover pruning
    SpilloverPruning,
    /// F2: Early termination on deterministic hit
    EarlyTermination,
    /// F3: Lazy spillover (demand-driven replay)
    LazySpillover,
    /// G1: Backtracking elimination via compile-time FIRST set analysis.
    /// Used by both DT-driven NfaTryAll path (suffix_disjointness_check)
    /// and legacy fallback path.
    BacktrackingElimination,
    /// H1: ContextWeight-based disambiguation (Sprint 6).
    /// Uses powerset WFST to narrow NFA try-all candidate sets at compile time.
    ContextDisambiguation,
    /// G25: WPDS stack-aware reachability check.
    /// Uses poststar saturation to confirm/refute WFST-based dead-rule detection
    /// with full pushdown precision.
    WpdsReachabilityCheck,
    /// TRS confluence check: Knuth-Bendix critical pair analysis.
    TrsConfluenceCheck,
    /// VPA inclusion check: decidable structured sublanguage verification.
    VpaInclusionCheck,
    /// Safety verification: WPDS prestar against bad-state automaton.
    SafetyVerification,
    /// CEGAR refinement: iterative abstraction refinement loop.
    CegarRefinement,
    /// Petri net deadlock check: coverability analysis for concurrent patterns.
    PetriDeadlockCheck,

    // ── Advanced Automata Infrastructure ─────────────────────────────────────

    /// SYM01: Symbolic automata guard analysis (satisfiability, overlap, subsumption).
    #[cfg(feature = "symbolic-automata")]
    SymbolicGuardAnalysis,
    /// O01: Weighted Büchi automaton analysis (liveness, accepting cycle weight).
    #[cfg(feature = "omega")]
    WeightedBuchiAnalysis,
    /// N06: Weighted alternating automaton analysis (polynomial transitions, game value).
    #[cfg(feature = "alternating")]
    WeightedAlternatingAnalysis,
    /// V05: Weighted VPA analysis (weighted determinization, inclusion).
    #[cfg(feature = "vpa")]
    WeightedVpaAnalysis,
    /// PT01: Parity tree automaton analysis (emptiness, mu-calculus).
    #[cfg(feature = "parity-tree-automata")]
    ParityTreeAnalysis,
    /// RA01: Register automaton analysis (dead registers, unbound references).
    #[cfg(feature = "register-automata")]
    RegisterAnalysis,
    /// PR01: Probabilistic automaton analysis (selectivity, entropy, training).
    #[cfg(feature = "probabilistic")]
    ProbabilisticAnalysis,
    /// MT01: Multi-tape automaton analysis (disconnected/overlapping tapes).
    #[cfg(feature = "multi-tape")]
    MultiTapeAnalysis,
    /// MS01: Multiset automaton analysis (cardinality constraints, feature interactions).
    #[cfg(feature = "multiset-automata")]
    MultisetAnalysis,
    /// MSO01: Weighted MSO logic analysis (formula classification, decidability).
    #[cfg(feature = "weighted-mso")]
    WeightedMsoAnalysis,
    /// TW01: Two-way transducer analysis (deadlock cycles, one-way equivalence).
    #[cfg(feature = "two-way-transducer")]
    TwoWayTransducerAnalysis,

    /// PD01: Predicate dispatch — algebraic variety classification for directed
    /// module spawning. Skips irrelevant Phase 7 modules based on predicate morphemes.
    #[cfg(feature = "predicate-dispatch")]
    PredicateDispatch,

    // ── Codegen Optimization Catalog ─────────────────────────────────────────

    /// ART01: Hash-consing for recursive term types (Rc/Arc + interning).
    HashConsing,
    /// ART02: Incremental semi-naive delta guards.
    IncrementalDelta,
    /// ART03: Relation indexing hints via #[index] annotations.
    RelationIndexing,
    /// ART04: Bloom filter pre-check for congruence rules.
    CongruenceBloom,
    /// ART05: Fixpoint convergence bound via term-depth analysis.
    DepthBound,
    /// ART06: Demand-driven relation population.
    DemandDriven,

    /// BCG01: Join ordering optimization (reorder body clauses by cost).
    JoinOrdering,
    /// BCG02: Rule fusion for chained deconstruction-rewrite.
    RuleFusion,
    /// BCG03: Selective equality congruence pruning.
    EqCongruencePrune,
    /// BCG04: Ground-term short-circuit in rewrite rules.
    GroundShortCircuit,
    /// BCG05: Normalize-on-insert deduplication.
    NormalizeDedup,
    /// BCG06: Stratified equation evaluation.
    EqStrata,

    /// AL01: DFA transition table multi-row repacking.
    CombRepacking,
    /// AL02: Hybrid direct-coded + compressed lexer.
    HybridLexer,
    /// AL03: SIMD-accelerated whitespace skipping.
    SimdWhitespace,
    /// AL04: Keyword recognition via minimal perfect hashing.
    KeywordMph,
    /// AL05: Multi-byte chain transitions.
    MultiByteChain,
    /// AL06: Accept state bitmap widening.
    AcceptBitmapWiden,

    /// BP01: Pratt BP table compaction via range encoding.
    BpCompaction,
    /// BP02: Tail-call elimination in recursive descent.
    TailCallElim,
    /// BP03: Token peek cache / BP table lookup.
    BpTableLookup,
    /// BP04: Prefix handler inlining for trivial rules.
    TrivialInline,
    /// BP05: Specialized Pratt loop for fixed BP ranges.
    BpRangeLoop,

    /// CD01: Hot-path arm reordering via WFST frequency weights.
    FrequencyOrdering,
    /// CD02: Decision tree segment merging at safe nonterminal boundaries.
    SegmentMerging,
    /// CD03: Computed goto dispatch via function pointer tables.
    ComputedGoto,
    /// CD04: Jump threading through decision tree branches.
    JumpThreading,
    /// CD05: Prefix CSE for shared nonterminal parses.
    PrefixCse,

    /// DB01: Incremental FIRST/FOLLOW recomputation.
    IncrementalFirstFollow,
    /// DB02: Lazy analysis phase execution (skip for small grammars).
    LazyAnalysis,
    /// DB03: Parallel analysis phase execution.
    ParallelAnalysis,
    /// DB04: Cached lint results across builds.
    CachedLints,
}

impl fmt::Display for Optimization {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LeftFactoring => write!(f, "A1:LeftFactoring"),
            Self::HotColdSplitting => write!(f, "A2:HotColdSplitting"),
            Self::EnhancedDeadCodeElimination => write!(f, "A4:EnhancedDCE"),
            Self::AmbiguityTargeting => write!(f, "A5:AmbiguityTargeting"),
            Self::MultiTokenLookahead => write!(f, "B1:MultiTokenLookahead"),
            Self::AdaptiveRecovery => write!(f, "B2:AdaptiveRecovery"),
            Self::WfstMinimization => write!(f, "B3:WfstMinimization"),
            Self::SpilloverPruning => write!(f, "F1:SpilloverPruning"),
            Self::EarlyTermination => write!(f, "F2:EarlyTermination"),
            Self::LazySpillover => write!(f, "F3:LazySpillover"),
            Self::BacktrackingElimination => write!(f, "G1:BacktrackingElimination"),
            Self::ContextDisambiguation => write!(f, "H1:ContextDisambiguation"),
            Self::WpdsReachabilityCheck => write!(f, "G25:WpdsReachabilityCheck"),
            Self::TrsConfluenceCheck => write!(f, "T01:TrsConfluenceCheck"),
            Self::VpaInclusionCheck => write!(f, "V01:VpaInclusionCheck"),
            Self::SafetyVerification => write!(f, "S01:SafetyVerification"),
            Self::CegarRefinement => write!(f, "S03:CegarRefinement"),
            Self::PetriDeadlockCheck => write!(f, "N01:PetriDeadlockCheck"),
            #[cfg(feature = "symbolic-automata")]
            Self::SymbolicGuardAnalysis => write!(f, "SYM01:SymbolicGuardAnalysis"),
            #[cfg(feature = "omega")]
            Self::WeightedBuchiAnalysis => write!(f, "O01:WeightedBuchiAnalysis"),
            #[cfg(feature = "alternating")]
            Self::WeightedAlternatingAnalysis => write!(f, "N06:WeightedAlternatingAnalysis"),
            #[cfg(feature = "vpa")]
            Self::WeightedVpaAnalysis => write!(f, "V05:WeightedVpaAnalysis"),
            #[cfg(feature = "parity-tree-automata")]
            Self::ParityTreeAnalysis => write!(f, "PT01:ParityTreeAnalysis"),
            #[cfg(feature = "register-automata")]
            Self::RegisterAnalysis => write!(f, "RA01:RegisterAnalysis"),
            #[cfg(feature = "probabilistic")]
            Self::ProbabilisticAnalysis => write!(f, "PR01:ProbabilisticAnalysis"),
            #[cfg(feature = "multi-tape")]
            Self::MultiTapeAnalysis => write!(f, "MT01:MultiTapeAnalysis"),
            #[cfg(feature = "multiset-automata")]
            Self::MultisetAnalysis => write!(f, "MS01:MultisetAnalysis"),
            #[cfg(feature = "weighted-mso")]
            Self::WeightedMsoAnalysis => write!(f, "MSO01:WeightedMsoAnalysis"),
            #[cfg(feature = "two-way-transducer")]
            Self::TwoWayTransducerAnalysis => write!(f, "TW01:TwoWayTransducerAnalysis"),
            #[cfg(feature = "predicate-dispatch")]
            Self::PredicateDispatch => write!(f, "PD01:PredicateDispatch"),
            Self::HashConsing => write!(f, "ART01:HashConsing"),
            Self::IncrementalDelta => write!(f, "ART02:IncrementalDelta"),
            Self::RelationIndexing => write!(f, "ART03:RelationIndexing"),
            Self::CongruenceBloom => write!(f, "ART04:CongruenceBloom"),
            Self::DepthBound => write!(f, "ART05:DepthBound"),
            Self::DemandDriven => write!(f, "ART06:DemandDriven"),
            Self::JoinOrdering => write!(f, "BCG01:JoinOrdering"),
            Self::RuleFusion => write!(f, "BCG02:RuleFusion"),
            Self::EqCongruencePrune => write!(f, "BCG03:EqCongruencePrune"),
            Self::GroundShortCircuit => write!(f, "BCG04:GroundShortCircuit"),
            Self::NormalizeDedup => write!(f, "BCG05:NormalizeDedup"),
            Self::EqStrata => write!(f, "BCG06:EqStrata"),
            Self::CombRepacking => write!(f, "AL01:CombRepacking"),
            Self::HybridLexer => write!(f, "AL02:HybridLexer"),
            Self::SimdWhitespace => write!(f, "AL03:SimdWhitespace"),
            Self::KeywordMph => write!(f, "AL04:KeywordMph"),
            Self::MultiByteChain => write!(f, "AL05:MultiByteChain"),
            Self::AcceptBitmapWiden => write!(f, "AL06:AcceptBitmapWiden"),
            Self::BpCompaction => write!(f, "BP01:BpCompaction"),
            Self::TailCallElim => write!(f, "BP02:TailCallElim"),
            Self::BpTableLookup => write!(f, "BP03:BpTableLookup"),
            Self::TrivialInline => write!(f, "BP04:TrivialInline"),
            Self::BpRangeLoop => write!(f, "BP05:BpRangeLoop"),
            Self::FrequencyOrdering => write!(f, "CD01:FrequencyOrdering"),
            Self::SegmentMerging => write!(f, "CD02:SegmentMerging"),
            Self::ComputedGoto => write!(f, "CD03:ComputedGoto"),
            Self::JumpThreading => write!(f, "CD04:JumpThreading"),
            Self::PrefixCse => write!(f, "CD05:PrefixCse"),
            Self::IncrementalFirstFollow => write!(f, "DB01:IncrementalFirstFollow"),
            Self::LazyAnalysis => write!(f, "DB02:LazyAnalysis"),
            Self::ParallelAnalysis => write!(f, "DB03:ParallelAnalysis"),
            Self::CachedLints => write!(f, "DB04:CachedLints"),
        }
    }
}

impl std::str::FromStr for Optimization {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim() {
            // Short codes
            "A1" => Ok(Self::LeftFactoring),
            "A2" => Ok(Self::HotColdSplitting),
            "A4" => Ok(Self::EnhancedDeadCodeElimination),
            "A5" => Ok(Self::AmbiguityTargeting),
            "B1" => Ok(Self::MultiTokenLookahead),
            "B2" => Ok(Self::AdaptiveRecovery),
            "B3" => Ok(Self::WfstMinimization),
            "F1" => Ok(Self::SpilloverPruning),
            "F2" => Ok(Self::EarlyTermination),
            "F3" => Ok(Self::LazySpillover),
            "G1" => Ok(Self::BacktrackingElimination),
            "H1" => Ok(Self::ContextDisambiguation),
            "G25" => Ok(Self::WpdsReachabilityCheck),
            // Full names (case-insensitive)
            s if s.eq_ignore_ascii_case("LeftFactoring") => Ok(Self::LeftFactoring),
            s if s.eq_ignore_ascii_case("HotColdSplitting") => Ok(Self::HotColdSplitting),
            s if s.eq_ignore_ascii_case("EnhancedDeadCodeElimination")
                || s.eq_ignore_ascii_case("EnhancedDCE") =>
            {
                Ok(Self::EnhancedDeadCodeElimination)
            },
            s if s.eq_ignore_ascii_case("AmbiguityTargeting") => Ok(Self::AmbiguityTargeting),
            s if s.eq_ignore_ascii_case("MultiTokenLookahead") => Ok(Self::MultiTokenLookahead),
            s if s.eq_ignore_ascii_case("AdaptiveRecovery") => Ok(Self::AdaptiveRecovery),
            s if s.eq_ignore_ascii_case("WfstMinimization") => Ok(Self::WfstMinimization),
            s if s.eq_ignore_ascii_case("SpilloverPruning") => Ok(Self::SpilloverPruning),
            s if s.eq_ignore_ascii_case("EarlyTermination") => Ok(Self::EarlyTermination),
            s if s.eq_ignore_ascii_case("LazySpillover") => Ok(Self::LazySpillover),
            s if s.eq_ignore_ascii_case("BacktrackingElimination") => Ok(Self::BacktrackingElimination),
            s if s.eq_ignore_ascii_case("ContextDisambiguation") => Ok(Self::ContextDisambiguation),
            s if s.eq_ignore_ascii_case("WpdsReachabilityCheck") => Ok(Self::WpdsReachabilityCheck),
            "T01" => Ok(Self::TrsConfluenceCheck),
            s if s.eq_ignore_ascii_case("TrsConfluenceCheck") => Ok(Self::TrsConfluenceCheck),
            "V01" => Ok(Self::VpaInclusionCheck),
            s if s.eq_ignore_ascii_case("VpaInclusionCheck") => Ok(Self::VpaInclusionCheck),
            "S01" => Ok(Self::SafetyVerification),
            s if s.eq_ignore_ascii_case("SafetyVerification") => Ok(Self::SafetyVerification),
            "S03" => Ok(Self::CegarRefinement),
            s if s.eq_ignore_ascii_case("CegarRefinement") => Ok(Self::CegarRefinement),
            "N01" => Ok(Self::PetriDeadlockCheck),
            s if s.eq_ignore_ascii_case("PetriDeadlockCheck") => Ok(Self::PetriDeadlockCheck),
            #[cfg(feature = "symbolic-automata")]
            "SYM01" => Ok(Self::SymbolicGuardAnalysis),
            #[cfg(feature = "symbolic-automata")]
            s if s.eq_ignore_ascii_case("SymbolicGuardAnalysis") => Ok(Self::SymbolicGuardAnalysis),
            #[cfg(feature = "omega")]
            "O01" => Ok(Self::WeightedBuchiAnalysis),
            #[cfg(feature = "omega")]
            s if s.eq_ignore_ascii_case("WeightedBuchiAnalysis") => Ok(Self::WeightedBuchiAnalysis),
            #[cfg(feature = "alternating")]
            "N06" => Ok(Self::WeightedAlternatingAnalysis),
            #[cfg(feature = "alternating")]
            s if s.eq_ignore_ascii_case("WeightedAlternatingAnalysis") => Ok(Self::WeightedAlternatingAnalysis),
            #[cfg(feature = "vpa")]
            "V05" => Ok(Self::WeightedVpaAnalysis),
            #[cfg(feature = "vpa")]
            s if s.eq_ignore_ascii_case("WeightedVpaAnalysis") => Ok(Self::WeightedVpaAnalysis),
            #[cfg(feature = "parity-tree-automata")]
            "PT01" => Ok(Self::ParityTreeAnalysis),
            #[cfg(feature = "parity-tree-automata")]
            s if s.eq_ignore_ascii_case("ParityTreeAnalysis") => Ok(Self::ParityTreeAnalysis),
            #[cfg(feature = "register-automata")]
            "RA01" => Ok(Self::RegisterAnalysis),
            #[cfg(feature = "register-automata")]
            s if s.eq_ignore_ascii_case("RegisterAnalysis") => Ok(Self::RegisterAnalysis),
            #[cfg(feature = "probabilistic")]
            "PR01" => Ok(Self::ProbabilisticAnalysis),
            #[cfg(feature = "probabilistic")]
            s if s.eq_ignore_ascii_case("ProbabilisticAnalysis") => Ok(Self::ProbabilisticAnalysis),
            #[cfg(feature = "multi-tape")]
            "MT01" => Ok(Self::MultiTapeAnalysis),
            #[cfg(feature = "multi-tape")]
            s if s.eq_ignore_ascii_case("MultiTapeAnalysis") => Ok(Self::MultiTapeAnalysis),
            #[cfg(feature = "multiset-automata")]
            "MS01" => Ok(Self::MultisetAnalysis),
            #[cfg(feature = "multiset-automata")]
            s if s.eq_ignore_ascii_case("MultisetAnalysis") => Ok(Self::MultisetAnalysis),
            #[cfg(feature = "weighted-mso")]
            "MSO01" => Ok(Self::WeightedMsoAnalysis),
            #[cfg(feature = "weighted-mso")]
            s if s.eq_ignore_ascii_case("WeightedMsoAnalysis") => Ok(Self::WeightedMsoAnalysis),
            #[cfg(feature = "two-way-transducer")]
            "TW01" => Ok(Self::TwoWayTransducerAnalysis),
            #[cfg(feature = "two-way-transducer")]
            s if s.eq_ignore_ascii_case("TwoWayTransducerAnalysis") => Ok(Self::TwoWayTransducerAnalysis),
            #[cfg(feature = "predicate-dispatch")]
            "PD01" => Ok(Self::PredicateDispatch),
            #[cfg(feature = "predicate-dispatch")]
            s if s.eq_ignore_ascii_case("PredicateDispatch") => Ok(Self::PredicateDispatch),
            "ART01" => Ok(Self::HashConsing),
            "ART02" => Ok(Self::IncrementalDelta),
            "ART03" => Ok(Self::RelationIndexing),
            "ART04" => Ok(Self::CongruenceBloom),
            "ART05" => Ok(Self::DepthBound),
            "ART06" => Ok(Self::DemandDriven),
            "BCG01" => Ok(Self::JoinOrdering),
            "BCG02" => Ok(Self::RuleFusion),
            "BCG03" => Ok(Self::EqCongruencePrune),
            "BCG04" => Ok(Self::GroundShortCircuit),
            "BCG05" => Ok(Self::NormalizeDedup),
            "BCG06" => Ok(Self::EqStrata),
            "AL01" => Ok(Self::CombRepacking),
            "AL02" => Ok(Self::HybridLexer),
            "AL03" => Ok(Self::SimdWhitespace),
            "AL04" => Ok(Self::KeywordMph),
            "AL05" => Ok(Self::MultiByteChain),
            "AL06" => Ok(Self::AcceptBitmapWiden),
            "BP01" => Ok(Self::BpCompaction),
            "BP02" => Ok(Self::TailCallElim),
            "BP03" => Ok(Self::BpTableLookup),
            "BP04" => Ok(Self::TrivialInline),
            "BP05" => Ok(Self::BpRangeLoop),
            "CD01" => Ok(Self::FrequencyOrdering),
            "CD02" => Ok(Self::SegmentMerging),
            "CD03" => Ok(Self::ComputedGoto),
            "CD04" => Ok(Self::JumpThreading),
            "CD05" => Ok(Self::PrefixCse),
            "DB01" => Ok(Self::IncrementalFirstFollow),
            "DB02" => Ok(Self::LazyAnalysis),
            "DB03" => Ok(Self::ParallelAnalysis),
            "DB04" => Ok(Self::CachedLints),
            s if s.eq_ignore_ascii_case("HashConsing") => Ok(Self::HashConsing),
            s if s.eq_ignore_ascii_case("IncrementalDelta") => Ok(Self::IncrementalDelta),
            s if s.eq_ignore_ascii_case("RelationIndexing") => Ok(Self::RelationIndexing),
            s if s.eq_ignore_ascii_case("CongruenceBloom") => Ok(Self::CongruenceBloom),
            s if s.eq_ignore_ascii_case("DepthBound") => Ok(Self::DepthBound),
            s if s.eq_ignore_ascii_case("DemandDriven") => Ok(Self::DemandDriven),
            s if s.eq_ignore_ascii_case("JoinOrdering") => Ok(Self::JoinOrdering),
            s if s.eq_ignore_ascii_case("RuleFusion") => Ok(Self::RuleFusion),
            s if s.eq_ignore_ascii_case("EqCongruencePrune") => Ok(Self::EqCongruencePrune),
            s if s.eq_ignore_ascii_case("GroundShortCircuit") => Ok(Self::GroundShortCircuit),
            s if s.eq_ignore_ascii_case("NormalizeDedup") => Ok(Self::NormalizeDedup),
            s if s.eq_ignore_ascii_case("EqStrata") => Ok(Self::EqStrata),
            s if s.eq_ignore_ascii_case("CombRepacking") => Ok(Self::CombRepacking),
            s if s.eq_ignore_ascii_case("HybridLexer") => Ok(Self::HybridLexer),
            s if s.eq_ignore_ascii_case("SimdWhitespace") => Ok(Self::SimdWhitespace),
            s if s.eq_ignore_ascii_case("KeywordMph") => Ok(Self::KeywordMph),
            s if s.eq_ignore_ascii_case("MultiByteChain") => Ok(Self::MultiByteChain),
            s if s.eq_ignore_ascii_case("AcceptBitmapWiden") => Ok(Self::AcceptBitmapWiden),
            s if s.eq_ignore_ascii_case("BpCompaction") => Ok(Self::BpCompaction),
            s if s.eq_ignore_ascii_case("TailCallElim") => Ok(Self::TailCallElim),
            s if s.eq_ignore_ascii_case("BpTableLookup") => Ok(Self::BpTableLookup),
            s if s.eq_ignore_ascii_case("TrivialInline") => Ok(Self::TrivialInline),
            s if s.eq_ignore_ascii_case("BpRangeLoop") => Ok(Self::BpRangeLoop),
            s if s.eq_ignore_ascii_case("FrequencyOrdering") => Ok(Self::FrequencyOrdering),
            s if s.eq_ignore_ascii_case("SegmentMerging") => Ok(Self::SegmentMerging),
            s if s.eq_ignore_ascii_case("ComputedGoto") => Ok(Self::ComputedGoto),
            s if s.eq_ignore_ascii_case("JumpThreading") => Ok(Self::JumpThreading),
            s if s.eq_ignore_ascii_case("PrefixCse") => Ok(Self::PrefixCse),
            s if s.eq_ignore_ascii_case("IncrementalFirstFollow") => Ok(Self::IncrementalFirstFollow),
            s if s.eq_ignore_ascii_case("LazyAnalysis") => Ok(Self::LazyAnalysis),
            s if s.eq_ignore_ascii_case("ParallelAnalysis") => Ok(Self::ParallelAnalysis),
            s if s.eq_ignore_ascii_case("CachedLints") => Ok(Self::CachedLints),
            // Display format: "A1:LeftFactoring"
            s if s.contains(':') => s
                .split_once(':')
                .map(|(code, _)| code)
                .unwrap_or(s)
                .parse(),
            other => Err(format!(
                "unknown optimization: '{}'. Valid values: A1, A2, A4, A5, B1, B2, B3, F1, F2, F3, G1, H1, G25, T01, V01, S01, S03, N01, \
                 SYM01, O01, N06, V05, PT01, RA01, PR01, MT01, MS01, MSO01, TW01, \
                 ART01-ART06, BCG01-BCG06, AL01-AL06, BP01-BP05, CD01-CD05, DB01-DB04",
                other
            )),
        }
    }
}

/// A candidate optimization with cost-benefit analysis.
#[derive(Debug, Clone)]
pub struct OptimizationCandidate {
    /// Which optimization this is.
    pub optimization: Optimization,
    /// Estimated speedup (tropical: lower = more speedup).
    pub speedup: TropicalWeight,
    /// Estimated compile cost (tropical: lower = cheaper).
    pub compile_cost: TropicalWeight,
    /// Combined score: `ProductWeight<speedup, compile_cost>` with lexicographic
    /// ordering. Lower is better.
    pub score: ProductWeight<TropicalWeight, TropicalWeight>,
    /// Whether this optimization is applicable to the current grammar.
    pub applicable: bool,
    /// Human-readable reason for applicability decision.
    pub reason: String,
}

impl OptimizationCandidate {
    fn new(
        optimization: Optimization,
        speedup: f64,
        compile_cost: f64,
        applicable: bool,
        reason: String,
    ) -> Self {
        let speedup_w = TropicalWeight::new(speedup);
        let compile_cost_w = TropicalWeight::new(compile_cost);
        OptimizationCandidate {
            optimization,
            speedup: speedup_w,
            compile_cost: compile_cost_w,
            score: ProductWeight::new(speedup_w, compile_cost_w),
            applicable,
            reason,
        }
    }
}

/// Grammar profile extracted from WFST analysis and PathMap decision trees.
///
/// Computed once during pipeline execution and passed to `evaluate_optimizations()`.
#[derive(Debug, Clone)]
pub struct GrammarProfile {
    /// Fraction of dispatch tokens that share a prefix with another rule (0.0..1.0).
    pub shared_prefix_ratio: f64,
    /// Fraction of dispatch arms with weight >= cold threshold (0.0..1.0).
    pub cold_fraction: f64,
    /// Fraction of dispatch tokens that are ambiguous (CountingWeight > 1) (0.0..1.0).
    pub ambiguous_fraction: f64,
    /// Number of ambiguous dispatch tokens across all categories.
    pub ambiguous_count: usize,
    /// Total number of categories in the grammar.
    pub category_count: usize,
    /// Total number of rules in the grammar.
    pub rule_count: usize,
    /// Number of categories requiring NFA spillover.
    pub nfa_spillover_categories: usize,
    /// Whether beam width is configured.
    pub has_beam_width: bool,
    /// Number of PredictionWfst states (sum across all categories).
    pub total_wfst_states: usize,

    // ── PathMap decision tree metrics ─────────────────────────────────────
    /// Mean max_depth across all category decision trees.
    pub avg_trie_depth: f64,
    /// Fraction of ambiguous nodes across all decision trees (ambiguous / total_states).
    pub ambiguity_score: f64,
    /// Fraction of rules that have fully deterministic dispatch (no ambiguity at prefix).
    pub deterministic_ratio: f64,

    // ── Advanced automata codegen promotion metrics ───────────────────────

    /// Number of unsatisfiable guards detected by symbolic analysis.
    #[cfg(feature = "symbolic-automata")]
    pub unsatisfiable_guard_count: usize,

    /// Mean entropy from probabilistic analysis (higher = more ambiguous).
    #[cfg(feature = "probabilistic")]
    pub probabilistic_mean_entropy: f64,

    /// Number of low-selectivity rules from probabilistic analysis.
    #[cfg(feature = "probabilistic")]
    pub low_selectivity_count: usize,

    /// Number of bisimulation-equivalent category pairs beyond De Bruijn groups.
    #[cfg(feature = "alternating")]
    pub bisimulation_extra_groups: usize,

    /// Number of dead binder registers.
    #[cfg(feature = "register-automata")]
    pub dead_register_count: usize,
}

/// Build a `GrammarProfile` from pipeline data and decision tree metrics.
///
/// This is the main analysis entry point, called from the pipeline after
/// WFST and decision tree construction.
pub fn build_grammar_profile(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    nfa_spillover_cats: &std::collections::HashSet<String>,
    rule_count: usize,
    has_beam_width: bool,
    decision_trees: &HashMap<String, crate::decision_tree::CategoryDecisionTree>,
) -> GrammarProfile {
    let category_count = prediction_wfsts.len();

    // Count ambiguous dispatch tokens (prediction returns > 1 action for a token)
    let mut total_dispatch_tokens = 0usize;
    let mut ambiguous_tokens = 0usize;

    for (cat, wfst) in prediction_wfsts {
        if let Some(first_set) = first_sets.get(cat) {
            for token in &first_set.tokens {
                total_dispatch_tokens += 1;
                let predictions = wfst.predict(token);
                if predictions.len() > 1 {
                    ambiguous_tokens += 1;
                }
            }
        }
    }

    let ambiguous_fraction = if total_dispatch_tokens > 0 {
        ambiguous_tokens as f64 / total_dispatch_tokens as f64
    } else {
        0.0
    };

    // Cold fraction: count dispatch actions with weight >= 1.0
    let mut total_actions = 0usize;
    let mut cold_actions = 0usize;

    for wfst in prediction_wfsts.values() {
        for action in &wfst.actions {
            total_actions += 1;
            if action.weight.value() >= 1.0 {
                cold_actions += 1;
            }
        }
    }

    let cold_fraction = if total_actions > 0 {
        cold_actions as f64 / total_actions as f64
    } else {
        0.0
    };

    // Shared prefix ratio: count NFA-ambiguous categories / total
    let shared_prefix_ratio = if category_count > 0 {
        nfa_spillover_cats.len() as f64 / category_count as f64
    } else {
        0.0
    };

    // Total WFST states
    let total_wfst_states: usize = prediction_wfsts.values().map(|w| w.states.len()).sum();

    // PathMap decision tree metrics
    let (avg_trie_depth, ambiguity_score, deterministic_ratio) = if decision_trees.is_empty() {
        (0.0, 0.0, 1.0)
    } else {
        let mut total_depth = 0usize;
        let mut total_ambiguous = 0usize;
        let mut total_states = 0usize;
        let mut total_det_rules = 0usize;
        let mut total_rules = 0usize;
        for tree in decision_trees.values() {
            total_depth += tree.stats.max_depth;
            total_ambiguous += tree.stats.ambiguous_nodes;
            total_states += tree.stats.total_states;
            total_det_rules += tree.stats.deterministic_rules;
            total_rules += tree.stats.total_rules;
        }
        let n = decision_trees.len() as f64;
        (
            total_depth as f64 / n,
            if total_states > 0 { total_ambiguous as f64 / total_states as f64 } else { 0.0 },
            if total_rules > 0 { total_det_rules as f64 / total_rules as f64 } else { 1.0 },
        )
    };

    GrammarProfile {
        shared_prefix_ratio,
        cold_fraction,
        ambiguous_fraction,
        ambiguous_count: ambiguous_tokens,
        category_count,
        rule_count,
        nfa_spillover_categories: nfa_spillover_cats.len(),
        has_beam_width,
        total_wfst_states,
        avg_trie_depth,
        ambiguity_score,
        deterministic_ratio,
        // Advanced automata metrics — populated from PipelineAnalysis at the call site.
        // Defaults to zero here; the caller enriches after construction.
        #[cfg(feature = "symbolic-automata")]
        unsatisfiable_guard_count: 0,
        #[cfg(feature = "probabilistic")]
        probabilistic_mean_entropy: 0.0,
        #[cfg(feature = "probabilistic")]
        low_selectivity_count: 0,
        #[cfg(feature = "alternating")]
        bisimulation_extra_groups: 0,
        #[cfg(feature = "register-automata")]
        dead_register_count: 0,
    }
}

/// Evaluate all optimizations against the grammar profile.
///
/// Returns candidates sorted by score (best first, via lexicographic ordering
/// on `ProductWeight<speedup, compile_cost>`). Only `applicable` candidates
/// should be acted upon.
pub fn evaluate_optimizations(profile: &GrammarProfile) -> Vec<OptimizationCandidate> {
    let mut candidates = Vec::with_capacity(50);

    // A1: Left-factoring — beneficial when many rules share prefixes
    candidates.push(OptimizationCandidate::new(
        Optimization::LeftFactoring,
        // speedup: -ln(shared_prefix_ratio) — more sharing = lower (better) weight
        if profile.shared_prefix_ratio > 0.0 {
            -profile.shared_prefix_ratio.ln()
        } else {
            f64::INFINITY
        },
        // cost: proportional to category count (each category may need factoring)
        profile.category_count as f64 * 0.1,
        profile.shared_prefix_ratio > 0.3,
        format!(
            "shared_prefix_ratio={:.2} (threshold: >0.3)",
            profile.shared_prefix_ratio
        ),
    ));

    // A2: Hot/cold splitting — beneficial when many dispatch arms are cold
    candidates.push(OptimizationCandidate::new(
        Optimization::HotColdSplitting,
        // speedup: -ln(cold_fraction)
        if profile.cold_fraction > 0.0 {
            -profile.cold_fraction.ln()
        } else {
            f64::INFINITY
        },
        0.05, // fixed low cost
        profile.cold_fraction > 0.4,
        format!(
            "cold_fraction={:.2} (threshold: >0.4)",
            profile.cold_fraction
        ),
    ));

    // A4: Enhanced DCE — always beneficial for grammar validation
    candidates.push(OptimizationCandidate::new(
        Optimization::EnhancedDeadCodeElimination,
        0.5, // moderate speedup (removes dead codegen)
        0.2, // low-medium cost
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // A5: Ambiguity targeting — enables B1, useful when there's ambiguity
    candidates.push(OptimizationCandidate::new(
        Optimization::AmbiguityTargeting,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln()
        } else {
            f64::INFINITY
        },
        0.1, // low cost (analysis only)
        profile.ambiguous_fraction > 0.1,
        format!(
            "ambiguous_fraction={:.2} (threshold: >0.1)",
            profile.ambiguous_fraction
        ),
    ));

    // B1: Multi-token lookahead — beneficial for ambiguous grammars with few tokens
    candidates.push(OptimizationCandidate::new(
        Optimization::MultiTokenLookahead,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln()
        } else {
            f64::INFINITY
        },
        profile.ambiguous_count as f64 * 0.5,
        profile.ambiguous_fraction > 0.1 && profile.ambiguous_count < 10,
        format!(
            "ambiguous_fraction={:.2}, ambiguous_count={} (thresholds: >0.1, <10)",
            profile.ambiguous_fraction, profile.ambiguous_count
        ),
    ));

    // B2: Adaptive recovery — always applicable, zero happy-path cost
    candidates.push(OptimizationCandidate::new(
        Optimization::AdaptiveRecovery,
        0.3, // modest benefit (error path only)
        0.1, // low cost
        true,
        "always applicable (zero happy-path overhead)".to_string(),
    ));

    // B3: WFST minimization — beneficial when WFST has many states
    candidates.push(OptimizationCandidate::new(
        Optimization::WfstMinimization,
        if profile.total_wfst_states > 0 {
            -(profile.total_wfst_states as f64).ln()
        } else {
            f64::INFINITY
        },
        0.15,
        profile.total_wfst_states > 4,
        format!(
            "total_wfst_states={} (threshold: >4)",
            profile.total_wfst_states
        ),
    ));

    // F1: Spillover pruning — beneficial when beam is set and there's spillover
    candidates.push(OptimizationCandidate::new(
        Optimization::SpilloverPruning,
        0.2, // low weight = high benefit
        0.01, // trivial cost
        profile.has_beam_width && profile.nfa_spillover_categories > 0,
        format!(
            "has_beam_width={}, nfa_spillover_categories={}",
            profile.has_beam_width, profile.nfa_spillover_categories
        ),
    ));

    // F2: Early termination — beneficial when deterministic alternatives exist
    candidates.push(OptimizationCandidate::new(
        Optimization::EarlyTermination,
        0.1, // very beneficial
        0.01, // trivial cost
        profile.nfa_spillover_categories == 0 && profile.ambiguous_count > 0,
        format!(
            "nfa_spillover_categories={}, ambiguous_count={}",
            profile.nfa_spillover_categories, profile.ambiguous_count
        ),
    ));

    // F3: Lazy spillover — beneficial when there's spillover
    candidates.push(OptimizationCandidate::new(
        Optimization::LazySpillover,
        0.3,
        0.3, // medium cost (refactoring parse_preserving_vars)
        profile.nfa_spillover_categories > 0,
        format!(
            "nfa_spillover_categories={}",
            profile.nfa_spillover_categories
        ),
    ));

    // G1: Backtracking elimination — always beneficial (removes redundant save/restore)
    candidates.push(OptimizationCandidate::new(
        Optimization::BacktrackingElimination,
        0.2, // good speedup (eliminates speculative parses)
        0.1, // low cost (compile-time FIRST set analysis)
        true,
        "always applicable (static FIRST set analysis)".to_string(),
    ));

    // H1: ContextWeight-based disambiguation
    candidates.push(OptimizationCandidate::new(
        Optimization::ContextDisambiguation,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln() * 0.8
        } else {
            f64::INFINITY
        },
        0.2,
        profile.nfa_spillover_categories > 0 && profile.ambiguous_fraction > 0.05,
        format!(
            "nfa_spillover_categories={}, ambiguous_fraction={:.2}",
            profile.nfa_spillover_categories, profile.ambiguous_fraction
        ),
    ));

    // G25: WPDS stack-aware reachability — beneficial for multi-category grammars
    candidates.push(OptimizationCandidate::new(
        Optimization::WpdsReachabilityCheck,
        0.4, // moderate benefit (refines dead-rule detection)
        0.3, // medium cost (WPDS construction + poststar saturation)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count
        ),
    ));

    // T01: TRS confluence check — beneficial when rules have overlapping patterns
    candidates.push(OptimizationCandidate::new(
        Optimization::TrsConfluenceCheck,
        0.5, // diagnostic benefit (catches rewriting bugs)
        0.15, // low cost (critical pair enumeration)
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // V01: VPA inclusion check — beneficial for grammars with delimiter structure
    candidates.push(OptimizationCandidate::new(
        Optimization::VpaInclusionCheck,
        0.6, // diagnostic benefit (identifies zero-backtracking sublanguage)
        0.1, // low cost (VPA construction)
        profile.category_count >= 1,
        format!(
            "category_count={} (threshold: >=1)",
            profile.category_count,
        ),
    ));

    // S01: Safety verification — beneficial when WPDS detects unreachable rules
    candidates.push(OptimizationCandidate::new(
        Optimization::SafetyVerification,
        0.3, // good benefit (confirms unreachability with prestar)
        0.25, // moderate cost (prestar saturation)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count,
        ),
    ));

    // S03: CEGAR refinement — beneficial when WPDS reports unreachable rules
    candidates.push(OptimizationCandidate::new(
        Optimization::CegarRefinement,
        0.45, // diagnostic benefit
        0.3, // medium cost (iterative refinement)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count,
        ),
    ));

    // N01: Petri net deadlock check — beneficial for grammars with parallel composition
    candidates.push(OptimizationCandidate::new(
        Optimization::PetriDeadlockCheck,
        0.7, // diagnostic benefit (deadlock detection)
        0.1, // low cost (coverability check)
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // SYM01: Symbolic guard analysis — Auto: unsatisfiable guards → dead rule elimination
    #[cfg(feature = "symbolic-automata")]
    candidates.push(OptimizationCandidate::new(
        Optimization::SymbolicGuardAnalysis,
        if profile.unsatisfiable_guard_count > 0 { 0.3 } else { 0.5 },
        0.15, // low cost (reuses existing SFA analysis)
        profile.rule_count > 5,
        format!(
            "rule_count={}, unsatisfiable_guards={} → dead rule elimination",
            profile.rule_count, profile.unsatisfiable_guard_count
        ),
    ));

    // O01: Weighted Büchi analysis — beneficial for liveness checking
    #[cfg(feature = "omega")]
    candidates.push(OptimizationCandidate::new(
        Optimization::WeightedBuchiAnalysis,
        0.6, // diagnostic benefit (liveness verification)
        0.1, // low cost
        profile.category_count >= 2,
        format!("category_count={} (threshold: >=2)", profile.category_count),
    ));

    // N06: Weighted alternating analysis — Auto: bisimulation → extended isomorphic groups
    #[cfg(feature = "alternating")]
    candidates.push(OptimizationCandidate::new(
        Optimization::WeightedAlternatingAnalysis,
        if profile.bisimulation_extra_groups > 0 { 0.3 } else { 0.5 },
        0.2, // moderate cost
        profile.rule_count > 5,
        format!(
            "rule_count={}, bisim_extra_groups={} → shared dispatch templates",
            profile.rule_count, profile.bisimulation_extra_groups
        ),
    ));

    // V05: Weighted VPA analysis — beneficial for nested structure analysis
    #[cfg(feature = "vpa")]
    candidates.push(OptimizationCandidate::new(
        Optimization::WeightedVpaAnalysis,
        0.5, // diagnostic benefit (weighted determinization)
        0.15, // low cost
        profile.category_count >= 1,
        format!("category_count={} (threshold: >=1)", profile.category_count),
    ));

    // PT01: Parity tree analysis — beneficial for AST verification
    #[cfg(feature = "parity-tree-automata")]
    candidates.push(OptimizationCandidate::new(
        Optimization::ParityTreeAnalysis,
        0.7, // diagnostic benefit (mu-calculus verification)
        0.2, // moderate cost
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // RA01: Register analysis — Auto: dead registers → skip binder alpha-equiv
    #[cfg(feature = "register-automata")]
    candidates.push(OptimizationCandidate::new(
        Optimization::RegisterAnalysis,
        if profile.dead_register_count > 0 { 0.3 } else { 0.6 },
        0.1, // low cost
        profile.category_count >= 1,
        format!(
            "category_count={}, dead_registers={} → skip binder α-equiv",
            profile.category_count, profile.dead_register_count
        ),
    ));

    // PR01: Probabilistic analysis — Auto: DCE + weight blending
    #[cfg(feature = "probabilistic")]
    candidates.push(OptimizationCandidate::new(
        Optimization::ProbabilisticAnalysis,
        if profile.low_selectivity_count > 0 { 0.25 } else { 0.4 },
        0.15, // low cost
        profile.rule_count > 3,
        format!(
            "rule_count={}, low_selectivity={}, entropy={:.2} → DCE + weight blend",
            profile.rule_count, profile.low_selectivity_count,
            profile.probabilistic_mean_entropy
        ),
    ));

    // MT01: Multi-tape analysis — beneficial for multi-stream parsing
    #[cfg(feature = "multi-tape")]
    candidates.push(OptimizationCandidate::new(
        Optimization::MultiTapeAnalysis,
        0.5, // diagnostic benefit (tape interaction analysis)
        0.1, // low cost
        profile.category_count >= 2,
        format!("category_count={} (threshold: >=2)", profile.category_count),
    ));

    // MS01: Multiset analysis — beneficial for resource counting
    #[cfg(feature = "multiset-automata")]
    candidates.push(OptimizationCandidate::new(
        Optimization::MultisetAnalysis,
        0.5, // diagnostic benefit (cardinality constraints)
        0.1, // low cost
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // MSO01: Weighted MSO analysis — beneficial for formula classification
    #[cfg(feature = "weighted-mso")]
    candidates.push(OptimizationCandidate::new(
        Optimization::WeightedMsoAnalysis,
        0.4, // diagnostic benefit (decidability classification)
        0.15, // low cost
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // TW01: Two-way transducer analysis — beneficial for deadlock detection
    #[cfg(feature = "two-way-transducer")]
    candidates.push(OptimizationCandidate::new(
        Optimization::TwoWayTransducerAnalysis,
        0.6, // diagnostic benefit (deadlock cycle detection)
        0.15, // low cost
        profile.category_count >= 2,
        format!("category_count={} (threshold: >=2)", profile.category_count),
    ));

    // ── Tier 1: Low complexity ───────────────────────────────────────────

    // ART03: Relation indexing — beneficial for grammars with many rules
    candidates.push(OptimizationCandidate::new(
        Optimization::RelationIndexing,
        0.3,
        0.05,
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // BCG04: Ground-term short-circuit — beneficial for grammars with rewrite rules
    candidates.push(OptimizationCandidate::new(
        Optimization::GroundShortCircuit,
        0.4,
        0.05,
        profile.rule_count > 2,
        format!("rule_count={} (threshold: >2)", profile.rule_count),
    ));

    // BP04: Prefix handler inlining for trivial rules — always applicable
    candidates.push(OptimizationCandidate::new(
        Optimization::TrivialInline,
        0.3,
        0.05,
        true,
        "always applicable (trivial prefix handlers)".to_string(),
    ));

    // BP01: Pratt BP table compaction — beneficial when categories exist
    candidates.push(OptimizationCandidate::new(
        Optimization::BpCompaction,
        0.25,
        0.05,
        profile.category_count >= 1,
        format!(
            "category_count={} (threshold: >=1)",
            profile.category_count
        ),
    ));

    // AL06: Accept state bitmap widening — always applicable
    candidates.push(OptimizationCandidate::new(
        Optimization::AcceptBitmapWiden,
        0.15,
        0.02,
        true,
        "always applicable (bitmap widening)".to_string(),
    ));

    // DB02: Lazy analysis phase execution — beneficial for small grammars
    candidates.push(OptimizationCandidate::new(
        Optimization::LazyAnalysis,
        0.5,
        0.02,
        profile.category_count < 3,
        format!(
            "category_count={} (threshold: <3)",
            profile.category_count
        ),
    ));

    // ── Tier 2: Moderate complexity ──────────────────────────────────────

    // ART04: Bloom filter pre-check for congruence rules
    candidates.push(OptimizationCandidate::new(
        Optimization::CongruenceBloom,
        0.35,
        0.15,
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // ART05: Fixpoint convergence bound via term-depth analysis
    candidates.push(OptimizationCandidate::new(
        Optimization::DepthBound,
        0.4,
        0.1,
        profile.rule_count > 2,
        format!("rule_count={} (threshold: >2)", profile.rule_count),
    ));

    // ART06: Demand-driven relation population
    candidates.push(OptimizationCandidate::new(
        Optimization::DemandDriven,
        0.5,
        0.1,
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count
        ),
    ));

    // BCG01: Join ordering optimization
    candidates.push(OptimizationCandidate::new(
        Optimization::JoinOrdering,
        0.4,
        0.15,
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // BCG03: Selective equality congruence pruning
    candidates.push(OptimizationCandidate::new(
        Optimization::EqCongruencePrune,
        0.35,
        0.15,
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // AL02: Hybrid direct-coded + compressed lexer
    candidates.push(OptimizationCandidate::new(
        Optimization::HybridLexer,
        0.3,
        0.2,
        profile.total_wfst_states > 30,
        format!(
            "total_wfst_states={} (threshold: >30)",
            profile.total_wfst_states
        ),
    ));

    // BP03: Token peek cache / BP table lookup
    candidates.push(OptimizationCandidate::new(
        Optimization::BpTableLookup,
        0.3,
        0.15,
        profile.rule_count > 8,
        format!("rule_count={} (threshold: >8)", profile.rule_count),
    ));

    // CD01: Hot-path arm reordering via WFST frequency weights — always applicable
    candidates.push(OptimizationCandidate::new(
        Optimization::FrequencyOrdering,
        0.35,
        0.1,
        true,
        "always applicable (WFST frequency-based arm reordering)".to_string(),
    ));

    // CD03: Computed goto dispatch — beneficial for large grammars
    candidates.push(OptimizationCandidate::new(
        Optimization::ComputedGoto,
        0.25,
        0.15,
        profile.rule_count > 20,
        format!("rule_count={} (threshold: >20)", profile.rule_count),
    ));

    // DB01: Incremental FIRST/FOLLOW recomputation
    candidates.push(OptimizationCandidate::new(
        Optimization::IncrementalFirstFollow,
        0.4,
        0.2,
        profile.category_count >= 3,
        format!(
            "category_count={} (threshold: >=3)",
            profile.category_count
        ),
    ));

    // ── Tier 3: High complexity ──────────────────────────────────────────

    // ART01: Hash-consing for recursive term types
    candidates.push(OptimizationCandidate::new(
        Optimization::HashConsing,
        0.15,
        0.5,
        profile.rule_count > 10,
        format!("rule_count={} (threshold: >10)", profile.rule_count),
    ));

    // ART02: Incremental semi-naive delta guards
    candidates.push(OptimizationCandidate::new(
        Optimization::IncrementalDelta,
        0.3,
        0.35,
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // BCG02: Rule fusion for chained deconstruction-rewrite
    candidates.push(OptimizationCandidate::new(
        Optimization::RuleFusion,
        0.4,
        0.4,
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // BCG05: Normalize-on-insert deduplication
    candidates.push(OptimizationCandidate::new(
        Optimization::NormalizeDedup,
        0.45,
        0.1,
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // BCG06: Stratified equation evaluation
    candidates.push(OptimizationCandidate::new(
        Optimization::EqStrata,
        0.3,
        0.4,
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count
        ),
    ));

    // AL01: DFA transition table multi-row repacking — always applicable
    candidates.push(OptimizationCandidate::new(
        Optimization::CombRepacking,
        0.4,
        0.1,
        true,
        "always applicable (DFA table repacking)".to_string(),
    ));

    // AL03: SIMD-accelerated whitespace skipping — always applicable (feature-gated at codegen)
    candidates.push(OptimizationCandidate::new(
        Optimization::SimdWhitespace,
        0.2,
        0.3,
        true,
        "always applicable (feature-gated at codegen)".to_string(),
    ));

    // AL04: Keyword recognition via minimal perfect hashing
    candidates.push(OptimizationCandidate::new(
        Optimization::KeywordMph,
        0.2,
        0.3,
        profile.rule_count > 15,
        format!("rule_count={} (threshold: >15)", profile.rule_count),
    ));

    // AL05: Multi-byte chain transitions
    candidates.push(OptimizationCandidate::new(
        Optimization::MultiByteChain,
        0.25,
        0.35,
        profile.rule_count > 10,
        format!("rule_count={} (threshold: >10)", profile.rule_count),
    ));

    // BP02: Tail-call elimination in recursive descent
    candidates.push(OptimizationCandidate::new(
        Optimization::TailCallElim,
        0.4,
        0.2,
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count
        ),
    ));

    // BP05: Specialized Pratt loop for fixed BP ranges
    candidates.push(OptimizationCandidate::new(
        Optimization::BpRangeLoop,
        0.45,
        0.15,
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // CD02: Decision tree segment merging
    candidates.push(OptimizationCandidate::new(
        Optimization::SegmentMerging,
        0.3,
        0.35,
        profile.avg_trie_depth > 3.0,
        format!(
            "avg_trie_depth={:.1} (threshold: >3.0)",
            profile.avg_trie_depth
        ),
    ));

    // CD04: Jump threading through decision tree branches
    candidates.push(OptimizationCandidate::new(
        Optimization::JumpThreading,
        0.35,
        0.25,
        profile.avg_trie_depth > 2.0,
        format!(
            "avg_trie_depth={:.1} (threshold: >2.0)",
            profile.avg_trie_depth
        ),
    ));

    // CD05: Prefix CSE for shared nonterminal parses
    candidates.push(OptimizationCandidate::new(
        Optimization::PrefixCse,
        0.15,
        0.45,
        profile.shared_prefix_ratio > 0.2,
        format!(
            "shared_prefix_ratio={:.2} (threshold: >0.2)",
            profile.shared_prefix_ratio
        ),
    ));

    // DB03: Parallel analysis phase execution
    candidates.push(OptimizationCandidate::new(
        Optimization::ParallelAnalysis,
        0.3,
        0.3,
        profile.category_count >= 3,
        format!(
            "category_count={} (threshold: >=3)",
            profile.category_count
        ),
    ));

    // DB04: Cached lint results across builds
    candidates.push(OptimizationCandidate::new(
        Optimization::CachedLints,
        0.45,
        0.2,
        profile.rule_count > 10,
        format!("rule_count={} (threshold: >10)", profile.rule_count),
    ));

    // Sort by score (lexicographic: speedup first, then compile_cost)
    candidates.sort_by(|a, b| a.score.cmp(&b.score));

    candidates
}

/// Return only the applicable optimizations, sorted by score.
pub fn recommended_optimizations(profile: &GrammarProfile) -> Vec<OptimizationCandidate> {
    evaluate_optimizations(profile)
        .into_iter()
        .filter(|c| c.applicable)
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// A3: Optimization Gates — pipeline self-tuning via cost-benefit results
// ══════════════════════════════════════════════════════════════════════════════

/// Boolean gates for each optimization pass, derived from cost-benefit analysis.
///
/// The pipeline populates this from `recommended_optimizations()` and threads it
/// into `TrampolineConfig` and `write_category_dispatch()`. Each gate controls
/// whether the corresponding codegen optimization is emitted. When a gate is
/// `false`, the codegen falls back to the default (unoptimized) path for that
/// optimization, avoiding code bloat and compile overhead for grammars that
/// don't benefit from it.
#[derive(Debug, Clone)]
pub struct OptimizationGates {
    /// A1: Grammar left-factoring via shared terminal prefix extraction.
    /// When false, NFA try-all always emits full save/restore per alternative.
    pub left_factoring: bool,
    /// A2: Hot/cold dispatch path splitting in `write_category_dispatch()`.
    /// When false, all dispatch arms are inlined regardless of weight.
    pub hot_cold_splitting: bool,
    /// B1: Multi-token lookahead via second-token dispatch.
    /// When false, ambiguous prefix groups always use NFA try-all.
    pub multi_token_lookahead: bool,
    /// F1: Weight-based spillover pruning (beam-gated alternative filtering).
    /// When false, all position-matching alternatives are spilled regardless of weight.
    pub spillover_pruning: bool,
    /// F2: Early termination on deterministic hit (weight == 0.0).
    /// When false, all alternatives are always tried even if the first succeeds.
    pub early_termination: bool,
    /// F3: Lazy spillover (demand-driven forced-prefix replay).
    /// When false, spillover is eager (all alternatives replayed immediately).
    pub lazy_spillover: bool,
    /// B3: WFST minimization via TransducerCascade.
    /// When false, the cascade is not run after WFST construction.
    pub wfst_minimization: bool,
    /// A4: Enhanced dead-code elimination via forward-backward analysis.
    pub enhanced_dce: bool,
    /// A5: CountingWeight-guided ambiguity targeting.
    pub ambiguity_targeting: bool,
    /// B2: Adaptive recovery via runtime weight accumulation.
    pub adaptive_recovery: bool,
    /// G1: Backtracking elimination via compile-time FIRST set analysis.
    /// Controls Phases 1-4: deterministic cross-cat arm commit, NFA suffix
    /// disjointness, LParen LL(2)/LL(3), optional LL(1) guard.
    pub backtracking_elimination: bool,
    /// H1: ContextWeight-based disambiguation (Sprint 6).
    /// When true, NFA try-all codegen narrows candidates via ContextWeight.
    pub context_disambiguation: bool,
    /// G25: WPDS stack-aware reachability check.
    /// When true, poststar analysis refines dead-rule detection.
    pub wpds_reachability: bool,
    /// T01: TRS confluence check.
    #[cfg(feature = "trs-analysis")]
    pub trs_confluence: bool,
    /// V01: VPA inclusion check.
    #[cfg(feature = "vpa")]
    pub vpa_inclusion: bool,
    /// S01: Safety verification via WPDS prestar.
    pub safety_verification: bool,
    /// S03: CEGAR refinement loop.
    pub cegar_refinement: bool,
    /// N01: Petri net deadlock check.
    #[cfg(feature = "petri")]
    pub petri_deadlock: bool,

    // ── Advanced Automata Infrastructure ─────────────────────────────────────
    /// SYM01: Symbolic automata guard analysis.
    #[cfg(feature = "symbolic-automata")]
    pub symbolic_guard: bool,
    /// O01: Weighted Büchi automaton analysis.
    #[cfg(feature = "omega")]
    pub weighted_buchi: bool,
    /// N06: Weighted alternating automaton analysis.
    #[cfg(feature = "alternating")]
    pub weighted_alternating: bool,
    /// V05: Weighted VPA analysis.
    #[cfg(feature = "vpa")]
    pub weighted_vpa: bool,
    /// PT01: Parity tree automaton analysis.
    #[cfg(feature = "parity-tree-automata")]
    pub parity_tree: bool,
    /// RA01: Register automaton analysis.
    #[cfg(feature = "register-automata")]
    pub register_analysis: bool,
    /// PR01: Probabilistic automaton analysis.
    #[cfg(feature = "probabilistic")]
    pub probabilistic: bool,
    /// MT01: Multi-tape automaton analysis.
    #[cfg(feature = "multi-tape")]
    pub multi_tape: bool,
    /// MS01: Multiset automaton analysis.
    #[cfg(feature = "multiset-automata")]
    pub multiset: bool,
    /// MSO01: Weighted MSO logic analysis.
    #[cfg(feature = "weighted-mso")]
    pub weighted_mso: bool,
    /// TW01: Two-way transducer analysis.
    #[cfg(feature = "two-way-transducer")]
    pub two_way_transducer: bool,

    // ── Advanced Automata Codegen Promotions ─────────────────────────────────

    /// SYM01-DCE: Symbolic unsatisfiable guard → dead rule elimination.
    #[cfg(feature = "symbolic-automata")]
    pub symbolic_guard_dce: bool,
    /// PR01-DCE: Probabilistic low-selectivity → dead rule elimination.
    #[cfg(feature = "probabilistic")]
    pub probabilistic_dce: bool,
    /// PR01-WEIGHT: Probabilistic weights refine constructor ordering.
    #[cfg(feature = "probabilistic")]
    pub probabilistic_weight_blend: bool,
    /// N06-ISO: Bisimulation equivalence → extended isomorphic groups.
    /// Also enables Sprint A3 (bisimilar weight discount): the lexicographically
    /// second category in each bisimilar pair receives a +0.5 tropical weight
    /// penalty on its constructor weights, reducing redundant NFA try-all work.
    #[cfg(feature = "alternating")]
    pub bisimulation_iso_groups: bool,
    /// RA01-SKIP: Dead registers → skip binder alpha-equiv.
    #[cfg(feature = "register-automata")]
    pub skip_dead_binders: bool,

    // ── Codegen Optimization Catalog ─────────────────────────────────────────
    /// ART01: Hash-consing for recursive term types.
    pub hash_consing: bool,
    /// ART02: Incremental semi-naive delta guards.
    pub incremental_delta: bool,
    /// ART03: Relation indexing hints.
    pub relation_indexing: bool,
    /// ART04: Bloom filter pre-check for congruence rules.
    pub congruence_bloom: bool,
    /// ART05: Fixpoint convergence bound via term-depth analysis.
    pub depth_bound: bool,
    /// ART06: Demand-driven relation population.
    pub demand_driven: bool,

    /// BCG01: Join ordering optimization.
    pub join_ordering: bool,
    /// BCG02: Rule fusion for chained deconstruction-rewrite.
    pub rule_fusion: bool,
    /// BCG03: Selective equality congruence pruning.
    pub eq_congruence_prune: bool,
    /// BCG04: Ground-term short-circuit in rewrite rules.
    pub ground_short_circuit: bool,
    /// BCG05: Normalize-on-insert deduplication.
    pub normalize_dedup: bool,
    /// BCG06: Stratified equation evaluation.
    pub eq_strata: bool,

    /// AL01: DFA transition table multi-row repacking.
    pub comb_repacking: bool,
    /// AL02: Hybrid direct-coded + compressed lexer.
    pub hybrid_lexer: bool,
    /// AL03: SIMD-accelerated whitespace skipping.
    pub simd_whitespace: bool,
    /// AL04: Keyword recognition via minimal perfect hashing.
    pub keyword_mph: bool,
    /// AL05: Multi-byte chain transitions.
    pub multi_byte_chain: bool,
    /// AL06: Accept state bitmap widening.
    pub accept_bitmap_widen: bool,

    /// BP01: Pratt BP table compaction via range encoding.
    pub bp_compaction: bool,
    /// BP02: Tail-call elimination in recursive descent.
    pub tail_call_elim: bool,
    /// BP03: Token peek cache / BP table lookup.
    pub bp_table_lookup: bool,
    /// BP04: Prefix handler inlining for trivial rules.
    pub trivial_inline: bool,
    /// BP05: Specialized Pratt loop for fixed BP ranges.
    pub bp_range_loop: bool,

    /// CD01: Hot-path arm reordering via WFST frequency weights.
    pub frequency_ordering: bool,
    /// CD02: Decision tree segment merging.
    pub segment_merging: bool,
    /// CD03: Computed goto dispatch via function pointer tables.
    pub computed_goto: bool,
    /// CD04: Jump threading through decision tree branches.
    pub jump_threading: bool,
    /// CD05: Prefix CSE for shared nonterminal parses.
    pub prefix_cse: bool,

    /// DB01: Incremental FIRST/FOLLOW recomputation.
    pub incremental_first_follow: bool,
    /// DB02: Lazy analysis phase execution.
    pub lazy_analysis: bool,
    /// DB03: Parallel analysis phase execution.
    pub parallel_analysis: bool,
    /// DB04: Cached lint results across builds.
    pub cached_lints: bool,
}

impl OptimizationGates {
    /// Create gates where all optimizations are enabled (for backward compatibility).
    pub fn all_enabled() -> Self {
        OptimizationGates {
            left_factoring: true,
            hot_cold_splitting: true,
            multi_token_lookahead: true,
            spillover_pruning: true,
            early_termination: true,
            lazy_spillover: true,
            wfst_minimization: true,
            enhanced_dce: true,
            ambiguity_targeting: true,
            adaptive_recovery: true,
            backtracking_elimination: true,
            context_disambiguation: true,
            wpds_reachability: true,
            #[cfg(feature = "trs-analysis")]
            trs_confluence: true,
            #[cfg(feature = "vpa")]
            vpa_inclusion: true,
            safety_verification: true,
            cegar_refinement: true,
            #[cfg(feature = "petri")]
            petri_deadlock: true,
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard: true,
            #[cfg(feature = "omega")]
            weighted_buchi: true,
            #[cfg(feature = "alternating")]
            weighted_alternating: true,
            #[cfg(feature = "vpa")]
            weighted_vpa: true,
            #[cfg(feature = "parity-tree-automata")]
            parity_tree: true,
            #[cfg(feature = "register-automata")]
            register_analysis: true,
            #[cfg(feature = "probabilistic")]
            probabilistic: true,
            #[cfg(feature = "multi-tape")]
            multi_tape: true,
            #[cfg(feature = "multiset-automata")]
            multiset: true,
            #[cfg(feature = "weighted-mso")]
            weighted_mso: true,
            #[cfg(feature = "two-way-transducer")]
            two_way_transducer: true,
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard_dce: true,
            #[cfg(feature = "probabilistic")]
            probabilistic_dce: true,
            #[cfg(feature = "probabilistic")]
            probabilistic_weight_blend: true,
            #[cfg(feature = "alternating")]
            bisimulation_iso_groups: true,
            #[cfg(feature = "register-automata")]
            skip_dead_binders: true,
            hash_consing: true,
            incremental_delta: true,
            relation_indexing: true,
            congruence_bloom: true,
            depth_bound: true,
            demand_driven: true,
            join_ordering: true,
            rule_fusion: true,
            eq_congruence_prune: true,
            ground_short_circuit: true,
            normalize_dedup: true,
            eq_strata: true,
            comb_repacking: true,
            hybrid_lexer: true,
            simd_whitespace: true,
            keyword_mph: true,
            multi_byte_chain: true,
            accept_bitmap_widen: true,
            bp_compaction: true,
            tail_call_elim: true,
            bp_table_lookup: true,
            trivial_inline: true,
            bp_range_loop: true,
            frequency_ordering: true,
            segment_merging: true,
            computed_goto: true,
            jump_threading: true,
            prefix_cse: true,
            incremental_first_follow: true,
            lazy_analysis: true,
            parallel_analysis: true,
            cached_lints: true,
        }
    }

    /// Populate gates from cost-benefit recommendations.
    ///
    /// Only optimizations that appear in `recommended` are enabled.
    /// All others default to `false`.
    pub fn from_recommendations(recommended: &[OptimizationCandidate]) -> Self {
        let enabled: std::collections::HashSet<Optimization> = recommended
            .iter()
            .map(|c| c.optimization)
            .collect();

        OptimizationGates {
            left_factoring: enabled.contains(&Optimization::LeftFactoring),
            hot_cold_splitting: enabled.contains(&Optimization::HotColdSplitting),
            multi_token_lookahead: enabled.contains(&Optimization::MultiTokenLookahead),
            spillover_pruning: enabled.contains(&Optimization::SpilloverPruning),
            early_termination: enabled.contains(&Optimization::EarlyTermination),
            lazy_spillover: enabled.contains(&Optimization::LazySpillover),
            wfst_minimization: enabled.contains(&Optimization::WfstMinimization),
            enhanced_dce: enabled.contains(&Optimization::EnhancedDeadCodeElimination),
            ambiguity_targeting: enabled.contains(&Optimization::AmbiguityTargeting),
            adaptive_recovery: enabled.contains(&Optimization::AdaptiveRecovery),
            backtracking_elimination: enabled.contains(&Optimization::BacktrackingElimination),
            context_disambiguation: enabled.contains(&Optimization::ContextDisambiguation),
            wpds_reachability: enabled.contains(&Optimization::WpdsReachabilityCheck),
            #[cfg(feature = "trs-analysis")]
            trs_confluence: enabled.contains(&Optimization::TrsConfluenceCheck),
            #[cfg(feature = "vpa")]
            vpa_inclusion: enabled.contains(&Optimization::VpaInclusionCheck),
            safety_verification: enabled.contains(&Optimization::SafetyVerification),
            cegar_refinement: enabled.contains(&Optimization::CegarRefinement),
            #[cfg(feature = "petri")]
            petri_deadlock: enabled.contains(&Optimization::PetriDeadlockCheck),
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard: enabled.contains(&Optimization::SymbolicGuardAnalysis),
            #[cfg(feature = "omega")]
            weighted_buchi: enabled.contains(&Optimization::WeightedBuchiAnalysis),
            #[cfg(feature = "alternating")]
            weighted_alternating: enabled.contains(&Optimization::WeightedAlternatingAnalysis),
            #[cfg(feature = "vpa")]
            weighted_vpa: enabled.contains(&Optimization::WeightedVpaAnalysis),
            #[cfg(feature = "parity-tree-automata")]
            parity_tree: enabled.contains(&Optimization::ParityTreeAnalysis),
            #[cfg(feature = "register-automata")]
            register_analysis: enabled.contains(&Optimization::RegisterAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "multi-tape")]
            multi_tape: enabled.contains(&Optimization::MultiTapeAnalysis),
            #[cfg(feature = "multiset-automata")]
            multiset: enabled.contains(&Optimization::MultisetAnalysis),
            #[cfg(feature = "weighted-mso")]
            weighted_mso: enabled.contains(&Optimization::WeightedMsoAnalysis),
            #[cfg(feature = "two-way-transducer")]
            two_way_transducer: enabled.contains(&Optimization::TwoWayTransducerAnalysis),
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard_dce: enabled.contains(&Optimization::SymbolicGuardAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic_dce: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic_weight_blend: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "alternating")]
            bisimulation_iso_groups: enabled.contains(&Optimization::WeightedAlternatingAnalysis),
            #[cfg(feature = "register-automata")]
            skip_dead_binders: enabled.contains(&Optimization::RegisterAnalysis),
            hash_consing: enabled.contains(&Optimization::HashConsing),
            incremental_delta: enabled.contains(&Optimization::IncrementalDelta),
            relation_indexing: enabled.contains(&Optimization::RelationIndexing),
            congruence_bloom: enabled.contains(&Optimization::CongruenceBloom),
            depth_bound: enabled.contains(&Optimization::DepthBound),
            demand_driven: enabled.contains(&Optimization::DemandDriven),
            join_ordering: enabled.contains(&Optimization::JoinOrdering),
            rule_fusion: enabled.contains(&Optimization::RuleFusion),
            eq_congruence_prune: enabled.contains(&Optimization::EqCongruencePrune),
            ground_short_circuit: enabled.contains(&Optimization::GroundShortCircuit),
            normalize_dedup: enabled.contains(&Optimization::NormalizeDedup),
            eq_strata: enabled.contains(&Optimization::EqStrata),
            comb_repacking: enabled.contains(&Optimization::CombRepacking),
            hybrid_lexer: enabled.contains(&Optimization::HybridLexer),
            simd_whitespace: enabled.contains(&Optimization::SimdWhitespace),
            keyword_mph: enabled.contains(&Optimization::KeywordMph),
            multi_byte_chain: enabled.contains(&Optimization::MultiByteChain),
            accept_bitmap_widen: enabled.contains(&Optimization::AcceptBitmapWiden),
            bp_compaction: enabled.contains(&Optimization::BpCompaction),
            tail_call_elim: enabled.contains(&Optimization::TailCallElim),
            bp_table_lookup: enabled.contains(&Optimization::BpTableLookup),
            trivial_inline: enabled.contains(&Optimization::TrivialInline),
            bp_range_loop: enabled.contains(&Optimization::BpRangeLoop),
            frequency_ordering: enabled.contains(&Optimization::FrequencyOrdering),
            segment_merging: enabled.contains(&Optimization::SegmentMerging),
            computed_goto: enabled.contains(&Optimization::ComputedGoto),
            jump_threading: enabled.contains(&Optimization::JumpThreading),
            prefix_cse: enabled.contains(&Optimization::PrefixCse),
            incremental_first_follow: enabled.contains(&Optimization::IncrementalFirstFollow),
            lazy_analysis: enabled.contains(&Optimization::LazyAnalysis),
            parallel_analysis: enabled.contains(&Optimization::ParallelAnalysis),
            cached_lints: enabled.contains(&Optimization::CachedLints),
        }
    }

    /// Create gates where no optimizations are enabled.
    pub fn none_enabled() -> Self {
        OptimizationGates {
            left_factoring: false,
            hot_cold_splitting: false,
            multi_token_lookahead: false,
            spillover_pruning: false,
            early_termination: false,
            lazy_spillover: false,
            wfst_minimization: false,
            enhanced_dce: false,
            ambiguity_targeting: false,
            adaptive_recovery: false,
            backtracking_elimination: false,
            context_disambiguation: false,
            wpds_reachability: false,
            #[cfg(feature = "trs-analysis")]
            trs_confluence: false,
            #[cfg(feature = "vpa")]
            vpa_inclusion: false,
            safety_verification: false,
            cegar_refinement: false,
            #[cfg(feature = "petri")]
            petri_deadlock: false,
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard: false,
            #[cfg(feature = "omega")]
            weighted_buchi: false,
            #[cfg(feature = "alternating")]
            weighted_alternating: false,
            #[cfg(feature = "vpa")]
            weighted_vpa: false,
            #[cfg(feature = "parity-tree-automata")]
            parity_tree: false,
            #[cfg(feature = "register-automata")]
            register_analysis: false,
            #[cfg(feature = "probabilistic")]
            probabilistic: false,
            #[cfg(feature = "multi-tape")]
            multi_tape: false,
            #[cfg(feature = "multiset-automata")]
            multiset: false,
            #[cfg(feature = "weighted-mso")]
            weighted_mso: false,
            #[cfg(feature = "two-way-transducer")]
            two_way_transducer: false,
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard_dce: false,
            #[cfg(feature = "probabilistic")]
            probabilistic_dce: false,
            #[cfg(feature = "probabilistic")]
            probabilistic_weight_blend: false,
            #[cfg(feature = "alternating")]
            bisimulation_iso_groups: false,
            #[cfg(feature = "register-automata")]
            skip_dead_binders: false,
            hash_consing: false,
            incremental_delta: false,
            relation_indexing: false,
            congruence_bloom: false,
            depth_bound: false,
            demand_driven: false,
            join_ordering: false,
            rule_fusion: false,
            eq_congruence_prune: false,
            ground_short_circuit: false,
            normalize_dedup: false,
            eq_strata: false,
            comb_repacking: false,
            hybrid_lexer: false,
            simd_whitespace: false,
            keyword_mph: false,
            multi_byte_chain: false,
            accept_bitmap_widen: false,
            bp_compaction: false,
            tail_call_elim: false,
            bp_table_lookup: false,
            trivial_inline: false,
            bp_range_loop: false,
            frequency_ordering: false,
            segment_merging: false,
            computed_goto: false,
            jump_threading: false,
            prefix_cse: false,
            incremental_first_follow: false,
            lazy_analysis: false,
            parallel_analysis: false,
            cached_lints: false,
        }
    }

    /// Read optimization gates from the `PRATTAIL_AUTO_OPTIMIZE` environment variable.
    ///
    /// Returns:
    /// - `Ok(None)` if the variable is not set
    /// - `Ok(Some(gates))` on success
    /// - `Err(msg)` on parse failure
    ///
    /// Special values:
    /// - `all` — all optimizations enabled
    /// - `none` — all optimizations disabled
    ///
    /// Otherwise, a comma-separated list of optimization codes or names:
    /// `PRATTAIL_AUTO_OPTIMIZE=A1,B2,F3`
    pub fn from_env() -> Result<Option<Self>, String> {
        let val = match std::env::var("PRATTAIL_AUTO_OPTIMIZE") {
            Ok(v) => v,
            Err(std::env::VarError::NotPresent) => return Ok(None),
            Err(std::env::VarError::NotUnicode(_)) => {
                return Err("PRATTAIL_AUTO_OPTIMIZE contains non-UTF-8 data".to_string());
            },
        };

        let trimmed = val.trim();
        if trimmed.eq_ignore_ascii_case("all") {
            return Ok(Some(Self::all_enabled()));
        }
        if trimmed.eq_ignore_ascii_case("none") {
            return Ok(Some(Self::none_enabled()));
        }

        let mut enabled = std::collections::HashSet::new();
        for part in trimmed.split(',') {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let opt: Optimization = part.parse()?;
            enabled.insert(opt);
        }

        Ok(Some(OptimizationGates {
            left_factoring: enabled.contains(&Optimization::LeftFactoring),
            hot_cold_splitting: enabled.contains(&Optimization::HotColdSplitting),
            multi_token_lookahead: enabled.contains(&Optimization::MultiTokenLookahead),
            spillover_pruning: enabled.contains(&Optimization::SpilloverPruning),
            early_termination: enabled.contains(&Optimization::EarlyTermination),
            lazy_spillover: enabled.contains(&Optimization::LazySpillover),
            wfst_minimization: enabled.contains(&Optimization::WfstMinimization),
            enhanced_dce: enabled.contains(&Optimization::EnhancedDeadCodeElimination),
            ambiguity_targeting: enabled.contains(&Optimization::AmbiguityTargeting),
            adaptive_recovery: enabled.contains(&Optimization::AdaptiveRecovery),
            backtracking_elimination: enabled.contains(&Optimization::BacktrackingElimination),
            context_disambiguation: enabled.contains(&Optimization::ContextDisambiguation),
            wpds_reachability: enabled.contains(&Optimization::WpdsReachabilityCheck),
            #[cfg(feature = "trs-analysis")]
            trs_confluence: enabled.contains(&Optimization::TrsConfluenceCheck),
            #[cfg(feature = "vpa")]
            vpa_inclusion: enabled.contains(&Optimization::VpaInclusionCheck),
            safety_verification: enabled.contains(&Optimization::SafetyVerification),
            cegar_refinement: enabled.contains(&Optimization::CegarRefinement),
            #[cfg(feature = "petri")]
            petri_deadlock: enabled.contains(&Optimization::PetriDeadlockCheck),
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard: enabled.contains(&Optimization::SymbolicGuardAnalysis),
            #[cfg(feature = "omega")]
            weighted_buchi: enabled.contains(&Optimization::WeightedBuchiAnalysis),
            #[cfg(feature = "alternating")]
            weighted_alternating: enabled.contains(&Optimization::WeightedAlternatingAnalysis),
            #[cfg(feature = "vpa")]
            weighted_vpa: enabled.contains(&Optimization::WeightedVpaAnalysis),
            #[cfg(feature = "parity-tree-automata")]
            parity_tree: enabled.contains(&Optimization::ParityTreeAnalysis),
            #[cfg(feature = "register-automata")]
            register_analysis: enabled.contains(&Optimization::RegisterAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "multi-tape")]
            multi_tape: enabled.contains(&Optimization::MultiTapeAnalysis),
            #[cfg(feature = "multiset-automata")]
            multiset: enabled.contains(&Optimization::MultisetAnalysis),
            #[cfg(feature = "weighted-mso")]
            weighted_mso: enabled.contains(&Optimization::WeightedMsoAnalysis),
            #[cfg(feature = "two-way-transducer")]
            two_way_transducer: enabled.contains(&Optimization::TwoWayTransducerAnalysis),
            #[cfg(feature = "symbolic-automata")]
            symbolic_guard_dce: enabled.contains(&Optimization::SymbolicGuardAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic_dce: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "probabilistic")]
            probabilistic_weight_blend: enabled.contains(&Optimization::ProbabilisticAnalysis),
            #[cfg(feature = "alternating")]
            bisimulation_iso_groups: enabled.contains(&Optimization::WeightedAlternatingAnalysis),
            #[cfg(feature = "register-automata")]
            skip_dead_binders: enabled.contains(&Optimization::RegisterAnalysis),
            hash_consing: enabled.contains(&Optimization::HashConsing),
            incremental_delta: enabled.contains(&Optimization::IncrementalDelta),
            relation_indexing: enabled.contains(&Optimization::RelationIndexing),
            congruence_bloom: enabled.contains(&Optimization::CongruenceBloom),
            depth_bound: enabled.contains(&Optimization::DepthBound),
            demand_driven: enabled.contains(&Optimization::DemandDriven),
            join_ordering: enabled.contains(&Optimization::JoinOrdering),
            rule_fusion: enabled.contains(&Optimization::RuleFusion),
            eq_congruence_prune: enabled.contains(&Optimization::EqCongruencePrune),
            ground_short_circuit: enabled.contains(&Optimization::GroundShortCircuit),
            normalize_dedup: enabled.contains(&Optimization::NormalizeDedup),
            eq_strata: enabled.contains(&Optimization::EqStrata),
            comb_repacking: enabled.contains(&Optimization::CombRepacking),
            hybrid_lexer: enabled.contains(&Optimization::HybridLexer),
            simd_whitespace: enabled.contains(&Optimization::SimdWhitespace),
            keyword_mph: enabled.contains(&Optimization::KeywordMph),
            multi_byte_chain: enabled.contains(&Optimization::MultiByteChain),
            accept_bitmap_widen: enabled.contains(&Optimization::AcceptBitmapWiden),
            bp_compaction: enabled.contains(&Optimization::BpCompaction),
            tail_call_elim: enabled.contains(&Optimization::TailCallElim),
            bp_table_lookup: enabled.contains(&Optimization::BpTableLookup),
            trivial_inline: enabled.contains(&Optimization::TrivialInline),
            bp_range_loop: enabled.contains(&Optimization::BpRangeLoop),
            frequency_ordering: enabled.contains(&Optimization::FrequencyOrdering),
            segment_merging: enabled.contains(&Optimization::SegmentMerging),
            computed_goto: enabled.contains(&Optimization::ComputedGoto),
            jump_threading: enabled.contains(&Optimization::JumpThreading),
            prefix_cse: enabled.contains(&Optimization::PrefixCse),
            incremental_first_follow: enabled.contains(&Optimization::IncrementalFirstFollow),
            lazy_analysis: enabled.contains(&Optimization::LazyAnalysis),
            parallel_analysis: enabled.contains(&Optimization::ParallelAnalysis),
            cached_lints: enabled.contains(&Optimization::CachedLints),
        }))
    }

    /// Try env override first, fall back to cost-benefit recommendations.
    ///
    /// Logs a warning when the env override is active.
    pub fn from_env_or_recommendations(recommended: &[OptimizationCandidate]) -> Self {
        match Self::from_env() {
            Ok(Some(gates)) => {
                crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                    id: "I08",
                    name: "env-override-active",
                    severity: crate::lint::LintSeverity::Warning,
                    category: None,
                    rule: None,
                    message: "PRATTAIL_AUTO_OPTIMIZE override active — cost-benefit recommendations bypassed".to_string(),
                    hint: Some("unset PRATTAIL_AUTO_OPTIMIZE to use automatic cost-benefit analysis".to_string()),
                    grammar_name: None,
                    source_location: None,
                });
                gates
            },
            Ok(None) => Self::from_recommendations(recommended),
            Err(e) => {
                crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                    id: "I09",
                    name: "env-override-parse-error",
                    severity: crate::lint::LintSeverity::Error,
                    category: None,
                    rule: None,
                    message: format!("PRATTAIL_AUTO_OPTIMIZE parse error: {} — falling back to cost-benefit analysis", e),
                    hint: Some("valid values: `all`, `none`, or comma-separated optimization codes (e.g., `A1,B2,F3`)".to_string()),
                    grammar_name: None,
                    source_location: None,
                });
                Self::from_recommendations(recommended)
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// A5: Ambiguity Targeting Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Per-token ambiguity analysis for a single category.
///
/// Identifies which dispatch tokens are ambiguous (multiple rules match) and
/// computes the ambiguity count for each. Used by:
/// - B1 (multi-token lookahead) to select tokens that need extended WFSTs
/// - NFA spillover to pre-size buffers
/// - Grammar diagnostics to report per-token ambiguity
#[derive(Debug, Clone)]
pub struct TokenAmbiguityInfo {
    /// Category this token belongs to.
    pub category: String,
    /// Token variant name (e.g., "Ident", "LParen").
    pub token: String,
    /// Number of dispatch alternatives for this token (CountingWeight value).
    pub alternative_count: u64,
    /// Rule labels that match this token.
    pub rule_labels: Vec<String>,
    /// Whether this token is a candidate for multi-token lookahead (B1).
    /// True when alternative_count > 1 and the alternatives differ on
    /// their second token.
    pub lookahead_candidate: bool,
}

/// Result of A5 ambiguity targeting analysis.
#[derive(Debug, Clone)]
pub struct AmbiguityTargetingResult {
    /// All ambiguous tokens across all categories.
    pub ambiguous_tokens: Vec<TokenAmbiguityInfo>,
    /// Total number of unambiguous tokens (for reporting).
    pub unambiguous_count: usize,
    /// Maximum ambiguity count observed across all tokens.
    pub max_ambiguity: u64,
    /// Categories where NFA spillover buffer should be pre-sized.
    pub presized_categories: Vec<(String, usize)>,
}

/// Perform A5 ambiguity targeting analysis.
///
/// Scans all prediction WFSTs and identifies per-token ambiguity using
/// `predict_with_confidence()`. Returns structured analysis that downstream
/// optimizations (B1, F3) can consume.
///
/// The `ambiguity_threshold` parameter controls which tokens are flagged
/// as candidates for multi-token lookahead (B1). Tokens with
/// `alternative_count > threshold` are flagged.
pub fn analyze_ambiguity_targets(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    ambiguity_threshold: u64,
) -> AmbiguityTargetingResult {
    let mut ambiguous_tokens = Vec::new();
    let mut unambiguous_count = 0usize;
    let mut max_ambiguity = 0u64;
    let mut category_max_ambiguity: HashMap<String, usize> = HashMap::new();

    for (cat, wfst) in prediction_wfsts {
        if let Some(first_set) = first_sets.get(cat) {
            let mut cat_max = 0usize;

            for token in first_set.sorted_tokens() {
                let predictions = wfst.predict_with_confidence(&token);
                let count = predictions.first().map_or(0, |(_, cw)| cw.count());

                if count > 1 {
                    let rule_labels: Vec<String> = predictions
                        .iter()
                        .map(|(a, _)| a.action.rule_label().to_string())
                        .collect();

                    let lookahead_candidate = count > ambiguity_threshold;

                    ambiguous_tokens.push(TokenAmbiguityInfo {
                        category: cat.clone(),
                        token: token.to_string(),
                        alternative_count: count,
                        rule_labels,
                        lookahead_candidate,
                    });

                    if count > max_ambiguity {
                        max_ambiguity = count;
                    }

                    cat_max = cat_max.max(count as usize);
                } else {
                    unambiguous_count += 1;
                }
            }

            if cat_max > 0 {
                category_max_ambiguity.insert(cat.clone(), cat_max);
            }
        }
    }

    // Pre-size NFA spillover buffers based on maximum ambiguity per category
    let presized_categories: Vec<(String, usize)> = category_max_ambiguity
        .into_iter()
        .map(|(cat, max)| (cat, max.saturating_sub(1))) // N-1 alternatives spilled
        .collect();

    AmbiguityTargetingResult {
        ambiguous_tokens,
        unambiguous_count,
        max_ambiguity,
        presized_categories,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D2: Grammar Complexity Report
// ══════════════════════════════════════════════════════════════════════════════

/// D2: Per-category complexity metrics for the grammar complexity report.
#[derive(Debug, Clone)]
pub struct CategoryComplexity {
    /// Category name.
    pub name: String,
    /// Number of dispatch tokens in FIRST set.
    pub dispatch_token_count: usize,
    /// Number of ambiguous dispatch tokens (>1 action).
    pub ambiguous_token_count: usize,
    /// Maximum ambiguity factor (most alternatives for any single token).
    pub max_ambiguity: usize,
    /// Number of WFST states.
    pub wfst_state_count: usize,
    /// Number of WFST actions.
    pub wfst_action_count: usize,
}

/// Status of an optimization in the report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationStatus {
    /// Automatically applied when the gate is enabled — no user action needed.
    Auto,
    /// Diagnostic only — results are reported but no codegen changes are made.
    Diagnostic,
}

impl Optimization {
    /// Whether this optimization is auto-applied (controls codegen) or
    /// diagnostic-only (info messages).
    pub fn status(&self) -> OptimizationStatus {
        match self {
            // Auto-applied: gate is checked in codegen paths
            Self::LeftFactoring        // A1: write_nfa_merged_prefix_arm left-factoring
            | Self::HotColdSplitting   // A2: dispatch hot/cold splitting
            | Self::MultiTokenLookahead // B1: NFA multi-token dispatch
            | Self::SpilloverPruning   // F1: beam-based spill filter
            | Self::EarlyTermination   // F2: deterministic NFA early exit
            | Self::LazySpillover      // F3: weight-gated spillover
            | Self::WfstMinimization   // B3: cascade gating
            | Self::EnhancedDeadCodeElimination // A4: dead-rule codegen suppression
            | Self::AdaptiveRecovery   // B2: adaptive recovery weight expr
            | Self::BacktrackingElimination // G1: FIRST-set backtracking elimination
            => OptimizationStatus::Auto,

            // Auto-applied (Sprint 6): ContextWeight narrowing in NFA try-all
            | Self::ContextDisambiguation // H1: powerset WFST candidate narrowing
            => OptimizationStatus::Auto,

            // Diagnostic: info messages only, no codegen effect
            Self::AmbiguityTargeting   // A5: per-token ambiguity report
            | Self::WpdsReachabilityCheck // G25: WPDS stack-aware dead-rule verification
            | Self::TrsConfluenceCheck    // T01: Knuth-Bendix critical pair analysis
            | Self::VpaInclusionCheck     // V01: VPA structured sublanguage check
            | Self::SafetyVerification    // S01: WPDS prestar safety check
            | Self::CegarRefinement       // S03: CEGAR refinement loop
            | Self::PetriDeadlockCheck    // N01: Petri net coverability
            // Codegen catalog: planned optimizations (diagnostic until implemented)
            | Self::HashConsing           // ART01
            | Self::IncrementalDelta      // ART02
            | Self::RelationIndexing      // ART03
            | Self::CongruenceBloom       // ART04
            | Self::DepthBound            // ART05
            | Self::DemandDriven          // ART06
            | Self::JoinOrdering          // BCG01
            | Self::RuleFusion            // BCG02
            | Self::EqCongruencePrune     // BCG03
            | Self::GroundShortCircuit    // BCG04
            | Self::NormalizeDedup        // BCG05
            | Self::EqStrata              // BCG06
            | Self::CombRepacking         // AL01
            | Self::HybridLexer           // AL02
            | Self::SimdWhitespace        // AL03
            | Self::KeywordMph            // AL04
            | Self::MultiByteChain        // AL05
            | Self::AcceptBitmapWiden      // AL06
            | Self::BpCompaction          // BP01
            | Self::TailCallElim          // BP02
            | Self::BpTableLookup         // BP03
            | Self::TrivialInline         // BP04
            | Self::BpRangeLoop           // BP05
            | Self::FrequencyOrdering     // CD01
            | Self::SegmentMerging        // CD02
            | Self::ComputedGoto          // CD03
            | Self::JumpThreading         // CD04
            | Self::PrefixCse             // CD05
            | Self::IncrementalFirstFollow // DB01
            | Self::LazyAnalysis          // DB02
            | Self::ParallelAnalysis      // DB03
            | Self::CachedLints           // DB04
            => OptimizationStatus::Diagnostic,

            // Advanced automata infrastructure: promoted to Auto where analysis drives codegen
            #[cfg(feature = "symbolic-automata")]
            Self::SymbolicGuardAnalysis => OptimizationStatus::Auto, // SYM01-DCE
            #[cfg(feature = "omega")]
            Self::WeightedBuchiAnalysis => OptimizationStatus::Diagnostic,
            #[cfg(feature = "alternating")]
            Self::WeightedAlternatingAnalysis => OptimizationStatus::Auto, // N06-ISO
            #[cfg(feature = "vpa")]
            Self::WeightedVpaAnalysis => OptimizationStatus::Diagnostic, // V05-INFO (informational)
            #[cfg(feature = "parity-tree-automata")]
            Self::ParityTreeAnalysis => OptimizationStatus::Diagnostic,
            #[cfg(feature = "register-automata")]
            Self::RegisterAnalysis => OptimizationStatus::Auto, // RA01-SKIP
            #[cfg(feature = "probabilistic")]
            Self::ProbabilisticAnalysis => OptimizationStatus::Auto, // PR01-DCE + PR01-WEIGHT
            #[cfg(feature = "multi-tape")]
            Self::MultiTapeAnalysis => OptimizationStatus::Diagnostic, // MT01-INFO
            #[cfg(feature = "multiset-automata")]
            Self::MultisetAnalysis => OptimizationStatus::Diagnostic,
            #[cfg(feature = "weighted-mso")]
            Self::WeightedMsoAnalysis => OptimizationStatus::Diagnostic,
            #[cfg(feature = "two-way-transducer")]
            Self::TwoWayTransducerAnalysis => OptimizationStatus::Diagnostic,
            #[cfg(feature = "predicate-dispatch")]
            Self::PredicateDispatch => OptimizationStatus::Diagnostic,
        }
    }
}

impl fmt::Display for OptimizationStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Auto => write!(f, "auto"),
            Self::Diagnostic => write!(f, "diag"),
        }
    }
}

/// D2: Unified grammar complexity report.
///
/// Combines per-category metrics, cross-category coupling, WFST analysis,
/// and optimization recommendations into a single structured report.
/// Suitable for output as formatted text or structured JSON for CI integration.
#[derive(Debug, Clone)]
pub struct GrammarComplexityReport {
    /// Grammar name.
    pub grammar_name: String,
    /// Overall grammar profile.
    pub profile: GrammarProfile,
    /// Per-category complexity metrics.
    pub categories: Vec<CategoryComplexity>,
    /// Recommended optimizations: (name, speedup, cost, reason, status).
    pub recommended_optimizations: Vec<(String, f64, f64, String, OptimizationStatus)>,
    /// Total number of WFST states across all categories.
    pub total_wfst_states: usize,
    /// Total number of WFST transitions across all categories.
    pub total_wfst_transitions: usize,
    /// Number of entries in the composed dispatch weight map.
    /// Covers all `(category, token)` pairs with resolved weights.
    pub composed_dispatch_entries: usize,
    /// Number of ambiguities resolved deterministically by composed dispatch.
    /// These are tokens where the lexer×parser composition picks a unique winner.
    pub resolved_ambiguities: usize,
}

impl GrammarComplexityReport {
    /// D2: Build a complexity report from pipeline data.
    ///
    /// `composed_dispatch_entries`: total entries in the composed weight map.
    /// `resolved_ambiguities`: number of ambiguous tokens resolved by composition.
    pub fn build(
        grammar_name: &str,
        profile: &GrammarProfile,
        prediction_wfsts: &HashMap<String, PredictionWfst>,
        first_sets: &HashMap<String, FirstSet>,
        composed_dispatch_entries: usize,
        resolved_ambiguities: usize,
    ) -> Self {
        let mut categories = Vec::with_capacity(prediction_wfsts.len());
        let mut total_transitions = 0usize;
        let mut total_states = 0usize;

        for (cat_name, wfst) in prediction_wfsts {
            let dispatch_token_count = first_sets
                .get(cat_name)
                .map(|fs| fs.tokens.len())
                .unwrap_or(0);

            let mut ambiguous_count = 0;
            let mut max_ambiguity = 0;
            if let Some(first_set) = first_sets.get(cat_name) {
                for token in &first_set.tokens {
                    let predictions = wfst.predict(token);
                    if predictions.len() > 1 {
                        ambiguous_count += 1;
                        max_ambiguity = max_ambiguity.max(predictions.len());
                    }
                }
            }

            let state_count = wfst.num_states();
            let action_count = wfst.num_actions();
            total_states += state_count;
            total_transitions += wfst.states.iter().map(|s| s.transitions.len()).sum::<usize>();

            categories.push(CategoryComplexity {
                name: cat_name.clone(),
                dispatch_token_count,
                ambiguous_token_count: ambiguous_count,
                max_ambiguity,
                wfst_state_count: state_count,
                wfst_action_count: action_count,
            });
        }

        // Sort categories by name for deterministic output
        categories.sort_by(|a, b| a.name.cmp(&b.name));

        let recommended = recommended_optimizations(profile);
        let recommended_optimizations = recommended
            .iter()
            .map(|c| {
                (
                    format!("{:?}", c.optimization),
                    c.speedup.value(),
                    c.compile_cost.value(),
                    c.reason.clone(),
                    c.optimization.status(),
                )
            })
            .collect();

        GrammarComplexityReport {
            grammar_name: grammar_name.to_string(),
            profile: profile.clone(),
            categories,
            recommended_optimizations,
            total_wfst_states: total_states,
            total_wfst_transitions: total_transitions,
            composed_dispatch_entries,
            resolved_ambiguities,
        }
    }

    /// D2: Format as a compact single-line summary with optional per-category detail.
    pub fn format_compact(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();

        // Line 1: key scalar metrics
        write!(
            out,
            "{} cats, {} rules, {} WFST states, {} transitions, {:.1}% ambiguous, {:.1}% cold, {} NFA spill, {} dispatch entries ({} resolved)",
            self.profile.category_count,
            self.profile.rule_count,
            self.total_wfst_states,
            self.total_wfst_transitions,
            self.profile.ambiguous_fraction * 100.0,
            self.profile.cold_fraction * 100.0,
            self.profile.nfa_spillover_categories,
            self.composed_dispatch_entries,
            self.resolved_ambiguities,
        ).unwrap();

        // Line 2: per-category summary (only if ≤ 8 categories)
        if !self.categories.is_empty() && self.categories.len() <= 8 {
            let cat_parts: Vec<String> = self.categories.iter()
                .map(|c| format!("{}({}t/{}a)", c.name, c.dispatch_token_count, c.wfst_action_count))
                .collect();
            write!(out, "\n  per-category: {}", cat_parts.join(" ")).unwrap();
        }

        out
    }

    /// D2: Convert to a lint diagnostic for consistent emission.
    pub fn to_diagnostic(&self) -> crate::lint::LintDiagnostic {
        crate::lint::LintDiagnostic {
            id: "D02",
            name: "grammar-profile",
            severity: crate::lint::LintSeverity::Note,
            category: None,
            rule: None,
            message: self.format_compact(),
            hint: None,
            grammar_name: Some(self.grammar_name.clone()),
            source_location: None,
        }
    }

    /// D2: Format as a human-readable table (legacy, kept for backward compatibility).
    pub fn format_table(&self) -> String {
        self.format_compact()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// Mutex to serialize tests that read/write the `PRATTAIL_AUTO_OPTIMIZE`
    /// environment variable. Env vars are process-global, so concurrent
    /// set/remove from parallel test threads causes non-deterministic failures.
    static ENV_MUTEX: Mutex<()> = Mutex::new(());

    fn simple_profile() -> GrammarProfile {
        GrammarProfile {
            shared_prefix_ratio: 0.0,
            cold_fraction: 0.0,
            ambiguous_fraction: 0.0,
            ambiguous_count: 0,
            category_count: 4,
            rule_count: 20,
            nfa_spillover_categories: 0,
            has_beam_width: false,
            total_wfst_states: 10,
            avg_trie_depth: 0.0,
            ambiguity_score: 0.0,
            deterministic_ratio: 1.0,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
        }
    }

    #[test]
    fn test_simple_grammar_few_optimizations() {
        let profile = simple_profile();
        let recommended = recommended_optimizations(&profile);
        // Simple grammar: B2 (adaptive recovery) and A4 (DCE) should be recommended
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::AdaptiveRecovery),
            "adaptive recovery should always be recommended"
        );
        assert!(
            names.contains(&Optimization::EnhancedDeadCodeElimination),
            "DCE should be recommended for grammars with >5 rules"
        );
    }

    #[test]
    fn test_ambiguous_grammar_enables_lookahead() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.25,
            ambiguous_count: 3,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::MultiTokenLookahead),
            "multi-token lookahead should be recommended for ambiguous grammars: {:?}",
            names
        );
        assert!(
            names.contains(&Optimization::AmbiguityTargeting),
            "ambiguity targeting should be recommended: {:?}",
            names
        );
    }

    #[test]
    fn test_cold_heavy_grammar() {
        let profile = GrammarProfile {
            cold_fraction: 0.6,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::HotColdSplitting),
            "hot/cold splitting should be recommended when cold_fraction > 0.4: {:?}",
            names
        );
    }

    #[test]
    fn test_spillover_with_beam() {
        let profile = GrammarProfile {
            nfa_spillover_categories: 2,
            has_beam_width: true,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::SpilloverPruning),
            "spillover pruning should be recommended when beam is set: {:?}",
            names
        );
        assert!(
            names.contains(&Optimization::LazySpillover),
            "lazy spillover should be recommended when spillover categories exist: {:?}",
            names
        );
    }

    #[test]
    fn test_lexicographic_ordering() {
        // Verify that among candidates with equal speedup, cheaper ones come first
        let a = OptimizationCandidate::new(
            Optimization::LeftFactoring,
            0.5,
            1.0,
            true,
            "test".to_string(),
        );
        let b = OptimizationCandidate::new(
            Optimization::HotColdSplitting,
            0.5,
            0.05,
            true,
            "test".to_string(),
        );
        assert!(
            b.score < a.score,
            "cheaper compile cost should rank better when speedup is equal"
        );
    }

    #[test]
    fn test_all_candidates_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        // 50 base + 11 cfg-gated advanced automata variants (when all features enabled)
        #[cfg(feature = "full-analysis")]
        assert_eq!(all.len(), 61, "should evaluate all 61 optimization candidates");
        #[cfg(not(feature = "full-analysis"))]
        assert!(all.len() >= 50, "should evaluate at least 50 optimization candidates");
    }

    #[test]
    fn test_ambiguity_targeting_empty() {
        let wfsts = HashMap::new();
        let first_sets = HashMap::new();
        let result = analyze_ambiguity_targets(&wfsts, &first_sets, 1);
        assert!(result.ambiguous_tokens.is_empty());
        assert_eq!(result.unambiguous_count, 0);
        assert_eq!(result.max_ambiguity, 0);
        assert!(result.presized_categories.is_empty());
    }

    #[test]
    fn test_ambiguity_targeting_result_fields() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Build a WFST with one ambiguous token (Ident → 2 rules) and one unambiguous (LParen)
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string(), "LParen".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "POutput".to_string(),
                parse_fn: "parse_poutput".to_string(),
            },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "LParen",
            DispatchAction::Direct {
                rule_label: "PSend".to_string(),
                parse_fn: "parse_psend".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut first_set = FirstSet::new();
        first_set.tokens.insert("Ident".to_string());
        first_set.tokens.insert("LParen".to_string());

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        fsets.insert("Proc".to_string(), first_set);

        let result = analyze_ambiguity_targets(&wfsts, &fsets, 1);

        // One ambiguous token (Ident with 2 alternatives), one unambiguous (LParen)
        assert_eq!(result.ambiguous_tokens.len(), 1);
        assert_eq!(result.unambiguous_count, 1);
        assert_eq!(result.max_ambiguity, 2);

        let ident_info = &result.ambiguous_tokens[0];
        assert_eq!(ident_info.category, "Proc");
        assert_eq!(ident_info.token, "Ident");
        assert_eq!(ident_info.alternative_count, 2);
        assert_eq!(ident_info.rule_labels.len(), 2);
        assert!(ident_info.lookahead_candidate); // count=2 > threshold=1

        // Pre-sizing: Proc category should have max_ambiguity-1 = 1
        assert_eq!(result.presized_categories.len(), 1);
        let (cat, size) = &result.presized_categories[0];
        assert_eq!(cat, "Proc");
        assert_eq!(*size, 1); // 2-1 = 1 alternative spilled
    }

    #[test]
    fn test_f2_requires_no_spillover() {
        // F2 with spillover categories — should NOT be recommended
        let profile = GrammarProfile {
            nfa_spillover_categories: 1,
            ambiguous_count: 2,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            !names.contains(&Optimization::EarlyTermination),
            "F2 should not be recommended when NFA spillover is needed: {:?}",
            names
        );
    }

    // ── A3: OptimizationGates tests ──────────────────────────────────────

    #[test]
    fn test_all_enabled_gates() {
        let gates = OptimizationGates::all_enabled();
        assert!(gates.left_factoring);
        assert!(gates.hot_cold_splitting);
        assert!(gates.multi_token_lookahead);
        assert!(gates.spillover_pruning);
        assert!(gates.early_termination);
        assert!(gates.lazy_spillover);
        assert!(gates.wfst_minimization);
        assert!(gates.enhanced_dce);
        assert!(gates.ambiguity_targeting);
        assert!(gates.adaptive_recovery);
    }

    #[test]
    fn test_gates_from_simple_grammar() {
        // Simple grammar: only B2 (adaptive recovery) and A4 (DCE) recommended
        let profile = simple_profile();
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.adaptive_recovery,
            "B2 should be enabled for simple grammars"
        );
        assert!(
            gates.enhanced_dce,
            "A4 should be enabled for grammars with >5 rules"
        );
        // All other gates should be disabled for a simple grammar
        assert!(
            !gates.left_factoring,
            "A1 should not be enabled: shared_prefix_ratio=0.0"
        );
        assert!(
            !gates.hot_cold_splitting,
            "A2 should not be enabled: cold_fraction=0.0"
        );
        assert!(
            !gates.multi_token_lookahead,
            "B1 should not be enabled: ambiguous_fraction=0.0"
        );
    }

    #[test]
    fn test_gates_from_ambiguous_grammar() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.25,
            ambiguous_count: 3,
            nfa_spillover_categories: 2,
            has_beam_width: true,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(gates.multi_token_lookahead, "B1 should be enabled for ambiguous grammars");
        assert!(gates.ambiguity_targeting, "A5 should be enabled");
        assert!(gates.spillover_pruning, "F1 should be enabled with beam + spillover");
        assert!(gates.lazy_spillover, "F3 should be enabled with spillover categories");
        // F2 should NOT be enabled when spillover categories exist
        assert!(
            !gates.early_termination,
            "F2 should not be enabled when NFA spillover is needed"
        );
    }

    #[test]
    fn test_gates_from_cold_heavy_grammar() {
        let profile = GrammarProfile {
            cold_fraction: 0.6,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.hot_cold_splitting,
            "A2 should be enabled when cold_fraction > 0.4"
        );
    }

    #[test]
    fn test_gates_from_large_wfst_grammar() {
        let profile = GrammarProfile {
            total_wfst_states: 50,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.wfst_minimization,
            "B3 should be enabled when total_wfst_states > 4"
        );
    }

    // ── D2: GrammarComplexityReport tests ──────────────────────────────

    #[test]
    fn test_d2_report_build_empty() {
        let profile = simple_profile();
        let wfsts = HashMap::new();
        let first_sets = HashMap::new();
        let report = GrammarComplexityReport::build("empty", &profile, &wfsts, &first_sets, 0, 0);
        assert_eq!(report.grammar_name, "empty");
        assert!(report.categories.is_empty());
        assert_eq!(report.total_wfst_states, 0);
        assert_eq!(report.total_wfst_transitions, 0);
    }

    #[test]
    fn test_d2_report_build_with_wfst() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string(), "LParen".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "POutput".to_string(),
                parse_fn: "parse_poutput".to_string(),
            },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "LParen",
            DispatchAction::Direct {
                rule_label: "PSend".to_string(),
                parse_fn: "parse_psend".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut first_set = FirstSet::new();
        first_set.tokens.insert("Ident".to_string());
        first_set.tokens.insert("LParen".to_string());

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        fsets.insert("Proc".to_string(), first_set);

        let profile = GrammarProfile {
            category_count: 1,
            rule_count: 3,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };

        let report = GrammarComplexityReport::build("test_lang", &profile, &wfsts, &fsets, 0, 0);
        assert_eq!(report.grammar_name, "test_lang");
        assert_eq!(report.categories.len(), 1);

        let cat = &report.categories[0];
        assert_eq!(cat.name, "Proc");
        assert_eq!(cat.dispatch_token_count, 2);
        assert_eq!(cat.ambiguous_token_count, 1); // Ident is ambiguous
        assert_eq!(cat.max_ambiguity, 2); // Ident has 2 alternatives
        assert!(cat.wfst_state_count > 0);
        assert_eq!(cat.wfst_action_count, 3);
        assert!(report.total_wfst_states > 0);
        assert!(report.total_wfst_transitions > 0);
    }

    #[test]
    fn test_d2_report_categories_sorted_by_name() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Create two categories: "Proc" and "Int" — report should sort alphabetically
        let mut wfsts = HashMap::new();
        let mut fsets = HashMap::new();

        for cat_name in &["Proc", "Int"] {
            let token_map = TokenIdMap::from_names(
                vec!["Ident".to_string()].into_iter(),
            );
            let mut builder = PredictionWfstBuilder::new(cat_name, token_map);
            builder.add_action(
                "Ident",
                DispatchAction::Direct {
                    rule_label: format!("{}_rule", cat_name),
                    parse_fn: format!("parse_{}", cat_name.to_lowercase()),
                },
                TropicalWeight::new(0.0),
            );
            wfsts.insert(cat_name.to_string(), builder.build());
            let mut fs = FirstSet::new();
            fs.tokens.insert("Ident".to_string());
            fsets.insert(cat_name.to_string(), fs);
        }

        let profile = GrammarProfile {
            category_count: 2,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let report = GrammarComplexityReport::build("multi", &profile, &wfsts, &fsets, 0, 0);
        assert_eq!(report.categories.len(), 2);
        assert_eq!(report.categories[0].name, "Int"); // Int before Proc alphabetically
        assert_eq!(report.categories[1].name, "Proc");
    }

    #[test]
    fn test_d2_format_compact_contains_key_metrics() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.15,
            cold_fraction: 0.3,
            nfa_spillover_categories: 1,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let report = GrammarComplexityReport {
            grammar_name: "TestLang".to_string(),
            profile: profile.clone(),
            categories: vec![CategoryComplexity {
                name: "Expr".to_string(),
                dispatch_token_count: 5,
                ambiguous_token_count: 2,
                max_ambiguity: 3,
                wfst_state_count: 8,
                wfst_action_count: 10,
            }],
            recommended_optimizations: vec![
                ("AmbiguityTargeting".to_string(), 1.9, 0.1, "ambiguous_fraction=0.15".to_string(), OptimizationStatus::Diagnostic),
            ],
            total_wfst_states: 8,
            total_wfst_transitions: 12,
            composed_dispatch_entries: 7,
            resolved_ambiguities: 2,
        };

        let compact = report.format_compact();
        assert!(compact.contains("4 cats"), "should contain category count");
        assert!(compact.contains("20 rules"), "should contain rule count");
        assert!(compact.contains("8 WFST states"), "should contain WFST state count");
        assert!(compact.contains("12 transitions"), "should contain transition count");
        assert!(compact.contains("15.0% ambiguous"), "should contain ambiguous fraction");
        assert!(compact.contains("30.0% cold"), "should contain cold fraction");
        assert!(compact.contains("1 NFA spill"), "should contain NFA spillover count");
        assert!(compact.contains("7 dispatch entries"), "should contain dispatch entries");
        assert!(compact.contains("2 resolved"), "should contain resolved count");
        assert!(compact.contains("Expr(5t/10a)"), "should contain per-category summary");
        // Recommendations are NOT in compact format (I05 lint handles them)
        assert!(!compact.contains("AmbiguityTargeting"), "recommendations should not appear in compact format");
    }

    #[test]
    fn test_d2_format_compact_empty_categories() {
        let profile = simple_profile();
        let report = GrammarComplexityReport {
            grammar_name: "Simple".to_string(),
            profile,
            categories: vec![],
            recommended_optimizations: vec![],
            total_wfst_states: 0,
            total_wfst_transitions: 0,
            composed_dispatch_entries: 0,
            resolved_ambiguities: 0,
        };
        let compact = report.format_compact();
        // Should NOT contain per-category line when no categories
        assert!(!compact.contains("per-category"), "empty categories should not show per-category line");
        // Should still contain scalar metrics
        assert!(compact.contains("4 cats"), "should contain category count");
        assert!(compact.contains("20 rules"), "should contain rule count");
    }

    #[test]
    fn test_d2_to_diagnostic() {
        let profile = simple_profile();
        let report = GrammarComplexityReport {
            grammar_name: "TestLang".to_string(),
            profile,
            categories: vec![],
            recommended_optimizations: vec![],
            total_wfst_states: 0,
            total_wfst_transitions: 0,
            composed_dispatch_entries: 0,
            resolved_ambiguities: 0,
        };
        let diag = report.to_diagnostic();
        assert_eq!(diag.id, "D02");
        assert_eq!(diag.name, "grammar-profile");
        assert_eq!(diag.grammar_name.as_deref(), Some("TestLang"));
        assert!(matches!(diag.severity, crate::lint::LintSeverity::Note));
    }

    #[test]
    fn test_d2_report_includes_recommendations() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Build a grammar profile that triggers B2 (adaptive recovery) + A4 (DCE)
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        let mut fs = FirstSet::new();
        fs.tokens.insert("Ident".to_string());
        fsets.insert("Proc".to_string(), fs);

        let profile = simple_profile(); // rule_count=20 > 5 → A4 applicable
        let report = GrammarComplexityReport::build("reco_test", &profile, &wfsts, &fsets, 0, 0);

        // Should have at least B2 (adaptive recovery) and A4 (DCE) in recommendations
        assert!(
            !report.recommended_optimizations.is_empty(),
            "should have at least one recommendation"
        );
        let opt_names: Vec<&str> = report.recommended_optimizations.iter()
            .map(|(name, _, _, _, _)| name.as_str())
            .collect();
        assert!(
            opt_names.iter().any(|n| n.contains("AdaptiveRecovery")),
            "B2 should be recommended: {:?}",
            opt_names
        );

        // Verify status tags in report: B2 (AdaptiveRecovery) should be auto
        let statuses: Vec<(&str, &OptimizationStatus)> = report.recommended_optimizations.iter()
            .map(|(name, _, _, _, status)| (name.as_str(), status))
            .collect();
        assert!(
            statuses.iter().any(|(n, s)| n.contains("AdaptiveRecovery") && **s == OptimizationStatus::Auto),
            "B2 should have Auto status: {:?}", statuses
        );
    }

    // ══════════════════════════════════════════════════════════════════
    // Sprint 4: FromStr, none_enabled, from_env, from_env_or_recommendations
    // ══════════════════════════════════════════════════════════════════

    #[test]
    fn test_optimization_from_str_short_codes() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("A1").expect("A1"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("A2").expect("A2"), Optimization::HotColdSplitting);
        assert_eq!(Optimization::from_str("A4").expect("A4"), Optimization::EnhancedDeadCodeElimination);
        assert_eq!(Optimization::from_str("A5").expect("A5"), Optimization::AmbiguityTargeting);
        assert_eq!(Optimization::from_str("B1").expect("B1"), Optimization::MultiTokenLookahead);
        assert_eq!(Optimization::from_str("B2").expect("B2"), Optimization::AdaptiveRecovery);
        assert_eq!(Optimization::from_str("B3").expect("B3"), Optimization::WfstMinimization);
        assert_eq!(Optimization::from_str("F1").expect("F1"), Optimization::SpilloverPruning);
        assert_eq!(Optimization::from_str("F2").expect("F2"), Optimization::EarlyTermination);
        assert_eq!(Optimization::from_str("F3").expect("F3"), Optimization::LazySpillover);
    }

    #[test]
    fn test_optimization_from_str_full_names() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("LeftFactoring").expect("name"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("adaptiverecovery").expect("lower"), Optimization::AdaptiveRecovery);
        assert_eq!(Optimization::from_str("LAZYSPILLOVER").expect("upper"), Optimization::LazySpillover);
        assert_eq!(Optimization::from_str("EnhancedDCE").expect("alias"), Optimization::EnhancedDeadCodeElimination);
    }

    #[test]
    fn test_optimization_from_str_display_format() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("A1:LeftFactoring").expect("display"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("B2:AdaptiveRecovery").expect("display"), Optimization::AdaptiveRecovery);
    }

    #[test]
    fn test_optimization_from_str_invalid() {
        use std::str::FromStr;
        assert!(Optimization::from_str("bogus").is_err());
        assert!(Optimization::from_str("X9").is_err());
        assert!(Optimization::from_str("A3").is_err()); // A3 does not exist
    }

    #[test]
    fn test_none_enabled_all_false() {
        let gates = OptimizationGates::none_enabled();
        assert!(!gates.left_factoring);
        assert!(!gates.hot_cold_splitting);
        assert!(!gates.multi_token_lookahead);
        assert!(!gates.spillover_pruning);
        assert!(!gates.early_termination);
        assert!(!gates.lazy_spillover);
        assert!(!gates.wfst_minimization);
        assert!(!gates.enhanced_dce);
        assert!(!gates.ambiguity_targeting);
        assert!(!gates.adaptive_recovery);
    }

    #[test]
    fn test_from_env_with_specific_opts() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        // Set env var to enable only A1 and F3
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "A1,F3");
        let result = OptimizationGates::from_env();
        // Clean up before asserting (env is process-global)
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(gates.left_factoring, "A1 should be enabled");
        assert!(gates.lazy_spillover, "F3 should be enabled");
        assert!(!gates.hot_cold_splitting, "A2 should not be enabled");
        assert!(!gates.adaptive_recovery, "B2 should not be enabled");
        assert!(!gates.enhanced_dce, "A4 should not be enabled");
    }

    #[test]
    fn test_from_env_all() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "all");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(gates.left_factoring);
        assert!(gates.hot_cold_splitting);
        assert!(gates.multi_token_lookahead);
        assert!(gates.spillover_pruning);
        assert!(gates.early_termination);
        assert!(gates.lazy_spillover);
        assert!(gates.wfst_minimization);
        assert!(gates.enhanced_dce);
        assert!(gates.ambiguity_targeting);
        assert!(gates.adaptive_recovery);
        assert!(gates.backtracking_elimination);
    }

    #[test]
    fn test_from_env_none() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "none");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(!gates.left_factoring);
        assert!(!gates.adaptive_recovery);
        assert!(!gates.backtracking_elimination);
    }

    #[test]
    fn test_from_env_unset() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");
        let result = OptimizationGates::from_env();
        assert!(result.expect("no error").is_none(), "unset should return None");
    }

    #[test]
    fn test_from_env_invalid_value() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "A1,bogus,F3");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        assert!(result.is_err(), "should fail on invalid optimization name");
    }

    #[test]
    fn test_from_env_or_recommendations_fallback() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        // Ensure env var is unset so it falls back to recommendations
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");
        let profile = GrammarProfile {
            rule_count: 20,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_env_or_recommendations(&recommended);
        // Should be identical to from_recommendations
        let expected = OptimizationGates::from_recommendations(&recommended);
        assert_eq!(gates.left_factoring, expected.left_factoring);
        assert_eq!(gates.adaptive_recovery, expected.adaptive_recovery);
        assert_eq!(gates.enhanced_dce, expected.enhanced_dce);
    }

    #[test]
    fn test_trs_confluence_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::TrsConfluenceCheck),
            "TrsConfluenceCheck should be in evaluated candidates"
        );
    }

    #[test]
    fn test_vpa_inclusion_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::VpaInclusionCheck),
            "VpaInclusionCheck should be in evaluated candidates"
        );
    }

    #[test]
    fn test_safety_verification_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::SafetyVerification),
            "SafetyVerification should be in evaluated candidates"
        );
    }

    #[test]
    fn test_cegar_refinement_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::CegarRefinement),
            "CegarRefinement should be in evaluated candidates"
        );
    }

    #[test]
    fn test_petri_deadlock_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::PetriDeadlockCheck),
            "PetriDeadlockCheck should be in evaluated candidates"
        );
    }

    // ── New codegen catalog tests ────────────────────────────────────────

    #[test]
    fn test_art03_from_str() {
        use std::str::FromStr;
        assert_eq!(
            Optimization::from_str("ART03").expect("ART03"),
            Optimization::RelationIndexing
        );
        assert_eq!(
            Optimization::from_str("relationindexing").expect("lower"),
            Optimization::RelationIndexing
        );
        assert_eq!(
            Optimization::from_str("ART03:RelationIndexing").expect("display"),
            Optimization::RelationIndexing
        );
    }

    #[test]
    fn test_db02_applicable_small_grammar() {
        // DB02 (LazyAnalysis) is applicable when category_count < 3
        let profile = GrammarProfile {
            category_count: 2,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let all = evaluate_optimizations(&profile);
        let db02 = all.iter().find(|c| c.optimization == Optimization::LazyAnalysis);
        assert!(db02.is_some(), "DB02 should be in evaluated candidates");
        assert!(
            db02.expect("db02").applicable,
            "DB02 should be applicable when category_count=2 < 3"
        );

        // Not applicable for large grammars
        let profile_large = GrammarProfile {
            category_count: 5,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let all_large = evaluate_optimizations(&profile_large);
        let db02_large = all_large.iter().find(|c| c.optimization == Optimization::LazyAnalysis);
        assert!(
            !db02_large.expect("db02_large").applicable,
            "DB02 should not be applicable when category_count=5 >= 3"
        );
    }

    #[test]
    fn test_evaluate_includes_new_optimizations() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        let opt_set: std::collections::HashSet<Optimization> =
            all.iter().map(|c| c.optimization).collect();

        // Spot-check representatives from each category
        assert!(opt_set.contains(&Optimization::HashConsing), "ART01 missing");
        assert!(opt_set.contains(&Optimization::RelationIndexing), "ART03 missing");
        assert!(opt_set.contains(&Optimization::DemandDriven), "ART06 missing");
        assert!(opt_set.contains(&Optimization::JoinOrdering), "BCG01 missing");
        assert!(opt_set.contains(&Optimization::GroundShortCircuit), "BCG04 missing");
        assert!(opt_set.contains(&Optimization::EqStrata), "BCG06 missing");
        assert!(opt_set.contains(&Optimization::CombRepacking), "AL01 missing");
        assert!(opt_set.contains(&Optimization::HybridLexer), "AL02 missing");
        assert!(opt_set.contains(&Optimization::AcceptBitmapWiden), "AL06 missing");
        assert!(opt_set.contains(&Optimization::BpCompaction), "BP01 missing");
        assert!(opt_set.contains(&Optimization::TrivialInline), "BP04 missing");
        assert!(opt_set.contains(&Optimization::BpRangeLoop), "BP05 missing");
        assert!(opt_set.contains(&Optimization::FrequencyOrdering), "CD01 missing");
        assert!(opt_set.contains(&Optimization::ComputedGoto), "CD03 missing");
        assert!(opt_set.contains(&Optimization::PrefixCse), "CD05 missing");
        assert!(opt_set.contains(&Optimization::IncrementalFirstFollow), "DB01 missing");
        assert!(opt_set.contains(&Optimization::LazyAnalysis), "DB02 missing");
        assert!(opt_set.contains(&Optimization::ParallelAnalysis), "DB03 missing");
        assert!(opt_set.contains(&Optimization::CachedLints), "DB04 missing");
    }

    #[test]
    fn test_new_optimization_from_str_all_codes() {
        use std::str::FromStr;
        let codes_and_variants = [
            ("ART01", Optimization::HashConsing),
            ("ART02", Optimization::IncrementalDelta),
            ("ART03", Optimization::RelationIndexing),
            ("ART04", Optimization::CongruenceBloom),
            ("ART05", Optimization::DepthBound),
            ("ART06", Optimization::DemandDriven),
            ("BCG01", Optimization::JoinOrdering),
            ("BCG02", Optimization::RuleFusion),
            ("BCG03", Optimization::EqCongruencePrune),
            ("BCG04", Optimization::GroundShortCircuit),
            ("BCG05", Optimization::NormalizeDedup),
            ("BCG06", Optimization::EqStrata),
            ("AL01", Optimization::CombRepacking),
            ("AL02", Optimization::HybridLexer),
            ("AL03", Optimization::SimdWhitespace),
            ("AL04", Optimization::KeywordMph),
            ("AL05", Optimization::MultiByteChain),
            ("AL06", Optimization::AcceptBitmapWiden),
            ("BP01", Optimization::BpCompaction),
            ("BP02", Optimization::TailCallElim),
            ("BP03", Optimization::BpTableLookup),
            ("BP04", Optimization::TrivialInline),
            ("BP05", Optimization::BpRangeLoop),
            ("CD01", Optimization::FrequencyOrdering),
            ("CD02", Optimization::SegmentMerging),
            ("CD03", Optimization::ComputedGoto),
            ("CD04", Optimization::JumpThreading),
            ("CD05", Optimization::PrefixCse),
            ("DB01", Optimization::IncrementalFirstFollow),
            ("DB02", Optimization::LazyAnalysis),
            ("DB03", Optimization::ParallelAnalysis),
            ("DB04", Optimization::CachedLints),
        ];
        for (code, expected) in &codes_and_variants {
            assert_eq!(
                Optimization::from_str(code).unwrap_or_else(|e| panic!("{}: {}", code, e)),
                *expected,
                "short code {} should parse",
                code
            );
        }
    }

    #[test]
    fn test_new_optimization_gates_from_env_codegen() {
        let _lock = ENV_MUTEX.lock().expect("env mutex poisoned");
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "ART03,BP04,CD01");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(gates.relation_indexing, "ART03 should be enabled");
        assert!(gates.trivial_inline, "BP04 should be enabled");
        assert!(gates.frequency_ordering, "CD01 should be enabled");
        assert!(!gates.hash_consing, "ART01 should not be enabled");
        assert!(!gates.computed_goto, "CD03 should not be enabled");
    }

    // ── Display / FromStr roundtrip tests ────────────────────────────────

    /// Returns all 52 `Optimization` variants in declaration order.
    fn all_optimizations() -> Vec<Optimization> {
        vec![
            Optimization::LeftFactoring,
            Optimization::HotColdSplitting,
            Optimization::EnhancedDeadCodeElimination,
            Optimization::AmbiguityTargeting,
            Optimization::MultiTokenLookahead,
            Optimization::AdaptiveRecovery,
            Optimization::WfstMinimization,
            Optimization::SpilloverPruning,
            Optimization::EarlyTermination,
            Optimization::LazySpillover,
            Optimization::BacktrackingElimination,
            Optimization::ContextDisambiguation,
            Optimization::WpdsReachabilityCheck,
            Optimization::TrsConfluenceCheck,
            Optimization::VpaInclusionCheck,
            Optimization::SafetyVerification,
            Optimization::CegarRefinement,
            Optimization::PetriDeadlockCheck,
            Optimization::HashConsing,
            Optimization::IncrementalDelta,
            Optimization::RelationIndexing,
            Optimization::CongruenceBloom,
            Optimization::DepthBound,
            Optimization::DemandDriven,
            Optimization::JoinOrdering,
            Optimization::RuleFusion,
            Optimization::EqCongruencePrune,
            Optimization::GroundShortCircuit,
            Optimization::NormalizeDedup,
            Optimization::EqStrata,
            Optimization::CombRepacking,
            Optimization::HybridLexer,
            Optimization::SimdWhitespace,
            Optimization::KeywordMph,
            Optimization::MultiByteChain,
            Optimization::AcceptBitmapWiden,
            Optimization::BpCompaction,
            Optimization::TailCallElim,
            Optimization::BpTableLookup,
            Optimization::TrivialInline,
            Optimization::BpRangeLoop,
            Optimization::FrequencyOrdering,
            Optimization::SegmentMerging,
            Optimization::ComputedGoto,
            Optimization::JumpThreading,
            Optimization::PrefixCse,
            Optimization::IncrementalFirstFollow,
            Optimization::LazyAnalysis,
            Optimization::ParallelAnalysis,
            Optimization::CachedLints,
        ]
    }

    #[test]
    fn test_optimization_display_fromstr_roundtrip_all() {
        use std::str::FromStr;
        let variants = all_optimizations();
        assert_eq!(variants.len(), 50, "expected exactly 50 variants");

        for variant in &variants {
            let display = variant.to_string();
            // Display format is "CODE:Name" — verify it contains a colon
            assert!(
                display.contains(':'),
                "Display output for {:?} should contain ':', got: {}",
                variant,
                display
            );

            let (short_code, name) = display.split_once(':').expect("split on ':'");

            // Roundtrip via short code
            let parsed_code = Optimization::from_str(short_code).unwrap_or_else(|e| {
                panic!(
                    "FromStr should accept short code '{}' for {:?}: {}",
                    short_code, variant, e
                )
            });
            assert_eq!(
                parsed_code, *variant,
                "short code '{}' should roundtrip to {:?}",
                short_code, variant
            );

            // Roundtrip via name
            let parsed_name = Optimization::from_str(name).unwrap_or_else(|e| {
                panic!(
                    "FromStr should accept name '{}' for {:?}: {}",
                    name, variant, e
                )
            });
            assert_eq!(
                parsed_name, *variant,
                "name '{}' should roundtrip to {:?}",
                name, variant
            );

            // Roundtrip via full Display output (colon-separated form)
            let parsed_full = Optimization::from_str(&display).unwrap_or_else(|e| {
                panic!(
                    "FromStr should accept full display '{}' for {:?}: {}",
                    display, variant, e
                )
            });
            assert_eq!(
                parsed_full, *variant,
                "full display '{}' should roundtrip to {:?}",
                display, variant
            );
        }
    }

    #[test]
    fn test_optimization_fromstr_short_codes() {
        use std::str::FromStr;
        let all_codes: Vec<(&str, Optimization)> = vec![
            ("A1", Optimization::LeftFactoring),
            ("A2", Optimization::HotColdSplitting),
            ("A4", Optimization::EnhancedDeadCodeElimination),
            ("A5", Optimization::AmbiguityTargeting),
            ("B1", Optimization::MultiTokenLookahead),
            ("B2", Optimization::AdaptiveRecovery),
            ("B3", Optimization::WfstMinimization),
            ("F1", Optimization::SpilloverPruning),
            ("F2", Optimization::EarlyTermination),
            ("F3", Optimization::LazySpillover),
            ("G1", Optimization::BacktrackingElimination),
            ("H1", Optimization::ContextDisambiguation),
            ("G25", Optimization::WpdsReachabilityCheck),
            ("T01", Optimization::TrsConfluenceCheck),
            ("V01", Optimization::VpaInclusionCheck),
            ("S01", Optimization::SafetyVerification),
            ("S03", Optimization::CegarRefinement),
            ("N01", Optimization::PetriDeadlockCheck),
            ("ART01", Optimization::HashConsing),
            ("ART02", Optimization::IncrementalDelta),
            ("ART03", Optimization::RelationIndexing),
            ("ART04", Optimization::CongruenceBloom),
            ("ART05", Optimization::DepthBound),
            ("ART06", Optimization::DemandDriven),
            ("BCG01", Optimization::JoinOrdering),
            ("BCG02", Optimization::RuleFusion),
            ("BCG03", Optimization::EqCongruencePrune),
            ("BCG04", Optimization::GroundShortCircuit),
            ("BCG05", Optimization::NormalizeDedup),
            ("BCG06", Optimization::EqStrata),
            ("AL01", Optimization::CombRepacking),
            ("AL02", Optimization::HybridLexer),
            ("AL03", Optimization::SimdWhitespace),
            ("AL04", Optimization::KeywordMph),
            ("AL05", Optimization::MultiByteChain),
            ("AL06", Optimization::AcceptBitmapWiden),
            ("BP01", Optimization::BpCompaction),
            ("BP02", Optimization::TailCallElim),
            ("BP03", Optimization::BpTableLookup),
            ("BP04", Optimization::TrivialInline),
            ("BP05", Optimization::BpRangeLoop),
            ("CD01", Optimization::FrequencyOrdering),
            ("CD02", Optimization::SegmentMerging),
            ("CD03", Optimization::ComputedGoto),
            ("CD04", Optimization::JumpThreading),
            ("CD05", Optimization::PrefixCse),
            ("DB01", Optimization::IncrementalFirstFollow),
            ("DB02", Optimization::LazyAnalysis),
            ("DB03", Optimization::ParallelAnalysis),
            ("DB04", Optimization::CachedLints),
        ];
        assert_eq!(all_codes.len(), 50, "expected 50 short codes for all 50 variants");

        for (code, expected) in &all_codes {
            let parsed = Optimization::from_str(code).unwrap_or_else(|e| {
                panic!("FromStr should accept short code '{}': {}", code, e)
            });
            assert_eq!(
                parsed, *expected,
                "short code '{}' should parse to {:?}",
                code, expected
            );
        }
    }

    #[test]
    fn test_optimization_fromstr_invalid() {
        use std::str::FromStr;
        let result = Optimization::from_str("NotAnOptimization");
        assert!(
            result.is_err(),
            "FromStr should reject 'NotAnOptimization', got: {:?}",
            result
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("unknown optimization"),
            "error message should contain 'unknown optimization', got: {}",
            err
        );
    }

    #[test]
    fn test_optimization_fromstr_case_insensitive() {
        use std::str::FromStr;
        // Test several case variations for LeftFactoring
        for input in &["leftfactoring", "LEFTFACTORING", "LeftFactoring", "lEfTfAcToRiNg"] {
            let parsed = Optimization::from_str(input).unwrap_or_else(|e| {
                panic!("FromStr should accept '{}': {}", input, e)
            });
            assert_eq!(
                parsed,
                Optimization::LeftFactoring,
                "'{}' should parse to LeftFactoring",
                input
            );
        }

        // Test case insensitivity for EnhancedDCE (the abbreviated Display name)
        for input in &["enhanceddce", "ENHANCEDDCE", "EnhancedDCE"] {
            let parsed = Optimization::from_str(input).unwrap_or_else(|e| {
                panic!("FromStr should accept '{}': {}", input, e)
            });
            assert_eq!(
                parsed,
                Optimization::EnhancedDeadCodeElimination,
                "'{}' should parse to EnhancedDeadCodeElimination",
                input
            );
        }

        // Test case insensitivity for a catalog name
        for input in &["hashconsing", "HASHCONSING", "HashConsing"] {
            let parsed = Optimization::from_str(input).unwrap_or_else(|e| {
                panic!("FromStr should accept '{}': {}", input, e)
            });
            assert_eq!(
                parsed,
                Optimization::HashConsing,
                "'{}' should parse to HashConsing",
                input
            );
        }
    }

    #[test]
    fn test_all_variants_covered() {
        use std::collections::HashSet;
        use std::str::FromStr;

        // Collect all variants from all_optimizations() into a set
        let variants: HashSet<Optimization> = all_optimizations().into_iter().collect();
        assert_eq!(
            variants.len(),
            50,
            "all_optimizations() should return exactly 50 unique variants"
        );

        // Also verify each variant has a unique Display representation
        let display_strings: HashSet<String> =
            all_optimizations().iter().map(|o| o.to_string()).collect();
        assert_eq!(
            display_strings.len(),
            50,
            "each variant should have a unique Display string"
        );

        // Verify all short codes parse to unique variants
        let all_short_codes = [
            "A1", "A2", "A4", "A5", "B1", "B2", "B3", "F1", "F2", "F3",
            "G1", "H1", "G25", "T01", "V01", "S01", "S03", "N01",
            "ART01", "ART02", "ART03", "ART04", "ART05", "ART06",
            "BCG01", "BCG02", "BCG03", "BCG04", "BCG05", "BCG06",
            "AL01", "AL02", "AL03", "AL04", "AL05", "AL06",
            "BP01", "BP02", "BP03", "BP04", "BP05",
            "CD01", "CD02", "CD03", "CD04", "CD05",
            "DB01", "DB02", "DB03", "DB04",
        ];
        let parsed_variants: HashSet<Optimization> = all_short_codes
            .iter()
            .map(|code| {
                Optimization::from_str(code)
                    .unwrap_or_else(|e| panic!("short code '{}' should parse: {}", code, e))
            })
            .collect();

        // All 50 short codes should map to 50 unique variants (one per variant).
        assert_eq!(
            parsed_variants.len(),
            all_short_codes.len(),
            "each short code should map to a unique variant"
        );
        // Verify every variant from all_optimizations() is reachable via some short code
        for variant in &variants {
            assert!(
                parsed_variants.contains(variant),
                "variant {:?} should be reachable via a short code",
                variant
            );
        }
    }

    // ── Advanced Automata Codegen Promotion Tests ──────────────────────────

    #[cfg(feature = "symbolic-automata")]
    #[test]
    fn test_optimization_status_auto_symbolic() {
        assert_eq!(
            Optimization::SymbolicGuardAnalysis.status(),
            OptimizationStatus::Auto,
            "SYM01 should be Auto (drives SYM01-DCE codegen)"
        );
    }

    #[cfg(feature = "probabilistic")]
    #[test]
    fn test_optimization_status_auto_probabilistic() {
        assert_eq!(
            Optimization::ProbabilisticAnalysis.status(),
            OptimizationStatus::Auto,
            "PR01 should be Auto (drives PR01-DCE + PR01-WEIGHT codegen)"
        );
    }

    #[cfg(feature = "alternating")]
    #[test]
    fn test_optimization_status_auto_alternating() {
        assert_eq!(
            Optimization::WeightedAlternatingAnalysis.status(),
            OptimizationStatus::Auto,
            "N06 should be Auto (drives N06-ISO bisimulation codegen)"
        );
    }

    #[cfg(feature = "register-automata")]
    #[test]
    fn test_optimization_status_auto_register() {
        assert_eq!(
            Optimization::RegisterAnalysis.status(),
            OptimizationStatus::Auto,
            "RA01 should be Auto (drives RA01-SKIP dead binder codegen)"
        );
    }

    #[cfg(feature = "vpa")]
    #[test]
    fn test_optimization_status_diagnostic_vpa() {
        assert_eq!(
            Optimization::WeightedVpaAnalysis.status(),
            OptimizationStatus::Diagnostic,
            "V05 should be Diagnostic (informational only)"
        );
    }

    #[cfg(feature = "multi-tape")]
    #[test]
    fn test_optimization_status_diagnostic_multi_tape() {
        assert_eq!(
            Optimization::MultiTapeAnalysis.status(),
            OptimizationStatus::Diagnostic,
            "MT01 should be Diagnostic (informational only)"
        );
    }

    #[cfg(feature = "symbolic-automata")]
    #[test]
    fn test_gates_symbolic_dce_set_when_applicable() {
        let profile = GrammarProfile {
            unsatisfiable_guard_count: 3,
            rule_count: 10,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.symbolic_guard_dce,
            "symbolic_guard_dce should be true when unsatisfiable_guard_count > 0 and rule_count > 5"
        );
    }

    #[cfg(feature = "symbolic-automata")]
    #[test]
    fn test_gates_symbolic_dce_profile_default_zero() {
        let profile = simple_profile();
        assert_eq!(
            profile.unsatisfiable_guard_count, 0,
            "simple_profile() should have unsatisfiable_guard_count == 0"
        );
    }

    #[cfg(feature = "probabilistic")]
    #[test]
    fn test_gates_probabilistic_set_when_applicable() {
        let profile = GrammarProfile {
            low_selectivity_count: 2,
            rule_count: 10,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            #[cfg(feature = "register-automata")]
            dead_register_count: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.probabilistic_dce,
            "probabilistic_dce should be true when low_selectivity_count > 0 and rule_count > 3"
        );
        assert!(
            gates.probabilistic_weight_blend,
            "probabilistic_weight_blend should be true when ProbabilisticAnalysis is recommended"
        );
    }

    #[cfg(feature = "register-automata")]
    #[test]
    fn test_gates_register_set_when_applicable() {
        let profile = GrammarProfile {
            dead_register_count: 1,
            category_count: 3,
            #[cfg(feature = "symbolic-automata")]
            unsatisfiable_guard_count: 0,
            #[cfg(feature = "probabilistic")]
            probabilistic_mean_entropy: 0.0,
            #[cfg(feature = "probabilistic")]
            low_selectivity_count: 0,
            #[cfg(feature = "alternating")]
            bisimulation_extra_groups: 0,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.skip_dead_binders,
            "skip_dead_binders should be true when dead_register_count > 0 and category_count >= 1"
        );
    }

    #[test]
    fn test_grammar_profile_new_fields_default() {
        #[allow(unused_variables)]
        let profile = simple_profile();

        // Verify all advanced automata fields default to zero/0.0
        #[cfg(feature = "symbolic-automata")]
        assert_eq!(
            profile.unsatisfiable_guard_count, 0,
            "unsatisfiable_guard_count should default to 0"
        );

        #[cfg(feature = "probabilistic")]
        {
            assert!(
                profile.probabilistic_mean_entropy == 0.0,
                "probabilistic_mean_entropy should default to 0.0"
            );
            assert_eq!(
                profile.low_selectivity_count, 0,
                "low_selectivity_count should default to 0"
            );
        }

        #[cfg(feature = "alternating")]
        assert_eq!(
            profile.bisimulation_extra_groups, 0,
            "bisimulation_extra_groups should default to 0"
        );

        #[cfg(feature = "register-automata")]
        assert_eq!(
            profile.dead_register_count, 0,
            "dead_register_count should default to 0"
        );
    }

    #[cfg(feature = "symbolic-automata")]
    #[test]
    fn test_all_enabled_includes_new_gates() {
        let gates = OptimizationGates::all_enabled();
        assert!(
            gates.symbolic_guard_dce,
            "all_enabled() should have symbolic_guard_dce == true"
        );
    }

    #[cfg(feature = "probabilistic")]
    #[test]
    fn test_none_enabled_excludes_new_gates() {
        let gates = OptimizationGates::none_enabled();
        assert!(
            !gates.probabilistic_dce,
            "none_enabled() should have probabilistic_dce == false"
        );
    }
}
