//! Core language traits and types for MeTTaIL
//!
//! These types are shared between the macro-generated code and the REPL.

use std::any::Any;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::LanguageMetadata;

/// Seed facts for pre-populating Ascent relations before fixpoint.
///
/// Keys are relation names (e.g., `"certified"`), values are tuples
/// represented as string vectors (e.g., `vec![vec!["item_A"]]`).
/// The codegen parses each string into the relation's parameter type
/// at runtime.
pub type SeedFacts = HashMap<String, Vec<Vec<String>>>;

// =============================================================================
// Type Inference Types
// =============================================================================

/// Runtime representation of inferred types for REPL display
///
/// This mirrors the compile-time `InferredType` but is available at runtime
/// for displaying types to users.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermType {
    /// Base type: Name, Proc, etc.
    Base(String),
    /// Function type: [Domain -> Codomain]
    Arrow(Box<TermType>, Box<TermType>),
    /// Multi-argument function type: [Domain* -> Codomain]
    MultiArrow(Box<TermType>, Box<TermType>),
    /// Phase D.7 (2026-05-17, M14.4): union type capturing inference
    /// over an `Ambiguous(Vec<Inner>)` term. Each alternative's
    /// inferred type lives in the inner vec; downstream callers can
    /// inspect every typing or pick one.
    ///
    /// Constructor `union(types)` deduplicates and collapses
    /// trivial cases: empty → `Unknown`; single-elem → that element;
    /// otherwise the resulting `Ambiguous(Vec<TermType>)`.
    Ambiguous(Vec<TermType>),
    /// Unknown type (inference failed or not applicable)
    Unknown,
}

impl fmt::Display for TermType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermType::Base(name) => write!(f, "{}", name),
            TermType::Arrow(domain, codomain) => write!(f, "[{} -> {}]", domain, codomain),
            TermType::MultiArrow(domain, codomain) => write!(f, "[{}* -> {}]", domain, codomain),
            TermType::Ambiguous(types) => {
                // Render as a pipe-separated union: `Int | Bool | Float`.
                let parts: Vec<String> = types.iter().map(|t| format!("{}", t)).collect();
                write!(f, "{}", parts.join(" | "))
            },
            TermType::Unknown => write!(f, "?"),
        }
    }
}

impl TermType {
    /// Create a base type
    pub fn base(name: impl Into<String>) -> Self {
        TermType::Base(name.into())
    }

    /// Create a function type
    pub fn arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::Arrow(Box::new(domain), Box::new(codomain))
    }

    /// Create a multi-argument function type
    pub fn multi_arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::MultiArrow(Box::new(domain), Box::new(codomain))
    }

    /// Phase D.7 (2026-05-17, M14.4): construct an `Ambiguous` union
    /// type with trivial-case folding. Pass in any number of
    /// alternatives; the constructor deduplicates them and collapses:
    ///   - empty input  → `Unknown`
    ///   - 1 unique     → the single element (no wrapper)
    ///   - 2+ unique    → `Ambiguous(Vec<TermType>)`
    pub fn union(types: Vec<TermType>) -> Self {
        // Flatten nested Ambiguous and deduplicate.
        let mut seen: Vec<TermType> = Vec::with_capacity(types.len());
        for ty in types {
            let to_add: Vec<TermType> = match ty {
                TermType::Ambiguous(inner) => inner,
                other => vec![other],
            };
            for t in to_add {
                if !seen.contains(&t) {
                    seen.push(t);
                }
            }
        }
        match seen.len() {
            0 => TermType::Unknown,
            1 => seen.into_iter().next().expect("checked len == 1"),
            _ => TermType::Ambiguous(seen),
        }
    }

    /// Check if this is a function type
    pub fn is_function(&self) -> bool {
        matches!(self, TermType::Arrow(..) | TermType::MultiArrow(..))
    }

    /// Get the domain type if this is a function type
    pub fn domain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(d, _) | TermType::MultiArrow(d, _) => Some(d),
            _ => None,
        }
    }

    /// Get the codomain type if this is a function type
    pub fn codomain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(_, c) | TermType::MultiArrow(_, c) => Some(c),
            _ => None,
        }
    }
}

/// Information about a variable's type in a term
#[derive(Debug, Clone)]
pub struct VarTypeInfo {
    /// The variable name
    pub name: String,
    /// The inferred type
    pub ty: TermType,
}

impl fmt::Display for VarTypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {}", self.name, self.ty)
    }
}

/// A trait for terms (AST nodes) that can be manipulated generically
pub trait Term: fmt::Display + fmt::Debug + Send + Sync {
    /// Clone this term into a Box
    fn clone_box(&self) -> Box<dyn Term>;

    /// Get a unique identifier for this term (for equality comparison)
    fn term_id(&self) -> u64;

    /// Check if this term is equal to another
    fn term_eq(&self, other: &dyn Term) -> bool;

    /// Get this as Any for downcasting
    fn as_any(&self) -> &dyn Any;

    /// Phase F.12.A (2026-05-20): return the `(term_id, Display)` pairs for
    /// each single-category derivation this term represents.
    ///
    /// For unambiguous terms this returns exactly one entry whose `term_id`
    /// equals `self.term_id()`. For `Ambiguous` wrappers, each inner alt
    /// contributes one entry whose `term_id` MUST match the hash recipe
    /// used to construct the corresponding `TermInfo` in `run_ascent`
    /// (DefaultHasher applied to the single-category `Inner::Cat(t)`
    /// variant — this is the load-bearing invariant that lets the
    /// simulation runner and REPL seed multi-source BFS from the
    /// post-parse Ambiguous set).
    ///
    /// Default impl: returns `vec![(self.term_id(), format!("{}", self))]`,
    /// which is correct for any language that has no `Ambiguous` variant.
    /// Generated `impl Term for <Lang>Term` blocks override this when the
    /// language has cross-category projection.
    fn rewrite_seed_ids(&self) -> Vec<(u64, String)> {
        vec![(self.term_id(), format!("{}", self))]
    }
}

/// A trait that all languages must implement
///
/// This trait is auto-generated by the `language!` macro.
pub trait Language: Send + Sync {
    /// Get the name of this language (e.g., "RhoCalc")
    fn name(&self) -> &'static str;

    /// Get static metadata for this language (types, terms, equations, rewrites)
    fn metadata(&self) -> &'static dyn LanguageMetadata;

    /// Parse a term from a string (clears var cache for fresh evaluation)
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Parse a term for environment storage (does NOT clear var cache)
    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Run Ascent on a term and return results
    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String>;

    /// Run Ascent on a term with pre-seeded relation facts.
    ///
    /// The `facts` map keys are relation names (e.g., `"certified"`)
    /// and values are tuples as string vectors (e.g.,
    /// `vec![vec!["item_A"]]`). Before fixpoint evaluation, the
    /// codegen:
    /// 1. Parses each tuple's strings into the relation's parameter
    ///    types and pushes them into the Ascent program struct
    /// 2. Populates the thread-local fact snapshot so the Comm rule's
    ///    `if { evaluate_pred_with_bindings(...) }` guard can check
    ///    per-instance predicates
    ///
    /// Default: delegates to `run_ascent` (ignores facts).
    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = facts;
        self.run_ascent(term)
    }

    /// If the term is fully evaluable (no free variables), evaluate it and return the result term.
    /// Otherwise return `None` (e.g. term contains vars, or language has no native eval).
    /// Default: `None` so languages without native types need not implement.
    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        let _ = term;
        None
    }

    /// Normalize a term (beta-reduce Apply/MApply of Lam/MLam, flatten collections, etc.)
    /// Default: returns a clone (no normalization).
    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        term.clone_box()
    }

    /// Format a term as a string
    fn format_term(&self, term: &dyn Term) -> String {
        format!("{}", term)
    }

    // === Environment Support ===

    /// Create a new empty environment for this language
    fn create_env(&self) -> Box<dyn Any + Send + Sync>;

    /// Add a term to the environment under the given name
    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String>;

    /// Remove a binding from the environment
    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String>;

    /// Clear all bindings from the environment
    fn clear_env(&self, env: &mut dyn Any);

    /// Apply environment substitution to a term (includes normalization/constant folding).
    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String>;

    /// Substitute environment variables without normalizing (no constant folding).
    /// Use for step mode so the term tree is preserved and rewrites can be applied one by one.
    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.substitute_env(term, env)
    }

    /// List all environment bindings as (name, display, optional_comment) tuples
    ///
    /// Returns bindings in insertion order, with any associated comments.
    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)>;

    /// Set a comment for a binding in the environment
    fn set_env_comment(&self, env: &mut dyn Any, name: &str, comment: String)
        -> Result<(), String>;

    /// Check if the environment is empty
    fn is_env_empty(&self, env: &dyn Any) -> bool;

    /// Get a term by name from the environment (any category).
    /// Used so that `exec z` uses the stored term for "z" instead of parsing "z" as a variable,
    /// which can leave e.g. IVar(z) unsubstituted when "z" is bound in another category (e.g. Proc).
    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        let _ = (env, name);
        None
    }

    // === Type Inference Support ===

    /// Infer the type of a term
    ///
    /// For lambda expressions, returns the full function type (e.g., `[Name -> Proc]`).
    /// For other terms, returns their category (e.g., `Proc`, `Name`).
    fn infer_term_type(&self, term: &dyn Term) -> TermType;

    /// Get all free variables and their inferred types in a term
    ///
    /// Returns a list of variable names with their types, inferred from
    /// how they are used in the term.
    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo>;

    /// Infer the type of a specific variable from its usage in a term
    ///
    /// Returns `None` if the variable is not found or its type cannot be inferred.
    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType>;

    /// Decompose a parsed term into CEK evaluation frames.
    ///
    /// Pattern-matches on the language's AST variants and pushes appropriate
    /// `EvalFrame`s onto the evaluator's continuation stack. After this call,
    /// the evaluator is ready to be driven via `step()` or `run_to_completion()`.
    ///
    /// Returns `true` if the term was decomposed (frames were pushed),
    /// `false` if the language has no CEK decomposition (default).
    ///
    /// The same evaluator + observer pattern supports all consumers:
    /// - REPL `exec`: `NullEvalObserver` + `run_to_completion()`
    /// - nREPL: same, with `reset_with_term()` for env persistence
    /// - CLI debugger: custom observer + `step()` loop
    /// - DAP server: protocol observer + `step()` loop
    fn decompose_into_cek(
        &self,
        term: &dyn Term,
        evaluator: &mut mettail_prattail::cek_eval::CekEvaluator,
    ) -> bool {
        let _ = (term, evaluator);
        false
    }
}

/// Results from running Ascent
#[derive(Debug, Clone)]
pub struct AscentResults {
    /// All reachable terms
    pub all_terms: Vec<TermInfo>,

    /// All rewrites (from -> to)
    pub rewrites: Vec<Rewrite>,

    /// Equivalence classes (terms related by equations)
    pub equivalences: Vec<EquivClass>,

    /// Custom relations: name -> relation data
    pub custom_relations: std::collections::HashMap<String, RelationData>,
}

/// Data for a custom relation
#[derive(Debug, Clone)]
pub struct RelationData {
    /// Parameter type names (e.g., ["Proc", "Proc"])
    pub param_types: Vec<String>,
    /// Tuples as formatted strings (each tuple is a Vec of formatted elements)
    pub tuples: Vec<Vec<String>>,
}

/// Information about a term in the rewrite graph
#[derive(Debug, Clone)]
pub struct TermInfo {
    pub term_id: u64,
    pub display: String,
    pub is_normal_form: bool,
}

/// A rewrite from one term to another
#[derive(Debug, Clone)]
pub struct Rewrite {
    pub from_id: u64,
    pub to_id: u64,
    pub rule_name: Option<String>,
}

/// An equivalence class of terms
#[derive(Debug, Clone)]
pub struct EquivClass {
    pub term_ids: Vec<u64>,
}

/// Lazy breadth-first iterator over normal forms reachable from one or more
/// rewrite-graph seeds.
///
/// The iterator preserves seed order and yields every reachable normal form by
/// graph identity. It does not rank by display text or any other presentation
/// heuristic. The rewrite adjacency index is built only when expansion is
/// needed, so an already-normal seed can be observed without scanning the whole
/// rewrite relation.
pub struct ReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: VecDeque<u64>,
    visited: HashSet<u64>,
    term_index: Option<HashMap<u64, usize>>,
    rewrites_by_from: Option<HashMap<u64, Vec<u64>>>,
}

impl<'a> ReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, seed_ids: &[u64]) -> Self {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        for &id in seed_ids {
            if visited.insert(id) {
                queue.push_back(id);
            }
        }
        Self {
            results,
            queue,
            visited,
            term_index: None,
            rewrites_by_from: None,
        }
    }

    fn term_info(&self, id: u64) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(&id).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.all_terms.iter().find(|t| t.term_id == id)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.term_id, idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<u64, Vec<u64>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_id)
                    .or_default()
                    .push(rewrite.to_id);
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for ReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(id) = self.queue.pop_front() {
            let info = match self.term_info(id) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&id))
                .cloned()
                .unwrap_or_default();
            for to_id in next_ids {
                if self.visited.insert(to_id) {
                    self.queue.push_back(to_id);
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy)]
struct WeightedQueueEntry {
    term_id: u64,
    weight: f64,
    sequence: usize,
}

impl PartialEq for WeightedQueueEntry {
    fn eq(&self, other: &Self) -> bool {
        self.term_id == other.term_id
            && self.weight.total_cmp(&other.weight) == Ordering::Equal
            && self.sequence == other.sequence
    }
}

impl Eq for WeightedQueueEntry {}

impl PartialOrd for WeightedQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for WeightedQueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // BinaryHeap pops the greatest element, so reverse the natural order:
        // lower weight first, then lower insertion sequence.
        other
            .weight
            .total_cmp(&self.weight)
            .then_with(|| other.sequence.cmp(&self.sequence))
            .then_with(|| other.term_id.cmp(&self.term_id))
    }
}

/// Lazy priority traversal over normal forms reachable from weighted seeds.
///
/// The queue orders work by the caller-provided seed weight, with seed order as
/// the deterministic tie breaker. Expansion indexes are still built only when a
/// non-normal term is popped, so an already-normal best seed can satisfy a
/// bounded prefix request without scanning the rewrite relation.
pub struct WeightedReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: BinaryHeap<WeightedQueueEntry>,
    visited: HashSet<u64>,
    term_index: Option<HashMap<u64, usize>>,
    rewrites_by_from: Option<HashMap<u64, Vec<u64>>>,
    next_sequence: usize,
}

impl<'a> WeightedReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, weighted_seed_ids: &[(u64, f64)]) -> Self {
        let mut best_by_id: HashMap<u64, (f64, usize)> = HashMap::new();
        for (sequence, &(term_id, weight)) in weighted_seed_ids.iter().enumerate() {
            let weight = if weight.is_nan() {
                f64::INFINITY
            } else {
                weight
            };
            best_by_id
                .entry(term_id)
                .and_modify(|best| {
                    if weight.total_cmp(&best.0) == Ordering::Less
                        || (weight.total_cmp(&best.0) == Ordering::Equal && sequence < best.1)
                    {
                        *best = (weight, sequence);
                    }
                })
                .or_insert((weight, sequence));
        }

        let mut queue = BinaryHeap::new();
        let mut visited = HashSet::new();
        let mut next_sequence = weighted_seed_ids.len();
        for (term_id, (weight, sequence)) in best_by_id {
            visited.insert(term_id);
            next_sequence = next_sequence.max(sequence.saturating_add(1));
            queue.push(WeightedQueueEntry { term_id, weight, sequence });
        }

        Self {
            results,
            queue,
            visited,
            term_index: None,
            rewrites_by_from: None,
            next_sequence,
        }
    }

    fn term_info(&self, id: u64) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(&id).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.all_terms.iter().find(|t| t.term_id == id)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.term_id, idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<u64, Vec<u64>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_id)
                    .or_default()
                    .push(rewrite.to_id);
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for WeightedReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.queue.pop() {
            let info = match self.term_info(entry.term_id) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&entry.term_id))
                .cloned()
                .unwrap_or_default();
            for to_id in next_ids {
                if self.visited.insert(to_id) {
                    let sequence = self.next_sequence;
                    self.next_sequence = self.next_sequence.saturating_add(1);
                    self.queue.push(WeightedQueueEntry {
                        term_id: to_id,
                        weight: entry.weight,
                        sequence,
                    });
                }
            }
        }
        None
    }
}

impl AscentResults {
    /// Create empty results
    pub fn empty() -> Self {
        Self {
            all_terms: Vec::new(),
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    /// Create minimal results for a single term (e.g. after direct eval). One term, no rewrites.
    pub fn from_single_term(term: &dyn Term) -> Self {
        Self {
            all_terms: vec![TermInfo {
                term_id: term.term_id(),
                display: format!("{}", term),
                is_normal_form: true,
            }],
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    /// Lazily iterate normal forms (terms with no outgoing rewrites).
    pub fn normal_forms_iter(&self) -> impl Iterator<Item = &TermInfo> {
        self.all_terms.iter().filter(|t| t.is_normal_form)
    }

    /// Get normal forms (terms with no outgoing rewrites).
    pub fn normal_forms(&self) -> Vec<&TermInfo> {
        self.normal_forms_iter().collect()
    }

    /// Lazily iterate rewrites from a specific term.
    pub fn rewrites_from_iter(&self, term_id: u64) -> impl Iterator<Item = &Rewrite> {
        self.rewrites.iter().filter(move |r| r.from_id == term_id)
    }

    /// Get rewrites from a specific term
    pub fn rewrites_from(&self, term_id: u64) -> Vec<&Rewrite> {
        self.rewrites_from_iter(term_id).collect()
    }

    /// Find a normal form reachable from the given term by following rewrites.
    /// Returns the first normal form reached (BFS). If the start term is already
    /// a normal form, returns it. Returns `None` if the term is not in the graph.
    pub fn normal_form_reachable_from(&self, start_id: u64) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(&[start_id])
            .next()
    }

    /// Multi-source normal-form traversal.
    ///
    /// Yields every normal form reachable from the given seeds, preserving
    /// seed/BFS order. This is the ambiguity-preserving surface for consumers
    /// that receive an `Ambiguous` wrapper from parsing and need to carry all
    /// alternatives into evaluation.
    ///
    /// The rewrite adjacency index is initialized only if a non-normal seed
    /// must be expanded; asking for the first result from an already-normal
    /// seed does not scan the rewrite relation.
    pub fn normal_forms_reachable_from_seeds_iter<'a>(
        &'a self,
        seed_ids: &[u64],
    ) -> ReachableNormalForms<'a> {
        ReachableNormalForms::new(self, seed_ids)
    }

    /// Collect all normal forms reachable from the given seeds.
    pub fn normal_forms_reachable_from_seeds(&self, seed_ids: &[u64]) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids)
            .collect()
    }

    /// Compatibility helper for callers that explicitly want one witness.
    ///
    /// This returns the first result from the lazy multi-source traversal. It
    /// deliberately does not choose by display length or any other heuristic.
    pub fn normal_form_reachable_from_seeds(&self, seed_ids: &[u64]) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids).next()
    }

    /// Multi-source normal-form traversal ordered by seed weight.
    ///
    /// This is the explicit priority-queue surface for callers that carry
    /// parser/evidence weights through to evaluation. It is demand bounded:
    /// callers can use `.take(n)` or `.next()` without collecting all reachable
    /// normal forms.
    pub fn normal_forms_reachable_from_weighted_seeds_iter<'a>(
        &'a self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> WeightedReachableNormalForms<'a> {
        WeightedReachableNormalForms::new(self, weighted_seed_ids)
    }

    /// Collect all normal forms reachable from weighted seeds.
    pub fn normal_forms_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .collect()
    }

    /// Return the first normal form from the lazy weighted traversal.
    pub fn normal_form_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .next()
    }

    /// Get the equivalence class containing a term
    pub fn equiv_class(&self, term_id: u64) -> Option<&EquivClass> {
        self.equivalences
            .iter()
            .find(|ec| ec.term_ids.contains(&term_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_results() -> AscentResults {
        AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    display: "start".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    display: "mid".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 3,
                    display: "done".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 2,
                    rule_name: Some("step1".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 3,
                    rule_name: Some("step2".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn normal_forms_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .normal_forms_iter()
            .map(|term| term.display.as_str())
            .collect();
        let eager: Vec<_> = results
            .normal_forms()
            .iter()
            .map(|term| term.display.as_str())
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec!["done"]);
    }

    #[test]
    fn rewrites_from_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .rewrites_from_iter(1)
            .map(|rewrite| rewrite.to_id)
            .collect();
        let eager: Vec<_> = results
            .rewrites_from(1)
            .iter()
            .map(|rewrite| rewrite.to_id)
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec![2]);
    }

    #[test]
    fn reachable_normal_form_uses_lazy_rewrite_iteration() {
        let results = sample_results();
        let nf = results
            .normal_form_reachable_from(1)
            .expect("normal form should be reachable");

        assert_eq!(nf.term_id, 3);
        assert_eq!(nf.display, "done");
    }

    #[test]
    fn reachable_normal_forms_from_seeds_preserves_ambiguous_alternatives() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    display: "longer-but-first".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    display: "a".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    rule_name: Some("left".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    rule_name: Some("right".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_seeds(&[1, 2])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["longer-but-first", "a"]);

        let first = results
            .normal_form_reachable_from_seeds(&[1, 2])
            .expect("at least one normal form should be reachable");
        assert_eq!(
            first.display, "longer-but-first",
            "single-witness helper must not choose the shortest display"
        );
    }

    #[test]
    fn weighted_reachable_normal_forms_choose_lower_weight_seed_first() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    display: "higher_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    display: "lower_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    display: "higher_weight_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    display: "lower_weight_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    rule_name: Some("high".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    rule_name: Some("low".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let first = results
            .normal_form_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .expect("weighted normal form should be reachable");
        assert_eq!(first.display, "lower_weight_result");

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["lower_weight_result", "higher_weight_result"]);
    }

    #[test]
    fn weighted_reachable_normal_forms_preserve_equal_weight_seed_order() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    display: "first_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    display: "second_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    rule_name: Some("first".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    rule_name: Some("second".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 3.0), (2, 3.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["first_result", "second_result"]);
    }
}
