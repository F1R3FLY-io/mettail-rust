//! Structural Unification with Occurs Check (Martelli & Montanari 1982)
//!
//! Implements first-order syntactic unification as a [`ConstraintTheory`] for
//! pattern matching, type variable solving, and polymorphic type instantiation.
//!
//! ## Algorithm
//!
//! The Martelli-Montanari algorithm maintains a work stack of pending equations
//! `s ≡ t` and a substitution `σ`. At each step it pops an equation, applies `σ`,
//! then dispatches on the structure of the two sides:
//!
//! | Case                              | Action                            |
//! |-----------------------------------|-----------------------------------|
//! | `Var(x) ≡ Var(x)`                 | Skip (trivial identity)           |
//! | `Var(x) ≡ t` (or `t ≡ Var(x)`)   | Occurs check; bind `x ↦ t` in σ  |
//! | `App(f, args₁) ≡ App(f, args₂)`  | Decompose: push `argsᵢ₁ ≡ argsᵢ₂`|
//! | `App(f, _) ≡ App(g, _)` (f ≠ g)  | Constructor clash → failure       |
//! | `Const(a) ≡ Const(a)`            | Skip (trivial identity)           |
//! | `Const(a) ≡ Const(b)` (a ≠ b)   | Constant clash → failure          |
//! | `Const(_) ≡ App(_, _)` or v.v.   | Kind clash → failure              |
//!
//! The algorithm terminates in O(n·α(n)) amortized time with path compression
//! (though this implementation uses explicit substitution application for clarity).
//!
//! ## References
//!
//! - Martelli, A. & Montanari, U. (1982). "An Efficient Unification Algorithm."
//!   ACM Transactions on Programming Languages and Systems, 4(2), 258-282.
//! - Robinson, J. A. (1965). "A Machine-Oriented Logic Based on the Resolution
//!   Principle." Journal of the ACM, 12(1), 23-41.
//! - Baader, F. & Snyder, W. (2001). "Unification Theory." In Handbook of
//!   Automated Reasoning, vol. 1, ch. 8, pp. 445-533.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::logict::{ConstraintTheory, LogicStream};

// ══════════════════════════════════════════════════════════════════════════════
// Term representation
// ══════════════════════════════════════════════════════════════════════════════

/// A term in the unification theory.
///
/// Terms form a free algebra over variables (`Var`), constants (`Const`),
/// and function applications (`App`). This is the standard first-order term
/// language used in unification, logic programming, and type inference.
///
/// # Examples
///
/// ```
/// # use mettail_prattail::unification::TermExpr;
/// // Variable x₀
/// let x = TermExpr::Var(0);
///
/// // Constant "a"
/// let a = TermExpr::Const("a".into());
///
/// // Function application f(x₀, a)
/// let term = TermExpr::App {
///     head: "f".into(),
///     args: vec![x, a],
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TermExpr {
    /// A variable (identified by index).
    Var(usize),
    /// A constant (identified by name).
    Const(String),
    /// A function application f(t₁, ..., tₙ).
    App {
        /// The function/constructor name.
        head: String,
        /// The argument sub-terms.
        args: Vec<TermExpr>,
    },
}

impl fmt::Display for TermExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermExpr::Var(idx) => write!(f, "x{}", idx),
            TermExpr::Const(name) => write!(f, "{}", name),
            TermExpr::App { head, args } => {
                write!(f, "{}(", head)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl TermExpr {
    /// Apply a substitution to this term, replacing bound variables with their
    /// mapped terms. Applies transitively (follows chains of bindings).
    ///
    /// # Algorithm
    ///
    /// Uses an explicit work stack to avoid recursion:
    /// 1. Push the root term onto the stack.
    /// 2. Pop a term. If it is a `Var(x)` with a binding `x ↦ t` in `subst`,
    ///    replace with `t` and re-push (to follow transitive bindings).
    /// 3. For `App(f, args)`, recursively apply to each argument.
    /// 4. `Const` values are unchanged.
    pub fn apply_substitution(&self, subst: &HashMap<usize, TermExpr>) -> TermExpr {
        match self {
            TermExpr::Var(idx) => {
                if let Some(bound) = subst.get(idx) {
                    // Follow transitive bindings: if x ↦ y and y ↦ t, return t.
                    bound.apply_substitution(subst)
                } else {
                    self.clone()
                }
            }
            TermExpr::Const(_) => self.clone(),
            TermExpr::App { head, args } => {
                let applied_args: Vec<TermExpr> = args
                    .iter()
                    .map(|arg| arg.apply_substitution(subst))
                    .collect();
                TermExpr::App {
                    head: head.clone(),
                    args: applied_args,
                }
            }
        }
    }

    /// Check whether variable `var` occurs anywhere in `term`.
    ///
    /// This is the "occurs check" that prevents circular bindings like
    /// `x ↦ f(x)`, which would create infinite terms.
    ///
    /// # Algorithm
    ///
    /// Uses an explicit work stack to avoid recursion. Pushes sub-terms
    /// onto the stack and checks each for the target variable.
    pub fn occurs_in(var: usize, term: &TermExpr) -> bool {
        let mut work_stack: Vec<&TermExpr> = vec![term];
        while let Some(current) = work_stack.pop() {
            match current {
                TermExpr::Var(idx) => {
                    if *idx == var {
                        return true;
                    }
                }
                TermExpr::Const(_) => {}
                TermExpr::App { args, .. } => {
                    for arg in args {
                        work_stack.push(arg);
                    }
                }
            }
        }
        false
    }

    /// Collect the set of all variable indices appearing in this term.
    ///
    /// Uses an explicit work stack to avoid recursion.
    pub fn variables(&self) -> HashSet<usize> {
        let mut vars = HashSet::new();
        let mut work_stack: Vec<&TermExpr> = vec![self];
        while let Some(current) = work_stack.pop() {
            match current {
                TermExpr::Var(idx) => {
                    vars.insert(*idx);
                }
                TermExpr::Const(_) => {}
                TermExpr::App { args, .. } => {
                    for arg in args {
                        work_stack.push(arg);
                    }
                }
            }
        }
        vars
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Term signature
// ══════════════════════════════════════════════════════════════════════════════

/// Set of known constructors with their arities.
///
/// The signature defines the well-formed terms in the algebra. During
/// unification, the signature is not directly enforced (any term can unify
/// with any other structurally compatible term), but it provides metadata
/// for downstream analyses like exhaustiveness checking.
#[derive(Clone, Debug)]
pub struct TermSignature {
    /// Constructor name to arity mapping.
    pub constructors: HashMap<String, usize>,
}

impl TermSignature {
    /// Create an empty signature (no constructors declared).
    pub fn new() -> Self {
        TermSignature {
            constructors: HashMap::new(),
        }
    }

    /// Register a constructor with its arity.
    pub fn add_constructor(&mut self, name: impl Into<String>, arity: usize) {
        self.constructors.insert(name.into(), arity);
    }

    /// Check whether a term is well-formed under this signature.
    ///
    /// Variables and constants are always well-formed. An `App(f, args)` is
    /// well-formed iff `f` is a registered constructor and `|args| == arity(f)`.
    pub fn is_well_formed(&self, term: &TermExpr) -> bool {
        match term {
            TermExpr::Var(_) | TermExpr::Const(_) => true,
            TermExpr::App { head, args } => {
                if let Some(&arity) = self.constructors.get(head) {
                    args.len() == arity && args.iter().all(|a| self.is_well_formed(a))
                } else {
                    // Unknown constructor — accept if signature is open
                    // (for structural unification, we allow unregistered constructors)
                    args.iter().all(|a| self.is_well_formed(a))
                }
            }
        }
    }
}

impl Default for TermSignature {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Unification equation
// ══════════════════════════════════════════════════════════════════════════════

/// An equation between two terms: `lhs ≡ rhs`.
///
/// The fundamental constraint in unification theory. A set of equations
/// is satisfiable iff there exists a substitution σ such that
/// `σ(lhs) = σ(rhs)` for every equation in the set.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnificationEquation {
    /// Left-hand side of the equation.
    pub lhs: TermExpr,
    /// Right-hand side of the equation.
    pub rhs: TermExpr,
}

impl UnificationEquation {
    /// Create a new equation `lhs ≡ rhs`.
    pub fn new(lhs: TermExpr, rhs: TermExpr) -> Self {
        UnificationEquation { lhs, rhs }
    }
}

impl fmt::Display for UnificationEquation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ≡ {}", self.lhs, self.rhs)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Substitution
// ══════════════════════════════════════════════════════════════════════════════

/// A substitution mapping variable indices to terms.
///
/// Wraps `HashMap<usize, TermExpr>` with convenience methods for
/// composition, domain queries, and display.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution {
    /// The underlying variable-to-term bindings.
    pub bindings: HashMap<usize, TermExpr>,
}

impl Substitution {
    /// Create an empty substitution (identity).
    pub fn empty() -> Self {
        Substitution {
            bindings: HashMap::new(),
        }
    }

    /// Create a substitution from a map of bindings.
    pub fn from_bindings(bindings: HashMap<usize, TermExpr>) -> Self {
        Substitution { bindings }
    }

    /// Check if this substitution is empty (identity).
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Return the number of bindings.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Look up the binding for a variable.
    pub fn get(&self, var: usize) -> Option<&TermExpr> {
        self.bindings.get(&var)
    }

    /// Apply this substitution to a term.
    pub fn apply(&self, term: &TermExpr) -> TermExpr {
        term.apply_substitution(&self.bindings)
    }

    /// Return the domain (set of bound variables).
    pub fn domain(&self) -> HashSet<usize> {
        self.bindings.keys().copied().collect()
    }
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut sorted_bindings: Vec<_> = self.bindings.iter().collect();
        sorted_bindings.sort_by_key(|(k, _)| *k);
        for (i, (var, term)) in sorted_bindings.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "x{} ↦ {}", var, term)?;
        }
        write!(f, "}}")
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Unification store
// ══════════════════════════════════════════════════════════════════════════════

/// Constraint store for the unification theory.
///
/// Maintains the current substitution (solved bindings) and a queue of
/// pending equations awaiting decomposition.
#[derive(Clone, Debug)]
pub struct UnificationStore {
    /// Current substitution (variable → term bindings).
    substitution: HashMap<usize, TermExpr>,
    /// Pending equations awaiting decomposition.
    pending: Vec<UnificationEquation>,
}

impl UnificationStore {
    /// Create an empty store with no bindings and no pending equations.
    pub fn new() -> Self {
        UnificationStore {
            substitution: HashMap::new(),
            pending: Vec::new(),
        }
    }

    /// Return a reference to the current substitution.
    pub fn substitution(&self) -> &HashMap<usize, TermExpr> {
        &self.substitution
    }

    /// Return a reference to the pending equations.
    pub fn pending(&self) -> &[UnificationEquation] {
        &self.pending
    }

    /// Check whether all equations have been solved (no pending equations).
    pub fn is_solved(&self) -> bool {
        self.pending.is_empty()
    }
}

impl Default for UnificationStore {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Unification theory
// ══════════════════════════════════════════════════════════════════════════════

/// Structural unification constraint theory (Martelli & Montanari 1982).
///
/// Implements first-order syntactic unification with occurs check as a
/// [`ConstraintTheory`]. This is a decidable, deterministic theory:
/// propagation alone determines satisfiability, so `label()` returns an
/// empty `LogicStream`.
///
/// # Usage
///
/// ```
/// # use mettail_prattail::unification::*;
/// # use mettail_prattail::logict::ConstraintTheory;
/// let theory = UnificationTheory::new();
/// let store = theory.empty_store();
///
/// // Unify f(x₀, a) ≡ f(b, x₁)
/// let eq = UnificationEquation::new(
///     TermExpr::App {
///         head: "f".into(),
///         args: vec![TermExpr::Var(0), TermExpr::Const("a".into())],
///     },
///     TermExpr::App {
///         head: "f".into(),
///         args: vec![TermExpr::Const("b".into()), TermExpr::Var(1)],
///     },
/// );
///
/// let result = theory.propagate(&store, &eq).expect("should unify");
/// let witness = theory.witness(&result).expect("should have witness");
/// assert_eq!(witness.get(0), Some(&TermExpr::Const("b".into())));
/// assert_eq!(witness.get(1), Some(&TermExpr::Const("a".into())));
/// ```
#[derive(Clone, Debug)]
pub struct UnificationTheory {
    /// Optional signature for well-formedness checking.
    /// Not enforced during unification; available for downstream analysis.
    pub signature: Option<TermSignature>,
}

impl UnificationTheory {
    /// Create a new unification theory without a signature constraint.
    pub fn new() -> Self {
        UnificationTheory { signature: None }
    }

    /// Create a new unification theory with a term signature.
    pub fn with_signature(signature: TermSignature) -> Self {
        UnificationTheory {
            signature: Some(signature),
        }
    }

    /// Run the Martelli-Montanari unification algorithm.
    ///
    /// Takes an initial substitution and a work stack of equations. Processes
    /// equations iteratively (no recursion) until the stack is empty or a
    /// clash/occurs-check failure is detected.
    ///
    /// # Returns
    ///
    /// - `Some(substitution)` if all equations can be unified.
    /// - `None` if unification fails (constructor clash, arity mismatch,
    ///   constant clash, kind clash, or occurs-check failure).
    ///
    /// # Algorithm complexity
    ///
    /// Each equation is processed at most once (modulo decomposition into
    /// sub-equations). The work stack grows by at most `max_arity` entries
    /// per decomposition step. Total work is O(|equations| * max_term_depth).
    fn unify(
        &self,
        mut substitution: HashMap<usize, TermExpr>,
        initial_equations: &[UnificationEquation],
    ) -> Option<HashMap<usize, TermExpr>> {
        // Work stack: pending equations to process.
        let mut work_stack: Vec<(TermExpr, TermExpr)> =
            Vec::with_capacity(initial_equations.len());
        for eq in initial_equations {
            work_stack.push((eq.lhs.clone(), eq.rhs.clone()));
        }

        while let Some((lhs, rhs)) = work_stack.pop() {
            // Apply the current substitution to both sides before matching.
            let s = lhs.apply_substitution(&substitution);
            let t = rhs.apply_substitution(&substitution);

            match (&s, &t) {
                // ── Case 1: Identical variables — trivial, skip ──────────
                (TermExpr::Var(x), TermExpr::Var(y)) if x == y => {
                    continue;
                }

                // ── Case 2: Variable on left — bind after occurs check ───
                (TermExpr::Var(x), _) => {
                    if TermExpr::occurs_in(*x, &t) {
                        // Occurs check failure: x cannot unify with a term
                        // containing x (would create an infinite term).
                        return None;
                    }
                    // Bind x ↦ t in the substitution.
                    // Apply the new binding to all existing bindings to maintain
                    // the substitution in solved form.
                    let new_binding_map: HashMap<usize, TermExpr> =
                        std::iter::once((*x, t.clone())).collect();
                    for value in substitution.values_mut() {
                        *value = value.apply_substitution(&new_binding_map);
                    }
                    substitution.insert(*x, t);
                }

                // ── Case 3: Variable on right — orient and bind ──────────
                (_, TermExpr::Var(y)) => {
                    if TermExpr::occurs_in(*y, &s) {
                        return None;
                    }
                    let new_binding_map: HashMap<usize, TermExpr> =
                        std::iter::once((*y, s.clone())).collect();
                    for value in substitution.values_mut() {
                        *value = value.apply_substitution(&new_binding_map);
                    }
                    substitution.insert(*y, s);
                }

                // ── Case 4: Two Apps with same head — decompose ──────────
                (
                    TermExpr::App {
                        head: head_s,
                        args: args_s,
                    },
                    TermExpr::App {
                        head: head_t,
                        args: args_t,
                    },
                ) => {
                    if head_s != head_t {
                        // Constructor clash: f(...) ≢ g(...)
                        return None;
                    }
                    if args_s.len() != args_t.len() {
                        // Arity mismatch: f(a, b) ≢ f(a)
                        return None;
                    }
                    // Decompose: push each pair of corresponding arguments.
                    for (arg_s, arg_t) in args_s.iter().zip(args_t.iter()) {
                        work_stack.push((arg_s.clone(), arg_t.clone()));
                    }
                }

                // ── Case 5: Identical constants — trivial, skip ──────────
                (TermExpr::Const(a), TermExpr::Const(b)) => {
                    if a != b {
                        // Constant clash: a ≢ b
                        return None;
                    }
                    // Same constant — nothing to do.
                }

                // ── Case 6: Kind clash — Const vs App or App vs Const ────
                (TermExpr::Const(_), TermExpr::App { .. })
                | (TermExpr::App { .. }, TermExpr::Const(_)) => {
                    // A constant cannot unify with a function application.
                    return None;
                }
            }
        }

        Some(substitution)
    }
}

impl Default for UnificationTheory {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// ConstraintTheory implementation
// ══════════════════════════════════════════════════════════════════════════════

impl ConstraintTheory for UnificationTheory {
    type Constraint = UnificationEquation;
    type Assignment = Substitution;
    type Store = UnificationStore;

    /// Create an empty store with no bindings and no pending equations.
    fn empty_store(&self) -> UnificationStore {
        UnificationStore::new()
    }

    /// Add an equation to the store and run Martelli-Montanari propagation.
    ///
    /// Takes the current store's substitution and all pending equations plus the
    /// new constraint, and attempts to unify them all. Returns `None` if the
    /// system of equations is unsatisfiable.
    fn propagate(
        &self,
        store: &UnificationStore,
        constraint: &UnificationEquation,
    ) -> Option<UnificationStore> {
        // Collect all equations: existing pending + the new constraint.
        let mut all_equations: Vec<UnificationEquation> =
            Vec::with_capacity(store.pending.len() + 1);
        all_equations.extend(store.pending.iter().cloned());
        all_equations.push(constraint.clone());

        // Run unification starting from the current substitution.
        let result = self.unify(store.substitution.clone(), &all_equations)?;

        Some(UnificationStore {
            substitution: result,
            // All equations have been processed — pending is empty.
            pending: Vec::new(),
        })
    }

    /// Check whether the store is consistent (no unsatisfiable equations).
    ///
    /// For unification, a store is consistent iff all pending equations can be
    /// solved with the current substitution. Since `propagate` eagerly solves
    /// all equations, a store produced by `propagate` is always consistent
    /// (pending is empty). We verify by re-running unification.
    fn is_consistent(&self, store: &UnificationStore) -> bool {
        if store.pending.is_empty() {
            true
        } else {
            self.unify(store.substitution.clone(), &store.pending)
                .is_some()
        }
    }

    /// Extract a substitution witness from a consistent store.
    ///
    /// Returns the solved substitution if the store is consistent and fully
    /// solved (no pending equations). Returns `None` if there are unsolved
    /// equations remaining.
    fn witness(&self, store: &UnificationStore) -> Option<Substitution> {
        if !store.pending.is_empty() {
            // There are unsolved equations — need further propagation.
            return None;
        }
        Some(Substitution::from_bindings(store.substitution.clone()))
    }

    /// Generate labeling choices for search.
    ///
    /// Unification is a decidable, deterministic theory: propagation alone
    /// determines satisfiability. No search choices are needed, so this
    /// always returns an empty stream.
    fn label(&self, _store: &UnificationStore) -> LogicStream<UnificationEquation> {
        LogicStream::empty()
    }

    /// Evaluate whether an equation is satisfied under a given substitution.
    ///
    /// Applies the substitution to both sides and checks structural equality.
    fn evaluate(
        &self,
        constraint: &UnificationEquation,
        assignment: &Substitution,
    ) -> bool {
        let lhs_applied = constraint.lhs.apply_substitution(&assignment.bindings);
        let rhs_applied = constraint.rhs.apply_substitution(&assignment.bindings);
        lhs_applied == rhs_applied
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis result
// ══════════════════════════════════════════════════════════════════════════════

/// Analysis result from structural unification guard checking.
#[derive(Debug, Clone, Default)]
pub struct UnificationAnalysis {
    /// Guards with unsatisfiable unification (constructor clash / occurs check).
    pub unsatisfiable_guards: Vec<(String, String)>,
    /// Guards with trivially satisfiable unification.
    pub tautological_guards: Vec<(String, String)>,
    /// Guard pairs where one pattern is strictly more general.
    pub subsumed_guards: Vec<(String, String, String)>,
    /// Descriptions of constraints where LogicT search bound was exceeded.
    pub search_bound_exceeded: Vec<String>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Bundle analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Convert a rule's syntax items into a `TermExpr` for unification checking.
///
/// The mapping is:
/// - [`SyntaxItemSpec::Terminal`] → `Const(token_text)`
/// - [`SyntaxItemSpec::IdentCapture`] / [`SyntaxItemSpec::Binder`] → `Var(index)`
///   (indices are assigned by first-seen order via `param_index`)
/// - [`SyntaxItemSpec::NonTerminal`] → `App(category_name, [])`
/// - [`SyntaxItemSpec::Optional`] → `App("optional", [items_to_term(inner)])`
/// - [`SyntaxItemSpec::Collection`] → `App("collection", [App(element_category, [])])`
/// - A sequence of multiple items → `App("seq", [t₁, t₂, ...])`
/// - An empty item list → `Const("ε")`
///
/// The `param_index` map is shared across calls so that the same parameter name
/// always maps to the same variable index within a rule.
fn items_to_term(
    items: &[crate::SyntaxItemSpec],
    param_index: &mut HashMap<String, usize>,
) -> TermExpr {
    if items.is_empty() {
        return TermExpr::Const("ε".into());
    }

    if items.len() == 1 {
        return item_to_term(&items[0], param_index);
    }

    let child_terms: Vec<TermExpr> = items
        .iter()
        .map(|it| item_to_term(it, param_index))
        .collect();
    TermExpr::App {
        head: "seq".into(),
        args: child_terms,
    }
}

/// Convert a single [`SyntaxItemSpec`] to a `TermExpr`.
fn item_to_term(
    item: &crate::SyntaxItemSpec,
    param_index: &mut HashMap<String, usize>,
) -> TermExpr {
    match item {
        crate::SyntaxItemSpec::Terminal(tok) => TermExpr::Const(tok.clone()),

        crate::SyntaxItemSpec::IdentCapture { param_name } => {
            let next = param_index.len();
            let idx = *param_index.entry(param_name.clone()).or_insert(next);
            TermExpr::Var(idx)
        }

        crate::SyntaxItemSpec::Binder { param_name, .. } => {
            let next = param_index.len();
            let idx = *param_index.entry(param_name.clone()).or_insert(next);
            TermExpr::Var(idx)
        }

        crate::SyntaxItemSpec::NonTerminal { category, .. } => TermExpr::App {
            head: category.clone(),
            args: vec![],
        },

        crate::SyntaxItemSpec::Optional { inner } => {
            let inner_term = items_to_term(inner, param_index);
            TermExpr::App {
                head: "optional".into(),
                args: vec![inner_term],
            }
        }

        crate::SyntaxItemSpec::Collection {
            element_category, ..
        } => TermExpr::App {
            head: "collection".into(),
            args: vec![TermExpr::App {
                head: element_category.clone(),
                args: vec![],
            }],
        },

        // For Sep/Map/Zip/BinderCollection we produce an opaque App so they
        // participate in structural unification without special-casing.
        crate::SyntaxItemSpec::Sep { body, .. } => {
            let body_term = item_to_term(body, param_index);
            TermExpr::App {
                head: "sep".into(),
                args: vec![body_term],
            }
        }

        crate::SyntaxItemSpec::Map { body_items } => {
            let child_terms: Vec<TermExpr> = body_items
                .iter()
                .map(|it| item_to_term(it, param_index))
                .collect();
            TermExpr::App {
                head: "map".into(),
                args: child_terms,
            }
        }

        crate::SyntaxItemSpec::Zip {
            left_category,
            right_category,
            ..
        } => TermExpr::App {
            head: "zip".into(),
            args: vec![
                TermExpr::App {
                    head: left_category.clone(),
                    args: vec![],
                },
                TermExpr::App {
                    head: right_category.clone(),
                    args: vec![],
                },
            ],
        },

        crate::SyntaxItemSpec::BinderCollection { .. } => TermExpr::App {
            head: "binder_collection".into(),
            args: vec![],
        },
    }
}

/// Check whether a term is *tautological* — i.e., it consists only of
/// variables (no constants or ground constructors), meaning any input
/// satisfies it.
fn is_tautological(term: &TermExpr) -> bool {
    match term {
        TermExpr::Var(_) => true,
        TermExpr::Const(_) => false,
        TermExpr::App { args, .. } => {
            // Pure-variable App: all args must themselves be tautological.
            !args.is_empty() && args.iter().all(is_tautological)
        }
    }
}

/// Check whether a term is *satisfiable* — whether any ground instantiation
/// can match it. For first-order syntactic unification every term (even a
/// variable) is satisfiable; a wildcard (pure-variable) term is always
/// satisfiable.
///
/// Returns `false` only for structurally empty patterns that were generated
/// from an item list that has no terminals, non-terminals, or variables at
/// all (which in practice never arises, but is encoded as `Const("ε")`
/// with the intent that the *caller* checks for the sentinel).
///
/// Because `TermExpr::Var` unifies with anything, every term is trivially
/// satisfiable in syntactic unification; we keep the predicate for
/// completeness and symmetry with the tautology check.
fn is_satisfiable(term: &TermExpr) -> bool {
    // In first-order syntactic unification every well-formed term is
    // satisfiable (variables unify with anything).
    let _ = term;
    true
}

/// Check whether pattern `general` subsumes `specific` — i.e., every
/// input that matches `specific` also matches `general` but not vice-versa.
///
/// In syntactic unification, `general` subsumes `specific` iff `general`
/// unifies with `specific` AND after that unification `general` is
/// strictly more general (has free variables that `specific` does not).
///
/// Concretely: `general` subsumes `specific` when the unifier maps
/// only variables from `general` to ground terms (or sub-terms of
/// `specific`), while `specific` is ground (or at least no variable from
/// `specific` is left free).
fn subsumes(general: &TermExpr, specific: &TermExpr) -> bool {
    let theory = UnificationTheory::new();
    let store = theory.empty_store();
    let eq = UnificationEquation::new(general.clone(), specific.clone());
    match theory.propagate(&store, &eq) {
        None => false, // patterns are disjoint, no subsumption
        Some(_unified_store) => {
            // general subsumes specific when general has strictly more
            // unbound variables than specific.
            let gen_vars = general.variables();
            let spec_vars = specific.variables();
            // Check that general has variables not present in specific.
            gen_vars.len() > spec_vars.len()
                || gen_vars.iter().any(|v| !spec_vars.contains(v))
        }
    }
}

/// Walk a grammar bundle and perform structural unification checks on
/// same-category rules.
///
/// For each rule the function:
/// 1. Converts the rule's syntax items to a `TermExpr` via [`items_to_term`].
/// 2. Checks satisfiability (every term is satisfiable in first-order
///    unification, so wildcard/variable-only patterns are flagged as
///    tautological instead).
/// 3. Checks tautology: a pattern consisting purely of variables matches
///    any input unconditionally.
///
/// For each *pair* of rules in the same category it:
/// 1. Attempts unification — if it fails the patterns are structurally
///    disjoint (logged at info level, not reported as unsatisfiable).
/// 2. Checks subsumption — if one pattern is strictly more general than
///    the other, it is recorded in `subsumed_guards`.
///
/// The `search_bound_exceeded` field is always empty for the unification
/// theory (which is decidable and uses no labelling search), but is
/// included for interface consistency.
///
/// # Parameters
///
/// - `all_syntax` — triples of `(rule_label, category, items)` from the
///   grammar bundle.
///
/// # Returns
///
/// A [`UnificationAnalysis`] populated with the findings above.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> UnificationAnalysis {
    if all_syntax.is_empty() {
        return UnificationAnalysis::default();
    }

    let mut unsatisfiable_guards: Vec<(String, String)> = Vec::new();
    let mut tautological_guards: Vec<(String, String)> = Vec::new();
    let mut subsumed_guards: Vec<(String, String, String)> = Vec::new();
    // The unification theory is decidable; no LogicT search is performed.
    let search_bound_exceeded: Vec<String> = Vec::new();

    // ── Phase 1: Convert each rule to a TermExpr ─────────────────────────

    // (qualified_label, category, term, param_index_map)
    let mut rule_terms: Vec<(String, String, TermExpr)> =
        Vec::with_capacity(all_syntax.len());

    for (label, cat, items) in all_syntax {
        let qualified = format!("{}::{}", cat, label);
        let mut param_index: HashMap<String, usize> = HashMap::new();
        let term = items_to_term(items, &mut param_index);
        rule_terms.push((qualified, cat.clone(), term));
    }

    // ── Phase 2: Per-rule satisfiability and tautology checks ────────────

    let theory = UnificationTheory::new();

    for (qualified, cat, term) in &rule_terms {
        // Satisfiability: in first-order unification every term is
        // satisfiable (variables unify with anything). We keep the check for
        // symmetry; no rule is ever flagged unsatisfiable here.
        if !is_satisfiable(term) {
            unsatisfiable_guards.push((qualified.clone(), cat.clone()));
        }

        // Tautology: a pattern that is purely variables (wildcards) matches
        // every input unconditionally.
        if is_tautological(term) {
            tautological_guards.push((qualified.clone(), cat.clone()));
        }
    }

    // ── Phase 3: Pairwise unification and subsumption within a category ──

    for i in 0..rule_terms.len() {
        for j in (i + 1)..rule_terms.len() {
            let (ref qual_i, ref cat_i, ref term_i) = rule_terms[i];
            let (ref qual_j, ref cat_j, ref term_j) = rule_terms[j];

            if cat_i != cat_j {
                continue;
            }

            // Rename variables in term_j so they don't clash with term_i.
            // We shift j's variable indices by a large offset.
            let offset = term_i.variables().len() + 1;
            let term_j_renamed = rename_vars(term_j, offset);

            let store = theory.empty_store();
            let eq = UnificationEquation::new(term_i.clone(), term_j_renamed.clone());

            match theory.propagate(&store, &eq) {
                None => {
                    // Patterns are structurally disjoint — not reported as
                    // unsatisfiable because disjoint patterns are a normal and
                    // expected outcome in well-structured grammars.
                    // (No action needed.)
                }
                Some(_unified_store) => {
                    // Patterns can unify — check subsumption.
                    if subsumes(term_i, term_j) {
                        subsumed_guards.push((
                            qual_i.clone(),
                            qual_j.clone(),
                            format!(
                                "'{}' is more general than '{}'",
                                qual_i, qual_j
                            ),
                        ));
                    } else if subsumes(term_j, term_i) {
                        subsumed_guards.push((
                            qual_j.clone(),
                            qual_i.clone(),
                            format!(
                                "'{}' is more general than '{}'",
                                qual_j, qual_i
                            ),
                        ));
                    }
                }
            }
        }
    }

    UnificationAnalysis {
        unsatisfiable_guards,
        tautological_guards,
        subsumed_guards,
        search_bound_exceeded,
    }
}

/// Shift all variable indices in `term` by `offset`.
///
/// Used to alpha-rename a term so its variables do not clash with those
/// from another term before attempting unification.
fn rename_vars(term: &TermExpr, offset: usize) -> TermExpr {
    match term {
        TermExpr::Var(idx) => TermExpr::Var(idx + offset),
        TermExpr::Const(_) => term.clone(),
        TermExpr::App { head, args } => TermExpr::App {
            head: head.clone(),
            args: args.iter().map(|a| rename_vars(a, offset)).collect(),
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logict::ConstraintTheory;

    // ── Helper constructors ──────────────────────────────────────────────

    fn var(idx: usize) -> TermExpr {
        TermExpr::Var(idx)
    }

    fn constant(name: &str) -> TermExpr {
        TermExpr::Const(name.into())
    }

    fn app(head: &str, args: Vec<TermExpr>) -> TermExpr {
        TermExpr::App {
            head: head.into(),
            args,
        }
    }

    fn eq(lhs: TermExpr, rhs: TermExpr) -> UnificationEquation {
        UnificationEquation::new(lhs, rhs)
    }

    // ── TermExpr helper method tests ─────────────────────────────────────

    #[test]
    fn variables_of_var() {
        let t = var(3);
        let vars = t.variables();
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&3));
    }

    #[test]
    fn variables_of_const() {
        let t = constant("a");
        let vars = t.variables();
        assert!(vars.is_empty());
    }

    #[test]
    fn variables_of_app() {
        let t = app("f", vec![var(0), constant("a"), var(1), var(0)]);
        let vars = t.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&0));
        assert!(vars.contains(&1));
    }

    #[test]
    fn variables_of_nested_app() {
        let t = app("f", vec![app("g", vec![var(2)]), var(3)]);
        let vars = t.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&2));
        assert!(vars.contains(&3));
    }

    #[test]
    fn occurs_in_direct() {
        assert!(TermExpr::occurs_in(0, &var(0)));
    }

    #[test]
    fn occurs_in_not_found() {
        assert!(!TermExpr::occurs_in(0, &var(1)));
        assert!(!TermExpr::occurs_in(0, &constant("a")));
    }

    #[test]
    fn occurs_in_nested() {
        let t = app("f", vec![app("g", vec![var(0)]), constant("a")]);
        assert!(TermExpr::occurs_in(0, &t));
        assert!(!TermExpr::occurs_in(1, &t));
    }

    #[test]
    fn apply_substitution_var_bound() {
        let mut subst = HashMap::new();
        subst.insert(0, constant("a"));
        let result = var(0).apply_substitution(&subst);
        assert_eq!(result, constant("a"));
    }

    #[test]
    fn apply_substitution_var_unbound() {
        let subst = HashMap::new();
        let result = var(0).apply_substitution(&subst);
        assert_eq!(result, var(0));
    }

    #[test]
    fn apply_substitution_const_unchanged() {
        let mut subst = HashMap::new();
        subst.insert(0, constant("b"));
        let result = constant("a").apply_substitution(&subst);
        assert_eq!(result, constant("a"));
    }

    #[test]
    fn apply_substitution_app_recursive() {
        let mut subst = HashMap::new();
        subst.insert(0, constant("a"));
        subst.insert(1, constant("b"));
        let t = app("f", vec![var(0), var(1)]);
        let result = t.apply_substitution(&subst);
        assert_eq!(result, app("f", vec![constant("a"), constant("b")]));
    }

    #[test]
    fn apply_substitution_transitive() {
        // x₀ ↦ x₁, x₁ ↦ a — applying to x₀ should yield a
        let mut subst = HashMap::new();
        subst.insert(0, var(1));
        subst.insert(1, constant("a"));
        let result = var(0).apply_substitution(&subst);
        assert_eq!(result, constant("a"));
    }

    // ── Display tests ────────────────────────────────────────────────────

    #[test]
    fn display_var() {
        assert_eq!(format!("{}", var(0)), "x0");
    }

    #[test]
    fn display_const() {
        assert_eq!(format!("{}", constant("a")), "a");
    }

    #[test]
    fn display_app() {
        let t = app("f", vec![var(0), constant("a")]);
        assert_eq!(format!("{}", t), "f(x0, a)");
    }

    #[test]
    fn display_equation() {
        let e = eq(var(0), constant("a"));
        assert_eq!(format!("{}", e), "x0 ≡ a");
    }

    #[test]
    fn display_substitution() {
        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        bindings.insert(1, constant("b"));
        let subst = Substitution::from_bindings(bindings);
        assert_eq!(format!("{}", subst), "{x0 ↦ a, x1 ↦ b}");
    }

    // ── TermSignature tests ──────────────────────────────────────────────

    #[test]
    fn signature_well_formed() {
        let mut sig = TermSignature::new();
        sig.add_constructor("f", 2);
        sig.add_constructor("g", 1);

        assert!(sig.is_well_formed(&var(0)));
        assert!(sig.is_well_formed(&constant("a")));
        assert!(sig.is_well_formed(&app("f", vec![var(0), constant("a")])));
        assert!(sig.is_well_formed(&app("g", vec![var(0)])));
    }

    #[test]
    fn signature_arity_mismatch() {
        let mut sig = TermSignature::new();
        sig.add_constructor("f", 2);

        // f has arity 2, but we give 1 argument — ill-formed
        assert!(!sig.is_well_formed(&app("f", vec![var(0)])));
        // f has arity 2, but we give 3 arguments — ill-formed
        assert!(!sig.is_well_formed(&app("f", vec![var(0), var(1), var(2)])));
    }

    // ── Substitution tests ───────────────────────────────────────────────

    #[test]
    fn substitution_empty() {
        let subst = Substitution::empty();
        assert!(subst.is_empty());
        assert_eq!(subst.len(), 0);
        assert!(subst.domain().is_empty());
    }

    #[test]
    fn substitution_from_bindings() {
        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        bindings.insert(1, constant("b"));
        let subst = Substitution::from_bindings(bindings);
        assert!(!subst.is_empty());
        assert_eq!(subst.len(), 2);
        assert_eq!(subst.get(0), Some(&constant("a")));
        assert_eq!(subst.get(1), Some(&constant("b")));
        assert_eq!(subst.get(2), None);
    }

    #[test]
    fn substitution_apply() {
        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        let subst = Substitution::from_bindings(bindings);
        let result = subst.apply(&app("f", vec![var(0), var(1)]));
        assert_eq!(result, app("f", vec![constant("a"), var(1)]));
    }

    #[test]
    fn substitution_domain() {
        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        bindings.insert(3, constant("b"));
        let subst = Substitution::from_bindings(bindings);
        let domain = subst.domain();
        assert_eq!(domain.len(), 2);
        assert!(domain.contains(&0));
        assert!(domain.contains(&3));
    }

    // ── Core unification tests ───────────────────────────────────────────

    #[test]
    fn simple_unification() {
        // f(x₀, a) ≡ f(b, x₁) → {x₀ ↦ b, x₁ ↦ a}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![var(0), constant("a")]),
            app("f", vec![constant("b"), var(1)]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("b")));
        assert_eq!(witness.get(1), Some(&constant("a")));
    }

    #[test]
    fn occurs_check_failure() {
        // x₀ ≡ f(x₀) → unsatisfiable (infinite term)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(var(0), app("f", vec![var(0)]));

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "occurs check should fail"
        );
    }

    #[test]
    fn constructor_clash() {
        // f(a) ≡ g(a) → unsatisfiable (different constructors)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![constant("a")]),
            app("g", vec![constant("a")]),
        );

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "constructor clash should fail"
        );
    }

    #[test]
    fn const_clash() {
        // a ≡ b → unsatisfiable (different constants)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(constant("a"), constant("b"));

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "constant clash should fail"
        );
    }

    #[test]
    fn identity_unification() {
        // x₀ ≡ x₀ → empty substitution
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(var(0), var(0));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify trivially");
        let witness = theory.witness(&result).expect("should have witness");

        assert!(
            witness.is_empty(),
            "identity unification should produce empty substitution"
        );
    }

    #[test]
    fn nested_unification() {
        // f(g(x₀), a) ≡ f(g(b), a) → {x₀ ↦ b}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![app("g", vec![var(0)]), constant("a")]),
            app("f", vec![app("g", vec![constant("b")]), constant("a")]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("b")));
        assert_eq!(witness.len(), 1);
    }

    #[test]
    fn arity_mismatch_failure() {
        // f(a, b) ≡ f(a) → unsatisfiable (different arities)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![constant("a"), constant("b")]),
            app("f", vec![constant("a")]),
        );

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "arity mismatch should fail"
        );
    }

    #[test]
    fn const_vs_app_clash() {
        // a ≡ f(b) → unsatisfiable (kind clash)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(constant("a"), app("f", vec![constant("b")]));

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "const vs app should fail"
        );
    }

    #[test]
    fn app_vs_const_clash() {
        // f(b) ≡ a → unsatisfiable (kind clash, reversed)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(app("f", vec![constant("b")]), constant("a"));

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "app vs const should fail"
        );
    }

    #[test]
    fn var_binds_to_app() {
        // x₀ ≡ f(a, b) → {x₀ ↦ f(a, b)}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let rhs = app("f", vec![constant("a"), constant("b")]);
        let equation = eq(var(0), rhs.clone());

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&rhs));
    }

    #[test]
    fn var_binds_to_var() {
        // x₀ ≡ x₁ → {x₀ ↦ x₁} (or {x₁ ↦ x₀})
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(var(0), var(1));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        // One variable should be bound to the other.
        assert_eq!(witness.len(), 1);
        let bound_var = if witness.get(0).is_some() { 0 } else { 1 };
        let target_var = if bound_var == 0 { 1 } else { 0 };
        assert_eq!(witness.get(bound_var), Some(&var(target_var)));
    }

    #[test]
    fn const_identity() {
        // a ≡ a → empty substitution
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(constant("a"), constant("a"));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert!(witness.is_empty());
    }

    // ── Multiple equations via repeated propagation ──────────────────────

    #[test]
    fn multiple_equations_sequential() {
        // Equation 1: f(x₀) ≡ f(a) → x₀ ↦ a
        // Equation 2: g(x₁) ≡ g(x₀) → x₁ ↦ a (via transitivity)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(app("f", vec![var(0)]), app("f", vec![constant("a")]));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(app("g", vec![var(1)]), app("g", vec![var(0)]));
        let store = theory
            .propagate(&store, &eq2)
            .expect("eq2 should unify");

        let witness = theory.witness(&store).expect("should have witness");
        assert_eq!(witness.get(0), Some(&constant("a")));
        assert_eq!(witness.get(1), Some(&constant("a")));
    }

    #[test]
    fn multiple_equations_contradiction() {
        // Equation 1: x₀ ≡ a → x₀ ↦ a
        // Equation 2: x₀ ≡ b → clash (a ≢ b)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(var(0), constant("a"));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(var(0), constant("b"));
        assert!(
            theory.propagate(&store, &eq2).is_none(),
            "should fail: x₀ already bound to a, cannot bind to b"
        );
    }

    #[test]
    fn multiple_equations_consistent_rebinding() {
        // Equation 1: x₀ ≡ a → x₀ ↦ a
        // Equation 2: x₀ ≡ a → consistent (a ≡ a)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(var(0), constant("a"));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(var(0), constant("a"));
        let store = theory
            .propagate(&store, &eq2)
            .expect("eq2 should unify (consistent rebinding)");

        let witness = theory.witness(&store).expect("should have witness");
        assert_eq!(witness.get(0), Some(&constant("a")));
    }

    // ── Deeply nested terms ──────────────────────────────────────────────

    #[test]
    fn deeply_nested_unification() {
        // f(g(h(x₀))) ≡ f(g(h(a))) → {x₀ ↦ a}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![app("g", vec![app("h", vec![var(0)])])]),
            app("f", vec![app("g", vec![app("h", vec![constant("a")])])]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
    }

    #[test]
    fn deeply_nested_occurs_check() {
        // x₀ ≡ f(g(h(x₀))) → unsatisfiable
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            var(0),
            app("f", vec![app("g", vec![app("h", vec![var(0)])])]),
        );

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "deeply nested occurs check should fail"
        );
    }

    // ── Multiple variables ───────────────────────────────────────────────

    #[test]
    fn three_variable_unification() {
        // f(x₀, x₁, x₂) ≡ f(a, b, c) → {x₀ ↦ a, x₁ ↦ b, x₂ ↦ c}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![var(0), var(1), var(2)]),
            app("f", vec![constant("a"), constant("b"), constant("c")]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
        assert_eq!(witness.get(1), Some(&constant("b")));
        assert_eq!(witness.get(2), Some(&constant("c")));
    }

    #[test]
    fn shared_variable_unification() {
        // f(x₀, x₀) ≡ f(a, a) → {x₀ ↦ a}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![var(0), var(0)]),
            app("f", vec![constant("a"), constant("a")]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
    }

    #[test]
    fn shared_variable_clash() {
        // f(x₀, x₀) ≡ f(a, b) → unsatisfiable (x₀ cannot be both a and b)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![var(0), var(0)]),
            app("f", vec![constant("a"), constant("b")]),
        );

        assert!(
            theory.propagate(&store, &equation).is_none(),
            "shared variable with different bindings should fail"
        );
    }

    // ── Witness extraction and evaluation ────────────────────────────────

    #[test]
    fn witness_extraction() {
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app("f", vec![var(0), var(1)]),
            app("f", vec![constant("a"), constant("b")]),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        // Verify witness structure
        assert_eq!(witness.len(), 2);
        assert!(witness.domain().contains(&0));
        assert!(witness.domain().contains(&1));
    }

    #[test]
    fn witness_from_empty_store() {
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let witness = theory.witness(&store).expect("empty store has empty witness");
        assert!(witness.is_empty());
    }

    #[test]
    fn evaluate_satisfied_equation() {
        let theory = UnificationTheory::new();

        let equation = eq(
            app("f", vec![var(0), constant("a")]),
            app("f", vec![constant("b"), var(1)]),
        );

        let mut bindings = HashMap::new();
        bindings.insert(0, constant("b"));
        bindings.insert(1, constant("a"));
        let assignment = Substitution::from_bindings(bindings);

        assert!(
            theory.evaluate(&equation, &assignment),
            "equation should be satisfied under the correct substitution"
        );
    }

    #[test]
    fn evaluate_unsatisfied_equation() {
        let theory = UnificationTheory::new();

        let equation = eq(
            app("f", vec![var(0), constant("a")]),
            app("f", vec![constant("b"), var(1)]),
        );

        // Wrong substitution: x₀ ↦ a (should be b)
        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        bindings.insert(1, constant("a"));
        let assignment = Substitution::from_bindings(bindings);

        assert!(
            !theory.evaluate(&equation, &assignment),
            "equation should not be satisfied under wrong substitution"
        );
    }

    #[test]
    fn evaluate_with_partial_substitution() {
        let theory = UnificationTheory::new();

        // x₀ ≡ a: only needs x₀ ↦ a
        let equation = eq(var(0), constant("a"));

        let mut bindings = HashMap::new();
        bindings.insert(0, constant("a"));
        let assignment = Substitution::from_bindings(bindings);

        assert!(theory.evaluate(&equation, &assignment));
    }

    // ── is_consistent tests ──────────────────────────────────────────────

    #[test]
    fn empty_store_is_consistent() {
        let theory = UnificationTheory::new();
        let store = theory.empty_store();
        assert!(theory.is_consistent(&store));
    }

    #[test]
    fn solved_store_is_consistent() {
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(var(0), constant("a"));
        let store = theory
            .propagate(&store, &equation)
            .expect("should unify");

        assert!(theory.is_consistent(&store));
    }

    // ── label tests ──────────────────────────────────────────────────────

    #[test]
    fn label_returns_empty_stream() {
        // Unification is decidable and deterministic: no search needed.
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let stream = theory.label(&store);
        assert!(
            stream.is_empty(),
            "label should return empty stream for decidable theory"
        );
    }

    // ── Variable chain unification ───────────────────────────────────────

    #[test]
    fn variable_chain() {
        // x₀ ≡ x₁, x₁ ≡ x₂, x₂ ≡ a → all map to a
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(var(0), var(1));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(var(1), var(2));
        let store = theory
            .propagate(&store, &eq2)
            .expect("eq2 should unify");

        let eq3 = eq(var(2), constant("a"));
        let store = theory
            .propagate(&store, &eq3)
            .expect("eq3 should unify");

        let witness = theory.witness(&store).expect("should have witness");

        // All three variables should resolve to "a"
        assert_eq!(witness.apply(&var(0)), constant("a"));
        assert_eq!(witness.apply(&var(1)), constant("a"));
        assert_eq!(witness.apply(&var(2)), constant("a"));
    }

    // ── Nullary constructor ──────────────────────────────────────────────

    #[test]
    fn nullary_constructor_unification() {
        // nil() ≡ nil() → empty substitution
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(app("nil", vec![]), app("nil", vec![]));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert!(witness.is_empty());
    }

    #[test]
    fn nullary_constructor_clash() {
        // nil() ≡ cons() → unsatisfiable
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(app("nil", vec![]), app("cons", vec![]));

        assert!(theory.propagate(&store, &equation).is_none());
    }

    // ── Complex term structures ──────────────────────────────────────────

    #[test]
    fn list_cons_unification() {
        // cons(x₀, cons(x₁, nil())) ≡ cons(a, cons(b, nil()))
        // → {x₀ ↦ a, x₁ ↦ b}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let nil = app("nil", vec![]);
        let equation = eq(
            app("cons", vec![var(0), app("cons", vec![var(1), nil.clone()])]),
            app(
                "cons",
                vec![
                    constant("a"),
                    app("cons", vec![constant("b"), nil]),
                ],
            ),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
        assert_eq!(witness.get(1), Some(&constant("b")));
    }

    #[test]
    fn pair_of_pairs() {
        // pair(pair(x₀, x₁), pair(x₂, x₃)) ≡ pair(pair(a, b), pair(c, d))
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(
            app(
                "pair",
                vec![
                    app("pair", vec![var(0), var(1)]),
                    app("pair", vec![var(2), var(3)]),
                ],
            ),
            app(
                "pair",
                vec![
                    app("pair", vec![constant("a"), constant("b")]),
                    app("pair", vec![constant("c"), constant("d")]),
                ],
            ),
        );

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
        assert_eq!(witness.get(1), Some(&constant("b")));
        assert_eq!(witness.get(2), Some(&constant("c")));
        assert_eq!(witness.get(3), Some(&constant("d")));
    }

    // ── Symmetry tests ──────────────────────────────────────────────────

    #[test]
    fn unification_is_symmetric_for_vars() {
        // f(a) ≡ f(x₀) should yield the same result as f(x₀) ≡ f(a)
        let theory = UnificationTheory::new();

        let eq1 = eq(
            app("f", vec![constant("a")]),
            app("f", vec![var(0)]),
        );
        let eq2 = eq(
            app("f", vec![var(0)]),
            app("f", vec![constant("a")]),
        );

        let store = theory.empty_store();
        let r1 = theory.propagate(&store, &eq1).expect("eq1 should unify");
        let w1 = theory.witness(&r1).expect("should have witness");

        let store = theory.empty_store();
        let r2 = theory.propagate(&store, &eq2).expect("eq2 should unify");
        let w2 = theory.witness(&r2).expect("should have witness");

        // Both should bind x₀ ↦ a
        assert_eq!(w1.get(0), Some(&constant("a")));
        assert_eq!(w2.get(0), Some(&constant("a")));
    }

    // ── with_signature constructor ──────────────────────────────────────

    #[test]
    fn theory_with_signature() {
        let mut sig = TermSignature::new();
        sig.add_constructor("f", 2);

        let theory = UnificationTheory::with_signature(sig);
        assert!(theory.signature.is_some());
        let sig = theory.signature.as_ref().expect("signature should exist");
        assert_eq!(sig.constructors.get("f"), Some(&2));
    }

    // ── Edge cases ──────────────────────────────────────────────────────

    #[test]
    fn variable_unifies_with_const() {
        // x₀ ≡ a → {x₀ ↦ a}
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(var(0), constant("a"));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
    }

    #[test]
    fn const_unifies_with_variable() {
        // a ≡ x₀ → {x₀ ↦ a} (orient: variable goes to left)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let equation = eq(constant("a"), var(0));

        let result = theory
            .propagate(&store, &equation)
            .expect("should unify");
        let witness = theory.witness(&result).expect("should have witness");

        assert_eq!(witness.get(0), Some(&constant("a")));
    }

    #[test]
    fn transitive_var_binding() {
        // x₀ ≡ x₁, then x₁ ≡ f(a)
        // Should yield x₀ ↦ f(a), x₁ ↦ f(a) (via transitive closure)
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(var(0), var(1));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(var(1), app("f", vec![constant("a")]));
        let store = theory
            .propagate(&store, &eq2)
            .expect("eq2 should unify");

        let witness = theory.witness(&store).expect("should have witness");

        // Both should resolve to f(a)
        assert_eq!(
            witness.apply(&var(0)),
            app("f", vec![constant("a")])
        );
        assert_eq!(
            witness.apply(&var(1)),
            app("f", vec![constant("a")])
        );
    }

    #[test]
    fn occurs_check_through_transitive_binding() {
        // x₀ ≡ x₁, then x₁ ≡ f(x₀) → occurs check failure
        let theory = UnificationTheory::new();
        let store = theory.empty_store();

        let eq1 = eq(var(0), var(1));
        let store = theory
            .propagate(&store, &eq1)
            .expect("eq1 should unify");

        let eq2 = eq(var(1), app("f", vec![var(0)]));
        assert!(
            theory.propagate(&store, &eq2).is_none(),
            "transitive occurs check should fail"
        );
    }

    // ── Default trait implementations ────────────────────────────────────

    #[test]
    fn default_theory() {
        let theory: UnificationTheory = Default::default();
        assert!(theory.signature.is_none());
    }

    #[test]
    fn default_store() {
        let store: UnificationStore = Default::default();
        assert!(store.is_solved());
        assert!(store.substitution().is_empty());
        assert!(store.pending().is_empty());
    }

    #[test]
    fn default_signature() {
        let sig: TermSignature = Default::default();
        assert!(sig.constructors.is_empty());
    }

    // ── UnificationAnalysis ─────────────────────────────────────────────

    #[test]
    fn analysis_default_is_empty() {
        let analysis = UnificationAnalysis::default();
        assert!(analysis.unsatisfiable_guards.is_empty());
        assert!(analysis.tautological_guards.is_empty());
        assert!(analysis.subsumed_guards.is_empty());
        assert!(analysis.search_bound_exceeded.is_empty());
    }

    // ── analyze_from_bundle tests ────────────────────────────────────────

    /// An empty grammar bundle produces the default (all-empty) analysis.
    #[test]
    fn test_analyze_from_bundle_no_patterns() {
        let bundle: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = Vec::new();
        let analysis = analyze_from_bundle(&bundle);
        assert!(
            analysis.unsatisfiable_guards.is_empty(),
            "empty bundle: no unsatisfiable guards"
        );
        assert!(
            analysis.tautological_guards.is_empty(),
            "empty bundle: no tautological guards"
        );
        assert!(
            analysis.subsumed_guards.is_empty(),
            "empty bundle: no subsumed guards"
        );
        assert!(
            analysis.search_bound_exceeded.is_empty(),
            "empty bundle: search_bound_exceeded always empty for unification"
        );
    }

    /// Two rules in the same category whose leading terminals are different
    /// constants clash under unification — their patterns are disjoint.
    /// The analysis does NOT flag them as `unsatisfiable_guards`; it merely
    /// logs them at info level.  Neither rule is tautological (they have
    /// a leading `Terminal`), and neither subsumes the other.
    #[test]
    fn test_analyze_from_bundle_constructor_clash() {
        // Rule "A" in category "Expr": Terminal("foo") ...
        // Rule "B" in category "Expr": Terminal("bar") ...
        // "foo" ≢ "bar" → disjoint patterns (not subsumed, not tautological).
        let bundle = vec![
            (
                "A".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("foo".to_string())],
            ),
            (
                "B".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("bar".to_string())],
            ),
        ];
        let analysis = analyze_from_bundle(&bundle);
        // Disjoint patterns are *not* reported as unsatisfiable.
        assert!(
            analysis.unsatisfiable_guards.is_empty(),
            "disjoint terminal patterns should not be unsatisfiable"
        );
        // Leading-terminal rules are not tautological.
        assert!(
            analysis.tautological_guards.is_empty(),
            "leading-terminal rules should not be tautological"
        );
        // No subsumption between two disjoint patterns.
        assert!(
            analysis.subsumed_guards.is_empty(),
            "disjoint patterns should not produce subsumption"
        );
        assert!(analysis.search_bound_exceeded.is_empty());
    }

    /// When one rule has a variable-only pattern (wildcard) and another has
    /// a concrete terminal, the wildcard rule subsumes the concrete rule.
    #[test]
    fn test_analyze_from_bundle_subsumption() {
        // Rule "Wild" in category "Expr": IdentCapture { param_name: "x" }
        //   → Var(0)  — matches anything
        // Rule "Lit" in category "Expr": Terminal("lit")
        //   → Const("lit")  — matches only "lit"
        // Wild subsumes Lit: Var(0) unifies with Const("lit"), and Wild has
        // a free variable that Lit does not.
        let bundle = vec![
            (
                "Wild".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::IdentCapture {
                    param_name: "x".to_string(),
                }],
            ),
            (
                "Lit".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("lit".to_string())],
            ),
        ];
        let analysis = analyze_from_bundle(&bundle);
        assert!(
            !analysis.subsumed_guards.is_empty(),
            "wildcard rule should subsume the concrete terminal rule"
        );
        // The subsumed entry should name "Wild" as the more-general rule.
        let found = analysis
            .subsumed_guards
            .iter()
            .any(|(gen, _spec, _desc)| gen.contains("Wild"));
        assert!(found, "subsumed_guards should report Wild as the more general rule");
        // "Wild" is tautological (pure variable pattern).
        assert!(
            !analysis.tautological_guards.is_empty(),
            "the wildcard rule should be flagged as tautological"
        );
        let taut = analysis
            .tautological_guards
            .iter()
            .any(|(q, _)| q.contains("Wild"));
        assert!(taut, "Wild should appear in tautological_guards");
    }

    /// A rule whose entire pattern consists of variables (IdentCapture items)
    /// is tautological — it matches any input unconditionally.
    #[test]
    fn test_analyze_from_bundle_tautological() {
        // Rule "AllVar" in category "Stmt":
        //   IdentCapture("a"), IdentCapture("b")  → seq(Var(0), Var(1))
        // Both items are wildcards — the pattern is tautological.
        let bundle = vec![(
            "AllVar".to_string(),
            "Stmt".to_string(),
            vec![
                crate::SyntaxItemSpec::IdentCapture {
                    param_name: "a".to_string(),
                },
                crate::SyntaxItemSpec::IdentCapture {
                    param_name: "b".to_string(),
                },
            ],
        )];
        let analysis = analyze_from_bundle(&bundle);
        assert!(
            !analysis.tautological_guards.is_empty(),
            "all-variable pattern should be flagged as tautological"
        );
        let taut = analysis
            .tautological_guards
            .iter()
            .any(|(q, _)| q.contains("AllVar"));
        assert!(taut, "AllVar should appear in tautological_guards");
        // No subsumption with only one rule.
        assert!(
            analysis.subsumed_guards.is_empty(),
            "single rule: no subsumption possible"
        );
        assert!(analysis.search_bound_exceeded.is_empty());
    }
}
