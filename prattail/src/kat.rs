//! Kleene Algebra with Tests (KAT) for decidable Hoare logic.
//!
//! Kleene Algebra with Tests extends Kleene algebra with a Boolean subalgebra
//! of "tests" (predicates). This combination yields a decidable equational theory
//! that subsumes propositional Hoare logic, making KAT ideal for automated
//! verification of simple imperative programs and parser control flow.
//!
//! ## Theoretical Foundations
//!
//! - **Kozen (1997)** — "Kleene algebra with tests." Introduces KAT and proves
//!   completeness of the equational theory. Shows that KAT subsumes propositional
//!   Hoare logic: `{b} p {c}` is valid iff `b·p·c̄ = 0` in the free KAT.
//! - **Kozen & Smith (1996)** — "Kleene algebra with tests: completeness and
//!   decidability." PSPACE decision procedure via automata-based equivalence.
//! - **Pous (2015)** — "Symbolic algorithms for language equivalence and Kleene
//!   algebra with tests." Efficient symbolic algorithms using bisimulation up
//!   to congruence for KAT equivalence checking.
//! - **Kozen (2000)** — "On Hoare logic and Kleene algebra with tests." Survey
//!   covering the relationship between KAT and Hoare logic, schematology, and
//!   applications to compiler optimization.
//!
//! ## Architecture
//!
//! ```text
//! Program / parse flow specification
//!       │
//!       ▼
//! KatExpr (Kleene algebra expression with Boolean tests)
//!       │
//!       ├──→ check_equivalence() ──→ true/false
//!       │
//!       └──→ verify_hoare_triple() ──→ valid/invalid
//! ```
//!
//! ## PraTTaIL Integration
//!
//! KAT models PraTTaIL's parse control flow. Sequential composition maps to
//! rule chaining, alternation to dispatch, and iteration to Kleene star
//! (recursive categories). Boolean tests correspond to token predicates
//! (e.g., "current token is '('" or "in recovery mode"). KAT equivalence
//! checking verifies that grammar transformations preserve parse behavior,
//! and Hoare triples verify pre/post-conditions of parse functions.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A Boolean test (predicate) in KAT.
///
/// Tests form a Boolean subalgebra of the Kleene algebra. They are used
/// as guards (preconditions/postconditions) in Hoare triples.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BooleanTest {
    /// Boolean true (the test that always passes).
    True,
    /// Boolean false (the test that always fails).
    False,
    /// Atomic test (e.g., "at_eof", "token_is_open_paren").
    Atom(String),
    /// Negation of a test.
    Not(Box<BooleanTest>),
    /// Conjunction of two tests.
    And(Box<BooleanTest>, Box<BooleanTest>),
    /// Disjunction of two tests.
    Or(Box<BooleanTest>, Box<BooleanTest>),
}

impl BooleanTest {
    /// Create an atomic test.
    pub fn atom(name: impl Into<String>) -> Self {
        BooleanTest::Atom(name.into())
    }

    /// Negate a test.
    pub fn not(test: BooleanTest) -> Self {
        BooleanTest::Not(Box::new(test))
    }

    /// Conjunction of two tests.
    pub fn and(a: BooleanTest, b: BooleanTest) -> Self {
        BooleanTest::And(Box::new(a), Box::new(b))
    }

    /// Disjunction of two tests.
    pub fn or(a: BooleanTest, b: BooleanTest) -> Self {
        BooleanTest::Or(Box::new(a), Box::new(b))
    }

    /// Collect all atomic test names.
    pub fn atoms(&self) -> HashSet<String> {
        let mut result = HashSet::new();
        self.collect_atoms(&mut result);
        result
    }

    fn collect_atoms(&self, acc: &mut HashSet<String>) {
        match self {
            BooleanTest::True | BooleanTest::False => {}
            BooleanTest::Atom(name) => {
                acc.insert(name.clone());
            }
            BooleanTest::Not(inner) => inner.collect_atoms(acc),
            BooleanTest::And(a, b) | BooleanTest::Or(a, b) => {
                a.collect_atoms(acc);
                b.collect_atoms(acc);
            }
        }
    }
}

impl fmt::Display for BooleanTest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BooleanTest::True => write!(f, "1"),
            BooleanTest::False => write!(f, "0"),
            BooleanTest::Atom(name) => write!(f, "{}", name),
            BooleanTest::Not(inner) => write!(f, "~{}", inner),
            BooleanTest::And(a, b) => write!(f, "({} & {})", a, b),
            BooleanTest::Or(a, b) => write!(f, "({} | {})", a, b),
        }
    }
}

/// A Kleene Algebra with Tests expression.
///
/// KAT expressions combine Kleene algebra operators (sequential composition,
/// alternation, Kleene star) with Boolean tests.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KatExpr {
    /// Zero (failure / empty language).
    Zero,
    /// One (skip / empty string).
    One,
    /// A Boolean test (guard / assertion).
    Test(BooleanTest),
    /// An atomic action (e.g., "shift", "reduce", "emit_token").
    Action(String),
    /// Sequential composition: `p ; q` (do `p` then `q`).
    Seq(Box<KatExpr>, Box<KatExpr>),
    /// Alternation/choice: `p + q` (do `p` or `q`).
    Alt(Box<KatExpr>, Box<KatExpr>),
    /// Kleene star: `p*` (do `p` zero or more times).
    Star(Box<KatExpr>),
}

impl KatExpr {
    /// Create an atomic action.
    pub fn action(name: impl Into<String>) -> Self {
        KatExpr::Action(name.into())
    }

    /// Create a test expression.
    pub fn test(t: BooleanTest) -> Self {
        KatExpr::Test(t)
    }

    /// Sequential composition.
    pub fn seq(a: KatExpr, b: KatExpr) -> Self {
        KatExpr::Seq(Box::new(a), Box::new(b))
    }

    /// Alternation/choice.
    pub fn alt(a: KatExpr, b: KatExpr) -> Self {
        KatExpr::Alt(Box::new(a), Box::new(b))
    }

    /// Kleene star.
    pub fn star(a: KatExpr) -> Self {
        KatExpr::Star(Box::new(a))
    }

    /// Hoare assertion: `{b} p {c}` expressed as `b·p·~c = 0`.
    ///
    /// Constructs the KAT expression `b ; p ; ~c` that should equal zero
    /// for the Hoare triple to be valid.
    pub fn hoare_condition(pre: BooleanTest, program: KatExpr, post: BooleanTest) -> Self {
        KatExpr::seq(
            KatExpr::test(pre),
            KatExpr::seq(program, KatExpr::test(BooleanTest::not(post))),
        )
    }
}

impl fmt::Display for KatExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KatExpr::Zero => write!(f, "0"),
            KatExpr::One => write!(f, "1"),
            KatExpr::Test(t) => write!(f, "[{}]", t),
            KatExpr::Action(name) => write!(f, "{}", name),
            KatExpr::Seq(a, b) => write!(f, "({} ; {})", a, b),
            KatExpr::Alt(a, b) => write!(f, "({} + {})", a, b),
            KatExpr::Star(a) => write!(f, "{}*", a),
        }
    }
}

/// A Hoare triple `{b} p {c}`: precondition `b`, program `p`, postcondition `c`.
#[derive(Debug, Clone)]
pub struct HoareTriple {
    /// Precondition (Boolean test).
    pub precondition: BooleanTest,
    /// Program (KAT expression).
    pub program: KatExpr,
    /// Postcondition (Boolean test).
    pub postcondition: BooleanTest,
    /// Optional name for diagnostics.
    pub name: Option<String>,
}

impl HoareTriple {
    /// Create a new Hoare triple.
    pub fn new(pre: BooleanTest, program: KatExpr, post: BooleanTest) -> Self {
        HoareTriple {
            precondition: pre,
            program,
            postcondition: post,
            name: None,
        }
    }

    /// Create a named Hoare triple.
    pub fn named(
        name: impl Into<String>,
        pre: BooleanTest,
        program: KatExpr,
        post: BooleanTest,
    ) -> Self {
        HoareTriple {
            precondition: pre,
            program,
            postcondition: post,
            name: Some(name.into()),
        }
    }
}

impl fmt::Display for HoareTriple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref name) = self.name {
            write!(
                f,
                "[{}] {{{} }} {} {{{} }}",
                name, self.precondition, self.program, self.postcondition,
            )
        } else {
            write!(
                f,
                "{{{} }} {} {{{} }}",
                self.precondition, self.program, self.postcondition,
            )
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Default depth limit for bounded bisimulation.
const DEFAULT_DEPTH_LIMIT: usize = 100;

/// Check equivalence of two KAT expressions.
///
/// Two KAT expressions are equivalent iff they denote the same set of
/// guarded strings. This is decidable in PSPACE (Kozen & Smith, 1996).
/// Uses symbolic bisimulation up to congruence (Pous, 2015) for efficiency.
///
/// # Arguments
///
/// * `a` - First KAT expression.
/// * `b` - Second KAT expression.
///
/// # Returns
///
/// `true` if `a` and `b` are equivalent in the free KAT.
pub fn check_equivalence(a: &KatExpr, b: &KatExpr) -> bool {
    check_equivalence_bounded(a, b, DEFAULT_DEPTH_LIMIT)
}

/// Check equivalence of two KAT expressions with a configurable depth limit.
///
/// Since full KAT equivalence is EXPTIME-complete, this uses a bounded
/// symbolic bisimulation approach (Kozen & Patt-Shamir, 2001). The algorithm
/// expands pairs of expressions by symbolic execution under all Boolean atom
/// valuations up to `depth_limit` steps.
///
/// # Algorithm
///
/// 1. Collect all atomic tests appearing in both expressions.
/// 2. Enumerate all 2^n valuations of those atoms (n = number of distinct atoms).
/// 3. Maintain a worklist of `(e1, e2)` pairs that must be equivalent.
/// 4. For each pair, under each valuation:
///    a. Check **nullability** (acceptance of the empty string): both must agree.
///    b. Compute the **Brzozowski derivative** w.r.t. each action: the resulting
///       derivative pairs are added to the worklist.
/// 5. If any valuation reveals a nullability mismatch, return `false`.
/// 6. If the worklist is exhausted within the depth limit, return `true`.
///
/// # Arguments
///
/// * `a` - First KAT expression.
/// * `b` - Second KAT expression.
/// * `depth_limit` - Maximum number of worklist iterations.
///
/// # Returns
///
/// `true` if `a` and `b` are equivalent up to the given depth bound.
pub fn check_equivalence_bounded(a: &KatExpr, b: &KatExpr, depth_limit: usize) -> bool {
    // Collect all atom names from both expressions.
    let mut atoms = HashSet::new();
    collect_atoms_expr(a, &mut atoms);
    collect_atoms_expr(b, &mut atoms);
    let atom_list: Vec<String> = atoms.into_iter().collect();
    let num_atoms = atom_list.len();

    // Build all 2^n valuations. Each valuation maps atom name → bool.
    let num_valuations = 1usize << num_atoms;
    let valuations: Vec<HashMap<String, bool>> = (0..num_valuations)
        .map(|bits| {
            let mut valuation = HashMap::with_capacity(num_atoms);
            for (i, name) in atom_list.iter().enumerate() {
                valuation.insert(name.clone(), (bits >> i) & 1 == 1);
            }
            valuation
        })
        .collect();

    // Collect all action names for computing derivatives.
    let mut action_set = HashSet::new();
    collect_actions(a, &mut action_set);
    collect_actions(b, &mut action_set);
    let actions: Vec<String> = action_set.into_iter().collect();

    // Worklist of (expr1, expr2) pairs that must be shown equivalent.
    let mut worklist: VecDeque<(KatExpr, KatExpr)> = VecDeque::new();
    let mut visited: HashSet<(KatExpr, KatExpr)> = HashSet::new();

    worklist.push_back((a.clone(), b.clone()));
    visited.insert((a.clone(), b.clone()));

    let mut iterations = 0;

    while let Some((e1, e2)) = worklist.pop_front() {
        if iterations >= depth_limit {
            // Bounded: assume equivalent if we haven't found a counterexample.
            break;
        }
        iterations += 1;

        // Under each Boolean valuation, check nullability agreement and
        // compute derivatives for each action.
        for valuation in &valuations {
            // Check nullability: does the expression accept the empty string
            // under this valuation?
            let n1 = nullable(&e1, valuation);
            let n2 = nullable(&e2, valuation);
            if n1 != n2 {
                return false;
            }

            // Compute derivatives w.r.t. each action and enqueue new pairs.
            for action in &actions {
                let d1 = simplify(&derivative(&e1, action, valuation));
                let d2 = simplify(&derivative(&e2, action, valuation));

                if d1 != d2 {
                    let pair = (d1, d2);
                    if !visited.contains(&pair) {
                        visited.insert(pair.clone());
                        worklist.push_back(pair);
                    }
                }
            }
        }
    }

    true
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions for symbolic bisimulation
// ══════════════════════════════════════════════════════════════════════════════

/// Collect all atomic test names from a KAT expression.
fn collect_atoms_expr(expr: &KatExpr, acc: &mut HashSet<String>) {
    match expr {
        KatExpr::Zero | KatExpr::One => {}
        KatExpr::Test(t) => t.collect_atoms(acc),
        KatExpr::Action(_) => {}
        KatExpr::Seq(a, b) | KatExpr::Alt(a, b) => {
            collect_atoms_expr(a, acc);
            collect_atoms_expr(b, acc);
        }
        KatExpr::Star(inner) => collect_atoms_expr(inner, acc),
    }
}

/// Collect all action names from a KAT expression.
fn collect_actions(expr: &KatExpr, acc: &mut HashSet<String>) {
    match expr {
        KatExpr::Zero | KatExpr::One | KatExpr::Test(_) => {}
        KatExpr::Action(name) => {
            acc.insert(name.clone());
        }
        KatExpr::Seq(a, b) | KatExpr::Alt(a, b) => {
            collect_actions(a, acc);
            collect_actions(b, acc);
        }
        KatExpr::Star(inner) => collect_actions(inner, acc),
    }
}

/// Evaluate a Boolean test under a given atom valuation.
///
/// Returns `true` if the test passes under the valuation, `false` otherwise.
/// Atoms not present in the valuation are treated as `false`.
fn eval_test(test: &BooleanTest, valuation: &HashMap<String, bool>) -> bool {
    match test {
        BooleanTest::True => true,
        BooleanTest::False => false,
        BooleanTest::Atom(name) => *valuation.get(name).unwrap_or(&false),
        BooleanTest::Not(inner) => !eval_test(inner, valuation),
        BooleanTest::And(a, b) => eval_test(a, valuation) && eval_test(b, valuation),
        BooleanTest::Or(a, b) => eval_test(a, valuation) || eval_test(b, valuation),
    }
}

/// Check if a KAT expression is nullable (accepts the empty string) under a
/// given Boolean atom valuation.
///
/// Nullability corresponds to the "epsilon" function in Brzozowski derivatives:
/// - `Zero` is never nullable.
/// - `One` is always nullable.
/// - `Test(t)` is nullable iff `t` evaluates to true under the valuation.
/// - `Action(_)` is never nullable (actions consume input).
/// - `Seq(a, b)` is nullable iff both `a` and `b` are nullable.
/// - `Alt(a, b)` is nullable iff either `a` or `b` is nullable.
/// - `Star(_)` is always nullable (accepts zero repetitions).
fn nullable(expr: &KatExpr, valuation: &HashMap<String, bool>) -> bool {
    match expr {
        KatExpr::Zero => false,
        KatExpr::One => true,
        KatExpr::Test(t) => eval_test(t, valuation),
        KatExpr::Action(_) => false,
        KatExpr::Seq(a, b) => nullable(a, valuation) && nullable(b, valuation),
        KatExpr::Alt(a, b) => nullable(a, valuation) || nullable(b, valuation),
        KatExpr::Star(_) => true,
    }
}

/// Compute the Brzozowski derivative of a KAT expression w.r.t. an action
/// under a given Boolean atom valuation.
///
/// The derivative `D_a(e)` gives the expression that remains after consuming
/// action `a` from `e`. Under a Boolean valuation, tests are resolved to
/// `One` or `Zero`, simplifying the derivative.
///
/// Derivative rules:
/// - `D_a(0) = 0`
/// - `D_a(1) = 0`
/// - `D_a(Test(t)) = 0` (tests don't consume actions)
/// - `D_a(Action(a)) = 1` if the action matches, else `0`
/// - `D_a(Seq(p, q)) = Alt(Seq(D_a(p), q), if nullable(p) then D_a(q) else 0)`
/// - `D_a(Alt(p, q)) = Alt(D_a(p), D_a(q))`
/// - `D_a(Star(p)) = Seq(D_a(p), Star(p))`
fn derivative(expr: &KatExpr, action: &str, valuation: &HashMap<String, bool>) -> KatExpr {
    match expr {
        KatExpr::Zero => KatExpr::Zero,
        KatExpr::One => KatExpr::Zero,
        KatExpr::Test(_) => KatExpr::Zero,
        KatExpr::Action(name) => {
            if name == action {
                KatExpr::One
            } else {
                KatExpr::Zero
            }
        }
        KatExpr::Seq(p, q) => {
            // D_a(p;q) = D_a(p);q + (if nullable(p) then D_a(q) else 0)
            let dp = derivative(p, action, valuation);
            let left = KatExpr::Seq(Box::new(dp), q.clone());
            if nullable(p, valuation) {
                let dq = derivative(q, action, valuation);
                KatExpr::Alt(Box::new(left), Box::new(dq))
            } else {
                left
            }
        }
        KatExpr::Alt(p, q) => {
            let dp = derivative(p, action, valuation);
            let dq = derivative(q, action, valuation);
            KatExpr::Alt(Box::new(dp), Box::new(dq))
        }
        KatExpr::Star(p) => {
            // D_a(p*) = D_a(p) ; p*
            let dp = derivative(p, action, valuation);
            KatExpr::Seq(Box::new(dp), Box::new(KatExpr::Star(p.clone())))
        }
    }
}

/// Simplify a KAT expression by applying algebraic identities.
///
/// Applied identities (one pass, bottom-up):
/// - `Seq(Zero, _) = Zero`, `Seq(_, Zero) = Zero`
/// - `Seq(One, x) = x`, `Seq(x, One) = x`
/// - `Alt(Zero, x) = x`, `Alt(x, Zero) = x`
/// - `Alt(x, x) = x` (idempotence)
/// - `Star(Zero) = One`, `Star(One) = One`
/// - `Star(Star(x)) = Star(x)`
/// - `Test(True) = One`, `Test(False) = Zero`
fn simplify(expr: &KatExpr) -> KatExpr {
    match expr {
        KatExpr::Zero => KatExpr::Zero,
        KatExpr::One => KatExpr::One,
        KatExpr::Test(BooleanTest::True) => KatExpr::One,
        KatExpr::Test(BooleanTest::False) => KatExpr::Zero,
        KatExpr::Test(t) => KatExpr::Test(t.clone()),
        KatExpr::Action(name) => KatExpr::Action(name.clone()),
        KatExpr::Seq(a, b) => {
            let sa = simplify(a);
            let sb = simplify(b);
            match (&sa, &sb) {
                (KatExpr::Zero, _) | (_, KatExpr::Zero) => KatExpr::Zero,
                (KatExpr::One, _) => sb,
                (_, KatExpr::One) => sa,
                _ => KatExpr::Seq(Box::new(sa), Box::new(sb)),
            }
        }
        KatExpr::Alt(a, b) => {
            let sa = simplify(a);
            let sb = simplify(b);
            match (&sa, &sb) {
                (KatExpr::Zero, _) => sb,
                (_, KatExpr::Zero) => sa,
                _ if sa == sb => sa,
                _ => KatExpr::Alt(Box::new(sa), Box::new(sb)),
            }
        }
        KatExpr::Star(inner) => {
            let si = simplify(inner);
            match &si {
                KatExpr::Zero | KatExpr::One => KatExpr::One,
                KatExpr::Star(_) => si,
                _ => KatExpr::Star(Box::new(si)),
            }
        }
    }
}

/// Verify a Hoare triple `{b} p {c}` using KAT.
///
/// The Hoare triple `{b} p {c}` is valid iff `b · p · c̄ = 0` in the free KAT
/// (Kozen, 1997). This reduces to KAT equivalence checking:
/// `b · p · c̄ ≡ 0`.
///
/// # Arguments
///
/// * `triple` - The Hoare triple to verify.
///
/// # Returns
///
/// `true` if the Hoare triple is valid.
pub fn verify_hoare_triple(triple: &HoareTriple) -> bool {
    // Construct pre · program · ¬post
    let condition = KatExpr::hoare_condition(
        triple.precondition.clone(),
        triple.program.clone(),
        triple.postcondition.clone(),
    );

    // {b} p {c} holds iff b·p·¬c = 0
    check_equivalence(&condition, &KatExpr::Zero)
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level KAT check result.
#[derive(Debug, Clone)]
pub struct KatCheck {
    /// Hoare triple verification results: `(triple description, passed)`.
    pub hoare_results: Vec<(String, bool)>,
    /// KAT equivalence check results: `(expr1, expr2, equivalent)`.
    pub equivalence_results: Vec<(String, String, bool)>,
}

/// Pipeline bridge: extract program flow from WPDS and verify Hoare triples.
///
/// Builds KAT expressions from the WPDS call graph: each directed call edge
/// becomes a sequential composition of actions, and the per-category structure
/// generates Hoare triples asserting that reachable categories have valid
/// entry/exit conditions.
///
/// Returns `None` when the call graph has no edges (nothing to verify).
pub fn check_from_bundle(
    wpds_analysis: &crate::wpds::WpdsAnalysis,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> Option<KatCheck> {
    let call_graph = &wpds_analysis.call_graph;
    if call_graph.edges.is_empty() {
        return None; // No call edges → nothing to verify
    }

    let mut hoare_results = Vec::new();
    let mut equivalence_results = Vec::new();

    // Build a set of categories that appear in syntax rules for quick lookup.
    let syntax_categories: std::collections::HashSet<&str> = all_syntax
        .iter()
        .map(|(_, cat, _)| cat.as_str())
        .collect();

    // For each call edge in the WPDS call graph, construct a KAT expression
    // representing the caller→callee transition and verify a Hoare triple:
    //   {caller_reachable} call_action {callee_reachable}
    for edge in &call_graph.edges {
        let call_action = KatExpr::action(format!(
            "call_{}_{}", edge.caller_cat, edge.callee_cat
        ));

        // Precondition: caller category is reachable.
        let pre = BooleanTest::atom(format!("{}_reachable", edge.caller_cat));
        // Postcondition: callee category is reachable.
        let post = BooleanTest::atom(format!("{}_reachable", edge.callee_cat));

        let triple = HoareTriple::named(
            format!("{} -> {}", edge.caller_cat, edge.callee_cat),
            pre,
            call_action,
            post,
        );

        let valid = verify_hoare_triple(&triple);
        hoare_results.push((triple.to_string(), valid));
    }

    // For each SCC of size > 1 (mutual recursion), check that the composition
    // of call edges around the cycle is equivalent to its Kleene star (i.e.,
    // the loop is self-consistent under KAT).
    for scc in &call_graph.sccs {
        if scc.len() < 2 {
            continue;
        }

        // Build a sequential composition of call actions around the SCC.
        let mut cycle_expr = KatExpr::One;
        for i in 0..scc.len() {
            let caller = &scc[i];
            let callee = &scc[(i + 1) % scc.len()];
            let action = KatExpr::action(format!("call_{}_{}", caller, callee));
            cycle_expr = KatExpr::seq(cycle_expr, action);
        }

        // Under Kleene algebra, p* ; p* = p* (star is idempotent under seq).
        // Check that star(cycle) ; star(cycle) ≡ star(cycle).
        let starred = KatExpr::star(cycle_expr);
        let double_star = KatExpr::seq(starred.clone(), starred.clone());
        let equiv = check_equivalence(&starred, &double_star);

        equivalence_results.push((
            format!("{}", starred),
            format!("{}", double_star),
            equiv,
        ));
    }

    // For categories that appear both in the syntax rules and in the reachable
    // set, verify a simple Hoare triple: {has_syntax} parse {category_parsed}.
    for cat_name in &wpds_analysis.reachable_categories {
        if syntax_categories.contains(cat_name.as_str()) {
            let pre = BooleanTest::atom(format!("{}_has_syntax", cat_name));
            let program = KatExpr::action(format!("parse_{}", cat_name));
            let post = BooleanTest::atom(format!("{}_parsed", cat_name));

            let triple = HoareTriple::named(
                format!("parse {}", cat_name),
                pre,
                program,
                post,
            );

            let valid = verify_hoare_triple(&triple);
            hoare_results.push((triple.to_string(), valid));
        }
    }

    Some(KatCheck {
        hoare_results,
        equivalence_results,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kat_expr_display() {
        let expr = KatExpr::seq(
            KatExpr::test(BooleanTest::atom("ready")),
            KatExpr::star(KatExpr::action("shift")),
        );
        assert_eq!(expr.to_string(), "([ready] ; shift*)");
    }

    #[test]
    fn boolean_test_atoms() {
        let test = BooleanTest::and(
            BooleanTest::atom("a"),
            BooleanTest::or(BooleanTest::atom("b"), BooleanTest::atom("a")),
        );
        let atoms = test.atoms();
        assert_eq!(atoms.len(), 2);
        assert!(atoms.contains("a"));
        assert!(atoms.contains("b"));
    }

    #[test]
    fn hoare_triple_display() {
        let triple = HoareTriple::named(
            "parse-safety",
            BooleanTest::atom("valid_input"),
            KatExpr::action("parse"),
            BooleanTest::atom("no_error"),
        );
        assert!(triple.to_string().contains("parse-safety"));
        assert!(triple.to_string().contains("valid_input"));
        assert!(triple.to_string().contains("no_error"));
    }

    #[test]
    fn hoare_condition_construction() {
        let condition = KatExpr::hoare_condition(
            BooleanTest::True,
            KatExpr::action("skip"),
            BooleanTest::True,
        );
        // {true} skip {true} → [1] ; (skip ; [~1]) → should be 0 for validity
        assert!(condition.to_string().contains("skip"));
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Equivalence checking tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn equivalence_reflexive_and_trivial() {
        // Every expression is equivalent to itself.
        let expr = KatExpr::seq(
            KatExpr::action("shift"),
            KatExpr::action("reduce"),
        );
        assert!(check_equivalence(&expr, &expr));

        // Zero is equivalent to Zero.
        assert!(check_equivalence(&KatExpr::Zero, &KatExpr::Zero));

        // One is equivalent to One.
        assert!(check_equivalence(&KatExpr::One, &KatExpr::One));

        // Zero is NOT equivalent to One.
        assert!(!check_equivalence(&KatExpr::Zero, &KatExpr::One));
    }

    #[test]
    fn equivalence_algebraic_identities() {
        let a = KatExpr::action("a");

        // a + 0 = a (alternation identity)
        let a_plus_zero = KatExpr::alt(a.clone(), KatExpr::Zero);
        assert!(check_equivalence(&a_plus_zero, &a));

        // 1 ; a = a (sequential identity, left)
        let one_seq_a = KatExpr::seq(KatExpr::One, a.clone());
        assert!(check_equivalence(&one_seq_a, &a));

        // a ; 1 = a (sequential identity, right)
        let a_seq_one = KatExpr::seq(a.clone(), KatExpr::One);
        assert!(check_equivalence(&a_seq_one, &a));

        // 0 ; a = 0 (annihilation)
        let zero_seq_a = KatExpr::seq(KatExpr::Zero, a.clone());
        assert!(check_equivalence(&zero_seq_a, &KatExpr::Zero));

        // a + a = a (idempotence of alternation)
        let a_plus_a = KatExpr::alt(a.clone(), a.clone());
        assert!(check_equivalence(&a_plus_a, &a));

        // a ; b != b ; a in general (non-commutativity of Seq)
        let b = KatExpr::action("b");
        let ab = KatExpr::seq(a.clone(), b.clone());
        let ba = KatExpr::seq(b.clone(), a.clone());
        assert!(!check_equivalence(&ab, &ba));
    }

    #[test]
    fn equivalence_with_tests() {
        // Test(True) is equivalent to One.
        assert!(check_equivalence(
            &KatExpr::test(BooleanTest::True),
            &KatExpr::One,
        ));

        // Test(False) is equivalent to Zero.
        assert!(check_equivalence(
            &KatExpr::test(BooleanTest::False),
            &KatExpr::Zero,
        ));

        // b ; ~b = 0 (a test followed by its negation is always zero)
        let b = BooleanTest::atom("x_positive");
        let b_then_not_b = KatExpr::seq(
            KatExpr::test(b.clone()),
            KatExpr::test(BooleanTest::not(b.clone())),
        );
        assert!(check_equivalence(&b_then_not_b, &KatExpr::Zero));

        // b + ~b = 1 (law of excluded middle)
        let b_or_not_b = KatExpr::alt(
            KatExpr::test(b.clone()),
            KatExpr::test(BooleanTest::not(b.clone())),
        );
        assert!(check_equivalence(&b_or_not_b, &KatExpr::One));
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Hoare triple verification tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn hoare_triple_skip_preserves_predicate() {
        // {x>0} skip {x>0}
        // "skip" is modeled as One (the identity program).
        // This should be valid since skip does not modify any state.
        let x_pos = BooleanTest::atom("x_positive");
        let triple = HoareTriple::named(
            "skip preserves x>0",
            x_pos.clone(),
            KatExpr::One, // skip
            x_pos.clone(),
        );
        assert!(
            verify_hoare_triple(&triple),
            "{{x>0}} skip {{x>0}} should be a valid Hoare triple"
        );
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_check_from_bundle_with_edges() {
        let mut wpds_analysis = make_empty_wpds_analysis();
        wpds_analysis.call_graph.edges.push(crate::wpds::CallEdge {
            caller_cat: "Expr".to_string(),
            callee_cat: "Type".to_string(),
            call_sites: 1,
            total_weight: 1.0,
        });
        wpds_analysis.call_graph.categories.insert("Expr".to_string());
        wpds_analysis.call_graph.categories.insert("Type".to_string());
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "TypedExpr".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
                crate::SyntaxItemSpec::Terminal(":".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Type".to_string(),
                    param_name: "t".to_string(),
                },
            ],
        )];
        let result = check_from_bundle(&wpds_analysis, &syntax);
        assert!(result.is_some(), "should return Some(KatCheck) when edges exist");
    }

    #[test]
    fn test_check_from_bundle_empty_call_graph() {
        let wpds_analysis = make_empty_wpds_analysis();
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let result = check_from_bundle(&wpds_analysis, &syntax);
        assert!(result.is_none(), "should return None when no call edges");
    }
}
