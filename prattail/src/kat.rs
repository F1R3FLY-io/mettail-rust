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
use std::sync::Arc;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A Boolean test (predicate) in KAT.
///
/// Tests form a Boolean subalgebra of the Kleene algebra. They are used
/// as guards (preconditions/postconditions) in Hoare triples.
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
        let mut work = vec![self];
        while let Some(test) = work.pop() {
            match test {
                BooleanTest::True | BooleanTest::False => {},
                BooleanTest::Atom(name) => {
                    acc.insert(name.clone());
                },
                BooleanTest::Not(inner) => work.push(inner),
                BooleanTest::And(left, right) | BooleanTest::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

impl fmt::Display for BooleanTest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'test> {
            Visit(&'test BooleanTest),
            Text(&'static str),
        }

        fn push_binary<'test>(
            tasks: &mut Vec<Task<'test>>,
            left: &'test BooleanTest,
            right: &'test BooleanTest,
            operator: &'static str,
        ) {
            tasks.push(Task::Text(")"));
            tasks.push(Task::Visit(right));
            tasks.push(Task::Text(operator));
            tasks.push(Task::Visit(left));
            tasks.push(Task::Text("("));
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Visit(BooleanTest::True) => f.write_str("1")?,
                Task::Visit(BooleanTest::False) => f.write_str("0")?,
                Task::Visit(BooleanTest::Atom(name)) => f.write_str(name)?,
                Task::Visit(BooleanTest::Not(inner)) => {
                    tasks.push(Task::Visit(inner));
                    tasks.push(Task::Text("~"));
                },
                Task::Visit(BooleanTest::And(left, right)) => {
                    push_binary(&mut tasks, left, right, " & ");
                },
                Task::Visit(BooleanTest::Or(left, right)) => {
                    push_binary(&mut tasks, left, right, " | ");
                },
            }
        }
        Ok(())
    }
}

/// A Kleene Algebra with Tests expression.
///
/// KAT expressions combine Kleene algebra operators (sequential composition,
/// alternation, Kleene star) with Boolean tests.
#[derive(Clone)]
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
    Seq(Arc<KatExpr>, Arc<KatExpr>),
    /// Alternation/choice: `p + q` (do `p` or `q`).
    Alt(Arc<KatExpr>, Arc<KatExpr>),
    /// Kleene star: `p*` (do `p` zero or more times).
    Star(Arc<KatExpr>),
}

#[path = "kat/lifecycle.rs"]
mod lifecycle;

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
        KatExpr::Seq(Arc::new(a), Arc::new(b))
    }

    /// Alternation/choice.
    pub fn alt(a: KatExpr, b: KatExpr) -> Self {
        KatExpr::Alt(Arc::new(a), Arc::new(b))
    }

    /// Kleene star.
    pub fn star(a: KatExpr) -> Self {
        KatExpr::Star(Arc::new(a))
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
        enum Task<'expr> {
            Visit(&'expr KatExpr),
            Bool(&'expr BooleanTest),
            Text(&'static str),
        }

        fn push_binary<'expr>(
            tasks: &mut Vec<Task<'expr>>,
            left: &'expr KatExpr,
            right: &'expr KatExpr,
            operator: &'static str,
        ) {
            tasks.push(Task::Text(")"));
            tasks.push(Task::Visit(right));
            tasks.push(Task::Text(operator));
            tasks.push(Task::Visit(left));
            tasks.push(Task::Text("("));
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Bool(test) => write!(f, "{test}")?,
                Task::Visit(KatExpr::Zero) => f.write_str("0")?,
                Task::Visit(KatExpr::One) => f.write_str("1")?,
                Task::Visit(KatExpr::Test(test)) => {
                    tasks.push(Task::Text("]"));
                    tasks.push(Task::Bool(test));
                    tasks.push(Task::Text("["));
                },
                Task::Visit(KatExpr::Action(name)) => f.write_str(name)?,
                Task::Visit(KatExpr::Seq(left, right)) => {
                    push_binary(&mut tasks, left, right, " ; ");
                },
                Task::Visit(KatExpr::Alt(left, right)) => {
                    push_binary(&mut tasks, left, right, " + ");
                },
                Task::Visit(KatExpr::Star(inner)) => {
                    tasks.push(Task::Text("*"));
                    tasks.push(Task::Visit(inner));
                },
            }
        }
        Ok(())
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
            write!(f, "{{{} }} {} {{{} }}", self.precondition, self.program, self.postcondition,)
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

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
    check_equivalence_exact(a, b)
}

/// Check equivalence of two KAT expressions exactly.
///
/// The procedure computes the reachable subset states of Antimirov partial
/// derivatives to exhaustion.  Expressions are hash-consed and each derivative
/// state is a sorted set of expression identifiers; this supplies a compact,
/// canonical finite-state representation without relying on a search budget.
/// Boolean valuations are generated lazily with an arbitrary-width bit vector,
/// so the number of test atoms is not capped by a machine-word shift.
///
/// # Algorithm
///
/// 1. Collect all atomic tests appearing in both expressions.
/// 2. Lazily enumerate all `2^n` valuations of those atoms (`n` is the number
///    of distinct atoms).
/// 3. Maintain a worklist of pairs of canonical partial-derivative subsets.
/// 4. For each pair, under each valuation:
///   a. Check **nullability** (acceptance of the empty string): both must agree.
///   b. Compute the **Antimirov partial derivative** w.r.t. each action, intern
///      its residual expressions, and add the resulting subset pair to the
///      worklist.
/// 5. If any valuation reveals a nullability mismatch, return `false`.
/// 6. Return `true` only after the derivative-pair worklist is exhausted.
///
/// # Arguments
///
/// * `a` - First KAT expression.
/// * `b` - Second KAT expression.
/// # Returns
///
/// `true` if and only if `a` and `b` are equivalent in the free KAT.
pub fn check_equivalence_exact(a: &KatExpr, b: &KatExpr) -> bool {
    // Collect all atom names from both expressions.
    let mut atoms = HashSet::new();
    collect_atoms_expr(a, &mut atoms);
    collect_atoms_expr(b, &mut atoms);
    let mut atom_list: Vec<String> = atoms.into_iter().collect();
    atom_list.sort_unstable();

    // Collect all action names for computing derivatives.
    let mut action_set = HashSet::new();
    collect_actions(a, &mut action_set);
    collect_actions(b, &mut action_set);
    let mut actions: Vec<String> = action_set.into_iter().collect();
    actions.sort_unstable();

    let mut expressions = ExprInterner::default();
    let initial_left = vec![expressions.intern(simplify(a))];
    let initial_right = vec![expressions.intern(simplify(b))];

    // Worklist of canonical subset-state pairs that must be shown equivalent.
    let mut worklist = VecDeque::from([(initial_left.clone(), initial_right.clone())]);
    let mut visited = HashSet::from([(initial_left, initial_right)]);

    while let Some((left, right)) = worklist.pop_front() {
        // Under each Boolean valuation, check nullability agreement and
        // compute derivatives for each action.
        for valuation in BooleanValuations::new(&atom_list) {
            // Check nullability: does the expression accept the empty string
            // under this valuation?
            let n1 = expressions.nullable(&left, &valuation);
            let n2 = expressions.nullable(&right, &valuation);
            if n1 != n2 {
                return false;
            }

            // Compute derivatives w.r.t. each action and enqueue new pairs.
            for action in &actions {
                let d1 = expressions.derivative(&left, action, &valuation);
                let d2 = expressions.derivative(&right, action, &valuation);

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

/// Hash-consed expression storage used to canonicalize partial-derivative
/// subsets.  The vector supplies stable small identifiers; the map ensures that
/// structurally equal residuals share one identifier.
#[derive(Default)]
struct ExprInterner {
    ids: HashMap<KatExpr, usize>,
    expressions: Vec<KatExpr>,
}

impl ExprInterner {
    fn intern(&mut self, expression: KatExpr) -> usize {
        if let Some(index) = self.ids.get(&expression) {
            return *index;
        }
        let index = self.expressions.len();
        self.expressions.push(expression.clone());
        self.ids.insert(expression, index);
        index
    }

    fn nullable(&self, state: &[usize], valuation: &HashMap<String, bool>) -> bool {
        state
            .iter()
            .any(|index| nullable(&self.expressions[*index], valuation))
    }

    fn derivative(
        &mut self,
        state: &[usize],
        action: &str,
        valuation: &HashMap<String, bool>,
    ) -> Vec<usize> {
        let mut residuals = Vec::new();
        for index in state {
            residuals.extend(partial_derivative(&self.expressions[*index], action, valuation));
        }
        let mut result: Vec<_> = residuals
            .into_iter()
            .map(|expression| self.intern(expression))
            .collect();
        result.sort_unstable();
        result.dedup();
        result
    }
}

/// Compatibility entry point retained for downstream callers that selected a
/// budget before the checker became exact.
///
/// The former implementation treated budget exhaustion as proof of
/// equivalence, which could return a false positive.  The argument is therefore
/// intentionally ignored: this function now has the same exact semantics as
/// [`check_equivalence_exact`].
pub fn check_equivalence_bounded(a: &KatExpr, b: &KatExpr, _depth_limit: usize) -> bool {
    check_equivalence_exact(a, b)
}

/// Lazy, arbitrary-width enumeration of Boolean valuations.
///
/// `bits[0]` is the least-significant position.  Keeping the counter as a
/// vector avoids `1usize << atom_count`, which both overflowed for large atom
/// sets and forced every valuation to be resident at once.
struct BooleanValuations<'a> {
    atoms: &'a [String],
    bits: Vec<bool>,
    first: bool,
    exhausted: bool,
}

impl<'a> BooleanValuations<'a> {
    fn new(atoms: &'a [String]) -> Self {
        Self {
            atoms,
            bits: vec![false; atoms.len()],
            first: true,
            exhausted: false,
        }
    }

    fn materialize(&self) -> HashMap<String, bool> {
        self.atoms
            .iter()
            .cloned()
            .zip(self.bits.iter().copied())
            .collect()
    }
}

impl Iterator for BooleanValuations<'_> {
    type Item = HashMap<String, bool>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }
        if self.first {
            self.first = false;
            return Some(self.materialize());
        }

        for bit in &mut self.bits {
            if *bit {
                *bit = false;
            } else {
                *bit = true;
                return Some(self.materialize());
            }
        }
        self.exhausted = true;
        None
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions for symbolic bisimulation
// ══════════════════════════════════════════════════════════════════════════════

/// Collect all atomic test names from a KAT expression.
fn collect_atoms_expr(expr: &KatExpr, acc: &mut HashSet<String>) {
    let mut work = vec![expr];
    while let Some(expr) = work.pop() {
        match expr {
            KatExpr::Zero | KatExpr::One | KatExpr::Action(_) => {},
            KatExpr::Test(test) => test.collect_atoms(acc),
            KatExpr::Seq(left, right) | KatExpr::Alt(left, right) => {
                work.push(right);
                work.push(left);
            },
            KatExpr::Star(inner) => work.push(inner),
        }
    }
}

/// Collect all action names from a KAT expression.
fn collect_actions(expr: &KatExpr, acc: &mut HashSet<String>) {
    let mut work = vec![expr];
    while let Some(expr) = work.pop() {
        match expr {
            KatExpr::Zero | KatExpr::One | KatExpr::Test(_) => {},
            KatExpr::Action(name) => {
                acc.insert(name.clone());
            },
            KatExpr::Seq(left, right) | KatExpr::Alt(left, right) => {
                work.push(right);
                work.push(left);
            },
            KatExpr::Star(inner) => work.push(inner),
        }
    }
}

/// Evaluate a Boolean test under a given atom valuation.
///
/// Returns `true` if the test passes under the valuation, `false` otherwise.
/// Atoms not present in the valuation are treated as `false`.
pub(crate) fn eval_test(test: &BooleanTest, valuation: &HashMap<String, bool>) -> bool {
    enum Task<'test> {
        Visit(&'test BooleanTest),
        Not,
        AndAfterLeft(&'test BooleanTest),
        OrAfterLeft(&'test BooleanTest),
    }

    let mut tasks = vec![Task::Visit(test)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(BooleanTest::True) => values.push(true),
            Task::Visit(BooleanTest::False) => values.push(false),
            Task::Visit(BooleanTest::Atom(name)) => {
                values.push(*valuation.get(name).unwrap_or(&false));
            },
            Task::Visit(BooleanTest::Not(inner)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(inner));
            },
            Task::Visit(BooleanTest::And(left, right)) => {
                tasks.push(Task::AndAfterLeft(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(BooleanTest::Or(left, right)) => {
                tasks.push(Task::OrAfterLeft(right));
                tasks.push(Task::Visit(left));
            },
            Task::Not => {
                let value = values
                    .last_mut()
                    .expect("BooleanTest evaluation lost value");
                *value = !*value;
            },
            Task::AndAfterLeft(right) => {
                if *values
                    .last()
                    .expect("BooleanTest evaluation lost left value")
                {
                    values.pop();
                    tasks.push(Task::Visit(right));
                }
            },
            Task::OrAfterLeft(right) => {
                if !*values
                    .last()
                    .expect("BooleanTest evaluation lost left value")
                {
                    values.pop();
                    tasks.push(Task::Visit(right));
                }
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("BooleanTest evaluation produced no value")
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
    enum Task<'expr> {
        Visit(&'expr KatExpr),
        SeqAfterLeft(&'expr KatExpr),
        AltAfterLeft(&'expr KatExpr),
    }

    let mut tasks = vec![Task::Visit(expr)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(KatExpr::Zero) | Task::Visit(KatExpr::Action(_)) => values.push(false),
            Task::Visit(KatExpr::One) | Task::Visit(KatExpr::Star(_)) => values.push(true),
            Task::Visit(KatExpr::Test(test)) => values.push(eval_test(test, valuation)),
            Task::Visit(KatExpr::Seq(left, right)) => {
                tasks.push(Task::SeqAfterLeft(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(KatExpr::Alt(left, right)) => {
                tasks.push(Task::AltAfterLeft(right));
                tasks.push(Task::Visit(left));
            },
            Task::SeqAfterLeft(right) => {
                if *values.last().expect("KAT nullability lost left value") {
                    values.pop();
                    tasks.push(Task::Visit(right));
                }
            },
            Task::AltAfterLeft(right) => {
                if !*values.last().expect("KAT nullability lost left value") {
                    values.pop();
                    tasks.push(Task::Visit(right));
                }
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("KAT nullability produced no value")
}

/// Compute the Antimirov partial derivative of a KAT expression w.r.t. an
/// action under a given Boolean atom valuation.
///
/// Each returned expression is one residual alternative after consuming the
/// action.  Keeping alternatives as a set avoids constructing ever-larger
/// nested `Alt` trees; the caller interns and canonicalizes the set.
///
/// Partial-derivative rules:
/// - `d_a(0) = d_a(1) = d_a(Test(t)) = {}`
/// - `d_a(Action(a)) = {1}` and `d_a(Action(b)) = {}` for `a != b`
/// - `d_a(p q) = {r q | r in d_a(p)} union d_a(q)` when `p` is nullable
/// - `d_a(p + q) = d_a(p) union d_a(q)`
/// - `d_a(p*) = {r p* | r in d_a(p)}`
fn partial_derivative(
    expr: &KatExpr,
    action: &str,
    valuation: &HashMap<String, bool>,
) -> Vec<KatExpr> {
    enum Task<'expr> {
        Visit(&'expr KatExpr),
        FinishSeq {
            right: &'expr Arc<KatExpr>,
            right_derivative: bool,
        },
        FinishAlt,
        FinishStar(&'expr Arc<KatExpr>),
    }

    let mut tasks = vec![Task::Visit(expr)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(KatExpr::Zero | KatExpr::One | KatExpr::Test(_)) => {
                values.push(Vec::new());
            },
            Task::Visit(KatExpr::Action(name)) => values.push(if name == action {
                vec![KatExpr::One]
            } else {
                Vec::new()
            }),
            Task::Visit(KatExpr::Seq(left, right)) => {
                let right_derivative = nullable(left, valuation);
                tasks.push(Task::FinishSeq { right, right_derivative });
                if right_derivative {
                    tasks.push(Task::Visit(right));
                }
                tasks.push(Task::Visit(left));
            },
            Task::Visit(KatExpr::Alt(left, right)) => {
                tasks.push(Task::FinishAlt);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(KatExpr::Star(inner)) => {
                tasks.push(Task::FinishStar(inner));
                tasks.push(Task::Visit(inner));
            },
            Task::FinishSeq { right, right_derivative } => {
                let mut derivative_right = if right_derivative {
                    values
                        .pop()
                        .expect("KAT partial derivative lost right result")
                } else {
                    Vec::new()
                };
                let derivative_left = values
                    .pop()
                    .expect("KAT partial derivative lost left result");
                let mut result = Vec::with_capacity(derivative_left.len() + derivative_right.len());
                result.extend(derivative_left.into_iter().filter_map(|residual| {
                    let sequence = simplify(&KatExpr::Seq(Arc::new(residual), Arc::clone(right)));
                    (!matches!(&sequence, KatExpr::Zero)).then_some(sequence)
                }));
                result.append(&mut derivative_right);
                values.push(result);
            },
            Task::FinishAlt => {
                let mut right = values
                    .pop()
                    .expect("KAT partial derivative lost right result");
                let mut left = values
                    .pop()
                    .expect("KAT partial derivative lost left result");
                left.append(&mut right);
                values.push(left);
            },
            Task::FinishStar(inner) => {
                let derivative = values
                    .pop()
                    .expect("KAT partial derivative lost star result");
                let star = Arc::new(KatExpr::Star(Arc::clone(inner)));
                values.push(
                    derivative
                        .into_iter()
                        .filter_map(|residual| {
                            let sequence =
                                simplify(&KatExpr::Seq(Arc::new(residual), Arc::clone(&star)));
                            (!matches!(&sequence, KatExpr::Zero)).then_some(sequence)
                        })
                        .collect(),
                );
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("KAT partial derivative produced no result")
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
    enum Task<'expr> {
        Visit(&'expr KatExpr),
        FinishSeq,
        FinishAlt,
        FinishStar,
    }

    let mut tasks = vec![Task::Visit(expr)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(KatExpr::Zero) => values.push(KatExpr::Zero),
            Task::Visit(KatExpr::One) => values.push(KatExpr::One),
            Task::Visit(KatExpr::Test(BooleanTest::True)) => values.push(KatExpr::One),
            Task::Visit(KatExpr::Test(BooleanTest::False)) => values.push(KatExpr::Zero),
            Task::Visit(KatExpr::Test(test)) => values.push(KatExpr::Test(test.clone())),
            Task::Visit(KatExpr::Action(name)) => values.push(KatExpr::Action(name.clone())),
            Task::Visit(KatExpr::Seq(left, right)) => {
                tasks.push(Task::FinishSeq);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(KatExpr::Alt(left, right)) => {
                tasks.push(Task::FinishAlt);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(KatExpr::Star(inner)) => {
                tasks.push(Task::FinishStar);
                tasks.push(Task::Visit(inner));
            },
            Task::FinishSeq => {
                let right = values.pop().expect("KAT simplifier lost right operand");
                let left = values.pop().expect("KAT simplifier lost left operand");
                values.push(if matches!(&left, KatExpr::Zero) || matches!(&right, KatExpr::Zero) {
                    KatExpr::Zero
                } else if matches!(&left, KatExpr::One) {
                    right
                } else if matches!(&right, KatExpr::One) {
                    left
                } else {
                    KatExpr::Seq(Arc::new(left), Arc::new(right))
                });
            },
            Task::FinishAlt => {
                let right = values.pop().expect("KAT simplifier lost right operand");
                let left = values.pop().expect("KAT simplifier lost left operand");
                values.push(if matches!(&left, KatExpr::Zero) {
                    right
                } else if matches!(&right, KatExpr::Zero) || left == right {
                    left
                } else {
                    KatExpr::Alt(Arc::new(left), Arc::new(right))
                });
            },
            Task::FinishStar => {
                let inner = values.pop().expect("KAT simplifier lost star operand");
                values.push(if matches!(&inner, KatExpr::Zero | KatExpr::One) {
                    KatExpr::One
                } else if matches!(&inner, KatExpr::Star(_)) {
                    inner
                } else {
                    KatExpr::Star(Arc::new(inner))
                });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("KAT simplifier produced no result")
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
    let syntax_categories: std::collections::HashSet<&str> =
        all_syntax.iter().map(|(_, cat, _)| cat.as_str()).collect();

    // For each call edge in the WPDS call graph, construct a KAT expression
    // representing the caller→callee transition and verify a Hoare triple:
    //   {caller_reachable} call_action {callee_reachable}
    for edge in &call_graph.edges {
        let call_action = KatExpr::action(format!("call_{}_{}", edge.caller_cat, edge.callee_cat));

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

        equivalence_results.push((format!("{}", starred), format!("{}", double_star), equiv));
    }

    // For categories that appear both in the syntax rules and in the reachable
    // set, verify a simple Hoare triple: {has_syntax} parse {category_parsed}.
    for cat_name in &wpds_analysis.reachable_categories {
        if syntax_categories.contains(cat_name.as_str()) {
            let pre = BooleanTest::atom(format!("{}_has_syntax", cat_name));
            let program = KatExpr::action(format!("parse_{}", cat_name));
            let post = BooleanTest::atom(format!("{}_parsed", cat_name));

            let triple = HoareTriple::named(format!("parse {}", cat_name), pre, program, post);

            let valid = verify_hoare_triple(&triple);
            hoare_results.push((triple.to_string(), valid));
        }
    }

    Some(KatCheck { hoare_results, equivalence_results })
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
        let condition =
            KatExpr::hoare_condition(BooleanTest::True, KatExpr::action("skip"), BooleanTest::True);
        // {true} skip {true} → [1] ; (skip ; [~1]) → should be 0 for validity
        assert!(condition.to_string().contains("skip"));
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Equivalence checking tests
    // ══════════════════════════════════════════════════════════════════════════

    #[test]
    fn equivalence_reflexive_and_trivial() {
        // Every expression is equivalent to itself.
        let expr = KatExpr::seq(KatExpr::action("shift"), KatExpr::action("reduce"));
        assert!(check_equivalence(&expr, &expr));

        // Zero is equivalent to Zero.
        assert!(check_equivalence(&KatExpr::Zero, &KatExpr::Zero));

        // One is equivalent to One.
        assert!(check_equivalence(&KatExpr::One, &KatExpr::One));

        // Zero is NOT equivalent to One.
        assert!(!check_equivalence(&KatExpr::Zero, &KatExpr::One));
    }

    #[test]
    fn compatibility_budget_cannot_turn_an_unfinished_proof_into_equivalence() {
        // The initial pair is non-nullable on both sides.  The mismatch becomes
        // visible only after taking the derivative for `step`, so the former
        // one-iteration budget incorrectly returned true.
        let one_step = KatExpr::action("step");
        let two_steps = KatExpr::seq(one_step.clone(), one_step.clone());
        assert!(!check_equivalence_bounded(&one_step, &two_steps, 1));
        assert!(!check_equivalence_bounded(&KatExpr::Zero, &KatExpr::One, 0));
    }

    #[test]
    fn lazy_valuation_counter_covers_all_small_assignments_in_binary_order() {
        let atoms = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let valuations: Vec<_> = BooleanValuations::new(&atoms).collect();
        assert_eq!(valuations.len(), 8);
        for (index, valuation) in valuations.iter().enumerate() {
            for (bit, atom) in atoms.iter().enumerate() {
                assert_eq!(valuation[atom], index & (1 << bit) != 0);
            }
        }
        assert_eq!(BooleanValuations::new(&[]).count(), 1);
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
        assert!(check_equivalence(&KatExpr::test(BooleanTest::True), &KatExpr::One,));

        // Test(False) is equivalent to Zero.
        assert!(check_equivalence(&KatExpr::test(BooleanTest::False), &KatExpr::Zero,));

        // b ; ~b = 0 (a test followed by its negation is always zero)
        let b = BooleanTest::atom("x_positive");
        let b_then_not_b =
            KatExpr::seq(KatExpr::test(b.clone()), KatExpr::test(BooleanTest::not(b.clone())));
        assert!(check_equivalence(&b_then_not_b, &KatExpr::Zero));

        // b + ~b = 1 (law of excluded middle)
        let b_or_not_b =
            KatExpr::alt(KatExpr::test(b.clone()), KatExpr::test(BooleanTest::not(b.clone())));
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
            cek_bijection: crate::wpds::CekWpdsBijection::default(),
            pautomaton: crate::wpds::PAutomaton::new(0),
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
        wpds_analysis
            .call_graph
            .categories
            .insert("Expr".to_string());
        wpds_analysis
            .call_graph
            .categories
            .insert("Type".to_string());
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
