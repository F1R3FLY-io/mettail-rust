//! SMT-backed [`ConstraintTheory`] backend (Z3 library, in-process) — OSLF Phase 8.
//!
//! Backported from `lling-llang`'s `src/symbolic/logict_smt.rs`, **with the
//! soundness defect of the upstream `§4-B` design removed**. The upstream header
//! advertised that implementing [`ConstraintTheory`] for [`Z3Theory`] makes
//! `TheoryAlgebra<Z3Theory>` a [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra)
//! "for free", so that every Symbolic-Finite-Automaton algorithm (emptiness,
//! intersection, **complement**, **determinization**, **language inclusion /
//! equivalence**) would run over SMT guards. That is the defect: an SMT solver is
//! a *semi*-decision procedure (it may answer `Unknown`), and the SFA complement /
//! determinize / equivalence algorithms are sound **only** over a *classical*
//! (decidable, involutive-complement, excluded-middle) Boolean algebra. Routing an
//! `Unknown`-producing oracle through them silently fabricates a classical answer
//! where none exists.
//!
//! # The Sat3-only doctrine (this backport)
//!
//! Z3 is reachable here **only** as a three-valued *classifier*:
//!
//! - [`is_satisfiable_3v`] — the single public satisfiability entrypoint. It returns
//!   a [`Sat3`] (`Sat` / `Unsat` / `DontKnow`) and **never collapses `DontKnow`** to
//!   either side. This mirrors the reject-safe behavioral oracle
//!   [`crate::behavioral_algebra`]'s `is_satisfiable_3v`: an undecided guard is
//!   reported honestly as `DontKnow` (tier `T3`, degrading any `T4` caller to `T3`),
//!   never as a wrong `Sat`/`Unsat`.
//! - [`checked_witness`] — returns a model **only** when the solver answers `Sat`
//!   *and* the returned assignment re-satisfies the constraint under the pure
//!   [`eval_constraint`] evaluator (a certificate check; cf. `GuardTierCertificate`).
//!   `DontKnow` never fabricates a witness.
//!
//! [`Z3Theory`] implements **only** [`ConstraintTheory`]. It is deliberately **not**
//! an exact/decidable theory, so the generic [`crate::logict::TheoryAlgebra`]
//! exposes only its reject-safe three-valued behavior, never a classical
//! [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra). The verified deciders
//! (Presburger, the ordered-field / string SFAs, the behavioral algebra) remain the
//! **primary** guard deciders; Z3 is a *secondary gap-filler* invoked only where
//! those return `DontKnow` (e.g. mixed numeric/bitvector guards), and its verdict is
//! never fed into the SFA classical consumers (complement / determinize /
//! equivalence).
//!
//! # `ConstraintTheory` and the `Sat3` channel for SMT `Unknown`
//!
//! [`ConstraintTheory::propagate`] is *two-valued* — `Some(store)` (consistent) or
//! `None` (inconsistent) — but an SMT solver may return **`Unknown`** (timeout,
//! incompleteness, non-linear arithmetic). Collapsing `Unknown` to either side is
//! unsound: as "consistent" it lets an unsatisfiable guard through; as "inconsistent"
//! it rejects a satisfiable one. So the [`SmtStore`] carries a [`Sat3`]:
//!
//! - `propagate` returns `None` **only** on a proven `Unsat`; both `Sat` and `Unknown`
//!   yield `Some(store)`, recording `Sat3::Sat` / `Sat3::DontKnow`.
//! - [`ConstraintTheory::witness`] returns a model **only** on `Sat3::Sat` — never on
//!   `DontKnow`, so an undecided guard never fabricates a witness.
//!
//! Thus `Unknown` is treated as *possibly satisfiable* — the conservative
//! over-approximation that keeps the propagation channel sound — and
//! [`Sat3::into_safe_bool`] forces callers to handle the undecided case rather than
//! silently treat it as `false`. This is exactly why the `algebra_tower`'s
//! three-valued logic is load-bearing here.
//!
//! # Boundary
//!
//! The Z3 **library** (the `z3` crate, dynamically linked against the system libz3) is
//! in-process — in-boundary, behind the off-by-default `smt` feature. The cvc5 / Z3
//! **CLI** certificate path (`--produce-proofs` → Alethe/LFSC) is a *subprocess* and
//! lives in the WFST sidecar, never here. A fresh Z3 `Context`/`Solver` is built per
//! check, so no Z3 AST (which borrows its `Context`) is ever stored in a `Store` —
//! keeping [`SmtStore`] `Clone + Send + Sync` and lifetime-free.

use std::collections::BTreeMap;
use std::fmt;
use std::num::NonZeroU32;
use std::str::FromStr;
use std::sync::OnceLock;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::One;
use z3::ast::Ast; // brings `_eq` into scope for Int/BV

use crate::algebra_tower::Sat3;
use crate::logict::{ConstraintTheory, LogicStream};

// ══════════════════════════════════════════════════════════════════════════════
// Constraint AST (self-contained: Clone + Eq + Hash, no Z3 Context lifetime)
// ══════════════════════════════════════════════════════════════════════════════

/// A numeric term: linear integer arithmetic or a fixed-width bitvector.
///
/// Kept independent of any Z3 `Context` so [`SmtConstraint`] satisfies
/// `ConstraintTheory::Constraint: Clone + Eq + Hash`; translated to a fresh Z3 AST at
/// solve time by [`Z3Env`].
pub enum SmtTerm {
    /// Mathematical integer literal (arbitrary precision).
    IntLit(BigInt),
    /// Integer variable (by name).
    IntVar(String),
    /// Bitvector literal `(value, width)`. Validation rejects width zero and
    /// interpretation normalizes `value` modulo `2^width`.
    BvLit(BigUint, u32),
    /// Bitvector variable `(name, width)`.
    BvVar(String, u32),
    /// `a + b`.
    Add(Box<SmtTerm>, Box<SmtTerm>),
    /// `a - b`.
    Sub(Box<SmtTerm>, Box<SmtTerm>),
    /// `k · a` (linear: integer/bitvector coefficient).
    Scale(BigInt, Box<SmtTerm>),
}

impl SmtTerm {
    /// Construct an arbitrary-precision mathematical integer literal.
    pub fn int(value: impl Into<BigInt>) -> Self {
        Self::IntLit(value.into())
    }

    /// Construct a raw fixed-width bitvector literal.
    ///
    /// Width validation is deliberately performed at the checked boundary so an
    /// untrusted decoded AST cannot bypass the same validation as programmatic input.
    pub fn bit_vector(value: impl Into<BigUint>, width: u32) -> Self {
        Self::BvLit(value.into(), width)
    }

    /// Construct a scalar multiplication.
    pub fn scale(coefficient: impl Into<BigInt>, term: SmtTerm) -> Self {
        Self::Scale(coefficient.into(), Box::new(term))
    }
}

/// A guard constraint over [`SmtTerm`]s: booleans + (in)equalities. Boolean
/// connectives compose constraints; comparisons relate two terms **of the same sort**
/// (both integer or both bitvector of equal width).
pub enum SmtConstraint {
    /// Constant truth.
    True,
    /// Constant falsity.
    False,
    /// Boolean variable (by name).
    BoolVar(String),
    /// `a = b`.
    Eq(SmtTerm, SmtTerm),
    /// `a ≤ b` (signed for integers, unsigned for bitvectors).
    Le(SmtTerm, SmtTerm),
    /// `a < b`.
    Lt(SmtTerm, SmtTerm),
    /// `a ≥ b`.
    Ge(SmtTerm, SmtTerm),
    /// `a > b`.
    Gt(SmtTerm, SmtTerm),
    /// `¬a`.
    Not(Box<SmtConstraint>),
    /// `a ∧ b`.
    And(Box<SmtConstraint>, Box<SmtConstraint>),
    /// `a ∨ b`.
    Or(Box<SmtConstraint>, Box<SmtConstraint>),
}

#[path = "logict_smt/lifecycle.rs"]
mod lifecycle;

/// Sorts admitted by the checked SMT boundary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SmtSort {
    /// Boolean proposition.
    Bool,
    /// Mathematical (unbounded) integer.
    Int,
    /// Unsigned fixed-width bitvector. A checked sort always has positive width.
    BitVector(u32),
}

/// Why an untrusted SMT AST or model could not be admitted as a typed formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtValidationError {
    /// Z3 and the mathematical model do not define a zero-width bitvector.
    ZeroBitVectorWidth,
    /// One variable name was reused at two incompatible sorts.
    VariableSortConflict {
        name: String,
        first: SmtSort,
        second: SmtSort,
    },
    /// An arithmetic operator was applied to terms of different sorts.
    ArithmeticSortMismatch {
        operation: &'static str,
        left: SmtSort,
        right: SmtSort,
    },
    /// A comparison related terms of different sorts.
    ComparisonSortMismatch { left: SmtSort, right: SmtSort },
    /// The supplied model omitted a variable required by the formula.
    MissingModelBinding { name: String, expected: SmtSort },
    /// A bitvector model value carried a different width from its use site.
    ModelBitVectorWidthMismatch { name: String, expected: u32, actual: u32 },
    /// A raw model value was not normalized to its declared bitvector width.
    ModelBitVectorOutOfRange { name: String, width: u32 },
    /// A checked mathematical numeral could not be represented by the Z3 API.
    SolverNumeralEncoding,
    /// A Z3 model numeral could not be extracted exactly.
    SolverModelNumeral { name: String, expected: SmtSort },
    /// An internal typed translation result contradicted prior validation.
    InternalSortInvariant { operation: &'static str },
    /// Deterministic preflight demand exceeded an explicit work limit.
    WorkBudgetExceeded {
        resource: SmtWorkResource,
        required: u64,
        limit: u64,
    },
}

impl fmt::Display for SmtValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for SmtValidationError {}

/// Deterministic variable-sort environment produced by validation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SmtSignature {
    /// One globally consistent sort for every variable name.
    pub variables: BTreeMap<String, SmtSort>,
}

/// Independently charged resources at the SMT validation/translation boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmtWorkResource {
    /// Raw AST constructors visited by the iterative validator.
    AstNodes,
    /// Sum of binary digits across literal and scale numerals.
    NumeralBits,
    /// Largest fixed-width bitvector sort requested by the formula.
    BitVectorWidth,
}

/// Deterministic work demand measured before allocation-heavy Z3 translation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SmtWorkDemand {
    /// Raw AST constructors visited.
    pub ast_nodes: u64,
    /// Total binary numeral digits.
    pub numeral_bits: u64,
    /// Largest requested bitvector width.
    pub max_bitvector_width: u32,
}

/// Explicit, versionable resource policy for one SMT classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SmtWorkBudget {
    /// Maximum raw AST constructors accepted by preflight.
    pub max_ast_nodes: u64,
    /// Maximum total binary digits across input numerals.
    pub max_numeral_bits: u64,
    /// Maximum individual bitvector width.
    pub max_bitvector_width: u32,
    /// Z3 deterministic resource-limit counter (`rlimit`).
    pub solver_rlimit: u32,
}

impl Default for SmtWorkBudget {
    fn default() -> Self {
        Self {
            max_ast_nodes: 100_000,
            max_numeral_bits: 1_048_576,
            max_bitvector_width: 65_536,
            solver_rlimit: 10_000_000,
        }
    }
}

/// Result of the single iterative type-and-resource preflight pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmtValidationReport {
    /// Globally consistent variable sorts.
    pub signature: SmtSignature,
    /// Deterministic charged input demand.
    pub demand: SmtWorkDemand,
}

/// An unsigned bitvector value paired with the width that determines its modulus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmtBitVector {
    /// Canonical unsigned representative in `[0, 2^width)`.
    pub value: BigUint,
    /// Positive bit width.
    pub width: u32,
}

impl SmtBitVector {
    /// Construct and normalize a bitvector value, rejecting width zero.
    pub fn new(value: impl Into<BigUint>, width: u32) -> Result<Self, SmtValidationError> {
        Self::new_with_budget(value, width, &SmtWorkBudget::default())
    }

    /// Construct under an explicit resource policy.
    pub fn new_with_budget(
        value: impl Into<BigUint>,
        width: u32,
        budget: &SmtWorkBudget,
    ) -> Result<Self, SmtValidationError> {
        let value = value.into();
        ensure_width_within_budget(width, budget)?;
        ensure_numeral_within_budget(value.bits().max(1), budget)?;
        let width = checked_width(width)?;
        let modulus = bitvector_modulus(width);
        Ok(Self {
            value: value % modulus,
            width: width.get(),
        })
    }
}

/// A satisfying assignment extracted from a [`Sat3::Sat`] store.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SmtModel {
    /// Integer variable assignments.
    pub ints: BTreeMap<String, BigInt>,
    /// Bitvector variable assignments with explicit, checked widths.
    pub bvs: BTreeMap<String, SmtBitVector>,
    /// Boolean variable assignments.
    pub bools: BTreeMap<String, bool>,
}

fn bitvector_modulus(width: NonZeroU32) -> BigUint {
    BigUint::one() << width.get()
}

fn checked_width(width: u32) -> Result<NonZeroU32, SmtValidationError> {
    NonZeroU32::new(width).ok_or(SmtValidationError::ZeroBitVectorWidth)
}

fn ensure_width_within_budget(
    width: u32,
    budget: &SmtWorkBudget,
) -> Result<(), SmtValidationError> {
    if width > budget.max_bitvector_width {
        return Err(SmtValidationError::WorkBudgetExceeded {
            resource: SmtWorkResource::BitVectorWidth,
            required: u64::from(width),
            limit: u64::from(budget.max_bitvector_width),
        });
    }
    Ok(())
}

fn ensure_numeral_within_budget(
    bits: u64,
    budget: &SmtWorkBudget,
) -> Result<(), SmtValidationError> {
    if bits > budget.max_numeral_bits {
        return Err(SmtValidationError::WorkBudgetExceeded {
            resource: SmtWorkResource::NumeralBits,
            required: bits,
            limit: budget.max_numeral_bits,
        });
    }
    Ok(())
}

fn charge_node(
    demand: &mut SmtWorkDemand,
    budget: &SmtWorkBudget,
) -> Result<(), SmtValidationError> {
    demand.ast_nodes =
        demand
            .ast_nodes
            .checked_add(1)
            .ok_or(SmtValidationError::WorkBudgetExceeded {
                resource: SmtWorkResource::AstNodes,
                required: u64::MAX,
                limit: budget.max_ast_nodes,
            })?;
    if demand.ast_nodes > budget.max_ast_nodes {
        return Err(SmtValidationError::WorkBudgetExceeded {
            resource: SmtWorkResource::AstNodes,
            required: demand.ast_nodes,
            limit: budget.max_ast_nodes,
        });
    }
    Ok(())
}

fn charge_numeral(
    demand: &mut SmtWorkDemand,
    bits: u64,
    budget: &SmtWorkBudget,
) -> Result<(), SmtValidationError> {
    demand.numeral_bits =
        demand
            .numeral_bits
            .checked_add(bits)
            .ok_or(SmtValidationError::WorkBudgetExceeded {
                resource: SmtWorkResource::NumeralBits,
                required: u64::MAX,
                limit: budget.max_numeral_bits,
            })?;
    ensure_numeral_within_budget(demand.numeral_bits, budget)
}

fn charge_width(
    demand: &mut SmtWorkDemand,
    width: u32,
    budget: &SmtWorkBudget,
) -> Result<(), SmtValidationError> {
    checked_width(width)?;
    ensure_width_within_budget(width, budget)?;
    demand.max_bitvector_width = demand.max_bitvector_width.max(width);
    Ok(())
}

fn register_variable(
    signature: &mut SmtSignature,
    name: &str,
    sort: SmtSort,
) -> Result<(), SmtValidationError> {
    if let Some(first) = signature.variables.get(name) {
        if first != &sort {
            return Err(SmtValidationError::VariableSortConflict {
                name: name.to_string(),
                first: first.clone(),
                second: sort,
            });
        }
        return Ok(());
    }
    signature.variables.insert(name.to_string(), sort);
    Ok(())
}

fn infer_term_sort(
    term: &SmtTerm,
    signature: &mut SmtSignature,
    demand: &mut SmtWorkDemand,
    budget: &SmtWorkBudget,
) -> Result<SmtSort, SmtValidationError> {
    enum Task<'term> {
        Visit(&'term SmtTerm),
        Binary(&'static str),
    }

    let mut tasks = vec![Task::Visit(term)];
    let mut sorts = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(term) => {
                charge_node(demand, budget)?;
                match term {
                    SmtTerm::IntLit(value) => {
                        charge_numeral(demand, value.bits().max(1), budget)?;
                        sorts.push(SmtSort::Int);
                    },
                    SmtTerm::IntVar(name) => {
                        register_variable(signature, name, SmtSort::Int)?;
                        sorts.push(SmtSort::Int);
                    },
                    SmtTerm::BvLit(value, width) => {
                        charge_numeral(demand, value.bits().max(1), budget)?;
                        charge_width(demand, *width, budget)?;
                        sorts.push(SmtSort::BitVector(*width));
                    },
                    SmtTerm::BvVar(name, width) => {
                        charge_width(demand, *width, budget)?;
                        let sort = SmtSort::BitVector(*width);
                        register_variable(signature, name, sort.clone())?;
                        sorts.push(sort);
                    },
                    SmtTerm::Add(left, right) => {
                        tasks.push(Task::Binary("addition"));
                        tasks.push(Task::Visit(right));
                        tasks.push(Task::Visit(left));
                    },
                    SmtTerm::Sub(left, right) => {
                        tasks.push(Task::Binary("subtraction"));
                        tasks.push(Task::Visit(right));
                        tasks.push(Task::Visit(left));
                    },
                    SmtTerm::Scale(coefficient, inner) => {
                        charge_numeral(demand, coefficient.bits().max(1), budget)?;
                        tasks.push(Task::Visit(inner));
                    },
                }
            },
            Task::Binary(operation) => {
                let right = sorts
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant { operation })?;
                let left = sorts
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant { operation })?;
                if left != right {
                    return Err(SmtValidationError::ArithmeticSortMismatch {
                        operation,
                        left,
                        right,
                    });
                }
                sorts.push(left);
            },
        }
    }
    if sorts.len() != 1 {
        return Err(SmtValidationError::InternalSortInvariant { operation: "term validation" });
    }
    Ok(sorts.pop().expect("length checked"))
}

fn validate_constraints(
    asserts: &[SmtConstraint],
    budget: &SmtWorkBudget,
) -> Result<SmtValidationReport, SmtValidationError> {
    let mut signature = SmtSignature::default();
    let mut demand = SmtWorkDemand::default();
    let mut tasks: Vec<&SmtConstraint> = asserts.iter().rev().collect();
    while let Some(constraint) = tasks.pop() {
        charge_node(&mut demand, budget)?;
        match constraint {
            SmtConstraint::True | SmtConstraint::False => {},
            SmtConstraint::BoolVar(name) => {
                register_variable(&mut signature, name, SmtSort::Bool)?;
            },
            SmtConstraint::Eq(left, right)
            | SmtConstraint::Le(left, right)
            | SmtConstraint::Lt(left, right)
            | SmtConstraint::Ge(left, right)
            | SmtConstraint::Gt(left, right) => {
                let left_sort = infer_term_sort(left, &mut signature, &mut demand, budget)?;
                let right_sort = infer_term_sort(right, &mut signature, &mut demand, budget)?;
                if left_sort != right_sort {
                    return Err(SmtValidationError::ComparisonSortMismatch {
                        left: left_sort,
                        right: right_sort,
                    });
                }
            },
            SmtConstraint::Not(inner) => tasks.push(inner),
            SmtConstraint::And(left, right) | SmtConstraint::Or(left, right) => {
                tasks.push(right);
                tasks.push(left);
            },
        }
    }
    Ok(SmtValidationReport { signature, demand })
}

/// Validate one untrusted formula and return its deterministic variable signature.
///
/// This pass is iterative, so adversarially deep terms and constraints consume heap
/// worklists rather than the native call stack.
pub fn validate_constraint(constraint: &SmtConstraint) -> Result<SmtSignature, SmtValidationError> {
    validate_constraint_with_budget(constraint, &SmtWorkBudget::default())
        .map(|report| report.signature)
}

/// Validate and charge one formula under an explicit resource policy.
pub fn validate_constraint_with_budget(
    constraint: &SmtConstraint,
    budget: &SmtWorkBudget,
) -> Result<SmtValidationReport, SmtValidationError> {
    validate_constraints(std::slice::from_ref(constraint), budget)
}

/// Accumulated assertions plus the tri-state of the last check.
#[derive(Clone, Debug)]
pub struct SmtStore {
    /// The asserted guard constraints (conjoined).
    pub asserts: Vec<SmtConstraint>,
    /// Tri-state result of the most recent solve over `asserts`.
    pub status: Sat3,
}

// ══════════════════════════════════════════════════════════════════════════════
// Z3Theory
// ══════════════════════════════════════════════════════════════════════════════

/// A [`ConstraintTheory`] backed by the in-process Z3 library.
///
/// Deliberately implements **only** [`ConstraintTheory`] — never
/// [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra) / `RejectSafeAlgebra` /
/// `HeytingAlgebra`. Satisfiability is exposed through the Sat3-only
/// [`is_satisfiable_3v`] / [`checked_witness`] free functions, never a classical cap.
#[derive(Clone, Debug)]
pub struct Z3Theory {
    /// Per-check solver timeout in milliseconds (`0` = no timeout).
    pub timeout_ms: u32,
    /// Deterministic preflight and solver resource policy.
    pub work_budget: SmtWorkBudget,
}

impl Default for Z3Theory {
    fn default() -> Self {
        Z3Theory {
            timeout_ms: 5_000,
            work_budget: SmtWorkBudget::default(),
        }
    }
}

/// Runtime probe: can a Z3 `Context` be constructed? Cached after the first call;
/// never panics (a missing/incompatible libz3 yields `false` rather than aborting).
pub fn z3_available() -> bool {
    static AVAIL: OnceLock<bool> = OnceLock::new();
    *AVAIL.get_or_init(|| {
        std::panic::catch_unwind(|| {
            let cfg = z3::Config::new();
            let _ctx = z3::Context::new(&cfg);
            true
        })
        .unwrap_or(false)
    })
}

impl Z3Theory {
    /// Construct a theory iff Z3 is available at runtime; otherwise `None`.
    pub fn new() -> Option<Self> {
        z3_available().then(Z3Theory::default)
    }

    /// Solve `asserts` for satisfiability, optionally extracting a model on `Sat`.
    fn solve(&self, asserts: &[SmtConstraint], want_model: bool) -> (Sat3, Option<SmtModel>) {
        let validation = match validate_constraints(asserts, &self.work_budget) {
            Ok(validation) => validation,
            Err(_) => return (Sat3::DontKnow, None),
        };
        let mut cfg = z3::Config::new();
        if self.timeout_ms > 0 {
            cfg.set_timeout_msec(self.timeout_ms as u64);
        }
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        if self.work_budget.solver_rlimit > 0 {
            let mut parameters = z3::Params::new(&ctx);
            parameters.set_u32("rlimit", self.work_budget.solver_rlimit);
            solver.set_params(&parameters);
        }
        let mut env = Z3Env::new(&ctx);
        for c in asserts {
            let Ok(b) = env.constraint(c) else {
                return (Sat3::DontKnow, None);
            };
            solver.assert(&b);
        }
        match solver.check() {
            z3::SatResult::Unsat => (Sat3::Unsat, None),
            z3::SatResult::Unknown => (Sat3::DontKnow, None),
            z3::SatResult::Sat => {
                let model = if want_model {
                    solver.get_model().and_then(|model| {
                        env.extract_model(&model, &validation.signature, &self.work_budget)
                            .ok()
                    })
                } else {
                    None
                };
                (Sat3::Sat, model)
            },
        }
    }
}

impl ConstraintTheory for Z3Theory {
    type Constraint = SmtConstraint;
    type Assignment = SmtModel;
    type Store = SmtStore;

    fn empty_store(&self) -> Self::Store {
        // The empty conjunction is trivially satisfiable.
        SmtStore { asserts: Vec::new(), status: Sat3::Sat }
    }

    fn propagate(&self, store: &Self::Store, c: &Self::Constraint) -> Option<Self::Store> {
        let mut asserts = store.asserts.clone();
        asserts.push(c.clone());
        let (status, _) = self.solve(&asserts, false);
        match status {
            // A proven Unsat is the ONLY inconsistency. `Unknown` (DontKnow) is kept
            // as "possibly satisfiable" — sound for the over-approximating propagation
            // channel.
            Sat3::Unsat => None,
            Sat3::Sat | Sat3::DontKnow => Some(SmtStore { asserts, status }),
        }
    }

    fn is_consistent(&self, store: &Self::Store) -> bool {
        store.status != Sat3::Unsat
    }

    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment> {
        // A witness is produced ONLY from a definitely-`Sat` store — never from
        // `DontKnow` (an undecided guard must not fabricate a model).
        match store.status {
            Sat3::Sat => self.solve(&store.asserts, true).1,
            Sat3::Unsat | Sat3::DontKnow => None,
        }
    }

    fn label(&self, _store: &Self::Store) -> LogicStream<Self::Constraint> {
        // Z3 decides ground guards by `check-sat`; propagation is the oracle, so no
        // explicit labeling search is generated (cf. the decidable-theory convention).
        LogicStream::empty()
    }

    fn evaluate(&self, c: &Self::Constraint, assignment: &Self::Assignment) -> bool {
        eval_constraint(c, assignment)
    }

    fn evaluate_checked(
        &self,
        c: &Self::Constraint,
        assignment: &Self::Assignment,
    ) -> Option<bool> {
        eval_constraint_checked_with_budget(c, assignment, &self.work_budget).ok()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sat3-only public satisfiability API (the OSLF-Phase-8 soundness contract)
// ══════════════════════════════════════════════════════════════════════════════

/// Three-valued satisfiability of a single guard constraint via Z3.
///
/// This is the **only** sanctioned satisfiability entrypoint for the SMT backend.
/// The solver's `Sat` / `Unsat` / `Unknown` results flow straight through as
/// [`Sat3::Sat`] / [`Sat3::Unsat`] / [`Sat3::DontKnow`] — **`DontKnow` is never
/// collapsed** to `Sat` or `Unsat`. This mirrors
/// [`crate::behavioral_algebra`]'s reject-safe `is_satisfiable_3v`: an undecided
/// guard is reported honestly (tier `T3`), never as a wrong classical answer.
///
/// For Boolean combinations of independent satisfiability verdicts, compose with
/// [`Sat3::and`] / [`Sat3::or`] (Kleene strong connectives) rather than collapsing to
/// `bool` first.
pub fn is_satisfiable_3v(theory: &Z3Theory, c: &SmtConstraint) -> Sat3 {
    theory.solve(std::slice::from_ref(c), false).0
}

/// A *certificate-checked* witness for a guard constraint.
///
/// Returns a model **only** when the solver answers [`Sat3::Sat`] **and** the
/// returned assignment re-satisfies `c` under the pure [`eval_constraint`] evaluator
/// (a certificate check). On [`Sat3::Unsat`], [`Sat3::DontKnow`], a missing model, or
/// a model that fails to re-confirm the constraint, returns `None` — so an undecided
/// or unverifiable result never fabricates a witness. Cf. `GuardTierCertificate`.
pub fn checked_witness(theory: &Z3Theory, c: &SmtConstraint) -> Option<SmtModel> {
    let (status, model) = theory.solve(std::slice::from_ref(c), true);
    match status {
        Sat3::Sat => {
            let m = model?;
            // Certificate check: the model must re-satisfy the constraint under the
            // independent pure evaluator before we trust it.
            eval_constraint_checked_with_budget(c, &m, &theory.work_budget)
                .ok()?
                .then_some(m)
        },
        Sat3::Unsat | Sat3::DontKnow => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pure evaluator (model checking a constraint under an assignment)
// ══════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug, PartialEq, Eq)]
enum SmtValue {
    Int(BigInt),
    BitVector(SmtBitVector),
}

fn bigint_modulus(value: &BigInt, modulus: &BigUint) -> BigUint {
    let modulus = BigInt::from(modulus.clone());
    let mut remainder = value % &modulus;
    if remainder.sign() == Sign::Minus {
        remainder += &modulus;
    }
    remainder
        .to_biguint()
        .expect("non-negative residue must convert to BigUint")
}

fn checked_model_bitvector(
    name: &str,
    expected_width: u32,
    value: &SmtBitVector,
    budget: &SmtWorkBudget,
) -> Result<SmtBitVector, SmtValidationError> {
    let width = checked_width(expected_width)?;
    ensure_width_within_budget(expected_width, budget)?;
    ensure_numeral_within_budget(value.value.bits().max(1), budget)?;
    if value.width != expected_width {
        return Err(SmtValidationError::ModelBitVectorWidthMismatch {
            name: name.to_string(),
            expected: expected_width,
            actual: value.width,
        });
    }
    if value.value >= bitvector_modulus(width) {
        return Err(SmtValidationError::ModelBitVectorOutOfRange {
            name: name.to_string(),
            width: expected_width,
        });
    }
    Ok(value.clone())
}

/// Evaluate a validated [`SmtTerm`] under an assignment without truncation,
/// signedness confusion, implicit zero bindings, or native-stack recursion.
fn eval_term_checked(
    t: &SmtTerm,
    m: &SmtModel,
    budget: &SmtWorkBudget,
) -> Result<SmtValue, SmtValidationError> {
    enum Task<'term> {
        Visit(&'term SmtTerm),
        Add,
        Sub,
        Scale(&'term BigInt),
    }

    let mut tasks = vec![Task::Visit(t)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(SmtTerm::IntLit(value)) => values.push(SmtValue::Int(value.clone())),
            Task::Visit(SmtTerm::IntVar(name)) => {
                let value = m.ints.get(name).cloned().ok_or_else(|| {
                    SmtValidationError::MissingModelBinding {
                        name: name.clone(),
                        expected: SmtSort::Int,
                    }
                })?;
                values.push(SmtValue::Int(value));
            },
            Task::Visit(SmtTerm::BvLit(value, width)) => {
                values.push(SmtValue::BitVector(SmtBitVector::new_with_budget(
                    value.clone(),
                    *width,
                    budget,
                )?));
            },
            Task::Visit(SmtTerm::BvVar(name, width)) => {
                let value =
                    m.bvs
                        .get(name)
                        .ok_or_else(|| SmtValidationError::MissingModelBinding {
                            name: name.clone(),
                            expected: SmtSort::BitVector(*width),
                        })?;
                values.push(SmtValue::BitVector(checked_model_bitvector(
                    name, *width, value, budget,
                )?));
            },
            Task::Visit(SmtTerm::Add(left, right)) => {
                tasks.push(Task::Add);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(SmtTerm::Sub(left, right)) => {
                tasks.push(Task::Sub);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(SmtTerm::Scale(coefficient, term)) => {
                tasks.push(Task::Scale(coefficient));
                tasks.push(Task::Visit(term));
            },
            Task::Add => {
                let right = values
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant {
                        operation: "evaluation addition RHS",
                    })?;
                let left = values
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant {
                        operation: "evaluation addition LHS",
                    })?;
                values.push(match (left, right) {
                    (SmtValue::Int(left), SmtValue::Int(right)) => SmtValue::Int(left + right),
                    (SmtValue::BitVector(left), SmtValue::BitVector(right))
                        if left.width == right.width =>
                    {
                        let width = checked_width(left.width)?;
                        SmtValue::BitVector(SmtBitVector {
                            value: (left.value + right.value) % bitvector_modulus(width),
                            width: left.width,
                        })
                    },
                    _ => {
                        return Err(SmtValidationError::InternalSortInvariant {
                            operation: "evaluation addition",
                        });
                    },
                });
            },
            Task::Sub => {
                let right = values
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant {
                        operation: "evaluation subtraction RHS",
                    })?;
                let left = values
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant {
                        operation: "evaluation subtraction LHS",
                    })?;
                values.push(match (left, right) {
                    (SmtValue::Int(left), SmtValue::Int(right)) => SmtValue::Int(left - right),
                    (SmtValue::BitVector(left), SmtValue::BitVector(right))
                        if left.width == right.width =>
                    {
                        let width = checked_width(left.width)?;
                        let modulus = bitvector_modulus(width);
                        SmtValue::BitVector(SmtBitVector {
                            value: (left.value + &modulus - right.value) % &modulus,
                            width: left.width,
                        })
                    },
                    _ => {
                        return Err(SmtValidationError::InternalSortInvariant {
                            operation: "evaluation subtraction",
                        });
                    },
                });
            },
            Task::Scale(coefficient) => {
                let value = values
                    .pop()
                    .ok_or(SmtValidationError::InternalSortInvariant {
                        operation: "evaluation scale operand",
                    })?;
                values.push(match value {
                    SmtValue::Int(value) => SmtValue::Int(coefficient * value),
                    SmtValue::BitVector(value) => {
                        let width = checked_width(value.width)?;
                        let modulus = bitvector_modulus(width);
                        let coefficient = bigint_modulus(coefficient, &modulus);
                        SmtValue::BitVector(SmtBitVector {
                            value: (coefficient * value.value) % modulus,
                            width: value.width,
                        })
                    },
                });
            },
        }
    }
    if values.len() != 1 {
        return Err(SmtValidationError::InternalSortInvariant { operation: "term evaluation" });
    }
    Ok(values.pop().expect("length checked"))
}

fn compare_values(
    left: SmtValue,
    right: SmtValue,
    comparison: Cmp,
) -> Result<bool, SmtValidationError> {
    match (left, right) {
        (SmtValue::Int(left), SmtValue::Int(right)) => Ok(match comparison {
            Cmp::Eq => left == right,
            Cmp::Le => left <= right,
            Cmp::Lt => left < right,
            Cmp::Ge => left >= right,
            Cmp::Gt => left > right,
        }),
        (SmtValue::BitVector(left), SmtValue::BitVector(right)) if left.width == right.width => {
            Ok(match comparison {
                Cmp::Eq => left.value == right.value,
                Cmp::Le => left.value <= right.value,
                Cmp::Lt => left.value < right.value,
                Cmp::Ge => left.value >= right.value,
                Cmp::Gt => left.value > right.value,
            })
        },
        _ => Err(SmtValidationError::InternalSortInvariant { operation: "comparison evaluation" }),
    }
}

/// Evaluate an [`SmtConstraint`] under an assignment with explicit malformed and
/// incomplete-model errors.
pub fn eval_constraint_checked(
    c: &SmtConstraint,
    m: &SmtModel,
) -> Result<bool, SmtValidationError> {
    eval_constraint_checked_with_budget(c, m, &SmtWorkBudget::default())
}

/// Checked independent model evaluation under an explicit work budget.
pub fn eval_constraint_checked_with_budget(
    c: &SmtConstraint,
    m: &SmtModel,
    budget: &SmtWorkBudget,
) -> Result<bool, SmtValidationError> {
    // Validate the complete formula before short-circuiting. Therefore an invalid
    // right branch cannot be hidden behind `false && _` or `true || _`, and negating
    // malformed syntax remains malformed rather than becoming accepted.
    validate_constraint_with_budget(c, budget)?;

    enum Task<'constraint> {
        Visit(&'constraint SmtConstraint),
        Not,
        AndRight(&'constraint SmtConstraint),
        OrRight(&'constraint SmtConstraint),
    }

    let mut tasks = vec![Task::Visit(c)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(SmtConstraint::True) => values.push(true),
            Task::Visit(SmtConstraint::False) => values.push(false),
            Task::Visit(SmtConstraint::BoolVar(name)) => {
                values.push(m.bools.get(name).copied().ok_or_else(|| {
                    SmtValidationError::MissingModelBinding {
                        name: name.clone(),
                        expected: SmtSort::Bool,
                    }
                })?);
            },
            Task::Visit(SmtConstraint::Eq(left, right)) => {
                values.push(compare_values(
                    eval_term_checked(left, m, budget)?,
                    eval_term_checked(right, m, budget)?,
                    Cmp::Eq,
                )?);
            },
            Task::Visit(SmtConstraint::Le(left, right)) => {
                values.push(compare_values(
                    eval_term_checked(left, m, budget)?,
                    eval_term_checked(right, m, budget)?,
                    Cmp::Le,
                )?);
            },
            Task::Visit(SmtConstraint::Lt(left, right)) => {
                values.push(compare_values(
                    eval_term_checked(left, m, budget)?,
                    eval_term_checked(right, m, budget)?,
                    Cmp::Lt,
                )?);
            },
            Task::Visit(SmtConstraint::Ge(left, right)) => {
                values.push(compare_values(
                    eval_term_checked(left, m, budget)?,
                    eval_term_checked(right, m, budget)?,
                    Cmp::Ge,
                )?);
            },
            Task::Visit(SmtConstraint::Gt(left, right)) => {
                values.push(compare_values(
                    eval_term_checked(left, m, budget)?,
                    eval_term_checked(right, m, budget)?,
                    Cmp::Gt,
                )?);
            },
            Task::Visit(SmtConstraint::Not(inner)) => {
                tasks.push(Task::Not);
                tasks.push(Task::Visit(inner));
            },
            Task::Visit(SmtConstraint::And(left, right)) => {
                tasks.push(Task::AndRight(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(SmtConstraint::Or(left, right)) => {
                tasks.push(Task::OrRight(right));
                tasks.push(Task::Visit(left));
            },
            Task::Not => {
                let value = values.pop().expect("SMT evaluator lost negated value");
                values.push(!value);
            },
            Task::AndRight(right) => {
                if values.pop().expect("SMT evaluator lost conjunction LHS") {
                    tasks.push(Task::Visit(right));
                } else {
                    values.push(false);
                }
            },
            Task::OrRight(right) => {
                if values.pop().expect("SMT evaluator lost disjunction LHS") {
                    values.push(true);
                } else {
                    tasks.push(Task::Visit(right));
                }
            },
        }
    }
    if values.len() != 1 {
        return Err(SmtValidationError::InternalSortInvariant {
            operation: "constraint evaluation",
        });
    }
    Ok(values.pop().expect("length checked"))
}

/// Compatibility projection for Boolean-only callers. Any malformed formula or
/// incomplete/ill-typed assignment fails closed. Security-sensitive callers should
/// use [`eval_constraint_checked`] so they retain the reason for indeterminacy.
pub fn eval_constraint(c: &SmtConstraint, m: &SmtModel) -> bool {
    eval_constraint_checked(c, m).unwrap_or(false)
}

// ══════════════════════════════════════════════════════════════════════════════
// Z3 translation environment
// ══════════════════════════════════════════════════════════════════════════════

/// A translated numeric term — either an integer or a fixed-width bitvector AST.
enum Z3Num<'ctx> {
    Int(z3::ast::Int<'ctx>),
    Bv(z3::ast::BV<'ctx>),
}

/// Builds Z3 ASTs from the self-contained constraint AST, caching declared variables
/// so repeated occurrences share one Z3 constant.
struct Z3Env<'ctx> {
    ctx: &'ctx z3::Context,
    ints: BTreeMap<String, z3::ast::Int<'ctx>>,
    bvs: BTreeMap<String, (z3::ast::BV<'ctx>, u32)>,
    bools: BTreeMap<String, z3::ast::Bool<'ctx>>,
}

impl<'ctx> Z3Env<'ctx> {
    fn new(ctx: &'ctx z3::Context) -> Self {
        Z3Env {
            ctx,
            ints: BTreeMap::new(),
            bvs: BTreeMap::new(),
            bools: BTreeMap::new(),
        }
    }

    fn int_var(&mut self, name: &str) -> z3::ast::Int<'ctx> {
        self.ints
            .entry(name.to_string())
            .or_insert_with(|| z3::ast::Int::new_const(self.ctx, name))
            .clone()
    }

    fn bv_var(&mut self, name: &str, width: u32) -> z3::ast::BV<'ctx> {
        self.bvs
            .entry(name.to_string())
            .or_insert_with(|| (z3::ast::BV::new_const(self.ctx, name, width), width))
            .0
            .clone()
    }

    fn bool_var(&mut self, name: &str) -> z3::ast::Bool<'ctx> {
        self.bools
            .entry(name.to_string())
            .or_insert_with(|| z3::ast::Bool::new_const(self.ctx, name))
            .clone()
    }

    fn term(&mut self, t: &SmtTerm) -> Result<Z3Num<'ctx>, SmtValidationError> {
        enum Task<'term> {
            Visit(&'term SmtTerm),
            Add,
            Sub,
            Scale(&'term BigInt),
        }

        let mut tasks = vec![Task::Visit(t)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SmtTerm::IntLit(value)) => {
                    let value = z3::ast::Int::from_str(self.ctx, &value.to_string())
                        .ok_or(SmtValidationError::SolverNumeralEncoding)?;
                    values.push(Z3Num::Int(value));
                },
                Task::Visit(SmtTerm::IntVar(name)) => {
                    values.push(Z3Num::Int(self.int_var(name)));
                },
                Task::Visit(SmtTerm::BvLit(value, width)) => {
                    let width = checked_width(*width)?;
                    let value = value % bitvector_modulus(width);
                    let value = z3::ast::BV::from_str(self.ctx, width.get(), &value.to_string())
                        .ok_or(SmtValidationError::SolverNumeralEncoding)?;
                    values.push(Z3Num::Bv(value));
                },
                Task::Visit(SmtTerm::BvVar(name, width)) => {
                    values.push(Z3Num::Bv(self.bv_var(name, *width)));
                },
                Task::Visit(SmtTerm::Add(left, right)) => {
                    tasks.push(Task::Add);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtTerm::Sub(left, right)) => {
                    tasks.push(Task::Sub);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtTerm::Scale(coefficient, term)) => {
                    tasks.push(Task::Scale(coefficient));
                    tasks.push(Task::Visit(term));
                },
                Task::Add | Task::Sub => {
                    let right = values
                        .pop()
                        .ok_or(SmtValidationError::InternalSortInvariant {
                            operation: "Z3 binary RHS",
                        })?;
                    let left = values
                        .pop()
                        .ok_or(SmtValidationError::InternalSortInvariant {
                            operation: "Z3 binary LHS",
                        })?;
                    let result = match (task, left, right) {
                        (Task::Add, Z3Num::Int(x), Z3Num::Int(y)) => Z3Num::Int(x + y),
                        (Task::Sub, Z3Num::Int(x), Z3Num::Int(y)) => Z3Num::Int(x - y),
                        (Task::Add, Z3Num::Bv(x), Z3Num::Bv(y)) if x.get_size() == y.get_size() => {
                            Z3Num::Bv(x.bvadd(&y))
                        },
                        (Task::Sub, Z3Num::Bv(x), Z3Num::Bv(y)) if x.get_size() == y.get_size() => {
                            Z3Num::Bv(x.bvsub(&y))
                        },
                        _ => {
                            return Err(SmtValidationError::InternalSortInvariant {
                                operation: "Z3 binary translation",
                            });
                        },
                    };
                    values.push(result);
                },
                Task::Scale(coefficient) => {
                    let value = values.pop().expect("SMT Z3 translation lost scale operand");
                    let result = match value {
                        Z3Num::Int(value) => {
                            let coefficient =
                                z3::ast::Int::from_str(self.ctx, &coefficient.to_string())
                                    .ok_or(SmtValidationError::SolverNumeralEncoding)?;
                            Z3Num::Int(coefficient * value)
                        },
                        Z3Num::Bv(value) => {
                            let width = checked_width(value.get_size())?;
                            let modulus = bitvector_modulus(width);
                            let coefficient = bigint_modulus(coefficient, &modulus);
                            let coefficient = z3::ast::BV::from_str(
                                self.ctx,
                                width.get(),
                                &coefficient.to_string(),
                            )
                            .ok_or(SmtValidationError::SolverNumeralEncoding)?;
                            Z3Num::Bv(coefficient.bvmul(&value))
                        },
                    };
                    values.push(result);
                },
            }
        }
        if values.len() != 1 {
            return Err(SmtValidationError::InternalSortInvariant {
                operation: "Z3 term translation",
            });
        }
        Ok(values.pop().expect("length checked"))
    }

    fn constraint(&mut self, c: &SmtConstraint) -> Result<z3::ast::Bool<'ctx>, SmtValidationError> {
        enum Task<'constraint> {
            Visit(&'constraint SmtConstraint),
            Not,
            Binary(Binary),
        }

        enum Binary {
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(c)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SmtConstraint::True) => {
                    values.push(z3::ast::Bool::from_bool(self.ctx, true));
                },
                Task::Visit(SmtConstraint::False) => {
                    values.push(z3::ast::Bool::from_bool(self.ctx, false));
                },
                Task::Visit(SmtConstraint::BoolVar(name)) => values.push(self.bool_var(name)),
                Task::Visit(SmtConstraint::Eq(left, right)) => {
                    values.push(self.compare(left, right, Cmp::Eq)?);
                },
                Task::Visit(SmtConstraint::Le(left, right)) => {
                    values.push(self.compare(left, right, Cmp::Le)?);
                },
                Task::Visit(SmtConstraint::Lt(left, right)) => {
                    values.push(self.compare(left, right, Cmp::Lt)?);
                },
                Task::Visit(SmtConstraint::Ge(left, right)) => {
                    values.push(self.compare(left, right, Cmp::Ge)?);
                },
                Task::Visit(SmtConstraint::Gt(left, right)) => {
                    values.push(self.compare(left, right, Cmp::Gt)?);
                },
                Task::Visit(SmtConstraint::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(SmtConstraint::And(left, right)) => {
                    tasks.push(Task::Binary(Binary::And));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtConstraint::Or(left, right)) => {
                    tasks.push(Task::Binary(Binary::Or));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Not => {
                    let value = values.pop().expect("SMT Z3 translation lost negated value");
                    values.push(value.not());
                },
                Task::Binary(binary) => {
                    let right = values.pop().expect("SMT Z3 translation lost boolean RHS");
                    let left = values.pop().expect("SMT Z3 translation lost boolean LHS");
                    let value = match binary {
                        Binary::And => z3::ast::Bool::and(self.ctx, &[&left, &right]),
                        Binary::Or => z3::ast::Bool::or(self.ctx, &[&left, &right]),
                    };
                    values.push(value);
                },
            }
        }
        if values.len() != 1 {
            return Err(SmtValidationError::InternalSortInvariant {
                operation: "Z3 constraint translation",
            });
        }
        Ok(values.pop().expect("length checked"))
    }

    fn compare(
        &mut self,
        a: &SmtTerm,
        b: &SmtTerm,
        cmp: Cmp,
    ) -> Result<z3::ast::Bool<'ctx>, SmtValidationError> {
        let comparison = match (self.term(a)?, self.term(b)?) {
            (Z3Num::Int(x), Z3Num::Int(y)) => match cmp {
                Cmp::Eq => x._eq(&y),
                Cmp::Le => x.le(&y),
                Cmp::Lt => x.lt(&y),
                Cmp::Ge => x.ge(&y),
                Cmp::Gt => x.gt(&y),
            },
            (Z3Num::Bv(x), Z3Num::Bv(y)) if x.get_size() == y.get_size() => match cmp {
                Cmp::Eq => x._eq(&y),
                Cmp::Le => x.bvule(&y),
                Cmp::Lt => x.bvult(&y),
                Cmp::Ge => x.bvuge(&y),
                Cmp::Gt => x.bvugt(&y),
            },
            _ => {
                return Err(SmtValidationError::InternalSortInvariant {
                    operation: "Z3 comparison translation",
                });
            },
        };
        Ok(comparison)
    }

    fn extract_model(
        &self,
        model: &z3::Model<'ctx>,
        signature: &SmtSignature,
        budget: &SmtWorkBudget,
    ) -> Result<SmtModel, SmtValidationError> {
        let mut out = SmtModel::default();
        for (name, sort) in &signature.variables {
            match sort {
                SmtSort::Bool => {
                    let value = self
                        .bools
                        .get(name)
                        .and_then(|ast| model.eval(ast, true))
                        .and_then(|ast| ast.as_bool())
                        .ok_or_else(|| SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: SmtSort::Bool,
                        })?;
                    out.bools.insert(name.clone(), value);
                },
                SmtSort::Int => {
                    let rendered = self
                        .ints
                        .get(name)
                        .and_then(|ast| model.eval(ast, true))
                        .map(|ast| ast.to_string())
                        .ok_or_else(|| SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: SmtSort::Int,
                        })?;
                    let value = parse_z3_integer_numeral(&rendered).ok_or_else(|| {
                        SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: SmtSort::Int,
                        }
                    })?;
                    ensure_numeral_within_budget(value.bits().max(1), budget)?;
                    out.ints.insert(name.clone(), value);
                },
                SmtSort::BitVector(width) => {
                    let ast = self.bvs.get(name).map(|(ast, _)| ast).ok_or_else(|| {
                        SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: sort.clone(),
                        }
                    })?;
                    let rendered = model
                        .eval(&ast.to_int(false), true)
                        .map(|ast| ast.to_string())
                        .ok_or_else(|| SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: sort.clone(),
                        })?;
                    let value = parse_z3_integer_numeral(&rendered)
                        .and_then(|value| value.to_biguint())
                        .ok_or_else(|| SmtValidationError::SolverModelNumeral {
                            name: name.clone(),
                            expected: sort.clone(),
                        })?;
                    out.bvs.insert(
                        name.clone(),
                        SmtBitVector::new_with_budget(value, *width, budget)?,
                    );
                },
            }
        }
        Ok(out)
    }
}

fn parse_z3_integer_numeral(rendered: &str) -> Option<BigInt> {
    let rendered = rendered.trim();
    if let Ok(value) = BigInt::from_str(rendered) {
        return Some(value);
    }
    let inner = rendered.strip_prefix("(- ")?.strip_suffix(')')?.trim();
    BigInt::from_str(inner).ok().map(|value| -value)
}

/// Comparison operator selector for [`Z3Env::compare`].
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ivar(s: &str) -> SmtTerm {
        SmtTerm::IntVar(s.to_string())
    }
    fn ilit(n: i64) -> SmtTerm {
        SmtTerm::int(n)
    }

    #[test]
    fn z3_is_available() {
        // System libz3 is present in this environment.
        assert!(z3_available());
    }

    #[test]
    fn satisfiable_linear_arithmetic_yields_witness() {
        let th = Z3Theory::new().expect("z3 available");
        // x > 3 ∧ x < 7
        let s = th.empty_store();
        let s = th
            .propagate(&s, &SmtConstraint::Gt(ivar("x"), ilit(3)))
            .expect("consistent");
        let s = th
            .propagate(&s, &SmtConstraint::Lt(ivar("x"), ilit(7)))
            .expect("consistent");
        assert_eq!(s.status, Sat3::Sat);
        assert!(th.is_consistent(&s));
        let m = th.witness(&s).expect("witness on Sat");
        let x = m.ints.get("x").cloned().unwrap_or_default();
        assert!((BigInt::from(4)..=BigInt::from(6)).contains(&x), "x = {x} not in (3,7)");
        // The witness re-satisfies the guard under the pure evaluator.
        assert!(th.evaluate(&SmtConstraint::Gt(ivar("x"), ilit(3)), &m));
        assert!(th.evaluate(&SmtConstraint::Lt(ivar("x"), ilit(7)), &m));
    }

    #[test]
    fn contradiction_is_inconsistent_no_witness() {
        let th = Z3Theory::new().expect("z3 available");
        // x ≥ 5 ∧ x ≤ 2  →  Unsat
        let s = th.empty_store();
        let s = th
            .propagate(&s, &SmtConstraint::Ge(ivar("x"), ilit(5)))
            .expect("consistent so far");
        let r = th.propagate(&s, &SmtConstraint::Le(ivar("x"), ilit(2)));
        assert!(r.is_none(), "contradiction must propagate to None");
    }

    #[test]
    fn bitvector_overflow_wraps() {
        let th = Z3Theory::new().expect("z3 available");
        // (bv8 a) + 1 = 0  is satisfiable at a = 255 (wraparound).
        let a = SmtTerm::BvVar("a".to_string(), 8);
        let sum = SmtTerm::Add(Box::new(a), Box::new(SmtTerm::bit_vector(1u8, 8)));
        let s = th.empty_store();
        let s = th
            .propagate(&s, &SmtConstraint::Eq(sum, SmtTerm::bit_vector(0u8, 8)))
            .expect("wraparound is sat");
        assert_eq!(s.status, Sat3::Sat);
        let m = th.witness(&s).expect("witness");
        assert_eq!(m.bvs.get("a"), Some(&SmtBitVector::new(255u16, 8).expect("valid width")));
    }

    #[test]
    fn theory_algebra_is_satisfiable_3v() {
        // OSLF Phase 8: the SOUND replacement for lling-llang's
        // `theory_algebra_is_boolean_algebra` defect-blessing test. Z3 is reachable
        // ONLY through the Sat3-only `is_satisfiable_3v` / `checked_witness`
        // entrypoints — NEVER a classical `BooleanAlgebra` cap, NEVER routed into SFA
        // complement / determinize / equivalence. `DontKnow` must never collapse to a
        // wrong `Sat`/`Unsat`.
        let th = Z3Theory::new().expect("z3 available");

        // (a) A satisfiable guard: 0 < y < 10 → Sat, with a certificate-checked model.
        let sat = SmtConstraint::And(
            Box::new(SmtConstraint::Gt(ivar("y"), ilit(0))),
            Box::new(SmtConstraint::Lt(ivar("y"), ilit(10))),
        );
        assert_eq!(is_satisfiable_3v(&th, &sat), Sat3::Sat);
        let m = checked_witness(&th, &sat).expect("certificate-checked witness on Sat");
        // The certificate-checked model genuinely satisfies the guard.
        assert!(eval_constraint(&sat, &m));

        // (b) An unsatisfiable guard: y > 10 ∧ y < 0 → Unsat, with NO witness.
        let unsat = SmtConstraint::And(
            Box::new(SmtConstraint::Gt(ivar("y"), ilit(10))),
            Box::new(SmtConstraint::Lt(ivar("y"), ilit(0))),
        );
        assert_eq!(is_satisfiable_3v(&th, &unsat), Sat3::Unsat);
        assert!(checked_witness(&th, &unsat).is_none(), "Unsat must not fabricate a witness");

        // (c) Kleene-strong composition of the two independent verdicts.
        let s3 = is_satisfiable_3v(&th, &sat);
        let u3 = is_satisfiable_3v(&th, &unsat);
        assert_eq!(s3.and(u3), Sat3::Unsat, "Sat ∧ Unsat = Unsat");
        assert_eq!(s3.or(u3), Sat3::Sat, "Sat ∨ Unsat = Sat");

        // (d) The CRITICAL soundness invariant the upstream defect violated: a
        // tight-timeout solve must NEVER silently collapse to a wrong classical
        // answer. Here the guard is genuinely UNSATISFIABLE —
        //   x > 100 ∧ x < 0
        // — so under ANY budget the only two sound verdicts are `Unsat` (proven) or
        // `DontKnow` (budget exhausted before a proof); a `Sat` would be the wrong,
        // over-eager classical answer, and a witness must never be fabricated. We
        // pin the verdict to `≠ Sat` (sound under both decided and undecided outcomes)
        // rather than forcing a particular tri-state, since Z3's actual answer for
        // such a trivial contradiction is build-dependent under a 1 ms budget.
        let hard = SmtConstraint::And(
            Box::new(SmtConstraint::Gt(ivar("x"), ilit(100))),
            Box::new(SmtConstraint::Lt(ivar("x"), ilit(0))),
        );
        let tight = Z3Theory { timeout_ms: 1, ..Z3Theory::default() };
        let verdict = is_satisfiable_3v(&tight, &hard);
        assert_ne!(
            verdict,
            Sat3::Sat,
            "an unsatisfiable guard must never be reported Sat (DontKnow is allowed; Unsat is allowed)"
        );
        // A witness is produced ONLY on a checked `Sat`; never on `Unsat`/`DontKnow`.
        assert!(checked_witness(&tight, &hard).is_none(), "no witness for a non-Sat verdict");
    }

    #[test]
    fn malformed_sorts_are_undetermined_and_fail_closed_even_under_negation() {
        let theory = Z3Theory::new().expect("z3 available");
        let malformed = SmtConstraint::Eq(
            SmtTerm::Add(Box::new(ivar("x")), Box::new(SmtTerm::bit_vector(1u8, 8))),
            ilit(0),
        );
        assert!(matches!(
            validate_constraint(&malformed),
            Err(SmtValidationError::ArithmeticSortMismatch { .. })
        ));
        assert_eq!(is_satisfiable_3v(&theory, &malformed), Sat3::DontKnow);
        assert!(checked_witness(&theory, &malformed).is_none());
        assert!(!eval_constraint(&malformed, &SmtModel::default()));

        let negated = SmtConstraint::Not(Box::new(malformed));
        assert_eq!(is_satisfiable_3v(&theory, &negated), Sat3::DontKnow);
        assert!(checked_witness(&theory, &negated).is_none());
        assert!(!eval_constraint(&negated, &SmtModel::default()));
    }

    #[test]
    fn bitvector_width_and_variable_sort_conflicts_are_rejected() {
        let theory = Z3Theory::new().expect("z3 available");
        let width_mismatch =
            SmtConstraint::Eq(SmtTerm::BvVar("word".into(), 8), SmtTerm::bit_vector(0u8, 16));
        assert!(matches!(
            validate_constraint(&width_mismatch),
            Err(SmtValidationError::ComparisonSortMismatch { .. })
        ));
        assert_eq!(is_satisfiable_3v(&theory, &width_mismatch), Sat3::DontKnow);

        let zero_width =
            SmtConstraint::Eq(SmtTerm::BvVar("empty".into(), 0), SmtTerm::bit_vector(0u8, 0));
        assert_eq!(validate_constraint(&zero_width), Err(SmtValidationError::ZeroBitVectorWidth));
        assert_eq!(is_satisfiable_3v(&theory, &zero_width), Sat3::DontKnow);

        let reused_name = SmtConstraint::And(
            Box::new(SmtConstraint::BoolVar("shared".into())),
            Box::new(SmtConstraint::Eq(SmtTerm::IntVar("shared".into()), ilit(0))),
        );
        assert!(matches!(
            validate_constraint(&reused_name),
            Err(SmtValidationError::VariableSortConflict { .. })
        ));
        assert_eq!(is_satisfiable_3v(&theory, &reused_name), Sat3::DontKnow);

        let reused_bitvector_name = SmtConstraint::And(
            Box::new(SmtConstraint::Eq(
                SmtTerm::BvVar("sized".into(), 8),
                SmtTerm::bit_vector(0u8, 8),
            )),
            Box::new(SmtConstraint::Eq(
                SmtTerm::BvVar("sized".into(), 16),
                SmtTerm::bit_vector(0u8, 16),
            )),
        );
        assert!(matches!(
            validate_constraint(&reused_bitvector_name),
            Err(SmtValidationError::VariableSortConflict { .. })
        ));
        assert_eq!(is_satisfiable_3v(&theory, &reused_bitvector_name), Sat3::DontKnow);
    }

    #[test]
    fn mathematical_integers_and_wide_bitvectors_round_trip_exactly() {
        let theory = Z3Theory::new().expect("z3 available");
        let beyond_i64 = BigInt::from(i64::MAX) + BigInt::one();
        let integer_formula =
            SmtConstraint::Eq(SmtTerm::IntVar("large".into()), SmtTerm::int(beyond_i64.clone()));
        let integer_model = checked_witness(&theory, &integer_formula)
            .expect("arbitrary-precision integer witness");
        assert_eq!(integer_model.ints.get("large"), Some(&beyond_i64));
        assert_eq!(eval_constraint_checked(&integer_formula, &integer_model), Ok(true));

        let below_i64 = BigInt::from(i64::MIN) - BigInt::one();
        let negative_formula =
            SmtConstraint::Eq(SmtTerm::IntVar("negative".into()), SmtTerm::int(below_i64.clone()));
        let negative_model = checked_witness(&theory, &negative_formula)
            .expect("negative arbitrary-precision integer witness");
        assert_eq!(negative_model.ints.get("negative"), Some(&below_i64));
        assert_eq!(eval_constraint_checked(&negative_formula, &negative_model), Ok(true));

        let wide_value = (BigUint::one() << 100usize) + BigUint::from(17u8);
        let bitvector_formula = SmtConstraint::Eq(
            SmtTerm::BvVar("wide".into(), 130),
            SmtTerm::bit_vector(wide_value.clone(), 130),
        );
        let bitvector_model =
            checked_witness(&theory, &bitvector_formula).expect("wide bitvector witness");
        assert_eq!(
            bitvector_model.bvs.get("wide"),
            Some(&SmtBitVector::new(wide_value, 130).expect("positive width"))
        );
        assert_eq!(eval_constraint_checked(&bitvector_formula, &bitvector_model), Ok(true));
    }

    #[test]
    fn bitvector_comparison_is_unsigned_and_arithmetic_is_modular() {
        let unsigned =
            SmtConstraint::Gt(SmtTerm::bit_vector(255u16, 8), SmtTerm::bit_vector(1u8, 8));
        assert_eq!(eval_constraint_checked(&unsigned, &SmtModel::default()), Ok(true));

        let wraps = SmtConstraint::Eq(
            SmtTerm::Add(
                Box::new(SmtTerm::bit_vector(255u16, 8)),
                Box::new(SmtTerm::bit_vector(1u8, 8)),
            ),
            SmtTerm::bit_vector(0u8, 8),
        );
        assert_eq!(eval_constraint_checked(&wraps, &SmtModel::default()), Ok(true));
    }

    #[test]
    fn incomplete_or_width_inconsistent_models_never_validate_certificates() {
        let formula = SmtConstraint::Eq(SmtTerm::IntVar("x".into()), ilit(0));
        assert!(matches!(
            eval_constraint_checked(&formula, &SmtModel::default()),
            Err(SmtValidationError::MissingModelBinding { .. })
        ));
        assert!(!eval_constraint(&formula, &SmtModel::default()));

        let bitvector_formula =
            SmtConstraint::Eq(SmtTerm::BvVar("byte".into(), 8), SmtTerm::bit_vector(0u8, 8));
        let mut wrong_width = SmtModel::default();
        wrong_width
            .bvs
            .insert("byte".into(), SmtBitVector::new(0u8, 16).expect("positive width"));
        assert!(matches!(
            eval_constraint_checked(&bitvector_formula, &wrong_width),
            Err(SmtValidationError::ModelBitVectorWidthMismatch { .. })
        ));
        assert!(!eval_constraint(&bitvector_formula, &wrong_width));
    }

    #[test]
    fn preflight_charges_exact_demand_before_translation() {
        let formula = SmtConstraint::Eq(
            SmtTerm::Add(Box::new(SmtTerm::int(1)), Box::new(ivar("x"))),
            SmtTerm::int(2),
        );
        let budget = SmtWorkBudget {
            max_ast_nodes: 5,
            max_numeral_bits: 3,
            max_bitvector_width: 8,
            solver_rlimit: 1_000,
        };
        let report = validate_constraint_with_budget(&formula, &budget)
            .expect("the exact preflight demand fits");
        assert_eq!(
            report.demand,
            SmtWorkDemand {
                ast_nodes: 5,
                numeral_bits: 3,
                max_bitvector_width: 0
            }
        );
        assert_eq!(report.signature.variables.get("x"), Some(&SmtSort::Int));

        let larger = SmtWorkBudget {
            max_ast_nodes: 50,
            max_numeral_bits: 30,
            max_bitvector_width: 80,
            solver_rlimit: 10_000,
        };
        assert_eq!(
            validate_constraint_with_budget(&formula, &larger)
                .expect("larger budget preserves validation")
                .demand,
            report.demand
        );
    }

    #[test]
    fn every_preflight_exhaustion_mode_is_undetermined_and_fails_closed() {
        let formula =
            SmtConstraint::Eq(SmtTerm::BvVar("word".into(), 16), SmtTerm::bit_vector(0x1ffu16, 16));
        let baseline = SmtWorkBudget {
            max_ast_nodes: 3,
            max_numeral_bits: 9,
            max_bitvector_width: 16,
            solver_rlimit: 10_000,
        };
        validate_constraint_with_budget(&formula, &baseline).expect("baseline fits exactly");

        let exhausted = [
            (SmtWorkBudget { max_ast_nodes: 2, ..baseline }, SmtWorkResource::AstNodes),
            (SmtWorkBudget { max_numeral_bits: 8, ..baseline }, SmtWorkResource::NumeralBits),
            (
                SmtWorkBudget { max_bitvector_width: 15, ..baseline },
                SmtWorkResource::BitVectorWidth,
            ),
        ];

        for (work_budget, expected_resource) in exhausted {
            assert!(matches!(
                validate_constraint_with_budget(&formula, &work_budget),
                Err(SmtValidationError::WorkBudgetExceeded { resource, .. })
                    if resource == expected_resource
            ));
            let theory = Z3Theory { timeout_ms: 5_000, work_budget };
            assert_eq!(is_satisfiable_3v(&theory, &formula), Sat3::DontKnow);
            assert!(checked_witness(&theory, &formula).is_none());
            assert!(matches!(
                eval_constraint_checked_with_budget(
                    &SmtConstraint::Not(Box::new(formula.clone())),
                    &SmtModel::default(),
                    &work_budget,
                ),
                Err(SmtValidationError::WorkBudgetExceeded { .. })
            ));
        }
    }

    #[test]
    fn excessive_width_is_rejected_before_modulus_allocation() {
        let budget = SmtWorkBudget {
            max_bitvector_width: 256,
            ..SmtWorkBudget::default()
        };
        assert!(matches!(
            SmtBitVector::new_with_budget(0u8, u32::MAX, &budget),
            Err(SmtValidationError::WorkBudgetExceeded {
                resource: SmtWorkResource::BitVectorWidth,
                required,
                limit: 256,
            }) if required == u64::from(u32::MAX)
        ));

        let formula = SmtConstraint::Eq(
            SmtTerm::BvVar("hostile".into(), u32::MAX),
            SmtTerm::BvVar("hostile".into(), u32::MAX),
        );
        assert!(matches!(
            validate_constraint_with_budget(&formula, &budget),
            Err(SmtValidationError::WorkBudgetExceeded {
                resource: SmtWorkResource::BitVectorWidth,
                ..
            })
        ));
    }
}
