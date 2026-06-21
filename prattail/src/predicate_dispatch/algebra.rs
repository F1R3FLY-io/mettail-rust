use super::*;

// ═══════════════════════════════════════════════════════════════════════════════
// §8  Dispatch Algebra — BooleanAlgebra impl for SFA verification
// ═══════════════════════════════════════════════════════════════════════════════

/// Predicates over `PredicateSignature` values (bit-membership tests).
///
/// Used as the `Predicate` type in `DispatchAlgebra : BooleanAlgebra`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SignaturePred {
    /// Satisfied by all signatures.
    True,
    /// Satisfied by no signatures.
    False,
    /// Satisfied iff bit `i` is set (module M_{i+1} is active).
    HasBit(u16),
    /// Conjunction.
    And(Box<SignaturePred>, Box<SignaturePred>),
    /// Disjunction.
    Or(Box<SignaturePred>, Box<SignaturePred>),
    /// Negation.
    Not(Box<SignaturePred>),
}

impl SignaturePred {
    /// Evaluate this predicate against a concrete signature.
    pub fn eval(&self, sig: PredicateSignature) -> bool {
        match self {
            Self::True => true,
            Self::False => false,
            Self::HasBit(bit) => sig.contains(*bit),
            Self::And(a, b) => a.eval(sig) && b.eval(sig),
            Self::Or(a, b) => a.eval(sig) || b.eval(sig),
            Self::Not(a) => !a.eval(sig),
        }
    }
}

/// Boolean algebra over signature-membership predicates.
///
/// Domain: `PredicateSignature` (u16 bitfields).
/// Predicates: `SignaturePred` (bit-membership tests + Boolean connectives).
///
/// This implements the same `BooleanAlgebra` trait that `IntervalAlgebra` and
/// `CharClassAlgebra` implement in `symbolic.rs`, making the dispatch layer
/// self-referential: M1's trait verifies M1–M11 dispatch.
#[derive(Clone, Debug)]
pub struct DispatchAlgebra;

impl BooleanAlgebra for DispatchAlgebra {
    type Predicate = SignaturePred;
    type Domain = PredicateSignature;

    fn true_pred(&self) -> SignaturePred {
        SignaturePred::True
    }

    fn false_pred(&self) -> SignaturePred {
        SignaturePred::False
    }

    fn and(&self, a: &SignaturePred, b: &SignaturePred) -> SignaturePred {
        match (a, b) {
            (SignaturePred::True, _) => b.clone(),
            (_, SignaturePred::True) => a.clone(),
            (SignaturePred::False, _) | (_, SignaturePred::False) => SignaturePred::False,
            _ => SignaturePred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &SignaturePred, b: &SignaturePred) -> SignaturePred {
        match (a, b) {
            (SignaturePred::False, _) => b.clone(),
            (_, SignaturePred::False) => a.clone(),
            (SignaturePred::True, _) | (_, SignaturePred::True) => SignaturePred::True,
            _ => SignaturePred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &SignaturePred) -> SignaturePred {
        match a {
            SignaturePred::True => SignaturePred::False,
            SignaturePred::False => SignaturePred::True,
            SignaturePred::Not(inner) => (**inner).clone(),
            _ => SignaturePred::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable(&self, a: &SignaturePred) -> bool {
        // Brute-force over all 2^11 = 2048 signatures (fast enough for 11 bits)
        (0..=PredicateSignature::ALL).any(|bits| a.eval(PredicateSignature::from_raw(bits)))
    }

    fn witness(&self, a: &SignaturePred) -> Option<PredicateSignature> {
        // Fast paths aligned with Rocq witness_satisfies_has_bit theorem:
        // For HasBit(bit), the bit itself is the witness (Nat.land_diag).
        match a {
            SignaturePred::True => Some(PredicateSignature::new()),
            SignaturePred::False => None,
            SignaturePred::HasBit(bit) => {
                if *bit != 0 {
                    Some(PredicateSignature::from_raw(*bit))
                } else {
                    None
                }
            },
            // Compound predicates: brute-force over all 2^11 signatures
            _ => (0..=PredicateSignature::ALL)
                .map(PredicateSignature::from_raw)
                .find(|sig| a.eval(*sig)),
        }
    }

    fn evaluate(&self, pred: &SignaturePred, elem: &PredicateSignature) -> bool {
        pred.eval(*elem)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §9  Dispatch SFA — verification automaton
// ═══════════════════════════════════════════════════════════════════════════════

/// Build the dispatch SFA: a 17-state automaton (q₀ + 15 module states + q_⊥)
/// that verifies dispatch completeness and consistency.
///
/// State diagram:
/// ```text
///     q₀ ──HasBit(0)──→ ◉ q_M1  (Symbolic)
///        ──HasBit(1)──→ ◉ q_M2  (Büchi)
///        ──HasBit(2)──→ ◉ q_M3  (AWA)
///        ...
///        ──HasBit(10)─→ ◉ q_M11 (Two-Way)
///        ──HasBit(11)─→ ◉ q_M12 (Linear Arithmetic)
///        ──HasBit(12)─→ ◉ q_M13 (Unification)
///        ──HasBit(13)─→ ◉ q_M14 (Subtype Lattice)
///        ──¬(any bit)─→ ○ q_⊥   (reject)
/// ```
pub fn build_dispatch_sfa() -> SymbolicAutomaton<DispatchAlgebra> {
    let mut sfa = SymbolicAutomaton::new(DispatchAlgebra);

    // q₀ (state 0): initial, non-accepting
    let q0 = sfa.add_state(false, Some("q₀".to_string()));
    sfa.set_initial(q0);

    // 11 module states (states 1–11): all accepting
    for module in &ModuleId::ALL {
        let q = sfa.add_state(true, Some(format!("q_{}", module)));
        sfa.add_transition(q0, q, SignaturePred::HasBit(module.bit()));
    }

    // q_⊥ (state 12): reject state — reached when no bit is set
    let q_reject = sfa.add_state(false, Some("q_⊥".to_string()));
    // Guard: ¬(HasBit(0) ∨ HasBit(1) ∨ ... ∨ HasBit(10))
    let any_bit = (0..PredicateSignature::NUM_MODULES)
        .map(|i| SignaturePred::HasBit(PredicateSignature::module_bit(i)))
        .reduce(|acc, p| SignaturePred::Or(Box::new(acc), Box::new(p)))
        .expect("at least one module");
    let no_bits = SignaturePred::Not(Box::new(any_bit));
    sfa.add_transition(q0, q_reject, no_bits);

    sfa
}

/// Verify that the dispatch SFA accepts every non-zero signature.
///
/// **Theorem 3.1** (Completeness): For every σ ∈ D with σ ≠ 0, A_D accepts σ.
pub fn verify_completeness(sfa: &SymbolicAutomaton<DispatchAlgebra>) -> bool {
    // Check all non-zero signatures in [1, 0x07FF]
    (1..=PredicateSignature::ALL).all(|bits| {
        let sig = PredicateSignature::from_raw(bits);
        sfa.accepts(&[sig])
    })
}

/// Verify that zero signature is rejected (PD01 condition).
pub fn verify_zero_rejected(sfa: &SymbolicAutomaton<DispatchAlgebra>) -> bool {
    !sfa.accepts(&[PredicateSignature::from_raw(0)])
}

/// Find module pairs that are always co-activated.
///
/// Returns pairs (M_i, M_j) such that for every signature produced by
/// `extract_features()`, if M_i is active then M_j is always also active.
pub fn dispatch_overlap_pairs() -> Vec<(ModuleId, ModuleId)> {
    // M1 and M10 are always co-activated (both in BASE)
    // M8 and M11 are typically co-activated (cross-channel triggers both)
    vec![(ModuleId::Symbolic, ModuleId::Mso), (ModuleId::Mso, ModuleId::Symbolic)]
}

// ═══════════════════════════════════════════════════════════════════════════════
// §10 Dispatch Diagnostics — collected diagnostic data
// ═══════════════════════════════════════════════════════════════════════════════

/// Diagnostic data from predicate dispatch, consumed by lint functions.
#[derive(Debug, Clone)]
pub struct DispatchDiagnostics {
    /// Per-predicate profiles.
    pub profiles: Vec<PredicateProfile>,
    /// Predicates that activate only base modules (PD01 candidates).
    pub degenerate_predicates: Vec<usize>,
    /// Predicates that activate all 11 modules (PD02 candidates).
    pub full_activation_predicates: Vec<usize>,
    /// Total modules skipped across all predicates.
    pub total_modules_skipped: u32,
    /// Predicates with backward (cross-channel) constraints. Pre-feature-flag-
    /// consolidation this was gated on a removed `two-way-transducer` cargo
    /// feature; now the field reports all backward-constraint predicates
    /// unconditionally, as the two-way-transducer module is always-on
    /// (`prattail/src/two_way_transducer.rs`). Useful as a diagnostic for
    /// callers that want to know which predicates require the two-way
    /// compiler pass.
    pub cross_channel_without_two_way: Vec<usize>,
}

impl DispatchDiagnostics {
    /// Compute diagnostics from a `GrammarDispatchPlan`.
    pub fn from_plan(plan: &GrammarDispatchPlan) -> Self {
        let mut degenerate = Vec::new();
        let mut full_activation = Vec::new();
        let mut cross_channel_no_tw = Vec::new();

        for (i, profile) in plan.predicate_profiles.iter().enumerate() {
            if profile.signature.is_base_only() {
                degenerate.push(i);
            }
            if profile.signature.is_full() {
                full_activation.push(i);
            }
            if profile.has_backward_constraint {
                cross_channel_no_tw.push(i);
            }
        }

        Self {
            profiles: plan.predicate_profiles.clone(),
            degenerate_predicates: degenerate,
            full_activation_predicates: full_activation,
            total_modules_skipped: plan.modules_skipped,
            cross_channel_without_two_way: cross_channel_no_tw,
        }
    }
}
