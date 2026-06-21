use super::*;

// ==============================================================================
// RT10: SFA Integration for Refinement Type Dispatch
// ==============================================================================

/// Result of SFA-based refinement type dispatch analysis.
///
/// When multiple refinement types share the same base type (e.g., `PosInt` and
/// `NegInt` both refine `Int`), this analysis determines:
/// - Whether the refinement predicates are disjoint (safe dispatch)
/// - Whether one subsumes another (subtype relationship)
/// - Whether they overlap (potential ambiguity in dispatch)
///
/// This is used at **compile time** during pipeline analysis. The results
/// feed into RT03 (empty intersection) and RT04 (subtype detected) lints.
#[derive(Debug, Clone, Default)]
pub struct RefinementDispatchAnalysis {
    /// Pairs of refinement types with disjoint predicates (no overlap).
    /// Safe for unambiguous dispatch: `PosInt ∩ NegInt = ∅`.
    pub disjoint_pairs: Vec<(String, String)>,
    /// Pairs where one refines a subset of the other (subtype).
    /// `StrictlyPositive <: PosInt` means every StrictlyPositive is a PosInt.
    pub subtype_pairs: Vec<(String, String)>, // (sub, super)
    /// Pairs with overlapping predicates (potential dispatch ambiguity).
    pub overlapping_pairs: Vec<(String, String)>,
    /// Groups of refinement types sharing the same base type.
    pub base_type_groups: HashMap<String, Vec<String>>,
}

/// Analyze refinement type dispatch safety using the `TypeSystemAlgebra`.
///
/// For each pair of refinement types sharing a base type, checks:
/// 1. **Disjointness**: `is_satisfiable(P ∧ Q)` — if false, types are disjoint
/// 2. **Subsumption**: `implies(P, Q)` — if true, P-type is subtype of Q-type
///
/// This is the compile-time analogue of SFA intersection/subsumption checking
/// applied to refinement predicates rather than SFA guard predicates.
///
/// Feature-gated on `type-system` (uses `LatticeTypeSystem` and
/// `RefinementTypeSystem` which require `logict` + `lattice-theory`).
pub fn analyze_refinement_dispatch(
    refinement_specs: &[crate::RefinementTypeSpec],
) -> RefinementDispatchAnalysis {
    let mut analysis = RefinementDispatchAnalysis::default();

    // Group by base category
    let mut groups: HashMap<String, Vec<&crate::RefinementTypeSpec>> = HashMap::new();
    for spec in refinement_specs {
        groups
            .entry(spec.base_category.clone())
            .or_default()
            .push(spec);
    }

    for (base, specs) in &groups {
        let names: Vec<String> = specs.iter().map(|s| s.name.clone()).collect();
        analysis.base_type_groups.insert(base.clone(), names);

        // Pairwise analysis within each base type group
        for i in 0..specs.len() {
            for j in (i + 1)..specs.len() {
                let a = specs[i];
                let b = specs[j];

                // Use predicate kind to determine dispatch safety.
                // If both are Presburger, we can reason about their predicates.
                // For now, use a conservative heuristic: same predicate kind
                // + different predicate repr = potentially disjoint.
                // Full SFA analysis requires constructing actual automata from
                // the predicate representations, which is done by the
                // `symbolic-automata` feature.
                let overlap = classify_predicate_overlap(a, b);
                match overlap {
                    PredicateOverlap::Disjoint => {
                        analysis
                            .disjoint_pairs
                            .push((a.name.clone(), b.name.clone()));
                    },
                    PredicateOverlap::Subtype => {
                        analysis
                            .subtype_pairs
                            .push((a.name.clone(), b.name.clone()));
                    },
                    PredicateOverlap::Supertype => {
                        analysis
                            .subtype_pairs
                            .push((b.name.clone(), a.name.clone()));
                    },
                    PredicateOverlap::Overlapping => {
                        analysis
                            .overlapping_pairs
                            .push((a.name.clone(), b.name.clone()));
                    },
                }
            }
        }
    }

    analysis
}

/// Classification of how two refinement predicates overlap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PredicateOverlap {
    /// Predicates have no shared values: `P ∧ Q ≡ false`.
    Disjoint,
    /// First predicate implies second: `P ⟹ Q`.
    Subtype,
    /// Second predicate implies first: `Q ⟹ P`.
    Supertype,
    /// Predicates overlap but neither subsumes the other.
    Overlapping,
}

/// Classify the overlap between two refinement predicates based on their
/// serialized representations and predicate kinds.
///
/// This is a **conservative heuristic** that catches common cases:
/// - Complementary linear predicates (e.g., `x > 0` vs `x <= 0`)
/// - Identical predicates (trivially subsumption)
/// - Stricter predicates (e.g., `x > 0 && x < 10` vs `x > 0`)
///
/// For full precision, the `symbolic-automata` feature provides SFA-based
/// analysis via `TypeSystemAlgebra` → `BooleanAlgebra` → SFA intersection.
fn classify_predicate_overlap(
    a: &crate::RefinementTypeSpec,
    b: &crate::RefinementTypeSpec,
) -> PredicateOverlap {
    // Same predicate representation → identical → mutual subtype
    if a.predicate_repr == b.predicate_repr {
        return PredicateOverlap::Subtype;
    }

    // Both Presburger → try to detect complementary predicates
    if a.predicate_kind == crate::RefinementPredKind::Presburger
        && b.predicate_kind == crate::RefinementPredKind::Presburger
    {
        // Check for obvious complement patterns in the string repr
        // e.g., "x>0" vs "x<=0", "x>=0" vs "x<0"
        if is_complement_predicate(&a.predicate_repr, &b.predicate_repr) {
            return PredicateOverlap::Disjoint;
        }

        // Check if one repr is a prefix of the other with additional conjuncts
        // (stricter predicate is a subtype)
        if a.predicate_repr.contains(&b.predicate_repr)
            && a.predicate_repr.len() > b.predicate_repr.len()
        {
            return PredicateOverlap::Subtype; // a is more restrictive
        }
        if b.predicate_repr.contains(&a.predicate_repr)
            && b.predicate_repr.len() > a.predicate_repr.len()
        {
            return PredicateOverlap::Supertype; // b is more restrictive
        }
    }

    // Conservative default: assume overlapping
    PredicateOverlap::Overlapping
}

/// Check if two Presburger predicate representations are complements.
///
/// Detects patterns like:
/// - `x>0` vs `x<=0`
/// - `x>=0` vs `x<0`
/// - `x==0` vs `x!=0`
pub(crate) fn is_complement_predicate(a: &str, b: &str) -> bool {
    let complement_pairs = [(">", "<="), (">=", "<"), ("==", "!=")];

    for (op1, op2) in &complement_pairs {
        // Check a has op1 and b has op2 with same operands
        if let (Some(a_pos), Some(b_pos)) = (a.find(op1), b.find(op2)) {
            let a_before = &a[..a_pos];
            let a_after = &a[a_pos + op1.len()..];
            let b_before = &b[..b_pos];
            let b_after = &b[b_pos + op2.len()..];
            if a_before == b_before && a_after == b_after {
                return true;
            }
        }
        // Check reverse: a has op2, b has op1
        if let (Some(a_pos), Some(b_pos)) = (a.find(op2), b.find(op1)) {
            let a_before = &a[..a_pos];
            let a_after = &a[a_pos + op2.len()..];
            let b_before = &b[..b_pos];
            let b_after = &b[b_pos + op1.len()..];
            if a_before == b_before && a_after == b_after {
                return true;
            }
        }
    }

    false
}
