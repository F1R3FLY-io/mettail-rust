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

// ══════════════════════════════════════════════════════════════════════════════
// RT10 `.1`: structural refinement dispatch via the sym_tree recognizer
// ══════════════════════════════════════════════════════════════════════════════

/// Analyze refinement-type dispatch with **precise** structural reasoning for
/// `Structural` (term-pattern) refinements, deciding disjointness / subtype with
/// the `sym_tree`-based recognizer (`crate::structural_types`) instead of the
/// string heuristic.
///
/// For each pair of refinements sharing a base category:
///   - if **both** are `Structural`, each `predicate_repr` is parsed into a
///     [`TreePred`](crate::sym_tree::TreePred) and *refined* against the base
///     category automaton (`L(base) ∩ L(pattern)`), and the pair is classified:
///       - **Disjoint** iff `A ∩ B` is empty (`is_empty`);
///       - **Subtype** (`A <: B`) iff `A ∩ ¬B` is empty;
///       - **Supertype** iff `B ∩ ¬A` is empty;
///       - else **Overlapping**.
///     `!=` (inequality) patterns are handled by complementing the parsed pattern
///     within the base category (the refined set is the base minus the pattern).
///   - otherwise (Presburger / Behavioral / Mixed, or a structural pair whose
///     predicate fails to parse) the existing [`classify_predicate_overlap`]
///     heuristic is used — so this is **never worse** than the status quo.
///
/// This is the live path; it is selected by
/// [`pipeline::analysis::analyze_refinement_types`](crate::pipeline). Analysis
/// only — runtime `match_pattern` codegen is untouched.
pub fn analyze_refinement_dispatch_structural(
    refinement_specs: &[crate::RefinementTypeSpec],
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> RefinementDispatchAnalysis {
    use crate::structural_types::{build_tree_algebra, ranked_alphabet};

    let mut analysis = RefinementDispatchAnalysis::default();

    // The grammar's ranked alphabet + tree algebra, built once.
    let alpha = ranked_alphabet(all_syntax, categories);
    let elem = build_tree_algebra(&alpha);

    // Group refinements by base category (same as the heuristic path).
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

        for i in 0..specs.len() {
            for j in (i + 1)..specs.len() {
                let a = specs[i];
                let b = specs[j];

                let overlap = structural_pair_overlap(a, b, base, &alpha, &elem)
                    .unwrap_or_else(|| classify_predicate_overlap(a, b));

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

/// Try to classify a refinement pair *structurally* (precise tree-automaton
/// decision). Returns `None` to signal "not a structural pair I can decide" — the
/// caller then falls back to the string heuristic. `None` covers: either side not
/// `Structural`, a `predicate_repr` that does not parse into a tree pattern, or a
/// tree algebra that is not `AnyAlgebra::Tree` (never happens for
/// `build_tree_algebra`, but guarded defensively).
fn structural_pair_overlap(
    a: &crate::RefinementTypeSpec,
    b: &crate::RefinementTypeSpec,
    base: &str,
    alpha: &crate::structural_types::RankedAlphabet,
    elem: &crate::any_algebra::AnyAlgebra,
) -> Option<PredicateOverlap> {
    use crate::structural_types::parse_structural_predicate;

    if a.predicate_kind != crate::RefinementPredKind::Structural
        || b.predicate_kind != crate::RefinementPredKind::Structural
    {
        return None;
    }

    let (pat_a, eq_a) = parse_structural_predicate(&a.predicate_repr, alpha)?;
    let (pat_b, eq_b) = parse_structural_predicate(&b.predicate_repr, alpha)?;

    // Build the refined automaton for each side. An equality refinement is the
    // pattern itself; an inequality is the base category minus the pattern
    // (pattern complemented within the base alphabet, then intersected with the
    // base category — which `refined_automaton` already does via the product, so
    // we complement the *pattern automaton* and re-intersect).
    let auto_a = refined_side(base, &pat_a, eq_a, alpha, elem)?;
    let auto_b = refined_side(base, &pat_b, eq_b, alpha, elem)?;

    let inter = auto_a.intersect(&auto_b);
    if inter.is_empty() {
        return Some(PredicateOverlap::Disjoint);
    }
    // Subtype: A ⊆ B iff A ∩ ¬B = ∅. Complement is over the shared alphabet.
    let a_minus_b = auto_a.intersect(&auto_b.complement());
    if a_minus_b.is_empty() {
        return Some(PredicateOverlap::Subtype);
    }
    let b_minus_a = auto_b.intersect(&auto_a.complement());
    if b_minus_a.is_empty() {
        return Some(PredicateOverlap::Supertype);
    }
    // Inhabited intersection, neither contained in the other.
    Some(PredicateOverlap::Overlapping)
}

/// The refined automaton for one side of a structural pair: the pattern's
/// language (equality) or its complement within the base category (inequality).
fn refined_side(
    base: &str,
    pattern: &crate::sym_tree::TreePred<crate::any_algebra::AnyPred>,
    is_equality: bool,
    alpha: &crate::structural_types::RankedAlphabet,
    elem: &crate::any_algebra::AnyAlgebra,
) -> Option<crate::sym_tree::SymbolicTreeAutomaton<crate::any_algebra::AnyAlgebra>> {
    use crate::structural_types::{category_automaton, refined_automaton};

    let refined = refined_automaton(base, pattern, alpha, elem)?;
    if is_equality {
        Some(refined)
    } else {
        // Inequality: base ∩ ¬pattern. We have `refined = base ∩ pattern`; the
        // inequality side is the base category restricted to NOT matching the
        // pattern, i.e. `base ∩ (¬refined)` — but complementing `refined`
        // (= base ∩ pattern) and re-intersecting with base yields exactly
        // `base \ (base ∩ pattern) = base ∩ ¬pattern`.
        let base_auto = category_automaton(base, alpha, elem);
        Some(base_auto.intersect(&refined.complement()))
    }
}
