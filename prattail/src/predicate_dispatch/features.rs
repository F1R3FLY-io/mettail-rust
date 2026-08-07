use super::*;

/// Equality-like relation names that trigger M6 (Register).
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
pub(crate) fn is_equality_relation(name: &str) -> bool {
    matches!(
        name,
        "eq" | "neq" | "equal" | "not_equal" | "fresh" | "==" | "!=" | "equals" | "related"
    )
}

/// Cardinality-like relation names that trigger M9 (Multiset).
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
pub(crate) fn is_cardinality_relation(name: &str) -> bool {
    matches!(
        name,
        "count"
            | "size"
            | "cardinality"
            | "length"
            | ">="
            | "<="
            | ">"
            | "<"
            | "at_least"
            | "at_most"
    )
}

/// Fixpoint/recursive relation names that trigger M4 (VPA) + M5 (Parity Tree).
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
fn is_fixpoint_relation(name: &str) -> bool {
    matches!(name, "letprop" | "fixpoint" | "mu" | "nu" | "letrec" | "recursive")
}

/// Arithmetic/numeric relation names that trigger M12 (Linear Arithmetic / Presburger).
///
/// Recognizes arithmetic operators, comparison operators, and numeric range
/// predicates. Note overlap with `is_cardinality_relation` for `>`, `<`, `>=`,
/// `<=` — both M9 and M12 may activate for the same relation.
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
fn is_arithmetic_relation(name: &str) -> bool {
    matches!(
        name,
        "add"
            | "sub"
            | "mul"
            | "sum"
            | "diff"
            | "plus"
            | "minus"
            | "linear"
            | "arithmetic"
            | "numeric"
            | ">"
            | "<"
            | ">="
            | "<="
            | "=="
            | "!="
            | "gt"
            | "lt"
            | "ge"
            | "le"
            | "bounded"
            | "range"
            | "between"
            | "clamp"
            | "mod"
            | "div"
            | "rem"
    )
}

/// Unification/pattern-matching relation names that trigger M13 (Unification).
///
/// Recognizes structural matching, type variable instantiation, and substitution
/// predicates common in MeTTa (`match`, `unify`) and Rholang (quoted process
/// matching). User-defined languages with custom matching semantics should
/// eventually register their relation names via the `theories { }` block.
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
fn is_unification_relation(name: &str) -> bool {
    matches!(
        name,
        "match"
            | "unify"
            | "bind"
            | "pattern"
            | "match_type"
            | "instantiate"
            | "substitute"
            | "custom_match"
            | "structural_match"
    )
}

/// Subtype/type-hierarchy relation names that trigger M14 (Subtype Lattice).
///
/// Recognizes subtype declarations, join/meet operations, type compatibility
/// checks, and exhaustiveness predicates. Covers MeTTa `(:<  sub super)`,
/// Rholang bundle capabilities (`bundle+ ≤ bundle0`), and general type
/// hierarchy constraints.
///
/// Temporary heuristic — see module-level comment on relation name heuristics.
fn is_subtype_relation(name: &str) -> bool {
    matches!(
        name,
        "subtype"
            | "supertype"
            | ":<"
            | ":>"
            | "is_a"
            | "join"
            | "meet"
            | "lub"
            | "glb"
            | "type_compatible"
            | "assignable"
            | "exhaustive"
            | "covers"
    )
}

/// Extract variety features from a `PredicateExpr` in O(|AST|) time.
///
/// Single post-order traversal accumulating:
/// - Module bits (signature)
/// - Quantifier depth
/// - Channel/register counts
/// - Boolean flags for backward constraints, cardinality, recursion
///
/// The signature is a conservative approximation: it may activate extra modules
/// but never misses a needed one (Lemma 1.1 in variety-classification.md).
/// Backward-compatible 2-argument wrapper around `extract_features_with_config`.
///
/// Equivalent to `extract_features_with_config(expr, ctx, None)`. All
/// heuristic relation-name dispatchers fire as before, since no explicit
/// theory registrations are provided.
pub fn extract_features(expr: &PredicateExpr, ctx: &ChannelContext) -> PredicateProfile {
    extract_features_with_config(expr, ctx, None)
}

/// Configurable feature extraction that consults `GuardConfigSpec` to gate
/// heuristic relation-name dispatch.
///
/// Override semantics (Layer C cleanup, design doc §2A):
/// - When the guard config registers a `Presburger` theory, the
///   `is_arithmetic_relation` heuristic is bypassed; M12 is activated only
///   by the explicit theory registration in `classify_grammar_with_config`.
/// - Same for `Unification → M13`, `Lattice → M14`, `Register → M6`,
///   `Multiset → M9`, `Fixpoint → M4 + M5`.
/// - Heuristics that are not gated by any registered theory continue to
///   fire as before (backward compatible).
///
/// Soundness: this is a *bypass*, not an override — the explicit
/// activation block in `classify_grammar_with_config` still sets the
/// corresponding bits. The configured profile signature is therefore
/// always a subset of the unconfigured signature for the gated bits, with
/// equality for unaffected bits.
///
/// See: docs/design/dispatch/predicate-dispatch-integration.md
pub fn extract_features_with_config(
    expr: &PredicateExpr,
    ctx: &ChannelContext,
    guard_config: Option<&crate::GuardConfigSpec>,
) -> PredicateProfile {
    let mut profile = PredicateProfile::base();
    let mut channels_seen: HashSet<String> = HashSet::new();
    let mut register_vars: HashSet<String> = HashSet::new();
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    walk_predicate(
        expr,
        ctx,
        &mut profile.signature,
        &mut depth,
        &mut max_depth,
        &mut channels_seen,
        &mut register_vars,
        &mut profile.has_backward_constraint,
        &mut profile.has_cardinality,
        &mut profile.has_recursive_predicate,
        &mut profile.has_arithmetic,
        &mut profile.has_unification,
        &mut profile.has_subtype,
        guard_config,
    );

    profile.quantifier_depth = max_depth;
    profile.channel_count = channels_seen.len() as u32;
    profile.register_count = register_vars.len() as u32;
    // NOTE: this tiers a *parsing/dispatch* predicate skeleton; it is intentionally
    // left as the untyped `classify_decidability` (changing it risks a scheduling
    // regression). The structural-vs-behavioral guard *typing* — routing data-sort
    // type assertions through the EBA-backed sorted classifier and rewrite-relation
    // side conditions to their runtime tier — is handled in
    // `testkit/src/analytical/guards.rs`; the `algebra_tower`-backed behavioral
    // tiering (modal/μ-calculus) moves here in Phase 3.
    profile.decidability_tier = crate::symbolic::classify_decidability(expr);

    // Multi-guard heuristic: ≥2 channels suggests selectivity ordering need.
    if channels_seen.len() >= 2 {
        profile.signature.set(PredicateSignature::M7_PROBABILISTIC);
        profile.signature.set(PredicateSignature::M8_MULTI_TAPE);
    }

    profile
}

/// Stack-safe AST walk for `PredicateExpr` feature extraction.
#[allow(clippy::too_many_arguments)]
fn walk_predicate(
    expr: &PredicateExpr,
    ctx: &ChannelContext,
    sig: &mut PredicateSignature,
    depth: &mut u32,
    max_depth: &mut u32,
    channels: &mut HashSet<String>,
    registers: &mut HashSet<String>,
    has_backward: &mut bool,
    has_cardinality: &mut bool,
    has_recursive: &mut bool,
    has_arithmetic: &mut bool,
    has_unification: &mut bool,
    has_subtype: &mut bool,
    guard_config: Option<&crate::GuardConfigSpec>,
) {
    let initial_depth = *depth;
    let mut pending = vec![(expr, initial_depth)];

    while let Some((expr, current_depth)) = pending.pop() {
        match expr {
            PredicateExpr::True | PredicateExpr::False | PredicateExpr::Atom(_) => {},

            PredicateExpr::Not(inner) | PredicateExpr::Bounded { body: inner, .. } => {
                pending.push((inner, current_depth));
            },

            PredicateExpr::And(left, right) | PredicateExpr::Or(left, right) => {
                pending.push((right, current_depth));
                pending.push((left, current_depth));
            },

            PredicateExpr::ForallFinite { body, .. } => {
                sig.set(PredicateSignature::M3_AWA);
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },

            PredicateExpr::ExistsFinite { body, .. } => {
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },

            PredicateExpr::ForallInfinite { body, .. } => {
                sig.set(PredicateSignature::M2_BUCHI);
                sig.set(PredicateSignature::M3_AWA);
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },

            PredicateExpr::ExistsInfinite { body, .. } => {
                sig.set(PredicateSignature::M2_BUCHI);
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },

            PredicateExpr::Relation { name, args } => {
                if !theory_registered(guard_config, TheoryKind::Register)
                    && is_equality_relation(name)
                {
                    sig.set(PredicateSignature::M6_REGISTER);
                    for arg in args {
                        registers.insert(arg.clone());
                    }
                }
                if !theory_registered(guard_config, TheoryKind::Multiset)
                    && is_cardinality_relation(name)
                {
                    sig.set(PredicateSignature::M9_MULTISET);
                    *has_cardinality = true;
                }
                if !theory_registered(guard_config, TheoryKind::Fixpoint)
                    && is_fixpoint_relation(name)
                {
                    sig.set(PredicateSignature::M4_VPA);
                    sig.set(PredicateSignature::M5_PARITY_TREE);
                    *has_recursive = true;
                }
                if !theory_registered(guard_config, TheoryKind::Presburger)
                    && is_arithmetic_relation(name)
                {
                    sig.set(PredicateSignature::M12_LINEAR_ARITHMETIC);
                    *has_arithmetic = true;
                }
                if !theory_registered(guard_config, TheoryKind::Unification)
                    && is_unification_relation(name)
                {
                    sig.set(PredicateSignature::M13_UNIFICATION);
                    *has_unification = true;
                }
                if !theory_registered(guard_config, TheoryKind::Lattice)
                    && is_subtype_relation(name)
                {
                    sig.set(PredicateSignature::M14_SUBTYPE_LATTICE);
                    *has_subtype = true;
                }
                for arg in args {
                    if ctx.is_cross_channel(arg) {
                        sig.set(PredicateSignature::M8_MULTI_TAPE);
                        sig.set(PredicateSignature::M11_TWO_WAY);
                        *has_backward = true;
                    }
                    if let Some(channel) = ctx.channel_of(arg) {
                        channels.insert(channel.to_string());
                    }
                }
                if !theory_registered(guard_config, TheoryKind::Register)
                    && !is_equality_relation(name)
                    && !is_cardinality_relation(name)
                {
                    sig.set(PredicateSignature::M6_REGISTER);
                    for arg in args {
                        registers.insert(arg.clone());
                    }
                }
            },
        }
    }

    *depth = initial_depth;
}
// ═══════════════════════════════════════════════════════════════════════════════
// §6  Feature Extraction — WeightedMsoFormula → PredicateProfile
// ═══════════════════════════════════════════════════════════════════════════════

/// Backward-compatible 2-argument wrapper around
/// `extract_features_mso_with_config`.
///
/// Equivalent to `extract_features_mso_with_config(formula, ctx, None)`.
pub fn extract_features_mso(
    formula: &WeightedMsoFormula,
    ctx: &ChannelContext,
) -> PredicateProfile {
    extract_features_mso_with_config(formula, ctx, None)
}

/// Configurable feature extraction for `WeightedMsoFormula`.
///
/// Analogous to `extract_features_with_config()` for `PredicateExpr`, with
/// MSO-specific rules:
/// - `ForallSecond` → M3_AWA (universal second-order quantification)
/// - `AtomicPos { label: "letprop" }` → M4_VPA + M5_PARITY_TREE (gated on
///   the `Fixpoint` theory kind being absent)
///
/// See `extract_features_with_config` for full bypass semantics.
pub fn extract_features_mso_with_config(
    formula: &WeightedMsoFormula,
    ctx: &ChannelContext,
    guard_config: Option<&crate::GuardConfigSpec>,
) -> PredicateProfile {
    let mut profile = PredicateProfile::base();
    let mut channels_seen: HashSet<String> = HashSet::new();
    let mut register_vars: HashSet<String> = HashSet::new();
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    walk_mso_formula(
        formula,
        ctx,
        &mut profile.signature,
        &mut depth,
        &mut max_depth,
        &mut channels_seen,
        &mut register_vars,
        &mut profile.has_backward_constraint,
        &mut profile.has_recursive_predicate,
        guard_config,
    );

    profile.quantifier_depth = max_depth;
    profile.channel_count = channels_seen.len() as u32;
    profile.register_count = register_vars.len() as u32;
    profile.decidability_tier = crate::weighted_mso::check_decidability(formula);

    // Multi-guard heuristic
    if channels_seen.len() >= 2 {
        profile.signature.set(PredicateSignature::M7_PROBABILISTIC);
        profile.signature.set(PredicateSignature::M8_MULTI_TAPE);
    }

    profile
}

/// Stack-safe AST walk for `WeightedMsoFormula` feature extraction.
#[allow(clippy::too_many_arguments)]
fn walk_mso_formula(
    formula: &WeightedMsoFormula,
    ctx: &ChannelContext,
    sig: &mut PredicateSignature,
    depth: &mut u32,
    max_depth: &mut u32,
    channels: &mut HashSet<String>,
    registers: &mut HashSet<String>,
    has_backward: &mut bool,
    has_recursive: &mut bool,
    guard_config: Option<&crate::GuardConfigSpec>,
) {
    let fixpoint_bypassed = theory_registered(guard_config, TheoryKind::Fixpoint);
    let register_bypassed = theory_registered(guard_config, TheoryKind::Register);
    let initial_depth = *depth;
    let mut pending = vec![(formula, initial_depth)];

    while let Some((formula, current_depth)) = pending.pop() {
        match formula {
            WeightedMsoFormula::Constant(_) => {},

            WeightedMsoFormula::AtomicPos { label, var }
            | WeightedMsoFormula::NegAtomicPos { label, var } => {
                if !fixpoint_bypassed
                    && (label == "letprop" || label == "fixpoint" || label == "mu" || label == "nu")
                {
                    sig.set(PredicateSignature::M4_VPA);
                    sig.set(PredicateSignature::M5_PARITY_TREE);
                    *has_recursive = true;
                }
                if ctx.is_cross_channel(var) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(channel) = ctx.channel_of(var) {
                    channels.insert(channel.to_string());
                }
            },

            WeightedMsoFormula::Order { x, y } | WeightedMsoFormula::NegOrder { x, y } => {
                if !register_bypassed {
                    sig.set(PredicateSignature::M6_REGISTER);
                    registers.insert(x.clone());
                    registers.insert(y.clone());
                }
                for variable in [x, y] {
                    if ctx.is_cross_channel(variable) {
                        sig.set(PredicateSignature::M8_MULTI_TAPE);
                        sig.set(PredicateSignature::M11_TWO_WAY);
                        *has_backward = true;
                    }
                    if let Some(channel) = ctx.channel_of(variable) {
                        channels.insert(channel.to_string());
                    }
                }
            },

            WeightedMsoFormula::InSet { var, set_var }
            | WeightedMsoFormula::NotInSet { var, set_var } => {
                for variable in [var, set_var] {
                    if ctx.is_cross_channel(variable) {
                        sig.set(PredicateSignature::M8_MULTI_TAPE);
                        sig.set(PredicateSignature::M11_TWO_WAY);
                        *has_backward = true;
                    }
                    if let Some(channel) = ctx.channel_of(variable) {
                        channels.insert(channel.to_string());
                    }
                }
            },

            WeightedMsoFormula::And(left, right) | WeightedMsoFormula::Or(left, right) => {
                pending.push((right, current_depth));
                pending.push((left, current_depth));
            },

            WeightedMsoFormula::ExistsFirst { body, .. }
            | WeightedMsoFormula::ExistsSecond { body, .. } => {
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },

            WeightedMsoFormula::ForallFirst { body, .. }
            | WeightedMsoFormula::ForallSecond { body, .. } => {
                sig.set(PredicateSignature::M3_AWA);
                let child_depth = current_depth + 1;
                *max_depth = (*max_depth).max(child_depth);
                pending.push((body, child_depth));
            },
        }
    }

    *depth = initial_depth;
}
