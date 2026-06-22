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

/// Recursive AST walker for `PredicateExpr` feature extraction.
///
/// The `guard_config` parameter (optional) gates the heuristic
/// relation-name dispatchers: when an explicit theory of the matching
/// kind is registered, the corresponding heuristic is bypassed and the
/// `classify_grammar_with_config` explicit-theory activation block sets
/// the affected module bits instead.
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
    match expr {
        PredicateExpr::True | PredicateExpr::False | PredicateExpr::Atom(_) => {
            // Base cases: only M1 + M10 (already in base signature)
        },

        PredicateExpr::Not(inner) => {
            walk_predicate(
                inner,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
        },

        PredicateExpr::And(a, b) | PredicateExpr::Or(a, b) => {
            walk_predicate(
                a,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
            walk_predicate(
                b,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
        },

        PredicateExpr::ForallFinite { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal branching
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
            *depth -= 1;
        },

        PredicateExpr::ExistsFinite { body, .. } => {
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
            *depth -= 1;
        },

        PredicateExpr::ForallInfinite { body, .. } => {
            sig.set(PredicateSignature::M2_BUCHI); // omega-regular
            sig.set(PredicateSignature::M3_AWA); // universal branching
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
            *depth -= 1;
        },

        PredicateExpr::ExistsInfinite { body, .. } => {
            sig.set(PredicateSignature::M2_BUCHI); // omega-regular
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
            *depth -= 1;
        },

        PredicateExpr::Relation { name, args } => {
            // ── Layer C cleanup: gate every heuristic relation-name dispatch
            // ── on the absence of an explicit theory of the matching kind ──
            //
            // When the language registers (e.g.) `Presburger`, the
            // `is_arithmetic_relation` heuristic is bypassed; the explicit
            // theory activation block in `classify_grammar_with_config`
            // sets M12 instead.
            if !theory_registered(guard_config, TheoryKind::Register) && is_equality_relation(name)
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
            // Fixpoint/recursive relation → VPA + Parity Tree
            if !theory_registered(guard_config, TheoryKind::Fixpoint) && is_fixpoint_relation(name)
            {
                sig.set(PredicateSignature::M4_VPA);
                sig.set(PredicateSignature::M5_PARITY_TREE);
                *has_recursive = true;
            }
            // M12: Arithmetic comparisons → Presburger linear arithmetic
            if !theory_registered(guard_config, TheoryKind::Presburger)
                && is_arithmetic_relation(name)
            {
                sig.set(PredicateSignature::M12_LINEAR_ARITHMETIC);
                *has_arithmetic = true;
            }
            // M13: Unification/pattern-matching → structural unification
            if !theory_registered(guard_config, TheoryKind::Unification)
                && is_unification_relation(name)
            {
                sig.set(PredicateSignature::M13_UNIFICATION);
                *has_unification = true;
            }
            // M14: Subtype/type-hierarchy → subtype lattice
            if !theory_registered(guard_config, TheoryKind::Lattice) && is_subtype_relation(name) {
                sig.set(PredicateSignature::M14_SUBTYPE_LATTICE);
                *has_subtype = true;
            }
            // Cross-channel detection (independent of theory registration —
            // channel structure is orthogonal to theory dispatch).
            for arg in args {
                if ctx.is_cross_channel(arg) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(arg) {
                    channels.insert(ch.to_string());
                }
            }
            // Default M6 fallback: if no equality / cardinality match was
            // recorded, the predicate is still a data comparison and feeds
            // the register automaton. Bypassed under an explicit Register
            // theory registration, since that becomes the sole authority.
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

        PredicateExpr::Bounded { body, .. } => {
            walk_predicate(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                has_arithmetic,
                has_unification,
                has_subtype,
                guard_config,
            );
        },
    }
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
        &mut profile.has_cardinality,
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

/// Recursive AST walker for `WeightedMsoFormula` feature extraction.
///
/// The `guard_config` parameter (optional) gates the `letprop`/`fixpoint`/
/// `mu`/`nu` recognition (against the `Fixpoint` theory kind) and the
/// `Order` register activation (against the `Register` theory kind).
/// All other dispatch is structural (channels, quantifier nesting) and
/// independent of theory registration.
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
    has_cardinality: &mut bool,
    has_recursive: &mut bool,
    guard_config: Option<&crate::GuardConfigSpec>,
) {
    let fixpoint_bypassed = theory_registered(guard_config, TheoryKind::Fixpoint);
    let register_bypassed = theory_registered(guard_config, TheoryKind::Register);

    match formula {
        WeightedMsoFormula::Constant(_) => {
            // Base: only M1 + M10
        },

        WeightedMsoFormula::AtomicPos { label, var } => {
            // "letprop" triggers VPA + Parity Tree (recursive predicate definition)
            if !fixpoint_bypassed
                && (label == "letprop" || label == "fixpoint" || label == "mu" || label == "nu")
            {
                sig.set(PredicateSignature::M4_VPA);
                sig.set(PredicateSignature::M5_PARITY_TREE);
                *has_recursive = true;
            }
            // Check cross-channel
            if ctx.is_cross_channel(var) {
                sig.set(PredicateSignature::M8_MULTI_TAPE);
                sig.set(PredicateSignature::M11_TWO_WAY);
                *has_backward = true;
            }
            if let Some(ch) = ctx.channel_of(var) {
                channels.insert(ch.to_string());
            }
        },

        WeightedMsoFormula::NegAtomicPos { label, var } => {
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
            if let Some(ch) = ctx.channel_of(var) {
                channels.insert(ch.to_string());
            }
        },

        WeightedMsoFormula::Order { x, y } | WeightedMsoFormula::NegOrder { x, y } => {
            // Order relations are register-relevant — bypassed under
            // explicit Register theory registration.
            if !register_bypassed {
                sig.set(PredicateSignature::M6_REGISTER);
                registers.insert(x.clone());
                registers.insert(y.clone());
            }
            for v in [x, y] {
                if ctx.is_cross_channel(v) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(v) {
                    channels.insert(ch.to_string());
                }
            }
        },

        WeightedMsoFormula::InSet { var, set_var }
        | WeightedMsoFormula::NotInSet { var, set_var } => {
            // Set membership is MSO-native (already base)
            for v in [var, set_var] {
                if ctx.is_cross_channel(v) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(v) {
                    channels.insert(ch.to_string());
                }
            }
        },

        WeightedMsoFormula::And(a, b) | WeightedMsoFormula::Or(a, b) => {
            walk_mso_formula(
                a,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
            walk_mso_formula(
                b,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
        },

        WeightedMsoFormula::ExistsFirst { body, .. } => {
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
            *depth -= 1;
        },

        WeightedMsoFormula::ForallFirst { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal first-order
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
            *depth -= 1;
        },

        WeightedMsoFormula::ExistsSecond { body, .. } => {
            // Second-order existential: MSO-native (already base)
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
            *depth -= 1;
        },

        WeightedMsoFormula::ForallSecond { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal second-order
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(
                body,
                ctx,
                sig,
                depth,
                max_depth,
                channels,
                registers,
                has_backward,
                has_cardinality,
                has_recursive,
                guard_config,
            );
            *depth -= 1;
        },
    }
}
