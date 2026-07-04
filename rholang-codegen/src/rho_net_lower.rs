//! RhoNet → `rhoapi::Par` lowering (Epic 4, slice 1 — codegen only).
//!
//! This module lowers the classified rules of a [`RhoNetProgram`] to concrete
//! normalized Rholang AST (`rhoapi::Par`), under the CORRECTED
//! set-automaton-assisted execution model:
//!
//! - Dovetail's set automaton performs ALL structural + non-linear matching and
//!   produces a flat substitution `σ` (the LHS variables' matched sub-terms in
//!   canonical **first-occurrence** order). The Rho side therefore does NO
//!   re-matching: every base rewrite lowers to a FLAT `k`-ary contract shaped
//!   EXACTLY like a scalar operator contract (cf. [`crate::lower::contract_ast`]):
//!   `for([f0..f_{k}] <- c(ℓ)){ out!(⟦R⟧σ) }` — a single persistent
//!   `(k+1)`-ary `ReceiveBind` (`k` LHS variables + 1 out channel), body sends
//!   the lowered RHS on the out channel.
//! - De Bruijn indices collapse to the scalar case: formal `i` (a LHS variable
//!   in first-occurrence order) → `BoundVar(k - i)`; the out channel (formal
//!   `k`) → `BoundVar(0)`.
//! - Semantic-predicate guards are checked off-machine (the audit boundary), so
//!   a guarded rewrite keeps its σ-receiver and emits NO guard `Par`.
//!
//! This slice materializes `NativeFold` (reusing the proven scalar contract) and
//! `BaseRewrite` (the σ-receiver). Structural congruence (equations) records a
//! `CongruenceClosure` (compile-time e-graph, empty `Par` contribution).
//! Contextual rewrites, declared joins (`Comm`), native system processes, and
//! constructor reflection are recognized but not yet materialized — they are
//! reported fail-closed (never silently dropped). The lowering deliberately does
//! not tighten the flip gate: it is stored and exposed for the runtime bridge
//! that lands in a later slice.

use std::collections::{HashMap, HashSet};

use mettail_ast::language::{LanguageDef, Premise, RewriteRule};
use mettail_ast::pattern::{Pattern, PatternTerm};
use models::create_bit_vector;
use models::rhoapi::{Par, Receive, ReceiveBind};
use models::rust::utils::{new_boundvar_par, new_freevar_par, new_gstring_par, new_send_par};
use syn::Ident;

use crate::lower::{scalar_contract_par_for, RhoLowering};
use crate::rho_net::{
    behavioral_predicate_has_structural_component, rule_id_equation, rule_id_join, rule_id_native,
    rule_id_rewrite, rule_id_scalar, rule_id_term, term_requires_native_system_process,
    RhoNetProgram, RhoNetRule, RhoNetRuleKind,
};

/// Source-construct family that is out of scope for σ-receiver lowering this
/// slice. Every variant is a genuine, fail-closed classification reached by
/// pattern-tree or premise inspection — never a placeholder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnsupportedFamily {
    /// A collection literal `{P, Q, ...rest}` (associative-commutative match).
    CollectionAc,
    /// A `xs.#map(|x| body)` collection map.
    MapAc,
    /// A `#zip(first, second)` correlated collection pattern.
    ZipAc,
    /// A single-binder lambda `\x.body`.
    LambdaBinder,
    /// A multi-binder lambda `^[x0, x1, ...].body`.
    MultiLambda,
    /// A `subst`/`multisubst` node.
    Substitution,
    /// A constructor application on the RHS. Reflecting a general MeTTaIL term
    /// into a Rho `Par` value is not defined this slice (see the reflection-ABI
    /// investigation), so a constructor RHS fails closed.
    ConstructorRhsNotYetReflectable,
    /// A rewrite premise that the flat σ-receiver cannot enforce (freshness,
    /// relation query, universal quantification, a structural behavioral guard,
    /// ...). Dovetail carries structural matching into σ and semantic-predicate
    /// guards are off-machine, but any other side condition has no receiver
    /// representation this (bridge-less) slice.
    NonCongruenceSideCondition,
}

/// One lowered RhoNet rule.
///
/// `NativeFold` and `BaseRewrite` carry a materialized `Par`; the remaining
/// variants are recognized-but-not-yet-materialized classifications (they
/// contribute no `Par` to [`RhoNetLowered::installed_program_par`]).
#[derive(Debug, Clone, PartialEq)]
pub enum RhoNetLoweredRule {
    /// Scalar native-fold reusing the proven scalar operator contract.
    NativeFold { rule_id: String, par: Par },
    /// A base rewrite lowered to a flat σ-receiver contract.
    BaseRewrite { rule_id: String, par: Par },
    /// A structural-congruence equation (compile-time e-graph closure).
    CongruenceClosure { rule_id: String },
    /// A congruence (contextual) rewrite — deferred to the next slice.
    ContextualRewrite { rule_id: String },
    /// A declared join (COMM) — deferred to the next slice.
    Comm { rule_id: String },
    /// A native system-process dispatch — deferred to the next slice.
    NativeSystemProcess { rule_id: String },
    /// A rule whose source construct is out of scope this slice (fail-closed).
    Unsupported { rule_id: String, family: UnsupportedFamily },
}

impl RhoNetLoweredRule {
    /// The stable RhoNet rule identifier this lowered rule corresponds to.
    pub fn rule_id(&self) -> &str {
        match self {
            Self::NativeFold { rule_id, .. }
            | Self::BaseRewrite { rule_id, .. }
            | Self::CongruenceClosure { rule_id }
            | Self::ContextualRewrite { rule_id }
            | Self::Comm { rule_id }
            | Self::NativeSystemProcess { rule_id }
            | Self::Unsupported { rule_id, .. } => rule_id,
        }
    }

    /// The materialized contract `Par`, when this rule lowered to executable Rho
    /// AST (`NativeFold`/`BaseRewrite`).
    pub fn par(&self) -> Option<&Par> {
        match self {
            Self::NativeFold { par, .. } | Self::BaseRewrite { par, .. } => Some(par),
            _ => None,
        }
    }
}

/// A diagnostic recorded during lowering. These are surfaced (never silently
/// dropped) but do NOT tighten the flip gate this slice.
#[derive(Debug, Clone, PartialEq)]
pub enum RhoNetLoweringError {
    /// A rewrite/equation whose source construct is out of scope this slice.
    UnsupportedFamily { rule_id: String, family: UnsupportedFamily },
    /// The independently re-derived rule-id sequence disagreed with
    /// `program.rules` (the program was paired with a different def/lowering, or
    /// the two walks drifted).
    RuleSourceDrift { rule_id: String },
    /// A `NativeFold` rule had no matching scalar operator contract.
    MissingScalarContract { label: String },
    /// A rule's input channel name could not be resolved to a Rho name.
    ChannelResolution { channel: String },
}

/// The lowered Rho-native execution plan for one `RhoNetProgram`.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoNetLowered {
    /// Stable compiler-facing identity of the source `LanguageDef`.
    pub language_fingerprint: String,
    rules: Vec<RhoNetLoweredRule>,
    errors: Vec<RhoNetLoweringError>,
}

impl RhoNetLowered {
    /// The lowered rules, aligned to the classified rules of the source program
    /// (hard internal errors — missing contract / channel — are surfaced via
    /// [`Self::errors`] instead of a fabricated rule).
    pub fn rules(&self) -> &[RhoNetLoweredRule] {
        &self.rules
    }

    /// Fail-closed diagnostics collected during lowering.
    pub fn errors(&self) -> &[RhoNetLoweringError] {
        &self.errors
    }

    /// Parallel-compose every materialized contract `Par` (`NativeFold` +
    /// `BaseRewrite`) into a single installable Rho program. Classifications
    /// with no `Par` contribute nothing.
    pub fn installed_program_par(&self) -> Par {
        self.rules.iter().fold(Par::default(), |program, rule| match rule.par() {
            Some(par) => program.append(par.clone()),
            None => program,
        })
    }
}

impl RhoNetProgram {
    /// Lower this planning artifact to concrete Rho AST under the corrected
    /// set-automaton-assisted model. See the module documentation.
    pub fn lower_to_par(&self, def: &LanguageDef, lowering: &RhoLowering) -> RhoNetLowered {
        lower(self, def, lowering)
    }
}

/// De Bruijn index of the RHS occurrence of the `occurrence_index`-th LHS
/// variable (first-occurrence order) in a `k`-variable rewrite. Equal to
/// `bound_formal(k + 1, occurrence_index)`'s index: formal `i` → `BoundVar(k - i)`.
pub(crate) fn rhs_var_index(k: usize, occurrence_index: usize) -> i32 {
    (k - occurrence_index) as i32
}

/// The `k`-ary lowering driver. Mirrors [`RhoNetProgram::from_language_def`]'s
/// rule order via [`expected_rule_ids`] (anti-drift cross-check), then lowers
/// each classified rule using its source construct.
pub(crate) fn lower(
    program: &RhoNetProgram,
    def: &LanguageDef,
    lowering: &RhoLowering,
) -> RhoNetLowered {
    let mut rules = Vec::with_capacity(program.rules.len());
    let mut errors = Vec::new();

    // Anti-drift: independently re-derive the canonical rule-id sequence from
    // `def`/`lowering` in the exact order `from_language_def` emits rules, using
    // the SHARED id + emission predicates, then compare against `program.rules`.
    // A mismatch means the program was paired with a different def/lowering (or
    // the two walks drifted) — fail closed with `RuleSourceDrift`.
    let expected_ids = expected_rule_ids(def, lowering);
    for (index, rule) in program.rules.iter().enumerate() {
        if expected_ids.get(index).map(String::as_str) != Some(rule.id.as_str()) {
            errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        }
    }
    for extra in expected_ids.iter().skip(program.rules.len()) {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: extra.clone() });
    }

    // Correlate rewrite rule-ids back to their source `RewriteRule` (which
    // carries the LHS/RHS patterns that `program.rules` does not retain).
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    for rule in &program.rules {
        let lowered = match rule.kind {
            RhoNetRuleKind::NativeFold => lower_native_fold(rule, lowering, &mut errors),
            // A grammar constructor is realized in model b by inline RHS
            // reflection, not as a standalone Rho contract; reflection is not
            // yet defined, so it fails closed.
            RhoNetRuleKind::StructuralConstructor => Some(RhoNetLoweredRule::Unsupported {
                rule_id: rule.id.clone(),
                family: UnsupportedFamily::ConstructorRhsNotYetReflectable,
            }),
            RhoNetRuleKind::NativeSystemProcess => {
                Some(RhoNetLoweredRule::NativeSystemProcess { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::StructuralCongruence => {
                Some(RhoNetLoweredRule::CongruenceClosure { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::BaseRewrite => lower_base_rewrite(rule, &rewrite_by_id, &mut errors),
            RhoNetRuleKind::ContextualRewrite => {
                lower_contextual_rewrite(rule, &rewrite_by_id, &mut errors)
            },
            RhoNetRuleKind::Comm => Some(RhoNetLoweredRule::Comm { rule_id: rule.id.clone() }),
        };
        if let Some(lowered) = lowered {
            rules.push(lowered);
        }
    }

    RhoNetLowered {
        language_fingerprint: program.language_fingerprint.clone(),
        rules,
        errors,
    }
}

/// Re-derive the canonical rule-id sequence in `from_language_def` order. This
/// reuses the SAME id + emission predicates as the builder so the two walks
/// cannot disagree by construction; the result is the anti-drift oracle.
fn expected_rule_ids(def: &LanguageDef, lowering: &RhoLowering) -> Vec<String> {
    let mut ids = Vec::new();
    for abi in &lowering.scalar_contract_abi {
        ids.push(rule_id_scalar(&abi.rule_label));
    }
    for (index, term) in def.terms.iter().enumerate() {
        ids.push(rule_id_term(index, &term.label.to_string()));
    }
    let rejected: HashSet<&str> = lowering.rejected.iter().map(String::as_str).collect();
    for (index, term) in def.terms.iter().enumerate() {
        let label = term.label.to_string();
        if rejected.contains(label.as_str()) && term_requires_native_system_process(term) {
            ids.push(rule_id_native(index, &label));
        }
    }
    for (index, equation) in def.equations.iter().enumerate() {
        ids.push(rule_id_equation(index, &equation.name.to_string()));
    }
    for (index, rewrite) in def.rewrites.iter().enumerate() {
        ids.push(rule_id_rewrite(index, &rewrite.name.to_string()));
    }
    if let Some(channels) = def
        .guard_config
        .as_ref()
        .and_then(|guards| guards.channels.as_ref())
    {
        for join in &channels.join_patterns {
            ids.push(rule_id_join(&join.label.to_string()));
        }
    }
    ids
}

/// Lower a `NativeFold` rule by reusing its proven scalar operator contract.
fn lower_native_fold(
    rule: &RhoNetRule,
    lowering: &RhoLowering,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let label = rule.label.as_deref().unwrap_or(rule.id.as_str());
    match scalar_contract_par_for(lowering, label) {
        Some(par) => Some(RhoNetLoweredRule::NativeFold { rule_id: rule.id.clone(), par }),
        None => {
            errors.push(RhoNetLoweringError::MissingScalarContract { label: label.to_string() });
            None
        },
    }
}

/// Lower a base rewrite to the flat σ-receiver contract.
fn lower_base_rewrite(
    rule: &RhoNetRule,
    rewrite_by_id: &HashMap<String, &RewriteRule>,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let Some(rewrite) = rewrite_by_id.get(rule.id.as_str()) else {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };

    // Fail closed on premises the flat σ-receiver cannot enforce this slice.
    // Dovetail carries structural matching into σ, and purely-semantic
    // behavioral guards are checked off-machine (so they are fine); any other
    // side condition has no receiver representation in a bridge-less slice.
    if !rewrite_premises_receiver_safe(&rewrite.premises) {
        return Some(record_unsupported(
            rule,
            UnsupportedFamily::NonCongruenceSideCondition,
            errors,
        ));
    }

    // Primary constructive detection: `lower_lhs_vars`/`lower_rhs` walk the real
    // pattern trees to build the receiver and return `UnsupportedFamily` on any
    // out-of-scope node.
    let vars = match lower_lhs_vars(&rewrite.left) {
        Ok(vars) => vars,
        Err(family) => return Some(record_unsupported(rule, family, errors)),
    };
    let k = vars.len();
    let rhs_par = match lower_rhs(&rewrite.right, &vars, k) {
        Ok(par) => par,
        Err(family) => return Some(record_unsupported(rule, family, errors)),
    };

    // Independent P2 defensive cross-check: the standalone pattern-tree detector
    // must agree the rewrite is lowerable (it walks the trees, so it does NOT
    // rely on constructor rejection). On the success path it returns `None`.
    if let Some(family) = rewrite_pattern_unsupported(&rewrite.left, &rewrite.right) {
        return Some(record_unsupported(rule, family, errors));
    }

    let Some(channel) = rule.input_channels.first() else {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };
    let source = match resolve_channel(channel) {
        Ok(source) => source,
        Err(error) => {
            errors.push(error);
            return None;
        },
    };

    let par = sigma_receiver_par(k, rhs_par, source);
    Some(RhoNetLoweredRule::BaseRewrite { rule_id: rule.id.clone(), par })
}

/// Lower a congruence (contextual) rewrite. Not materialized to a σ-receiver
/// this slice, but the P2 detector still records an out-of-scope family
/// fail-closed rather than silently deferring it.
fn lower_contextual_rewrite(
    rule: &RhoNetRule,
    rewrite_by_id: &HashMap<String, &RewriteRule>,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let Some(rewrite) = rewrite_by_id.get(rule.id.as_str()) else {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };
    match rewrite_pattern_unsupported(&rewrite.left, &rewrite.right) {
        Some(family) => Some(record_unsupported(rule, family, errors)),
        None => Some(RhoNetLoweredRule::ContextualRewrite { rule_id: rule.id.clone() }),
    }
}

/// Record an `UnsupportedFamily` diagnostic and return the matching classified
/// rule (both, so the failure is surfaced AND the rule stays accounted for).
fn record_unsupported(
    rule: &RhoNetRule,
    family: UnsupportedFamily,
    errors: &mut Vec<RhoNetLoweringError>,
) -> RhoNetLoweredRule {
    errors.push(RhoNetLoweringError::UnsupportedFamily { rule_id: rule.id.clone(), family });
    RhoNetLoweredRule::Unsupported { rule_id: rule.id.clone(), family }
}

/// A base rewrite's premises are receiver-safe iff every premise is a
/// purely-semantic behavioral guard (checked off-machine). Any structural or
/// relational side condition fails closed. An empty premise list is safe.
fn rewrite_premises_receiver_safe(premises: &[Premise]) -> bool {
    premises.iter().all(|premise| match premise {
        Premise::BehavioralGuard(pred) => !behavioral_predicate_has_structural_component(pred),
        _ => false,
    })
}

/// Resolve a channel name to a Rho `GString` name, rejecting an empty name.
fn resolve_channel(name: &str) -> Result<Par, RhoNetLoweringError> {
    if name.trim().is_empty() {
        Err(RhoNetLoweringError::ChannelResolution { channel: name.to_string() })
    } else {
        Ok(new_gstring_par(name.to_string(), Vec::new(), false))
    }
}

/// Collect the LHS pattern variables in canonical first-occurrence order,
/// de-duplicated (a repeated variable keeps only its first occurrence — dovetail
/// resolves the non-linear equality into σ). Returns `UnsupportedFamily` for any
/// out-of-scope node.
pub(crate) fn lower_lhs_vars(pattern: &Pattern) -> Result<Vec<Ident>, UnsupportedFamily> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    collect_lhs_vars(pattern, &mut vars, &mut seen)?;
    Ok(vars)
}

fn collect_lhs_vars(
    pattern: &Pattern,
    vars: &mut Vec<Ident>,
    seen: &mut HashSet<String>,
) -> Result<(), UnsupportedFamily> {
    match pattern {
        Pattern::Term(term) => collect_lhs_vars_term(term, vars, seen),
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
    }
}

fn collect_lhs_vars_term(
    term: &PatternTerm,
    vars: &mut Vec<Ident>,
    seen: &mut HashSet<String>,
) -> Result<(), UnsupportedFamily> {
    match term {
        PatternTerm::Var(ident) => {
            if seen.insert(ident.to_string()) {
                vars.push(ident.clone());
            }
            Ok(())
        },
        PatternTerm::Apply { args, .. } => {
            for arg in args {
                collect_lhs_vars(arg, vars, seen)?;
            }
            Ok(())
        },
        PatternTerm::Lambda { .. } => Err(UnsupportedFamily::LambdaBinder),
        PatternTerm::MultiLambda { .. } => Err(UnsupportedFamily::MultiLambda),
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => {
            Err(UnsupportedFamily::Substitution)
        },
    }
}

/// Lower the RHS pattern to a `Par`, substituting each LHS variable reference
/// with its σ-tuple De Bruijn index. Structured RHS nodes fail closed exactly
/// like the LHS (a constructor application additionally needs term reflection,
/// deferred this slice).
pub(crate) fn lower_rhs(rhs: &Pattern, vars: &[Ident], k: usize) -> Result<Par, UnsupportedFamily> {
    match rhs {
        Pattern::Term(PatternTerm::Var(name)) => match vars.iter().position(|var| var == name) {
            Some(index) => Ok(new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)),
            // A RHS variable not bound by the LHS has no σ-tuple slot; the
            // rewrite is ill-formed for a flat receiver. Fail closed rather than
            // emit a dangling De Bruijn index.
            None => Err(UnsupportedFamily::ConstructorRhsNotYetReflectable),
        },
        Pattern::Term(PatternTerm::Apply { .. }) => {
            Err(UnsupportedFamily::ConstructorRhsNotYetReflectable)
        },
        Pattern::Term(PatternTerm::Lambda { .. }) => Err(UnsupportedFamily::LambdaBinder),
        Pattern::Term(PatternTerm::MultiLambda { .. }) => Err(UnsupportedFamily::MultiLambda),
        Pattern::Term(PatternTerm::Subst { .. }) | Pattern::Term(PatternTerm::MultiSubst { .. }) => {
            Err(UnsupportedFamily::Substitution)
        },
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
    }
}

/// P2 defensive detector (independent of the constructive walk): report the
/// first out-of-scope family in a rewrite's LHS/RHS patterns. Constructor
/// applications and variables are the supported LHS shapes; a variable is the
/// only fully-supported RHS shape (a constructor RHS needs reflection).
pub(crate) fn rewrite_pattern_unsupported(
    left: &Pattern,
    right: &Pattern,
) -> Option<UnsupportedFamily> {
    if let Some(family) = pattern_binder_or_collection_family(left) {
        return Some(family);
    }
    match right {
        Pattern::Term(PatternTerm::Var(_)) => None,
        Pattern::Term(PatternTerm::Apply { .. }) => {
            Some(UnsupportedFamily::ConstructorRhsNotYetReflectable)
        },
        other => pattern_binder_or_collection_family(other),
    }
}

fn pattern_binder_or_collection_family(pattern: &Pattern) -> Option<UnsupportedFamily> {
    match pattern {
        Pattern::Term(term) => pattern_term_binder_family(term),
        Pattern::Collection { .. } => Some(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Some(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Some(UnsupportedFamily::ZipAc),
    }
}

fn pattern_term_binder_family(term: &PatternTerm) -> Option<UnsupportedFamily> {
    match term {
        PatternTerm::Var(_) => None,
        PatternTerm::Apply { args, .. } => args.iter().find_map(pattern_binder_or_collection_family),
        PatternTerm::Lambda { .. } => Some(UnsupportedFamily::LambdaBinder),
        PatternTerm::MultiLambda { .. } => Some(UnsupportedFamily::MultiLambda),
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => {
            Some(UnsupportedFamily::Substitution)
        },
    }
}

/// Build the flat σ-receiver `Par` for a `k`-variable base rewrite. Shaped
/// exactly like [`crate::lower::contract_ast`] with `formal_count = k + 1`: one
/// persistent `(k+1)`-ary `ReceiveBind` over `source`, body sends `rhs_par` on
/// the out channel (`BoundVar(0)`).
fn sigma_receiver_par(k: usize, rhs_par: Par, source: Par) -> Par {
    let formal_count = k + 1;
    let all_formals = all_formals_bitvec(formal_count);
    let out_channel = bound_formal(formal_count, k);
    let body = new_send_par(
        out_channel,
        vec![rhs_par],
        false,
        all_formals.clone(),
        false,
        all_formals.clone(),
        false,
    );
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: (0..formal_count)
                .map(|i| new_freevar_par(i as i32, Vec::new()))
                .collect(),
            source: Some(source),
            remainder: None,
            free_count: formal_count as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: formal_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    Par::default().with_receives(vec![receive])
}

/// The `n`-th De Bruijn formal of a receiver with `total_formals` formals
/// (`BoundVar(total_formals - 1 - formal_index)`). Mirrors `lower::bound_formal`.
fn bound_formal(total_formals: usize, formal_index: usize) -> Par {
    new_boundvar_par((total_formals - 1 - formal_index) as i32, Vec::new(), false)
}

/// The locally-free bit vector covering formals `0..count` (empty when there are
/// no formals). Mirrors `lower::binding_bitvec`.
fn all_formals_bitvec(count: usize) -> Vec<u8> {
    if count == 0 {
        Vec::new()
    } else {
        create_bit_vector(&(0..count).collect::<Vec<_>>())
    }
}

#[cfg(test)]
mod tests {
    // `super::*` already re-exports the parent module's imports (`Par`,
    // `Pattern`/`PatternTerm`, `LanguageDef`/`Premise`/`RewriteRule`,
    // `scalar_contract_par_for`, `RhoNetProgram`, `rule_id_rewrite`, ...) plus
    // every type defined in this module; only the extras below are new.
    use super::*;
    use crate::lower::lower_language_def;
    use mettail_ast::language::Equation;
    use models::rhoapi::expr::ExprInstance;
    use models::rhoapi::var::VarInstance;

    const SCALAR_FRAGMENT: &str = r#"
        name: RhoNetLowerScalarFrag,
        types {
            ![i32] as Int
            ![bool] as Bool
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            EqInt . a:Int, b:Int |- a "==" b : Bool ;
        }
    "#;

    const MINIRHO_FOR_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniRhoFor,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types {
            Proc
            Name
        },
        terms {
            PZero . |- "0" : Proc ;

            PPar . ps:HashBag(Proc)
                |- "{" ps.*sep("|") "}" : Proc ;

            POutput . n:Name, q:Name
                |- n "!" "(" q ")" : Proc ;

            PFor . n:Name, ^x.p:[Name -> Proc]
                |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
        },
        equations {},
        rewrites {
            Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
                ~> (PPar {(eval cont Q), ...rest});

            ParCong . | S ~> T
                |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
        }
    "#;

    fn ident(name: &str) -> syn::Ident {
        syn::parse_str(name).expect("test identifier must parse")
    }

    fn var_pattern(name: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(ident(name)))
    }

    fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
    }

    fn scalar_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(SCALAR_FRAGMENT).expect("scalar fragment must parse")
    }

    /// Extract the De Bruijn `BoundVar` index from a single-expr `Par`.
    fn boundvar_index(par: &Par) -> Option<i32> {
        match par.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::EVarBody(evar) => match evar.v.as_ref()?.var_instance.as_ref()? {
                VarInstance::BoundVar(index) => Some(*index),
                _ => None,
            },
            _ => None,
        }
    }

    /// Push a single rewrite onto the scalar fragment (rewrite index 0), lower,
    /// and return the lowered rule for it plus the collected errors.
    fn lower_single_rewrite(
        rewrite: RewriteRule,
    ) -> (RhoNetLoweredRule, Vec<RhoNetLoweringError>) {
        let name = rewrite.name.to_string();
        let mut def = scalar_def();
        def.rewrites.push(rewrite);
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        let id = rule_id_rewrite(0, &name);
        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == id)
            .cloned()
            .unwrap_or_else(|| panic!("rewrite {id} must be lowered"));
        (rule, lowered.errors().to_vec())
    }

    #[test]
    fn native_fold_reuses_scalar_contract_par() {
        let def = scalar_def();
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let expected = scalar_contract_par_for(&lowering, "AddInt")
            .expect("scalar lowering must expose the AddInt contract");
        let native = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::NativeFold { rule_id, par } if rule_id == "rule:AddInt" => {
                    Some(par)
                },
                _ => None,
            })
            .expect("AddInt must lower to a NativeFold rule");
        assert_eq!(native, &expected);

        // A scalar-only language lowers with no diagnostics, and the installed
        // program is exactly the two native-fold contracts.
        assert!(lowered.errors().is_empty(), "scalar-only lowering must not error");
        assert_eq!(lowered.installed_program_par().receives.len(), 2);
    }

    #[test]
    fn base_rewrite_double_negation_lowers_to_flat_sigma_receiver() {
        // Neg(Neg(x)) ~> x — one LHS variable (k = 1), RHS is that variable.
        let mut def = scalar_def();
        def.rewrites.push(RewriteRule {
            name: ident("DoubleNeg"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Neg", vec![apply("Neg", vec![var_pattern("x")])]),
            right: var_pattern("x"),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let par = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::BaseRewrite { rule_id, par }
                    if rule_id == "rule:rewrite:0:DoubleNeg" =>
                {
                    Some(par)
                },
                _ => None,
            })
            .expect("DoubleNeg must lower to a BaseRewrite σ-receiver");

        // Exactly one persistent receive.
        assert_eq!(par.receives.len(), 1);
        let receive = &par.receives[0];
        assert!(receive.persistent, "the σ-receiver must self-reinstall (persistent)");
        // k = 1 LHS variable + 1 out channel ⇒ bind_count / free_count == 2.
        assert_eq!(receive.bind_count, 2);
        assert_eq!(receive.binds.len(), 1);
        assert_eq!(receive.binds[0].free_count, 2);

        // Body is a single send.
        let body = receive.body.as_ref().expect("σ-receiver body");
        assert_eq!(body.sends.len(), 1);
        let send = &body.sends[0];

        // Out channel is BoundVar(0) (formal k = the out channel).
        let channel = send.chan.as_ref().expect("send channel");
        assert_eq!(boundvar_index(channel), Some(0), "out channel must be BoundVar(0)");

        // Payload is BoundVar(rhs_var_index(1, 0)) = BoundVar(1) — the LHS var x.
        assert_eq!(rhs_var_index(1, 0), 1);
        assert_eq!(send.data.len(), 1);
        assert_eq!(
            boundvar_index(&send.data[0]),
            Some(1),
            "RHS payload must be the σ-tuple De Bruijn index of x"
        );

        assert!(lowered.errors().is_empty(), "a well-formed base rewrite must not error");
    }

    #[test]
    fn lower_rhs_variable_uses_first_occurrence_de_bruijn_index() {
        let vars = vec![ident("a"), ident("b"), ident("c")]; // k = 3
        // b is the second variable (occurrence index 1) ⇒ BoundVar(3 - 1) = 2.
        let par = lower_rhs(&var_pattern("b"), &vars, 3).expect("bound RHS variable");
        assert_eq!(boundvar_index(&par), Some(2));
        assert_eq!(rhs_var_index(3, 0), 3);
        assert_eq!(rhs_var_index(3, 2), 1);
    }

    #[test]
    fn lower_lhs_vars_preserves_first_occurrence_and_dedups() {
        // Eq(x, Pair(x, y)) — x appears twice; keep the first occurrence, then y.
        let lhs = apply(
            "Eq",
            vec![var_pattern("x"), apply("Pair", vec![var_pattern("x"), var_pattern("y")])],
        );
        let vars = lower_lhs_vars(&lhs).expect("supported constructor LHS");
        let names: Vec<String> = vars.iter().map(|var| var.to_string()).collect();
        assert_eq!(names, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn collection_lhs_rewrite_is_unsupported_collection_ac() {
        let (rule, errors) = lower_single_rewrite(RewriteRule {
            name: ident("CollLhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: None,
                    elements: vec![var_pattern("P")],
                    rest: Some(ident("rest")),
                }],
            ),
            right: var_pattern("P"),
            is_auto_injected: false,
        });
        assert_eq!(
            rule,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:CollLhs".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }
        );
        assert!(errors.contains(&RhoNetLoweringError::UnsupportedFamily {
            rule_id: "rule:rewrite:0:CollLhs".to_string(),
            family: UnsupportedFamily::CollectionAc,
        }));
    }

    #[test]
    fn map_and_zip_lhs_rewrites_are_unsupported() {
        let (map_rule, _) = lower_single_rewrite(RewriteRule {
            name: ident("MapLhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PMap",
                vec![Pattern::Map {
                    collection: Box::new(var_pattern("xs")),
                    params: vec![ident("x")],
                    body: Box::new(var_pattern("x")),
                }],
            ),
            right: var_pattern("xs"),
            is_auto_injected: false,
        });
        assert!(matches!(
            map_rule,
            RhoNetLoweredRule::Unsupported { family: UnsupportedFamily::MapAc, .. }
        ));

        let (zip_rule, _) = lower_single_rewrite(RewriteRule {
            name: ident("ZipLhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PZip",
                vec![Pattern::Zip {
                    first: Box::new(var_pattern("a")),
                    second: Box::new(var_pattern("b")),
                }],
            ),
            right: var_pattern("a"),
            is_auto_injected: false,
        });
        assert!(matches!(
            zip_rule,
            RhoNetLoweredRule::Unsupported { family: UnsupportedFamily::ZipAc, .. }
        ));
    }

    #[test]
    fn lambda_lhs_rewrite_is_unsupported_lambda_binder() {
        let (rule, _) = lower_single_rewrite(RewriteRule {
            name: ident("LamLhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PLam",
                vec![Pattern::Term(PatternTerm::Lambda {
                    binder: ident("x"),
                    body: Box::new(var_pattern("p")),
                })],
            ),
            right: var_pattern("p"),
            is_auto_injected: false,
        });
        assert!(matches!(
            rule,
            RhoNetLoweredRule::Unsupported { family: UnsupportedFamily::LambdaBinder, .. }
        ));
    }

    #[test]
    fn constructor_rhs_rewrite_is_unsupported_reflection() {
        // Foo(x) ~> Bar(x): the LHS lowers (vars = [x]) but the constructor RHS
        // needs term reflection, which is deferred.
        let (rule, errors) = lower_single_rewrite(RewriteRule {
            name: ident("CtorRhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Foo", vec![var_pattern("x")]),
            right: apply("Bar", vec![var_pattern("x")]),
            is_auto_injected: false,
        });
        assert_eq!(
            rule,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:CtorRhs".to_string(),
                family: UnsupportedFamily::ConstructorRhsNotYetReflectable,
            }
        );
        assert!(errors.contains(&RhoNetLoweringError::UnsupportedFamily {
            rule_id: "rule:rewrite:0:CtorRhs".to_string(),
            family: UnsupportedFamily::ConstructorRhsNotYetReflectable,
        }));
    }

    #[test]
    fn non_semantic_premise_rewrite_is_unsupported_side_condition() {
        // A relation-query premise on a base rewrite cannot be enforced by the
        // flat σ-receiver this (bridge-less) slice, so it fails closed.
        let (rule, _) = lower_single_rewrite(RewriteRule {
            name: ident("SideCond"),
            type_context: Vec::new(),
            premises: vec![Premise::RelationQuery {
                relation: ident("rel"),
                args: vec![ident("x")],
            }],
            left: apply("Id", vec![var_pattern("x")]),
            right: var_pattern("x"),
            is_auto_injected: false,
        });
        assert!(matches!(
            rule,
            RhoNetLoweredRule::Unsupported {
                family: UnsupportedFamily::NonCongruenceSideCondition,
                ..
            }
        ));
    }

    #[test]
    fn equation_lowers_to_congruence_closure() {
        let mut def = scalar_def();
        def.equations.push(Equation {
            name: ident("StructEq"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Neg", vec![apply("Neg", vec![var_pattern("x")])]),
            right: var_pattern("x"),
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:equation:0:StructEq")
            .expect("equation must lower to a congruence closure");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::CongruenceClosure {
                rule_id: "rule:equation:0:StructEq".to_string()
            }
        );
    }

    #[test]
    fn minirho_rewrites_are_unsupported_via_both_detectors() {
        let def =
            syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        // Comm is a BASE rewrite whose Collection LHS is caught by the
        // constructive `lower_lhs_vars` walk.
        let comm = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:0:Comm")
            .expect("Comm must be lowered");
        assert_eq!(
            *comm,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:Comm".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }
        );

        // ParCong is a CONTEXTUAL rewrite whose Collection LHS is caught by the
        // independent P2 detector.
        let parcong = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:1:ParCong")
            .expect("ParCong must be lowered");
        assert_eq!(
            *parcong,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:1:ParCong".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }
        );

        // The independent id re-derivation matched program.rules exactly.
        assert!(
            !lowered
                .errors()
                .iter()
                .any(|error| matches!(error, RhoNetLoweringError::RuleSourceDrift { .. })),
            "faithful re-derivation must not report rule-source drift"
        );
    }

    #[test]
    fn rewrite_pattern_unsupported_detects_families_independently() {
        // Supported: constructor LHS, variable RHS.
        assert_eq!(
            rewrite_pattern_unsupported(&apply("Neg", vec![var_pattern("x")]), &var_pattern("x")),
            None
        );
        // Collection LHS.
        assert_eq!(
            rewrite_pattern_unsupported(
                &Pattern::Collection {
                    coll_type: None,
                    elements: vec![var_pattern("P")],
                    rest: None,
                },
                &var_pattern("P"),
            ),
            Some(UnsupportedFamily::CollectionAc)
        );
        // Constructor RHS.
        assert_eq!(
            rewrite_pattern_unsupported(&var_pattern("x"), &apply("Bar", vec![var_pattern("x")])),
            Some(UnsupportedFamily::ConstructorRhsNotYetReflectable)
        );
        // Lambda nested inside an LHS constructor.
        assert_eq!(
            rewrite_pattern_unsupported(
                &apply(
                    "PLam",
                    vec![Pattern::Term(PatternTerm::Lambda {
                        binder: ident("x"),
                        body: Box::new(var_pattern("p")),
                    })],
                ),
                &var_pattern("p"),
            ),
            Some(UnsupportedFamily::LambdaBinder)
        );
    }
}
