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
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gstring_par, new_send_par, union,
};
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
    /// A RHS variable with no binding occurrence in the LHS. It has no σ-tuple
    /// slot, so a flat receiver cannot supply its value; the rewrite is ill-formed
    /// for σ-receiver lowering and fails closed rather than emit a dangling De
    /// Bruijn index. (A constructor RHS is now reflected — see
    /// [`reflect_term_par`] — so it is no longer an unsupported family.)
    DanglingRhsVariable,
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
    /// A grammar structural constructor. In model b a constructor is realized
    /// inline via RHS term reflection (see [`reflect_term_par`]), never as a
    /// standalone installed contract, so this classification contributes no `Par`
    /// (like [`Self::CongruenceClosure`]) — recognized, not fail-closed.
    StructuralConstructor { rule_id: String },
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
            | Self::StructuralConstructor { rule_id }
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
/// dropped); a non-empty set makes the σ-receiver program fail closed at the
/// install boundary ([`RhoNetLowered::installed_program_par`], Epic 4 #2011),
/// so an unsupported lowering is caught at install time, never after partial
/// execution on the Rho machine.
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// Why a lowered RhoNet program cannot be installed as an executable σ-receiver
/// program (Epic 4 #2011).
///
/// Installing an incomplete program would silently drop unlowered work and no-op
/// at runtime; [`RhoNetLowered::installed_program_par`] returns this instead, so an
/// unsupported / not-yet-lowered rule is caught at INSTALL time — never after
/// partial execution on the Rho machine. Formal model:
/// `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
/// (`Section RhoNetInstallBoundary`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoNetInstallError {
    /// Lowering recorded fail-closed diagnostics; the program is incomplete.
    LoweringErrors(Vec<RhoNetLoweringError>),
    /// A recognized-but-not-yet-executable rule family (`ContextualRewrite` /
    /// `Comm` / `NativeSystemProcess` / `Unsupported`) whose contract the installed
    /// program would silently omit.
    UnmaterializedRule { rule_id: String, family: &'static str },
}

impl std::fmt::Display for RhoNetInstallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RhoNetInstallError::LoweringErrors(errors) => write!(
                f,
                "RhoNet σ-receiver program is not installable: {} lowering diagnostic(s): {errors:?}",
                errors.len()
            ),
            RhoNetInstallError::UnmaterializedRule { rule_id, family } => write!(
                f,
                "RhoNet σ-receiver program is not installable: rule {rule_id} is an unlowered {family} \
                 family that the installed program would silently drop"
            ),
        }
    }
}

impl std::error::Error for RhoNetInstallError {}

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
    /// `BaseRewrite`) into a single installable Rho program — FAIL-CLOSED at the
    /// install boundary (Epic 4 #2011).
    ///
    /// Rather than silently dropping unlowered work (the pre-#2011 behavior, which
    /// produced a partial σ-receiver program that no-ops at runtime), this returns
    /// `Err` so an incomplete lowering is caught at INSTALL time, never after
    /// partial execution on the Rho machine:
    ///
    /// * [`RhoNetInstallError::LoweringErrors`] if lowering recorded any diagnostic
    ///   (e.g. an `Unsupported` family), and
    /// * [`RhoNetInstallError::UnmaterializedRule`] if any rule is a
    ///   recognized-but-not-yet-lowered family (`ContextualRewrite` / `Comm` /
    ///   `NativeSystemProcess` / `Unsupported`) that [`RhoNetLoweredRule::par`]
    ///   would silently omit.
    ///
    /// `StructuralConstructor` / `CongruenceClosure` legitimately contribute no
    /// `Par` (inline RHS reflection / compile-time e-graph closure) and never block
    /// the install. Formal model:
    /// `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
    /// (`Section RhoNetInstallBoundary`).
    pub fn installed_program_par(&self) -> Result<Par, RhoNetInstallError> {
        if !self.errors.is_empty() {
            return Err(RhoNetInstallError::LoweringErrors(self.errors.clone()));
        }
        for rule in &self.rules {
            let family = match rule {
                RhoNetLoweredRule::ContextualRewrite { .. } => "ContextualRewrite",
                RhoNetLoweredRule::Comm { .. } => "Comm",
                RhoNetLoweredRule::NativeSystemProcess { .. } => "NativeSystemProcess",
                RhoNetLoweredRule::Unsupported { .. } => "Unsupported",
                RhoNetLoweredRule::NativeFold { .. }
                | RhoNetLoweredRule::BaseRewrite { .. }
                | RhoNetLoweredRule::StructuralConstructor { .. }
                | RhoNetLoweredRule::CongruenceClosure { .. } => continue,
            };
            return Err(RhoNetInstallError::UnmaterializedRule {
                rule_id: rule.rule_id().to_string(),
                family,
            });
        }
        Ok(self.rules.iter().fold(Par::default(), |program, rule| match rule.par() {
            Some(par) => program.append(par.clone()),
            None => program,
        }))
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
            // A grammar constructor is realized in model b by inline RHS term
            // reflection (see `reflect_term_par`), not as a standalone Rho
            // contract, so it contributes no `Par` — recognized, never
            // fail-closed and never silently dropped.
            RhoNetRuleKind::StructuralConstructor => {
                Some(RhoNetLoweredRule::StructuralConstructor { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::NativeSystemProcess => {
                Some(RhoNetLoweredRule::NativeSystemProcess { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::StructuralCongruence => {
                Some(RhoNetLoweredRule::CongruenceClosure { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::BaseRewrite => {
                lower_base_rewrite(rule, &rewrite_by_id, &program.language_fingerprint, &mut errors)
            },
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
    language_fingerprint: &str,
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
    let rhs_par = match lower_rhs(&rewrite.right, &vars, k, language_fingerprint) {
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
/// with its σ-tuple De Bruijn index and reflecting each constructor application
/// to its tagged-`EList` term value (see [`reflect_term_par`]). Binder,
/// collection, and substitution RHS nodes fail closed exactly like the LHS.
pub(crate) fn lower_rhs(
    rhs: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
) -> Result<Par, UnsupportedFamily> {
    reflect_term_par(rhs, vars, k, language_fingerprint)
}

/// The nominal unforgeable ABI tag identifying a reflected constructor term:
/// `mettail.term.{fingerprint}.{label}`, deterministic per
/// `(language_fingerprint, constructor_label)`. Being carried by a `GPrivate`
/// unforgeable (not a `GString`), it is collision-free with any user `GString`
/// term data. Mirrors the rhocalc bag ABI tag ([`crate::RHOCALC_BAG_ABI_TAG`]).
pub(crate) fn reflect_tag(language_fingerprint: &str, constructor_label: &str) -> String {
    format!(
        "{}{language_fingerprint}.{constructor_label}",
        crate::REFLECTED_TERM_ABI_PREFIX
    )
}

/// A ground (variable-free) constructor term: a constructor label applied to
/// ground children. This is the caller-facing input to
/// [`reflect_ground_term_par`] — the closed value a runtime injection supplies as
/// a σ argument. Because dovetail has already matched the LHS, every σ argument
/// is a fully-instantiated ground term, so this representation carries no bound
/// variables (unlike an RHS pattern, which does).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroundTerm {
    /// The constructor label (a grammar term's label, e.g. `Pair`), reflected
    /// verbatim into the unforgeable tag via [`reflect_tag`].
    pub constructor: String,
    /// The ground children, in constructor-argument order.
    pub children: Vec<GroundTerm>,
}

impl GroundTerm {
    /// A constructor applied to ground children.
    pub fn new(constructor: impl Into<String>, children: Vec<GroundTerm>) -> Self {
        Self { constructor: constructor.into(), children }
    }

    /// A nullary constructor (no children), e.g. the `A`/`B` operands of
    /// `Swap(A, B)`.
    pub fn nullary(constructor: impl Into<String>) -> Self {
        Self::new(constructor, Vec::new())
    }
}

/// A codegen-owned Rho-net σ-injection call, ready for the runtime to run against
/// a language's INSTALLED σ-receiver program.
///
/// This is the Rho-net analogue of [`crate::RhoFoldDataflowInvocation`]: the
/// generated `<Lang>::rho_net_invocation_from_dovetail_to` builds the closed
/// injection `call` `Par` (via [`term_contract_call`] over reflected σ arguments),
/// and a runtime adapter normalizes it into a `RhoMachineInvocation` that runs
/// `installed_rho_net_program_par() ∥ call` and observes `out_channel`. Kept in
/// codegen (no `mettail-rholang-runtime` dependency), exactly like the
/// fold-dataflow path, so generated language crates stay substrate-neutral.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoNetInjectionInvocation {
    /// The closed σ-injection `call` `Par`: `channel!(⟦σ₀⟧, …, ⟦σ_{k-1}⟧, @out_channel)`.
    pub call: Par,
    /// The quoted channel the σ-receiver's reflected RHS rests on.
    pub out_channel: String,
}

/// One base-rewrite σ-receiver injection site derived from a `LanguageDef`: the
/// rule's bare label, its σ-receiver source channel, and the LHS first-occurrence
/// variable order the receiver consumes σ arguments in.
///
/// A runtime σ-injection F-function (`rho_net_invocation_from_dovetail_to`) reads a
/// rewrite firing's justification from the Dovetail report, matches its bare rule
/// label to a site, reorders the report's (name-sorted) σ into
/// [`lhs_var_order`](Self::lhs_var_order), reflects each σ sub-term to a ground
/// `Par`, and sends the reflected arguments on [`channel`](Self::channel). Only
/// rewrites that actually lowered to a σ-receiver ([`RhoNetLoweredRule::BaseRewrite`])
/// are surfaced, so a site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetInjectionSite {
    /// The bare source rewrite label (the σ-receiver rule's label, e.g. `SwapStep`).
    pub rule_label: String,
    /// The σ-receiver source channel (`RhoNetRule::input_channels.first()`).
    pub channel: String,
    /// The LHS first-occurrence variable order the σ-receiver binds σ arguments in
    /// (the order [`lower_lhs_vars`] collects them).
    pub lhs_var_order: Vec<String>,
}

/// Derive every base-rewrite σ-receiver injection site for a language — the sites a
/// runtime σ-injection F-function targets.
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the σ-receiver contracts
/// are compiled from, keeps only the rewrites that lowered to a
/// [`RhoNetLoweredRule::BaseRewrite`] σ-receiver, and reports each one's bare rule
/// label, source channel, and LHS first-occurrence variable order. The channel is
/// content-derived from the LHS pattern (see `RhoNetProgram::pattern_trace_channel`),
/// not the language fingerprint, so a site derived here matches the channel the
/// installed σ-receiver was compiled with for the same rewrite.
pub fn rho_net_injection_sites(def: &LanguageDef) -> Vec<RhoNetInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> =
        program.rules.iter().map(|rule| (rule.id.as_str(), rule)).collect();
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::BaseRewrite { rule_id, .. } = lowered_rule else {
            continue;
        };
        let Some(program_rule) = rule_by_id.get(rule_id.as_str()) else {
            continue;
        };
        let Some(channel) = program_rule.input_channels.first() else {
            continue;
        };
        let Some(rule_label) = program_rule.label.as_deref() else {
            continue;
        };
        let Some(rewrite) = rewrite_by_id.get(rule_id) else {
            continue;
        };
        // A `BaseRewrite` lowered iff `lower_lhs_vars` succeeded, so this cannot
        // fail; a defensive `continue` keeps the derivation total.
        let Ok(vars) = lower_lhs_vars(&rewrite.left) else {
            continue;
        };
        sites.push(RhoNetInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            lhs_var_order: vars.iter().map(|var| var.to_string()).collect(),
        });
    }
    sites
}

/// Reflect a GROUND constructor term to a normalized `Par` value under the SAME
/// constructor reflection ABI as the internal RHS reflector `reflect_term_par`:
///
/// ```text
/// ⟦f(t₁,…,tₙ)⟧ = EList[ GPrivate(reflect_tag(f)), ⟦t₁⟧, …, ⟦tₙ⟧ ]
/// ```
///
/// A ground term binds no σ-tuple variable, so it reflects to a leaf-free nest of
/// tagged `EList`s with no `BoundVar` (the one difference from the RHS reflector,
/// whose variable occurrences become σ-tuple De Bruijn indices). The `GPrivate`
/// head tag is built exactly like the RHS reflector via
/// [`GPrivateBuilder::new_par_from_string`] over the SHARED [`reflect_tag`], and
/// each `EList`'s `locally_free` is the union of the tag's and every child's —
/// so a ground σ argument is byte-for-byte the value a lowered RHS constructor of
/// the same shape would emit, and the runtime `decode_reflected_term` counterpart
/// decodes both identically.
pub fn reflect_ground_term_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    let tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &term.constructor));
    let mut elements = Vec::with_capacity(term.children.len() + 1);
    let mut locally_free = tag.locally_free.clone();
    elements.push(tag);
    for child in &term.children {
        let child = reflect_ground_term_par(child, language_fingerprint);
        locally_free = union(locally_free, child.locally_free.clone());
        elements.push(child);
    }
    new_elist_par(elements, locally_free.clone(), false, None, locally_free, false)
}

/// Build the flat σ-injection call for a base rewrite's σ-receiver:
/// `channel_name!(arg₀, …, arg_{k-1}, @"out_channel")` as normalized `rhoapi::Par`.
///
/// This mirrors [`crate::RhoAstSend::contract_call`]'s shape — the SAME shape the
/// proven scalar operator path uses — but carries already-reflected `Par` σ
/// arguments (each an [`reflect_ground_term_par`] tagged `EList`) rather than
/// [`crate::RhoAstLiteral`] scalars, which cannot hold a `Par`. The `k` σ
/// arguments MUST be supplied in the σ-receiver's canonical first-occurrence LHS
/// variable order (the order `lower_lhs_vars` collects them), and the out channel
/// is appended last as a quoted-name channel (a `GString` `Par`, exactly how
/// `contract_call` lowers its `RhoAstLiteral::QuotedChannel` return channel), so
/// the σ-receiver's formal-`k` out channel (`BoundVar(0)`) sends the reflected RHS
/// there.
pub fn term_contract_call(channel_name: &str, mut args: Vec<Par>, out_channel: &str) -> Par {
    args.push(new_gstring_par(out_channel.to_string(), Vec::new(), false));
    new_send_par(
        new_gstring_par(channel_name.to_string(), Vec::new(), false),
        args,
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// The location channel of a spread term's ROOT — a `loc:`-kind quoted name
/// derived from the site-root string `root_location`.
///
/// Per INV-7 / `rem:fresh` ("freshness is supplied as rho supplies all freshness,
/// by quoting … no ν, no central allocator") the whole location scheme is ν-free:
/// location channels are deterministic ground names, never fresh `New` bindings.
/// `root_location` is the quoted per-site nonce ρ of the `⌜(ρ,ℓ)⌝` idiom — a plain
/// string IS its quote — so distinct redex sites use disjoint channel prefixes.
pub fn spread_root_location(root_location: &str) -> String {
    format!("loc:{root_location}")
}

/// The location channel of the `index`-th child (under constructor `op`) of the
/// node at `parent` — the derived location `ℓ·(op,index)` of `knotted-topoi`
/// Appendix A. The spread emitter and the in-Rho automaton MUST derive every
/// child channel through THIS one helper so they agree on the channel a subterm
/// is published on and matched at.
pub fn spread_child_location(parent: &str, op: &str, index: usize) -> String {
    format!("{parent}/{op}.{index}")
}

/// Spread a ground subject term across per-location channels for in-Rho
/// set-automaton matching (`knotted-topoi` Appendix A):
///
/// ```text
/// ⟦f(t₁,…,tₙ)⟧_ℓ = c(ℓ)!(f̲) │ ∏ᵢ ⟦tᵢ⟧_{ℓ·(f,i)}
/// ```
///
/// Each node publishes ONLY its head tag `f̲` (byte-identical to
/// [`reflect_ground_term_par`]'s tag — the SHARED [`reflect_tag`] ABI) on its
/// deterministic quoted location channel ([`spread_root_location`] /
/// [`spread_child_location`]); the child subterms are spread on the derived child
/// channels, which the automaton knows statically. This is the ν-free scheme
/// (INV-7): a flat parallel composition of ground sends — no `New`, no `BoundVar`
/// — and the message carries the tag ALONE, never child channels. `root_location`
/// is the site root ρ of the `⌜(ρ,ℓ)⌝` freshness idiom.
///
/// The dual of the collapsed [`reflect_ground_term_par`]: same head tags at the
/// same positions, spread across channels rather than nested in one `EList`.
pub fn spread_term_par(term: &GroundTerm, language_fingerprint: &str, root_location: &str) -> Par {
    spread_term_par_at(term, language_fingerprint, &spread_root_location(root_location))
}

fn spread_term_par_at(term: &GroundTerm, language_fingerprint: &str, location: &str) -> Par {
    // This node's head-tag send on its location channel — the tag ALONE (Appendix
    // A publishes `f̲`; child locations are derived, never carried in the message).
    let head_tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &term.constructor));
    let mut par = new_send_par(
        new_gstring_par(location.to_string(), Vec::new(), false),
        vec![head_tag],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    // Spread each child on its derived location channel, in left-to-right `L` order.
    for (index, child) in term.children.iter().enumerate() {
        let child_location = spread_child_location(location, &term.constructor, index);
        par = par.append(spread_term_par_at(child, language_fingerprint, &child_location));
    }
    par
}

/// Reflect an RHS pattern term to a normalized `Par` value under the constructor
/// reflection ABI:
///
/// ```text
/// ⟦f(t₁,…,tₙ)⟧ = EList[ GPrivate(reflect_tag(f)), ⟦t₁⟧, …, ⟦tₙ⟧ ]
/// ```
///
/// A LHS-bound variable reflects to its σ-tuple De Bruijn index (the slice-1
/// `lower_rhs` index logic: first-occurrence formal `i` → `BoundVar(k − i)`). The
/// `GPrivate` head tag is built exactly like the rhocalc bag ABI tag via
/// [`GPrivateBuilder::new_par_from_string`], and the `EList`'s `locally_free` is
/// the union of the tag's and every child's — mirroring `lower_rhocalc`'s bag
/// construction. The decoder counterpart (a future `decode_reflected_term`) will
/// live beside `rholang_runtime::run::par_as_runtime_observation_value`; it is
/// not part of this codegen slice.
///
/// Binder / collection / substitution nodes and a dangling RHS variable (one with
/// no LHS binding) fail closed with their [`UnsupportedFamily`].
fn reflect_term_par(
    pattern: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
) -> Result<Par, UnsupportedFamily> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => match vars.iter().position(|var| var == name) {
            Some(index) => Ok(new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)),
            // A RHS variable not bound by the LHS has no σ-tuple slot; the
            // rewrite is ill-formed for a flat receiver. Fail closed rather than
            // emit a dangling De Bruijn index.
            None => Err(UnsupportedFamily::DanglingRhsVariable),
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
                language_fingerprint,
                &constructor.to_string(),
            ));
            let mut elements = Vec::with_capacity(args.len() + 1);
            let mut locally_free = tag.locally_free.clone();
            elements.push(tag);
            for arg in args {
                let child = reflect_term_par(arg, vars, k, language_fingerprint)?;
                locally_free = union(locally_free, child.locally_free.clone());
                elements.push(child);
            }
            Ok(new_elist_par(elements, locally_free.clone(), false, None, locally_free, false))
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
/// applications and variables are the supported shapes on BOTH sides; a
/// constructor RHS is now reflected ([`reflect_term_par`]), so the RHS is scanned
/// by the same binder/collection/substitution family detector as the LHS (which
/// recurses through constructor args). A dangling RHS variable is caught by the
/// constructive walk, not this family-only detector.
pub(crate) fn rewrite_pattern_unsupported(
    left: &Pattern,
    right: &Pattern,
) -> Option<UnsupportedFamily> {
    pattern_binder_or_collection_family(left)
        .or_else(|| pattern_binder_or_collection_family(right))
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

    // ---- Stage 1 M0: the term-spread encoding (`spread_term_par`) ----

    fn ground(constructor: &str, children: Vec<GroundTerm>) -> GroundTerm {
        GroundTerm::new(constructor, children)
    }

    fn gstring_value(par: &Par) -> Option<String> {
        match par.exprs.first()?.expr_instance.as_ref()? {
            ExprInstance::GString(value) => Some(value.clone()),
            _ => None,
        }
    }

    /// The (location channel, constructor) nodes the spread must publish, in
    /// pre-order — the forward image of `spread_term_par` over a ground term.
    fn expected_spread_nodes(term: &GroundTerm, location: &str, out: &mut Vec<(String, String)>) {
        out.push((location.to_string(), term.constructor.clone()));
        for (index, child) in term.children.iter().enumerate() {
            let child_location = spread_child_location(location, &term.constructor, index);
            expected_spread_nodes(child, &child_location, out);
        }
    }

    /// INV-10 witness: the spread encodes EXACTLY the term — one head-tag send per
    /// node, on the derived location channel, carrying the shared-`reflect_tag`-ABI
    /// head tag (byte-identical to `reflect_ground_term_par`'s tag); and it is
    /// ν-free (no `New`, INV-7) and sends-only (a matching subject, not a program).
    fn assert_spread_encodes(term: &GroundTerm, fingerprint: &str, root: &str) {
        let spread = spread_term_par(term, fingerprint, root);
        let mut expected = Vec::new();
        expected_spread_nodes(term, &spread_root_location(root), &mut expected);

        assert_eq!(spread.sends.len(), expected.len(), "one head-tag send per node");
        assert!(spread.news.is_empty(), "ν-free spread: no New (INV-7)");
        assert!(spread.receives.is_empty(), "a spread subject is sends only");
        assert!(spread.matches.is_empty() && spread.bundles.is_empty(), "no Match/Bundle in a spread");

        for (channel, constructor) in &expected {
            let expected_channel = new_gstring_par(channel.clone(), Vec::new(), false);
            let expected_tag =
                GPrivateBuilder::new_par_from_string(reflect_tag(fingerprint, constructor));
            assert!(
                spread.sends.iter().any(|send| {
                    send.chan.as_ref() == Some(&expected_channel)
                        && send.data == vec![expected_tag.clone()]
                }),
                "spread must publish the head tag for `{constructor}` on `{channel}`"
            );
        }
    }

    #[test]
    fn spread_encodes_a_flat_application() {
        // Swap(A, B): the root plus two nullary leaves on their derived channels.
        let term = ground("Swap", vec![ground("A", Vec::new()), ground("B", Vec::new())]);
        assert_spread_encodes(&term, "testfp", "site0");
        let spread = spread_term_par(&term, "testfp", "site0");
        let channels: std::collections::BTreeSet<String> =
            spread.sends.iter().filter_map(|s| s.chan.as_ref()).filter_map(gstring_value).collect();
        let want: std::collections::BTreeSet<String> =
            ["loc:site0", "loc:site0/Swap.0", "loc:site0/Swap.1"]
                .into_iter()
                .map(String::from)
                .collect();
        assert_eq!(channels, want, "the exact derived location channels");
    }

    #[test]
    fn spread_encodes_a_nested_term() {
        // Pair(Swap(A, B), Swap(B, A)) — two distinct subtrees, six nodes.
        let term = ground(
            "Pair",
            vec![
                ground("Swap", vec![ground("A", Vec::new()), ground("B", Vec::new())]),
                ground("Swap", vec![ground("B", Vec::new()), ground("A", Vec::new())]),
            ],
        );
        assert_spread_encodes(&term, "testfp", "site0");
    }

    #[test]
    fn spread_leaf_head_tag_equals_collapsed_reflection_abi() {
        // A nullary spread is a single head-tag send; the collapsed reflector wraps
        // the SAME tag in an EList — the shared reflect_tag ABI, one dual of the other.
        let leaf = ground("A", Vec::new());
        let spread = spread_term_par(&leaf, "testfp", "site0");
        assert_eq!(spread.sends.len(), 1);
        let spread_tag = &spread.sends[0].data[0];
        let expected_tag = GPrivateBuilder::new_par_from_string(reflect_tag("testfp", "A"));
        assert_eq!(spread_tag, &expected_tag, "spread head tag is the shared-ABI tag");
    }

    mod spread_property {
        use super::*;
        use proptest::prelude::*;

        /// A bounded strategy for ground constructor trees: `A`/`B`/`Nil` leaves and
        /// unary/binary applications, to `max_depth` levels.
        fn arb_ground_term(max_depth: u32) -> impl Strategy<Value = GroundTerm> {
            let leaf = prop_oneof![
                Just(GroundTerm::new("A", Vec::new())),
                Just(GroundTerm::new("B", Vec::new())),
                Just(GroundTerm::new("Nil", Vec::new())),
            ];
            leaf.prop_recursive(max_depth, 48, 3, |inner| {
                prop_oneof![
                    inner.clone().prop_map(|c| GroundTerm::new("Wrap", vec![c])),
                    (inner.clone(), inner.clone())
                        .prop_map(|(l, r)| GroundTerm::new("Swap", vec![l, r])),
                    (inner.clone(), inner)
                        .prop_map(|(l, r)| GroundTerm::new("Pair", vec![l, r])),
                ]
            })
        }

        proptest! {
            /// INV-10 property: an ARBITRARY ground term spreads to exactly one
            /// head-tag send per node, on the derived location channels, ν-free —
            /// `spread_term_par` is an information-preserving transient scaffold.
            #[test]
            fn spread_encodes_arbitrary_ground_terms(term in arb_ground_term(4)) {
                assert_spread_encodes(&term, "propfp", "site0");
            }
        }
    }

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

    /// Like [`lower_single_rewrite`] but returns the whole lowering (needed for
    /// its `language_fingerprint`, from which reflected `GPrivate` tags are
    /// reconstructed) alongside the rewrite's derived rule id.
    fn lower_single_rewrite_full(rewrite: RewriteRule) -> (RhoNetLowered, String) {
        let name = rewrite.name.to_string();
        let mut def = scalar_def();
        def.rewrites.push(rewrite);
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        (lowered, rule_id_rewrite(0, &name))
    }

    /// Extract the `EList` body of a single-expr `Par` (panicking unless the Par
    /// is exactly one plain `EList` expression).
    fn elist_body(par: &Par) -> &models::rhoapi::EList {
        match par.exprs.first().and_then(|expr| expr.expr_instance.as_ref()) {
            Some(ExprInstance::EListBody(list)) => list,
            other => panic!("expected an EList body, got {other:?}"),
        }
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
        // program is exactly the two native-fold contracts (installs cleanly).
        assert!(lowered.errors().is_empty(), "scalar-only lowering must not error");
        assert_eq!(
            lowered
                .installed_program_par()
                .expect("a diagnostic-free native-fold program installs")
                .receives
                .len(),
            2
        );
    }

    #[test]
    fn install_boundary_fails_closed_on_lowering_errors() {
        // A lowering diagnostic (e.g. an unsupported family) makes the σ-receiver
        // program non-installable — caught at INSTALL time, never after partial
        // execution on the Rho machine (Epic 4 #2011).
        let lowered = RhoNetLowered {
            language_fingerprint: "test-fp".to_string(),
            rules: vec![RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:BadAc".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }],
            errors: vec![RhoNetLoweringError::UnsupportedFamily {
                rule_id: "rule:rewrite:0:BadAc".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }],
        };
        match lowered.installed_program_par() {
            Err(RhoNetInstallError::LoweringErrors(errors)) => assert_eq!(errors.len(), 1),
            other => panic!("expected LoweringErrors, got {other:?}"),
        }
    }

    #[test]
    fn install_boundary_fails_closed_on_unmaterialized_deferred_family() {
        // A recognized-but-deferred family (`Comm`) carries no `par` and no error;
        // installing it would silently drop the rule, so the boundary fails closed
        // and names the offending family (Epic 4 #2011).
        let lowered = RhoNetLowered {
            language_fingerprint: "test-fp".to_string(),
            rules: vec![
                RhoNetLoweredRule::BaseRewrite {
                    rule_id: "rule:rewrite:0:Ok".to_string(),
                    par: Par::default(),
                },
                RhoNetLoweredRule::Comm { rule_id: "rule:rewrite:1:Join".to_string() },
            ],
            errors: Vec::new(),
        };
        match lowered.installed_program_par() {
            Err(RhoNetInstallError::UnmaterializedRule { rule_id, family }) => {
                assert_eq!(family, "Comm");
                assert_eq!(rule_id, "rule:rewrite:1:Join");
            },
            other => panic!("expected UnmaterializedRule(Comm), got {other:?}"),
        }
    }

    #[test]
    fn install_boundary_admits_materialized_and_inline_only_rules() {
        // Legitimately-inline rules (`StructuralConstructor` / `CongruenceClosure`)
        // contribute no `Par` yet must NOT block the install — only a diagnostic or
        // a deferred family does.
        let lowered = RhoNetLowered {
            language_fingerprint: "test-fp".to_string(),
            rules: vec![
                RhoNetLoweredRule::StructuralConstructor { rule_id: "rule:term:0:A".to_string() },
                RhoNetLoweredRule::CongruenceClosure { rule_id: "rule:eq:0:Cong".to_string() },
            ],
            errors: Vec::new(),
        };
        let installed = lowered
            .installed_program_par()
            .expect("inline-only rules install as an empty program");
        assert_eq!(installed.receives.len(), 0);
        assert_eq!(installed.sends.len(), 0);
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
        // The fingerprint is unused for a bare variable RHS.
        let par = lower_rhs(&var_pattern("b"), &vars, 3, "fp").expect("bound RHS variable");
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

    /// `Swap(a, b) ~> Pair(b, a)`: the reflected σ-receiver body sends the tagged
    /// `EList[ GPrivate("mettail.term.{fp}.Pair"), BoundVar(1), BoundVar(2) ]` —
    /// the RHS order `(b, a)` using the LHS first-occurrence σ-tuple indices.
    #[test]
    fn base_rewrite_reflects_constructor_rhs_to_tagged_elist() {
        let (lowered, id) = lower_single_rewrite_full(RewriteRule {
            name: ident("Swap"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Swap", vec![var_pattern("a"), var_pattern("b")]),
            right: apply("Pair", vec![var_pattern("b"), var_pattern("a")]),
            is_auto_injected: false,
        });

        let par = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::BaseRewrite { rule_id, par } if *rule_id == id => Some(par),
                _ => None,
            })
            .expect("Swap must lower to a BaseRewrite σ-receiver");

        // k = 2 LHS variables (a, b) + 1 out channel ⇒ bind_count 3.
        let receive = &par.receives[0];
        assert_eq!(receive.bind_count, 3);
        let body = receive.body.as_ref().expect("σ-receiver body");
        let send = &body.sends[0];
        assert_eq!(
            boundvar_index(send.chan.as_ref().expect("send channel")),
            Some(0),
            "out channel must be BoundVar(0)"
        );

        // Payload is the reflected Pair term: EList[ GPrivate(tag), b, a ].
        assert_eq!(send.data.len(), 1);
        let elist = elist_body(&send.data[0]);
        assert_eq!(elist.ps.len(), 3, "head tag + two children");

        let expected_tag = GPrivateBuilder::new_par_from_string(format!(
            "mettail.term.{}.Pair",
            lowered.language_fingerprint
        ));
        assert_eq!(elist.ps[0], expected_tag, "head is the unforgeable Pair reflection tag");

        // RHS order (b, a): b = rhs_var_index(2, 1) = 1, a = rhs_var_index(2, 0) = 2.
        assert_eq!(rhs_var_index(2, 1), 1);
        assert_eq!(rhs_var_index(2, 0), 2);
        assert_eq!(boundvar_index(&elist.ps[1]), Some(1), "first child is b");
        assert_eq!(boundvar_index(&elist.ps[2]), Some(2), "second child is a");

        assert!(lowered.errors().is_empty(), "a reflectable constructor RHS must not error");
    }

    /// `Wrap(x) ~> Outer(Inner(x))`: a nested constructor RHS reflects to a nested
    /// tagged `EList`; the inner `Inner(x)` is `[GPrivate("…Inner"), BoundVar(1)]`
    /// embedded as the sole child of `[GPrivate("…Outer"), …]`.
    #[test]
    fn base_rewrite_reflects_nested_constructor_rhs() {
        let (lowered, id) = lower_single_rewrite_full(RewriteRule {
            name: ident("Wrap"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Wrap", vec![var_pattern("x")]),
            right: apply("Outer", vec![apply("Inner", vec![var_pattern("x")])]),
            is_auto_injected: false,
        });

        let par = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::BaseRewrite { rule_id, par } if *rule_id == id => Some(par),
                _ => None,
            })
            .expect("Wrap must lower to a BaseRewrite σ-receiver");

        let send = &par.receives[0].body.as_ref().expect("σ-receiver body").sends[0];
        let outer = elist_body(&send.data[0]);
        assert_eq!(outer.ps.len(), 2, "outer head tag + one child");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!(
                "mettail.term.{}.Outer",
                lowered.language_fingerprint
            )),
            "outer head is the unforgeable Outer reflection tag"
        );

        let inner = elist_body(&outer.ps[1]);
        assert_eq!(inner.ps.len(), 2, "inner head tag + one child");
        assert_eq!(
            inner.ps[0],
            GPrivateBuilder::new_par_from_string(format!(
                "mettail.term.{}.Inner",
                lowered.language_fingerprint
            )),
            "inner head is the unforgeable Inner reflection tag"
        );
        // x = rhs_var_index(1, 0) = 1.
        assert_eq!(rhs_var_index(1, 0), 1);
        assert_eq!(boundvar_index(&inner.ps[1]), Some(1), "inner child is x");

        assert!(lowered.errors().is_empty());
    }

    /// The Swap→Pair base rewrite surfaces exactly one injection site whose channel
    /// equals the σ-receiver's source channel and whose LHS variable order is the
    /// first-occurrence order (a, b) the receiver binds σ arguments in.
    #[test]
    fn rho_net_injection_sites_surface_base_rewrite_channel_and_var_order() {
        let mut def = scalar_def();
        def.rewrites.push(RewriteRule {
            name: ident("Swap"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Swap", vec![var_pattern("a"), var_pattern("b")]),
            right: apply("Pair", vec![var_pattern("b"), var_pattern("a")]),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        // The σ-receiver's source channel, resolved exactly as the runtime injection
        // must reproduce it (the base rewrite's first input channel).
        let base_rewrite_id = rule_id_rewrite(0, "Swap");
        let expected_channel = program
            .rules
            .iter()
            .find(|rule| rule.id == base_rewrite_id)
            .and_then(|rule| rule.input_channels.first())
            .expect("Swap base rewrite must have a source channel")
            .clone();
        assert!(lowered.rules().iter().any(|rule| matches!(
            rule,
            RhoNetLoweredRule::BaseRewrite { rule_id, .. } if *rule_id == base_rewrite_id
        )));

        let sites = rho_net_injection_sites(&def);
        assert_eq!(sites.len(), 1, "one base-rewrite σ-receiver ⇒ one injection site");
        assert_eq!(
            sites[0],
            RhoNetInjectionSite {
                rule_label: "Swap".to_string(),
                channel: expected_channel,
                lhs_var_order: vec!["a".to_string(), "b".to_string()],
            }
        );
    }

    /// A scalar-only language (no base rewrites) surfaces no injection sites, so a
    /// non-rho-net language emits no σ-injection F-function match arms.
    #[test]
    fn rho_net_injection_sites_are_empty_without_base_rewrites() {
        assert!(rho_net_injection_sites(&scalar_def()).is_empty());
    }

    /// `Id(x) ~> y`: a RHS variable with no LHS binding has no σ-tuple slot, so the
    /// rewrite fails closed even though the LHS itself lowers.
    #[test]
    fn dangling_rhs_variable_is_unsupported() {
        let (rule, errors) = lower_single_rewrite(RewriteRule {
            name: ident("Dangle"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Id", vec![var_pattern("x")]),
            right: var_pattern("y"),
            is_auto_injected: false,
        });
        assert_eq!(
            rule,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:Dangle".to_string(),
                family: UnsupportedFamily::DanglingRhsVariable,
            }
        );
        assert!(errors.contains(&RhoNetLoweringError::UnsupportedFamily {
            rule_id: "rule:rewrite:0:Dangle".to_string(),
            family: UnsupportedFamily::DanglingRhsVariable,
        }));
    }

    /// Fail-closed still holds through reflection: a collection nested inside a
    /// constructor RHS is caught while recursing into the constructor's args.
    #[test]
    fn collection_inside_constructor_rhs_is_unsupported() {
        let (rule, _) = lower_single_rewrite(RewriteRule {
            name: ident("CollRhs"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply("Id", vec![var_pattern("x")]),
            right: apply(
                "Wrap",
                vec![Pattern::Collection {
                    coll_type: None,
                    elements: vec![var_pattern("x")],
                    rest: None,
                }],
            ),
            is_auto_injected: false,
        });
        assert!(matches!(
            rule,
            RhoNetLoweredRule::Unsupported { family: UnsupportedFamily::CollectionAc, .. }
        ));
    }

    /// Every grammar term produces a `StructuralConstructor` rule; in model b the
    /// constructor is realized inline via RHS reflection, so it is recognized (not
    /// fail-closed) and contributes no installed `Par`.
    #[test]
    fn structural_constructor_rule_is_recognized_without_par() {
        let def = scalar_def();
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:term:0:AddInt")
            .expect("AddInt term must lower to a structural-constructor rule");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::StructuralConstructor {
                rule_id: "rule:term:0:AddInt".to_string()
            }
        );
        assert_eq!(rule.par(), None, "a structural constructor contributes no installed Par");
        assert!(
            !lowered.errors().iter().any(|error| matches!(
                error,
                RhoNetLoweringError::UnsupportedFamily { rule_id, .. }
                    if rule_id == "rule:term:0:AddInt"
            )),
            "a structural constructor is recognized, not fail-closed"
        );
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

    /// The Swap→Pair demo language: nullary `A`/`B`, binary constructors
    /// `Pair`/`Swap` (all non-scalar `Proc`, so all four are rejected and covered
    /// by structural Rho-AST dispositions), and the base rewrite `Swap(x, y) ~>
    /// Pair(y, x)` that lowers to the σ-receiver the runtime bridge injects into.
    const SWAP_DEMO_FRAGMENT: &str = r#"
        name: SwapDemo,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types {
            Proc
        },
        terms {
            A . |- "A" : Proc ;
            B . |- "B" : Proc ;
            Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
            Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
        },
        equations {},
        rewrites {
            SwapStep . |- (Swap x y) ~> (Pair y x) ;
        }
    "#;

    /// `reflect_ground_term_par` reflects a ground constructor tree to the tagged
    /// `EList` ABI, sharing `reflect_tag` with the RHS reflector: the reflection
    /// of the ground `Pair(B, A)` is exactly the value the `Swap` σ-receiver emits
    /// once `a ↦ A`, `b ↦ B` are substituted into the reflected RHS `Pair(b, a)`.
    #[test]
    fn reflect_ground_term_par_reflects_ground_pair_to_tagged_elist() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let pair = GroundTerm::new(
            "Pair",
            vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")],
        );
        let par = reflect_ground_term_par(&pair, fp);

        let outer = elist_body(&par);
        assert_eq!(outer.ps.len(), 3, "head tag + two ground children");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Pair")),
            "head is the shared unforgeable Pair reflection tag"
        );

        let b = elist_body(&outer.ps[1]);
        assert_eq!(b.ps.len(), 1, "nullary B is a lone head tag");
        assert_eq!(
            b.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.B"))
        );
        let a = elist_body(&outer.ps[2]);
        assert_eq!(a.ps.len(), 1, "nullary A is a lone head tag");
        assert_eq!(
            a.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.A"))
        );

        // Ground reflection binds no σ variable: no BoundVar leaves anywhere and
        // empty locally_free (byte-identical to a lowered ground RHS constructor).
        assert!(par.locally_free.is_empty());
        assert_eq!(boundvar_index(&par), None);
    }

    /// `term_contract_call` builds `chan!(arg₀, …, @"out")`: a single flat send on
    /// `GString(chan)` whose data is the σ arguments in first-occurrence order with
    /// the quoted out channel appended last (mirroring `RhoAstSend::contract_call`).
    #[test]
    fn term_contract_call_builds_flat_send_with_quoted_out_channel() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let arg_a = reflect_ground_term_par(&GroundTerm::nullary("A"), fp);
        let arg_b = reflect_ground_term_par(&GroundTerm::nullary("B"), fp);
        let call = term_contract_call("sa:pattern/demo", vec![arg_a.clone(), arg_b.clone()], "OUT");

        assert_eq!(call.sends.len(), 1, "exactly one flat injection send");
        assert!(call.receives.is_empty());
        let send = &call.sends[0];
        assert!(!send.persistent, "the injection call is a one-shot send");
        assert_eq!(
            send.chan.as_ref().expect("send channel"),
            &new_gstring_par("sa:pattern/demo".to_string(), Vec::new(), false),
            "channel is the σ-receiver's source name"
        );
        assert_eq!(send.data.len(), 3, "two σ args + the out channel");
        assert_eq!(send.data[0], arg_a, "first σ arg in first-occurrence order");
        assert_eq!(send.data[1], arg_b, "second σ arg in first-occurrence order");
        assert_eq!(
            send.data[2],
            new_gstring_par("OUT".to_string(), Vec::new(), false),
            "out channel appended last as a quoted-name channel"
        );
    }

    /// The Swap→Pair language passes the Rho-default flip gate (its four
    /// non-scalar constructors are rejected and covered by structural Rho-AST
    /// dispositions), and its installed Rho-net program is exactly the one
    /// persistent `(k+1)`-ary σ-receiver for the base rewrite `SwapStep`. This is
    /// the plan the R-2 runtime demo injects into; deriving the σ source channel
    /// from `input_channels.first()` here mirrors what the demo does.
    #[test]
    fn swap_language_plans_to_installed_sigma_receiver() {
        use crate::backend::{
            plan_rho_default_backend, suggest_rejected_rule_dispositions,
            RhoDefaultBackendRequirements,
        };
        use crate::{RhoCoverageEvidence, RhoGuardCoverageEvidence};

        let def = syn::parse_str::<LanguageDef>(SWAP_DEMO_FRAGMENT).expect("Swap fragment parses");
        let lowering = lower_language_def(&def);
        // All four constructors are non-scalar → rejected, none lowered.
        assert_eq!(lowering.lowered, Vec::<String>::new());
        assert_eq!(lowering.rejected, vec!["A", "B", "Pair", "Swap"]);

        let dispositions = suggest_rejected_rule_dispositions(&def, &lowering);
        let requirements = RhoDefaultBackendRequirements {
            coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
            guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
        };
        let plan = plan_rho_default_backend(&def, requirements)
            .unwrap_or_else(|err| panic!("Swap language must flip to Rho: {:?}", err.decision));
        assert_eq!(plan.language_name(), "SwapDemo");

        // The base rewrite lowered to exactly one persistent 3-ary σ-receiver
        // (k = 2 LHS vars + 1 out channel); the four constructors contribute no
        // installed Par.
        let installed = plan
            .installed_rho_net_program_par()
            .expect("the clean Swap base-rewrite program installs");
        assert_eq!(installed.receives.len(), 1, "one σ-receiver installed");
        assert_eq!(installed.sends.len(), 0);
        assert_eq!(installed.receives[0].bind_count, 3);
        assert!(installed.receives[0].persistent);

        // The σ-receiver's source channel is the base rewrite's first input
        // channel — the name the runtime demo sends the injection to.
        let swap_rule = plan
            .rho_net_program()
            .rules
            .iter()
            .find(|rule| rule.label.as_deref() == Some("SwapStep"))
            .expect("SwapStep base rewrite must be planned");
        assert_eq!(swap_rule.kind, RhoNetRuleKind::BaseRewrite);
        let channel = swap_rule
            .input_channels
            .first()
            .expect("σ-receiver source channel");
        assert!(
            channel.starts_with("sa:pattern/"),
            "σ source is the LHS pattern-trace channel, got {channel:?}"
        );

        // No lowering diagnostics for the well-formed base rewrite, and the flip
        // decision is unblocked.
        assert!(
            !plan.rho_net_lowered().errors().iter().any(|error| matches!(
                error,
                RhoNetLoweringError::UnsupportedFamily { rule_id, .. } if rule_id.contains("SwapStep")
            )),
            "the well-formed Swap base rewrite must not be fail-closed"
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
        // Constructor RHS of bound variables is now reflectable ⇒ supported.
        assert_eq!(
            rewrite_pattern_unsupported(&var_pattern("x"), &apply("Bar", vec![var_pattern("x")])),
            None
        );
        // ...but a binder nested inside a constructor RHS still fails closed.
        assert_eq!(
            rewrite_pattern_unsupported(
                &var_pattern("x"),
                &apply(
                    "Bar",
                    vec![Pattern::Term(PatternTerm::Lambda {
                        binder: ident("y"),
                        body: Box::new(var_pattern("x")),
                    })],
                ),
            ),
            Some(UnsupportedFamily::LambdaBinder)
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
