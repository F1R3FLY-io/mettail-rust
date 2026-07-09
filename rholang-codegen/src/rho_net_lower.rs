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

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::{LanguageDef, Premise, RewriteRule};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_ast::types::{CollectionType, EvalMode};
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{EAnd, EEq, Expr, KeyValuePair, Par, Receive, ReceiveBind, Var};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_eset_par, new_freevar_par, new_gstring_par,
    new_send_par, new_wildcard_par, union,
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
    /// A native system process (`![…]` HOL term) whose evaluation mode is NOT
    /// `fold` (Stage 3e). A `fold` native process reduces to a host-computed
    /// value INSIDE Dovetail saturation, producing a rewrite justification whose
    /// contractum the native σ-injection delegates. A `step` (or annotation-less)
    /// native process reduces on a different path (e.g. a partial `step` rule
    /// routing to an `Err` normal form) and exposes no funded-best contractum for
    /// the flat dispatch receiver to forward, so it fails closed with this precise
    /// reason rather than installing a receiver that no native firing would drive.
    NativeSystemProcessNotFold,
}

/// One lowered RhoNet rule.
///
/// `NativeFold` and `BaseRewrite` carry a materialized `Par`; the remaining
/// variants are recognized-but-not-yet-materialized classifications (they
/// contribute no `Par` to [`RhoNetLowered::installed_program_par`]).
#[derive(Debug, Clone, PartialEq)]
pub enum RhoNetLoweredRule {
    /// A native SCALAR fold `AddInt(a, b) ~> a + b` (a `![…] fold` HOL term whose output is a
    /// native scalar and whose operator the Rho scalar path DOES lower to an in-Rho contract —
    /// `+`, `-`, `*`, `==` — hence classified `RhoNetRuleKind::NativeFold`, not the rejected
    /// `NativeSystemProcess` family) lowered to a persistent flat DISPATCH RECEIVER whose body
    /// forwards the host-computed reduced value (Stage 3f, the scalar-fold analogue of
    /// [`Self::NativeSystemProcessRewrite`]). By the fold-vs-equation criterion (D3, INV-9) a
    /// native COMPUTE is directed motion changing a CLTS barb, so it fires as a COMM (a lossless
    /// iso coercion / `NormCast` would instead be compile-time congruence — see
    /// [`Self::CongruenceClosure`]).
    ///
    /// model-b: the host (Dovetail) matches `AddInt(a, b)` AND computes the reduced value `a + b`
    /// via its trusted `fold` handler, and the reduced value reflects to the receiver's single
    /// ground σ slot, which the body emits as `⟦value⟧`. The receiver is the flat one-slot
    /// [`sigma_receiver_par`] `for (result, out <- c) { out!(result) }` — IDENTICAL to
    /// [`Self::NativeSystemProcessRewrite`] — resting on the rule's dispatch channel
    /// (`RhoNetRule::input_channels.first()`, the `sa:scalar/{label}` trace); the native-fold
    /// injection site ([`rho_net_native_fold_injection_sites`]) delivers the firing's CONTRACTUM
    /// (the reduced value, carried on [`RuntimeRewriteJustification::contractum`]) in that slot.
    /// Materialized/installed exactly like [`Self::NativeSystemProcessRewrite`] — so native-scalar
    /// firing rides the same install∥call seam. The structural rendezvous (the COMM on the fold's
    /// dedicated dispatch channel) is real; only the PAYLOAD is delegated to the trusted handler.
    ///
    /// This same variant ALSO carries the disposition of a NON-`fold` scalar op (a `step`
    /// comparison, or a bare scalar constructor): such an op has no funded-best contractum, so its
    /// `par` is instead the Model-T Rho SCALAR CONTRACT (`contract @"L"(@a, @b, ret){ret!(a op b)}`,
    /// [`lower_native_fold`]) — recognized and installed, but never driven by the Model-N native-fold
    /// σ-injection (it surfaces no native-fold injection site). Only a `fold` op gets the firing
    /// dispatch receiver; the discriminator is [`lower_native_fold`].
    ///
    /// FV: `formal/rocq/rho_bridge/theories/FoldMotionVsCongruence.v` (a computing fold changes a
    /// barb ⇒ COMM, while a lossless iso preserves all barbs ⇒ congruence) +
    /// `NativeSystemProcessBoundary.v` (total-or-reject dispatch + the emitted payload is exactly
    /// the trusted handler's value) + the trust boundary `RhoHostObligationBoundary.v`.
    NativeFold { rule_id: String, par: Par },
    /// A base rewrite lowered to a flat σ-receiver contract.
    BaseRewrite { rule_id: String, par: Par },
    /// A linear with-rest HashBag AC base rewrite un-skipped to an in-Rho AC receiver
    /// (`ac_rule_receiver`): the connective process-soup pattern matches the bag ORDER-
    /// INDEPENDENTLY (native `sub_pars`/`MaximumBipartiteMatch`) and fires `⟦R⟧σ` on the
    /// dynamic out. Materialized exactly like [`Self::BaseRewrite`] — installed into the
    /// program and given a real AC injection site — so AC firing rides the same install∥call
    /// seam (Stage AC). Nested/non-linear/no-rest / Map-Zip AC rules stay `Unsupported`.
    AcRewrite { rule_id: String, par: Par },
    /// A canonical single-receive Rholang COMMUNICATION rewrite
    /// `op{(PFor N cont), (POutput N Q), ...rest} ~> op{(eval cont Q), ...rest}` un-skipped to a
    /// NON-LINEAR AC σ-receiver ([`comm_rule_receiver`]): the connective process-soup pattern
    /// matches the two STRUCTURED elements ORDER-INDEPENDENTLY, a `Receive.condition`
    /// `EEq(N_recv, N_send)` enforces the shared channel `N ≡ N` (reject-safe), and the body emits
    /// the bag RHS `@"ac:op"!(reduct) | rest` where the reduct is the host-computed contractum
    /// `cont[Q/y]`. Materialized exactly like [`Self::AcRewrite`] — installed into the program and
    /// fired by a Comm injection ([`comm_contract_call`]) on the same install∥call seam (Stage 3b).
    /// The FIRST non-linear AC firing. A structured/non-linear AC rewrite whose RHS is not a
    /// single-substitution with-rest bag (e.g. Ambient's structural `OpenRule`) declines here and
    /// is instead handled by [`Self::StructuralAcRewrite`].
    CommRewrite { rule_id: String, par: Par },
    /// A STRUCTURAL non-linear AC rewrite `op{ E0, E1, ...rest } ~> op{ r0, …, r_{m-1}, ...rest }`
    /// (Stage 3d — the Ambient-calculus `OpenRule` `{(open N P), N[Q], ...rest} ~> {P, Q, ...rest}`)
    /// un-skipped to a NON-LINEAR AC σ-receiver ([`structural_ac_rule_receiver`]). Like
    /// [`Self::CommRewrite`] the connective process-soup pattern matches the `k` STRUCTURED elements
    /// ORDER-INDEPENDENTLY and a `Receive.condition` `EEq(N_0, N_1)` enforces the shared channel
    /// `N ≡ N` (reject-safe); UNLIKE Comm the RHS is a PURE STRUCTURAL restructuring (no
    /// substitution) — each RHS element `r_j` is a bare LHS-element argument variable, so the body
    /// splices `@"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | rest` where every `r_j` is delivered
    /// directly from the firing's σ (it is an LHS-element arg — recovered by
    /// [`rho_net_structural_ac_injection_sites`]). Materialized exactly like [`Self::CommRewrite`] —
    /// installed into the program and fired by a structural-AC injection
    /// ([`structural_ac_contract_call`]) on the same install∥call seam. A structured/non-linear AC
    /// rewrite whose RHS elements are not all bare LHS-element arg variables (e.g. Ambient's NESTED
    /// `InRule`/`OutRule`) declines and stays `Unsupported` (fail-closed).
    StructuralAcRewrite { rule_id: String, par: Par },
    /// A grammar structural constructor. In model b a constructor is realized
    /// inline via RHS term reflection (see [`reflect_term_par`]), never as a
    /// standalone installed contract, so this classification contributes no `Par`
    /// (like [`Self::CongruenceClosure`]) — recognized, not fail-closed.
    StructuralConstructor { rule_id: String },
    /// A structural-congruence equation (compile-time e-graph closure).
    CongruenceClosure { rule_id: String },
    /// A congruence (contextual) rewrite lowered to an atomic polyadic JOIN receiver
    /// (`contextual_join_receiver_par`, INV-6): a length-`n` `Receive.binds`, one flat
    /// σ-slot per premise hole on that premise's location channel, whose body emits the
    /// reduced context `⟦K'⟧` on the rule's dynamic out channel. Materialized exactly like
    /// [`Self::BaseRewrite`]/[`Self::AcRewrite`] — installed into the program and given a
    /// contextual injection site — so contextual firing rides the same install∥call seam
    /// (Stage 3a). A congruence rule whose context is AC / binder / substitution, or which
    /// carries a non-congruence side condition, has no flat join image and stays
    /// `Unsupported` (fail-closed).
    ContextualRewrite { rule_id: String, par: Par },
    /// A binder/β-substitution base rewrite `App(Lam(^x. b), a) ~> subst(b, x := a)`
    /// lowered to a flat σ-receiver whose body FORWARDS the host-computed reduct
    /// (Stage 3c). The receiver is a plain `(k+1)`-ary σ-receiver
    /// ([`sigma_receiver_par`]) whose reflected RHS is `BoundVar(scope-slot)`: the
    /// host (Dovetail, model-b) does the matching AND the capture-avoiding
    /// substitution, and the reduced term reflects to the scope variable's ground σ
    /// slot, which the receiver emits as `⟦R⟧σ`. Materialized exactly like
    /// [`Self::BaseRewrite`]/[`Self::AcRewrite`]/[`Self::ContextualRewrite`] —
    /// installed into the program and given a substitution injection site
    /// ([`rho_net_subst_injection_sites`]) that delivers the firing's contractum in
    /// the scope slot — so binder firing rides the same install∥call seam. A
    /// substitution rewrite whose scope is a genuinely-free variable (open
    /// substitution), or whose RHS is not a top-level `Subst`/`MultiSubst`, has no
    /// flat σ-receiver image and stays `Unsupported` (fail-closed).
    SubstRewrite { rule_id: String, par: Par },
    /// A native system-process dispatch `NativeProc(a₀..a_{k-1}) ~> ⟨native value⟩`
    /// lowered to a persistent flat DISPATCH RECEIVER whose body forwards the
    /// host-computed native value (Stage 3e). The `NativeProc` is a `![…] fold`
    /// HOL term (BigInt/large-int arithmetic, `PowInt`, factorial-style built-ins)
    /// that the Rho scalar-contract path rejects, so the value is produced by a
    /// TRUSTED native handler (the host's Dovetail native fold) rather than by an
    /// in-Rho scalar contract: model-b — the host matches AND computes, the
    /// reduced value reflects to a ground σ slot, and the receiver fires `⟦value⟧`.
    /// The receiver is the flat one-slot [`sigma_receiver_par`] `for (result, out
    /// <- c) { out!(result) }`; the native injection site
    /// ([`rho_net_native_injection_sites`]) delivers the firing's CONTRACTUM (the
    /// native handler's value, carried on
    /// [`RuntimeRewriteJustification::contractum`]) in that slot. Materialized
    /// exactly like [`Self::SubstRewrite`] — installed into the program and given a
    /// native injection site — so native dispatch rides the same install∥call
    /// seam. The structural rendezvous (the COMM on the native rule's dedicated
    /// dispatch channel) is real; only the PAYLOAD is delegated to the trusted
    /// handler. A native process whose evaluation mode is not `fold` (no
    /// host-computed contractum) stays `Unsupported`
    /// ([`UnsupportedFamily::NativeSystemProcessNotFold`], fail-closed).
    ///
    /// FV: `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v`
    /// (total-or-reject dispatch + the emitted payload is exactly the trusted
    /// handler's value — the encoder delegates, never fabricates) and the trust
    /// boundary `RhoHostObligationBoundary.v`.
    NativeSystemProcessRewrite { rule_id: String, par: Par },
    /// A declared join (COMM) — deferred to the next slice.
    Comm { rule_id: String },
    /// A native system-process dispatch whose source construct has no flat
    /// dispatch-receiver image (fail-closed; see
    /// [`UnsupportedFamily::NativeSystemProcessNotFold`]). Retained as a recognized
    /// classify-only family so a genuinely-unhandleable native process is caught at
    /// the install boundary, never silently dropped.
    NativeSystemProcess { rule_id: String },
    /// A rule whose source construct is out of scope this slice (fail-closed).
    Unsupported {
        rule_id: String,
        family: UnsupportedFamily,
    },
}

impl RhoNetLoweredRule {
    /// The stable RhoNet rule identifier this lowered rule corresponds to.
    pub fn rule_id(&self) -> &str {
        match self {
            Self::NativeFold { rule_id, .. }
            | Self::BaseRewrite { rule_id, .. }
            | Self::AcRewrite { rule_id, .. }
            | Self::CommRewrite { rule_id, .. }
            | Self::StructuralAcRewrite { rule_id, .. }
            | Self::ContextualRewrite { rule_id, .. }
            | Self::SubstRewrite { rule_id, .. }
            | Self::NativeSystemProcessRewrite { rule_id, .. }
            | Self::StructuralConstructor { rule_id }
            | Self::CongruenceClosure { rule_id }
            | Self::Comm { rule_id }
            | Self::NativeSystemProcess { rule_id }
            | Self::Unsupported { rule_id, .. } => rule_id,
        }
    }

    /// The materialized contract `Par`, when this rule lowered to executable Rho
    /// AST (`NativeFold`/`BaseRewrite`).
    pub fn par(&self) -> Option<&Par> {
        match self {
            Self::NativeFold { par, .. }
            | Self::BaseRewrite { par, .. }
            | Self::AcRewrite { par, .. }
            | Self::CommRewrite { par, .. }
            | Self::StructuralAcRewrite { par, .. }
            | Self::ContextualRewrite { par, .. }
            | Self::SubstRewrite { par, .. }
            | Self::NativeSystemProcessRewrite { par, .. } => Some(par),
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
    UnsupportedFamily {
        rule_id: String,
        family: UnsupportedFamily,
    },
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
    /// A recognized-but-not-yet-executable rule family (`Comm` /
    /// `NativeSystemProcess` / `Unsupported`) whose contract the installed
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
    ///   recognized-but-not-yet-lowered family (`Comm` / `NativeSystemProcess` /
    ///   `Unsupported`) that [`RhoNetLoweredRule::par`] would silently omit.
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
                RhoNetLoweredRule::Comm { .. } => "Comm",
                RhoNetLoweredRule::NativeSystemProcess { .. } => "NativeSystemProcess",
                RhoNetLoweredRule::Unsupported { .. } => "Unsupported",
                RhoNetLoweredRule::NativeFold { .. }
                | RhoNetLoweredRule::BaseRewrite { .. }
                | RhoNetLoweredRule::AcRewrite { .. }
                | RhoNetLoweredRule::CommRewrite { .. }
                | RhoNetLoweredRule::StructuralAcRewrite { .. }
                | RhoNetLoweredRule::ContextualRewrite { .. }
                | RhoNetLoweredRule::SubstRewrite { .. }
                | RhoNetLoweredRule::NativeSystemProcessRewrite { .. }
                | RhoNetLoweredRule::StructuralConstructor { .. }
                | RhoNetLoweredRule::CongruenceClosure { .. } => continue,
            };
            return Err(RhoNetInstallError::UnmaterializedRule {
                rule_id: rule.rule_id().to_string(),
                family,
            });
        }
        Ok(self
            .rules
            .iter()
            .fold(Par::default(), |program, rule| match rule.par() {
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

    // Correlate native-system-process rule-ids back to their source `GrammarRule` (the `![…]`
    // HOL term), which carries the eval mode + result category `program.rules` does not retain
    // (Stage 3e). Keyed exactly as `add_native_system_process_rules` derives the id
    // (`rule_id_native(index, label)`), so the two walks cannot drift.
    let term_by_id: HashMap<String, &GrammarRule> = def
        .terms
        .iter()
        .enumerate()
        .map(|(index, term)| (rule_id_native(index, &term.label.to_string()), term))
        .collect();

    // Correlate native SCALAR-FOLD rule-ids back to their source `GrammarRule` (Stage 3f). A
    // `NativeFold` rule is keyed by `rule_id_scalar(label)` (NOT `rule_id_native`), so it correlates
    // by the term LABEL the scalar contract carries (`RhoNetRule::label`), which is the term's
    // constructor label — unique across `def.terms`.
    let term_by_label: HashMap<String, &GrammarRule> = def
        .terms
        .iter()
        .map(|term| (term.label.to_string(), term))
        .collect();

    for rule in &program.rules {
        let lowered = match rule.kind {
            RhoNetRuleKind::NativeFold => {
                lower_native_fold(rule, lowering, &term_by_label, &mut errors)
            },
            // A grammar constructor is realized in model b by inline RHS term
            // reflection (see `reflect_term_par`), not as a standalone Rho
            // contract, so it contributes no `Par` — recognized, never
            // fail-closed and never silently dropped.
            RhoNetRuleKind::StructuralConstructor => {
                Some(RhoNetLoweredRule::StructuralConstructor { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::NativeSystemProcess => {
                lower_native_system_process(rule, &term_by_id, &mut errors)
            },
            RhoNetRuleKind::StructuralCongruence => {
                Some(RhoNetLoweredRule::CongruenceClosure { rule_id: rule.id.clone() })
            },
            RhoNetRuleKind::BaseRewrite => lower_base_rewrite(
                rule,
                &rewrite_by_id,
                def,
                &program.language_fingerprint,
                &mut errors,
            ),
            RhoNetRuleKind::ContextualRewrite => lower_contextual_rewrite(
                rule,
                &rewrite_by_id,
                &program.language_fingerprint,
                &mut errors,
            ),
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

/// Lower a `NativeFold`-classified rule (a scalar op with an in-Rho scalar contract).
///
/// Two dispositions, discriminated by the fold-vs-equation criterion (D3) applied to the op's
/// evaluation mode (Stage 3f):
///
/// * **A `fold` native scalar op** (`AddInt(a, b) ~> a + b`, a `![a + b] fold` HOL term) is
///   directed COMPUTE — it fires as a COMM. It lowers to the flat one-slot DISPATCH RECEIVER
///   [`sigma_receiver_par`] `for (result, out <- c) { out!(result) }` on the rule's dispatch
///   channel (`sa:scalar/{label}`) — IDENTICAL to [`lower_native_system_process`] — and gets a
///   native-fold injection site ([`rho_net_native_fold_injection_sites`]). model-b: the host
///   (Dovetail) matches AND computes the reduced value `a + b` via its trusted `fold` handler, and
///   the firing's CONTRACTUM reflects to the receiver's single ground σ slot, which the body
///   forwards on `@out` as `⟦value⟧`. The structural rendezvous (the COMM on the dispatch channel)
///   is real; only the PAYLOAD is delegated (`RhoHostObligationBoundary.v`).
///
/// * **A NON-`fold` native scalar op** (a `step` comparison like `EqInt`, or a bare scalar
///   constructor) has no funded-best contractum for the flat receiver to forward, so it keeps its
///   Model-T Rho SCALAR CONTRACT artifact ([`scalar_contract_par_for`]) `contract @"L"(@a, @b,
///   ret) { ret!(a op b) }` — recognized and installed, but NOT driven by the Model-N native-fold
///   σ-injection (it surfaces NO native-fold injection site). This keeps a mixed scalar language
///   installable (never a fail-close) and is byte-identical to the pre-Stage-3f behavior for every
///   non-fold scalar op.
///
/// The Rho scalar contract's GInt-scalar-arg ABI differs from the reflected-ground-term σ-injection
/// ABI, so the campaign's model-b firing forwards the host-computed contractum through the dispatch
/// receiver rather than re-deriving `a op b` in-Rho — hence the `fold` disposition installs the
/// dispatch receiver (Model-N), while the scalar contract remains the separate Model-T artifact
/// (`lowering.scalar_contract_abi`, consumed by `invocation.rs`).
fn lower_native_fold(
    rule: &RhoNetRule,
    lowering: &RhoLowering,
    term_by_label: &HashMap<String, &GrammarRule>,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let label = rule.label.as_deref().unwrap_or(rule.id.as_str());
    // D3: a `fold` op is directed compute (fires as a COMM). `native_rule_shape` returns `Some`
    // iff the source term is a `fold` HOL term (the SAME fold-gate the injection site uses, so the
    // receiver and its injection agree by construction).
    let is_fold = term_by_label
        .get(label)
        .and_then(|term| native_rule_shape(term))
        .is_some();
    if is_fold {
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
        // The one-slot dispatch receiver `for (result, out <- c) { out!(result) }`: `k = 1` σ slot
        // (the reduced value), body forwards that slot (`BoundVar(rhs_var_index(1, 0))`) —
        // IDENTICAL to `lower_native_system_process`.
        let rhs_par = new_boundvar_par(rhs_var_index(1, 0), Vec::new(), false);
        let par = sigma_receiver_par(1, rhs_par, source);
        return Some(RhoNetLoweredRule::NativeFold { rule_id: rule.id.clone(), par });
    }
    // Non-`fold`: keep the proven Model-T scalar operator contract (installed, never driven by the
    // Model-N native-fold σ-injection).
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
    def: &LanguageDef,
    language_fingerprint: &str,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let Some(rewrite) = rewrite_by_id.get(rule.id.as_str()) else {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };

    // D3 (fold-vs-equation criterion, INV-9): a LOSSLESS ISO COERCION — an auto-injected
    // cast-canonicalization `NormCast<Src>To<Tgt>In<Result>` `(Cast<Src> v) ~> (Cast<Tgt>
    // (SrcToTgt v))` (uniquely identified by its `Premise::SyntheticInjGuard`, which auto-injection
    // adds to `NormCast*` rules ONLY) — is a SYMMETRIC representation change that preserves the
    // value, NOT directed motion changing a CLTS barb. So it compiles to compile-time structural
    // congruence (the host normalizes the cast in its e-graph closure), NOT a firing COMM: it
    // lowers to a [`RhoNetLoweredRule::CongruenceClosure`] (recognized, contributes no `Par`, does
    // NOT install a firing receiver, and — unlike an `Unsupported` fail-close — does NOT block the
    // install boundary). This is exactly the D3 boundary a COMPUTING fold (`NativeFold`,
    // [`lower_native_fold`]) sits on the other side of: the fold FIRES (motion), the lossless cast
    // is CONGRUENCE (plugging). FV: `formal/rocq/rho_bridge/theories/FoldMotionVsCongruence.v`.
    if is_lossless_cast_congruence(rewrite) {
        return Some(RhoNetLoweredRule::CongruenceClosure { rule_id: rule.id.clone() });
    }

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
        // Stage AC un-skip: a HashBag AC LHS has no flat σ-receiver (`lower_lhs_vars` fails
        // `CollectionAc`), but a linear with-rest HashBag rule lowers to an in-Rho AC receiver
        // via `ac_rule_receiver`, on the rule's OWN trace channel — the same channel the AC
        // injection targets (accept-triad coherence by symmetric derivation). Fall through to
        // `Unsupported{CollectionAc}` when it declines (nested/non-linear/no-rest, or a LHS
        // whose collection is not a confirmed HashBag — Set/Map await a later slice).
        Err(UnsupportedFamily::CollectionAc) => {
            let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
            let source = rule
                .input_channels
                .first()
                .and_then(|channel| resolve_channel(channel).ok());
            // Linear with-rest HashBag AC (bare-var elements) → AcRewrite.
            if let Some(par) = source.clone().and_then(|source| {
                ac_rule_receiver(
                    &rewrite.left,
                    &rewrite.right,
                    source,
                    language_fingerprint,
                    resolved_kind.clone(),
                    Some(def),
                )
            }) {
                return Some(RhoNetLoweredRule::AcRewrite { rule_id: rule.id.clone(), par });
            }
            // Stage 3b: the canonical single-receive COMMUNICATION rule (structured non-linear AC
            // LHS + substitution-in-bag RHS) → a non-linear AC σ-receiver whose `Receive.condition`
            // `EEq(N_recv, N_send)` enforces the shared channel. Declines for every other
            // structured/non-linear AC rewrite (e.g. Ambient's structural `OpenRule`).
            if let Some(par) = source.clone().and_then(|source| {
                comm_rule_receiver(
                    &rewrite.left,
                    &rewrite.right,
                    source,
                    language_fingerprint,
                    resolved_kind.clone(),
                )
            }) {
                return Some(RhoNetLoweredRule::CommRewrite { rule_id: rule.id.clone(), par });
            }
            // Stage 3d: a STRUCTURAL non-linear AC rewrite (structured non-linear AC LHS + a
            // STRUCTURAL — no-substitution — bag RHS whose fixed elements are bare LHS-element arg
            // variables, e.g. Ambient's `OpenRule` `{(open N P), N[Q], ...rest} ~> {P, Q, ...rest}`)
            // → a non-linear AC σ-receiver whose `Receive.condition` `EEq(N_0, N_1)` enforces the
            // shared channel and whose body splices the σ-delivered reduct elements with `rest`.
            // Declines (stays `Unsupported`) for a nested-element AC rewrite (Ambient's
            // `InRule`/`OutRule`) whose RHS elements are not all bare LHS-element arg variables.
            if let Some(par) = source.and_then(|source| {
                structural_ac_rule_receiver(
                    &rewrite.left,
                    &rewrite.right,
                    source,
                    language_fingerprint,
                    resolved_kind,
                )
            }) {
                return Some(RhoNetLoweredRule::StructuralAcRewrite {
                    rule_id: rule.id.clone(),
                    par,
                });
            }
            return Some(record_unsupported(rule, UnsupportedFamily::CollectionAc, errors));
        },
        Err(family) => return Some(record_unsupported(rule, family, errors)),
    };
    let k = vars.len();

    // Stage 3c: a binder/β-substitution rewrite whose RHS is a top-level `Subst`/`MultiSubst`
    // (`App(Lam(^x. b), a) ~> subst(b, x := a)`) lowers to a `SubstRewrite` σ-receiver whose
    // body forwards the host-computed reduct at the scope slot. Route it BEFORE the generic
    // base path, whose P2 defensive detector (`rewrite_pattern_unsupported`) would otherwise
    // reject the substitution RHS. A malformed subst (open scope / non-variable scope) falls
    // closed inside `lower_subst_rewrite`.
    if is_top_level_substitution(&rewrite.right) {
        return lower_subst_rewrite(rule, rewrite, &vars, k, language_fingerprint, errors);
    }

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

/// Whether a rewrite RHS is a top-level β-style substitution — `subst(scope, …)` /
/// `(eval scope arg)`, i.e. a `Pattern::Term(Subst { .. })` or
/// `Pattern::Term(MultiSubst { .. })` (never nested inside an `Apply`/collection).
/// The Stage 3c substitution-rewrite shape (mirrors the "WHOLE RHS, never nested"
/// requirement of the Dovetail `is_substitution_rewrite` classifier).
pub(crate) fn is_top_level_substitution(rhs: &Pattern) -> bool {
    matches!(
        rhs,
        Pattern::Term(PatternTerm::Subst { .. }) | Pattern::Term(PatternTerm::MultiSubst { .. })
    )
}

/// The shape of a binder/β-substitution base rewrite `LHS ~> subst(scope, …)`: the LHS
/// σ-variables (first-occurrence order, binder-excluded — the order [`lower_lhs_vars`]
/// collects them) and the SCOPE variable (the `scope`/`term` of the RHS `Subst`/`MultiSubst`,
/// which must be a bound LHS variable). Returns `None` unless the RHS is a top-level
/// substitution whose scope is a bound LHS variable — a non-variable / open scope (open
/// substitution), or a LHS with no flat σ image, declines here and the caller fails closed.
///
/// This is the SINGLE subst-LHS/RHS extraction shared by [`lower_subst_rewrite`] (which
/// materializes the installed σ-receiver) and [`rho_net_subst_injection_sites`] (which surfaces
/// the runtime subst injection site), so both agree byte-for-byte on the σ order and the scope
/// variable. The AC/contextual analogue of [`ac_rule_shape`].
pub(crate) fn subst_rule_shape(left: &Pattern, right: &Pattern) -> Option<(Vec<Ident>, Ident)> {
    let scope = match right {
        Pattern::Term(PatternTerm::MultiSubst { scope, .. }) => scope.as_ref(),
        Pattern::Term(PatternTerm::Subst { term, .. }) => term.as_ref(),
        _ => return None,
    };
    let Pattern::Term(PatternTerm::Var(scope_var)) = scope else {
        return None;
    };
    let vars = lower_lhs_vars(left).ok()?;
    // The scope variable MUST be a bound LHS σ-slot (a closed substitution); an open
    // substitution under a genuinely-free scope has no slot to carry the reduct.
    if !vars.iter().any(|var| var == scope_var) {
        return None;
    }
    Some((vars, scope_var.clone()))
}

/// Lower a binder/β-substitution base rewrite to its flat `SubstRewrite` σ-receiver (Stage 3c).
///
/// The receiver is a plain `(k+1)`-ary σ-receiver ([`sigma_receiver_par`]) whose reflected RHS is
/// `BoundVar(scope-slot)` (built by [`reflect_term_par`]'s `Subst`/`MultiSubst` arm): the host
/// (Dovetail, model-b) matches the redex AND applies the capture-avoiding substitution, and the
/// reduced term reflects to the scope variable's ground σ slot — which the receiver body forwards
/// on the dynamic out channel as `⟦R⟧σ`. The substitution injection site
/// ([`rho_net_subst_injection_sites`]) delivers the firing's contractum in that slot.
///
/// FAIL-CLOSED (never silently deferred): a malformed subst whose scope is not a bound LHS
/// variable — an OPEN substitution — is rejected by [`reflect_term_par`] with
/// [`UnsupportedFamily::Substitution`]; a resolution failure surfaces via `errors`.
fn lower_subst_rewrite(
    rule: &RhoNetRule,
    rewrite: &RewriteRule,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    // The RHS `⟦R⟧σ` = `BoundVar(scope-slot)` (the host hands the reduct at the scope slot).
    // An open substitution (scope not a bound LHS var) fails closed here.
    // A subst RHS is a top-level `Subst`/`MultiSubst` (never a collection), so no HashBag bag-RHS
    // resolver is needed here (`None`) — the scope reflects to its σ-slot regardless.
    let rhs_par = match reflect_term_par(&rewrite.right, vars, k, language_fingerprint, None) {
        Ok(par) => par,
        Err(family) => return Some(record_unsupported(rule, family, errors)),
    };
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
    Some(RhoNetLoweredRule::SubstRewrite { rule_id: rule.id.clone(), par })
}

/// The S-native LOCATE→VALUE bridge (Stage 4): gate the trusted handler's native VALUE on the
/// automaton LOCATING the native process head IN RHO.
///
/// The positional receiver network's accept for a native `NativeProc(a₀..a_{k-1})` entry sends
/// `trigger!(⟦a₀⟧, …, ⟦a_{k-1}⟧, @out)` once it has MATCHED the head tag + arity and CAPTURED the
/// `k` structural args ON the interpreter (the `sa:` τ COMMs) — exactly the base-rewrite accept,
/// since a native process is a plain App-rooted node. This bridge binds those `k` captures (which
/// only GATE the delivery — the value is NOT computed from them) plus the dynamic `out`, and
/// forwards the host-supplied native value on `dispatch_channel`, where the installed
/// `NativeSystemProcessRewrite` / `NativeFold` dispatch receiver `for (result, out <- c) {
/// out!(result) }` forwards it on `@out`.
///
/// So the LOCATION is the automaton's (produced in Rho from the structurally reflected subject,
/// never the report σ), and ONLY the VALUE stays the trusted handler's payload (the firing's
/// CONTRACTUM — the inherent boundary modeled by `NativeSystemProcessBoundary.v` /
/// `RhoHostObligationBoundary.v`), delivered as `dispatch(⟦value⟧, out)`.
///
/// `value` MUST be a closed ground `Par` (the reflected contractum). `trigger_channel` is the
/// native entry's accept channel (its [`InRhoMatchingRuleset`](crate::InRhoMatchingRuleset)
/// `accept_channels` entry); `dispatch_channel` is the installed dispatch receiver's SOURCE.
/// Non-persistent: one located native firing delivers exactly one value.
pub fn native_locate_bridge_par(
    trigger_channel: &str,
    k: usize,
    dispatch_channel: &str,
    value: Par,
) -> Par {
    let formal_count = k + 1;
    // The dynamic out channel is the LAST bound formal (`BoundVar(0)`), exactly as the σ-receiver
    // binds its out slot; the `k` captured args are the higher indices, bound but unused here.
    let out_channel = bound_formal(formal_count, k);
    let out_free = create_bit_vector(&[0]);
    // Body: `dispatch_channel!(⟦value⟧, out)` — the value is a closed ground `Par`, so the send is
    // free only in the `out` slot (`BoundVar(0)`).
    let body = new_send_par(
        new_gstring_par(dispatch_channel.to_string(), Vec::new(), false),
        vec![value, out_channel],
        false,
        out_free.clone(),
        false,
        out_free,
        false,
    );
    let source = new_gstring_par(trigger_channel.to_string(), Vec::new(), false);
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
        persistent: false,
        peek: false,
        bind_count: formal_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    Par::default().with_receives(vec![receive])
}

/// The bare RULE LABEL a `fold` native system process's Dovetail firing carries in a runtime
/// rewrite justification (Stage 3e): `"{Category}_{Label}"` — the op-enum variant identity the
/// macro's native-fold rule uses (`{Lang}::fold::{Category}_{Label}`), bare-ified by the report
/// producer's `split("::").nth(2)` to `"{Category}_{Label}"`. Returns `None` unless the term is a
/// `fold`-mode native process (a `step` / annotation-less native process reduces on a different
/// path and exposes no funded-best contractum for the flat dispatch receiver to forward).
///
/// This is the SINGLE native-process shape shared by [`lower_native_system_process`] (which
/// materializes the installed dispatch receiver) and [`rho_net_native_injection_sites`] (which
/// surfaces the runtime native injection site), so both agree byte-for-byte on the rule label the
/// native σ-injection F-function matches the firing on. The native-dispatch analogue of
/// [`subst_rule_shape`].
pub(crate) fn native_rule_shape(term: &GrammarRule) -> Option<String> {
    // Only a `fold` native process reduces to a host-computed value inside Dovetail saturation
    // (producing a rewrite justification whose contractum the injection delegates). A `step`
    // native process (partial / routing to an `Err` normal form) has no funded-best contractum.
    if term.eval_mode != Some(EvalMode::Fold) {
        return None;
    }
    Some(format!("{}_{}", term.category, term.label))
}

/// Lower a native system process `NativeProc(a₀..a_{k-1}) ~> ⟨native value⟩` to its flat
/// `NativeSystemProcessRewrite` DISPATCH RECEIVER (Stage 3e).
///
/// The receiver is the one-slot [`sigma_receiver_par`] `for (result, out <- c) { out!(result) }`:
/// the host (Dovetail, model-b) matches the redex AND computes the native value via its TRUSTED
/// native handler (the `![…] fold` HOL body — BigInt add, `PowInt`, factorial), and the reduced
/// value reflects to the receiver's single ground σ slot, which the body forwards on the dynamic
/// out channel as `⟦value⟧`. The native injection site ([`rho_net_native_injection_sites`])
/// delivers the firing's CONTRACTUM (the native handler's value) in that slot; the structural
/// rendezvous is the COMM on the native rule's dedicated dispatch channel
/// (`RhoNetRule::input_channels.first()`), so only the PAYLOAD is delegated to the trusted
/// handler (`RhoHostObligationBoundary.v`).
///
/// FAIL-CLOSED (never silently deferred): a native process whose evaluation mode is not `fold`
/// (no host-computed contractum for the receiver to forward) is rejected with
/// [`UnsupportedFamily::NativeSystemProcessNotFold`]; a missing source term or an unresolvable
/// dispatch channel surfaces via `errors`.
fn lower_native_system_process(
    rule: &RhoNetRule,
    term_by_id: &HashMap<String, &GrammarRule>,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let Some(term) = term_by_id.get(rule.id.as_str()) else {
        // The RhoNet program carried a native rule with no source `GrammarRule` — the program
        // was paired with a drifted def; fail closed rather than fabricate a receiver.
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };
    // A non-`fold` native process has no host-computed contractum; fail closed with the precise
    // reason (never install a receiver no native firing would drive).
    if native_rule_shape(term).is_none() {
        return Some(record_unsupported(
            rule,
            UnsupportedFamily::NativeSystemProcessNotFold,
            errors,
        ));
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
    // The one-slot dispatch receiver `for (result, out <- c) { out!(result) }`: `k = 1` σ slot
    // (the delegated native value), body forwards that slot (`BoundVar(rhs_var_index(1, 0))`).
    let rhs_par = new_boundvar_par(rhs_var_index(1, 0), Vec::new(), false);
    let par = sigma_receiver_par(1, rhs_par, source);
    Some(RhoNetLoweredRule::NativeSystemProcessRewrite { rule_id: rule.id.clone(), par })
}

/// Lower a congruence (contextual) rewrite `⟦…S_i ~> T_i… |- K(S_1..S_n) ~> K'(T_1..T_n)⟧`
/// to the atomic polyadic JOIN receiver (INV-6, Stage 3a).
///
/// The hypothesis-carrying contextual rewrite fires as ONE `Receive` with `n` binds — one
/// flat σ-slot per premise hole on that premise's location channel — whose body emits the
/// reduced context `⟦K'⟧` on the rule's dynamic out channel; the contextual injection
/// ([`contextual_contract_call`]) delivers the `n` reduced holes `T_i`. See
/// [`contextual_join_receiver_par`].
///
/// FAIL-CLOSED (never silently deferred) when the rewrite has no flat join image:
///
///  - the independent P2 detector reports a binder / collection / substitution context
///    (e.g. RhoCalc's `ParCong` over an AC `PPar` bag has an AC-collection LHS/RHS) — such a
///    context stays `Unsupported{family}`, exactly as before this slice;
///  - a non-congruence side condition (a semantic-predicate guard, freshness, relation
///    query, universal) appears as a premise — it has no join slot ([`congruence_targets`]);
///  - the reduced context RHS `K'` is unreflectable (binder / collection / substitution /
///    dangling hole) — caught by [`reflect_term_par`].
fn lower_contextual_rewrite(
    rule: &RhoNetRule,
    rewrite_by_id: &HashMap<String, &RewriteRule>,
    language_fingerprint: &str,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    let Some(rewrite) = rewrite_by_id.get(rule.id.as_str()) else {
        errors.push(RhoNetLoweringError::RuleSourceDrift { rule_id: rule.id.clone() });
        return None;
    };
    // Independent P2 detector: a binder / collection / substitution context (RhoCalc's
    // ParCong over an AC PPar bag) has no flat contextual-join image — fail closed with the
    // out-of-scope family, exactly as the classify-only predecessor did.
    if let Some(family) = rewrite_pattern_unsupported(&rewrite.left, &rewrite.right) {
        return Some(record_unsupported(rule, family, errors));
    }
    match contextual_join_rule_par(rewrite, rule, language_fingerprint) {
        Ok(par) => Some(RhoNetLoweredRule::ContextualRewrite { rule_id: rule.id.clone(), par }),
        Err(family) => Some(record_unsupported(rule, family, errors)),
    }
}

/// Build the atomic polyadic-join `Par` for a contextual rewrite, or return the
/// [`UnsupportedFamily`] the rewrite fails closed on. The premise holes come from the
/// congruence premises (in premise order), the premise location channels from the rule's
/// `input_channels[1..]` (the LHS trace channel is `input_channels[0]`), and the reduced
/// context `⟦K'⟧` from reflecting `rewrite.right` over the `n` target holes.
fn contextual_join_rule_par(
    rewrite: &RewriteRule,
    rule: &RhoNetRule,
    language_fingerprint: &str,
) -> Result<Par, UnsupportedFamily> {
    let targets = congruence_targets(&rewrite.premises)?;
    let n = targets.len();
    // The reduced context `⟦K'⟧`: `rewrite.right` reflected over the target holes, so hole
    // `i` (`targets[i]`) reflects to `BoundVar(rhs_var_index(n, i)) = BoundVar(n - i)` — the
    // reverse-De-Bruijn slot the join binds it at (out is `BoundVar(0)`).
    // A contextual (congruence) RHS with a collection context is already rejected by the P2
    // detector before reaching here (RhoCalc's `ParCong` over an AC bag), so no HashBag bag-RHS
    // resolver is threaded (`None`) — a bag context stays fail-closed, exactly as before.
    let context_rhs = reflect_term_par(&rewrite.right, &targets, n, language_fingerprint, None)?;
    // The `n` premise location channels are `input_channels[1..]` (channel 0 is the LHS
    // trace channel). A congruence premise contributes exactly one channel, so the slice
    // has length `n` — a drift here means the rule was paired with a mismatched program.
    let premise_channel_names = rule
        .input_channels
        .get(1..)
        .filter(|channels| channels.len() == n)
        .ok_or(UnsupportedFamily::NonCongruenceSideCondition)?;
    let mut premise_channels = Vec::with_capacity(n);
    for name in premise_channel_names {
        premise_channels.push(resolve_channel(name).map_err(|_| {
            // An empty premise channel name has no location rendezvous; treat it as an
            // unenforceable side condition rather than emit a nameless join.
            UnsupportedFamily::NonCongruenceSideCondition
        })?);
    }
    Ok(contextual_join_receiver_par(context_rhs, &premise_channels))
}

/// The `n` target (reduced-hole) variables of a contextual rewrite's congruence premises,
/// in premise order. Returns [`UnsupportedFamily::NonCongruenceSideCondition`] if ANY
/// premise is not a `Premise::Congruence` hole (a semantic-predicate guard, freshness,
/// relation query, or universal has no join slot and must stay off-machine / fail closed),
/// so a mixed-premise congruence rule does not silently drop its side condition.
fn congruence_targets(premises: &[Premise]) -> Result<Vec<Ident>, UnsupportedFamily> {
    let mut targets = Vec::with_capacity(premises.len());
    for premise in premises {
        match premise {
            Premise::Congruence { target, .. } => targets.push(target.clone()),
            _ => return Err(UnsupportedFamily::NonCongruenceSideCondition),
        }
    }
    Ok(targets)
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

/// D3 (fold-vs-equation criterion, INV-9): is this rewrite a LOSSLESS ISO COERCION that must be
/// treated as compile-time structural CONGRUENCE (not a firing COMM)?
///
/// True iff the rewrite carries a [`Premise::SyntheticInjGuard`] — the guard auto-injection adds
/// EXCLUSIVELY to its synthetic cast-canonicalization `NormCast<Src>To<Tgt>In<Result>` rules (see
/// `mettail_ast::auto_inject`: the post-process loop skips any rule whose name does not start with
/// `"NormCast"`). Such a rule `(Cast<Src> v) ~> (Cast<Tgt> (SrcToTgt v))` rewrites a cast wrapper to
/// its canonical form — a lossless representation change over the numeric-widening lattice, NOT
/// directed motion changing a CLTS barb — so per D3 it is congruence (plugging), never a COMM. A
/// COMPUTING native fold ([`lower_native_fold`]) sits on the FIRING side of this exact boundary.
fn is_lossless_cast_congruence(rewrite: &RewriteRule) -> bool {
    rewrite
        .premises
        .iter()
        .any(|premise| matches!(premise, Premise::SyntheticInjGuard { .. }))
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
///
/// **De Bruijn binder environment (Stage 3c)**: a `Lambda`/`MultiLambda` node
/// brings its binder(s) into scope over the body — a bound occurrence of a binder
/// is NOT a free σ-slot (it is delivered by the binder, not by σ), while the free
/// variables of the body ARE σ-slots (first-occurrence order preserved). So the
/// σ-slots of a binder rule's LHS are exactly its free metavariables, correctly
/// excluding the binder. A `Subst`/`MultiSubst` node in a MATCH (LHS) position has
/// no receiver representation and stays fail-closed (`Substitution`); the binder
/// firing lives in the RHS ([`reflect_term_par`]), not the LHS.
pub(crate) fn lower_lhs_vars(pattern: &Pattern) -> Result<Vec<Ident>, UnsupportedFamily> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    let mut bound = Vec::new();
    collect_lhs_vars(pattern, &mut vars, &mut seen, &mut bound)?;
    Ok(vars)
}

fn collect_lhs_vars(
    pattern: &Pattern,
    vars: &mut Vec<Ident>,
    seen: &mut HashSet<String>,
    bound: &mut Vec<String>,
) -> Result<(), UnsupportedFamily> {
    match pattern {
        Pattern::Term(term) => collect_lhs_vars_term(term, vars, seen, bound),
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
    }
}

fn collect_lhs_vars_term(
    term: &PatternTerm,
    vars: &mut Vec<Ident>,
    seen: &mut HashSet<String>,
    bound: &mut Vec<String>,
) -> Result<(), UnsupportedFamily> {
    match term {
        PatternTerm::Var(ident) => {
            // A bound occurrence (in scope of an enclosing binder) is delivered by the
            // binder, not by σ — it is never a free σ-slot.
            if bound.contains(&ident.to_string()) {
                return Ok(());
            }
            if seen.insert(ident.to_string()) {
                vars.push(ident.clone());
            }
            Ok(())
        },
        PatternTerm::Apply { args, .. } => {
            for arg in args {
                collect_lhs_vars(arg, vars, seen, bound)?;
            }
            Ok(())
        },
        // A binder brings `binder`/`binders` into scope over `body`: push them onto the
        // De Bruijn environment, collect the body's FREE σ-slots, then pop (the binder
        // leaves scope). The binder itself is excluded from σ.
        PatternTerm::Lambda { binder, body } => {
            bound.push(binder.to_string());
            let result = collect_lhs_vars(body, vars, seen, bound);
            bound.pop();
            result
        },
        PatternTerm::MultiLambda { binders, body } => {
            for binder in binders {
                bound.push(binder.to_string());
            }
            let result = collect_lhs_vars(body, vars, seen, bound);
            for _ in binders {
                bound.pop();
            }
            result
        },
        // A substitution in a MATCH (LHS) position has no flat-receiver representation
        // (the set automaton matches structure, not a substitution result). The binder
        // firing is a RHS construct; a subst LHS fails closed.
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
    // A base rewrite (non-AC LHS) keeps its byte-identical reflection: a collection RHS stays
    // fail-closed (`None` — no HashBag bag-RHS resolver). A bag-VALUED RHS is only reachable via
    // the AC path ([`ac_rule_receiver`]), whose LHS is the operand bag; a base rewrite has no AC
    // receiver to consume/produce the soup carrier.
    reflect_term_par(rhs, vars, k, language_fingerprint, None)
}

/// The nominal unforgeable ABI tag identifying a reflected constructor term:
/// `mettail.term.{fingerprint}.{label}`, deterministic per
/// `(language_fingerprint, constructor_label)`. Being carried by a `GPrivate`
/// unforgeable (not a `GString`), it is collision-free with any user `GString`
/// term data. Mirrors the rhocalc bag ABI tag ([`crate::RHOCALC_BAG_ABI_TAG`]).
pub(crate) fn reflect_tag(language_fingerprint: &str, constructor_label: &str) -> String {
    format!("{}{language_fingerprint}.{constructor_label}", crate::REFLECTED_TERM_ABI_PREFIX)
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
    /// The ground children, in constructor-argument order (or the bag elements when
    /// [`coll_type`](Self::coll_type) is `Some`).
    pub children: Vec<GroundTerm>,
    /// `Some(kind)` when this term is an AC operand COLLECTION — its elements are
    /// reflected as the kind's native matching carrier (a process-`Par` soup for
    /// `HashBag`), order-independent and multiplicity-preserving, so the native
    /// spatial matcher can AC-match it. `None` (the common case) reflects positionally
    /// as the tagged `EList`.
    pub coll_type: Option<CollectionType>,
}

impl GroundTerm {
    /// A constructor applied to ground children (positional, `coll_type = None`).
    pub fn new(constructor: impl Into<String>, children: Vec<GroundTerm>) -> Self {
        Self {
            constructor: constructor.into(),
            children,
            coll_type: None,
        }
    }

    /// A nullary constructor (no children), e.g. the `A`/`B` operands of
    /// `Swap(A, B)`.
    pub fn nullary(constructor: impl Into<String>) -> Self {
        Self::new(constructor, Vec::new())
    }

    /// An AC operand collection of `kind` — its elements reflected as the native carrier
    /// (Stage AC / AC4). `HashBag` → the order-independent process-`Par` soup; `HashSet` → a native
    /// `ESet`; `HashMap` → a native `EMap` (whose `elements` are [`map_entry`](Self::map_entry)
    /// `^kv(key, value)` nodes).
    pub fn collection(
        kind: CollectionType,
        constructor: impl Into<String>,
        elements: Vec<GroundTerm>,
    ) -> Self {
        Self {
            constructor: constructor.into(),
            children: elements,
            coll_type: Some(kind),
        }
    }

    /// A `HashMap` AC operand ENTRY `key => value` — the reserved `^kv(key, value)` envelope
    /// ([`AC_MAP_ENTRY_LABEL`]) [`reflect_ac_map_par`] reads back as one `EMap` `KeyValuePair`. A
    /// `HashMap` [`collection`](Self::collection)'s `elements` are these entry nodes.
    pub fn map_entry(key: GroundTerm, value: GroundTerm) -> Self {
        Self::new(AC_MAP_ENTRY_LABEL, vec![key, value])
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

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
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

/// One AC-rewrite σ-injection site derived from a `LanguageDef`: an un-skipped linear with-rest
/// HashBag AC rewrite's bare label, its AC receiver SOURCE channel, the HashBag constructor `op`,
/// the `k` linear element σ variables (first-occurrence order), and the `rest` variable.
///
/// The AC firing analogue of [`RhoNetInjectionSite`]. A runtime AC σ-injection F-function reads a
/// rewrite firing's justification, reconstructs the WHOLE operand bag from σ — the `k` matched
/// element sub-terms (`element_var_order`) followed by the CHILDREN of the [`rest_var`] sub-term
/// (the canonical bag over the multiset complement) — reflects it to the process-soup carrier, and
/// sends it on [`channel`](Self::channel), where the installed AC receiver
/// ([`ac_sigma_receiver_par`]) consumes it and re-does the order-independent match. Only rewrites
/// that actually lowered to an AC receiver ([`RhoNetLoweredRule::AcRewrite`]) are surfaced, so a
/// site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetAcInjectionSite {
    /// The bare source rewrite label (the AC receiver rule's label, e.g. `AcStep`).
    pub rule_label: String,
    /// The AC receiver SOURCE channel (`RhoNetRule::input_channels.first()`) — the SAME channel
    /// the AC receiver rests on, so the accept triad (receiver source ≡ injection channel) holds
    /// by symmetric derivation (`ac_contract_call`'s coherence contract).
    pub channel: String,
    /// The HashBag operand constructor (`op` in `op{…}`, e.g. `PPar`). Both the receiver's element
    /// pattern channel `ac:{op}` and the reflected carrier's send channel derive from this.
    pub op: String,
    /// The `k` element σ variables the AC LHS binds, in first-occurrence order.
    pub element_var_order: Vec<String>,
    /// The `rest` variable the AC LHS binds to the residual bag (whose σ sub-term is a canonical
    /// `op` node over the multiset complement).
    pub rest_var: String,
}

/// Derive every AC-rewrite σ-injection site for a language — the sites a runtime AC σ-injection
/// F-function targets.
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the AC receivers are compiled from, keeps
/// only the rewrites that un-skipped to a [`RhoNetLoweredRule::AcRewrite`] receiver, and reports
/// each one's bare rule label, source channel, HashBag constructor, element variable order, and
/// `rest` variable (extracted through the SAME [`ac_rule_shape`] the receiver materialized from, so
/// the injection agrees with the receiver on `op`/elements/`rest`). The AC firing analogue of
/// [`rho_net_injection_sites`].
pub fn rho_net_ac_injection_sites(def: &LanguageDef) -> Vec<RhoNetAcInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::AcRewrite { rule_id, .. } = lowered_rule else {
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
        // An `AcRewrite` lowered iff `ac_rule_shape` succeeded under the resolved kind, so this
        // cannot fail; a defensive `continue` keeps the derivation total.
        let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
        let Some((op, element_vars, rest)) = ac_rule_shape(&rewrite.left, resolved_kind.as_ref())
        else {
            continue;
        };
        sites.push(RhoNetAcInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            op,
            element_var_order: element_vars.iter().map(|var| var.to_string()).collect(),
            rest_var: rest.to_string(),
        });
    }
    sites
}

/// One contextual-rewrite JOIN injection site derived from a `LanguageDef`: a congruence
/// rewrite's bare label and its `n` premise location channels (the join binds one reduced
/// hole per channel).
///
/// The contextual firing analogue of [`RhoNetInjectionSite`] / [`RhoNetAcInjectionSite`]. A
/// runtime contextual σ-injection F-function reads the premise firing(s) from the Dovetail
/// report, reconstructs each reduced hole `T_i = RHS_premise[σ]` (via
/// [`reconstruct_contractum`]), reflects it, and delivers the `n` holes on
/// [`premise_channels`](Self::premise_channels) via [`contextual_contract_call`], where the
/// installed [`contextual_join_receiver_par`] binds them and emits `⟦K'⟧` on `@out`. Only
/// rewrites that lowered to a [`RhoNetLoweredRule::ContextualRewrite`] join are surfaced, so
/// a site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetContextualInjectionSite {
    /// The bare source rewrite label (the contextual join rule's label, e.g. `WrapCong`).
    pub rule_label: String,
    /// The `n` premise location channels the join binds, in premise order
    /// (`RhoNetRule::input_channels[1..]`, since `input_channels[0]` is the LHS trace
    /// channel). The contextual injection sends one reduced hole per channel; the LAST
    /// channel additionally carries the dynamic out channel.
    pub premise_channels: Vec<String>,
}

/// Derive every contextual-rewrite JOIN injection site for a language — the sites a runtime
/// contextual σ-injection F-function targets.
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the contextual joins are compiled
/// from, keeps only the rewrites that materialized to a
/// [`RhoNetLoweredRule::ContextualRewrite`] join, and reports each one's bare rule label and
/// premise location channels (the `input_channels[1..]` the join binds). The contextual
/// firing analogue of [`rho_net_injection_sites`] / [`rho_net_ac_injection_sites`].
pub fn rho_net_contextual_injection_sites(def: &LanguageDef) -> Vec<RhoNetContextualInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::ContextualRewrite { rule_id, .. } = lowered_rule else {
            continue;
        };
        let Some(program_rule) = rule_by_id.get(rule_id.as_str()) else {
            continue;
        };
        let Some(rule_label) = program_rule.label.as_deref() else {
            continue;
        };
        // The premise channels are `input_channels[1..]` (channel 0 is the LHS trace
        // channel). A materialized `ContextualRewrite` has at least one premise channel.
        let premise_channels: Vec<String> = program_rule
            .input_channels
            .get(1..)
            .unwrap_or(&[])
            .iter()
            .cloned()
            .collect();
        if premise_channels.is_empty() {
            continue;
        }
        sites.push(RhoNetContextualInjectionSite {
            rule_label: rule_label.to_string(),
            premise_channels,
        });
    }
    sites
}

/// One binder/β-substitution σ-injection site derived from a `LanguageDef` (Stage 3c): a
/// substitution rewrite's bare label, its σ-receiver SOURCE channel, the `k` LHS σ variables
/// (first-occurrence order, binder-excluded), and the SCOPE variable (the `subst` scope, a bound
/// LHS variable at which the host-computed reduct is delivered).
///
/// The binder firing analogue of [`RhoNetInjectionSite`]. A runtime subst σ-injection F-function
/// reads a rewrite firing's justification, reflects each LHS σ variable's sub-term EXCEPT the
/// scope variable — at whose slot it instead reflects the firing's CONTRACTUM (the reduced term
/// `RHS[σ]` the host computed via capture-avoiding substitution, carried in
/// `RuntimeRewriteJustification::contractum`) — and sends the σ tuple on [`channel`](Self::channel)
/// via [`term_contract_call`], where the installed `SubstRewrite` σ-receiver
/// ([`sigma_receiver_par`]) forwards the scope slot (the reduct) on `@out`. Only rewrites that
/// lowered to a [`RhoNetLoweredRule::SubstRewrite`] are surfaced, so a site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetSubstInjectionSite {
    /// The bare source rewrite label (the SubstRewrite σ-receiver rule's label, e.g. `Beta`).
    pub rule_label: String,
    /// The σ-receiver SOURCE channel (`RhoNetRule::input_channels.first()`) — the SAME channel the
    /// receiver rests on, so the accept triad (receiver source ≡ injection channel) holds by
    /// symmetric derivation.
    pub channel: String,
    /// The `k` LHS σ variables the receiver binds, in first-occurrence (binder-excluded) order —
    /// the order [`term_contract_call`] expects the σ arguments in.
    pub lhs_var_order: Vec<String>,
    /// The SCOPE variable (`subst` scope). Its σ slot carries the host-computed reduct (the
    /// firing's contractum), not the raw matched sub-term.
    pub scope_var: String,
}

/// Derive every binder/β-substitution σ-injection site for a language — the sites a runtime subst
/// σ-injection F-function targets (Stage 3c).
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the SubstRewrite σ-receivers are compiled
/// from, keeps only the rewrites that lowered to a [`RhoNetLoweredRule::SubstRewrite`] receiver,
/// and reports each one's bare rule label, source channel, LHS σ variable order, and scope
/// variable (extracted through the SAME [`subst_rule_shape`] the receiver materialized from, so the
/// injection agrees with the receiver on the σ order and the scope slot). The binder firing
/// analogue of [`rho_net_injection_sites`] / [`rho_net_ac_injection_sites`].
pub fn rho_net_subst_injection_sites(def: &LanguageDef) -> Vec<RhoNetSubstInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::SubstRewrite { rule_id, .. } = lowered_rule else {
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
        // A `SubstRewrite` lowered iff `subst_rule_shape` succeeded, so this cannot fail; a
        // defensive `continue` keeps the derivation total.
        let Some((vars, scope_var)) = subst_rule_shape(&rewrite.left, &rewrite.right) else {
            continue;
        };
        sites.push(RhoNetSubstInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            lhs_var_order: vars.iter().map(|var| var.to_string()).collect(),
            scope_var: scope_var.to_string(),
        });
    }
    sites
}

/// One native-system-process σ-injection site derived from a `LanguageDef` (Stage 3e): a `fold`
/// native process's Dovetail firing label and its dispatch-receiver SOURCE channel.
///
/// The native-dispatch analogue of [`RhoNetSubstInjectionSite`]. A runtime native σ-injection
/// F-function reads a rewrite firing's justification, reflects the firing's CONTRACTUM (the native
/// value the host's trusted handler computed via its `![…] fold` HOL body, carried in
/// [`RuntimeRewriteJustification::contractum`]) — the WHOLE payload, no structural RHS — and sends
/// it on [`channel`](Self::channel) via [`term_contract_call`], where the installed
/// `NativeSystemProcessRewrite` dispatch receiver ([`sigma_receiver_par`]) forwards that slot on
/// `@out`. Only native processes that lowered to a
/// [`RhoNetLoweredRule::NativeSystemProcessRewrite`] are surfaced, so a site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetNativeInjectionSite {
    /// The RULE LABEL the `fold` native process's Dovetail firing carries in a runtime rewrite
    /// justification: `"{Category}_{Label}"` (the op-enum variant identity, e.g. `Int_PowInt`).
    /// This is what the native σ-injection F-function matches the fired justification on — NOT the
    /// bare source label — because the macro's native-fold rule labels its firing
    /// `{Lang}::fold::{Category}_{Label}`, which the report producer bare-ifies to
    /// `"{Category}_{Label}"`.
    pub rule_label: String,
    /// The dispatch-receiver SOURCE channel (`RhoNetRule::input_channels.first()`) — the SAME
    /// channel the receiver rests on, so the accept triad (receiver source ≡ injection channel)
    /// holds by symmetric derivation.
    pub channel: String,
}

/// Derive every native-system-process σ-injection site for a language — the sites a runtime
/// native σ-injection F-function targets (Stage 3e).
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the `NativeSystemProcessRewrite` dispatch
/// receivers are compiled from, keeps only the native processes that lowered to a
/// [`RhoNetLoweredRule::NativeSystemProcessRewrite`] receiver, and reports each one's Dovetail
/// firing label and source channel (the label extracted through the SAME [`native_rule_shape`] the
/// receiver materialized from, so the injection agrees with the receiver and with the report
/// producer's bare-ified firing label). The native-dispatch analogue of
/// [`rho_net_injection_sites`] / [`rho_net_subst_injection_sites`].
pub fn rho_net_native_injection_sites(def: &LanguageDef) -> Vec<RhoNetNativeInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let term_by_id: HashMap<String, &GrammarRule> = def
        .terms
        .iter()
        .enumerate()
        .map(|(index, term)| (rule_id_native(index, &term.label.to_string()), term))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::NativeSystemProcessRewrite { rule_id, .. } = lowered_rule else {
            continue;
        };
        let Some(program_rule) = rule_by_id.get(rule_id.as_str()) else {
            continue;
        };
        let Some(channel) = program_rule.input_channels.first() else {
            continue;
        };
        let Some(term) = term_by_id.get(rule_id) else {
            continue;
        };
        // A `NativeSystemProcessRewrite` lowered iff `native_rule_shape` succeeded, so this cannot
        // fail; a defensive `continue` keeps the derivation total.
        let Some(rule_label) = native_rule_shape(term) else {
            continue;
        };
        sites.push(RhoNetNativeInjectionSite { rule_label, channel: channel.clone() });
    }
    sites
}

/// Derive every native-SCALAR-FOLD σ-injection site for a language — the sites a runtime native
/// σ-injection F-function targets for the `NativeFold` family (Stage 3f). The scalar-fold analogue
/// of [`rho_net_native_injection_sites`], reusing the same [`RhoNetNativeInjectionSite`] shape
/// (`(rule_label, channel)`) because both native families fire the SAME contractum lane onto the
/// SAME flat one-slot dispatch receiver.
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the `NativeFold` dispatch receivers are
/// compiled from, keeps only the native scalar folds that lowered to a
/// [`RhoNetLoweredRule::NativeFold`] receiver, and reports each one's Dovetail firing label
/// (`{Category}_{Label}`, via the SAME [`native_rule_shape`] the receiver's fold-gate used) and its
/// source dispatch channel (`sa:scalar/{label}`). Unlike the native-system-process sites (keyed by
/// `rule_id_native`), a `NativeFold` rule is keyed by `rule_id_scalar`, so it correlates back to
/// its source `GrammarRule` by the term LABEL the scalar rule carries.
pub fn rho_net_native_fold_injection_sites(def: &LanguageDef) -> Vec<RhoNetNativeInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let term_by_label: HashMap<String, &GrammarRule> = def
        .terms
        .iter()
        .map(|term| (term.label.to_string(), term))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::NativeFold { rule_id, .. } = lowered_rule else {
            continue;
        };
        let Some(program_rule) = rule_by_id.get(rule_id.as_str()) else {
            continue;
        };
        let Some(channel) = program_rule.input_channels.first() else {
            continue;
        };
        let Some(label) = program_rule.label.as_deref() else {
            continue;
        };
        let Some(term) = term_by_label.get(label) else {
            continue;
        };
        // A `NativeFold` receiver lowered iff its fold-gate (`native_rule_shape`) succeeded, so this
        // cannot fail; a defensive `continue` keeps the derivation total.
        let Some(rule_label) = native_rule_shape(term) else {
            continue;
        };
        sites.push(RhoNetNativeInjectionSite { rule_label, channel: channel.clone() });
    }
    sites
}

/// One in-Rho MATCHING entry for a native process family (`NativeSystemProcessRewrite` /
/// `NativeFold`, Stage 4 S-native): the data the in-Rho matcher needs to ADMIT the native redex
/// into the positional automaton and route its located accept to the value-carrying bridge.
///
/// A native process `NativeProc(a₀..a_{k-1})` is a plain App-rooted node, so the SAME positional
/// set-automaton LOCATES it by its head tag + arity and CAPTURES its `k` structural args, exactly
/// as a base rewrite — once ADMITTED (`compile_in_rho_matching_ruleset`). The native family differs
/// only in the VALUE: it has no structural RHS, so its reduced value is the trusted host handler's
/// payload (the firing's contractum), delivered by the [`native_locate_bridge_par`] on the
/// [`dispatch_channel`](Self::dispatch_channel). This entry carries the bare head label + arity
/// (the automaton pattern `bare_label(x₀..x_{arity-1})`, which the structurally reflected subject's
/// tag matches), the Dovetail firing label the report keys on, and that dispatch channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetNativeMatchEntry {
    /// The Dovetail firing label (`"{Category}_{Label}"`, e.g. `Int_PowInt`) the native firing
    /// carries in a runtime rewrite justification — what the match driver keys the report firing on
    /// (identical to [`RhoNetNativeInjectionSite::rule_label`]).
    pub fired_rule_label: String,
    /// The BARE head label (`"PowInt"`) — the automaton pattern's root op AND the tag the
    /// structurally reflected subject node carries, so the located head matches.
    pub bare_label: String,
    /// The native process's arity `k` (its structural arg count) — the automaton pattern
    /// `bare_label(x₀..x_{k-1})` and the number of captures the located accept sends.
    pub arity: usize,
    /// The installed dispatch receiver's SOURCE channel — where the bridge forwards `⟦value⟧`.
    pub dispatch_channel: String,
}

/// Derive every in-Rho MATCHING entry for a language's native process families (Stage 4 S-native)
/// — the native analogue of the base [`rho_net_injection_sites`], routed for the automaton MATCH
/// path rather than the host-σ replay path.
///
/// Correlates each installed native firing site ([`rho_net_native_injection_sites`] ∪
/// [`rho_net_native_fold_injection_sites`] — the processes that actually lowered to a dispatch
/// receiver) back to its source `GrammarRule` by the SAME `"{Category}_{Label}"` firing label, and
/// reads the bare head label + arity the automaton pattern is synthesized from. Only fold-mode
/// native processes with a materialized dispatch receiver are surfaced, so an entry is always
/// executable (its dispatch receiver is installed).
pub fn rho_net_native_match_entries(def: &LanguageDef) -> Vec<RhoNetNativeMatchEntry> {
    // `"{Category}_{Label}"` → (bare head label, arity) over fold-mode native processes. The arity
    // is the structural arg count (its `term_context` parameters), matching the reflected subject
    // node's child count and the automaton pattern's Var-leaf count.
    let mut shape_by_fired: HashMap<String, (String, usize)> = HashMap::new();
    for term in &def.terms {
        if term.eval_mode != Some(EvalMode::Fold) {
            continue;
        }
        let fired = format!("{}_{}", term.category, term.label);
        let arity = term.term_context.as_ref().map_or(0, Vec::len);
        shape_by_fired.insert(fired, (term.label.to_string(), arity));
    }

    let mut entries = Vec::new();
    for site in rho_net_native_injection_sites(def)
        .into_iter()
        .chain(rho_net_native_fold_injection_sites(def))
    {
        // A materialized site whose source term is a fold-mode native process is always found; a
        // defensive skip keeps the derivation total.
        let Some((bare_label, arity)) = shape_by_fired.get(&site.rule_label) else {
            continue;
        };
        entries.push(RhoNetNativeMatchEntry {
            fired_rule_label: site.rule_label,
            bare_label: bare_label.clone(),
            arity: *arity,
            dispatch_channel: site.channel,
        });
    }
    entries
}

/// One in-Rho MATCHING entry for a linear with-rest HashBag AC family rewrite
/// (`RhoNetLoweredRule::AcRewrite`, Stage 4 S-AC): the data the in-Rho matcher needs to ADMIT the
/// AC redex and co-install a per-site AC receiver that re-sources the operand bag from the SPREAD
/// of the reflected subject (NOT the host-σ report).
///
/// An AC operand bag `op{x₀..x_{k-1}, ...rest}` has no positional set-automaton image (it is an
/// `AcApp`, which `compile_structural` rejects), so — unlike a base rewrite or a native process —
/// it is NOT an automaton entry. Instead the match driver ([`ac_match_call_par`]) LOCATES each bag
/// position in the reflected subject, publishes the site-keyed process-soup carrier `ac:⌜ℓ⌝/op`
/// from that bag's ground elements, and co-installs an [`ac_sigma_receiver_par`] over that carrier
/// which picks k-of-n + binds `rest` ON the interpreter (one atomic `consume`, native `sub_pars`)
/// and fires the rule's RHS. This entry carries the firing label the report keys on, the HashBag
/// operand constructor `op`, the `k` fixed element slots, and the pre-built RHS `⟦R⟧σ` (the AC
/// receiver frame — site-independent, so one build serves every located site). The VALUE is the
/// rule's own structural RHS (no host handler), so — unlike S-native — AC has NO host-supplied
/// residue: the whole match AND fire is in Rho.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoNetAcMatchEntry {
    /// The Dovetail firing label the AC firing carries in a runtime rewrite justification (the bare
    /// AC receiver rule label, e.g. `AcStep`) — what the match driver keys the report firing on and
    /// the gate admits.
    pub fired_rule_label: String,
    /// The AC operand constructor (`op` in `op{…}`, e.g. `PPar`) — the reflected subject collection
    /// node's `constructor`, so the located collection matches, and the soup carrier / element
    /// pattern channel derive from it.
    pub op: String,
    /// The AC operand COLLECTION kind (`HashBag` soup / `HashSet` `ESet`, Stage 4 S-AC / AC4): it
    /// selects the co-installed receiver's connective pattern ([`ac_collection_pattern`]) and the
    /// carrier reflection ([`reflect_ac_collection_par`]), so the located collection is re-sourced
    /// from the SPREAD with the SAME kind the installed receiver expects.
    pub kind: CollectionType,
    /// The `k` fixed element slots the AC LHS binds (the element variable count) — the
    /// [`ac_collection_pattern`] arity the co-installed receiver picks from the collection.
    pub arity: usize,
    /// The pre-built RHS `⟦R⟧σ` in the AC receiver's `k+2`-formal frame ([`reflect_term_par`] at
    /// `k+1` over the `[x₀..x_{k-1}, rest]` σ order — the SAME reflection [`ac_rule_receiver`]
    /// materializes the installed AC receiver from). Site-independent: the co-installed per-site
    /// receiver differs from the installed one ONLY in its source channel.
    pub rhs_par: Par,
    /// The NON-LINEAR consistency `Receive.condition` (Stage 4 S-AC, AC3) for a repeated bare
    /// element var (`{x, x, ...rest}` — the `N ≡ N` shape), or `None` for a LINEAR LHS. Site-
    /// independent (it references only the receiver's bound element slots), so the co-installed
    /// per-site receiver carries the SAME guard as the installed one.
    pub condition: Option<Par>,
}

/// Derive every in-Rho MATCHING entry for a language's linear with-rest HashBag AC family rewrites
/// (Stage 4 S-AC) — the AC analogue of [`rho_net_native_match_entries`], routed for the automaton
/// MATCH path (bag re-sourced from the subject spread) rather than the host-σ replay path.
///
/// Correlates each installed AC firing site ([`rho_net_ac_injection_sites`] — the rewrites that
/// actually un-skipped to an [`RhoNetLoweredRule::AcRewrite`] receiver) back to its source
/// `RewriteRule`, re-extracts its AC LHS shape through the SAME [`ac_rule_shape`] the receiver
/// materialized from (so the op / element count / `rest` agree byte-for-byte), and pre-builds the
/// RHS `⟦R⟧σ` in the AC receiver frame with the language fingerprint the spread + installed
/// receivers share ([`language_definition_fingerprint`](mettail_ast::identity::language_definition_fingerprint)).
/// Only rewrites with a materialized AC receiver are surfaced, so an entry is always executable.
pub fn rho_net_ac_match_entries(def: &LanguageDef) -> Vec<RhoNetAcMatchEntry> {
    let language_fingerprint =
        mettail_ast::identity::language_definition_fingerprint(def);
    let sites = rho_net_ac_injection_sites(def);
    let mut entries = Vec::with_capacity(sites.len());
    for site in sites {
        // The source rewrite an AC injection site surfaced is always present; a defensive skip keeps
        // the derivation total.
        let Some(rewrite) = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == site.rule_label)
        else {
            continue;
        };
        let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
        // An `AcRewrite` lowered iff `ac_rule_shape` succeeded under the resolved kind, so this
        // cannot fail; a defensive skip keeps the derivation total.
        let Some((op, element_vars, rest)) = ac_rule_shape(&rewrite.left, resolved_kind.as_ref())
        else {
            continue;
        };
        // The effective operand kind (`HashBag` soup / `HashSet` `ESet`) — SAME as the installed
        // receiver's, so the co-installed per-site receiver's connective pattern matches the carrier.
        let kind = ac_effective_bare_var_kind(&rewrite.left, resolved_kind.as_ref());
        let k = element_vars.len();
        // The NON-LINEAR consistency guard (AC3) for a repeated bare element var, computed BEFORE
        // `element_vars` is moved — SAME as the installed receiver's ([`ac_rule_receiver`]).
        let condition = ac_nonlinear_condition(&element_vars, k + 2);
        // The σ variable order: the k element vars (first-occurrence), then `rest` — EXACTLY the
        // frame `ac_rule_receiver` reflects the RHS in, so the co-installed receiver is byte-
        // identical to the installed one apart from its source channel.
        let mut vars: Vec<Ident> = element_vars;
        vars.push(rest);
        let Ok(rhs_par) =
            reflect_term_par(&rewrite.right, &vars, k + 1, &language_fingerprint, Some(def))
        else {
            continue;
        };
        entries.push(RhoNetAcMatchEntry {
            fired_rule_label: site.rule_label,
            op,
            kind,
            arity: k,
            rhs_par,
            condition,
        });
    }
    entries
}

/// One in-Rho MATCHING entry for a contextual (congruence) rewrite family
/// (`RhoNetLoweredRule::ContextualRewrite`, Stage 4 S-contextual): the data the in-Rho matcher
/// needs to ADMIT the contextual redex and route each hole position's IN-RHO nested firing to the
/// installed join's premise channel — so the reduced holes come from the automaton's nested
/// firings, NOT the host-σ [`reconstruct_contractum`] report replay.
///
/// A contextual rewrite `⟦…S_i ~> T_i… |- K(S_1..S_n) ~> K'(T_1..T_n)⟧` fires no explicit Dovetail
/// rule of its own (the e-graph congruence closure closes the outer context `K` implicitly), so —
/// unlike a base rewrite or a native process — it is NOT an automaton entry (it has no positional
/// LHS to `Match` at the root). Instead the outer context spine `K` is the subject term with `n`
/// distinguished hole positions ℓ_i (already reflected by the base M-reflect); the base automaton's
/// locate-all LOCATES each hole's PREMISE redex from the ONE spread (the nested-App descent through
/// `K`'s spine), fires its σ-receiver, and the contextual match driver
/// ([`contextual_match_call_par`](crate::contextual_match_call_par)) routes that reduced hole to the
/// join's premise channel `c(ℓ_i)` (via [`contextual_hole_bridge_par`]) INSTEAD of a shared `OUT`.
/// The reused, unchanged [`contextual_join_receiver_par`] then binds the `n` reduced holes and emits
/// ⟦K'⟧. This entry carries the contextual rule label the gate admits and the `n` premise location
/// channels the located holes route to. The VALUE is the rule's own reduced context (no host
/// handler), so — like S-AC — the whole match AND reassembly is in Rho; the only inherent host
/// residue is a premise's SEMANTIC-PREDICATE guard (INV-14), which stays off-machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetContextualMatchEntry {
    /// The bare contextual rule label (e.g. `WrapCong`) — what the capability gate admits (so a
    /// fired contextual rule is no longer skipped) and the match path keys the join on. Identical
    /// to [`RhoNetContextualInjectionSite::rule_label`].
    pub fired_rule_label: String,
    /// The `n` premise location channels the installed [`contextual_join_receiver_par`] binds, in
    /// premise order — the channels each located hole redex's reduced contractum routes to (via
    /// [`contextual_hole_bridge_par`]), so the join reassembles ⟦K'⟧. Identical to
    /// [`RhoNetContextualInjectionSite::premise_channels`]; the LAST additionally carries the
    /// dynamic out channel (the join's `(T_{n-1}, out)` bind ABI).
    pub premise_channels: Vec<String>,
    /// The `n` HOLE POSITIONS in the outer context `K`, in premise order — one `(op, index)` path
    /// per premise, locating that premise's SOURCE variable `S_i` in the contextual rule's LHS
    /// (`K(S_0..S_{n-1})`). The match driver
    /// ([`contextual_match_call_par`](crate::contextual_match_call_par)) derives each hole's location
    /// site `ℓ_i` by folding [`spread_child_location`] over its path from the spread root (the SAME
    /// derivation `collect_redex_sites` uses), so a premise-`i` located firing routes to premise
    /// channel `i` — the hole↔channel correspondence that makes the n-ary reassembly `K'(T_0..T_{n-1})`
    /// place each reduced hole at its context position. Aligned index-for-index with
    /// [`premise_channels`](Self::premise_channels).
    pub hole_positions: Vec<Vec<(String, usize)>>,
}

/// Derive every in-Rho MATCHING entry for a language's contextual (congruence) rewrite families
/// (Stage 4 S-contextual) — the contextual analogue of [`rho_net_native_match_entries`] /
/// [`rho_net_ac_match_entries`], routed for the automaton MATCH path (reduced holes re-sourced from
/// the IN-RHO nested firings at the hole positions) rather than the host-σ [`reconstruct_contractum`]
/// replay path.
///
/// Reads each materialized contextual JOIN site ([`rho_net_contextual_injection_sites`] — the
/// congruence rewrites that actually lowered to a [`RhoNetLoweredRule::ContextualRewrite`] join) and
/// carries its rule label + premise channels. Only rewrites with a materialized join are surfaced,
/// so an entry is always executable (its join receiver is installed).
pub fn rho_net_contextual_match_entries(def: &LanguageDef) -> Vec<RhoNetContextualMatchEntry> {
    rho_net_contextual_injection_sites(def)
        .into_iter()
        .map(|site| {
            // The hole positions: for each premise (in premise order), the `(op, index)` path to its
            // SOURCE variable in the contextual rule's LHS `K`. A materialized `ContextualRewrite`
            // has all-congruence premises (`congruence_targets` succeeded) whose sources are LHS
            // variables, so each path is found; a defensive empty path (source absent) keeps the
            // derivation total (the match driver's bijection check then fails closed).
            let hole_positions = def
                .rewrites
                .iter()
                .find(|rewrite| rewrite.name.to_string() == site.rule_label)
                .map(|rewrite| {
                    rewrite
                        .premises
                        .iter()
                        .filter_map(|premise| match premise {
                            Premise::Congruence { source, .. } => {
                                Some(contextual_source_path(&rewrite.left, &source.to_string())
                                    .unwrap_or_default())
                            },
                            _ => None,
                        })
                        .collect()
                })
                .unwrap_or_default();
            RhoNetContextualMatchEntry {
                fired_rule_label: site.rule_label,
                premise_channels: site.premise_channels,
                hole_positions,
            }
        })
        .collect()
}

/// The `(op, index)` path to the SOURCE variable `source` in a contextual rule's LHS context `K`
/// (`pattern`) — the hole position the automaton descends `K`'s spine to. A DFS returning the first
/// occurrence's path (empty when `pattern` IS the source var — a degenerate hole-only context — and
/// `None` when `source` does not occur). The path is folded through [`spread_child_location`] by the
/// match driver into the hole's location site, so the derivation matches `collect_redex_sites`.
fn contextual_source_path(pattern: &Pattern, source: &str) -> Option<Vec<(String, usize)>> {
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) if id.to_string() == source => Some(Vec::new()),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            for (index, arg) in args.iter().enumerate() {
                if let Some(mut suffix) = contextual_source_path(arg, source) {
                    let mut path = Vec::with_capacity(suffix.len() + 1);
                    path.push((constructor.to_string(), index));
                    path.append(&mut suffix);
                    return Some(path);
                }
            }
            None
        },
        _ => None,
    }
}

/// Reconstruct the reduced hole `T = RHS_premise[σ]` a fired premise rewrite produced — the
/// contractum a contextual JOIN plugs into its context `K'`. Finds the rewrite named
/// `rule_label` in `def` and instantiates its RHS with `σ` (the premise firing's
/// substitution, mapping the premise rewrite's LHS variables to ground sub-terms).
///
/// The RHS-instantiation dual of [`reconstruct_redex_subject`](crate::reconstruct_redex_subject)
/// (which instantiates the LHS). Total + fail-closed: a premise rewrite's RHS is Var/Apply
/// only, so the collection/binder/substitution arms are defensive (a contextual join over
/// such a premise would already have failed closed at lowering).
pub fn reconstruct_contractum(
    def: &LanguageDef,
    rule_label: &str,
    sigma: &[(String, GroundTerm)],
) -> Result<GroundTerm, String> {
    let rewrite = def
        .rewrites
        .iter()
        .find(|rewrite| rewrite.name.to_string() == rule_label)
        .ok_or_else(|| format!("contextual contractum: no rewrite named {rule_label}"))?;
    let bindings: HashMap<&str, &GroundTerm> = sigma
        .iter()
        .map(|(name, ground)| (name.as_str(), ground))
        .collect();
    instantiate_rhs(&rewrite.right, &bindings, rule_label)
}

fn instantiate_rhs(
    pattern: &Pattern,
    sigma: &HashMap<&str, &GroundTerm>,
    rule: &str,
) -> Result<GroundTerm, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) => {
            let name = id.to_string();
            sigma
                .get(name.as_str())
                .map(|ground| (*ground).clone())
                .ok_or_else(|| {
                    format!("contextual contractum for {rule}: σ missing RHS variable {name}")
                })
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { .. }] = args.as_slice() {
                return Err(format!(
                    "contextual contractum for {rule}: AC constructor {constructor} has no positional contractum image"
                ));
            }
            let children = args
                .iter()
                .map(|arg| instantiate_rhs(arg, sigma, rule))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(GroundTerm::new(constructor.to_string(), children))
        },
        // binder / subst / collection RHS → a premise rewrite whose contractum has no
        // positional ground image; never reached past a materialized contextual join.
        _ => Err(format!(
            "contextual contractum for {rule}: non-structural RHS has no ground contractum image"
        )),
    }
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
    // Stage AC / AC4: an AC operand COLLECTION reflects as its kind's native matching CARRIER,
    // not the positional tagged `EList`. A `HashBag` reflects to the order-independent process-`Par`
    // soup; a `HashSet` to a native `ESet`; a `HashMap` to a native `EMap` (key-uniqueness enforced
    // by `ParMap`'s sorted-dedup). See [`reflect_ac_collection_par`].
    if matches!(
        term.coll_type,
        Some(CollectionType::HashBag | CollectionType::HashSet | CollectionType::HashMap)
    ) {
        return reflect_ac_collection_par(term, language_fingerprint);
    }
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

/// Reflect a HashBag AC operand bag as the process-`Par` matching CARRIER: each element is a
/// ground send `@"ac:{op}"!(⟦e⟧)`, so the soup is order-independent (the native connective /
/// `sub_pars` matcher picks any element↔pattern assignment) and multiplicity-preserving (a
/// `Vec` of sends, duplicates disambiguated by `Indexed`), and element slots never collide
/// with the pattern's process remainder. This is the subject side of Stage AC's Scheme B —
/// the AC receiver's collection pattern matches this carrier inside one atomic `consume`.
fn reflect_ac_bag_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    let element_channel = format!("ac:{}", term.constructor);
    let mut soup = Par::default();
    for child in &term.children {
        let element = reflect_ground_term_par(child, language_fingerprint);
        let free = element.locally_free.clone();
        let send = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![element],
            false,
            free.clone(),
            false,
            free,
            false,
        );
        soup = soup.append(send);
    }
    soup
}

/// The reserved constructor label a HashMap AC operand entry (`key => value`) reflects to in a
/// [`GroundTerm`]: a synthetic node `^kv(⟦key⟧, ⟦value⟧)` whose two children are the entry's key
/// and value. It cannot collide with any user constructor (a Rust `Ident`, never containing `^`),
/// so the map carrier's entry envelope is distinct from every `Apply` node. The macro
/// `reflect_category_fn`'s `HashMap` arm emits one such node per entry; [`reflect_ac_map_par`] reads
/// the two children back as the `EMap`'s key/value.
pub(crate) const AC_MAP_ENTRY_LABEL: &str = "^kv";

/// Reflect an AC operand COLLECTION [`GroundTerm`] as its kind's native matching CARRIER — the
/// subject side of Stage 4 S-AC / AC4. A `HashBag` reflects to the order-independent process-`Par`
/// soup ([`reflect_ac_bag_par`]); a `HashSet` to a native `ESet` ([`reflect_ac_set_par`]); a
/// `HashMap` to a native `EMap` ([`reflect_ac_map_par`]). The `ESet`/`EMap` carriers ride
/// `ParSet`/`ParMap`, whose construction SORTS + DEDUPES (so `ESet` is a genuine set and `EMap`'s
/// keys are unique — the key-uniqueness invariant survives reflection), and the native spatial
/// matcher AC-matches each carrier order-independently with a remainder.
fn reflect_ac_collection_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    match term.coll_type {
        Some(CollectionType::HashSet) => reflect_ac_set_par(term, language_fingerprint),
        Some(CollectionType::HashMap) => reflect_ac_map_par(term, language_fingerprint),
        // `HashBag` (and any other kind routed here) → the process-soup carrier.
        _ => reflect_ac_bag_par(term, language_fingerprint),
    }
}

/// Reflect a `HashSet` AC operand set as a native `ESet` matching CARRIER: each element reflects to
/// its ground `Par` and the set rides `ParSet` (sorted + deduplicated), so the carrier is a genuine
/// order-independent, uniqueness-preserving set. The AC receiver's `ESet` connective pattern
/// ([`ac_set_pattern`]) matches this carrier inside one atomic `consume` (native `list_match_single_`
/// over `sorted_pars`), binding `k` element slots + the residual set to the remainder.
fn reflect_ac_set_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    let mut elements = Vec::with_capacity(term.children.len());
    let mut locally_free = Vec::new();
    for child in &term.children {
        let element = reflect_ground_term_par(child, language_fingerprint);
        locally_free = union(locally_free, element.locally_free.clone());
        elements.push(element);
    }
    // A GROUND set: no free vars, no connective, no remainder. `ParSet::new` sorts + dedupes.
    new_eset_par(elements, locally_free.clone(), false, None, locally_free, false)
}

/// Reflect a `HashMap` AC operand map as a native `EMap` matching CARRIER: each `^kv(key, value)`
/// entry ([`AC_MAP_ENTRY_LABEL`]) reflects to a `KeyValuePair`, and the map rides `ParMap` (sorted by
/// key + deduplicated on key), so KEY-UNIQUENESS is enforced natively — the sorted-dedup `ParMap`
/// invariant survives the reflect. The AC receiver's `EMap` connective pattern ([`ac_map_pattern`])
/// matches this carrier inside one atomic `consume` (native `list_match_single_` over the
/// key-sorted kv list), binding `k` `(key, value)` slots + the residual map to the remainder.
fn reflect_ac_map_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    let mut kvs = Vec::with_capacity(term.children.len());
    let mut locally_free = Vec::new();
    for entry in &term.children {
        // Each entry is a `^kv(key, value)` node ([`AC_MAP_ENTRY_LABEL`]) — read its two children
        // back as key/value. A malformed entry (defensive) is skipped, keeping the reflection total.
        let ([key, value], true) =
            (entry.children.as_slice(), entry.constructor == AC_MAP_ENTRY_LABEL)
        else {
            continue;
        };
        let key_par = reflect_ground_term_par(key, language_fingerprint);
        let value_par = reflect_ground_term_par(value, language_fingerprint);
        locally_free = union(locally_free, key_par.locally_free.clone());
        locally_free = union(locally_free, value_par.locally_free.clone());
        kvs.push(KeyValuePair { key: Some(key_par), value: Some(value_par) });
    }
    // A GROUND map: no free vars, no connective, no remainder. `ParMap::new` sorts by key + dedupes
    // on key (so duplicate keys collapse to the last write — the key-uniqueness invariant).
    new_emap_par(kvs, locally_free.clone(), false, None, locally_free, false)
}

/// The AC receiver's collection PATTERN for an operand of `kind` with `k` fixed element slots
/// (Stage 4 S-AC / AC4): a `HashBag` yields the process-soup connective ([`ac_bag_pattern`]); a
/// `HashSet` the `ESet` connective ([`ac_set_pattern`]); a `HashMap` the `EMap` connective
/// ([`ac_map_pattern`]). Each binds the fixed element slots + a residual-binding remainder, matched
/// order-independently by the native spatial matcher inside one atomic `consume`. `op` is used only
/// by the `HashBag` soup (its element channel `ac:{op}`); the native `ESet`/`EMap` carriers need no
/// element channel.
pub fn ac_collection_pattern(kind: CollectionType, op: &str, k: usize) -> Par {
    match kind {
        CollectionType::HashSet => ac_set_pattern(k),
        CollectionType::HashMap => ac_map_pattern(k),
        // `HashBag` (and any other kind routed here) → the process-soup pattern.
        _ => ac_bag_pattern(op, k),
    }
}

/// The AC receiver's `ESet` connective PATTERN for a `HashSet` operand with `k` fixed element slots:
/// a connective `ESet` whose `k` elements are free vars `FreeVar(0..k-1)` (each binding element σ
/// slot `i`) plus a remainder free var `FreeVar(k)` (binding `rest`, the residual set). The native
/// `list_match_single_` (spatial matcher's `ESetBody` arm) assigns the `k` free-var patterns to `k`
/// set elements in ANY order and binds the residual SET to the remainder — the order-independent set
/// match — inside one atomic `consume`. The remainder is a `FreeVar(k)` `Var` (exactly the
/// `remainder_var_opt` level the matcher reads); element `i` binds `FreeVar(i)`.
pub fn ac_set_pattern(k: usize) -> Par {
    let elements: Vec<Par> = (0..k).map(|i| new_freevar_par(i as i32, Vec::new())).collect();
    let remainder = Var { var_instance: Some(VarInstance::FreeVar(k as i32)) };
    new_eset_par(elements, Vec::new(), true, Some(remainder), Vec::new(), true)
}

/// The AC receiver's `EMap` connective PATTERN for a `HashMap` operand with `k` fixed `(key, value)`
/// slots: a connective `EMap` whose `k` entries are free-var pairs `(FreeVar(2i), FreeVar(2i+1))`
/// (key σ slot `2i`, value σ slot `2i+1`) plus a remainder free var `FreeVar(2k)` (binding `rest`,
/// the residual map). The native `list_match_single_` (spatial matcher's `EMapBody` arm) assigns the
/// `k` entry patterns to `k` map entries (matched key-first over the key-sorted kv list) and binds
/// the residual MAP to the remainder — inside one atomic `consume`. KEY-UNIQUENESS holds because the
/// target rides `ParMap` (key-sorted, deduped) and each residual is re-wrapped as an `EMap`.
pub fn ac_map_pattern(k: usize) -> Par {
    let kvs: Vec<KeyValuePair> = (0..k)
        .map(|i| KeyValuePair {
            key: Some(new_freevar_par((2 * i) as i32, Vec::new())),
            value: Some(new_freevar_par((2 * i + 1) as i32, Vec::new())),
        })
        .collect();
    let remainder = Var { var_instance: Some(VarInstance::FreeVar((2 * k) as i32)) };
    new_emap_par(kvs, Vec::new(), true, Some(remainder), Vec::new(), true)
}

/// The AC receiver's collection PATTERN for a HashBag operand `op` with `k` fixed element
/// slots: a connective process-`Par` with `k` send-patterns `@"ac:{op}"!(FreeVar(i))` (each
/// binding element σ slot `i`) plus a process remainder `EVar(FreeVar(k))` (binding `rest`,
/// the residual soup). The native connective / `sub_pars` matcher assigns the `k` send-
/// patterns to `k` carrier sends in ANY order (`MaximumBipartiteMatch`) and binds the residual
/// to the remainder — the order-independent multiset match — inside one atomic `consume`.
///
/// The remainder is `new_freevar_par(k)`, whose `EVar(FreeVar(k))` in `exprs` is exactly the
/// `var_level` the spatial matcher reads (`spatial_matcher.rs`); element `i` binds `FreeVar(i)`.
pub fn ac_bag_pattern(op: &str, k: usize) -> Par {
    let element_channel = format!("ac:{op}");
    // Start from the process remainder (a top-level free var at level k; connective_used).
    let mut pattern = new_freevar_par(k as i32, Vec::new());
    for i in 0..k {
        let send_pattern = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![new_freevar_par(i as i32, Vec::new())],
            false,
            Vec::new(),
            true,
            Vec::new(),
            true,
        );
        pattern = pattern.append(send_pattern);
    }
    pattern
}

/// A STRUCTURED `ESet` element PATTERN `⟦op(FreeVar(base), …, FreeVar(base+arity-1))⟧` for the AC4
/// paired/correlated set match (`ZipAc`): a tagged `EList` `[GPrivate(reflect_tag(op)), FreeVar(base),
/// …]` — byte-identical to [`reflect_ground_term_par`]'s image of an `op`-headed element, but with
/// the `arity` argument positions as consecutive free-var σ slots. Inside an [`ac_set_paired_receiver_par`]
/// `ESet` connective, this pattern matches ONE set element whose head constructor is `op` and binds
/// its args, so two such patterns sharing a slot (via the receiver's `Receive.condition`) express a
/// correlated pairing (e.g. `Pair(a, x)` and `Pair(a, y)` sharing `a`). `fingerprint` MUST be the
/// carrier's, so the pattern's head tag equals the reflected element's.
pub fn ac_set_element_pattern(op: &str, arity: usize, base: usize, fingerprint: &str) -> Par {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(fingerprint, op));
    let mut elements = Vec::with_capacity(arity + 1);
    elements.push(tag);
    for i in 0..arity {
        elements.push(new_freevar_par((base + i) as i32, Vec::new()));
    }
    // A connective element pattern (free-var args); free vars are tracked by the bind `free_count`,
    // so `locally_free` is empty and `connective_used` is set.
    new_elist_par(elements, Vec::new(), true, None, Vec::new(), true)
}

/// Build the AC4 PAIRED/CORRELATED `ESet` receiver (`ZipAc`) — the native-set analogue of
/// [`comm_receiver_par`] / [`structural_ac_receiver_par`] (which match a process-soup): a persistent
///
/// ```text
/// for( < ESet[ ⟦elem_0⟧, …, ⟦elem_{k-1}⟧ ... rest ] , out > <- source )
///   where ( condition )
///   { out!( rhs ) }
/// ```
///
/// The `ESet` connective pattern matches `k` STRUCTURED set elements ([`ac_set_element_pattern`])
/// ORDER-INDEPENDENTLY (native `list_match_single_` over `ParSet`) + binds the residual set to the
/// remainder, inside ONE atomic `consume`. The `element_patterns` bind `element_slots` free-var σ
/// slots in total (their argument positions, `FreeVar(0..element_slots-1)`); the remainder is
/// `FreeVar(element_slots)` and `out` is `FreeVar(element_slots + 1)`, so `free_count = element_slots
/// + 2`. The `condition` (a `Receive.condition` over the bound slots, e.g.
/// [`nonlinear_consistency_condition`] `EEq(slot_i, slot_j)`) commits the COMM only when the
/// correlation holds — the CORRELATED pairing enforced on the reducer. The body fires `rhs` (the RHS
/// `⟦R⟧σ`, referencing the bound slots) on `out` (`BoundVar(0)`).
pub fn ac_set_paired_receiver_par(
    element_patterns: Vec<Par>,
    element_slots: usize,
    condition: Option<Par>,
    rhs: Par,
    source: Par,
) -> Par {
    let free_count = element_slots + 2; // element slots + rest + out
    let remainder = Var { var_instance: Some(VarInstance::FreeVar(element_slots as i32)) };
    let eset_pattern =
        new_eset_par(element_patterns, Vec::new(), true, Some(remainder), Vec::new(), true);
    let out_channel = bound_formal(free_count, element_slots + 1); // out = BoundVar(0)
    let body_free = union(rhs.locally_free.clone(), create_bit_vector(&[0]));
    let body =
        new_send_par(out_channel, vec![rhs], false, body_free.clone(), false, body_free, false);
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![eset_pattern, new_freevar_par((element_slots + 1) as i32, Vec::new())],
            source: Some(source),
            remainder: None,
            free_count: free_count as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: free_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition,
    };
    Par::default().with_receives(vec![receive])
}

/// The AC4 paired/correlated set CONSISTENCY guard: an `EEq(slot_i, slot_j) ∧ …` `Receive.condition`
/// over the receiver's bound slots enforcing that the `occurrence_slots` (the free-var positions a
/// non-linear shared variable binds across the paired elements) are name-equal — the `N ≡ N`
/// correlation, expressed as the [`ac_set_paired_receiver_par`] receiver's condition. `free_count`
/// is the receiver's total (`element_slots + 2`). This reuses the SAME
/// [`nonlinear_consistency_condition`] machinery as the Comm / structural-AC soup path, so the native
/// set pairing matches ONLY correlated picks.
pub fn ac_set_correlation_condition(occurrence_slots: &[usize], free_count: usize) -> Par {
    nonlinear_consistency_condition(occurrence_slots, free_count)
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

/// The AC injection `call` for an un-skipped HashBag AC rewrite: `channel!(⟦whole_bag⟧, @out)`,
/// where `⟦whole_bag⟧` is the process-soup carrier ([`reflect_ground_term_par`] routes a HashBag
/// `GroundTerm` to the soup). This is the exact 2-value message the AC receiver
/// ([`ac_sigma_receiver_par`]) consumes — the connective collection pattern matches the soup
/// order-independently and the out formal binds `@out`. `channel_name` MUST be the AC receiver's
/// SOURCE (the rule's trace channel), so the accept triad (receiver source ≡ injection channel)
/// holds by symmetric derivation, exactly as the flat `term_contract_call` path.
pub fn ac_contract_call(
    channel_name: &str,
    whole_bag: &GroundTerm,
    fingerprint: &str,
    out_channel: &str,
) -> Par {
    let soup = reflect_ground_term_par(whole_bag, fingerprint);
    new_send_par(
        new_gstring_par(channel_name.to_string(), Vec::new(), false),
        vec![soup, new_gstring_par(out_channel.to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// The contextual-JOIN injection `call` for a congruence rewrite (Stage 3a): deliver the
/// `n` reduced holes `⟦T_i⟧` on their premise location channels so the installed
/// [`contextual_join_receiver_par`] fires, emitting `⟦K'⟧` on `@out`.
///
/// The atomic n-ary join binds ALL `n` premise channels, so the injection publishes one send
/// per premise: `c(ℓ_i)!(⟦T_i⟧)` for `i < n-1`, and `c(ℓ_{n-1})!(⟦T_{n-1}⟧, @out)` on the
/// LAST channel (which also carries the dynamic out channel the join's body sends `⟦K'⟧` on).
/// `premise_channels` and `reduced_holes` MUST be the join's premise channels and the reduced
/// holes in premise order (`premise_channels.len() == reduced_holes.len() == n`), so the
/// accept triad (receiver premise channels ≡ injection channels) holds by symmetric
/// derivation, exactly as the flat [`term_contract_call`] / [`ac_contract_call`] paths.
///
/// A degenerate `n = 0` (no premise holes — not a real congruence rule) yields an empty
/// `Par`: nothing to deliver, and the join could never fire.
pub fn contextual_contract_call(
    premise_channels: &[&str],
    reduced_holes: Vec<Par>,
    out_channel: &str,
) -> Par {
    let n = premise_channels.len().min(reduced_holes.len());
    let mut call = Par::default();
    for (index, (channel, hole)) in premise_channels
        .iter()
        .zip(reduced_holes.into_iter())
        .enumerate()
    {
        // The last premise send also carries the dynamic out channel (a quoted GString name,
        // exactly how `term_contract_call` lowers its return channel).
        let data = if index + 1 == n {
            vec![hole, new_gstring_par(out_channel.to_string(), Vec::new(), false)]
        } else {
            vec![hole]
        };
        let free = data
            .iter()
            .fold(Vec::new(), |acc, par| union(acc, par.locally_free.clone()));
        let send = new_send_par(
            new_gstring_par(channel.to_string(), Vec::new(), false),
            data,
            false,
            free.clone(),
            false,
            free,
            false,
        );
        call = call.append(send);
    }
    call
}

/// The intermediate PREMISE-HOLE channel `ph:{premise_channel}` an in-Rho contextual match routes
/// a hole position's nested firing to (Stage 4 S-contextual) before the [`contextual_hole_bridge_par`]
/// re-delivers the reduced hole on the join's premise channel.
///
/// The base automaton's located accept fires the hole's premise σ-receiver with THIS channel as its
/// dynamic out, so the reduced hole `T_i` lands on `ph:c(ℓ_i)` as a bare single-value send
/// `ph:c(ℓ_i)!(⟦T_i⟧)`. The bridge then reads it and re-sends it on the actual premise channel
/// `c(ℓ_i)` in the join's bind ABI (the last hole additionally carrying the dynamic out). The `ph:`
/// prefix keeps this channel DISJOINT from the join's own premise channel `c(ℓ_i)` (so the σ-receiver
/// firing and the join never race for one send) and from every `loc:`/`cap:`/`ac:` automaton channel.
pub fn contextual_premise_hole_channel(premise_channel: &str) -> String {
    format!("ph:{premise_channel}")
}

/// The Stage-4 S-contextual HOLE BRIDGE: forward a hole position's IN-RHO reduced hole from its
/// intermediate [`contextual_premise_hole_channel`] onto the installed join's premise channel in the
/// join's bind ABI.
///
/// ```text
/// for( T <- ph:c(ℓ_i) ){ c(ℓ_i)!(T [, @out]) }
/// ```
///
/// The base automaton locates the hole's premise redex from the ONE spread and fires its
/// σ-receiver, which emits the reduced hole `⟦T_i⟧` on `ph:c(ℓ_i)` (the σ-receiver's dynamic out was
/// routed there). This one-shot bridge binds that reduced hole (`T = BoundVar(0)`) and re-delivers
/// it on the premise channel `c(ℓ_i)` exactly as the host-σ [`contextual_contract_call`] would — a
/// bare `c(ℓ_i)!(T)` for a non-last hole (`out_channel = None`), or `c(ℓ_i)!(T, @out)` for the LAST
/// hole (`out_channel = Some(out)`, which also carries the join's dynamic out channel). So the
/// reduced hole the reused [`contextual_join_receiver_par`] binds is the automaton's NESTED FIRING,
/// never the report σ.
pub fn contextual_hole_bridge_par(
    hole_channel: &str,
    premise_channel: &str,
    out_channel: Option<&str>,
) -> Par {
    // The reduced hole is the single bound formal `T = BoundVar(0)`; the send is free only there.
    let hole = bound_formal(1, 0);
    let mut data = Vec::with_capacity(2);
    data.push(hole);
    if let Some(out) = out_channel {
        // The LAST hole's send also carries the dynamic out channel (a quoted GString name), exactly
        // how `contextual_contract_call` lowers the join's out — so the unary join's `(T_0, out)`
        // bind is satisfied.
        data.push(new_gstring_par(out.to_string(), Vec::new(), false));
    }
    let free = create_bit_vector(&[0]);
    let body = new_send_par(
        new_gstring_par(premise_channel.to_string(), Vec::new(), false),
        data,
        false,
        free.clone(),
        false,
        free,
        false,
    );
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(new_gstring_par(hole_channel.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: 1,
        }],
        body: Some(body),
        persistent: false,
        peek: false,
        bind_count: 1,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    Par::default().with_receives(vec![receive])
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

/// The CHAIN collapse channel of the node at `root_location`'s spread — the `col:`-kind
/// quoted name that carries `⟦subtree⟧` UP to the parent's collapse receiver. It is read
/// exactly once (by the parent), so the bottom-up fold never contends with the automaton.
pub fn collapse_chain_location(root_location: &str) -> String {
    format!("col:{root_location}")
}

/// The CAPTURE collapse channel of the node at `root_location`'s spread — the `cap:`-kind
/// quoted name the in-Rho automaton reads at a Var-leaf state to bind the positional σ for
/// an ARBITRARY-depth matched subterm (the M-collapse fix). It carries the SAME `⟦subtree⟧`
/// value as the chain channel but on a DISJOINT name, so the parent's chain read and the
/// automaton's capture read never race for one value (each is consumed at most once — O1).
pub fn collapse_capture_location(root_location: &str) -> String {
    format!("cap:{root_location}")
}

/// The SITE-KEYED AC carrier channel of a HashBag AC operand bag at the spread node whose `loc:`
/// head-tag channel is `loc_channel`, for operand constructor `op` — the `ac:`-kind quoted name the
/// match driver ([`ac_match_call_par`]) publishes the bag's process-soup on and the co-installed
/// [`ac_sigma_receiver_par`] reads from.
///
/// The site key `⌜(ρ,ℓ)⌝` is inherited from `loc_channel` (the ν-free location path the spread and
/// automaton already agree on via [`spread_root_location`] / [`spread_child_location`]), so two
/// same-`op` bags at DISTINCT positions (`loc:ρ/ℓ₁ ≠ loc:ρ/ℓ₂`) get DISJOINT carriers
/// (`ac:loc:ρ/ℓ₁/op ≠ ac:loc:ρ/ℓ₂/op`) — Red-team #5: without the site key two same-`op` bags'
/// soups would intermingle on one `ac:op` channel and the native matcher could pick cross-bag
/// elements, a latent soundness bug. Both the carrier delivery and the co-installed receiver derive
/// the channel through THIS one helper, so they rendezvous on exactly one bag's soup.
pub fn ac_carrier_channel(loc_channel: &str, op: &str) -> String {
    format!("ac:{loc_channel}/{op}")
}

/// Spread a ground subject term across per-location channels for in-Rho
/// set-automaton matching (`knotted-topoi` Appendix A):
///
/// ```text
/// ⟦f(t₁,…,tₙ)⟧_ℓ = loc(ℓ)!(f̲) │ ∏ᵢ ⟦tᵢ⟧_{ℓ·(f,i)} │ collapse(f̲; ℓ)
/// ```
///
/// Each node publishes its head tag `f̲` (byte-identical to
/// [`reflect_ground_term_par`]'s tag — the SHARED [`reflect_tag`] ABI) on its
/// deterministic `loc:` location channel ([`spread_root_location`] /
/// [`spread_child_location`]), which the automaton reads to DISPATCH / DESCEND; the
/// child subterms are spread on the derived child channels, which the automaton knows
/// statically. This is the ν-free scheme (INV-7): a flat parallel composition of ground
/// sends — no `New` — and the head-tag message carries the tag ALONE, never child channels.
///
/// It ALSO emits the M-collapse machinery: a bottom-up `collapse` fold that publishes the
/// FULLY COLLAPSED subterm value `⟦subtree⟧` on two DISJOINT channels — `col:` (read once by
/// the parent's fold) and `cap:` (read once by the automaton's Var-leaf state). A Var-leaf
/// matching a NON-nullary subterm therefore binds `⟦subtree⟧` (not just its head tag), the
/// positional σ for an arbitrary-depth subject. Each `col:`/`cap:` value is consumed at most
/// once — the collapse IS that consumption — so matching stays O1 (each symbol once).
/// `root_location` is the site root ρ of the `⌜(ρ,ℓ)⌝` freshness idiom.
///
/// The `col:`/`cap:` fold is the Rho realization of [`reflect_ground_term_par`]: the value
/// published at a node's collapse channels is byte-identical to `reflect_ground_term_par`
/// over that subtree, assembled bottom-up rather than in one host-side nest.
pub fn spread_term_par(term: &GroundTerm, language_fingerprint: &str, root_location: &str) -> Par {
    spread_term_par_at(
        term,
        language_fingerprint,
        &spread_root_location(root_location),
        &collapse_chain_location(root_location),
        &collapse_capture_location(root_location),
    )
}

/// Stage 4 (S-AC) — build the co-install `Par` that LOCATES every HashBag AC redex of `subject` and
/// fires it IN RHO, re-sourcing each operand bag from the SPREAD of the subject (NOT the host-σ
/// report). The AC analogue of the base [`in_rho_match_all_sites_call_par`](crate::in_rho_match_all_sites_call_par)
/// leg: walk `subject` (from root nonce `root_site`, the SAME `loc:` derivation the spread uses),
/// and at every bag node whose constructor is one of the admitted AC `entries`' ops:
///
///   1. derive the SITE-KEYED carrier `ac:⌜ℓ⌝/op` ([`ac_carrier_channel`], disjoint per position);
///   2. co-install an [`ac_sigma_receiver_par`] over that carrier — byte-identical to the installed
///      AC receiver EXCEPT its source is the per-site carrier — which picks k-of-n + binds `rest`
///      via the native connective match (`ac_bag_pattern`) inside ONE atomic `consume` and fires
///      the rule's RHS `⟦R⟧σ` on `@out`;
///   3. publish `carrier!(⟦bag⟧, @out)` where `⟦bag⟧` is [`reflect_ac_bag_par`] over THIS node's
///      ground elements (the subject bag — NO `find_sigma`).
///
/// A HashBag has no positional child descent, so the walk does NOT recurse into a bag's elements
/// (it keeps descending the structural children of non-bag nodes, so a nested bag is located). The
/// carrier delivery and the receiver both derive the carrier through [`ac_carrier_channel`], so they
/// rendezvous on exactly one bag's soup; distinct sites are disjoint. Returns the parallel
/// composition of every located bag's `(receiver ‖ delivery)` (empty when `subject` has no AC redex
/// — the caller then runs the bare base call).
///
/// `language_fingerprint` MUST be the ruleset's (the spread's) fingerprint, and each entry's
/// `rhs_par` was reflected with it, so the soup's element tags and the receiver's RHS tags agree.
pub fn ac_match_call_par(
    subject: &GroundTerm,
    entries: &[RhoNetAcMatchEntry],
    root_site: &str,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    if entries.is_empty() {
        return Par::default();
    }
    let by_op: HashMap<&str, &RhoNetAcMatchEntry> =
        entries.iter().map(|entry| (entry.op.as_str(), entry)).collect();
    ac_match_install_at(
        subject,
        &spread_root_location(root_site),
        &by_op,
        out_channel,
        language_fingerprint,
    )
}

/// Recursively LOCATE + co-install the AC receivers for `node` at the position whose `loc:` head-tag
/// channel is `loc_channel` (the SAME location derivation the spread uses). See
/// [`ac_match_call_par`].
fn ac_match_install_at(
    node: &GroundTerm,
    loc_channel: &str,
    by_op: &HashMap<&str, &RhoNetAcMatchEntry>,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    // A HashBag AC operand bag: fire it IN RHO over the site-keyed carrier if its op is admitted.
    // Do NOT recurse into its elements (a bag has no positional child descent).
    if let Some(CollectionType::HashBag) = node.coll_type {
        let Some(entry) = by_op.get(node.constructor.as_str()) else {
            return Par::default();
        };
        let carrier = ac_carrier_channel(loc_channel, &node.constructor);
        // The co-installed AC receiver over the site-keyed carrier — SAME `ac_sigma_receiver_par`
        // shape (incl. the AC3 non-linear `Receive.condition` guard) as the installed one, only the
        // source differs (so it picks k-of-n from the SPREAD bag, not the report σ).
        let receiver = ac_sigma_receiver_par_with_condition(
            entry.kind.clone(),
            &entry.op,
            entry.arity,
            entry.rhs_par.clone(),
            new_gstring_par(carrier.clone(), Vec::new(), false),
            entry.condition.clone(),
        );
        // The carrier delivery `carrier!(⟦bag⟧, @out)` — the process-soup sourced from THIS subject
        // bag's ground elements (`reflect_ac_bag_par`), NOT `find_sigma`. The soup is ground, so the
        // send is closed.
        let soup = reflect_ac_bag_par(node, language_fingerprint);
        let delivery = new_send_par(
            new_gstring_par(carrier, Vec::new(), false),
            vec![soup, new_gstring_par(out_channel.to_string(), Vec::new(), false)],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        return receiver.append(delivery);
    }
    // A structural node: descend into each child at its derived `loc:` channel (a nested bag is
    // located), composing every located bag's co-install.
    let mut par = Par::default();
    for (index, child) in node.children.iter().enumerate() {
        let child_loc = spread_child_location(loc_channel, &node.constructor, index);
        par = par.append(ac_match_install_at(
            child,
            &child_loc,
            by_op,
            out_channel,
            language_fingerprint,
        ));
    }
    par
}

fn spread_term_par_at(
    term: &GroundTerm,
    language_fingerprint: &str,
    location: &str,
    chain_location: &str,
    capture_location: &str,
) -> Par {
    // Stage 4 (S-AC): a HashBag AC operand bag has NO positional `loc:`/child descent structure —
    // the in-Rho AC matcher (a co-installed [`ac_sigma_receiver_par`], see
    // [`ac_match_call_par`](crate::ac_match_call_par)) picks k-of-n + binds `rest` from the bag's
    // order-independent process-soup carrier ON the interpreter, NOT by positional descent. So the
    // spread publishes ONLY the bag's COLLAPSE value (the soup = [`reflect_ac_bag_par`], the same
    // value [`reflect_ground_term_par`] produces for a HashBag `GroundTerm`) on this node's
    // `col:`/`cap:` channels — the value a PARENT's fold / a Var-leaf `cap:` capture binds when the
    // bag is a σ subterm — and does NOT positionally recurse (no `loc:` head-tag, no child spread).
    // The AC redex firing is the co-installed receiver over the DISJOINT site-keyed `ac:` carrier
    // (Red-team #1: the `ac:` carrier and the `col:`/`cap:` collapse are disjoint channels, each
    // consumed at most once), so re-sourcing the collection from the spread is the genuine in-Rho AC
    // match. Every AC operand collection kind (`HashBag` soup / `HashSet` `ESet` / `HashMap` `EMap`)
    // publishes only its native carrier value on `col:`/`cap:` — the value a parent's fold or a
    // Var-leaf `cap:` capture binds — and does NOT positionally recurse.
    if matches!(
        term.coll_type,
        Some(CollectionType::HashBag | CollectionType::HashSet | CollectionType::HashMap)
    ) {
        let soup = reflect_ac_collection_par(term, language_fingerprint);
        let free = soup.locally_free.clone();
        let chain = new_send_par(
            new_gstring_par(chain_location.to_string(), Vec::new(), false),
            vec![soup.clone()],
            false,
            free.clone(),
            false,
            free.clone(),
            false,
        );
        let capture = new_send_par(
            new_gstring_par(capture_location.to_string(), Vec::new(), false),
            vec![soup],
            false,
            free.clone(),
            false,
            free,
            false,
        );
        return chain.append(capture);
    }
    // This node's head-tag send on its `loc:` channel — the tag ALONE (Appendix A publishes
    // `f̲`; child locations are derived, never carried in the message). The automaton reads
    // it to Match-dispatch (root / nested App descent), NEVER the collapse fold.
    let head_tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &term.constructor));
    let mut par = new_send_par(
        new_gstring_par(location.to_string(), Vec::new(), false),
        vec![head_tag.clone()],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    // Spread each child on its derived `loc:`/`col:`/`cap:` channels, in left-to-right `L`
    // order, and collect the children's CHAIN channels so this node's fold can read them.
    let mut child_chain_channels = Vec::with_capacity(term.children.len());
    for (index, child) in term.children.iter().enumerate() {
        let child_location = spread_child_location(location, &term.constructor, index);
        let child_chain = spread_child_location(chain_location, &term.constructor, index);
        let child_capture = spread_child_location(capture_location, &term.constructor, index);
        child_chain_channels.push(child_chain.clone());
        par = par.append(spread_term_par_at(
            child,
            language_fingerprint,
            &child_location,
            &child_chain,
            &child_capture,
        ));
    }
    // Bottom-up collapse: publish `⟦subtree⟧` on this node's `col:` (chain) and `cap:`
    // (capture) channels.
    par.append(collapse_publish(
        chain_location,
        capture_location,
        head_tag,
        &child_chain_channels,
    ))
}

/// Publish `⟦subtree⟧` on this node's CHAIN (`col:`) and CAPTURE (`cap:`) channels.
///
/// A leaf (no children) is two ground sends `col!(EList[f̲]) │ cap!(EList[f̲])` (`⟦leaf⟧`,
/// byte-identical to [`reflect_ground_term_par`] over a nullary constructor). An internal
/// node is the collapse RECEIVER
/// `for(v₀ <- col:…/f.0 ; … ; v_{n-1} <- col:…/f.{n-1}){ col!(EList[f̲,v₀,…]) │ cap!(EList[f̲,v₀,…]) }`
/// that CONSUMES its children's chain values (each once) and REBUILDS its own `⟦subtree⟧` —
/// so a Var-leaf state reading `cap:ℓ` binds the full positional σ for an arbitrary-depth
/// subterm. The head tag `f̲` is baked GROUND (never read from `loc:`), so the fold never
/// contends with the automaton's head-tag descent. Child `i` binds `BoundVar(n-1-i)` (the
/// join flattens in bind order), so `EList[f̲, v₀, …, v_{n-1}]` reproduces
/// [`reflect_ground_term_par`]'s `[tag, ⟦c₀⟧, …]` shape.
fn collapse_publish(
    chain_location: &str,
    capture_location: &str,
    head_tag: Par,
    child_chain_channels: &[String],
) -> Par {
    let n = child_chain_channels.len();
    if n == 0 {
        // Leaf: ⟦leaf⟧ = EList[tag]; two linear ground sends (chain + capture).
        let collapsed = new_elist_par(vec![head_tag], Vec::new(), false, None, Vec::new(), false);
        let chain = new_send_par(
            new_gstring_par(chain_location.to_string(), Vec::new(), false),
            vec![collapsed.clone()],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let capture = new_send_par(
            new_gstring_par(capture_location.to_string(), Vec::new(), false),
            vec![collapsed],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        return chain.append(capture);
    }
    // Internal: one polyadic join binding all `n` children's chain values (child `i` →
    // BoundVar(n-1-i)); the body republishes `⟦subtree⟧` on chain + capture.
    let binds: Vec<ReceiveBind> = child_chain_channels
        .iter()
        .map(|channel| ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(new_gstring_par(channel.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: 1,
        })
        .collect();
    let all_free: Vec<usize> = (0..n).collect();
    let free_bits = create_bit_vector(&all_free);
    let mut elements = Vec::with_capacity(n + 1);
    elements.push(head_tag);
    for i in 0..n {
        let idx = n - 1 - i;
        elements.push(new_boundvar_par(idx as i32, create_bit_vector(&[idx]), false));
    }
    let collapsed =
        new_elist_par(elements, free_bits.clone(), false, None, free_bits.clone(), false);
    let chain = new_send_par(
        new_gstring_par(chain_location.to_string(), Vec::new(), false),
        vec![collapsed.clone()],
        false,
        free_bits.clone(),
        false,
        free_bits.clone(),
        false,
    );
    let capture = new_send_par(
        new_gstring_par(capture_location.to_string(), Vec::new(), false),
        vec![collapsed],
        false,
        free_bits.clone(),
        false,
        free_bits,
        false,
    );
    let receive = Receive {
        binds,
        body: Some(chain.append(capture)),
        persistent: false,
        peek: false,
        bind_count: n as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    Par::default().with_receives(vec![receive])
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
/// A LHS-bound variable reflects to its σ-tuple De Bruijn index; a `Lambda`/
/// `MultiLambda` reflects to a tagged binder node (Stage 3c) and a `Subst`/
/// `MultiSubst` resolves to the host-computed reduct at its scope variable's σ-slot
/// (see [`reflect_term_par_env`]). A dangling RHS variable (one with no LHS
/// binding and not bound by an enclosing binder) fails closed
/// (`DanglingRhsVariable`); collection nodes fail closed with their
/// [`UnsupportedFamily`].
fn reflect_term_par(
    pattern: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    reflect_term_par_env(pattern, vars, k, language_fingerprint, &mut Vec::new(), def)
}

/// The reserved reflection tag for a single-binder `Lambda` node — a synthetic
/// constructor label (`^lambda`) that cannot collide with any user constructor
/// (which is a Rust `Ident`, never containing `^`), so the tagged binder node is
/// distinct from every `Apply` node AND from any user `GString` term data. The
/// multi-binder tag is `^multilambda`; a bound-variable occurrence uses `^bound`.
const LAMBDA_REFLECT_LABEL: &str = "^lambda";
const MULTILAMBDA_REFLECT_LABEL: &str = "^multilambda";
const BOUND_VAR_REFLECT_LABEL: &str = "^bound";

/// Reflect an RHS pattern term to a normalized `Par`, threading a **binder
/// environment** (the RHS binders currently in scope, De Bruijn stack). A variable
/// occurrence that names an in-scope binder reflects to a distinguished bound-var
/// leaf (`EList[GPrivate(reflect_tag(^bound)), GString(name)]`), NOT a σ-slot
/// `BoundVar`; a free variable reflects to its σ-slot index; any other free name
/// fails closed. This is the RHS dual of [`collect_lhs_vars_term`]'s De Bruijn
/// environment.
fn reflect_term_par_env(
    pattern: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            // A bound occurrence (in scope of an enclosing RHS binder) reflects to a
            // distinguished bound-var leaf — it is supplied by the binder, not by σ.
            if binder_env.contains(&name.to_string()) {
                return Ok(reflect_bound_var_leaf(name, language_fingerprint));
            }
            match vars.iter().position(|var| var == name) {
                Some(index) => Ok(new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)),
                // A RHS variable not bound by the LHS (and not a binder) has no σ-tuple
                // slot; the rewrite is ill-formed for a flat receiver. Fail closed rather
                // than emit a dangling De Bruijn index.
                None => Err(UnsupportedFamily::DanglingRhsVariable),
            }
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            // Stage AC2b: a HashBag constructor over a single collection metapattern
            // `op{e_0, …, ...rest}` reflects to the BARE process-soup carrier — the SAME shape
            // `reflect_ground_term_par` emits for a HashBag ground term — NOT a tagged `EList`, so
            // a bag-VALUED RHS fires as one FLAT bag: each fixed element is a send
            // `@"ac:{op}"!(⟦e_i⟧σ)` and the `...rest` σ-slot delivers the residual bag's sends,
            // which parallel composition SPLICES in (mirroring `dovetail::rules::add_flattened_bag`).
            // Only when `def` resolves `op` to a HashBag; every other collection RHS (no `def`, a
            // non-HashBag kind, or an unresolved kind) falls through to the fail-closed `Collection`
            // arm below, exactly as before this stage.
            if let (Some(def), [Pattern::Collection { coll_type, elements, rest }]) =
                (def, args.as_slice())
            {
                if resolve_collection_kind(def, constructor, coll_type.as_ref())
                    == Some(CollectionType::HashBag)
                {
                    return reflect_hashbag_soup_par(
                        constructor,
                        elements,
                        rest.as_ref(),
                        vars,
                        k,
                        language_fingerprint,
                        binder_env,
                        def,
                    );
                }
            }
            let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
                language_fingerprint,
                &constructor.to_string(),
            ));
            let mut elements = Vec::with_capacity(args.len() + 1);
            let mut locally_free = tag.locally_free.clone();
            elements.push(tag);
            for arg in args {
                let child =
                    reflect_term_par_env(arg, vars, k, language_fingerprint, binder_env, def)?;
                locally_free = union(locally_free, child.locally_free.clone());
                elements.push(child);
            }
            Ok(new_elist_par(elements, locally_free.clone(), false, None, locally_free, false))
        },
        // A binder reflects to a tagged binder node `EList[tag, ⟦binder⟧, ⟦body⟧]`
        // (mirrors the Apply arm): the binder name is captured as a bound-var leaf, and
        // the body is reflected with the binder pushed onto the De Bruijn environment,
        // so a bound occurrence in the body reflects to a bound-var leaf, not a σ-slot.
        Pattern::Term(PatternTerm::Lambda { binder, body }) => reflect_binder_node(
            LAMBDA_REFLECT_LABEL,
            std::slice::from_ref(binder),
            body,
            vars,
            k,
            language_fingerprint,
            binder_env,
            def,
        ),
        Pattern::Term(PatternTerm::MultiLambda { binders, body }) => reflect_binder_node(
            MULTILAMBDA_REFLECT_LABEL,
            binders,
            body,
            vars,
            k,
            language_fingerprint,
            binder_env,
            def,
        ),
        // A substitution `subst(scope, …)` / `(eval scope arg)` resolves to the
        // host-computed REDUCED term at its scope variable's σ-slot (Stage 3c model-b):
        // the host applies the capture-avoiding substitution and hands the reduct as the
        // scope slot's σ, so the receiver body forwards `BoundVar(scope-slot)`. Requires
        // the scope to be a bound LHS variable; an OPEN substitution under a
        // genuinely-free scope fails closed (`Substitution`).
        Pattern::Term(PatternTerm::MultiSubst { scope, .. }) => {
            reflect_subst_scope_slot(scope, vars, k)
        },
        Pattern::Term(PatternTerm::Subst { term, .. }) => reflect_subst_scope_slot(term, vars, k),
        // A HashBag bag-VALUED RHS is intercepted at its ENCLOSING `Apply` (which supplies the `op`
        // for the `@"ac:{op}"` soup channel — see the `Apply` arm's Stage AC2b intercept above). A
        // BARE collection reaching here has no enclosing constructor, hence no `op` and no soup
        // image; it fails closed (mirrors `pattern_to_dovetail`'s bare-collection rejection).
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
    }
}

/// A bound-variable occurrence reflected to its distinguished leaf
/// `EList[GPrivate(reflect_tag(^bound)), GString(name)]` — the reserved `^bound`
/// tag makes it collision-free with any `Apply` node (a real constructor) and with
/// any σ-slot `BoundVar`, and the `GString` name distinguishes distinct binders, so
/// the binder-node reflection is injective.
fn reflect_bound_var_leaf(name: &Ident, language_fingerprint: &str) -> Par {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
        language_fingerprint,
        BOUND_VAR_REFLECT_LABEL,
    ));
    let name_leaf = new_gstring_par(name.to_string(), Vec::new(), false);
    let locally_free = union(tag.locally_free.clone(), name_leaf.locally_free.clone());
    new_elist_par(vec![tag, name_leaf], locally_free.clone(), false, None, locally_free, false)
}

/// Reflect a binder node (`Lambda`/`MultiLambda`) as a tagged `EList`
/// `[GPrivate(reflect_tag(label)), ⟦binder₀⟧, …, ⟦binderₘ₋₁⟧, ⟦body⟧]`: each binder
/// name is a bound-var leaf and the body is reflected with the binders pushed onto
/// the De Bruijn environment. Injective and collision-free (reserved `label`).
#[allow(clippy::too_many_arguments)]
fn reflect_binder_node(
    label: &str,
    binders: &[Ident],
    body: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, label));
    let mut elements = Vec::with_capacity(binders.len() + 2);
    let mut locally_free = tag.locally_free.clone();
    elements.push(tag);
    for binder in binders {
        let leaf = reflect_bound_var_leaf(binder, language_fingerprint);
        locally_free = union(locally_free, leaf.locally_free.clone());
        elements.push(leaf);
    }
    for binder in binders {
        binder_env.push(binder.to_string());
    }
    let body_result = reflect_term_par_env(body, vars, k, language_fingerprint, binder_env, def);
    for _ in binders {
        binder_env.pop();
    }
    let body_par = body_result?;
    locally_free = union(locally_free, body_par.locally_free.clone());
    elements.push(body_par);
    Ok(new_elist_par(elements, locally_free.clone(), false, None, locally_free, false))
}

/// Resolve a substitution's scope to its σ-slot `BoundVar`: the host hands the
/// REDUCED term (`RHS[σ]` after capture-avoiding substitution) as the σ of the
/// scope variable, so the receiver body simply forwards that slot. The scope MUST
/// be a bound LHS variable; an OPEN substitution under a genuinely-free scope (no σ
/// binding) has no slot and fails closed (`Substitution`).
fn reflect_subst_scope_slot(
    scope: &Pattern,
    vars: &[Ident],
    k: usize,
) -> Result<Par, UnsupportedFamily> {
    match scope {
        Pattern::Term(PatternTerm::Var(name)) => match vars.iter().position(|var| var == name) {
            Some(index) => Ok(new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)),
            None => Err(UnsupportedFamily::Substitution),
        },
        // A non-variable scope (a literal binder body / nested term) has no single σ-slot
        // that the host can fill with one reduct — out of scope this slice, fail closed.
        _ => Err(UnsupportedFamily::Substitution),
    }
}

/// Reflect a HashBag constructor's bag-VALUED RHS `op{e_0, …, e_{m-1}, ...rest}` to the
/// process-soup carrier (Stage AC2b): each fixed element `e_i` becomes a send
/// `@"ac:{op}"!(⟦e_i⟧σ)` and the residual `...rest` becomes the reflected `rest` σ-slot — all
/// parallel-composed.
///
/// This is byte-identical in SHAPE to [`reflect_ground_term_par`]'s HashBag reflection
/// ([`reflect_ac_bag_par`]): a sends-only `Par` on the `@"ac:{op}"` element channel, one send per
/// element, order-independent and multiplicity-preserving. So when this is the AC receiver body's
/// `⟦R⟧σ` ([`ac_sigma_receiver_par`]), firing it emits a FLAT bag: the AC receiver bound `rest`
/// (`ac_bag_pattern`'s process remainder) to the residual soup — the leftover `@"ac:{op}"!(…)`
/// sends — so the reflected `rest` σ-slot substitutes to those sends and parallel composition
/// SPLICES them into the fixed-element sends, never nesting (mirroring the host's
/// `dovetail::rules::add_flattened_bag`).
///
/// Each fixed element reflects through the SAME [`reflect_term_par_env`] (so a `Wrap(x)` element →
/// `EList[tag_Wrap, ⟦x⟧σ]`), threading `binder_env`/`def` so a nested binder or a nested same-op
/// bag element reflects correctly. `rest`, when present, is reflected as its σ-slot `BoundVar`
/// (`Pattern::Var`), so an unbound `rest` fails closed exactly like any dangling RHS variable
/// ([`UnsupportedFamily::DanglingRhsVariable`]); a `None` rest yields an exact (rest-free) bag.
#[allow(clippy::too_many_arguments)]
fn reflect_hashbag_soup_par(
    op: &Ident,
    elements: &[Pattern],
    rest: Option<&Ident>,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: &LanguageDef,
) -> Result<Par, UnsupportedFamily> {
    let element_channel = format!("ac:{op}");
    let mut soup = Par::default();
    // Each fixed element `e_i` → a ground send `@"ac:{op}"!(⟦e_i⟧σ)` (the subject side's
    // `reflect_ac_bag_par` element shape). Reflected with `Some(def)` so a nested same-op bag
    // element is itself intercepted at its `Apply`.
    for element in elements {
        let reflected =
            reflect_term_par_env(element, vars, k, language_fingerprint, binder_env, Some(def))?;
        let free = reflected.locally_free.clone();
        let send = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![reflected],
            false,
            free.clone(),
            false,
            free,
            false,
        );
        soup = soup.append(send);
    }
    // The residual `...rest`: reflect the σ-bound variable to its `BoundVar` slot. The AC receiver
    // bound it to the leftover soup (a parallel composition of `@"ac:{op}"!(…)` sends), so
    // appending it here parallel-composes — hence SPLICES — the residual sends into the flat bag.
    if let Some(rest_name) = rest {
        let rest_var = Pattern::Term(PatternTerm::Var(rest_name.clone()));
        let rest_par =
            reflect_term_par_env(&rest_var, vars, k, language_fingerprint, binder_env, Some(def))?;
        soup = soup.append(rest_par);
    }
    Ok(soup)
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
    pattern_binder_or_collection_family(left).or_else(|| pattern_binder_or_collection_family(right))
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
        PatternTerm::Apply { args, .. } => {
            args.iter().find_map(pattern_binder_or_collection_family)
        },
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

/// Build the atomic polyadic-JOIN receiver for a contextual (congruence) rewrite (INV-6):
///
/// ```text
/// for( T_0 <- c(ℓ_0) ; … ; (T_{n-1}, out) <- c(ℓ_{n-1}) ){ out!(⟦K'⟧) }
/// ```
///
/// a single persistent `Receive` with `n` binds — ONE flat σ-slot per premise hole `T_i` on
/// that premise's location channel `c(ℓ_i)` — whose body emits the reduced context `⟦K'⟧`
/// (`context_rhs`) on the dynamic out channel. The `n` reduced holes must ALL arrive for the
/// join to fire (the atomic n-ary rendezvous the tex's Appendix A / `[optimal]` Def 3.1
/// contextual clause demands); the [`contextual_contract_call`] injection delivers them.
///
/// De Bruijn frame (`n + 1` bound vars total: `n` holes + `out`). Each `ReceiveBind` uses
/// LOCAL free-var indices (the reducer numbers a bind's patterns from 0), and the merged
/// binding order is bind-0-first, so hole `i` sits at global level `i` and `out` at global
/// level `n`; the body therefore references hole `i` as `BoundVar(n - i)` and `out` as
/// `BoundVar(0)` — the SAME frame [`sigma_receiver_par`] uses, so `context_rhs` is built by
/// the SHARED [`reflect_term_par`] over the `n` target holes (`BoundVar(rhs_var_index(n,i))`
/// `= BoundVar(n - i)`). The out channel rides the LAST bind (`(T_{n-1}, out)`), keeping the
/// receive an `n`-bind join. For `n = 1` this is byte-identical to
/// `sigma_receiver_par(1, context_rhs, c(ℓ_0))`.
///
/// FV: `formal/rocq/rho_bridge/theories/ContextualAtomicJoinPlugging.v` (atomic n-ary join +
/// plugging-stability, generalizing `LinearCommCorrespondence.v`'s `SameChannelJoin` 2→n).
pub fn contextual_join_receiver_par(context_rhs: Par, premise_channels: &[Par]) -> Par {
    let n = premise_channels.len();
    let free_count = n + 1; // n reduced holes + out
    let all_formals = all_formals_bitvec(free_count);
    let out_channel = bound_formal(free_count, n); // out = BoundVar(0)
    let body = new_send_par(
        out_channel,
        vec![context_rhs],
        false,
        all_formals.clone(),
        false,
        all_formals,
        false,
    );
    let mut binds = Vec::with_capacity(n.max(1));
    for (index, channel) in premise_channels.iter().enumerate() {
        // The last bind also carries the out channel (LOCAL free var 1); each premise bind
        // otherwise carries just its one reduced hole (LOCAL free var 0).
        let is_last = index + 1 == n;
        let (patterns, free_count_bind) = if is_last {
            (vec![new_freevar_par(0, Vec::new()), new_freevar_par(1, Vec::new())], 2)
        } else {
            (vec![new_freevar_par(0, Vec::new())], 1)
        };
        binds.push(ReceiveBind {
            patterns,
            source: Some(channel.clone()),
            remainder: None,
            free_count: free_count_bind,
        });
    }
    let receive = Receive {
        binds,
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: free_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    Par::default().with_receives(vec![receive])
}

/// Build the AC receiver for a HashBag base rewrite `op{L_1..L_k, ...rest} ~> R`: a persistent
/// `for( <ac_bag_pattern(op,k)> , out <- source ){ out!(rhs_par) }` over the AC channel. The
/// connective collection pattern matches the reflected bag carrier ORDER-INDEPENDENTLY (the
/// native `sub_pars` / `MaximumBipartiteMatch`), binding the `k` element σ slots (`FreeVar(0..k-1)`),
/// the residual `rest` (`FreeVar(k)`), and `out` (`FreeVar(k+1)`); the body fires `rhs_par` on
/// `out` (`BoundVar(0)`). `rhs_par` = `⟦R⟧σ` must reference element `i` as `BoundVar(k+1-i)` and
/// `rest` as `BoundVar(1)` (the reverse De Bruijn over the `k+2` bind free vars). Verified end to
/// end by `ac_receiver_fires_the_matched_element_on_the_dynamic_out`.
pub fn ac_sigma_receiver_par(op: &str, k: usize, rhs_par: Par, source: Par) -> Par {
    ac_sigma_receiver_par_with_condition(CollectionType::HashBag, op, k, rhs_par, source, None)
}

/// The number of connective element σ SLOTS an AC receiver of `kind` binds for `k` fixed LHS
/// elements: a `HashMap` binds `2k` slots (one key + one value per entry), every other kind (soup
/// `HashBag`, `ESet`) binds `k`. The residual `rest` is then `FreeVar(slots)` and `out` is
/// `FreeVar(slots + 1)`, so the receiver's `free_count` is `slots + 2`.
pub fn ac_element_slot_count(kind: CollectionType, k: usize) -> usize {
    match kind {
        CollectionType::HashMap => 2 * k,
        _ => k,
    }
}

/// [`ac_sigma_receiver_par`] with an optional NON-LINEAR consistency `Receive.condition` (Stage 4
/// S-AC, AC3): a LINEAR AC rule (`op{x_0, …, x_{k-1}, ...rest}`, all element vars DISTINCT) passes
/// `None` (byte-identical to [`ac_sigma_receiver_par`]); a NON-LINEAR one (`op{x, x, ...rest}` — the
/// `N ≡ N` shape a repeated bare element var expresses) passes the [`ac_nonlinear_condition`] guard
/// `EEq(slot_i, slot_j) ∧ …`, which the reducer evaluates before committing the COMM so the k
/// element slots the connective [`ac_bag_pattern`] binds are picked ONLY when the repeated
/// occurrences are name-equal. The RHS references each repeated var's FIRST occurrence slot
/// (`reflect_term_par`'s first-occurrence resolution), consistent with the guard's canonical slot.
///
/// This reuses the same [`nonlinear_consistency_condition`] machinery as [`comm_receiver_par`] /
/// [`structural_ac_receiver_par`], generalized to the bare-var connective bag pattern — so a
/// non-linear AC rewrite over bare element vars matches ONLY equal picks, closing the latent
/// condition-less gap. Every other formal (rest, out) and the body are the linear receiver's.
pub fn ac_sigma_receiver_par_with_condition(
    kind: CollectionType,
    op: &str,
    k: usize,
    rhs_par: Par,
    source: Par,
    condition: Option<Par>,
) -> Par {
    // The connective pattern binds `slots` element σ vars (`2k` for a `HashMap` key+value, `k`
    // otherwise), then the residual `rest` (`FreeVar(slots)`) and `out` (`FreeVar(slots + 1)`).
    let slots = ac_element_slot_count(kind.clone(), k);
    let free_count = slots + 2; // element slots + rest + out
    let out_channel = bound_formal(free_count, slots + 1); // out = BoundVar(0)
    let body_free = union(rhs_par.locally_free.clone(), create_bit_vector(&[0]));
    let body =
        new_send_par(out_channel, vec![rhs_par], false, body_free.clone(), false, body_free, false);
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![
                ac_collection_pattern(kind, op, k),
                new_freevar_par((slots + 1) as i32, Vec::new()),
            ],
            source: Some(source),
            remainder: None,
            free_count: free_count as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: free_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition,
    };
    Par::default().with_receives(vec![receive])
}

/// The NON-LINEAR consistency `Receive.condition` for a bare-var AC LHS `op{x_0, …, x_{k-1},
/// ...rest}` (Stage 4 S-AC, AC3), or `None` when the LHS is LINEAR (every element var distinct — no
/// guard needed). Groups the `k` element positions by variable name; each group with ≥2 positions
/// is a repeated (non-linear) var whose occurrences must be name-equal, contributing an
/// [`nonlinear_consistency_condition`] `EEq(slot_first, slot_other) ∧ …` over the receiver's `k+2`
/// formals (`ac_bag_pattern` binds element `i` as `FreeVar(i)` → `BoundVar(k+1-i)`). Multiple
/// non-linear groups are conjoined with `EAnd`. This is the AC analogue of the automaton's flat
/// `eq:` consistency join, expressed as the connective receiver's guard.
fn ac_nonlinear_condition(element_vars: &[Ident], free_count: usize) -> Option<Par> {
    // Element positions grouped by variable name (first-occurrence order).
    let mut groups: Vec<(String, Vec<usize>)> = Vec::with_capacity(element_vars.len());
    for (pos, var) in element_vars.iter().enumerate() {
        let name = var.to_string();
        match groups.iter_mut().find(|(existing, _)| *existing == name) {
            Some((_, positions)) => positions.push(pos),
            None => groups.push((name, vec![pos])),
        }
    }
    let mut condition: Option<Par> = None;
    for (_, positions) in &groups {
        if positions.len() < 2 {
            continue;
        }
        let group = nonlinear_consistency_condition(positions, free_count);
        condition = Some(match condition {
            None => group,
            Some(existing) => {
                let union_free = union(existing.locally_free.clone(), group.locally_free.clone());
                let and = Expr {
                    expr_instance: Some(ExprInstance::EAndBody(EAnd {
                        p1: Some(existing),
                        p2: Some(group),
                    })),
                };
                Par {
                    exprs: vec![and],
                    locally_free: union_free,
                    connective_used: false,
                    ..Par::default()
                }
            },
        });
    }
    condition
}

/// Whether `kind` is a BARE-VAR AC operand collection whose linear with-rest LHS
/// `op({x_1, …, x_k, ...rest})` binds one σ var per element — a `HashBag` (process-soup carrier) or a
/// `HashSet` (`ESet` carrier). A `HashMap` is NOT (its entries are `key => value` pairs, not bare
/// vars — a distinct shape), and `Vec`/`PathMap` are not AC. Both [`ac_rule_shape`] and the AC
/// carriers key off this, so the LHS extraction and the connective pattern agree on the kind.
pub(crate) fn is_bare_var_ac_kind(kind: Option<&CollectionType>) -> bool {
    matches!(kind, Some(CollectionType::HashBag | CollectionType::HashSet))
}

/// The shape of a linear with-rest bare-var AC rewrite LHS `op({x_1, …, x_k, ...rest})`: the
/// collection constructor `op`, the `k` linear element variables in first-occurrence order, and
/// the `rest` variable. Returns `None` unless the LHS is a constructor applied to a SINGLE
/// with-rest bare-var AC collection (`HashBag` or `HashSet`, [`is_bare_var_ac_kind`]) whose elements
/// are ALL linear `Var`s.
///
/// The parser leaves a rewrite-LHS collection's `coll_type` as `None` (it is "inferred from the
/// enclosing constructor's grammar"), so the effective kind is the pattern's `coll_type` when
/// set, else `resolved_kind` — resolved from `op`'s declared collection param via
/// [`resolve_ac_collection_type`]. A `HashBag` routes to the process-soup carrier and a `HashSet` to
/// the native `ESet` carrier (Stage 4 S-AC / AC4); a `HashMap` (`key => value` entries) has its own
/// shape and an unresolved kind (`None`) does not match, and a no-rest exact match or a
/// nested/non-linear element returns `None`.
///
/// This is the SINGLE AC-LHS extraction shared by [`ac_rule_receiver`] (which materializes the
/// installed AC receiver) and [`rho_net_ac_injection_sites`] (which surfaces the runtime AC
/// injection site), so both agree byte-for-byte on `op`, the element order, and `rest`.
pub(crate) fn ac_rule_shape(
    left: &Pattern,
    resolved_kind: Option<&CollectionType>,
) -> Option<(String, Vec<Ident>, Ident)> {
    let (op, elements, rest_name) = match left {
        Pattern::Term(PatternTerm::Apply { constructor, args }) => match args.as_slice() {
            [Pattern::Collection { coll_type, elements, rest }]
                if is_bare_var_ac_kind(coll_type.as_ref().or(resolved_kind)) =>
            {
                (constructor.to_string(), elements, rest.clone())
            },
            _ => return None,
        },
        _ => return None,
    };
    // Require an explicit `...rest` (the connective pattern always binds a remainder; a
    // no-rest exact-match rule is a later slice).
    let rest = rest_name?;
    // The k element vars (first-occurrence). Linear (Var) elements only — a nested/non-linear
    // element defers the rule.
    let mut element_vars: Vec<Ident> = Vec::with_capacity(elements.len());
    for element in elements {
        match element {
            Pattern::Term(PatternTerm::Var(name)) => element_vars.push(name.clone()),
            _ => return None,
        }
    }
    Some((op, element_vars, rest))
}

/// Un-skip a `DeferReason::Ac` base rewrite whose LHS is a linear HashBag AC pattern
/// `op{x_1, …, x_k, ...rest} ~> R`: extract the element variables + `rest` (via the shared
/// [`ac_rule_shape`]), reflect the RHS in the AC receiver frame (`reflect_term_par` at `k+1`
/// over the `[x_1..x_k, rest]` σ order — verified by `ac_rhs_reflects_with_the_ac_receiver_frame`),
/// and build the receiver via [`ac_sigma_receiver_par`]. Returns `None` when the LHS is not a
/// with-rest linear HashBag AC pattern (a no-rest exact match, a nested/non-linear element, or a
/// non-HashBag collection — those stay on their existing path, later slices), so the caller keeps
/// them fail-closed.
///
/// The RHS `R` may be a plain term (`Wrap(x)` — a tagged `EList`) OR itself a HashBag bag
/// `op'{e_0, …, ...rest}` (Stage AC2b — a bare process-soup carrier, so a bag-TRANSFORMING AC rule
/// fires as one flat bag). The bag-RHS reflection needs the constructor's declared collection kind
/// when the parser left the RHS collection's `coll_type` as `None`, so `def` is threaded to
/// [`reflect_term_par`] (`Some(def)` from the lowering driver; `None` in unit tests whose RHS is a
/// plain term).
pub fn ac_rule_receiver(
    left: &Pattern,
    right: &Pattern,
    source: Par,
    language_fingerprint: &str,
    resolved_kind: Option<CollectionType>,
    def: Option<&LanguageDef>,
) -> Option<Par> {
    let (op, element_vars, rest) = ac_rule_shape(left, resolved_kind.as_ref())?;
    let k = element_vars.len();
    // The effective operand kind (`HashBag` soup or `HashSet` `ESet`) — the pattern's `coll_type`
    // when the parser set it, else `resolved_kind` (both are `is_bare_var_ac_kind` since
    // `ac_rule_shape` succeeded), defaulting to `HashBag`.
    let kind = ac_effective_bare_var_kind(left, resolved_kind.as_ref());
    // The NON-LINEAR consistency guard for a repeated bare element var (`{x, x, ...rest}` — the
    // `N ≡ N` shape); `None` for a linear LHS (byte-identical to the pre-AC3 receiver). Computed
    // BEFORE `element_vars` is moved into the σ order.
    let condition = ac_nonlinear_condition(&element_vars, k + 2);
    // The σ variable order: the k element vars (first-occurrence), then `rest`.
    let mut vars: Vec<Ident> = element_vars;
    vars.push(rest);
    // The RHS `⟦R⟧σ` in the AC receiver's `k+2`-formal frame (`reflect_term_par` at `k+1`). A
    // collection-VALUED RHS reflects to the kind's carrier (soup / `ESet`) via `def`. A repeated var
    // resolves to its FIRST occurrence slot (matching the guard's canonical slot).
    let rhs = reflect_term_par(right, &vars, k + 1, language_fingerprint, def).ok()?;
    Some(ac_sigma_receiver_par_with_condition(kind, &op, k, rhs, source, condition))
}

/// The effective BARE-VAR AC operand kind of a linear AC rewrite LHS: the pattern collection's own
/// `coll_type` when the parser set it, else `resolved_kind`, defaulting to `HashBag`. Only reached
/// after [`ac_rule_shape`] confirmed [`is_bare_var_ac_kind`], so the result is always `HashBag` or
/// `HashSet`.
pub(crate) fn ac_effective_bare_var_kind(
    left: &Pattern,
    resolved_kind: Option<&CollectionType>,
) -> CollectionType {
    let pattern_kind = match left {
        Pattern::Term(PatternTerm::Apply { args, .. }) => match args.as_slice() {
            [Pattern::Collection { coll_type, .. }] => coll_type.as_ref(),
            _ => None,
        },
        _ => None,
    };
    pattern_kind.or(resolved_kind).cloned().unwrap_or(CollectionType::HashBag)
}

/// Resolve the collection kind a CONSTRUCTOR declares (`op . ps:HashBag(..) |- ..`), keyed on the
/// op label. The parser leaves a rewrite pattern collection's `coll_type` as `None` ("inferred from
/// the enclosing constructor's grammar"), so BOTH the AC LHS un-skip ([`resolve_ac_collection_type`])
/// AND the AC bag-VALUED RHS reflection ([`reflect_hashbag_soup_par`], Stage AC2b) resolve it from
/// `op`'s declared collection parameter in `def.terms` (the type alias is inlined to a
/// `TypeExpr::Collection`). Returns `None` when `op` is not a constructor over a collection
/// parameter — so a non-collection or unknown constructor is never mis-classified as a HashBag.
fn resolve_constructor_collection_type(def: &LanguageDef, op: &str) -> Option<CollectionType> {
    let rule = def.terms.iter().find(|rule| rule.label.to_string() == op)?;
    rule.term_context
        .as_ref()?
        .iter()
        .find_map(|param| match param {
            mettail_ast::grammar::TermParam::Simple {
                ty: mettail_ast::types::TypeExpr::Collection { coll_type, .. },
                ..
            } => Some(coll_type.clone()),
            _ => None,
        })
}

/// Resolve the collection kind the AC rule's constructor declares (`op . ps:HashBag(..) |- ..`) —
/// [`resolve_constructor_collection_type`] keyed on the LHS `Apply`'s constructor. Returns `None`
/// when the LHS is not a constructor application.
fn resolve_ac_collection_type(def: &LanguageDef, left: &Pattern) -> Option<CollectionType> {
    let op = match left {
        Pattern::Term(PatternTerm::Apply { constructor, .. }) => constructor.to_string(),
        _ => return None,
    };
    resolve_constructor_collection_type(def, &op)
}

/// The effective collection kind of a rewrite-pattern collection nested under constructor `op`:
/// the pattern's own `coll_type` when the parser set it, else the kind `op`'s collection parameter
/// declares (via [`resolve_constructor_collection_type`]). This mirrors the LHS
/// `coll_type.as_ref().or(resolved_kind)` precedence in [`ac_rule_shape`], so the AC bag-RHS
/// reflection ([`reflect_hashbag_soup_par`]) agrees with the AC LHS un-skip on the operand kind.
fn resolve_collection_kind(
    def: &LanguageDef,
    constructor: &Ident,
    pattern_kind: Option<&CollectionType>,
) -> Option<CollectionType> {
    pattern_kind
        .cloned()
        .or_else(|| resolve_constructor_collection_type(def, &constructor.to_string()))
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

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Stage 3b: the canonical single-receive Rholang COMMUNICATION rule as a NON-LINEAR AC σ-receiver.
//
//     Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest}) ~> (PPar {(eval cont Q), ...rest})
//
// i.e. `for(y <- N){ cont } | N!(Q)  ~>  cont[Q/y]`, spliced back into the residual bag. This is
// the FIRST rewrite family that COMPOSES, in one atomic COMM on the reducer:
//
//   * HashBag AC over `op` (`PPar`) with k=2 STRUCTURED fixed elements (the `PFor` receive + the
//     `POutput` send) + `...rest` — the order-independent process-soup match (the `ac_bag_pattern`
//     shape, but with structured element patterns instead of bare σ slots);
//   * a NON-LINEAR consistency guard: the shared channel variable `N` occurs in BOTH elements, so
//     each occurrence binds a DISTINCT free σ slot (Rholang rejects a pattern free variable that
//     occurs twice), and a `Receive.condition` `EEq(N_recv, N_send)` — the `where`-clause the
//     f1r3node reducer commits the COMM under only when it evaluates to `GBool(true)` — enforces
//     `N ≡ N`, reject-safe (a mismatched-channel soup leaves the data resting, the
//     `merge_substs → None` analogue). This is Def 4.9's enable-gate / `AcNonLinearConsistency.v`'s
//     `ac_nl_guard`, realized as the AC receiver's condition;
//   * host-computed capture-avoiding substitution `cont[Q/y]` (the `(eval cont Q)` operator IS the
//     substitution — model-b, exactly as the Stage 3c binder path) delivered as the firing's
//     CONTRACTUM at a dedicated σ slot the receiver forwards;
//   * a bag RHS `op{ cont[Q/y], ...rest }` — the receiver body `@"ac:op"!(reduct) | rest` is the
//     Stage AC2b process-soup carrier (`reflect_hashbag_soup_par` shape): the reduct is the one
//     fixed element and the bound `rest` remainder splices the residual sends back flat.
//
// The non-linear channel guard cannot be a repeated pattern variable (`for(@N!(_) & @N!(_) …)` is
// rejected: a free variable may occur at most once in a Rholang pattern), so — exactly as the
// positional set-automaton `eq:` join does (`rho_net_automaton::consistency_guard`) — the two
// occurrences bind distinct slots and the equality is a depth-1-substituted `Receive.condition`.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// One structured fixed element of a Comm rule's AC bag LHS — a constructor applied to bare
/// variables (e.g. `(PFor N cont)`, `(POutput N Q)`). `nonlinear_index` is the position, within
/// `args`, of the shared non-linear channel variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommElement {
    pub constructor: String,
    pub args: Vec<Ident>,
    pub nonlinear_index: usize,
}

/// The recognized shape of the canonical single-receive Rholang COMMUNICATION rule
/// `op{ E0, E1, ...rest } ~> op{ (eval scope arg), ...rest }`: two STRUCTURED constructor elements
/// `E0`/`E1` sharing exactly one NON-LINEAR channel variable `N` (each occurrence a distinct slot),
/// a with-rest remainder, and an RHS whose sole fixed element is a substitution `(eval scope arg)`
/// over LHS variables (the receive continuation `scope` and the sent name `arg`). Returned only for
/// this precise shape; every other structured / non-linear AC rewrite (e.g. Ambient's `OpenRule`,
/// whose RHS is structural, not a substitution) declines and stays on its existing path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommShape {
    pub op: String,
    pub elements: Vec<CommElement>,
    pub rest: Ident,
    pub nonlinear_var: Ident,
    pub scope_var: Ident,
    pub arg_var: Ident,
}

/// Extract `op{ elements, ...rest }` from a constructor applied to a SINGLE with-rest HashBag
/// collection (the `coll_type` precedence mirrors [`ac_rule_shape`]). Returns the op label, the
/// element patterns, and the (optional) rest variable.
fn collection_apply<'a>(
    pattern: &'a Pattern,
    resolved_kind: Option<&CollectionType>,
) -> Option<(String, &'a [Pattern], Option<Ident>)> {
    match pattern {
        Pattern::Term(PatternTerm::Apply { constructor, args }) => match args.as_slice() {
            [Pattern::Collection { coll_type, elements, rest }]
                if coll_type.as_ref().or(resolved_kind) == Some(&CollectionType::HashBag) =>
            {
                Some((constructor.to_string(), elements.as_slice(), rest.clone()))
            },
            _ => None,
        },
        _ => None,
    }
}

/// A structured element `C(v_0, …, v_{m-1})` — a constructor applied to bare variables. Returns
/// `None` for a bare variable element (that is the linear [`ac_rule_shape`] path) or any element
/// whose arguments are not all bare variables (a nested structured element is a later slice).
fn structured_element(pattern: &Pattern) -> Option<CommElement> {
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    let mut vars: Vec<Ident> = Vec::with_capacity(args.len());
    for arg in args {
        match arg {
            Pattern::Term(PatternTerm::Var(name)) => vars.push(name.clone()),
            _ => return None,
        }
    }
    Some(CommElement {
        constructor: constructor.to_string(),
        args: vars,
        nonlinear_index: 0,
    })
}

/// The unique variable shared across ALL elements, each occurrence exactly once per element — the
/// non-linear channel variable `N`. Returns `None` unless exactly one variable is shared by every
/// element and appears exactly once in each (the canonical `{(PFor N …), (POutput N …)}` shape).
fn unique_shared_variable(elements: &[CommElement]) -> Option<Ident> {
    let mut shared: Option<Ident> = None;
    // Candidates: variables of the first element that occur (exactly once) in EVERY element.
    let first = elements.first()?;
    for candidate in &first.args {
        let appears_once_in_all = elements
            .iter()
            .all(|element| element.args.iter().filter(|v| *v == candidate).count() == 1);
        if appears_once_in_all {
            // Reject a SECOND distinct shared variable (ambiguous non-linear guard).
            if shared.replace(candidate.clone()).is_some() {
                return None;
            }
        }
    }
    shared
}

/// The RHS substitution element `(eval scope arg)` — a `MultiSubst`/`Subst` whose scope and single
/// replacement are bare variables. Returns `(scope_var, arg_var)`.
fn subst_element(pattern: &Pattern) -> Option<(Ident, Ident)> {
    let Pattern::Term(term) = pattern else {
        return None;
    };
    let (scope, arg) = match term {
        PatternTerm::MultiSubst { scope, replacements } if replacements.len() == 1 => {
            (scope.as_ref(), &replacements[0])
        },
        PatternTerm::Subst { term, replacement, .. } => (term.as_ref(), replacement.as_ref()),
        _ => return None,
    };
    match (scope, arg) {
        (Pattern::Term(PatternTerm::Var(scope_var)), Pattern::Term(PatternTerm::Var(arg_var))) => {
            Some((scope_var.clone(), arg_var.clone()))
        },
        _ => None,
    }
}

/// Recognize the canonical single-receive Rholang COMMUNICATION rule
/// `op{ E0, E1, ...rest } ~> op{ (eval scope arg), ...rest }` — see [`CommShape`]. Fail-closed on
/// every other shape (a non-HashBag collection, an element that is not a constructor over bare
/// variables, 0 or ≥2 shared variables, or an RHS that is not a single-substitution with-rest bag
/// over the SAME op and rest).
pub(crate) fn comm_rule_shape(
    left: &Pattern,
    right: &Pattern,
    resolved_kind: Option<&CollectionType>,
) -> Option<CommShape> {
    // LHS: op{ E0, E1, ...rest } — a with-rest HashBag with exactly two structured elements.
    let (op, lhs_elements, rest) = collection_apply(left, resolved_kind)?;
    if lhs_elements.len() != 2 {
        return None;
    }
    let rest = rest?;

    let mut elements: Vec<CommElement> = Vec::with_capacity(lhs_elements.len());
    for element in lhs_elements {
        elements.push(structured_element(element)?);
    }

    // The shared non-linear channel variable, and each element's occurrence index of it.
    let nonlinear_var = unique_shared_variable(&elements)?;
    for element in &mut elements {
        element.nonlinear_index = element.args.iter().position(|v| v == &nonlinear_var)?;
    }

    // RHS: op{ (eval scope arg), ...rest } — the SAME op + rest, a single substitution element.
    let (rhs_op, rhs_elements, rhs_rest) = collection_apply(right, resolved_kind)?;
    if rhs_op != op || rhs_elements.len() != 1 || rhs_rest.as_ref() != Some(&rest) {
        return None;
    }
    let (scope_var, arg_var) = subst_element(&rhs_elements[0])?;

    // The substitution's scope + arg must be LHS variables (supplied by the AC match's σ).
    let lhs_vars: HashSet<String> = elements
        .iter()
        .flat_map(|element| element.args.iter())
        .map(|var| var.to_string())
        .collect();
    if !lhs_vars.contains(&scope_var.to_string()) || !lhs_vars.contains(&arg_var.to_string()) {
        return None;
    }

    Some(CommShape {
        op,
        elements,
        rest,
        nonlinear_var,
        scope_var,
        arg_var,
    })
}

/// The Comm receiver's σ-slot frame (a single polyadic `ReceiveBind`, free-var levels): the two
/// structured elements' non-linear channel slots come first (`0` = first element = `N_recv`, `1` =
/// second = `N_send`), then the bag remainder `rest` (`2`), the host-delivered reduct (`3`), and
/// the dynamic out channel (`4`). `free_count = 5`. Body/condition read these back as
/// `BoundVar(free_count - 1 - level)`.
const COMM_FREE_COUNT: usize = 5;

/// The reflected pattern for one structured Comm element `C(v_0, …)`: a tagged `EList`
/// `[ GPrivate(reflect_tag(C)), … ]` whose non-linear-channel position is the free σ slot
/// `FreeVar(nl_level)` and whose every OTHER position is a wildcard `_` (the AC match consumes the
/// whole element structurally, but only the channel — for the guard — and the tag — to route the
/// PFor pattern to the PFor send and the POutput pattern to the POutput send — are read; the
/// continuation / sent-name are supplied host-side via the reduct). Byte-identical in the tag +
/// EList shape to [`reflect_ground_term_par`]'s constructor reflection, so the reflected ground
/// element in the injected soup matches this pattern.
fn comm_element_pattern(element: &CommElement, nl_level: usize, language_fingerprint: &str) -> Par {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
        language_fingerprint,
        &element.constructor,
    ));
    let mut items = Vec::with_capacity(element.args.len() + 1);
    items.push(tag);
    for index in 0..element.args.len() {
        if index == element.nonlinear_index {
            items.push(new_freevar_par(nl_level as i32, Vec::new()));
        } else {
            items.push(new_wildcard_par(Vec::new(), true));
        }
    }
    // A pattern EList carrying free vars / wildcards is connective; its `locally_free` is empty
    // (free vars are pattern binders, not locally-free bound vars).
    new_elist_par(items, Vec::new(), true, None, Vec::new(), true)
}

/// The non-linear consistency `Receive.condition` for a Comm receiver: the conjunction (`EAnd`) of
/// `EEq(BoundVar, BoundVar)` over each repeated variable's occurrence slot pairs — for the
/// canonical single shared channel with two occurrences, exactly one conjunct
/// `EEq(BoundVar(N_recv), BoundVar(N_send))`. Child `i`'s slot at free level `l` is
/// `BoundVar(COMM_FREE_COUNT - 1 - l)` (the receive binds flattened, so body + condition share the
/// reverse De Bruijn frame). Mirrors `rho_net_automaton::consistency_guard`, kept self-contained.
fn comm_consistency_condition(occurrence_levels: &[usize]) -> Par {
    nonlinear_consistency_condition(occurrence_levels, COMM_FREE_COUNT)
}

/// The non-linear consistency `Receive.condition` for a receiver whose flattened receive binds
/// `free_count` slots: the conjunction (`EAnd`) of `EEq(BoundVar, BoundVar)` over each repeated
/// variable's occurrence slot pairs. Child slot at free level `l` is `BoundVar(free_count - 1 - l)`
/// (the receive binds flattened, so body + condition share the reverse De Bruijn frame). Shared by
/// the Comm receiver ([`comm_consistency_condition`], `free_count = COMM_FREE_COUNT`) and the
/// structural-AC receiver ([`structural_ac_receiver_par`]).
fn nonlinear_consistency_condition(occurrence_levels: &[usize], free_count: usize) -> Par {
    let mut conjuncts: Vec<(Par, Vec<usize>)> = Vec::with_capacity(occurrence_levels.len());
    let idx0 = free_count - 1 - occurrence_levels[0];
    for &level in &occurrence_levels[1..] {
        let idxj = free_count - 1 - level;
        let eq = Expr {
            expr_instance: Some(ExprInstance::EEqBody(EEq {
                p1: Some(new_boundvar_par(idx0 as i32, create_bit_vector(&[idx0]), false)),
                p2: Some(new_boundvar_par(idxj as i32, create_bit_vector(&[idxj]), false)),
            })),
        };
        let free = vec![idx0.min(idxj), idx0.max(idxj)];
        conjuncts.push((expr_par_with(eq, &free), free));
    }
    let (mut guard, mut free) = conjuncts
        .first()
        .cloned()
        .expect("a non-linear guard has at least one repeated-occurrence conjunct");
    for (conjunct, conjunct_free) in conjuncts.into_iter().skip(1) {
        let mut union_free = free.clone();
        union_free.extend(conjunct_free);
        union_free.sort_unstable();
        union_free.dedup();
        let and = Expr {
            expr_instance: Some(ExprInstance::EAndBody(EAnd {
                p1: Some(guard),
                p2: Some(conjunct),
            })),
        };
        guard = expr_par_with(and, &union_free);
        free = union_free;
    }
    guard
}

/// A ground `Par` carrying the single expression `instance`, locally-free in `free`. Mirrors
/// `rho_net_automaton::expr_par`.
fn expr_par_with(instance: Expr, free: &[usize]) -> Par {
    Par {
        exprs: vec![instance],
        locally_free: create_bit_vector(free),
        connective_used: false,
        ..Par::default()
    }
}

/// Build the Comm σ-receiver for `op{ E0, E1, ...rest } ~> op{ (eval scope arg), ...rest }`
/// ([`CommShape`]): a persistent
///
/// ```text
/// for( < rest_rem | @"ac:op"!(⟦E0⟧) | @"ac:op"!(⟦E1⟧) >, reduct, out <- source )
///   where ( N_recv == N_send )
///   { out!( @"ac:op"!(reduct) | rest_rem ) }
/// ```
///
/// The connective process-soup pattern (element 0) matches the reflected operand bag carrier
/// ORDER-INDEPENDENTLY (native `sub_pars`/`MaximumBipartiteMatch`), binding the two elements' channel
/// σ slots (`FreeVar(0)`/`FreeVar(1)`) — via the structured [`comm_element_pattern`]s, whose tags
/// route each pattern to its like-tagged send — and the residual soup to the remainder `rest`
/// (`FreeVar(2)`). The `reduct` (`FreeVar(3)`) is the host-computed contractum `cont[Q/y]`; `out`
/// (`FreeVar(4)`) is the dynamic out channel. The `condition` fires the COMM only when the two
/// channel slots are name-equal ([`comm_consistency_condition`]); the body emits the bag RHS
/// `@"ac:op"!(reduct) | rest` on `out`.
fn comm_receiver_par(shape: &CommShape, source: Par, language_fingerprint: &str) -> Par {
    let element_channel = format!("ac:{}", shape.op);
    let rest_level = shape.elements.len(); // 2
    let reduct_level = rest_level + 1; // 3
    let out_level = reduct_level + 1; // 4
    debug_assert_eq!(out_level + 1, COMM_FREE_COUNT);

    // Element 0 of the receive bind: the structured with-rest process-soup pattern.
    let mut bag_pattern = new_freevar_par(rest_level as i32, Vec::new()); // the `rest` remainder
    let mut occurrence_levels = Vec::with_capacity(shape.elements.len());
    for (nl_level, element) in shape.elements.iter().enumerate() {
        occurrence_levels.push(nl_level);
        let element_pattern = comm_element_pattern(element, nl_level, language_fingerprint);
        let send_pattern = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![element_pattern],
            false,
            Vec::new(),
            true,
            Vec::new(),
            true,
        );
        bag_pattern = bag_pattern.append(send_pattern);
    }

    // The non-linear consistency guard `EEq(N_recv, N_send)`.
    let condition = comm_consistency_condition(&occurrence_levels);

    // Body: `out!( @"ac:op"!(reduct) | rest )`.
    let reduct_bv_index = COMM_FREE_COUNT - 1 - reduct_level; // 1
    let rest_bv_index = COMM_FREE_COUNT - 1 - rest_level; // 2
    let out_bv_index = COMM_FREE_COUNT - 1 - out_level; // 0
    let reduct_free = create_bit_vector(&[reduct_bv_index]);
    let reduct_send = new_send_par(
        new_gstring_par(element_channel.clone(), Vec::new(), false),
        vec![new_boundvar_par(reduct_bv_index as i32, reduct_free.clone(), false)],
        false,
        reduct_free.clone(),
        false,
        reduct_free.clone(),
        false,
    );
    let rest_bv =
        new_boundvar_par(rest_bv_index as i32, create_bit_vector(&[rest_bv_index]), false);
    let body_soup = reduct_send.append(rest_bv); // `@"ac:op"!(reduct) | rest`
    let body_free = union(body_soup.locally_free.clone(), create_bit_vector(&[out_bv_index]));
    let body = new_send_par(
        new_boundvar_par(out_bv_index as i32, create_bit_vector(&[out_bv_index]), false),
        vec![body_soup],
        false,
        body_free.clone(),
        false,
        body_free,
        false,
    );

    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![
                bag_pattern,
                new_freevar_par(reduct_level as i32, Vec::new()),
                new_freevar_par(out_level as i32, Vec::new()),
            ],
            source: Some(source),
            remainder: None,
            free_count: COMM_FREE_COUNT as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: COMM_FREE_COUNT as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: Some(condition),
    };
    Par::default().with_receives(vec![receive])
}

/// Un-skip a Comm-shaped base rewrite to its non-linear AC σ-receiver ([`comm_receiver_par`]),
/// on the rule's OWN trace channel `source` (the channel the Comm injection targets — accept-triad
/// coherence by symmetric derivation, exactly as [`ac_rule_receiver`]). Returns `None` when the
/// rewrite is not the canonical single-receive Comm shape ([`comm_rule_shape`]), so the caller keeps
/// it fail-closed.
pub fn comm_rule_receiver(
    left: &Pattern,
    right: &Pattern,
    source: Par,
    language_fingerprint: &str,
    resolved_kind: Option<CollectionType>,
) -> Option<Par> {
    let shape = comm_rule_shape(left, right, resolved_kind.as_ref())?;
    Some(comm_receiver_par(&shape, source, language_fingerprint))
}

/// The Comm injection `call` for an un-skipped Comm rewrite: `channel!(⟦whole_bag⟧, ⟦reduct⟧, @out)`,
/// where `⟦whole_bag⟧` is the operand bag's process-soup carrier ([`reflect_ground_term_par`] routes
/// a HashBag to the soup) and `⟦reduct⟧` is the host-computed contractum `cont[Q/y]`. This is the
/// exact 3-value message the Comm receiver ([`comm_receiver_par`]) consumes: the connective bag
/// pattern matches the soup (binding the two channel slots + the remainder and enforcing the
/// non-linear guard), the reduct fills the dedicated slot, and the out formal binds `@out`.
/// `channel` MUST be the Comm receiver's SOURCE (the rule's trace channel), so the accept triad
/// (receiver source ≡ injection channel) holds by symmetric derivation, exactly as
/// [`ac_contract_call`].
pub fn comm_contract_call(
    channel_name: &str,
    whole_bag: &GroundTerm,
    reduct: &GroundTerm,
    fingerprint: &str,
    out_channel: &str,
) -> Par {
    let soup = reflect_ground_term_par(whole_bag, fingerprint);
    let reduct_par = reflect_ground_term_par(reduct, fingerprint);
    new_send_par(
        new_gstring_par(channel_name.to_string(), Vec::new(), false),
        vec![soup, reduct_par, new_gstring_par(out_channel.to_string(), Vec::new(), false)],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// One Comm-rewrite σ-injection site derived from a `LanguageDef` (Stage 3b): the canonical
/// single-receive Rholang COMMUNICATION rule's bare label, its Comm σ-receiver SOURCE channel, the
/// HashBag operand constructor `op`, the two structured elements' constructors (in LHS order), the
/// shared non-linear channel variable, the `rest` variable, and the RHS substitution's scope/arg
/// variables.
///
/// The Comm firing analogue of [`RhoNetAcInjectionSite`]. A Comm σ-injection reconstructs the whole
/// operand bag from the firing's σ and the host-computed reduct `cont[Q/y]`, reflects them, and
/// sends `channel!(⟦bag⟧, ⟦reduct⟧, @out)` via [`comm_contract_call`], where the installed
/// [`comm_receiver_par`] consumes the soup (enforcing `N ≡ N`) and emits the bag RHS. Only rewrites
/// that lowered to a [`RhoNetLoweredRule::CommRewrite`] are surfaced, so a site is always
/// executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetCommInjectionSite {
    /// The bare source rewrite label (the Comm receiver rule's label, e.g. `Comm`).
    pub rule_label: String,
    /// The Comm receiver SOURCE channel (`RhoNetRule::input_channels.first()`) — the SAME channel
    /// the receiver rests on, so the accept triad (receiver source ≡ injection channel) holds by
    /// symmetric derivation (`comm_contract_call`'s coherence contract).
    pub channel: String,
    /// The HashBag operand constructor (`op` in `op{…}`, e.g. `PPar`). Both the receiver's element
    /// pattern channel `ac:{op}` and the reflected carrier's send channel derive from this.
    pub op: String,
    /// The two structured elements' constructors, in LHS order (e.g. `["PFor", "POutput"]`).
    pub element_constructors: Vec<String>,
    /// Each structured element's argument variables, in LHS order — PARALLEL to
    /// [`element_constructors`](Self::element_constructors) (e.g. `[["N", "cont"], ["N", "Q"]]`).
    /// The Comm σ-injection rebuilds each operand-bag element `C(σ[a_0], …)` from these slots, so
    /// the reflected soup carries the tags + channels the installed receiver's element patterns
    /// route on.
    pub element_arg_vars: Vec<Vec<String>>,
    /// The shared NON-LINEAR channel variable the two elements enforce equal (`N`).
    pub nonlinear_var: String,
    /// The `rest` variable the LHS binds to the residual bag.
    pub rest_var: String,
    /// The RHS substitution's scope variable (the receive continuation `cont`).
    pub scope_var: String,
    /// The RHS substitution's argument variable (the sent name `Q`).
    pub arg_var: String,
}

/// Derive every Comm-rewrite σ-injection site for a language — the sites a Comm σ-injection targets.
///
/// Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the Comm receivers are compiled from, keeps
/// only the rewrites that un-skipped to a [`RhoNetLoweredRule::CommRewrite`] receiver, and reports
/// each one's bare rule label, source channel, and Comm shape (extracted through the SAME
/// [`comm_rule_shape`] the receiver materialized from, so the injection agrees with the receiver on
/// `op`/elements/`rest`/scope/arg). The Comm firing analogue of [`rho_net_ac_injection_sites`].
pub fn rho_net_comm_injection_sites(def: &LanguageDef) -> Vec<RhoNetCommInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::CommRewrite { rule_id, .. } = lowered_rule else {
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
        // A `CommRewrite` lowered iff `comm_rule_shape` succeeded under the resolved kind, so this
        // cannot fail; a defensive `continue` keeps the derivation total.
        let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
        let Some(shape) = comm_rule_shape(&rewrite.left, &rewrite.right, resolved_kind.as_ref())
        else {
            continue;
        };
        sites.push(RhoNetCommInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            op: shape.op,
            element_constructors: shape
                .elements
                .iter()
                .map(|element| element.constructor.clone())
                .collect(),
            element_arg_vars: shape
                .elements
                .iter()
                .map(|element| element.args.iter().map(|arg| arg.to_string()).collect())
                .collect(),
            nonlinear_var: shape.nonlinear_var.to_string(),
            rest_var: shape.rest.to_string(),
            scope_var: shape.scope_var.to_string(),
            arg_var: shape.arg_var.to_string(),
        });
    }
    sites
}

// ─── Stage 3d: the STRUCTURAL non-linear AC rewrite (Ambient `OpenRule`) ────────────────────────

/// The recognized shape of a STRUCTURAL non-linear AC rewrite
/// `op{ E0, …, E_{k-1}, ...rest } ~> op{ r0, …, r_{m-1}, ...rest }`: `k ≥ 2` STRUCTURED constructor
/// elements sharing exactly one NON-LINEAR channel variable `N` (each occurrence a distinct slot), a
/// with-rest remainder, and an RHS whose fixed elements are ALL bare LHS-element argument variables
/// (a PURE structural restructuring — NO substitution). Ambient's `OpenRule`
/// `{(open N P), N[Q], ...rest} ~> {P, Q, ...rest}` is `k = 2` (`open`, `amb`), `m = 2` (`P`, `Q`).
/// Returned only for this precise shape; a Comm-shaped rewrite (RHS is a `(eval scope arg)`
/// substitution) or a nested-element rewrite (Ambient's `InRule`/`OutRule`) declines and stays on
/// its existing path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructuralAcShape {
    pub op: String,
    pub elements: Vec<CommElement>,
    pub rest: Ident,
    pub nonlinear_var: Ident,
    /// The RHS fixed element variables, in RHS order — each a bare argument variable of some LHS
    /// element (recovered directly from the firing's σ, since the reduct is structural, never
    /// host-computed). For `OpenRule`, `[P, Q]`.
    pub reduct_vars: Vec<Ident>,
}

/// The RHS fixed elements of a structural AC rewrite — each MUST be a bare `Var`. Returns the
/// variable list, or `None` if any element is a substitution / constructor application / collection
/// (a Comm or nested rewrite, not a structural restructuring).
fn structural_reduct_vars(elements: &[Pattern]) -> Option<Vec<Ident>> {
    let mut vars: Vec<Ident> = Vec::with_capacity(elements.len());
    for element in elements {
        match element {
            Pattern::Term(PatternTerm::Var(name)) => vars.push(name.clone()),
            _ => return None,
        }
    }
    Some(vars)
}

/// Recognize a STRUCTURAL non-linear AC rewrite `op{ E0, …, ...rest } ~> op{ r0, …, ...rest }` — see
/// [`StructuralAcShape`]. Fail-closed on every other shape (a non-HashBag collection, an element
/// that is not a constructor over bare variables, 0/≥2 shared variables, an RHS that is not a
/// with-rest bag over the SAME op and rest, an RHS with a non-bare-variable fixed element — the Comm
/// substitution case — or an RHS reduct variable that is not an LHS-element argument).
pub(crate) fn structural_ac_rule_shape(
    left: &Pattern,
    right: &Pattern,
    resolved_kind: Option<&CollectionType>,
) -> Option<StructuralAcShape> {
    // LHS: op{ E0, …, ...rest } — a with-rest HashBag with ≥2 structured elements.
    let (op, lhs_elements, rest) = collection_apply(left, resolved_kind)?;
    if lhs_elements.len() < 2 {
        return None;
    }
    let rest = rest?;

    let mut elements: Vec<CommElement> = Vec::with_capacity(lhs_elements.len());
    for element in lhs_elements {
        elements.push(structured_element(element)?);
    }

    // The shared non-linear channel variable, and each element's occurrence index of it.
    let nonlinear_var = unique_shared_variable(&elements)?;
    for element in &mut elements {
        element.nonlinear_index = element.args.iter().position(|v| v == &nonlinear_var)?;
    }

    // RHS: op{ r0, …, ...rest } — the SAME op + rest, all-bare-variable fixed elements.
    let (rhs_op, rhs_elements, rhs_rest) = collection_apply(right, resolved_kind)?;
    if rhs_op != op || rhs_elements.is_empty() || rhs_rest.as_ref() != Some(&rest) {
        return None;
    }
    let reduct_vars = structural_reduct_vars(rhs_elements)?;

    // Every reduct variable must be a bare argument of some LHS element (supplied by the AC match's
    // σ). This rejects an RHS that reintroduces a fresh variable the σ cannot supply.
    let lhs_vars: HashSet<String> = elements
        .iter()
        .flat_map(|element| element.args.iter())
        .map(|var| var.to_string())
        .collect();
    if !reduct_vars
        .iter()
        .all(|v| lhs_vars.contains(&v.to_string()))
    {
        return None;
    }

    Some(StructuralAcShape {
        op,
        elements,
        rest,
        nonlinear_var,
        reduct_vars,
    })
}

/// Build the structural-AC σ-receiver for `op{ E0, …, ...rest } ~> op{ r0, …, ...rest }`
/// ([`StructuralAcShape`]): a persistent
///
/// ```text
/// for( < rest_rem | @"ac:op"!(⟦E0⟧) | … | @"ac:op"!(⟦E_{k-1}⟧) >, r0, …, r_{m-1}, out <- source )
///   where ( N_0 == N_1 == … )
///   { out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | rest_rem ) }
/// ```
///
/// The connective process-soup pattern (element 0) matches the reflected operand bag carrier
/// ORDER-INDEPENDENTLY (native `sub_pars`/`MaximumBipartiteMatch`), binding each structured element's
/// channel σ slot (`FreeVar(i)`) — via the tag-routed [`comm_element_pattern`], whose every
/// non-channel arg is a wildcard (the reduct elements are delivered host-side, exactly as the Comm
/// receiver) — and the residual soup to the remainder `rest` (`FreeVar(k)`). The `m` reduct slots
/// (`FreeVar(k+1..k+1+m)`) carry the σ-delivered RHS elements; `out` (`FreeVar(k+1+m)`) is the
/// dynamic out channel. The `condition` fires the COMM only when all channel slots are name-equal
/// ([`nonlinear_consistency_condition`]); the body splices the `m` reduct elements with `rest` on
/// `out`. This is the [`comm_receiver_par`] mechanism generalized from ONE host-computed reduct to
/// `m` structural (σ-delivered) reducts.
fn structural_ac_receiver_par(
    shape: &StructuralAcShape,
    source: Par,
    language_fingerprint: &str,
) -> Par {
    let element_channel = format!("ac:{}", shape.op);
    let k = shape.elements.len();
    let m = shape.reduct_vars.len();
    let rest_level = k;
    let first_reduct_level = k + 1;
    let out_level = k + 1 + m;
    let free_count = out_level + 1;

    // Element 0 of the receive bind: the structured with-rest process-soup pattern (channel slots
    // `FreeVar(0..k)`, wildcards elsewhere; the `rest` remainder is `FreeVar(k)`).
    let mut bag_pattern = new_freevar_par(rest_level as i32, Vec::new());
    let mut occurrence_levels = Vec::with_capacity(k);
    for (nl_level, element) in shape.elements.iter().enumerate() {
        occurrence_levels.push(nl_level);
        let element_pattern = comm_element_pattern(element, nl_level, language_fingerprint);
        let send_pattern = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![element_pattern],
            false,
            Vec::new(),
            true,
            Vec::new(),
            true,
        );
        bag_pattern = bag_pattern.append(send_pattern);
    }

    // The non-linear consistency guard `EEq(N_0, N_1) ∧ …`.
    let condition = nonlinear_consistency_condition(&occurrence_levels, free_count);

    // Body: `out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | rest )`.
    let rest_bv_index = free_count - 1 - rest_level;
    let out_bv_index = free_count - 1 - out_level; // 0
    let mut body_soup: Option<Par> = None;
    for j in 0..m {
        let reduct_level = first_reduct_level + j;
        let reduct_bv_index = free_count - 1 - reduct_level;
        let reduct_free = create_bit_vector(&[reduct_bv_index]);
        let reduct_send = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![new_boundvar_par(reduct_bv_index as i32, reduct_free.clone(), false)],
            false,
            reduct_free.clone(),
            false,
            reduct_free,
            false,
        );
        body_soup = Some(match body_soup {
            None => reduct_send,
            Some(soup) => soup.append(reduct_send),
        });
    }
    let rest_bv =
        new_boundvar_par(rest_bv_index as i32, create_bit_vector(&[rest_bv_index]), false);
    // `m ≥ 1` (a structural AC rewrite has ≥1 RHS element), so `body_soup` is always `Some`.
    let body_soup = match body_soup {
        Some(soup) => soup.append(rest_bv),
        None => rest_bv,
    };
    let body_free = union(body_soup.locally_free.clone(), create_bit_vector(&[out_bv_index]));
    let body = new_send_par(
        new_boundvar_par(out_bv_index as i32, create_bit_vector(&[out_bv_index]), false),
        vec![body_soup],
        false,
        body_free.clone(),
        false,
        body_free,
        false,
    );

    // Receive-bind patterns: [bag_pattern, FreeVar(reduct_0), …, FreeVar(reduct_{m-1}), FreeVar(out)].
    let mut patterns = Vec::with_capacity(m + 2);
    patterns.push(bag_pattern);
    for j in 0..m {
        patterns.push(new_freevar_par((first_reduct_level + j) as i32, Vec::new()));
    }
    patterns.push(new_freevar_par(out_level as i32, Vec::new()));

    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns,
            source: Some(source),
            remainder: None,
            free_count: free_count as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: free_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: Some(condition),
    };
    Par::default().with_receives(vec![receive])
}

/// Un-skip a structural-AC-shaped base rewrite to its non-linear AC σ-receiver
/// ([`structural_ac_receiver_par`]), on the rule's OWN trace channel `source` (the channel the
/// structural-AC injection targets — accept-triad coherence by symmetric derivation, exactly as
/// [`comm_rule_receiver`]). Returns `None` when the rewrite is not a structural non-linear AC shape
/// ([`structural_ac_rule_shape`]), so the caller keeps it fail-closed.
pub fn structural_ac_rule_receiver(
    left: &Pattern,
    right: &Pattern,
    source: Par,
    language_fingerprint: &str,
    resolved_kind: Option<CollectionType>,
) -> Option<Par> {
    let shape = structural_ac_rule_shape(left, right, resolved_kind.as_ref())?;
    Some(structural_ac_receiver_par(&shape, source, language_fingerprint))
}

/// The structural-AC injection `call` for an un-skipped structural-AC rewrite:
/// `channel!(⟦whole_bag⟧, ⟦r0⟧, …, ⟦r_{m-1}⟧, @out)`, where `⟦whole_bag⟧` is the operand bag's
/// process-soup carrier ([`reflect_ground_term_par`] routes a HashBag to the soup) and each `⟦r_j⟧`
/// is a structural reduct element recovered DIRECTLY from the firing's σ (an LHS-element argument —
/// there is no host-computed contractum). This is the exact `(m + 2)`-value message the structural-AC
/// receiver ([`structural_ac_receiver_par`]) consumes: the connective bag pattern matches the soup
/// (binding the channel slots + the remainder and enforcing the non-linear guard), the `m` reduct
/// values fill the dedicated slots, and the out formal binds `@out`. `channel` MUST be the receiver's
/// SOURCE (the rule's trace channel), so the accept triad holds by symmetric derivation, exactly as
/// [`comm_contract_call`].
pub fn structural_ac_contract_call(
    channel_name: &str,
    whole_bag: &GroundTerm,
    reducts: &[GroundTerm],
    fingerprint: &str,
    out_channel: &str,
) -> Par {
    let mut values = Vec::with_capacity(reducts.len() + 2);
    values.push(reflect_ground_term_par(whole_bag, fingerprint));
    for reduct in reducts {
        values.push(reflect_ground_term_par(reduct, fingerprint));
    }
    values.push(new_gstring_par(out_channel.to_string(), Vec::new(), false));
    new_send_par(
        new_gstring_par(channel_name.to_string(), Vec::new(), false),
        values,
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// One structural-AC-rewrite σ-injection site derived from a `LanguageDef` (Stage 3d): the
/// structural non-linear AC rule's bare label, its σ-receiver SOURCE channel, the HashBag operand
/// constructor `op`, the `k` structured elements' constructors + argument variables (in LHS order),
/// the shared non-linear channel variable, the `rest` variable, and the `m` RHS reduct variables
/// (each an LHS-element argument the σ supplies).
///
/// The structural-AC firing analogue of [`RhoNetCommInjectionSite`]. A structural-AC σ-injection
/// reconstructs the whole operand bag from the firing's σ and recovers each reduct element `r_j`
/// directly from σ (no contractum), reflects them, and sends
/// `channel!(⟦bag⟧, ⟦r0⟧, …, @out)` via [`structural_ac_contract_call`], where the installed
/// [`structural_ac_receiver_par`] consumes the soup (enforcing `N ≡ N`) and splices the reduct
/// elements with `rest`. Only rewrites that lowered to a [`RhoNetLoweredRule::StructuralAcRewrite`]
/// are surfaced, so a site is always executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetStructuralAcInjectionSite {
    /// The bare source rewrite label (the receiver rule's label, e.g. `OpenRule`).
    pub rule_label: String,
    /// The σ-receiver SOURCE channel (`RhoNetRule::input_channels.first()`) — the SAME channel the
    /// receiver rests on, so the accept triad holds by symmetric derivation.
    pub channel: String,
    /// The HashBag operand constructor (`op` in `op{…}`, e.g. `PPar`).
    pub op: String,
    /// The `k` structured elements' constructors, in LHS order (e.g. `["POpen", "PAmb"]`).
    pub element_constructors: Vec<String>,
    /// Each structured element's argument variables, in LHS order — PARALLEL to
    /// [`element_constructors`](Self::element_constructors) (e.g. `[["N", "P"], ["N", "Q"]]`). The
    /// σ-injection rebuilds each operand-bag element `C(σ[a_0], …)` from these slots.
    pub element_arg_vars: Vec<Vec<String>>,
    /// The shared NON-LINEAR channel variable the elements enforce equal (`N`).
    pub nonlinear_var: String,
    /// The `rest` variable the LHS binds to the residual bag.
    pub rest_var: String,
    /// The `m` RHS reduct variables, in RHS order (each an LHS-element argument — e.g. `["P", "Q"]`).
    /// The σ-injection delivers `σ[r_j]` as the `j`-th reduct value.
    pub reduct_vars: Vec<String>,
}

/// Derive every structural-AC-rewrite σ-injection site for a language — the sites a structural-AC
/// σ-injection targets. Builds the same [`RhoNetProgram`] + [`RhoNetLowered`] the receivers are
/// compiled from, keeps only the rewrites that un-skipped to a
/// [`RhoNetLoweredRule::StructuralAcRewrite`] receiver, and reports each one's bare rule label,
/// source channel, and structural-AC shape (extracted through the SAME [`structural_ac_rule_shape`]
/// the receiver materialized from). The structural-AC firing analogue of
/// [`rho_net_comm_injection_sites`].
pub fn rho_net_structural_ac_injection_sites(
    def: &LanguageDef,
) -> Vec<RhoNetStructuralAcInjectionSite> {
    let lowering = crate::lower::lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);

    let rule_by_id: HashMap<&str, &RhoNetRule> = program
        .rules
        .iter()
        .map(|rule| (rule.id.as_str(), rule))
        .collect();
    let rewrite_by_id: HashMap<String, &RewriteRule> = def
        .rewrites
        .iter()
        .enumerate()
        .map(|(index, rewrite)| (rule_id_rewrite(index, &rewrite.name.to_string()), rewrite))
        .collect();

    let mut sites = Vec::new();
    for lowered_rule in lowered.rules() {
        let RhoNetLoweredRule::StructuralAcRewrite { rule_id, .. } = lowered_rule else {
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
        // A `StructuralAcRewrite` lowered iff `structural_ac_rule_shape` succeeded under the
        // resolved kind, so this cannot fail; a defensive `continue` keeps the derivation total.
        let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
        let Some(shape) =
            structural_ac_rule_shape(&rewrite.left, &rewrite.right, resolved_kind.as_ref())
        else {
            continue;
        };
        sites.push(RhoNetStructuralAcInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            op: shape.op,
            element_constructors: shape
                .elements
                .iter()
                .map(|element| element.constructor.clone())
                .collect(),
            element_arg_vars: shape
                .elements
                .iter()
                .map(|element| element.args.iter().map(|arg| arg.to_string()).collect())
                .collect(),
            nonlinear_var: shape.nonlinear_var.to_string(),
            rest_var: shape.rest.to_string(),
            reduct_vars: shape.reduct_vars.iter().map(|v| v.to_string()).collect(),
        });
    }
    sites
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

    /// The `loc:` head-tag sends of a spread (one per node) — the tag-dispatch surface the
    /// automaton descends. The M-collapse `col:`/`cap:` collapse sends/folds are ADDITIONAL and
    /// checked separately in [`assert_spread_collapses`].
    fn loc_head_tag_sends(spread: &Par) -> usize {
        spread
            .sends
            .iter()
            .filter(|send| {
                send.chan
                    .as_ref()
                    .and_then(gstring_value)
                    .is_some_and(|channel| channel.starts_with("loc:"))
            })
            .count()
    }

    /// INV-10 witness: the spread encodes EXACTLY the term — one `loc:` head-tag send per
    /// node, on the derived location channel, carrying the shared-`reflect_tag`-ABI head tag
    /// (byte-identical to `reflect_ground_term_par`'s tag); and it is ν-free (no `New`, INV-7).
    /// The spread ALSO carries the M-collapse `col:`/`cap:` fold (leaf sends + internal collapse
    /// receivers), so it is no longer sends-only — but it stays Match/Bundle-free.
    fn assert_spread_encodes(term: &GroundTerm, fingerprint: &str, root: &str) {
        let spread = spread_term_par(term, fingerprint, root);
        let mut expected = Vec::new();
        expected_spread_nodes(term, &spread_root_location(root), &mut expected);

        assert_eq!(loc_head_tag_sends(&spread), expected.len(), "one loc: head-tag send per node");
        assert!(spread.news.is_empty(), "ν-free spread: no New (INV-7)");
        assert!(
            spread.matches.is_empty() && spread.bundles.is_empty(),
            "no Match/Bundle in a spread"
        );

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

    /// The `⟦subtree⟧` value a Var-leaf state would capture at each spread node's `cap:`
    /// channel MUST be byte-identical to `reflect_ground_term_par` over that subtree — the
    /// M-collapse fold IS the Rho realization of the host reflector. A leaf's `cap:` send is a
    /// ground `EList[tag]`; an internal node's `cap:` value is assembled by a collapse receiver,
    /// so we assert the leaf sends directly and that every internal node carries a fold.
    fn assert_spread_collapses(term: &GroundTerm, fingerprint: &str, root: &str) {
        fn walk(term: &GroundTerm, fingerprint: &str, capture: &str, spread: &Par) {
            let capture_channel = new_gstring_par(capture.to_string(), Vec::new(), false);
            if term.children.is_empty() {
                // Leaf: a ground `cap:ℓ!(⟦leaf⟧)` send equals reflect_ground_term_par(leaf).
                let collapsed = reflect_ground_term_par(term, fingerprint);
                assert!(
                    spread.sends.iter().any(|send| {
                        send.chan.as_ref() == Some(&capture_channel)
                            && send.data == vec![collapsed.clone()]
                    }),
                    "leaf `{}` must publish ⟦leaf⟧ on its capture channel `{capture}`",
                    term.constructor,
                );
            }
            for (index, child) in term.children.iter().enumerate() {
                let child_capture = spread_child_location(capture, &term.constructor, index);
                walk(child, fingerprint, &child_capture, spread);
            }
        }
        let spread = spread_term_par(term, fingerprint, root);
        walk(term, fingerprint, &collapse_capture_location(root), &spread);
    }

    #[test]
    fn spread_encodes_a_flat_application() {
        // Swap(A, B): the root plus two nullary leaves on their derived channels.
        let term = ground("Swap", vec![ground("A", Vec::new()), ground("B", Vec::new())]);
        assert_spread_encodes(&term, "testfp", "site0");
        assert_spread_collapses(&term, "testfp", "site0");
        let spread = spread_term_par(&term, "testfp", "site0");
        let loc_channels: std::collections::BTreeSet<String> = spread
            .sends
            .iter()
            .filter_map(|s| s.chan.as_ref())
            .filter_map(gstring_value)
            .filter(|c| c.starts_with("loc:"))
            .collect();
        let want: std::collections::BTreeSet<String> =
            ["loc:site0", "loc:site0/Swap.0", "loc:site0/Swap.1"]
                .into_iter()
                .map(String::from)
                .collect();
        assert_eq!(loc_channels, want, "the exact derived location channels");
        // The two leaves publish their collapse values on the derived `cap:` channels.
        let cap_channels: std::collections::BTreeSet<String> = spread
            .sends
            .iter()
            .filter_map(|s| s.chan.as_ref())
            .filter_map(gstring_value)
            .filter(|c| c.starts_with("cap:"))
            .collect();
        let want_cap: std::collections::BTreeSet<String> = ["cap:site0/Swap.0", "cap:site0/Swap.1"]
            .into_iter()
            .map(String::from)
            .collect();
        assert_eq!(cap_channels, want_cap, "the leaves' capture channels");
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
        assert_spread_collapses(&term, "testfp", "site0");
    }

    #[test]
    fn spread_leaf_head_tag_equals_collapsed_reflection_abi() {
        // A nullary spread publishes the head tag on `loc:` (for dispatch) AND the collapsed
        // ⟦leaf⟧ = EList[tag] on `col:`/`cap:` — the shared reflect_tag ABI, one dual of the other.
        let leaf = ground("A", Vec::new());
        let spread = spread_term_par(&leaf, "testfp", "site0");
        let expected_tag = GPrivateBuilder::new_par_from_string(reflect_tag("testfp", "A"));
        // The `loc:` head-tag send carries the tag ALONE.
        let loc_channel = new_gstring_par("loc:site0".to_string(), Vec::new(), false);
        let loc_send = spread
            .sends
            .iter()
            .find(|s| s.chan.as_ref() == Some(&loc_channel))
            .expect("the leaf publishes its head tag on loc:site0");
        assert_eq!(
            loc_send.data,
            vec![expected_tag.clone()],
            "loc: head tag is the shared-ABI tag"
        );
        // The `cap:` collapse send carries ⟦leaf⟧ = EList[tag] = reflect_ground_term_par(leaf).
        let cap_channel = new_gstring_par("cap:site0".to_string(), Vec::new(), false);
        let cap_send = spread
            .sends
            .iter()
            .find(|s| s.chan.as_ref() == Some(&cap_channel))
            .expect("the leaf publishes its collapse value on cap:site0");
        assert_eq!(
            cap_send.data,
            vec![reflect_ground_term_par(&leaf, "testfp")],
            "cap: collapse value is ⟦leaf⟧ (byte-identical to reflect_ground_term_par)"
        );
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
                    (inner.clone(), inner).prop_map(|(l, r)| GroundTerm::new("Pair", vec![l, r])),
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

    // A HashBag language: `PPar` is a constructor over a HashBag operand. The AC un-skip must
    // resolve `PPar`'s collection kind from THIS declaration even though the parser leaves a
    // rewrite-LHS collection's `coll_type` as `None`.
    const AC_DEMO_FRAGMENT: &str = r##"
        name: AcDemoFrag,
        types {
            ![i32] as Int
            ![mettail_runtime::HashBag<Int>] as Bag {
                open_parts: ["#{"],
                close_parts: ["}#"],
                sep: "|",
            }
        }
        terms {
            Wrap . x:Int |- "wrap" "(" x ")" : Int ;
            PPar . ps:HashBag(Int) |- "#{" ps.*sep("|") "}#" : Int ;
        }
    "##;

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
    fn lower_single_rewrite(rewrite: RewriteRule) -> (RhoNetLoweredRule, Vec<RhoNetLoweringError>) {
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
        match par
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        {
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

        // D3 (fold-vs-equation): a BARE (non-`fold`) scalar op is NOT directed compute, so it
        // surfaces NO native-fold FIRING site — its scalar contract is the Model-T artifact only.
        assert!(
            rho_net_native_fold_injection_sites(&def).is_empty(),
            "a bare (non-fold) scalar op must surface no native-fold firing site"
        );
    }

    /// A pure scalar fragment whose `+` op is a `fold` HOL term (`![a + b] fold`) — the Stage 3f
    /// firing shape (mirrors `NativeFoldDemo`), contrasted against the BARE `SCALAR_FRAGMENT`.
    const NATIVE_FOLD_FRAGMENT: &str = r#"
        name: RhoNetLowerNativeFoldFrag,
        types {
            ![i64] as Int
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        }
    "#;

    /// D3 (Stage 3f) — the FIRING side of the fold-vs-equation criterion: a COMPUTING native scalar
    /// `fold` (`AddInt ~> a + b`) lowers to a flat FIRING DISPATCH RECEIVER (NOT the Model-T scalar
    /// contract) and surfaces a native-fold injection site, so it fires as a COMM. Contrast with
    /// [`native_fold_reuses_scalar_contract_par`] (a bare non-fold op keeps its scalar contract and
    /// surfaces NO firing site).
    #[test]
    fn native_scalar_fold_lowers_to_a_firing_dispatch_receiver() {
        let def =
            syn::parse_str::<LanguageDef>(NATIVE_FOLD_FRAGMENT).expect("fold fragment must parse");
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        // AddInt lowers to a `NativeFold` whose `par` is the flat one-slot DISPATCH RECEIVER
        // `for (result, out <- sa:scalar/AddInt) { out!(result) }` — `bind_count == 2` (result +
        // out), NOT the 3-formal scalar contract `contract @"AddInt"(@a, @b, ret)` (bind_count 3).
        let par = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::NativeFold { rule_id, par } if rule_id == "rule:AddInt" => {
                    Some(par)
                },
                _ => None,
            })
            .expect("a `fold` AddInt must lower to a NativeFold dispatch receiver");
        let receive = par
            .receives
            .first()
            .expect("the NativeFold dispatch receiver is a single persistent receive");
        assert_eq!(
            receive.bind_count, 2,
            "the firing dispatch receiver binds exactly (result, out) — 2 formals, NOT the \
             3-formal scalar contract"
        );
        let source = receive.binds[0]
            .source
            .as_ref()
            .expect("the dispatch receiver rests on its source channel");
        assert_eq!(
            source,
            &new_gstring_par("sa:scalar/AddInt".to_string(), Vec::new(), false),
            "the firing dispatch receiver rests on the `sa:scalar/AddInt` trace channel, NOT the \
             scalar contract's `@\"AddInt\"` channel"
        );

        // It surfaces a native-fold FIRING site (Int_AddInt) on that same dispatch channel — so the
        // fold fires as a COMM (the accept-triad: receiver source ≡ injection channel).
        let sites = rho_net_native_fold_injection_sites(&def);
        assert_eq!(
            sites.len(),
            1,
            "the `fold` AddInt must surface exactly one native-fold firing site"
        );
        assert_eq!(sites[0].rule_label, "Int_AddInt");
        assert_eq!(sites[0].channel, "sa:scalar/AddInt");

        // The program installs cleanly (the firing receiver is a real materialized contract).
        assert!(
            lowered.errors().is_empty(),
            "a `fold` scalar language lowers without diagnostics"
        );
        assert!(
            lowered.installed_program_par().is_ok(),
            "the native-fold firing receiver installs"
        );
    }

    /// D3 (Stage 3f) — the CONGRUENCE side of the fold-vs-equation criterion: a LOSSLESS ISO
    /// COERCION (an auto-injected cast-canonicalization `NormCast`, identified by its
    /// `Premise::SyntheticInjGuard`) is a symmetric representation change, NOT directed motion, so
    /// it lowers to a `CongruenceClosure` — recognized, NO firing receiver (does not install a
    /// σ-receiver), and — unlike a fail-closed `Unsupported` — does NOT block the install boundary.
    /// This is the exact boundary a computing fold ([`native_scalar_fold_lowers_to_a_firing_dispatch_receiver`])
    /// sits on the FIRING side of.
    #[test]
    fn lossless_cast_normcast_lowers_to_congruence_not_a_firing_receiver() {
        // A rewrite mirroring the auto-injected `NormCast<Src>To<Tgt>In<Result>`:
        // `(CastInt v) ~> (CastBigRat (IntToBigRat v))` carrying the `SyntheticInjGuard` premise
        // (the sole marker of a lossless cast-canonicalization; auto-injection attaches it ONLY to
        // `NormCast*` rules).
        let (lowered, id) = lower_single_rewrite_full(RewriteRule {
            name: ident("NormCastIntToBigRatInInt"),
            type_context: Vec::new(),
            premises: vec![Premise::SyntheticInjGuard {
                inner_var: ident("v"),
                source_category: ident("Int"),
                excluded_variants: vec![ident("BoolToInt")],
            }],
            left: apply("CastInt", vec![var_pattern("v")]),
            right: apply("CastBigRat", vec![apply("IntToBigRat", vec![var_pattern("v")])]),
            is_auto_injected: true,
        });

        // It lowers to a CONGRUENCE closure — NOT a firing receiver (no `par`), NOT a fail-closed
        // `Unsupported` (which would block the install).
        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == id)
            .expect("the NormCast rewrite must be lowered");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::CongruenceClosure { rule_id: id.clone() },
            "a lossless cast (NormCast/SyntheticInjGuard) is congruence, not a firing receiver"
        );
        assert!(
            rule.par().is_none(),
            "a congruence closure installs NO firing receiver Par (D3: no COMM for a lossless iso)"
        );

        // Crucially, it does NOT block the install boundary (unlike a fail-closed side condition):
        // the scalar contracts still install, the NormCast contributes no Par (compile-time
        // congruence). Contrast `rewrite_premises_receiver_safe`, which would fail-close a
        // structural side condition into an `Unsupported` that blocks the install.
        assert!(
            lowered.errors().is_empty(),
            "a lossless-cast congruence records no fail-closed diagnostic, got {:?}",
            lowered.errors()
        );
        assert!(
            lowered.installed_program_par().is_ok(),
            "the program still installs — the lossless cast is congruence, not an install blocker"
        );

        // And the discriminator itself: the SyntheticInjGuard marks it a lossless cast.
        assert!(is_lossless_cast_congruence(&RewriteRule {
            name: ident("NormCastIntToBigRatInInt"),
            type_context: Vec::new(),
            premises: vec![Premise::SyntheticInjGuard {
                inner_var: ident("v"),
                source_category: ident("Int"),
                excluded_variants: Vec::new(),
            }],
            left: var_pattern("v"),
            right: var_pattern("v"),
            is_auto_injected: true,
        }));
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
                RhoNetLoweredRule::Comm {
                    rule_id: "rule:rewrite:1:Join".to_string(),
                },
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
            RhoNetLoweredRule::Unsupported {
                family: UnsupportedFamily::LambdaBinder,
                ..
            }
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

        let send = &par.receives[0]
            .body
            .as_ref()
            .expect("σ-receiver body")
            .sends[0];
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

    /// Stage AC-U3: an un-skipped linear with-rest HashBag AC rewrite surfaces exactly one
    /// AC injection site whose channel equals the AC receiver's SOURCE channel (accept-triad
    /// coherence), whose `op` is the HashBag constructor, whose `element_var_order` is the
    /// first-occurrence element vars, and whose `rest_var` is the residual binder — the AC
    /// firing analogue of the base-rewrite site test. Uses a `coll_type: None` LHS collection
    /// (the parser default) so the site derivation exercises the same kind resolution the
    /// receiver un-skip does.
    #[test]
    fn rho_net_ac_injection_sites_surface_the_ac_rewrite_channel_op_vars_and_rest() {
        let mut def: LanguageDef =
            syn::parse_str(AC_DEMO_FRAGMENT).expect("the AcDemo fragment parses");
        def.rewrites.push(RewriteRule {
            name: ident("AcStep"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: None,
                    elements: vec![var_pattern("x")],
                    rest: Some(ident("rest")),
                }],
            ),
            right: apply("Wrap", vec![var_pattern("x")]),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);

        // The AC receiver's source channel, resolved exactly as the runtime AC injection must
        // reproduce it (the un-skipped rewrite's first input channel).
        let ac_rewrite_id = rule_id_rewrite(0, "AcStep");
        let expected_channel = program
            .rules
            .iter()
            .find(|rule| rule.id == ac_rewrite_id)
            .and_then(|rule| rule.input_channels.first())
            .expect("AcStep AC rewrite must have a source channel")
            .clone();

        let sites = rho_net_ac_injection_sites(&def);
        assert_eq!(sites.len(), 1, "one un-skipped AC receiver ⇒ one AC injection site");
        assert_eq!(
            sites[0],
            RhoNetAcInjectionSite {
                rule_label: "AcStep".to_string(),
                channel: expected_channel,
                op: "PPar".to_string(),
                element_var_order: vec!["x".to_string()],
                rest_var: "rest".to_string(),
            }
        );

        // The AC rule is NOT a flat base-rewrite site: the two site derivations partition the
        // rewrites by receiver family, so an AC firing routes to the AC arm exclusively.
        assert!(
            rho_net_injection_sites(&def).is_empty(),
            "an AC rewrite is not a flat base-rewrite σ-receiver site"
        );
    }

    /// A language with no un-skipped AC rewrites surfaces no AC injection sites (the AC firing
    /// analogue of `rho_net_injection_sites_are_empty_without_base_rewrites`).
    #[test]
    fn rho_net_ac_injection_sites_are_empty_without_ac_rewrites() {
        assert!(rho_net_ac_injection_sites(&scalar_def()).is_empty());
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
            RhoNetLoweredRule::Unsupported {
                family: UnsupportedFamily::CollectionAc,
                ..
            }
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
    fn minirho_comm_materializes_and_parcong_is_unsupported() {
        let def = syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        // Stage 3b: Comm is a BASE rewrite whose Collection LHS `lower_lhs_vars` rejects
        // (`CollectionAc`), the linear `ac_rule_receiver` declines (structured elements), and the
        // Comm detector un-skips to a non-linear AC σ-receiver — no longer fail-closed.
        let comm = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:0:Comm")
            .expect("Comm must be lowered");
        assert!(
            matches!(comm, RhoNetLoweredRule::CommRewrite { .. }),
            "Comm must materialize as a CommRewrite, got {comm:?}"
        );

        // ParCong is a CONTEXTUAL rewrite whose Collection LHS is caught by the
        // independent P2 detector — still fail-closed (a congruence over an AC context).
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

    /// The Comm rule un-skips to a non-linear AC σ-receiver: a single persistent polyadic
    /// `Receive` carrying the `EEq(N_recv, N_send)` consistency `condition`, the structured
    /// process-soup bag pattern, and a bag-RHS body. This is the codegen half of the Stage 3b
    /// end-to-end firing (`rho_net_comm_firing`).
    #[test]
    fn comm_rule_un_skips_to_a_guarded_non_linear_ac_receiver() {
        let def = syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");

        // The shape is recognized (structured non-linear AC LHS + substitution-in-bag RHS).
        let comm_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == "Comm")
            .expect("MiniRhoFor has a Comm rewrite");
        let shape = comm_rule_shape(
            &comm_rewrite.left,
            &comm_rewrite.right,
            Some(&CollectionType::HashBag),
        )
        .expect("Comm rule must be recognized as a Comm shape");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "N");
        assert_eq!(shape.rest.to_string(), "rest");
        assert_eq!(shape.scope_var.to_string(), "cont");
        assert_eq!(shape.arg_var.to_string(), "Q");
        assert_eq!(
            shape
                .elements
                .iter()
                .map(|element| element.constructor.clone())
                .collect::<Vec<_>>(),
            vec!["PFor".to_string(), "POutput".to_string()]
        );
        // Each element carries the non-linear channel var once (`PFor N …` / `POutput N …`).
        for element in &shape.elements {
            assert_eq!(element.args[element.nonlinear_index].to_string(), "N");
        }

        // The materialized receiver carries a persistent guarded Receive.
        let receiver = comm_rule_receiver(
            &comm_rewrite.left,
            &comm_rewrite.right,
            new_gstring_par("c(root)".to_string(), Vec::new(), false),
            "fp",
            Some(CollectionType::HashBag),
        )
        .expect("Comm rule must materialize a receiver");
        let receive = receiver
            .receives
            .first()
            .expect("the Comm receiver is a single Receive");
        assert!(receive.persistent, "the Comm σ-receiver is persistent");
        assert_eq!(receive.bind_count, COMM_FREE_COUNT as i32);
        // Exactly one polyadic bind: [ bag-soup pattern, reduct, out ].
        assert_eq!(receive.binds.len(), 1);
        assert_eq!(receive.binds[0].patterns.len(), 3);
        assert_eq!(receive.binds[0].free_count, COMM_FREE_COUNT as i32);

        // The consistency `condition` is `EEq(BoundVar, BoundVar)` over the two channel slots.
        let condition = receive
            .condition
            .as_ref()
            .expect("the Comm receiver carries a non-linear condition");
        let expr = condition
            .exprs
            .first()
            .expect("the condition is a single expression");
        let ExprInstance::EEqBody(eq) = expr.expr_instance.as_ref().expect("condition has an expr")
        else {
            panic!("the Comm consistency condition must be an EEq, got {expr:?}");
        };
        // N_recv is slot 0 (BoundVar 4), N_send is slot 1 (BoundVar 3), free_count 5.
        assert_eq!(boundvar_index(eq.p1.as_ref().expect("EEq p1")), Some(4));
        assert_eq!(boundvar_index(eq.p2.as_ref().expect("EEq p2")), Some(3));

        // The bag pattern (first bind pattern) is a connective process soup with two like-tagged
        // element sends + a remainder.
        let bag_pattern = &receive.binds[0].patterns[0];
        assert_eq!(bag_pattern.sends.len(), 2, "two structured element sends");
        assert!(
            bag_pattern
                .exprs
                .iter()
                .any(|expr| matches!(expr.expr_instance, Some(ExprInstance::EVarBody(_)))),
            "the bag pattern binds a process remainder"
        );
    }

    /// The Comm injection site surfaces the receiver's channel + shape so a Comm σ-injection
    /// (`comm_contract_call`) can target it.
    #[test]
    fn comm_injection_site_is_surfaced_for_the_comm_rule() {
        let def = syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");
        let sites = rho_net_comm_injection_sites(&def);
        assert_eq!(sites.len(), 1, "MiniRhoFor has exactly one Comm rewrite");
        let site = &sites[0];
        assert_eq!(site.rule_label, "Comm");
        assert_eq!(site.op, "PPar");
        assert_eq!(site.nonlinear_var, "N");
        assert_eq!(site.rest_var, "rest");
        assert_eq!(site.scope_var, "cont");
        assert_eq!(site.arg_var, "Q");
        assert_eq!(site.element_constructors, vec!["PFor".to_string(), "POutput".to_string()]);
        // Each element's arg vars (parallel to `element_constructors`) — the σ slots the Comm
        // injection rebuilds each operand-bag element from.
        assert_eq!(
            site.element_arg_vars,
            vec![
                vec!["N".to_string(), "cont".to_string()],
                vec!["N".to_string(), "Q".to_string()],
            ]
        );
        assert!(!site.channel.is_empty(), "the Comm receiver has a source channel");
    }

    /// Ambient's structural `OpenRule` (`{(POpen N P), (PAmb N Q), ...rest} ~> {P, Q, ...rest}`) is
    /// non-linear structured AC but its RHS is STRUCTURAL, not a substitution-in-bag, so the Comm
    /// detector DECLINES it (fail-closed / handled on its existing path) — the Comm shape is the
    /// precise substitution-communication shape, never a generic non-linear AC rewrite.
    #[test]
    fn structural_non_linear_ac_rewrite_is_not_a_comm_shape() {
        let open_rule_left = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![
                    apply("POpen", vec![var_pattern("N"), var_pattern("P")]),
                    apply("PAmb", vec![var_pattern("N"), var_pattern("Q")]),
                ],
                rest: Some(ident("rest")),
            }],
        );
        let open_rule_right = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![var_pattern("P"), var_pattern("Q")],
                rest: Some(ident("rest")),
            }],
        );
        assert!(
            comm_rule_shape(&open_rule_left, &open_rule_right, Some(&CollectionType::HashBag))
                .is_none(),
            "a structural (non-substitution) non-linear AC RHS is not a Comm shape"
        );
    }

    /// Stage 3d: a minimal Ambient whose `OpenRule` is a STRUCTURAL non-linear AC rewrite
    /// `{(open N P), N[Q], ...rest} ~> {P, Q, ...rest}` — the clean OpenRule target isolated from
    /// the deep-nesting `InRule`/`OutRule` and the `PNew` binder.
    const MINI_AMBIENT_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniAmbient,
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
            PA . |- "a" : Proc ;
            PB . |- "b" : Proc ;

            Na . |- "na" : Name ;
            Nb . |- "nb" : Name ;

            PPar . ps:HashBag(Proc)
                |- "{" ps.*sep("|") "}" : Proc ;

            POpen . n:Name, p:Proc
                |- "open" "(" n "," p ")" : Proc ;

            PAmb . n:Name, p:Proc
                |- n "[" p "]" : Proc ;
        },
        equations {},
        rewrites {
            OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
                ~> (PPar {P, Q, ...rest});

            ParCong . | S ~> T
                |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
        }
    "#;

    /// The `OpenRule` un-skips to a `StructuralAcRewrite`: its Collection LHS `lower_lhs_vars`
    /// rejects (`CollectionAc`), the linear `ac_rule_receiver` declines (structured elements), the
    /// `comm_rule_receiver` declines (structural RHS, not a substitution), and the structural-AC
    /// detector un-skips to a non-linear AC σ-receiver — no longer fail-closed.
    #[test]
    fn mini_ambient_open_rule_materializes_structural_ac() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let open = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:0:OpenRule")
            .expect("OpenRule must be lowered");
        assert!(
            matches!(open, RhoNetLoweredRule::StructuralAcRewrite { .. }),
            "OpenRule must materialize as a StructuralAcRewrite, got {open:?}"
        );
        assert!(
            !lowered
                .errors()
                .iter()
                .any(|error| matches!(error, RhoNetLoweringError::RuleSourceDrift { .. })),
            "faithful re-derivation must not report rule-source drift"
        );
    }

    /// `structural_ac_rule_shape` recognizes the OpenRule shape (`op`, non-linear var, `rest`, the
    /// two structured elements, and the two STRUCTURAL reduct vars `P`/`Q` — never a substitution).
    #[test]
    fn structural_ac_rule_shape_recognizes_open_rule() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let open_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == "OpenRule")
            .expect("MiniAmbient has an OpenRule rewrite");
        let shape = structural_ac_rule_shape(
            &open_rewrite.left,
            &open_rewrite.right,
            Some(&CollectionType::HashBag),
        )
        .expect("OpenRule must be recognized as a structural AC shape");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "N");
        assert_eq!(shape.rest.to_string(), "rest");
        assert_eq!(
            shape
                .elements
                .iter()
                .map(|element| element.constructor.clone())
                .collect::<Vec<_>>(),
            vec!["POpen".to_string(), "PAmb".to_string()]
        );
        // Each element carries the non-linear channel var once (`POpen N …` / `PAmb N …`).
        for element in &shape.elements {
            assert_eq!(element.args[element.nonlinear_index].to_string(), "N");
        }
        // The reduct vars are the STRUCTURAL RHS elements `P`, `Q` (bare LHS-element args).
        assert_eq!(
            shape
                .reduct_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["P".to_string(), "Q".to_string()]
        );
    }

    /// The Comm shape (substitution-in-bag RHS) is NOT a structural AC shape — the two detectors are
    /// mutually exclusive by RHS shape (bare-var elements vs a single `(eval scope arg)` element).
    #[test]
    fn comm_rule_is_not_a_structural_ac_shape() {
        let def = syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");
        let comm_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == "Comm")
            .expect("MiniRhoFor has a Comm rewrite");
        assert!(
            structural_ac_rule_shape(
                &comm_rewrite.left,
                &comm_rewrite.right,
                Some(&CollectionType::HashBag),
            )
            .is_none(),
            "a substitution-in-bag (Comm) RHS is not a structural AC shape"
        );
    }

    /// The OpenRule un-skips to a non-linear AC σ-receiver: a single persistent polyadic `Receive`
    /// carrying the `EEq(N_0, N_1)` consistency `condition`, the structured process-soup bag
    /// pattern, and `m + 2` bind patterns (bag, the two reduct slots, out). This is the codegen half
    /// of the Stage 3d end-to-end firing (`rho_net_ambient_firing`).
    #[test]
    fn structural_ac_rule_un_skips_to_a_guarded_non_linear_ac_receiver() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let open_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == "OpenRule")
            .expect("MiniAmbient has an OpenRule rewrite");

        let receiver = structural_ac_rule_receiver(
            &open_rewrite.left,
            &open_rewrite.right,
            new_gstring_par("c(root)".to_string(), Vec::new(), false),
            "fp",
            Some(CollectionType::HashBag),
        )
        .expect("OpenRule must materialize a receiver");
        let receive = receiver
            .receives
            .first()
            .expect("the structural-AC receiver is a single Receive");
        assert!(receive.persistent, "the structural-AC σ-receiver is persistent");
        // free_count = k + 1 + m + 1 = 2 + 1 + 2 + 1 = 6.
        assert_eq!(receive.bind_count, 6);
        // Exactly one polyadic bind: [ bag-soup pattern, reduct_0, reduct_1, out ] = m + 2 = 4.
        assert_eq!(receive.binds.len(), 1);
        assert_eq!(receive.binds[0].patterns.len(), 4);
        assert_eq!(receive.binds[0].free_count, 6);

        // The consistency `condition` is `EEq(BoundVar(5), BoundVar(4))` over the two channel slots
        // (levels 0/1 → BoundVar(free_count - 1 - level) = 5/4).
        let condition = receive
            .condition
            .as_ref()
            .expect("the structural-AC receiver carries a non-linear condition");
        let expr = condition
            .exprs
            .first()
            .expect("the condition is a single expression");
        let ExprInstance::EEqBody(eq) = expr.expr_instance.as_ref().expect("condition has an expr")
        else {
            panic!("the consistency condition must be an EEq, got {expr:?}");
        };
        assert_eq!(boundvar_index(eq.p1.as_ref().expect("EEq p1")), Some(5));
        assert_eq!(boundvar_index(eq.p2.as_ref().expect("EEq p2")), Some(4));

        // The bag pattern (first bind pattern) is a connective process soup with two like-tagged
        // element sends + a remainder.
        let bag_pattern = &receive.binds[0].patterns[0];
        assert_eq!(bag_pattern.sends.len(), 2, "two structured element sends");
        assert!(
            bag_pattern
                .exprs
                .iter()
                .any(|expr| matches!(expr.expr_instance, Some(ExprInstance::EVarBody(_)))),
            "the bag pattern binds a process remainder"
        );
    }

    /// The structural-AC injection site surfaces the receiver's channel + shape so a structural-AC
    /// σ-injection (`structural_ac_contract_call`) can target it.
    #[test]
    fn structural_ac_injection_site_is_surfaced_for_the_open_rule() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let sites = rho_net_structural_ac_injection_sites(&def);
        assert_eq!(sites.len(), 1, "MiniAmbient has exactly one structural AC rewrite");
        let site = &sites[0];
        assert_eq!(site.rule_label, "OpenRule");
        assert_eq!(site.op, "PPar");
        assert_eq!(site.nonlinear_var, "N");
        assert_eq!(site.rest_var, "rest");
        assert_eq!(site.reduct_vars, vec!["P".to_string(), "Q".to_string()]);
        assert_eq!(site.element_constructors, vec!["POpen".to_string(), "PAmb".to_string()]);
        // Each element's arg vars (parallel to `element_constructors`) — the σ slots the injection
        // rebuilds each operand-bag element from.
        assert_eq!(
            site.element_arg_vars,
            vec![vec!["N".to_string(), "P".to_string()], vec!["N".to_string(), "Q".to_string()],]
        );
        assert!(!site.channel.is_empty(), "the structural-AC receiver has a source channel");
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

    /// Stage 3c: a minimal untyped λ-calculus whose β-reduction is a BASE rewrite over a binder
    /// LHS with a substitution RHS (`(eval fun arg)` is the capture-avoiding substitution). Mirrors
    /// `mettail_languages::lambdademo`.
    const LAMBDA_DEMO_FRAGMENT: &str = r#"
        name: LambdaDemo,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types {
            Term
        },
        terms {
            Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
            App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            F . a:Term |- "f" "(" a ")" : Term ;
            A . |- "A" : Term ;
        },
        equations {},
        rewrites {
            Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
        }
    "#;

    fn lambda_demo_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(LAMBDA_DEMO_FRAGMENT)
            .expect("lambda-demo fragment must parse")
    }

    /// Stage 3c: the β-reduction `App(Lam(^x. b), a) ~> subst(b, x := a)` (DSL `(App (Lam fun) arg)
    /// ~> (eval fun arg)`) lowers to a `SubstRewrite` σ-receiver (NOT `BaseRewrite`/`Unsupported`),
    /// and its subst injection site carries the LHS σ order `[fun, arg]` (binder-excluded, since
    /// `(Lam fun)` binds `fun` as `Lam`'s ARGUMENT — a σ-slot) with scope variable `fun`.
    #[test]
    fn lambda_demo_beta_lowers_to_subst_rewrite() {
        let def = lambda_demo_def();

        // The subst-rule shape: σ order [fun, arg], scope = fun.
        let rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name.to_string() == "Beta")
            .expect("the Beta rewrite exists");
        let (vars, scope) = subst_rule_shape(&rewrite.left, &rewrite.right)
            .expect("Beta is a substitution rewrite");
        assert_eq!(
            vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
            vec!["fun".to_string(), "arg".to_string()],
            "the LHS σ order is [fun, arg] (binder-excluded)"
        );
        assert_eq!(scope.to_string(), "fun", "the substitution scope variable is fun");

        // It materializes to a SubstRewrite lowered rule (installable).
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        assert!(
            lowered.errors().is_empty(),
            "the β base rewrite lowers with no fail-closed diagnostics, got {:?}",
            lowered.errors()
        );
        let beta = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id().ends_with("Beta"))
            .expect("Beta is a lowered rule");
        assert!(
            matches!(beta, RhoNetLoweredRule::SubstRewrite { .. }),
            "Beta lowers to a SubstRewrite σ-receiver, got {beta:?}"
        );
        assert!(
            lowered.installed_program_par().is_ok(),
            "the SubstRewrite σ-receiver installs (a plain flat receiver)"
        );

        // The subst injection site is derived (drives the runtime subst σ-injection).
        let sites = rho_net_subst_injection_sites(&def);
        assert_eq!(sites.len(), 1, "one subst injection site for Beta, got {sites:?}");
        assert_eq!(sites[0].rule_label, "Beta");
        assert_eq!(sites[0].scope_var, "fun");
        assert_eq!(sites[0].lhs_var_order, vec!["fun".to_string(), "arg".to_string()]);
        assert!(!sites[0].channel.trim().is_empty(), "the site carries a source channel");
    }

    /// Stage 3e: a minimal integer calculator whose only reducing rule is the native
    /// exponentiation `PowInt(a, b) ~> a^b` (`a "^" b`, a `![…] fold` HOL term). The `^` operator
    /// has no in-Rho scalar contract, so it is rejected by the scalar lowering and classified as a
    /// `RhoNetRuleKind::NativeSystemProcess`. Mirrors `mettail_languages::nativedemo`.
    const NATIVE_DEMO_FRAGMENT: &str = r#"
        name: NativeDemo,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types {
            ![i64] as Int
        },
        terms {
            PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] fold;
        },
        equations {},
        rewrites {}
    "#;

    fn native_demo_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(NATIVE_DEMO_FRAGMENT)
            .expect("native-demo fragment must parse")
    }

    /// Stage 3e: the native system process `PowInt(a, b) ~> a^b` (a `![…] fold` HOL term the Rho
    /// scalar path rejects) lowers to a `NativeSystemProcessRewrite` dispatch receiver (NOT
    /// `NativeSystemProcess`/`Unsupported`), and its native injection site carries the op-variant
    /// firing label `Int_PowInt` (the label the report producer bare-ifies the native firing to)
    /// plus a source dispatch channel.
    #[test]
    fn native_demo_pow_lowers_to_native_system_process_rewrite() {
        let def = native_demo_def();

        // The native-rule shape: fold-mode, op-variant firing label "Int_PowInt".
        let term = def
            .terms
            .iter()
            .find(|term| term.label.to_string() == "PowInt")
            .expect("the PowInt term exists");
        assert_eq!(
            native_rule_shape(term).as_deref(),
            Some("Int_PowInt"),
            "PowInt (fold) yields its op-variant firing label Int_PowInt"
        );

        // It materializes to a NativeSystemProcessRewrite lowered rule (installable).
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        assert!(
            lowered.errors().is_empty(),
            "the PowInt native process lowers with no fail-closed diagnostics, got {:?}",
            lowered.errors()
        );
        // A rejected native term generates BOTH a `rule:term:*` structural constructor AND a
        // `rule:native:*` dispatch rule; the native process is the `rule:native:` one.
        let pow = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:native:0:PowInt")
            .expect("PowInt has a native-dispatch lowered rule");
        assert!(
            matches!(pow, RhoNetLoweredRule::NativeSystemProcessRewrite { .. }),
            "PowInt lowers to a NativeSystemProcessRewrite dispatch receiver, got {pow:?}"
        );
        assert!(
            lowered.installed_program_par().is_ok(),
            "the NativeSystemProcessRewrite dispatch receiver installs (a plain flat receiver)"
        );

        // The native injection site is derived (drives the runtime native σ-injection).
        let sites = rho_net_native_injection_sites(&def);
        assert_eq!(sites.len(), 1, "one native injection site for PowInt, got {sites:?}");
        assert_eq!(
            sites[0].rule_label, "Int_PowInt",
            "the site's rule label is the op-variant identity Int_PowInt the firing bare-ifies to"
        );
        assert!(!sites[0].channel.trim().is_empty(), "the site carries a source channel");
    }

    /// Stage 3e (fail-closed): [`native_rule_shape`] is `fold`-gated — only a `fold` native
    /// process has a host-computed contractum for the flat dispatch receiver to forward. A `step`
    /// native process (partial / routing to an `Err` normal form) yields no firing label and, if
    /// classified as a native system process, fails closed with the precise
    /// [`UnsupportedFamily::NativeSystemProcessNotFold`] reason (never installs a receiver no
    /// native firing would drive).
    #[test]
    fn native_rule_shape_is_fold_gated_and_a_step_native_process_fails_closed() {
        const FRAGMENT: &str = r#"
            name: NativeStepDemo,
            options {
                emit_simulator: false,
                emit_blockly: false,
            },
            types {
                ![i64] as Int
            },
            terms {
                PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] fold;
                FactInt . a:Int |- a "!" : Int ![a] step;
            },
            equations {},
            rewrites {}
        "#;
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("native-step fragment must parse");

        let pow = def
            .terms
            .iter()
            .find(|term| term.label.to_string() == "PowInt")
            .expect("PowInt exists");
        let fact = def
            .terms
            .iter()
            .find(|term| term.label.to_string() == "FactInt")
            .expect("FactInt exists");
        assert_eq!(
            native_rule_shape(pow).as_deref(),
            Some("Int_PowInt"),
            "a fold native process yields its op-variant firing label"
        );
        assert_eq!(
            native_rule_shape(fact),
            None,
            "a step native process has no host-computed contractum, so no native firing label"
        );

        // The step native process (a rejected native system process) fails closed with the precise
        // reason; the fold sibling still materializes.
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        let fact_lowered = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:native:1:FactInt")
            .expect("FactInt has a native-dispatch lowered rule");
        assert!(
            matches!(
                fact_lowered,
                RhoNetLoweredRule::Unsupported {
                    family: UnsupportedFamily::NativeSystemProcessNotFold,
                    ..
                }
            ),
            "a step native process fails closed as NativeSystemProcessNotFold, got {fact_lowered:?}"
        );
        assert!(
            lowered.errors().iter().any(|error| matches!(
                error,
                RhoNetLoweringError::UnsupportedFamily {
                    family: UnsupportedFamily::NativeSystemProcessNotFold,
                    ..
                }
            )),
            "the step native process records the precise fail-closed reason, got {:?}",
            lowered.errors()
        );
        // The fold sibling still materializes a dispatch receiver.
        let pow_lowered = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:native:0:PowInt")
            .expect("PowInt has a native-dispatch lowered rule");
        assert!(
            matches!(pow_lowered, RhoNetLoweredRule::NativeSystemProcessRewrite { .. }),
            "the fold sibling still materializes a dispatch receiver, got {pow_lowered:?}"
        );
    }

    /// Stage 3c (item 1): the De Bruijn binder environment in the LHS σ-variable extraction — a
    /// binder brought into scope by a `Lambda`/`MultiLambda` NODE is EXCLUDED from the σ-slots,
    /// while the body's FREE variables are preserved in first-occurrence order.
    #[test]
    fn lower_lhs_vars_excludes_the_binder_and_preserves_free_body_vars() {
        // `Wrap(^x. Pair(x, y))`: the binder `x` (bound in the body) is NOT a σ-slot; the free `y`
        // IS. So the σ order is exactly `[y]`.
        let lam = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(apply("Pair", vec![var_pattern("x"), var_pattern("y")])),
        });
        let lhs = apply("Wrap", vec![lam]);
        let vars = lower_lhs_vars(&lhs).expect("a binder LHS lowers its free σ-slots");
        assert_eq!(
            vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
            vec!["y".to_string()],
            "the binder x is excluded; only the free body var y is a σ-slot"
        );

        // A binder whose body references ONLY the binder has NO σ-slots (fully closed).
        let closed = apply(
            "Wrap",
            vec![Pattern::Term(PatternTerm::Lambda {
                binder: ident("x"),
                body: Box::new(var_pattern("x")),
            })],
        );
        let closed_vars = lower_lhs_vars(&closed).expect("a closed binder LHS lowers");
        assert!(
            closed_vars.is_empty(),
            "a closed binder has no free σ-slots, got {closed_vars:?}"
        );
    }

    /// Stage 3c (item 2): the RHS `Lambda`-node reflection is a tagged binder node
    /// `EList[GPrivate(reflect_tag(^lambda)), ⟦binder⟧, ⟦body⟧]` (mirrors the Apply arm), a bound
    /// occurrence in the body reflects to a distinguished bound-var leaf (NOT a σ-slot `BoundVar`),
    /// and a free body var reflects to its σ-slot. The reserved `^lambda`/`^bound` tags make the
    /// binder node collision-free with any `Apply` node and any σ-slot.
    #[test]
    fn reflect_term_par_reflects_lambda_as_a_tagged_binder_node() {
        let fp = "mettail-langdef-v1:0011223344556677";
        // `⟦^x. Pair(x, y)⟧` with σ-slots `[y]` (k = 1): the head tag is `^lambda`, the binder `x`
        // is a `^bound` leaf, and inside the body `x` is a `^bound` leaf while `y` is `BoundVar`.
        let lam = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(apply("Pair", vec![var_pattern("x"), var_pattern("y")])),
        });
        let vars = vec![ident("y")];
        let reflected =
            reflect_term_par(&lam, &vars, 1, fp, None).expect("the binder node reflects");

        let lambda_tag = GPrivateBuilder::new_par_from_string(reflect_tag(fp, "^lambda"));
        let bound_tag = GPrivateBuilder::new_par_from_string(reflect_tag(fp, "^bound"));
        let pair_tag = GPrivateBuilder::new_par_from_string(reflect_tag(fp, "Pair"));

        // The head element carries the reserved `^lambda` tag (a GPrivate, collision-free with
        // any Apply node and any σ-slot).
        let elements = &elist_body(&reflected).ps;
        assert_eq!(elements.len(), 3, "EList[^lambda tag, ⟦binder⟧, ⟦body⟧]");
        assert_eq!(elements[0], lambda_tag, "the head tag is the reserved ^lambda binder tag");
        // The binder leaf is a `^bound` node (not a σ-slot BoundVar).
        let binder_leaf = &elist_body(&elements[1]).ps;
        assert_eq!(binder_leaf[0], bound_tag, "the binder reflects to a ^bound leaf");
        // Inside the body `Pair(x, y)`: x is a ^bound leaf, y is a σ-slot BoundVar(1).
        let body = &elist_body(&elements[2]).ps; // [Pair tag, ⟦x⟧, ⟦y⟧]
        assert_eq!(body[0], pair_tag, "the body head tag is the Pair constructor tag");
        let x_leaf = &elist_body(&body[1]).ps;
        assert_eq!(
            x_leaf[0], bound_tag,
            "the bound occurrence x reflects to a ^bound leaf, not a σ-slot"
        );
        assert_eq!(
            boundvar_index(&body[2]),
            Some(rhs_var_index(1, 0)),
            "the free body var y reflects to its σ-slot BoundVar"
        );
    }

    /// Stage 3c (item 2): a top-level `Subst`/`MultiSubst` RHS resolves to the host-computed reduct
    /// at its scope variable's σ-slot — `reflect_term_par(MultiSubst{scope: Var(fun)}, [fun, arg])`
    /// is `BoundVar(scope-slot)` (the receiver forwards the reduct the host injects there). An OPEN
    /// substitution under a genuinely-free scope fails closed.
    #[test]
    fn reflect_term_par_resolves_substitution_to_the_scope_slot() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let vars = vec![ident("fun"), ident("arg")];
        // `⟦(eval fun arg)⟧` = `BoundVar(scope-slot of fun)`.
        let subst = Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(var_pattern("fun")),
            replacements: vec![var_pattern("arg")],
        });
        let reflected =
            reflect_term_par(&subst, &vars, 2, fp, None).expect("closed substitution reflects");
        assert_eq!(
            boundvar_index(&reflected),
            Some(rhs_var_index(2, 0)),
            "the substitution forwards the scope variable's σ-slot (fun at index 0)"
        );

        // An OPEN substitution (scope not a bound LHS var) fails closed.
        let open = Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(var_pattern("free")),
            replacements: vec![var_pattern("arg")],
        });
        assert_eq!(
            reflect_term_par(&open, &vars, 2, fp, None),
            Err(UnsupportedFamily::Substitution),
            "an open substitution under a free scope fails closed"
        );
    }

    /// `reflect_ground_term_par` reflects a ground constructor tree to the tagged
    /// `EList` ABI, sharing `reflect_tag` with the RHS reflector: the reflection
    /// of the ground `Pair(B, A)` is exactly the value the `Swap` σ-receiver emits
    /// once `a ↦ A`, `b ↦ B` are substituted into the reflected RHS `Pair(b, a)`.
    #[test]
    fn reflect_ground_term_par_reflects_ground_pair_to_tagged_elist() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let pair =
            GroundTerm::new("Pair", vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")]);
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
        assert_eq!(b.ps[0], GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.B")));
        let a = elist_body(&outer.ps[2]);
        assert_eq!(a.ps.len(), 1, "nullary A is a lone head tag");
        assert_eq!(a.ps[0], GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.A")));

        // Ground reflection binds no σ variable: no BoundVar leaves anywhere and
        // empty locally_free (byte-identical to a lowered ground RHS constructor).
        assert!(par.locally_free.is_empty());
        assert_eq!(boundvar_index(&par), None);
    }

    #[test]
    fn reflects_a_hashbag_as_the_ac_process_soup() {
        // Stage AC0: a HashBag AC operand bag reflects as the ORDER-INDEPENDENT process-`Par`
        // matching carrier — one ground send `@"ac:PPar"!(⟦e⟧)` per element (multiplicity-
        // preserving), NOT the positional tagged EList.
        let fp = "mettail-langdef-v1:0011223344556677";
        let bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        );
        let par = reflect_ground_term_par(&bag, fp);

        assert_eq!(par.sends.len(), 2, "one send per bag element");
        assert!(par.exprs.is_empty(), "the ground bag carrier is a pure send soup (no EList)");
        for send in &par.sends {
            assert_eq!(send.data.len(), 1, "each send carries one reflected element");
            assert_eq!(
                send.chan.as_ref().unwrap(),
                &new_gstring_par("ac:PPar".to_string(), Vec::new(), false),
                "elements are sent on the AC element channel ac:{{op}}"
            );
            assert_eq!(elist_body(&send.data[0]).ps.len(), 1, "nullary element = lone head tag");
        }

        // Multiplicity: a duplicate element yields a duplicate send (2 x A + B -> 3 sends).
        let bag2 = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        );
        assert_eq!(reflect_ground_term_par(&bag2, fp).sends.len(), 3);
    }

    #[test]
    fn ac_bag_pattern_is_a_connective_soup_with_a_remainder() {
        // The AC receiver's collection pattern: k send-patterns @"ac:PPar"!(FreeVar(i)) + a
        // process remainder EVar(FreeVar(k)), connective (the native sub_pars matcher assigns
        // the k patterns to k carrier sends in any order and binds the residual to `rest`).
        let pattern = ac_bag_pattern("PPar", 2);
        assert_eq!(pattern.sends.len(), 2, "one send-pattern per fixed element");
        assert!(pattern.connective_used, "a matching pattern with free vars is connective");
        assert_eq!(pattern.exprs.len(), 1, "the process remainder is one top-level free var");
        for send in &pattern.sends {
            assert_eq!(send.data.len(), 1, "each send-pattern carries one element free var");
            assert!(send.connective_used, "the send-pattern binds a free element var");
        }
    }

    #[test]
    fn ac_rhs_reflects_with_the_ac_receiver_frame() {
        // Stage AC2: the AC RHS `⟦R⟧σ` reuses `reflect_term_par` with `k' = k+1` (the AC
        // receiver has k+2 formals: k elements + rest + out), so element var `x_i` maps to
        // `BoundVar(k+2-i)` and `rest` to `BoundVar(1)` — NO new reflection frame is needed.
        // For k=1, `PPar{x, ...rest} ~> Wrap(x)`: `⟦Wrap(x)⟧ = EList[tag_Wrap, BoundVar(2)]`
        // (x = element 1 = BoundVar(2), matching the receiver's `ac_receiver_fires` frame).
        let fp = "mettail-langdef-v1:0011223344556677";
        let rhs = apply("Wrap", vec![var_pattern("x")]);
        let vars = vec![ident("x"), ident("rest")]; // [element, rest] — the AC σ order
        let reflected = reflect_term_par(&rhs, &vars, 2, fp, None).expect("Wrap(x) reflects");
        let outer = elist_body(&reflected);
        assert_eq!(outer.ps.len(), 2, "head tag + one element σ");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the RHS head is the Wrap reflection tag"
        );
        assert_eq!(
            boundvar_index(&outer.ps[1]),
            Some(2),
            "element x = BoundVar(2) — the AC receiver frame (k+2-1 for k=1)"
        );
    }

    #[test]
    fn ac_bag_rhs_reflects_to_the_hashbag_soup_carrier() {
        // Stage AC2b: a bag-VALUED RHS `PPar{Wrap(x), ...rest}` reflects to the process-soup
        // carrier (the SAME shape `reflect_ground_term_par` emits for a HashBag) — one send
        // `@"ac:PPar"!(⟦Wrap(x)⟧σ)` per fixed element, parallel-composed with the `rest` σ-slot (a
        // top-level process `BoundVar` that splices the residual sends at runtime) — NOT a tagged
        // `EList`. The parser leaves the RHS collection's `coll_type` as `None`, so the kind is
        // resolved from `PPar`'s declared HashBag param via the threaded `def`.
        let fp = "mettail-langdef-v1:0011223344556677";
        let def = syn::parse_str::<LanguageDef>(AC_DEMO_FRAGMENT).expect("AC demo fragment parses");
        let rhs = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: None,
                elements: vec![apply("Wrap", vec![var_pattern("x")])],
                rest: Some(ident("rest")),
            }],
        );
        let vars = vec![ident("x"), ident("rest")]; // the AC σ order [element, rest]
        let soup = reflect_term_par(&rhs, &vars, 2, fp, Some(&def))
            .expect("the bag RHS reflects to a soup");

        // A bare soup, NOT a tagged EList: exactly one fixed-element send + the rest process var.
        assert_eq!(soup.sends.len(), 1, "one send per fixed element (Wrap(x))");
        let send = &soup.sends[0];
        assert_eq!(
            gstring_value(send.chan.as_ref().expect("send channel")),
            Some("ac:PPar".to_string()),
            "the element send is on the @\"ac:{{op}}\" carrier channel"
        );
        let elem = elist_body(&send.data[0]);
        assert_eq!(
            elem.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the fixed element head is the Wrap reflection tag"
        );
        assert_eq!(
            boundvar_index(&elem.ps[1]),
            Some(2),
            "x = element BoundVar(2) (the AC receiver's k+2-formal frame, k=1)"
        );

        // The `rest` σ-slot is the one top-level process var BoundVar(1) — the AC receiver's
        // residual-soup formal — which parallel-composes (SPLICES) the residual sends at runtime.
        assert_eq!(soup.exprs.len(), 1, "the rest σ-slot is the one top-level process var");
        assert_eq!(
            boundvar_index(&soup),
            Some(1),
            "rest = BoundVar(1) (the AC receiver's residual-soup formal)"
        );
    }

    #[test]
    fn ac_bag_rhs_without_a_def_stays_fail_closed() {
        // Without a `def` to resolve the constructor's HashBag kind, a collection RHS has no soup
        // image and fails closed exactly as before Stage AC2b — so a base/subst/contextual RHS
        // (which thread `None`) never accidentally emits a bag soup.
        let fp = "mettail-langdef-v1:0011223344556677";
        let rhs = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: None,
                elements: vec![apply("Wrap", vec![var_pattern("x")])],
                rest: Some(ident("rest")),
            }],
        );
        let vars = vec![ident("x"), ident("rest")];
        assert_eq!(
            reflect_term_par(&rhs, &vars, 2, fp, None),
            Err(UnsupportedFamily::CollectionAc),
            "a bag RHS with no def resolver fails closed"
        );
    }

    #[test]
    fn ac_rule_receiver_un_skips_a_bag_transforming_rule() {
        // Stage AC2b end-to-end (codegen): `PPar{x, ...rest} ~> PPar{Wrap(x), ...rest}` un-skips to
        // an AC receiver whose body fires the transformed bag-soup carrier on out:
        // `out!( @"ac:PPar"!(⟦Wrap(x)⟧σ) | rest )`. The rest σ-slot BoundVar(1) splices the
        // residual soup, so the fired value is a FLAT bag (mirrors `add_flattened_bag`).
        let fp = "mettail-langdef-v1:0011223344556677";
        let def = syn::parse_str::<LanguageDef>(AC_DEMO_FRAGMENT).expect("AC demo fragment parses");
        let left = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![var_pattern("x")],
                rest: Some(ident("rest")),
            }],
        );
        let right = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: None,
                elements: vec![apply("Wrap", vec![var_pattern("x")])],
                rest: Some(ident("rest")),
            }],
        );
        let receiver = ac_rule_receiver(
            &left,
            &right,
            new_gstring_par("c_ac".to_string(), Vec::new(), false),
            fp,
            Some(CollectionType::HashBag),
            Some(&def),
        )
        .expect("the bag-transforming AC rule un-skips to an AC receiver");

        let recv = &receiver.receives[0];
        assert!(recv.persistent, "the AC receiver is persistent");
        // Body: out!(soup) with out = BoundVar(0), soup = @"ac:PPar"!(⟦Wrap(x)⟧) | BoundVar(1).
        let body_send = &recv.body.as_ref().expect("receiver body").sends[0];
        assert_eq!(
            boundvar_index(body_send.chan.as_ref().expect("out channel")),
            Some(0),
            "fires on out = BoundVar(0)"
        );
        let soup = &body_send.data[0];
        assert_eq!(soup.sends.len(), 1, "the transformed bag has one fixed-element send");
        assert_eq!(
            gstring_value(soup.sends[0].chan.as_ref().expect("element channel")),
            Some("ac:PPar".to_string()),
            "the fixed element rides the @\"ac:PPar\" carrier"
        );
        let elem = elist_body(&soup.sends[0].data[0]);
        assert_eq!(
            elem.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the transformed element is Wrap(...)"
        );
        assert_eq!(boundvar_index(&elem.ps[1]), Some(2), "x = element BoundVar(2)");
        // The rest σ-slot BoundVar(1) at the soup top level splices the residual bag.
        assert_eq!(
            boundvar_index(soup),
            Some(1),
            "rest = BoundVar(1) splices the residual soup (the flat bag)"
        );
    }

    #[test]
    fn ac_rule_receiver_un_skips_a_hashbag_rule() {
        // PPar{x, ...rest} ~> Wrap(x): a HashBag AC base rewrite un-skips to a working AC receiver.
        let fp = "mettail-langdef-v1:0011223344556677";
        let left = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![var_pattern("x")],
                rest: Some(ident("rest")),
            }],
        );
        let right = apply("Wrap", vec![var_pattern("x")]);
        let receiver = ac_rule_receiver(
            &left,
            &right,
            new_gstring_par("c_ac".to_string(), Vec::new(), false),
            fp,
            Some(CollectionType::HashBag),
            None,
        )
        .expect("the HashBag AC rule un-skips to an AC receiver");

        // A persistent receive over [connective collection pattern, out].
        let recv = &receiver.receives[0];
        assert!(recv.persistent, "the AC receiver is persistent");
        assert_eq!(recv.binds[0].patterns.len(), 2, "[collection pattern, out]");
        let pattern = &recv.binds[0].patterns[0];
        assert_eq!(pattern.sends.len(), 1, "k=1 element send-pattern");
        assert!(pattern.connective_used, "the collection pattern is connective");

        // The body fires ⟦Wrap(x)⟧ = EList[tag_Wrap, BoundVar(2)] on out = BoundVar(0).
        let send = &recv.body.as_ref().unwrap().sends[0];
        assert_eq!(
            boundvar_index(send.chan.as_ref().unwrap()),
            Some(0),
            "fires on out = BoundVar(0)"
        );
        let rhs = elist_body(&send.data[0]);
        assert_eq!(rhs.ps.len(), 2, "Wrap tag + the element σ");
        assert_eq!(boundvar_index(&rhs.ps[1]), Some(2), "element x = BoundVar(2) (the AC frame)");

        // A non-AC rule (structural Swap) is NOT un-skipped — stays on its existing path.
        let swap = apply("Swap", vec![var_pattern("a"), var_pattern("b")]);
        assert!(
            ac_rule_receiver(
                &swap,
                &right,
                new_gstring_par("c".to_string(), Vec::new(), false),
                fp,
                None,
                None
            )
            .is_none(),
            "a non-HashBag LHS is not un-skipped"
        );
    }

    #[test]
    fn hashbag_ac_rewrite_un_skips_to_an_installed_ac_receiver() {
        // Stage AC-U1: a linear with-rest HashBag AC base rewrite PPar{P, ...rest} ~> Wrap(P)
        // un-skips (in lower_base_rewrite, where lower_lhs_vars fails CollectionAc) to an
        // AcRewrite — a materialized in-Rho AC receiver — NOT Unsupported, and it installs.
        let rewrite = RewriteRule {
            name: ident("AcStep"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: Some(CollectionType::HashBag),
                    elements: vec![var_pattern("P")],
                    rest: Some(ident("rest")),
                }],
            ),
            right: apply("Wrap", vec![var_pattern("P")]),
            is_auto_injected: false,
        };
        let (rule, errors) = lower_single_rewrite(rewrite.clone());
        assert!(
            matches!(rule, RhoNetLoweredRule::AcRewrite { .. }),
            "HashBag AC rewrite un-skips to AcRewrite, got {rule:?}"
        );
        assert!(errors.is_empty(), "no lowering errors: {errors:?}");

        // It installs: the AcRewrite materializes a persistent AC receiver, past the boundary.
        let (lowered, id) = lower_single_rewrite_full(rewrite);
        let ac_par = lowered
            .rules()
            .iter()
            .find_map(|r| match r {
                RhoNetLoweredRule::AcRewrite { par, rule_id } if rule_id == &id => Some(par),
                _ => None,
            })
            .expect("the lowering carries the AcRewrite par");
        assert_eq!(ac_par.receives.len(), 1, "the AC receiver is one receive");
        assert!(ac_par.receives[0].persistent, "the AC receiver is persistent");
        assert!(
            lowered.installed_program_par().is_ok(),
            "the AC rewrite installs (does not block the fail-closed boundary)"
        );
    }

    #[test]
    fn resolve_ac_collection_type_reads_the_constructor_declaration() {
        // Stage AC-U0: the resolver reads PPar's declared HashBag collection param from
        // def.terms, even though a rewrite-LHS collection's coll_type is None (parser default) —
        // this is what lets a PARSER-produced AC rule un-skip.
        let def: LanguageDef =
            syn::parse_str(AC_DEMO_FRAGMENT).expect("the AcDemo fragment parses");
        let lhs = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: None,
                elements: vec![var_pattern("x")],
                rest: Some(ident("rest")),
            }],
        );
        assert_eq!(
            resolve_ac_collection_type(&def, &lhs),
            Some(CollectionType::HashBag),
            "PPar's HashBag collection param resolves despite coll_type: None"
        );
        // A non-collection constructor resolves to None (never mis-classified as AC).
        assert_eq!(
            resolve_ac_collection_type(&def, &apply("Wrap", vec![var_pattern("x")])),
            None,
            "a non-collection constructor is not an AC HashBag rule"
        );
    }

    #[test]
    fn parser_none_hashbag_rule_un_skips_via_resolution() {
        // The end-to-end AC-U0 path: a rewrite whose LHS collection has coll_type: None (the
        // parser default) un-skips to AcRewrite because lower_base_rewrite resolves PPar's
        // declared HashBag kind from def.terms — the fix that makes REAL (parsed) AC rules fire.
        let mut def: LanguageDef =
            syn::parse_str(AC_DEMO_FRAGMENT).expect("the AcDemo fragment parses");
        def.rewrites.push(RewriteRule {
            name: ident("AcStep"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: None,
                    elements: vec![var_pattern("x")],
                    rest: Some(ident("rest")),
                }],
            ),
            right: apply("Wrap", vec![var_pattern("x")]),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        let id = rule_id_rewrite(0, "AcStep");
        assert!(
            lowered
                .rules()
                .iter()
                .any(|r| r.rule_id() == id && matches!(r, RhoNetLoweredRule::AcRewrite { .. })),
            "a coll_type: None HashBag rule un-skips to AcRewrite via resolution: {:?}",
            lowered
                .rules()
                .iter()
                .map(|r| r.rule_id())
                .collect::<Vec<_>>()
        );
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

    // ---- Stage 3a: contextual (congruence) rewrite → atomic polyadic join ----

    /// A clean UNARY congruence language: a base rewrite `Flip: Swap(x, y) ~> Pair(y, x)`
    /// fires the premise `S ~> T`, and the congruence rewrite `WrapCong: | S ~> T |-
    /// Wrap(S) ~> Wrap(T)` closes the context. The mirror of `swapdemo` with a Wrap
    /// congruence — the codegen fixture for the contextual join lowering.
    const CTX_DEMO_FRAGMENT: &str = r#"
        name: RhoNetCtxFrag,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types { Proc },
        terms {
            A . |- "A" : Proc ;
            B . |- "B" : Proc ;
            Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
            Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
            Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
        },
        equations {},
        rewrites {
            Flip . |- (Swap x y) ~> (Pair y x) ;
            WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;
        }
    "#;

    fn ctx_demo_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(CTX_DEMO_FRAGMENT).expect("ctx-demo fragment must parse")
    }

    /// The bare `GString` channel of a single-expr `Par`, or `None`.
    fn send_channel_gstring(send: &models::rhoapi::Send) -> Option<String> {
        gstring_value(send.chan.as_ref()?)
    }

    #[test]
    fn contextual_join_unary_is_the_sigma_receiver_frame() {
        // n = 1: `for( (T, out) <- c_ctx ){ out!(⟦Wrap(T)⟧) }`. The single-premise join is
        // BYTE-IDENTICAL to `sigma_receiver_par(1, ⟦Wrap(T)⟧, c_ctx)` — the reduced hole T is
        // the one σ-slot and the context Wrap(_) is the RHS.
        let fp = "ctxfp";
        let context_rhs =
            reflect_term_par(&apply("Wrap", vec![var_pattern("T")]), &[ident("T")], 1, fp, None)
                .expect("Wrap(T) reflects");
        let c_ctx = new_gstring_par("c_ctx".to_string(), Vec::new(), false);

        let join = contextual_join_receiver_par(context_rhs.clone(), &[c_ctx.clone()]);
        let sigma = sigma_receiver_par(1, context_rhs, c_ctx);
        assert_eq!(join, sigma, "the unary contextual join is the k=1 σ-receiver frame");

        // Structure: one persistent receive, one bind on c_ctx binding [hole, out].
        assert_eq!(join.receives.len(), 1);
        let receive = &join.receives[0];
        assert!(receive.persistent, "the contextual join must self-reinstall (persistent)");
        assert_eq!(receive.bind_count, 2, "1 reduced hole + out");
        assert_eq!(receive.binds.len(), 1, "one premise channel ⇒ one bind");
        assert_eq!(receive.binds[0].free_count, 2);
        assert_eq!(
            receive.binds[0].patterns.len(),
            2,
            "the last (only) bind carries the hole and the out channel"
        );

        // Body: out!(⟦Wrap(T)⟧) with out = BoundVar(0) and the hole at BoundVar(1).
        let body = receive.body.as_ref().expect("join body");
        assert_eq!(body.sends.len(), 1);
        let send = &body.sends[0];
        assert_eq!(
            boundvar_index(send.chan.as_ref().expect("out channel")),
            Some(0),
            "the join emits on the dynamic out channel (BoundVar(0))"
        );
        // The emitted context is ⟦Wrap(T)⟧ = EList[tag_Wrap, BoundVar(1)].
        let list = elist_body(&send.data[0]);
        assert_eq!(
            &list.ps[0],
            &GPrivateBuilder::new_par_from_string(reflect_tag(fp, "Wrap")),
            "the reduced context head is the Wrap reflection tag"
        );
        assert_eq!(
            boundvar_index(&list.ps[1]),
            Some(1),
            "the reduced hole T sits at BoundVar(rhs_var_index(1,0)) = BoundVar(1)"
        );
    }

    #[test]
    fn contextual_join_binary_builds_two_binds() {
        // n = 2: `for( T0 <- c0 ; (T1, out) <- c1 ){ out!(⟦Pair(T0, T1)⟧) }`. Two premise
        // channels ⇒ two binds; the out channel rides the LAST bind.
        let fp = "ctxfp";
        let context_rhs = reflect_term_par(
            &apply("Pair", vec![var_pattern("T0"), var_pattern("T1")]),
            &[ident("T0"), ident("T1")],
            2,
            fp,
            None,
        )
        .expect("Pair(T0, T1) reflects");
        let c0 = new_gstring_par("c0".to_string(), Vec::new(), false);
        let c1 = new_gstring_par("c1".to_string(), Vec::new(), false);

        let join = contextual_join_receiver_par(context_rhs, &[c0, c1]);
        assert_eq!(join.receives.len(), 1);
        let receive = &join.receives[0];
        assert_eq!(receive.bind_count, 3, "2 reduced holes + out");
        assert_eq!(receive.binds.len(), 2, "two premise channels ⇒ two binds");

        // Bind 0 (c0): one hole, LOCAL free var 0.
        assert_eq!(receive.binds[0].free_count, 1);
        assert_eq!(receive.binds[0].patterns.len(), 1, "a non-last bind carries only its hole");
        assert_eq!(send_channel_gstring_of_bind(&receive.binds[0]), Some("c0".to_string()));
        // Bind 1 (c1): hole + out, LOCAL free vars 0, 1.
        assert_eq!(receive.binds[1].free_count, 2);
        assert_eq!(
            receive.binds[1].patterns.len(),
            2,
            "the last bind also carries the out channel"
        );
        assert_eq!(send_channel_gstring_of_bind(&receive.binds[1]), Some("c1".to_string()));

        // Body: out!(⟦Pair(T0, T1)⟧) with hole i = BoundVar(2 - i), out = BoundVar(0).
        let body = receive.body.as_ref().expect("join body");
        let list = elist_body(&body.sends[0].data[0]);
        assert_eq!(
            boundvar_index(&list.ps[1]),
            Some(2),
            "hole T0 at BoundVar(n - 0) = BoundVar(2)"
        );
        assert_eq!(
            boundvar_index(&list.ps[2]),
            Some(1),
            "hole T1 at BoundVar(n - 1) = BoundVar(1)"
        );
    }

    fn send_channel_gstring_of_bind(bind: &ReceiveBind) -> Option<String> {
        gstring_value(bind.source.as_ref()?)
    }

    #[test]
    fn contextual_rewrite_materializes_an_atomic_join() {
        let def = ctx_demo_def();
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        let par = lowered
            .rules()
            .iter()
            .find_map(|rule| match rule {
                RhoNetLoweredRule::ContextualRewrite { rule_id, par }
                    if rule_id == "rule:rewrite:1:WrapCong" =>
                {
                    Some(par)
                },
                _ => None,
            })
            .expect("WrapCong must materialize to a ContextualRewrite join");

        assert_eq!(par.receives.len(), 1, "the contextual join is one persistent receive");
        let receive = &par.receives[0];
        assert_eq!(receive.bind_count, 2, "1 premise hole + out");
        assert_eq!(receive.binds.len(), 1, "one congruence premise ⇒ one bind");
        // The join binds the premise location channel (`input_channels[1..]`).
        let channel = send_channel_gstring_of_bind(&receive.binds[0]).expect("premise channel");
        assert!(
            channel.contains("contextual-premise"),
            "the join binds the premise location channel, got {channel}"
        );
        // Body emits ⟦Wrap(T)⟧ on the dynamic out channel.
        let body = receive.body.as_ref().expect("join body");
        let list = elist_body(&body.sends[0].data[0]);
        let fp = &program.language_fingerprint;
        assert_eq!(
            &list.ps[0],
            &GPrivateBuilder::new_par_from_string(reflect_tag(fp, "Wrap")),
            "the reduced context is Wrap(_)"
        );
        assert!(lowered.errors().is_empty(), "a clean congruence rewrite must not error");
    }

    #[test]
    fn contextual_rewrite_with_side_condition_fails_closed() {
        // A congruence rule carrying a non-congruence side condition (a relation query) has
        // no flat join slot for that premise — it must stay `Unsupported`, not silently drop
        // the side condition.
        let mut def = scalar_def();
        def.rewrites.push(RewriteRule {
            name: ident("GuardedCong"),
            type_context: Vec::new(),
            premises: vec![
                Premise::Congruence { source: ident("S"), target: ident("T") },
                Premise::RelationQuery {
                    relation: ident("ok"),
                    args: vec![ident("S")],
                },
            ],
            left: apply("Wrap", vec![var_pattern("S")]),
            right: apply("Wrap", vec![var_pattern("T")]),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:0:GuardedCong")
            .expect("GuardedCong must be lowered");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::Unsupported {
                rule_id: "rule:rewrite:0:GuardedCong".to_string(),
                family: UnsupportedFamily::NonCongruenceSideCondition,
            },
            "a mixed-premise congruence rule fails closed on its side condition"
        );
    }

    #[test]
    fn contextual_injection_sites_derive_the_wrapcong_site() {
        let def = ctx_demo_def();
        let sites = rho_net_contextual_injection_sites(&def);
        assert_eq!(sites.len(), 1, "exactly one contextual join (WrapCong)");
        let site = &sites[0];
        assert_eq!(site.rule_label, "WrapCong");
        assert_eq!(site.premise_channels.len(), 1, "one congruence premise ⇒ one channel");
        assert!(
            site.premise_channels[0].contains("contextual-premise"),
            "the site's premise channel is the contextual-premise location channel, got {}",
            site.premise_channels[0]
        );
    }

    #[test]
    fn contextual_contract_call_delivers_hole_and_out() {
        // The unary injection: c_ctx!(⟦Pair(B, A)⟧, @"OUT").
        let fp = "ctxfp";
        let hole = reflect_ground_term_par(
            &GroundTerm::new("Pair", vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")]),
            fp,
        );
        let call = contextual_contract_call(&["c_ctx"], vec![hole.clone()], "OUT");
        assert_eq!(call.sends.len(), 1, "one premise ⇒ one delivery send");
        let send = &call.sends[0];
        assert_eq!(send_channel_gstring(send), Some("c_ctx".to_string()));
        assert_eq!(send.data.len(), 2, "the (only, last) send carries the hole and @out");
        assert_eq!(&send.data[0], &hole, "the reduced hole ⟦Pair(B, A)⟧");
        assert_eq!(
            gstring_value(&send.data[1]),
            Some("OUT".to_string()),
            "the dynamic out channel"
        );
    }

    #[test]
    fn contextual_contract_call_binary_puts_out_on_the_last_channel() {
        let fp = "ctxfp";
        let h0 = reflect_ground_term_par(&GroundTerm::nullary("A"), fp);
        let h1 = reflect_ground_term_par(&GroundTerm::nullary("B"), fp);
        let call = contextual_contract_call(&["c0", "c1"], vec![h0, h1], "OUT");
        assert_eq!(call.sends.len(), 2, "two premises ⇒ two delivery sends");
        // Sends land in premise order; find by channel to be robust to `append` order.
        let on = |name: &str| {
            call.sends
                .iter()
                .find(|s| send_channel_gstring(s).as_deref() == Some(name))
        };
        assert_eq!(
            on("c0").expect("c0 send").data.len(),
            1,
            "a non-last send carries only its hole"
        );
        let last = on("c1").expect("c1 send");
        assert_eq!(last.data.len(), 2, "the last send also carries @out");
        assert_eq!(gstring_value(&last.data[1]), Some("OUT".to_string()));
    }

    #[test]
    fn reconstruct_contractum_instantiates_the_premise_rhs() {
        // The premise `Flip: Swap(x, y) ~> Pair(y, x)` under σ = {x ↦ A, y ↦ B} produces the
        // reduced hole T = Pair(B, A) — the contractum a contextual join plugs into Wrap(_).
        let def = ctx_demo_def();
        let sigma = vec![
            ("x".to_string(), GroundTerm::nullary("A")),
            ("y".to_string(), GroundTerm::nullary("B")),
        ];
        let contractum =
            reconstruct_contractum(&def, "Flip", &sigma).expect("Flip contractum reconstructs");
        assert_eq!(
            contractum,
            GroundTerm::new("Pair", vec![GroundTerm::nullary("B"), GroundTerm::nullary("A")]),
            "RHS(Flip)[σ] = Pair(σ[y], σ[x]) = Pair(B, A)"
        );
    }

    #[test]
    fn installed_program_admits_a_contextual_join() {
        // The whole ctx-demo language installs: the base Flip σ-receiver AND the WrapCong
        // contextual join compose into one installable program (no fail-closed diagnostic).
        let def = ctx_demo_def();
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        assert!(lowered.errors().is_empty(), "ctx-demo lowers cleanly: {:?}", lowered.errors());
        let installed = lowered
            .installed_program_par()
            .expect("the base rewrite + contextual join install together");
        // Two persistent receives: the Flip base σ-receiver and the WrapCong contextual join.
        assert_eq!(
            installed.receives.len(),
            2,
            "installed = Flip σ-receiver ∥ WrapCong contextual join"
        );
    }

    #[test]
    fn contextual_premise_hole_channel_prefixes_ph() {
        // The intermediate channel is DISJOINT from the join's own premise channel (the `ph:`
        // prefix), so the σ-receiver firing and the join never race for one send.
        assert_eq!(contextual_premise_hole_channel("c_ctx"), "ph:c_ctx");
        assert_ne!(contextual_premise_hole_channel("c_ctx"), "c_ctx");
    }

    #[test]
    fn contextual_hole_bridge_reroutes_the_reduced_hole_to_the_premise_channel() {
        // Stage 4 S-contextual: the UNARY bridge `for (T <- ph:c_ctx) { c_ctx!(T, @OUT) }` — the
        // LAST (unary) hole carries @out, satisfying the join's `(T_0, out)` bind ABI.
        let bridge = contextual_hole_bridge_par("ph:c_ctx", "c_ctx", Some("OUT"));
        assert_eq!(bridge.receives.len(), 1, "one bridge receive");
        let receive = &bridge.receives[0];
        assert!(!receive.persistent, "the hole bridge is one-shot (a single located hole)");
        assert_eq!(receive.bind_count, 1, "binds the single reduced hole T");
        assert_eq!(receive.binds.len(), 1);
        assert_eq!(
            send_channel_gstring_of_bind(&receive.binds[0]),
            Some("ph:c_ctx".to_string()),
            "the bridge reads the reduced hole off the intermediate ph: channel"
        );
        let body = receive.body.as_ref().expect("bridge body");
        assert_eq!(body.sends.len(), 1, "one re-delivery send");
        let send = &body.sends[0];
        assert_eq!(
            send_channel_gstring(send),
            Some("c_ctx".to_string()),
            "the bridge re-delivers on the join's premise channel"
        );
        assert_eq!(send.data.len(), 2, "the last hole carries the reduced hole T and @out");
        assert_eq!(
            gstring_value(&send.data[1]),
            Some("OUT".to_string()),
            "the dynamic out channel rides the last premise send"
        );
    }

    #[test]
    fn contextual_hole_bridge_non_last_omits_the_out_channel() {
        // A non-last hole (n-ary, the next sub-slice) carries only its hole: `for (T <- ph:c0) {
        // c0!(T) }` — matching the join's non-last single-slot bind.
        let bridge = contextual_hole_bridge_par("ph:c0", "c0", None);
        let send = &bridge.receives[0].body.as_ref().expect("body").sends[0];
        assert_eq!(send.data.len(), 1, "a non-last hole carries only its reduced hole");
        assert_eq!(send_channel_gstring(send), Some("c0".to_string()));
    }

    #[test]
    fn contextual_match_entries_mirror_the_injection_sites() {
        // The match entries carry the SAME rule label + premise channels the installed join was
        // compiled with (the coherence anchor), so the routed hole lands on the join's channel.
        let def = ctx_demo_def();
        let entries = rho_net_contextual_match_entries(&def);
        let sites = rho_net_contextual_injection_sites(&def);
        assert_eq!(entries.len(), 1, "one contextual family (WrapCong)");
        assert_eq!(entries[0].fired_rule_label, "WrapCong");
        assert_eq!(
            entries[0].premise_channels, sites[0].premise_channels,
            "the match entry carries the join's premise channels verbatim"
        );
    }
}
