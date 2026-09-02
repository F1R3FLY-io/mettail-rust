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

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use mettail_ast::language::{
    Equation, FreshnessCondition, FreshnessTarget, LanguageDef, Premise, RewriteRule,
};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_ast::types::{CollectionType, EvalMode, TypeExpr};
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
use crate::rho_net_location::{SubjectLocationIndex, SubjectPosition};

/// Source-construct family that is out of scope for σ-receiver lowering this
/// slice. Every variant is a genuine, fail-closed classification reached by
/// pattern-tree or premise inspection — never a placeholder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnsupportedFamily {
    /// A collection literal `{P, Q, ...rest}` (associative-commutative match).
    CollectionAc,
    /// An indexed positional element `args[i := S]` over an ORDERED (`Vec`) payload.
    ///
    /// ⚠ DELIBERATELY NOT [`Self::CollectionAc`]. That variant is routed into the A-S5.5
    /// AC-CARRIER transcription (`rho_net_drive.rs:366`, `rho_net_lower.rs:943`), whose
    /// matching is ASSOCIATIVE-COMMUTATIVE — it is licensed to PERMUTE the payload. An
    /// indexed `Vec` element is the exact opposite: its whole purpose is that position is
    /// PRESERVED, so every other argument stays where it was. Reusing the AC rejection
    /// would hand an ordered pattern to a carrier allowed to reorder it — a semantic bug
    /// no type would catch. Failing closed under its own name keeps the limitation
    /// visible and stops the wrong carrier from claiming it.
    IndexedVecOrdered,
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
    /// INDEPENDENTLY (native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders)
    /// and fires `⟦R⟧σ` on the
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
    /// A DEPTH-2 NESTED structural non-linear AC rewrite (Stage 4 — the Ambient-calculus
    /// `InRule`/`OutRule`, `{ n[{in(m,P), ...q}], m[R], ...s } ~> { m[{ n[{P, ...q}], R }], ...s }`
    /// and its `out` dual) un-skipped to a nested σ-receiver ([`nested_structural_ac_rule_receiver`]).
    /// GENERALIZES [`Self::StructuralAcRewrite`]: the connective pattern matches a DEPTH-2 nested bag
    /// (an element whose argument is itself a HashBag carrying the capability) ORDER-INDEPENDENTLY at
    /// every level, and a DEPTH-AGNOSTIC `Receive.condition` `EEq(M_outer, M_inner)` enforces the
    /// CROSS-LEVEL shared channel `M ≡ M` (reject-safe). UNLIKE the flat structural-AC rewrite the RHS
    /// reduct is a NESTED re-assembly (never a bare LHS var), so the body splices the host-computed
    /// reduct element(s) — reflected from σ by walking a [`AcReconstructTemplate`] and delivered via
    /// the SAME [`structural_ac_contract_call`] seam ([`rho_net_nested_structural_ac_injection_sites`]).
    /// Gated to binder-free languages (empty `equations`); a `new`-scoped language (the full
    /// `Ambient`) keeps its In/Out on the untyped binder-congruence path and stays `Unsupported`.
    NestedStructuralAcRewrite { rule_id: String, par: Par },
    /// A-S5.8 (F8-AM-1b): a recognized DEPTH-2 nested structural-AC rewrite whose RHS
    /// reduct templates INTRODUCE a binder ([`AcReconstructTemplate::Binder`] — the
    /// constructive-discharge witness shape `… ~> op{ B(^x. …), … }`) — the fail-closed
    /// NO-MATCH-ENTRY disposition, RECORDED, NEVER an install error.
    ///
    /// The site-keyed match receiver cannot carry the rule: the F8-AM-1c σ-slot shift rule
    /// requires each slot value under `k` template binders to be pre-shifted by `k`
    /// applications of the ASYNC `^shift(Z, ·)` receiver, and a value-position reduct
    /// rebuild ([`reflect_ac_template_bound_par`]) cannot inline an async COMM. So the rule
    /// contributes NO receiver `Par`, surfaces in NO match entry / injection site (the
    /// locate-all match paths stay fail-closed for it — the A-S2 static gate keeps
    /// deferring it), and never blocks [`RhoNetLowered::installed_program_par`] (like the
    /// other recognized no-`Par` dispositions). Its FIRING mechanism is the A-S5.8 DRIVE
    /// carrier ([`crate::rho_net_drive`]), which pre-computes the shifted σ slots on fresh
    /// channels before its join and emits the ctor-erased `⌜^lambda⌝` node — the drive
    /// admission discharges the static-gate defer for exactly this driver-transcribable
    /// shape (`drive_admissible`, the A-S5.8 conjunct-1 refinement).
    NestedStructuralAcBinderTemplated { rule_id: String },
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
    /// A congruence (contextual) rewrite whose flat join image FAILED to materialize
    /// (binder / collection / dangling-passenger context / unenforceable premise —
    /// exactly the reasons that fail [`Self::ContextualRewrite`] closed) but whose
    /// premise set is NON-EMPTY and ALL-congruence ([`congruence_only_premises`]):
    /// the A-S5.1 (leg i) install-EXEMPT disposition — RECORDED, NEVER SILENT.
    ///
    /// Like [`Self::CongruenceClosure`] it contributes no `Par` and never blocks
    /// [`RhoNetLowered::installed_program_par`], because a congruence-only rewrite
    /// declares no motion of its own — it only closes a context around premise
    /// reductions, and that context closure is already carried WITHOUT a dedicated
    /// receiver: by the locate-all / driver descent IN RHO (every candidate subterm
    /// position is visited and its redex fired at its own site) and by the e-graph
    /// congruence closure on the host (Dovetail) paths (a congruence label is never
    /// a fired-rule label — the same fact the A-S2 static gate's exemption rests
    /// on). The failed [`UnsupportedFamily`] is retained as the recorded WHY and
    /// surfaced by [`RhoNetLowered::congruence_exempt_rules`] plus the A-S5c family
    /// table — an exemption is evidence, never an omission.
    ///
    /// A lowering failure on a rewrite with ANY non-congruence premise (mixed
    /// premises) stays [`Self::Unsupported`] with a fail-closed diagnostic: its
    /// side condition has no in-Rho image and must never be silently dropped.
    ///
    /// FV: `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
    /// (`Section CongruenceExemptInstallBoundary`,
    /// `install_admits_iff_no_nonexempt_unlowered`).
    CongruenceExemptRewrite {
        rule_id: String,
        family: UnsupportedFamily,
    },
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
            | Self::NestedStructuralAcRewrite { rule_id, .. }
            | Self::NestedStructuralAcBinderTemplated { rule_id }
            | Self::ContextualRewrite { rule_id, .. }
            | Self::SubstRewrite { rule_id, .. }
            | Self::NativeSystemProcessRewrite { rule_id, .. }
            | Self::StructuralConstructor { rule_id }
            | Self::CongruenceClosure { rule_id }
            | Self::CongruenceExemptRewrite { rule_id, .. }
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
            | Self::NestedStructuralAcRewrite { par, .. }
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
    /// The generated de-Bruijn subst/shift TRS program (Stage 4 S-binder SLICE 2a): the five
    /// reserved receivers ([`crate::rho_net_subst_trs::subst_trs_program_par`]) that drive the in-Rho
    /// β cascade. `Some` iff the language carries a `SubstRewrite`; installed ONCE (appended by
    /// [`Self::installed_program_par`]) alongside the β SEED σ-receiver — persistent, on disjoint
    /// reserved roots, disturbing no landed receiver.
    subst_trs: Option<Par>,
    /// The generated in-Rho quiescence-DRIVER program (A-S5.2, plan v2 §4): the persistent
    /// `^drive` receiver family ([`crate::rho_net_drive::drive_program_par`]) that normalizes
    /// a seeded reflected subject to quiescence fully in-Rho — redex arms firing through the
    /// EXISTING σ ABI, congruence-descent arms with the post-join re-check, the binder arm,
    /// leaf/reserved passthroughs, and the typed `^drive-err` wildcard. `Some` iff
    /// [`drive_admission`](Self::drive_admission) is
    /// [`DriveAdmission::Admitted`](crate::rho_net_drive::DriveAdmission::Admitted); appended
    /// ONCE by [`Self::installed_program_par`] — persistent, on a disjoint reserved root,
    /// disturbing no landed receiver.
    drive: Option<Par>,
    /// The RECORDED driver-admission disposition (A-S5.2, plan v2 §4.4 / F9): `Admitted` /
    /// `NotRequested` (not opted in — every non-`DRIVE_OPT_IN` language, zero-cost) /
    /// `Unsupported { reason }` (opted in, but the static gate rejects, a matching family is
    /// not yet driver-supported, or a seed does not transcribe). Recorded-never-silent, the
    /// same discipline as [`Self::congruence_exempt_rules`].
    drive_admission: crate::rho_net_drive::DriveAdmission,
    /// The generated in-Rho `^float` receiver family (A-S5.8): the per-iteration binder-float
    /// canonicalizer — the `^float` dispatcher, the equation-derived `^float-hoist:{C}` /
    /// `^float-merge:{op}` satellites, and (first-time, when the language carries no subst
    /// TRS) the shared `^shift`/`^cmp` satellites
    /// ([`crate::rho_net_float::float_program_par`]). `Some` iff the language passes the
    /// A-S5.8 gate: [`language_has_float_handler`] ∧ [`equations_boundary_canonicalizable`]
    /// ∧ [`Self::drive_admission`] is `Admitted` (bundled corpus: exactly the production
    /// Ambient). Appended ONCE by [`Self::installed_program_par`] — persistent, on disjoint
    /// reserved roots, disturbing no landed receiver.
    float: Option<Par>,
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

    /// The congruence-exempt unmaterialized rewrites (A-S5.1 leg i), each as
    /// `(rule_id, the failed lowering family)` — the RECORDED-never-silent
    /// diagnostic surface for [`RhoNetLoweredRule::CongruenceExemptRewrite`].
    /// These rules contribute no receiver `Par` and never block
    /// [`Self::installed_program_par`]; their context closure is carried by the
    /// locate-all / driver descent in Rho and by the e-graph congruence closure
    /// on host paths. Empty for every language whose contextual lowerings all
    /// materialize (e.g. SwapDemo / CtxDemo / BiCongDemo).
    pub fn congruence_exempt_rules(&self) -> Vec<(&str, &UnsupportedFamily)> {
        self.rules
            .iter()
            .filter_map(|rule| match rule {
                RhoNetLoweredRule::CongruenceExemptRewrite { rule_id, family } => {
                    Some((rule_id.as_str(), family))
                },
                _ => None,
            })
            .collect()
    }

    /// The RECORDED in-Rho quiescence-driver admission disposition (A-S5.2, plan v2 §4.4 /
    /// F9). `Admitted` iff [`Self::drive`] carries the generated `^drive` receiver family.
    pub fn drive_admission(&self) -> &crate::rho_net_drive::DriveAdmission {
        &self.drive_admission
    }

    /// The generated in-Rho quiescence-driver program (`Some` iff
    /// [`Self::drive_admission`] is `Admitted`).
    pub fn drive(&self) -> Option<&Par> {
        self.drive.as_ref()
    }

    /// The generated in-Rho `^float` receiver family (A-S5.8; `Some` iff the language
    /// passes the float gate — see the [`Self`] field docs).
    pub fn float(&self) -> Option<&Par> {
        self.float.as_ref()
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
    /// `StructuralConstructor` / `CongruenceClosure` / `CongruenceExemptRewrite`
    /// legitimately contribute no `Par` (inline RHS reflection / compile-time
    /// e-graph closure / the A-S5.1 recorded congruence exemption — see
    /// [`RhoNetLoweredRule::CongruenceExemptRewrite`]) and never block the
    /// install. Formal model:
    /// `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
    /// (`Section RhoNetInstallBoundary` + `Section CongruenceExemptInstallBoundary`).
    pub fn installed_program_par(&self) -> Result<Par, RhoNetInstallError> {
        // E-3 Stage-0: SELF-time phase span (no-op without an active collection window).
        let _installed_program_par_span = crate::pipeline_spans::phase_span(
            crate::pipeline_spans::PipelinePhase::InstalledProgramPar,
        );
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
                | RhoNetLoweredRule::NestedStructuralAcRewrite { .. }
                // A-S5.8 (F8-AM-1b): a binder-templated nested-AC rewrite is a RECORDED
                // NO-MATCH-ENTRY disposition, not silently dropped work — its firing
                // mechanism is the A-S5.8 drive carrier (which pre-shifts σ slots async),
                // so no receiver is missing from the installed program.
                | RhoNetLoweredRule::NestedStructuralAcBinderTemplated { .. }
                | RhoNetLoweredRule::ContextualRewrite { .. }
                | RhoNetLoweredRule::SubstRewrite { .. }
                | RhoNetLoweredRule::NativeSystemProcessRewrite { .. }
                | RhoNetLoweredRule::StructuralConstructor { .. }
                | RhoNetLoweredRule::CongruenceClosure { .. }
                // A-S5.1 (leg i): a congruence-exempt unmaterialized rewrite is a
                // RECORDED disposition (`congruence_exempt_rules`), not silently
                // dropped work — its context closure is carried by the locate-all /
                // driver descent in Rho and the e-graph congruence closure on host
                // paths, so no receiver is missing from the installed program.
                | RhoNetLoweredRule::CongruenceExemptRewrite { .. } => continue,
            };
            return Err(RhoNetInstallError::UnmaterializedRule {
                rule_id: rule.rule_id().to_string(),
                family,
            });
        }
        let mut program =
            self.rules
                .iter()
                .fold(Par::default(), |program, rule| match rule.par() {
                    Some(par) => program.append(par.clone()),
                    None => program,
                });
        // Stage 4 S-binder SLICE 2a: append the generated de-Bruijn subst/shift TRS ONCE (the five
        // reserved receivers that drive the in-Rho β cascade), so the β SEED σ-receiver's
        // `^subst(⟦Z⟧, a, b, out)` self-drives to the β-normal form on `out`. Persistent + disjoint
        // reserved roots — disturbs no landed base/AC/contextual/native receiver.
        if let Some(trs) = &self.subst_trs {
            program = program.append(trs.clone());
        }
        // A-S5.2 (leg v): append the in-Rho quiescence-DRIVER receiver family ONCE for
        // driver-admitted languages (the subst-TRS append pattern above) — persistent, on the
        // disjoint reserved `^drive` root, disturbing no landed receiver. Non-admitted
        // languages append nothing (their installed program is byte-identical to pre-A-S5.2);
        // the disposition is RECORDED in [`Self::drive_admission`], never silent.
        if let Some(drive) = &self.drive {
            program = program.append(drive.clone());
        }
        // A-S5.8: append the in-Rho `^float` receiver family ONCE for languages passing the
        // float gate (float-bearing ∧ drive-admitted — bundled corpus: exactly Ambient), the
        // third `Option<Par>` beside `subst_trs`/`drive`. Persistent, on the disjoint
        // reserved `^float`/`^float-hoist:{C}`/`^float-merge:{op}` roots (plus the shared
        // `^shift`/`^cmp` when the language installs them here first-time); non-float
        // languages append nothing — their installed program is byte-identical to pre-A-S5.8.
        if let Some(float) = &self.float {
            program = program.append(float.clone());
        }
        Ok(program)
    }
}

impl RhoNetProgram {
    /// Lower this planning artifact to concrete Rho AST under the corrected
    /// set-automaton-assisted model. See the module documentation.
    pub fn lower_to_par(&self, def: &LanguageDef, lowering: &RhoLowering) -> RhoNetLowered {
        // E-3 Stage-0: SELF-time phase span (no-op without an active collection window).
        // DRIVE_OPT_IN languages re-enter `compile_in_rho_matching_ruleset` from
        // `drive_lowering` inside this call (EM-4); that nested activation is attributed
        // to the ruleset phase and excluded from this span's self time.
        let _lower_to_par_span =
            crate::pipeline_spans::phase_span(crate::pipeline_spans::PipelinePhase::LowerToPar);
        // PRODUCTION always lowers under `AllRedrive` — every emitted driver Par is
        // byte-identical to pre-E-1 (the a_s5_6 / a_s5_8 byte pins guard this).
        let manifest = crate::rho_net_coinstall::CoInstallManifest::isolated(def);
        lower(self, def, lowering, crate::rho_net_drive::ScionPolicy::AllRedrive, &manifest)
    }

    /// Lower this language for installation beside the foreign languages recorded
    /// in `manifest`.
    ///
    /// The manifest changes only the persistent drive/substitution machines: ordinary
    /// contracts and isolated-language lowering remain byte-identical.  A manifest
    /// derived for a different host fails closed before any partial artifact is built.
    pub fn lower_to_par_with_coinstall_manifest(
        &self,
        def: &LanguageDef,
        lowering: &RhoLowering,
        manifest: &crate::rho_net_coinstall::CoInstallManifest,
    ) -> Result<RhoNetLowered, String> {
        manifest.validate_host(&self.language_fingerprint)?;
        let _lower_to_par_span =
            crate::pipeline_spans::phase_span(crate::pipeline_spans::PipelinePhase::LowerToPar);
        Ok(lower(
            self,
            def,
            lowering,
            crate::rho_net_drive::ScionPolicy::AllRedrive,
            manifest,
        ))
    }

    /// E-1 `bench-scion` surface (design v1 §3.6): lower under a chosen [`ScionPolicy`], so
    /// the measurement harness can build the TREATMENT installed program (positional
    /// `BaseRewrite` arms scion'd) alongside the CONTROL ([`Self::lower_to_par`], all
    /// re-drive). Feature-gated: production never reaches it, and `DRIVE_OPT_IN` is
    /// untouched.
    #[cfg(feature = "bench-scion")]
    pub fn lower_to_par_with_scion_policy(
        &self,
        def: &LanguageDef,
        lowering: &RhoLowering,
        scion_policy: crate::rho_net_drive::ScionPolicy,
    ) -> RhoNetLowered {
        let _lower_to_par_span =
            crate::pipeline_spans::phase_span(crate::pipeline_spans::PipelinePhase::LowerToPar);
        let manifest = crate::rho_net_coinstall::CoInstallManifest::isolated(def);
        lower(self, def, lowering, scion_policy, &manifest)
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
    scion_policy: crate::rho_net_drive::ScionPolicy,
    coinstall: &crate::rho_net_coinstall::CoInstallManifest,
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

    // Stage 4 S-binder SLICE 2a: if any rule lowered to a β SEED `SubstRewrite`, build the generated
    // de-Bruijn subst/shift TRS ONCE (`^cmp`/`^pred`/`^shiftk` fixed + `^subst`/`^shift` with `def`'s
    // object-congruence arms). It is installed alongside the SEED σ-receivers to drive the in-Rho β
    // cascade.
    let subst_trs = rules
        .iter()
        .any(|rule| matches!(rule, RhoNetLoweredRule::SubstRewrite { .. }))
        .then(|| {
            crate::rho_net_subst_trs::subst_trs_program_par_with_coinstall_manifest(
                def,
                &program.language_fingerprint,
                coinstall,
            )
        });

    // A-S5.2 (leg v): the in-Rho quiescence-driver lowering — admission is decided (and
    // RECORDED) here, and the `^drive` receiver family is built for admitted languages. The
    // opt-in check is a name comparison against `crate::rho_net_drive::DRIVE_OPT_IN`
    // (AM-4), so every non-opted-in language takes the `NotRequested` arm at zero cost and
    // its lowering artifact is byte-identical to pre-A-S5.2.
    let (drive, drive_admission) = crate::rho_net_drive::drive_lowering(
        def,
        program,
        &rules,
        &errors,
        &rewrite_by_id,
        scion_policy,
        coinstall,
    );

    // A-S5.8: the in-Rho `^float` receiver family — generated + installed iff the language
    // passes the float gate (`language_has_float_handler` ∧
    // `equations_boundary_canonicalizable` ∧ drive Admitted). The `^shift`/`^cmp` shared
    // satellites join the family exactly when the language installs no subst TRS (Ambient:
    // first-time install — no `SubstRewrite`); a language whose TRS already carries them
    // never double-installs a reserved receiver.
    let float = (matches!(drive_admission, crate::rho_net_drive::DriveAdmission::Admitted)
        && crate::rho_net_float::language_is_float_bearing(def))
    .then(|| {
        crate::rho_net_float::float_program_par(
            def,
            &program.language_fingerprint,
            subst_trs.is_none(),
            coinstall,
        )
    });

    RhoNetLowered {
        language_fingerprint: program.language_fingerprint.clone(),
        rules,
        errors,
        subst_trs,
        drive,
        drive_admission,
        float,
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
            if let Some(par) = source.clone().and_then(|source| {
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
            // Stage 4: a DEPTH-2 NESTED structural non-linear AC rewrite (Ambient's `InRule`/`OutRule`
            // — a nested `PAmb N (PPar {…})` element carrying the cross-level capability
            // `in(m,·)`/`out(m,·)`) → a nested σ-receiver whose DEPTH-AGNOSTIC `Receive.condition`
            // `EEq(M_outer, M_inner)` enforces the cross-level channel and whose body splices the
            // host-computed reduct element(s) with the outer `rest`. A-S5.4b (design v2 §3.2): GATED
            // by [`equations_boundary_canonicalizable`] — a binder-free language (empty `equations`,
            // e.g. `InOutDemo`) admits as before, and a language whose EVERY equation is a
            // recognized BINDER-FLOAT congruence discharged by the generated unconditional
            // unbind-first float at the invocation boundary (the full `Ambient`: `NewComm` +
            // `ScopeExtrusion` + the corrected capability-float trio + `AmbNew`) NOW admits too —
            // the boundary canonicalization (`binder_congruence_nf_term` before M-reflect) exposes
            // every redex modulo the equational theory syntactically (FV:
            // `BinderFloatCanonicalization.v`), so the nested receiver sees float-canonical
            // subjects. Any OTHER equation keeps the fail-closed decline (stays `Unsupported`).
            if equations_boundary_canonicalizable(def) {
                // A-S5.8 (F8-AM-1b): a RECOGNIZED nested shape whose reduct templates
                // introduce a binder takes the fail-closed NO-MATCH-ENTRY disposition
                // BEFORE the receiver build — recorded, no `Par`, no install error (the
                // firing mechanism is the A-S5.8 drive carrier; the site-keyed receiver
                // cannot inline the async `^shift` the F8-AM-1c σ-slot shift rule needs).
                if let Some(shape) =
                    nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, def)
                {
                    if shape
                        .reduct_templates
                        .iter()
                        .any(AcReconstructTemplate::contains_binder)
                    {
                        return Some(RhoNetLoweredRule::NestedStructuralAcBinderTemplated {
                            rule_id: rule.id.clone(),
                        });
                    }
                }
                if let Some(par) = source.and_then(|source| {
                    nested_structural_ac_rule_receiver(
                        &rewrite.left,
                        &rewrite.right,
                        source,
                        language_fingerprint,
                        def,
                    )
                }) {
                    return Some(RhoNetLoweredRule::NestedStructuralAcRewrite {
                        rule_id: rule.id.clone(),
                        par,
                    });
                }
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

/// The shape of a binder/β-substitution base rewrite `LHS ~> subst(scope, x := repl)`: the LHS
/// σ-variables (first-occurrence order, binder-excluded — the order [`lower_lhs_vars`] collects
/// them), the SCOPE variable (the `scope`/`term` of the RHS `Subst`/`MultiSubst`, the lambda body
/// `b`), and the REPLACEMENT variable (the `replacements[0]`/`replacement`, the argument `a`) —
/// BOTH of which must be bound LHS variables (their σ slots carry the captured body + argument the
/// in-Rho β SEED threads into `^subst(⟦Z⟧, a, b, out)`, Stage 4 SLICE 2a). Returns `None` unless the
/// RHS is a top-level substitution whose scope AND replacement are bound LHS variables — a
/// non-variable / open scope or replacement, or a LHS with no flat σ image, declines here and the
/// caller fails closed.
///
/// This is the SINGLE subst-LHS/RHS extraction shared by [`lower_subst_rewrite`] (which materializes
/// the installed β SEED σ-receiver) and [`rho_net_subst_injection_sites`] (which surfaces the runtime
/// subst injection site), so both agree byte-for-byte on the σ order + the scope/replacement slots.
/// The AC/contextual analogue of [`ac_rule_shape`].
pub(crate) fn subst_rule_shape(
    left: &Pattern,
    right: &Pattern,
) -> Option<(Vec<Ident>, Ident, Ident)> {
    // Extract the scope (`b`) and the replacement (`a`) from the top-level substitution RHS. A
    // `MultiSubst` β-substitution has exactly one replacement (`(eval fun arg)` = `MultiSubst{scope:
    // fun, replacements: [arg]}`); a 3-arg `Subst{term, var, replacement}` carries the replacement
    // directly. Both must be BARE variables.
    let (scope, replacement) = match right {
        Pattern::Term(PatternTerm::MultiSubst { scope, replacements }) => {
            let [replacement] = replacements.as_slice() else {
                return None;
            };
            (scope.as_ref(), replacement)
        },
        Pattern::Term(PatternTerm::Subst { term, replacement, .. }) => {
            (term.as_ref(), replacement.as_ref())
        },
        _ => return None,
    };
    let Pattern::Term(PatternTerm::Var(scope_var)) = scope else {
        return None;
    };
    let Pattern::Term(PatternTerm::Var(repl_var)) = replacement else {
        return None;
    };
    let vars = lower_lhs_vars(left).ok()?;
    // The scope AND replacement variables MUST be bound LHS σ-slots (a closed substitution): the SEED
    // reads the captured body `b` from the scope slot and the argument `a` from the replacement slot.
    // An open substitution (a genuinely-free scope/replacement) has no slot and fails closed.
    if !vars.iter().any(|var| var == scope_var) || !vars.iter().any(|var| var == repl_var) {
        return None;
    }
    Some((vars, scope_var.clone(), repl_var.clone()))
}

/// Lower a binder/β-substitution base rewrite to its `SubstRewrite` β SEED σ-receiver — the in-Rho β
/// FIRING (Stage 4 S-binder SLICE 2a; supersedes the Stage 3c host-σ forward).
///
/// The receiver is a `(k+1)`-ary σ-receiver whose body — instead of forwarding a host-computed
/// reduct — SENDS the SEED `^subst(⟦Z⟧, σ_repl, σ_scope, out)` on the reserved `^subst` channel
/// ([`crate::rho_net_subst_trs::subst_seed_receiver_par`]), threading `out` as the cascade's
/// continuation. THIS ONE COMM is the observable β-FIRE; the reduct is the τ-cascade normal form the
/// installed TRS delivers on `out` (`b[a/0]`, capture-avoiding, IN RHO). The captured lambda body
/// `b` (the scope slot) and argument `a` (the replacement slot) flow from the AUTOMATON's in-Rho
/// capture (the MATCH path) straight into the seed with NO host substitution.
///
/// σ frame: `σ_scope = BoundVar(rhs_var_index(k, pos_of_scope))` and
/// `σ_repl = BoundVar(rhs_var_index(k, pos_of_repl))`; `out = BoundVar(0)`. Both slots MUST be bound
/// LHS variables ([`subst_rule_shape`]); an open substitution fails closed.
///
/// RETIRED (see the commented `subst_site_arms` / [`reflect_subst_scope_slot`]): the Stage 3c
/// host-contractum σ-replay, where the receiver forwarded `BoundVar(scope-slot)` carrying the
/// host-computed reduct. The in-Rho β now COMPUTES the reduct via the TRS, so the seed needs the RAW
/// captured body — incompatible with a receiver that expected the already-reduced contractum.
fn lower_subst_rewrite(
    rule: &RhoNetRule,
    rewrite: &RewriteRule,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    errors: &mut Vec<RhoNetLoweringError>,
) -> Option<RhoNetLoweredRule> {
    // The subst SCOPE (body `b`) + REPLACEMENT (argument `a`) σ slots the SEED reads. An open
    // substitution (scope/replacement not a bound LHS var, or a non-variable) fails closed.
    let Some((_shape_vars, scope_var, repl_var)) = subst_rule_shape(&rewrite.left, &rewrite.right)
    else {
        return Some(record_unsupported(rule, UnsupportedFamily::Substitution, errors));
    };
    // Positions in the σ-receiver's first-occurrence LHS order (`vars`), which equals
    // `subst_rule_shape`'s `lower_lhs_vars(left)` order — so the reverse-De-Bruijn indices agree.
    let (Some(scope_pos), Some(repl_pos)) = (
        vars.iter().position(|var| var == &scope_var),
        vars.iter().position(|var| var == &repl_var),
    ) else {
        // Cannot happen (both checked bound by `subst_rule_shape`); fail closed defensively.
        return Some(record_unsupported(rule, UnsupportedFamily::Substitution, errors));
    };
    let scope_bv = rhs_var_index(k, scope_pos) as usize;
    let repl_bv = rhs_var_index(k, repl_pos) as usize;
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
    let par = crate::rho_net_subst_trs::subst_seed_receiver_par(
        k,
        scope_bv,
        repl_bv,
        language_fingerprint,
        source,
    );
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

/// The A-S3 LOCATE→CONTRACT-CALL bridge: gate the MACHINE-invoked native handler on the
/// automaton LOCATING the native process head IN RHO, and forward the located σ operands to the
/// registered handler `Definition`'s reserved channel — the report-free ADMITTED counterpart of
/// [`native_locate_bridge_par`] (which stays byte-identical on the report-carrying deferral
/// path, where it forwards the host-computed contractum instead).
///
/// The positional network's accept for a native `NativeProc(a₀..a_{k-1})` entry sends
/// `trigger!(⟦a₀⟧, …, ⟦a_{k-1}⟧, @out)` once it has MATCHED the head tag + arity and CAPTURED
/// the `k` structural args ON the interpreter. This bridge binds those `k` captures plus the
/// dynamic `out` and forwards ALL of them — a value-free pure forwarder — to the native
/// handler contract channel (`[0xF1, rule_index]`,
/// [`native_contract_channel`](crate::native_contract_channel)):
///
/// ```text
/// for (a₀, …, a_{k-1}, out <- @"trigger") { native_channel!(a₀, …, a_{k-1}, out) }
/// ```
///
/// The installed handler `Definition` (arity `k + 1`) is dispatched by that COMM — the MACHINE
/// invokes the trusted evaluator on the located σ at COMM time — and `produce`s
/// `[value, out]` on the rule's dispatch channel, where the installed dispatch receiver
/// (`for (result, out <- c) { out!(result) }`) consumes the RETURNED value and emits it on
/// `@out`. So the LOCATION is the automaton's, the VALUE is the registered handler's output at
/// COMM time, and NO host-pre-computed value rides the call `Par` (the A-S3 boundary,
/// `NativeSystemProcessBoundary.v` section 4).
///
/// Non-persistent: one located native site's accept drives exactly one contract call, so the
/// caller installs one bridge copy PER located site (the copies are identical — the bridge
/// carries no per-site value — so any accept↔bridge pairing is correct).
pub fn native_locate_contract_bridge_par(
    trigger_channel: &str,
    k: usize,
    native_channel: Par,
) -> Par {
    let formal_count = k + 1;
    // Forward every bound formal in binding order: captured arg `i` is `BoundVar(k - i)` (the
    // reverse De Bruijn convention of the `formal_count` binders), the dynamic out (the LAST
    // bound formal) is `BoundVar(0)` — exactly the accept send's argument order, so the handler
    // `Definition` receives `[⟦a₀⟧, …, ⟦a_{k-1}⟧, out]`.
    let data: Vec<Par> = (0..formal_count)
        .map(|i| {
            let idx = formal_count - 1 - i;
            new_boundvar_par(idx as i32, create_bit_vector(&[idx]), false)
        })
        .collect();
    let all_free = create_bit_vector(&(0..formal_count).collect::<Vec<_>>());
    // Body: `native_channel!(a₀, …, a_{k-1}, out)` — the channel is the closed unforgeable
    // `[0xF1, rule_index]` Par, so the send is free exactly in the forwarded formals.
    let body = new_send_par(native_channel, data, false, all_free.clone(), false, all_free, false);
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
///    (e.g. Rholang's `ParCong` over an AC `PPar` bag has an AC-collection LHS/RHS) — such a
///    context stays `Unsupported{family}`, exactly as before this slice;
///  - a non-congruence side condition (a semantic-predicate guard, freshness, relation
///    query, universal) appears as a premise — it has no join slot ([`congruence_targets`]);
///  - the reduced context RHS `K'` is unreflectable (binder / collection / substitution /
///    dangling hole) — caught by [`reflect_term_par`].
///
/// A-S5.1 (leg i) refinement: when the failing rewrite's premise set is NON-EMPTY and
/// ALL-congruence ([`congruence_only_premises`]), BOTH failure sites dispose it as the
/// install-exempt [`RhoNetLoweredRule::CongruenceExemptRewrite`] (recorded — never an
/// `errors` push) instead of fail-closing the whole program: a congruence-only rewrite
/// declares no motion of its own, and its context closure is carried by the locate-all /
/// driver descent in Rho and the e-graph congruence closure on host paths. A mixed-premise
/// failure keeps the pre-A-S5.1 fail-closed behavior byte-identically
/// ([`exempt_or_record`]).
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
    // Independent P2 detector: a binder / collection / substitution context (Rholang's
    // ParCong over an AC PPar bag) has no flat contextual-join image — fail closed with the
    // out-of-scope family, exactly as the classify-only predecessor did.
    if let Some(family) = rewrite_pattern_unsupported(&rewrite.left, &rewrite.right) {
        return Some(exempt_or_record(rule, rewrite, family, errors));
    }
    match contextual_join_rule_par(rewrite, rule, language_fingerprint) {
        Ok(par) => Some(RhoNetLoweredRule::ContextualRewrite { rule_id: rule.id.clone(), par }),
        Err(family) => Some(exempt_or_record(rule, rewrite, family, errors)),
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
    // detector before reaching here (Rholang's `ParCong` over an AC bag), so no HashBag bag-RHS
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

/// A-S5.1 (leg i): dispose one contextual-lowering FAILURE. Congruence-exempt
/// ([`RhoNetLoweredRule::CongruenceExemptRewrite`] — recorded, no diagnostic
/// pushed, never blocks the install) iff the source rewrite's premises are
/// all-congruence and non-empty ([`congruence_only_premises`]); otherwise exactly
/// the pre-A-S5.1 fail-closed behavior ([`record_unsupported`]) — a mixed-premise
/// side condition is never silently dropped.
fn exempt_or_record(
    rule: &RhoNetRule,
    rewrite: &RewriteRule,
    family: UnsupportedFamily,
    errors: &mut Vec<RhoNetLoweringError>,
) -> RhoNetLoweredRule {
    if congruence_only_premises(&rewrite.premises) {
        RhoNetLoweredRule::CongruenceExemptRewrite { rule_id: rule.id.clone(), family }
    } else {
        record_unsupported(rule, family, errors)
    }
}

/// The A-S5.1 (leg i) congruence-exemption predicate, SHARED verbatim by the
/// contextual lowering ([`exempt_or_record`], both failure sites of
/// [`lower_contextual_rewrite`]) and the A-S2 static capability gate
/// (`rho_net_ruleset::in_rho_static_gate`): a rewrite is congruence-exempt iff
/// its premise set is NON-EMPTY and EVERY premise is a `Premise::Congruence`
/// hole.
///
/// `all(..)` + non-empty (not `any(..)`) is the A-S5.1 hardening: a MIXED-premise
/// rewrite (a congruence hole plus a freshness / guard / relation side condition)
/// is NEVER exempt — exempting it would silently drop the side condition — and an
/// empty premise list (a base rewrite) is never exempt either. Proven
/// outcome-neutral corpus-wide (red-team F13): every bundled congruence rewrite
/// carries only congruence premises — the only multi-premise rewrite,
/// `bicongdemo`'s `NodeCong` (`languages/tests/definitions/bicongdemo.rs`), carries two
/// congruence premises and stays exempt under `all`; auto-injected `NormCast`
/// rules carry only `SyntheticInjGuard` (no congruence premise) and are unaffected.
///
/// FV mirror (1:1): `congruence_only_premises` in
/// `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`
/// (`Section CongruenceExemptInstallBoundary`).
pub fn congruence_only_premises(premises: &[Premise]) -> bool {
    !premises.is_empty()
        && premises
            .iter()
            .all(|premise| matches!(premise, Premise::Congruence { .. }))
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
    enum Task<'a> {
        Visit(&'a Pattern),
        ExitBinders(&'a [Ident]),
    }

    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    // Counts, rather than a linear binder-name stack, make a bound-variable query O(1) while
    // preserving shadowing: an exit decrements the exact names its matching entry introduced.
    let mut bound_counts: HashMap<String, usize> = HashMap::new();
    let mut tasks = vec![Task::Visit(pattern)];

    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(ident))) => {
                let name = ident.to_string();
                if !bound_counts.contains_key(&name) && seen.insert(name) {
                    vars.push(ident.clone());
                }
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { args, .. })) => {
                tasks.extend(args.iter().rev().map(Task::Visit));
            },
            Task::Visit(Pattern::Term(PatternTerm::Lambda { binder, body })) => {
                *bound_counts.entry(binder.to_string()).or_insert(0) += 1;
                tasks.push(Task::ExitBinders(std::slice::from_ref(binder)));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(Pattern::Term(PatternTerm::MultiLambda { binders, body })) => {
                for binder in binders {
                    *bound_counts.entry(binder.to_string()).or_insert(0) += 1;
                }
                tasks.push(Task::ExitBinders(binders));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(Pattern::Term(
                PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. },
            )) => return Err(UnsupportedFamily::Substitution),
            Task::Visit(Pattern::Collection { .. }) => {
                return Err(UnsupportedFamily::CollectionAc);
            },
            Task::Visit(Pattern::Map { .. }) => return Err(UnsupportedFamily::MapAc),
            Task::Visit(Pattern::Zip { .. }) => return Err(UnsupportedFamily::ZipAc),
            Task::Visit(Pattern::IndexedVec { .. }) => {
                return Err(UnsupportedFamily::IndexedVecOrdered);
            },
            Task::ExitBinders(binders) => {
                for binder in binders {
                    let name = binder.to_string();
                    let count = bound_counts
                        .get_mut(&name)
                        .expect("LHS-variable PDA exited an inactive binder");
                    *count -= 1;
                    if *count == 0 {
                        bound_counts.remove(&name);
                    }
                }
            },
        }
    }

    Ok(vars)
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
/// term data. Mirrors the rholang bag ABI tag ([`crate::RHOLANG_BAG_ABI_TAG`]).
///
/// ## The parse invariant, stated once (S1)
///
/// The tag is `{prefix}{fingerprint}.{label}` with NO length prefix and NO escaping,
/// so it is unambiguously decomposable **iff the fingerprint contains no `.`** — and
/// then only by splitting at the FIRST `.` after the prefix, because a LABEL may
/// legitimately contain dots: [`crate::REFLECTED_TERM_ABI_PREFIX`] tags are minted for
/// synthesized literal-leaf labels of the form `{Label}({value:?})`, and a
/// `FloatLit(8.5)` / `RatLit(…)` / `StringLit("a.b")` label is dotted by construction
/// (`macros/src/gen/runtime/rho_invocation.rs` `format!("{}({:?})", …)`).
///
/// The invariant is NOT "the fingerprint has a fixed length" — the parse is entirely
/// length-agnostic, so a future wider fingerprint scheme is free to change it. What the
/// parse depends on is only dot-freedom, which [`ast::language_definition_fingerprint`]'s
/// `mettail-langdef-v1:{:016x}` form satisfies. The `debug_assert!` below is the single
/// place a scheme that broke it would fail loudly, instead of silently mis-splitting at
/// five hand-rolled reader sites.
///
/// [`parse_reflected_tag`] is the sole inverse. Do not hand-roll another.
pub(crate) fn reflect_tag(language_fingerprint: &str, constructor_label: &str) -> String {
    debug_assert!(
        !language_fingerprint.contains('.'),
        "reflected-tag ABI: the fingerprint must be dot-free so `parse_reflected_tag` can split \
         at the FIRST `.` and leave a dotted literal-leaf label intact; got {language_fingerprint:?}"
    );
    format!("{}{language_fingerprint}.{constructor_label}", crate::REFLECTED_TERM_ABI_PREFIX)
}

/// The SOLE inverse of [`reflect_tag`]: split a reflected-term ABI tag into its
/// `(fingerprint, label)` halves, or `None` if `tag` is not one.
///
/// ## Why this exists (S1)
///
/// Before this function the tree held ONE writer and FIVE independently hand-rolled
/// readers, and they did not agree: `native_contract::par_to_ground_term` split at the
/// first `.` (correct) while `run::decode_reflected_term` and the three
/// `bench_support::is_*_channel_tag` classifiers split at the LAST `.` (wrong for any
/// dotted label). The two sites' doc comments asserted contradictory invariants — one
/// said a label "may itself contain dots", the other that "a constructor label is a
/// dot-free identifier" — and nothing enforced either.
///
/// The consequence of the `rsplit` form on a `FloatLit(8.5)` label is silent corruption
/// rather than an error: the split yields `fingerprint = "…:XXXX.FloatLit(8"` and
/// `label = "5)"`, the corrupted fingerprint then fails
/// [`crate::is_ground_marker_par`], so the hereditary-ground marker is NOT skipped and
/// leaks into the decoded term as a phantom child. No rho-backed language declares a
/// dot-producing carrier today (all fifteen carry `![i64] as Int` or
/// `![HashBag<Proc>] as Bag`), so the defect is LATENT — but it is armed the moment a
/// float, rational, fixed-point, or string category joins a rho-backed language.
///
/// Splitting at the first `.` is correct exactly because of [`reflect_tag`]'s asserted
/// invariant: the fingerprint is dot-free, so the first `.` after the prefix is the
/// separator, and everything after it — dots and all — is the label.
pub fn parse_reflected_tag(tag: &str) -> Option<(&str, &str)> {
    let suffix = tag.strip_prefix(crate::REFLECTED_TERM_ABI_PREFIX)?;
    let (fingerprint, label) = suffix.split_once('.')?;
    (!label.is_empty()).then_some((fingerprint, label))
}

/// The PUBLIC read surface of [`reflect_tag`] (A-S5.6): the deterministic reflect-tag
/// STRING for one `(fingerprint, label)` pair, so runtime-side channel classifiers (the
/// Layer-2 τ-COMM classifier over "reconstructible GPrivate reflect tags", plan v2 §6.4)
/// can reconstruct reserved rendezvous names — `^drive`, `^drive-ac:{Rule}`, the
/// `^subst` TRS family — without duplicating the ABI format. Purely a naming helper: no
/// emission goes through it.
pub fn reflected_tag_string(language_fingerprint: &str, constructor_label: &str) -> String {
    reflect_tag(language_fingerprint, constructor_label)
}

/// A ground (variable-free) constructor term: a constructor label applied to
/// ground children. This is the caller-facing input to
/// [`reflect_ground_term_par`] — the closed value a runtime injection supplies as
/// a σ argument. Because dovetail has already matched the LHS, every σ argument
/// is a fully-instantiated ground term, so this representation carries no bound
/// variables (unlike an RHS pattern, which does).
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

impl std::fmt::Debug for GroundTerm {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum DebugTask<'a> {
            Visit(&'a GroundTerm),
            Separator,
            Tail(&'a Option<CollectionType>),
        }

        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Visit(term) => {
                    write!(
                        formatter,
                        "GroundTerm {{ constructor: {:?}, children: [",
                        term.constructor
                    )?;
                    tasks.push(DebugTask::Tail(&term.coll_type));
                    for (index, child) in term.children.iter().enumerate().rev() {
                        tasks.push(DebugTask::Visit(child));
                        if index > 0 {
                            tasks.push(DebugTask::Separator);
                        }
                    }
                },
                DebugTask::Separator => formatter.write_str(", ")?,
                DebugTask::Tail(coll_type) => {
                    write!(formatter, "], coll_type: {coll_type:?} }}")?;
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for GroundTerm {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.constructor != right.constructor
                || left.coll_type != right.coll_type
                || left.children.len() != right.children.len()
            {
                return false;
            }
            pending.extend(left.children.iter().zip(&right.children));
        }
        true
    }
}

impl Eq for GroundTerm {}

impl Clone for GroundTerm {
    fn clone(&self) -> Self {
        enum CloneTask<'a> {
            Visit(&'a GroundTerm),
            Assemble {
                constructor: String,
                coll_type: Option<CollectionType>,
                child_count: usize,
            },
        }

        let mut tasks = Vec::new();
        let mut values = Vec::new();
        tasks.push(CloneTask::Visit(self));
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(term) => {
                    tasks.push(CloneTask::Assemble {
                        constructor: term.constructor.clone(),
                        coll_type: term.coll_type.clone(),
                        child_count: term.children.len(),
                    });
                    for child in term.children.iter().rev() {
                        tasks.push(CloneTask::Visit(child));
                    }
                },
                CloneTask::Assemble { constructor, coll_type, child_count } => {
                    let first_child = values
                        .len()
                        .checked_sub(child_count)
                        .expect("GroundTerm clone PDA lost a child result");
                    let children = values.split_off(first_child);
                    values.push(GroundTerm { constructor, children, coll_type });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("GroundTerm clone PDA produced no result")
    }
}

impl Drop for GroundTerm {
    fn drop(&mut self) {
        // Empty each descendant before it is dropped. Every implicit call to
        // this `Drop` implementation therefore sees an empty `children` vec,
        // keeping native stack usage independent of term depth.
        let mut pending = Vec::new();
        pending.append(&mut self.children);
        while let Some(mut child) = pending.pop() {
            pending.append(&mut child.children);
        }
    }
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
    /// ([`AC_MAP_ENTRY_LABEL`]) [`reflect_ground_term_par`] reads back as one `EMap`
    /// `KeyValuePair`. A
    /// `HashMap` [`collection`](Self::collection)'s `elements` are these entry nodes.
    pub fn map_entry(key: GroundTerm, value: GroundTerm) -> Self {
        Self::new(AC_MAP_ENTRY_LABEL, vec![key, value])
    }

    /// An exact byte-string leaf. Hex is a canonical transport encoding: two
    /// octets per byte, lowercase, with no locale or UTF-8 interpretation.
    pub fn bytes(bytes: &[u8]) -> Self {
        use std::fmt::Write as _;

        let mut constructor = String::with_capacity(BYTES_REFLECT_LABEL.len() + bytes.len() * 2);
        constructor.push_str(BYTES_REFLECT_LABEL);
        for byte in bytes {
            write!(&mut constructor, "{byte:02x}").expect("String writes are infallible");
        }
        Self::nullary(constructor)
    }

    /// The closed PathMap mode leaf used by static and dynamic structural
    /// reflection. Unknown tags fail closed instead of being reflected as a
    /// user constructor.
    pub fn pathmap_mode(mode: u8) -> Option<Self> {
        let constructor = match mode {
            0 => PATHMAP_EMPTY_REFLECT_LABEL,
            1 => PATHMAP_SET_REFLECT_LABEL,
            2 => PATHMAP_MAP_REFLECT_LABEL,
            _ => return None,
        };
        Some(Self::nullary(constructor))
    }
}

/// Which side of a rewrite is being reconstructed as a positional ground image.
///
/// The LHS redex and RHS contractum walkers have the same automaton; this tag keeps their
/// established fail-closed diagnostics distinct while sharing one stack-safe implementation.
#[derive(Clone, Copy)]
pub(crate) enum StructuralGroundImage {
    Lhs,
    Rhs,
}

/// Instantiate a Var/Apply-only pattern with `sigma` using an explicit post-order PDA.
///
/// This is shared by contextual RHS reconstruction and the ruleset's LHS redex oracle. It
/// deliberately rejects AC, binder, substitution, and collection-search nodes exactly where the
/// former recursive implementations did. One heap task and one result slot are retained per
/// active/pending node; native stack usage is constant in pattern depth.
pub(crate) fn instantiate_structural_ground_pattern(
    pattern: &Pattern,
    sigma: &HashMap<&str, &GroundTerm>,
    rule: &str,
    image: StructuralGroundImage,
) -> Result<GroundTerm, String> {
    enum Task<'a> {
        Visit(&'a Pattern),
        Assemble { constructor: String, child_count: usize },
    }

    let (context, side, noun) = match image {
        StructuralGroundImage::Lhs => ("in-Rho match subject", "LHS", "redex"),
        StructuralGroundImage::Rhs => ("contextual contractum", "RHS", "contractum"),
    };
    let mut tasks = vec![Task::Visit(pattern)];
    let mut values = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(id))) => {
                let name = id.to_string();
                let ground = sigma.get(name.as_str()).ok_or_else(|| {
                    format!("{context} for {rule}: σ missing {side} variable {name}")
                })?;
                values.push((*ground).clone());
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { constructor, args })) => {
                if let [Pattern::Collection { .. }] = args.as_slice() {
                    return Err(format!(
                        "{context} for {rule}: AC constructor {constructor} has no positional {noun} image"
                    ));
                }
                tasks.push(Task::Assemble {
                    constructor: constructor.to_string(),
                    child_count: args.len(),
                });
                tasks.extend(args.iter().rev().map(Task::Visit));
            },
            Task::Visit(_) => {
                return Err(format!(
                    "{context} for {rule}: non-structural {side} has no ground {noun} image"
                ));
            },
            Task::Assemble { constructor, child_count } => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("ground-pattern PDA lost a child result");
                let children = values.split_off(first_child);
                values.push(GroundTerm::new(constructor, children));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values.pop().expect("ground-pattern PDA produced no result"))
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
        let premise_channels: Vec<String> =
            program_rule.input_channels.get(1..).unwrap_or(&[]).to_vec();
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
    /// The SCOPE variable (`subst` scope, the lambda body `b`). Its σ slot carries the captured body
    /// the in-Rho β SEED threads into `^subst(⟦Z⟧, a, b, out)` (Stage 4 SLICE 2a). (In the retired
    /// host-σ path it carried the host-computed reduct/contractum — see the commented
    /// `subst_site_arms`.)
    pub scope_var: String,
    /// The REPLACEMENT variable (`subst` replacement, the argument `a`). Its σ slot carries the
    /// captured argument the SEED threads into `^subst(⟦Z⟧, a, b, out)`.
    pub repl_var: String,
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
        let Some((vars, scope_var, repl_var)) = subst_rule_shape(&rewrite.left, &rewrite.right)
        else {
            continue;
        };
        sites.push(RhoNetSubstInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            lhs_var_order: vars.iter().map(|var| var.to_string()).collect(),
            scope_var: scope_var.to_string(),
            repl_var: repl_var.to_string(),
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
    let language_fingerprint = mettail_ast::identity::language_definition_fingerprint(def);
    let sites = rho_net_ac_injection_sites(def);
    let mut entries = Vec::with_capacity(sites.len());
    for site in sites {
        // The source rewrite an AC injection site surfaced is always present; a defensive skip keeps
        // the derivation total.
        let Some(rewrite) = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == site.rule_label)
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
    /// site `ℓ_i` by resolving its path through the shared subject-location index (the SAME
    /// index `collect_redex_sites` uses), so a premise-`i` located firing routes to premise
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
                .find(|rewrite| rewrite.name == site.rule_label)
                .map(|rewrite| {
                    rewrite
                        .premises
                        .iter()
                        .filter_map(|premise| match premise {
                            Premise::Congruence { source, .. } => Some(
                                contextual_source_path(&rewrite.left, &source.to_string())
                                    .unwrap_or_default(),
                            ),
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
/// `None` when `source` does not occur). The match driver resolves the path through its
/// [`SubjectLocationIndex`], so the derivation matches `collect_redex_sites` without constructing
/// an ancestor-copying channel path.
fn contextual_source_path(pattern: &Pattern, source: &str) -> Option<Vec<(String, usize)>> {
    enum Task<'pattern> {
        Visit(&'pattern Pattern),
        Enter {
            pattern: &'pattern Pattern,
            constructor: String,
            index: usize,
        },
        Truncate(usize),
    }

    let mut work = vec![Task::Visit(pattern)];
    let mut path = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(id))) if id == source => {
                return Some(path);
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { constructor, args })) => {
                let constructor = constructor.to_string();
                work.extend(
                    args.iter()
                        .enumerate()
                        .rev()
                        .map(|(index, pattern)| Task::Enter {
                            pattern,
                            constructor: constructor.clone(),
                            index,
                        }),
                );
            },
            Task::Enter { pattern, constructor, index } => {
                let old_len = path.len();
                path.push((constructor, index));
                work.push(Task::Truncate(old_len));
                work.push(Task::Visit(pattern));
            },
            Task::Truncate(len) => path.truncate(len),
            Task::Visit(_) => {},
        }
    }
    None
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
        .find(|rewrite| rewrite.name == rule_label)
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
    instantiate_structural_ground_pattern(pattern, sigma, rule, StructuralGroundImage::Rhs)
}

/// E-2-D: does a reflected node with head `label` carry the hereditary-ground marker?
///
/// TRUE for OBJECT nodes — the binder/variable leaves (`^lambda`/`^multilambda`/`^bound`/
/// `^free`) and every USER constructor (a Rust `Ident`, so NEVER `^`-prefixed). FALSE for
/// MACHINERY — the Peano numerals `^Z`/`^S`, the `^cmp` results, the reserved reduction tags
/// (`^subst`/`^shift`/`^cmp`/…), and the marker tokens themselves (every `^`-prefixed label
/// that is not a binder/variable leaf). The subst cascade dispatches on OBJECT nodes; the
/// numeric machinery is byte-unchanged.
///
/// ★ #36 S3 changed the answer for exactly one input class: a USER constructor literally named
/// `Z` or `S` is now MARKED, like every other user constructor. Before the Peano rename it was
/// forced UNMARKED by an explicit arm, because it was indistinguishable from the machinery
/// numerals. That was sound but name-dependent — such a language silently forfeited the `^gnd`
/// ground short-circuit while an identical language naming its successor `Succ` kept it. With
/// the numerals moved into the `^` namespace the ambiguity is gone at the source and the rule
/// is uniform: marked ⟺ not `^`-prefixed, plus the four binder/variable leaves.
pub fn is_marked_object_label(label: &str) -> bool {
    match label {
        LAMBDA_REFLECT_LABEL
        | MULTILAMBDA_REFLECT_LABEL
        | BOUND_VAR_REFLECT_LABEL
        | FREE_VAR_REFLECT_LABEL => true,
        // ★ #36 S3: REDUNDANT once the Peano labels are `^`-prefixed — the generic
        // `other => !other.starts_with('^')` arm below now covers them. Retained,
        // commented out, as the record of why it existed: while the labels were bare
        // `Z`/`S` they were indistinguishable from user constructors and needed the
        // explicit exclusion.
        //   PEANO_ZERO_REFLECT_LABEL | PEANO_SUCC_REFLECT_LABEL => false,
        other => !other.starts_with('^'),
    }
}

/// E-2-D: the hereditary-ground marker token `GPrivate(reflect_tag(fp, ^gnd | ^nog))`.
///
/// FLT Phase 2 (P3): `pub` so the public reflector API ([`crate::rho_net_flt`]) can build the
/// exact `^gnd`/`^nog` marker a hole-free FLT subtree carries and the C2 construction path can
/// recompute a filled node's marker — the same token every reflected object node interposes at
/// index 1.
pub fn ground_marker_tag_par(fp: &str, is_ground: bool) -> Par {
    GPrivateBuilder::new_par_from_string(reflect_tag(
        fp,
        if is_ground {
            GROUND_MARK_REFLECT_LABEL
        } else {
            NONGROUND_MARK_REFLECT_LABEL
        },
    ))
}

/// E-2-D: is `par` one of the two hereditary-ground marker tokens for `fp`? The DECODERS
/// (`run::decode_reflected_term`, `native_contract::par_to_ground_term`,
/// `rho_net_pattern_guard`)
/// SKIP it when it sits at a reflected object node's index 1, recovering the pre-D positional
/// child sequence. A bare marker GPrivate never occurs as a genuine reflected child (children
/// are tagged `EList`s / `GString` names / scalars), so the skip is unambiguous.
pub fn is_ground_marker_par(par: &Par, fp: &str) -> bool {
    par == &ground_marker_tag_par(fp, true) || par == &ground_marker_tag_par(fp, false)
}

/// E-2-D: does the reflected object node `par` carry the `^gnd` (GROUND) marker at index 1?
/// The combinator [`crate::rho_net_subst_trs::tagged`] uses this to fold a reassembled node's
/// marker from its ALREADY-reflected children (a runtime σ-var child is a BoundVar, not a marked
/// `EList`, so it reads false — the conservative `^nog`). Cheap O(1): peek the second element.
// FLT Phase 2 (P3): `pub` so the public construction reflector (`crate::rho_net_flt`) can
// recompute EVERY ancestor's marker from its FILLED subtree's own ground bit (C2), never keeping
// a stale template `^gnd` over a `^bound`-carrying fill.
pub fn par_carries_ground_marker(par: &Par, fingerprint: &str) -> bool {
    matches!(
        par.exprs.first().and_then(|expr| expr.expr_instance.as_ref()),
        Some(ExprInstance::EListBody(list))
            if list.ps.get(1) == Some(&ground_marker_tag_par(fingerprint, true))
    )
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
    reflect_ground_term_marked(term, language_fingerprint).0
}

/// [`reflect_ground_term_par`] threading the E-2-D hereditary-ground bit bottom-up in ONE O(n)
/// pass: an OBJECT node (`is_marked_object_label`) interposes the `^gnd`/`^nog` marker at index 1
/// (right after the head tag), with `^gnd` iff the subtree contains no `^bound` leaf (`^bound` ⟹
/// false, `^free` ⟹ true, else ⟹ all children ground — the FV `oground`). Machinery labels + AC
/// carriers get NO marker (and count as NOT ground for a parent's marker). Returns the reflected
/// `Par` and its ground bit (so a parent computes its marker without re-traversing — no O(n²)).
fn reflect_ground_term_marked(term: &GroundTerm, language_fingerprint: &str) -> (Par, bool) {
    enum ReflectTask<'term> {
        Visit(&'term GroundTerm),
        Assemble {
            term: &'term GroundTerm,
            value_count: usize,
        },
    }

    let mut tasks = vec![ReflectTask::Visit(term)];
    let mut values: Vec<(Par, bool)> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ReflectTask::Visit(term) => {
                if term.coll_type == Some(CollectionType::HashMap) {
                    let entries = term
                        .children
                        .iter()
                        .filter(|entry| {
                            entry.constructor == AC_MAP_ENTRY_LABEL && entry.children.len() == 2
                        })
                        .count();
                    tasks.push(ReflectTask::Assemble { term, value_count: entries * 2 });
                    for entry in term.children.iter().rev() {
                        let [key, value] = entry.children.as_slice() else {
                            continue;
                        };
                        if entry.constructor != AC_MAP_ENTRY_LABEL {
                            continue;
                        }
                        tasks.push(ReflectTask::Visit(value));
                        tasks.push(ReflectTask::Visit(key));
                    }
                } else {
                    tasks.push(ReflectTask::Assemble { term, value_count: term.children.len() });
                    for child in term.children.iter().rev() {
                        tasks.push(ReflectTask::Visit(child));
                    }
                }
            },
            ReflectTask::Assemble { term, value_count } => {
                let first = values
                    .len()
                    .checked_sub(value_count)
                    .expect("ground reflection PDA lost a child result");
                let children = values.split_off(first);
                let reflected = match term.coll_type {
                    Some(CollectionType::HashBag) => {
                        (assemble_ac_bag_par(term, children, language_fingerprint), false)
                    },
                    Some(CollectionType::HashSet) => (assemble_ac_set_par(children), false),
                    Some(CollectionType::HashMap) => (assemble_ac_map_par(children), false),
                    _ => assemble_positional_ground_node(term, children, language_fingerprint),
                };
                values.push(reflected);
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("ground reflection PDA produced no result")
}

/// Assemble one positional reflected node from already-reflected children.
///
/// This is the shared reduce step for the ground reflector and the FLT pattern/
/// construction PDAs. Keeping it here makes the E-2-D marker and `locally_free`
/// invariants single-sourced while every caller owns only its traversal policy.
pub(crate) fn assemble_positional_ground_node(
    term: &GroundTerm,
    children: Vec<(Par, bool)>,
    language_fingerprint: &str,
) -> (Par, bool) {
    let tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &term.constructor));
    let marked = is_marked_object_label(&term.constructor);
    let mut elements = Vec::with_capacity(term.children.len() + 2);
    let mut locally_free = tag.locally_free.clone();
    elements.push(tag);
    // Reserve the marker slot (filled after the children so ground-ness is known); a GPrivate
    // marker has empty `locally_free`, so it never contributes to the node's free-set.
    let marker_slot = marked.then(|| {
        elements.push(Par::default());
        elements.len() - 1
    });
    let mut children_ground = true;
    for (child_par, child_ground) in children {
        children_ground &= child_ground;
        locally_free = union(locally_free, child_par.locally_free.clone());
        elements.push(child_par);
    }
    let is_ground = match term.constructor.as_str() {
        BOUND_VAR_REFLECT_LABEL => false,
        FREE_VAR_REFLECT_LABEL => true,
        _ => children_ground,
    };
    if let Some(index) = marker_slot {
        elements[index] = ground_marker_tag_par(language_fingerprint, is_ground);
    }
    (
        new_elist_par(elements, locally_free.clone(), false, None, locally_free, false),
        is_ground,
    )
}

/// Reflect a HashBag AC operand bag as the process-`Par` matching CARRIER: each element is a
/// ground send `@"ac:{op}"!(⟦e⟧)`, so the soup is order-independent (the native connective /
/// `sub_pars` matcher picks any element↔pattern assignment) and multiplicity-preserving (a
/// `Vec` of sends, duplicates disambiguated by `Indexed`), and element slots never collide
/// with the pattern's process remainder. This is the subject side of Stage AC's Scheme B —
/// the AC receiver's collection pattern matches this carrier inside one atomic `consume`.
fn assemble_ac_bag_par(
    term: &GroundTerm,
    children: Vec<(Par, bool)>,
    language_fingerprint: &str,
) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, &term.constructor);
    let mut soup = Par::default();
    for (element, _) in children {
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

fn reflect_ac_bag_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    reflect_ground_term_marked(term, language_fingerprint).0
}

/// The reserved constructor label a HashMap AC operand entry (`key => value`) reflects to in a
/// [`GroundTerm`]: a synthetic node `^kv(⟦key⟧, ⟦value⟧)` whose two children are the entry's key
/// and value. It cannot collide with any user constructor (a Rust `Ident`, never containing `^`),
/// so the map carrier's entry envelope is distinct from every `Apply` node. The macro
/// `reflect_category_fn`'s `HashMap` arm emits one such node per entry; the ground-reflection PDA
/// reads the two children back as the `EMap`'s key/value.
pub(crate) const AC_MAP_ENTRY_LABEL: &str = "^kv";

/// Reflect an AC operand COLLECTION [`GroundTerm`] as its kind's native matching CARRIER — the
/// subject side of Stage 4 S-AC / AC4. A `HashBag` reflects to the order-independent process-`Par`
/// soup; a `HashSet` to a native `ESet`; a `HashMap` to a native `EMap`. The `ESet`/`EMap`
/// carriers ride
/// `ParSet`/`ParMap`, whose construction SORTS + DEDUPES (so `ESet` is a genuine set and `EMap`'s
/// keys are unique — the key-uniqueness invariant survives reflection), and the native spatial
/// production `spatial_matcher_pda::ListMachine` AC-matches each carrier
/// order-independently with a remainder.
fn reflect_ac_collection_par(term: &GroundTerm, language_fingerprint: &str) -> Par {
    reflect_ground_term_marked(term, language_fingerprint).0
}

/// Reflect a `HashSet` AC operand set as a native `ESet` matching CARRIER: each element reflects to
/// its ground `Par` and the set rides `ParSet` (sorted + deduplicated), so the carrier is a genuine
/// order-independent, uniqueness-preserving set. The AC receiver's `ESet` connective pattern
/// ([`ac_set_pattern`]) matches this carrier inside one atomic `consume` (native
/// `spatial_matcher_pda::ListMachine` over `sorted_pars`), binding `k` element slots + the residual
/// set to the remainder.
fn assemble_ac_set_par(children: Vec<(Par, bool)>) -> Par {
    let mut elements = Vec::with_capacity(children.len());
    let mut locally_free = Vec::new();
    for (element, _) in children {
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
/// matches this carrier inside one atomic `consume` (native
/// `spatial_matcher_pda::ListMachine` over the key-sorted kv list), binding `k` `(key, value)`
/// slots + the residual map to the remainder.
fn assemble_ac_map_par(children: Vec<(Par, bool)>) -> Par {
    debug_assert_eq!(children.len() % 2, 0);
    let mut kvs = Vec::with_capacity(children.len() / 2);
    let mut locally_free = Vec::new();
    let mut children = children.into_iter();
    while let Some((key_par, _)) = children.next() {
        let (value_par, _) = children
            .next()
            .expect("map reflection PDA pairs each key with one value");
        locally_free = union(locally_free, key_par.locally_free.clone());
        locally_free = union(locally_free, value_par.locally_free.clone());
        kvs.push(KeyValuePair {
            key: Some(key_par),
            value: Some(value_par),
        });
    }
    // A GROUND map: no free vars, no connective, no remainder. `ParMap::new` sorts by key + dedupes
    // on key (so duplicate keys collapse to the last write — the key-uniqueness invariant).
    new_emap_par(kvs, locally_free.clone(), false, None, locally_free, false)
}

/// The AC receiver's collection PATTERN for an operand of `kind` with `k` fixed element slots
/// (Stage 4 S-AC / AC4): a `HashBag` yields the process-soup connective ([`ac_bag_pattern`]); a
/// `HashSet` the `ESet` connective ([`ac_set_pattern`]); a `HashMap` the `EMap` connective
/// ([`ac_map_pattern`]). Each binds the fixed element slots + a residual-binding remainder, matched
/// order-independently by the native spatial matcher inside one atomic `consume`. `op` and
/// `language_fingerprint` are used only by the `HashBag` soup (its element channel
/// [`ac_soup_channel`]); the native `ESet`/`EMap` carriers are structural connectives that
/// name no channel at all, so INV-S6 has nothing to scope on those two arms.
pub fn ac_collection_pattern(
    kind: CollectionType,
    language_fingerprint: &str,
    op: &str,
    k: usize,
) -> Par {
    match kind {
        CollectionType::HashSet => ac_set_pattern(k),
        CollectionType::HashMap => ac_map_pattern(k),
        // `HashBag` (and any other kind routed here) → the process-soup pattern.
        _ => ac_bag_pattern(language_fingerprint, op, k),
    }
}

/// The AC receiver's `ESet` connective PATTERN for a `HashSet` operand with `k` fixed element slots:
/// a connective `ESet` whose `k` elements are free vars `FreeVar(0..k-1)` (each binding element σ
/// slot `i`) plus a remainder free var `FreeVar(k)` (binding `rest`, the residual set). The native
/// production `spatial_matcher_pda::ListMachine` (`ESetBody`) assigns the `k` free-var patterns to `k`
/// set elements in ANY order and binds the residual SET to the remainder — the order-independent set
/// match — inside one atomic `consume`. The remainder is a `FreeVar(k)` `Var` (exactly the
/// `remainder_var_opt` level the matcher reads); element `i` binds `FreeVar(i)`.
pub fn ac_set_pattern(k: usize) -> Par {
    let elements: Vec<Par> = (0..k)
        .map(|i| new_freevar_par(i as i32, Vec::new()))
        .collect();
    let remainder = Var {
        var_instance: Some(VarInstance::FreeVar(k as i32)),
    };
    new_eset_par(elements, Vec::new(), true, Some(remainder), Vec::new(), true)
}

/// The AC receiver's `EMap` connective PATTERN for a `HashMap` operand with `k` fixed `(key, value)`
/// slots: a connective `EMap` whose `k` entries are free-var pairs `(FreeVar(2i), FreeVar(2i+1))`
/// (key σ slot `2i`, value σ slot `2i+1`) plus a remainder free var `FreeVar(2k)` (binding `rest`,
/// the residual map). The production `spatial_matcher_pda::ListMachine` (`EMapBody`) assigns the
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
    let remainder = Var {
        var_instance: Some(VarInstance::FreeVar((2 * k) as i32)),
    };
    new_emap_par(kvs, Vec::new(), true, Some(remainder), Vec::new(), true)
}

/// The AC receiver's collection PATTERN for a HashBag operand `op` with `k` fixed element
/// slots: a connective process-`Par` with `k` send-patterns `@"ac:{op}"!(FreeVar(i))` (each
/// binding element σ slot `i`) plus a process remainder `EVar(FreeVar(k))` (binding `rest`,
/// the residual soup). The production `spatial_matcher_pda::ListMachine`, after `sub_pars`
/// supplies connective remainder candidates, assigns the `k` send-patterns to `k` carrier sends
/// in ANY order and binds the residual
/// to the remainder — the order-independent multiset match — inside one atomic `consume`.
///
/// The remainder is `new_freevar_par(k)`, whose `EVar(FreeVar(k))` in `exprs` is exactly the
/// `var_level` the spatial matcher reads (`spatial_matcher_pda.rs`); element `i` binds `FreeVar(i)`.
pub fn ac_bag_pattern(language_fingerprint: &str, op: &str, k: usize) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, op);
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
    let mut elements = Vec::with_capacity(arity + 2);
    elements.push(tag);
    // E-2-D: the reflected op-headed element carries the marker at index 1 — this positional
    // pattern absorbs it with a wildcard (the paired match is over head + args, not the marker),
    // keeping the arg FreeVar σ levels unchanged (a wildcard binds nothing).
    if is_marked_object_label(op) {
        elements.push(new_wildcard_par(Vec::new(), true));
    }
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
/// ORDER-INDEPENDENTLY (native `spatial_matcher_pda::ListMachine` over `ParSet`) + binds the residual set to the
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
    let remainder = Var {
        var_instance: Some(VarInstance::FreeVar(element_slots as i32)),
    };
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
    for (index, (channel, hole)) in premise_channels.iter().zip(reduced_holes).enumerate() {
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

/// Legacy structural-path location helper retained for the quarantined E-6a comparison
/// treatment and external compatibility. Production [`spread_term_par`] and the positional
/// automata use the shared fixed-width [`SubjectLocationIndex`] channel ABI instead.
///
/// Per INV-7 / `rem:fresh` ("freshness is supplied as rho supplies all freshness,
/// by quoting … no ν, no central allocator") the whole location scheme is ν-free:
/// location channels are deterministic ground names, never fresh `New` bindings.
/// `root_location` is the quoted per-site nonce ρ of the `⌜(ρ,ℓ)⌝` idiom — a plain
/// string IS its quote — so distinct redex sites within ONE language use disjoint channel
/// prefixes.
///
/// ★ `root_location` alone is NOT a cross-language separator, and this doc comment used to
/// imply otherwise. It is a plain caller-supplied `&str`, never derived from the
/// fingerprint — `spread_term_par(term, language_fingerprint, root_location)` takes the
/// fingerprint FOR THE TAGS and the location as an INDEPENDENT argument — so two languages
/// spreading at the same site string (`"site0"`, or a `rewrite/{label}/…` path built from a
/// constructor name they happen to share) collided on every `loc:`/`col:`/`cap:` channel of
/// that site.
///
/// A pure `loc:` collision alone would be destructive starvation rather than a wrong
/// firing: `wrap_descent` builds `for(h <- loc){ match h { op̲ => … } }`, so the receive
/// binds `h` UNCONDITIONALLY and the tag test is a `match` INSIDE the continuation with a
/// single ground arm and no wildcard — the COMM fires, the match finds no arm, and both
/// languages starve. But `cap:` is not an independent family: it is derived from the SAME
/// `root_location` by [`collapse_capture_location`], and `rho_net_automaton` derives both
/// roots together. A σ capture CANNOT discriminate by construction — `wrap_children` /
/// `wrap_capture_chain` bind the fully collapsed subterm, because a pattern variable must
/// accept an arbitrary subterm, so there is no tag to match on and there could not be one.
/// Language B's capture receiver therefore consumed language A's collapsed subterm and
/// instantiated B's RHS with A's operand.
///
/// Hence INV-S6: the fingerprint scopes this compatibility key, and every derived child path
/// inherits it because [`spread_child_location`] composes from the parent. See
/// [`crate::rho_net::scoped_channel_name`].
pub fn spread_root_location(language_fingerprint: &str, root_location: &str) -> String {
    crate::rho_net::scoped_channel_name("loc", language_fingerprint, root_location)
}

/// Legacy structural child-path helper. It remains the one component spelling used by the
/// E-6a PathMap comparison treatment, but production spread/matcher rendezvous is keyed by
/// [`SubjectPosition`] and does not copy ancestor paths.
pub fn spread_child_location(parent: &str, op: &str, index: usize) -> String {
    format!("{parent}/{op}.{index}")
}

/// Legacy structural-path CHAIN collapse helper retained for compatibility. Production spread
/// derives `col:` directly from its shared [`SubjectPosition`].
///
/// Fingerprint-scoped per INV-S6 ([`crate::rho_net::scoped_channel_name`]), from the SAME
/// `(language_fingerprint, root_location)` pair as [`spread_root_location`] — the three
/// matching-τ families are ONE key, so scoping them apart would be a latent divergence.
pub fn collapse_chain_location(language_fingerprint: &str, root_location: &str) -> String {
    crate::rho_net::scoped_channel_name("col", language_fingerprint, root_location)
}

/// Legacy structural-path CAPTURE collapse helper retained for compatibility. Production spread
/// derives `cap:` directly from its shared [`SubjectPosition`]. A capture carries the same
/// `⟦subtree⟧` value as the chain channel but on a disjoint name, so the parent's chain read and
/// the automaton's capture read never race for one value (each is consumed at most once — O1).
///
/// ★ THIS is the channel the S6 cross-fingerprint wrong firing rode on, and it is the one
/// family that cannot defend itself: the value it carries is a fully collapsed subterm bound
/// by a pattern VARIABLE, which must accept an arbitrary subterm, so no tag test is possible
/// at the capture. Scoping the name is therefore the only available discriminator. Derived
/// from the SAME `(language_fingerprint, root_location)` pair as [`spread_root_location`].
pub fn collapse_capture_location(language_fingerprint: &str, root_location: &str) -> String {
    crate::rho_net::scoped_channel_name("cap", language_fingerprint, root_location)
}

/// The BARE AC soup carrier channel for operand constructor `op` — `ac:{fingerprint}/{op}`,
/// the process-soup name a bag's element sends ride when the carrier is NOT site-keyed.
///
/// THE single derivation point for the bare `ac:` family (fourteen call sites across
/// `rho_net_lower` and `rho_net_drive` reached it independently before S6, all of them
/// spelling `format!("ac:{op}")`). Its site-keyed sibling [`ac_carrier_channel`] inherits
/// its scope from the `loc:` channel instead and needs no fingerprint of its own.
///
/// ★ Keyed by the BARE constructor label, this was the family that collided WITHOUT an
/// attacker and without even a shared site string: two languages that each declare an AC
/// constructor named `PPar` shared `@"ac:PPar"`, and `PPar` is the actual name used in
/// `rholang` and in every AC/Ambient demo. Co-installing two process calculi collided here
/// BY DEFAULT.
pub fn ac_soup_channel(language_fingerprint: &str, op: &str) -> String {
    crate::rho_net::scoped_channel_name("ac", language_fingerprint, op)
}

/// The SITE-KEYED AC carrier channel of a HashBag AC operand bag at the spread node whose `loc:`
/// head-tag channel is `loc_channel`, for operand constructor `op` — the `ac:`-kind quoted name the
/// match driver ([`ac_match_call_par`]) publishes the bag's process-soup on and the co-installed
/// [`ac_sigma_receiver_par`] reads from.
///
/// The site key is inherited from `loc_channel` (the exact indexed identity the spread and
/// automaton already share), so two same-`op` bags at distinct positions get disjoint carriers —
/// Red-team #5: without the site key two same-`op` bags'
/// soups would intermingle on one `ac:op` channel and the native matcher could pick cross-bag
/// elements, a latent soundness bug. Both the carrier delivery and the co-installed receiver derive
/// the channel through THIS one helper, so they rendezvous on exactly one bag's soup.
///
/// INV-S6: this family takes NO fingerprint argument because it already inherits one —
/// `loc_channel` is already fingerprint-scoped, so the carrier inherits that scope. The bare
/// (non-site-keyed) sibling has no such
/// parent and scopes itself via [`ac_soup_channel`].
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
/// deterministic fixed-width `loc:` channel from the shared [`SubjectLocationIndex`], which the
/// automaton reads to DISPATCH / DESCEND. Child positions are exact integer identities assigned
/// once by the same prefix-compressed topology; no absolute ancestor path is materialized. This
/// is the ν-free scheme (INV-7): a flat parallel composition of ground sends — no `New` — and the
/// head-tag message carries the tag alone, never child channels.
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
    let locations = SubjectLocationIndex::new(term);
    spread_term_par_indexed(&locations, language_fingerprint, root_location)
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
    let by_op: HashMap<&str, &RhoNetAcMatchEntry> = entries
        .iter()
        .map(|entry| (entry.op.as_str(), entry))
        .collect();
    let locations = SubjectLocationIndex::new(subject);
    ac_match_install_at(
        &locations,
        SubjectPosition::ROOT,
        root_site,
        &by_op,
        out_channel,
        language_fingerprint,
    )
}

/// Recursively LOCATE + co-install the AC receivers for `node` at the position whose `loc:` head-tag
/// channel is `loc_channel` (the SAME location derivation the spread uses). See
/// [`ac_match_call_par`].
fn ac_match_install_at(
    locations: &SubjectLocationIndex<'_>,
    start: SubjectPosition,
    root_site: &str,
    by_op: &HashMap<&str, &RhoNetAcMatchEntry>,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    let mut par = Par::default();
    locations.walk(start, |position, node| {
        // A HashBag has no positional child descent, whether or not its op is admitted.
        if !matches!(node.coll_type, Some(CollectionType::HashBag)) {
            return true;
        }
        if let Some(entry) = by_op.get(node.constructor.as_str()) {
            let loc_channel = locations.channel("loc", language_fingerprint, root_site, position);
            let carrier = ac_carrier_channel(&loc_channel, &node.constructor);
            let receiver = ac_sigma_receiver_par_with_condition(
                entry.kind.clone(),
                language_fingerprint,
                &entry.op,
                entry.arity,
                entry.rhs_par.clone(),
                new_gstring_par(carrier.clone(), Vec::new(), false),
                entry.condition.clone(),
            );
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
            let preceding = std::mem::take(&mut par);
            par = preceding.append(receiver).append(delivery);
        }
        false
    });
    par
}

pub(crate) fn spread_term_par_indexed(
    locations: &SubjectLocationIndex<'_>,
    language_fingerprint: &str,
    root_location: &str,
) -> Par {
    enum SpreadTask {
        Visit { position: SubjectPosition },
        Collapse { position: SubjectPosition, head_tag: Par },
    }

    let mut tasks = vec![SpreadTask::Visit { position: SubjectPosition::ROOT }];
    // This is an evaluation stack, not a per-node table.  Its live length is
    // bounded by pending sibling results (maximum active frontier), and is
    // constant on a unary spine.  Reserving `locations.len()` here would add
    // an artificial linear RSS slope to deep subjects.
    let mut ground_values = Vec::new();
    let mut output = Par::default();

    while let Some(task) = tasks.pop() {
        match task {
            SpreadTask::Visit { position } => {
                let term = locations.term(position);
                let location =
                    locations.channel("loc", language_fingerprint, root_location, position);
                let chain_location =
                    locations.channel("col", language_fingerprint, root_location, position);
                let capture_location =
                    locations.channel("cap", language_fingerprint, root_location, position);
                // Stage 4 (S-AC): an AC operand collection has no positional child structure.
                // Publish only its native carrier on `col:`/`cap:` and treat it as one completed,
                // conservatively non-ground child result for its positional parent.
                if matches!(
                    term.coll_type,
                    Some(
                        CollectionType::HashBag | CollectionType::HashSet | CollectionType::HashMap
                    )
                ) {
                    let carrier = reflect_ac_collection_par(term, language_fingerprint);
                    let free = carrier.locally_free.clone();
                    let chain = new_send_par(
                        new_gstring_par(chain_location, Vec::new(), false),
                        vec![carrier.clone()],
                        false,
                        free.clone(),
                        false,
                        free.clone(),
                        false,
                    );
                    let capture = new_send_par(
                        new_gstring_par(capture_location, Vec::new(), false),
                        vec![carrier],
                        false,
                        free.clone(),
                        false,
                        free,
                        false,
                    );
                    extend_parallel_par(&mut output, chain);
                    extend_parallel_par(&mut output, capture);
                    ground_values.push(false);
                    continue;
                }

                // The head send is a pre-order event. The matching post-order Collapse event is
                // scheduled below every child, exactly preserving the recursive component order.
                let head_tag = GPrivateBuilder::new_par_from_string(reflect_tag(
                    language_fingerprint,
                    &term.constructor,
                ));
                extend_parallel_par(
                    &mut output,
                    new_send_par(
                        new_gstring_par(location, Vec::new(), false),
                        vec![head_tag.clone()],
                        false,
                        Vec::new(),
                        false,
                        Vec::new(),
                        false,
                    ),
                );

                tasks.push(SpreadTask::Collapse { position, head_tag });
                for child in locations.children(position).rev() {
                    tasks.push(SpreadTask::Visit { position: child });
                }
            },
            SpreadTask::Collapse { position, head_tag } => {
                let term = locations.term(position);
                let first_child = ground_values
                    .len()
                    .checked_sub(term.children.len())
                    .expect("spread PDA lost a child groundness result");
                let children_ground = ground_values[first_child..].iter().all(|ground| *ground);
                ground_values.truncate(first_child);
                let ground = if term.constructor == FREE_VAR_REFLECT_LABEL {
                    true
                } else {
                    term.constructor != BOUND_VAR_REFLECT_LABEL && children_ground
                };
                let marker = is_marked_object_label(&term.constructor)
                    .then(|| ground_marker_tag_par(language_fingerprint, ground));
                let chain_location =
                    locations.channel("col", language_fingerprint, root_location, position);
                let capture_location =
                    locations.channel("cap", language_fingerprint, root_location, position);
                let child_chain_channels: Vec<String> = locations
                    .children(position)
                    .map(|child| {
                        locations.channel("col", language_fingerprint, root_location, child)
                    })
                    .collect();
                extend_parallel_par(
                    &mut output,
                    collapse_publish(
                        &chain_location,
                        &capture_location,
                        head_tag,
                        marker,
                        &child_chain_channels,
                    ),
                );
                ground_values.push(ground);
            },
        }
    }

    debug_assert_eq!(ground_values.len(), 1);
    output
}

/// Move one parallel `Par` component into an accumulator without cloning the accumulator.
///
/// `models::Par::append` intentionally takes `&self`, so a left fold over it clones every vector
/// accumulated so far. Code generators routinely assemble large flat parallel compositions; this
/// move-based equivalent preserves every field's order and cached union while keeping assembly
/// linear in the emitted artifact size.
fn extend_parallel_par(target: &mut Par, mut source: Par) {
    target.sends.append(&mut source.sends);
    target.receives.append(&mut source.receives);
    target.news.append(&mut source.news);
    target.exprs.append(&mut source.exprs);
    target.matches.append(&mut source.matches);
    target.unforgeables.append(&mut source.unforgeables);
    target.bundles.append(&mut source.bundles);
    target.connectives.append(&mut source.connectives);
    target.conditionals.append(&mut source.conditionals);
    target.locally_free = union(
        std::mem::take(&mut target.locally_free),
        std::mem::take(&mut source.locally_free),
    );
    target.connective_used |= source.connective_used;
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
    marker: Option<Par>,
    child_chain_channels: &[String],
) -> Par {
    let n = child_chain_channels.len();
    if n == 0 {
        // Leaf: ⟦leaf⟧ = EList[tag] (+ E-2-D marker at index 1 for a marked-object leaf);
        // two linear ground sends (chain + capture).
        let leaf_elements = match marker {
            Some(m) => vec![head_tag, m],
            None => vec![head_tag],
        };
        let collapsed = new_elist_par(leaf_elements, Vec::new(), false, None, Vec::new(), false);
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
    let mut elements = Vec::with_capacity(n + 2);
    elements.push(head_tag);
    // E-2-D: interpose the marker at index 1 for a marked-object node (a GPrivate marker has
    // empty `locally_free`, and the child BoundVar indices are join-binder-relative, NOT EList
    // positions, so the marker shifts nothing) — byte-identical to `reflect_ground_term_par`.
    if let Some(m) = marker {
        elements.push(m);
    }
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
/// `GPrivate` head tag is built exactly like the rholang bag ABI tag via
/// [`GPrivateBuilder::new_par_from_string`], and the `EList`'s `locally_free` is
/// the union of the tag's and every child's — mirroring `lower_rholang`'s bag
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
    reflect_term_par_env(pattern, vars, k, language_fingerprint, def)
}

/// The reserved reflection tag for a single-binder `Lambda` node — a synthetic
/// constructor label (`^lambda`) that cannot collide with any user constructor
/// (which is a Rust `Ident`, never containing `^`), so the tagged binder node is
/// distinct from every `Apply` node AND from any user `GString` term data. The
/// multi-binder tag is `^multilambda`; a bound-variable occurrence uses `^bound`.
///
/// These are `pub` so the Stage-4 S-binder MATCH-side reflection (the macro
/// `reflect_category_fn` in `macros/src/gen/runtime/rho_invocation.rs`) bakes the
/// SAME strings into the generated `Term → GroundTerm` reflection it emits, keeping
/// the reflected subject's tags coherent with the spread's `reflect_tag` and the
/// automaton's compiled entry ops (all three derive from these labels).
pub const LAMBDA_REFLECT_LABEL: &str = "^lambda";
pub const MULTILAMBDA_REFLECT_LABEL: &str = "^multilambda";
pub const BOUND_VAR_REFLECT_LABEL: &str = "^bound";
/// The reserved reflection tag for a FREE-variable occurrence — a `^free(name)` leaf
/// (Stage 4 S-binder). The runtime is already de-Bruijn, so a subject bound
/// occurrence reflects to `^bound(peano(scope))` and only a genuinely-free variable
/// reflects to `^free`; the `^` prefix keeps it unforgeable vs any user `Ident`.
pub const FREE_VAR_REFLECT_LABEL: &str = "^free";
/// The reserved Peano tags for a de-Bruijn `^bound` index (Stage 4 S-binder): the
/// scope offset `n` of a runtime `Var::Bound{scope,binder}` reflects to
/// `S(S(…(Z)))` with `n` `S`s — `^bound(peano(n))`. `Z`/`S` are ordinary (unquoted)
/// nullary/unary tags: the reserved-ness is carried by the enclosing `^bound`, and a
/// user constructor named `Z`/`S` only appears UNDER `^bound` in a bound-var leaf
/// (its own `Z`/`S` term reflects structurally, never mistaken for a Peano index).
/// ★ #36 S3. `^`-PREFIXED, so the reserved namespace is a prefix and the rule
/// `is_reserved_reflect_label(l) = l.starts_with('^')` is complete BY CONSTRUCTION.
///
/// These were the bare identifiers `Z` and `S`, which made them the only two members
/// of the reserved set that a user constructor could collide with — and
/// `S . x:Proc |- "s" "(" x ")" : Proc` already appears as a fixture in four places
/// in this tree, so the collision needed no attacker and no network.
///
/// The alternative — reserving the bare identifiers — would have made the namespace
/// rule "starts with `^`, OR is one of these magic words", a permanent special case
/// in every future safety argument, and would have REJECTED those four fixtures.
/// Prefixing costs two bytes per tag and makes the rule true.
pub const PEANO_ZERO_REFLECT_LABEL: &str = "^Z";
pub const PEANO_SUCC_REFLECT_LABEL: &str = "^S";

/// (A4) The reserved reflection tag PREFIX for an **identifier-text leaf** — a constructor
/// field carrying a captured token text (`m:Ident`, `v@Tok`; `OpaqueLeafKind::TokenText`).
///
/// Such a field has no positional ground image the M-reflect walk can RECURSE into: it is not
/// a subterm, it is atomic data. It does, however, have a perfectly good NULLARY image, which
/// is the shape [`reflect_category_fn`]'s `Literal` arm already emits for a native-scalar leaf
/// (`GroundTerm::new(format!("{}({:?})", label, value), vec![])` — `"NumLit(8)"`). The tag
/// BAKES the text, so `l.nth(0)` and `l.last(0)` reflect to structurally distinct ground
/// terms and the in-Rho set automaton can LOCATE either.
///
/// The emitted tag is `^ident("nth")` — this prefix, then the text under `{:?}`. `^`-prefixed
/// ⟹ unforgeable versus any user `Ident` (a Rust identifier never contains `^`), so it
/// satisfies [`mettail_ast::validation::is_reserved_reflect_label`] exactly as `^lambda` /
/// `^bound` / `^free` do; and an identifier's own charset is dot-free, so the decoders'
/// `{fp}.{label}` split stays unambiguous.
///
/// ★ WHY THIS IS NOT COSMETIC. Without it, `is_structural_category_field` answers `false` for
/// a token-text field, so its host constructor fails reflection CLOSED and every firing on it
/// routes to σ-replay. That costs nothing while only `PFlt` is affected — but a language that
/// collapses a large method surface onto ONE `recv . name ( args )` constructor would trade
/// its whole *located* in-Rho method match for σ-replay, silently and with no diagnostic.
pub const IDENT_TEXT_REFLECT_LABEL: &str = "^ident";

/// Exact byte-string reflection prefix and closed PathMap mode labels. These
/// live in the reserved namespace and are shared by generated static carriers
/// and GrammarCore dynamic reflection.
pub const BYTES_REFLECT_LABEL: &str = "^dynamic-bytes:";
pub const PATHMAP_EMPTY_REFLECT_LABEL: &str = "^pathmap-empty";
pub const PATHMAP_SET_REFLECT_LABEL: &str = "^pathmap-set";
pub const PATHMAP_MAP_REFLECT_LABEL: &str = "^pathmap-map";

/// E-2 MECHANISM D — the reflected-ABI HEREDITARY-GROUND MARKER (reflected-ABI v2).
///
/// Every reflected OBJECT node (`is_marked_object_label`) carries, as its FIRST element
/// right after the head tag, one of these two distinguished GPrivate tokens:
///
/// ```text
/// ⟦f(t₁,…,tₙ)⟧ = EList[ GPrivate(reflect_tag(f)), GROUND-or-NONGROUND, ⟦t₁⟧, …, ⟦tₙ⟧ ]
/// ```
///
/// `^gnd` = HEREDITARILY GROUND (the subtree contains NO `^bound` de-Bruijn leaf, so
/// `^subst`/`^shift` is the IDENTITY on it — the FV `InRhoCreeperTrace.oground_subst_id`
/// / `oground_shift_id`), `^nog` = NOT (provably) ground. The `^subst`/`^shift` receiver
/// ENTRY guard fires `ret!(t)` immediately on `^gnd`, skipping the dispatch + reassembly
/// joins for the whole closed subtree. `^`-prefixed + fingerprint-namespaced ⟹ unforgeable
/// vs any user `Ident` and vs every other reserved tag; dot-free ⟹ the decoders' `{fp}.{label}`
/// split is unambiguous. The marker is SOUND under-approximation: `^gnd` ⟹ ground, but a
/// runtime-reassembled node conservatively carries `^nog` (never wrong, only a missed skip).
///
/// This is the reflected-ABI VERSION BUMP: pre-D reflected object nodes were `EList[tag,
/// children…]`; v2 interposes the marker at index 1. Machinery labels (Peano `^Z`/`^S`, `^cmp`
/// results, reserved reduction tags) are NOT marked (`is_marked_object_label` = false), so the
/// numeric cascade is byte-unchanged.
pub const GROUND_MARK_REFLECT_LABEL: &str = "^gnd";
pub const NONGROUND_MARK_REFLECT_LABEL: &str = "^nog";

/// S2 — EVERY reserved reflect label, enumerated in ONE place.
///
/// The families were previously enumerated three times and never together:
/// [`crate::rho_net_subst_trs::reserved_subst_trs_labels`] (19, the C2
/// object-congruence exclusion set),
/// [`crate::rho_net_pattern_guard::respread_reserved_labels`]
/// (3, the R3 walker), and a scatter of loose constants (the markers, the `^cmp`
/// results, the float family, the Peano numerals) that no list contained. Nothing
/// ever asserted that the union satisfies the namespace rule
/// [`mettail_ast::validation::is_reserved_reflect_label`] the whole safety
/// argument rests on — and two members did not (the bare `Z`/`S`, until S3
/// renamed them to `^Z`/`^S`).
///
/// This is the census that makes that assertion possible. Adding a reserved label
/// without adding it here is caught by
/// `every_reserved_label_is_in_the_reserved_namespace`.
///
/// ★ THE CENSUS IS AN INVENTORY, NOT A SWITCH. It is read by tests only; nothing in
/// codegen branches on membership. That is exactly why the Peano numerals belong
/// here and NOT in [`crate::rho_net_subst_trs::reserved_subst_trs_labels`], which
/// IS a switch (it drives `object_congruence_constructors`). Wanting a label to be
/// censused is never a reason to add it to a switch; add it to this list.
pub fn all_reserved_reflect_labels() -> Vec<&'static str> {
    let mut labels: Vec<&'static str> = Vec::with_capacity(32);
    labels.extend(crate::rho_net_subst_trs::reserved_subst_trs_labels());
    // The `^respread` family is used by the production persistent-root PDA.
    labels.extend(crate::rho_net_pattern_guard::respread_reserved_labels());
    labels.extend([
        GROUND_MARK_REFLECT_LABEL,
        NONGROUND_MARK_REFLECT_LABEL,
        DRIVE_AC_RESERVED_LABEL,
        FLOAT_RESERVED_LABEL,
        FLOAT_HOIST_RESERVED_LABEL,
        FLOAT_MERGE_RESERVED_LABEL,
        PEANO_ZERO_REFLECT_LABEL,
        PEANO_SUCC_REFLECT_LABEL,
        // (A4) The identifier-text leaf tag PREFIX. Censused as the prefix because the
        // emitted tag is `^ident("<text>")` — text-dependent, so no `&'static str` names an
        // instance. The namespace assertion is about the RESERVED PREFIX, and every instance
        // inherits it: `format!("{}({:?})", "^ident", …)` starts with `^` for every text.
        IDENT_TEXT_REFLECT_LABEL,
        BYTES_REFLECT_LABEL,
        PATHMAP_EMPTY_REFLECT_LABEL,
        PATHMAP_SET_REFLECT_LABEL,
        PATHMAP_MAP_REFLECT_LABEL,
    ]);
    labels.sort_unstable();
    labels.dedup();
    labels
}

/// ★ THE KNOWN VIOLATORS of the reserved-namespace rule, named rather than omitted.
/// **EMPTY as of #36 S3 — the namespace rule is now complete by construction.**
///
/// [`all_reserved_reflect_labels`] is complete, and every member of it MUST satisfy
/// [`mettail_ast::validation::is_reserved_reflect_label`]. This list is the named
/// escape hatch for members that do not, so that a gap is VISIBLE IN CODE rather
/// than expressed as a silent omission from the census. It is empty, so
/// `every_reserved_label_is_in_the_reserved_namespace` now asserts the unqualified
/// claim, with no edit to the assertion itself.
///
/// # What it held, and why it is empty (the historical record)
///
/// It held the two bare identifiers `Z` and `S` — the Peano numeral encoding of a de
/// Bruijn scope offset, read by the `^cmp`/`^pred`/`^shiftk` receivers and carried in
/// the `^bound` payload. They were reserved IN FACT but not `^`-prefixed, so the
/// namespace rule did not cover them, and they were the ONLY two members of the
/// reserved set a user constructor could collide with.
///
/// That was a live defect, not a theoretical one: `S . x:Proc |- "s" "(" x ")" : Proc`
/// already appears as a fixture in four places in this tree, and a language declaring
/// natural-number constructors named `S`/`Z` collided from the macro frontend with no
/// attacker involved. Traced, the collision was fail-closed rather than wrong-answer —
/// [`shift_reflected_ground_term_by`] declines any σ value carrying an `S`/`Z` node under
/// a binder, and the `^gnd` short-circuit was permanently lost on such subtrees — but
/// "a language that names its successor `Succ` reduces and one that names it `S` does
/// not" is a name-dependent semantic difference, which is not a semantics anyone chose.
///
/// S3 renamed the two constants to `^Z`/`^S`
/// ([`PEANO_ZERO_REFLECT_LABEL`] / [`PEANO_SUCC_REFLECT_LABEL`]) and emptied this list.
/// The alternative — reserving the bare identifiers — would have made the namespace
/// rule "starts with `^`, OR is one of these magic words", a permanent special case in
/// every future safety argument, and would have REJECTED those four fixtures.
///
/// # Why it is retained rather than deleted
///
/// The assertion it feeds is written as "every censused label is in the namespace,
/// EXCEPT the named exceptions, and every named exception is itself censused". With
/// the list empty both halves are the strongest form of the claim. Deleting the hatch
/// would mean a future reserved family that cannot be `^`-prefixed (e.g. one whose tag
/// is dictated by an external ABI) has nowhere to declare itself and would be pushed
/// back into being a silent census omission — which is the failure mode this list was
/// created to end. Keeping it empty costs one function and preserves the escape.
pub fn reserved_labels_outside_the_namespace() -> [&'static str; 0] {
    []
}

/// The reserved reduction-channel / rule tags for the generated de-Bruijn substitution
/// term-rewriting system (Stage 4 S-binder SLICE 2a — the in-Rho β cascade). Each names one
/// reserved TRS receiver's rendezvous channel (`GPrivate(reflect_tag(fp, LABEL))`, unforgeable
/// vs any user `Ident`), and the whole set is the C2 object-congruence EXCLUSION set: an
/// object constructor may NOT reflect to any of these (else `^lambda` would receive a generic
/// congruence — losing the `S j` depth increment — causing non-confluence and variable capture).
/// See [`crate::rho_net_subst_trs`] (the receiver builders) and
/// [`crate::rho_net_subst_trs::reserved_subst_trs_labels`] (the assertion source).
///
/// `^sb`/`^shb` are the `^cmp`-result dispatch rules (`^subst(_,_,^bound n)` and
/// `^shift(_,^bound n)` after the comparison resolves). The spike / codegen INLINE their three
/// arms inside the `^subst`/`^shift` receivers (a `match cr { … }` on the returned `^cmp` result),
/// so they have no standalone channel; the labels are reserved so a user constructor named `sb`/
/// `shb` still cannot collide with the (future) split form.
pub const SUBST_RESERVED_LABEL: &str = "^subst";
pub const SHIFT_RESERVED_LABEL: &str = "^shift";
pub const CMP_RESERVED_LABEL: &str = "^cmp";
pub const SHIFTK_RESERVED_LABEL: &str = "^shiftk";
pub const PRED_RESERVED_LABEL: &str = "^pred";
pub const SB_RESERVED_LABEL: &str = "^sb";
pub const SHB_RESERVED_LABEL: &str = "^shb";

/// The reserved tags of the A-S5.2 in-Rho quiescence DRIVER (plan v2 §4, leg v).
///
/// `^drive` names the driver's persistent rendezvous channel
/// (`GPrivate(reflect_tag(fp, "^drive"))` — like every in-Rho-only rendezvous, unforgeable
/// and NOT host-readable). The other three name the driver's HOST-READABLE observation
/// channels, which are **GString** — `"{label}:{fp}"` via
/// [`crate::rho_net_drive::drive_fired_channel`] et al. (plan v2 §4.5 rationale: host
/// readback rides the proven GString `get_data` path; the `^` prefix + fingerprint suffix
/// keep them collision-free with user constructors, which are Rust `Ident`s). All four join
/// [`crate::rho_net_subst_trs::reserved_subst_trs_labels`], so the C2 object-congruence
/// exclusion assertion also guards them against any user-constructor collision.
pub const DRIVE_RESERVED_LABEL: &str = "^drive";
pub const DRIVE_ERR_RESERVED_LABEL: &str = "^drive-err";
pub const DRIVE_FUEL_RESERVED_LABEL: &str = "^drive-fuel";
pub const FIRED_RESERVED_LABEL: &str = "^fired";

/// The reserved PER-RULE AC-carrier tag PREFIX of the A-S5.5 driver AC arms (plan v2
/// §4.3.1): an admitted structural-AC / nested-structural-AC rule `R` fires through ONE
/// reserved `GPrivate` carrier channel `⌜^drive-ac:R⌝ = GPrivate(reflect_tag(fp,
/// "^drive-ac:R"))` — the fixed-channel persistent AC-carrier receiver (the driver-path
/// variant of the site-keyed `ac:` match receivers) rests on it. The `^` prefix keeps the
/// whole per-rule label family (`"^drive-ac:{RuleLabel}"`) collision-free with user
/// constructors (Rust `Ident`s contain neither `^` nor `:`); the BASE label joins
/// [`crate::rho_net_subst_trs::reserved_subst_trs_labels`] so the C2 assertion guards it
/// like every other reserved tag.
pub const DRIVE_AC_RESERVED_LABEL: &str = "^drive-ac";

/// The reserved tags of the A-S5.8 in-Rho `^float` receiver family (design
/// `a_s5_8_float_design_v1.md` §2) — the per-iteration binder-float canonicalizer that
/// constructively discharges the boundary-float premise for float-bearing languages.
///
/// `^float` names the DISPATCHER's persistent rendezvous channel
/// (`GPrivate(reflect_tag(fp, "^float"))`); the other two are per-constructor /
/// per-collection-op SATELLITE tag PREFIXES — `⌜^float-hoist:{C}⌝` (one per recognized
/// float-across-constructor equation's constructor, e.g. Ambient `PIn`/`POut`/`POpen`/
/// `PAmb`) and `⌜^float-merge:{op}⌝` (one per recognized collection-form float equation's
/// bag op, e.g. Ambient `PPar` — the ScopeExtrusion merge). The `^` prefix keeps the whole
/// `:`-suffixed families collision-free with user constructors (Rust `Ident`s contain
/// neither `^` nor `:`); all three BASE labels join
/// [`crate::rho_net_subst_trs::reserved_subst_trs_labels`] (registry 16 → 19), so the C2
/// object-congruence exclusion assertion guards them like every other reserved tag.
pub const FLOAT_RESERVED_LABEL: &str = "^float";
pub const FLOAT_HOIST_RESERVED_LABEL: &str = "^float-hoist";
pub const FLOAT_MERGE_RESERVED_LABEL: &str = "^float-merge";

/// Reflect an RHS pattern term to a normalized `Par`, threading a **binder
/// environment** (the RHS binders currently in scope, De Bruijn stack). A variable
/// occurrence that names an in-scope binder reflects to a distinguished bound-var
/// leaf (`EList[GPrivate(reflect_tag(^bound)), GString(name)]`), NOT a σ-slot
/// `BoundVar`; a free variable reflects to its σ-slot index; any other free name
/// fails closed. This is the RHS dual of [`lower_lhs_vars`]'s De Bruijn
/// environment.
fn reflect_term_par_env(
    pattern: &Pattern,
    vars: &[Ident],
    k: usize,
    language_fingerprint: &str,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    enum Task<'a> {
        Visit(&'a Pattern),
        VisitVariable(&'a Ident),
        AssembleApply {
            label: String,
            child_count: usize,
        },
        AssembleBinder {
            label: &'static str,
            binders: &'a [Ident],
        },
        AssembleHashBag {
            op: String,
            fixed_count: usize,
            has_rest: bool,
        },
        ExitBinders(&'a [Ident]),
    }

    let mut var_index = HashMap::new();
    for (index, var) in vars.iter().enumerate() {
        var_index.entry(var.to_string()).or_insert(index);
    }
    let mut bound_counts: HashMap<String, usize> = HashMap::new();
    let mut tasks = vec![Task::Visit(pattern)];
    // Each result carries the reflected Par and this pattern node's hereditary-ground bit. The
    // latter is folded once bottom-up, eliminating the former subtree rescan at every ancestor.
    let mut values: Vec<(Par, bool)> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(name))) | Task::VisitVariable(name) => {
                let name_text = name.to_string();
                let par = if bound_counts.contains_key(&name_text) {
                    reflect_bound_var_leaf(name, language_fingerprint)
                } else if let Some(index) = var_index.get(&name_text).copied() {
                    new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)
                } else {
                    return Err(UnsupportedFamily::DanglingRhsVariable);
                };
                values.push((par, false));
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { constructor, args })) => {
                if let (Some(def), [Pattern::Collection { coll_type, elements, rest }]) =
                    (def, args.as_slice())
                {
                    if resolve_collection_kind(def, constructor, coll_type.as_ref())
                        == Some(CollectionType::HashBag)
                    {
                        tasks.push(Task::AssembleHashBag {
                            op: constructor.to_string(),
                            fixed_count: elements.len(),
                            has_rest: rest.is_some(),
                        });
                        if let Some(rest) = rest {
                            tasks.push(Task::VisitVariable(rest));
                        }
                        tasks.extend(elements.iter().rev().map(Task::Visit));
                        continue;
                    }
                }
                tasks.push(Task::AssembleApply {
                    label: constructor.to_string(),
                    child_count: args.len(),
                });
                tasks.extend(args.iter().rev().map(Task::Visit));
            },
            Task::Visit(Pattern::Term(PatternTerm::Lambda { binder, body })) => {
                let binders = std::slice::from_ref(binder);
                *bound_counts.entry(binder.to_string()).or_insert(0) += 1;
                tasks.push(Task::AssembleBinder { label: LAMBDA_REFLECT_LABEL, binders });
                tasks.push(Task::ExitBinders(binders));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(Pattern::Term(PatternTerm::MultiLambda { binders, body })) => {
                for binder in binders {
                    *bound_counts.entry(binder.to_string()).or_insert(0) += 1;
                }
                tasks.push(Task::AssembleBinder {
                    label: MULTILAMBDA_REFLECT_LABEL,
                    binders,
                });
                tasks.push(Task::ExitBinders(binders));
                tasks.push(Task::Visit(body));
            },
            Task::Visit(Pattern::Term(
                PatternTerm::MultiSubst { .. } | PatternTerm::Subst { .. },
            )) => return Err(UnsupportedFamily::Substitution),
            Task::Visit(Pattern::Collection { .. }) => {
                return Err(UnsupportedFamily::CollectionAc);
            },
            Task::Visit(Pattern::Map { .. }) => return Err(UnsupportedFamily::MapAc),
            Task::Visit(Pattern::Zip { .. }) => return Err(UnsupportedFamily::ZipAc),
            Task::Visit(Pattern::IndexedVec { .. }) => {
                return Err(UnsupportedFamily::IndexedVecOrdered);
            },
            Task::ExitBinders(binders) => {
                for binder in binders {
                    let name = binder.to_string();
                    let count = bound_counts
                        .get_mut(&name)
                        .expect("reflection PDA exited an inactive binder");
                    *count -= 1;
                    if *count == 0 {
                        bound_counts.remove(&name);
                    }
                }
            },
            Task::AssembleApply { label, child_count } => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("reflection PDA lost an application child");
                let children = values.split_off(first_child);
                let ground = children.iter().all(|(_, ground)| *ground);
                let tag =
                    GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &label));
                let mut elements = Vec::with_capacity(child_count + 2);
                let mut locally_free = tag.locally_free.clone();
                elements.push(tag);
                if is_marked_object_label(&label) {
                    elements.push(ground_marker_tag_par(language_fingerprint, ground));
                }
                for (child, _) in children {
                    locally_free = union(locally_free, child.locally_free.clone());
                    elements.push(child);
                }
                values.push((
                    new_elist_par(elements, locally_free.clone(), false, None, locally_free, false),
                    ground,
                ));
            },
            Task::AssembleBinder { label, binders } => {
                let (body, body_ground) = values.pop().expect("reflection PDA lost a binder body");
                let tag =
                    GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, label));
                let mut elements = Vec::with_capacity(binders.len() + 3);
                let mut locally_free = tag.locally_free.clone();
                elements.push(tag);
                elements.push(ground_marker_tag_par(language_fingerprint, body_ground));
                for binder in binders {
                    let leaf = reflect_bound_var_leaf(binder, language_fingerprint);
                    locally_free = union(locally_free, leaf.locally_free.clone());
                    elements.push(leaf);
                }
                locally_free = union(locally_free, body.locally_free.clone());
                elements.push(body);
                values.push((
                    new_elist_par(elements, locally_free.clone(), false, None, locally_free, false),
                    body_ground,
                ));
            },
            Task::AssembleHashBag { op, fixed_count, has_rest } => {
                let result_count = fixed_count + usize::from(has_rest);
                let first_child = values
                    .len()
                    .checked_sub(result_count)
                    .expect("reflection PDA lost a HashBag child");
                let mut children = values.split_off(first_child).into_iter();
                let channel = ac_soup_channel(language_fingerprint, &op);
                let mut soup = Par::default();
                for (reflected, _) in children.by_ref().take(fixed_count) {
                    let free = reflected.locally_free.clone();
                    extend_parallel_par(
                        &mut soup,
                        new_send_par(
                            new_gstring_par(channel.clone(), Vec::new(), false),
                            vec![reflected],
                            false,
                            free.clone(),
                            false,
                            free,
                            false,
                        ),
                    );
                }
                if has_rest {
                    let (rest, _) = children
                        .next()
                        .expect("reflection PDA lost a HashBag remainder");
                    extend_parallel_par(&mut soup, rest);
                }
                values.push((soup, false));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values.pop().expect("reflection PDA produced no result").0)
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
    // E-2-D: `^bound` is the substitutable de-Bruijn leaf — NEVER hereditarily ground (`^nog`).
    new_elist_par(
        vec![tag, ground_marker_tag_par(language_fingerprint, false), name_leaf],
        locally_free.clone(),
        false,
        None,
        locally_free,
        false,
    )
}

// RETIRED (Stage 4 S-binder SLICE 2a): the host-σ-slot substitution-scope resolver.
//
// This resolved a substitution's scope variable to its σ-slot `BoundVar`, so the σ-receiver body
// forwarded that slot — into which the host (Dovetail, model-b) injected the CONTRACTUM (the
// capture-avoiding substitution `RHS[σ]` it computed). The in-Rho β now COMPUTES the reduct with the
// generated de-Bruijn TRS (`crate::rho_net_subst_trs`), driven by the β SEED (`subst_seed_receiver_par`),
// so the receiver no longer forwards a host reduct — it seeds `^subst(⟦Z⟧, a, b, out)` with the RAW
// captured body `b`. The host-contractum path is therefore incompatible with the seed and retired.
//
// Kept (commented) for reference / the σ-replay fallback, per the "disable-don't-delete" rule: were a
// future slice to re-enable a host-σ-replay for substitution, it would need a SEED-compatible raw-σ
// injection (the RAW matched body, NOT the contractum). Its former call sites — the `reflect_term_par_env`
// `Subst`/`MultiSubst` arms — now fail closed (`UnsupportedFamily::Substitution`).
//
// fn reflect_subst_scope_slot(
//     scope: &Pattern,
//     vars: &[Ident],
//     k: usize,
// ) -> Result<Par, UnsupportedFamily> {
//     match scope {
//         Pattern::Term(PatternTerm::Var(name)) => match vars.iter().position(|var| var == name) {
//             Some(index) => Ok(new_boundvar_par(rhs_var_index(k, index), Vec::new(), false)),
//             None => Err(UnsupportedFamily::Substitution),
//         },
//         // A non-variable scope (a literal binder body / nested term) has no single σ-slot
//         // that the host can fill with one reduct — out of scope this slice, fail closed.
//         _ => Err(UnsupportedFamily::Substitution),
//     }
// }

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
        Pattern::IndexedVec { .. } => Some(UnsupportedFamily::IndexedVecOrdered),
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
/// native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders), binding the `k`
/// element σ slots (`FreeVar(0..k-1)`),
/// the residual `rest` (`FreeVar(k)`), and `out` (`FreeVar(k+1)`); the body fires `rhs_par` on
/// `out` (`BoundVar(0)`). `rhs_par` = `⟦R⟧σ` must reference element `i` as `BoundVar(k+1-i)` and
/// `rest` as `BoundVar(1)` (the reverse De Bruijn over the `k+2` bind free vars). Verified end to
/// end by `ac_receiver_fires_the_matched_element_on_the_dynamic_out`.
pub fn ac_sigma_receiver_par(
    language_fingerprint: &str,
    op: &str,
    k: usize,
    rhs_par: Par,
    source: Par,
) -> Par {
    ac_sigma_receiver_par_with_condition(
        CollectionType::HashBag,
        language_fingerprint,
        op,
        k,
        rhs_par,
        source,
        None,
    )
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
    language_fingerprint: &str,
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
                ac_collection_pattern(kind, language_fingerprint, op, k),
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
                let mut par = Par::default();
                par.exprs = vec![and];
                par.locally_free = union_free;
                par.connective_used = false;
                par
            },
        });
    }
    // ★ COMPILE-TIME GUARD DISCHARGE — ASSERT ONLY, NEVER BRANCH. Every conjunct is an
    // `EEq(BoundVar_i, BoundVar_j)` over the AC receiver's OWN element slots: payload-dependent
    // by construction, 0% dischargeable. See `crate::guard_closure` and
    // `mettail_rholang_runtime::guard_discharge`.
    debug_assert!(
        condition
            .as_ref()
            .is_none_or(|cond| !crate::guard_closure::is_binder_closed(cond)),
        "an AC non-linear consistency guard is EEq over the receiver's own element slots and \
         can never be binder-closed"
    );
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
    Some(ac_sigma_receiver_par_with_condition(
        kind,
        language_fingerprint,
        &op,
        k,
        rhs,
        source,
        condition,
    ))
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
    pattern_kind
        .or(resolved_kind)
        .cloned()
        .unwrap_or(CollectionType::HashBag)
}

/// Resolve the collection kind a CONSTRUCTOR declares, keyed on the op label, from EITHER
/// declaration syntax:
///
/// * the NEW judgement form `op . ps:HashBag(..) |- ..` — the kind sits in a `term_context`
///   collection parameter (the type alias is inlined to a `TypeExpr::Collection`); this scan stays
///   PRIMARY, so every already-admitted (term-context-declared) language resolves byte-identically;
/// * the old-BNFC production form `op . Cat ::= HashBag(Cat) sep ".." delim ".." ".."` (the
///   production `Ambient` `PPar`, `languages/src/ambient.rs`) — `term_context` is `None` while the
///   kind sits in `rule.items` as a [`mettail_ast::grammar::GrammarItem::Collection`]; the FIRST
///   such item is the A-S5.3 fallback. `items` is the uniform source for both forms
///   (`convert_term_context_to_items` populates it for the new syntax too), but term-context stays
///   the primary read to keep the admitted corpus byte-identical.
///
/// The parser leaves a rewrite pattern collection's `coll_type` as `None` ("inferred from the
/// enclosing constructor's grammar"), so BOTH the AC LHS un-skip ([`resolve_ac_collection_type`])
/// AND the AC bag-valued RHS reflection ([`reflect_term_par_env`], Stage AC2b) resolve it here.
/// Returns `None` when `op` is not a constructor over a collection parameter under EITHER form — so
/// a non-collection or unknown constructor is never mis-classified as a HashBag.
pub(crate) fn resolve_constructor_collection_type(
    def: &LanguageDef,
    op: &str,
) -> Option<CollectionType> {
    let rule = def.terms.iter().find(|rule| rule.label == op)?;
    rule.term_context
        .as_ref()
        .and_then(|params| {
            params.iter().find_map(|param| match param {
                mettail_ast::grammar::TermParam::Simple {
                    ty: mettail_ast::types::TypeExpr::Collection { coll_type, .. },
                    ..
                } => Some(coll_type.clone()),
                _ => None,
            })
        })
        .or_else(|| {
            // A-S5.3 (leg ii): the `::=`-declared fallback — the first grammar-item collection.
            rule.items.iter().find_map(|item| match item {
                mettail_ast::grammar::GrammarItem::Collection { coll_type, .. } => {
                    Some(coll_type.clone())
                },
                _ => None,
            })
        })
}

/// Resolve the collection kind the AC rule's constructor declares (`op . ps:HashBag(..) |- ..`) —
/// [`resolve_constructor_collection_type`] keyed on the LHS `Apply`'s constructor. Returns `None`
/// when the LHS is not a constructor application.
pub(crate) fn resolve_ac_collection_type(
    def: &LanguageDef,
    left: &Pattern,
) -> Option<CollectionType> {
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
/// reflection ([`reflect_term_par_env`]) agrees with the AC LHS un-skip on the operand kind.
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
//     Stage AC2b process-soup carrier (`reflect_term_par_env` HashBag shape): the reduct is the one
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

/// (D10) One fixed element of a Comm rule's AC bag REDUCT, in RHS order. The reduct admits `m ≥ 1`
/// elements: EXACTLY ONE host-computed substitution plus `m - 1` σ-delivered LHS variables. `m = 1`
/// is the ASYNCHRONOUS communication (Rholang / `CommDemo`); `m = 2` is the omnibus's SYNCHRONOUS π
/// `Comm`, whose output `n!m.q` carries a continuation that runs in parallel with the substituted
/// receive continuation. The Rho mirror of `dovetail_report::CommReductElement`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CommReduct {
    /// The HOST-COMPUTED substitution `(eval scope arg)` = `cont[Q/y]`, delivered at its own
    /// receive-bind slot (the receiver FORWARDS it, never fabricates it).
    Substitution,
    /// A σ-DELIVERED reduct element: a bare LHS-element argument recovered directly from the
    /// firing's σ, exactly as [`StructuralAcShape::reduct_vars`].
    Var(Ident),
}

/// The recognized shape of the canonical single-receive Rholang COMMUNICATION rule
/// `op{ E0, E1, ...rest } ~> op{ r_0, …, r_{m-1}, ...rest }`: two STRUCTURED constructor elements
/// `E0`/`E1` sharing exactly one NON-LINEAR channel variable `N` (each occurrence a distinct slot),
/// a with-rest remainder, and an RHS whose `m ≥ 1` fixed elements are EXACTLY ONE substitution
/// `(eval scope arg)` over LHS variables (the receive continuation `scope` and the sent name `arg`)
/// plus `m - 1` bare LHS variables. Returned only for this shape; every other structured /
/// non-linear AC rewrite (e.g. Ambient's `OpenRule`, whose RHS is PURELY structural — no
/// substitution at all) declines and stays on its existing path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommShape {
    pub op: String,
    pub elements: Vec<CommElement>,
    pub rest: Ident,
    pub nonlinear_var: Ident,
    pub scope_var: Ident,
    pub arg_var: Ident,
    /// (D10) The `m ≥ 1` reduct elements, in RHS order.
    pub reducts: Vec<CommReduct>,
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

/// (D10) A structured element for the COMM lane specifically: [`structured_element`], but the LAST
/// argument may ALSO be an EXPLICIT single binder abstraction `^x.body` whose body is a bare
/// variable — the omnibus π spelling `(PIn n ^x.p)` (`omnibus.tex:1988`) of the element the
/// Rholang/`CommDemo` rules write as a bare scope variable `(PFor N cont)`. The abstraction
/// contributes its BODY variable, so `args.last()` is the scope under either spelling and the
/// emitted [`comm_element_pattern`] (whose non-channel positions are wildcards) is IDENTICAL.
///
/// The second element of the pair is `true` when the abstraction spelling was used.
/// [`comm_rule_shape`] then requires that element's scope to be the RHS substitution's `scope_var`
/// — tying every abstraction to the ONE sound way to consume a scope, which is why this needs no
/// `LanguageDef` binder lookup. `structural_ac_rule_shape` deliberately keeps the strict
/// [`structured_element`]: a PURELY structural reduct has no substitution to consume a scope with,
/// so an abstraction there could only be spliced open (letting the bound variable escape).
fn comm_structured_element(pattern: &Pattern) -> Option<(CommElement, bool)> {
    if let Some(element) = structured_element(pattern) {
        return Some((element, false));
    }
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    let mut vars: Vec<Ident> = Vec::with_capacity(args.len());
    let mut explicit_lambda_scope = false;
    for (index, arg) in args.iter().enumerate() {
        match arg {
            Pattern::Term(PatternTerm::Var(name)) => vars.push(name.clone()),
            Pattern::Term(PatternTerm::Lambda { body, .. }) if index + 1 == args.len() => {
                let Pattern::Term(PatternTerm::Var(body_var)) = body.as_ref() else {
                    return None;
                };
                vars.push(body_var.clone());
                explicit_lambda_scope = true;
            },
            _ => return None,
        }
    }
    Some((
        CommElement {
            constructor: constructor.to_string(),
            args: vars,
            nonlinear_index: 0,
        },
        explicit_lambda_scope,
    ))
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
/// `op{ E0, E1, ...rest } ~> op{ r_0, …, r_{m-1}, ...rest }` — see [`CommShape`]. Fail-closed on
/// every other shape (a non-HashBag collection, an element that is not a constructor over bare
/// variables — modulo the [`comm_structured_element`] abstraction spelling — 0 or ≥2 shared
/// variables, an RHS that is not a with-rest bag over the SAME op and rest, an RHS with ≠1
/// substitution element, an RHS non-substitution element that is not a bare LHS variable or that is
/// the substitution's own scope, or an abstraction-spelled element whose scope the substitution does
/// not consume).
///
/// (D10) The reduct admits `m ≥ 1` fixed elements — exactly ONE substitution plus `m - 1` bare LHS
/// variables — so the omnibus's SYNCHRONOUS π `Comm` (`omnibus.tex:1988-1989`), whose output
/// `n!m.q` carries a continuation, is realized in Rho as a `CommRewrite` instead of failing closed
/// to `Unsupported`. This is the exact mirror of `dovetail_report::is_comm_rewrite`'s generalization,
/// so the host lane and the Rho lane cannot drift: a rule the host fires is a rule the backend
/// realizes, which is what the modality generator's realization fence reads.
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
    let mut abstraction_scopes: Vec<Ident> = Vec::new();
    for element in lhs_elements {
        let (info, explicit_lambda_scope) = comm_structured_element(element)?;
        if explicit_lambda_scope {
            abstraction_scopes.push(info.args.last()?.clone());
        }
        elements.push(info);
    }

    // The shared non-linear channel variable, and each element's occurrence index of it.
    let nonlinear_var = unique_shared_variable(&elements)?;
    for element in &mut elements {
        element.nonlinear_index = element.args.iter().position(|v| v == &nonlinear_var)?;
    }

    // RHS: op{ r_0, …, r_{m-1}, ...rest } — the SAME op + rest, `m ≥ 1` fixed elements of which
    // EXACTLY ONE is a substitution and the rest are bare variables.
    let (rhs_op, rhs_elements, rhs_rest) = collection_apply(right, resolved_kind)?;
    if rhs_op != op || rhs_elements.is_empty() || rhs_rest.as_ref() != Some(&rest) {
        return None;
    }
    let mut subst_slot: Option<(Ident, Ident)> = None;
    let mut reducts: Vec<CommReduct> = Vec::with_capacity(rhs_elements.len());
    for element in rhs_elements {
        match subst_element(element) {
            Some(pair) => {
                if subst_slot.replace(pair).is_some() {
                    return None; // ≥2 substitutions — an ambiguous host-computed reduct slot.
                }
                reducts.push(CommReduct::Substitution);
            },
            None => match element {
                Pattern::Term(PatternTerm::Var(name)) => {
                    reducts.push(CommReduct::Var(name.clone()))
                },
                _ => return None,
            },
        }
    }
    // No substitution at all ⇒ a PURELY structural AC rewrite, not a Comm (mutual exclusion).
    let (scope_var, arg_var) = subst_slot?;

    // Every abstraction-spelled element's scope must be the substitution's scope: the substitution
    // is the ONLY sound consumer of a binder scope (see `comm_structured_element`).
    if abstraction_scopes.iter().any(|scope| scope != &scope_var) {
        return None;
    }

    // The substitution's scope + arg, and every σ-delivered reduct element, must be LHS variables
    // (supplied by the AC match's σ).
    let lhs_vars: HashSet<String> = elements
        .iter()
        .flat_map(|element| element.args.iter())
        .map(|var| var.to_string())
        .collect();
    if !lhs_vars.contains(&scope_var.to_string()) || !lhs_vars.contains(&arg_var.to_string()) {
        return None;
    }
    // A σ-delivered reduct element may never be the substitution's SCOPE — splicing the raw binder
    // body beside the substitution would let its bound variable escape.
    for reduct in &reducts {
        let CommReduct::Var(var) = reduct else {
            continue;
        };
        if !lhs_vars.contains(&var.to_string()) || var == &scope_var {
            return None;
        }
    }

    Some(CommShape {
        op,
        elements,
        rest,
        nonlinear_var,
        scope_var,
        arg_var,
        reducts,
    })
}

/// The Comm receiver's σ-slot frame for the ASYNCHRONOUS `m = 1` reduct (a single polyadic
/// `ReceiveBind`, free-var levels): the two structured elements' non-linear channel slots come first
/// (`0` = first element = `N_recv`, `1` = second = `N_send`), then the bag remainder `rest` (`2`),
/// the host-delivered reduct (`3`), and the dynamic out channel (`4`). `free_count = 5`.
/// Body/condition read these back as `BoundVar(free_count - 1 - level)`.
///
/// (D10) [`comm_receiver_par`] computes the frame as `k + 1 + m + 1` for `k` structured elements and
/// `m` reduct slots, which is exactly this constant at `k = 2, m = 1` (asserted there), so the
/// asynchronous receiver stays BYTE-IDENTICAL while a synchronous `m = 2` rule gets its extra slot.
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
    let mut items = Vec::with_capacity(element.args.len() + 2);
    items.push(tag);
    // E-2-D: the reflected element carries the marker at index 1 — absorb it with a wildcard
    // (this channel/consistency match is over head + args, not the marker); the arg σ levels
    // are unchanged (a wildcard binds nothing).
    if is_marked_object_label(&element.constructor) {
        items.push(new_wildcard_par(Vec::new(), true));
    }
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

// DISABLED (never called; superseded by D10) — and it is not merely dead, it is a TRAP.
//
//     /// The non-linear consistency `Receive.condition` for a Comm receiver: the conjunction
//     /// (`EAnd`) of `EEq(BoundVar, BoundVar)` over each repeated variable's occurrence slot
//     /// pairs — for the canonical single shared channel with two occurrences, exactly one
//     /// conjunct `EEq(BoundVar(N_recv), BoundVar(N_send))`. Child `i`'s slot at free level
//     /// `l` is `BoundVar(COMM_FREE_COUNT - 1 - l)` (the receive binds flattened, so body +
//     /// condition share the reverse De Bruijn frame). Mirrors
//     /// `rho_net_automaton::consistency_guard`, kept self-contained.
//     fn comm_consistency_condition(occurrence_levels: &[usize]) -> Par {
//         nonlinear_consistency_condition(occurrence_levels, COMM_FREE_COUNT)
//     }
//
// It hardcodes `COMM_FREE_COUNT`, which is the ASYNCHRONOUS (`m = 1`) frame width. The D10
// generalization made the Comm receiver's width depend on the reduct count:
// [`comm_receiver_par`] computes `free_count = k + 1 + m + 1` and calls
// [`nonlinear_consistency_condition`] with it directly, so `COMM_FREE_COUNT` now survives only
// as the `m = 1` invariant its `debug_assert!` pins. A future caller reaching for the obvious
// name would silently build a synchronous (`m ≥ 2`) receiver's guard against the `m = 1` frame
// — every `BoundVar(free_count - 1 - l)` off by `m - 1`. Kept commented rather than deleted so
// the reason survives; restore it ONLY with `free_count` as a parameter, at which point it is
// `nonlinear_consistency_condition` itself.

/// The non-linear consistency `Receive.condition` for a receiver whose flattened receive binds
/// `free_count` slots: the conjunction (`EAnd`) of `EEq(BoundVar, BoundVar)` over each repeated
/// variable's occurrence slot pairs. Child slot at free level `l` is `BoundVar(free_count - 1 - l)`
/// (the receive binds flattened, so body + condition share the reverse De Bruijn frame). Shared by
/// the Comm receiver ([`comm_receiver_par`], `free_count = k + 1 + m + 1` — `COMM_FREE_COUNT` only
/// at `m = 1`) and the structural-AC receiver ([`structural_ac_receiver_par`]).
///
/// `pub(crate)`: the A-S5.5 driver AC arms (`crate::rho_net_drive`) ride the SAME
/// conjunction as a `MatchCase.guard` (evaluated in the case env, which shares the
/// reverse-De-Bruijn frame convention with a receive of the same `free_count` — F12), so
/// the driver's non-linear checks can never drift from the installed receivers'.
pub(crate) fn nonlinear_consistency_condition(
    occurrence_levels: &[usize],
    free_count: usize,
) -> Par {
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
    // ★ COMPILE-TIME GUARD DISCHARGE — ASSERT ONLY, NEVER BRANCH. The conjunction is
    // `EEq(BoundVar_i, BoundVar_j)` over the receive's (or match case's) OWN formals:
    // payload-dependent by construction, 0% dischargeable, so this guard always stays wired to
    // the machine's own evaluator. See `crate::guard_closure` and
    // `mettail_rholang_runtime::guard_discharge`.
    debug_assert!(
        !crate::guard_closure::is_binder_closed(&guard),
        "a non-linear consistency guard is EEq over the frame's own formals and can never be \
         binder-closed"
    );
    guard
}

/// A ground `Par` carrying the single expression `instance`, locally-free in `free`. Mirrors
/// `rho_net_automaton::expr_par`.
fn expr_par_with(instance: Expr, free: &[usize]) -> Par {
    let mut par = Par::default();
    par.exprs = vec![instance];
    par.locally_free = create_bit_vector(free);
    par.connective_used = false;
    par
}

/// Build the Comm σ-receiver for `op{ E0, E1, ...rest } ~> op{ r_0, …, r_{m-1}, ...rest }`
/// ([`CommShape`]): a persistent
///
/// ```text
/// for( < rest_rem | @"ac:op"!(⟦E0⟧) | @"ac:op"!(⟦E1⟧) >, r_0, …, r_{m-1}, out <- source )
///   where ( N_recv == N_send )
///   { out!( @"ac:op"!(r_0) | … | @"ac:op"!(r_{m-1}) | rest_rem ) }
/// ```
///
/// The connective process-soup pattern (element 0) matches the reflected operand bag carrier
/// ORDER-INDEPENDENTLY (native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders),
/// binding the two elements' channel
/// σ slots (`FreeVar(0)`/`FreeVar(1)`) — via the structured [`comm_element_pattern`]s, whose tags
/// route each pattern to its like-tagged send — and the residual soup to the remainder `rest`
/// (`FreeVar(2)`). The `m` reduct slots (`FreeVar(3 .. 3+m)`) carry the RHS elements in order; `out`
/// (`FreeVar(3+m)`) is the dynamic out channel. The `condition` fires the COMM only when the two
/// channel slots are name-equal ([`nonlinear_consistency_condition`]); the body emits the bag RHS
/// `@"ac:op"!(r_0) | … | rest` on `out`.
///
/// (D10) The receiver does not distinguish a HOST-COMPUTED reduct slot from a σ-DELIVERED one — it
/// FORWARDS whatever the injection sends at each slot — so the arity generalization is entirely in
/// the slot COUNT. At `m = 1` (`free_count = 2 + 1 + 1 + 1 = COMM_FREE_COUNT`) every emitted byte is
/// unchanged, which is the asynchronous receiver `CommDemo`/Rholang install. This is the same frame
/// [`structural_ac_receiver_par`] uses for its `m` σ-delivered reducts; the two receivers now differ
/// only in WHERE the injection sources each slot's value.
fn comm_receiver_par(shape: &CommShape, source: Par, language_fingerprint: &str) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, &shape.op);
    let k = shape.elements.len(); // 2
    let m = shape.reducts.len(); // 1 (asynchronous) or ≥2 (synchronous)
    let rest_level = k;
    let first_reduct_level = k + 1;
    let out_level = k + 1 + m;
    let free_count = out_level + 1;
    debug_assert!(m >= 1, "a Comm reduct has at least the substitution element");
    debug_assert!(m > 1 || free_count == COMM_FREE_COUNT, "m = 1 keeps the async frame");

    // Element 0 of the receive bind: the structured with-rest process-soup pattern.
    let mut bag_pattern = new_freevar_par(rest_level as i32, Vec::new()); // the `rest` remainder
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

    // The non-linear consistency guard `EEq(N_recv, N_send)`.
    let condition = nonlinear_consistency_condition(&occurrence_levels, free_count);

    // Body: `out!( @"ac:op"!(r_0) | … | @"ac:op"!(r_{m-1}) | rest )`.
    let rest_bv_index = free_count - 1 - rest_level;
    let out_bv_index = free_count - 1 - out_level; // 0
    let mut body_soup: Option<Par> = None;
    for j in 0..m {
        let reduct_bv_index = free_count - 1 - (first_reduct_level + j);
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
    // `m ≥ 1` (a Comm reduct always carries the substitution), so `body_soup` is always `Some`.
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

    // Receive-bind patterns: [bag_pattern, FreeVar(r_0), …, FreeVar(r_{m-1}), FreeVar(out)].
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

/// The Comm injection `call` for an un-skipped Comm rewrite:
/// `channel!(⟦whole_bag⟧, ⟦r_0⟧, …, ⟦r_{m-1}⟧, @out)`, where `⟦whole_bag⟧` is the operand bag's
/// process-soup carrier ([`reflect_ground_term_par`] routes a HashBag to the soup) and each `⟦r_j⟧`
/// is one reduct element in RHS order — the host-computed contractum `cont[Q/y]` at the substitution
/// slot, a σ-recovered LHS-element argument at every other. This is the exact `(m + 2)`-value message
/// the Comm receiver ([`comm_receiver_par`]) consumes: the connective bag pattern matches the soup
/// (binding the two channel slots + the remainder and enforcing the non-linear guard), the `m`
/// reduct values fill the dedicated slots, and the out formal binds `@out`. `channel` MUST be the
/// Comm receiver's SOURCE (the rule's trace channel), so the accept triad (receiver source ≡
/// injection channel) holds by symmetric derivation, exactly as [`ac_contract_call`].
///
/// (D10) `reducts.len()` is `1` for the ASYNCHRONOUS communication — byte-identical to the
/// pre-generalization 3-value call — and `≥2` for the SYNCHRONOUS one.
pub fn comm_contract_call(
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
    /// (D10) The `m ≥ 1` reduct slots, in RHS order: `None` marks the ONE host-computed substitution
    /// slot (`cont[Q/y]`, recovered from the firing's contractum), `Some(var)` a σ-delivered
    /// LHS-element argument the injection reads straight out of σ. `[None]` is the ASYNCHRONOUS
    /// communication; `[None, Some("q")]` is the omnibus's SYNCHRONOUS π `Comm`, whose output
    /// continuation runs in parallel with the substituted receive continuation.
    pub reduct_slots: Vec<Option<String>>,
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
            reduct_slots: shape
                .reducts
                .iter()
                .map(|reduct| match reduct {
                    CommReduct::Substitution => None,
                    CommReduct::Var(var) => Some(var.to_string()),
                })
                .collect(),
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
/// ORDER-INDEPENDENTLY (native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders),
/// binding each structured element's
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
    let element_channel = ac_soup_channel(language_fingerprint, &shape.op);
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

// ─── Stage 4 S-binder SLICE 3b: the STRUCTURAL-AC SPREAD MATCH (Ambient `OpenRule` in-Rho) ────────

/// One in-Rho MATCHING entry for a STRUCTURAL non-linear AC family rewrite
/// (`RhoNetLoweredRule::StructuralAcRewrite`, Stage 3d — the Ambient `OpenRule`
/// `op{ E0, E1, ...rest } ~> op{ r0, …, ...rest }`): the data the in-Rho matcher needs to ADMIT the
/// structural-AC redex and co-install a per-site MATCH receiver that re-sources BOTH the operand bag
/// AND the structural reducts from the SPREAD of the reflected subject (never the host-σ report).
///
/// The STRUCTURAL twin of [`RhoNetAcMatchEntry`]: where a LINEAR AC element is a bare variable (its
/// value IS the reduct), a structural AC element is a constructor `C(N, …, r_j, …)` whose reduct args
/// `r_j` are INNER arguments. The report-path [`structural_ac_receiver_par`] wildcards those args and
/// takes them as separately DELIVERED σ slots; the MATCH receiver ([`structural_ac_match_receiver_par`])
/// instead BINDS them from the bag's connective pattern — so, exactly like the linear
/// [`ac_match_call_par`], its message is the 2-value `carrier!(⟦bag⟧, @out)` the spread delivers, with
/// NO host σ. Like a linear AC redex, a structural-AC redex is NOT an automaton entry (its `AcApp`
/// bag has no positional image), so it carries no `accept_channels` entry and no `PatternId`; the
/// match driver LOCATES it by a separate structural walk ([`structural_ac_match_install_at`]) that
/// rides the SAME `^lambda`/nested descent — so a bag under a `new(x, ·)` binder is reached for free.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetStructuralAcMatchEntry {
    /// The Dovetail firing label the structural-AC firing carries (the bare rewrite label, e.g.
    /// `OpenRule`) — what the report keys the firing on and the in-Rho gate admits.
    pub fired_rule_label: String,
    /// The recognized structural-AC shape (`op`, the `k` structured elements, the shared non-linear
    /// channel var, `rest`, and the `m` structural reduct vars) — the per-site MATCH receiver is
    /// materialized from it (byte-identical guard + body to the installed receiver, only re-sourced
    /// from the bag). Crate-private: only [`structural_ac_match_call_par`] (same crate) reads it.
    pub(crate) shape: StructuralAcShape,
}

impl RhoNetStructuralAcMatchEntry {
    /// The HashBag operand constructor `op` (`PPar` for `OpenRule`) — the located bag's constructor,
    /// which the match driver keys the co-install on.
    pub fn op(&self) -> &str {
        &self.shape.op
    }
}

/// Whether a structural-AC `shape` is faithfully representable as an in-Rho MATCH receiver
/// ([`structural_ac_match_receiver_par`]): every STRUCTURAL reduct var that is NOT the non-linear
/// channel var must occur EXACTLY ONCE across all element arguments, so the connective pattern binds
/// it at a single unambiguous position (a Rholang pattern free variable may occur at most once). A
/// reduct that is itself the non-linear var rides the guard's first occurrence slot and needs no bag
/// binding, so it is exempt. Fail-closed (returns `false`) for a within-element repeated argument
/// (e.g. `C(P, P)`) — a degenerate shape that would need an intra-element non-linear guard — which
/// then routes that firing to the host-σ replay path rather than a wrong in-Rho pattern.
pub(crate) fn structural_ac_shape_is_match_representable(shape: &StructuralAcShape) -> bool {
    let nonlinear = shape.nonlinear_var.to_string();
    shape
        .reduct_vars
        .iter()
        .map(|var| var.to_string())
        .filter(|name| *name != nonlinear)
        .all(|name| {
            let occurrences: usize = shape
                .elements
                .iter()
                .flat_map(|element| element.args.iter())
                .filter(|arg| arg.to_string() == name)
                .count();
            occurrences == 1
        })
}

/// Derive every in-Rho MATCHING entry for a language's STRUCTURAL non-linear AC family rewrites
/// (Stage 3d Ambient `OpenRule`) — the structural-AC analogue of [`rho_net_ac_match_entries`],
/// routed for the automaton MATCH path (bag + reducts re-sourced from the subject spread) rather than
/// the host-σ [`structural_ac_contract_call`] replay path.
///
/// Correlates each installed structural-AC firing site ([`rho_net_structural_ac_injection_sites`] —
/// the rewrites that actually un-skipped to a [`RhoNetLoweredRule::StructuralAcRewrite`] receiver)
/// back to its source `RewriteRule`, re-extracts its shape through the SAME [`structural_ac_rule_shape`]
/// the receiver materialized from (so the op / elements / non-linear var / reducts agree
/// byte-for-byte), and keeps only those a MATCH receiver can faithfully bind
/// ([`structural_ac_shape_is_match_representable`]). A non-representable shape is DROPPED here (not
/// surfaced), so it stays deferred and the gate routes its firing to the host-σ replay path — never
/// a wrong in-Rho match.
pub fn rho_net_structural_ac_match_entries(def: &LanguageDef) -> Vec<RhoNetStructuralAcMatchEntry> {
    let sites = rho_net_structural_ac_injection_sites(def);
    let mut entries = Vec::with_capacity(sites.len());
    for site in sites {
        // The source rewrite a structural-AC injection site surfaced is always present; a defensive
        // skip keeps the derivation total.
        let Some(rewrite) = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == site.rule_label)
        else {
            continue;
        };
        let resolved_kind = resolve_ac_collection_type(def, &rewrite.left);
        // A `StructuralAcRewrite` lowered iff `structural_ac_rule_shape` succeeded under the resolved
        // kind, so this cannot fail; a defensive skip keeps the derivation total.
        let Some(shape) =
            structural_ac_rule_shape(&rewrite.left, &rewrite.right, resolved_kind.as_ref())
        else {
            continue;
        };
        // Fail-closed: a shape the MATCH receiver cannot faithfully bind stays on the host-σ path.
        if !structural_ac_shape_is_match_representable(&shape) {
            continue;
        }
        entries.push(RhoNetStructuralAcMatchEntry { fired_rule_label: site.rule_label, shape });
    }
    entries
}

/// Stage 4 (S-binder SLICE 3b) — walk `subject`, LOCATE every STRUCTURAL non-linear AC redex (an
/// admitted operand bag), and co-install a per-site MATCH receiver over the SPREAD, re-sourcing the
/// operand bag + reducts from the subject (NOT the host-σ report). The structural-AC analogue of the
/// linear [`ac_match_call_par`]: it reuses the SAME structural descent ([`structural_ac_match_install_at`],
/// mirroring [`ac_match_install_at`]) from root nonce `root_site` — so it rides the `^lambda`/nested
/// descent through a `new(x, ·)` binder for FREE, locating a bag ARBITRARILY deep. At every bag node
/// whose constructor is one of the admitted `entries`' ops it derives the site-keyed carrier `ac:⌜ℓ⌝/op`
/// ([`ac_carrier_channel`], disjoint per position — SAME channel family the linear AC walk uses),
/// co-installs a [`structural_ac_match_receiver_par`] over it, and publishes `carrier!(⟦bag⟧, @out)`
/// where `⟦bag⟧` is [`reflect_ac_bag_par`] over THIS node's ground elements. Returns the parallel
/// composition of every located bag's `(receiver ‖ delivery)` (empty when `subject` has no structural
/// AC redex). `language_fingerprint` MUST be the ruleset's (the spread's) fingerprint, so the soup's
/// element tags and the receiver's element patterns agree.
pub fn structural_ac_match_call_par(
    subject: &GroundTerm,
    entries: &[RhoNetStructuralAcMatchEntry],
    root_site: &str,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    if entries.is_empty() {
        return Par::default();
    }
    let by_op: HashMap<&str, &RhoNetStructuralAcMatchEntry> = entries
        .iter()
        .map(|entry| (entry.shape.op.as_str(), entry))
        .collect();
    let locations = SubjectLocationIndex::new(subject);
    structural_ac_match_install_at(
        &locations,
        SubjectPosition::ROOT,
        root_site,
        &by_op,
        out_channel,
        language_fingerprint,
    )
}

/// Recursively LOCATE + co-install the structural-AC MATCH receivers for `node` at the position whose
/// `loc:` head-tag channel is `loc_channel` (the SAME location derivation the spread uses). The
/// structural-AC twin of [`ac_match_install_at`]: identical descent (a HashBag whose op is admitted
/// fires in Rho over the site-keyed carrier; a non-bag node descends its structural children — so a
/// bag under a `^lambda` binder image is located), only the co-installed receiver differs
/// ([`structural_ac_match_receiver_par`] instead of the linear [`ac_sigma_receiver_par_with_condition`]).
fn structural_ac_match_install_at(
    locations: &SubjectLocationIndex<'_>,
    start: SubjectPosition,
    root_site: &str,
    by_op: &HashMap<&str, &RhoNetStructuralAcMatchEntry>,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    let mut par = Par::default();
    locations.walk(start, |position, node| {
        if !matches!(node.coll_type, Some(CollectionType::HashBag)) {
            return true;
        }
        if let Some(entry) = by_op.get(node.constructor.as_str()) {
            let loc_channel = locations.channel("loc", language_fingerprint, root_site, position);
            let carrier = ac_carrier_channel(&loc_channel, &node.constructor);
            let receiver = structural_ac_match_receiver_par(
                &entry.shape,
                new_gstring_par(carrier.clone(), Vec::new(), false),
                language_fingerprint,
            );
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
            let preceding = std::mem::take(&mut par);
            par = preceding.append(receiver).append(delivery);
        }
        false
    });
    par
}

/// The reflected element PATTERN for one structured element `C(a_0, …)` in a structural-AC MATCH
/// receiver: a tagged `EList` `[ GPrivate(reflect_tag(C)), … ]` (byte-identical in tag + shape to
/// [`reflect_ground_term_par`]'s constructor image, so the reflected element in the soup matches)
/// whose NON-LINEAR channel position binds `FreeVar(nl_level)` (the guard slot), whose STRUCTURAL
/// reduct positions bind `FreeVar(reduct_slots[name])` (the RHS elements, sourced FROM the bag —
/// unlike the report-path [`comm_element_pattern`], which wildcards them and takes them as delivered
/// slots), and whose every OTHER position is a wildcard `_` (a dropped argument).
fn structural_ac_match_element_pattern(
    element: &CommElement,
    nl_level: usize,
    reduct_slots: &HashMap<String, usize>,
    language_fingerprint: &str,
) -> Par {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
        language_fingerprint,
        &element.constructor,
    ));
    let mut items = Vec::with_capacity(element.args.len() + 2);
    items.push(tag);
    // E-2-D: the reflected element carries the marker at index 1 — absorb it with a wildcard
    // (the match is over head + args; the arg σ levels are unchanged, a wildcard binds nothing).
    if is_marked_object_label(&element.constructor) {
        items.push(new_wildcard_par(Vec::new(), true));
    }
    for (index, arg) in element.args.iter().enumerate() {
        if index == element.nonlinear_index {
            // The non-linear channel occurrence — the guard slot (`FreeVar(nl_level)`).
            items.push(new_freevar_par(nl_level as i32, Vec::new()));
        } else if let Some(level) = reduct_slots.get(&arg.to_string()) {
            // A structural reduct argument — bound FROM the bag at its dedicated slot.
            items.push(new_freevar_par(*level as i32, Vec::new()));
        } else {
            // A dropped argument (not the channel, not an RHS reduct) — a wildcard.
            items.push(new_wildcard_par(Vec::new(), true));
        }
    }
    // A pattern EList carrying free vars / wildcards is connective; its `locally_free` is empty (free
    // vars are pattern binders, not locally-free bound vars).
    new_elist_par(items, Vec::new(), true, None, Vec::new(), true)
}

/// Build the STRUCTURAL-AC MATCH receiver for a per-site co-install (Stage 4 S-binder SLICE 3b): the
/// SPREAD analogue of [`structural_ac_receiver_par`]. A persistent
///
/// ```text
/// for( < rest_rem | @"ac:op"!(⟦E0⟧) | … | @"ac:op"!(⟦E_{k-1}⟧) >, out <- source )
///   where ( N_0 == N_1 == … )
///   { out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | rest_rem ) }
/// ```
///
/// Where the installed (report-path) receiver takes the `m` reduct elements as SEPARATELY DELIVERED
/// message slots (host-σ sourced) and WILDCARDS the reduct arguments in its element patterns, the
/// MATCH receiver binds EVERYTHING from the operand bag — exactly like the linear
/// [`ac_sigma_receiver_par_with_condition`] — so its message is the 2-value `carrier!(⟦bag⟧, @out)`
/// the spread delivers (NO host σ). The connective process-soup pattern (element 0) binds, ORDER-
/// INDEPENDENTLY (native `spatial_matcher_pda::ListMachine`, with `sub_pars` for remainders), from the bag:
///   * each element's non-linear channel occurrence `FreeVar(i)` (element `i`, for the `N ≡ N` guard);
///   * each DISTINCT structural reduct var's argument `FreeVar(k+1+j)` (bound WHERE it occurs as an
///     element argument — the RHS element `r_j`), a reduct that IS the channel var riding slot `0`;
///   * the residual soup to `rest` (`FreeVar(k)`).
///
/// The `condition` fires the COMM only when all channel slots are name-equal
/// ([`nonlinear_consistency_condition`]); the body splices `out!( @"ac:op"!(r0) | … | rest )` — one
/// send per RHS reduct occurrence (multiplicity-preserving) — from the bag-bound slots. Guard + body
/// share the installed receiver's reverse-De-Bruijn frame; only the element patterns bind (not
/// wildcard) the reduct args and the message drops the reduct formals. The caller
/// ([`structural_ac_match_install_at`]) has already checked (via
/// [`structural_ac_shape_is_match_representable`]) that each distinct non-channel reduct occurs once,
/// so no bag position is double-bound.
fn structural_ac_match_receiver_par(
    shape: &StructuralAcShape,
    source: Par,
    language_fingerprint: &str,
) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, &shape.op);
    let k = shape.elements.len();
    let rest_level = k;

    // The DISTINCT structural reduct vars that need a fresh bag-bound slot — those NOT the non-linear
    // channel var (a reduct that IS the channel var rides the guard's first occurrence slot `0`), in
    // first-appearance order over the RHS reduct vars.
    let nonlinear = shape.nonlinear_var.to_string();
    let mut distinct_reducts: Vec<String> = Vec::with_capacity(shape.reduct_vars.len());
    for var in &shape.reduct_vars {
        let name = var.to_string();
        if name != nonlinear && !distinct_reducts.contains(&name) {
            distinct_reducts.push(name);
        }
    }
    let first_reduct_level = k + 1;
    let out_level = first_reduct_level + distinct_reducts.len();
    let free_count = out_level + 1;

    // reduct var name → its bound slot LEVEL (`0` = the non-linear var's first occurrence).
    let reduct_slots: HashMap<String, usize> = distinct_reducts
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), first_reduct_level + index))
        .collect();
    let reduct_level = |name: &str| -> usize {
        if name == nonlinear {
            0
        } else {
            *reduct_slots
                .get(name)
                .expect("a distinct structural reduct var is indexed")
        }
    };

    // Element 0 of the receive bind: the structured with-rest process-soup pattern (each element
    // binds its channel occurrence + any structural reduct arg; the `rest` remainder is `FreeVar(k)`).
    let mut bag_pattern = new_freevar_par(rest_level as i32, Vec::new());
    let mut occurrence_levels = Vec::with_capacity(k);
    for (nl_level, element) in shape.elements.iter().enumerate() {
        occurrence_levels.push(nl_level);
        let element_pattern = structural_ac_match_element_pattern(
            element,
            nl_level,
            &reduct_slots,
            language_fingerprint,
        );
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

    // Body: `out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | rest )` — one send per RHS reduct
    // occurrence (multiplicity-preserving), each referencing its bag-bound slot.
    let rest_bv_index = free_count - 1 - rest_level;
    let out_bv_index = free_count - 1 - out_level; // 0
    let mut body_soup: Option<Par> = None;
    for var in &shape.reduct_vars {
        let level = reduct_level(&var.to_string());
        let reduct_bv_index = free_count - 1 - level;
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

    // Receive-bind patterns: [bag_pattern, FreeVar(out)] — the 2-value spread message
    // `carrier!(⟦bag⟧, @out)`, exactly as the linear AC match receiver.
    let patterns = vec![bag_pattern, new_freevar_par(out_level as i32, Vec::new())];

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

// ─── Stage 4 (Ambient In/Out): the DEPTH-2 NESTED structural non-linear AC rewrite ────────────────
//
// The Ambient-calculus `InRule`/`OutRule` GENERALIZE the flat [`structural_ac_rule_shape`]
// (`OpenRule`) to an element whose ARGUMENT is itself a HashBag, with a CROSS-LEVEL non-linear
// equality:
//
//   InRule  . { n[{ in(m,P), ...q }], m[R], ...s } ~> { m[{ n[{ P, ...q }], R }], ...s }
//   OutRule . m[{ n[{ out(m,P), ...q }], R, ...s }] ~> { n[{ P, ...q }], m[R], ...s }
//
// The reducer's `SpatialMatcher<Par,Par>` matches a DEPTH-2 nested bag PATTERN + the cross-level
// `Receive.condition` `EEq(M_outer, M_inner)` in ONE atomic `consume` (no depth cap; a HashBag
// ARGUMENT reflects to the SAME order-independent process-soup carrier as the top bag, so the inner
// capability binds one level down in the SAME match). The receiver VERIFIES the depth-2 shape + the
// cross-level guard + binds the SPLICED outer remainder; the NESTED reduct (a re-assembled
// restructuring, never a bare LHS var) is the host-computed contractum `RHS[σ]`, reflected from σ and
// delivered as the host-σ-sourced reduct value(s) — the firing seam
// ([`structural_ac_contract_call`], `channel!(⟦operand⟧, ⟦r0⟧, …, @out)`) is REUSED unchanged.

/// A σ-reconstruction template for a nested structural-AC operand or reduct: walk it with a firing's
/// resolved σ ([`instantiate_ac_reconstruct_template`]) to rebuild the ground term the structural-AC
/// σ-injection reflects. Depth-agnostic — an element's argument may itself be a [`Self::Bag`] — so it
/// captures the DEPTH-2 nesting of the Ambient `InRule`/`OutRule` (and any deeper future shape)
/// uniformly. Built from the rewrite's AST [`Pattern`] via [`Self::from_pattern`].
pub enum AcReconstructTemplate {
    /// A bare LHS variable — reconstructs to `σ[name]`.
    Var(String),
    /// A plain constructor node `ctor(children…)` — `GroundTerm::new(ctor, [walk children])`.
    Node {
        /// The constructor label.
        constructor: String,
        /// The argument templates, in constructor-argument order.
        children: Vec<AcReconstructTemplate>,
    },
    /// A HashBag `op{ elements…, ...rest }` — `GroundTerm::collection(HashBag, op, [walk elements] ⊎
    /// σ[rest].children)`. `rest` is `None` for a rest-less bag (e.g. the `InRule` reduct's inner bag
    /// `{ n[{P,...q}], R }`).
    Bag {
        /// The AC bag operator constructor (e.g. `PPar`).
        op: String,
        /// The fixed element templates.
        elements: Vec<AcReconstructTemplate>,
        /// The `...rest` remainder variable, if any — its σ children are spliced in.
        rest: Option<String>,
    },
    /// A-S5.8 (F8-AM-1): a RHS-introduced SINGLE-binder scope `B(^x. body)` — the reflected
    /// image is the ctor-tag-ERASED `^lambda([⟦body⟧])` node (exactly the M-reflect image of a
    /// runtime binder, `rho_invocation.rs`), so the template erases the surface constructor too
    /// and carries only the body. σ-SLOT SHIFT RULE (F8-AM-1c): every σ slot referenced UNDER
    /// `k` template binders is instantiated as `k` composed applications of the de Bruijn shift
    /// `^shift(Z, ·)` to its matched value, PRE-SPLICE — never by shifting a composed body
    /// (which would corrupt template-introduced `^bound(0)` coordinates) and never
    /// depth-plus-per-level (a double shift). A template binder's own bound occurrences CANNOT
    /// appear in the body (the AST has no bound-var pattern leaf, and a `Var` naming the binder
    /// would fail the σ-closure check), so the body's `Var` leaves are exactly the shifted σ
    /// slots. Constructed only by [`Self::from_pattern`]'s binder-constructor arm — a binder at
    /// the RHS ROOT is rejected upstream (`resolve_bag_apply` demands a bag root), so a
    /// `Binder` sits only at ELEMENT/child template positions (the F8-AM-1a witness shape).
    Binder {
        /// The scope-body template (under ONE more binder than this node's position).
        body: Box<AcReconstructTemplate>,
    },
}

impl Clone for AcReconstructTemplate {
    fn clone(&self) -> Self {
        enum Task<'template> {
            Visit(&'template AcReconstructTemplate),
            Node {
                constructor: String,
                child_count: usize,
            },
            Bag {
                op: String,
                rest: Option<String>,
                element_count: usize,
            },
            Binder,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(AcReconstructTemplate::Var(name)) => {
                    values.push(Self::Var(name.clone()));
                },
                Task::Visit(AcReconstructTemplate::Node { constructor, children }) => {
                    tasks.push(Task::Node {
                        constructor: constructor.clone(),
                        child_count: children.len(),
                    });
                    tasks.extend(children.iter().rev().map(Task::Visit));
                },
                Task::Visit(AcReconstructTemplate::Bag { op, elements, rest }) => {
                    tasks.push(Task::Bag {
                        op: op.clone(),
                        rest: rest.clone(),
                        element_count: elements.len(),
                    });
                    tasks.extend(elements.iter().rev().map(Task::Visit));
                },
                Task::Visit(AcReconstructTemplate::Binder { body }) => {
                    tasks.push(Task::Binder);
                    tasks.push(Task::Visit(body));
                },
                Task::Node { constructor, child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("template clone PDA lost a child result");
                    let children = values.split_off(first);
                    values.push(Self::Node { constructor, children });
                },
                Task::Bag { op, rest, element_count } => {
                    let first = values
                        .len()
                        .checked_sub(element_count)
                        .expect("template clone PDA lost a bag element result");
                    let elements = values.split_off(first);
                    values.push(Self::Bag { op, elements, rest });
                },
                Task::Binder => {
                    let body = values.pop().expect("template clone PDA lost a binder body");
                    values.push(Self::Binder { body: Box::new(body) });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("template clone PDA produced no result")
    }
}

impl std::fmt::Debug for AcReconstructTemplate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'template> {
            Text(&'static str),
            String(&'template str),
            OptionalString(&'template Option<String>),
            Visit(&'template AcReconstructTemplate),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => formatter.write_str(text)?,
                Task::String(value) => write!(formatter, "{value:?}")?,
                Task::OptionalString(value) => write!(formatter, "{value:?}")?,
                Task::Visit(Self::Var(name)) => {
                    formatter.write_str("Var(")?;
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::String(name));
                },
                Task::Visit(Self::Node { constructor, children }) => {
                    formatter.write_str("Node { constructor: ")?;
                    tasks.push(Task::Text("] }"));
                    for (index, child) in children.iter().enumerate().rev() {
                        tasks.push(Task::Visit(child));
                        if index != 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text(", children: ["));
                    tasks.push(Task::String(constructor));
                },
                Task::Visit(Self::Bag { op, elements, rest }) => {
                    formatter.write_str("Bag { op: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::OptionalString(rest));
                    tasks.push(Task::Text(", rest: "));
                    tasks.push(Task::Text("]"));
                    for (index, element) in elements.iter().enumerate().rev() {
                        tasks.push(Task::Visit(element));
                        if index != 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text(", elements: ["));
                    tasks.push(Task::String(op));
                },
                Task::Visit(Self::Binder { body }) => {
                    formatter.write_str("Binder { body: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Visit(body));
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for AcReconstructTemplate {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (Self::Var(left), Self::Var(right)) if left == right => {},
                (
                    Self::Node {
                        constructor: left_constructor,
                        children: left_children,
                    },
                    Self::Node {
                        constructor: right_constructor,
                        children: right_children,
                    },
                ) if left_constructor == right_constructor
                    && left_children.len() == right_children.len() =>
                {
                    work.extend(left_children.iter().zip(right_children).rev());
                },
                (
                    Self::Bag {
                        op: left_op,
                        elements: left_elements,
                        rest: left_rest,
                    },
                    Self::Bag {
                        op: right_op,
                        elements: right_elements,
                        rest: right_rest,
                    },
                ) if left_op == right_op
                    && left_rest == right_rest
                    && left_elements.len() == right_elements.len() =>
                {
                    work.extend(left_elements.iter().zip(right_elements).rev());
                },
                (Self::Binder { body: left }, Self::Binder { body: right }) => {
                    work.push((left, right));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for AcReconstructTemplate {}

fn drain_owned_ac_template(
    mut template: AcReconstructTemplate,
    work: &mut Vec<AcReconstructTemplate>,
) {
    match &mut template {
        AcReconstructTemplate::Node { children, .. } => work.append(children),
        AcReconstructTemplate::Bag { elements, .. } => work.append(elements),
        AcReconstructTemplate::Binder { body } => {
            let child =
                std::mem::replace(body, Box::new(AcReconstructTemplate::Var(String::new())));
            work.push(*child);
        },
        AcReconstructTemplate::Var(_) => {},
    }
}

impl Drop for AcReconstructTemplate {
    fn drop(&mut self) {
        let mut work = Vec::new();
        match self {
            Self::Node { children, .. } => work.append(children),
            Self::Bag { elements, .. } => work.append(elements),
            Self::Binder { body } => {
                let child = std::mem::replace(body, Box::new(Self::Var(String::new())));
                work.push(*child);
            },
            Self::Var(_) => {},
        }
        while let Some(template) = work.pop() {
            drain_owned_ac_template(template, &mut work);
        }
    }
}

impl AcReconstructTemplate {
    /// Convert an AST rewrite pattern into a σ-reconstruction template. Returns `None` for a node the
    /// nested structural-AC reconstruction does not model (a substitution / bare lambda / map / zip —
    /// never present in a well-formed In/Out rule). A constructor applied to a SINGLE HashBag
    /// collection lowers to [`Self::Bag`]; a SINGLE-binder constructor applied to one `^x. body`
    /// lambda lowers to [`Self::Binder`] (A-S5.8, F8-AM-1 — the ctor tag is ERASED, mirroring the
    /// `^lambda` M-reflect image; a multi-binder or a pre-scope-field binder stays `None`,
    /// fail-closed); every other `Apply` to [`Self::Node`]; a bare `Var` to [`Self::Var`].
    fn from_pattern(pattern: &Pattern, def: &LanguageDef) -> Option<Self> {
        enum Task<'pattern> {
            Visit(&'pattern Pattern),
            Node {
                constructor: String,
                child_count: usize,
            },
            Bag {
                op: String,
                rest: Option<String>,
                element_count: usize,
            },
            Binder,
        }

        let mut tasks = vec![Task::Visit(pattern)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Term(PatternTerm::Var(name))) => {
                    values.push(Self::Var(name.to_string()));
                },
                Task::Visit(Pattern::Term(PatternTerm::Apply { constructor, args })) => {
                    if let [Pattern::Collection { coll_type, elements, rest }] = args.as_slice() {
                        if !matches!(coll_type, None | Some(CollectionType::HashBag)) {
                            return None;
                        }
                        tasks.push(Task::Bag {
                            op: constructor.to_string(),
                            rest: rest.as_ref().map(ToString::to_string),
                            element_count: elements.len(),
                        });
                        tasks.extend(elements.iter().rev().map(Task::Visit));
                    } else if let [Pattern::Term(PatternTerm::Lambda { body, .. })] =
                        args.as_slice()
                    {
                        let label = constructor.to_string();
                        let is_single_binder = def.terms.iter().any(|term| {
                            term.label == label
                                && crate::rho_net_subst_trs::is_binder_term(term)
                                && !term.term_context.as_ref().is_some_and(|params| {
                                    params.iter().any(|param| {
                                        matches!(param, TermParam::MultiAbstraction { .. })
                                    })
                                })
                        });
                        if !is_single_binder {
                            return None;
                        }
                        tasks.push(Task::Binder);
                        tasks.push(Task::Visit(body));
                    } else {
                        tasks.push(Task::Node {
                            constructor: constructor.to_string(),
                            child_count: args.len(),
                        });
                        tasks.extend(args.iter().rev().map(Task::Visit));
                    }
                },
                Task::Visit(_) => return None,
                Task::Node { constructor, child_count } => {
                    let first = values.len().checked_sub(child_count)?;
                    let children = values.split_off(first);
                    values.push(Self::Node { constructor, children });
                },
                Task::Bag { op, rest, element_count } => {
                    let first = values.len().checked_sub(element_count)?;
                    let elements = values.split_off(first);
                    values.push(Self::Bag { op, elements, rest });
                },
                Task::Binder => {
                    let body = values.pop()?;
                    values.push(Self::Binder { body: Box::new(body) });
                },
            }
        }
        (values.len() == 1).then(|| values.pop()).flatten()
    }

    /// Collect every LHS-variable name the template references (the `Var` leaves + each `Bag`'s
    /// `rest`) into `out`. Used to check the RHS reduct templates are σ-closed (every var an LHS var).
    ///
    /// `pub(crate)`: the A-S5.5 driver AC-carrier receivers (`crate::rho_net_drive`) compute
    /// the SAME referenced-name set to lay out their bind-pattern slots.
    pub(crate) fn collect_vars(&self, out: &mut HashSet<String>) {
        let mut work = vec![self];
        while let Some(template) = work.pop() {
            match template {
                Self::Var(name) => {
                    out.insert(name.clone());
                },
                Self::Node { children, .. } => work.extend(children.iter().rev()),
                Self::Bag { elements, rest, .. } => {
                    work.extend(elements.iter().rev());
                    if let Some(rest) = rest {
                        out.insert(rest.clone());
                    }
                },
                Self::Binder { body } => work.push(body),
            }
        }
    }

    /// A-S5.8 (F8-AM-1): whether this template introduces a binder anywhere — the
    /// fail-closed routing predicate: a binder-templated nested structural-AC rule gets the
    /// NO-MATCH-ENTRY disposition ([`RhoNetLoweredRule::NestedStructuralAcBinderTemplated`])
    /// instead of a site-keyed match receiver (the receiver's VALUE-position rebuild cannot
    /// inline the async `^shift` the σ-slot shift rule requires), while the DRIVE carrier —
    /// which pre-computes shifted slots on fresh channels before its join — carries the rule.
    pub(crate) fn contains_binder(&self) -> bool {
        let mut work = vec![self];
        while let Some(template) = work.pop() {
            match template {
                Self::Var(_) => {},
                Self::Node { children, .. } => work.extend(children.iter().rev()),
                Self::Bag { elements, .. } => work.extend(elements.iter().rev()),
                Self::Binder { .. } => return true,
            }
        }
        false
    }
}

/// Walk a [`AcReconstructTemplate`] with a firing's resolved σ (`find_sigma`, mapping an LHS variable
/// name to its matched ground sub-term) and rebuild the ground term — the host-computed operand /
/// reduct the nested structural-AC σ-injection reflects. Returns `None` if σ is missing any variable
/// the template references (fail-closed: the σ-injection then declines rather than reflect a partial
/// term). `Bag` splices `σ[rest].children` (the residual bag the AC match bound the remainder to).
///
/// A-S5.8 (F8-AM-1b/1c): a [`AcReconstructTemplate::Binder`] wraps its instantiated body in the
/// ctor-erased `^lambda` node, and every σ-slot value fetched UNDER `k` template binders is
/// pre-shifted by `k` composed applications of the HOST de Bruijn shift
/// ([`shift_reflected_ground_term_by`], the `^shift(Z, ·)` mirror) — PRE-SPLICE, per slot, never by
/// shifting a composed body. A slot value the mirror cannot shift (a reserved shape `^shift` has
/// no arm for, e.g. a `^multilambda`) fails closed (`None`).
pub fn instantiate_ac_reconstruct_template(
    template: &AcReconstructTemplate,
    find_sigma: &impl Fn(&str) -> Option<GroundTerm>,
) -> Option<GroundTerm> {
    instantiate_ac_reconstruct_template_at_depth(template, find_sigma, 0)
}

/// The depth-threaded core of [`instantiate_ac_reconstruct_template`]: `binder_depth` counts the
/// enclosing [`AcReconstructTemplate::Binder`] scopes (the F8-AM-1c statically-known `k`); every
/// σ fetch at this depth is shifted `k` times before splicing.
fn instantiate_ac_reconstruct_template_at_depth(
    template: &AcReconstructTemplate,
    find_sigma: &impl Fn(&str) -> Option<GroundTerm>,
    binder_depth: usize,
) -> Option<GroundTerm> {
    enum Task<'template> {
        Visit {
            template: &'template AcReconstructTemplate,
            binder_depth: usize,
        },
        Node {
            constructor: String,
            child_count: usize,
        },
        Bag {
            op: String,
            rest: Option<String>,
            element_count: usize,
            binder_depth: usize,
        },
        Binder,
    }

    let shifted_sigma = |name: &str, depth: usize| -> Option<GroundTerm> {
        let value = find_sigma(name)?;
        if depth == 0 {
            Some(value)
        } else {
            shift_reflected_ground_term_by(&value, 0, depth)
        }
    };

    let mut tasks = vec![Task::Visit { template, binder_depth }];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit {
                template: AcReconstructTemplate::Var(name),
                binder_depth,
            } => {
                values.push(shifted_sigma(name, binder_depth)?);
            },
            Task::Visit {
                template: AcReconstructTemplate::Node { constructor, children },
                binder_depth,
            } => {
                tasks.push(Task::Node {
                    constructor: constructor.clone(),
                    child_count: children.len(),
                });
                tasks.extend(
                    children
                        .iter()
                        .rev()
                        .map(|template| Task::Visit { template, binder_depth }),
                );
            },
            Task::Visit {
                template: AcReconstructTemplate::Bag { op, elements, rest },
                binder_depth,
            } => {
                tasks.push(Task::Bag {
                    op: op.clone(),
                    rest: rest.clone(),
                    element_count: elements.len(),
                    binder_depth,
                });
                tasks.extend(
                    elements
                        .iter()
                        .rev()
                        .map(|template| Task::Visit { template, binder_depth }),
                );
            },
            Task::Visit {
                template: AcReconstructTemplate::Binder { body },
                binder_depth,
            } => {
                tasks.push(Task::Binder);
                tasks.push(Task::Visit {
                    template: body,
                    binder_depth: binder_depth + 1,
                });
            },
            Task::Node { constructor, child_count } => {
                let first = values.len().checked_sub(child_count)?;
                let children = values.split_off(first);
                values.push(GroundTerm::new(constructor, children));
            },
            Task::Bag { op, rest, element_count, binder_depth } => {
                let first = values.len().checked_sub(element_count)?;
                let mut elements = values.split_off(first);
                if let Some(rest) = rest {
                    let rest = shifted_sigma(&rest, binder_depth)?;
                    elements.extend(rest.children.iter().cloned());
                }
                values.push(GroundTerm::collection(CollectionType::HashBag, op, elements));
            },
            Task::Binder => {
                let body = values.pop()?;
                values.push(GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![body]));
            },
        }
    }
    (values.len() == 1).then(|| values.pop()).flatten()
}

/// A-S5.8: the HOST-side mirror of the in-Rho `^shift(c, t, ret)` receiver over the reflected
/// [`GroundTerm`] encoding (`rho_net_subst_trs.rs` — the σ-slot pre-shift of the F8-AM-1c rule):
///
/// * `^bound(peano(n))` — increment `n ≥ cutoff` (the Peano numeral re-encoded), else unchanged;
/// * `^lambda(b)` — descend with `cutoff + 1` (the depth increment);
/// * `^free(x)` — inert;
/// * a HashBag collection — descend every element at an UNCHANGED cutoff (a bag crosses no
///   binder — the mirror of the A-S5.8 `^shift` soup arm, F8-AM-5e);
/// * any other positional constructor — structural descent (the C2 congruence arms).
///
/// `None` (fail-closed) exactly where the in-Rho `^shift` has NO arm and would stall: a
/// `^multilambda`, a reserved reduction tag, a malformed `^bound` payload, or a non-HashBag
/// collection — the host mirror never invents semantics the receiver family lacks.
/// Apply `amount` composed de Bruijn shifts in one bottom-up pass. Repeating
/// the one-step `^shift` mirror `amount` times increments every
/// qualifying bound index by exactly `amount`; traversing the same ground tree
/// once is equivalent and removes the former binder-depth multiplication.
fn shift_reflected_ground_term_by(
    term: &GroundTerm,
    cutoff: usize,
    amount: usize,
) -> Option<GroundTerm> {
    enum Task<'term> {
        Visit {
            term: &'term GroundTerm,
            cutoff: usize,
        },
        Assemble {
            constructor: String,
            coll_type: Option<CollectionType>,
            child_count: usize,
        },
    }

    let mut tasks = vec![Task::Visit { term, cutoff }];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { term, cutoff } => {
                if let Some(kind) = &term.coll_type {
                    if *kind != CollectionType::HashBag {
                        return None;
                    }
                    tasks.push(Task::Assemble {
                        constructor: term.constructor.clone(),
                        coll_type: Some(CollectionType::HashBag),
                        child_count: term.children.len(),
                    });
                    tasks.extend(
                        term.children
                            .iter()
                            .rev()
                            .map(|term| Task::Visit { term, cutoff }),
                    );
                    continue;
                }
                match term.constructor.as_str() {
                    BOUND_VAR_REFLECT_LABEL => {
                        let [numeral] = term.children.as_slice() else {
                            return None;
                        };
                        let n = decode_peano_ground(numeral)?;
                        values.push(if n >= cutoff {
                            GroundTerm::new(
                                BOUND_VAR_REFLECT_LABEL,
                                vec![encode_peano_ground(n + amount)],
                            )
                        } else {
                            term.clone()
                        });
                    },
                    LAMBDA_REFLECT_LABEL => {
                        let [body] = term.children.as_slice() else {
                            return None;
                        };
                        tasks.push(Task::Assemble {
                            constructor: LAMBDA_REFLECT_LABEL.to_owned(),
                            coll_type: None,
                            child_count: 1,
                        });
                        tasks.push(Task::Visit { term: body, cutoff: cutoff + 1 });
                    },
                    FREE_VAR_REFLECT_LABEL => values.push(term.clone()),
                    MULTILAMBDA_REFLECT_LABEL
                    | SUBST_RESERVED_LABEL
                    | SHIFT_RESERVED_LABEL
                    | SHIFTK_RESERVED_LABEL
                    | CMP_RESERVED_LABEL
                    | PRED_RESERVED_LABEL
                    | PEANO_ZERO_REFLECT_LABEL
                    | PEANO_SUCC_REFLECT_LABEL => return None,
                    _ => {
                        tasks.push(Task::Assemble {
                            constructor: term.constructor.clone(),
                            coll_type: None,
                            child_count: term.children.len(),
                        });
                        tasks.extend(
                            term.children
                                .iter()
                                .rev()
                                .map(|term| Task::Visit { term, cutoff }),
                        );
                    },
                }
            },
            Task::Assemble { constructor, coll_type, child_count } => {
                let first = values.len().checked_sub(child_count)?;
                let children = values.split_off(first);
                values.push(GroundTerm { constructor, children, coll_type });
            },
        }
    }
    (values.len() == 1).then(|| values.pop()).flatten()
}

/// Decode a reflected Peano numeral `S(S(…(Z)))` [`GroundTerm`] to its `usize`, `None` on any
/// non-numeral shape (fail-closed).
fn decode_peano_ground(term: &GroundTerm) -> Option<usize> {
    let mut n = 0usize;
    let mut cursor = term;
    loop {
        if cursor.coll_type.is_some() {
            return None;
        }
        match cursor.constructor.as_str() {
            PEANO_ZERO_REFLECT_LABEL if cursor.children.is_empty() => return Some(n),
            PEANO_SUCC_REFLECT_LABEL => {
                let [inner] = cursor.children.as_slice() else {
                    return None;
                };
                n += 1;
                cursor = inner;
            },
            _ => return None,
        }
    }
}

/// Encode a `usize` as the reflected Peano numeral `S^n(Z)` [`GroundTerm`].
fn encode_peano_ground(n: usize) -> GroundTerm {
    let mut numeral = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..n {
        numeral = GroundTerm::new(PEANO_SUCC_REFLECT_LABEL, vec![numeral]);
    }
    numeral
}

/// Extract `op{ elements, ...rest }` from a constructor applied to a SINGLE HashBag collection,
/// resolving the operand kind PER-CONSTRUCTOR via the grammar (`op`'s declared collection parameter)
/// when the parser left the pattern's own `coll_type` unset. UNLIKE [`collection_apply`] (which takes
/// a single `resolved_kind` for the WHOLE rule — correct only when the operand bag is the pattern
/// ROOT), this resolves the kind from the bag's OWN op, so it also finds a bag NESTED under a wrapper
/// constructor (`OutRule`'s root `PAmb(M, PPar{…})`, whose inner `PPar` the root's kind cannot name).
fn resolve_bag_apply<'a>(
    pattern: &'a Pattern,
    def: &LanguageDef,
) -> Option<(String, &'a [Pattern], Option<Ident>)> {
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    let [Pattern::Collection { coll_type, elements, rest }] = args.as_slice() else {
        return None;
    };
    let kind = coll_type
        .clone()
        .or_else(|| resolve_constructor_collection_type(def, &constructor.to_string()));
    if kind != Some(CollectionType::HashBag) {
        return None;
    }
    Some((constructor.to_string(), elements.as_slice(), rest.clone()))
}

/// Whether `element` is a DEPTH-2 NESTED element `C(a₀, …, op'{ … }, …)` — a constructor one of whose
/// arguments is itself a HashBag ([`resolve_bag_apply`]). The nested element is `PAmb N (PPar {…})` in
/// the Ambient In/Out rules; a flat `OpenRule` element (`POpen N P`) has no bag argument, so this
/// distinguishes the nested rule from the flat [`structural_ac_rule_shape`] path.
fn element_is_nested(element: &Pattern, def: &LanguageDef) -> bool {
    matches!(
        element,
        Pattern::Term(PatternTerm::Apply { args, .. })
            if args.iter().any(|arg| resolve_bag_apply(arg, def).is_some())
    )
}

/// Accumulate the per-name occurrence count of every `PatternTerm::Var` in `pattern` (recursing
/// through `Apply` args and `Collection` elements; a `Collection`'s `...rest` remainder is NOT a
/// `Var` node, so remainder variables are excluded). The cross-level non-linear variable `M` is the
/// unique name whose count is exactly `2` (it occurs in the inner capability AND at the outer level).
fn collect_pattern_var_counts(pattern: &Pattern, counts: &mut HashMap<String, usize>) {
    let mut work = vec![pattern];
    while let Some(pattern) = work.pop() {
        match pattern {
            Pattern::Term(PatternTerm::Var(name)) => {
                *counts.entry(name.to_string()).or_insert(0) += 1;
            },
            Pattern::Term(PatternTerm::Apply { args, .. }) => {
                work.extend(args.iter().rev());
            },
            Pattern::Collection { elements, .. } => {
                work.extend(elements.iter().rev());
            },
            _ => {},
        }
    }
}

/// The number of `PatternTerm::Var(var)` occurrences in `pattern` (the cross-level `M`'s occurrence
/// count = the number of guard σ slots the receiver's match pattern binds).
pub(crate) fn count_var_occurrences(pattern: &Pattern, var: &Ident) -> usize {
    let mut counts = HashMap::new();
    collect_pattern_var_counts(pattern, &mut counts);
    counts.get(&var.to_string()).copied().unwrap_or(0)
}

/// Collect every LHS-bound variable NAME `pattern` supplies to σ — both `PatternTerm::Var` leaves AND
/// each `Collection`'s `...rest` remainder marker (an `Ident`, not a `Var` node, but bound by the AC
/// match and available to the RHS templates, e.g. the inner `rest1` the reduct's `{P, ...rest1}`
/// splices). Used to check the RHS reduct templates are σ-closed.
fn collect_pattern_lhs_vars(pattern: &Pattern, out: &mut HashSet<String>) {
    let mut work = vec![pattern];
    while let Some(pattern) = work.pop() {
        match pattern {
            Pattern::Term(PatternTerm::Var(name)) => {
                out.insert(name.to_string());
            },
            Pattern::Term(PatternTerm::Apply { args, .. }) => {
                work.extend(args.iter().rev());
            },
            Pattern::Collection { elements, rest, .. } => {
                work.extend(elements.iter().rev());
                if let Some(rest) = rest {
                    out.insert(rest.to_string());
                }
            },
            _ => {},
        }
    }
}

/// The first `PatternTerm::Var` in `pattern` whose name is `name` — used to recover the cross-level
/// channel variable's `Ident` (preserving its span) after locating it by name via occurrence counts.
fn find_var_ident(pattern: &Pattern, name: &str) -> Option<Ident> {
    let mut work = vec![pattern];
    while let Some(pattern) = work.pop() {
        match pattern {
            Pattern::Term(PatternTerm::Var(ident)) if ident == name => {
                return Some(ident.clone());
            },
            Pattern::Term(PatternTerm::Apply { args, .. }) => {
                work.extend(args.iter().rev());
            },
            Pattern::Collection { elements, .. } => {
                work.extend(elements.iter().rev());
            },
            _ => {},
        }
    }
    None
}

#[cfg(test)]
#[path = "../tests/support/rho_net_pattern_analysis_recursive_oracle.rs"]
mod pattern_analysis_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/ac_template_recursive_oracle.rs"]
mod ac_template_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/nested_match_pattern_recursive_oracle.rs"]
mod nested_match_pattern_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/spread_term_recursive_oracle.rs"]
mod spread_term_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/lower_lhs_vars_recursive_oracle.rs"]
mod lower_lhs_vars_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/rho_net_reflection_recursive_oracle.rs"]
mod reflection_recursive_oracle;

/// The recognized shape of a DEPTH-2 NESTED structural non-linear AC rewrite (the Ambient
/// `InRule`/`OutRule`). Both are `k = 2` outer elements where EXACTLY ONE is NESTED (`PAmb N (PPar
/// {…})`, whose second argument is a HashBag carrying the capability `in(m,·)`/`out(m,·)`), sharing a
/// CROSS-LEVEL non-linear channel `M` (occurring in the inner capability AND — for `InRule` — a
/// sibling outer ambient, or — for `OutRule` — the ROOT ambient wrapping the bag). The RHS is a
/// re-assembled NESTED restructuring whose fixed elements are host-computed from σ (never bare LHS
/// vars, unlike the flat [`StructuralAcShape`]). Returned only for this precise shape.
///
/// (No `PartialEq`/`Eq`: it stores an AST [`Pattern`], which is not `PartialEq`.)
#[derive(Debug, Clone)]
pub(crate) struct NestedStructuralAcShape {
    /// The AC bag operator constructor (e.g. `PPar`) — the outer operand bag AND the RHS reduct bag.
    pub op: String,
    /// The LHS root pattern (the operand). `InRule`: the bag `Apply(PPar, [Collection…])`. `OutRule`:
    /// the wrapper `Apply(PAmb, [Var(M), Apply(PPar, [Collection…])])`. The receiver's match pattern
    /// AND the operand reconstruction template are both derived from it.
    pub root_pattern: Pattern,
    /// The shared cross-level NON-LINEAR channel variable `M`.
    pub nonlinear_var: Ident,
    /// The outer bag's `...rest` remainder — bound (a σ slot) on the receiver. Where it is
    /// CONSUMED on the RHS is [`Self::rest_splices_at_top`]. Nested-bag remainders (e.g. `rest1`)
    /// ride the reduct either way.
    pub spliced_rest: Ident,
    /// The `m` RHS reduct element templates (in RHS order) — each reconstructed from σ and delivered
    /// as a host-σ-sourced value (the reduct is a NESTED restructuring, never a bare LHS var).
    pub reduct_templates: Vec<AcReconstructTemplate>,
    /// Where the outer `...rest` remainder is consumed on the RHS (A-S5.4b, AM-1 — exactly-once):
    ///
    /// * `true` — TOP-SPLICED: the RHS bag is `op{ r₀, …, ...rest }` and the receiver body splices
    ///   the bound rest slot at the top level (`InRule` and the InOutDemo ejection-shaped
    ///   `OutRule`).
    /// * `false` — TEMPLATE-CONSUMED: the RHS bag carries NO top-level rest; the remainder is
    ///   referenced exactly once INSIDE a reduct template (the C-G (Red Out) redeclared Ambient
    ///   `OutRule`, whose residual `...rest2` is KEPT INSIDE `m` as the rest-only inner bag
    ///   `(PAmb M (PPar {...rest2}))`) and rides the rebuilt reduct, so the body splices nothing
    ///   at the top.
    pub rest_splices_at_top: bool,
}

/// Recognize a DEPTH-2 NESTED structural non-linear AC rewrite ([`NestedStructuralAcShape`], the
/// Ambient `InRule`/`OutRule`). Fail-closed on every other shape: a flat `OpenRule` (no nested
/// element — handled by [`structural_ac_rule_shape`]), a Comm/substitution, an LHS with no
/// with-rest HashBag operand (bag-rooted OR constructor-wrapping-a-bag), ≠1 cross-level (count-2)
/// non-linear variable, an RHS that is not a bag over the SAME `op` consuming the outer rest
/// EXACTLY ONCE (top-spliced OR template-consumed — [`NestedStructuralAcShape::rest_splices_at_top`],
/// A-S5.4b AM-1), or an RHS template referencing a variable σ cannot supply.
pub(crate) fn nested_structural_ac_rule_shape(
    left: &Pattern,
    right: &Pattern,
    def: &LanguageDef,
) -> Option<NestedStructuralAcShape> {
    // (1) The outer operand bag + entry shape.
    //     InRule:  left = op{ elements, ...rest }               (bag-rooted).
    //     OutRule: left = W(v, op{ elements, ...rest })          (wrapper-rooted; v is the root name).
    let (op, outer_elements, outer_rest, wrapper_rooted): (String, &[Pattern], Ident, bool) =
        if let Some((op, elements, Some(rest))) = resolve_bag_apply(left, def) {
            (op, elements, rest, false)
        } else if let Pattern::Term(PatternTerm::Apply { args, .. }) = left {
            // Wrapper-rooted: a constructor `W(v, op{ … })` whose SECOND argument is the with-rest
            // HashBag. The first argument is the root ambient name (the cross-level `M`).
            let [Pattern::Term(PatternTerm::Var(_)), inner] = args.as_slice() else {
                return None;
            };
            match resolve_bag_apply(inner, def) {
                Some((op, elements, Some(rest))) => (op, elements, rest, true),
                _ => return None,
            }
        } else {
            return None;
        };
    // A bag-rooted rule needs ≥2 outer elements for a cross-level pair (both `M` occurrences sit
    // in the bag). A wrapper-rooted rule carries one `M` occurrence at the root name, so ONE
    // nested element suffices — the A-S5.4b (AM-1) redeclared Ambient `OutRule`
    // `(PAmb M (PPar {nested, ...rest2}))` is exactly this rest-only inner-bag shape.
    let minimum_outer_elements = if wrapper_rooted { 1 } else { 2 };
    if outer_elements.len() < minimum_outer_elements {
        return None;
    }

    // (2) Exactly the nested shape: at least one outer element is DEPTH-2 nested (a bag argument).
    //     A flat `OpenRule` (`{ (open N P), (amb N Q), ...rest }`) has NO nested element, so it is
    //     rejected here and stays on the flat [`structural_ac_rule_shape`] path.
    if !outer_elements
        .iter()
        .any(|element| element_is_nested(element, def))
    {
        return None;
    }

    // (3) The cross-level non-linear channel `M`: the UNIQUE variable occurring exactly twice in the
    //     LHS (once in the inner capability, once at the outer level). A second count-2 variable
    //     (ambiguous guard) or none rejects the shape.
    let mut counts: HashMap<String, usize> = HashMap::new();
    collect_pattern_var_counts(left, &mut counts);
    let mut cross_level: Option<String> = None;
    for (name, count) in &counts {
        if *count == 2 {
            if cross_level.replace(name.clone()).is_some() {
                return None;
            }
        } else if *count > 2 {
            // A variable occurring ≥3 times is not the canonical single cross-level pair.
            return None;
        }
    }
    let nonlinear_name = cross_level?;
    // Recover the actual `Ident` (with its span) rather than synthesize one.
    let nonlinear_var = find_var_ident(left, &nonlinear_name)?;

    // (4) RHS: a bag over the SAME `op`, ≥1 reduct element, consuming the outer rest EXACTLY ONCE
    //     (A-S5.4b, AM-1) in one of the two legal placements:
    //       * TOP-SPLICED — `op{ r₀, …, ...outer_rest }` (the pre-A-S5.4b-only form: `InRule`,
    //         the InOutDemo ejection-shaped `OutRule`); the rest must then appear in NO template.
    //       * TEMPLATE-CONSUMED — `op{ r₀, … }` with NO top-level rest, the outer rest referenced
    //         exactly once INSIDE a reduct template (the C-G (Red Out) redeclared Ambient
    //         `OutRule`: `...rest2` rides the rest-only inner bag `(PAmb M (PPar {...rest2}))`).
    //     Anything else — a different rest name, a dropped rest (residual material silently
    //     discarded), or a duplicated rest (residual material duplicated) — is rejected.
    let (rhs_op, rhs_elements, rhs_rest) = resolve_bag_apply(right, def)?;
    if rhs_op != op || rhs_elements.is_empty() {
        return None;
    }
    let mut reduct_templates = Vec::with_capacity(rhs_elements.len());
    for element in rhs_elements {
        reduct_templates.push(AcReconstructTemplate::from_pattern(element, def)?);
    }
    let rest_template_occurrences: usize = reduct_templates
        .iter()
        .map(|template| count_template_name_occurrences(template, &outer_rest.to_string()))
        .sum();
    let rest_splices_at_top = match (rhs_rest.as_ref(), rest_template_occurrences) {
        // Top-spliced: the RHS bag's remainder IS the outer rest, and no template touches it.
        (Some(rest), 0) if *rest == outer_rest => true,
        // Template-consumed: no top-level rest; exactly one template reference carries it.
        (None, 1) => false,
        // Every other combination violates exactly-once consumption — fail closed.
        _ => return None,
    };

    // (5) Every RHS-template variable must be an LHS variable — a `Var` leaf OR a nested `...rest`
    //     remainder the AC match binds (e.g. the inner `rest1` the reduct's `{P, ...rest1}` splices).
    //     This rejects an RHS that reintroduces a fresh variable the σ cannot supply.
    let mut lhs_vars: HashSet<String> = HashSet::new();
    collect_pattern_lhs_vars(left, &mut lhs_vars);
    let mut reduct_vars: HashSet<String> = HashSet::new();
    for template in &reduct_templates {
        template.collect_vars(&mut reduct_vars);
    }
    // The spliced outer-rest rides the RHS bag's remainder (not a template var), so exempt it.
    reduct_vars.remove(&outer_rest.to_string());
    if !reduct_vars.iter().all(|v| lhs_vars.contains(v)) {
        return None;
    }

    Some(NestedStructuralAcShape {
        op,
        root_pattern: left.clone(),
        nonlinear_var,
        spliced_rest: outer_rest,
        reduct_templates,
        rest_splices_at_top,
    })
}

/// The number of times `name` is referenced by `template` — a `Var(name)` leaf or a `Bag` whose
/// `...rest` remainder is `name`, recursively. Drives the AM-1 exactly-once outer-rest consumption
/// check in [`nested_structural_ac_rule_shape`].
fn count_template_name_occurrences(template: &AcReconstructTemplate, name: &str) -> usize {
    let mut count = 0;
    let mut work = vec![template];
    while let Some(template) = work.pop() {
        match template {
            AcReconstructTemplate::Var(var) => count += usize::from(var == name),
            AcReconstructTemplate::Node { children, .. } => {
                work.extend(children.iter().rev());
            },
            AcReconstructTemplate::Bag { elements, rest, .. } => {
                count += usize::from(rest.as_deref() == Some(name));
                work.extend(elements.iter().rev());
            },
            AcReconstructTemplate::Binder { body } => work.push(body),
        }
    }
    count
}

/// Build the receiver's match PATTERN for a nested structural-AC operand by walking the LHS root
/// pattern, threading the flat σ-slot layout: each occurrence of the cross-level channel `M` binds a
/// distinct GUARD slot (`FreeVar(0…g)`, recorded in `occurrence_levels`); the OUTER bag's remainder
/// binds the SPLICED-rest slot (`FreeVar(spliced_rest_slot)`); every OTHER position is a wildcard `_`
/// (its value rides the host-computed reduct, delivered separately). A constructor applied to a
/// single HashBag lowers to the order-independent process-soup `remainder | @"ac:op"!(⟦e⟧) | …`
/// (byte-identical to [`reflect_ac_bag_par`]'s carrier, so the reflected operand matches); every
/// other constructor to the tagged `EList[ GPrivate(tag), … ]` (byte-identical to
/// [`reflect_ground_term_par`]). The guard slot counter is threaded via `next_guard_slot`, so a
/// nested `M` (inside the inner capability) and an outer `M` bind DISTINCT slots joined by the
/// depth-agnostic `EEq` guard.
///
/// `pub(crate)`: the A-S5.5 driver (`crate::rho_net_drive`) transcribes each admitted
/// structural-AC / nested-structural-AC rule's CHECK pattern with this SAME builder in
/// `Match`-case position over the driven value (plan v2 §4.3.1), so the driver's redex
/// checks can never drift from the installed receivers' operand patterns.
trait NestedMatchPatternPolicy {
    fn variable(&mut self, variable: &Ident) -> Par;
    fn remainder(&mut self, remainder: Option<&Ident>) -> Par;
}

/// Shared bottom-up PDA for the two nested-AC receiver pattern layouts. The
/// policies allocate only leaf/remainder slots; constructor tagging, marker
/// absorption, soup sends, child ordering, and result assembly live here once.
fn build_nested_match_pattern(
    pattern: &Pattern,
    policy: &mut impl NestedMatchPatternPolicy,
    language_fingerprint: &str,
) -> Par {
    enum Task<'pattern> {
        Visit(&'pattern Pattern),
        AssembleBag {
            soup: Par,
            element_channel: String,
            element_count: usize,
        },
        AssembleNode {
            prefix: Vec<Par>,
            child_count: usize,
        },
    }

    let mut tasks = vec![Task::Visit(pattern)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Pattern::Term(PatternTerm::Var(variable))) => {
                values.push(policy.variable(variable));
            },
            Task::Visit(Pattern::Term(PatternTerm::Apply { constructor, args })) => {
                if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                    let element_channel =
                        ac_soup_channel(language_fingerprint, &constructor.to_string());
                    let soup = policy.remainder(rest.as_ref());
                    tasks.push(Task::AssembleBag {
                        soup,
                        element_channel,
                        element_count: elements.len(),
                    });
                    tasks.extend(elements.iter().rev().map(Task::Visit));
                } else {
                    let label = constructor.to_string();
                    let mut prefix = Vec::with_capacity(args.len() + 2);
                    prefix.push(GPrivateBuilder::new_par_from_string(reflect_tag(
                        language_fingerprint,
                        &label,
                    )));
                    if is_marked_object_label(&label) {
                        prefix.push(new_wildcard_par(Vec::new(), true));
                    }
                    tasks.push(Task::AssembleNode { prefix, child_count: args.len() });
                    tasks.extend(args.iter().rev().map(Task::Visit));
                }
            },
            Task::Visit(_) => values.push(new_wildcard_par(Vec::new(), true)),
            Task::AssembleBag { mut soup, element_channel, element_count } => {
                let first = values
                    .len()
                    .checked_sub(element_count)
                    .expect("nested match PDA lost a bag element result");
                for element_pattern in values.drain(first..) {
                    let send_pattern = new_send_par(
                        new_gstring_par(element_channel.clone(), Vec::new(), false),
                        vec![element_pattern],
                        false,
                        Vec::new(),
                        true,
                        Vec::new(),
                        true,
                    );
                    soup = soup.append(send_pattern);
                }
                values.push(soup);
            },
            Task::AssembleNode { mut prefix, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .expect("nested match PDA lost a constructor child result");
                prefix.extend(values.drain(first..));
                values.push(new_elist_par(prefix, Vec::new(), true, None, Vec::new(), true));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("nested match PDA produced no result")
}

struct ReportNestedMatchPolicy<'a> {
    nonlinear_var: &'a Ident,
    spliced_rest: &'a Ident,
    spliced_rest_slot: usize,
    next_guard_slot: &'a mut usize,
    occurrence_levels: &'a mut Vec<usize>,
}

impl NestedMatchPatternPolicy for ReportNestedMatchPolicy<'_> {
    fn variable(&mut self, variable: &Ident) -> Par {
        if variable == self.nonlinear_var {
            let slot = *self.next_guard_slot;
            *self.next_guard_slot += 1;
            self.occurrence_levels.push(slot);
            new_freevar_par(slot as i32, Vec::new())
        } else {
            new_wildcard_par(Vec::new(), true)
        }
    }

    fn remainder(&mut self, remainder: Option<&Ident>) -> Par {
        if remainder == Some(self.spliced_rest) {
            new_freevar_par(self.spliced_rest_slot as i32, Vec::new())
        } else {
            new_wildcard_par(Vec::new(), true)
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn nested_match_pattern_for(
    pattern: &Pattern,
    nonlinear_var: &Ident,
    spliced_rest: &Ident,
    spliced_rest_slot: usize,
    next_guard_slot: &mut usize,
    occurrence_levels: &mut Vec<usize>,
    language_fingerprint: &str,
) -> Par {
    build_nested_match_pattern(
        pattern,
        &mut ReportNestedMatchPolicy {
            nonlinear_var,
            spliced_rest,
            spliced_rest_slot,
            next_guard_slot,
            occurrence_levels,
        },
        language_fingerprint,
    )
}

/// Build the DEPTH-2 nested structural-AC σ-receiver for a [`NestedStructuralAcShape`]: a persistent
///
/// ```text
/// for( < ⟦nested operand pattern⟧ >, r0, …, r_{m-1}, out <- source )
///   where ( M_a == M_b )
///   { out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | spliced_rest ) }
/// ```
///
/// The connective operand pattern (element 0) matches the reflected operand ORDER-INDEPENDENTLY at
/// every depth (native `spatial_matcher_pda::ListMachine`, with `sub_pars` per level), binding the
/// two cross-level `M`
/// occurrences (the guard slots) + the outer bag's remainder (the spliced-rest slot), and WILDCARDING
/// everything the host-computed reduct carries. The `m` reduct slots (`FreeVar(g+1..g+1+m)`) carry
/// the host-σ-delivered NESTED reduct elements; `out` is the dynamic out channel. The `condition`
/// fires the COMM only when the two `M` slots are name-equal ([`nonlinear_consistency_condition`],
/// DEPTH-AGNOSTIC — it indexes the flat receive frame); the body splices the `m` reduct elements with
/// `spliced_rest`. This is [`structural_ac_receiver_par`] generalized from a FLAT bag pattern +
/// per-element channel slots to a DEPTH-2 NESTED pattern + two cross-level guard slots.
fn nested_structural_ac_receiver_par(
    shape: &NestedStructuralAcShape,
    source: Par,
    language_fingerprint: &str,
) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, &shape.op);
    let g = count_var_occurrences(&shape.root_pattern, &shape.nonlinear_var);
    let m = shape.reduct_templates.len();
    let spliced_rest_slot = g;
    let first_reduct_level = g + 1;
    let out_level = g + 1 + m;
    let free_count = out_level + 1;

    // Element 0 of the receive bind: the nested with-remainder operand pattern (guard slots `0..g`,
    // the spliced-rest slot `g`, wildcards elsewhere).
    let mut next_guard_slot = 0usize;
    let mut occurrence_levels = Vec::with_capacity(g);
    let bag_pattern = nested_match_pattern_for(
        &shape.root_pattern,
        &shape.nonlinear_var,
        &shape.spliced_rest,
        spliced_rest_slot,
        &mut next_guard_slot,
        &mut occurrence_levels,
        language_fingerprint,
    );

    // The cross-level non-linear consistency guard `EEq(M_a, M_b)`.
    let condition = nonlinear_consistency_condition(&occurrence_levels, free_count);

    // Body: `out!( @"ac:op"!(r0) | … | @"ac:op"!(r_{m-1}) | spliced_rest? )` — one send per RHS
    // reduct, then the spliced outer remainder IFF the shape is top-spliced (identical structure
    // to [`structural_ac_receiver_par`]). A TEMPLATE-CONSUMED shape (A-S5.4b, AM-1 — the
    // redeclared Ambient `OutRule`) carries the remainder INSIDE a host-delivered reduct, so its
    // body splices nothing at the top (the rest slot stays bound-but-unused, keeping the σ slot
    // layout uniform across both placements).
    let rest_bv_index = free_count - 1 - spliced_rest_slot;
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
    // `m ≥ 1` (a nested structural-AC rewrite has ≥1 RHS element), so `body_soup` is always `Some`.
    let body_soup = if shape.rest_splices_at_top {
        let rest_bv =
            new_boundvar_par(rest_bv_index as i32, create_bit_vector(&[rest_bv_index]), false);
        match body_soup {
            Some(soup) => soup.append(rest_bv),
            None => rest_bv,
        }
    } else {
        body_soup.expect("a nested structural-AC rewrite carries at least one RHS reduct element")
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

    // Receive-bind patterns: [operand_pattern, FreeVar(reduct_0), …, FreeVar(reduct_{m-1}), FreeVar(out)].
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

/// Un-skip a DEPTH-2 nested structural-AC-shaped base rewrite to its σ-receiver
/// ([`nested_structural_ac_receiver_par`]), on the rule's OWN trace channel `source` (accept-triad
/// coherence by symmetric derivation, exactly as [`structural_ac_rule_receiver`]). Returns `None`
/// when the rewrite is not a nested structural-AC shape ([`nested_structural_ac_rule_shape`]), so the
/// caller keeps it fail-closed.
pub fn nested_structural_ac_rule_receiver(
    left: &Pattern,
    right: &Pattern,
    source: Par,
    language_fingerprint: &str,
    def: &LanguageDef,
) -> Option<Par> {
    let shape = nested_structural_ac_rule_shape(left, right, def)?;
    // A-S5.8 (F8-AM-1b): a BINDER-TEMPLATED shape has no site-keyed match receiver — the
    // σ-slot shift rule (F8-AM-1c) needs the ASYNC `^shift`, which the receiver's
    // value-position reduct rebuild cannot inline. Decline fail-closed; the rule's lowering
    // disposition is [`RhoNetLoweredRule::NestedStructuralAcBinderTemplated`] (NO-MATCH-ENTRY,
    // recorded, never an install error) and its FIRING mechanism is the A-S5.8 drive
    // carrier, which pre-computes the shifted slots on fresh channels before its join.
    if shape
        .reduct_templates
        .iter()
        .any(AcReconstructTemplate::contains_binder)
    {
        return None;
    }
    Some(nested_structural_ac_receiver_par(&shape, source, language_fingerprint))
}

/// Whether `(left, right)` is a DEPTH-2 NESTED structural non-linear AC rewrite
/// ([`nested_structural_ac_rule_shape`]) — the SINGLE-SOURCE-OF-TRUTH shape predicate the macro's
/// typed-path gate (`needs_typed_dovetail_path`), the typed-lowering routing, and the typed
/// native-rule collector reuse, so the Dovetail report path and the Rho lowering agree byte-for-byte
/// on which rewrites are nested structural-AC firings.
pub fn is_nested_structural_ac_rewrite(left: &Pattern, right: &Pattern, def: &LanguageDef) -> bool {
    nested_structural_ac_rule_shape(left, right, def).is_some()
}

// ─── A-S5.4b (design v2 §3.2): the equations-gate BOUNDARY-CANONICALIZATION recognizer ─────────
//
// The nested structural-AC receiver was gated to binder-free languages (`def.equations.is_empty()`)
// because a declared equational theory could hide a redex from the syntactic matcher. A-S5.4a made
// the generated binder float UNCONDITIONAL (freshen-then-float, `binder_congruence.rs`), and the
// generated report-free invocation bodies now canonicalize the subject through it BEFORE M-reflect
// — so a language whose equations are EXACTLY the float-discharged binder congruences no longer
// needs the gate: every redex modulo its equational theory is syntactically present in the
// canonicalized subject (FV: `BinderFloatCanonicalization.v`, proven over the Cardelli–Gordon
// subset (Struct Res Par) + (Struct Res Amb) + (Struct Res Res); `ma_theory_alignment.md`).
//
// [`equations_boundary_canonicalizable`] recognizes exactly that discharge: empty equations, OR
// (every equation is a recognized binder-float congruence AND the float handler is actually
// generated for the language). The per-equation recognizer [`is_binder_float_equation`] accepts
// exactly two families, checked against the CORRECTED (capture-avoidance-premised) declarations:
//
//   (i)  BINDER-BINDER COMMUTATION — `B(^x. B(^y. V)) = B(^y. B(^x. V))`, the single surface
//        binder nested over itself with the same body variable and swapped binders, premise-free
//        (Ambient `NewComm` = C-G (Struct Res Res));
//   (ii) FLOAT-ACROSS-CONSTRUCTOR — `C(a₁, …, B(^x. P), …) = B(^x. C(a₁, …, P, …))` (either
//        orientation), same constructor `C`, same argument variables, with freshness declared on
//        EVERY floated-past field (`x # aᵢ` and/or `x # ...rest`) — the corrected `InNew`-family
//        (+ `AmbNew` = C-G (Struct Res Amb)) prefix shape and the `ScopeExtrusion` = C-G
//        (Struct Res Par) collection shape. AM-6e HARDENING: `C` must additionally have the exact
//        shape the generated float handler's arms recurse into — the prefix arm floats only a
//        constructor with EXACTLY ONE plain primary-category field (and the binder must sit at
//        that field), and the bag arm only the primary-category collection constructor; a
//        constructor that would fall to the handler's no-recursion catch-all
//        (`binder_congruence.rs` prefix-arm filter) must NOT pass, else a future language admits
//        with a never-floated equation.
//
// [`language_has_float_handler`] restates `should_emit_binder_congruence`'s three conditions
// (`macros/src/gen/runtime/binder_congruence.rs`) on this side of the crate boundary; a macros
// cross-crate agreement test pins the two predicates equal over every bundled language, and a
// macros build check pins the generated float UNCONDITIONAL (no `is_fresh` gate) — the
// recognizer's soundness is versioned on A-S5.4a.

/// A-S5.4b: whether `def`'s declared equational theory is fully discharged by the generated
/// unconditional binder float at the invocation boundary — the replacement for the nested
/// receiver's `def.equations.is_empty()` gate. `true` iff the equations are empty, OR every
/// equation is a recognized binder-float congruence ([`is_binder_float_equation`]) AND the float
/// handler is generated for the language ([`language_has_float_handler`]).
pub fn equations_boundary_canonicalizable(def: &LanguageDef) -> bool {
    if def.equations.is_empty() {
        return true;
    }
    if !language_has_float_handler(def) {
        return false;
    }
    let Some(binder_label) = float_surface_binder_label(def) else {
        return false;
    };
    def.equations
        .iter()
        .all(|equation| is_binder_float_equation(def, equation, &binder_label))
}

/// A-S5.8: the equation-DERIVED satellite table of the in-Rho `^float` receiver family — one
/// `^float-hoist:{C}` satellite per recognized PREFIX float-across-constructor equation
/// (deduplicated by constructor, declaration order) and one `^float-merge:{op}` satellite per
/// recognized COLLECTION float equation (deduplicated by op, declaration order). Read off the
/// SAME per-equation recognizer walk [`equations_boundary_canonicalizable`] admits with
/// ([`classify_float_across_constructor_equation`]), so the emitted family can never drift
/// from the admission (never hardcoded to Ambient). A binder-commutation equation (`NewComm`)
/// derives NO satellite — the Q-NC user decision: in-Rho NewComm reordering is DELIBERATELY
/// omitted (the host's α-canonical-key minimization is not Match-expressible; redex exposure
/// is NewComm-invariant), so the float NF is unique UP TO the NewComm run permutation.
///
/// ★ A-S5.4c — TWO CONSUMERS, ONE DERIVATION. This is no longer only the in-Rho family's
/// table; it is the table of the float congruences a language actually DECLARES, and the
/// generated HOST binder-congruence normal form
/// (`macros/src/gen/runtime/binder_congruence.rs`) now emits one float arm per entry. Hence
/// `pub`. Consumer 2 is why: the host NF used to derive its arms from the primary category's
/// TERM FORMERS instead, floating the binder outward through every constructor of the category
/// whether or not an equation licensed it. For Ambient the two sets coincide; for Pi they did
/// not, and the surplus included `PRep` — a float out of replication (`!(νx.P) ⟶ νx.!P`),
/// UNSOUND in the π-calculus (fresh name per replica on the left, one name shared across all
/// replicas on the right) and not repairable by freshening, because it is not a
/// capture-avoidance failure. Deriving both consumers here is the structural fix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FloatSatelliteTable {
    /// The recognized PREFIX floats: `(constructor, float_index, arity)` per equation — the
    /// `^float-hoist:{C}` satellite in-Rho, the prefix float arm on the host.
    pub hoist: Vec<(String, usize, usize)>,
    /// The recognized COLLECTION floats: the bag op per equation — the `^float-merge:{op}`
    /// satellite in-Rho, the bag-extrusion float arm on the host.
    pub merge_ops: Vec<String>,
}

/// Derive the [`FloatSatelliteTable`] of `def`'s declared float equations (A-S5.8). Total:
/// unrecognized/commutation equations contribute nothing. The in-Rho consumer gates on
/// [`equations_boundary_canonicalizable`] ∧ [`language_has_float_handler`] before emitting; the
/// host consumer (A-S5.4c) does NOT — a language whose equations are not WHOLLY float-discharged
/// (Pi, whose `RepUnfold` is no float) still gets a host NF, just one restricted to the floats it
/// does declare — which is exactly why this table is TOTAL rather than an `Option`.
pub fn float_satellite_table(def: &LanguageDef) -> FloatSatelliteTable {
    let mut table = FloatSatelliteTable::default();
    let Some(binder_label) = float_surface_binder_label(def) else {
        return table;
    };
    for equation in &def.equations {
        match classify_float_across_constructor_equation(def, equation, &binder_label) {
            Some(FloatAcrossClassification::Prefix { constructor, float_index, arity }) => {
                if !table
                    .hoist
                    .iter()
                    .any(|(label, _, _)| *label == constructor)
                {
                    table.hoist.push((constructor, float_index, arity));
                }
            },
            // `collapsible_match` is wrong HERE, and provably so: its suggestion moves the
            // dedup test into a match GUARD, and guarded arms do not count toward
            // exhaustivity — the rewrite stops compiling with E0004 (`Collection` no longer
            // covered). `cargo clippy --fix` applied it, failed to build, and reverted the
            // whole crate's fixes. The `if` stays in the arm BODY.
            #[allow(clippy::collapsible_match)]
            Some(FloatAcrossClassification::Collection { op }) => {
                if !table.merge_ops.contains(&op) {
                    table.merge_ops.push(op);
                }
            },
            None => {},
        }
    }
    table
}

/// A-S5.4b: whether the macros side generates the binder-congruence float handler for `def` — the
/// `rholang-codegen` restatement of `should_emit_binder_congruence`'s three conditions
/// (`macros/src/gen/runtime/binder_congruence.rs`):
///
///   1. the language declares structural-congruence equations,
///   2. it is host-less — no `RhoNativeJoin` guard obligation
///      ([`crate::backend::collect_guard_obligations`]), and
///   3. it has a surface SINGLE-binder constructor over the primary category
///      ([`float_surface_binder_label`]).
///
/// A macros-side cross-crate agreement test pins this predicate ≡ `should_emit_binder_congruence`
/// over every bundled language definition, so the two crates cannot drift.
pub fn language_has_float_handler(def: &LanguageDef) -> bool {
    !def.equations.is_empty()
        && !crate::backend::collect_guard_obligations(def)
            .iter()
            .any(|obligation| {
                matches!(obligation.kind, crate::backend::RhoGuardObligationKind::RhoNativeJoin)
            })
        && float_surface_binder_label(def).is_some()
}

/// The label of the FIRST surface (user-declared) single-binder constructor over the primary
/// category, if any — the binder the generated float handler floats (`Ambient`'s `PNew`). Mirrors
/// the macros-side `surface_single_binder_label` over the AST: a `term_context`-declared rule is a
/// single binder iff it carries a `TermParam::Abstraction` (and no `MultiAbstraction` — the
/// message-passing multi-binders route to the host); an items-declared rule iff its first
/// `bindings` entry points a `GrammarItem::Binder` at a body `NonTerminal`. The body category must
/// be the primary category.
fn float_surface_binder_label(def: &LanguageDef) -> Option<String> {
    let primary = def.types.first()?.name.to_string();
    def.terms
        .iter()
        .filter(|rule| rule.category == primary)
        .find_map(|rule| {
            single_binder_body_category(rule)
                .filter(|body_category| *body_category == primary)
                .map(|_| rule.label.to_string())
        })
}

/// The body category of a surface SINGLE-binder rule, or `None` when the rule is not a single
/// binder (nullary/regular/collection/multi-binder). Mirrors the macros-side
/// `variant_kind_from_term_context` / `variant_kind_from_items` binder classification.
fn single_binder_body_category(rule: &GrammarRule) -> Option<String> {
    if let Some(term_context) = &rule.term_context {
        // A `MultiAbstraction` anywhere makes the rule a MULTI-binder (checked FIRST, exactly as
        // `variant_kind_from_term_context` does) — not a single binder.
        if term_context
            .iter()
            .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
        {
            return None;
        }
        return term_context.iter().find_map(|param| match param {
            TermParam::Abstraction { ty: TypeExpr::Arrow { codomain, .. }, .. } => {
                base_category_name(codomain)
            },
            _ => None,
        });
    }
    // Items route: the single-collection classification takes precedence over bindings (exactly as
    // `variant_kind_from_items` orders its checks), then the first bindings entry names the binder.
    let collection_items = rule
        .items
        .iter()
        .filter(|item| matches!(item, GrammarItem::Collection { .. }))
        .count();
    let non_terminal_items = rule
        .items
        .iter()
        .filter(|item| !matches!(item, GrammarItem::Terminal(_)))
        .count();
    if collection_items == 1 && non_terminal_items == 1 {
        return None;
    }
    let (binder_index, body_indices) = rule.bindings.first()?;
    if !matches!(rule.items.get(*binder_index), Some(GrammarItem::Binder { .. })) {
        return None;
    }
    match rule.items.get(*body_indices.first()?) {
        Some(GrammarItem::NonTerminal { ident, .. }) => Some(ident.to_string()),
        _ => None,
    }
}

/// The base category name of a type expression (`Base` directly; a `Collection`'s element,
/// recursively — the macros-side `extract_base_category` behavior). `None` for shapes a binder
/// codomain never takes (fail-closed).
fn base_category_name(ty: &TypeExpr) -> Option<String> {
    let mut ty = ty;
    loop {
        ty = match ty {
            TypeExpr::Base(ident) => return Some(ident.to_string()),
            TypeExpr::Collection { element, .. } => element,
            _ => return None,
        };
    }
}

/// A-S5.4b: whether `equation` is a recognized BINDER-FLOAT congruence over the surface binder
/// `binder_label` — binder-binder commutation or float-across-constructor (module doc above).
fn is_binder_float_equation(def: &LanguageDef, equation: &Equation, binder_label: &str) -> bool {
    is_binder_commutation_equation(equation, binder_label)
        || is_float_across_constructor_equation(def, equation, binder_label)
}

/// Task #94: how the BINDER-FLOAT lane disposes of one declared equation.
///
/// The Dovetail structural lowering cannot lower a binder-shaped equation — its LHS carries a
/// `Lambda` metapattern, which `pattern_to_dovetail` fails closed on. Until this classifier
/// existed, every such equation looked identical from outside: an entry in a dropped
/// `Vec<String>`. But the three cases are not the same thing at all, and conflating them is
/// exactly the defect Task #94 names:
///
///   * [`Self::FloatAcrossConstructor`] — the generated binder-congruence normal form
///     (`macros/src/gen/runtime/binder_congruence.rs`) DISCHARGES this equation by floating the
///     binder outward before reduction. It is delivered, just on another lane.
///   * [`Self::BinderCommutation`] — `NewComm`. In-Rho reordering is DELIBERATELY omitted (the
///     user's Q-NC decision; see [`float_satellite_table`]): the host's α-canonical-key
///     minimization is not Match-expressible, and redex exposure is NewComm-invariant, so the
///     float normal form is unique UP TO the NewComm run permutation. It is suppressed by
///     decision, not declined by omission.
///   * [`Self::NotFloatFamily`] — genuinely nothing here covers it.
///
/// Total and side-effect-free; reads the SAME recognizer walk `equations_boundary_canonicalizable`
/// admits with, so it can never claim coverage the float handler does not provide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EquationFloatDisposition {
    /// Not a recognized member of the binder-float family (or the language has no generated
    /// float handler at all).
    NotFloatFamily,
    /// Family (ii): FLOAT-ACROSS-CONSTRUCTOR — discharged by the generated float handler.
    FloatAcrossConstructor,
    /// Family (i): BINDER-BINDER COMMUTATION (`NewComm`) — deliberately derives no satellite.
    BinderCommutation,
}

/// Classify one declared equation against the binder-float lane
/// ([`EquationFloatDisposition`]).
///
/// ★ FAILS CLOSED IN THREE PLACES, because a wrong answer here is a *false claim of coverage*
/// — the one failure mode a disposition record must never have:
///
///   1. a language with no generated float handler ([`language_has_float_handler`]) yields
///      `NotFloatFamily` for every equation;
///   2. so does a language with no surface single-binder constructor
///      ([`float_surface_binder_label`]);
///   3. ★ and a recognized float equation whose classification is NOT PRESENT in the emitted
///      [`float_satellite_table`] also yields `NotFloatFamily`.
///
/// Point 3 is not paranoia. `float_satellite_table` DEDUPLICATES hoists by constructor, so two
/// equations that float across the same constructor at DIFFERENT argument positions derive one
/// satellite between them, and the generated handler therefore floats only one of them. Merely
/// *recognizing* the second as float-shaped would attribute it to a lane that does not carry
/// it. Requiring the exact `(constructor, float_index, arity)` triple — or, for the collection
/// form, the exact bag operator — to appear in the emitted table ties the claim to the arm that
/// actually exists.
pub fn classify_equation_float_disposition(
    def: &LanguageDef,
    equation: &Equation,
) -> EquationFloatDisposition {
    if !language_has_float_handler(def) {
        return EquationFloatDisposition::NotFloatFamily;
    }
    let Some(binder_label) = float_surface_binder_label(def) else {
        return EquationFloatDisposition::NotFloatFamily;
    };
    if is_binder_commutation_equation(equation, &binder_label) {
        return EquationFloatDisposition::BinderCommutation;
    }
    let Some(classification) =
        classify_float_across_constructor_equation(def, equation, &binder_label)
    else {
        return EquationFloatDisposition::NotFloatFamily;
    };
    let table = float_satellite_table(def);
    let emitted = match &classification {
        FloatAcrossClassification::Prefix { constructor, float_index, arity } => {
            table.hoist.iter().any(|(label, index, count)| {
                label == constructor && index == float_index && count == arity
            })
        },
        FloatAcrossClassification::Collection { op } => table.merge_ops.contains(op),
    };
    if emitted {
        EquationFloatDisposition::FloatAcrossConstructor
    } else {
        EquationFloatDisposition::NotFloatFamily
    }
}

/// Family (i): BINDER-BINDER COMMUTATION — both sides the single surface binder nested over
/// itself, same body variable, swapped binders, premise-free (`NewComm` = C-G (Struct Res Res)).
fn is_binder_commutation_equation(equation: &Equation, binder_label: &str) -> bool {
    if !equation.premises.is_empty() {
        return false;
    }
    let (Some((left_outer, left_inner, left_body)), Some((right_outer, right_inner, right_body))) = (
        double_binder_shape(&equation.left, binder_label),
        double_binder_shape(&equation.right, binder_label),
    ) else {
        return false;
    };
    left_outer == right_inner && left_inner == right_outer && left_body == right_body
}

/// `B(^a. B(^b. Var(v)))` → `(a, b, v)` (names), else `None`.
fn double_binder_shape(pattern: &Pattern, binder_label: &str) -> Option<(String, String, String)> {
    let (outer, inner_scope) = binder_scope(pattern, binder_label)?;
    let (inner, body) = binder_scope(inner_scope, binder_label)?;
    match body {
        Pattern::Term(PatternTerm::Var(var)) => Some((outer, inner, var.to_string())),
        _ => None,
    }
}

/// `B(^x. body)` → `(x, body)` when `pattern` is the surface binder applied to a single-binder
/// lambda, else `None`.
fn binder_scope<'a>(pattern: &'a Pattern, binder_label: &str) -> Option<(String, &'a Pattern)> {
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    if constructor != binder_label {
        return None;
    }
    let [Pattern::Term(PatternTerm::Lambda { binder, body })] = args.as_slice() else {
        return None;
    };
    Some((binder.to_string(), body.as_ref()))
}

/// A-S5.8: the CLASSIFICATION a recognized float-across-constructor equation carries — the
/// satellite-derivation record ([`float_satellite_table`]) the `^float` family's emitters
/// consume, read off the SAME recognizer walk `equations_boundary_canonicalizable` admits
/// with (never a parallel hand-maintained table).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FloatAcrossClassification {
    /// The PREFIX form (`InNew`-family + `AmbNew`): `C(a₁, …, B(^x. P), …) = B(^x. C(…))` —
    /// the `^float-hoist:{C}` satellite's derivation.
    Prefix {
        /// The floated-across constructor label `C`.
        constructor: String,
        /// The binder-scoped argument's position (the single plain primary-category field).
        float_index: usize,
        /// `C`'s total field count.
        arity: usize,
    },
    /// The COLLECTION form (`ScopeExtrusion`): `op{ …, B(^x. P), …, ...rest } = B(^x. op{…})`
    /// — the `^float-merge:{op}` satellite's derivation.
    Collection {
        /// The AC bag operator constructor `op`.
        op: String,
    },
}

/// Family (ii): FLOAT-ACROSS-CONSTRUCTOR, either orientation.
fn is_float_across_constructor_equation(
    def: &LanguageDef,
    equation: &Equation,
    binder_label: &str,
) -> bool {
    classify_float_across_constructor_equation(def, equation, binder_label).is_some()
}

/// A-S5.8: the classification core of [`is_float_across_constructor_equation`] — the SAME
/// recognizer walk, returning WHICH satellite the equation derives (either orientation).
fn classify_float_across_constructor_equation(
    def: &LanguageDef,
    equation: &Equation,
    binder_label: &str,
) -> Option<FloatAcrossClassification> {
    float_across_sides(def, &equation.left, &equation.right, binder_label, &equation.premises)
        .or_else(|| {
            float_across_sides(
                def,
                &equation.right,
                &equation.left,
                binder_label,
                &equation.premises,
            )
        })
}

/// One orientation of family (ii): `c_side = C(a₁, …, B(^x. P), …)` (prefix form) or
/// `C{ …, (B ^x. P), …, ...rest }` (collection form), `b_side = B(^x. C(a₁, …, P, …))` — same
/// constructor, same argument variables, the freshness premises exactly covering every
/// floated-past field, and `C` in the exact shape the generated float handler floats (AM-6e).
/// Returns the A-S5.8 satellite classification on recognition (`None` = not this family).
fn float_across_sides(
    def: &LanguageDef,
    c_side: &Pattern,
    b_side: &Pattern,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    let (binder_name, b_inner) = binder_scope(b_side, binder_label)?;
    let Pattern::Term(PatternTerm::Apply { constructor: c_ctor, args: c_args }) = c_side else {
        return None;
    };
    // The floated-across constructor must not be the binder itself (a binder-over-binder equation
    // is family (i)'s commutation, never a float-across).
    if c_ctor == binder_label {
        return None;
    }
    let Pattern::Term(PatternTerm::Apply {
        constructor: b_inner_ctor,
        args: b_inner_args,
    }) = b_inner
    else {
        return None;
    };
    if b_inner_ctor != c_ctor {
        return None;
    }
    match (c_args.as_slice(), b_inner_args.as_slice()) {
        // COLLECTION form (`ScopeExtrusion`): both sides one collection literal.
        (
            [Pattern::Collection { elements: c_elements, rest: c_rest, .. }],
            [Pattern::Collection { elements: b_elements, rest: b_rest, .. }],
        ) => float_across_collection(
            def,
            c_ctor,
            c_elements,
            c_rest.as_ref(),
            b_elements,
            b_rest.as_ref(),
            &binder_name,
            binder_label,
            premises,
        ),
        // PREFIX form (`InNew` family + `AmbNew`): plain argument lists.
        _ => float_across_prefix(
            def,
            c_ctor,
            c_args,
            b_inner_args,
            &binder_name,
            binder_label,
            premises,
        ),
    }
}

/// The PREFIX float form: exactly one `C` argument is `B(^x. Var(P))` (the same binder and body
/// variable reappearing on the `b_side` at the same position), every other argument a bare
/// variable equal on both sides; freshness declared on every other argument; `C` in the handler's
/// prefix shape with the binder at the single plain primary-category field (AM-6e). Returns the
/// `^float-hoist:{C}` satellite classification on recognition.
#[allow(clippy::too_many_arguments)]
fn float_across_prefix(
    def: &LanguageDef,
    c_ctor: &Ident,
    c_args: &[Pattern],
    b_args: &[Pattern],
    binder_name: &str,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    if c_args.len() != b_args.len() {
        return None;
    }
    let mut float_position: Option<(usize, String)> = None;
    let mut floated_past: Vec<String> = Vec::with_capacity(c_args.len().saturating_sub(1));
    for (index, (c_arg, b_arg)) in c_args.iter().zip(b_args).enumerate() {
        if let Some((scope_binder, scope_body)) = binder_scope(c_arg, binder_label) {
            // The floated position: same binder as the b_side scope, bare-variable body, and the
            // b_side carries exactly that body variable here.
            if scope_binder != binder_name {
                return None;
            }
            let Pattern::Term(PatternTerm::Var(body_var)) = scope_body else {
                return None;
            };
            let Pattern::Term(PatternTerm::Var(b_var)) = b_arg else {
                return None;
            };
            if b_var != body_var {
                return None;
            }
            if float_position
                .replace((index, body_var.to_string()))
                .is_some()
            {
                // Two binder-scoped arguments — not the single-float shape.
                return None;
            }
        } else {
            let (Pattern::Term(PatternTerm::Var(c_var)), Pattern::Term(PatternTerm::Var(b_var))) =
                (c_arg, b_arg)
            else {
                return None;
            };
            if c_var != b_var {
                return None;
            }
            floated_past.push(c_var.to_string());
        }
    }
    let (float_index, body_var) = float_position?;
    if !float_metavariables_distinct(binder_name, &body_var, &floated_past) {
        return None;
    }
    // AM-6e: `C` must be the handler's prefix shape — exactly one plain primary-category field —
    // and the equation's binder argument must sit AT that field.
    let shape_matches = match float_constructor_shape(def, c_ctor) {
        FloatConstructorShape::Prefix { primary_field_index, field_count } => {
            field_count == c_args.len() && primary_field_index == float_index
        },
        _ => return None,
    };
    (shape_matches
        && premises_are_exactly_float_freshness(premises, binder_name, &floated_past, None))
    .then(|| FloatAcrossClassification::Prefix {
        constructor: c_ctor.to_string(),
        float_index,
        arity: c_args.len(),
    })
}

/// The COLLECTION float form (`ScopeExtrusion`): exactly one collection element is `B(^x. Var(P))`
/// (reappearing as `Var(P)` at the same position on the `b_side`), every other element a bare
/// variable equal on both sides, the same `...rest` on both sides; freshness declared on every
/// other element and on the rest; `C` the primary-category collection constructor (AM-6e).
/// Returns the `^float-merge:{op}` satellite classification on recognition.
#[allow(clippy::too_many_arguments)]
fn float_across_collection(
    def: &LanguageDef,
    c_ctor: &Ident,
    c_elements: &[Pattern],
    c_rest: Option<&Ident>,
    b_elements: &[Pattern],
    b_rest: Option<&Ident>,
    binder_name: &str,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    if c_elements.len() != b_elements.len() {
        return None;
    }
    if c_rest != b_rest {
        return None;
    }
    let mut float_position: Option<(usize, String)> = None;
    let mut floated_past: Vec<String> = Vec::with_capacity(c_elements.len().saturating_sub(1));
    for (index, (c_element, b_element)) in c_elements.iter().zip(b_elements).enumerate() {
        if let Some((scope_binder, scope_body)) = binder_scope(c_element, binder_label) {
            if scope_binder != binder_name {
                return None;
            }
            let Pattern::Term(PatternTerm::Var(body_var)) = scope_body else {
                return None;
            };
            let Pattern::Term(PatternTerm::Var(b_var)) = b_element else {
                return None;
            };
            if b_var != body_var {
                return None;
            }
            if float_position
                .replace((index, body_var.to_string()))
                .is_some()
            {
                return None;
            }
        } else {
            let (Pattern::Term(PatternTerm::Var(c_var)), Pattern::Term(PatternTerm::Var(b_var))) =
                (c_element, b_element)
            else {
                return None;
            };
            if c_var != b_var {
                return None;
            }
            floated_past.push(c_var.to_string());
        }
    }
    let (_, body_var) = float_position?;
    if !float_metavariables_distinct(binder_name, &body_var, &floated_past) {
        return None;
    }
    // AM-6e: `C` must be the handler's bag-extrusion shape — the primary-category collection
    // constructor (the bag arm extrudes a binder MEMBER against the whole residual).
    (matches!(
        float_constructor_shape(def, c_ctor),
        FloatConstructorShape::CollectionOverPrimary
    ) && premises_are_exactly_float_freshness(
        premises,
        binder_name,
        &floated_past,
        c_rest.map(|rest| rest.to_string()).as_deref(),
    ))
    .then(|| FloatAcrossClassification::Collection { op: c_ctor.to_string() })
}

/// The float's metavariables must be pairwise distinct — the binder, the body variable, and every
/// floated-past field variable. A shared name (e.g. the body variable doubling as a sibling field)
/// would make the equation assert more than the handler's float performs — fail closed.
fn float_metavariables_distinct(
    binder_name: &str,
    body_var: &str,
    floated_past: &[String],
) -> bool {
    let mut seen: HashSet<&str> = HashSet::with_capacity(floated_past.len() + 2);
    seen.insert(binder_name);
    if !seen.insert(body_var) {
        return false;
    }
    floated_past.iter().all(|name| seen.insert(name.as_str()))
}

/// The freshness premises are EXACTLY the float's capture-avoidance conditions: every premise is
/// `binder # target` with `target` a floated-past field (`Var`) or the floated-past collection
/// rest (`...rest`), AND every floated-past field/rest is covered by such a premise. Any other
/// premise kind, a premise over a different variable, or a MISSING freshness condition rejects.
fn premises_are_exactly_float_freshness(
    premises: &[Premise],
    binder_name: &str,
    floated_past: &[String],
    floated_past_rest: Option<&str>,
) -> bool {
    for premise in premises {
        let Premise::Freshness(FreshnessCondition { var, term }) = premise else {
            return false;
        };
        if var != binder_name {
            return false;
        }
        let recognized = match term {
            FreshnessTarget::Var(target) => floated_past.iter().any(|name| target == name),
            FreshnessTarget::CollectionRest(target) => {
                floated_past_rest.is_some_and(|rest| target == rest)
            },
        };
        if !recognized {
            return false;
        }
    }
    let var_covered = |name: &String| {
        premises.iter().any(|premise| {
            matches!(
                premise,
                Premise::Freshness(FreshnessCondition { var, term: FreshnessTarget::Var(target) })
                    if var == binder_name && target == name
            )
        })
    };
    let rest_covered = |name: &str| {
        premises.iter().any(|premise| {
            matches!(
                premise,
                Premise::Freshness(FreshnessCondition {
                    var,
                    term: FreshnessTarget::CollectionRest(target),
                }) if var == binder_name && target == name
            )
        })
    };
    floated_past.iter().all(var_covered) && floated_past_rest.is_none_or(rest_covered)
}

/// How the generated float handler treats a constructor `C` (AM-6e) — derived from the SAME shape
/// logic `binder_congruence.rs`'s arms use, restated over the AST on this side of the crate
/// boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FloatConstructorShape {
    /// The prefix arm's shape: a regular constructor with EXACTLY ONE plain (non-collection,
    /// non-optional) primary-category field, at `primary_field_index` of `field_count` fields.
    Prefix {
        primary_field_index: usize,
        field_count: usize,
    },
    /// The bag-extrusion arm's shape: the collection constructor over the primary category.
    CollectionOverPrimary,
    /// Every other shape falls to the handler's no-recursion catch-all — never floated.
    Other,
}

/// One restated constructor field — the (category, is_collection, is_optional) triple the
/// handler's prefix-arm filter reads (`f.category == proc_cat && !f.is_collection &&
/// !f.is_optional`), mirrored from the macros-side `FieldInfo` derivation.
#[derive(Debug, PartialEq, Eq)]
struct RestatedField {
    category: String,
    is_collection: bool,
    is_optional: bool,
}

/// Classify constructor `label` by the float handler's arm shapes ([`FloatConstructorShape`]).
fn float_constructor_shape(def: &LanguageDef, label: &Ident) -> FloatConstructorShape {
    let Some(primary) = def
        .types
        .first()
        .map(|lang_type| lang_type.name.to_string())
    else {
        return FloatConstructorShape::Other;
    };
    let Some(rule) = def.get_constructor(label) else {
        return FloatConstructorShape::Other;
    };
    // The handler emits arms for primary-category variants only.
    if rule.category != primary {
        return FloatConstructorShape::Other;
    }
    // A binder rule (either declaration route) is the binder arm, never a float-across target.
    if single_binder_body_category(rule).is_some() {
        return FloatConstructorShape::Other;
    }
    let fields: Vec<RestatedField> = if let Some(term_context) = &rule.term_context {
        // A MULTI-binder rule is not a float-across target either.
        if term_context
            .iter()
            .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
        {
            return FloatConstructorShape::Other;
        }
        let mut fields = Vec::with_capacity(term_context.len());
        restated_fields_from_params(term_context, false, &mut fields);
        fields
    } else {
        if !rule.bindings.is_empty() {
            return FloatConstructorShape::Other;
        }
        restated_fields_from_items(&rule.items)
    };
    // The collection classification (`variant_kind_from_term_context` / `variant_kind_from_items`):
    // exactly one field and it is a collection.
    if let [field] = fields.as_slice() {
        if field.is_collection {
            return if field.category == primary {
                FloatConstructorShape::CollectionOverPrimary
            } else {
                FloatConstructorShape::Other
            };
        }
    }
    // The prefix arm's filter: exactly one plain primary-category field.
    let primary_positions: Vec<usize> = fields
        .iter()
        .enumerate()
        .filter(|(_, field)| {
            field.category == primary && !field.is_collection && !field.is_optional
        })
        .map(|(index, _)| index)
        .collect();
    match primary_positions.as_slice() {
        [position] => FloatConstructorShape::Prefix {
            primary_field_index: *position,
            field_count: fields.len(),
        },
        _ => FloatConstructorShape::Other,
    }
}

/// Restate a `term_context` parameter list as constructor fields — the mirror of the macros-side
/// `field_infos_from_term_param` (abstractions contribute no field outside an `Optional` group;
/// `Optional` groups flatten with `is_optional` set; a guard slot is a non-primary marker field).
fn restated_fields_from_params(
    params: &[TermParam],
    in_optional: bool,
    out: &mut Vec<RestatedField>,
) {
    let mut work: Vec<_> = params
        .iter()
        .rev()
        .map(|param| (param, in_optional))
        .collect();
    while let Some((param, in_optional)) = work.pop() {
        match param {
            TermParam::Simple { ty, .. } => out.push(restated_field_from_type(ty, in_optional)),
            // The macros-side `field_info_for_guard_slot` marker category, byte-exact.
            TermParam::GuardBody { .. } => out.push(RestatedField {
                category: "Guard".to_string(),
                is_collection: false,
                is_optional: in_optional,
            }),
            TermParam::Optional { params: inner } => {
                work.extend(inner.iter().rev().map(|param| (param, true)));
            },
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. }
                if in_optional =>
            {
                let category = match ty {
                    TypeExpr::Arrow { codomain, .. } => {
                        base_category_name(codomain).unwrap_or_else(|| "__unknown".to_string())
                    },
                    _ => "__unknown".to_string(),
                };
                out.push(RestatedField {
                    category,
                    is_collection: false,
                    is_optional: true,
                });
            },
            TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

#[cfg(test)]
#[path = "../tests/support/rho_net_metadata_recursive_oracle.rs"]
mod metadata_recursive_oracle;

/// Restate a grammar-item list as constructor fields — the mirror of the macros-side
/// `variant_kind_from_items` field derivation (non-`Var` non-terminals and collections contribute
/// fields; terminals, `Var` non-terminals, and binder items do not).
fn restated_fields_from_items(items: &[GrammarItem]) -> Vec<RestatedField> {
    items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal { ident, kind } if *kind != NonTerminalKind::Var => {
                Some(RestatedField {
                    category: ident.to_string(),
                    is_collection: false,
                    is_optional: false,
                })
            },
            GrammarItem::Collection { element_type, .. } => Some(RestatedField {
                category: element_type.to_string(),
                is_collection: true,
                is_optional: false,
            }),
            _ => None,
        })
        .collect()
}

/// Restate one `TypeExpr` as a constructor field — the mirror of the macros-side
/// `field_info_from_type_expr` (base category; collections and maps as collection fields).
fn restated_field_from_type(ty: &TypeExpr, is_optional: bool) -> RestatedField {
    match ty {
        TypeExpr::Base(ident) => RestatedField {
            category: ident.to_string(),
            is_collection: false,
            is_optional,
        },
        TypeExpr::Collection { element, .. } => RestatedField {
            category: base_category_name(element).unwrap_or_else(|| "__unknown".to_string()),
            is_collection: true,
            is_optional,
        },
        TypeExpr::Map { value, .. } => RestatedField {
            category: base_category_name(value).unwrap_or_else(|| "__unknown".to_string()),
            is_collection: true,
            is_optional,
        },
        _ => RestatedField {
            category: "__unknown".to_string(),
            is_collection: false,
            is_optional,
        },
    }
}

/// One DEPTH-2 nested structural-AC-rewrite σ-injection site derived from a `LanguageDef` (the
/// Ambient `InRule`/`OutRule`): the rule's bare label, its σ-receiver SOURCE channel, the HashBag
/// operand constructor `op`, the OPERAND reconstruction template (the whole nested operand, rebuilt
/// from σ and reflected as `⟦operand⟧`), and the `m` REDUCT element templates (each a NESTED
/// restructuring rebuilt from σ and delivered as a host-σ-sourced value). Only rewrites that lowered
/// to a [`RhoNetLoweredRule::NestedStructuralAcRewrite`] are surfaced, so a site is always executable.
///
/// The nested analogue of [`RhoNetStructuralAcInjectionSite`]: where the flat site recovers each
/// reduct element DIRECTLY from a σ variable, the nested site reconstructs the operand AND each reduct
/// by walking a [`AcReconstructTemplate`] with σ ([`instantiate_ac_reconstruct_template`]), because
/// the operand element AND the reduct nest a bag the flat `GroundTerm::new` builder cannot express.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetNestedStructuralAcInjectionSite {
    /// The bare source rewrite label (the receiver rule's label, e.g. `InRule`).
    pub rule_label: String,
    /// The σ-receiver SOURCE channel — the SAME channel the receiver rests on (accept triad by
    /// symmetric derivation).
    pub channel: String,
    /// The HashBag operand constructor (`op` in `op{…}`, e.g. `PPar`).
    pub op: String,
    /// The shared cross-level NON-LINEAR channel variable (`M`) — for diagnostics / test assertions.
    pub nonlinear_var: String,
    /// The outer bag's spliced remainder variable (`s`) — for diagnostics / test assertions.
    pub rest_var: String,
    /// The OPERAND reconstruction template (the LHS root) — walked with σ to rebuild the whole nested
    /// operand `⟦operand⟧` the receiver's nested pattern matches.
    pub operand_template: AcReconstructTemplate,
    /// The `m` REDUCT element templates (RHS order) — each walked with σ to rebuild a host-σ-sourced
    /// nested reduct `⟦r_j⟧`.
    pub reduct_templates: Vec<AcReconstructTemplate>,
}

/// Derive every DEPTH-2 nested structural-AC-rewrite σ-injection site for a language — the sites the
/// nested structural-AC σ-injection targets. Builds the same [`RhoNetProgram`] + [`RhoNetLowered`]
/// the receivers compile from, keeps only the rewrites that un-skipped to a
/// [`RhoNetLoweredRule::NestedStructuralAcRewrite`] receiver, and reports each one's bare rule label,
/// source channel, and nested structural-AC templates (extracted through the SAME
/// [`nested_structural_ac_rule_shape`] the receiver materialized from). The nested analogue of
/// [`rho_net_structural_ac_injection_sites`].
pub fn rho_net_nested_structural_ac_injection_sites(
    def: &LanguageDef,
) -> Vec<RhoNetNestedStructuralAcInjectionSite> {
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
        let RhoNetLoweredRule::NestedStructuralAcRewrite { rule_id, .. } = lowered_rule else {
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
        // A `NestedStructuralAcRewrite` lowered iff `nested_structural_ac_rule_shape` succeeded, so
        // this cannot fail; a defensive `continue` keeps the derivation total.
        let Some(shape) = nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, def)
        else {
            continue;
        };
        // The operand reconstruction template is the LHS root walked with σ.
        let Some(operand_template) = AcReconstructTemplate::from_pattern(&rewrite.left, def) else {
            continue;
        };
        sites.push(RhoNetNestedStructuralAcInjectionSite {
            rule_label: rule_label.to_string(),
            channel: channel.clone(),
            op: shape.op,
            nonlinear_var: shape.nonlinear_var.to_string(),
            rest_var: shape.spliced_rest.to_string(),
            operand_template,
            reduct_templates: shape.reduct_templates,
        });
    }
    sites
}

// ─── Stage 4 (Ambient In/Out): the DEPTH-2 NESTED structural-AC SPREAD MATCH (in-Rho locate+reduct) ─
//
// The SPREAD analogue of the report-path `nested_structural_ac_receiver_par` — the DEPTH-2
// generalization of the flat `structural_ac_match_receiver_par` (OpenRule). Where the report path
// (`structural_ac_contract_call` → `nested_structural_ac_receiver_par`) HOST-locates the redex,
// HOST-reflects the operand bag, and HOST-builds the nested reduct `⟦R⟧σ`, delivering the reduct(s)
// as separately-delivered message slots, the SPREAD path:
//
//   * LOCATES the operand IN RHO by a structural walk of the reflected subject
//     ([`nested_structural_ac_match_call_par`]), re-sourcing the operand bag from the SUBJECT (not
//     the host-σ report) — the corrupted-σ probe proof;
//   * BINDS every σ slot the reduct needs (`na`, `A`, `nb`, `B`, the inner `rest1`, the outer
//     `rest2`, and the cross-level `M` guard slots) FROM the operand bag's connective pattern
//     ([`nested_match_bind_pattern_for`], the binding twin of the report-path
//     `nested_match_pattern_for`, which WILDCARDS those positions); and
//   * BUILDS the nested reduct `⟦nb[{ na[{A}] | B }]⟧` (or Out's `⟦{ na[{A} ] | nb[B] }⟧`) IN THE
//     RECEIVER BODY from the bag-bound σ slots ([`reflect_ac_template_bound_par`], the bound-var twin
//     of `reflect_ground_term_par` — reusing the reflection PDA's HashBag idiom so a NESTED AC bag
//     rebuilds via the `ac:` carrier + a σ-slot rest), NOT host-delivered as a message slot.
//
// So its message is the 2-value `carrier!(⟦operand⟧, @out)` the spread delivers (NO host σ), exactly
// like the flat [`structural_ac_match_receiver_par`]; the reducer still matches the DEPTH-2 nested
// pattern + the cross-level `EEq(M_outer, M_inner)` guard in ONE atomic `consume` (a HashBag argument
// reflects to the same order-independent process-soup carrier as the top bag — feasibility already
// proven by the report-path receiver).

/// One in-Rho MATCHING entry for a DEPTH-2 NESTED structural non-linear AC family rewrite
/// (`RhoNetLoweredRule::NestedStructuralAcRewrite`, the Ambient `InRule`/`OutRule`): the data the
/// in-Rho matcher needs to ADMIT the nested-structural-AC redex and co-install a per-site MATCH
/// receiver that re-sources BOTH the operand AND the nested reducts from the SPREAD of the reflected
/// subject (never the host-σ report).
///
/// The DEPTH-2 twin of [`RhoNetStructuralAcMatchEntry`]: where a flat structural-AC element is a
/// constructor over BARE variables (its reduct args bound directly), a nested element's argument is
/// itself a HashBag, and the reduct is a NESTED restructuring (never a bare LHS var). The report-path
/// [`nested_structural_ac_receiver_par`] takes those reducts as separately DELIVERED σ slots; the
/// MATCH receiver ([`nested_structural_ac_match_receiver_par`]) instead BINDS every σ slot from the
/// operand's connective pattern and REBUILDS the nested reduct in its body — so, exactly like the flat
/// [`structural_ac_match_call_par`], its message is the 2-value `carrier!(⟦operand⟧, @out)` the spread
/// delivers, with NO host σ. Like every AC redex, a nested-structural-AC redex is NOT an automaton
/// entry (its `AcApp` bag has no positional image), so it carries no `accept_channels` entry and no
/// `PatternId`; the match driver LOCATES it by a separate walk ([`nested_structural_ac_match_install_at`])
/// that keys on the LHS root pattern's TOP constructor (a bag op for `InRule`, a wrapper for `OutRule`).
#[derive(Debug, Clone)]
pub struct RhoNetNestedStructuralAcMatchEntry {
    /// The Dovetail firing label the nested-structural-AC firing carries (the bare rewrite label,
    /// e.g. `InRule`) — what the report keys the firing on and the in-Rho gate admits.
    pub fired_rule_label: String,
    /// The recognized nested-structural-AC shape (`op`, the LHS root pattern, the cross-level
    /// non-linear channel var, the spliced outer rest, and the `m` NESTED reduct templates) — the
    /// per-site MATCH receiver is materialized from it. Crate-private: only
    /// [`nested_structural_ac_match_call_par`] (same crate) reads it. (No `PartialEq`/`Eq`:
    /// [`NestedStructuralAcShape`] stores an AST [`Pattern`], which is not `PartialEq`.)
    pub(crate) shape: NestedStructuralAcShape,
}

impl RhoNetNestedStructuralAcMatchEntry {
    /// The HashBag operand constructor `op` (`PPar` for both `InRule`/`OutRule`) — the AC element
    /// channel of the operand/reduct soup.
    pub fn op(&self) -> &str {
        &self.shape.op
    }

    /// The LHS root pattern's TOP constructor — the located subject node's constructor the match
    /// driver keys the co-install on (`PPar` for the bag-rooted `InRule`; `PAmb` for the
    /// wrapper-rooted `OutRule`).
    pub fn root_constructor(&self) -> Option<String> {
        nested_root_constructor(&self.shape.root_pattern)
    }
}

/// The LHS root pattern's TOP constructor of a nested structural-AC shape — a bag op `PPar`
/// (bag-rooted `InRule`) or a wrapper constructor `PAmb` (wrapper-rooted `OutRule`). `None` for a
/// non-`Apply` root (never a recognized nested shape).
fn nested_root_constructor(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Term(PatternTerm::Apply { constructor, .. }) => Some(constructor.to_string()),
        _ => None,
    }
}

/// Whether a nested-structural-AC `shape` is faithfully representable as an in-Rho MATCH receiver
/// ([`nested_structural_ac_match_receiver_par`]): every REDUCT-referenced var that is NOT the
/// cross-level channel var must occur EXACTLY ONCE across the LHS (so the connective pattern binds it
/// at a single unambiguous position — a Rholang pattern free variable may occur at most once). The
/// nested twin of [`structural_ac_shape_is_match_representable`]. The recognizer
/// ([`nested_structural_ac_rule_shape`]) already guarantees only `M` has count 2 and every reduct var
/// is an LHS var, so this passes for every recognized In/Out shape; it is the defensive fail-closed
/// gate that keeps a degenerate future shape (a repeated non-channel reduct arg) on the host-σ replay
/// path rather than a wrong in-Rho pattern.
pub(crate) fn nested_structural_ac_shape_is_match_representable(
    shape: &NestedStructuralAcShape,
) -> bool {
    let nonlinear = shape.nonlinear_var.to_string();
    let mut referenced: HashSet<String> = HashSet::new();
    for template in &shape.reduct_templates {
        template.collect_vars(&mut referenced);
    }
    referenced.insert(shape.spliced_rest.to_string());

    let mut var_counts: HashMap<String, usize> = HashMap::new();
    collect_pattern_var_counts(&shape.root_pattern, &mut var_counts);

    referenced
        .iter()
        .filter(|name| **name != nonlinear)
        .all(|name| match var_counts.get(name) {
            // A `Var` leaf: it must occur exactly once (else two pattern free vars would collide).
            Some(&count) => count == 1,
            // A `...rest` remainder (not a `Var` node): structurally unique — appears once as its
            // bag's with-rest marker.
            None => true,
        })
}

/// The mutable slot-allocation state threaded through the SPREAD nested-AC operand pattern walk
/// ([`nested_match_bind_pattern_for`]): the next unused receive-frame free level, the map from a
/// bound σ var/rest NAME to its assigned level, and the cross-level `M`'s occurrence levels (for the
/// `EEq` guard).
/// `pub(crate)` (fields included): the A-S5.5 driver AC-CARRIER receivers
/// (`crate::rho_net_drive::ac_carrier_receiver_par`) run the same bind walk to lay out
/// their σ-slot frame, so the carrier's slot map can never drift from the site-keyed
/// receivers'.
pub(crate) struct NestedBindState {
    pub(crate) next_level: usize,
    pub(crate) slot_of: HashMap<String, usize>,
    pub(crate) occurrence_levels: Vec<usize>,
}

struct BindingNestedMatchPolicy<'a> {
    nonlinear_var: &'a Ident,
    referenced: &'a HashSet<String>,
    state: &'a mut NestedBindState,
}

impl NestedMatchPatternPolicy for BindingNestedMatchPolicy<'_> {
    fn variable(&mut self, variable: &Ident) -> Par {
        let name = variable.to_string();
        if variable == self.nonlinear_var {
            let slot = self.state.next_level;
            self.state.next_level += 1;
            self.state.occurrence_levels.push(slot);
            self.state.slot_of.entry(name).or_insert(slot);
            new_freevar_par(slot as i32, Vec::new())
        } else if self.referenced.contains(&name) {
            let slot = self.state.next_level;
            self.state.next_level += 1;
            self.state.slot_of.entry(name).or_insert(slot);
            new_freevar_par(slot as i32, Vec::new())
        } else {
            new_wildcard_par(Vec::new(), true)
        }
    }

    fn remainder(&mut self, remainder: Option<&Ident>) -> Par {
        match remainder {
            Some(remainder) => {
                let name = remainder.to_string();
                if self.referenced.contains(&name) {
                    let slot = self.state.next_level;
                    self.state.next_level += 1;
                    self.state.slot_of.entry(name).or_insert(slot);
                    new_freevar_par(slot as i32, Vec::new())
                } else {
                    new_wildcard_par(Vec::new(), true)
                }
            },
            None => Par::default(),
        }
    }
}

/// Build the SPREAD nested-AC receiver's match PATTERN by walking the LHS root pattern, BINDING every
/// σ slot the reduct needs (unlike the report-path [`nested_match_pattern_for`], which wildcards
/// every non-`M`, non-spliced-rest position because the report delivers the reduct host-side): each
/// occurrence of the cross-level channel `M` binds a distinct GUARD slot (recorded in
/// `state.occurrence_levels`, its FIRST occurrence the reduct's `M` slot); each other
/// reduct-referenced var binds one slot; each reduct-referenced bag `...rest` (the inner `rest1`
/// AND the outer spliced `rest2`) binds the soup remainder to a slot; every OTHER position is a
/// wildcard `_` (a dropped argument). A constructor over a single HashBag lowers to the
/// order-independent process-soup `remainder | @"ac:op"!(⟦e⟧) | …` (byte-identical to
/// [`reflect_ac_bag_par`], so the reflected operand matches); every other constructor to the tagged
/// `EList[ GPrivate(tag), … ]` (byte-identical to [`reflect_ground_term_par`]). `referenced` is the
/// set of var/rest NAMES the reducts (plus the spliced outer rest) reference — only those are bound;
/// the rest ride nothing and stay wildcards.
///
/// `pub(crate)`: shared with the A-S5.5 driver AC-carrier receivers
/// (`crate::rho_net_drive`) — see [`NestedBindState`].
pub(crate) fn nested_match_bind_pattern_for(
    pattern: &Pattern,
    nonlinear_var: &Ident,
    referenced: &HashSet<String>,
    state: &mut NestedBindState,
    language_fingerprint: &str,
) -> Par {
    build_nested_match_pattern(
        pattern,
        &mut BindingNestedMatchPolicy { nonlinear_var, referenced, state },
        language_fingerprint,
    )
}

/// Reflect a nested-AC reduct [`AcReconstructTemplate`] to a receiver-BODY `Par` whose leaves are the
/// operand-pattern's BAG-BOUND σ slots (a `BoundVar` at `free_count - 1 - level`) — the bound-var
/// twin of [`reflect_ground_term_par`]. A `Var` (or a `Bag`'s `...rest`) reflects to its bound σ
/// slot; a `Node` to the tagged `EList[ GPrivate(tag), ⟦child⟧… ]` (byte-identical to
/// `reflect_ground_term_par`'s constructor image); a `Bag` to the process-soup `@"ac:op"!(⟦e⟧) | … |
/// BoundVar(rest)` (byte-identical to [`reflect_ac_bag_par`] / the [`reflect_term_par_env`]
/// HashBag case, so a
/// NESTED AC bag rebuilds through the `ac:` carrier with its residual bag spliced via the bound `rest`
/// slot). This is how the SPREAD receiver BUILDS `⟦R⟧σ` in its body from the in-Rho-bound σ — never a
/// host-delivered message slot. `slot_of` MUST bind every var/rest the template references (the walk
/// [`nested_match_bind_pattern_for`] ensures this), so the `expect`s are unreachable past the
/// representability gate.
fn reflect_ac_template_bound_par(
    template: &AcReconstructTemplate,
    slot_of: &HashMap<String, usize>,
    free_count: usize,
    language_fingerprint: &str,
) -> Par {
    enum Task<'template> {
        Visit(&'template AcReconstructTemplate),
        AssembleNode {
            constructor: &'template str,
            child_count: usize,
        },
        AssembleBag {
            op: &'template str,
            rest: Option<&'template str>,
            element_count: usize,
        },
    }

    let bound_slot = |name: &str| {
        let level = *slot_of
            .get(name)
            .expect("a nested-AC reduct var is bound by the operand pattern");
        let bv_index = free_count - 1 - level;
        new_boundvar_par(bv_index as i32, create_bit_vector(&[bv_index]), false)
    };

    let mut tasks = vec![Task::Visit(template)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(AcReconstructTemplate::Var(name)) => values.push(bound_slot(name)),
            Task::Visit(AcReconstructTemplate::Node { constructor, children }) => {
                tasks.push(Task::AssembleNode { constructor, child_count: children.len() });
                tasks.extend(children.iter().rev().map(Task::Visit));
            },
            Task::Visit(AcReconstructTemplate::Bag { op, elements, rest }) => {
                tasks.push(Task::AssembleBag {
                    op,
                    rest: rest.as_deref(),
                    element_count: elements.len(),
                });
                tasks.extend(elements.iter().rev().map(Task::Visit));
            },
            // A-S5.8 (F8-AM-1b): UNREACHABLE BY CONSTRUCTION — a binder-templated rule never
            // builds a site-keyed match receiver (its σ-slot shift rule needs the ASYNC
            // `^shift`, which a value-position rebuild cannot inline): `lower_base_rewrite`
            // routes such a rule to the fail-closed NO-MATCH-ENTRY disposition
            // (`NestedStructuralAcBinderTemplated`) and `nested_structural_ac_rule_receiver`
            // declines it, so this builder is only ever called on binder-free templates. The
            // assertion is the codegen-time guard that keeps it that way (the C2-assertion
            // discipline).
            Task::Visit(AcReconstructTemplate::Binder { .. }) => unreachable!(
                "reflect_ac_template_bound_par reached a Binder template — binder-templated \
                 nested-AC rules take the NO-MATCH-ENTRY disposition (A-S5.8 F8-AM-1b) and \
                 never build a site-keyed match receiver"
            ),
            Task::AssembleNode { constructor, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .expect("nested-AC reflection PDA lost a node child result");
                let children = values.split_off(first);
                let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
                    language_fingerprint,
                    constructor,
                ));
                let mut items = Vec::with_capacity(children.len() + 1);
                let mut locally_free = tag.locally_free.clone();
                items.push(tag);
                for child in children {
                    locally_free = union(locally_free, child.locally_free.clone());
                    items.push(child);
                }
                values.push(new_elist_par(
                    items,
                    locally_free.clone(),
                    false,
                    None,
                    locally_free,
                    false,
                ));
            },
            Task::AssembleBag { op, rest, element_count } => {
                let first = values
                    .len()
                    .checked_sub(element_count)
                    .expect("nested-AC reflection PDA lost a bag element result");
                let elements = values.split_off(first);
                let element_channel = ac_soup_channel(language_fingerprint, op);
                let mut components =
                    Vec::with_capacity(elements.len() + usize::from(rest.is_some()));
                for element in elements {
                    let free = element.locally_free.clone();
                    components.push(new_send_par(
                        new_gstring_par(element_channel.clone(), Vec::new(), false),
                        vec![element],
                        false,
                        free.clone(),
                        false,
                        free,
                        false,
                    ));
                }
                // The residual `...rest`: the operand pattern bound it to the leftover bag soup,
                // so parallel composition SPLICES the residual sends into the flat reduct bag.
                if let Some(rest_name) = rest {
                    components.push(bound_slot(rest_name));
                }
                values.push(crate::rho_net_subst_trs::parallel_par(components));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("nested-AC reflection PDA produced no result")
}

/// Build the SPREAD DEPTH-2 nested structural-AC MATCH receiver for a [`NestedStructuralAcShape`]: a
/// persistent
///
/// ```text
/// for( < ⟦nested operand pattern⟧ >, out <- source )
///   where ( M_a == M_b )
///   { out!( @"ac:op"!(⟦r0⟧) | … | @"ac:op"!(⟦r_{m-1}⟧) | spliced_rest ) }
/// ```
///
/// The 2-value spread message `carrier!(⟦operand⟧, @out)` (NO host σ) — the DEPTH-2 generalization of
/// the flat [`structural_ac_match_receiver_par`]. The connective operand pattern (element 0,
/// [`nested_match_bind_pattern_for`]) matches the reflected operand ORDER-INDEPENDENTLY at every depth
/// (native `spatial_matcher_pda::ListMachine`, with `sub_pars` per level), BINDING every σ slot the
/// reducts need — the
/// two cross-level `M` occurrences (the guard slots), the outer spliced rest, the inner bag rest, and
/// each reduct var — and wildcarding the rest. The `condition` fires the COMM only when the two `M`
/// slots are name-equal ([`nonlinear_consistency_condition`], DEPTH-AGNOSTIC — it indexes the flat
/// receive frame); the body BUILDS each nested reduct `⟦r_j⟧` from the bag-bound σ slots
/// ([`reflect_ac_template_bound_par`]) and splices the outer remainder. Unlike the report-path
/// [`nested_structural_ac_receiver_par`] (which takes the `m` reducts as separately-delivered host-σ
/// slots and wildcards the reduct positions), this binds + rebuilds EVERYTHING from the operand, so
/// the reduct comes from the SPREAD, not the report.
fn nested_structural_ac_match_receiver_par(
    shape: &NestedStructuralAcShape,
    source: Par,
    language_fingerprint: &str,
) -> Par {
    let element_channel = ac_soup_channel(language_fingerprint, &shape.op);

    // The var/rest NAMES the RHS reducts reference, PLUS the outer spliced rest — the operand pattern
    // must BIND each (the report-path pattern wildcards them, taking them host-side), so the body can
    // rebuild the nested reduct + splice the outer remainder from the bag-bound slots.
    let mut referenced: HashSet<String> = HashSet::new();
    for template in &shape.reduct_templates {
        template.collect_vars(&mut referenced);
    }
    referenced.insert(shape.spliced_rest.to_string());

    // Walk the LHS root pattern, binding every referenced var/rest (guard slots for the cross-level
    // `M`, a slot for each other referenced var/rest) and wildcarding the rest.
    let mut state = NestedBindState {
        next_level: 0,
        slot_of: HashMap::new(),
        occurrence_levels: Vec::new(),
    };
    let bag_pattern = nested_match_bind_pattern_for(
        &shape.root_pattern,
        &shape.nonlinear_var,
        &referenced,
        &mut state,
        language_fingerprint,
    );

    let out_level = state.next_level;
    let free_count = out_level + 1;
    let slot_of = state.slot_of;

    // The cross-level non-linear consistency guard `EEq(M_a, M_b)` over the two `M` occurrence slots.
    let condition = nonlinear_consistency_condition(&state.occurrence_levels, free_count);

    // Body: `out!( @"ac:op"!(⟦r0⟧) | … | @"ac:op"!(⟦r_{m-1}⟧) | spliced_rest )` — each nested reduct
    // BUILT from the bag-bound σ slots, then the outer remainder spliced (identical top-level shape
    // to [`nested_structural_ac_receiver_par`], only the reduct is rebuilt in-body not delivered).
    let out_bv_index = free_count - 1 - out_level; // 0
    let mut body_soup: Option<Par> = None;
    for template in &shape.reduct_templates {
        let reduct =
            reflect_ac_template_bound_par(template, &slot_of, free_count, language_fingerprint);
        let free = reduct.locally_free.clone();
        let reduct_send = new_send_par(
            new_gstring_par(element_channel.clone(), Vec::new(), false),
            vec![reduct],
            false,
            free.clone(),
            false,
            free,
            false,
        );
        body_soup = Some(match body_soup {
            None => reduct_send,
            Some(soup) => soup.append(reduct_send),
        });
    }
    // Splice the outer remainder (`spliced_rest`) — bound by the operand pattern — IFF the shape
    // is top-spliced. A TEMPLATE-CONSUMED shape (A-S5.4b, AM-1 — the redeclared Ambient `OutRule`)
    // already spent the bound rest slot inside the rebuilt reduct
    // (`reflect_ac_template_bound_par`'s rest-only `Bag` arm), so the body adds nothing at the top.
    // `m ≥ 1` (a nested structural-AC rewrite has ≥1 RHS element), so `body_soup` is always `Some`.
    let body_soup = if shape.rest_splices_at_top {
        let rest_level = *slot_of
            .get(&shape.spliced_rest.to_string())
            .expect("the spliced outer rest is bound by the operand pattern");
        let rest_bv_index = free_count - 1 - rest_level;
        let rest_bv =
            new_boundvar_par(rest_bv_index as i32, create_bit_vector(&[rest_bv_index]), false);
        match body_soup {
            Some(soup) => soup.append(rest_bv),
            None => rest_bv,
        }
    } else {
        body_soup.expect("a nested structural-AC rewrite carries at least one RHS reduct element")
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

    // Receive-bind patterns: [operand_pattern, FreeVar(out)] — the 2-value spread message
    // `carrier!(⟦operand⟧, @out)`, exactly as the flat structural-AC match receiver.
    let patterns = vec![bag_pattern, new_freevar_par(out_level as i32, Vec::new())];

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

/// Derive every in-Rho MATCHING entry for a language's DEPTH-2 NESTED structural non-linear AC family
/// rewrites (the Ambient `InRule`/`OutRule`) — the nested twin of [`rho_net_structural_ac_match_entries`],
/// routed for the automaton MATCH path (operand + nested reducts re-sourced from the subject spread)
/// rather than the host-σ [`structural_ac_contract_call`] replay path.
///
/// Correlates each installed nested-structural-AC firing site
/// ([`rho_net_nested_structural_ac_injection_sites`] — the rewrites that un-skipped to a
/// [`RhoNetLoweredRule::NestedStructuralAcRewrite`] receiver) back to its source `RewriteRule`,
/// re-extracts its shape through the SAME [`nested_structural_ac_rule_shape`] the receiver
/// materialized from, and keeps only those a MATCH receiver can faithfully bind
/// ([`nested_structural_ac_shape_is_match_representable`]). A non-representable shape is DROPPED here
/// (not surfaced), so it stays deferred and the gate routes its firing to the host-σ replay path —
/// never a wrong in-Rho match.
pub fn rho_net_nested_structural_ac_match_entries(
    def: &LanguageDef,
) -> Vec<RhoNetNestedStructuralAcMatchEntry> {
    let sites = rho_net_nested_structural_ac_injection_sites(def);
    let mut entries = Vec::with_capacity(sites.len());
    for site in &sites {
        // The source rewrite a nested-structural-AC injection site surfaced is always present; a
        // defensive skip keeps the derivation total.
        let Some(rewrite) = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == site.rule_label)
        else {
            continue;
        };
        // A `NestedStructuralAcRewrite` lowered iff `nested_structural_ac_rule_shape` succeeded, so
        // this cannot fail; a defensive skip keeps the derivation total.
        let Some(shape) = nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, def)
        else {
            continue;
        };
        // Fail-closed: a shape the MATCH receiver cannot faithfully bind stays on the host-σ path.
        if !nested_structural_ac_shape_is_match_representable(&shape) {
            continue;
        }
        entries.push(RhoNetNestedStructuralAcMatchEntry {
            fired_rule_label: site.rule_label.clone(),
            shape,
        });
    }
    entries
}

/// Recursively LOCATE + co-install the DEPTH-2 nested structural-AC MATCH receivers for `node` at the
/// position whose `loc:` head-tag channel is `loc_channel` (the SAME location derivation the spread
/// uses). The nested twin of [`structural_ac_match_install_at`], keyed on the LHS root pattern's TOP
/// constructor (`by_root`) rather than a bag op — because a nested rule may be WRAPPER-rooted (the
/// `OutRule`, root `PAmb`) as well as bag-rooted (the `InRule`, root `PPar`). At every node whose
/// constructor is an admitted nested root it derives the site-keyed carrier `ac:⌜ℓ⌝/ctor`
/// ([`ac_carrier_channel`], disjoint per position), co-installs a
/// [`nested_structural_ac_match_receiver_par`] over it, and publishes `carrier!(⟦node⟧, @out)` where
/// `⟦node⟧` is [`reflect_ground_term_par`] over THIS node — a bag-rooted operand delivers its
/// process-soup, a wrapper-rooted operand delivers `EList[tag, ⟦name⟧, soup]`, each matching its
/// receiver's element-0 pattern (both derived from the SAME root pattern). It then DESCENDS into every
/// child (locating a nested redex too, and riding a `^lambda` binder image for free). A co-installed
/// receiver whose full nested pattern + cross-level guard does not match the delivered operand simply
/// never consumes (single-shot, isolated run) — never a false firing.
fn nested_structural_ac_match_install_at(
    locations: &SubjectLocationIndex<'_>,
    start: SubjectPosition,
    root_site: &str,
    by_root: &HashMap<String, &RhoNetNestedStructuralAcMatchEntry>,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    let mut par = Par::default();
    locations.walk(start, |position, node| {
        if let Some(entry) = by_root.get(&node.constructor) {
            let loc_channel = locations.channel("loc", language_fingerprint, root_site, position);
            let carrier = ac_carrier_channel(&loc_channel, &node.constructor);
            let receiver = nested_structural_ac_match_receiver_par(
                &entry.shape,
                new_gstring_par(carrier.clone(), Vec::new(), false),
                language_fingerprint,
            );
            let operand = reflect_ground_term_par(node, language_fingerprint);
            let delivery = new_send_par(
                new_gstring_par(carrier, Vec::new(), false),
                vec![operand, new_gstring_par(out_channel.to_string(), Vec::new(), false)],
                false,
                Vec::new(),
                false,
                Vec::new(),
                false,
            );
            let preceding = std::mem::take(&mut par);
            par = preceding.append(receiver).append(delivery);
        }
        true
    });
    par
}

/// Stage 4 (Ambient In/Out) — walk `subject`, LOCATE every DEPTH-2 NESTED structural non-linear AC
/// redex (an admitted operand whose head is a nested rule's LHS root constructor), and co-install a
/// per-site MATCH receiver over the SPREAD, re-sourcing the operand + nested reducts from the subject
/// (NOT the host-σ report). The DEPTH-2 generalization of the flat [`structural_ac_match_call_par`]:
/// it walks the subject from root nonce `root_site` ([`nested_structural_ac_match_install_at`]) and at
/// every node whose constructor is an admitted nested root — a bag op (`PPar`, the bag-rooted
/// `InRule`) OR a wrapper (`PAmb`, the wrapper-rooted `OutRule`) — co-installs a
/// [`nested_structural_ac_match_receiver_par`] over the site-keyed carrier `ac:⌜ℓ⌝/ctor` and publishes
/// `carrier!(⟦node⟧, @out)`. The reducer then matches the DEPTH-2 nested pattern + the cross-level
/// `EEq(M_outer, M_inner)` guard and BUILDS the nested reduct in the receiver body — all from the
/// spread — in ONE atomic `consume`. Returns the parallel composition of every located node's
/// `(receiver ‖ delivery)` (empty when `subject` has no nested-AC redex). `language_fingerprint` MUST
/// be the ruleset's (the spread's) fingerprint, so the operand's element tags and the receiver's
/// patterns agree.
pub fn nested_structural_ac_match_call_par(
    subject: &GroundTerm,
    entries: &[RhoNetNestedStructuralAcMatchEntry],
    root_site: &str,
    out_channel: &str,
    language_fingerprint: &str,
) -> Par {
    if entries.is_empty() {
        return Par::default();
    }
    // Key each entry by its LHS root-pattern's TOP constructor (`InRule` → the bag op `PPar`;
    // `OutRule` → the wrapper `PAmb`). Mirrors the flat [`structural_ac_match_call_par`]'s `by_op`
    // (one entry per root constructor — the Ambient In/Out roots are distinct).
    let mut by_root: HashMap<String, &RhoNetNestedStructuralAcMatchEntry> =
        HashMap::with_capacity(entries.len());
    for entry in entries {
        if let Some(root_ctor) = nested_root_constructor(&entry.shape.root_pattern) {
            by_root.insert(root_ctor, entry);
        }
    }
    let locations = SubjectLocationIndex::new(subject);
    nested_structural_ac_match_install_at(
        &locations,
        SubjectPosition::ROOT,
        root_site,
        &by_root,
        out_channel,
        language_fingerprint,
    )
}

#[cfg(test)]
mod tests {
    // `super::*` already re-exports the parent module's imports (`Par`,
    // `Pattern`/`PatternTerm`, `LanguageDef`/`Premise`/`RewriteRule`,
    // `scalar_contract_par_for`, `RhoNetProgram`, `rule_id_rewrite`, ...) plus
    // every type defined in this module; only the extras below are new.
    use super::*;
    use crate::lower::lower_language_def;

    /// The INV-S6 scope these unit tests derive their channel names under. Any
    /// slash-free string serves: these tests assert Par SHAPE (case structure, send
    /// targets, receiver arity), not the scope's value — a production emission takes
    /// its scope from `language_definition_fingerprint`.
    const TEST_FP: &str = "mettail-langdef-v1:0000000000000000";
    use mettail_ast::language::{Equation, FreshnessCondition, FreshnessTarget};

    /// Every public lifecycle traversal over a generated reflection result is heap-bounded.
    /// A stack-safe reflector would still be unsafe if its result recursively cloned, compared,
    /// formatted, or dropped after the traversal returned.
    #[test]
    fn ground_term_lifecycle_is_stack_safe_at_depth() {
        const DEPTH: usize = 16_384;

        let mut term = GroundTerm::nullary("leaf");
        for _ in 0..DEPTH {
            term = GroundTerm::new("node", vec![term]);
        }

        let cloned = term.clone();
        assert_eq!(term, cloned);
        let rendered = format!("{term:?}");
        assert!(rendered.contains("leaf"));

        drop(cloned);
        drop(term);
    }

    /// S1 — the reflected-tag ABI has ONE writer and ONE reader, and they are
    /// mutual inverses on every label the tree can mint, INCLUDING dotted ones.
    ///
    /// This is the test the tree did not have. Before S1 there were five
    /// hand-rolled readers over one writer; four split at the LAST `.` and one at
    /// the FIRST, and their doc comments asserted contradictory invariants about
    /// whether a label may contain a dot. It may: synthesized literal leaves are
    /// `format!("{}({:?})", label, value)`, so a `Float32`/`Float64` category
    /// yields `FloatLit(8.5)` and a rational yields `RatLit(…)`.
    ///
    /// The dotted rows are the point. Under the old `rsplit_once` form
    /// `FloatLit(8.5)` split as `fingerprint = "…:0000.FloatLit(8"`,
    /// `label = "5)"` — no error, just a corrupted fingerprint that then failed
    /// the ground-marker check, leaking the marker into the decoded term as a
    /// phantom child.
    #[test]
    fn reflected_tag_round_trips_through_the_single_shared_inverse() {
        // Real fingerprints are `mettail-langdef-v1:{:016x}` — dot-free, which is
        // exactly the invariant `reflect_tag` asserts and the parse relies on.
        // The parse is LENGTH-agnostic, so a wider future scheme still round-trips;
        // the short and long rows below pin that.
        let fingerprints = [
            "mettail-langdef-v1:0123456789abcdef",
            "mettail-langdef-v1:0",
            "x",
            &"f".repeat(83),
        ];

        let mut labels: Vec<String> = vec![
            // Ordinary constructor labels (`syn::Ident`s — dot-free by construction).
            "Lam".into(),
            "App".into(),
            "NumLit(8)".into(),
            // ★ The dotted literal leaves that the `rsplit` form corrupted.
            "FloatLit(8.5)".into(),
            "FloatLit(-0.0)".into(),
            "RatLit(1.5)".into(),
            "FixedLit(2.25)".into(),
            r#"StringLit("a.b.c")"#.into(),
            // Pathological: a label that is nothing but dots and one that ends in one.
            "...".into(),
            "Weird.".into(),
        ];
        // Every reserved label, so a future addition to any reserved family is
        // automatically covered by this round trip.
        labels.extend(
            crate::rho_net_subst_trs::reserved_subst_trs_labels()
                .iter()
                .map(|l| (*l).to_string()),
        );
        labels.extend(
            crate::rho_net_pattern_guard::respread_reserved_labels()
                .iter()
                .map(|l| (*l).to_string()),
        );
        labels.push(DRIVE_RESERVED_LABEL.to_string());
        labels.push(GROUND_MARK_REFLECT_LABEL.to_string());
        labels.push(NONGROUND_MARK_REFLECT_LABEL.to_string());
        // The per-rule AC-carrier family, which carries a `:` and must survive intact.
        labels.push(format!("{DRIVE_RESERVED_LABEL}-ac:SomeRule"));

        for fingerprint in fingerprints {
            for label in &labels {
                let tag = reflect_tag(fingerprint, label);
                assert_eq!(
                    parse_reflected_tag(&tag),
                    Some((fingerprint, label.as_str())),
                    "reflect_tag/parse_reflected_tag must be mutual inverses on \
                     ({fingerprint:?}, {label:?}); tag was {tag:?}"
                );
            }
        }
    }

    /// S2 — the reserved-namespace claim, ASSERTED for the first time.
    ///
    /// Three places in this tree justify their safety by the sentence "a user
    /// constructor is a Rust `Ident`, so it cannot contain `^`", and one of them is
    /// a stated adequacy premise of `BinderReflectionTotalOrReject.v`. The sentence
    /// only means anything if every reserved label is in fact `^`-prefixed. Nothing
    /// checked that, and two labels are not.
    ///
    /// This test is the check. The exception list is closed and named, so S3 empties
    /// it by construction: rename the two Peano constants and this test tightens on
    /// its own.
    #[test]
    fn every_reserved_label_is_in_the_reserved_namespace() {
        use mettail_ast::validation::is_reserved_reflect_label;

        // ★ #36 S3: this list is now EMPTY, so the assertion below is the unqualified
        // claim — EVERY reserved label is in the reserved namespace. It was written with
        // a named-exception escape precisely so that emptying the exceptions would
        // tighten the test with no edit to the assertion itself.
        let mut exceptions = reserved_labels_outside_the_namespace();
        exceptions.sort_unstable();
        let violators: Vec<&str> = all_reserved_reflect_labels()
            .into_iter()
            .filter(|label| !is_reserved_reflect_label(label))
            .collect();

        assert_eq!(
            violators,
            exceptions.to_vec(),
            "the reserved-label census must satisfy the namespace rule except for the \
             two NAMED violators. A new name here means a reserved label was added \
             without a `^` prefix — which silently voids the unforgeability argument \
             the substitution TRS and BinderReflectionTotalOrReject.v both rest on."
        );

        // And any exception must still be genuinely reserved — never a licence to
        // drop a label from the census. Vacuous now that the list is empty; retained
        // so a future exception cannot be added without also being censused.
        for exception in exceptions {
            assert!(
                all_reserved_reflect_labels().contains(&exception),
                "{exception:?} is listed as a namespace exception but is not in the census"
            );
        }
    }

    /// The census is a SUPERSET of every family list, so a family can grow without
    /// silently escaping the namespace assertion above.
    #[test]
    fn the_reserved_census_covers_every_family() {
        let census = all_reserved_reflect_labels();
        let families: [&[&str]; 2] = [
            &crate::rho_net_subst_trs::reserved_subst_trs_labels()[..],
            &crate::rho_net_pattern_guard::respread_reserved_labels()[..],
        ];
        for family in families {
            for label in family {
                assert!(census.contains(label), "census is missing the reserved label {label:?}");
            }
        }
        for loose in [
            GROUND_MARK_REFLECT_LABEL,
            NONGROUND_MARK_REFLECT_LABEL,
            DRIVE_AC_RESERVED_LABEL,
            FLOAT_RESERVED_LABEL,
            FLOAT_HOIST_RESERVED_LABEL,
            FLOAT_MERGE_RESERVED_LABEL,
            // ★ #36 S3: the Peano numerals belong to NO family list — they are the
            // payload alphabet of a numeral argument, not a dispatch head, so they are
            // deliberately absent from the C2 exclusion set
            // (`reserved_subst_trs_labels`, which is a SWITCH). Pinning them here is
            // what keeps them censused: this loop is the inventory obligation the
            // family lists discharge for their own members.
            PEANO_ZERO_REFLECT_LABEL,
            PEANO_SUCC_REFLECT_LABEL,
        ] {
            assert!(census.contains(&loose), "census is missing the reserved label {loose:?}");
        }
    }

    /// ★ #36 S3 — the C2 exclusion set is a SWITCH, not an inventory, and the Peano
    /// numerals are not in it.
    ///
    /// `reserved_subst_trs_labels` drives `object_congruence_constructors`: membership
    /// asserts that the generated TRS installs a SPECIFIC subject-position arm for the
    /// tag which a generic congruence arm would shadow. `^Z`/`^S` have no such arm —
    /// they are a numeral ARGUMENT's alphabet, and a bare numeral in subject position
    /// is a malformed subject the cascade fails closed on. They are nonetheless fully
    /// reserved and fully censused, which the two assertions below pin TOGETHER so a
    /// future reader cannot conclude from the absence that they were forgotten.
    #[test]
    fn the_peano_numerals_are_censused_and_reserved_but_not_c2_excluded() {
        use mettail_ast::validation::is_reserved_reflect_label;

        let census = all_reserved_reflect_labels();
        let c2 = crate::rho_net_subst_trs::reserved_subst_trs_labels();
        for label in [PEANO_ZERO_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL] {
            assert!(
                is_reserved_reflect_label(label),
                "{label:?} must be in the `^` namespace — the S3 rename is what made \
                 `reserved_labels_outside_the_namespace` empty"
            );
            assert!(census.contains(&label), "{label:?} must be censused");
            assert!(
                !c2.contains(&label),
                "{label:?} must NOT be in the C2 object-congruence exclusion set: it has no \
                 subject-position arm for a generic congruence arm to shadow, so membership \
                 would assert a protection that protects nothing. Wanting it enumerated is a \
                 reason to add it to `all_reserved_reflect_labels`, never to a switch."
            );
        }
    }

    /// The inverse REJECTS anything that is not a reflected tag, so a classifier
    /// built on it cannot mistake foreign traffic for a reserved rendezvous.
    #[test]
    fn parse_reflected_tag_rejects_non_tags() {
        for bad in [
            "",
            "mettail.term.",                 // prefix only — no separator
            "mettail.term.fingerprint",      // no separator after the fingerprint
            "mettail.term.fingerprint.",     // empty label
            "sa:pattern/lhs:0123",           // a different channel family entirely
            "mettail.bag.fingerprint.Label", // adjacent ABI, wrong prefix
        ] {
            assert_eq!(parse_reflected_tag(bad), None, "must reject {bad:?}");
        }
    }
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

    /// The (compact location channel, constructor) nodes the spread must
    /// publish, in pre-order — the forward image of `spread_term_par` over a
    /// ground term, derived through the same exact index as the implementation.
    fn expected_spread_nodes(
        term: &GroundTerm,
        fingerprint: &str,
        root: &str,
    ) -> Vec<(String, String)> {
        let locations = SubjectLocationIndex::new(term);
        let mut out = Vec::new();
        locations.walk(SubjectPosition::ROOT, |position, term| {
            out.push((
                locations.channel("loc", fingerprint, root, position),
                term.constructor.clone(),
            ));
            true
        });
        out
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
        let expected = expected_spread_nodes(term, fingerprint, root);

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
        let spread = spread_term_par(term, fingerprint, root);
        let locations = SubjectLocationIndex::new(term);
        locations.walk(SubjectPosition::ROOT, |position, term| {
            if term.children.is_empty() {
                let capture = locations.channel("cap", fingerprint, root, position);
                let capture_channel = new_gstring_par(capture.clone(), Vec::new(), false);
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
            true
        });
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
        let locations = SubjectLocationIndex::new(&term);
        let root = locations.channel("loc", "testfp", "site0", SubjectPosition::ROOT);
        let want: std::collections::BTreeSet<String> = [
            root.clone(),
            locations.channel(
                "loc",
                "testfp",
                "site0",
                locations
                    .child(SubjectPosition::ROOT, 0)
                    .expect("left child"),
            ),
            locations.channel(
                "loc",
                "testfp",
                "site0",
                locations
                    .child(SubjectPosition::ROOT, 1)
                    .expect("right child"),
            ),
        ]
        .into_iter()
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
        let want_cap: std::collections::BTreeSet<String> = [
            locations.channel(
                "cap",
                "testfp",
                "site0",
                locations
                    .child(SubjectPosition::ROOT, 0)
                    .expect("left child"),
            ),
            locations.channel(
                "cap",
                "testfp",
                "site0",
                locations
                    .child(SubjectPosition::ROOT, 1)
                    .expect("right child"),
            ),
        ]
        .into_iter()
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
        let locations = SubjectLocationIndex::new(&leaf);
        let loc_channel = new_gstring_par(
            locations.channel("loc", "testfp", "site0", SubjectPosition::ROOT),
            Vec::new(),
            false,
        );
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
        let cap_channel = new_gstring_par(
            locations.channel("cap", "testfp", "site0", SubjectPosition::ROOT),
            Vec::new(),
            false,
        );
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

    // A-S5.3 (leg ii): the OLD-BNFC `::=` twin of AC_DEMO_FRAGMENT — the production `Ambient`
    // declaration shape (`PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}"`,
    // `languages/src/ambient.rs`), whose `term_context` is `None` while the HashBag kind sits in
    // `rule.items` as a `GrammarItem::Collection`. The resolver must fall back to the grammar
    // items here.
    const AC_COLONS_FRAGMENT: &str = r##"
        name: AcColonsFrag,
        types {
            Proc
        }
        terms {
            PZero . Proc ::= "0" ;
            Wrap . Proc ::= "wrap" "(" Proc ")" ;
            PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
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
            &new_gstring_par(
                crate::rho_net::RhoNetChannel::set_automaton_trace(
                    &program.language_fingerprint,
                    "scalar/AddInt",
                )
                .name,
                Vec::new(),
                false,
            ),
            "the firing dispatch receiver rests on the INV-S6-scoped \
             `sa:{{fingerprint}}/scalar/AddInt` \
             trace channel, NOT the \
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
        assert_eq!(
            sites[0].channel,
            crate::rho_net::RhoNetChannel::set_automaton_trace(
                &program.language_fingerprint,
                "scalar/AddInt",
            )
            .name
        );

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
            subst_trs: None,
            drive: None,
            drive_admission: crate::rho_net_drive::DriveAdmission::NotRequested,
            float: None,
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
            subst_trs: None,
            drive: None,
            drive_admission: crate::rho_net_drive::DriveAdmission::NotRequested,
            float: None,
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
            subst_trs: None,
            drive: None,
            drive_admission: crate::rho_net_drive::DriveAdmission::NotRequested,
            float: None,
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

        // Payload is the reflected Pair term: EList[ GPrivate(tag), ^nog, b, a ] (E-2-D v2:
        // the `^nog` marker at index 1 — a σ-var RHS is not hereditarily ground).
        assert_eq!(send.data.len(), 1);
        let elist = elist_body(&send.data[0]);
        assert_eq!(elist.ps.len(), 4, "head tag + ^nog marker + two children");

        let expected_tag = GPrivateBuilder::new_par_from_string(format!(
            "mettail.term.{}.Pair",
            lowered.language_fingerprint
        ));
        assert_eq!(elist.ps[0], expected_tag, "head is the unforgeable Pair reflection tag");
        assert_eq!(
            elist.ps[1],
            GPrivateBuilder::new_par_from_string(format!(
                "mettail.term.{}.^nog",
                lowered.language_fingerprint
            )),
            "index 1 is the ^nog marker (a σ-var-bearing RHS is not hereditarily ground)"
        );

        // RHS order (b, a): b = rhs_var_index(2, 1) = 1, a = rhs_var_index(2, 0) = 2.
        assert_eq!(rhs_var_index(2, 1), 1);
        assert_eq!(rhs_var_index(2, 0), 2);
        assert_eq!(boundvar_index(&elist.ps[2]), Some(1), "first child is b");
        assert_eq!(boundvar_index(&elist.ps[3]), Some(2), "second child is a");

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
        assert_eq!(outer.ps.len(), 3, "outer head tag + E-2-D marker + one child");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!(
                "mettail.term.{}.Outer",
                lowered.language_fingerprint
            )),
            "outer head is the unforgeable Outer reflection tag"
        );

        let inner = elist_body(&outer.ps[2]);
        assert_eq!(inner.ps.len(), 3, "inner head tag + E-2-D marker + one child");
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
        assert_eq!(
            boundvar_index(&inner.ps[2]),
            Some(1),
            "inner child is x (E-2-D marker at ps[1])"
        );

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
    fn minirho_comm_materializes_and_parcong_is_congruence_exempt() {
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
        // independent P2 detector; being congruence-ONLY (one `S ~> T` premise), it is the
        // A-S5.1 recorded install-exempt disposition at that detector site — the failed
        // `CollectionAc` family retained as the WHY, no fail-closed diagnostic pushed
        // (pre-A-S5.1 this row pinned `Unsupported(CollectionAc)` + an install error).
        let parcong = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == "rule:rewrite:1:ParCong")
            .expect("ParCong must be lowered");
        assert_eq!(
            *parcong,
            RhoNetLoweredRule::CongruenceExemptRewrite {
                rule_id: "rule:rewrite:1:ParCong".to_string(),
                family: UnsupportedFamily::CollectionAc,
            }
        );
        assert_eq!(
            lowered.congruence_exempt_rules(),
            vec![("rule:rewrite:1:ParCong", &UnsupportedFamily::CollectionAc)],
            "the P2-detector-site exemption is on the record"
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
            .find(|rewrite| rewrite.name == "Comm")
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
        // (D10) The ASYNCHRONOUS reduct is the single host-computed substitution slot.
        assert_eq!(site.reduct_slots, vec![None]);
        assert!(!site.channel.is_empty(), "the Comm receiver has a source channel");
    }

    // ─── D10: the SYNCHRONOUS π `Comm` — an arity-2 reduct + an explicit `^x.p` scope ────────────

    /// The GSLT omnibus's SYNCHRONOUS π communication (`omnibus.tex:1988-1989`): the receive scope
    /// is an EXPLICIT abstraction `^x.p` and the output `n!m.q` carries a continuation, so the
    /// reduct is the TWO-element bag `{(eval ^x.p m), q, ...rest}` — the parallel composition
    /// `p[m/x] | q`. Both were rejected before D10 closed.
    const MINIPI_SYNC_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniPiSync,
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

            POut . n:Name, m:Name, p:Proc
                |- n "!" m "." p : Proc ;

            PIn . n:Name, ^x.p:[Name -> Proc]
                |- "in" "(" n "," x ")" "." p : Proc ;
        },
        equations {},
        rewrites {
            Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest})
                ~> (PPar {(eval ^x.p m), q, ...rest});

            ParCong . | S ~> T
                |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
        }
    "#;

    /// (D10) The SYNCHRONOUS π `Comm` is recognized as a Comm shape: the `^x.p` abstraction
    /// contributes its body variable `p` as the receive element's scope, and the reduct carries the
    /// substitution AND the σ-delivered continuation `q`.
    #[test]
    fn synchronous_pi_comm_is_a_comm_shape_with_a_two_element_reduct() {
        let def = syn::parse_str::<LanguageDef>(MINIPI_SYNC_FRAGMENT).expect("fragment must parse");
        let comm_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "Comm")
            .expect("MiniPiSync has a Comm rewrite");
        let shape = comm_rule_shape(
            &comm_rewrite.left,
            &comm_rewrite.right,
            Some(&CollectionType::HashBag),
        )
        .expect("the synchronous Comm must be recognized as a Comm shape");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "n");
        assert_eq!(shape.rest.to_string(), "rest");
        assert_eq!(shape.scope_var.to_string(), "p", "`^x.p` contributes its body variable");
        assert_eq!(shape.arg_var.to_string(), "m");
        assert_eq!(
            shape
                .elements
                .iter()
                .map(|e| e.constructor.clone())
                .collect::<Vec<_>>(),
            vec!["PIn".to_string(), "POut".to_string()]
        );
        assert_eq!(
            shape.reducts,
            vec![CommReduct::Substitution, CommReduct::Var(ident("q"))],
            "the synchronous reduct is `(eval ^x.p m) | q`"
        );
    }

    /// (D10) The synchronous receiver gets ONE MORE receive-bind slot than the asynchronous one:
    /// `free_count = k + 1 + m + 1 = 2 + 1 + 2 + 1 = 6`, four bind patterns
    /// (`[bag, r_0, r_1, out]`), and a body that splices BOTH reduct sends with `rest`. The
    /// asynchronous receiver is unchanged at `COMM_FREE_COUNT = 5` / three patterns.
    #[test]
    fn synchronous_comm_receiver_carries_one_slot_per_reduct_element() {
        let def = syn::parse_str::<LanguageDef>(MINIPI_SYNC_FRAGMENT).expect("fragment must parse");
        let comm_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "Comm")
            .expect("MiniPiSync has a Comm rewrite");
        let receiver = comm_rule_receiver(
            &comm_rewrite.left,
            &comm_rewrite.right,
            new_gstring_par("c(root)".to_string(), Vec::new(), false),
            "fp",
            Some(CollectionType::HashBag),
        )
        .expect("the synchronous Comm must materialize a receiver");
        let receive = receiver
            .receives
            .first()
            .expect("the Comm receiver is a single Receive");
        assert!(receive.persistent);
        assert_eq!(receive.bind_count, 6, "k=2 channels + rest + 2 reducts + out");
        assert_eq!(receive.binds.len(), 1);
        assert_eq!(
            receive.binds[0].patterns.len(),
            4,
            "[bag-soup, r_0, r_1, out] — one pattern per reduct element"
        );
        assert_eq!(receive.binds[0].free_count, 6);
        // The non-linear guard still compares the two channel slots, in the WIDER frame:
        // `BoundVar(free_count - 1 - level)` = 5 and 4.
        let condition = receive.condition.as_ref().expect("non-linear condition");
        let expr = condition
            .exprs
            .first()
            .expect("a single condition expression");
        let ExprInstance::EEqBody(eq) = expr.expr_instance.as_ref().expect("condition expr") else {
            panic!("the Comm consistency condition must be an EEq, got {expr:?}");
        };
        assert_eq!(boundvar_index(eq.p1.as_ref().expect("EEq p1")), Some(5));
        assert_eq!(boundvar_index(eq.p2.as_ref().expect("EEq p2")), Some(4));
        // The body emits BOTH reduct sends plus the `rest` remainder.
        let body = receive.body.as_ref().expect("the receiver has a body");
        let soup = body.sends[0]
            .data
            .first()
            .expect("the out-send carries the bag soup");
        assert_eq!(soup.sends.len(), 2, "one `@\"ac:PPar\"!(r_j)` send per reduct element");
    }

    /// (D10) The synchronous injection site names its reduct slots: `None` for the ONE
    /// host-computed substitution, `Some("q")` for the σ-delivered output continuation.
    #[test]
    fn synchronous_comm_injection_site_names_its_reduct_slots() {
        let def = syn::parse_str::<LanguageDef>(MINIPI_SYNC_FRAGMENT).expect("fragment must parse");
        let sites = rho_net_comm_injection_sites(&def);
        assert_eq!(sites.len(), 1, "MiniPiSync has exactly one Comm rewrite");
        let site = &sites[0];
        assert_eq!(site.rule_label, "Comm");
        assert_eq!(site.scope_var, "p");
        assert_eq!(site.arg_var, "m");
        assert_eq!(
            site.reduct_slots,
            vec![None, Some("q".to_string())],
            "slot 0 is the host-computed substitution, slot 1 the σ-delivered continuation"
        );
        assert_eq!(
            site.element_arg_vars,
            vec![
                vec!["n".to_string(), "p".to_string()],
                vec!["n".to_string(), "m".to_string(), "q".to_string()],
            ]
        );
    }

    /// (D10, fail-closed) An abstraction-spelled element whose scope the substitution does NOT
    /// consume is rejected: the substitution is the only sound consumer of a binder scope, so a
    /// reduct that splices the raw body would let the bound variable escape.
    #[test]
    fn an_unconsumed_abstraction_scope_is_not_a_comm_shape() {
        // `{(PIn n ^x.p), (POut n m q), ...rest} ~> {(eval q m), p, ...rest}` — the substitution
        // consumes `q` (not the scope `p`), and `p` would be spliced raw.
        let left = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![
                    apply(
                        "PIn",
                        vec![
                            var_pattern("n"),
                            Pattern::Term(PatternTerm::Lambda {
                                binder: ident("x"),
                                body: Box::new(var_pattern("p")),
                            }),
                        ],
                    ),
                    apply("POut", vec![var_pattern("n"), var_pattern("m"), var_pattern("q")]),
                ],
                rest: Some(ident("rest")),
            }],
        );
        let right = apply(
            "PPar",
            vec![Pattern::Collection {
                coll_type: Some(CollectionType::HashBag),
                elements: vec![
                    Pattern::Term(PatternTerm::Subst {
                        term: Box::new(var_pattern("q")),
                        var: ident("x"),
                        replacement: Box::new(var_pattern("m")),
                    }),
                    var_pattern("p"),
                ],
                rest: Some(ident("rest")),
            }],
        );
        assert!(
            comm_rule_shape(&left, &right, Some(&CollectionType::HashBag)).is_none(),
            "an abstraction scope the substitution does not consume must fail closed"
        );
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
            .find(|rewrite| rewrite.name == "OpenRule")
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

    /// Stage 4 (Ambient In/Out): a minimal binder-free language whose `InRule`/`OutRule` are DEPTH-2
    /// NESTED structural non-linear AC rewrites — the generalization target isolated from the `PNew`
    /// binder + the `new`-floating equations (empty `equations {}`, so the nested Rho lowering gate
    /// `equations_boundary_canonicalizable` admits them on its empty-equations leg). The `OutRule`
    /// here keeps the InOutDemo EJECTION shape (`R` + top-spliced `...rest2`) — the A-S5.4b
    /// redeclared C-G (Red Out) shape has its own fragment below.
    const MINI_INOUT_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniInOut,
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
            Na . |- "na" : Name ;
            Nb . |- "nb" : Name ;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
            PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc ;
            POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc ;
            PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
        },
        equations {},
        rewrites {
            InRule . |- (PPar {(PAmb N (PPar {(PIn M P), ...rest1})), (PAmb M R), ...rest2})
                ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2}) ;
            OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
                ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2}) ;
        }
    "#;

    /// `nested_structural_ac_rule_shape` recognizes the bag-rooted `InRule` (op / cross-level `M` /
    /// spliced `rest2` / one nested reduct template) — and REJECTS the flat `OpenRule` (no nested
    /// element).
    #[test]
    fn nested_structural_ac_rule_shape_recognizes_in_rule() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let in_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "InRule")
            .expect("MiniInOut has an InRule rewrite");
        let shape = nested_structural_ac_rule_shape(&in_rewrite.left, &in_rewrite.right, &def)
            .expect("InRule must be recognized as a nested structural-AC shape");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "M");
        assert_eq!(shape.spliced_rest.to_string(), "rest2");
        // InRule's RHS bag has ONE fixed element `m[{ n[{P,...q}], R }]` (+ ...rest2).
        assert_eq!(shape.reduct_templates.len(), 1);
        assert!(shape.rest_splices_at_top, "InRule's ...rest2 rides the RHS bag's top remainder");

        // The flat OpenRule (no nested element) is REJECTED by the nested recognizer.
        let open_fragment = MINI_AMBIENT_FRAGMENT;
        let open_def = syn::parse_str::<LanguageDef>(open_fragment).expect("fragment must parse");
        let open_rewrite = open_def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "OpenRule")
            .expect("OpenRule present");
        assert!(
            nested_structural_ac_rule_shape(&open_rewrite.left, &open_rewrite.right, &open_def)
                .is_none(),
            "the flat OpenRule (no nested element) must NOT be a nested structural-AC shape"
        );
    }

    /// `nested_structural_ac_rule_shape` recognizes the WRAPPER-rooted `OutRule` (root `PAmb(M, {…})`,
    /// cross-level `M`, TWO reduct elements — `n[{P,...q}]` and `m[R]`).
    #[test]
    fn nested_structural_ac_rule_shape_recognizes_out_rule() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let out_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "OutRule")
            .expect("MiniInOut has an OutRule rewrite");
        let shape = nested_structural_ac_rule_shape(&out_rewrite.left, &out_rewrite.right, &def)
            .expect("OutRule (wrapper-rooted) must be recognized as a nested structural-AC shape");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "M");
        assert_eq!(shape.spliced_rest.to_string(), "rest2");
        // OutRule's RHS bag has TWO fixed elements `n[{P,...q}]` and `m[R]` (+ ...rest2).
        assert_eq!(shape.reduct_templates.len(), 2);
        assert!(
            shape.rest_splices_at_top,
            "the InOutDemo ejection-shaped OutRule top-splices its ...rest2 — still recognized"
        );
    }

    /// A-S5.4b (AM-1): a mini fragment carrying the REDECLARED C-G (Red Out) `OutRule` — the whole
    /// residual `...rest2` KEPT INSIDE `M` as the rest-only inner bag `(PAmb M (PPar {...rest2}))`,
    /// with a SINGLE fixed inner element (the wrapper-rooted rest-only inner-bag shape the
    /// recognizer must accept per `ma_theory_alignment.md`'s CORRECTED section).
    const MINI_REDECLARED_OUT_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniRedeclaredOut,
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
            Na . |- "na" : Name ;
            Nb . |- "nb" : Name ;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
            POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc ;
            PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
        },
        equations {},
        rewrites {
            OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), ...rest2}))
                ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))}) ;
        }
    "#;

    /// A-S5.4b (AM-1): `nested_structural_ac_rule_shape` ACCEPTS the redeclared C-G (Red Out)
    /// `OutRule` — wrapper-rooted with ONE fixed inner element + rest, the outer rest
    /// TEMPLATE-CONSUMED (referenced exactly once, as the rest-only inner bag of the second
    /// reduct), so `rest_splices_at_top` is `false`.
    #[test]
    fn nested_structural_ac_rule_shape_recognizes_the_redeclared_out_rule() {
        let def = syn::parse_str::<LanguageDef>(MINI_REDECLARED_OUT_FRAGMENT)
            .expect("fragment must parse");
        let out_rewrite = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "OutRule")
            .expect("the redeclared OutRule is present");
        let shape = nested_structural_ac_rule_shape(&out_rewrite.left, &out_rewrite.right, &def)
            .expect("the redeclared (Red Out) OutRule must be recognized");
        assert_eq!(shape.op, "PPar");
        assert_eq!(shape.nonlinear_var.to_string(), "M");
        assert_eq!(shape.spliced_rest.to_string(), "rest2");
        assert!(
            !shape.rest_splices_at_top,
            "the redeclared OutRule consumes ...rest2 INSIDE the m-reduct template, never at the top"
        );
        // The two reducts: the moving ambient `n[{P, ...rest1}]` and the residual-keeping
        // `m[{...rest2}]` — the second is exactly the rest-only inner-bag template.
        assert_eq!(shape.reduct_templates.len(), 2);
        let AcReconstructTemplate::Node { constructor, children } = &shape.reduct_templates[1]
        else {
            panic!("the second reduct is the m-ambient node, got {:?}", shape.reduct_templates[1]);
        };
        assert_eq!(constructor, "PAmb");
        assert_eq!(children[0], AcReconstructTemplate::Var("M".to_string()));
        assert_eq!(
            children[1],
            AcReconstructTemplate::Bag {
                op: "PPar".to_string(),
                elements: Vec::new(),
                rest: Some("rest2".to_string()),
            },
            "the residual is KEPT INSIDE M as the rest-only inner bag (empty rest legal)"
        );
    }

    /// A-S5.4b (AM-1) fail-closed: the outer rest must be consumed EXACTLY ONCE. A rewrite that
    /// consumes it twice (top splice AND template reference) or not at all (residual silently
    /// dropped) is rejected.
    #[test]
    fn nested_structural_ac_rule_shape_rejects_rest_misconsumption() {
        // Twice: `...rest2` both top-spliced and inside the m-reduct.
        let duplicated = MINI_REDECLARED_OUT_FRAGMENT.replace(
            "~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))}) ;",
            "~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2})), ...rest2}) ;",
        );
        let def = syn::parse_str::<LanguageDef>(&duplicated).expect("fragment must parse");
        let rewrite = &def.rewrites[0];
        assert!(
            nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, &def).is_none(),
            "a doubly-consumed outer rest (top splice + template) must be rejected"
        );

        // Never: `...rest2` absent from the RHS (the residual would be silently dropped; the RHS
        // stays σ-closed — `rest1` is an LHS binding — so the rejection is the rest-placement
        // check, not the σ-closure check).
        let dropped = MINI_REDECLARED_OUT_FRAGMENT.replace(
            "~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))}) ;",
            "~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest1}))}) ;",
        );
        let def = syn::parse_str::<LanguageDef>(&dropped).expect("fragment must parse");
        let rewrite = &def.rewrites[0];
        assert!(
            nested_structural_ac_rule_shape(&rewrite.left, &rewrite.right, &def).is_none(),
            "a dropped outer rest (residual material discarded) must be rejected"
        );
    }

    // ─── A-S5.4b: the equations-gate boundary-canonicalization recognizer ───────────────────────

    /// The CORRECTED Ambient equation set (A-S5.4b premise fix: capture-avoidance `x # N` on the
    /// capability trio + `AmbNew`; `ScopeExtrusion` freshness on the floated-past `...rest`;
    /// `NewComm` premise-free) over the production constructor inventory — the exact declarations
    /// `equations_boundary_canonicalizable` must admit.
    const MINI_CORRECTED_AMBIENT_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniCorrectedAmbient,
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
            PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc ;
            POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc ;
            POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc ;
            PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
            PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
        },
        equations {
            NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
            ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
            InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
            OutNew . | x # N |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
            OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
            AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
        },
        rewrites {}
    "#;

    fn corrected_ambient_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(MINI_CORRECTED_AMBIENT_FRAGMENT)
            .expect("the corrected mini-Ambient fragment must parse")
    }

    /// Every one of the six CORRECTED Ambient equations is individually recognized as a
    /// binder-float congruence, the handler leg holds, and the whole language is boundary-
    /// canonicalizable — the exact A-S5.4b admission.
    #[test]
    fn equations_gate_accepts_all_six_corrected_ambient_equations() {
        let def = corrected_ambient_def();
        assert!(
            language_has_float_handler(&def),
            "the mini corrected Ambient has equations + no RhoNativeJoin + the single PNew binder"
        );
        assert_eq!(
            float_surface_binder_label(&def).as_deref(),
            Some("PNew"),
            "PNew is the surface single binder"
        );
        for equation in &def.equations {
            assert!(
                is_binder_float_equation(&def, equation, "PNew"),
                "corrected equation {} must be recognized as a binder-float congruence",
                equation.name
            );
        }
        assert!(
            equations_boundary_canonicalizable(&def),
            "the corrected Ambient equation set is fully float-discharged at the boundary"
        );
    }

    /// A NON-binder equation (no float, no commutation — here a bare constructor identity) rejects
    /// the whole language: the gate stays fail-closed.
    #[test]
    fn equations_gate_rejects_a_non_binder_equation() {
        let with_non_binder = MINI_CORRECTED_AMBIENT_FRAGMENT.replace(
            "NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));",
            "NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));\n            \
             Swap . |- (PIn N P) = (POut N P);",
        );
        let def = syn::parse_str::<LanguageDef>(&with_non_binder).expect("fragment must parse");
        let swap = def
            .equations
            .iter()
            .find(|equation| equation.name == "Swap")
            .expect("the Swap equation is present");
        assert!(
            !is_binder_float_equation(&def, swap, "PNew"),
            "a non-binder equation is never a float congruence"
        );
        assert!(
            !equations_boundary_canonicalizable(&def),
            "one unrecognized equation keeps the language gated"
        );
    }

    /// A float with a MISSING freshness premise (the pre-A-S5.4b vacuous-binder `x # P` — or no
    /// premise at all — instead of the capture-avoidance `x # N`) is rejected: the recognizer
    /// checks freshness on EVERY floated-past field, against the CORRECTED declarations only.
    #[test]
    fn equations_gate_rejects_a_float_with_a_missing_freshness_premise() {
        for wrong in [
            // No premise at all.
            "InNew . |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));",
            // The pre-A-S5.4b vacuous-binder premise (freshness on the BODY, not the passed field).
            "InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));",
        ] {
            let variant = MINI_CORRECTED_AMBIENT_FRAGMENT
                .replace("InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));", wrong);
            let def = syn::parse_str::<LanguageDef>(&variant).expect("fragment must parse");
            let in_new = def
                .equations
                .iter()
                .find(|equation| equation.name == "InNew")
                .expect("InNew present");
            assert!(
                !is_binder_float_equation(&def, in_new, "PNew"),
                "a float missing the capture-avoidance freshness on the passed field must be \
                 rejected (declared: {wrong})"
            );
            assert!(!equations_boundary_canonicalizable(&def));
        }
    }

    /// A TWO-binder language whose extra equation floats the SECOND binder is rejected: the float
    /// handler floats only THE surface binder (the first single binder over the primary category),
    /// so an equation over any other binder is not discharged at the boundary.
    #[test]
    fn equations_gate_rejects_a_float_over_a_different_binder_in_a_two_binder_language() {
        let two_binder = MINI_CORRECTED_AMBIENT_FRAGMENT
            .replace(
                "PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc ;",
                "PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc ;\n            \
                 PBind . ^x.p:[Name -> Proc] |- \"bind\" \"(\" x \",\" p \")\" : Proc ;",
            )
            .replace(
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));",
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));\n            \
                 BindNew . | x # N |- (PIn N (PBind ^x.P)) = (PBind ^x.(PIn N P));",
            );
        let def = syn::parse_str::<LanguageDef>(&two_binder).expect("fragment must parse");
        // The surface binder is STILL the first single binder (PNew) — the handler's target.
        assert_eq!(float_surface_binder_label(&def).as_deref(), Some("PNew"));
        let bind_new = def
            .equations
            .iter()
            .find(|equation| equation.name == "BindNew")
            .expect("BindNew present");
        assert!(
            !is_binder_float_equation(&def, bind_new, "PNew"),
            "a float over the NON-surface binder is not discharged by the handler"
        );
        assert!(
            !equations_boundary_canonicalizable(&def),
            "the two-binder language stays gated on its second-binder float"
        );
    }

    /// AM-6e: a float-across-constructor whose `C` LACKS the handler's prefix shape (here TWO
    /// plain primary-category fields — the handler's prefix arm floats only the exactly-one-field
    /// shape and everything else falls to its no-recursion catch-all) is rejected, even with a
    /// complete freshness premise set.
    #[test]
    fn equations_gate_rejects_a_float_across_a_non_prefix_shape_constructor() {
        let with_both = MINI_CORRECTED_AMBIENT_FRAGMENT
            .replace(
                "PZero . |- \"0\" : Proc ;",
                "PZero . |- \"0\" : Proc ;\n            \
                 PBoth . a:Proc, b:Proc |- \"both\" \"(\" a \",\" b \")\" : Proc ;",
            )
            .replace(
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));",
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));\n            \
                 BothNew . | x # Q |- (PBoth (PNew ^x.P) Q) = (PNew ^x.(PBoth P Q));",
            );
        let def = syn::parse_str::<LanguageDef>(&with_both).expect("fragment must parse");
        // PBoth has TWO plain primary-category fields — the handler's catch-all, never floated.
        assert_eq!(
            float_constructor_shape(&def, &ident("PBoth")),
            FloatConstructorShape::Other,
            "PBoth is not the handler's exactly-one-primary-field prefix shape"
        );
        let both_new = def
            .equations
            .iter()
            .find(|equation| equation.name == "BothNew")
            .expect("BothNew present");
        assert!(
            !is_binder_float_equation(&def, both_new, "PNew"),
            "AM-6e: a float across a catch-all-shaped constructor must NOT pass the recognizer"
        );
        assert!(!equations_boundary_canonicalizable(&def));
    }

    /// The handler-shape classifier agrees with the handler's arms on the production inventory:
    /// the capability prefixes + the ambient are prefix-shaped with the binder at the single
    /// primary field, the bag is the collection shape, and the binder itself is neither.
    #[test]
    fn float_constructor_shape_classifies_the_ambient_inventory() {
        let def = corrected_ambient_def();
        for label in ["PIn", "POut", "POpen", "PAmb"] {
            assert_eq!(
                float_constructor_shape(&def, &ident(label)),
                FloatConstructorShape::Prefix { primary_field_index: 1, field_count: 2 },
                "{label} is the handler's prefix shape (Name field 0, Proc field 1)"
            );
        }
        assert_eq!(
            float_constructor_shape(&def, &ident("PPar")),
            FloatConstructorShape::CollectionOverPrimary,
            "PPar is the handler's bag-extrusion shape"
        );
        assert_eq!(
            float_constructor_shape(&def, &ident("PNew")),
            FloatConstructorShape::Other,
            "the binder itself is the binder arm, never a float-across target"
        );
        assert_eq!(
            float_constructor_shape(&def, &ident("PZero")),
            FloatConstructorShape::Other,
            "a nullary constructor has no float arm"
        );
    }

    /// Both `InRule` and `OutRule` un-skip to a `NestedStructuralAcRewrite`, and
    /// `rho_net_nested_structural_ac_injection_sites` surfaces exactly the two firing sites with their
    /// operand + reduct templates.
    #[test]
    fn mini_inout_materializes_nested_structural_ac() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);

        for label in ["InRule", "OutRule"] {
            let rule = lowered
                .rules()
                .iter()
                .find(|rule| rule.rule_id().contains(label))
                .unwrap_or_else(|| panic!("{label} must be lowered"));
            assert!(
                matches!(rule, RhoNetLoweredRule::NestedStructuralAcRewrite { .. }),
                "{label} must materialize as a NestedStructuralAcRewrite, got {rule:?}"
            );
        }

        let sites = rho_net_nested_structural_ac_injection_sites(&def);
        assert_eq!(sites.len(), 2, "InRule + OutRule surface two nested sites, got {sites:?}");
        let labels: HashSet<String> = sites.iter().map(|s| s.rule_label.clone()).collect();
        assert!(labels.contains("InRule") && labels.contains("OutRule"));
        for site in &sites {
            assert_eq!(site.op, "PPar");
            assert_eq!(site.nonlinear_var, "M");
            assert_eq!(site.rest_var, "rest2");
            assert!(!site.reduct_templates.is_empty());
        }
    }

    /// `instantiate_ac_reconstruct_template` rebuilds the `InRule` NESTED reduct
    /// `m[{ n[{P,...q}], R }]` from a synthetic σ (with `q = {}` empty) — the exact ground term the
    /// structural-AC σ-injection reflects.
    #[test]
    fn instantiate_ac_reconstruct_template_rebuilds_the_in_reduct() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let sites = rho_net_nested_structural_ac_injection_sites(&def);
        let in_site = sites
            .iter()
            .find(|s| s.rule_label == "InRule")
            .expect("InRule site present");
        let reduct_template = &in_site.reduct_templates[0];

        // σ: N=na, M=nb, P=0, R=0, rest1={} (empty inner residual bag).
        let sigma: HashMap<&str, GroundTerm> = HashMap::from([
            ("N", GroundTerm::nullary("Na")),
            ("M", GroundTerm::nullary("Nb")),
            ("P", GroundTerm::nullary("PZero")),
            ("R", GroundTerm::nullary("PZero")),
            ("rest1", GroundTerm::collection(CollectionType::HashBag, "PPar", Vec::new())),
        ]);
        let find = |name: &str| sigma.get(name).cloned();
        let reduct = instantiate_ac_reconstruct_template(reduct_template, &find)
            .expect("the reduct template must rebuild from a complete σ");

        // Expected: PAmb(Nb, PPar{ PAmb(Na, PPar{ PZero }), PZero }).
        assert_eq!(reduct.constructor, "PAmb");
        assert_eq!(reduct.coll_type, None);
        assert_eq!(reduct.children[0].constructor, "Nb"); // the moved-into ambient name M
        let inner_bag = &reduct.children[1];
        assert_eq!(inner_bag.coll_type, Some(CollectionType::HashBag));
        assert_eq!(inner_bag.constructor, "PPar");
        // { n[{P}], R } — two elements (the residual q was empty).
        assert_eq!(inner_bag.children.len(), 2);
        assert!(inner_bag.children.iter().any(|c| c.constructor == "PAmb"));
        assert!(inner_bag.children.iter().any(|c| c.constructor == "PZero"));
    }

    /// The DEPTH-2 nested structural-AC MATCH entries surface both `InRule` (bag-rooted, root
    /// constructor `PPar`) and `OutRule` (wrapper-rooted, root constructor `PAmb`) — the data the
    /// SPREAD path co-installs a MATCH receiver from, keyed on the LHS root pattern's TOP constructor.
    #[test]
    fn nested_structural_ac_match_entries_surface_in_and_out() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_nested_structural_ac_match_entries(&def);
        assert_eq!(entries.len(), 2, "InRule + OutRule surface two match entries, got {entries:?}");

        let in_entry = entries
            .iter()
            .find(|e| e.fired_rule_label == "InRule")
            .expect("the InRule match entry is present");
        assert_eq!(in_entry.op(), "PPar");
        assert_eq!(
            in_entry.root_constructor().as_deref(),
            Some("PPar"),
            "InRule is bag-rooted — its LHS root TOP constructor is the bag op PPar"
        );

        let out_entry = entries
            .iter()
            .find(|e| e.fired_rule_label == "OutRule")
            .expect("the OutRule match entry is present");
        assert_eq!(out_entry.op(), "PPar");
        assert_eq!(
            out_entry.root_constructor().as_deref(),
            Some("PAmb"),
            "OutRule is wrapper-rooted — its LHS root TOP constructor is the wrapper PAmb"
        );
    }

    /// The SPREAD nested-AC MATCH receiver is a persistent single `Receive` carrying the cross-level
    /// `EEq(M_outer, M_inner)` guard `condition` and — unlike the report-path
    /// `nested_structural_ac_receiver_par` (which takes the `m` reducts as SEPARATELY DELIVERED slots,
    /// a `(m + 2)`-value message) — exactly a 2-VALUE message `[operand_pattern, out]`, because it
    /// BINDS every σ slot from the operand and REBUILDS the nested reduct in its body. Both In (a soup
    /// operand pattern) and Out (a wrapper `EList` operand pattern) bind the same 8-slot frame
    /// (2 cross-level `M` + the outer/inner rests + `N`/`P`/`R` + out).
    #[test]
    fn nested_structural_ac_match_receiver_is_a_two_value_message_with_the_cross_level_guard() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_nested_structural_ac_match_entries(&def);
        let fp = mettail_ast::identity::language_definition_fingerprint(&def);
        let source = new_gstring_par("ac:site".to_string(), Vec::new(), false);

        for label in ["InRule", "OutRule"] {
            let entry = entries
                .iter()
                .find(|e| e.fired_rule_label == label)
                .unwrap_or_else(|| panic!("{label} match entry present"));
            let receiver =
                nested_structural_ac_match_receiver_par(&entry.shape, source.clone(), &fp);

            assert_eq!(receiver.receives.len(), 1, "{label}: one receive");
            let receive = &receiver.receives[0];
            assert!(receive.persistent, "{label}: the match receiver is persistent");
            assert!(receive.condition.is_some(), "{label}: the cross-level M ≡ M guard is present");
            assert_eq!(receive.binds.len(), 1, "{label}: one polyadic bind");
            assert_eq!(
                receive.binds[0].patterns.len(),
                2,
                "{label}: the 2-value spread message [operand_pattern, out] — NOT the report-path reduct slots"
            );
            // 2 cross-level M occurrences + outer rest2 + inner rest1 + N + P + R + out = 8 slots.
            assert_eq!(
                receive.binds[0].free_count, 8,
                "{label}: the operand binds every reduct σ slot (M×2, rest1, rest2, N, P, R) + out"
            );
            // The body sends the rebuilt reduct on the bound `out` (BoundVar(0)) channel.
            assert!(receive.body.is_some(), "{label}: the body rebuilds + emits the reduct on out");
        }
    }

    /// The DEPTH-2 nested structural-AC MATCH call LOCATES the `InRule` operand at a bag-rooted node
    /// (root `PPar`) AND the `OutRule` operand at a wrapper-rooted node (root `PAmb`) — keyed on the
    /// LHS root TOP constructor — co-installing a MATCH receiver + the site-keyed carrier delivery at
    /// each, and co-installs NOTHING for a non-matching subject (fail-closed).
    #[test]
    fn nested_structural_ac_match_call_locates_the_in_bag_and_the_out_wrapper() {
        let def = syn::parse_str::<LanguageDef>(MINI_INOUT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_nested_structural_ac_match_entries(&def);
        let fp = mettail_ast::identity::language_definition_fingerprint(&def);

        // The InRule redex `{ na[{ in(nb, A) }] | nb[B] }` — a bag-rooted (`PPar`) operand.
        let in_bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![
                GroundTerm::new(
                    "PAmb",
                    vec![
                        GroundTerm::nullary("Na"),
                        GroundTerm::collection(
                            CollectionType::HashBag,
                            "PPar",
                            vec![GroundTerm::new(
                                "PIn",
                                vec![GroundTerm::nullary("Nb"), GroundTerm::nullary("PA")],
                            )],
                        ),
                    ],
                ),
                GroundTerm::new("PAmb", vec![GroundTerm::nullary("Nb"), GroundTerm::nullary("PB")]),
            ],
        );
        let in_call = nested_structural_ac_match_call_par(&in_bag, &entries, "site0", "OUT", &fp);
        assert!(
            !in_call.receives.is_empty(),
            "the bag-rooted InRule operand co-installs a nested-structural-AC MATCH receiver"
        );
        assert!(!in_call.sends.is_empty(), "the site-keyed carrier delivery is published");

        // The OutRule redex `nb[{ na[{ out(nb, A) }] | B }]` — a WRAPPER-rooted (`PAmb`) operand.
        let out_wrapper = GroundTerm::new(
            "PAmb",
            vec![
                GroundTerm::nullary("Nb"),
                GroundTerm::collection(
                    CollectionType::HashBag,
                    "PPar",
                    vec![
                        GroundTerm::new(
                            "PAmb",
                            vec![
                                GroundTerm::nullary("Na"),
                                GroundTerm::collection(
                                    CollectionType::HashBag,
                                    "PPar",
                                    vec![GroundTerm::new(
                                        "POut",
                                        vec![GroundTerm::nullary("Nb"), GroundTerm::nullary("PA")],
                                    )],
                                ),
                            ],
                        ),
                        GroundTerm::nullary("PB"),
                    ],
                ),
            ],
        );
        let out_call =
            nested_structural_ac_match_call_par(&out_wrapper, &entries, "site0", "OUT", &fp);
        assert!(
            !out_call.receives.is_empty(),
            "the wrapper-rooted OutRule operand co-installs a nested-structural-AC MATCH receiver"
        );
        assert!(!out_call.sends.is_empty(), "the site-keyed carrier delivery is published");

        // A non-matching subject (no PPar bag / PAmb wrapper) co-installs nothing (fail-closed).
        let leaf = GroundTerm::nullary("PZero");
        let none = nested_structural_ac_match_call_par(&leaf, &entries, "site0", "OUT", &fp);
        assert!(
            none.receives.is_empty() && none.sends.is_empty(),
            "no nested-AC operand ⇒ no nested-structural-AC co-install"
        );
    }

    /// Slice 3a: the AC match descent (`ac_match_install_at`, the routine the structural-AC spread
    /// matcher reuses) is STRUCTURAL — it descends the children of every non-bag node until it
    /// locates a HashBag. A PNew binder reflects to a single-child `^lambda([⟦body⟧])` (macro
    /// `reflect_category_fn`), so an operand bag UNDER a `new` is reached by the SAME descent with NO
    /// binder-specific code. We wrap the bag in a synthetic `^lambda` node (exactly the shape PNew
    /// reflects to) and confirm the co-install still fires at the bag — the reflection+descent the
    /// structural-AC spread matcher (slice 3b) rides for FREE.
    #[test]
    fn ac_match_call_descends_through_lambda_to_the_bag() {
        let mut def =
            syn::parse_str::<LanguageDef>(AC_DEMO_FRAGMENT).expect("the AcDemo fragment parses");
        // A linear with-rest HashBag AC rewrite `PPar{x, ...rest} ~> Wrap(x)` so `rho_net_ac_match_
        // entries` surfaces a real match entry (the AcDemo fragment declares only the constructors).
        def.rewrites.push(RewriteRule {
            name: ident("AcStep"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: Some(CollectionType::HashBag),
                    elements: vec![var_pattern("x")],
                    rest: Some(ident("rest")),
                }],
            ),
            right: apply("Wrap", vec![var_pattern("x")]),
            is_auto_injected: false,
        });
        let entries = rho_net_ac_match_entries(&def);
        assert!(!entries.is_empty(), "the linear AC rewrite surfaces a match entry");
        let fp = mettail_ast::identity::language_definition_fingerprint(&def);

        let bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
        );

        // Top-level bag: located at the spread root.
        let top = ac_match_call_par(&bag, &entries, "site0", "OUT", &fp);
        assert!(!top.receives.is_empty(), "the top-level bag co-installs an AC receiver");

        // Bag under a `^lambda` (the PNew reflection image): located by the SAME structural descent.
        let under_lambda = GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![bag.clone()]);
        let nested = ac_match_call_par(&under_lambda, &entries, "site0", "OUT", &fp);
        assert!(
            !nested.receives.is_empty(),
            "the descent rides the ^lambda child into the operand bag and co-installs there"
        );

        // No bag under the `^lambda` ⇒ fail-closed descent (nothing co-installed).
        let leaf = GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![GroundTerm::nullary("A")]);
        let none = ac_match_call_par(&leaf, &entries, "site0", "OUT", &fp);
        assert!(none.receives.is_empty(), "no bag under the ^lambda ⇒ no co-install");
    }

    /// Slice 3b: the STRUCTURAL non-linear AC match ENTRY surfaces the OpenRule (op `PPar`, the two
    /// structural reduct vars `P`/`Q`) — the structural-AC analogue of the linear `rho_net_ac_match_
    /// entries`. Only rewrites that un-skipped to a `StructuralAcRewrite` receiver are surfaced.
    #[test]
    fn structural_ac_match_entry_surfaces_the_open_rule() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_structural_ac_match_entries(&def);
        assert_eq!(entries.len(), 1, "MiniAmbient surfaces exactly one structural-AC match entry");
        assert_eq!(entries[0].fired_rule_label, "OpenRule");
        assert_eq!(entries[0].op(), "PPar");
        assert_eq!(
            entries[0]
                .shape
                .reduct_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>(),
            vec!["P".to_string(), "Q".to_string()]
        );
    }

    /// Slice 3b: the per-site MATCH receiver for OpenRule binds EVERYTHING from the bag — a 2-value
    /// message `[bag_pattern, out]` (NOT the report-path `[bag, r0, …, out]`), a persistent receive,
    /// the non-linear `N ≡ N` guard, and a connective soup with one send-pattern per structured
    /// element. `free_count = k + 2 + |distinct reducts| = 2 + 2 + 2 = 6`.
    #[test]
    fn structural_ac_match_receiver_binds_the_bag_and_reducts() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_structural_ac_match_entries(&def);
        let fp = mettail_ast::identity::language_definition_fingerprint(&def);
        let source = new_gstring_par("ac:site".to_string(), Vec::new(), false);
        let receiver = structural_ac_match_receiver_par(&entries[0].shape, source, &fp);

        assert_eq!(receiver.receives.len(), 1, "one receive");
        let receive = &receiver.receives[0];
        assert!(receive.persistent, "the match receiver is persistent");
        assert!(receive.condition.is_some(), "the non-linear N ≡ N guard is present");
        assert_eq!(receive.binds.len(), 1, "one polyadic bind");
        assert_eq!(
            receive.binds[0].patterns.len(),
            2,
            "the 2-value spread message [bag_pattern, out] — NOT the report-path reduct slots"
        );
        assert_eq!(receive.binds[0].free_count, 6, "k(2) + rest(1) + reducts(2) + out(1)");
        assert_eq!(
            receive.binds[0].patterns[0].sends.len(),
            2,
            "the connective bag soup has one send-pattern per structured element"
        );
    }

    /// Slice 3b: the structural-AC match CALL locates the OpenRule bag at the TOP LEVEL and UNDER a
    /// `^lambda` (the PNew reflection image) by the SAME structural descent, and co-installs nothing
    /// for a non-matching subject (fail-closed).
    #[test]
    fn structural_ac_match_call_locates_the_open_bag_top_level_and_under_lambda() {
        let def =
            syn::parse_str::<LanguageDef>(MINI_AMBIENT_FRAGMENT).expect("fragment must parse");
        let entries = rho_net_structural_ac_match_entries(&def);
        let fp = mettail_ast::identity::language_definition_fingerprint(&def);

        let bag = GroundTerm::collection(
            CollectionType::HashBag,
            "PPar",
            vec![
                GroundTerm::new(
                    "POpen",
                    vec![GroundTerm::nullary("Na"), GroundTerm::nullary("PA")],
                ),
                GroundTerm::new("PAmb", vec![GroundTerm::nullary("Na"), GroundTerm::nullary("PB")]),
            ],
        );

        // Top-level bag: located at the spread root.
        let top = structural_ac_match_call_par(&bag, &entries, "site0", "OUT", &fp);
        assert!(
            !top.receives.is_empty(),
            "the top-level open bag co-installs a structural-AC match receiver"
        );
        assert!(!top.sends.is_empty(), "the site-keyed carrier delivery is published");

        // Bag under a `^lambda` (the PNew reflection image): located by the SAME structural descent.
        let under_lambda = GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![bag.clone()]);
        let nested = structural_ac_match_call_par(&under_lambda, &entries, "site0", "OUT", &fp);
        assert!(
            !nested.receives.is_empty(),
            "the descent rides the ^lambda binder image into the open bag"
        );

        // A non-matching subject (no PPar bag anywhere) co-installs nothing (fail-closed).
        let leaf = GroundTerm::nullary("PZero");
        let none = structural_ac_match_call_par(&leaf, &entries, "site0", "OUT", &fp);
        assert!(
            none.receives.is_empty() && none.sends.is_empty(),
            "no operand bag ⇒ no structural-AC co-install"
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
            .find(|rewrite| rewrite.name == "Comm")
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
            .find(|rewrite| rewrite.name == "OpenRule")
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
            .find(|rewrite| rewrite.name == "Beta")
            .expect("the Beta rewrite exists");
        let (vars, scope, repl) = subst_rule_shape(&rewrite.left, &rewrite.right)
            .expect("Beta is a substitution rewrite");
        assert_eq!(
            vars.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
            vec!["fun".to_string(), "arg".to_string()],
            "the LHS σ order is [fun, arg] (binder-excluded)"
        );
        assert_eq!(scope.to_string(), "fun", "the substitution scope variable is fun");
        assert_eq!(repl.to_string(), "arg", "the substitution replacement variable is arg");

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
            .find(|term| term.label == "PowInt")
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

    /// A-S3: the LOCATE→CONTRACT-CALL bridge is a VALUE-FREE pure forwarder — a single
    /// non-persistent `(k+1)`-formal receive on the trigger channel whose only body is ONE send
    /// on the reserved handler contract channel forwarding EXACTLY the bound formals (the
    /// located σ operands + the dynamic out) in binding order. No ground value of any kind
    /// rides it — the A-S3 boundary: the value first exists when the machine's handler COMM
    /// produces it.
    #[test]
    fn native_locate_contract_bridge_is_a_value_free_forwarder() {
        let k = 2;
        let native_channel = crate::native_handler::native_contract_channel(
            0,
            "mettail-langdef-v1:6ef0c40636bb0bca",
        );
        let bridge =
            native_locate_contract_bridge_par("sa:scalar/PowInt", k, native_channel.clone());

        let [receive] = bridge.receives.as_slice() else {
            panic!("the bridge is a single receive, got {bridge:?}");
        };
        assert!(!receive.persistent, "one located site drives exactly one contract call");
        assert_eq!(receive.bind_count, (k + 1) as i32, "k captured args + the dynamic out");
        let [bind] = receive.binds.as_slice() else {
            panic!("one bind on the trigger channel");
        };
        assert_eq!(bind.patterns.len(), k + 1);
        assert_eq!(
            bind.source.as_ref().and_then(gstring_value).as_deref(),
            Some("sa:scalar/PowInt"),
            "the bridge consumes the native entry's accept"
        );

        let body = receive.body.as_ref().expect("the bridge has a body");
        let [send] = body.sends.as_slice() else {
            panic!("the body is exactly one contract-call send, got {body:?}");
        };
        assert_eq!(
            send.chan.as_ref(),
            Some(&native_channel),
            "the send targets the reserved [0xF1, rule_index] handler contract channel"
        );
        // Every datum is a BOUND FORMAL (BoundVar), in binding order (arg i = BoundVar(k - i),
        // out = BoundVar(0)) — no expression anywhere is a ground value.
        assert_eq!(send.data.len(), k + 1, "forwards all k captured args + out");
        for (i, datum) in send.data.iter().enumerate() {
            let [expr] = datum.exprs.as_slice() else {
                panic!("datum {i} is a single bound-var expr, got {datum:?}");
            };
            let Some(ExprInstance::EVarBody(evar)) = expr.expr_instance.as_ref() else {
                panic!("datum {i} is a var reference, got {expr:?}");
            };
            let Some(VarInstance::BoundVar(index)) =
                evar.v.as_ref().and_then(|v| v.var_instance.as_ref())
            else {
                panic!("datum {i} is a BOUND var (a forwarded formal), got {evar:?}");
            };
            assert_eq!(
                *index,
                (k - i) as i32,
                "datum {i} forwards formal {i} (reverse De Bruijn: BoundVar(k - i))"
            );
        }
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
            .find(|term| term.label == "PowInt")
            .expect("PowInt exists");
        let fact = def
            .terms
            .iter()
            .find(|term| term.label == "FactInt")
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
        // E-2-D v2: EList[^lambda tag, marker, ⟦binder⟧, ⟦body⟧] — the marker at index 1.
        assert_eq!(elements.len(), 4, "EList[^lambda tag, marker, ⟦binder⟧, ⟦body⟧]");
        assert_eq!(elements[0], lambda_tag, "the head tag is the reserved ^lambda binder tag");
        // The binder leaf is a `^bound` node (not a σ-slot BoundVar) — head tag at index 0, its
        // own `^nog` marker at index 1.
        let binder_leaf = &elist_body(&elements[2]).ps;
        assert_eq!(binder_leaf[0], bound_tag, "the binder reflects to a ^bound leaf");
        // Inside the body `Pair(x, y)`: x is a ^bound leaf, y is a σ-slot BoundVar(1). The body's
        // own marker sits at body[1]; children shift to body[2] / body[3].
        let body = &elist_body(&elements[3]).ps; // [Pair tag, marker, ⟦x⟧, ⟦y⟧]
        assert_eq!(body[0], pair_tag, "the body head tag is the Pair constructor tag");
        let x_leaf = &elist_body(&body[2]).ps;
        assert_eq!(
            x_leaf[0], bound_tag,
            "the bound occurrence x reflects to a ^bound leaf, not a σ-slot"
        );
        assert_eq!(
            boundvar_index(&body[3]),
            Some(rhs_var_index(1, 0)),
            "the free body var y reflects to its σ-slot BoundVar"
        );
    }

    /// Stage 4 S-binder SLICE 2a: a `Subst`/`MultiSubst` RHS reaching `reflect_term_par` fails closed
    /// (`Substitution`). The RETIRED Stage-3c behavior resolved it to the host-σ-slot `BoundVar`
    /// (the receiver forwarded the host-computed CONTRACTUM there — see the commented
    /// `reflect_subst_scope_slot`); the in-Rho β now lowers a TOP-LEVEL substitution rewrite to the
    /// β SEED (`lower_subst_rewrite` → `subst_seed_receiver_par`, which SENDS `^subst(⟦Z⟧, a, b, out)`
    /// so the TRS computes the reduct IN RHO), so a subst node reaching this general reflector (only a
    /// NESTED subst) has no in-Rho image this slice and fails closed — like the LHS subst arm.
    #[test]
    fn reflect_term_par_fails_closed_on_a_substitution_node() {
        let fp = "mettail-langdef-v1:0011223344556677";
        let vars = vec![ident("fun"), ident("arg")];
        // A (formerly scope-slot-resolving) closed substitution now fails closed here.
        let subst = Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(var_pattern("fun")),
            replacements: vec![var_pattern("arg")],
        });
        assert_eq!(
            reflect_term_par(&subst, &vars, 2, fp, None),
            Err(UnsupportedFamily::Substitution),
            "a substitution RHS is the in-Rho β SEED (lower_subst_rewrite), not a reflect_term_par slot",
        );

        // An OPEN substitution (scope not a bound LHS var) also fails closed.
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
        // E-2-D (reflected-ABI v2): head tag + `^gnd` marker at index 1 + two ground children.
        assert_eq!(outer.ps.len(), 4, "head tag + ^gnd marker + two ground children");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Pair")),
            "head is the shared unforgeable Pair reflection tag"
        );
        assert_eq!(
            outer.ps[1],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.^gnd")),
            "index 1 is the hereditary-ground marker (Pair(B, A) contains no ^bound leaf)"
        );

        let b = elist_body(&outer.ps[2]);
        assert_eq!(b.ps.len(), 2, "nullary B: head tag + ^gnd marker");
        assert_eq!(b.ps[0], GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.B")));
        let a = elist_body(&outer.ps[3]);
        assert_eq!(a.ps.len(), 2, "nullary A: head tag + ^gnd marker");
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
                &new_gstring_par(ac_soup_channel(fp, "PPar"), Vec::new(), false),
                "elements are sent on the AC element channel ac:{{op}}"
            );
            assert_eq!(
                elist_body(&send.data[0]).ps.len(),
                2,
                "nullary element = head tag + E-2-D ^gnd marker"
            );
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
        let pattern = ac_bag_pattern(TEST_FP, "PPar", 2);
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
        assert_eq!(outer.ps.len(), 3, "head tag + E-2-D marker + one element σ");
        assert_eq!(
            outer.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the RHS head is the Wrap reflection tag"
        );
        assert_eq!(
            boundvar_index(&outer.ps[2]),
            Some(2),
            "element x = BoundVar(2) — the AC receiver frame (k+2-1 for k=1); E-2-D marker at ps[1]"
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
            Some(ac_soup_channel(fp, "PPar")),
            "the element send is on the @\"ac:{{fingerprint}}/{{op}}\" carrier channel"
        );
        let elem = elist_body(&send.data[0]);
        assert_eq!(
            elem.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the fixed element head is the Wrap reflection tag"
        );
        assert_eq!(
            boundvar_index(&elem.ps[2]),
            Some(2),
            "x = element BoundVar(2) (the AC receiver's k+2-formal frame, k=1); E-2-D marker at ps[1]"
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
            Some(ac_soup_channel(fp, "PPar")),
            "the fixed element rides the INV-S6-scoped @\"ac:{{fingerprint}}/PPar\" carrier"
        );
        let elem = elist_body(&soup.sends[0].data[0]);
        assert_eq!(
            elem.ps[0],
            GPrivateBuilder::new_par_from_string(format!("mettail.term.{fp}.Wrap")),
            "the transformed element is Wrap(...)"
        );
        assert_eq!(
            boundvar_index(&elem.ps[2]),
            Some(2),
            "x = element BoundVar(2) (E-2-D marker at ps[1])"
        );
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
        assert_eq!(rhs.ps.len(), 3, "Wrap tag + E-2-D marker + the element σ");
        assert_eq!(
            boundvar_index(&rhs.ps[2]),
            Some(2),
            "element x = BoundVar(2) (the AC frame; E-2-D marker at ps[1])"
        );

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
    fn resolve_collection_type_falls_back_to_colons_declared_grammar_items() {
        // A-S5.3 (leg ii): the production `Ambient` declares `PPar` through the old-BNFC `::=`
        // form, so `term_context` is None and the kind must resolve from the FIRST
        // `GrammarItem::Collection` in `rule.items` — the items fallback that admits the real
        // Ambient AC family (the term-context scan stays primary, so the admitted corpus is
        // byte-identical).
        let def: LanguageDef = syn::parse_str(AC_COLONS_FRAGMENT).expect("the ::= fragment parses");
        let ppar = def
            .terms
            .iter()
            .find(|rule| rule.label == "PPar")
            .expect("PPar is declared");
        assert!(
            ppar.term_context.is_none(),
            "a `::=`-declared collection rule carries NO term-context params"
        );
        assert_eq!(
            resolve_constructor_collection_type(&def, "PPar"),
            Some(CollectionType::HashBag),
            "the HashBag kind resolves from the grammar items (the A-S5.3 fallback)"
        );
        // The same resolution reaches the AC recognizers through the LHS-keyed entry point the
        // un-skip chain uses (a parser-produced LHS collection carries `coll_type: None`).
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
            "a parser-None LHS collection resolves through the items fallback too"
        );
    }

    #[test]
    fn resolve_collection_type_stays_none_for_colons_rules_without_a_collection() {
        // A-S5.3 (leg ii): a `::=`-declared NON-collection rule must stay `None` under the items
        // fallback — never mis-classified as a HashBag (the resolver's fail-closed contract is
        // syntax-form-independent).
        let def: LanguageDef = syn::parse_str(AC_COLONS_FRAGMENT).expect("the ::= fragment parses");
        assert_eq!(
            resolve_constructor_collection_type(&def, "Wrap"),
            None,
            "a `::=` rule with no grammar-item collection resolves to None"
        );
        assert_eq!(
            resolve_constructor_collection_type(&def, "PZero"),
            None,
            "a `::=` terminal-only rule resolves to None"
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
            channel.starts_with(&format!("sa:{}/pattern/", plan.definition_fingerprint())),
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

        let join = contextual_join_receiver_par(context_rhs.clone(), std::slice::from_ref(&c_ctx));
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
            boundvar_index(&list.ps[2]),
            Some(1),
            "the reduced hole T sits at BoundVar(rhs_var_index(1,0)) = BoundVar(1) (E-2-D marker at ps[1])"
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
            boundvar_index(&list.ps[2]),
            Some(2),
            "hole T0 at BoundVar(n - 0) = BoundVar(2) (E-2-D marker at ps[1])"
        );
        assert_eq!(
            boundvar_index(&list.ps[3]),
            Some(1),
            "hole T1 at BoundVar(n - 1) = BoundVar(1) (E-2-D marker at ps[1] shifts children +1)"
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
    fn contextual_congruence_only_failure_is_recorded_exempt_and_installs() {
        // A-S5.1 (leg i): a congruence-ONLY rewrite whose flat join image FAILS
        // (the Lambda `AppCongL` shape — the passenger `N` is no premise target,
        // so the RHS reflect dangles) is the RECORDED install-exempt disposition:
        // no diagnostic pushed, the install admits, and the exemption (with its
        // failed family) surfaces via `congruence_exempt_rules`.
        let (lowered, id) = lower_single_rewrite_full(RewriteRule {
            name: ident("CongL"),
            type_context: Vec::new(),
            premises: vec![Premise::Congruence { source: ident("M0"), target: ident("M1") }],
            left: apply("Pair", vec![var_pattern("M0"), var_pattern("N")]),
            right: apply("Pair", vec![var_pattern("M1"), var_pattern("N")]),
            is_auto_injected: false,
        });
        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == id)
            .expect("CongL must be lowered");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::CongruenceExemptRewrite {
                rule_id: id.clone(),
                family: UnsupportedFamily::DanglingRhsVariable,
            },
            "a congruence-only join failure is exempt, retaining the failed family as the WHY"
        );
        assert!(
            lowered.errors().is_empty(),
            "an exemption pushes no fail-closed diagnostic: {:?}",
            lowered.errors()
        );
        assert_eq!(
            lowered.congruence_exempt_rules(),
            vec![(id.as_str(), &UnsupportedFamily::DanglingRhsVariable)],
            "the exemption is on the record — never silent"
        );
        lowered
            .installed_program_par()
            .expect("a recorded congruence exemption never blocks the install");
    }

    #[test]
    fn contextual_mixed_premise_failure_still_fails_install_closed() {
        // A-S5.1 hardening (`congruence_only_premises` = all + non-empty, never
        // `any`): a MIXED-premise congruence rewrite — one congruence hole plus a
        // FRESHNESS side condition — is NEVER exempt: the freshness premise has
        // no join slot, and exempting the rule would silently drop it. The
        // fail-closed behavior is byte-identical to pre-A-S5.1.
        let (lowered, id) = lower_single_rewrite_full(RewriteRule {
            name: ident("FreshGuardedCong"),
            type_context: Vec::new(),
            premises: vec![
                Premise::Congruence { source: ident("S"), target: ident("T") },
                Premise::Freshness(FreshnessCondition {
                    var: ident("x"),
                    term: FreshnessTarget::Var(ident("S")),
                }),
            ],
            left: apply("Wrap", vec![var_pattern("S")]),
            right: apply("Wrap", vec![var_pattern("T")]),
            is_auto_injected: false,
        });
        let rule = lowered
            .rules()
            .iter()
            .find(|rule| rule.rule_id() == id)
            .expect("FreshGuardedCong must be lowered");
        assert_eq!(
            *rule,
            RhoNetLoweredRule::Unsupported {
                rule_id: id.clone(),
                family: UnsupportedFamily::NonCongruenceSideCondition,
            },
            "mixed premises stay fail-closed Unsupported — never exempt"
        );
        assert!(
            lowered.congruence_exempt_rules().is_empty(),
            "a mixed-premise rewrite must never appear in the exemption record"
        );
        assert_eq!(
            lowered.errors().to_vec(),
            vec![RhoNetLoweringError::UnsupportedFamily {
                rule_id: id.clone(),
                family: UnsupportedFamily::NonCongruenceSideCondition,
            }],
            "the fail-closed diagnostic is recorded"
        );
        match lowered.installed_program_par() {
            Err(RhoNetInstallError::LoweringErrors(errors)) => {
                assert_eq!(errors.len(), 1, "the mixed-premise failure blocks the install");
            },
            other => panic!("expected LoweringErrors, got {other:?}"),
        }
    }

    #[test]
    fn swap_demo_records_zero_exemptions_and_installs_deterministically() {
        // A-S5.1 commit-boundary evidence (SwapDemo byte-identical): a language
        // whose every rewrite MATERIALIZES is untouched by the exemption seam —
        // zero `congruence_exempt_rules`, the install stays Ok, and two
        // independent compilations through the changed path produce EQUAL
        // installed `Par`s (prost message equality ⇒ identical encodings).
        // Subject: the module's canonical `SWAP_DEMO_FRAGMENT` (the real SwapDemo).
        let compile = || {
            let def = syn::parse_str::<LanguageDef>(SWAP_DEMO_FRAGMENT)
                .expect("the SwapDemo fragment parses");
            let lowering = lower_language_def(&def);
            let program = RhoNetProgram::from_language_def(&def, &lowering);
            program.lower_to_par(&def, &lowering)
        };
        let first = compile();
        assert!(
            first.congruence_exempt_rules().is_empty(),
            "SwapDemo has no congruence rewrite — nothing to exempt"
        );
        assert!(first.errors().is_empty(), "SwapDemo lowers cleanly: {:?}", first.errors());
        let first_par = first
            .installed_program_par()
            .expect("the SwapDemo σ-receiver program installs");
        let second_par = compile()
            .installed_program_par()
            .expect("the SwapDemo σ-receiver program installs again");
        assert_eq!(
            first_par, second_par,
            "the installed program is value-deterministic through the A-S5.1 path"
        );
        assert!(!first_par.receives.is_empty(), "the SwapStep σ-receiver is installed");
    }

    /// The BiCongDemo shape (mirrors `languages/tests/definitions/bicongdemo.rs` — `NodeCong`
    /// carries TWO congruence premises): the red-team F13 regression pin for the
    /// `any→all` hardening.
    const BICONG_DEMO_FRAGMENT: &str = r#"
        name: RhoNetBiCongFrag,
        types { Proc },
        terms {
            A . |- "A" : Proc ;
            B . |- "B" : Proc ;
            C . |- "C" : Proc ;
            D . |- "D" : Proc ;
            Pair . x:Proc, y:Proc |- "pair" "(" x "," y ")" : Proc ;
            Swap . x:Proc, y:Proc |- "swap" "(" x "," y ")" : Proc ;
            Node . x:Proc, y:Proc |- "node" "(" x "," y ")" : Proc ;
        },
        equations {},
        rewrites {
            Flip . |- (Swap x y) ~> (Pair y x) ;
            NodeCong . | S0 ~> T0, S1 ~> T1 |- (Node S0 S1) ~> (Node T0 T1) ;
        }
    "#;

    #[test]
    fn bicong_two_congruence_premises_stay_exempt_under_all_and_materialize() {
        // Red-team F13 pin: `bicongdemo`'s `NodeCong` is the ONLY bundled
        // multi-premise rewrite — two congruence premises. Under the hardened
        // `congruence_only_premises` (all + non-empty) it remains in the static
        // gate's exemption basis, AND (pinning reality, not the design's guess)
        // its lowering still MATERIALIZES the 2-ary contextual join — so the
        // exempt disposition never triggers, no exemption is recorded, and the
        // program installs exactly as before A-S5.1.
        use crate::rho_net_ruleset::{compile_in_rho_matching_ruleset, in_rho_static_gate};

        let def = syn::parse_str::<LanguageDef>(BICONG_DEMO_FRAGMENT)
            .expect("the BiCongDemo fragment parses");
        let node_cong = def
            .rewrites
            .iter()
            .find(|rewrite| rewrite.name == "NodeCong")
            .expect("NodeCong is a fragment rewrite");
        assert_eq!(node_cong.premises.len(), 2, "NodeCong carries two premises");
        assert!(
            congruence_only_premises(&node_cong.premises),
            "two congruence premises remain exempt under all(..) + non-empty"
        );

        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let lowered = program.lower_to_par(&def, &lowering);
        assert!(
            lowered.rules().iter().any(|rule| matches!(
                rule,
                RhoNetLoweredRule::ContextualRewrite { rule_id, .. }
                    if rule_id == "rule:rewrite:1:NodeCong"
            )),
            "NodeCong MATERIALIZES the 2-ary contextual join (reality pin)"
        );
        assert!(
            lowered.congruence_exempt_rules().is_empty(),
            "a materialized congruence rewrite records no exemption"
        );
        assert!(lowered.errors().is_empty(), "BiCongDemo lowers cleanly: {:?}", lowered.errors());
        lowered
            .installed_program_par()
            .expect("BiCongDemo installs — gate admission and install are unchanged");

        // And the static capability gate still admits under the hardened predicate.
        let ruleset = compile_in_rho_matching_ruleset(&def);
        assert_eq!(
            in_rho_static_gate(&ruleset, &def),
            Ok(()),
            "the hardened exemption basis leaves the BiCongDemo gate admission unchanged"
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
