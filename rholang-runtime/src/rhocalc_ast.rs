//! AST-first lowering from MeTTaIL's `rhocalc` terms to normalized Rholang `Par`.
//!
//! This module is an oracle/integration bridge for the Rho machine backend. It
//! consumes MeTTaIL/WPDA-produced `rhocalc` AST values and constructs
//! `rhoapi::Par` directly. Rholang-looking strings in docs/tests are reader
//! annotations only; they are never parsed on this execution path.

use std::any::Any;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::fold_contract::{fold_channel, FoldKind, FoldSpec};
use mettail_languages::rhocalc::{
    Bag, BigInt, BigRat, Bool, Bytes, Fixed, Float, ForRow, InputBind, Int, List, Map, Name,
    Pathmap, Proc, RhoCalcLanguage, RhoCalcTerm, RhoCalcTermInner, Set, Str, UInt32,
};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reflect_flt_construction, reflect_flt_pattern,
    suggest_rejected_rule_dispositions, EmptyFltResolver, FltHole, FltPatternReflection,
    FltResolve, GroundTerm, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence,
};
use mettail_runtime::{
    Binder, FltNode, FramedSemanticKeyHasher, FreeVar, Language, LanguageMetadata, OrdVar,
    RuntimeDovetailRunReport, Term, TermType, Var, VarTypeInfo, WeightedRewriteSeed,
    WeightedSeedId,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    EAnd, EDiv, EEq, EGt, EGte, ELt, ELte, EMethod, EMinus, EMod, EMult, ENeg, ENeq, ENot, EOr,
    EPlus, EPlusPlus, Expr, Par, ReceiveBind,
};
use models::create_bit_vector;
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_eset_par, new_freevar_par, new_gbigint_expr,
    new_gbigrat_expr, new_gbool_par, new_gdouble_expr, new_gfixedpoint_expr, new_gint_par,
    new_gstring_par, new_key_value_pair, new_new_par, new_receive_par, new_send_par,
    new_wildcard_par, union,
};

const FREE_NAME_PREFIX: &str = "mtl:";
const FREE_PROC_OUTPUT: &str = "mtl#out";

/// L9-6: the read-only lowering environment — the de-Bruijn binder map PLUS the
/// FLT resolver ([`FltResolve`]). The resolver rides INSIDE the env (as an
/// `Arc<dyn FltResolve>`, so `BoundEnv` carries no lifetime) precisely so it
/// threads through the entire recursive lowering without touching a single one of
/// the ~90 `lower_*` call sites — every one already passes `&BoundEnv`.
/// [`BoundEnv::new`] installs the EMPTY resolver ([`EmptyFltResolver`]), so an
/// FLT-free lowering is byte-identical to the pre-L9-6 pipeline; the resolver is
/// consulted ONLY by the `PFlt` arm (L9-6b).
#[derive(Clone)]
struct BoundEnv {
    binders: HashMap<FreeVar<String>, usize>,
    /// L9-6b: FLT hole name → de-Bruijn level. A `${name}` hole captured by an FLT
    /// receive pattern ([`reflect_flt_pattern`]) is a receive binder, but — unlike
    /// a RhoCalc `PVar` binder — it is a STRING metavar, not a moniker `FreeVar`
    /// shared with the continuation's `name` reference (whose `FreeVar` carries a
    /// distinct `unique_id`). So the continuation's reference resolves by NAME
    /// through this map (`lower_proc_var`/`lower_name_var` fall back to it when the
    /// `FreeVar`-keyed lookup misses), and a construction-position `${name}` reads
    /// its fill's `^bound` level from here too.
    hole_binders: HashMap<String, usize>,
    resolver: Arc<dyn FltResolve>,
}

impl BoundEnv {
    /// The empty environment with the empty (no-guest) resolver — the
    /// zero-behavior-change default used by every existing lowering entry point.
    fn new() -> Self {
        BoundEnv {
            binders: HashMap::new(),
            hole_binders: HashMap::new(),
            resolver: Arc::new(EmptyFltResolver),
        }
    }

    /// The empty binder environment carrying `resolver` — the L9-6b entry that
    /// installs a populated FLT registry so `PFlt` arms can elaborate.
    fn with_resolver(resolver: Arc<dyn FltResolve>) -> Self {
        BoundEnv { binders: HashMap::new(), hole_binders: HashMap::new(), resolver }
    }

    /// L9-6b: the de-Bruijn level a `${name}` FLT hole binds to (via the receive
    /// pattern that introduced it), or `None` when `name` names no FLT hole.
    fn flt_hole_level(&self, name: &str) -> Option<usize> {
        self.hole_binders.get(name).copied()
    }

    /// L9-6b/#14: derive the continuation scope of a receive whose `slots` are its
    /// binders IN BIND ORDER — each either a moniker [`Binder`] (a `PVar` binder) or a
    /// name-keyed FLT hole ([`ReceiveSlot`]). Existing binder/hole levels shift up by
    /// the slot width; the new slot at formal index `i` binds at de-Bruijn level
    /// `width - 1 - i` — the SAME convention [`extend_env`] uses for moniker joins, so
    /// an FLT hole and a moniker binder that co-occur in a `&`-join share one coherent
    /// level space (fixes the L9-6b `&`-join fail-closed).
    fn extend_slots(&self, slots: &[ReceiveSlot]) -> BoundEnv {
        let width = slots.len();
        let mut binders = self
            .binders
            .iter()
            .map(|(var, index)| (var.clone(), index + width))
            .collect::<HashMap<FreeVar<String>, usize>>();
        let mut hole_binders = self
            .hole_binders
            .iter()
            .map(|(name, index)| (name.clone(), index + width))
            .collect::<HashMap<String, usize>>();
        for (formal_index, slot) in slots.iter().enumerate() {
            let level = width - 1 - formal_index;
            match slot {
                ReceiveSlot::Moniker(binder) => {
                    binders.insert(binder.0.clone(), level);
                },
                ReceiveSlot::Hole(name) => {
                    hole_binders.insert(name.clone(), level);
                },
            }
        }
        BoundEnv { binders, hole_binders, resolver: Arc::clone(&self.resolver) }
    }
}

/// #14: one binder slot of a receive, IN BIND ORDER — a moniker `PVar` binder or a
/// name-keyed FLT hole. Unifying the two into a single ordered list lets an FLT hole
/// and a moniker binder co-occur in a `&`-join with one coherent de-Bruijn numbering.
enum ReceiveSlot {
    Moniker(Binder<String>),
    Hole(String),
}

/// Reconstruct the REAL `RhoCalcLanguage` augmented `LanguageDef` from the
/// generated metadata's `definition_source()`.
///
/// The generated `RhoCalcLanguage` is both the parser/AST model AND the source
/// of identity here: the dynamic Rho backend plan is built from this exact
/// augmented definition (composition + auto-injection), so its
/// `definition_fingerprint()` equals `RhoCalcLanguage.metadata().definition_fingerprint()`.
/// The runtime wrapper therefore installs on the real RhoCalc identity and
/// still rejects plans for any other language — without the prior
/// fingerprint-spoofing minimal fragment.
///
/// RhoCalc is a standalone language (no `extends`/`includes`/`mixins`), so the
/// reconstruction is exact (see [`reconstruct_language_def`]).
pub fn rhocalc_ast_runtime_def() -> mettail_ast::language::LanguageDef {
    let source = RhoCalcLanguage
        .metadata()
        .definition_source()
        .expect("generated RhoCalcLanguage must expose its definition_source");
    mettail_rholang_codegen::reconstruct_language_def(source)
        .expect("RhoCalcLanguage definition_source must reconstruct as a LanguageDef")
}

/// Invocation mapper used by the RhoCalc runtime-backed wrapper helpers.
pub type RhocalcInvocationMapper =
    Box<dyn Fn(&dyn Term) -> Result<crate::backend::RhoMachineInvocation, String> + Send + Sync>;

/// Rho-default wrapper type used by the RhoCalc helper constructors.
pub type RhocalcRuntimeBackedLanguage =
    crate::backend::RhoRuntimeBackedLanguage<RhocalcAstRuntimeLanguage, RhocalcInvocationMapper>;

/// Fallible RhoCalc runtime-backed wrapper construction result.
pub type RhocalcRuntimeBackedLanguageResult =
    Result<RhocalcRuntimeBackedLanguage, crate::backend::RhoRuntimeBackedLanguageError>;

/// Fallible rhocalc-to-Rholang-AST lowering error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhocalcAstLowerError {
    ExpectedRhoCalcTerm,
    ExpectedProcTerm,
    UnsupportedProc(&'static str),
    UnsupportedName(&'static str),
    FreeVarWithoutName,
    EmptyInputJoin,
    InputArityMismatch { names: usize, binders: usize },
    /// L9-6: a `PFlt` node's `tag` resolves to no guest in the installed
    /// [`FltResolve`] registry (the empty-resolver default, or an unregistered
    /// tag). A `PFlt` cannot elaborate without its guest reflector — fail closed.
    UnresolvedFltTag(String),
    /// L9-6: the resolved guest exposes no `definition_fingerprint` (a guest with
    /// no lowered/planned identity), so its reflected tags cannot be minted.
    FltGuestHasNoFingerprint(String),
    /// L9-6: the guest reflector failed to parse-and-reflect the FLT body, or the
    /// pattern/construction admission gate rejected it (a category mismatch, a
    /// malformed hole envelope, or an unfilled construction hole).
    FltReflect(String),
}

/// RhoCalc language adapter for the AST-first Rho machine runtime path.
///
/// This adapter delegates parsing, formatting, normalization, environment
/// handling, type inference, AND metadata (including the definition
/// fingerprint) to the generated `RhoCalcLanguage`. It exposes the real RhoCalc
/// identity — the dynamic Rho backend plan is built from the reconstructed real
/// `LanguageDef` ([`rhocalc_ast_runtime_def`]), so installation matches on the
/// genuine fingerprint rather than a reduced fragment. It does not forward the
/// generated Ascent oracle; raw `run_ascent` remains fail-closed and reference
/// comparison stays behind explicit oracle features.
pub struct RhocalcAstRuntimeLanguage;

impl Language for RhocalcAstRuntimeLanguage {
    fn name(&self) -> &'static str {
        RhoCalcLanguage.name()
    }

    fn metadata(&self) -> &'static dyn LanguageMetadata {
        // Real generated RhoCalc metadata — including the real
        // `definition_fingerprint()` and `definition_source()`. No spoofing
        // shim: the dynamic backend plan is built from the reconstructed real
        // definition, so the fingerprints match by construction.
        RhoCalcLanguage.metadata()
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        RhoCalcLanguage.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        RhoCalcLanguage.parse_term_for_env(input)
    }

    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        RhoCalcLanguage.parse_term_with_weighted_seed_ids(input)
    }

    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        RhoCalcLanguage.parse_term_with_weighted_rewrite_seeds(input)
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        RhoCalcLanguage.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        RhoCalcLanguage.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        RhoCalcLanguage.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        RhoCalcLanguage.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        RhoCalcLanguage.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        RhoCalcLanguage.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        RhoCalcLanguage.clear_env(env)
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        RhoCalcLanguage.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        RhoCalcLanguage.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        RhoCalcLanguage.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        RhoCalcLanguage.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        RhoCalcLanguage.is_env_empty(env)
    }

    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        RhoCalcLanguage.get_env_term(env, name)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        RhoCalcLanguage.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        RhoCalcLanguage.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        RhoCalcLanguage.infer_var_type(term, var_name)
    }
}

fn rhocalc_invocation_stage(
    mapper: RhocalcInvocationMapper,
) -> Result<
    crate::backend::RhoInvocationCompilerStage<RhocalcInvocationMapper>,
    crate::backend::RhoRuntimeBackedLanguageError,
> {
    let language_name = RhocalcAstRuntimeLanguage.name();
    let fingerprint = RhocalcAstRuntimeLanguage
        .metadata()
        .definition_fingerprint()
        .ok_or_else(|| {
            crate::backend::RhoRuntimeBackedLanguageError::MissingLanguageDefinitionFingerprint {
                language_name: language_name.to_string(),
            }
        })?;
    Ok(crate::backend::RhoInvocationCompilerStage::new(fingerprint, mapper))
}

/// Build a Rho runtime invocation that executes a parsed `RhoCalcLanguage`
/// process and observes strings from `out_channel`.
pub fn rhocalc_observe_strings_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveStrings {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RhoCalcLanguage`
/// process and observes integers from `out_channel`.
pub fn rhocalc_observe_ints_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveInts {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RhoCalcLanguage`
/// process and observes closed Rho ground values from `out_channel`.
pub fn rhocalc_observe_values_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveRuntimeValues {
        call,
        out_channel: out_channel.into(),
    })
}

/// Wrap RhoCalc as an AST-first Rho-default language whose default report
/// observes strings on `out_channel`.
pub fn rho_runtime_backed_rhocalc_strings(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RhocalcRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RhocalcInvocationMapper =
        Box::new(move |term| rhocalc_observe_strings_invocation(term, out_channel.clone()));
    let invocation = rhocalc_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RhocalcAstRuntimeLanguage, backend, invocation)
}

/// Wrap RhoCalc as an AST-first Rho-default language whose default report
/// observes integers on `out_channel`.
pub fn rho_runtime_backed_rhocalc_ints(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RhocalcRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RhocalcInvocationMapper =
        Box::new(move |term| rhocalc_observe_ints_invocation(term, out_channel.clone()));
    let invocation = rhocalc_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RhocalcAstRuntimeLanguage, backend, invocation)
}

/// Wrap RhoCalc as an AST-first Rho-default language whose default report
/// observes closed Rho ground values on `out_channel`.
pub fn rho_runtime_backed_rhocalc_values(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RhocalcRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RhocalcInvocationMapper =
        Box::new(move |term| rhocalc_observe_values_invocation(term, out_channel.clone()));
    let invocation = rhocalc_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RhocalcAstRuntimeLanguage, backend, invocation)
}

/// Coverage requirements derived from the language-aware rejected-rule classifier.
/// Structural constructors are covered by generated Rho AST contracts; native/eval and unsupported
/// scalar operators are covered by Rho-native system-process rules. Labels are de-duplicated because
/// the same label can recur across categories and `RhoCoverageEvidence` forbids duplicate
/// dispositions. (Mirrors the `rho_rhocalc_ast` test helper, promoted for the production wrapper
/// builder.)
fn rho_default_coverage_requirements(
    def: &mettail_ast::language::LanguageDef,
) -> RhoDefaultBackendRequirements {
    let lowering = lower_language_def(def);
    let dispositions = suggest_rejected_rule_dispositions(def, &lowering);
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    }
}

/// Build the RhoCalc [`crate::backend::PlannedRhoBackend`] from the REAL reconstructed RhoCalc
/// augmented `LanguageDef` ([`rhocalc_ast_runtime_def`]) — so its fingerprint equals the generated
/// `RhoCalcLanguage` identity and the wrapper installs on the real RhoCalc.
pub fn rhocalc_planned_rho_backend() -> Result<crate::backend::PlannedRhoBackend, String> {
    let def = rhocalc_ast_runtime_def();
    let plan = plan_rho_default_backend(&def, rho_default_coverage_requirements(&def))
        .map_err(|err| format!("RhoCalc Rho-default backend planning failed: {err:?}"))?;
    Ok(crate::backend::PlannedRhoBackend::from_plan(plan))
}

/// Bounds for the RhoCalc Dovetail D-stage (mirror the generated `dovetail_compiler_stage`).
const RHOCALC_DOVETAIL_MAX_ITERS: usize = 64;
const RHOCALC_DOVETAIL_MAX_NODES: usize = 1_000_000;

/// The Dovetail D-stage report producer for RhoCalc (the bare fn
/// [`crate::backend::install_dovetail_rho_runtime_backend`] wraps): saturate the term to a runtime
/// report — native folds reduce; COMM/`new` remain Rho-machine work for the invocation stage.
fn rhocalc_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    RhoCalcLanguage::dovetail_report_for(
        term,
        RHOCALC_DOVETAIL_MAX_ITERS,
        RHOCALC_DOVETAIL_MAX_NODES,
    )
}

/// The step-only Dovetail producer for RhoCalc — the REPL `step` navigable one-step REWRITE-step
/// graph (Increment 4): each node is a whole program state in source syntax, each edge a one-step
/// rewrite successor (structural `Exec`/`QuoteDrop`/`Extrude` + folds; COMM is not a Dovetail
/// structural rewrite), and a node with no successor is a normal form. Reached only via the `step` path
/// (`Language::run_step_backend_report`); production `exec` uses `rhocalc_dovetail_report`.
fn rhocalc_dovetail_step_graph(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    RhoCalcLanguage::dovetail_step_graph(
        term,
        RHOCALC_DOVETAIL_MAX_ITERS,
        RHOCALC_DOVETAIL_MAX_NODES,
    )
}

/// The RhoCalc F-stage lowering shared by the report-free compile and the report-carrying
/// fallback.
///
/// A-S4 (lowering purity): the lowering is PURE structural translation — the host computes no
/// values. COMM (send/receive/`new`) lowers directly; arithmetic/comparison/logic lower to the
/// machine's own metered `Expr` algebra (`EPlus`/`EMinus`/…); width/precision folds lift into
/// fold-contract trampolines the MACHINE drives at COMM time (ground operands included — the
/// former Tier-1 in-place `try_eval` fold is deleted); a construct with no machine algebra fails
/// CLOSED with the typed lowering error naming it. The pre-A-S4 E2 fallback (fold-normalize via
/// `dovetail_normal_term`, then lower the host-computed normal form) is DELETED: it was the last
/// host-evaluation lane on the admitted exec path.
///
/// Pure VALUE terms (no machine effects — `1 + 2`, `int(5,8)`, `"hi"`) are wrapped as
/// `@("OUT")!(term)` BEFORE lowering ([`wrap_pure_value_term`]), so the observable result is
/// produced by RSpace and any fold trampoline lifts AROUND the observation send (the machine
/// computes, then sends the result to `OUT`). For a value term with no fold this produces the
/// byte-identical `Par` the post-lowering [`observe_pure_value_call`] wrap produced (the wrap
/// commutes with lowering: `lower(@("OUT")!(v)) == observe_pure_value_call(lower(v), "OUT")`),
/// which remains in place for the multi-alternative and lowers-to-pure cases.
fn rhocalc_backend_invocation(
    term: &dyn Term,
    out_channel: &str,
) -> Result<crate::backend::RhoBackendInvocation, String> {
    let call = lower_rhocalc_exec_term(term, out_channel).map_err(|err| {
        format!(
            "RhoCalc term could not be lowered to the Rho machine \
             (A-S4 fail-closed lowering; no host fold-normalization fallback): {err:?}"
        )
    })?;
    let call = if call_has_runtime_effects(&call) {
        call
    } else {
        observe_pure_value_call(call, out_channel)
    };
    Ok(crate::backend::RhoBackendInvocation::from(
        crate::backend::RhoMachineInvocation::RunWithCallAndObserveRuntimeValues {
            call,
            out_channel: out_channel.to_string(),
        },
    ))
}

/// Lower a term for EXEC, wrapping a single-alternative pure VALUE term as `@(out_channel)!(term)`
/// at the AST level first — see [`rhocalc_backend_invocation`]. Multi-alternative (ambiguous)
/// terms keep the historical par-level wrap ([`observe_pure_value_call`], applied by the caller):
/// per-alternative AST wrapping would change the observation shape (one send per alternative
/// instead of one send of the union), so it is not applied there.
fn lower_rhocalc_exec_term(
    term: &dyn Term,
    out_channel: &str,
) -> Result<Par, RhocalcAstLowerError> {
    let alternatives = rhocalc_proc_alternatives_from_term(term)?;
    if let [only] = alternatives.as_slice() {
        if !proc_has_machine_effects(only) {
            let wrapped = wrap_pure_value_term(only, out_channel);
            return lower_proc_alternatives([&wrapped]);
        }
    } else if alternatives
        .iter()
        .any(|alt| !proc_has_machine_effects(alt) && find_fold(alt).is_some())
    {
        // An AMBIGUOUS pure-value alternative containing a fold: the historical par-level wrap
        // observes the union par as one value, but a lifted fold makes the alternative
        // EFFECTFUL, so its trampolined result would rest in the space unobserved — a silent
        // value drop. Fail closed instead (honest, typed) until an ambiguous-value observation
        // shape is designed.
        return Err(RhocalcAstLowerError::UnsupportedProc(
            "ambiguous pure-value term containing a width/precision fold",
        ));
    }
    lower_proc_alternatives(alternatives)
}

/// `@(out_channel)!(term)` at the AST level: the value-observation input formation for a pure
/// value term. Uses the same channel construction the lowered [`observe_pure_value_call`] targets
/// (`NQuote(CastStr(out_channel))` lowers to the identical `GString` channel `Par`).
fn wrap_pure_value_term(value: &Proc, out_channel: &str) -> Proc {
    Proc::POutput(
        Arc::new(Name::NQuote(Arc::new(Proc::CastStr(Arc::new(Str::StringLit(
            out_channel.to_string(),
        )))))),
        Arc::new(value.clone()),
    )
}

/// Conservative AST-level effect analysis for the exec value-wrap: does lowering this proc yield
/// top-level machine effects (sends/receives/news)? Mirrors [`call_has_runtime_effects`] over the
/// AST — values (casts, literals, collections, arithmetic/comparison/logic exprs, folds) report
/// `false`; process constructs report `true`. Send sugar is desugared first so every send shape
/// is seen as a send. A free proc variable lowers to an `mtl#out` send, hence `true`.
fn proc_has_machine_effects(proc: &Proc) -> bool {
    if let Some(desugared) = desugar_send_node(proc) {
        return proc_has_machine_effects(&desugared);
    }
    match proc {
        Proc::POutput(..)
        | Proc::PPersistOutput(..)
        | Proc::POutputShort(..)
        | Proc::PPersistOutputShort(..)
        | Proc::PForUser(..)
        | Proc::CommWhere(..)
        | Proc::PNew(..)
        | Proc::PVar(..) => true,
        Proc::PPar(parts) => parts.iter_elements().any(proc_has_machine_effects),
        Proc::PParInfix(left, right) => {
            proc_has_machine_effects(left.as_ref()) || proc_has_machine_effects(right.as_ref())
        },
        Proc::GuardThen(cond, body) => {
            proc_has_machine_effects(cond.as_ref()) || proc_has_machine_effects(body.as_ref())
        },
        // `*(@(P))` inlines `P`; effects ride inside. `*(x)` / `*(@Nil)` lower to value pars.
        Proc::PDrop(name) => name_has_machine_effects(name.as_ref()),
        _ => false,
    }
}

fn name_has_machine_effects(name: &Name) -> bool {
    match name {
        Name::NQuote(proc) | Name::NQuoteShort(proc) => proc_has_machine_effects(proc.as_ref()),
        Name::NParen(inner) => name_has_machine_effects(inner.as_ref()),
        _ => false,
    }
}

/// Two-stage checked-Dovetail+Rho RhoCalc backend — the production default for the REPL `exec` of
/// RhoCalc.
///
/// One-way pipeline (no bidirectional bridge; see
/// `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`): the **F-stage**
/// lowers the term to a normalized `Par` ([`rhocalc_backend_invocation`]: PURE structural AST
/// lowering — A-S4 deleted the E2 `dovetail_normal_term` fold-normalization fallback, the last
/// host-evaluation lane) and routes every lowerable result through the real Rho machine. A term
/// carrying a send/receive/`new` runs as that process; arithmetic runs as the machine's metered
/// `Expr`s; width/precision folds run as machine-driven fold-contract COMMs. A closed pure
/// value/fold with no Rho effects is wrapped as `@"OUT"!(value)` so the observable result is
/// still produced by RSpace. An un-lowerable construct fails CLOSED with the typed lowering
/// error naming it.
///
/// A-S2 (D-stage demotion): the F-stage never read the Dovetail report, so the report-free
/// compile (`F2`) IS the same lowering; an admitted exec runs with ZERO D-stage. A lowering
/// failure defers ([`crate::backend::RhoInvocationDeferral::GateReject`]) to the LAZY D-stage:
/// the wrapper builds the checked report (surfacing the eager pipeline's D-stage error text for
/// budget-blown/malformed reports) and re-runs the SAME lowering as the report-carrying
/// fallback — whose error message is then the eager pipeline's F-stage message, byte-identical.
pub fn dovetail_rho_backed_rhocalc(
    out_channel: impl Into<String>,
) -> Result<Box<dyn Language>, String> {
    let out_channel = out_channel.into();
    let backend = rhocalc_planned_rho_backend()?;
    let invocation_free = {
        let out_channel = out_channel.clone();
        move |term: &dyn Term| -> Result<
            crate::backend::RhoBackendInvocation,
            crate::backend::RhoInvocationDeferral,
        > {
            rhocalc_backend_invocation(term, &out_channel)
                .map_err(|detail| crate::backend::RhoInvocationDeferral::GateReject { detail })
        }
    };
    let invocation = move |term: &dyn Term,
                           _report: &RuntimeDovetailRunReport|
          -> Result<crate::backend::RhoBackendInvocation, String> {
        rhocalc_backend_invocation(term, &out_channel)
    };
    let language = crate::backend::install_dovetail_rho_runtime_backend_lazy(
        RhocalcAstRuntimeLanguage,
        backend,
        rhocalc_dovetail_report,
        rhocalc_dovetail_step_graph,
        invocation_free,
        invocation,
    )
    .map_err(|err| format!("RhoCalc Dovetail+Rho backend install failed: {err:?}"))?;
    Ok(Box::new(language))
}

fn call_has_runtime_effects(call: &Par) -> bool {
    !call.sends.is_empty() || !call.receives.is_empty() || !call.news.is_empty()
}

fn observe_pure_value_call(value: Par, out_channel: &str) -> Par {
    send_par(new_gstring_par(out_channel.to_string(), Vec::new(), false), vec![value])
}

/// Lower a rhocalc process into normalized Rholang `Par`.
///
/// A-S4: width/precision folds ANYWHERE in the process (top level, send payloads, receive
/// bodies, `new` bodies — ground or COMM-held operands alike) lift into fold-contract
/// trampolines the machine drives; the host computes no fold values. Callers that execute the
/// result must register the recorded fold `Definition`s (the `clear_held_fold_sites` /
/// `take_held_fold_sites` bracket, or [`lower_rhocalc_term_with_folds`]).
pub fn lower_rhocalc_proc(proc: &Proc) -> Result<Par, RhocalcAstLowerError> {
    lower_body_lifting_folds(proc, &BoundEnv::new())
}

/// L9-6b: lower a RhoCalc `Proc` under an installed FLT resolver, so `PFlt` nodes
/// elaborate (construction position → [`reflect_flt_construction`]; receive-pattern
/// position → [`reflect_flt_pattern`]) via the guest each opener `tag` selects. With
/// the empty ([`EmptyFltResolver`]) default this is byte-identical to
/// [`lower_rhocalc_proc`]; a populated [`mettail_rholang_codegen::FltRegistry`]
/// (`"lam"` → `LambdaLanguage`, …) is what drives the Foreign-Exchange demo from
/// source.
pub fn lower_rhocalc_proc_with_resolver(
    proc: &Proc,
    resolver: Arc<dyn FltResolve>,
) -> Result<Par, RhocalcAstLowerError> {
    lower_body_lifting_folds(proc, &BoundEnv::with_resolver(resolver))
}

/// Lower a parsed `RhoCalcLanguage` term into normalized Rholang `Par`.
///
/// Ambiguous generated terms are preserved as parallel branches after exact
/// semantic-key deduplication. This prevents the runtime backend from silently
/// choosing the first parse alternative.
pub fn lower_rhocalc_term(term: &dyn Term) -> Result<Par, RhocalcAstLowerError> {
    let alternatives = rhocalc_proc_alternatives_from_term(term)?;
    lower_proc_alternatives(alternatives)
}

/// Lower a rhocalc name into the normalized Rholang `Par` representation used
/// for channels.
pub fn lower_rhocalc_name(name: &Name) -> Result<Par, RhocalcAstLowerError> {
    lower_name(name, &BoundEnv::new())
}

fn rhocalc_proc_alternatives_from_term(
    term: &dyn Term,
) -> Result<Vec<&Proc>, RhocalcAstLowerError> {
    let typed = term
        .as_any()
        .downcast_ref::<RhoCalcTerm>()
        .ok_or(RhocalcAstLowerError::ExpectedRhoCalcTerm)?;
    let mut alternatives = Vec::new();
    collect_proc_alternatives(&typed.0, &mut alternatives)?;
    if alternatives.is_empty() {
        Err(RhocalcAstLowerError::ExpectedProcTerm)
    } else {
        Ok(alternatives)
    }
}

fn collect_proc_alternatives<'a>(
    inner: &'a RhoCalcTermInner,
    alternatives: &mut Vec<&'a Proc>,
) -> Result<(), RhocalcAstLowerError> {
    match inner {
        RhoCalcTermInner::Proc(proc) => {
            alternatives.push(proc);
            Ok(())
        },
        RhoCalcTermInner::Ambiguous(inner_alternatives) => {
            for alternative in inner_alternatives {
                collect_proc_alternatives(alternative, alternatives)?;
            }
            Ok(())
        },
        _ => Err(RhocalcAstLowerError::ExpectedProcTerm),
    }
}

fn lower_proc_alternatives<'a>(
    alternatives: impl IntoIterator<Item = &'a Proc>,
) -> Result<Par, RhocalcAstLowerError> {
    let mut seen = BTreeSet::new();
    let mut lowered = Vec::new();
    for proc in alternatives {
        if seen.insert(rhocalc_proc_semantic_key(proc)) {
            lowered.push(lower_rhocalc_proc(proc)?);
        }
    }

    match lowered.len() {
        0 => Err(RhocalcAstLowerError::ExpectedProcTerm),
        1 => Ok(lowered.pop().expect("checked len == 1")),
        _ => Ok(lowered
            .into_iter()
            .fold(Par::default(), |program, branch| program.append(branch))),
    }
}

fn rhocalc_proc_semantic_key(proc: &Proc) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    proc.semantic_hash(&mut hasher);
    hasher.into_key()
}

fn lower_proc(proc: &Proc, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    // A-S4: exec submits the RAW parse tree (no pre-normalization), so the send-sugar nodes
    // (`x!()`, `c!(a,b)`, `@Nil!(q)`, `@n!(…)`, …) arrive unfolded. Desugar the HEAD node to its
    // canonical channel-first form first — a pure structural rearrangement (the same constructor
    // rewrite the rule's `fold` body performs, no value computation) — then lower that.
    if let Some(desugared) = desugar_send_node(proc) {
        return lower_proc(&desugared, env);
    }
    match proc {
        Proc::PZero => Ok(Par::default()),
        Proc::PDrop(name) => lower_drop(name.as_ref(), env),
        // L9-6b CONSTRUCTION arm: a `PFlt*` in VALUE position (a send payload, a
        // re-quote) elaborates to the reflected foreign term via the guest
        // reflector selected by its `tag`. The three delimiter forms are identical
        // at this level — same `Arc<FltNode>` payload.
        Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
            lower_flt_construction(node.as_ref(), env)
        },
        Proc::PPar(parts) => parts
            .iter_elements()
            .try_fold(Par::default(), |acc, part| Ok(acc.append(lower_proc(part, env)?))),
        // Bare infix parallel `a | b` (no outer braces). The WPDA parser emits the raw `PParInfix`
        // node; its `fold` to `PPar({a, b})` (`merge_pp_parallel`) runs only at eval time. Parallel
        // composition lowers to `Par::append` (associative/commutative over sends/receives/etc.),
        // which is exactly what lowering the folded `PPar` bag would produce. A free-process member
        // (e.g. `q` in `c!(p) | q`) lowers via its own `PVar` arm, so it rides this path too.
        Proc::PParInfix(left, right) => {
            Ok(lower_proc(left.as_ref(), env)?.append(lower_proc(right.as_ref(), env)?))
        },
        Proc::POutput(channel, payload) => {
            let channel = lower_name(channel.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par(channel, vec![payload]))
        },
        // `for(...)` receive. Each `;`-separated row nests as the continuation of the previous one;
        // each row may be a single bind, a `&`-join, persistent (`<=`), empty (`<- n`), and may
        // carry a `where` guard. See [`lower_pfor_user`].
        Proc::PForUser(rows, body) => lower_pfor_user(rows, body.as_ref(), env),
        Proc::PPersistOutput(channel, payload) => {
            let channel = lower_name(channel.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par_persistent(channel, vec![payload]))
        },
        // Rholang-style short sends `@P!(q)` / `@P!!(q)`. The WPDA parser emits the raw `*Short`
        // nodes (the `fold` to `POutput(NQuote(P), q)` / `PPersistOutput(NQuote(P), q)` runs only at
        // eval time), so lower them here with the SAME semantics: the channel is the quote of `P`,
        // i.e. `lower_name(NQuote(P)) == lower_proc(P)`. This is the canonical rho send idiom and the
        // body of most COMM examples (`@("c")!(@("OUT")!("p"))` nests two of these).
        Proc::POutputShort(channel_proc, payload) => {
            let channel = lower_proc(channel_proc.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par(channel, vec![payload]))
        },
        Proc::PPersistOutputShort(channel_proc, payload) => {
            let channel = lower_proc(channel_proc.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par_persistent(channel, vec![payload]))
        },
        Proc::PNew(scope) => {
            let (binders, body) = scope.clone().unbind::<String>();
            let extended_env = extend_env(env, &binders);
            // A-S4: the `new` body is a fold-lift scope — a width/precision fold inside it
            // trampolines here (mirrors receive bodies and the top level).
            let body = lower_body_lifting_folds(body.as_ref(), &extended_env)?;
            let locally_free = filter_and_adjust_bitset(&body.locally_free, binders.len());

            Ok(new_new_par(
                binders.len() as i32,
                body,
                Vec::new(),
                BTreeMap::new(),
                locally_free.clone(),
                locally_free,
                false,
            ))
        },
        // ── A-S4 cast purity: casts lower STRUCTURALLY ─────────────────────────────────────
        // A literal leaf is DATA (embedding `GInt(5)` is translation, not evaluation); a
        // structural node lowers to the machine's own metered `Expr` (`-a` → `ENeg`); anything
        // with no machine algebra (the macro-injected cross-type conversion constructors, an
        // unsubstituted category variable, a lambda) fails closed, typed and named. The former
        // `.try_eval()` arms computed those values host-side at lowering time.
        Proc::CastInt(value) => lower_int_value(value.as_ref(), env),
        Proc::CastBool(value) => match value.as_ref() {
            Bool::BoolLit(literal) => Ok(new_gbool_par(*literal, Vec::new(), false)),
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal boolean expression (Bool category)",
            )),
        },
        Proc::CastStr(value) => match value.as_ref() {
            Str::StringLit(literal) => Ok(new_gstring_par(literal.clone(), Vec::new(), false)),
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal string expression (Str category)",
            )),
        },
        Proc::PVar(var) => lower_proc_var(var, env),
        Proc::Err => Err(RhocalcAstLowerError::UnsupportedProc("error process")),
        Proc::CastBigRat(value) => match value.as_ref() {
            BigRat::RatLit(literal) => {
                let rational = literal.get();
                Ok(expr_par(new_gbigrat_expr(
                    rational.numer().to_signed_bytes_be(),
                    rational.denom().to_signed_bytes_be(),
                )))
            },
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal big-rational expression (BigRat category)",
            )),
        },
        Proc::CastFixed(value) => match value.as_ref() {
            Fixed::FixedLit(literal) => Ok(expr_par(new_gfixedpoint_expr(
                literal.unscaled().to_signed_bytes_be(),
                literal.places(),
            ))),
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal fixed-point expression (Fixed category)",
            )),
        },
        Proc::CastFloat(value) => match value.as_ref() {
            Float::FloatLit(literal) => Ok(expr_par(new_gdouble_expr(literal.get()))),
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal float expression (Float category)",
            )),
        },
        Proc::CastBigInt(value) => match value.as_ref() {
            BigInt::NumLit(literal) => {
                Ok(expr_par(new_gbigint_expr(literal.get().to_signed_bytes_be())))
            },
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal big-integer expression (BigInt category)",
            )),
        },
        Proc::CastUInt32(value) => match value.as_ref() {
            UInt32::NumLit(literal) => Ok(new_gint_par(i64::from(*literal), Vec::new(), false)),
            _ => Err(RhocalcAstLowerError::UnsupportedProc(
                "non-literal u32 expression (UInt32 category)",
            )),
        },
        Proc::CastList(value) => lower_list(value.as_ref(), env),
        Proc::CastBag(value) => lower_bag(value.as_ref(), env),
        Proc::CastMap(value) => lower_map(value.as_ref(), env),
        Proc::CastSet(value) => lower_set(value.as_ref(), env),
        Proc::CastPathmap(value) => lower_pathmap(value.as_ref(), env),
        Proc::CastBytes(value) => match value.as_ref() {
            // RhoCalc `Bytes` is a `String`-backed literal (`![String] as Bytes`); lower the ground
            // literal to a Rholang `GString` (mirrors `CastStr`). Non-ground bytes are unsupported.
            Bytes::StringLit(string) => Ok(new_gstring_par(string.clone(), Vec::new(), false)),
            _ => Err(RhocalcAstLowerError::UnsupportedProc("non-ground bytes process")),
        },
        // ── A-S4 fold purity: EVERY width/precision fold trampolines on the machine ─────────
        // Fold nodes are lifted into fold-contract trampolines by [`lower_body_lifting_folds`]
        // BEFORE `lower_proc` descends (ground operands included — the former Tier-1 in-place
        // `try_eval_fold_proc` host fold is deleted). A fold reaching THIS arm sits in a position
        // the lift traversal cannot reach (inside a hashed-collection literal, a receive
        // pattern, or a fold with a non-ground width) — fail closed, typed and named.
        Proc::IntBinProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "int(a, w) width fold outside a fold-liftable position (or non-ground width)",
        )),
        Proc::UIntBinProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "uint(a, w) width fold outside a fold-liftable position (or non-ground width)",
        )),
        Proc::FloatBinProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "float(a, w) width fold outside a fold-liftable position (or non-ground width)",
        )),
        Proc::FixedBinProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "fixed(a, w) width fold outside a fold-liftable position (or non-ground width)",
        )),
        Proc::BigintCastProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "bigint(a) precision cast outside a fold-liftable position",
        )),
        Proc::BigratCastProc(..) => Err(RhocalcAstLowerError::UnsupportedProc(
            "bigrat(a) precision cast outside a fold-liftable position",
        )),
        // ── A-S4 metered machine arithmetic (the RhoCalc face of the E3 pattern) ────────────
        // Operands lower STRUCTURALLY; the machine's reducer evaluates the expression with its
        // size-dependent primitive costs (f1r3node `reduce.rs`: `EPlus`/`EMinus`/`EMult`/`EDiv`/
        // `EMod`/`ENeg` over GInt/GDouble/GBigInt/GBigRat/GFixedPoint). String `+` is Rholang
        // `++` (`EPlusPlus`): when BOTH operands lower to ground string leaves the concat parity
        // arm is chosen; `EPlus` has no GString algebra.
        Proc::Add(a, b) => {
            let lhs = lower_proc(a.as_ref(), env)?;
            let rhs = lower_proc(b.as_ref(), env)?;
            if is_single_gstring_value(&lhs) && is_single_gstring_value(&rhs) {
                Ok(binary_expr_par(lhs, rhs, |p1, p2| {
                    ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 })
                }))
            } else {
                Ok(binary_expr_par(lhs, rhs, |p1, p2| {
                    ExprInstance::EPlusBody(EPlus { p1, p2 })
                }))
            }
        },
        Proc::Sub(a, b) => lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
            ExprInstance::EMinusBody(EMinus { p1, p2 })
        }),
        Proc::Mul(a, b) => lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
            ExprInstance::EMultBody(EMult { p1, p2 })
        }),
        Proc::Div(a, b) => lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
            ExprInstance::EDivBody(EDiv { p1, p2 })
        }),
        Proc::Mod(a, b) => lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
            ExprInstance::EModBody(EMod { p1, p2 })
        }),
        Proc::NegProc(a) => {
            let operand = lower_proc(a.as_ref(), env)?;
            Ok(unary_expr_par(operand, |p| ExprInstance::ENegBody(ENeg { p })))
        },
        // Boolean/comparison guard operators (used by `where`-conditions and boolean payloads):
        // lower both operands and wrap in the matching Rholang comparison/logical `Expr`.
        Proc::Eq(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EEqBody(EEq { p1, p2 }))
        },
        Proc::Ne(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ENeqBody(ENeq { p1, p2 }))
        },
        Proc::Lt(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELtBody(ELt { p1, p2 }))
        },
        Proc::Gt(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGtBody(EGt { p1, p2 }))
        },
        Proc::LtEq(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELteBody(ELte { p1, p2 }))
        },
        Proc::GtEq(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGteBody(EGte { p1, p2 }))
        },
        Proc::And(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EAndBody(EAnd { p1, p2 }))
        },
        Proc::Or(a, b) => {
            lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EOrBody(EOr { p1, p2 }))
        },
        Proc::Not(a) => {
            let operand = lower_proc(a.as_ref(), env)?;
            Ok(unary_expr_par(operand, |p| ExprInstance::ENotBody(ENot { p })))
        },
        // ── Methods routed to the reducer's OWN method table (option C, C2) ──────────────────
        // `.toByteArray()` is Rholang's `toByteArray` (`reduce.rs:4137-4160`: `eval_expr` +
        // `substitute`, then `p.encode_to_vec()`), returning a real `GByteArray` in the machine's
        // own `ScoredTerm` canonical order. It replaces the retired hand-maintained `rhoapi`
        // schema fork (`languages/proto/rhocalc_wire.proto` + `languages/src/rhocalc/wire.rs`),
        // which encoded a hex `GString` in protobuf BYTE order and could not encode any
        // collection the RhoCalc grammar actually produces.
        Proc::MToByteArray(m) => lower_method("toByteArray", m.as_ref(), &[], env),
        // A-S4 fail-closed: every remaining construct has no machine algebra (bitwise ops,
        // cross-type conversions, collection/zipper methods, lambda forms, internal gates). The
        // typed error NAMES the construct; nothing silently host-evaluates.
        other => Err(RhocalcAstLowerError::UnsupportedProc(unsupported_construct_name(other))),
    }
}

/// The static construct name for the A-S4 fail-closed lowering error — every `Proc` variant the
/// lowering does not translate is named here, so the error message identifies the exact syntax
/// (deliverable: "typed, naming the construct"). Variants handled by `lower_proc` never reach
/// this table.
fn unsupported_construct_name(proc: &Proc) -> &'static str {
    match proc {
        Proc::GuardThen(..) => "__guard_then internal guard gate",
        Proc::CommWhere(..) => "comm-where internal receive form",
        Proc::FractionProc(..) => "fraction(a, b) rational constructor",
        Proc::BitOr(..) => "bitor bitwise-or (no Rholang bitwise Expr)",
        Proc::BitAnd(..) => "bitand bitwise-and (no Rholang bitwise Expr)",
        Proc::BitNot(..) => "bitnot bitwise-not (no Rholang bitwise Expr)",
        Proc::MapEmpty => "Map() empty-map constructor",
        Proc::PathmapEmpty => "Pathmap() empty-pathmap constructor",
        Proc::MGet(..) => "m.get(k) map method",
        Proc::MSet(..) => "m.set(k, v) map method",
        Proc::MContains(..) => "m.contains(k) map method",
        Proc::MDelete(..) => "m.delete(k) map method",
        Proc::MUnion(..) => "m.union(n) map method",
        Proc::MSize(..) => "m.size() map method",
        Proc::MKeys(..) => "m.keys() map method",
        Proc::MValues(..) => "m.values() map method",
        Proc::LLength(..) => "l.length() list method",
        Proc::LNth(..) => "l.nth(i) list method",
        Proc::LConcat(..) => "l.concat(m) list method",
        Proc::BCount(..) => "b.count(e) bag method",
        Proc::BDiff(..) => "b.diff(c) bag method",
        Proc::BRemove(..) => "b.remove(e) bag method",
        Proc::PRestrict(..) => "p.restrict(q) pathmap method",
        Proc::PSubtract(..) => "p.subtract(q) pathmap method",
        Proc::PMeet(..) => "p.meet(q) pathmap method",
        Proc::PGetSubtrie(..) => "p.getSubtrie() pathmap method",
        Proc::PGetSubtrieAt(..) => "p.getSubtrieAt(q) pathmap method",
        Proc::PReadZipper(..) => "p.readZipper() zipper method",
        Proc::PReadZipperAt(..) => "p.readZipperAt(q) zipper method",
        Proc::PWriteZipper(..) => "p.writeZipper() zipper method",
        Proc::PWriteZipperAt(..) => "p.writeZipperAt(q) zipper method",
        Proc::RZGetLeaf(..) => "z.getLeaf() read-zipper method",
        Proc::RZDescendTo(..) => "z.descendTo(p) read-zipper method",
        Proc::RZChildCount(..) => "z.childCount() read-zipper method",
        Proc::RZDescendFirst(..) => "z.descendFirst() read-zipper method",
        Proc::RZToNextSibling(..) => "z.toNextSibling() read-zipper method",
        Proc::RZToPrevSibling(..) => "z.toPrevSibling() read-zipper method",
        Proc::RZDescendIndexedBranch(..) => "z.descendIndexedBranch(i) read-zipper method",
        Proc::RZAscendOne(..) => "z.ascendOne() read-zipper method",
        Proc::RZAscend(..) => "z.ascend(n) read-zipper method",
        Proc::WZSetLeaf(..) => "z.setLeaf(…) write-zipper method",
        Proc::WZSetSubtrie(..) => "z.setSubtrie(…) write-zipper method",
        Proc::WZRemoveLeaf(..) => "z.removeLeaf() write-zipper method",
        Proc::WZRemoveBranches(..) => "z.removeBranches() write-zipper method",
        Proc::WZGraft(..) => "z.graft(…) write-zipper method",
        Proc::WZJoinInto(..) => "z.joinInto(…) write-zipper method",
        Proc::SAdd(..) => "s.add(e) set method",
        Proc::ToBool(..) => "bool(a) boolean conversion",
        Proc::ToStr(..) => "str(a) string conversion",
        Proc::CastReadZipper(..) => "read-zipper literal",
        Proc::CastWriteZipper(..) => "write-zipper literal",
        _ => "computed rhocalc expression",
    }
}

/// Lower a binary expression `Proc` (comparison, logic, or A-S4 arithmetic; both operands lowered
/// in `env`) into the corresponding Rholang `Expr` `Par`, propagating `locally_free` and
/// `connective_used` from the operands so an expression that references bound/free variables is
/// tracked correctly. The machine's reducer evaluates the expression (metered).
fn lower_binary_expr(
    a: &Proc,
    b: &Proc,
    env: &BoundEnv,
    build: impl FnOnce(Option<Par>, Option<Par>) -> ExprInstance,
) -> Result<Par, RhocalcAstLowerError> {
    let lhs = lower_proc(a, env)?;
    let rhs = lower_proc(b, env)?;
    Ok(binary_expr_par(lhs, rhs, build))
}

/// Assemble a binary Rholang `Expr` `Par` from two already-lowered operand `Par`s
/// (`locally_free`/`connective_used` propagation shared by [`lower_binary_expr`] and the
/// ground-string `Add` dispatch).
fn binary_expr_par(
    lhs: Par,
    rhs: Par,
    build: impl FnOnce(Option<Par>, Option<Par>) -> ExprInstance,
) -> Par {
    let locally_free = union(lhs.locally_free.clone(), rhs.locally_free.clone());
    let connective_used = lhs.connective_used || rhs.connective_used;
    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(build(Some(lhs), Some(rhs))),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    par
}

/// Lower a RhoCalc **method call** to Rholang's own `EMethod` — the single-evaluator seam.
///
/// This is the mechanism of "option C — different carriers, ONE evaluator". Instead of RhoCalc
/// carrying a second implementation of a method Rholang already has, the method name is handed to
/// the reducer's own method table (`rholang/src/rust/interpreter/reduce.rs::method_table`,
/// 8197-8256), which dispatches on the *evaluated* receiver. Consequences that matter:
///
/// * the semantics are the consensus semantics, by construction — there is nothing left to
///   diverge from;
/// * dispatch is dynamic, so a COMM-bound receiver works exactly like a literal one (the class of
///   bug that divergence B is an instance of); and
/// * receivers Rholang supports but RhoCalc's fold bodies did not (e.g. `nth` over `ETuple` and
///   `GByteArray`, `reduce.rs:4106-4118`) come for free.
///
/// `locally_free`/`connective_used` are unioned over the receiver and every argument, exactly as
/// [`binary_expr_par`] does for operators, so a method call over bound/free variables stays
/// correctly tracked. `EMethod` carries its own copy of both (proto fields 5 and 6) in addition to
/// the enclosing `Par`'s, and the reducer reads the `EMethod`'s copy when it substitutes
/// (`reduce.rs:466`), so both are set.
fn lower_method(
    method_name: &str,
    target: &Proc,
    arguments: &[&Proc],
    env: &BoundEnv,
) -> Result<Par, RhocalcAstLowerError> {
    let target_par = lower_proc(target, env)?;
    let mut argument_pars = Vec::with_capacity(arguments.len());
    for argument in arguments {
        argument_pars.push(lower_proc(argument, env)?);
    }

    let mut locally_free = target_par.locally_free.clone();
    let mut connective_used = target_par.connective_used;
    for argument in &argument_pars {
        locally_free = union(locally_free, argument.locally_free.clone());
        connective_used = connective_used || argument.connective_used;
    }

    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EMethodBody(EMethod {
            method_name: method_name.to_string(),
            target: Some(target_par),
            arguments: argument_pars,
            locally_free: locally_free.clone(),
            connective_used,
        })),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    Ok(par)
}

/// Assemble a unary Rholang `Expr` `Par` from an already-lowered operand `Par` (the `ENeg`/`ENot`
/// propagation shape).
fn unary_expr_par(operand: Par, build: impl FnOnce(Option<Par>) -> ExprInstance) -> Par {
    let locally_free = operand.locally_free.clone();
    let connective_used = operand.connective_used;
    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(build(Some(operand))),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    par
}

/// Is this lowered `Par` a single ground string leaf (`GString`, nothing else)? Drives the
/// `Add` → `EPlusPlus` string-concat parity arm (Rholang `+` has no GString algebra; RhoCalc `+`
/// concatenates ground strings).
fn is_single_gstring_value(par: &Par) -> bool {
    par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.unforgeables.is_empty()
        && par.connectives.is_empty()
        && matches!(
            par.exprs.as_slice(),
            [Expr {
                expr_instance: Some(ExprInstance::GString(_)),
            }]
        )
}

/// Structural lowering of an `Int`-category value (the payload of `Proc::CastInt` and the only
/// grammar-reachable structural Int shape, unary minus). A literal is data; `-a` is the machine's
/// metered `ENeg`; the macro-injected conversion constructors (`BoolToInt`/`UInt32ToInt`), an
/// unsubstituted `IVar`, and lambdas have no machine algebra and fail closed, named.
fn lower_int_value(value: &Int, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match value {
        Int::NumLit(literal) => Ok(new_gint_par(*literal, Vec::new(), false)),
        Int::NegInt(inner) => {
            let operand = lower_int_value(inner.as_ref(), env)?;
            Ok(unary_expr_par(operand, |p| ExprInstance::ENegBody(ENeg { p })))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc(
            "non-literal integer expression (Int category)",
        )),
    }
}

// ── Fold trampoline lifting (Tier-3, generalized by A-S4 to EVERY fold site) ─────────────────────
//
// Pre-A-S4 only HELD folds lifted (e.g. `int(*(x), 8)` whose operand is bound by an enclosing COMM
// `receive` — no Rho primitive, and Dovetail cannot fold it before the rendezvous). A-S4 lowering
// purity lifts EVERY width/precision fold, ground operands included: the host never computes a
// fold value at lowering time. The lift replaces the fold with `*r`, sends the operand to the fold
// contract, and binds its reply `r` via `for(@r <- ret){…}`; the contract runs the exact native
// fold on the machine-delivered ground operand (a statically ground operand expression — e.g.
// `5 + 3` — is evaluated by the machine's metered send-data evaluation before the contract COMM).
// See `crate::fold_contract` and `formal/rocq/rho_bridge/theories/HeldFoldContractSound.v`.

thread_local! {
    // Fold sites collected during ONE lowering (cleared per `lower_rhocalc_term_with_folds`).
    // Mirrors the thread-local var-cache pattern in `mettail_runtime::binding` — single-threaded
    // lowering-session state, no locks.
    static HELD_FOLD_SITES: std::cell::RefCell<Vec<FoldSpec>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// A liftable fold node's static spec pieces: `(operand, kind, width)`. `None` if `proc` is not a
/// fold constructor OR its width is not a ground literal (the latter falls through to
/// `lower_proc`'s typed fold error). The unary precision casts carry width 0 (unused).
fn liftable_fold_parts(proc: &Proc) -> Option<(&Proc, FoldKind, i64)> {
    match proc {
        Proc::IntBinProc(a, w) => Some((a.as_ref(), FoldKind::Int, w.as_ref().try_eval()?)),
        Proc::UIntBinProc(a, w) => Some((a.as_ref(), FoldKind::UInt, w.as_ref().try_eval()?)),
        Proc::FloatBinProc(a, w) => Some((a.as_ref(), FoldKind::Float, w.as_ref().try_eval()?)),
        Proc::FixedBinProc(a, w) => Some((a.as_ref(), FoldKind::Fixed, w.as_ref().try_eval()?)),
        Proc::BigintCastProc(a) => Some((a.as_ref(), FoldKind::BigIntCast, 0)),
        Proc::BigratCastProc(a) => Some((a.as_ref(), FoldKind::BigRatCast, 0)),
        _ => None,
    }
    // NOTE on the width `try_eval`: the width slot `w:Int` is a STATIC rule-shape parameter (a
    // literal, possibly `NegInt`-negated — the grammar's only structural Int shapes). Reading it
    // with `try_eval` is literal decoding of a compile-time constant (the same standing as
    // A-S3's `rule_index`), not runtime value computation; the runtime OPERAND is never
    // host-evaluated.
}

/// Find the first (innermost) liftable fold in `proc`, NOT descending into nested binders
/// (`PForUser`/`PNew` — their bodies are lifted separately as their own fold-lift scopes).
/// Returns `(operand, kind, width)`. Send sugar is desugared in place so folds inside sugar
/// payloads (`c!(int(5,8), 7)`) are found; the traversal mirrors [`replace_fold`] exactly.
fn find_fold(proc: &Proc) -> Option<(Proc, FoldKind, i64)> {
    if let Some(desugared) = desugar_send_node(proc) {
        return find_fold(&desugared);
    }
    match proc {
        Proc::IntBinProc(a, _)
        | Proc::UIntBinProc(a, _)
        | Proc::FloatBinProc(a, _)
        | Proc::FixedBinProc(a, _)
        | Proc::BigintCastProc(a)
        | Proc::BigratCastProc(a) => {
            // Innermost-first: a nested fold inside the operand lifts before this one.
            if let Some(found) = find_fold(a.as_ref()) {
                return Some(found);
            }
            let (operand, kind, width) = liftable_fold_parts(proc)?;
            Some((operand.clone(), kind, width))
        },
        Proc::POutput(_, payload)
        | Proc::PPersistOutput(_, payload)
        | Proc::POutputShort(_, payload)
        | Proc::PPersistOutputShort(_, payload) => find_fold(payload.as_ref()),
        Proc::PParInfix(left, right) => {
            find_fold(left.as_ref()).or_else(|| find_fold(right.as_ref()))
        },
        Proc::PPar(parts) => parts.iter_elements().find_map(find_fold),
        // Expression operands: a fold there becomes `*r` and the machine evaluates the
        // expression after the trampoline COMM substitutes the folded value.
        Proc::Add(a, b)
        | Proc::Sub(a, b)
        | Proc::Mul(a, b)
        | Proc::Div(a, b)
        | Proc::Mod(a, b)
        | Proc::Eq(a, b)
        | Proc::Ne(a, b)
        | Proc::Lt(a, b)
        | Proc::Gt(a, b)
        | Proc::LtEq(a, b)
        | Proc::GtEq(a, b)
        | Proc::And(a, b)
        | Proc::Or(a, b) => find_fold(a.as_ref()).or_else(|| find_fold(b.as_ref())),
        Proc::NegProc(a) | Proc::Not(a) => find_fold(a.as_ref()),
        // `*(@(P))` inlines `P` — folds inside it lift at this scope.
        Proc::PDrop(name) => find_fold_in_name(name.as_ref()),
        // Ordered list literals: a fold element lifts (the literal is rebuilt around `*r`).
        // Hashed collections (Map/Set/Bag/Pathmap) are NOT descended: replacing inside them
        // would re-key the literal; a fold there fails closed via `lower_proc`'s typed error.
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => items.iter().find_map(find_fold),
            _ => None,
        },
        // Binder constructs (`PForUser` receive rows and `PNew`) have their bodies lifted
        // separately, so we do not descend here; anything else has no liftable position.
        Proc::PForUser(..) | Proc::PNew(..) => None,
        _ => None,
    }
}

fn find_fold_in_name(name: &Name) -> Option<(Proc, FoldKind, i64)> {
    match name {
        Name::NQuote(proc) | Name::NQuoteShort(proc) => find_fold(proc.as_ref()),
        Name::NParen(inner) => find_fold_in_name(inner.as_ref()),
        _ => None,
    }
}

/// Rebuild a fold constructor with a replaced operand (widths keep their original literal).
fn rebuild_fold(orig: &Proc, operand: Arc<Proc>) -> Proc {
    match orig {
        Proc::IntBinProc(_, w) => Proc::IntBinProc(operand, w.clone()),
        Proc::UIntBinProc(_, w) => Proc::UIntBinProc(operand, w.clone()),
        Proc::FloatBinProc(_, w) => Proc::FloatBinProc(operand, w.clone()),
        Proc::FixedBinProc(_, w) => Proc::FixedBinProc(operand, w.clone()),
        Proc::BigintCastProc(_) => Proc::BigintCastProc(operand),
        Proc::BigratCastProc(_) => Proc::BigratCastProc(operand),
        _ => orig.clone(),
    }
}

/// Replace the first (innermost) liftable fold in `proc` with `r_drop` (`*r`), mirroring
/// [`find_fold`]'s traversal (desugaring included). Sets `replaced` once a replacement is made.
fn replace_fold(proc: &Proc, r_drop: &Proc, replaced: &mut bool) -> Proc {
    if *replaced {
        return proc.clone();
    }
    if let Some(desugared) = desugar_send_node(proc) {
        return replace_fold(&desugared, r_drop, replaced);
    }
    match proc {
        Proc::IntBinProc(a, _)
        | Proc::UIntBinProc(a, _)
        | Proc::FloatBinProc(a, _)
        | Proc::FixedBinProc(a, _)
        | Proc::BigintCastProc(a)
        | Proc::BigratCastProc(a) => {
            let new_a = replace_fold(a.as_ref(), r_drop, replaced);
            if *replaced {
                return rebuild_fold(proc, Arc::new(new_a));
            }
            if liftable_fold_parts(proc).is_some() {
                *replaced = true;
                return r_drop.clone();
            }
            proc.clone()
        },
        Proc::POutput(name, payload) => Proc::POutput(
            name.clone(),
            Arc::new(replace_fold(payload.as_ref(), r_drop, replaced)),
        ),
        Proc::PPersistOutput(name, payload) => Proc::PPersistOutput(
            name.clone(),
            Arc::new(replace_fold(payload.as_ref(), r_drop, replaced)),
        ),
        // Short sends: replace the fold in the payload, keep the channel proc intact (mirrors
        // `find_fold`, which descends only into the payload).
        Proc::POutputShort(channel_proc, payload) => Proc::POutputShort(
            channel_proc.clone(),
            Arc::new(replace_fold(payload.as_ref(), r_drop, replaced)),
        ),
        Proc::PPersistOutputShort(channel_proc, payload) => Proc::PPersistOutputShort(
            channel_proc.clone(),
            Arc::new(replace_fold(payload.as_ref(), r_drop, replaced)),
        ),
        // Infix parallel: descend left then right. The top-of-function `*replaced` guard ensures the
        // right branch is left untouched once the (single) innermost fold has been replaced.
        Proc::PParInfix(left, right) => {
            let new_left = replace_fold(left.as_ref(), r_drop, replaced);
            let new_right = replace_fold(right.as_ref(), r_drop, replaced);
            Proc::PParInfix(Arc::new(new_left), Arc::new(new_right))
        },
        Proc::PPar(parts) => Proc::PPar(
            parts
                .iter_elements()
                .map(|part| replace_fold(part, r_drop, replaced))
                .collect(),
        ),
        Proc::Add(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Sub(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Mul(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Div(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Mod(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Eq(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Ne(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Lt(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Gt(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::LtEq(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::GtEq(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::And(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::Or(a, b) => rebuild_binary(proc, a, b, r_drop, replaced),
        Proc::NegProc(a) => {
            Proc::NegProc(Arc::new(replace_fold(a.as_ref(), r_drop, replaced)))
        },
        Proc::Not(a) => Proc::Not(Arc::new(replace_fold(a.as_ref(), r_drop, replaced))),
        Proc::PDrop(name) => {
            Proc::PDrop(Arc::new(replace_fold_in_name(name.as_ref(), r_drop, replaced)))
        },
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => Proc::CastList(Arc::new(List::ListLit(
                items
                    .iter()
                    .map(|item| replace_fold(item, r_drop, replaced))
                    .collect(),
            ))),
            _ => proc.clone(),
        },
        _ => proc.clone(),
    }
}

/// Rebuild a binary expression node with the fold replaced in its first-found operand (left then
/// right, mirroring [`find_fold`]).
fn rebuild_binary(
    orig: &Proc,
    a: &Arc<Proc>,
    b: &Arc<Proc>,
    r_drop: &Proc,
    replaced: &mut bool,
) -> Proc {
    let new_a = Arc::new(replace_fold(a.as_ref(), r_drop, replaced));
    let new_b = Arc::new(replace_fold(b.as_ref(), r_drop, replaced));
    match orig {
        Proc::Add(..) => Proc::Add(new_a, new_b),
        Proc::Sub(..) => Proc::Sub(new_a, new_b),
        Proc::Mul(..) => Proc::Mul(new_a, new_b),
        Proc::Div(..) => Proc::Div(new_a, new_b),
        Proc::Mod(..) => Proc::Mod(new_a, new_b),
        Proc::Eq(..) => Proc::Eq(new_a, new_b),
        Proc::Ne(..) => Proc::Ne(new_a, new_b),
        Proc::Lt(..) => Proc::Lt(new_a, new_b),
        Proc::Gt(..) => Proc::Gt(new_a, new_b),
        Proc::LtEq(..) => Proc::LtEq(new_a, new_b),
        Proc::GtEq(..) => Proc::GtEq(new_a, new_b),
        Proc::And(..) => Proc::And(new_a, new_b),
        Proc::Or(..) => Proc::Or(new_a, new_b),
        _ => orig.clone(),
    }
}

fn replace_fold_in_name(name: &Name, r_drop: &Proc, replaced: &mut bool) -> Name {
    match name {
        Name::NQuote(proc) => {
            Name::NQuote(Arc::new(replace_fold(proc.as_ref(), r_drop, replaced)))
        },
        Name::NQuoteShort(proc) => {
            Name::NQuoteShort(Arc::new(replace_fold(proc.as_ref(), r_drop, replaced)))
        },
        Name::NParen(inner) => {
            Name::NParen(Arc::new(replace_fold_in_name(inner.as_ref(), r_drop, replaced)))
        },
        _ => name.clone(),
    }
}

/// Lower a fold-lift scope body (the top level, a receive body, or a `new` body), lifting each
/// width/precision fold — ground or COMM-held — into a fold-contract trampoline. With no fold this
/// is exactly `lower_proc`. For one it emits
/// `new ret in { @"<fold>"!(operand, ret) | for(@r <- ret){ body[fold ↦ *r] } }` and records the
/// `FoldSpec`; the `for` body is lifted recursively (nested folds). All de Bruijn bookkeeping rides
/// `extend_env`.
fn lower_body_lifting_folds(body: &Proc, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    let Some((operand, kind, width)) = find_fold(body) else {
        return lower_proc(body, env);
    };
    let site_index = HELD_FOLD_SITES.with(|sites| sites.borrow().len()) as u8;
    HELD_FOLD_SITES.with(|sites| {
        sites
            .borrow_mut()
            .push(FoldSpec { kind, width, site_index })
    });
    let channel = fold_channel(site_index);

    // Fresh result binders: `new ret` (innermost) and the `for`-bound `r`.
    let ret_var = mettail_runtime::get_or_create_var(format!("__mtl_ret_{site_index}"));
    let r_var = mettail_runtime::get_or_create_var(format!("__mtl_r_{site_index}"));
    let r_drop = Proc::PDrop(Arc::new(Name::NVar(OrdVar(Var::Free(r_var.clone())))));

    let mut replaced = false;
    let transformed = replace_fold(body, &r_drop, &mut replaced);

    // `new ret` shifts `env` by 1; the `for` then binds `r` (index 0), `ret` (index 1).
    let env_new = extend_env(env, &[Binder(ret_var)]);
    let env_for = extend_env(&env_new, &[Binder(r_var)]);

    // Send `@channel!(operand, ret)` at the `new` level (ret = boundvar 0). A statically ground
    // operand EXPRESSION (`5 + 3`) lowers to its metered `Expr`; the machine evaluates it at
    // send time, so the contract always receives a ground value leaf.
    let operand_par = lower_proc(&operand, &env_new)?;
    let ret_channel = new_boundvar_par(0, Vec::new(), false);
    let send = send_par(channel, vec![operand_par, ret_channel.clone()]);

    // `for(@r <- ret){ <recursively-lifted transformed body> }`.
    let for_body = lower_body_lifting_folds(&transformed, &env_for)?;
    let bind = ReceiveBind {
        patterns: vec![new_freevar_par(0, Vec::new())],
        source: Some(ret_channel),
        remainder: None,
        free_count: 1,
    };
    let recv_locally_free = receive_locally_free(&[bind.clone()], &for_body, 1);
    let recv = new_receive_par(
        vec![bind],
        for_body,
        false,
        false,
        1,
        recv_locally_free.clone(),
        false,
        recv_locally_free,
        false,
    );

    // `new ret { send | recv }`.
    let inner = send.append(recv);
    let new_locally_free = filter_and_adjust_bitset(&inner.locally_free, 1);
    Ok(new_new_par(
        1,
        inner,
        Vec::new(),
        BTreeMap::new(),
        new_locally_free.clone(),
        new_locally_free,
        false,
    ))
}

/// Lower a term to a `Par` PLUS the fold contract `Definition` specs its trampolines need (A-S4:
/// every width/precision fold lifts — ground or COMM-held). The `Par` already targets the fold
/// channels; the caller registers the contracts via the runtime's `extra_system_processes` seam.
/// Equivalent to `lower_rhocalc_term` when the term has no folds (empty `Vec`).
pub fn lower_rhocalc_term_with_folds(
    term: &dyn Term,
) -> Result<(Par, Vec<FoldSpec>), RhocalcAstLowerError> {
    clear_held_fold_sites();
    let par = lower_rhocalc_term(term)?;
    Ok((par, take_held_fold_sites()))
}

/// Clear the fold-site session state. Call before a lowering whose fold contracts you intend to
/// collect with [`take_held_fold_sites`], so stale sites from a prior lowering don't leak. Used by
/// the wrapper's `start_reduction_stepper` / the exec path, which lower through the invocation
/// compiler (not [`lower_rhocalc_term_with_folds`] directly).
pub fn clear_held_fold_sites() {
    HELD_FOLD_SITES.with(|sites| sites.borrow_mut().clear());
}

/// Take (and clear) the fold sites recorded since the last clear. Empty if the lowering had no
/// folds (e.g. Calculator, whose invocation compiler never lifts; A-S4: RhoCalc records a site
/// for EVERY fold, ground or COMM-held). The caller materializes the contracts with
/// [`crate::fold_contract::fold_definitions_for`].
pub fn take_held_fold_sites() -> Vec<FoldSpec> {
    HELD_FOLD_SITES.with(|sites| std::mem::take(&mut *sites.borrow_mut()))
}

fn lower_bag(bag: &Bag, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match bag {
        Bag::BagLit(entries) => {
            let mut entries = entries.iter().collect::<Vec<_>>();
            entries.sort_by_key(|(item, _)| *item);

            let mut pairs = Vec::with_capacity(entries.len());
            for (item, count) in entries {
                let count = i64::try_from(count).map_err(|_| {
                    RhocalcAstLowerError::UnsupportedProc("bag multiplicity exceeds i64")
                })?;
                let item = lower_proc(item, env)?;
                let count = new_gint_par(count, Vec::new(), false);
                let pair_locally_free =
                    union(item.locally_free.clone(), count.locally_free.clone());
                pairs.push(new_elist_par(
                    vec![item, count],
                    pair_locally_free.clone(),
                    false,
                    None,
                    pair_locally_free,
                    false,
                ));
            }

            let pairs_locally_free = locally_free_union(&pairs);
            let pairs = new_elist_par(
                pairs,
                pairs_locally_free.clone(),
                false,
                None,
                pairs_locally_free,
                false,
            );
            let tag = GPrivateBuilder::new_par_from_string(crate::RHOCALC_BAG_ABI_TAG.to_string());
            let locally_free = union(tag.locally_free.clone(), pairs.locally_free.clone());

            Ok(new_elist_par(
                vec![tag, pairs],
                locally_free.clone(),
                false,
                None,
                locally_free,
                false,
            ))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed bag process")),
    }
}

fn lower_list(list: &List, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match list {
        List::ListLit(items) => {
            let items = items
                .iter()
                .map(|item| lower_proc(item, env))
                .collect::<Result<Vec<_>, _>>()?;
            let locally_free = locally_free_union(&items);
            Ok(new_elist_par(items, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed list process")),
    }
}

fn lower_map(map: &Map, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match map {
        Map::MapLit(entries) => {
            let mut pairs = Vec::with_capacity(entries.len());
            let mut locally_free = Vec::new();

            for (key, value) in entries.iter() {
                let key = lower_proc(key, env)?;
                let value = lower_proc(value, env)?;
                locally_free = union(
                    locally_free,
                    union(key.locally_free.clone(), value.locally_free.clone()),
                );
                pairs.push(new_key_value_pair(key, value));
            }

            Ok(new_emap_par(pairs, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed map process")),
    }
}

fn lower_set(set: &Set, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match set {
        Set::SetLit(items) => {
            // `HashSetLit` iterates in hash order; sort by `Proc` `Ord` for a deterministic `ESet`
            // (mirrors how `lower_bag` sorts its entries).
            let mut items: Vec<&Proc> = items.iter().collect();
            items.sort();
            let elements = items
                .into_iter()
                .map(|item| lower_proc(item, env))
                .collect::<Result<Vec<_>, _>>()?;
            let locally_free = locally_free_union(&elements);
            Ok(new_eset_par(elements, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed set process")),
    }
}

fn lower_pathmap(pathmap: &Pathmap, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match pathmap {
        Pathmap::PathmapLit(entries) => {
            // A pathmap is key/value like a map; lower to a Rholang `EMap` (mirrors `lower_map`).
            // `PathMapLit` (insertion-order) is sorted by key for a deterministic encoding.
            let mut entries: Vec<(&Proc, &Proc)> = entries.iter().collect();
            entries.sort_by(|(key_a, _), (key_b, _)| key_a.cmp(key_b));

            let mut pairs = Vec::with_capacity(entries.len());
            let mut locally_free = Vec::new();
            for (key, value) in entries {
                let key = lower_proc(key, env)?;
                let value = lower_proc(value, env)?;
                locally_free = union(
                    locally_free,
                    union(key.locally_free.clone(), value.locally_free.clone()),
                );
                pairs.push(new_key_value_pair(key, value));
            }

            Ok(new_emap_par(pairs, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed pathmap process")),
    }
}

/// Lower a `PForUser` receive (rows + body) into a normalized Rholang `Receive` `Par`.
///
/// `rows[0]` is the outermost receive; the remaining rows nest as the continuation. A row is a
/// single bind, a `&`-join (first bind + the rest), persistent (`<=`), empty (`<- n`), and may carry
/// a `where` guard. Binding mechanics mirror the former `PInputs` lowering, generalized to
/// multi-bind rows, multi-variable patterns, and where-guards:
///
/// - each bind's channel is lowered in the OUTER `env`;
/// - each bind's pattern free variables are numbered LOCALLY (0,1,… reset per bind) and become the
///   bind's `free_count`; their `Binder`s are concatenated across binds (bind order) and fed to
///   [`extend_env`] for the body, so the body's de Bruijn indices line up with the Rho machine;
/// - the innermost user body lifts folds via [`lower_body_lifting_folds`]; a nested row recurses;
/// - a `where`-guard is lowered (in the extended env) and attached as `Receive.condition`.
fn lower_pfor_user(
    rows: &[ForRow],
    body: &Proc,
    env: &BoundEnv,
) -> Result<Par, RhocalcAstLowerError> {
    if rows.is_empty() {
        // No rows left: the body is the whole process.
        return lower_body_lifting_folds(body, env);
    }
    let row = &rows[0];

    // Continuation = the remaining rows (nested `PForUser`) or the body when this is the last row.
    let continuation = if rows.len() > 1 {
        Proc::PForUser(rows[1..].to_vec(), Arc::new(body.clone()))
    } else {
        body.clone()
    };

    let (binds, persistent, cond) = decompose_for_row(row)?;
    if binds.is_empty() {
        return Err(RhocalcAstLowerError::EmptyInputJoin);
    }

    // Lower each bind: source channel (OUTER env) + pattern `Par`(s) + the bind's local binders.
    // #14: binders accumulate as `ReceiveSlot`s IN BIND ORDER — a moniker `PVar` binder or a
    // name-keyed FLT hole — so an FLT hole and a moniker binder that co-occur in a `&`-join share
    // one coherent de-Bruijn numbering (a hole's global level then follows from its slot position,
    // not the FLT bind's local `FreeVar` numbering).
    let mut binds_rho: Vec<ReceiveBind> = Vec::with_capacity(binds.len());
    let mut slots: Vec<ReceiveSlot> = Vec::new();
    for bind in &binds {
        let channel = bind_channel_name(bind)
            .ok_or(RhocalcAstLowerError::UnsupportedProc("for-row channel"))?;
        let source = lower_name(channel, env)?;

        if let Some(node) = bind_flt_node(bind) {
            let (pattern, free_count, hole_names) = lower_flt_pattern(node.as_ref(), env)?;
            // The FLT bind contributes one hole slot per `FreeVar`, in `FreeVar` order.
            for name in hole_names {
                slots.push(ReceiveSlot::Hole(name));
            }
            binds_rho.push(ReceiveBind {
                patterns: vec![pattern],
                source: Some(source),
                remainder: None,
                free_count,
            });
            continue;
        }

        let (patterns, bind_binders) = if is_empty_bind(bind) {
            // `for(_ <- c)` — match (and discard) any single message; no bound variables.
            (vec![new_wildcard_par(Vec::new(), false)], Vec::new())
        } else {
            let pat_proc = bind_pattern_proc(bind)
                .ok_or(RhocalcAstLowerError::UnsupportedProc("for-row pattern"))?;
            let mut counter = 0i32;
            let mut bind_binders = Vec::new();
            let pat_par = lower_pattern_proc(&pat_proc, &mut counter, &mut bind_binders)?;
            (vec![pat_par], bind_binders)
        };

        let free_count = bind_binders.len() as i32;
        for binder in bind_binders {
            slots.push(ReceiveSlot::Moniker(binder));
        }
        binds_rho.push(ReceiveBind {
            patterns,
            source: Some(source),
            remainder: None,
            free_count,
        });
    }

    // #14: ONE unified continuation scope over the receive's binder slots (moniker + FLT holes
    // interleaved in bind order). `receive_binder_count` is the receive's total bound-var width
    // used by the `locally_free` accounting below. For a moniker-only receive this is byte-identical
    // to the former `extend_env(env, &all_binders)` (same slot order, same `width - 1 - i` levels).
    let receive_binder_count = slots.len();
    let extended_env = env.extend_slots(&slots);

    // The continuation is lowered under the extended env: a nested row recurses; otherwise this is
    // the innermost user body, where held folds are lifted into Dovetail trampolines.
    let lowered_body = match &continuation {
        Proc::PForUser(rest_rows, rest_body) => {
            lower_pfor_user(rest_rows, rest_body.as_ref(), &extended_env)?
        },
        other => lower_body_lifting_folds(other, &extended_env)?,
    };

    // `where`-guard (if any) is an ordinary boolean `Proc`, lowered in the extended env.
    let condition = match &cond {
        Some(guard) => Some(lower_proc(guard, &extended_env)?),
        None => None,
    };

    let bind_count = receive_binder_count as i32;
    let mut locally_free = receive_locally_free(&binds_rho, &lowered_body, receive_binder_count);
    if let Some(cond_par) = &condition {
        // The guard is lowered in the same extended env as the body, so adjust its `locally_free`
        // the same way (drop this receive's own bound vars, shift outer references down).
        locally_free = union(
            locally_free,
            filter_and_adjust_bitset(&cond_par.locally_free, receive_binder_count),
        );
    }

    let mut receive_par = new_receive_par(
        binds_rho,
        lowered_body,
        persistent,
        false,
        bind_count,
        locally_free.clone(),
        false,
        locally_free,
        false,
    );

    if let Some(cond_par) = condition {
        // `new_receive_par` hardcodes `condition: None`; attach the `where`-guard post-construction
        // (the matcher coordinator evaluates it against the combined bindings of all binds).
        if let Some(receive) = receive_par.receives.get_mut(0) {
            receive.condition = Some(cond_par);
        }
    }

    Ok(receive_par)
}

/// Decompose a (non-lambda) [`ForRow`] into `(binds, persistent, where-cond)`. The lambda-calculus
/// `ForRow` variants (`FVar`/`Lam*`/`Apply*`/`MLam*`/`MApply*`) never appear in a normalized ground
/// term and are rejected as unsupported.
fn decompose_for_row(
    row: &ForRow,
) -> Result<(Vec<InputBind>, bool, Option<Proc>), RhocalcAstLowerError> {
    // `ForRow`/`InputBind` derive `Drop`; never move fields out — match by reference and clone.
    //
    // ROOT-P Layer F: the persistent-SPECIFIC ForRow arms (ForRowSinglePersistent*,
    // ForRowPersistent*, ForRowSingleEmptyPersistent*) and their `persistent_first`
    // helper were REMOVED with the now-deleted grammar rules (rhocalc.rs). A `<=`
    // head now lowers via the general arms below over a persistent InputBind
    // (InputBindPersistent / InputBindEmptyPersistent); `is_persistent_bind`
    // recovers the persistence flag from the bind itself — byte-identical result
    // (FV: ForRowPersistentRuleRedundancy.v T1).
    match row {
        ForRow::ForRowSingleNoWhere(b) => {
            let binds = vec![b.as_ref().clone()];
            let persistent = binds.iter().any(is_persistent_bind);
            Ok((binds, persistent, None))
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            let binds = vec![b.as_ref().clone()];
            let persistent = binds.iter().any(is_persistent_bind);
            Ok((binds, persistent, Some(cond.as_ref().clone())))
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut binds = Vec::with_capacity(1 + bs.len());
            binds.push(b.as_ref().clone());
            binds.extend(bs.iter().cloned());
            let persistent = binds.iter().any(is_persistent_bind);
            Ok((binds, persistent, None))
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut binds = Vec::with_capacity(1 + bs.len());
            binds.push(b.as_ref().clone());
            binds.extend(bs.iter().cloned());
            let persistent = binds.iter().any(is_persistent_bind);
            Ok((binds, persistent, Some(cond.as_ref().clone())))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("non-ground for-row")),
    }
}

/// Lower a receive-bind PATTERN proc (produced by [`bind_pattern_proc`]) into a Rholang pattern
/// `Par`. Each `Proc::PVar` leaf marks a bound position: it becomes a fresh `FreeVar(counter)`
/// (numbered left-to-right WITHIN this bind) and its `Binder` is pushed to `binders` in the same
/// order. `CastList` patterns recurse (threading the same counter/binders). Any other sub-pattern is
/// a GROUND value matched exactly, lowered via [`lower_proc`] in the empty env.
fn lower_pattern_proc(
    pat: &Proc,
    counter: &mut i32,
    binders: &mut Vec<Binder<String>>,
) -> Result<Par, RhocalcAstLowerError> {
    match pat {
        Proc::PVar(ordvar) => match &ordvar.0 {
            Var::Free(free_var) => {
                let index = *counter;
                *counter += 1;
                binders.push(Binder(free_var.clone()));
                Ok(new_freevar_par(index, Vec::new()))
            },
            Var::Bound(_) => {
                Err(RhocalcAstLowerError::UnsupportedProc("bound var in receive pattern"))
            },
        },
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => {
                let mut item_pars = Vec::with_capacity(items.len());
                for item in items {
                    item_pars.push(lower_pattern_proc(item, counter, binders)?);
                }
                let locally_free = locally_free_union(&item_pars);
                // A list pattern is "connective-using" iff it contains free variables; derive that
                // from the lowered children (a free-variable `Par` carries `connective_used = true`).
                let connective_used = item_pars.iter().any(|item| item.connective_used);
                Ok(new_elist_par(
                    item_pars,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RhocalcAstLowerError::UnsupportedProc("computed list receive pattern")),
        },
        // Map pattern `@{k: v, ...}` — keys/values may contain pattern variables (e.g. `{1: x}`
        // binds `x` to the value at key `1`). Recurse so embedded `PVar`s become free variables;
        // ground keys/values stay exact-match. Mirrors `lower_map` but threads the freevar counter.
        Proc::CastMap(map) => match map.as_ref() {
            Map::MapLit(entries) => {
                let mut pairs = Vec::with_capacity(entries.len());
                let mut locally_free = Vec::new();
                let mut connective_used = false;
                for (key, value) in entries.iter() {
                    let key = lower_pattern_proc(key, counter, binders)?;
                    let value = lower_pattern_proc(value, counter, binders)?;
                    connective_used = connective_used || key.connective_used || value.connective_used;
                    locally_free = union(
                        locally_free,
                        union(key.locally_free.clone(), value.locally_free.clone()),
                    );
                    pairs.push(new_key_value_pair(key, value));
                }
                Ok(new_emap_par(
                    pairs,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RhocalcAstLowerError::UnsupportedProc("computed map receive pattern")),
        },
        // Set pattern `@Set(e, ...)` — elements may contain pattern variables. Recurse; ground
        // elements stay exact-match. (Sorted for a deterministic `ESet`, as `lower_set` does.)
        Proc::CastSet(set) => match set.as_ref() {
            Set::SetLit(items) => {
                let mut items: Vec<&Proc> = items.iter().collect();
                items.sort();
                let mut elements = Vec::with_capacity(items.len());
                for item in items {
                    elements.push(lower_pattern_proc(item, counter, binders)?);
                }
                let locally_free = locally_free_union(&elements);
                let connective_used = elements.iter().any(|e| e.connective_used);
                Ok(new_eset_par(
                    elements,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RhocalcAstLowerError::UnsupportedProc("computed set receive pattern")),
        },
        // A ground sub-pattern (literal/constructor with no pattern variables): exact-match value.
        // This covers ground Bag/Pathmap/Drop/Nil/numeric/string patterns, whose `lower_proc`
        // encoding is itself the exact structure to match.
        other => lower_proc(other, &BoundEnv::new()),
    }
}

fn send_par_persistent(channel: Par, data: Vec<Par>) -> Par {
    let locally_free = data
        .iter()
        .fold(channel.locally_free.clone(), |acc, item| union(acc, item.locally_free.clone()));
    new_send_par(channel, data, true, locally_free.clone(), false, locally_free, false)
}

// ── Receive-bind helpers (replicated from `mettail_languages::rhocalc::receive`) ───────────────────
//
// The `receive` helpers there are `pub(crate)` to the `mettail_languages` crate and so are NOT
// reachable from this (`rholang-runtime`) crate. They are tiny pure functions over public AST
// constructors, so they are replicated here verbatim rather than widening cross-crate visibility.

/// `Proc::CastList([..])` constructor (the canonical arity list used by receive patterns).
fn mk_proc_list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

/// A-S4: desugar ONE raw send-sugar node (`x!()`, `c!(a,b)`, `@Nil!(q)`, `@n!(…)`, their `!!`
/// twins, and the internal `__ppar`) to its canonical channel-first form. Returns `None` for
/// every non-sugar node. Each arm performs EXACTLY the constructor rewrite the rule's `![{…}]
/// fold` body performs (`languages/src/rhocalc.rs`) — a pure structural rearrangement, no value
/// computation — so lowering the desugared node is byte-identical to lowering the eval-time fold
/// target. Exec submits the RAW parse tree post-A-S4, so these nodes reach the lowering unfolded.
fn desugar_send_node(proc: &Proc) -> Option<Proc> {
    let quote = |p: &Arc<Proc>| Arc::new(Name::NQuote(p.clone()));
    let quote_nil = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let quote_name = |n: &Arc<Name>| {
        Arc::new(Name::NQuote(Arc::new(name_pattern_to_proc(n.as_ref()))))
    };
    let list1 = |a: &Arc<Proc>, bs: &[Proc]| {
        let mut items = Vec::with_capacity(1 + bs.len());
        items.push(a.as_ref().clone());
        items.extend(bs.iter().cloned());
        Arc::new(mk_proc_list(items))
    };
    let empty = || Arc::new(mk_proc_list(Vec::new()));
    Some(match proc {
        // Empty sends: `x!()` / `x!!()` — payload is the empty canonical arity list.
        Proc::POutputEmpty(n) => Proc::POutput(n.clone(), empty()),
        Proc::PPersistOutputEmpty(n) => Proc::PPersistOutput(n.clone(), empty()),
        // Polyadic sends: `x!(a, b…)` — payload is the canonical arity list.
        Proc::POutput2Plus(n, a, bs) => Proc::POutput(n.clone(), list1(a, bs)),
        Proc::PPersistOutput2Plus(n, a, bs) => Proc::PPersistOutput(n.clone(), list1(a, bs)),
        // `@Nil` sends: channel is the quote of `Nil`.
        Proc::POutputNil(q) => Proc::POutput(quote_nil(), q.clone()),
        Proc::PPersistOutputNil(q) => Proc::PPersistOutput(quote_nil(), q.clone()),
        Proc::POutputNilEmpty => Proc::POutput(quote_nil(), empty()),
        Proc::PPersistOutputNilEmpty => Proc::PPersistOutput(quote_nil(), empty()),
        Proc::POutputNil2Plus(a, bs) => Proc::POutput(quote_nil(), list1(a, bs)),
        Proc::PPersistOutputNil2Plus(a, bs) => Proc::PPersistOutput(quote_nil(), list1(a, bs)),
        // `@n` (Name-shaped) sends: channel is the quote of the name's process image.
        Proc::POutputQuoted(n, q) => Proc::POutput(quote_name(n), q.clone()),
        Proc::POutputQuotedEmpty(n) => Proc::POutput(quote_name(n), empty()),
        Proc::POutputQuoted2Plus(n, a, bs) => Proc::POutput(quote_name(n), list1(a, bs)),
        // `@P` (Proc-shaped) empty/polyadic sends: channel is the quote of `P`. (The scalar
        // `POutputShort`/`PPersistOutputShort` are lowered directly by their own arms.)
        Proc::POutputShortEmpty(p) => Proc::POutput(quote(p), empty()),
        Proc::PPersistOutputShortEmpty(p) => Proc::PPersistOutput(quote(p), empty()),
        Proc::POutputShort2Plus(p, a, bs) => Proc::POutput(quote(p), list1(a, bs)),
        Proc::PPersistOutputShort2Plus(p, a, bs) => Proc::PPersistOutput(quote(p), list1(a, bs)),
        // Internal `__ppar(…)` constructor exposure: the multiset it denotes.
        Proc::PParInternal(parts) => Proc::PPar(parts.clone()),
        _ => return None,
    })
}

/// Map a name PATTERN to the `Proc` whose `PVar` leaves mark the bound positions.
fn name_pattern_to_proc(name_pat: &Name) -> Proc {
    match name_pat {
        Name::NVar(var) => Proc::PVar(var.clone()),
        Name::NQuote(proc) => proc.as_ref().clone(),
        Name::NQuoteShort(proc) => proc.as_ref().clone(),
        Name::NQuoteNil => Proc::PZero,
        _ => Proc::Err,
    }
}

/// Normalize a quoted pattern to the canonical arity shape (`CastList`/`PVar` pass through; anything
/// else is wrapped in a one-element list, matching scalar-send arity normalization).
fn canonicalize_arity_pattern(pattern: &Proc) -> Proc {
    match pattern {
        Proc::CastList(_) | Proc::PVar(_) => pattern.clone(),
        _ => mk_proc_list(vec![pattern.clone()]),
    }
}

/// The bind's pattern as a `Proc` whose `Proc::PVar` leaves mark the bound positions.
/// L9-6b: the `FltNode` of an FLT RECEIVE pattern (`for(@lam`…` <- c)`), or `None`
/// for a non-FLT bind. The FLT surface `@lam`…`` is a quoted `PFlt*` process
/// (`NQuote`/`NQuoteShort`); a `PFlt*` written directly as a quoted pattern rides
/// the `InputBindQuoted` family. Intercepting here (before [`bind_pattern_proc`]'s
/// arity-list wrapping) keeps the reflected FLT pattern the receive's SOLE pattern,
/// matching the single reflected datum a `@c!(⟦…⟧)` send carries.
fn bind_flt_node(bind: &InputBind) -> Option<Arc<FltNode>> {
    fn flt_of_proc(proc: &Proc) -> Option<Arc<FltNode>> {
        match proc {
            Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
                Some(Arc::clone(node))
            },
            _ => None,
        }
    }
    fn flt_of_name(name: &Name) -> Option<Arc<FltNode>> {
        match name {
            Name::NQuote(proc) | Name::NQuoteShort(proc) => flt_of_proc(proc.as_ref()),
            _ => None,
        }
    }
    match bind {
        InputBind::InputBind(lhs, _)
        | InputBind::InputBindPersistent(lhs, _)
        | InputBind::InputBindQuery(lhs, _, _) => flt_of_name(lhs.as_ref()),
        InputBind::InputBindQuoted(pat, _)
        | InputBind::InputBindQuotedPersistent(pat, _)
        | InputBind::InputBindQuotedQuery(pat, _, _) => flt_of_proc(pat.as_ref()),
        _ => None,
    }
}

fn bind_pattern_proc(bind: &InputBind) -> Option<Proc> {
    match bind {
        InputBind::InputBind(lhs, _)
        | InputBind::InputBindPersistent(lhs, _)
        | InputBind::InputBindQuery(lhs, _, _) => {
            if matches!(lhs.as_ref(), Name::NVar(_)) {
                Some(name_pattern_to_proc(lhs.as_ref()))
            } else {
                Some(mk_proc_list(vec![name_pattern_to_proc(lhs.as_ref())]))
            }
        },
        InputBind::InputBindPolyadic(lhs, lhss, _)
        | InputBind::InputBindPersistentPolyadic(lhs, lhss, _) => {
            let mut items = Vec::with_capacity(1 + lhss.len());
            items.push(name_pattern_to_proc(lhs.as_ref()));
            items.extend(lhss.iter().map(name_pattern_to_proc));
            Some(mk_proc_list(items))
        },
        InputBind::InputBindEmpty(_)
        | InputBind::InputBindEmptyPersistent(_)
        | InputBind::InputBindEmptyQuery(_, _) => Some(mk_proc_list(vec![])),
        InputBind::InputBindQuoted(pat, _)
        | InputBind::InputBindQuotedPersistent(pat, _)
        | InputBind::InputBindQuotedQuery(pat, _, _) => {
            Some(canonicalize_arity_pattern(pat.as_ref()))
        },
        _ => None,
    }
}

/// The channel name a bind receives on.
fn bind_channel_name(bind: &InputBind) -> Option<&Name> {
    match bind {
        InputBind::InputBind(_, n) => Some(n.as_ref()),
        InputBind::InputBindPersistent(_, n) => Some(n.as_ref()),
        InputBind::InputBindPolyadic(_, _, n) => Some(n.as_ref()),
        InputBind::InputBindPersistentPolyadic(_, _, n) => Some(n.as_ref()),
        InputBind::InputBindQuery(_, n, _) => Some(n.as_ref()),
        InputBind::InputBindEmpty(n) => Some(n.as_ref()),
        InputBind::InputBindEmptyPersistent(n) => Some(n.as_ref()),
        InputBind::InputBindEmptyQuery(n, _) => Some(n.as_ref()),
        InputBind::InputBindQuoted(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuotedPersistent(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuotedQuery(_, n, _) => Some(n.as_ref()),
        _ => None,
    }
}

/// Is this a persistent (`<=`) bind?
fn is_persistent_bind(bind: &InputBind) -> bool {
    matches!(
        bind,
        InputBind::InputBindPersistent(_, _)
            | InputBind::InputBindPersistentPolyadic(_, _, _)
            | InputBind::InputBindEmptyPersistent(_)
            | InputBind::InputBindQuotedPersistent(_, _)
    )
}

/// Is this an empty (`<- n`, no left-hand pattern) bind?
fn is_empty_bind(bind: &InputBind) -> bool {
    matches!(
        bind,
        InputBind::InputBindEmpty(_)
            | InputBind::InputBindEmptyPersistent(_)
            | InputBind::InputBindEmptyQuery(_, _)
    )
}

fn lower_drop(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        // `*@(P)` drops to `P`.
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        // `*@P` short-quote: the WPDA parser keeps the raw `NQuoteShort` node (its `fold` to
        // `NQuote(P)` runs only at eval time), and dropping `@P` yields `P`.
        Name::NQuoteShort(proc) => lower_proc(proc.as_ref(), env),
        // `*@Nil` drops the quote of `Nil` back to `Nil` (the empty process).
        Name::NQuoteNil => Ok(Par::default()),
        // Parenthesized name grouping `*(N)`: the WPDA parser keeps the raw `NParen` wrapper (its
        // `fold` to `N` runs only at eval time), so `*(N)` is just `*N`. This is the canonical
        // `*(x)` / `*(@(0))` rho drop idiom and the body of most COMM examples.
        Name::NParen(inner) => lower_drop(inner.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RhocalcAstLowerError::UnsupportedName("computed rhocalc name")),
    }
}

fn lower_name(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        // `@(P)` quotes `P`; its channel `Par` is just `P`'s lowering.
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        // `@P` short-quote (raw `NQuoteShort`; folds to `NQuote(P)` at eval time) — same channel.
        Name::NQuoteShort(proc) => lower_proc(proc.as_ref(), env),
        // `@Nil` quotes `Nil`; its channel is the empty process.
        Name::NQuoteNil => Ok(Par::default()),
        // Parenthesized name grouping `(N)` is transparent for channels (raw `NParen`; folds to `N`).
        Name::NParen(inner) => lower_name(inner.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RhocalcAstLowerError::UnsupportedName("computed rhocalc name")),
    }
}

fn lower_name_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.binders.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else if let Some(index) = flt_hole_bound_level(free_var, env) {
                // L9-6b: an FLT hole captured by an enclosing FLT receive pattern.
                Ok(new_boundvar_par(index as i32, Vec::new(), false))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false))
            }
        },
        Var::Bound(_) => Err(RhocalcAstLowerError::UnsupportedName("unopened bound name variable")),
    }
}

fn lower_proc_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.binders.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else if let Some(index) = flt_hole_bound_level(free_var, env) {
                // L9-6b: an FLT hole captured by an enclosing FLT receive pattern —
                // bound by NAME (the hole is a string metavar, so it never shares a
                // moniker `FreeVar` with this reference).
                Ok(new_boundvar_par(index as i32, Vec::new(), false))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(send_par(
                    new_gstring_par(FREE_PROC_OUTPUT.to_string(), Vec::new(), false),
                    vec![new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false)],
                ))
            }
        },
        Var::Bound(_) => {
            Err(RhocalcAstLowerError::UnsupportedProc("unopened bound process variable"))
        },
    }
}

/// L9-6b: the de-Bruijn level a free `var` binds to as an FLT hole captured by an
/// enclosing FLT receive pattern, or `None` when it names no such hole. Consulted
/// AFTER the moniker-`FreeVar` binder map misses (an FLT hole is a string metavar,
/// never a shared moniker `FreeVar`), so a genuine free variable with a colliding
/// pretty-name is never shadowed by a same-named hole in an unrelated scope — the
/// hole map only carries names introduced by an enclosing FLT pattern.
fn flt_hole_bound_level(free_var: &FreeVar<String>, env: &BoundEnv) -> Option<usize> {
    pretty_var_name(free_var).ok().and_then(|name| env.flt_hole_level(name))
}

// ── L9-6b: FLT `PFlt` elaboration (construction + pattern) ─────────────────────────────────────

/// Rewrite an FLT body's `${name}` / `${name:Cat}` metavariables to the bare guest
/// free variable `name`, so the guest parser (which knows nothing of the `${…}`
/// host hole syntax) reads each hole as an ordinary guest free variable. ONLY the
/// declared `${…}` spans are rewritten; every other byte — a spelled-out guest
/// subterm like a `lam a. lam b. a` combinator — is copied verbatim and so
/// reflects GROUND. Balanced by the lexer's raw guest mode, a `${` always closes
/// at the next `}` (a hole cannot nest), so a single left-to-right scan suffices.
fn flt_body_to_guest_syntax(body_src: &str) -> String {
    let mut out = String::with_capacity(body_src.len());
    let mut rest = body_src;
    while let Some(start) = rest.find("${") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        match after.find('}') {
            Some(end) => {
                let inner = &after[..end];
                // `name` or `name:Cat` — the guest free variable is the bare name.
                let name = inner.split(':').next().unwrap_or(inner).trim();
                out.push_str(name);
                rest = &after[end + 1..];
            },
            None => {
                // Malformed (no closing `}`): copy verbatim and stop (the assembler
                // guarantees balanced holes, so this is unreachable in practice).
                out.push_str(&rest[start..]);
                rest = "";
            },
        }
    }
    out.push_str(rest);
    out
}

/// The [`FltHole`] admission descriptors for a node's declared holes (name +
/// optional `:Cat`), in first-declaration order — the reflectors' hole input.
fn flt_holes_of(node: &FltNode) -> Vec<FltHole> {
    node.holes
        .iter()
        .map(|hole| match &hole.category {
            Some(category) => FltHole::typed(hole.name.clone(), category.clone()),
            None => FltHole::new(hole.name.clone()),
        })
        .collect()
}

/// Resolve a `PFlt` node's guest reflector + definition fingerprint, then reflect
/// its (hole-rewritten) body to a guest [`GroundTerm`] whose holes are `^free(name)`
/// leaves — the shared front half of both the construction and the pattern arm.
fn flt_resolve_and_reflect(
    node: &FltNode,
    env: &BoundEnv,
) -> Result<(GroundTerm, String), RhocalcAstLowerError> {
    let guest = env
        .resolver
        .resolve(&node.tag)
        .ok_or_else(|| RhocalcAstLowerError::UnresolvedFltTag(node.tag.clone()))?;
    let fingerprint = guest
        .metadata()
        .definition_fingerprint()
        .ok_or_else(|| RhocalcAstLowerError::FltGuestHasNoFingerprint(node.tag.clone()))?
        .to_string();
    let guest_body = flt_body_to_guest_syntax(&node.body_src);
    let ground = guest
        .parse_and_reflect_flt(&guest_body)
        .map_err(RhocalcAstLowerError::FltReflect)?;
    Ok((ground, fingerprint))
}

/// L9-6b CONSTRUCTION arm: lower a `PFlt` in a VALUE (send / re-quote) position.
/// Each declared hole `${name}` is FILLED with its in-scope binding — the reflected
/// `^bound(peano(level))` image (E-2-D-opaque to the host binder machinery, so a
/// captured hole survives the RhoCalc boundary), read by NAME from the enclosing
/// FLT pattern's hole bindings. `reflect_flt_construction` (C2) then recomputes each
/// hole-bearing node's `⌜^nog⌝` marker from the FILLED subtree — never a stale
/// `⌜^gnd⌝` — so a binder-carrying fill drives β. A hole-FREE `PFlt` (a spelled-out
/// subject) has an empty fill map and reflects to its exact ground image.
fn lower_flt_construction(node: &FltNode, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    let (ground, fingerprint) = flt_resolve_and_reflect(node, env)?;
    let mut fills: BTreeMap<String, Par> = BTreeMap::new();
    for hole in &node.holes {
        let level = env.flt_hole_level(&hole.name).ok_or_else(|| {
            RhocalcAstLowerError::FltReflect(format!(
                "construction hole ${{{}}} is not bound by an enclosing FLT pattern",
                hole.name
            ))
        })?;
        // The fill is a HOST `BoundVar` (not a reflected `⟦^bound⟧`, which is opaque
        // to the reducer): so when the enclosing receive's COMM commits, the matcher
        // SUBSTITUTES the captured value for this var INSIDE the reflected EList. Its
        // `locally_free` bit (`level`) rides up through `reflect_flt_construction`'s
        // child-`locally_free` union into the EList, marking the var for descent. Its
        // absent `^gnd` marker is read as non-ground by C2, so the hole-bearing node's
        // recomputed marker is `⌜^nog⌝` (a fill only ever makes a node LESS ground).
        fills.insert(
            hole.name.clone(),
            new_boundvar_par(level as i32, create_bit_vector(&[level]), false),
        );
    }
    reflect_flt_construction(&ground, &fills, &fingerprint)
        .map_err(|error| RhocalcAstLowerError::FltReflect(error.to_string()))
}

/// L9-6b/#14 PATTERN arm: reflect a `PFlt` receive pattern to its marked `Par`
/// pattern, its `free_count` (the receive-bind `FreeVar` count), and its hole names
/// ORDERED BY FreeVar level (`hole_names[j]` is the hole bound at this bind's
/// `FreeVar(j)`). Each hole becomes a receive match `FreeVar` ([`reflect_flt_pattern`]);
/// the CALLER interleaves `hole_names` (in FreeVar order) with any moniker binders as
/// [`ReceiveSlot`]s, so the global de-Bruijn level of each hole is assigned by
/// `extend_slots` — correct whether the FLT bind stands alone or joins moniker binders.
fn lower_flt_pattern(
    node: &FltNode,
    env: &BoundEnv,
) -> Result<(Par, i32, Vec<String>), RhocalcAstLowerError> {
    let (ground, fingerprint) = flt_resolve_and_reflect(node, env)?;
    let holes = flt_holes_of(node);
    let FltPatternReflection { pattern, free_count, mut hole_bindings, .. } =
        reflect_flt_pattern(&ground, &holes, &fingerprint)
            .map_err(|error| RhocalcAstLowerError::FltReflect(error.to_string()))?;
    // `hole_bindings` is `(name, FreeVar level)` in first-appearance order; sort by
    // level to index it positionally (defensive — first-appearance already IS level
    // order), then project to the names.
    hole_bindings.sort_by_key(|(_, level)| *level);
    let hole_names = hole_bindings.into_iter().map(|(name, _)| name).collect::<Vec<String>>();
    Ok((pattern, free_count, hole_names))
}

fn pretty_var_name(var: &FreeVar<String>) -> Result<&str, RhocalcAstLowerError> {
    var.pretty_name
        .as_deref()
        .ok_or(RhocalcAstLowerError::FreeVarWithoutName)
}

fn extend_env(env: &BoundEnv, binders: &[Binder<String>]) -> BoundEnv {
    let width = binders.len();
    let mut binder_map = env
        .binders
        .iter()
        .map(|(var, index)| (var.clone(), index + width))
        .collect::<HashMap<FreeVar<String>, usize>>();

    for (formal_index, binder) in binders.iter().enumerate() {
        binder_map.insert(binder.0.clone(), width - 1 - formal_index);
    }

    // L9-6b: FLT-hole binder levels shift up by the same `width` as the moniker
    // binders (they share the receive's de-Bruijn scope), and the extended scope
    // inherits the SAME resolver — the FLT registry is a whole-lowering constant,
    // unaffected by binder depth.
    let hole_binders = env
        .hole_binders
        .iter()
        .map(|(name, index)| (name.clone(), index + width))
        .collect::<HashMap<String, usize>>();

    BoundEnv { binders: binder_map, hole_binders, resolver: Arc::clone(&env.resolver) }
}

fn send_par(channel: Par, data: Vec<Par>) -> Par {
    let locally_free = data
        .iter()
        .fold(channel.locally_free.clone(), |acc, item| union(acc, item.locally_free.clone()));
    new_send_par(channel, data, false, locally_free.clone(), false, locally_free, false)
}

fn locally_free_union(parts: &[Par]) -> Vec<u8> {
    parts
        .iter()
        .fold(Vec::new(), |acc, part| union(acc, part.locally_free.clone()))
}

fn expr_par(expr: Expr) -> Par {
    Par::default().with_exprs(vec![expr])
}

fn receive_locally_free(binds: &[ReceiveBind], body: &Par, bind_count: usize) -> Vec<u8> {
    let sources = binds
        .iter()
        .filter_map(|bind| bind.source.as_ref())
        .fold(Vec::new(), |acc, source| union(acc, source.locally_free.clone()));
    union(sources, filter_and_adjust_bitset(&body.locally_free, bind_count))
}

fn filter_and_adjust_bitset(bitset: &[u8], bind_count: usize) -> Vec<u8> {
    let adjusted = bitset
        .iter()
        .enumerate()
        .filter_map(|(index, bit)| {
            if *bit != 0 && index >= bind_count {
                Some(index - bind_count)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    bitvec_from_indices(&adjusted)
}

fn bitvec_from_indices(indices: &[usize]) -> Vec<u8> {
    let Some(max_index) = indices.iter().copied().max() else {
        return Vec::new();
    };

    let mut bitset = vec![0; max_index + 1];
    for index in indices {
        bitset[*index] = 1;
    }
    bitset
}
