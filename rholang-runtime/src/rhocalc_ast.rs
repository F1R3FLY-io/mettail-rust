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
    Bag, Bytes, ForRow, InputBind, Int, List, Map, Name, Pathmap, Proc, RhoCalcLanguage,
    RhoCalcTerm, RhoCalcTermInner, Set,
};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, suggest_rejected_rule_dispositions,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_runtime::{
    Binder, FramedSemanticKeyHasher, FreeVar, Language, LanguageMetadata, OrdVar,
    RuntimeDovetailRunReport, Term, TermType, Var, VarTypeInfo, WeightedRewriteSeed,
    WeightedSeedId,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    EAnd, EEq, EGt, EGte, ELt, ELte, ENeq, ENot, EOr, Expr, Par, ReceiveBind,
};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_eset_par, new_freevar_par, new_gbigint_expr,
    new_gbigrat_expr, new_gbool_par, new_gdouble_expr, new_gfixedpoint_expr, new_gint_par,
    new_gstring_par, new_key_value_pair, new_new_par, new_receive_par, new_send_par,
    new_wildcard_par, union,
};

const FREE_NAME_PREFIX: &str = "mtl:";
const FREE_PROC_OUTPUT: &str = "mtl#out";

type BoundEnv = HashMap<FreeVar<String>, usize>;

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

/// Two-stage checked-Dovetail+Rho RhoCalc backend — the production default for the REPL `exec` of
/// RhoCalc.
///
/// One-way pipeline (no bidirectional bridge; see
/// `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`): the **D-stage**
/// Dovetail-saturates the whole term (native folds reduce; COMM/`new` remain for Rho lowering); the
/// **F-stage** takes the fold-normal term ([`RhoCalcLanguage::dovetail_normal_term`], extension E2),
/// lowers it to a normalized `Par`, and routes every lowerable result through the real Rho machine.
/// A term carrying a send/receive/`new` runs as that process. A closed pure value/fold with no Rho
/// effects is wrapped as `@"OUT"!(value)` so the observable result is still produced by RSpace.
pub fn dovetail_rho_backed_rhocalc(
    out_channel: impl Into<String>,
) -> Result<Box<dyn Language>, String> {
    let out_channel = out_channel.into();
    let backend = rhocalc_planned_rho_backend()?;
    let invocation = move |term: &dyn Term,
                           _report: &RuntimeDovetailRunReport|
          -> Result<crate::backend::RhoBackendInvocation, String> {
        // Lower the ORIGINAL term first: the AST mapper handles COMM (send/receive/`new`) directly
        // and reduces `int(..)`-cast embedded folds via `try_eval` (so `@("OUT")!(int(1+2,8))`
        // lowers to `@("OUT")!(3)`). ONLY if the original cannot lower (an un-reduced Proc-level
        // fold) do we fold-normalize via Dovetail (E2) and lower that. A stuck term — e.g. a
        // pure-COMM term whose receive does not reduce in Dovetail, where `dovetail_normal_term`
        // errors "stuck term" — now fails the Rho-default invocation instead of falling back to a
        // Dovetail backend report. Calling `dovetail_normal_term` unconditionally is wrong for
        // exactly that pure-COMM case.
        let call = match lower_rhocalc_term(term) {
            Ok(par) => par,
            Err(_) => match RhoCalcLanguage::dovetail_normal_term(
                term,
                RHOCALC_DOVETAIL_MAX_ITERS,
                RHOCALC_DOVETAIL_MAX_NODES,
            ) {
                Ok(normal) => lower_rhocalc_term(normal.as_ref()).map_err(|err| {
                    format!("RhoCalc normal form could not be lowered to the Rho machine: {err:?}")
                })?,
                Err(err) => {
                    return Err(format!(
                        "RhoCalc term could not be lowered directly or normalized for Rho-machine execution: {err}"
                    ))
                },
            },
        };
        let call = if call_has_runtime_effects(&call) {
            call
        } else {
            observe_pure_value_call(call, &out_channel)
        };
        Ok(crate::backend::RhoBackendInvocation::from(
            crate::backend::RhoMachineInvocation::RunWithCallAndObserveRuntimeValues {
                call,
                out_channel: out_channel.clone(),
            },
        ))
    };
    let language = crate::backend::install_dovetail_rho_runtime_backend(
        RhocalcAstRuntimeLanguage,
        backend,
        rhocalc_dovetail_report,
        rhocalc_dovetail_step_graph,
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
pub fn lower_rhocalc_proc(proc: &Proc) -> Result<Par, RhocalcAstLowerError> {
    lower_proc(proc, &BoundEnv::new())
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
    match proc {
        Proc::PZero => Ok(Par::default()),
        Proc::PDrop(name) => lower_drop(name.as_ref(), env),
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
            let body = lower_proc(body.as_ref(), &extended_env)?;
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
        Proc::CastInt(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gint_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground integer process")),
        Proc::CastBool(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gbool_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground boolean process")),
        Proc::CastStr(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gstring_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground string process")),
        Proc::PVar(var) => lower_proc_var(var, env),
        Proc::Err => Err(RhocalcAstLowerError::UnsupportedProc("error process")),
        Proc::CastBigRat(value) => value
            .as_ref()
            .try_eval()
            .map(|value| {
                let rational = value.get();
                expr_par(new_gbigrat_expr(
                    rational.numer().to_signed_bytes_be(),
                    rational.denom().to_signed_bytes_be(),
                ))
            })
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground big rational process")),
        Proc::CastFixed(value) => value
            .as_ref()
            .try_eval()
            .map(|value| {
                expr_par(new_gfixedpoint_expr(
                    value.unscaled().to_signed_bytes_be(),
                    value.places(),
                ))
            })
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground fixed-point process")),
        Proc::CastFloat(value) => value
            .as_ref()
            .try_eval()
            .map(|value| expr_par(new_gdouble_expr(value.get())))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground float process")),
        Proc::CastBigInt(value) => value
            .as_ref()
            .try_eval()
            .map(|value| expr_par(new_gbigint_expr(value.get().to_signed_bytes_be())))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground big integer process")),
        Proc::CastUInt32(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gint_par(i64::from(value), Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground u32 process")),
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
        // Ground width folds (operand statically known — NOT bound by a COMM): run the EXACT native
        // fold in place (`proc_*_bin` — the rule's own `![{…}]` body), recursively folding nested
        // ground folds via the operand's own lowering (`int(int(5,8),16) → 5`). A HELD fold (operand
        // bound by a receive) is lifted earlier in `lower_receive_body`; one reaching here was not in
        // a receive body, so it stays unsupported. This replaces the prior reliance on a two-stage
        // Dovetail normal-term pass for ground folds — needed so a term that ALSO contains a held
        // fold lowers in one pass (the Dovetail pass intentionally leaves the held fold stuck).
        Proc::IntBinProc(..)
        | Proc::UIntBinProc(..)
        | Proc::FloatBinProc(..)
        | Proc::FixedBinProc(..) => match try_eval_fold_proc(proc) {
            // Ground fold: reduced in place to a value leaf via the EXACT native fold (`proc_*_bin`,
            // nested ground folds and all). A HELD fold (operand bound by a COMM receive) reduces to
            // `None` here and is instead lifted to a trampoline in `lower_receive_body` before it
            // reaches this point.
            Some(folded) => lower_proc(&folded, env),
            None => Err(RhocalcAstLowerError::UnsupportedProc("computed rhocalc expression")),
        },
        // Boolean/comparison guard operators (used by `where`-conditions and boolean payloads):
        // lower both operands and wrap in the matching Rholang comparison/logical `Expr`.
        Proc::Eq(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EEqBody(EEq { p1, p2 }))
        },
        Proc::Ne(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ENeqBody(ENeq { p1, p2 }))
        },
        Proc::Lt(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELtBody(ELt { p1, p2 }))
        },
        Proc::Gt(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGtBody(EGt { p1, p2 }))
        },
        Proc::LtEq(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELteBody(ELte { p1, p2 }))
        },
        Proc::GtEq(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGteBody(EGte { p1, p2 }))
        },
        Proc::And(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EAndBody(EAnd { p1, p2 }))
        },
        Proc::Or(a, b) => {
            lower_binary_bool(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EOrBody(EOr { p1, p2 }))
        },
        Proc::Not(a) => {
            let operand = lower_proc(a.as_ref(), env)?;
            let locally_free = operand.locally_free.clone();
            let connective_used = operand.connective_used;
            let mut par = Par::default().with_exprs(vec![Expr {
                expr_instance: Some(ExprInstance::ENotBody(ENot { p: Some(operand) })),
            }]);
            par.locally_free = locally_free;
            par.connective_used = connective_used;
            Ok(par)
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed rhocalc expression")),
    }
}

/// Lower a binary boolean/comparison `Proc` (both operands lowered in `env`) into a Rholang
/// comparison/logical `Expr` `Par`, propagating `locally_free` and `connective_used` from the
/// operands so a guard or boolean payload that references bound/free variables is tracked correctly.
fn lower_binary_bool(
    a: &Proc,
    b: &Proc,
    env: &BoundEnv,
    build: impl FnOnce(Option<Par>, Option<Par>) -> ExprInstance,
) -> Result<Par, RhocalcAstLowerError> {
    let lhs = lower_proc(a, env)?;
    let rhs = lower_proc(b, env)?;
    let locally_free = union(lhs.locally_free.clone(), rhs.locally_free.clone());
    let connective_used = lhs.connective_used || rhs.connective_used;
    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(build(Some(lhs), Some(rhs))),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    Ok(par)
}

// ── Tier-3 held-fold trampoline lifting ──────────────────────────────────────────────────────────
//
// A held fold (e.g. `int(*(x), 8)` whose operand is bound by an enclosing COMM `receive`) cannot be
// lowered to a Rho primitive and cannot be folded by Dovetail (the operand is free until the COMM
// fires). Lift it: replace the fold with `*r`, send the operand to a Dovetail-backed fold contract,
// and bind its reply `r` via `for(@r <- ret){…}`. The contract runs the exact native fold on the
// now-ground operand. See `crate::fold_contract`.

thread_local! {
    // Held-fold sites collected during ONE lowering (cleared per `lower_rhocalc_term_with_folds`).
    // Mirrors the thread-local var-cache pattern in `mettail_runtime::binding` — single-threaded
    // lowering-session state, no locks.
    static HELD_FOLD_SITES: std::cell::RefCell<Vec<FoldSpec>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// The fold kind of a Proc width-fold constructor, if it is a trampolinable one.
fn fold_kind_of(proc: &Proc) -> Option<FoldKind> {
    match proc {
        Proc::IntBinProc(..) => Some(FoldKind::Int),
        Proc::UIntBinProc(..) => Some(FoldKind::UInt),
        Proc::FloatBinProc(..) => Some(FoldKind::Float),
        Proc::FixedBinProc(..) => Some(FoldKind::Fixed),
        _ => None,
    }
}

/// Recursively reduce a *ground* width fold to its value-leaf `Proc` via the EXACT native folds
/// (`proc_*_bin` — the rules' own `![{…}]` bodies), folding nested ground folds innermost-first
/// (`int(int(5,8),16) → 5`). Returns `None` if any leaf is not a ground numeric value (e.g. a fold
/// over a COMM-bound variable, which is instead lifted to a trampoline) or a fold errors
/// (`Proc::Err`).
fn try_eval_fold_proc(proc: &Proc) -> Option<Proc> {
    use mettail_runtime::ProcToNumericInput;
    match proc {
        Proc::IntBinProc(a, w)
        | Proc::UIntBinProc(a, w)
        | Proc::FloatBinProc(a, w)
        | Proc::FixedBinProc(a, w) => {
            let reduced = try_eval_fold_proc(a.as_ref())?;
            let width = w.as_ref().try_eval()?;
            let folded = match fold_kind_of(proc)? {
                FoldKind::Int => mettail_runtime::proc_int_bin::<Proc, i64>(&reduced, width),
                FoldKind::UInt => mettail_runtime::proc_uint_bin::<Proc, i64>(&reduced, width),
                FoldKind::Float => mettail_runtime::proc_float_bin::<Proc, i64>(&reduced, width),
                FoldKind::Fixed => mettail_runtime::proc_fixed_bin::<Proc, i64>(&reduced, width),
            };
            (!matches!(folded, Proc::Err)).then_some(folded)
        },
        // A ground numeric value leaf reduces to itself (`proc_*_bin` consumes it directly).
        _ if proc.to_numeric_input().is_some() => Some(proc.clone()),
        _ => None,
    }
}

/// An operand is *held* iff it references a name/proc variable bound in `env` — i.e. it becomes
/// ground only after a COMM binds that variable. A statically ground operand (e.g. `int(5,8)`) is
/// not held (it folds in place / via the D-stage); a free var not in `env` is a genuine error (left
/// to the existing `UnsupportedProc` path). We test the AST, not `locally_free`, because a lowered
/// bound var carries no `locally_free`.
fn operand_is_held(operand: &Proc, env: &BoundEnv) -> bool {
    proc_references_bound_var(operand, env)
}

/// Does `proc` reference a name/proc variable bound in `env`?
fn proc_references_bound_var(proc: &Proc, env: &BoundEnv) -> bool {
    match proc {
        Proc::PDrop(name) => name_references_bound_var(name, env),
        Proc::IntBinProc(a, _)
        | Proc::UIntBinProc(a, _)
        | Proc::FloatBinProc(a, _)
        | Proc::FixedBinProc(a, _) => proc_references_bound_var(a, env),
        Proc::POutput(name, payload) | Proc::PPersistOutput(name, payload) => {
            name_references_bound_var(name, env) || proc_references_bound_var(payload, env)
        },
        // Short sends `@P!(q)` / `@P!!(q)`: the channel `P` is itself a `Proc`, so check both it and
        // the payload (a held fold can ride either position once the sugar is lowered).
        Proc::POutputShort(channel_proc, payload)
        | Proc::PPersistOutputShort(channel_proc, payload) => {
            proc_references_bound_var(channel_proc, env)
                || proc_references_bound_var(payload, env)
        },
        Proc::PParInfix(left, right) => {
            proc_references_bound_var(left, env) || proc_references_bound_var(right, env)
        },
        Proc::PPar(parts) => {
            parts.iter_elements().any(|part| proc_references_bound_var(part, env))
        },
        Proc::PVar(var) => var_is_bound(var, env),
        _ => false,
    }
}

fn name_references_bound_var(name: &Name, env: &BoundEnv) -> bool {
    match name {
        Name::NVar(var) => var_is_bound(var, env),
        // `@(P)` / `@P` quote a process; a held var rides inside `P`.
        Name::NQuote(proc) | Name::NQuoteShort(proc) => proc_references_bound_var(proc, env),
        // Parenthesized grouping is transparent.
        Name::NParen(inner) => name_references_bound_var(inner, env),
        _ => false,
    }
}

fn var_is_bound(var: &OrdVar, env: &BoundEnv) -> bool {
    matches!(&var.0, Var::Free(free_var) if env.contains_key(free_var))
}

/// Find the first (innermost) held fold in `proc`, NOT descending into nested binders
/// (`PForUser`/`PNew` — their bodies are lifted separately). Returns `(operand, kind, width)`.
fn find_held_fold(proc: &Proc, env: &BoundEnv) -> Option<(Proc, FoldKind, i64)> {
    match proc {
        Proc::IntBinProc(a, w)
        | Proc::UIntBinProc(a, w)
        | Proc::FloatBinProc(a, w)
        | Proc::FixedBinProc(a, w) => {
            // Innermost-first: a nested fold inside the operand lifts before this one.
            if let Some(found) = find_held_fold(a.as_ref(), env) {
                return Some(found);
            }
            if operand_is_held(a.as_ref(), env) {
                let kind = fold_kind_of(proc)?;
                let width = w.as_ref().try_eval()?;
                return Some(((*a.as_ref()).clone(), kind, width));
            }
            None
        },
        Proc::POutput(_, payload)
        | Proc::PPersistOutput(_, payload)
        | Proc::POutputShort(_, payload)
        | Proc::PPersistOutputShort(_, payload) => find_held_fold(payload.as_ref(), env),
        Proc::PParInfix(left, right) => {
            find_held_fold(left.as_ref(), env).or_else(|| find_held_fold(right.as_ref(), env))
        },
        Proc::PPar(parts) => parts.iter_elements().find_map(|part| find_held_fold(part, env)),
        // Binder constructs (both the `PInputs` for-receive and the generalized
        // `PForUser` where-receive, plus `PNew`) have their bodies lifted separately,
        // so we do not descend here; anything else falls to the catch-all below.
        Proc::PForUser(..) | Proc::PNew(..) => None,
        _ => None,
    }
}

/// Rebuild a width-fold constructor with a replaced operand.
fn rebuild_fold(orig: &Proc, operand: Arc<Proc>, width: Arc<Int>) -> Proc {
    match orig {
        Proc::IntBinProc(..) => Proc::IntBinProc(operand, width),
        Proc::UIntBinProc(..) => Proc::UIntBinProc(operand, width),
        Proc::FloatBinProc(..) => Proc::FloatBinProc(operand, width),
        Proc::FixedBinProc(..) => Proc::FixedBinProc(operand, width),
        _ => orig.clone(),
    }
}

/// Replace the first (innermost) held fold in `proc` with `r_drop` (`*r`), mirroring
/// `find_held_fold`'s traversal. Sets `replaced` once a replacement is made.
fn replace_held_fold(proc: &Proc, env: &BoundEnv, r_drop: &Proc, replaced: &mut bool) -> Proc {
    if *replaced {
        return proc.clone();
    }
    match proc {
        Proc::IntBinProc(a, w)
        | Proc::UIntBinProc(a, w)
        | Proc::FloatBinProc(a, w)
        | Proc::FixedBinProc(a, w) => {
            let new_a = replace_held_fold(a.as_ref(), env, r_drop, replaced);
            if *replaced {
                return rebuild_fold(proc, Arc::new(new_a), w.clone());
            }
            if operand_is_held(a.as_ref(), env) {
                *replaced = true;
                return r_drop.clone();
            }
            proc.clone()
        },
        Proc::POutput(name, payload) => Proc::POutput(
            name.clone(),
            Arc::new(replace_held_fold(payload.as_ref(), env, r_drop, replaced)),
        ),
        Proc::PPersistOutput(name, payload) => Proc::PPersistOutput(
            name.clone(),
            Arc::new(replace_held_fold(payload.as_ref(), env, r_drop, replaced)),
        ),
        // Short sends: replace the held fold in the payload, keep the channel proc intact (mirrors
        // `find_held_fold`, which descends only into the payload).
        Proc::POutputShort(channel_proc, payload) => Proc::POutputShort(
            channel_proc.clone(),
            Arc::new(replace_held_fold(payload.as_ref(), env, r_drop, replaced)),
        ),
        Proc::PPersistOutputShort(channel_proc, payload) => Proc::PPersistOutputShort(
            channel_proc.clone(),
            Arc::new(replace_held_fold(payload.as_ref(), env, r_drop, replaced)),
        ),
        // Infix parallel: descend left then right. The top-of-function `*replaced` guard ensures the
        // right branch is left untouched once the (single) innermost held fold has been replaced.
        Proc::PParInfix(left, right) => {
            let new_left = replace_held_fold(left.as_ref(), env, r_drop, replaced);
            let new_right = replace_held_fold(right.as_ref(), env, r_drop, replaced);
            Proc::PParInfix(Arc::new(new_left), Arc::new(new_right))
        },
        Proc::PPar(parts) => Proc::PPar(
            parts
                .iter_elements()
                .map(|part| replace_held_fold(part, env, r_drop, replaced))
                .collect(),
        ),
        _ => proc.clone(),
    }
}

/// Lower a receive body, lifting each held fold into a Dovetail-backed fold-contract trampoline.
/// With no held fold this is exactly `lower_proc`. For one it emits
/// `new ret in { @"<fold>"!(operand, ret) | for(@r <- ret){ body[fold ↦ *r] } }` and records the
/// `FoldSpec`; the `for` body is lifted recursively (nested folds). All de Bruijn bookkeeping rides
/// `extend_env`.
fn lower_receive_body(body: &Proc, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    let Some((operand, kind, width)) = find_held_fold(body, env) else {
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
    let transformed = replace_held_fold(body, env, &r_drop, &mut replaced);

    // `new ret` shifts `env` by 1; the `for` then binds `r` (index 0), `ret` (index 1).
    let env_new = extend_env(env, &[Binder(ret_var)]);
    let env_for = extend_env(&env_new, &[Binder(r_var)]);

    // Send `@channel!(operand, ret)` at the `new` level (ret = boundvar 0).
    let operand_par = lower_proc(&operand, &env_new)?;
    let ret_channel = new_boundvar_par(0, Vec::new(), false);
    let send = send_par(channel, vec![operand_par, ret_channel.clone()]);

    // `for(@r <- ret){ <recursively-lifted transformed body> }`.
    let for_body = lower_receive_body(&transformed, &env_for)?;
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

/// Lower a term to a `Par` PLUS the held-fold contract `Definition` specs its trampolines need. The
/// `Par` already targets the fold channels; the caller registers the contracts via the runtime's
/// `extra_system_processes` seam. Equivalent to `lower_rhocalc_term` when the term has no held folds
/// (empty `Vec`).
pub fn lower_rhocalc_term_with_folds(
    term: &dyn Term,
) -> Result<(Par, Vec<FoldSpec>), RhocalcAstLowerError> {
    clear_held_fold_sites();
    let par = lower_rhocalc_term(term)?;
    Ok((par, take_held_fold_sites()))
}

/// Clear the held-fold session state. Call before a lowering whose fold contracts you intend to
/// collect with [`take_held_fold_sites`], so stale sites from a prior lowering don't leak. Used by
/// the wrapper's `start_reduction_stepper` / the exec path, which lower through the invocation
/// compiler (not [`lower_rhocalc_term_with_folds`] directly).
pub fn clear_held_fold_sites() {
    HELD_FOLD_SITES.with(|sites| sites.borrow_mut().clear());
}

/// Take (and clear) the held-fold sites recorded since the last clear. Empty if the lowering had no
/// held folds (e.g. Calculator, whose invocation compiler never lifts). The caller materializes the
/// contracts with [`crate::fold_contract::fold_definitions_for`].
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
/// - the innermost user body lifts held folds via [`lower_receive_body`]; a nested row recurses;
/// - a `where`-guard is lowered (in the extended env) and attached as `Receive.condition`.
fn lower_pfor_user(
    rows: &[ForRow],
    body: &Proc,
    env: &BoundEnv,
) -> Result<Par, RhocalcAstLowerError> {
    if rows.is_empty() {
        // No rows left: the body is the whole process.
        return lower_receive_body(body, env);
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
    let mut binds_rho: Vec<ReceiveBind> = Vec::with_capacity(binds.len());
    let mut all_binders: Vec<Binder<String>> = Vec::new();
    for bind in &binds {
        let channel = bind_channel_name(bind)
            .ok_or(RhocalcAstLowerError::UnsupportedProc("for-row channel"))?;
        let source = lower_name(channel, env)?;

        let (patterns, mut bind_binders) = if is_empty_bind(bind) {
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
        all_binders.append(&mut bind_binders);
        binds_rho.push(ReceiveBind {
            patterns,
            source: Some(source),
            remainder: None,
            free_count,
        });
    }

    let extended_env = extend_env(env, &all_binders);

    // The continuation is lowered under the extended env: a nested row recurses; otherwise this is
    // the innermost user body, where held folds are lifted into Dovetail trampolines.
    let lowered_body = match &continuation {
        Proc::PForUser(rest_rows, rest_body) => {
            lower_pfor_user(rest_rows, rest_body.as_ref(), &extended_env)?
        },
        other => lower_receive_body(other, &extended_env)?,
    };

    // `where`-guard (if any) is an ordinary boolean `Proc`, lowered in the extended env.
    let condition = match &cond {
        Some(guard) => Some(lower_proc(guard, &extended_env)?),
        None => None,
    };

    let bind_count = all_binders.len() as i32;
    let mut locally_free = receive_locally_free(&binds_rho, &lowered_body, all_binders.len());
    if let Some(cond_par) = &condition {
        // The guard is lowered in the same extended env as the body, so adjust its `locally_free`
        // the same way (drop this receive's own bound vars, shift outer references down).
        locally_free = union(
            locally_free,
            filter_and_adjust_bitset(&cond_par.locally_free, all_binders.len()),
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
            if let Some(index) = env.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
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
            if let Some(index) = env.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
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

fn pretty_var_name(var: &FreeVar<String>) -> Result<&str, RhocalcAstLowerError> {
    var.pretty_name
        .as_deref()
        .ok_or(RhocalcAstLowerError::FreeVarWithoutName)
}

fn extend_env(env: &BoundEnv, binders: &[Binder<String>]) -> BoundEnv {
    let width = binders.len();
    let mut extended = env
        .iter()
        .map(|(var, index)| (var.clone(), index + width))
        .collect::<BoundEnv>();

    for (formal_index, binder) in binders.iter().enumerate() {
        extended.insert(binder.0.clone(), width - 1 - formal_index);
    }

    extended
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
