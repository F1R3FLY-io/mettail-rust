//! AST-first lowering from MeTTaIL's `rhocalc` terms to normalized Rholang `Par`.
//!
//! This module is an oracle/integration bridge for the Rho machine backend. It
//! consumes MeTTaIL/WPDA-produced `rhocalc` AST values and constructs
//! `rhoapi::Par` directly. Rholang-looking strings in docs/tests are reader
//! annotations only; they are never parsed on this execution path.

use std::any::Any;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use mettail_languages::rhocalc::{
    Bag, List, Map, Name, Proc, RhoCalcLanguage, RhoCalcTerm, RhoCalcTermInner,
};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence, RhoRejectedRuleDisposition,
    RhoRejectedRuleDispositionKind,
};
use mettail_runtime::{
    Binder, FramedSemanticKeyHasher, FreeVar, Language, LanguageMetadata, OrdVar,
    RuntimeDovetailRunReport, Term, TermType, Var, VarTypeInfo, WeightedRewriteSeed,
    WeightedSeedId,
};
use models::rhoapi::{Expr, Par, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_freevar_par, new_gbigint_expr,
    new_gbigrat_expr, new_gbool_par, new_gdouble_expr, new_gfixedpoint_expr, new_gint_par,
    new_gstring_par, new_key_value_pair, new_new_par, new_receive_par, new_send_par, union,
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
    Box<dyn Fn(&dyn Term) -> Result<crate::backend::RhoBackendInvocation, String> + Send + Sync>;

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
) -> Result<crate::backend::RhoBackendInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoBackendInvocation::RunWithCallAndObserveStrings {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RhoCalcLanguage`
/// process and observes integers from `out_channel`.
pub fn rhocalc_observe_ints_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoBackendInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoBackendInvocation::RunWithCallAndObserveInts {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RhoCalcLanguage`
/// process and observes closed Rho ground values from `out_channel`.
pub fn rhocalc_observe_values_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoBackendInvocation, String> {
    let call = lower_rhocalc_term(term)
        .map_err(|err| format!("failed to lower RhoCalc process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoBackendInvocation::RunWithCallAndObserveRuntimeValues {
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

/// Coverage requirements routing every rejected rule through the verified native-handler boundary
/// (RhoCalc executes every process via the AST-first [`lower_rhocalc_term`] mapper). Labels are
/// de-duplicated because the same label can recur across categories and `RhoCoverageEvidence`
/// forbids duplicate dispositions. (Mirrors the `rho_rhocalc_ast` test helper, promoted for the
/// production wrapper builder.)
fn rho_native_handler_requirements(
    def: &mettail_ast::language::LanguageDef,
) -> RhoDefaultBackendRequirements {
    let lowering = lower_language_def(def);
    let dispositions: Vec<RhoRejectedRuleDisposition> = lowering
        .rejected
        .iter()
        .cloned()
        .collect::<BTreeSet<String>>()
        .into_iter()
        .map(|label| {
            RhoRejectedRuleDisposition::new(label, RhoRejectedRuleDispositionKind::NativeHandler)
        })
        .collect();
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
    let plan = plan_rho_default_backend(&def, rho_native_handler_requirements(&def))
        .map_err(|err| format!("RhoCalc Rho-default backend planning failed: {err:?}"))?;
    Ok(crate::backend::PlannedRhoBackend::from_plan(plan))
}

/// Bounds for the RhoCalc Dovetail D-stage (mirror the generated `dovetail_compiler_stage`).
const RHOCALC_DOVETAIL_MAX_ITERS: usize = 64;
const RHOCALC_DOVETAIL_MAX_NODES: usize = 1_000_000;

/// The Dovetail D-stage report producer for RhoCalc (the bare fn
/// [`crate::backend::install_dovetail_rho_runtime_backend`] wraps): saturate the term to a runtime
/// report — native folds reduce; COMM/`new` stay host-routed (non-fatal).
fn rhocalc_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    RhoCalcLanguage::dovetail_report_for(
        term,
        RHOCALC_DOVETAIL_MAX_ITERS,
        RHOCALC_DOVETAIL_MAX_NODES,
    )
}

/// Two-stage Dovetail+Rho RhoCalc backend — the production default for the REPL `exec` of RhoCalc.
///
/// One-way pipeline (no bidirectional bridge; see
/// `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`): the **D-stage**
/// Dovetail-saturates the whole term (native folds reduce; COMM/`new` stay host-routed); the
/// **F-stage** takes the fold-normal term ([`RhoCalcLanguage::dovetail_normal_term`], extension E2),
/// lowers it to a normalized `Par`, and routes by SHAPE — a term carrying a send/receive/`new` (a
/// COMM term, e.g. `@("OUT")!(int(1+2,8))` whose embedded fold already reduced to `@("OUT")!(3)`)
/// runs on the real Rho machine and observes `out_channel`; a pure value/fold (no COMM) defers to
/// the already-built Dovetail report. Arithmetic reduces in Dovetail; COMM fires on Rholang.
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
        // errors "stuck term" — defers to its Dovetail report instead of failing. (Calling
        // `dovetail_normal_term` unconditionally is WRONG for exactly that pure-COMM case.)
        let call = match lower_rhocalc_term(term) {
            Ok(par) => par,
            Err(_) => match RhoCalcLanguage::dovetail_normal_term(
                term,
                RHOCALC_DOVETAIL_MAX_ITERS,
                RHOCALC_DOVETAIL_MAX_NODES,
            ) {
                Ok(normal) => match lower_rhocalc_term(normal.as_ref()) {
                    Ok(par) => par,
                    Err(_) => {
                        return Ok(crate::backend::RhoBackendInvocation::DeferToDovetailReport)
                    },
                },
                Err(_) => return Ok(crate::backend::RhoBackendInvocation::DeferToDovetailReport),
            },
        };
        if call.sends.is_empty() && call.receives.is_empty() && call.news.is_empty() {
            // No COMM/`new` (a pure value/fold): nothing to run on the Rho machine — the Dovetail
            // report is the result.
            Ok(crate::backend::RhoBackendInvocation::DeferToDovetailReport)
        } else {
            Ok(crate::backend::RhoBackendInvocation::RunWithCallAndObserveRuntimeValues {
                call,
                out_channel: out_channel.clone(),
            })
        }
    };
    let language = crate::backend::install_dovetail_rho_runtime_backend(
        RhocalcAstRuntimeLanguage,
        backend,
        rhocalc_dovetail_report,
        invocation,
    )
    .map_err(|err| format!("RhoCalc Dovetail+Rho backend install failed: {err:?}"))?;
    Ok(Box::new(language))
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
        Proc::POutput(channel, payload) => {
            let channel = lower_name(channel.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par(channel, vec![payload]))
        },
        Proc::PInputs(channels, scope) => {
            if channels.is_empty() {
                return Err(RhocalcAstLowerError::EmptyInputJoin);
            }

            let (binders, body) = scope.clone().unbind::<String>();
            if channels.len() != binders.len() {
                return Err(RhocalcAstLowerError::InputArityMismatch {
                    names: channels.len(),
                    binders: binders.len(),
                });
            }

            let sources = channels
                .iter()
                .map(|channel| lower_name(channel, env))
                .collect::<Result<Vec<_>, _>>()?;
            let extended_env = extend_env(env, &binders);
            let body = lower_proc(body.as_ref(), &extended_env)?;

            let binds = sources
                .into_iter()
                .map(|source| ReceiveBind {
                    patterns: vec![new_freevar_par(0, Vec::new())],
                    source: Some(source),
                    remainder: None,
                    free_count: 1,
                })
                .collect::<Vec<_>>();
            let locally_free = receive_locally_free(&binds, &body, binders.len());

            Ok(new_receive_par(
                binds,
                body,
                false,
                false,
                binders.len() as i32,
                locally_free.clone(),
                false,
                locally_free,
                false,
            ))
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
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed rhocalc expression")),
    }
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

fn lower_drop(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RhocalcAstLowerError::UnsupportedName("computed rhocalc name")),
    }
}

fn lower_name(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
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
