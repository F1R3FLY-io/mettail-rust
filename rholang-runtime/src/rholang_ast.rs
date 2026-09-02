//! AST-first lowering from MeTTaIL's `rholang` terms to normalized Rholang `Par`.
//!
//! This module is an oracle/integration bridge for the Rho machine backend. It
//! consumes MeTTaIL/WPDA-produced `rholang` AST values and constructs
//! `rhoapi::Par` directly. Rholang-looking strings in docs/tests are reader
//! annotations only; they are never parsed on this execution path.

use std::any::Any;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::ddl_ast::{DdlLowerPlan, DdlRoot};
use crate::fold_contract::{fold_channel, FoldKind, FoldSpec};
use crate::guard_discharge::{self, GuardDischargeReport, LoweringOptions};
use crate::language_install::NamedRuntimeTemplateHole;
use mettail_grammar_core::RuntimeTemplatePiece;
use mettail_languages::rholang::receive::{
    desugar_for_rows, eval_guard_bool, pfor_user_still_has_query_rows,
};
use mettail_languages::rholang::{
    Bag, BigInt, BigRat, Bool, Bytes, Fixed, Float, ForRow, InputBind, Int, List, Map, Name,
    Pathmap, Proc, RholangLanguage, RholangTerm, RholangTermInner, Set, Str, UInt32, Uri,
};
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reflect_flt_construction, reflect_flt_pattern,
    suggest_rejected_rule_dispositions, EmptyFltResolver, FltHole, FltPatternReflection,
    FltResolve, GroundTerm, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, LANGUAGE_FLT_CONSTRUCT_BAND,
};
use mettail_runtime::{
    Binder, FltNode, FltPolarity, FramedSemanticKeyHasher, FreeVar, Language, LanguageMetadata,
    OrdVar, RuntimeDovetailRunReport, ScopedFltTemplate, Term, TermType, Var, VarTypeInfo,
    WeightedRewriteSeed, WeightedSeedId,
};
use models::create_bit_vector;
use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    Connective, EAnd, EDiv, EEq, EGt, EGte, ELt, ELte, EMatches, EMethod, EMinus, EMod, EMult,
    ENeg, ENeq, ENot, EOr, EPathMap, EPlus, EPlusPlus, Expr, Par, ReceiveBind, VarRef,
};
use models::rust::rholang::implicits::GPrivateBuilder;
use typed_arena::Arena;

use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_eset_par, new_freevar_par, new_gbigint_expr,
    new_gbigrat_expr, new_gbool_par, new_gbytearray_par, new_gdouble_expr, new_gfixedpoint_expr,
    new_gint_par, new_gstring_par, new_key_value_pair, new_new_par, new_receive_par, new_send_par,
    new_wildcard_par, union,
};

/// M-2's differential twin: the RECURSIVE lowering this file's driver replaced, kept verbatim
/// and compiled only under `cfg(test)`. See its module header for why a twin exists and why it
/// is not a fallback.
#[cfg(test)]
#[path = "../tests/support/rholang_ast_recursive_oracle.rs"]
mod recursive_oracle;

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
///
/// `pub(crate)` since M-1b: the formula compiler ([`crate::rholang_formula`])
/// lowers a formula's sub-TERMS with [`lower_proc_in_env`], which needs the same
/// live binder environment the surrounding term lowering is using. The fields
/// stay private to this module — `rholang_formula` only ever threads the value
/// through.
#[derive(Clone)]
pub struct BoundEnv {
    /// The compilation OPTIONS in force for this lowering — today just
    /// [`LoweringOptions::guard_discharge`] (S-D0).
    ///
    /// It rides here rather than in a global or an environment variable because the emitted
    /// artifact must be a function of the DECLARED inputs alone: two builds of the same source
    /// under the same options are byte-identical, and a validator can reproduce them. It rides
    /// on `BoundEnv` specifically because `BoundEnv` is already the lowering CONTEXT rather
    /// than a pure binder scope — it likewise carries the FLT `resolver`, which is also a
    /// compilation input — so every lowering function already receives it, with no new
    /// parameter threaded through the ~50 `lower_proc` call sites.
    ///
    /// It is scope-INVARIANT: `extend_slots`, `extend_env`, `in_pattern_position` and
    /// `with_resolver` all carry it through unchanged, so the option a caller declares at the
    /// entry point is the option every nested `for` sees.
    options: LoweringOptions,
    binders: HashMap<FreeVar<String>, usize>,
    /// L9-6b: FLT hole name → de-Bruijn level. A `${name}` hole captured by an FLT
    /// receive pattern ([`reflect_flt_pattern`]) is a receive binder, but — unlike
    /// a Rholang `PVar` binder — it is a STRING metavar, not a moniker `FreeVar`
    /// shared with the continuation's `name` reference (whose `FreeVar` carries a
    /// distinct `unique_id`). So the continuation's reference resolves by NAME
    /// through this map (`lower_proc_var`/`lower_name_var` fall back to it when the
    /// `FreeVar`-keyed lookup misses), and a construction-position `${name}` reads
    /// its fill's `^bound` level from here too.
    hole_binders: HashMap<String, usize>,
    resolver: Arc<dyn FltResolve>,
    /// M-1b: are unbound free variables being lowered in PATTERN position?
    ///
    /// `false` everywhere except inside a `matches` formula, so every pre-existing
    /// lowering path is byte-identical. Inside a formula it is `true`, and
    /// [`lower_proc_var`] / [`lower_name_var`] answer `Wildcard` instead of the
    /// free-variable MARKER (`@"mtl#out"!("mtl:v")` / `"mtl:v"`).
    ///
    /// ## Why the marker is wrong in a formula, and why `Wildcard` is right
    ///
    /// The marker is a TERM-position convention: it represents "a process
    /// reference we cannot resolve" as a distinguishable ground datum. In PATTERN
    /// position that reading is not merely unhelpful, it is a trap — it would make
    /// `x matches @"a"!(v)` mean *"x is a send on `@"a"` of the marker for `v`"*
    /// rather than the *"…of anything"* every reader (and official Rholang, and
    /// the host matcher) understands.
    ///
    /// `Wildcard` is right rather than a Rholang `FreeVar` because the guard
    /// oracle DISCARDS bindings — `SpatialMatcherOracle::matches` answers
    /// `spatial_match_result(...).is_some()` — so a pattern variable can only ever
    /// contribute "matches anything", never a usable binding. That is exactly
    /// `Wildcard`, and it needs no de-Bruijn numbering.
    ///
    /// It also makes the two evaluators agree on the nose. The generated host
    /// matcher binds a free pattern variable and merges the binding with
    /// `MatchBindings::merge`, which EXTENDS (it never rejects a conflict), so a
    /// repeated pattern variable imposes no equality constraint host-side either:
    /// host free-variable ≡ `Wildcard`, non-linear occurrences included. Pinned by
    /// `rho_matches_differential.rs`.
    free_vars_are_patterns: bool,
}

impl BoundEnv {
    /// The empty environment with the empty (no-guest) resolver, under the PRODUCTION
    /// lowering options (guard discharge ON) — the default used by every existing lowering
    /// entry point.
    pub fn new() -> Self {
        Self::with_options(LoweringOptions::PRODUCTION)
    }

    /// The empty environment under explicit [`LoweringOptions`].
    ///
    /// `LoweringOptions::NO_DISCHARGE` reproduces the pre-S-D0 compiler exactly: every `where`
    /// guard is emitted verbatim, so the emitted `Par` is byte-identical to what the previous
    /// compiler produced (pinned by the S-D0 byte-identity gate). The guard test harnesses use
    /// it so the ~100 tests that exist to exercise the RUNTIME guard evaluator keep doing so.
    pub fn with_options(options: LoweringOptions) -> Self {
        BoundEnv {
            options,
            binders: HashMap::new(),
            hole_binders: HashMap::new(),
            resolver: Arc::new(EmptyFltResolver),
            free_vars_are_patterns: false,
        }
    }

    /// M-1b: this environment, switched into PATTERN mode.
    ///
    /// The ONLY caller is `rholang_formula::lower_formula_in_env`'s
    /// `FormulaShape::Term` arm. Binders and FLT holes are carried over unchanged —
    /// a formula may legitimately reference the receive's bound variables, and
    /// those must still resolve to their `BoundVar`s; it is only the UNBOUND
    /// residue whose reading changes. See [`BoundEnv::free_vars_are_patterns`].
    pub fn in_pattern_position(&self) -> BoundEnv {
        BoundEnv {
            free_vars_are_patterns: true,
            ..self.clone()
        }
    }

    /// The empty binder environment carrying `resolver` — the L9-6b entry that
    /// installs a populated FLT registry so `PFlt` arms can elaborate.
    fn with_resolver(resolver: Arc<dyn FltResolve>) -> Self {
        Self::with_resolver_and_options(resolver, LoweringOptions::PRODUCTION)
    }

    /// [`BoundEnv::with_resolver`] under explicit [`LoweringOptions`].
    fn with_resolver_and_options(resolver: Arc<dyn FltResolve>, options: LoweringOptions) -> Self {
        BoundEnv {
            options,
            binders: HashMap::new(),
            hole_binders: HashMap::new(),
            resolver,
            free_vars_are_patterns: false,
        }
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
        BoundEnv {
            options: self.options,
            binders,
            hole_binders,
            resolver: Arc::clone(&self.resolver),
            free_vars_are_patterns: self.free_vars_are_patterns,
        }
    }
}

/// #14: one binder slot of a receive, IN BIND ORDER — a moniker `PVar` binder or a
/// name-keyed FLT hole. Unifying the two into a single ordered list lets an FLT hole
/// and a moniker binder co-occur in a `&`-join with one coherent de-Bruijn numbering.
enum ReceiveSlot {
    Moniker(Binder<String>),
    Hole(String),
}

/// Reconstruct the REAL `RholangLanguage` augmented `LanguageDef` from the
/// generated metadata's `definition_source()`.
///
/// The generated `RholangLanguage` is both the parser/AST model AND the source
/// of identity here: the dynamic Rho backend plan is built from this exact
/// augmented definition (composition + auto-injection), so its
/// `definition_fingerprint()` equals `RholangLanguage.metadata().definition_fingerprint()`.
/// The runtime wrapper therefore installs on the real Rholang identity and
/// still rejects plans for any other language — without the prior
/// fingerprint-spoofing minimal fragment.
///
/// Rholang is a standalone language (no `extends`/`includes`/`mixins`), so the
/// reconstruction is exact (see [`reconstruct_language_def`]).
pub fn rholang_ast_runtime_def() -> mettail_ast::language::LanguageDef {
    let source = RholangLanguage
        .metadata()
        .definition_source()
        .expect("generated RholangLanguage must expose its definition_source");
    mettail_rholang_codegen::reconstruct_language_def(source)
        .expect("RholangLanguage definition_source must reconstruct as a LanguageDef")
}

/// Invocation mapper used by the Rholang runtime-backed wrapper helpers.
pub type RholangInvocationMapper =
    Box<dyn Fn(&dyn Term) -> Result<crate::backend::RhoMachineInvocation, String> + Send + Sync>;

/// Rho-default wrapper type used by the Rholang helper constructors.
pub type RholangRuntimeBackedLanguage =
    crate::backend::RhoRuntimeBackedLanguage<RholangAstRuntimeLanguage, RholangInvocationMapper>;

/// Fallible Rholang runtime-backed wrapper construction result.
pub type RholangRuntimeBackedLanguageResult =
    Result<RholangRuntimeBackedLanguage, crate::backend::RhoRuntimeBackedLanguageError>;

/// Fallible rholang-to-Rholang-AST lowering error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RholangAstLowerError {
    ExpectedRholangTerm,
    ExpectedProcTerm,
    UnsupportedProc(&'static str),
    UnsupportedName(&'static str),
    FreeVarWithoutName,
    EmptyInputJoin,
    InputArityMismatch {
        names: usize,
        binders: usize,
    },
    InvalidUriBindings {
        binders: usize,
        uris: usize,
    },
    InvalidUriLiteral,
    DuplicateUriBinding(String),
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
    /// The already-parsed DDL AST could not be projected to its closed structural wire value.
    /// This is a structural encoding failure, never a request to fall back to source parsing.
    DdlWire(String),
    /// A lookahead suffix (`P[*]` / `P[n]`) was written over an operand that is not a send.
    ///
    /// The grammar takes `p:Proc` because Rholang's ~20 send sugars are all `: Proc` and there is
    /// no shared `Send` nonterminal to attach a suffix to, so "the operand must be a send" is a
    /// LOWERING obligation rather than a parsing one. It is discharged here, loudly, naming the
    /// constructor that was found — never by silently treating the lookahead as a no-op.
    LookaheadOperandNotASend(&'static str),
    /// The bound of a `P[n]` lookahead is not a ground non-negative integer literal.
    ///
    /// The step bound is consumed by the speculation engine BEFORE any reduction happens, so it
    /// has to be known at lowering time; a computed bound (`P[k + 1]`, or a bound read off a
    /// channel) would require the engine to reduce an expression to a number first. That is a
    /// named follow-on, not a silent coercion — an unusable bound fails closed here.
    LookaheadBoundNotAGroundNonNegativeInt(String),
}

/// Rholang language adapter for the AST-first Rho machine runtime path.
///
/// This adapter delegates parsing, formatting, normalization, environment
/// handling, type inference, AND metadata (including the definition
/// fingerprint) to the generated `RholangLanguage`. It exposes the real Rholang
/// identity — the dynamic Rho backend plan is built from the reconstructed real
/// `LanguageDef` ([`rholang_ast_runtime_def`]), so installation matches on the
/// genuine fingerprint rather than a reduced fragment. It does not forward the
/// generated Ascent oracle; raw `run_ascent` remains fail-closed and reference
/// comparison stays behind explicit oracle features.
pub struct RholangAstRuntimeLanguage;

impl Language for RholangAstRuntimeLanguage {
    fn name(&self) -> &'static str {
        RholangLanguage.name()
    }

    fn metadata(&self) -> &'static dyn LanguageMetadata {
        // Real generated Rholang metadata — including the real
        // `definition_fingerprint()` and `definition_source()`. No spoofing
        // shim: the dynamic backend plan is built from the reconstructed real
        // definition, so the fingerprints match by construction.
        RholangLanguage.metadata()
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        RholangLanguage.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        RholangLanguage.parse_term_for_env(input)
    }

    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        RholangLanguage.parse_term_with_weighted_seed_ids(input)
    }

    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        RholangLanguage.parse_term_with_weighted_rewrite_seeds(input)
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        RholangLanguage.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        RholangLanguage.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        RholangLanguage.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        RholangLanguage.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        RholangLanguage.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        RholangLanguage.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        RholangLanguage.clear_env(env)
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        RholangLanguage.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        RholangLanguage.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        RholangLanguage.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        RholangLanguage.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        RholangLanguage.is_env_empty(env)
    }

    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        RholangLanguage.get_env_term(env, name)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        RholangLanguage.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        RholangLanguage.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        RholangLanguage.infer_var_type(term, var_name)
    }
}

fn rholang_invocation_stage(
    mapper: RholangInvocationMapper,
) -> Result<
    crate::backend::RhoInvocationCompilerStage<RholangInvocationMapper>,
    crate::backend::RhoRuntimeBackedLanguageError,
> {
    let language_name = RholangAstRuntimeLanguage.name();
    let fingerprint = RholangAstRuntimeLanguage
        .metadata()
        .definition_fingerprint()
        .ok_or_else(|| {
            crate::backend::RhoRuntimeBackedLanguageError::MissingLanguageDefinitionFingerprint {
                language_name: language_name.to_string(),
            }
        })?;
    Ok(crate::backend::RhoInvocationCompilerStage::new(fingerprint, mapper))
}

/// Build a Rho runtime invocation that executes a parsed `RholangLanguage`
/// process and observes strings from `out_channel`.
pub fn rholang_observe_strings_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rholang_term(term)
        .map_err(|err| format!("failed to lower Rholang process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveStrings {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RholangLanguage`
/// process and observes integers from `out_channel`.
pub fn rholang_observe_ints_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rholang_term(term)
        .map_err(|err| format!("failed to lower Rholang process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveInts {
        call,
        out_channel: out_channel.into(),
    })
}

/// Build a Rho runtime invocation that executes a parsed `RholangLanguage`
/// process and observes closed Rho ground values from `out_channel`.
pub fn rholang_observe_values_invocation(
    term: &dyn Term,
    out_channel: impl Into<String>,
) -> Result<crate::backend::RhoMachineInvocation, String> {
    let call = lower_rholang_term(term)
        .map_err(|err| format!("failed to lower Rholang process to Rholang AST: {err:?}"))?;
    Ok(crate::backend::RhoMachineInvocation::RunWithCallAndObserveRuntimeValues {
        call,
        out_channel: out_channel.into(),
    })
}

/// Wrap Rholang as an AST-first Rho-default language whose default report
/// observes strings on `out_channel`.
pub fn rho_runtime_backed_rholang_strings(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RholangRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RholangInvocationMapper =
        Box::new(move |term| rholang_observe_strings_invocation(term, out_channel.clone()));
    let invocation = rholang_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RholangAstRuntimeLanguage, backend, invocation)
}

/// Wrap Rholang as an AST-first Rho-default language whose default report
/// observes integers on `out_channel`.
pub fn rho_runtime_backed_rholang_ints(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RholangRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RholangInvocationMapper =
        Box::new(move |term| rholang_observe_ints_invocation(term, out_channel.clone()));
    let invocation = rholang_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RholangAstRuntimeLanguage, backend, invocation)
}

/// Wrap Rholang as an AST-first Rho-default language whose default report
/// observes closed Rho ground values on `out_channel`.
pub fn rho_runtime_backed_rholang_values(
    backend: crate::backend::PlannedRhoBackend,
    out_channel: impl Into<String>,
) -> RholangRuntimeBackedLanguageResult {
    let out_channel = out_channel.into();
    let mapper: RholangInvocationMapper =
        Box::new(move |term| rholang_observe_values_invocation(term, out_channel.clone()));
    let invocation = rholang_invocation_stage(mapper)?;
    crate::backend::RhoRuntimeBackedLanguage::new(RholangAstRuntimeLanguage, backend, invocation)
}

/// Coverage requirements derived from the language-aware rejected-rule classifier.
/// Structural constructors are covered by generated Rho AST contracts; native/eval and unsupported
/// scalar operators are covered by Rho-native system-process rules. Labels are de-duplicated because
/// the same label can recur across categories and `RhoCoverageEvidence` forbids duplicate
/// dispositions. (Mirrors the `rho_rholang_ast` test helper, promoted for the production wrapper
/// builder.)
fn rho_default_coverage_requirements(
    def: &mettail_ast::language::LanguageDef,
) -> RhoDefaultBackendRequirements {
    let lowering = lower_language_def(def);
    let dispositions = suggest_rejected_rule_dispositions(def, &lowering);
    RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(dispositions),
        // DERIVED, not asserted — `NoGuardObligations` is a claim about the language that
        // silently becomes false the moment it declares a guard slot, and the plan then fails
        // coverage here with no local explanation. The substrate's own default disposition per
        // obligation kind is gate-compatible by construction; a language with no obligations
        // yields an empty vector, i.e. exactly the old behaviour.
        guard_coverage: RhoGuardCoverageEvidence::CoveredGuardObligations(
            mettail_rholang_codegen::guard_quality::substrate_guard_coverage(def),
        ),
    }
}

/// Build the Rholang [`crate::backend::PlannedRhoBackend`] from the REAL reconstructed Rholang
/// augmented `LanguageDef` ([`rholang_ast_runtime_def`]) — so its fingerprint equals the generated
/// `RholangLanguage` identity and the wrapper installs on the real Rholang.
pub fn rholang_planned_rho_backend() -> Result<crate::backend::PlannedRhoBackend, String> {
    let def = rholang_ast_runtime_def();
    let plan = plan_rho_default_backend(&def, rho_default_coverage_requirements(&def))
        .map_err(|err| format!("Rholang Rho-default backend planning failed: {err:?}"))?;
    Ok(crate::backend::PlannedRhoBackend::from_plan(plan))
}

/// Bounds for the Rholang Dovetail D-stage (mirror the generated `dovetail_compiler_stage`).
const RHOLANG_DOVETAIL_MAX_ITERS: usize = 64;
const RHOLANG_DOVETAIL_MAX_NODES: usize = 1_000_000;

/// The Dovetail D-stage report producer for Rholang (the bare fn
/// [`crate::backend::install_dovetail_rho_runtime_backend`] wraps): saturate the term to a runtime
/// report — native folds reduce; COMM/`new` remain Rho-machine work for the invocation stage.
fn rholang_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    RholangLanguage::dovetail_report_for(
        term,
        RHOLANG_DOVETAIL_MAX_ITERS,
        RHOLANG_DOVETAIL_MAX_NODES,
    )
}

/// The step-only Dovetail producer for Rholang — the REPL `step` navigable one-step REWRITE-step
/// graph (Increment 4): each node is a whole program state in source syntax, each edge a one-step
/// rewrite successor (structural `Exec`/`QuoteDrop`/`Extrude` + folds; COMM is not a Dovetail
/// structural rewrite), and a node with no successor is a normal form. Reached only via the `step` path
/// (`Language::run_step_backend_report`); production `exec` uses `rholang_dovetail_report`.
fn rholang_dovetail_step_graph(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
    RholangLanguage::dovetail_step_graph(
        term,
        RHOLANG_DOVETAIL_MAX_ITERS,
        RHOLANG_DOVETAIL_MAX_NODES,
    )
}

/// The Rholang F-stage lowering shared by the report-free compile and the report-carrying
/// fallback.
///
/// A-S4 (lowering purity), AS AMENDED BY S-D0: the lowering is PURE structural translation —
/// **the host computes no values that enter the program; it may decide a binder-closed guard
/// using the machine's own guard evaluator and record that decision by omitting the check.**
/// COMM (send/receive/`new`) lowers directly; arithmetic/comparison/logic lower to the machine's
/// own metered `Expr` algebra (`EPlus`/`EMinus`/…); width/precision folds lift into fold-contract
/// trampolines the MACHINE drives at COMM time (ground operands included — the former Tier-1
/// in-place `try_eval` fold is deleted); a construct with no machine algebra fails CLOSED with
/// the typed lowering error naming it. The pre-A-S4 E2 fallback (fold-normalize via
/// `dovetail_normal_term`, then lower the host-computed normal form) is DELETED: it was the last
/// host-evaluation lane on the admitted exec path.
///
/// ## Why the amendment preserves A-S4's substance (rationale, S-D0)
///
/// A-S4's letter said "the host computes no values"; its *substantive* rationales are
/// **single-source semantics** (one definition of what a construct means) and **no host/machine
/// divergence** (the answer the host would give and the answer the machine gives can never
/// differ). Compile-time guard discharge satisfies both, so only A-S4's letter needed widening:
///
/// 1. **It computes no value that enters the program.** The discharged guard's verdict is never
///    materialized as a `Par`, never sent, never bound. It is *forgotten* — the artifact simply
///    lacks a `Receive.condition`, and f1r3node's `check_commit` short-circuits an absent guard
///    to `true`, which is exactly what evaluating it would have returned. Contrast the deleted
///    E2 fallback, whose host-computed normal form WAS spliced into the emitted program.
/// 2. **It uses the machine's own evaluator.** The compile-time call is
///    `rho_pure_eval::eval_with(⟦φ⟧, Env::new(), SpatialMatcherOracle)` — the identical function,
///    on the identical `Par`, under the identical oracle, that `guard_passes` calls at COMM time.
///    For a binder-closed condition the `Env` is never read, so it is the same function on the
///    same input; there is no second semantics to diverge from. (`T-GD-5`.)
/// 3. **Divergence is fenced, not assumed away.** Discharge additionally requires the FRONT-END
///    evaluator (`eval_guard_bool`) to agree; a disagreement is a `WARN` diagnostic and a
///    `Residual`, never a silent elision. See [`crate::guard_discharge`].
///
/// The switch is a compilation INPUT ([`LoweringOptions`]), never an environment variable, so
/// the artifact stays a function of declared inputs alone.
///
/// Pure VALUE terms (no machine effects — `1 + 2`, `int(5,8)`, `"hi"`) are wrapped as
/// `@("OUT")!(term)` BEFORE lowering ([`wrap_pure_value_term`]), so the observable result is
/// produced by RSpace and any fold trampoline lifts AROUND the observation send (the machine
/// computes, then sends the result to `OUT`). For a value term with no fold this produces the
/// byte-identical `Par` the post-lowering [`observe_pure_value_call`] wrap produced (the wrap
/// commutes with lowering: `lower(@("OUT")!(v)) == observe_pure_value_call(lower(v), "OUT")`),
/// which remains in place for the multi-alternative and lowers-to-pure cases.
fn rholang_backend_invocation(
    term: &dyn Term,
    out_channel: &str,
) -> Result<crate::backend::RhoBackendInvocation, String> {
    let call = lower_rholang_exec_term(term, out_channel).map_err(|err| {
        format!(
            "Rholang term could not be lowered to the Rho machine \
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
/// at the AST level first — see [`rholang_backend_invocation`]. Multi-alternative (ambiguous)
/// terms keep the historical par-level wrap ([`observe_pure_value_call`], applied by the caller):
/// per-alternative AST wrapping would change the observation shape (one send per alternative
/// instead of one send of the union), so it is not applied there.
fn lower_rholang_exec_term(
    term: &dyn Term,
    out_channel: &str,
) -> Result<Par, RholangAstLowerError> {
    let alternatives = rholang_proc_alternatives_from_term(term)?;
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
        return Err(RholangAstLowerError::UnsupportedProc(
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
    enum Work<'a> {
        Proc(&'a Proc),
        Name(&'a Name),
    }

    // Surface desugaring returns owned nodes. The arena gives those nodes the same stable
    // reference lifetime as borrowed input nodes, so the worklist never clones a recursive
    // subtree merely to keep a continuation alive.
    let desugared_nodes = Arena::new();
    let mut work = vec![Work::Proc(proc)];
    while let Some(step) = work.pop() {
        match step {
            Work::Proc(proc) => {
                if let Some(desugared) = desugar_surface_sugar_node(proc) {
                    work.push(Work::Proc(desugared_nodes.alloc(desugared)));
                    continue;
                }
                match proc {
                    Proc::POutput(..)
                    | Proc::PPersistOutput(..)
                    | Proc::POutputShort(..)
                    | Proc::PPersistOutputShort(..)
                    | Proc::PForUser(..)
                    | Proc::CommWhere(..)
                    | Proc::PNew(..)
                    | Proc::PNewUris(..)
                    | Proc::PVar(..) => return true,
                    Proc::PPar(parts) => {
                        let first = work.len();
                        work.extend(parts.iter_elements().map(Work::Proc));
                        work[first..].reverse();
                    },
                    Proc::PParInfix(left, right) | Proc::GuardThen(left, right) => {
                        work.push(Work::Proc(right.as_ref()));
                        work.push(Work::Proc(left.as_ref()));
                    },
                    // `*(@(P))` inlines `P`; effects ride inside. `*(x)` / `*(@Nil)` lower to
                    // value pars.
                    Proc::PDrop(name) => work.push(Work::Name(name.as_ref())),
                    _ => {},
                }
            },
            Work::Name(name) => match name {
                Name::NQuote(proc) | Name::NQuoteShort(proc) => {
                    work.push(Work::Proc(proc.as_ref()));
                },
                Name::NParen(inner) => work.push(Work::Name(inner.as_ref())),
                _ => {},
            },
        }
    }
    false
}

/// Two-stage checked-Dovetail+Rho Rholang backend — the production default for the REPL `exec` of
/// Rholang.
///
/// One-way pipeline (no bidirectional bridge; see
/// `docs/architecture/rho-native-integration/09-term-level-reduction-split.md`): the **F-stage**
/// lowers the term to a normalized `Par` ([`rholang_backend_invocation`]: PURE structural AST
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
pub fn dovetail_rho_backed_rholang(
    out_channel: impl Into<String>,
) -> Result<Box<dyn Language>, String> {
    let out_channel = out_channel.into();
    let backend = rholang_planned_rho_backend()?;
    let invocation_free = {
        let out_channel = out_channel.clone();
        move |term: &dyn Term| -> Result<
            crate::backend::RhoBackendInvocation,
            crate::backend::RhoInvocationDeferral,
        > {
            rholang_backend_invocation(term, &out_channel)
                .map_err(|detail| crate::backend::RhoInvocationDeferral::GateReject { detail })
        }
    };
    let invocation = move |term: &dyn Term,
                           _report: &RuntimeDovetailRunReport|
          -> Result<crate::backend::RhoBackendInvocation, String> {
        rholang_backend_invocation(term, &out_channel)
    };
    let language = crate::backend::install_dovetail_rho_runtime_backend_lazy(
        RholangAstRuntimeLanguage,
        backend,
        rholang_dovetail_report,
        rholang_dovetail_step_graph,
        invocation_free,
        invocation,
    )
    .map_err(|err| format!("Rholang Dovetail+Rho backend install failed: {err:?}"))?;
    Ok(Box::new(language))
}

fn call_has_runtime_effects(call: &Par) -> bool {
    !call.sends.is_empty() || !call.receives.is_empty() || !call.news.is_empty()
}

fn observe_pure_value_call(value: Par, out_channel: &str) -> Par {
    send_par(new_gstring_par(out_channel.to_string(), Vec::new(), false), vec![value])
}

/// Lower a rholang process into normalized Rholang `Par`.
///
/// A-S4: width/precision folds ANYWHERE in the process (top level, send payloads, receive
/// bodies, `new` bodies — ground or COMM-held operands alike) lift into fold-contract
/// trampolines the machine drives; the host computes no fold values. Callers that execute the
/// result must register the recorded fold `Definition`s (the `clear_held_fold_sites` /
/// `take_held_fold_sites` bracket, or [`lower_rholang_term_with_folds`]).
pub fn lower_rholang_proc(proc: &Proc) -> Result<Par, RholangAstLowerError> {
    lower_rholang_proc_with_options(proc, LoweringOptions::PRODUCTION)
}

/// [`lower_rholang_proc`] under explicit compilation [`LoweringOptions`] (S-D0).
///
/// The only option today is `guard_discharge`. With
/// [`LoweringOptions::NO_DISCHARGE`](crate::guard_discharge::LoweringOptions::NO_DISCHARGE) the
/// emitted `Par` is BYTE-IDENTICAL to the pre-discharge compiler's on the whole corpus, which
/// is what the guard test harnesses rely on: they exist to exercise the RUNTIME guard
/// evaluator, and a discharged guard is one the runtime never sees. The discharge-ON arm is
/// covered by the parallel differential suite (`guard_discharge_corpus.rs`).
pub fn lower_rholang_proc_with_options(
    proc: &Proc,
    options: LoweringOptions,
) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Body(proc), &BoundEnv::with_options(options))
}

/// L9-6b: lower a Rholang `Proc` under an installed FLT resolver, so `PFlt` nodes
/// elaborate (construction position → [`reflect_flt_construction`]; receive-pattern
/// position → [`reflect_flt_pattern`]) via the guest each opener `tag` selects. With
/// the empty ([`EmptyFltResolver`]) default this is byte-identical to
/// [`lower_rholang_proc`]; a populated [`mettail_rholang_codegen::FltRegistry`]
/// (`"lambda"` → `LambdaLanguage`, …) is what drives the Foreign-Exchange demo from
/// source.
pub fn lower_rholang_proc_with_resolver(
    proc: &Proc,
    resolver: Arc<dyn FltResolve>,
) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Body(proc), &BoundEnv::with_resolver(resolver))
}

/// [`lower_rholang_proc_with_resolver`] under explicit compilation [`LoweringOptions`] (S-D0).
pub fn lower_rholang_proc_with_resolver_and_options(
    proc: &Proc,
    resolver: Arc<dyn FltResolve>,
    options: LoweringOptions,
) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Body(proc), &BoundEnv::with_resolver_and_options(resolver, options))
}

/// Lower a parsed `RholangLanguage` term into normalized Rholang `Par`.
///
/// Ambiguous generated terms are preserved as parallel branches after exact
/// semantic-key deduplication. This prevents the runtime backend from silently
/// choosing the first parse alternative.
pub fn lower_rholang_term(term: &dyn Term) -> Result<Par, RholangAstLowerError> {
    let alternatives = rholang_proc_alternatives_from_term(term)?;
    lower_proc_alternatives(alternatives)
}

/// Lower a rholang name into the normalized Rholang `Par` representation used
/// for channels.
pub fn lower_rholang_name(name: &Name) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Name(name), &BoundEnv::new())
}

fn rholang_proc_alternatives_from_term(
    term: &dyn Term,
) -> Result<Vec<&Proc>, RholangAstLowerError> {
    let typed = term
        .as_any()
        .downcast_ref::<RholangTerm>()
        .ok_or(RholangAstLowerError::ExpectedRholangTerm)?;
    let mut alternatives = Vec::new();
    collect_proc_alternatives(&typed.0, &mut alternatives)?;
    if alternatives.is_empty() {
        Err(RholangAstLowerError::ExpectedProcTerm)
    } else {
        Ok(alternatives)
    }
}

/// Flatten a parsed term's alternative tree into the list of `Proc` readings, in
/// source order.
///
/// ## ⚠ This is a CONSISTENCY fix, NOT a depth fix — and the distinction matters
///
/// This walk was the last hand-written *recursive* traversal over
/// `RholangTermInner::Ambiguous` in this crate. Every macro-generated traversal over
/// that same variant — `Clone`, `Hash`, `PartialEq`
/// (`macros/src/gen/runtime/language.rs`) — already uses an explicit work stack, and
/// says so: *"no compiler-generated recursion through nested Ambiguous trees. Per the
/// stack-safety mandate."* One hand-written exception to a mandate the generated code
/// already honours is worth removing on its own terms.
///
/// It is emphatically **not** part of the Θ(depth) work, and it must not be allowed to
/// borrow that work's justification, because **its recursion depth is bounded by 2 on
/// any parser-produced term**. Three independent mechanisms enforce that:
///
/// 1. **Construction flattens.** `<Lang>TermInner::from_alternatives`
///    (`macros/src/gen/runtime/language.rs:659`) opens with
///    `alts.into_iter().flat_map(|a| match a { Self::Ambiguous(inner) => inner, other => vec![other] })`
///    — one level of unwrapping on every construction, which maintains flatness
///    inductively as long as every input was itself flat.
/// 2. **The type says so.** The generated declaration is documented
///    *"Multiple parse alternatives (2+, flat — no nested Ambiguous)"*.
/// 3. **Four `unreachable!` guards assert it** at the `all_alts()` seams in
///    `macros/src/gen/runtime/dovetail_report.rs` and
///    `dovetail_report/typed_report.rs`: *"all_alts() returns flat alternatives, not
///    nested Ambiguous"*.
///
/// So there is no depth axis here to measure and none is gated. `Ambiguous` is a public
/// variant that a caller *can* nest by hand, which is why this walk stays total rather
/// than asserting flatness — but a bounded walk made iterative for uniformity is what
/// this is, and calling it anything grander would misrepresent it.
///
/// ## Order is load-bearing
///
/// Children are pushed in REVERSE so the LIFO pop order reproduces the recursive
/// pre-order walk exactly. That is not cosmetic: [`lower_proc_alternatives`] dedups by
/// semantic key with `BTreeSet::insert`, which keeps the FIRST occurrence, so a
/// different visit order could retain a different representative. Pinned by
/// `iterative_alternative_collection_matches_the_recursive_walk`.
fn collect_proc_alternatives<'a>(
    inner: &'a RholangTermInner,
    alternatives: &mut Vec<&'a Proc>,
) -> Result<(), RholangAstLowerError> {
    let mut work: Vec<&'a RholangTermInner> = vec![inner];
    while let Some(node) = work.pop() {
        match node {
            RholangTermInner::Proc(proc) => alternatives.push(proc),
            // Reversed, so the stack pops them left-to-right.
            RholangTermInner::Ambiguous(inner_alternatives) => {
                work.extend(inner_alternatives.iter().rev())
            },
            // Pre-order failure, exactly as the recursive form: alternatives collected
            // before the offending node stay collected, and the first bad node decides.
            _ => return Err(RholangAstLowerError::ExpectedProcTerm),
        }
    }
    Ok(())
}

fn lower_proc_alternatives<'a>(
    alternatives: impl IntoIterator<Item = &'a Proc>,
) -> Result<Par, RholangAstLowerError> {
    let mut seen = BTreeSet::new();
    let mut lowered = Vec::new();
    for proc in alternatives {
        if seen.insert(rholang_proc_semantic_key(proc)) {
            lowered.push(lower_rholang_proc(proc)?);
        }
    }

    match lowered.len() {
        0 => Err(RholangAstLowerError::ExpectedProcTerm),
        1 => Ok(lowered.pop().expect("checked len == 1")),
        _ => Ok(lowered
            .into_iter()
            .fold(Par::default(), |program, branch| program.append(branch))),
    }
}

fn rholang_proc_semantic_key(proc: &Proc) -> Vec<u8> {
    let mut hasher = FramedSemanticKeyHasher::default();
    proc.semantic_hash(&mut hasher);
    hasher.into_key()
}

/// M-1b: the crate-visible alias the formula compiler
/// ([`crate::rholang_formula::lower_formula_in_env`]) calls for a
/// [`mettail_languages::rholang::formula::FormulaShape::Term`] — an ordinary term
/// read as a pattern.
///
/// Delegating rather than duplicating is the whole point: a pattern and the term
/// it is meant to match are then lowered by literally the same code, so
/// `t matches t` cannot fail through a lowering asymmetry.
pub fn lower_proc_in_env(proc: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Proc(proc), env)
}

/// M-2 — the crate entry the formula compiler uses for a whole FORMULA.
///
/// `rholang_formula::lower_formula_in_env` is the 87th member of this file's recursion
/// component (§4.1 of the audit), so it cannot be driven by its own recursion without
/// leaving a reachable Θ(depth) path: `t matches (φ and (ψ and (…)))` nests through it.
/// It therefore delegates here, and the driver carries [`Job::Formula`] in its work
/// alphabet.
pub(crate) fn drive_formula(formula: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    drive(Seed::Formula(formula), env)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// M-2 — THE EXPLICIT-STACK LOWERING DRIVER
//
// ## What was wrong, in one paragraph
//
// The lowering was 87 mutually recursive functions (the Tarjan component of §4.1 of
// `docs/design/audits/lowering-stack-depth-audit-2026-07-27.md`, re-derived by
// `scratch/scc.py`: 19 helpers plus the 68 recursive `lower_arm_*` frames M-1 created). Every
// nesting level of the input term cost one native frame per member on the path, so a 30-byte
// program — `@"OUT"!([[[…[1]…]]])` — aborted the process with a `SIGSEGV` on the guard page at
// nesting depth 169. That is not a panic and not unwindable: it takes down the node, not the
// deploy.
//
// ★ The reproducer never recursed through a self-call. Its cycle is
// `lower_proc ▸ CastList ▸ lower_list ▸ lower_proc`, with twelve `core::iter` adapter
// monomorphizations between the last two. A conversion scoped to `lower_proc`'s own self-calls
// would have left it exactly as it was. THE WHOLE COMPONENT IS THE SUBJECT.
//
// ## The machine
//
// A deterministic, finite-control, **data-stack** transducer over a ranked tree, in the idiom
// of `prattail/src/sppf_realize.rs:164` — this repository's own explicit-stack pattern, already
// inside the WPDA pipeline. Its `Vec<(SppfId, Phase)>` with `Phase::{Enter, Leave}` is exactly
// [`Stacks::work`] carrying [`Job`] (Enter) and [`Job::Combine`] (Leave); the one deliberate
// divergence is that this machine also needs a VALUE stack, because `sppf_realize` memoizes
// results by node id in a `HashMap` and a lowering has no such reuse (each `Proc` occurrence
// lowers under its own binder environment, so a memo keyed by node would be wrong).
//
// * control: `{Enter, Combine} × Σ`, finite;
// * `δ` has exactly two shapes —
//   * **Enter**: push `Combine(k)`, then push children in REVERSE, so LIFO pops them
//     left-to-right (the order the recursive form evaluated them in, which is load-bearing:
//     the fold-site register, the receive binder counter and ERROR PRECEDENCE all depend on it);
//   * **Combine**: pop `arity(k)` values, apply the arm's post-order body, push one value;
// * final configuration: work empty, exactly one value.
//
// The stack alphabet is data-bearing (borrowed pointers, child counts, partially-built receive
// state) and therefore unbounded, so this is a STACK MACHINE, not a formal pushdown automaton.
// Saying so is cheaper than defending a class it does not occupy.
//
// ## ★ Unweighted, deliberately
//
// A `HeapSemiring` implementation was considered and declined. The one genuine `⊕` in the
// lowering — [`lower_proc_alternatives`]' `Par::append` fold over parse alternatives — fires
// ONCE, AT THE ROOT, over already-lowered whole alternatives, not at every meet point of a
// reachability computation; and `⊗` fails outright, because `Par` construction here is n-ary
// and labelled (an `EList` of 3 is not `EList(2) ⊗ EList(1)`), hence non-associative with no
// identity. `zero`/`is_zero` would be vacuous, and the impl would advertise that `poststar` /
// `prestar` apply to the lowering, which they do not. The depth fix comes from the pushdown
// part; there is no weight.
//
// ★ Relatedly: folding the recursion out must not move the merge point. Merging alternatives at
// every node IS the weighted reading, and it would collapse readings early — the loss this
// tree's "never disambiguate early" mandate forbids, reached by the back door of "integrating
// the merge into the driver". [`lower_proc_alternatives`] is untouched.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// What a drive starts from.
///
/// Two entry shapes share one machine because the formula compiler is a member of the same
/// recursion component; a second driver would be a second answer to "what does this lower to".
enum Seed<'a> {
    Proc(&'a Proc),
    /// A whole program: a binder body, so that a top-level held fold lifts to its trampoline
    /// before anything is lowered. Every `lower_rholang_proc*` entry point starts here.
    Body(&'a Proc),
    Name(&'a Name),
    Formula(&'a Proc),
}

/// An index into the drive's environment arena.
///
/// ★ **`BoundEnv` rides as a DELTA, never owned per work item.** It holds a
/// `HashMap<FreeVar<String>, usize>`, an FLT hole-level map and an `Arc<dyn FltResolve>`, so an
/// owned environment per work item would clone that map once per level and leave the traversal
/// Θ(depth) in HEAP anyway — refuted by measurement on the sibling f1r3node conversion, which
/// is why it is stated here as a constraint rather than a preference. Work items carry this
/// `u32`; an environment is materialised exactly once per BINDER SITE, which is precisely what
/// the recursive form did.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct EnvId(u32);

/// The environment the drive was called with. It is BORROWED, so the common case — a term with
/// no binders at all — allocates no environment whatsoever.
const ROOT_ENV: EnvId = EnvId(0);

/// The drive's environment store: one borrowed root plus the environments derived at binder
/// sites (`new`, a receive's continuation scope, a held-fold trampoline, a formula's pattern
/// position).
///
/// Derived environments are never freed before the drive ends. That is a deliberate trade: a
/// `Kont` may still name one, and reference-counting them would cost more than the few hundred
/// bytes a binder site's `HashMap` occupies. The recursive form held exactly the same set alive
/// on its native stack for the duration of the corresponding subtree.
struct EnvArena<'a> {
    root: &'a BoundEnv,
    derived: Vec<BoundEnv>,
}

impl<'a> EnvArena<'a> {
    fn new(root: &'a BoundEnv) -> Self {
        EnvArena { root, derived: Vec::new() }
    }

    fn get(&self, id: EnvId) -> &BoundEnv {
        match id.0 {
            0 => self.root,
            n => &self.derived[(n - 1) as usize],
        }
    }

    fn push(&mut self, env: BoundEnv) -> EnvId {
        self.derived.push(env);
        EnvId(
            u32::try_from(self.derived.len())
                .expect("rholang lowering: more than 2^32 binder sites in one term"),
        )
    }
}

/// The `ExprInstance` constructors [`Kont::BinExpr`] can name.
///
/// A DATA tag rather than the `impl FnOnce(Option<Par>, Option<Par>) -> ExprInstance` the
/// recursive `lower_binary_expr` took: a continuation has to be storable in a `Vec`, and a
/// closure whose type is unique per call site is not. The mapping back to the constructor is
/// [`BinOp::build`], one arm each, so the two statements sit next to each other.
#[derive(Clone, Copy, Debug)]
enum BinOp {
    Minus,
    Mult,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
    And,
    Or,
    /// `++` — the target string-concatenation expression selected by `Proc::Add` over two ground
    /// strings.
    PlusPlus,
    /// `+` — numeric addition.
    Plus,
}

impl BinOp {
    fn build(self, p1: Option<Par>, p2: Option<Par>) -> ExprInstance {
        match self {
            BinOp::Minus => ExprInstance::EMinusBody(EMinus { p1, p2 }),
            BinOp::Mult => ExprInstance::EMultBody(EMult { p1, p2 }),
            BinOp::Div => ExprInstance::EDivBody(EDiv { p1, p2 }),
            BinOp::Mod => ExprInstance::EModBody(EMod { p1, p2 }),
            BinOp::Eq => ExprInstance::EEqBody(EEq { p1, p2 }),
            BinOp::Neq => ExprInstance::ENeqBody(ENeq { p1, p2 }),
            BinOp::Lt => ExprInstance::ELtBody(ELt { p1, p2 }),
            BinOp::Gt => ExprInstance::EGtBody(EGt { p1, p2 }),
            BinOp::Lte => ExprInstance::ELteBody(ELte { p1, p2 }),
            BinOp::Gte => ExprInstance::EGteBody(EGte { p1, p2 }),
            BinOp::And => ExprInstance::EAndBody(EAnd { p1, p2 }),
            BinOp::Or => ExprInstance::EOrBody(EOr { p1, p2 }),
            BinOp::PlusPlus => ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 }),
            BinOp::Plus => ExprInstance::EPlusBody(EPlus { p1, p2 }),
        }
    }
}

/// The `ExprInstance` constructors [`Kont::UnExpr`] can name. See [`BinOp`].
#[derive(Clone, Copy, Debug)]
enum UnOp {
    Neg,
    Not,
}

impl UnOp {
    fn build(self, p: Option<Par>) -> ExprInstance {
        match self {
            UnOp::Neg => ExprInstance::ENegBody(ENeg { p }),
            UnOp::Not => ExprInstance::ENotBody(ENot { p }),
        }
    }
}

/// The receive under construction, threaded through [`Kont::ForSource`] →
/// [`Kont::ForPattern`] → [`Kont::ForBody`] → [`Kont::ForGuard`].
///
/// `lower_pfor_user` is the one member whose CHILD LIST IS NOT KNOWN UP FRONT: the
/// continuation's binder scope is derived from the binders its own PATTERNS introduce, so the
/// body cannot be scheduled until the patterns are lowered. The machine handles that with
/// STAGED continuations — a `Combine` that pops its values and pushes fresh work plus a
/// successor continuation. The deficit invariant survives it exactly (see [`Stacks::check`]):
/// popping `n` values and a continuation of arity `n`, then pushing `m` jobs and a continuation
/// of arity `m`, moves every term by an equal and opposite amount.
///
/// `Box`ed at the `Kont` site so one large stage does not set the size of every work item.
struct ForState<'a> {
    /// The rows of THIS `for`, `rows[0]` being the one under construction.
    rows: &'a [ForRow],
    /// The `for`'s body, shared by every row's continuation.
    body: &'a Proc,
    /// The scope the row's SOURCES and PATTERNS are read in (the enclosing scope).
    env: EnvId,
    /// `rows[0]`'s binds, BORROWED. The recursive `decompose_for_row` cloned each
    /// `InputBind` out of its `Arc`; nothing reads the clone, so the driver borrows.
    binds: Vec<&'a InputBind>,
    /// Per-bind prepared-pattern token binder. `Some` means this bind's FLT
    /// selector is lexical and its pattern must use the opaque token envelope.
    pattern_tokens: Vec<Option<FreeVar<String>>>,
    /// Nested pre-publication preparation frames, outermost first.
    pattern_preparations: Vec<PatternPrepFrame>,
    persistent: bool,
    cond: Option<&'a Proc>,
    /// How many of `binds` are done. `binds[next_bind]` is the one in flight.
    next_bind: usize,
    binds_rho: Vec<ReceiveBind>,
    slots: Vec<ReceiveSlot>,
    /// The lowered SOURCE of the bind in flight, held across its pattern's subtree. The
    /// recursive form kept it in a local across `lower_pattern_proc`'s call; the machine has no
    /// native frame to keep it in, so it rides the stage.
    pending_source: Option<Par>,
    /// The continuation scope, derived once every bind is done.
    extended_env: EnvId,
    /// The lowered continuation, held while the guard is lowered.
    lowered_body: Option<Par>,
}

struct PatternPrepFrame {
    channel: Par,
    request: Par,
}

/// The counter and binder list one receive PATTERN accumulates.
///
/// `lower_pattern_proc` threaded `&mut i32` and `&mut Vec<Binder<String>>` through a pre-order
/// walk. The driver gives each bind its own cell and jobs carry the cell's index, which
/// reproduces the threading exactly: the machine is depth-first, so a pattern's whole subtree
/// is drained before its next sibling job is entered, and the `PVar` leaves therefore visit in
/// the same left-to-right order that incremented the recursive counter.
#[derive(Default)]
struct PatternState {
    counter: i32,
    binders: Vec<Binder<String>>,
}

/// A unit of work: one subtree still to be lowered, or one continuation ready to run.
///
/// Every variant but [`Job::Combine`] is an **Enter**; `Combine` is a **Leave**.
enum Job<'a> {
    /// `lower_proc` — an ordinary term.
    Proc(&'a Proc, EnvId),
    /// `lower_name` / `lower_drop` — a channel or a dereference. The two were textually
    /// identical functions (they differ only in which of themselves the `NParen` arm recurses
    /// into, and both recurse into themselves), so the machine has one job for both.
    Name(&'a Name, EnvId),
    /// `lower_body_lifting_folds` — a binder body, with held width/precision folds lifted to
    /// trampolines before it is lowered.
    Body(&'a Proc, EnvId),
    /// `lower_pfor_user` — the receive rows still to nest, and the body under all of them.
    ForRows(&'a [ForRow], &'a Proc, EnvId),
    /// `lower_pattern_proc` — a receive pattern, whose free variables become binders in
    /// `pattern_states[slot]`.
    Pattern(&'a Proc, u32),
    /// `rholang_formula::lower_formula_in_env` — a spatial formula, compiled to a pattern.
    Formula(&'a Proc, EnvId),
    /// Run a continuation over the values its children left.
    Combine(Kont<'a>),
}

/// A continuation: the post-order half of one arm, plus whatever that arm needs to remember.
enum Kont<'a> {
    /// `parts.try_fold(Par::default(), append)` — the `PPar` bag.
    ParFold(usize),
    /// `left.append(right)` — `PParInfix`. Distinct from [`Kont::ParFold`] with `n = 2` on
    /// purpose: it is a different expression, and the differential compares expressions.
    ParPair,
    /// `send_par` / `send_par_persistent` over `(channel, payload)`.
    Send { persistent: bool },
    /// `binary_expr_par(lhs, rhs, op)`.
    BinExpr(BinOp),
    /// `unary_expr_par(operand, op)`.
    UnExpr(UnOp),
    /// `Proc::Add` — `EPlusPlus` when BOTH operands lower to ground strings, else `EPlus`. The
    /// parity is decided in the COMBINE, on the lowered operands, exactly as the recursive arm
    /// decided it.
    AddParity,
    /// `Proc::Implies` — `(not a) or b`, with the negation wrapping ONLY the antecedent.
    Implies,
    /// `lower_method`: an `EMethod` over `1 + argc` children, receiver first. The name is
    /// borrowed from `Proc::MethodCall`; accepting `&'a str` keeps arbitrary identifier
    /// names allocation-free until the final protobuf node is assembled.
    Method { name: &'a str, argc: usize },
    /// `EMatches` over `(target, pattern)`.
    Matches,
    /// §18.1's static-`false` fold: the formula is unsatisfiable by construction, so the whole
    /// guard is `GBool(false)` carrying the target's `locally_free`. The TARGET is still
    /// lowered — folding must not turn an ill-formed program into a well-formed `false`.
    MatchesStaticallyFalse,
    /// `new_elist_par` over `n` items — `CastList`, and the payload of the `!(a, b, …)` and
    /// `!()` send sugars.
    ListLit(usize),
    /// Structural Greg/Mike DDL projection. Its children are precisely the embedded Rholang
    /// process leaves (`Data(v)` and non-theory module programs); the post-order DDL plan owns
    /// every other node. This keeps mutual `DDL -> Proc -> DDL` nesting on the heap work stack.
    Ddl(Box<DdlLowerPlan<'a>>),
    /// `new_eset_par` over `n` elements, pre-sorted at Enter.
    SetLit(usize),
    /// `new_emap_par` over `n` key/value pairs, i.e. `2n` children.
    MapLit(usize),
    /// `lower_bag`'s tagged 2-element ABI encoding, carrying each item's multiplicity.
    BagLit(Vec<i64>),
    /// `lower_pathmap` — a homogeneous `EPathMap`. Set mode consumes `len`
    /// keys; map mode consumes `2 * len` interleaved keys and values. Empty is
    /// represented by `map == false, len == 0` and remains mode-neutral.
    PathmapLit { map: bool, len: usize },
    /// `PNew`'s `new`-scope wrapper over its lowered body.
    New { binder_count: usize, uris: Vec<String> },
    /// `x!(P)[*]` — an unbounded speculation request over `(channel, payload)`.
    SpecAll,
    /// `x!(P)[n]` — a bounded speculation request over `(channel, payload)`.
    SpecN { bound: i64 },
    /// `lower_body_lifting_folds`' trampoline: `new(ret){ fold!(operand, ret) | for(r <- ret){ … } }`
    /// over `(operand, for_body)`.
    ///
    /// `Box`ed for the reason [`ForState`] is, and the measurement is the same shape. A
    /// `Par` is 248 bytes; the next-largest `Kont` is [`Kont::Method`] at 24. Inline, this
    /// one field therefore set the width of EVERY `Kont`, hence of [`Job::Combine`], hence
    /// of every element of both stacks — 248 bytes moved per push and per pop of work that
    /// needs 24. Boxed, `Kont` is 32 bytes and `Job` is 40.
    ///
    /// The trade is one heap allocation against that, and it is not close: the allocation
    /// happens once per HELD-FOLD SITE, of which the overwhelming majority of programs
    /// have none, while the width is paid on every node of every term. MEASURED on a
    /// six-program lowering benchmark containing NO held folds at all — the case where
    /// boxing can only cost and never pay — the change was a 3.06 % IMPROVEMENT:
    /// 123.97 µs → 120.18 µs per iteration, Welch t = 29.8, p ≈ 6e-195, n = 1200 per arm
    /// over three interleaved rounds on a pinned core. Clippy's literal suggestion,
    /// `Combine(Box<Kont>)`, is the opposite trade — an allocation on the HOT path to hide
    /// a cold variant's width — and must not be taken.
    HeldFold { channel: Box<Par> },
    /// Run-time-selected FLT construction. `request` already contains the
    /// lexical handle, structural telescope, fills, and private reply channel
    /// under the surrounding `new`; the sole child is the transformed body.
    InstalledFlt { channel: Box<Par>, request: Box<Par> },
    /// Stage A of `lower_pfor_user`: the SOURCE of `binds[next_bind]` is on the value stack.
    ForSource(Box<ForState<'a>>),
    /// Stage B: the PATTERN of `binds[next_bind]` is on the value stack.
    ForPattern(Box<ForState<'a>>, u32),
    /// Stage C: the lowered CONTINUATION is on the value stack.
    ForBody(Box<ForState<'a>>),
    /// Stage D: the lowered GUARD is on the value stack.
    ForGuard(Box<ForState<'a>>),
    /// `lower_pattern_proc`'s list former.
    PatListLit(usize),
    /// `lower_pattern_proc`'s set former.
    PatSetLit(usize),
    /// `lower_pattern_proc`'s map former (`2n` children).
    PatMapLit(usize),
    /// `φ and ψ` — `ConnAndBody`.
    FormulaAnd,
    /// `φ or ψ` — `ConnOrBody`.
    FormulaOr,
    /// `not φ` — `ConnNotBody`.
    FormulaNot,
    /// `φ implies ψ` — `(not φ) or ψ`.
    FormulaImplies,
    /// `{ φ | ψ | … }` — the separating conjunction, `n` parts appended.
    FormulaSeparation(usize),
}

impl Kont<'_> {
    /// How many values this continuation pops.
    ///
    /// ⚠ Written as an exhaustive `match` that DELIBERATELY DUPLICATES the pop counts in
    /// [`Drive::combine`]. The duplication is the point: [`Stacks::check`] cross-checks the two
    /// statements on every step of every term, so a continuation whose arity and whose body
    /// disagree fails on the FIRST malformed configuration, on ANY input — whereas a
    /// differential fires only if the corpus happens to contain the witness.
    fn arity(&self) -> usize {
        match self {
            Kont::ParFold(n) => *n,
            Kont::ParPair => 2,
            Kont::Send { .. } => 2,
            Kont::BinExpr(_) => 2,
            Kont::UnExpr(_) => 1,
            Kont::AddParity => 2,
            Kont::Implies => 2,
            Kont::Method { argc, .. } => 1 + *argc,
            Kont::Matches => 2,
            Kont::MatchesStaticallyFalse => 1,
            Kont::ListLit(n) => *n,
            Kont::Ddl(plan) => plan.process_jobs().len(),
            Kont::SetLit(n) => *n,
            Kont::MapLit(n) => 2 * *n,
            Kont::BagLit(counts) => counts.len(),
            Kont::PathmapLit { map, len } => {
                if *map {
                    2 * *len
                } else {
                    *len
                }
            },
            Kont::New { .. } => 1,
            Kont::SpecAll => 2,
            Kont::SpecN { .. } => 2,
            Kont::HeldFold { .. } => 2,
            Kont::InstalledFlt { .. } => 1,
            // The four receive stages are STAGED: each awaits exactly one value.
            Kont::ForSource(_) => 1,
            Kont::ForPattern(..) => 1,
            Kont::ForBody(_) => 1,
            Kont::ForGuard(_) => 1,
            Kont::PatListLit(n) => *n,
            Kont::PatSetLit(n) => *n,
            Kont::PatMapLit(n) => 2 * *n,
            Kont::FormulaAnd => 2,
            Kont::FormulaOr => 2,
            Kont::FormulaNot => 1,
            Kont::FormulaImplies => 2,
            Kont::FormulaSeparation(n) => *n,
        }
    }

    /// This continuation's variant name.
    ///
    /// Exists for the differential's ANTI-VACUITY coverage assertion
    /// (`the_corpus_reaches_every_kont`): a corpus that never reaches a continuation proves
    /// nothing about it, and a coverage check that cannot NAME the gap is not a check. Paired
    /// with [`KONT_NAMES`], which must list exactly these strings — the test fails if a variant
    /// is added and no corpus entry reaches it.
    #[cfg(test)]
    fn name(&self) -> &'static str {
        match self {
            Kont::ParFold(_) => "ParFold",
            Kont::ParPair => "ParPair",
            Kont::Send { .. } => "Send",
            Kont::BinExpr(_) => "BinExpr",
            Kont::UnExpr(_) => "UnExpr",
            Kont::AddParity => "AddParity",
            Kont::Implies => "Implies",
            Kont::Method { .. } => "Method",
            Kont::Matches => "Matches",
            Kont::MatchesStaticallyFalse => "MatchesStaticallyFalse",
            Kont::ListLit(_) => "ListLit",
            Kont::Ddl(_) => "Ddl",
            Kont::SetLit(_) => "SetLit",
            Kont::MapLit(_) => "MapLit",
            Kont::BagLit(_) => "BagLit",
            Kont::PathmapLit { .. } => "PathmapLit",
            Kont::New { .. } => "New",
            Kont::SpecAll => "SpecAll",
            Kont::SpecN { .. } => "SpecN",
            Kont::HeldFold { .. } => "HeldFold",
            Kont::InstalledFlt { .. } => "InstalledFlt",
            Kont::ForSource(_) => "ForSource",
            Kont::ForPattern(..) => "ForPattern",
            Kont::ForBody(_) => "ForBody",
            Kont::ForGuard(_) => "ForGuard",
            Kont::PatListLit(_) => "PatListLit",
            Kont::PatSetLit(_) => "PatSetLit",
            Kont::PatMapLit(_) => "PatMapLit",
            Kont::FormulaAnd => "FormulaAnd",
            Kont::FormulaOr => "FormulaOr",
            Kont::FormulaNot => "FormulaNot",
            Kont::FormulaImplies => "FormulaImplies",
            Kont::FormulaSeparation(_) => "FormulaSeparation",
        }
    }
}

/// Every continuation the machine can push, by name. See [`Kont::name`].
#[cfg(test)]
pub(crate) const KONT_NAMES: &[&str] = &[
    "ParFold",
    "ParPair",
    "Send",
    "BinExpr",
    "UnExpr",
    "AddParity",
    "Implies",
    "Method",
    "Matches",
    "MatchesStaticallyFalse",
    "ListLit",
    "Ddl",
    "SetLit",
    "MapLit",
    "BagLit",
    "PathmapLit",
    "New",
    "SpecAll",
    "SpecN",
    "HeldFold",
    "InstalledFlt",
    "ForSource",
    "ForPattern",
    "ForBody",
    "ForGuard",
    "PatListLit",
    "PatSetLit",
    "PatMapLit",
    "FormulaAnd",
    "FormulaOr",
    "FormulaNot",
    "FormulaImplies",
    "FormulaSeparation",
];

#[cfg(test)]
thread_local! {
    /// The continuation names the most recent drive pushed. Written by [`Stacks::push`] and
    /// read by [`kont_trace`]; `cfg(test)` only, so the production drive carries no
    /// instrumentation at all.
    static KONT_TRACE: RefCell<std::collections::BTreeSet<&'static str>> =
        const { RefCell::new(std::collections::BTreeSet::new()) };
}

/// Lower `proc` and merge the continuations the drive pushed into `seen`.
///
/// The differential's coverage instrument. It runs the REAL driver — not a model of it — so a
/// continuation that the corpus reaches only on an error path still counts, and one that no
/// longer exists cannot be counted.
#[cfg(test)]
pub(crate) fn kont_trace(
    proc: &Proc,
    env: &BoundEnv,
    seen: &mut std::collections::BTreeSet<&'static str>,
) {
    KONT_TRACE.with(|trace| trace.borrow_mut().clear());
    let _ = drive(Seed::Proc(proc), env);
    KONT_TRACE.with(|trace| seen.extend(trace.borrow().iter().copied()));
}

/// The two stacks, plus the three incremental counters the deficit invariant needs.
struct Stacks<'a> {
    work: Vec<Job<'a>>,
    values: Vec<Par>,
    /// `D` — the number of **Enter** items in `work`.
    enters: usize,
    /// `|C|` — the number of pending continuations in `work`.
    konts: usize,
    /// `Σ_{k ∈ C} arity(k)`.
    kont_arity: usize,
}

impl<'a> Stacks<'a> {
    fn new(seed: Job<'a>) -> Self {
        // Preallocated: a term deep enough to matter will need these, and growing a `Vec` under
        // a hot post-order walk is pure waste. 64 covers every term in the test corpus without
        // a realloc; deeper terms grow amortised.
        let mut stacks = Stacks {
            work: Vec::with_capacity(64),
            values: Vec::with_capacity(64),
            enters: 0,
            konts: 0,
            kont_arity: 0,
        };
        stacks.push(seed);
        stacks
    }

    fn push(&mut self, job: Job<'a>) {
        match &job {
            Job::Combine(kont) => {
                self.konts += 1;
                self.kont_arity += kont.arity();
                #[cfg(test)]
                KONT_TRACE.with(|trace| trace.borrow_mut().insert(kont.name()));
            },
            _ => self.enters += 1,
        }
        self.work.push(job);
    }

    fn pop(&mut self) -> Option<Job<'a>> {
        let job = self.work.pop()?;
        match &job {
            Job::Combine(kont) => {
                self.konts -= 1;
                self.kont_arity -= kont.arity();
            },
            _ => self.enters -= 1,
        }
        Some(job)
    }

    fn value(&mut self, par: Par) {
        self.values.push(par);
    }

    /// Pop exactly one value. Every caller has already been told how many to expect by
    /// [`Kont::arity`], so an empty stack here is a machine bug, not an input error.
    fn pop_value(&mut self) -> Par {
        self.values
            .pop()
            .expect("rholang lowering: continuation popped more values than its arity")
    }

    /// Pop the last `n` values, LEFT TO RIGHT. Children are pushed in reverse and therefore
    /// pop — and push their values — in source order, so the tail of the value stack is
    /// already in the order an `EList` wants.
    fn pop_values(&mut self, n: usize) -> Vec<Par> {
        let start = self
            .values
            .len()
            .checked_sub(n)
            .expect("rholang lowering: continuation popped more values than its arity");
        self.values.split_off(start)
    }

    /// ★ **The deficit invariant**, asserted at the head of the drive loop.
    ///
    /// ```math
    /// |V| \;+\; D \;+\; |C| \;-\; \sum_{k \in C}\mathrm{arity}(k) \;=\; 1
    /// ```
    ///
    /// Read it as: *the machine owes exactly one value*. Every Enter still to run will produce
    /// one; every pending continuation will consume `arity` and produce one, a net debt of
    /// `arity − 1`; every value already on the stack is one paid. Verified transition by
    /// transition — over the two shapes `δ` has, in their general form, so exhaustively over
    /// reachable configurations rather than by spot check:
    ///
    /// | # | configuration | `\|V\|` | `D` | `\|C\|` | `Σ arity` | total |
    /// |---|---|---|---|---|---|---|
    /// | 0 | initial: `work = [Enter(root)]` | 0 | 1 | 0 | 0 | **1** ✓ |
    /// | 1 | after `Enter` of an `n`-ary node | 0 | `n` | 1 | `n` | **1** ✓ |
    /// | 2 | after `Enter` of a leaf (`n = 0`) | +1 | −1 | 0 | 0 | **1** ✓ |
    /// | 3 | after `j` of the `n` children resolve | `j` | `n − j` | 1 | `n` | **1** ✓ |
    /// | 4 | all `n` resolved | `n` | 0 | 1 | `n` | **1** ✓ |
    /// | 5 | after `Combine(k)` | `n − n + 1` | 0 | 0 | 0 | **1** ✓ |
    /// | 6 | final: work empty, one value | 1 | 0 | 0 | 0 | **1** ✓ |
    ///
    /// A STAGED continuation (row 5', the receive) pops `n` values and a continuation of arity
    /// `n`, then pushes `m` Enters and a continuation of arity `m`: `−n + m + 0 − (−n + m) = 0`.
    ///
    /// ⚠ An earlier form, `\|V\| + D = 1 + Σ arity`, is **wrong** — off by `|C|`, and it fires
    /// immediately after the root descends.
    ///
    /// ⚠ Maintained with INCREMENTAL counters, never an O(n) rescan: the gate bisects at depth
    /// 4,096, and a rescan would make the debug build O(n²) on exactly the terms that matter.
    #[inline]
    fn check(&self) {
        debug_assert_eq!(
            self.values.len() + self.enters + self.konts,
            1 + self.kont_arity,
            "rholang lowering: deficit invariant violated — |V|={} D={} |C|={} Σarity={}",
            self.values.len(),
            self.enters,
            self.konts,
            self.kont_arity
        );
    }
}

/// Everything one drive owns.
struct Drive<'a> {
    /// Nodes the drive MATERIALISES and must keep alive: a desugared send head, a fold operand,
    /// a fold-lifted body, an unbound `new` body, a receive's pattern process.
    ///
    /// `typed_arena::Arena` rather than a hand-rolled `Vec<Box<_>>`, because this crate is
    /// `#![forbid(unsafe_code)]` and the safe formulation of "hand out `&'arena T` while still
    /// accepting new allocations" is precisely what that crate is. It adds no crate to the
    /// build graph — it was already in `Cargo.lock` as a transitive dependency.
    arena: &'a Arena<Arc<Proc>>,
    envs: EnvArena<'a>,
    stacks: Stacks<'a>,
    /// One cell per receive bind that carries a `lower_pattern_proc` walk.
    pattern_states: Vec<PatternState>,
    /// `BoundEnv::new()`, materialised at most once. `lower_pattern_proc`'s fallback arm lowers
    /// a non-collection pattern in a FRESH empty environment, not the enclosing one; the
    /// recursive form built a new one at each such site, and they are all equal and immutable.
    empty_env: Option<EnvId>,
}

impl<'a> Drive<'a> {
    /// Keep a materialised node alive for the rest of the drive and borrow it back.
    ///
    /// `Arc<Proc>` rather than `Proc` so the two producers that already hand out an `Arc`
    /// (`Scope::unbind`, and the AST's own `Arc` fields) cost a refcount bump instead of a deep
    /// clone.
    fn keep(&self, node: Arc<Proc>) -> &'a Proc {
        self.arena.alloc(node)
    }

    fn env(&self, id: EnvId) -> &BoundEnv {
        self.envs.get(id)
    }

    fn empty_env(&mut self) -> EnvId {
        match self.empty_env {
            Some(id) => id,
            None => {
                let id = self.envs.push(BoundEnv::new());
                self.empty_env = Some(id);
                id
            },
        }
    }

    /// Push `children` so that LIFO pops them in the given (source) order.
    fn push_children(&mut self, kont: Kont<'a>, children: impl IntoIterator<Item = Job<'a>>) {
        let children: Vec<Job<'a>> = children.into_iter().collect();
        debug_assert_eq!(
            children.len(),
            kont.arity(),
            "rholang lowering: a continuation was pushed with a child count that disagrees \
             with Kont::arity"
        );
        self.stacks.push(Job::Combine(kont));
        for child in children.into_iter().rev() {
            self.stacks.push(child);
        }
    }
}

/// Run the machine to its final configuration.
fn drive(seed: Seed<'_>, root_env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    let arena: Arena<Arc<Proc>> = Arena::new();
    let seed_job = match seed {
        Seed::Proc(proc) => Job::Proc(proc, ROOT_ENV),
        Seed::Body(body) => Job::Body(body, ROOT_ENV),
        Seed::Name(name) => Job::Name(name, ROOT_ENV),
        Seed::Formula(formula) => Job::Formula(formula, ROOT_ENV),
    };
    let mut drive = Drive {
        arena: &arena,
        envs: EnvArena::new(root_env),
        stacks: Stacks::new(seed_job),
        pattern_states: Vec::new(),
        empty_env: None,
    };

    loop {
        drive.stacks.check();
        let Some(job) = drive.stacks.pop() else { break };
        match job {
            Job::Proc(proc, env) => drive.enter_proc(proc, env)?,
            Job::Name(name, env) => drive.enter_name(name, env)?,
            Job::Body(body, env) => drive.enter_body(body, env)?,
            Job::ForRows(rows, body, env) => drive.enter_for_rows(rows, body, env)?,
            Job::Pattern(pat, slot) => drive.enter_pattern(pat, slot)?,
            Job::Formula(formula, env) => drive.enter_formula(formula, env)?,
            Job::Combine(kont) => drive.combine(kont)?,
        }
    }

    debug_assert_eq!(
        drive.stacks.values.len(),
        1,
        "rholang lowering: the machine halted with {} values, not 1",
        drive.stacks.values.len()
    );
    Ok(drive.stacks.pop_value())
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// δ — THE ENTER HALF
//
// One arm per arm of the recursive `lower_proc`'s 89-arm match, IN THE SAME ORDER, so the two
// can be read side by side. The 21 arms with no recursive child call the very same
// `lower_arm_*` function the recursive form called and push its value; the rest name their
// children and their continuation.
// ═══════════════════════════════════════════════════════════════════════════════════════════

impl<'a> Drive<'a> {
    fn enter_proc(&mut self, proc: &'a Proc, env: EnvId) -> Result<(), RholangAstLowerError> {
        // A-S4: exec submits the RAW parse tree (no pre-normalization), so the surface-sugar
        // nodes (`x!()`, `c!(a,b)`, `@Nil!(q)`, `@n!(…)`, and the `!?` query binds) arrive
        // unfolded. Desugar the HEAD node to the core form it denotes first — a pure structural
        // rearrangement, no value computation — then lower that.
        //
        // A LOOP rather than the recursive form's tail call. It is equivalent for a different
        // reason than it looks: `desugar_surface_sugar_node` never returns a node that is
        // itself desugarable (its outputs are `POutput`/`PPersistOutput`/`PPar`/`PNew`, none of
        // which it matches), so the recursion was one deep — but writing it as a loop means the
        // machine does not have to KNOW that, and a new sugar rule cannot reintroduce a frame.
        let mut proc = proc;
        while let Some(desugared) = desugar_surface_sugar_node(proc) {
            proc = self.keep(Arc::new(desugared));
        }

        match proc {
            Proc::PZero => self.stacks.value(lower_arm_p_zero()?),
            Proc::PDrop(name) => self.stacks.push(Job::Name(name.as_ref(), env)),
            // L9-6b CONSTRUCTION arm: a `PFlt*` in VALUE position elaborates to the reflected
            // foreign term via the guest reflector selected by its `tag`. No recursive child:
            // the reflector owns the guest's own traversal.
            Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
                self.stacks.value(lower_arm_p_flt(node, self.env(env))?)
            },
            // A DDL declaration is immutable specification data. The generated parser has
            // already produced the complete structural AST. Project that AST to the closed
            // versioned value envelope without source rendering or a second parse. Embedded
            // Rholang values/programs are scheduled as ordinary jobs in THIS drive.
            Proc::DdlModule(name, items) => {
                self.enter_ddl(DdlRoot::Module { name, imports: None, items }, env)
            },
            Proc::DdlModuleImported(imports, name, items) => self.enter_ddl(
                DdlRoot::Module {
                    name,
                    imports: Some(imports.as_ref()),
                    items,
                },
                env,
            ),
            Proc::DdlTheory(name, parameters, body) => {
                self.enter_ddl(DdlRoot::Theory { name, parameters, body: body.as_ref() }, env)
            },
            Proc::PPar(parts) => {
                let members: Vec<&'a Proc> = parts.iter_elements().collect();
                self.push_children(
                    Kont::ParFold(members.len()),
                    members.into_iter().map(|part| Job::Proc(part, env)),
                );
            },
            // Bare infix parallel `a | b`. Parallel composition lowers to `Par::append`, which
            // is exactly what lowering the folded `PPar` bag would produce.
            Proc::PParInfix(left, right) => self.push_children(
                Kont::ParPair,
                [Job::Proc(left.as_ref(), env), Job::Proc(right.as_ref(), env)],
            ),
            Proc::POutput(channel, payload) => self.push_children(
                Kont::Send { persistent: false },
                [Job::Name(channel.as_ref(), env), Job::Proc(payload.as_ref(), env)],
            ),
            // ★ THE LOOKAHEAD ARMS — `x!(P)[*]` and `x!(P)[n]`. These do NOT lower to a send:
            // the lowering emits a speculation REQUEST and no send at all.
            Proc::PLookaheadAll(subject) => {
                let (channel, payload) = self.lookahead_operand(subject.as_ref(), env)?;
                self.push_children(Kont::SpecAll, [channel, payload]);
            },
            Proc::PLookahead(subject, bound) => {
                let (channel, payload) = self.lookahead_operand(subject.as_ref(), env)?;
                let bound = lookahead_bound(bound.as_ref())?;
                self.push_children(Kont::SpecN { bound }, [channel, payload]);
            },
            // `for(...)` receive. Each `;`-separated row nests as the continuation of the
            // previous one.
            Proc::PForUser(rows, body) => {
                self.stacks
                    .push(Job::ForRows(rows.as_slice(), body.as_ref(), env))
            },
            Proc::PPersistOutput(channel, payload) => self.push_children(
                Kont::Send { persistent: true },
                [Job::Name(channel.as_ref(), env), Job::Proc(payload.as_ref(), env)],
            ),
            // Rholang-style short sends `@P!(q)` / `@P!!(q)`: the channel is the quote of `P`,
            // i.e. `lower_name(NQuote(P)) == lower_proc(P)`.
            Proc::POutputShort(channel_proc, payload) => self.push_children(
                Kont::Send { persistent: false },
                [Job::Proc(channel_proc.as_ref(), env), Job::Proc(payload.as_ref(), env)],
            ),
            Proc::PPersistOutputShort(channel_proc, payload) => self.push_children(
                Kont::Send { persistent: true },
                [Job::Proc(channel_proc.as_ref(), env), Job::Proc(payload.as_ref(), env)],
            ),
            Proc::PNew(scope) => {
                let (binders, body) = scope.clone().unbind::<String>();
                let extended = self.envs.push(extend_env(self.env(env), &binders));
                let body = self.keep(body);
                self.push_children(
                    Kont::New {
                        binder_count: binders.len(),
                        uris: Vec::new(),
                    },
                    [Job::Body(body, extended)],
                );
            },
            Proc::PNewUris(uris, scope) => {
                let (ordered_binders, body, ordered_uris) = unbind_uri_scope(uris, scope)?;
                let extended = self.envs.push(extend_env(self.env(env), &ordered_binders));
                let body = self.keep(body);
                self.push_children(
                    Kont::New {
                        binder_count: ordered_binders.len(),
                        uris: ordered_uris,
                    },
                    [Job::Body(body, extended)],
                );
            },
            // ── A-S4 cast purity: casts lower STRUCTURALLY ───────────────────────────────────
            Proc::CastInt(value) => self
                .stacks
                .value(lower_int_value(value.as_ref(), self.env(env))?),
            Proc::CastBool(value) => self.stacks.value(lower_arm_cast_bool(value)?),
            Proc::CastStr(value) => self.stacks.value(lower_arm_cast_str(value)?),
            Proc::PVar(var) => self.stacks.value(lower_arm_p_var(var, self.env(env))?),
            Proc::Err => self.stacks.value(lower_arm_err()?),
            Proc::CastBigRat(value) => self.stacks.value(lower_arm_cast_big_rat(value)?),
            Proc::CastFixed(value) => self.stacks.value(lower_arm_cast_fixed(value)?),
            Proc::CastFloat(value) => self.stacks.value(lower_arm_cast_float(value)?),
            Proc::CastBigInt(value) => self.stacks.value(lower_arm_cast_big_int(value)?),
            Proc::CastUInt32(value) => self.stacks.value(lower_arm_cast_u_int32(value)?),
            Proc::CastList(value) => match value.as_ref() {
                List::ListLit(items) => self.push_children(
                    Kont::ListLit(items.len()),
                    items.iter().map(|item| Job::Proc(item, env)),
                ),
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc("computed list process"));
                },
            },
            Proc::CastBag(value) => match value.as_ref() {
                Bag::BagLit(entries) => {
                    let mut entries = entries.iter().collect::<Vec<_>>();
                    entries.sort_by_key(|(item, _)| *item);
                    let mut counts = Vec::with_capacity(entries.len());
                    for (_, count) in &entries {
                        counts.push(i64::try_from(*count).map_err(|_| {
                            RholangAstLowerError::UnsupportedProc("bag multiplicity exceeds i64")
                        })?);
                    }
                    self.push_children(
                        Kont::BagLit(counts),
                        entries.into_iter().map(|(item, _)| Job::Proc(item, env)),
                    );
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc("computed bag process"));
                },
            },
            Proc::CastMap(value) => match value.as_ref() {
                Map::MapLit(entries) => {
                    let mut children = Vec::with_capacity(2 * entries.len());
                    let mut pair_count = 0usize;
                    for (key, value) in entries.iter() {
                        children.push(Job::Proc(key, env));
                        children.push(Job::Proc(value, env));
                        pair_count += 1;
                    }
                    self.push_children(Kont::MapLit(pair_count), children);
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc("computed map process"));
                },
            },
            Proc::MapEmpty => self.stacks.value(new_emap_par(
                Vec::new(),
                Vec::new(),
                false,
                None,
                Vec::new(),
                false,
            )),
            Proc::CastSet(value) => match value.as_ref() {
                Set::SetLit(items) => {
                    let mut items: Vec<&Proc> = items.iter().collect();
                    items.sort();
                    self.push_children(
                        Kont::SetLit(items.len()),
                        items.into_iter().map(|item| Job::Proc(item, env)),
                    );
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc("computed set process"));
                },
            },
            Proc::CastPathmap(value) => match value.as_ref() {
                Pathmap::PathmapLit(entries) => {
                    // The continuation's arity follows the container mode:
                    // set entries contribute one child, map entries two. This
                    // feeds the target's specialized PathMap constructors
                    // directly and never materializes an EMap or per-entry tag.
                    match entries.mode() {
                        mettail_runtime::PathMapMode::Empty | mettail_runtime::PathMapMode::Set => {
                            let children = entries.iter().map(|entry| Job::Proc(entry.key(), env));
                            self.push_children(
                                Kont::PathmapLit { map: false, len: entries.len() },
                                children,
                            );
                        },
                        mettail_runtime::PathMapMode::Map => {
                            let mut children = Vec::with_capacity(2 * entries.len());
                            for entry in entries.iter() {
                                children.push(Job::Proc(entry.key(), env));
                                children.push(Job::Proc(
                                    entry.value().expect("map-mode entry has a value"),
                                    env,
                                ));
                            }
                            self.push_children(
                                Kont::PathmapLit { map: true, len: entries.len() },
                                children,
                            );
                        },
                    }
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc("computed pathmap process"));
                },
            },
            Proc::PathmapEmpty => {
                self.stacks
                    .value(new_epathmap_set_par(Vec::new(), Vec::new(), false))
            },
            Proc::CastBytes(value) => self.stacks.value(lower_arm_cast_bytes(value)?),
            // ── A-S4 fold purity: a fold reaching THIS arm sits where the lift traversal
            // cannot reach it — fail closed, typed and named.
            Proc::IntBinProc(..) => self.stacks.value(lower_arm_int_bin_proc()?),
            Proc::UIntBinProc(..) => self.stacks.value(lower_arm_u_int_bin_proc()?),
            Proc::FloatBinProc(..) => self.stacks.value(lower_arm_float_bin_proc()?),
            Proc::FixedBinProc(..) => self.stacks.value(lower_arm_fixed_bin_proc()?),
            Proc::BigintCastProc(..) => self.stacks.value(lower_arm_bigint_cast_proc()?),
            Proc::BigratCastProc(..) => self.stacks.value(lower_arm_bigrat_cast_proc()?),
            // ── A-S4 metered machine arithmetic ─────────────────────────────────────────────
            Proc::Add(a, b) => self.bin(Kont::AddParity, a, b, env),
            Proc::Sub(a, b) => self.bin(Kont::BinExpr(BinOp::Minus), a, b, env),
            Proc::Mul(a, b) => self.bin(Kont::BinExpr(BinOp::Mult), a, b, env),
            Proc::Div(a, b) => self.bin(Kont::BinExpr(BinOp::Div), a, b, env),
            Proc::Mod(a, b) => self.bin(Kont::BinExpr(BinOp::Mod), a, b, env),
            Proc::NegProc(a) => {
                self.push_children(Kont::UnExpr(UnOp::Neg), [Job::Proc(a.as_ref(), env)])
            },
            Proc::Eq(a, b) => self.bin(Kont::BinExpr(BinOp::Eq), a, b, env),
            Proc::Ne(a, b) => self.bin(Kont::BinExpr(BinOp::Neq), a, b, env),
            Proc::Lt(a, b) => self.bin(Kont::BinExpr(BinOp::Lt), a, b, env),
            Proc::Gt(a, b) => self.bin(Kont::BinExpr(BinOp::Gt), a, b, env),
            Proc::LtEq(a, b) => self.bin(Kont::BinExpr(BinOp::Lte), a, b, env),
            Proc::GtEq(a, b) => self.bin(Kont::BinExpr(BinOp::Gte), a, b, env),
            Proc::And(a, b) => self.bin(Kont::BinExpr(BinOp::And), a, b, env),
            Proc::Or(a, b) => self.bin(Kont::BinExpr(BinOp::Or), a, b, env),
            // M-0 — material implication: `a implies b ≡ (not a) or b`, with the negation
            // wrapping ONLY the antecedent.
            Proc::Implies(a, b) => self.bin(Kont::Implies, a, b, env),
            Proc::Not(a) => {
                self.push_children(Kont::UnExpr(UnOp::Not), [Job::Proc(a.as_ref(), env)])
            },
            // M-1b — the SPATIAL satisfaction operator `t matches φ`.
            //
            // ★ §18.1's static-`false` fold is decided HERE, on the formula's syntax, exactly
            // as the recursive arm decided it: the judgement is syntactic and conservative, so
            // the fold can only ever be a missed optimization, never a wrong verdict. The
            // TARGET is lowered either way, so an ill-formed target still fails.
            Proc::Matches(target, formula) => {
                match mettail_languages::rholang::formula::is_statically_false(formula.as_ref()) {
                    true => self.push_children(
                        Kont::MatchesStaticallyFalse,
                        [Job::Proc(target.as_ref(), env)],
                    ),
                    false => self.push_children(
                        Kont::Matches,
                        [Job::Proc(target.as_ref(), env), Job::Formula(formula.as_ref(), env)],
                    ),
                }
            },
            // M-1b — `PPar(φ, ψ)` is a PATTERN former, not a term former.
            Proc::SpatialPPar(..) => self.stacks.value(lower_arm_spatial_p_par()?),
            // ── Methods routed to the reducer's OWN method table (option C, C1/C2) ───────────
            Proc::MethodCall(receiver, method_name, arguments) => {
                // A literal Bag lowers through a two-element EList ABI. The three
                // list-indexing methods would therefore return a plausible answer about
                // the ABI rather than the multiset. Preserve the syntax-level refusal
                // before lowering; all other membership, arity, carrier, metering, and
                // result decisions belong to the reducer's method table.
                if receiver_is_literal_bag(receiver.as_ref())
                    && matches!(method_name.as_str(), "length" | "nth" | "last")
                {
                    return Err(RholangAstLowerError::UnsupportedProc(
                        "list-style indexing/cardinality on a bag (the machine would observe \
                         the bag's two-element ABI encoding rather than the multiset)",
                    ));
                }
                self.method(method_name.as_str(), receiver, arguments, env);
            },
            // A-S4 fail-closed: every remaining construct has no machine algebra. The typed
            // error NAMES the construct; nothing silently host-evaluates.
            other => self.stacks.value(lower_arm_unsupported(other)?),
        }
        Ok(())
    }

    /// The two-operand shape, which 15 arms share.
    fn bin(&mut self, kont: Kont<'a>, a: &'a Arc<Proc>, b: &'a Arc<Proc>, env: EnvId) {
        self.push_children(kont, [Job::Proc(a.as_ref(), env), Job::Proc(b.as_ref(), env)]);
    }

    /// The generic `EMethod` shape. The receiver is child 0 and the ordered argument
    /// vector follows without temporary `Arc` references or name-specific dispatch.
    fn method(&mut self, name: &'a str, target: &'a Arc<Proc>, arguments: &'a [Proc], env: EnvId) {
        let mut children = Vec::with_capacity(1 + arguments.len());
        children.push(Job::Proc(target.as_ref(), env));
        children.extend(arguments.iter().map(|argument| Job::Proc(argument, env)));
        self.push_children(Kont::Method { name, argc: arguments.len() }, children);
    }

    /// `lower_lookahead_operand` — the `(channel, payload)` split of `x!(P)[*]`'s operand.
    ///
    /// Returns the two child JOBS rather than two `Par`s: the operand's halves are ordinary
    /// subtrees and must be lowered by the machine, not by a nested traversal.
    fn lookahead_operand(
        &mut self,
        operand: &'a Proc,
        env: EnvId,
    ) -> Result<(Job<'a>, Job<'a>), RholangAstLowerError> {
        // A RECEIVE is diagnosed before expansion, not after. `desugar_surface_sugar_node`
        // rewrites a `!?`-carrying `for` into the `new`-scoped `send | receive` it denotes, and
        // that `new` would then be reported by the catch-all as "a non-send process" — true,
        // but useless. A receive is not a send under ANY spelling, so the specific diagnostic
        // is owed to every spelling of it.
        if matches!(operand, Proc::PForUser(..)) {
            return Err(RholangAstLowerError::LookaheadOperandNotASend("a receive"));
        }
        let mut operand = operand;
        while let Some(desugared) = desugar_surface_sugar_node(operand) {
            operand = self.keep(Arc::new(desugared));
        }
        match operand {
            Proc::POutput(channel, payload) => {
                Ok((Job::Name(channel.as_ref(), env), Job::Proc(payload.as_ref(), env)))
            },
            Proc::POutputShort(channel_proc, payload) => {
                Ok((Job::Proc(channel_proc.as_ref(), env), Job::Proc(payload.as_ref(), env)))
            },
            Proc::PPersistOutput(..) | Proc::PPersistOutputShort(..) => {
                Err(RholangAstLowerError::LookaheadOperandNotASend("a persistent send (`!!`)"))
            },
            Proc::PZero => Err(RholangAstLowerError::LookaheadOperandNotASend("Nil")),
            Proc::PForUser(..) => Err(RholangAstLowerError::LookaheadOperandNotASend("a receive")),
            Proc::PPar(..) | Proc::PParInfix(..) => {
                Err(RholangAstLowerError::LookaheadOperandNotASend("a parallel composition"))
            },
            Proc::CastList(..) => {
                Err(RholangAstLowerError::LookaheadOperandNotASend("a list literal"))
            },
            _ => Err(RholangAstLowerError::LookaheadOperandNotASend("a non-send process")),
        }
    }

    /// `lower_name` / `lower_drop`.
    fn enter_name(&mut self, name: &'a Name, env: EnvId) -> Result<(), RholangAstLowerError> {
        match name {
            // `@P` full quote — the channel IS the lowered process.
            Name::NQuote(proc) => self.stacks.push(Job::Proc(proc.as_ref(), env)),
            // `@P` short-quote (raw `NQuoteShort`; folds to `NQuote(P)` at eval time).
            Name::NQuoteShort(proc) => self.stacks.push(Job::Proc(proc.as_ref(), env)),
            // `@Nil` quotes `Nil`; its channel is the empty process.
            Name::NQuoteNil => self.stacks.value(Par::default()),
            // Parenthesized name grouping `(N)` is transparent for channels.
            Name::NParen(inner) => self.stacks.push(Job::Name(inner.as_ref(), env)),
            Name::NVar(var) => {
                let par = lower_name_var(var, self.env(env))?;
                self.stacks.value(par);
            },
            _ => {
                return Err(RholangAstLowerError::UnsupportedName("computed rholang name"));
            },
        }
        Ok(())
    }

    /// `lower_body_lifting_folds` — lift the outermost held width/precision fold out of a
    /// binder body into a trampoline, then lower what is left.
    ///
    /// The fold-site REGISTER is written at Enter, before either child is entered, which is
    /// where the recursive form wrote it. Order matters: the operand's own subtree may register
    /// further sites (a `new` inside an operand), and the site index is `HELD_FOLD_SITES.len()`
    /// at the moment of registration.
    fn enter_body(&mut self, body: &'a Proc, env: EnvId) -> Result<(), RholangAstLowerError> {
        if let Some(node) = find_dynamic_flt(body, self.env(env)) {
            let ret_var = FreeVar::fresh_named("__mtl_flt_ret".to_string());
            let result_var = FreeVar::fresh_named("__mtl_flt_result".to_string());
            let result_drop =
                Proc::PDrop(Arc::new(Name::NVar(OrdVar(Var::Free(result_var.clone())))));
            let mut replaced = false;
            let transformed =
                self.keep(Arc::new(replace_dynamic_flt(body, &node, &result_drop, &mut replaced)));
            debug_assert!(replaced, "the dynamic FLT finder and replacement PDA diverged");

            let env_new = self
                .envs
                .push(extend_env(self.env(env), &[Binder(ret_var)]));
            let selector = lower_proc_var(&node.selector, self.env(env_new))?;
            let mut fills = BTreeMap::new();
            for hole in &node.holes {
                let level = self
                    .env(env_new)
                    .flt_hole_level(&hole.name)
                    .ok_or_else(|| {
                        RholangAstLowerError::FltReflect(format!(
                            "construction hole ${{{}}} is not bound by an enclosing FLT pattern",
                            hole.name
                        ))
                    })?;
                fills.insert(
                    hole.name.clone(),
                    new_boundvar_par(level as i32, create_bit_vector(&[level]), false),
                );
            }
            node.validate()
                .map_err(|error| RholangAstLowerError::FltReflect(error.to_string()))?;
            let template = node.stage(FltPolarity::PositiveConstruction);
            let (pieces, holes) = runtime_template_parts(template);
            let reply = new_boundvar_par(0, create_bit_vector(&[0]), false);
            let request = crate::language_install::encode_flt_construct_call(
                selector,
                &pieces,
                &holes,
                template.category,
                &fills,
                reply,
            );
            let channel = LANGUAGE_FLT_CONSTRUCT_BAND
                .channel(0, crate::language_install::LANGUAGE_FLT_CONSTRUCT_ABI_V1);
            let env_for = self
                .envs
                .push(extend_env(self.env(env_new), &[Binder(result_var)]));
            self.push_children(
                Kont::InstalledFlt {
                    channel: Box::new(channel),
                    request: Box::new(request),
                },
                [Job::Body(transformed, env_for)],
            );
            return Ok(());
        }
        let Some((operand, kind, width)) = find_fold(body) else {
            self.stacks.push(Job::Proc(body, env));
            return Ok(());
        };
        let site_index = HELD_FOLD_SITES.with(|sites| sites.borrow().len()) as u8;
        let fingerprint = held_fold_language_fingerprint();
        HELD_FOLD_SITES.with(|sites| {
            sites.borrow_mut().push(FoldSpec {
                kind,
                width,
                site_index,
                fingerprint: fingerprint.clone(),
            })
        });
        let channel = fold_channel(site_index, &fingerprint);
        let ret_var = mettail_runtime::get_or_create_var(format!("__mtl_ret_{site_index}"));
        let r_var = mettail_runtime::get_or_create_var(format!("__mtl_r_{site_index}"));
        let r_drop = Proc::PDrop(Arc::new(Name::NVar(OrdVar(Var::Free(r_var.clone())))));
        let mut replaced = false;
        let transformed = self.keep(Arc::new(replace_fold(body, &r_drop, &mut replaced)));
        let env_new = self
            .envs
            .push(extend_env(self.env(env), &[Binder(ret_var)]));
        let env_for = self
            .envs
            .push(extend_env(self.env(env_new), &[Binder(r_var)]));
        let operand = self.keep(Arc::new(operand));
        self.push_children(
            Kont::HeldFold { channel: Box::new(channel) },
            [Job::Proc(operand, env_new), Job::Body(transformed, env_for)],
        );
        Ok(())
    }

    /// `lower_pattern_proc` — a receive pattern, whose free variables become binders.
    fn enter_pattern(&mut self, pat: &'a Proc, slot: u32) -> Result<(), RholangAstLowerError> {
        match pat {
            Proc::PVar(ordvar) => match &ordvar.0 {
                Var::Free(free_var) => {
                    let state = &mut self.pattern_states[slot as usize];
                    let index = state.counter;
                    state.counter += 1;
                    state.binders.push(Binder(free_var.clone()));
                    self.stacks.value(new_freevar_par(index, Vec::new()));
                },
                Var::Bound(_) => {
                    return Err(RholangAstLowerError::UnsupportedProc(
                        "bound var in receive pattern",
                    ));
                },
            },
            Proc::CastList(list) => match list.as_ref() {
                List::ListLit(items) => self.push_children(
                    Kont::PatListLit(items.len()),
                    items.iter().map(|item| Job::Pattern(item, slot)),
                ),
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc(
                        "computed list receive pattern",
                    ));
                },
            },
            Proc::CastMap(map) => match map.as_ref() {
                Map::MapLit(entries) => {
                    let mut children = Vec::with_capacity(2 * entries.len());
                    let mut pair_count = 0usize;
                    for (key, value) in entries.iter() {
                        children.push(Job::Pattern(key, slot));
                        children.push(Job::Pattern(value, slot));
                        pair_count += 1;
                    }
                    self.push_children(Kont::PatMapLit(pair_count), children);
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc(
                        "computed map receive pattern",
                    ));
                },
            },
            Proc::CastSet(set) => match set.as_ref() {
                Set::SetLit(items) => {
                    let mut items: Vec<&Proc> = items.iter().collect();
                    items.sort();
                    self.push_children(
                        Kont::PatSetLit(items.len()),
                        items.into_iter().map(|item| Job::Pattern(item, slot)),
                    );
                },
                _ => {
                    return Err(RholangAstLowerError::UnsupportedProc(
                        "computed set receive pattern",
                    ));
                },
            },
            // Anything else is an ordinary term read as a pattern, in a FRESH empty
            // environment — not the enclosing one. That is what the recursive arm did, and it
            // is load-bearing: a pattern's free variables are its own binders.
            other => {
                let empty = self.empty_env();
                self.stacks.push(Job::Proc(other, empty));
            },
        }
        Ok(())
    }

    /// `rholang_formula::lower_formula_in_env` — compile a spatial formula to a pattern.
    fn enter_formula(&mut self, formula: &'a Proc, env: EnvId) -> Result<(), RholangAstLowerError> {
        use mettail_languages::rholang::formula::{classify, FormulaShape};
        match classify(formula) {
            FormulaShape::Verum => self.stacks.value(crate::rholang_formula::verum_pattern()),
            FormulaShape::Falsum => self.stacks.value(crate::rholang_formula::falsum_pattern()),
            FormulaShape::Conjunction(left, right) => self.push_children(
                Kont::FormulaAnd,
                [Job::Formula(left, env), Job::Formula(right, env)],
            ),
            FormulaShape::Disjunction(left, right) => self.push_children(
                Kont::FormulaOr,
                [Job::Formula(left, env), Job::Formula(right, env)],
            ),
            FormulaShape::Negation(inner) => {
                self.push_children(Kont::FormulaNot, [Job::Formula(inner, env)])
            },
            FormulaShape::Implication(antecedent, consequent) => self.push_children(
                Kont::FormulaImplies,
                [Job::Formula(antecedent, env), Job::Formula(consequent, env)],
            ),
            FormulaShape::Separation(parts) => self.push_children(
                Kont::FormulaSeparation(parts.len()),
                parts.into_iter().map(|part| Job::Formula(part, env)),
            ),
            // An ordinary `Proc`, read as a Rholang pattern: unbound free variables become
            // `Wildcard` rather than the term-position free-variable MARKER.
            FormulaShape::Term => {
                let pattern_env = self.envs.push(self.env(env).in_pattern_position());
                self.stacks.push(Job::Proc(formula, pattern_env));
            },
        }
        Ok(())
    }
}

fn unbind_uri_scope(
    uris: &[Uri],
    scope: &mettail_runtime::Scope<Vec<Binder<String>>, Arc<Proc>>,
) -> Result<(Vec<Binder<String>>, Arc<Proc>, Vec<String>), RholangAstLowerError> {
    let (binders, body) = scope.clone().unbind::<String>();
    if binders.len() != uris.len() || binders.is_empty() {
        return Err(RholangAstLowerError::InvalidUriBindings {
            binders: binders.len(),
            uris: uris.len(),
        });
    }
    let mut bindings: Vec<(String, Binder<String>)> = binders
        .into_iter()
        .zip(uris)
        .map(|(binder, uri)| match uri {
            Uri::UriText(value) => value
                .strip_prefix('`')
                .and_then(|value| value.strip_suffix('`'))
                .filter(|value| !value.is_empty())
                .map(|value| (value.to_string(), binder))
                .ok_or(RholangAstLowerError::InvalidUriLiteral),
            _ => Err(RholangAstLowerError::InvalidUriLiteral),
        })
        .collect::<Result<_, _>>()?;
    bindings.sort_by(|left, right| left.0.cmp(&right.0));
    if let Some(pair) = bindings.windows(2).find(|pair| pair[0].0 == pair[1].0) {
        return Err(RholangAstLowerError::DuplicateUriBinding(pair[0].0.clone()));
    }
    let ordered_uris = bindings.iter().map(|(uri, _)| uri.clone()).collect();
    let ordered_binders = bindings.into_iter().map(|(_, binder)| binder).collect();
    Ok((ordered_binders, body, ordered_uris))
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// δ — THE COMBINE HALF
//
// Every arm here is the POST-ORDER body of the recursive function it replaces, with
// `lower_x(child)?` read off the value stack instead of called. Nothing is re-derived: the
// assembly expressions are the same expressions, and `recursive_oracle` holds the originals so
// a differential can say so rather than a reviewer having to.
// ═══════════════════════════════════════════════════════════════════════════════════════════

impl<'a> Drive<'a> {
    fn enter_ddl(&mut self, root: DdlRoot<'a>, env: EnvId) {
        let plan = DdlLowerPlan::build(root);
        let processes: Vec<_> = plan.process_jobs().collect();
        self.push_children(
            Kont::Ddl(Box::new(plan)),
            processes.into_iter().map(|process| Job::Proc(process, env)),
        );
    }

    fn combine(&mut self, kont: Kont<'a>) -> Result<(), RholangAstLowerError> {
        match kont {
            Kont::ParFold(n) => {
                let parts = self.stacks.pop_values(n);
                let par = parts
                    .into_iter()
                    .fold(Par::default(), |acc, part| acc.append(part));
                self.stacks.value(par);
            },
            Kont::ParPair => {
                let right = self.stacks.pop_value();
                let left = self.stacks.pop_value();
                self.stacks.value(left.append(right));
            },
            Kont::Send { persistent } => {
                let payload = self.stacks.pop_value();
                let channel = self.stacks.pop_value();
                let par = match persistent {
                    true => send_par_persistent(channel, vec![payload]),
                    false => send_par(channel, vec![payload]),
                };
                self.stacks.value(par);
            },
            Kont::BinExpr(op) => {
                let rhs = self.stacks.pop_value();
                let lhs = self.stacks.pop_value();
                self.stacks
                    .value(binary_expr_par(lhs, rhs, |p1, p2| op.build(p1, p2)));
            },
            Kont::UnExpr(op) => {
                let operand = self.stacks.pop_value();
                self.stacks.value(unary_expr_par(operand, |p| op.build(p)));
            },
            // String `+` is Rholang `++` (`EPlusPlus`): when BOTH operands lower to ground
            // string leaves the concat parity arm is chosen; `EPlus` has no GString algebra.
            Kont::AddParity => {
                let rhs = self.stacks.pop_value();
                let lhs = self.stacks.pop_value();
                let op = match is_single_gstring_value(&lhs) && is_single_gstring_value(&rhs) {
                    true => BinOp::PlusPlus,
                    false => BinOp::Plus,
                };
                self.stacks
                    .value(binary_expr_par(lhs, rhs, |p1, p2| op.build(p1, p2)));
            },
            // Built from the two shared assemblers rather than one `binary_expr_par` because
            // the negation must wrap ONLY the antecedent: `unary_expr_par` propagates the
            // antecedent's `locally_free`/`connective_used` onto the `ENot`, and
            // `binary_expr_par` then unions that with the consequent's.
            Kont::Implies => {
                let consequent = self.stacks.pop_value();
                let antecedent = self.stacks.pop_value();
                let negated = unary_expr_par(antecedent, |p| ExprInstance::ENotBody(ENot { p }));
                self.stacks
                    .value(binary_expr_par(negated, consequent, |p1, p2| {
                        ExprInstance::EOrBody(EOr { p1, p2 })
                    }));
            },
            Kont::Method { name, argc } => {
                let mut children = self.stacks.pop_values(1 + argc);
                let argument_pars = children.split_off(1);
                let target_par = children.pop().expect("Kont::Method always has a receiver");
                self.stacks
                    .value(method_par(name, target_par, argument_pars));
            },
            Kont::Matches => {
                let pattern = self.stacks.pop_value();
                let target = self.stacks.pop_value();
                let locally_free = union(target.locally_free.clone(), pattern.locally_free.clone());
                let mut par = Par::default().with_exprs(vec![Expr {
                    expr_instance: Some(ExprInstance::EMatchesBody(EMatches {
                        target: Some(target),
                        pattern: Some(pattern),
                    })),
                }]);
                par.locally_free = locally_free;
                par.connective_used = false;
                self.stacks.value(par);
            },
            Kont::MatchesStaticallyFalse => {
                let mut target = self.stacks.pop_value();
                let mut folded = new_gbool_par(false, Vec::new(), false);
                folded.locally_free = std::mem::take(&mut target.locally_free);
                self.stacks.value(folded);
            },
            Kont::ListLit(n) => {
                let items = self.stacks.pop_values(n);
                let locally_free = locally_free_union(&items);
                let connective_used = any_connective_used(&items);
                self.stacks.value(new_elist_par(
                    items,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::Ddl(plan) => {
                let process_values = self.stacks.pop_values(plan.process_jobs().len());
                let value = plan
                    .finish(process_values)
                    .map_err(RholangAstLowerError::DdlWire)?;
                self.stacks.value(value);
            },
            Kont::SetLit(n) => {
                let elements = self.stacks.pop_values(n);
                let locally_free = locally_free_union(&elements);
                let connective_used = any_connective_used(&elements);
                self.stacks.value(new_eset_par(
                    elements,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::MapLit(n) => {
                let children = self.stacks.pop_values(2 * n);
                let mut pairs = Vec::with_capacity(n);
                let mut locally_free = Vec::new();
                let mut connective_used = false;
                let mut children = children.into_iter();
                while let (Some(key), Some(value)) = (children.next(), children.next()) {
                    locally_free = union(
                        locally_free,
                        union(key.locally_free.clone(), value.locally_free.clone()),
                    );
                    connective_used |= key.connective_used || value.connective_used;
                    pairs.push(new_key_value_pair(key, value));
                }
                self.stacks.value(new_emap_par(
                    pairs,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::PathmapLit { map: false, len } => {
                let entries = self.stacks.pop_values(len);
                let locally_free = locally_free_union(&entries);
                let connective_used = any_connective_used(&entries);
                self.stacks
                    .value(new_epathmap_set_par(entries, locally_free, connective_used));
            },
            Kont::PathmapLit { map: true, len } => {
                let children = self.stacks.pop_values(2 * len);
                let mut entries = Vec::with_capacity(len);
                let mut locally_free = Vec::new();
                let mut connective_used = false;
                let mut children = children.into_iter();
                while let (Some(key), Some(value)) = (children.next(), children.next()) {
                    locally_free = union(
                        locally_free,
                        union(key.locally_free.clone(), value.locally_free.clone()),
                    );
                    connective_used |= key.connective_used || value.connective_used;
                    entries.push((key, value));
                }
                self.stacks
                    .value(new_epathmap_map_par(entries, locally_free, connective_used));
            },
            // A `Bag` becomes `EList[GPrivate(RHOLANG_BAG_ABI_TAG), EList[pairs]]` — always
            // exactly 2 elements. That ABI shape is what the routed-method carrier map in
            // `lower_proc`'s C1 block reasons about.
            Kont::BagLit(counts) => {
                let items = self.stacks.pop_values(counts.len());
                let mut pairs = Vec::with_capacity(items.len());
                for (item, count) in items.into_iter().zip(counts) {
                    let count = new_gint_par(count, Vec::new(), false);
                    let pair_locally_free =
                        union(item.locally_free.clone(), count.locally_free.clone());
                    let pair_connective = item.connective_used || count.connective_used;
                    pairs.push(new_elist_par(
                        vec![item, count],
                        pair_locally_free.clone(),
                        pair_connective,
                        None,
                        pair_locally_free,
                        pair_connective,
                    ));
                }
                let pairs_locally_free = locally_free_union(&pairs);
                let pairs_connective = any_connective_used(&pairs);
                let pairs = new_elist_par(
                    pairs,
                    pairs_locally_free.clone(),
                    pairs_connective,
                    None,
                    pairs_locally_free,
                    pairs_connective,
                );
                let tag =
                    GPrivateBuilder::new_par_from_string(crate::RHOLANG_BAG_ABI_TAG.to_string());
                let locally_free = union(tag.locally_free.clone(), pairs.locally_free.clone());
                let connective_used = tag.connective_used || pairs.connective_used;
                self.stacks.value(new_elist_par(
                    vec![tag, pairs],
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::New { binder_count, uris } => {
                let body = self.stacks.pop_value();
                let locally_free = filter_and_adjust_bitset(&body.locally_free, binder_count);
                let connective_used = body.connective_used;
                self.stacks.value(new_new_par(
                    binder_count as i32,
                    body,
                    uris,
                    BTreeMap::new(),
                    locally_free.clone(),
                    locally_free,
                    connective_used,
                ));
            },
            Kont::SpecAll => {
                let payload = self.stacks.pop_value();
                let channel = self.stacks.pop_value();
                self.stacks
                    .value(crate::lookahead::spec_all_request(payload, channel));
            },
            Kont::SpecN { bound } => {
                let payload = self.stacks.pop_value();
                let channel = self.stacks.pop_value();
                self.stacks
                    .value(crate::lookahead::spec_n_request(payload, bound, channel));
            },
            // `new ret { fold!(operand, *ret) | for(@r <- ret){ … } }` — the held-fold
            // trampoline. The operand is sent to the fold contract's channel; the transformed
            // body runs under the received result.
            Kont::HeldFold { channel } => {
                let for_body = self.stacks.pop_value();
                let operand_par = self.stacks.pop_value();
                let ret_channel = new_boundvar_par(0, Vec::new(), false);
                let send = send_par(*channel, vec![operand_par, ret_channel.clone()]);
                let bind = ReceiveBind {
                    patterns: vec![new_freevar_par(0, Vec::new())],
                    source: Some(ret_channel),
                    remainder: None,
                    free_count: 1,
                };
                let recv_locally_free =
                    receive_locally_free(std::slice::from_ref(&bind), &for_body, 1);
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
                let inner = send.append(recv);
                let new_locally_free = filter_and_adjust_bitset(&inner.locally_free, 1);
                self.stacks.value(new_new_par(
                    1,
                    inner,
                    Vec::new(),
                    BTreeMap::new(),
                    new_locally_free.clone(),
                    new_locally_free,
                    false,
                ));
            },
            // `new ret { construct!([..., ret]) | for(@result <- ret){ body[*result] } }`.
            // Parsing and structural reflection happen before the transformed
            // body is admitted to the machine; the lexical handle and fills in
            // `request` are substituted by the surrounding scopes first.
            Kont::InstalledFlt { channel, request } => {
                let for_body = self.stacks.pop_value();
                self.stacks
                    .value(installed_flt_trampoline(*channel, *request, for_body));
            },
            Kont::ForSource(state) => return self.for_source(state),
            Kont::ForPattern(state, slot) => return self.for_pattern(state, slot),
            Kont::ForBody(mut state) => {
                state.lowered_body = Some(self.stacks.pop_value());
                match state.cond {
                    Some(guard) => {
                        let extended = state.extended_env;
                        self.push_children(Kont::ForGuard(state), [Job::Proc(guard, extended)]);
                    },
                    None => return self.assemble_receive(state, None),
                }
            },
            Kont::ForGuard(state) => {
                let condition = self.stacks.pop_value();
                return self.assemble_receive(state, Some(condition));
            },
            Kont::PatListLit(n) => {
                let item_pars = self.stacks.pop_values(n);
                let locally_free = locally_free_union(&item_pars);
                let connective_used = item_pars.iter().any(|item| item.connective_used);
                self.stacks.value(new_elist_par(
                    item_pars,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::PatSetLit(n) => {
                let elements = self.stacks.pop_values(n);
                let locally_free = locally_free_union(&elements);
                let connective_used = elements.iter().any(|e| e.connective_used);
                self.stacks.value(new_eset_par(
                    elements,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::PatMapLit(n) => {
                let children = self.stacks.pop_values(2 * n);
                let mut pairs = Vec::with_capacity(n);
                let mut locally_free = Vec::new();
                let mut connective_used = false;
                let mut children = children.into_iter();
                while let (Some(key), Some(value)) = (children.next(), children.next()) {
                    connective_used =
                        connective_used || key.connective_used || value.connective_used;
                    locally_free = union(
                        locally_free,
                        union(key.locally_free.clone(), value.locally_free.clone()),
                    );
                    pairs.push(new_key_value_pair(key, value));
                }
                self.stacks.value(new_emap_par(
                    pairs,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ));
            },
            Kont::FormulaAnd => {
                let right = self.stacks.pop_value();
                let left = self.stacks.pop_value();
                let operands = [left, right];
                self.stacks.value(crate::rholang_formula::connective_par(
                    models::rust::utils::new_conn_and_body_par(operands.to_vec(), Vec::new(), true),
                    &operands,
                ));
            },
            Kont::FormulaOr => {
                let right = self.stacks.pop_value();
                let left = self.stacks.pop_value();
                let operands = [left, right];
                self.stacks.value(crate::rholang_formula::connective_par(
                    models::rust::utils::new_conn_or_body_par(operands.to_vec(), Vec::new(), true),
                    &operands,
                ));
            },
            Kont::FormulaNot => {
                let inner = self.stacks.pop_value();
                self.stacks.value(crate::rholang_formula::negated(inner));
            },
            Kont::FormulaImplies => {
                let consequent = self.stacks.pop_value();
                let antecedent = self.stacks.pop_value();
                let operands = [crate::rholang_formula::negated(antecedent), consequent];
                self.stacks.value(crate::rholang_formula::connective_par(
                    models::rust::utils::new_conn_or_body_par(operands.to_vec(), Vec::new(), true),
                    &operands,
                ));
            },
            Kont::FormulaSeparation(n) => {
                let parts = self.stacks.pop_values(n);
                let par = parts
                    .into_iter()
                    .fold(Par::default(), |acc, part| acc.append(part));
                self.stacks.value(par);
            },
        }
        Ok(())
    }
}

/// Assemble the capability-mediated construction request staged by [`Kont::InstalledFlt`].
///
/// Kept as one non-recursive constructor so the production PDA and the bounded recursive
/// differential oracle compare traversal strategy while sharing the exact ABI envelope. The
/// helper performs no parsing, matching, registry lookup, or authority decision.
fn installed_flt_trampoline(channel: Par, request: Par, for_body: Par) -> Par {
    let ret_channel = new_boundvar_par(0, Vec::new(), false);
    let send = send_par(channel, vec![request]);
    let bind = ReceiveBind {
        patterns: vec![new_freevar_par(0, Vec::new())],
        source: Some(ret_channel),
        remainder: None,
        free_count: 1,
    };
    let recv_locally_free = receive_locally_free(std::slice::from_ref(&bind), &for_body, 1);
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
    let inner = send.append(recv);
    let new_locally_free = filter_and_adjust_bitset(&inner.locally_free, 1);
    new_new_par(
        1,
        inner,
        Vec::new(),
        BTreeMap::new(),
        new_locally_free.clone(),
        new_locally_free,
        false,
    )
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// `lower_pfor_user`, staged
//
// The one member whose child list is not known up front. A row's continuation is lowered in a
// scope derived from the binders its own PATTERNS introduce, so the body cannot be scheduled
// until the patterns are done; and each bind's SOURCE must be lowered before that bind's
// pattern, because that is the order in which the recursive form reported errors.
// ═══════════════════════════════════════════════════════════════════════════════════════════

impl<'a> Drive<'a> {
    fn enter_for_rows(
        &mut self,
        rows: &'a [ForRow],
        body: &'a Proc,
        env: EnvId,
    ) -> Result<(), RholangAstLowerError> {
        if rows.is_empty() {
            self.stacks.push(Job::Body(body, env));
            return Ok(());
        }
        let (binds, persistent, cond) = decompose_for_row_borrowed(&rows[0])?;
        if binds.is_empty() {
            return Err(RholangAstLowerError::EmptyInputJoin);
        }
        let (env, pattern_tokens, pattern_preparations) =
            self.prepare_dynamic_patterns(&binds, env)?;
        let binds_rho = Vec::with_capacity(binds.len());
        self.schedule_bind_source(Box::new(ForState {
            rows,
            body,
            env,
            binds,
            pattern_tokens,
            pattern_preparations,
            persistent,
            cond,
            next_bind: 0,
            binds_rho,
            slots: Vec::new(),
            pending_source: None,
            extended_env: ROOT_ENV,
            lowered_body: None,
        }))
    }

    fn prepare_dynamic_patterns(
        &mut self,
        binds: &[&InputBind],
        mut env: EnvId,
    ) -> Result<(EnvId, Vec<Option<FreeVar<String>>>, Vec<PatternPrepFrame>), RholangAstLowerError>
    {
        let mut tokens = vec![None; binds.len()];
        let mut frames = Vec::new();
        for (index, bind) in binds.iter().enumerate() {
            let Some(node) = bind_flt_node(bind) else {
                continue;
            };
            if flt_selector_level(node.as_ref(), self.env(env)).is_none() {
                continue;
            }
            let ret_var = FreeVar::fresh_named("__mtl_flt_pattern_ret".to_string());
            let token_var = FreeVar::fresh_named("__mtl_flt_pattern_token".to_string());
            let env_new = self
                .envs
                .push(extend_env(self.env(env), &[Binder(ret_var)]));
            let selector = lower_proc_var(&node.selector, self.env(env_new))?;
            node.validate()
                .map_err(|error| RholangAstLowerError::FltReflect(error.to_string()))?;
            let template = node.stage(FltPolarity::NegativePattern);
            let (pieces, holes) = runtime_template_parts(template);
            let reply = new_boundvar_par(0, create_bit_vector(&[0]), false);
            let request = crate::language_install::encode_flt_pattern_call(
                selector,
                &pieces,
                &holes,
                template.category,
                reply,
            );
            frames.push(PatternPrepFrame {
                channel: mettail_rholang_codegen::LANGUAGE_FLT_PATTERN_BAND
                    .channel(0, crate::language_install::LANGUAGE_FLT_PATTERN_ABI_V1),
                request,
            });
            env = self
                .envs
                .push(extend_env(self.env(env_new), &[Binder(token_var.clone())]));
            tokens[index] = Some(token_var);
        }
        Ok((env, tokens, frames))
    }

    /// Schedule the next bind's SOURCE, or — once every bind is done — the continuation.
    fn schedule_bind_source(
        &mut self,
        state: Box<ForState<'a>>,
    ) -> Result<(), RholangAstLowerError> {
        match state.next_bind < state.binds.len() {
            true => {
                let channel = bind_channel_name(state.binds[state.next_bind])
                    .ok_or(RholangAstLowerError::UnsupportedProc("for-row channel"))?;
                let env = state.env;
                self.push_children(Kont::ForSource(state), [Job::Name(channel, env)]);
                Ok(())
            },
            false => self.schedule_for_body(state),
        }
    }

    fn for_source(&mut self, mut state: Box<ForState<'a>>) -> Result<(), RholangAstLowerError> {
        let source = self.stacks.pop_value();
        let bind = state.binds[state.next_bind];

        // L9-6b: an FLT receive pattern is reflected by the guest, not walked here. Its holes
        // are receive binders, so they enter the slot list in bind order alongside monikers.
        if let Some(node) = bind_flt_node(bind) {
            if let Some(token_var) = &state.pattern_tokens[state.next_bind] {
                // `Reduce::eval_receive` substitutes patterns at depth one. An outer value
                // referenced from a pattern is therefore a `VarRef { depth: 1 }`, not an
                // ordinary `BoundVar`; the latter is intentionally left untouched at pattern
                // depth. `index` remains the token's level in the enclosing environment, which
                // also handles several nested preparation frames without special cases.
                let token_level = self.env(state.env).binders.get(token_var).copied().ok_or(
                    RholangAstLowerError::UnsupportedProc("dynamic FLT pattern token scope"),
                )?;
                let token_index = i32::try_from(token_level).map_err(|_| {
                    RholangAstLowerError::FltReflect(
                        "dynamic FLT pattern scope exceeds the Rho de-Bruijn range".into(),
                    )
                })?;
                let mut token = Par::default().with_connectives(vec![Connective {
                    connective_instance: Some(ConnectiveInstance::VarRefBody(VarRef {
                        index: token_index,
                        depth: 1,
                    })),
                }]);
                token.locally_free = create_bit_vector(&[token_level]);
                token.connective_used = true;
                let pattern = crate::language_install::dynamic_flt_pattern_token_pattern(token);
                for hole in &node.holes {
                    state.slots.push(ReceiveSlot::Hole(hole.name.clone()));
                }
                state.binds_rho.push(ReceiveBind {
                    patterns: vec![pattern],
                    source: Some(source),
                    remainder: None,
                    free_count: i32::try_from(node.holes.len()).map_err(|_| {
                        RholangAstLowerError::FltReflect(
                            "FLT pattern telescope exceeds the Rho free-count range".into(),
                        )
                    })?,
                });
                state.next_bind += 1;
                return self.schedule_bind_source(state);
            }
            let (pattern, free_count, hole_names) =
                lower_flt_pattern(node.as_ref(), self.env(state.env))?;
            for name in hole_names {
                state.slots.push(ReceiveSlot::Hole(name));
            }
            state.binds_rho.push(ReceiveBind {
                patterns: vec![pattern],
                source: Some(source),
                remainder: None,
                free_count,
            });
            state.next_bind += 1;
            return self.schedule_bind_source(state);
        }

        // `for(<- n)` — an empty bind consumes without binding.
        if is_empty_bind(bind) {
            state.binds_rho.push(ReceiveBind {
                patterns: vec![new_wildcard_par(Vec::new(), false)],
                source: Some(source),
                remainder: None,
                free_count: 0,
            });
            state.next_bind += 1;
            return self.schedule_bind_source(state);
        }

        let pat_proc = bind_pattern_proc(bind)
            .ok_or(RholangAstLowerError::UnsupportedProc("for-row pattern"))?;
        let pat_proc = self.keep(Arc::new(pat_proc));
        let slot = u32::try_from(self.pattern_states.len())
            .expect("rholang lowering: more than 2^32 receive binds in one term");
        self.pattern_states.push(PatternState::default());
        state.pending_source = Some(source);
        self.push_children(Kont::ForPattern(state, slot), [Job::Pattern(pat_proc, slot)]);
        Ok(())
    }

    fn for_pattern(
        &mut self,
        mut state: Box<ForState<'a>>,
        slot: u32,
    ) -> Result<(), RholangAstLowerError> {
        let pat_par = self.stacks.pop_value();
        let source = state
            .pending_source
            .take()
            .expect("rholang lowering: a receive pattern ran without its source");
        let bind_binders = std::mem::take(&mut self.pattern_states[slot as usize].binders);
        let free_count = bind_binders.len() as i32;
        for binder in bind_binders {
            state.slots.push(ReceiveSlot::Moniker(binder));
        }
        state.binds_rho.push(ReceiveBind {
            patterns: vec![pat_par],
            source: Some(source),
            remainder: None,
            free_count,
        });
        state.next_bind += 1;
        self.schedule_bind_source(state)
    }

    /// Every bind is done, so the continuation scope is known: derive it and schedule the body.
    ///
    /// The recursive form built an owned `continuation` `Proc` here and immediately
    /// destructured it back apart. The driver skips the round trip and dispatches on the same
    /// three cases directly — which is why nothing needs to be materialised: `&rows[1..]` and
    /// `body` are borrowed from the caller's term.
    fn schedule_for_body(
        &mut self,
        mut state: Box<ForState<'a>>,
    ) -> Result<(), RholangAstLowerError> {
        let extended = self
            .envs
            .push(self.env(state.env).extend_slots(&state.slots));
        state.extended_env = extended;
        let job = match state.rows.len() > 1 {
            // More rows in THIS `for`: they nest as this row's continuation. These rows are
            // query-free by construction — `enter_proc` expanded every row of this `for`
            // together before scheduling it.
            true => Job::ForRows(&state.rows[1..], state.body, extended),
            false => match state.body {
                // The body is itself a `for`: its rows nest under this one's binders.
                //
                // ⚠ This shortcut hands the inner rows straight to `enter_for_rows`, bypassing
                // `enter_proc` — and with it the surface-sugar expansion. It is therefore valid
                // only when the inner `for` IS already a receive. A body carrying a `!?` query
                // bind denotes a `new`-scoped `send | receive`, not a receive, so it takes the
                // ordinary `Job::Body` route (→ `enter_body` → `enter_proc`) and is expanded
                // there. Without this guard `for(a <- x){ for(b <- y!?(1)){…} }` would keep the
                // exact inert reading the outer form was just fixed to lose.
                Proc::PForUser(rest_rows, rest_body)
                    if !pfor_user_still_has_query_rows(rest_rows) =>
                {
                    Job::ForRows(rest_rows.as_slice(), rest_body.as_ref(), extended)
                },
                other => Job::Body(other, extended),
            },
        };
        self.push_children(Kont::ForBody(state), [job]);
        Ok(())
    }

    fn assemble_receive(
        &mut self,
        state: Box<ForState<'a>>,
        condition: Option<Par>,
    ) -> Result<(), RholangAstLowerError> {
        let ForState {
            env,
            persistent,
            cond,
            binds_rho,
            slots,
            pattern_preparations,
            lowered_body,
            ..
        } = *state;
        let lowered_body =
            lowered_body.expect("rholang lowering: a receive assembled without its continuation");

        // S-D0: a `where` guard the compile-time authority can REFUTE is omitted from the
        // emitted `Par` rather than left for the runtime evaluator to decide again.
        let condition = match (cond, condition) {
            (Some(guard), Some(cond_par)) if self.env(env).options.guard_discharge => {
                let host_verdict = eval_guard_bool(guard);
                let outcome = guard_discharge::classify(
                    host_verdict,
                    &cond_par,
                    guard_discharge::GuardRouting::MachineEvaluated,
                );
                record_guard_outcome(outcome, guard);
                match outcome.omits_condition() {
                    true => None,
                    false => Some(cond_par),
                }
            },
            (_, condition) => condition,
        };

        let receive_binder_count = slots.len();
        let bind_count = receive_binder_count as i32;
        let mut locally_free =
            receive_locally_free(&binds_rho, &lowered_body, receive_binder_count);
        if let Some(cond_par) = &condition {
            locally_free = union(
                locally_free,
                filter_and_adjust_bitset(&cond_par.locally_free, receive_binder_count),
            );
        }
        let connective_used = binds_rho.iter().any(|bind| {
            bind.source
                .as_ref()
                .is_some_and(|source| source.connective_used)
        }) || lowered_body.connective_used;
        let mut receive_par = new_receive_par(
            binds_rho,
            lowered_body,
            persistent,
            false,
            bind_count,
            locally_free.clone(),
            connective_used,
            locally_free,
            connective_used,
        );
        if let Some(cond_par) = condition {
            if let Some(receive) = receive_par.receives.get_mut(0) {
                receive.condition = Some(cond_par);
            }
        }
        for frame in pattern_preparations.into_iter().rev() {
            receive_par = wrap_pattern_preparation(receive_par, frame);
        }
        self.stacks.value(receive_par);
        Ok(())
    }
}

/// [`decompose_for_row`], BORROWED.
///
/// The recursive twin cloned each `InputBind` out of its `Arc` and each `where` guard out of
/// its `Arc<Proc>`; nothing reads the clone, so the driver borrows and the receive path stops
/// deep-copying a bind per row. Otherwise arm-for-arm identical, including which `ForRow`
/// shapes are rejected.
fn decompose_for_row_borrowed(
    row: &ForRow,
) -> Result<(Vec<&InputBind>, bool, Option<&Proc>), RholangAstLowerError> {
    match row {
        ForRow::ForRowSingleNoWhere(b) => {
            let binds = vec![b.as_ref()];
            let persistent = binds.iter().any(|bind| is_persistent_bind(bind));
            Ok((binds, persistent, None))
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            let binds = vec![b.as_ref()];
            let persistent = binds.iter().any(|bind| is_persistent_bind(bind));
            Ok((binds, persistent, Some(cond.as_ref())))
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut binds = Vec::with_capacity(1 + bs.len());
            binds.push(b.as_ref());
            binds.extend(bs.iter());
            let persistent = binds.iter().any(|bind| is_persistent_bind(bind));
            Ok((binds, persistent, None))
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut binds = Vec::with_capacity(1 + bs.len());
            binds.push(b.as_ref());
            binds.extend(bs.iter());
            let persistent = binds.iter().any(|bind| is_persistent_bind(bind));
            Ok((binds, persistent, Some(cond.as_ref())))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("non-ground for-row")),
    }
}

/// The non-recursive half of `lower_method`: assemble an `EMethod` from an already-lowered
/// receiver and argument list.
///
/// Dispatch is on the EVALUATED receiver in the reducer, so one assembler covers every receiver
/// type Rholang supports and a COMM-bound receiver works exactly like a literal one.
fn method_par(method_name: &str, target_par: Par, argument_pars: Vec<Par>) -> Par {
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
    par
}
// ═══════════════════════════════════════════════════════════════════════════════════════════
// M-1 — THE PER-ARM FRAMES
//
// Every arm of [`lower_proc`]'s match lives below as its own `#[inline(never)]` function.
// This is PURE CODE MOTION: not one expression was rewritten, and the call sites above keep
// the documentation that explains each arm's semantics.
//
// ## Why the split is the point rather than a tidy-up
//
// At `-O0` rustc does not overlay the stack slots of mutually exclusive match arms. One
// function carrying 89 arms therefore pays the SUM of every arm's locals in a single frame —
// and `lower_proc` is self-recursive, so that sum was paid once PER NESTING LEVEL of the term
// being lowered. Measured before this split: 48,394 B per level (debug), which put a
// SIGSEGV at nesting depth 170 on an 8 MiB main-thread stack.
//
// After the split, each frame on the recursion path is bounded by ONE arm's locals BY
// CONSTRUCTION, rather than by an accidental property of how many unrelated arms happen to
// share the function. `#[inline(never)]` is what makes that a guarantee instead of a hope:
// without it, LLVM (or cranelift, which this workspace uses for `[profile.dev]`) is free to
// inline the callee straight back into the caller and restore the sum.
//
// ⚠ This is a CONSTANT-factor fix, not a class fix. The traversal is still Θ(depth); M-2
// converts it to an explicit-stack driver, which is what removes the class. The two are
// deliberately separate commits so that each is measured on its own.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The `Proc::PZero` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_p_zero() -> Result<Par, RholangAstLowerError> {
    Ok(Par::default())
}

/// The `Proc::PDrop(name)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_p_flt(
    node: &std::sync::Arc<mettail_runtime::FltNode>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_flt_construction(node.as_ref(), env)
}

/// The `Proc::PPar(parts)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PParInfix(left, right)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::POutput(channel, payload)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PLookaheadAll(subject)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PLookahead(subject, bound)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PForUser(rows, body)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PPersistOutput(channel, payload)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::POutputShort(channel_proc, payload)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PPersistOutputShort(channel_proc, payload)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::PNew(scope)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastInt(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
///
/// ⚠ M-2: the DRIVER calls [`lower_int_value`] directly (there is no frame to save by going
/// through a one-line forwarder in a machine that has no frames), so this is reached only from
/// [`recursive_oracle`]. It is retained because the bounded oracle deliberately preserves the
/// old recursive call graph; the differential suite compares that graph with the PDA driver.
#[cfg_attr(not(test), allow(dead_code))]
#[inline(never)]
fn lower_arm_cast_int(
    value: &std::sync::Arc<Int>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_int_value(value.as_ref(), env)
}

/// The `Proc::CastBool(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_bool(value: &std::sync::Arc<Bool>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        Bool::BoolLit(literal) => Ok(new_gbool_par(*literal, Vec::new(), false)),
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal boolean expression (Bool category)",
        )),
    }
}

/// The `Proc::CastStr(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_str(value: &std::sync::Arc<Str>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        Str::StringLit(literal) => Ok(new_gstring_par(literal.clone(), Vec::new(), false)),
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal string expression (Str category)",
        )),
    }
}

/// The `Proc::PVar(var)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_p_var(
    var: &mettail_runtime::OrdVar,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_proc_var(var, env)
}

/// The `Proc::Err` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_err() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc("error process"))
}

/// The `Proc::CastBigRat(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_big_rat(value: &std::sync::Arc<BigRat>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        BigRat::RatLit(literal) => {
            let rational = literal.get();
            Ok(expr_par(new_gbigrat_expr(
                rational.numer().to_signed_bytes_be(),
                rational.denom().to_signed_bytes_be(),
            )))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal big-rational expression (BigRat category)",
        )),
    }
}

/// The `Proc::CastFixed(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_fixed(value: &std::sync::Arc<Fixed>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        Fixed::FixedLit(literal) => Ok(expr_par(new_gfixedpoint_expr(
            literal.unscaled().to_signed_bytes_be(),
            literal.places(),
        ))),
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal fixed-point expression (Fixed category)",
        )),
    }
}

/// The `Proc::CastFloat(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_float(value: &std::sync::Arc<Float>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        Float::FloatLit(literal) => Ok(expr_par(new_gdouble_expr(literal.get()))),
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal float expression (Float category)",
        )),
    }
}

/// The `Proc::CastBigInt(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_big_int(value: &std::sync::Arc<BigInt>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        BigInt::NumLit(literal) => {
            Ok(expr_par(new_gbigint_expr(literal.get().to_signed_bytes_be())))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal big-integer expression (BigInt category)",
        )),
    }
}

/// The `Proc::CastUInt32(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_u_int32(value: &std::sync::Arc<UInt32>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        UInt32::NumLit(literal) => Ok(new_gint_par(i64::from(*literal), Vec::new(), false)),
        _ => Err(RholangAstLowerError::UnsupportedProc(
            "non-literal u32 expression (UInt32 category)",
        )),
    }
}

/// The `Proc::CastList(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastBag(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastMap(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastSet(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastPathmap(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::CastBytes(value)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_cast_bytes(value: &std::sync::Arc<Bytes>) -> Result<Par, RholangAstLowerError> {
    match value.as_ref() {
        // ★★ `Bytes` LOWERS TO `GByteArray`, NOT `GString` (2026-07-29).
        //
        // This arm read:
        //
        //     Bytes::StringLit(string) => Ok(new_gstring_par(string.clone(), …))
        //
        // justified by "Rholang `Bytes` is a `String`-backed literal
        // (`![String] as Bytes`) … mirrors `CastStr`". The justification was
        // accurate about the DECLARATION and wrong about the SEMANTICS: upstream's
        // wire model (`RhoTypes.proto`) carries `string g_string = 3` and
        // `bytes g_byte_array = 25` as TWO DISTINCT types, so lowering a `Bytes`
        // to a `GString` collapsed them — a `Bytes` and a `Str` of the same
        // content produced IDENTICAL `Par`s, hence identical serialized bytes and
        // identical post-state contributions.
        //
        // ★★ FIXED 2026-07-29: a `Bytes` lowers to `GByteArray`, not `GString`.
        //
        // The two are DISTINCT upstream types, not two spellings of one:
        // `rhoapi`'s `ExprInstance` carries `string g_string = 3` and
        // `bytes g_byte_array = 25`. Lowering a `Bytes` through `new_gstring_par`
        // CONFLATED them — a `Bytes` and a `Str` of the same content produced
        // IDENTICAL `Par`s, hence identical serialized bytes (both formats),
        // identical hashes, and identical post-state contributions. Upstream's own
        // reducer keeps them apart (`hexToBytes`/`bytesToHex`/`toUtf8Bytes` all
        // produce `GByteArray`), so this was not a divergence in semantics but a
        // loss of a distinction the wire model makes.
        //
        // ★ THE CARRIER LANDED 2026-07-30, so this arm is now DIRECT.
        //
        // It previously read `Bytes::StringLit(string) =>
        // new_gbytearray_par(string.clone().into_bytes(), …)` — a UTF-8 re-encode, which was the
        // only defensible reading of a `String`-carried byte array (it is exactly what upstream's
        // `toUtf8Bytes` means) but which could not express a byte sequence that is not valid
        // UTF-8. `![Vec<u8>] as Bytes` (see `languages/src/rholang.rs`) makes the payload the
        // bytes themselves, so there is nothing to re-encode and no unrepresentable value: the
        // literal `b"deadbeef"` carries `[0xde, 0xad, 0xbe, 0xef]`, which no `String` payload
        // could have held.
        Bytes::BytesLit(bytes) => Ok(new_gbytearray_par(bytes.clone(), Vec::new(), false)),
        _ => Err(RholangAstLowerError::UnsupportedProc("non-ground bytes process")),
    }
}

/// The `Proc::IntBinProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_int_bin_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "int(a, w) width fold outside a fold-liftable position (or non-ground width)",
    ))
}

/// The `Proc::UIntBinProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_u_int_bin_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "uint(a, w) width fold outside a fold-liftable position (or non-ground width)",
    ))
}

/// The `Proc::FloatBinProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_float_bin_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "float(a, w) width fold outside a fold-liftable position (or non-ground width)",
    ))
}

/// The `Proc::FixedBinProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_fixed_bin_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "fixed(a, w) width fold outside a fold-liftable position (or non-ground width)",
    ))
}

/// The `Proc::BigintCastProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_bigint_cast_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "bigint(a) precision cast outside a fold-liftable position",
    ))
}

/// The `Proc::BigratCastProc(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_bigrat_cast_proc() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "bigrat(a) precision cast outside a fold-liftable position",
    ))
}

/// The `Proc::Add(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Sub(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Mul(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Div(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Mod(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::NegProc(a)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Eq(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Ne(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Lt(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Gt(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::LtEq(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::GtEq(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::And(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Or(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Implies(a, b)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Not(a)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::Matches(target, formula)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
/// The `Proc::SpatialPPar(..)` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_spatial_p_par() -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(
        "PPar(a, b) outside a `matches` formula (the spatial connective is a pattern former, \
             not a term former; write `{ a | b }` for parallel composition)",
    ))
}

/// The `other` arm.
///
/// Hoisted out of [`lower_proc`] by M-1 — pure code motion. The semantics, and the
/// reasoning behind them, are documented at the call site.
#[inline(never)]
fn lower_arm_unsupported(other: &Proc) -> Result<Par, RholangAstLowerError> {
    Err(RholangAstLowerError::UnsupportedProc(unsupported_construct_name(other)))
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
        // Every method spelling is represented by `MethodCall` and handled before this
        // fail-closed table. Unknown names are intentionally lowered to `EMethod`; the
        // reducer's own table returns the typed method-not-found diagnostic.
        Proc::ToBool(..) => "bool(a) boolean conversion",
        Proc::ToStr(..) => "str(a) string conversion",
        Proc::CastReadZipper(..) => "read-zipper literal",
        Proc::CastWriteZipper(..) => "write-zipper literal",
        _ => "computed rholang expression",
    }
}

/// Lower a binary expression `Proc` (comparison, logic, or A-S4 arithmetic; both operands lowered
/// in `env`) into the corresponding Rholang `Expr` `Par`, propagating `locally_free` and
/// `connective_used` from the operands so an expression that references bound/free variables is
/// tracked correctly. The machine's reducer evaluates the expression (metered).
/// Assemble a binary Rholang `Expr` `Par` from two already-lowered operand `Par`s
/// (`locally_free`/`connective_used` propagation shared by [`lower_binary_expr`] and the
/// ground-string `Add` dispatch).
fn epathmap_par(pathmap: EPathMap, locally_free: Vec<u8>, connective_used: bool) -> Par {
    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EPathmapBody(pathmap)),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    par
}

fn new_epathmap_set_par(entries: Vec<Par>, locally_free: Vec<u8>, connective_used: bool) -> Par {
    let pathmap = EPathMap::new(entries, locally_free.clone(), connective_used, None);
    epathmap_par(pathmap, locally_free, connective_used)
}

fn new_epathmap_map_par(
    entries: Vec<(Par, Par)>,
    locally_free: Vec<u8>,
    connective_used: bool,
) -> Par {
    let pathmap = EPathMap::new_map(entries, locally_free.clone(), connective_used, None);
    epathmap_par(pathmap, locally_free, connective_used)
}

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

/// Is this receiver a `Bag` **written literally at the call site**, so the C1 routing can see that
/// the machine would be handed the bag ENCODING rather than a bag?
///
/// A `Bag` has no Rholang analog. [`lower_bag`] encodes it as
/// `EList[GPrivate(RHOLANG_BAG_ABI_TAG), EList[pairs]]` — an `EList` of **exactly two** elements,
/// whatever the multiset's cardinality. Most routed methods are safe from this by construction
/// (`size`, `union`, `diff`, `contains`, `keys`, … accept only `EMapBody`/`ESetBody`/`EPathmapBody`
/// and so reject the encoding outright), but `length`, `nth`, and `last` accept `EListBody` and would
/// happily answer *about the encoding*: `#{1|2|2}#.length()` would be `2` — the tag plus the pairs
/// list — where the fold body answers the multiset cardinality `3`.
///
/// ## ⚠ This gate is deliberately INCOMPLETE, and that is a reported divergence, not an oversight
///
/// It closes the case that is decidable here: a syntactically apparent bag. It cannot close the
/// case where the receiver's carrier is only known at run time — a COMM-bound variable, or a bag
/// projected out of another collection (`[#{1|2|2}#].nth(0).length()`). Deciding those would
/// require type inference over Rholang, and no shape check reaches them; this is the same class as
/// divergence B. The residue is MEASURED and pinned rather than assumed, by
/// `rho_rholang_conformance.rs::c1_bag_length_residue_when_the_carrier_is_only_known_at_runtime`.
///
/// Closing it completely needs **C3** (bag-aware collection methods injected as system-process
/// `Definition`, so the machine has a real bag algebra instead of an encoding) — it is NOT
/// closeable by changing [`lower_bag`], because the two-element tagged-`EList` shape is the wire
/// ABI that `run.rs:166` decodes.
fn receiver_is_literal_bag(proc: &Proc) -> bool {
    matches!(proc, Proc::CastBag(..))
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
/// `Add` → `EPlusPlus` string-concat parity arm (Rholang `+` has no GString algebra; Rholang `+`
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
///
/// ══ ✅ CLOSED DIVERGENCE — SIGN-ABUTTED NUMERIC LITERALS (measured + closed 2026-07-26) ═════════
///
/// ★ THIS NOTE WAS CORRECTED TWICE ON 2026-07-26. Its first version named the wrong mechanism and
/// drew the wrong conclusion from it; its second still named the k-best election as defect (B).
/// Both are recorded below under "REFUTED" / the ⚠ note so the same reasoning is not re-derived.
/// The fix does NOT belong in this file — see "WHERE THE FIX WENT". The history is kept because
/// this function is exactly where the next reader will be tempted to put the repair.
///
/// A negated numeral lowers to an unevaluated `ENeg`, and the two positions a `Par` can occupy
/// treat that differently: SEND DATA are evaluated by `eval_send` (`eval_expr` then
/// `substitute_and_charge`) before they are stored, PATTERNS are never evaluated. So, while the
/// front end still built a negation node for a sign-abutted numeral,
///
/// ```text
///   @"c"!(-7)          stored  GInt(-7)          (the ENeg was evaluated)
///   for(@-7 <- @"c")   matched ENeg(GInt(7))     (the ENeg was NOT evaluated)
/// ```
///
/// and the two never matched: `for(@-7 <- @"c"){…} | @"c"!(-7)` produced NO COMM — silently, with
/// no error, where consensus Rholang DOES commit it. Both sides now emit `GInt(-7)`, because no
/// negation node is built for a sign-abutted numeral in either implementation.
///
/// ── THE MECHANISM (established, not inferred) ──────────────────────────────────────────────────
///
/// f1r3node folds nothing. Its normalizer's `UnaryExpOp::Neg` arm (`compiler/normalize.rs:185`)
/// is a plain `ENeg` constructor (`unary_exp`, :89-105), and its matcher calls `eval` only for
/// `where`-guards (`matcher/match.rs:304`). The conformance comes from **its LEXER**: every
/// signed numeric literal token carries the sign INSIDE the token, so for a sign-abutted numeral
/// no negation node is ever built. Verified on the built grammar (`rholang-tree-sitter`
/// `grammar.js`, rev `9718ab2`): `for (@-7 <- @"c") …` yields `(long_literal [0,6]-[0,8])` — one
/// token spanning the sign. The discriminator is ADJACENCY: `- 7` and `-(7)` DO build an `ENeg`
/// on both sides, and MeTTaIL already agrees with f1r3node on those.
///
/// The divergent family is therefore EXACTLY the sign-abutted numerals — `-7`, `-0`, `-7i32`,
/// `-7i64`, `-7n`, `-7r`, `-1.5f64`, `-1.5p2`, and any collection containing one. `not true`,
/// `1 + 1`, the boolean and relational connectives, and the casts are all ALREADY conformant:
/// f1r3node leaves them unevaluated in pattern position too, so their non-matching is Rholang's
/// own semantics rather than a defect. Measured end-to-end in
/// `rholang_ground_literal_conformance.rs` against f1r3node's own `Compiler::source_to_adt`.
///
/// ── ⚠ WHY IT MUST NOT BE FIXED HERE ────────────────────────────────────────────────────────────
///
/// Folding `NegProc(<ground literal>)` in this function is the obvious-looking repair and it is
/// WRONG, by measurement: by lowering time the adjacency is already gone — `-7`, `- 7` and `-(7)`
/// all parse to the identical `NegProc(CastInt(NumLit(7)))`. A fold here would fix the abutted
/// spellings and simultaneously BREAK `- 7` / `-(7)` / `- 7n` / `- 1.5f64`, which conform today.
/// That trades one divergence for another; `rholang_ground_literal_conformance.rs::
/// adjacency_is_honoured` is the guard that makes the mistake fail loudly.
///
/// ── WHERE THE FIX WENT (two defects; NEITHER alone was sufficient) ─────────────────────────────
///
///  (A) ✅ CLOSED `98d861a3`. `languages/src/rholang.rs` — the `Int` and `BigRat` token patterns
///      lacked the leading `-?` that `BigInt`, `Fixed` and `Float` already carried, so for
///      `-7`/`-7i32`/`-7i64`/`-7r` no folded reading was generated at all. Both now mirror
///      f1r3node's token set, which signs `long`/`signed_int`/`bigint`/`bigrat`/`float`/
///      `fixed_point` but NOT `unsigned_int`. This closed every EMBEDDED and collection-element
///      position; it left the whole-input positions open, which is (B).
///  (B) ✅ CLOSED. **The projection-isolation helper's `Lit` matcher enforced a token boundary
///      only for IDENT-SHAPED literals.** `emit_projection_isolation_prologue(…,
///      SepSeam::Single)` (`macros/src/gen/runtime/wpda_codegen/facade.rs`) short-circuits —
///      `return Ok(__t)` — as soon as the helper matches, and `NegProc . a:Proc |- "-" a : Proc`
///      is a sigil-led projection shape, so for a whole-input `-7n` the helper framed the RAW
///      STRING as `- ⟨7n⟩`, sub-parsed the operand and wrapped it, destroying the adjacency the
///      lexer had preserved. The repair is
///      `macros/src/gen/runtime/wpda_codegen/lit_boundary.rs`: the matcher now derives each
///      literal's TOKEN-BOUNDARY ALPHABET from the grammar's own token patterns, so a `-`
///      abutting a digit is recognised as a proper prefix of the signed numeral and the helper
///      declines to the (authoritative) monolithic walker.
///
/// ⚠ (B) IS NOT THE k-BEST ELECTION, and an earlier version of this note said it was — recorded
/// so the refuted seam is not re-investigated. That version read: *"the seam is `wpda_walker.rs`'s
/// `RealizeRequestMode::SingleResultElection`, which disagrees with the ordering
/// `__all_with_weights_monolithic` reports."* Measured with `PRATTAIL_CGLL_DIAG` +
/// `PRATTAIL_KBEST_CAND_DIAG` on `-7n`, the single-result walker's accepting root carries a
/// packing family of exactly `{ CastBigInt, CastBigRat }` — there is no `NegProc` candidate in it
/// at all — and `[k-elect]` picks `CastBigInt`, the CONFORMING reading. The election was right and
/// the facade discarded its answer before ever asking. The decisive single-variable A/B was the
/// committed kill switch: `PRATTAIL_NO_PROJ_ISOLATION=1` made `Proc::parse_via_wpda("-7n")` return
/// the conforming `CastBigInt(NumLit(-7))` while the same call without it returned
/// `NegProc(CastBigInt(NumLit(7)))`.
///
/// (A) alone was provably insufficient: `BigInt`, `Float` and `Fixed` ALREADY carried `-?` and
/// diverged anyway, because (B) pre-empted the walker before the lexer's fork could be elected.
///
/// ── REFUTED (the original note's two grounds for declining the fix) ────────────────────────────
///
///   * "folding `-<literal>` removes a metered `ENeg` from consensus cost accounting, which is
///     F1r3node's to change" — REFUTED TWICE OVER. A pattern is matched, never evaluated, so in
///     pattern position there is no metered operation to remove; and in TERM position f1r3node
///     emits no `ENeg` for `-7` either, so MeTTaIL's `ENeg` is itself the cost divergence.
///     Conforming REMOVES a charge f1r3node never levies rather than dropping one it does.
///   * "folding only in pattern position would introduce the pattern-vs-term asymmetry
///     [`lower_proc_in_env`] exists to prevent" — REFUTED as inapplicable. The conforming fix is
///     LEXICAL and therefore position-independent: `-7` is one literal token in both positions,
///     so no asymmetry arises and `lower_proc_in_env`'s single-lowering invariant is untouched.
///
/// Pinned per row and per position (bare / send / pattern) in
/// `rholang-runtime/tests/rholang_ground_literal_conformance.rs`.
/// ★ M-2 (found while enumerating the component, and NOT a member of it).
///
/// `Int::NegInt` nests, so `- - - … - 5` gave this function its own Θ(depth) native-stack
/// axis — one frame per sign. It never appeared in the reproducer and it is not in the
/// 87-member Tarjan component (it calls nothing that calls back into `lower_proc`), which is
/// exactly why it would have survived a conversion scoped to the component. It is converted
/// here rather than logged for later: the fix is a loop, the cost of deferring it is a second
/// campaign, and "the lowering is depth-independent" must not have an asterisk.
///
/// The two passes are the same post-order the recursive form ran: strip the signs, lower the
/// literal, then re-apply the signs outermost-last so the `ENeg` nesting — and therefore the
/// `locally_free`/`connective_used` propagation `unary_expr_par` performs at each level — is
/// byte-identical.
fn lower_int_value(value: &Int, _env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    let mut signs = 0usize;
    let mut value = value;
    while let Int::NegInt(inner) = value {
        signs += 1;
        value = inner.as_ref();
    }
    let Int::NumLit(literal) = value else {
        return Err(RholangAstLowerError::UnsupportedProc(
            "non-literal integer expression (Int category)",
        ));
    };
    let mut par = new_gint_par(*literal, Vec::new(), false);
    for _ in 0..signs {
        par = unary_expr_par(par, |p| ExprInstance::ENegBody(ENeg { p }));
    }
    Ok(par)
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
    // Fold sites collected during ONE lowering (cleared per `lower_rholang_term_with_folds`).
    // Mirrors the thread-local var-cache pattern in `mettail_runtime::binding` — single-threaded
    // lowering-session state, no locks.
    static HELD_FOLD_SITES: std::cell::RefCell<Vec<FoldSpec>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// ★ #36 S5 — the language fingerprint every held-fold site is scoped to.
///
/// Held folds are lifted out of Rholang AST lowering, so the owning language is
/// [`RholangAstRuntimeLanguage`] and its fingerprint is a constant of the build. It is read
/// through the same `metadata().definition_fingerprint()` accessor every other emission path
/// uses, so the fold band can never disagree with the reflect-tag ABI about which language a
/// site belongs to.
///
/// A language whose metadata exposes no fingerprint has no identity to scope by; rather than
/// silently falling back to an unscoped band (which is the defect S5 removes) the sites are
/// scoped to the language NAME, which is still definition-specific and still keeps two
/// co-installed languages apart. `RholangAstRuntimeLanguage` always exposes one — it forwards
/// the generated `RholangLanguage`'s — so the fallback is unreachable in this build and exists
/// only so the derivation is total.
fn held_fold_language_fingerprint() -> String {
    RholangAstRuntimeLanguage
        .metadata()
        .definition_fingerprint()
        .map(|fingerprint| fingerprint.to_string())
        .unwrap_or_else(|| format!("mettail-langname:{}", RholangAstRuntimeLanguage.name()))
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

fn flt_selector_level(node: &FltNode, env: &BoundEnv) -> Option<usize> {
    match &node.selector.0 {
        Var::Free(selector) => env.binders.get(selector).copied(),
        Var::Bound(_) => None,
    }
}

/// Find the first post-order site in one binder body through the exact set of
/// value positions rebuilt by [`replace_first_body_site`]. Receive patterns and
/// nested binder bodies are opaque: the former have their own Match-authority
/// preparation pass and the latter stage in their own de-Bruijn environment.
fn find_first_body_site<T>(proc: &Proc, mut project: impl FnMut(&Proc) -> Option<T>) -> Option<T> {
    enum Work<'a> {
        Proc(&'a Proc),
        Name(&'a Name),
        Emit(&'a Proc),
    }

    let desugared_nodes = Arena::new();
    let mut work = vec![Work::Proc(proc)];
    while let Some(step) = work.pop() {
        match step {
            Work::Proc(proc) => {
                if let Some(desugared) = desugar_surface_sugar_node(proc) {
                    work.push(Work::Proc(desugared_nodes.alloc(desugared)));
                    continue;
                }
                work.push(Work::Emit(proc));
                match proc {
                    Proc::IntBinProc(child, _)
                    | Proc::UIntBinProc(child, _)
                    | Proc::FloatBinProc(child, _)
                    | Proc::FixedBinProc(child, _)
                    | Proc::BigintCastProc(child)
                    | Proc::BigratCastProc(child)
                    | Proc::NegProc(child)
                    | Proc::Not(child)
                    | Proc::PLookaheadAll(child)
                    | Proc::PLookahead(child, _)
                    | Proc::Matches(child, _) => work.push(Work::Proc(child.as_ref())),
                    Proc::POutput(channel, payload) | Proc::PPersistOutput(channel, payload) => {
                        work.push(Work::Proc(payload.as_ref()));
                        work.push(Work::Name(channel.as_ref()));
                    },
                    Proc::POutputShort(channel, payload)
                    | Proc::PPersistOutputShort(channel, payload) => {
                        work.push(Work::Proc(payload.as_ref()));
                        work.push(Work::Proc(channel.as_ref()));
                    },
                    Proc::PParInfix(left, right)
                    | Proc::Add(left, right)
                    | Proc::Sub(left, right)
                    | Proc::Mul(left, right)
                    | Proc::Div(left, right)
                    | Proc::Mod(left, right)
                    | Proc::Eq(left, right)
                    | Proc::Ne(left, right)
                    | Proc::Lt(left, right)
                    | Proc::Gt(left, right)
                    | Proc::LtEq(left, right)
                    | Proc::GtEq(left, right)
                    | Proc::And(left, right)
                    | Proc::Or(left, right)
                    | Proc::Implies(left, right) => {
                        work.push(Work::Proc(right.as_ref()));
                        work.push(Work::Proc(left.as_ref()));
                    },
                    Proc::PPar(parts) => {
                        let first = work.len();
                        work.extend(parts.iter_elements().map(Work::Proc));
                        work[first..].reverse();
                    },
                    Proc::PDrop(name) => work.push(Work::Name(name.as_ref())),
                    Proc::CastList(list) => {
                        if let List::ListLit(items) = list.as_ref() {
                            work.extend(items.iter().rev().map(Work::Proc));
                        }
                    },
                    Proc::CastBag(bag) => {
                        if let Bag::BagLit(entries) = bag.as_ref() {
                            let mut entries = entries.iter().collect::<Vec<_>>();
                            entries.sort_by_key(|(item, _)| *item);
                            work.extend(
                                entries.into_iter().rev().map(|(item, _)| Work::Proc(item)),
                            );
                        }
                    },
                    Proc::CastMap(map) => {
                        if let Map::MapLit(entries) = map.as_ref() {
                            let mut children = Vec::with_capacity(entries.len() * 2);
                            for (key, value) in entries.iter() {
                                children.push(Work::Proc(key));
                                children.push(Work::Proc(value));
                            }
                            work.extend(children.into_iter().rev());
                        }
                    },
                    Proc::CastSet(set) => {
                        if let Set::SetLit(items) = set.as_ref() {
                            let mut items = items.iter().collect::<Vec<_>>();
                            items.sort();
                            work.extend(items.into_iter().rev().map(Work::Proc));
                        }
                    },
                    Proc::CastPathmap(pathmap) => {
                        if let Pathmap::PathmapLit(entries) = pathmap.as_ref() {
                            let mut children = Vec::with_capacity(match entries.mode() {
                                mettail_runtime::PathMapMode::Map => entries.len() * 2,
                                _ => entries.len(),
                            });
                            for entry in entries.iter() {
                                children.push(Work::Proc(entry.key()));
                                if let Some(value) = entry.value() {
                                    children.push(Work::Proc(value));
                                }
                            }
                            work.extend(children.into_iter().rev());
                        }
                    },
                    Proc::MethodCall(receiver, _, arguments) => {
                        work.extend(arguments.iter().rev().map(Work::Proc));
                        work.push(Work::Proc(receiver.as_ref()));
                    },
                    Proc::PForUser(..) | Proc::PNew(..) | Proc::PNewUris(..) => {},
                    _ => {},
                }
            },
            Work::Name(name) => match name {
                Name::NQuote(proc) | Name::NQuoteShort(proc) => {
                    work.push(Work::Proc(proc.as_ref()));
                },
                Name::NParen(inner) => work.push(Work::Name(inner.as_ref())),
                _ => {},
            },
            Work::Emit(proc) => {
                if let Some(site) = project(proc) {
                    return Some(site);
                }
            },
        }
    }
    None
}

/// Find the first run-time-selected FLT in one binder body.
fn find_dynamic_flt(proc: &Proc, env: &BoundEnv) -> Option<Arc<FltNode>> {
    find_first_body_site(proc, |proc| {
        let node = match proc {
            Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => node,
            _ => return None,
        };
        flt_selector_level(node, env).map(|_| node.clone())
    })
}

/// Find the first (innermost) liftable fold in `proc`, NOT descending into nested binders
/// (`PForUser`/`PNew` — their bodies are lifted separately as their own fold-lift scopes).
/// Returns `(operand, kind, width)`. Send sugar is desugared in place so folds inside sugar
/// payloads (`c!(int(5,8), 7)`) are found; the traversal mirrors [`replace_fold`] exactly.
fn find_fold(proc: &Proc) -> Option<(Proc, FoldKind, i64)> {
    find_first_body_site(proc, |candidate| {
        liftable_fold_parts(candidate).map(|(operand, kind, width)| (operand.clone(), kind, width))
    })
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
    replace_first_body_site(proc, r_drop, replaced, |candidate| {
        liftable_fold_parts(candidate).is_some()
    })
}

fn replace_dynamic_flt(
    proc: &Proc,
    target: &Arc<FltNode>,
    result_drop: &Proc,
    replaced: &mut bool,
) -> Proc {
    replace_first_body_site(proc, result_drop, replaced, |candidate| {
        matches!(
            candidate,
            Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node)
                if Arc::ptr_eq(node, target)
        )
    })
}

/// Stack-safe post-order replacement shared by fold and installed-FLT body
/// staging. Binder bodies are intentionally opaque: each becomes its own
/// [`Job::Body`] scope and stages against its own de-Bruijn environment.
fn replace_first_body_site(
    proc: &Proc,
    replacement: &Proc,
    replaced: &mut bool,
    is_site: impl Fn(&Proc) -> bool,
) -> Proc {
    enum Job<'a> {
        VisitProc(&'a Proc),
        VisitName(&'a Name),
        BuildProc {
            proc: &'a Proc,
            proc_base: usize,
            name_base: usize,
        },
        BuildName {
            name: &'a Name,
            proc_base: usize,
            name_base: usize,
        },
    }

    fn take_children<T>(values: &mut Vec<T>, base: usize, expected: usize) -> Vec<T> {
        let children = values.split_off(base);
        assert_eq!(children.len(), expected, "fold-rewrite continuation received the wrong arity");
        children
    }

    let desugared_nodes = Arena::new();
    let mut jobs = vec![Job::VisitProc(proc)];
    let mut proc_values = Vec::new();
    let mut name_values = Vec::new();

    while let Some(job) = jobs.pop() {
        match job {
            Job::VisitProc(proc) => {
                if *replaced {
                    proc_values.push(proc.clone());
                    continue;
                }
                if let Some(desugared) = desugar_surface_sugar_node(proc) {
                    jobs.push(Job::VisitProc(desugared_nodes.alloc(desugared)));
                    continue;
                }

                let proc_base = proc_values.len();
                let name_base = name_values.len();
                match proc {
                    Proc::IntBinProc(a, _)
                    | Proc::UIntBinProc(a, _)
                    | Proc::FloatBinProc(a, _)
                    | Proc::FixedBinProc(a, _)
                    | Proc::BigintCastProc(a)
                    | Proc::BigratCastProc(a)
                    | Proc::Matches(a, _)
                    | Proc::NegProc(a)
                    | Proc::Not(a)
                    | Proc::PLookaheadAll(a)
                    | Proc::PLookahead(a, _) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.push(Job::VisitProc(a.as_ref()));
                    },
                    Proc::POutput(name, payload) | Proc::PPersistOutput(name, payload) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.push(Job::VisitProc(payload.as_ref()));
                        jobs.push(Job::VisitName(name.as_ref()));
                    },
                    Proc::POutputShort(channel, payload)
                    | Proc::PPersistOutputShort(channel, payload) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.push(Job::VisitProc(payload.as_ref()));
                        jobs.push(Job::VisitProc(channel.as_ref()));
                    },
                    Proc::PParInfix(left, right)
                    | Proc::Add(left, right)
                    | Proc::Sub(left, right)
                    | Proc::Mul(left, right)
                    | Proc::Div(left, right)
                    | Proc::Mod(left, right)
                    | Proc::Eq(left, right)
                    | Proc::Ne(left, right)
                    | Proc::Lt(left, right)
                    | Proc::Gt(left, right)
                    | Proc::LtEq(left, right)
                    | Proc::GtEq(left, right)
                    | Proc::And(left, right)
                    | Proc::Or(left, right)
                    | Proc::Implies(left, right) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.push(Job::VisitProc(right.as_ref()));
                        jobs.push(Job::VisitProc(left.as_ref()));
                    },
                    Proc::PPar(parts) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        let first = jobs.len();
                        jobs.extend(parts.iter_elements().map(Job::VisitProc));
                        jobs[first..].reverse();
                    },
                    Proc::PDrop(name) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.push(Job::VisitName(name.as_ref()));
                    },
                    Proc::CastList(list) => {
                        if let List::ListLit(items) = list.as_ref() {
                            jobs.push(Job::BuildProc { proc, proc_base, name_base });
                            jobs.extend(items.iter().rev().map(Job::VisitProc));
                        } else {
                            proc_values.push(proc.clone());
                        }
                    },
                    Proc::CastBag(bag) => {
                        if let Bag::BagLit(entries) = bag.as_ref() {
                            let mut entries = entries.iter().collect::<Vec<_>>();
                            entries.sort_by_key(|(item, _)| *item);
                            jobs.push(Job::BuildProc { proc, proc_base, name_base });
                            jobs.extend(
                                entries
                                    .into_iter()
                                    .rev()
                                    .map(|(item, _)| Job::VisitProc(item)),
                            );
                        } else {
                            proc_values.push(proc.clone());
                        }
                    },
                    Proc::CastMap(map) => {
                        if let Map::MapLit(entries) = map.as_ref() {
                            jobs.push(Job::BuildProc { proc, proc_base, name_base });
                            let mut children = Vec::with_capacity(entries.len() * 2);
                            for (key, value) in entries.iter() {
                                children.push(Job::VisitProc(key));
                                children.push(Job::VisitProc(value));
                            }
                            jobs.extend(children.into_iter().rev());
                        } else {
                            proc_values.push(proc.clone());
                        }
                    },
                    Proc::CastSet(set) => {
                        if let Set::SetLit(items) = set.as_ref() {
                            let mut items = items.iter().collect::<Vec<_>>();
                            items.sort();
                            jobs.push(Job::BuildProc { proc, proc_base, name_base });
                            jobs.extend(items.into_iter().rev().map(Job::VisitProc));
                        } else {
                            proc_values.push(proc.clone());
                        }
                    },
                    Proc::CastPathmap(pathmap) => {
                        if let Pathmap::PathmapLit(entries) = pathmap.as_ref() {
                            jobs.push(Job::BuildProc { proc, proc_base, name_base });
                            let mut children = Vec::with_capacity(match entries.mode() {
                                mettail_runtime::PathMapMode::Map => entries.len() * 2,
                                _ => entries.len(),
                            });
                            for entry in entries.iter() {
                                children.push(Job::VisitProc(entry.key()));
                                if let Some(value) = entry.value() {
                                    children.push(Job::VisitProc(value));
                                }
                            }
                            jobs.extend(children.into_iter().rev());
                        } else {
                            proc_values.push(proc.clone());
                        }
                    },
                    Proc::MethodCall(receiver, _, arguments) => {
                        jobs.push(Job::BuildProc { proc, proc_base, name_base });
                        jobs.extend(arguments.iter().rev().map(Job::VisitProc));
                        jobs.push(Job::VisitProc(receiver.as_ref()));
                    },
                    _ if is_site(proc) => {
                        *replaced = true;
                        proc_values.push(replacement.clone());
                    },
                    _ => proc_values.push(proc.clone()),
                }
            },
            Job::VisitName(name) => {
                if *replaced {
                    name_values.push(name.clone());
                    continue;
                }
                let proc_base = proc_values.len();
                let name_base = name_values.len();
                match name {
                    Name::NQuote(proc) | Name::NQuoteShort(proc) => {
                        jobs.push(Job::BuildName { name, proc_base, name_base });
                        jobs.push(Job::VisitProc(proc.as_ref()));
                    },
                    Name::NParen(inner) => {
                        jobs.push(Job::BuildName { name, proc_base, name_base });
                        jobs.push(Job::VisitName(inner.as_ref()));
                    },
                    _ => name_values.push(name.clone()),
                }
            },
            Job::BuildProc { proc, proc_base, name_base } => {
                let rebuilt = match proc {
                    Proc::IntBinProc(..)
                    | Proc::UIntBinProc(..)
                    | Proc::FloatBinProc(..)
                    | Proc::FixedBinProc(..)
                    | Proc::BigintCastProc(..)
                    | Proc::BigratCastProc(..) => {
                        let mut children = take_children(&mut proc_values, proc_base, 1);
                        let operand = children.pop().expect("one fold operand");
                        rebuild_fold(proc, Arc::new(operand))
                    },
                    Proc::POutput(_, _) => {
                        let payload = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one send payload");
                        let name = take_children(&mut name_values, name_base, 1)
                            .pop()
                            .expect("one send channel");
                        Proc::POutput(Arc::new(name), Arc::new(payload))
                    },
                    Proc::PPersistOutput(_, _) => {
                        let payload = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one persistent-send payload");
                        let name = take_children(&mut name_values, name_base, 1)
                            .pop()
                            .expect("one persistent-send channel");
                        Proc::PPersistOutput(Arc::new(name), Arc::new(payload))
                    },
                    Proc::POutputShort(..) => {
                        let mut children =
                            take_children(&mut proc_values, proc_base, 2).into_iter();
                        let channel = children.next().expect("one short-send channel");
                        let payload = children.next().expect("one short-send payload");
                        Proc::POutputShort(Arc::new(channel), Arc::new(payload))
                    },
                    Proc::PPersistOutputShort(..) => {
                        let mut children =
                            take_children(&mut proc_values, proc_base, 2).into_iter();
                        let channel = children.next().expect("one persistent-short-send channel");
                        let payload = children.next().expect("one persistent-short-send payload");
                        Proc::PPersistOutputShort(Arc::new(channel), Arc::new(payload))
                    },
                    Proc::PParInfix(..)
                    | Proc::Add(..)
                    | Proc::Sub(..)
                    | Proc::Mul(..)
                    | Proc::Div(..)
                    | Proc::Mod(..)
                    | Proc::Eq(..)
                    | Proc::Ne(..)
                    | Proc::Lt(..)
                    | Proc::Gt(..)
                    | Proc::LtEq(..)
                    | Proc::GtEq(..)
                    | Proc::And(..)
                    | Proc::Or(..)
                    | Proc::Implies(..) => {
                        let mut children =
                            take_children(&mut proc_values, proc_base, 2).into_iter();
                        let left = children.next().expect("left binary operand");
                        let right = children.next().expect("right binary operand");
                        rebuild_binary(proc, left, right)
                    },
                    Proc::PPar(..) => {
                        let child_count = proc_values.len() - proc_base;
                        Proc::PPar(
                            take_children(&mut proc_values, proc_base, child_count)
                                .into_iter()
                                .collect(),
                        )
                    },
                    Proc::Matches(_, formula) => {
                        let target = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one matches target");
                        Proc::Matches(Arc::new(target), formula.clone())
                    },
                    Proc::NegProc(..) => {
                        let inner = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one negation operand");
                        Proc::NegProc(Arc::new(inner))
                    },
                    Proc::Not(..) => {
                        let inner = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one not operand");
                        Proc::Not(Arc::new(inner))
                    },
                    Proc::PLookaheadAll(..) => {
                        let subject = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one lookahead subject");
                        Proc::PLookaheadAll(Arc::new(subject))
                    },
                    Proc::PLookahead(_, bound) => {
                        let subject = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one bounded-lookahead subject");
                        Proc::PLookahead(Arc::new(subject), bound.clone())
                    },
                    Proc::PDrop(..) => {
                        let name = take_children(&mut name_values, name_base, 1)
                            .pop()
                            .expect("one drop name");
                        Proc::PDrop(Arc::new(name))
                    },
                    Proc::CastList(..) => {
                        let child_count = proc_values.len() - proc_base;
                        Proc::CastList(Arc::new(List::ListLit(take_children(
                            &mut proc_values,
                            proc_base,
                            child_count,
                        ))))
                    },
                    Proc::CastBag(bag) => {
                        let Bag::BagLit(entries) = bag.as_ref() else {
                            unreachable!("only bag literals receive a continuation")
                        };
                        let mut ordered = entries.iter().collect::<Vec<_>>();
                        ordered.sort_by_key(|(item, _)| *item);
                        let children = take_children(&mut proc_values, proc_base, ordered.len());
                        let mut rebuilt = mettail_runtime::HashBag::new();
                        for (child, (_, count)) in children.into_iter().zip(ordered) {
                            rebuilt.insert_n(child, count);
                        }
                        Proc::CastBag(Arc::new(Bag::BagLit(rebuilt)))
                    },
                    Proc::CastMap(map) => {
                        let Map::MapLit(entries) = map.as_ref() else {
                            unreachable!("only map literals receive a continuation")
                        };
                        let mut children =
                            take_children(&mut proc_values, proc_base, entries.len() * 2)
                                .into_iter();
                        let mut rebuilt = mettail_runtime::HashMapLit::new();
                        for _ in 0..entries.len() {
                            let key = children.next().expect("one map key");
                            let value = children.next().expect("one map value");
                            rebuilt.insert(key, value);
                        }
                        Proc::CastMap(Arc::new(Map::MapLit(rebuilt)))
                    },
                    Proc::CastSet(set) => {
                        let Set::SetLit(items) = set.as_ref() else {
                            unreachable!("only set literals receive a continuation")
                        };
                        let children = take_children(&mut proc_values, proc_base, items.len());
                        Proc::CastSet(Arc::new(Set::SetLit(children.into_iter().collect())))
                    },
                    Proc::CastPathmap(pathmap) => {
                        let Pathmap::PathmapLit(entries) = pathmap.as_ref() else {
                            unreachable!("only pathmap literals receive a continuation")
                        };
                        let rebuilt = match entries.mode() {
                            mettail_runtime::PathMapMode::Empty => {
                                take_children(&mut proc_values, proc_base, 0);
                                mettail_runtime::PathMapLit::new()
                            },
                            mettail_runtime::PathMapMode::Set => {
                                let children =
                                    take_children(&mut proc_values, proc_base, entries.len());
                                mettail_runtime::PathMapLit::from_set_iter(children)
                            },
                            mettail_runtime::PathMapMode::Map => {
                                let mut children =
                                    take_children(&mut proc_values, proc_base, entries.len() * 2)
                                        .into_iter();
                                let mut pairs = Vec::with_capacity(entries.len());
                                for _ in 0..entries.len() {
                                    pairs.push((
                                        children.next().expect("one pathmap key"),
                                        children.next().expect("one pathmap value"),
                                    ));
                                }
                                mettail_runtime::PathMapLit::from_map_iter(pairs)
                            },
                        };
                        Proc::CastPathmap(Arc::new(Pathmap::PathmapLit(rebuilt)))
                    },
                    Proc::MethodCall(_, method, arguments) => {
                        let mut children =
                            take_children(&mut proc_values, proc_base, 1 + arguments.len())
                                .into_iter();
                        let receiver = children.next().expect("one method receiver");
                        Proc::MethodCall(Arc::new(receiver), method.clone(), children.collect())
                    },
                    _ => unreachable!("only traversed constructors receive a continuation"),
                };
                assert_eq!(name_values.len(), name_base);
                if !*replaced && is_site(&rebuilt) {
                    *replaced = true;
                    proc_values.push(replacement.clone());
                } else {
                    proc_values.push(rebuilt);
                }
            },
            Job::BuildName { name, proc_base, name_base } => {
                let rebuilt = match name {
                    Name::NQuote(..) => {
                        let proc = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one quoted proc");
                        Name::NQuote(Arc::new(proc))
                    },
                    Name::NQuoteShort(..) => {
                        let proc = take_children(&mut proc_values, proc_base, 1)
                            .pop()
                            .expect("one short-quoted proc");
                        Name::NQuoteShort(Arc::new(proc))
                    },
                    Name::NParen(..) => {
                        let inner = take_children(&mut name_values, name_base, 1)
                            .pop()
                            .expect("one parenthesized name");
                        Name::NParen(Arc::new(inner))
                    },
                    _ => unreachable!("only traversed names receive a continuation"),
                };
                name_values.push(rebuilt);
            },
        }
    }

    assert_eq!(proc_values.len(), 1);
    assert!(name_values.is_empty());
    proc_values.pop().expect("fold rewrite result")
}

/// Rebuild a binary expression node with the fold replaced in its first-found operand (left then
/// right, mirroring [`find_fold`]).
fn rebuild_binary(orig: &Proc, a: Proc, b: Proc) -> Proc {
    let new_a = Arc::new(a);
    let new_b = Arc::new(b);
    match orig {
        Proc::PParInfix(..) => Proc::PParInfix(new_a, new_b),
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
        // M-0 — the third of the three fold-traversal helpers. `replace_fold` routes
        // `Implies` here, and without this arm the `_` fallback would return the ORIGINAL
        // node, discarding the `*r` substitution `replace_fold` just computed.
        Proc::Implies(..) => Proc::Implies(new_a, new_b),
        // ⚠ `Proc::Matches` is deliberately ABSENT. `rebuild_binary` descends into
        // BOTH operands, which is wrong for `matches`: its right operand is a
        // pattern that must never have a fold lifted out of it. `replace_fold`
        // therefore handles `Matches` with its own arm and never routes it here.
        _ => orig.clone(),
    }
}

/// Lower a fold-lift scope body (the top level, a receive body, or a `new` body), lifting each
/// width/precision fold — ground or COMM-held — into a fold-contract trampoline. With no fold this
/// is exactly `lower_proc`. For one it emits
/// `new ret in { @"<fold>"!(operand, ret) | for(@r <- ret){ body[fold ↦ *r] } }` and records the
/// `FoldSpec`; the `for` body is lifted recursively (nested folds). All de Bruijn bookkeeping rides
/// `extend_env`.
/// Lower a term to a `Par` PLUS the fold contract `Definition` specs its trampolines need (A-S4:
/// every width/precision fold lifts — ground or COMM-held). The `Par` already targets the fold
/// channels; the caller registers the contracts via the runtime's `extra_system_processes` seam.
/// Equivalent to `lower_rholang_term` when the term has no folds (empty `Vec`).
pub fn lower_rholang_term_with_folds(
    term: &dyn Term,
) -> Result<(Par, Vec<FoldSpec>), RholangAstLowerError> {
    clear_held_fold_sites();
    let par = lower_rholang_term(term)?;
    Ok((par, take_held_fold_sites()))
}

/// Clear the fold-site session state. Call before a lowering whose fold contracts you intend to
/// collect with [`take_held_fold_sites`], so stale sites from a prior lowering don't leak. Used by
/// the wrapper's `start_reduction_stepper` / the exec path, which lower through the invocation
/// compiler (not [`lower_rholang_term_with_folds`] directly).
pub fn clear_held_fold_sites() {
    HELD_FOLD_SITES.with(|sites| sites.borrow_mut().clear());
}

/// Take (and clear) the fold sites recorded since the last clear. Empty if the lowering had no
/// folds (e.g. Calculator, whose invocation compiler never lifts; A-S4: Rholang records a site
/// for EVERY fold, ground or COMM-held). The caller materializes the contracts with
/// [`crate::fold_contract::fold_definitions_for`].
pub fn take_held_fold_sites() -> Vec<FoldSpec> {
    HELD_FOLD_SITES.with(|sites| std::mem::take(&mut *sites.borrow_mut()))
}

// ── S-D0/S-D0R: the guard-discharge lowering report ──────────────────────────────────────────
//
// OBSERVABILITY ONLY. Nothing here can change the emitted `Par`: the report is written, never
// read, by the lowering. It rides in thread-local session state for exactly the reason
// `HELD_FOLD_SITES` does — `lower_pfor_user` is reached through ~50 `lower_proc` call sites and
// has no accumulator to thread — and it is likewise cleared per lowering session.

thread_local! {
    /// Guard-discharge outcomes recorded during ONE lowering.
    static GUARD_DISCHARGE_REPORT: std::cell::RefCell<GuardDischargeReport> =
        RefCell::new(GuardDischargeReport::default());
}

/// Clear the guard-discharge session state. Call before a lowering whose guard report you
/// intend to collect with [`take_guard_discharge_report`].
pub fn clear_guard_discharge_report() {
    GUARD_DISCHARGE_REPORT.with(|report| *report.borrow_mut() = GuardDischargeReport::default());
}

/// Take (and clear) the guard outcomes recorded since the last clear: how many guard sites were
/// discharged, refuted (with their `W1 GuardStaticallyFalse` events) and left residual.
///
/// A `Refuted` count is informational — the artifact is byte-identical either way. A non-zero
/// `disagreements` count is a divergence-A-shaped defect that has already been logged at `WARN`.
pub fn take_guard_discharge_report() -> GuardDischargeReport {
    GUARD_DISCHARGE_REPORT.with(|report| std::mem::take(&mut *report.borrow_mut()))
}

/// Record one guard site's outcome on the session report (and emit its `W1` diagnostic if it
/// was refuted). `guard` is rendered lazily — only a refutation pays for the string.
fn record_guard_outcome(outcome: guard_discharge::GuardDischarge, guard: &Proc) {
    GUARD_DISCHARGE_REPORT.with(|report| {
        report.borrow_mut().record(outcome, || format!("{guard:?}"));
    });
}

/// ⚠ M-2: superseded in production by [`decompose_for_row_borrowed`], which returns the same
/// decomposition without cloning an `InputBind` out of its `Arc` per row. Reached only from
/// [`recursive_oracle`], which deliberately preserves the superseded recursive traversal for the
/// byte-equivalence differential.
#[cfg_attr(not(test), allow(dead_code))]
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
/// Decompose a (non-lambda) [`ForRow`] into `(binds, persistent, where-cond)`. The lambda-calculus
/// `ForRow` variants (`FVar`/`Lam*`/`Apply*`/`MLam*`/`MApply*`) never appear in a normalized ground
/// term and are rejected as unsupported.
fn decompose_for_row(
    row: &ForRow,
) -> Result<(Vec<InputBind>, bool, Option<Proc>), RholangAstLowerError> {
    // `ForRow`/`InputBind` derive `Drop`; never move fields out — match by reference and clone.
    //
    // ROOT-P Layer F: the persistent-SPECIFIC ForRow arms (ForRowSinglePersistent*,
    // ForRowPersistent*, ForRowSingleEmptyPersistent*) and their `persistent_first`
    // helper were REMOVED with the now-deleted grammar rules (rholang.rs). A `<=`
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
        _ => Err(RholangAstLowerError::UnsupportedProc("non-ground for-row")),
    }
}

/// Lower a receive-bind PATTERN proc (produced by [`bind_pattern_proc`]) into a Rholang pattern
/// `Par`. Each `Proc::PVar` leaf marks a bound position: it becomes a fresh `FreeVar(counter)`
/// (numbered left-to-right WITHIN this bind) and its `Binder` is pushed to `binders` in the same
/// order. `CastList` patterns recurse (threading the same counter/binders). Any other sub-pattern is
/// a GROUND value matched exactly, lowered via [`lower_proc`] in the empty env.
fn send_par_persistent(channel: Par, data: Vec<Par>) -> Par {
    let locally_free = data
        .iter()
        .fold(channel.locally_free.clone(), |acc, item| union(acc, item.locally_free.clone()));
    let connective_used = channel.connective_used || any_connective_used(&data);
    new_send_par(
        channel,
        data,
        true,
        locally_free.clone(),
        connective_used,
        locally_free,
        connective_used,
    )
}

// ── Receive-bind helpers (replicated from `mettail_languages::rholang::receive`) ───────────────────
//
// The `receive` helpers there are `pub(crate)` to the `mettail_languages` crate and so are NOT
// reachable from this (`rholang-runtime`) crate. They are tiny pure functions over public AST
// constructors, so they are replicated here verbatim rather than widening cross-crate visibility.

/// `Proc::CastList([..])` constructor (the canonical arity list used by receive patterns).
fn mk_proc_list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

/// A-S4: desugar ONE raw send-sugar node (`x!()`, `c!(a,b)`, `@Nil!(q)`, `@n!(…)`, and their `!!`
/// twins) to its canonical channel-first form. Returns `None` for
/// every non-sugar node. Each arm performs EXACTLY the constructor rewrite the rule's `![{…}]
/// fold` body performs (`languages/src/rholang.rs`) — a pure structural rearrangement, no value
/// computation — so lowering the desugared node is byte-identical to lowering the eval-time fold
/// target. Exec submits the RAW parse tree post-A-S4, so these nodes reach the lowering unfolded.
// ── the lookahead suffix: operand admission + bound admission ───────────────────────────────

/// Split a lookahead's operand into `(reply channel, reflected subject)`.
///
/// The operand must be a **send**. Every send SUGAR is admitted, because the operand is first run
/// through [`desugar_surface_sugar_node`] — the same canonicalization `lower_proc` performs on its head
/// node — so `@"r"!(P)[*]`, `r!(P)[*]`, `@Nil!(P)[*]` and the polyadic forms all reach the same
/// two arms rather than only the one shape the demo happens to use.
///
/// A **persistent** send (`x!!(P)[*]`) is deliberately NOT admitted: `!!` means "serve this datum
/// to every taker, forever", and there is no such thing as a persistent *exploration* — the
/// request is answered once, and repeating it would re-run the whole search per consumer. It
/// fails closed here rather than being silently demoted to a linear send.
/// Admit a `P[n]` step bound: a ground, non-negative integer literal.
///
/// Non-negative because `n` counts COMMs and a negative count denotes nothing; `0` is admitted
/// and is meaningful — it explores nothing and truncates immediately, which is the identity of
/// the bounded family and a useful probe.
fn lookahead_bound(bound: &Proc) -> Result<i64, RholangAstLowerError> {
    match bound {
        Proc::CastInt(value) => match value.as_ref() {
            Int::NumLit(literal) if *literal >= 0 => Ok(*literal),
            Int::NumLit(literal) => {
                Err(RholangAstLowerError::LookaheadBoundNotAGroundNonNegativeInt(format!(
                    "negative bound {literal}"
                )))
            },
            other => Err(RholangAstLowerError::LookaheadBoundNotAGroundNonNegativeInt(format!(
                "{other:?}"
            ))),
        },
        other => Err(RholangAstLowerError::LookaheadBoundNotAGroundNonNegativeInt(format!(
            "{other:?}"
        ))),
    }
}

/// Rewrite ONE surface-sugar node to the core form it denotes, or `None` if `proc` is already
/// core. Node-local: the children are untouched, because the driver reaches them itself.
///
/// This is where a Rholang surface abbreviation stops being an abbreviation. `enter_proc` runs
/// it to fixpoint on every `Proc` it visits, so a rule added here is applied at every depth for
/// free — and a surface form NOT handled here reaches the lowering arms verbatim, where it is
/// lowered as whatever core node it structurally resembles.
///
/// ## ⚠ That last sentence is not hypothetical — it is how `!?` came to do nothing
///
/// A query bind `for(p <- x!?(a,b))` means "send `(r, a, b)` to the service `x` on a private
/// return channel `r`, and receive the reply on `r`". Its expansion — `receive::desugar_for_rows`
/// — was correct, was tested, and was *called*: by `Proc::term_eq`, through
/// `rholang/runtime.rs::normalize_send_sugar_canon`. But `term_eq` builds a COMPARISON KEY. The
/// expanded program was computed, compared against, and dropped; the program that ran was the
/// unexpanded one, in which `InputBindQuery(lhs, n, args)` resembles an ordinary receive closely
/// enough that `bind_channel_name` reads `n` as the channel, `args` is discarded, and **no
/// request send is ever emitted**. The receive then rests forever on a channel nobody sends to —
/// silently, and with a zero exit code, because resting is what a receive with no partner is
/// supposed to do.
///
/// The grammar had already declared the expansion as the `PForUser` rule's action
/// (`languages/src/rholang.rs`, `![{ receive::desugar_for_rows(rows, body) }] fold`), but the
/// `fold` marker routes an action to the logic-relation metadata, not to the WPDA parser's
/// semantic action — `desugar_for_rows` does not appear in the generated `wpda.rs` at all — so
/// no expansion reached the term the parser built. Expanding HERE, in the hook every other
/// surface sugar already goes through, is what puts the expansion on the path into execution
/// rather than beside it. There is no second implementation: this arm calls the very function
/// the comparison path calls.
fn desugar_surface_sugar_node(proc: &Proc) -> Option<Proc> {
    let quote = |p: &Arc<Proc>| Arc::new(Name::NQuote(p.clone()));
    let quote_nil = || Arc::new(Name::NQuote(Arc::new(Proc::PZero)));
    let quote_name =
        |n: &Arc<Name>| Arc::new(Name::NQuote(Arc::new(name_pattern_to_proc(n.as_ref()))));
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
        // `!?` query binds: `for(p <- x!?(a, b)){B}` denotes
        // `new r in { x!(*r, a, b) | for(p <- r){B} }` — one fresh private return channel per
        // query bind, all of a `for`'s rows expanded together under one `new`.
        //
        // TERMINATION of `enter_proc`'s fixpoint loop: the result is a `PNew`, which this
        // function does not match, so the loop makes at most one pass here. That holds because
        // `desugar_for_rows` expands EVERY bind `pfor_user_still_has_query_rows` reports —
        // both are `receive::as_query_bind` over the same rows, which is why the classifier
        // exists.
        Proc::PForUser(rows, body) if pfor_user_still_has_query_rows(rows) => {
            desugar_for_rows(rows.clone(), body.as_ref())
        },
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

/// Normalize a MONADIC bind's quoted pattern to the canonical arity shape.
///
/// The arity convention is fixed by the SEND side and this function's only job is to mirror it.
/// `lower_proc`'s `POutput` arm emits `send_par(chan, vec![payload])` — a send always carries
/// EXACTLY ONE datum `Par` — and [`desugar_surface_sugar_node`] encodes the non-scalar arities INTO that one
/// datum as a list:
///
/// | send form   | datum                | matching bind form   | pattern              |
/// |-------------|----------------------|----------------------|----------------------|
/// | `c!(p)`     | `⟦p⟧`                | `for(@p <- c)`       | `⟦p⟧`  (**verbatim**)|
/// | `c!()`      | `⟦[]⟧`               | `for(<- c)`          | `⟦[]⟧`               |
/// | `c!(a,b,…)` | `⟦[a,b,…]⟧`          | `for(@a, @b… <- c)`  | `⟦[a,b,…]⟧`          |
///
/// So a MONADIC pattern is the payload pattern VERBATIM: the arity list is the encoding for the
/// EMPTY and POLYADIC forms only, and those are produced by [`bind_pattern_proc`]'s own
/// `InputBindEmpty*` / `InputBind*Polyadic` arms. There is no monadic shape that needs a wrap —
/// which is why this is the identity. It is kept as a named function so the convention lives in
/// ONE place next to the table that justifies it, rather than being an unexplained `.clone()` at
/// the call site.
///
/// ⚠ ARITY FIX (2026-07-26). The previous body wrapped every pattern EXCEPT `CastList`/`PVar`:
///
/// ```ignore
/// // fn canonicalize_arity_pattern(pattern: &Proc) -> Proc {
/// //     match pattern {
/// //         Proc::CastList(_) | Proc::PVar(_) => pattern.clone(),
/// //         _ => mk_proc_list(vec![pattern.clone()]),
/// //     }
/// // }
/// ```
///
/// That made NO scalar ground pattern able to match a scalar send — silently, with no error and
/// no COMM: `for(@42 <- c)` did not match `c!(42)` but DID match `c!([42])`, and likewise for
/// `@"hi"`, `@true`, `@{1:2}`, `@Set(1,2)`, `@#{1|2}#` and `@{|1:2|}`. The two exempted shapes
/// were precisely the two whose breakage would have been visible: `PVar` (a binder — wrapping it
/// would stop `for(@x <- c)` matching anything at all) and `CastList` (wrapping it would have
/// produced `[[…]]`). The exemption list, not the wrap, was carrying the correctness — so every
/// shape nobody had written a test for was broken.
fn canonicalize_arity_pattern(pattern: &Proc) -> Proc {
    pattern.clone()
}

/// The bind's pattern as a `Proc` whose `Proc::PVar` leaves mark the bound positions.
/// L9-6b: the `FltNode` of an FLT RECEIVE pattern (`for(@lambda`…` <- c)`), or `None`
/// for a non-FLT bind. The FLT surface `@lambda`…`` is a quoted `PFlt*` process
/// (`NQuote`/`NQuoteShort`); a `PFlt*` written directly as a quoted pattern rides
/// the `InputBindQuoted` family. It is intercepted here, ahead of
/// [`bind_pattern_proc`], because an FLT pattern is REFLECTED (its holes become
/// match `FreeVar`s) rather than lowered as an ordinary term — the reflected FLT
/// pattern is then the receive's SOLE pattern, matching the single reflected datum a
/// `@c!(⟦…⟧)` send carries. (Before the 2026-07-26 arity fix this interception was
/// ALSO what kept the FLT pattern clear of `bind_pattern_proc`'s spurious
/// one-element-list wrap; that wrap is gone, so only the reflection reason remains.)
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
        // Monadic binds, name-shaped LHS (`for(x <- c)`, `for(@P <- c)`). ONE datum, so the
        // pattern is the payload pattern verbatim — see [`canonicalize_arity_pattern`] for the
        // send/receive arity table. The former `NVar`-only exemption (everything else wrapped in
        // a one-element list) is the arity bug fixed there: it is now ONE rule for every shape,
        // so a binder and a ground pattern cannot disagree about arity.
        InputBind::InputBind(lhs, _)
        | InputBind::InputBindPersistent(lhs, _)
        | InputBind::InputBindQuery(lhs, _, _) => {
            Some(canonicalize_arity_pattern(&name_pattern_to_proc(lhs.as_ref())))
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

fn lower_name_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.binders.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else if let Some(index) = flt_hole_bound_level(free_var, env) {
                // L9-6b: an FLT hole captured by an enclosing FLT receive pattern.
                Ok(new_boundvar_par(index as i32, Vec::new(), false))
            } else if env.free_vars_are_patterns {
                // M-1b: inside a `matches` formula an unbound NAME variable is a
                // pattern placeholder, not a marker. See
                // `BoundEnv::free_vars_are_patterns`.
                Ok(new_wildcard_par(Vec::new(), true))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false))
            }
        },
        Var::Bound(_) => Err(RholangAstLowerError::UnsupportedName("unopened bound name variable")),
    }
}

fn lower_proc_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.binders.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else if let Some(index) = flt_hole_bound_level(free_var, env) {
                // L9-6b: an FLT hole captured by an enclosing FLT receive pattern —
                // bound by NAME (the hole is a string metavar, so it never shares a
                // moniker `FreeVar` with this reference).
                Ok(new_boundvar_par(index as i32, Vec::new(), false))
            } else if env.free_vars_are_patterns {
                // M-1b: inside a `matches` formula an unbound PROCESS variable is a
                // pattern placeholder, not a marker. See
                // `BoundEnv::free_vars_are_patterns`.
                Ok(new_wildcard_par(Vec::new(), true))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(send_par(
                    new_gstring_par(FREE_PROC_OUTPUT.to_string(), Vec::new(), false),
                    vec![new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false)],
                ))
            }
        },
        Var::Bound(_) => {
            Err(RholangAstLowerError::UnsupportedProc("unopened bound process variable"))
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
    pretty_var_name(free_var)
        .ok()
        .and_then(|name| env.flt_hole_level(name))
}

// ── L9-6b: FLT `PFlt` elaboration (construction + pattern) ─────────────────────────────────────

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

fn runtime_template_parts(
    template: ScopedFltTemplate<'_>,
) -> (Vec<RuntimeTemplatePiece>, Vec<NamedRuntimeTemplateHole>) {
    let pieces = template
        .pieces
        .iter()
        .map(|piece| match piece {
            mettail_runtime::FltTemplatePiece::Text { text, .. } => {
                RuntimeTemplatePiece::Text(text.clone())
            },
            mettail_runtime::FltTemplatePiece::Hole { id, .. } => RuntimeTemplatePiece::Hole(id.0),
        })
        .collect();
    let holes = template
        .telescope
        .iter()
        .map(|hole| NamedRuntimeTemplateHole {
            id: hole.id.0,
            name: hole.name.clone(),
            category: hole.category.clone(),
        })
        .collect();
    (pieces, holes)
}

/// Resolve a `PFlt` node's guest reflector + definition fingerprint, then reflect
/// its structural template to a guest [`GroundTerm`] whose holes are
/// `^free(name)` leaves — the shared front half of construction and matching.
fn flt_resolve_and_reflect(
    node: &FltNode,
    env: &BoundEnv,
) -> Result<(GroundTerm, String), RholangAstLowerError> {
    if flt_selector_level(node, env).is_some() {
        return Err(RholangAstLowerError::FltReflect(
            "a lexical installed-language selector reached the static FLT adapter without body staging"
                .into(),
        ));
    }
    let guest = env
        .resolver
        .resolve(&node.selector_name)
        .ok_or_else(|| RholangAstLowerError::UnresolvedFltTag(node.selector_name.clone()))?;
    let fingerprint = guest
        .metadata()
        .definition_fingerprint()
        .ok_or_else(|| RholangAstLowerError::FltGuestHasNoFingerprint(node.selector_name.clone()))?
        .to_string();
    let ground = guest
        .parse_and_reflect_flt_template(node)
        .map_err(RholangAstLowerError::FltReflect)?;
    Ok((ground, fingerprint))
}

/// L9-6b CONSTRUCTION arm: lower a `PFlt` in a VALUE (send / re-quote) position.
/// Each declared hole `${name}` is FILLED with its in-scope binding — the reflected
/// `^bound(peano(level))` image (E-2-D-opaque to the host binder machinery, so a
/// captured hole survives the Rholang boundary), read by NAME from the enclosing
/// FLT pattern's hole bindings. `reflect_flt_construction` (C2) then recomputes each
/// hole-bearing node's `⌜^nog⌝` marker from the FILLED subtree — never a stale
/// `⌜^gnd⌝` — so a binder-carrying fill drives β. A hole-FREE `PFlt` (a spelled-out
/// subject) has an empty fill map and reflects to its exact ground image.
fn lower_flt_construction(node: &FltNode, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    let (ground, fingerprint) = flt_resolve_and_reflect(node, env)?;
    let mut fills: BTreeMap<String, Par> = BTreeMap::new();
    for hole in &node.holes {
        let level = env.flt_hole_level(&hole.name).ok_or_else(|| {
            RholangAstLowerError::FltReflect(format!(
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
        .map_err(|error| RholangAstLowerError::FltReflect(error.to_string()))
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
) -> Result<(Par, i32, Vec<String>), RholangAstLowerError> {
    let (ground, fingerprint) = flt_resolve_and_reflect(node, env)?;
    let holes = flt_holes_of(node);
    let FltPatternReflection {
        pattern, free_count, mut hole_bindings, ..
    } = reflect_flt_pattern(&ground, &holes, &fingerprint)
        .map_err(|error| RholangAstLowerError::FltReflect(error.to_string()))?;
    // `hole_bindings` is `(name, FreeVar level)` in first-appearance order; sort by
    // level to index it positionally (defensive — first-appearance already IS level
    // order), then project to the names.
    hole_bindings.sort_by_key(|(_, level)| *level);
    let hole_names = hole_bindings
        .into_iter()
        .map(|(name, _)| name)
        .collect::<Vec<String>>();
    Ok((pattern, free_count, hole_names))
}

fn pretty_var_name(var: &FreeVar<String>) -> Result<&str, RholangAstLowerError> {
    var.pretty_name
        .as_deref()
        .ok_or(RholangAstLowerError::FreeVarWithoutName)
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

    BoundEnv {
        // Compilation options are scope-INVARIANT: a nested binder scope compiles under the
        // same declared options as its parent (S-D0).
        options: env.options,
        binders: binder_map,
        hole_binders,
        resolver: Arc::clone(&env.resolver),
        free_vars_are_patterns: env.free_vars_are_patterns,
    }
}

fn send_par(channel: Par, data: Vec<Par>) -> Par {
    let locally_free = data
        .iter()
        .fold(channel.locally_free.clone(), |acc, item| union(acc, item.locally_free.clone()));
    let connective_used = channel.connective_used || any_connective_used(&data);
    new_send_par(
        channel,
        data,
        false,
        locally_free.clone(),
        connective_used,
        locally_free,
        connective_used,
    )
}

fn wrap_pattern_preparation(inner: Par, frame: PatternPrepFrame) -> Par {
    let ret_channel = new_boundvar_par(0, Vec::new(), false);
    let send = send_par(frame.channel, vec![frame.request]);
    let bind = ReceiveBind {
        patterns: vec![new_freevar_par(0, Vec::new())],
        source: Some(ret_channel),
        remainder: None,
        free_count: 1,
    };
    let recv_locally_free = receive_locally_free(std::slice::from_ref(&bind), &inner, 1);
    let recv = new_receive_par(
        vec![bind],
        inner,
        false,
        false,
        1,
        recv_locally_free.clone(),
        false,
        recv_locally_free,
        false,
    );
    let staged = send.append(recv);
    let locally_free = filter_and_adjust_bitset(&staged.locally_free, 1);
    new_new_par(
        1,
        staged,
        Vec::new(),
        BTreeMap::new(),
        locally_free.clone(),
        locally_free,
        false,
    )
}

fn locally_free_union(parts: &[Par]) -> Vec<u8> {
    parts
        .iter()
        .fold(Vec::new(), |acc, part| union(acc, part.locally_free.clone()))
}

/// M-1b: does any of `parts` carry a connective (a Rholang connective, a free
/// variable, or a wildcard) — i.e. is the composite they build NON-CONCRETE?
///
/// ★ `connective_used` must be DERIVED, exactly as `locally_free` already is, and
/// for the same reason: it is a cached summary of the subtree, and a composite
/// that ASSERTS `false` over a non-concrete operand is simply wrong. Understating
/// it is not a cosmetic defect — `SpatialMatcher<Par,Par>::spatial_match` and
/// `spatial_match_par_ref` both short-circuit to structural EQUALITY when
/// `!pattern.connective_used`, so a pattern whose flag is understated is compared
/// for equality and a wildcard nested inside it never gets to match anything.
///
/// Every existing (term-position) call site lowers operands that are all
/// concrete, so this derivation returns `false` there and the emitted `Par` is
/// byte-identical to the pre-M-1b output. It becomes load-bearing only inside a
/// `matches` formula, where [`BoundEnv::free_vars_are_patterns`] turns an unbound
/// variable into a wildcard.
fn any_connective_used(parts: &[Par]) -> bool {
    parts.iter().any(|part| part.connective_used)
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

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Unit tests for the alternative-collection walk
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod alternative_collection_tests {
    use super::*;

    /// The RECURSIVE form of [`collect_proc_alternatives`], retained verbatim as a
    /// differential ORACLE.
    ///
    /// Keeping the superseded implementation as a test-only twin is the cheapest way to
    /// state what "the conversion changed nothing" means: not "the author believes the
    /// orders match", but "the two implementations were run against the same inputs and
    /// produced identical output, including the error cases".
    fn collect_recursive<'a>(
        inner: &'a RholangTermInner,
        alternatives: &mut Vec<&'a Proc>,
    ) -> Result<(), RholangAstLowerError> {
        match inner {
            RholangTermInner::Proc(proc) => {
                alternatives.push(proc);
                Ok(())
            },
            RholangTermInner::Ambiguous(inner_alternatives) => {
                for alternative in inner_alternatives {
                    collect_recursive(alternative, alternatives)?;
                }
                Ok(())
            },
            _ => Err(RholangAstLowerError::ExpectedProcTerm),
        }
    }

    fn proc_leaf(n: i64) -> RholangTermInner {
        RholangTermInner::Proc(Proc::CastInt(Arc::new(Int::NumLit(n))))
    }

    /// A non-`Proc`, non-`Ambiguous` node — the arm both forms answer `Err` on.
    fn foreign_leaf() -> RholangTermInner {
        RholangTermInner::Int(Int::NumLit(0))
    }

    /// Render a collected alternative list as the integers it carries, so the two walks
    /// can be compared on VALUE and ORDER rather than on pointer identity.
    fn as_ints(alternatives: &[&Proc]) -> Vec<i64> {
        alternatives
            .iter()
            .map(|proc| match proc {
                Proc::CastInt(value) => match value.as_ref() {
                    Int::NumLit(n) => *n,
                    other => panic!("test built only NumLit leaves, got {other:?}"),
                },
                other => panic!("test built only CastInt leaves, got {other:?}"),
            })
            .collect()
    }

    #[test]
    fn explicit_empty_collection_constructors_lower_to_exact_empty_carriers() {
        let map = lower_rholang_proc(&Proc::MapEmpty).expect("Map() lowers");
        let [map_expr] = map.exprs.as_slice() else {
            panic!("Map() must lower to exactly one expression")
        };
        let Some(ExprInstance::EMapBody(map_body)) = &map_expr.expr_instance else {
            panic!("Map() must lower to EMap, got {map_expr:?}")
        };
        assert!(map_body.kvs.is_empty());
        assert!(map_body.remainder.is_none());
        assert!(map_body.locally_free.is_empty());
        assert!(!map_body.connective_used);

        let pathmap = lower_rholang_proc(&Proc::PathmapEmpty).expect("Pathmap() lowers");
        let [pathmap_expr] = pathmap.exprs.as_slice() else {
            panic!("Pathmap() must lower to exactly one expression")
        };
        let Some(ExprInstance::EPathmapBody(pathmap_body)) = &pathmap_expr.expr_instance else {
            panic!("Pathmap() must lower to EPathMap, got {pathmap_expr:?}")
        };
        assert_eq!(pathmap_body.mode(), models::rust::epathmap_trie_codec::EPathMapMode::Empty);
        assert_eq!(pathmap_body.len(), 0);
        assert!(pathmap_body.remainder.is_none());
        assert!(pathmap_body.locally_free.is_empty());
        assert!(!pathmap_body.connective_used);
    }

    /// Every shape, including ones the parser cannot produce (nested `Ambiguous`) and
    /// ones that fail (a foreign leaf, in each position). The iterative walk must agree
    /// with the recursive oracle on the collected ORDER **and** on the `Result`.
    #[test]
    fn iterative_alternative_collection_matches_the_recursive_walk() {
        let shapes: Vec<RholangTermInner> = vec![
            // a bare reading
            proc_leaf(1),
            // the flat shape the parser actually produces
            RholangTermInner::Ambiguous(vec![proc_leaf(1), proc_leaf(2), proc_leaf(3)]),
            // NESTED — unreachable from `from_alternatives`, reachable by hand
            RholangTermInner::Ambiguous(vec![
                proc_leaf(1),
                RholangTermInner::Ambiguous(vec![proc_leaf(2), proc_leaf(3)]),
                proc_leaf(4),
            ]),
            // deeper nesting, left-leaning
            RholangTermInner::Ambiguous(vec![
                RholangTermInner::Ambiguous(vec![RholangTermInner::Ambiguous(vec![proc_leaf(1)])]),
                proc_leaf(2),
            ]),
            // an empty alternative vector
            RholangTermInner::Ambiguous(vec![]),
            // failures, in first / middle / last position and nested
            foreign_leaf(),
            RholangTermInner::Ambiguous(vec![foreign_leaf(), proc_leaf(1)]),
            RholangTermInner::Ambiguous(vec![proc_leaf(1), foreign_leaf(), proc_leaf(2)]),
            RholangTermInner::Ambiguous(vec![proc_leaf(1), proc_leaf(2), foreign_leaf()]),
            RholangTermInner::Ambiguous(vec![
                proc_leaf(1),
                RholangTermInner::Ambiguous(vec![proc_leaf(2), foreign_leaf()]),
                proc_leaf(3),
            ]),
        ];

        for (index, shape) in shapes.iter().enumerate() {
            let mut from_iterative = Vec::new();
            let iterative = collect_proc_alternatives(shape, &mut from_iterative);

            let mut from_recursive = Vec::new();
            let recursive = collect_recursive(shape, &mut from_recursive);

            assert_eq!(
                iterative.is_ok(),
                recursive.is_ok(),
                "shape {index}: the two walks disagreed on success/failure"
            );
            assert_eq!(
                as_ints(&from_iterative),
                as_ints(&from_recursive),
                "shape {index}: the iterative walk collected a DIFFERENT ORDER than the \
                 recursive oracle. Order is load-bearing — `lower_proc_alternatives` dedups \
                 with `BTreeSet::insert`, which keeps the FIRST occurrence."
            );
        }
    }

    /// The ordering property stated positively, so a reader does not have to run the
    /// oracle in their head to see what "source order" means.
    #[test]
    fn alternatives_are_collected_in_source_order_across_nesting() {
        let shape = RholangTermInner::Ambiguous(vec![
            proc_leaf(1),
            RholangTermInner::Ambiguous(vec![proc_leaf(2), proc_leaf(3)]),
            proc_leaf(4),
        ]);
        let mut collected = Vec::new();
        collect_proc_alternatives(&shape, &mut collected).expect("every leaf is a Proc");
        assert_eq!(as_ints(&collected), vec![1, 2, 3, 4]);
    }

    /// One oversized field must not set the width of every work item.
    ///
    /// `Job` and `Kont` are the element types of the driver's two stacks, so their size is
    /// paid on every push and every pop of every term the machine lowers — while the
    /// payloads that would inflate them ([`ForState`], and the `Par` in
    /// [`Kont::HeldFold`]) belong to STAGES that occur at most once per `for` row or per
    /// held-fold site. Both are behind a `Box` for that reason, and this is the statement
    /// that says so in numbers rather than in a comment nobody re-checks.
    ///
    /// The bound is a ceiling with headroom, not a fixture: it admits a new small variant
    /// without ceremony and fails the moment a large payload is inlined again. When it
    /// fires, box the offending field — do NOT raise the bound, and do NOT take clippy's
    /// literal suggestion of `Combine(Box<Kont>)`, which would put an allocation on the
    /// hot path to hide a cold variant's width.
    #[test]
    fn the_work_item_stays_narrow() {
        use std::mem::size_of;
        // Captured unless `--nocapture`, so this is the measurement on demand rather than
        // noise: `cargo test -p rholang-runtime --lib the_work_item_stays_narrow --
        // --nocapture` prints the current widths.
        println!(
            "Job = {} bytes, Kont = {} bytes, Par = {} bytes",
            size_of::<Job<'_>>(),
            size_of::<Kont<'_>>(),
            size_of::<Par>(),
        );
        assert!(
            size_of::<Job<'_>>() <= 64,
            "Job is {} bytes; something large was inlined into it (or into Kont, at {} \
             bytes, which Job::Combine carries)",
            size_of::<Job<'_>>(),
            size_of::<Kont<'_>>(),
        );
        assert!(size_of::<Kont<'_>>() <= 64, "Kont is {} bytes", size_of::<Kont<'_>>());
    }
}
