//! RhoNet execution-plan model for Rho-native MeTTaIL runtime semantics.
//!
//! This is a typed planning artifact, not a runtime interpreter. It records the
//! contract the production refactor is moving toward: every non-semantic-
//! predicate rule is represented as Rho-machine work, while semantic predicates
//! are the only external execution obligations allowed to remain.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::grammar::{GrammarItem, GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::identity::{
    behavioral_predicate_identity, equation_identity, grammar_rule_identity,
    language_definition_fingerprint, pattern_identity, premises_identity, rewrite_identity,
};
use mettail_ast::language::{
    BehavioralPred, ChannelConfig, Equation, GuardConfig, LanguageDef, Premise, RewriteRule,
};

use crate::lower::RhoLowering;

/// Stable rule identifiers for generated RhoNet rules.
///
/// These format helpers are the single source of truth for the six rule-id
/// namespaces. They are called from [`RhoNetProgram::from_language_def`] (which
/// builds the planning artifact) AND from the `rho_net_lower` walk (which
/// re-derives the same identifiers to align its lowered `Par` artifacts against
/// `program.rules`). Keeping one definition each guarantees the two walks cannot
/// drift apart on the id shape.
pub(crate) fn rule_id_scalar(label: &str) -> String {
    format!("rule:{label}")
}

pub(crate) fn rule_id_term(index: usize, label: &str) -> String {
    format!("rule:term:{index}:{label}")
}

pub(crate) fn rule_id_native(index: usize, label: &str) -> String {
    format!("rule:native:{index}:{label}")
}

pub(crate) fn rule_id_equation(index: usize, name: &str) -> String {
    format!("rule:equation:{index}:{name}")
}

pub(crate) fn rule_id_rewrite(index: usize, name: &str) -> String {
    format!("rule:rewrite:{index}:{name}")
}

pub(crate) fn rule_id_join(label: &str) -> String {
    format!("rule:join:{label}")
}

/// Stable channel name used by generated RhoNet rules.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RhoNetChannel {
    pub name: String,
    pub kind: RhoNetChannelKind,
}

impl RhoNetChannel {
    pub fn new(name: impl Into<String>, kind: RhoNetChannelKind) -> Self {
        Self { name: name.into(), kind }
    }

    /// Reflected term-location channel from the `knotted-topoi` semantics —
    /// `loc:{fingerprint}/{path}`, fingerprint-scoped per INV-S6.
    pub fn location(language_fingerprint: &str, path: impl Into<String>) -> Self {
        Self::new(
            scoped_channel_name("loc", language_fingerprint, path),
            RhoNetChannelKind::Location,
        )
    }

    /// Reflected set-automaton trace/state channel — `sa:{fingerprint}/{trace}`,
    /// fingerprint-scoped per INV-S6.
    pub fn set_automaton_trace(language_fingerprint: &str, trace: impl Into<String>) -> Self {
        Self::new(
            scoped_channel_name("sa", language_fingerprint, trace),
            RhoNetChannelKind::SetAutomatonTrace,
        )
    }

    /// Name-consistency channel used for non-linear pattern variables —
    /// `eq:{fingerprint}/{name}`, fingerprint-scoped per INV-S6.
    pub fn consistency(language_fingerprint: &str, name: impl Into<String>) -> Self {
        Self::new(
            scoped_channel_name("eq", language_fingerprint, name),
            RhoNetChannelKind::Consistency,
        )
    }

    /// User/runtime observation channel — `obs:{fingerprint}/{name}`, fingerprint-scoped
    /// per INV-S6.
    pub fn observation(language_fingerprint: &str, name: impl Into<String>) -> Self {
        Self::new(
            scoped_channel_name("obs", language_fingerprint, name),
            RhoNetChannelKind::Observation,
        )
    }
}

/// THE fingerprint-scoping primitive of INV-S6: `{family}:{language_fingerprint}/{path}`.
///
/// # The invariant
///
/// > Every channel name emitted by the driver network — firing-visible (`sa:`), carrier
/// > (`ac:`), matching-τ (`loc:`/`col:`/`cap:`), contextual plumbing (`ph:`), and PathMap
/// > index (`e6a:`) — contains the emitting language's fingerprint.
///
/// It is stated as an INVARIANT over emitted names rather than as a list of emission sites,
/// and enforced by a sweep of the emitted `Par` (`rholang-codegen/tests/s6_channel_
/// fingerprint_invariant.rs`) rather than by review of that list. Two prior enumerations of
/// the affected sites were both short — `RhoNetChannel::location` alone has nineteen
/// production callers — which is precisely why the scoping lives at the KEY DERIVATION
/// POINTS and every derived child name inherits it by composition:
///
/// ```text
///   spread_child_location(parent, op, i) = "{parent}/{op}.{i}"      ← inherits from parent
///   ac_carrier_channel(loc_channel, op)  = "ac:{loc_channel}/{op}"  ← inherits from loc:
///   contextual_premise_hole_channel(c)   = "ph:{c}"                 ← inherits from loc:
///   "{dispatch_channel}/sa-locate"                                  ← inherits from sa:
/// ```
///
/// so scoping the roots scopes the whole tree, and a new emission site cannot opt out
/// without constructing a raw `format!` that the sweep test then fails on.
///
/// # Why the fingerprint, and why verbatim
///
/// Without it, two co-installed languages can share a driver-network channel and consume
/// each other's operands — a cross-fingerprint WRONG FIRING, not merely starvation. The
/// sharpest construction is the capture channel: a σ capture CANNOT discriminate by
/// construction, because a pattern variable must accept an arbitrary subterm, so
/// `wrap_capture_chain` binds the fully collapsed subterm with no tag to match on and no
/// possibility of one. Language B's capture receiver therefore consumes language A's
/// collapsed subterm and instantiates B's RHS with A's operand. It needs only a shared
/// constructor name and site string — no shared pattern text, and no attacker.
///
/// The fingerprint rides VERBATIM (the S4/S5 convention: collision-free BY CONSTRUCTION,
/// not by digest), so two scoped names are equal iff their `(family, fingerprint, path)`
/// triples are equal. There is no collision probability to bound.
///
/// # Why `/` separates the fingerprint from the path
///
/// `language_definition_fingerprint` renders `mettail-langdef-v1:{16 hex}`, which contains
/// `:` but is slash-free. The FIRST `/` after the family prefix therefore splits the
/// fingerprint from the path unambiguously, which is what lets the `ac:` reader recover its
/// operator label and the classification taxonomy keep matching on the bare family prefix.
/// The slash-freedom is asserted here, mirroring the dot-free `debug_assert` that guards the
/// reflected-tag ABI in [`crate::rho_net_lower::reflect_tag`].
pub fn scoped_channel_name(
    family: &str,
    language_fingerprint: &str,
    path: impl Into<String>,
) -> String {
    debug_assert!(
        !language_fingerprint.contains('/'),
        "INV-S6 channel ABI: the fingerprint must be slash-free so a reader can split the \
         scope at the FIRST `/` and leave a slashed location path intact; got \
         {language_fingerprint:?}"
    );
    format!("{family}:{language_fingerprint}/{}", path.into())
}

/// Role of a channel in the lowered RhoNet program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoNetChannelKind {
    Location,
    SetAutomatonTrace,
    Consistency,
    Observation,
}

/// Class of generated Rho-machine rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoNetRuleKind {
    StructuralConstructor,
    BaseRewrite,
    ContextualRewrite,
    StructuralCongruence,
    NativeFold,
    NativeSystemProcess,
    Comm,
}

/// A semantic predicate obligation referenced by RhoNet guards.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RhoNetSemanticPredicate {
    pub id: String,
    pub quality: RhoNetSemanticPredicateQuality,
}

impl RhoNetSemanticPredicate {
    pub fn new(id: impl Into<String>, quality: RhoNetSemanticPredicateQuality) -> Self {
        Self { id: id.into(), quality }
    }
}

/// Admission quality for a semantic predicate obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoNetSemanticPredicateQuality {
    ExactDecidable,
    RejectSafeApprox,
    TrustedNativeGuard,
    RuntimeObservation,
}

/// Reusable RHS artifact template. Later lowering turns this into normalized
/// `rhoapi::Par`; this type intentionally stores only identity/provenance.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RhoNetRhsTemplate {
    pub id: String,
    pub fingerprint: String,
}

impl RhoNetRhsTemplate {
    pub fn new(id: impl Into<String>, fingerprint: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            fingerprint: fingerprint.into(),
        }
    }
}

/// One generated Rho-machine rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoNetRule {
    pub id: String,
    pub label: Option<String>,
    pub kind: RhoNetRuleKind,
    pub input_channels: Vec<String>,
    pub output_channel: String,
    pub semantic_predicate_guards: Vec<String>,
    pub rhs_template: String,
}

impl RhoNetRule {
    pub fn new(
        id: impl Into<String>,
        kind: RhoNetRuleKind,
        input_channels: Vec<String>,
        output_channel: impl Into<String>,
        rhs_template: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            label: None,
            kind,
            input_channels,
            output_channel: output_channel.into(),
            semantic_predicate_guards: Vec::new(),
            rhs_template: rhs_template.into(),
        }
    }

    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    pub fn with_semantic_predicate_guard(mut self, guard: impl Into<String>) -> Self {
        self.semantic_predicate_guards.push(guard.into());
        self
    }
}

/// Complete RhoNet planning artifact for one generated language/runtime.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RhoNetProgram {
    pub language_fingerprint: String,
    pub channels: Vec<RhoNetChannel>,
    pub semantic_predicates: Vec<RhoNetSemanticPredicate>,
    pub rhs_templates: Vec<RhoNetRhsTemplate>,
    pub rules: Vec<RhoNetRule>,
}

impl RhoNetProgram {
    pub fn new(language_fingerprint: impl Into<String>) -> Self {
        Self {
            language_fingerprint: language_fingerprint.into(),
            ..Self::default()
        }
    }

    /// Build the RhoNet planning view for scalar contracts that already lowered
    /// to normalized Rho AST.
    ///
    /// This does not claim rejected rules are covered. It records the covered
    /// scalar-native-fold subset as Rho-machine work, while the existing
    /// coverage gate remains responsible for every rejected rule and semantic
    /// predicate obligation.
    pub fn from_scalar_lowering(lowering: &RhoLowering) -> Self {
        let mut program = Self::new(lowering.definition_fingerprint());
        program.add_scalar_lowering(lowering);
        program
    }

    /// Build the RhoNet planning view from the full language definition plus
    /// the already-normalized scalar lowering.
    ///
    /// Scalar contracts become native-fold Rho-machine rules. Rejected native
    /// folds/operators that are admitted by backend coverage become explicit
    /// native system-process rules. Grammar constructors, equations, base
    /// rewrites, contextual rewrites, and declared joins are represented as Rho-machine graph rules with
    /// set-automaton trace inputs and location outputs. Behavioral semantic
    /// predicates remain explicit guard obligations; structural premises are
    /// modeled as Rho-machine consistency inputs instead of host fallback work.
    pub fn from_language_def(def: &LanguageDef, lowering: &RhoLowering) -> Self {
        // E-3 Stage-0: SELF-time phase span (no-op without an active collection window).
        let _from_language_def_span = crate::pipeline_spans::phase_span(
            crate::pipeline_spans::PipelinePhase::FromLanguageDef,
        );
        let mut program = Self::new(language_definition_fingerprint(def));
        program.add_scalar_lowering(lowering);
        program.add_constructor_rules(&def.terms);
        program.add_native_system_process_rules(&def.terms, lowering);
        program.add_term_guard_predicates(def);
        if let Some(guard_config) = def.guard_config.as_ref() {
            program.add_guard_config(guard_config);
        }
        program.add_equations(&def.equations);
        program.add_rewrites(&def.rewrites);
        if let Some(channels) = def
            .guard_config
            .as_ref()
            .and_then(|guards| guards.channels.as_ref())
        {
            program.add_join_patterns(channels);
        }
        program
    }

    fn add_scalar_lowering(&mut self, lowering: &RhoLowering) {
        for abi in &lowering.scalar_contract_abi {
            let input = RhoNetChannel::set_automaton_trace(
                &self.language_fingerprint,
                format!("scalar/{}", abi.rule_label),
            );
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("scalar/{}/result", abi.rule_label),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:{}", abi.rule_label),
                format!("{}:{}", self.language_fingerprint, abi.rule_label),
            );
            let rule = RhoNetRule::new(
                rule_id_scalar(&abi.rule_label),
                RhoNetRuleKind::NativeFold,
                vec![input.name.clone()],
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(abi.rule_label.clone());

            self.push_channel(input);
            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_constructor_rules(&mut self, terms: &[GrammarRule]) {
        for (index, term) in terms.iter().enumerate() {
            let label = term.label.to_string();
            let syntax = RhoNetChannel::set_automaton_trace(
                &self.language_fingerprint,
                format!("term/{index}/{label}/syntax"),
            );
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("term/{index}/{label}/value"),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:term:{index}:{label}"),
                format!(
                    "{}:{}",
                    self.language_fingerprint,
                    fingerprint_fragment("term", &grammar_rule_identity(term))
                ),
            );
            let mut inputs = vec![syntax.name.clone()];
            self.push_channel(syntax);
            self.add_constructor_child_inputs(index, &label, term, &mut inputs);

            let rule = RhoNetRule::new(
                rule_id_term(index, &label),
                RhoNetRuleKind::StructuralConstructor,
                inputs,
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(label);

            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_native_system_process_rules(&mut self, terms: &[GrammarRule], lowering: &RhoLowering) {
        let rejected = lowering
            .rejected
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        for (index, term) in terms.iter().enumerate() {
            let label = term.label.to_string();
            if !rejected.contains(label.as_str()) || !term_requires_native_system_process(term) {
                continue;
            }

            let constructed = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("term/{index}/{label}/value"),
            );
            let dispatch = RhoNetChannel::set_automaton_trace(
                &self.language_fingerprint,
                format!("native/{index}/{label}/dispatch"),
            );
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("native/{index}/{label}/result"),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:native:{index}:{label}"),
                format!(
                    "{}:{}",
                    self.language_fingerprint,
                    fingerprint_fragment("native", &grammar_rule_identity(term))
                ),
            );
            let rule = RhoNetRule::new(
                rule_id_native(index, &label),
                RhoNetRuleKind::NativeSystemProcess,
                vec![constructed.name.clone(), dispatch.name.clone()],
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(label);

            self.push_channel(constructed);
            self.push_channel(dispatch);
            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_constructor_child_inputs(
        &mut self,
        index: usize,
        label: &str,
        term: &GrammarRule,
        inputs: &mut Vec<String>,
    ) {
        if let Some(params) = term.term_context.as_ref() {
            self.add_constructor_term_param_inputs(index, label, params, inputs);
            return;
        }

        for (item_index, item) in term.items.iter().enumerate() {
            match item {
                GrammarItem::NonTerminal { ident, .. } => {
                    let channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/item/{item_index}/{ident}"),
                    );
                    inputs.push(channel.name.clone());
                    self.push_channel(channel);
                },
                GrammarItem::Binder { category } => {
                    let channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/binder/{item_index}/{category}"),
                    );
                    inputs.push(channel.name.clone());
                    self.push_channel(channel);
                },
                GrammarItem::Collection { element_type, .. } => {
                    let channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/collection/{item_index}/{element_type}"),
                    );
                    inputs.push(channel.name.clone());
                    self.push_channel(channel);
                },
                GrammarItem::Terminal(_) => {},
            }
        }
    }

    fn add_constructor_term_param_inputs(
        &mut self,
        index: usize,
        label: &str,
        params: &[TermParam],
        inputs: &mut Vec<String>,
    ) {
        let mut work: Vec<&TermParam> = params.iter().rev().collect();
        while let Some(param) = work.pop() {
            match param {
                TermParam::Simple { name, .. } => {
                    let channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/param/{name}"),
                    );
                    inputs.push(channel.name.clone());
                    self.push_channel(channel);
                },
                TermParam::Abstraction { binder, body, .. } => {
                    let binder_channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/binder-param/{binder}"),
                    );
                    let body_channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/param/{body}"),
                    );
                    inputs.push(binder_channel.name.clone());
                    inputs.push(body_channel.name.clone());
                    self.push_channel(binder_channel);
                    self.push_channel(body_channel);
                },
                TermParam::MultiAbstraction { binder, body, .. } => {
                    let binder_channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/multi-binder-param/{binder}"),
                    );
                    let body_channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!("term/{index}/{label}/param/{body}"),
                    );
                    inputs.push(binder_channel.name.clone());
                    inputs.push(body_channel.name.clone());
                    self.push_channel(binder_channel);
                    self.push_channel(body_channel);
                },
                TermParam::GuardBody { .. } => {},
                TermParam::Optional { params } => {
                    work.extend(params.iter().rev());
                },
            }
        }
    }

    fn add_equations(&mut self, equations: &[Equation]) {
        for (index, equation) in equations.iter().enumerate() {
            let name = equation.name.to_string();
            let input = self.pattern_trace_channel(&equation.left);
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("equation/{index}/{name}/structural-result"),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:equation:{index}:{name}"),
                format!(
                    "{}:{}",
                    self.language_fingerprint,
                    fingerprint_fragment("equation", &equation_identity(equation))
                ),
            );

            let mut inputs = vec![input.name.clone()];
            let semantic_guards =
                self.add_premise_inputs("equation", &name, &equation.premises, &mut inputs);
            let mut rule = RhoNetRule::new(
                rule_id_equation(index, &name),
                RhoNetRuleKind::StructuralCongruence,
                inputs,
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(name);
            for guard in semantic_guards {
                rule = rule.with_semantic_predicate_guard(guard);
            }

            self.push_channel(input);
            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_rewrites(&mut self, rewrites: &[RewriteRule]) {
        for (index, rewrite) in rewrites.iter().enumerate() {
            // ★★ (#195) A WITHHELD congruence (`| S ~/> T |-`) declares that the
            // inference its own conclusion spells out is NEVER DRAWN. It is therefore
            // not a rule of this net — not a `ContextualRewrite` (which would build the
            // very join the author refused) and not a `BaseRewrite` (which would fire
            // `POutput N S ~> POutput N S`, an identity step that saturation would
            // re-derive forever). It contributes nothing at all.
            //
            // ⚠ The `index` is still CONSUMED from the enumeration, deliberately: rule
            // ids are `rule_id_rewrite(index, name)` and the disposition inventory keys
            // on them, so compacting indices around a skipped rewrite would silently
            // RETARGET every later rule id. `#152` pinned eight such coordinates.
            if rewrite.withholds_congruence() {
                continue;
            }
            let name = rewrite.name.to_string();
            let input = self.pattern_trace_channel(&rewrite.left);
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("rewrite/{index}/{name}/rhs"),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:rewrite:{index}:{name}"),
                format!(
                    "{}:{}",
                    self.language_fingerprint,
                    fingerprint_fragment("rewrite", &rewrite_identity(rewrite))
                ),
            );
            let kind = if rewrite.is_congruence_rule() {
                RhoNetRuleKind::ContextualRewrite
            } else {
                RhoNetRuleKind::BaseRewrite
            };

            let mut inputs = vec![input.name.clone()];
            let semantic_guards =
                self.add_premise_inputs("rewrite", &name, &rewrite.premises, &mut inputs);
            let mut rule = RhoNetRule::new(
                rule_id_rewrite(index, &name),
                kind,
                inputs,
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(name);
            for guard in semantic_guards {
                rule = rule.with_semantic_predicate_guard(guard);
            }

            self.push_channel(input);
            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_join_patterns(&mut self, channels: &ChannelConfig) {
        for channel in &channels.channel_categories {
            self.push_channel(RhoNetChannel::location(
                &self.language_fingerprint,
                format!("channel/{}", channel.category),
            ));
        }

        for join in &channels.join_patterns {
            let label = join.label.to_string();
            let mut inputs = Vec::new();
            let mut signature = String::new();
            for param in &join.channel_params {
                let input = RhoNetChannel::location(
                    &self.language_fingerprint,
                    format!("join/{label}/input/{}:{}", param.param_name, param.category),
                );
                signature.push_str(&format!("{}:{};", param.param_name, param.category));
                inputs.push(input.name.clone());
                self.push_channel(input);
            }
            let output = RhoNetChannel::location(
                &self.language_fingerprint,
                format!("join/{label}/continuation"),
            );
            let rhs = RhoNetRhsTemplate::new(
                format!("rhs:join:{label}"),
                format!(
                    "{}:{}",
                    self.language_fingerprint,
                    fingerprint_fragment("join", &signature)
                ),
            );
            let rule = RhoNetRule::new(
                rule_id_join(&label),
                RhoNetRuleKind::Comm,
                inputs,
                output.name.clone(),
                rhs.id.clone(),
            )
            .with_label(label);

            self.push_channel(output);
            self.push_rhs_template(rhs);
            self.rules.push(rule);
        }
    }

    fn add_guard_config(&mut self, guard_config: &GuardConfig) {
        match guard_config.builtin_predicates.as_ref() {
            Some(predicates) => {
                for predicate in predicates {
                    self.push_semantic_predicate(RhoNetSemanticPredicate::new(
                        format!("predicate:{}", predicate.name),
                        RhoNetSemanticPredicateQuality::RejectSafeApprox,
                    ));
                }
            },
            None => {
                self.push_semantic_predicate(RhoNetSemanticPredicate::new(
                    "predicate:standard-builtins",
                    RhoNetSemanticPredicateQuality::RejectSafeApprox,
                ));
            },
        }

        for theory in &guard_config.theories {
            self.push_semantic_predicate(RhoNetSemanticPredicate::new(
                format!("theory:{}", theory.name),
                RhoNetSemanticPredicateQuality::ExactDecidable,
            ));
        }
    }

    fn add_term_guard_predicates(&mut self, def: &LanguageDef) {
        for rule in &def.terms {
            self.add_term_guard_predicates_for_rule(rule);
        }
    }

    fn add_term_guard_predicates_for_rule(&mut self, rule: &GrammarRule) {
        if let Some(params) = rule.term_context.as_ref() {
            self.add_term_guard_predicates_for_params(&rule.label.to_string(), params);
        }
    }

    fn add_term_guard_predicates_for_params(&mut self, label: &str, params: &[TermParam]) {
        let mut work: Vec<_> = params.iter().rev().collect();
        while let Some(param) = work.pop() {
            match param {
                TermParam::GuardBody { name } => {
                    self.push_semantic_predicate(RhoNetSemanticPredicate::new(
                        format!("term:{label}:guard:{name}"),
                        RhoNetSemanticPredicateQuality::RuntimeObservation,
                    ));
                },
                TermParam::Optional { params } => work.extend(params.iter().rev()),
                TermParam::Simple { .. }
                | TermParam::Abstraction { .. }
                | TermParam::MultiAbstraction { .. } => {},
            }
        }
    }

    fn add_premise_inputs(
        &mut self,
        owner_kind: &str,
        owner_name: &str,
        premises: &[Premise],
        inputs: &mut Vec<String>,
    ) -> Vec<String> {
        let mut semantic_guards = Vec::new();
        for (index, premise) in premises.iter().enumerate() {
            self.add_premise_input(
                owner_kind,
                owner_name,
                index,
                premise,
                inputs,
                &mut semantic_guards,
            );
        }
        semantic_guards
    }

    fn add_premise_input(
        &mut self,
        owner_kind: &str,
        owner_name: &str,
        index: usize,
        premise: &Premise,
        inputs: &mut Vec<String>,
        semantic_guards: &mut Vec<String>,
    ) {
        let mut premise = premise;
        loop {
            match premise {
                Premise::Freshness(_) => {
                    self.push_consistency_input(
                        format!("{owner_kind}/{owner_name}/freshness/{index}"),
                        premise,
                        inputs,
                    );
                    break;
                },
                Premise::RelationQuery { .. } => {
                    self.push_consistency_input(
                        format!("{owner_kind}/{owner_name}/relation/{index}"),
                        premise,
                        inputs,
                    );
                    break;
                },
                Premise::SyntheticInjGuard { .. } => {
                    self.push_consistency_input(
                        format!("{owner_kind}/{owner_name}/synthetic-injection/{index}"),
                        premise,
                        inputs,
                    );
                    break;
                },
                Premise::Congruence { source, target } => {
                    let channel = RhoNetChannel::location(
                        &self.language_fingerprint,
                        format!(
                        "{owner_kind}/{owner_name}/contextual-premise/{index}/{source}-to-{target}"
                    ),
                    );
                    inputs.push(channel.name.clone());
                    self.push_channel(channel);
                    break;
                },
                // ★★ (#195) A WITHHELD congruence contributes NO input channel and NO
                // channel declaration — the whole point of the declaration is that the
                // inference it spells out is never drawn, so there is nothing for a join to
                // wait on. `plan` additionally emits no `RhoNetRule` for the owning rewrite
                // at all (see `add_rewrites`), so a withholding is invisible to the in-Rho
                // net rather than a rule that fires and does nothing.
                //
                // ⚠ CONSENSUS-VISIBLE SURFACE, MEASURED NEUTRAL: this arm can only be
                // reached by a language that declares `S ~/> T`, and no production language
                // does (Ambient/Calculator/Json/Lambda/Monoid/Pi/Rholang/Turing: zero), so
                // every shipped Rho net plan is byte-identical across #195.
                Premise::CongruenceWithheld { .. } => break,
                Premise::ForAll { body, .. } => {
                    self.push_consistency_input(
                        format!("{owner_kind}/{owner_name}/forall/{index}"),
                        premise,
                        inputs,
                    );
                    premise = body;
                },
                Premise::BehavioralGuard(pred) => {
                    let id = format!("{owner_kind}:{owner_name}:guard:{index}");
                    if behavioral_predicate_has_structural_component(pred) {
                        let channel = RhoNetChannel::consistency(
                            &self.language_fingerprint,
                            format!(
                                "{owner_kind}/{owner_name}/structural-guard/{index}/{}",
                                fingerprint_fragment(
                                    "behavioral",
                                    &behavioral_predicate_identity(pred)
                                )
                            ),
                        );
                        inputs.push(channel.name.clone());
                        self.push_channel(channel);
                    } else {
                        self.push_semantic_predicate(RhoNetSemanticPredicate::new(
                            id.clone(),
                            semantic_predicate_quality(pred),
                        ));
                        semantic_guards.push(id);
                    }
                    break;
                },
            }
        }
    }

    fn push_consistency_input(
        &mut self,
        name: String,
        premise: &Premise,
        inputs: &mut Vec<String>,
    ) {
        let channel = RhoNetChannel::consistency(
            &self.language_fingerprint,
            format!(
                "{}/{}",
                name,
                fingerprint_fragment("premise", &premises_identity(std::slice::from_ref(premise)))
            ),
        );
        inputs.push(channel.name.clone());
        self.push_channel(channel);
    }

    fn pattern_trace_channel(&self, pattern: &mettail_ast::pattern::Pattern) -> RhoNetChannel {
        lhs_pattern_trace_channel(&self.language_fingerprint, pattern)
    }

    fn push_channel(&mut self, channel: RhoNetChannel) {
        if !self
            .channels
            .iter()
            .any(|existing| existing.name == channel.name)
        {
            self.channels.push(channel);
        }
    }

    fn push_semantic_predicate(&mut self, predicate: RhoNetSemanticPredicate) {
        if !self
            .semantic_predicates
            .iter()
            .any(|existing| existing.id == predicate.id)
        {
            self.semantic_predicates.push(predicate);
        }
    }

    fn push_rhs_template(&mut self, template: RhoNetRhsTemplate) {
        if !self
            .rhs_templates
            .iter()
            .any(|existing| existing.id == template.id)
        {
            self.rhs_templates.push(template);
        }
    }

    pub fn validate_rho_native_contract(&self) -> Result<(), Vec<RhoNetValidationError>> {
        let mut diagnostics = Vec::new();
        if self.language_fingerprint.trim().is_empty() {
            diagnostics.push(RhoNetValidationError::MissingLanguageFingerprint);
        }

        let channel_map = collect_unique(
            self.channels.iter().map(|channel| channel.name.as_str()),
            RhoNetValidationError::DuplicateChannel,
        );
        let predicate_map = collect_unique(
            self.semantic_predicates
                .iter()
                .map(|predicate| predicate.id.as_str()),
            RhoNetValidationError::DuplicateSemanticPredicate,
        );
        let template_map = collect_unique(
            self.rhs_templates
                .iter()
                .map(|template| template.id.as_str()),
            RhoNetValidationError::DuplicateRhsTemplate,
        );
        let rule_map = collect_unique(
            self.rules.iter().map(|rule| rule.id.as_str()),
            RhoNetValidationError::DuplicateRule,
        );

        diagnostics.extend(channel_map.diagnostics);
        diagnostics.extend(predicate_map.diagnostics);
        diagnostics.extend(template_map.diagnostics);
        diagnostics.extend(rule_map.diagnostics);

        for channel in &self.channels {
            if channel.name.trim().is_empty() {
                diagnostics.push(RhoNetValidationError::EmptyChannelName);
            }
        }
        for predicate in &self.semantic_predicates {
            if predicate.id.trim().is_empty() {
                diagnostics.push(RhoNetValidationError::EmptySemanticPredicateId);
            }
        }
        for template in &self.rhs_templates {
            if template.id.trim().is_empty() {
                diagnostics.push(RhoNetValidationError::EmptyRhsTemplateId);
            }
            if template.fingerprint.trim().is_empty() {
                diagnostics.push(RhoNetValidationError::EmptyRhsTemplateFingerprint {
                    template: template.id.clone(),
                });
            }
        }

        for rule in &self.rules {
            if rule.id.trim().is_empty() {
                diagnostics.push(RhoNetValidationError::EmptyRuleId);
            }
            if rule.input_channels.is_empty() {
                diagnostics
                    .push(RhoNetValidationError::RuleWithoutInputs { rule: rule.id.clone() });
            }
            if rule.output_channel.trim().is_empty() {
                diagnostics
                    .push(RhoNetValidationError::RuleWithoutOutput { rule: rule.id.clone() });
            }
            if rule.rhs_template.trim().is_empty() {
                diagnostics
                    .push(RhoNetValidationError::RuleWithoutRhsTemplate { rule: rule.id.clone() });
            }

            for channel in &rule.input_channels {
                if !channel_map.values.contains(channel.as_str()) {
                    diagnostics.push(RhoNetValidationError::UnknownInputChannel {
                        rule: rule.id.clone(),
                        channel: channel.clone(),
                    });
                }
            }
            if !channel_map.values.contains(rule.output_channel.as_str()) {
                diagnostics.push(RhoNetValidationError::UnknownOutputChannel {
                    rule: rule.id.clone(),
                    channel: rule.output_channel.clone(),
                });
            }
            if !template_map.values.contains(rule.rhs_template.as_str()) {
                diagnostics.push(RhoNetValidationError::UnknownRhsTemplate {
                    rule: rule.id.clone(),
                    template: rule.rhs_template.clone(),
                });
            }
            for guard in &rule.semantic_predicate_guards {
                if !predicate_map.values.contains(guard.as_str()) {
                    diagnostics.push(RhoNetValidationError::UnknownSemanticPredicateGuard {
                        rule: rule.id.clone(),
                        predicate: guard.clone(),
                    });
                }
            }
        }

        if diagnostics.is_empty() {
            Ok(())
        } else {
            Err(diagnostics)
        }
    }

    pub fn has_labeled_rule_kind(&self, label: &str, kind: RhoNetRuleKind) -> bool {
        self.rules
            .iter()
            .any(|rule| rule.kind == kind && rule.label.as_deref() == Some(label))
    }
}

/// Validation error for the Rho-native execution-plan contract.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoNetValidationError {
    MissingLanguageFingerprint,
    DuplicateChannel(String),
    DuplicateSemanticPredicate(String),
    DuplicateRhsTemplate(String),
    DuplicateRule(String),
    EmptyChannelName,
    EmptySemanticPredicateId,
    EmptyRhsTemplateId,
    EmptyRhsTemplateFingerprint { template: String },
    EmptyRuleId,
    RuleWithoutInputs { rule: String },
    RuleWithoutOutput { rule: String },
    RuleWithoutRhsTemplate { rule: String },
    UnknownInputChannel { rule: String, channel: String },
    UnknownOutputChannel { rule: String, channel: String },
    UnknownRhsTemplate { rule: String, template: String },
    UnknownSemanticPredicateGuard { rule: String, predicate: String },
}

struct UniqueIndex<'a> {
    values: BTreeSet<&'a str>,
    diagnostics: Vec<RhoNetValidationError>,
}

fn collect_unique<'a>(
    names: impl Iterator<Item = &'a str>,
    duplicate: fn(String) -> RhoNetValidationError,
) -> UniqueIndex<'a> {
    let mut counts = BTreeMap::<&'a str, usize>::new();
    for name in names {
        *counts.entry(name).or_insert(0) += 1;
    }
    let mut values = BTreeSet::new();
    let mut diagnostics = Vec::new();
    for (name, count) in counts {
        values.insert(name);
        if count > 1 {
            diagnostics.push(duplicate(name.to_string()));
        }
    }
    UniqueIndex { values, diagnostics }
}

/// The set-automaton TRACE channel of one rule-spec LHS pattern —
/// `sa:{fingerprint}/pattern/lhs:{fnv1a64(pattern_identity(lhs))}`. The SINGLE
/// derivation both the plan builder ([`RhoNetProgram::pattern_trace_channel`], which
/// delegates here) and the E-3 T-INCR per-rule bypass (`rho_net_incremental`) use, so
/// the incremental accept channel can never drift from the batch site channel.
///
/// Pattern-CONTENT-hashed and therefore DECLARATION-INDEX-independent (red-team
/// amendment EM-6): a rule append never changes an existing rule's trace channel
/// *within one language*, and the appended rule's channel is derivable per-rule without
/// re-running the lowering pipeline (EM-4b). Both properties EM-4b/EM-6 actually rest on
/// are preserved.
///
/// ★ It is NOT fingerprint-independent, and S6 removed that property deliberately: it was
/// the defect. Two languages whose LHS pattern TEXT coincides used to land two σ-receivers
/// on ONE channel, and whichever won the consume applied ITS OWN RHS to the other's σ — a
/// cross-fingerprint wrong firing. See [`scoped_channel_name`] for the invariant.
///
/// The consequence for the T-INCR bypass is real and is handled explicitly rather than
/// inherited: appending a rewrite changes the WHOLE-DEFINITION fingerprint, so the base
/// ruleset's cloned accept channels and contextual premise channels no longer match what a
/// batch compile of the extended definition would derive. `rho_net_incremental` re-scopes
/// them through [`rescope_channel_fingerprint`]; the debug cross-check against the batch
/// derivation is what proves the re-scope exact.
pub(crate) fn lhs_pattern_trace_channel(
    language_fingerprint: &str,
    pattern: &mettail_ast::pattern::Pattern,
) -> RhoNetChannel {
    RhoNetChannel::set_automaton_trace(
        language_fingerprint,
        format!("pattern/{}", fingerprint_fragment("lhs", &pattern_identity(pattern))),
    )
}

/// Re-scope an already-derived channel name from one language fingerprint to another —
/// the T-INCR (E-3) bypass's counterpart to [`scoped_channel_name`].
///
/// # Why a substring substitution is EXACT here, not a heuristic
///
/// Every INV-S6 name embeds the fingerprint VERBATIM, and derived families nest their
/// scopes (`ac:loc:{fp}/…`, `ph:loc:{fp}/…`), so there is no single fixed position to
/// splice. Substituting the fingerprint text itself handles every family — including the
/// nested ones — uniformly, and it is exactly the value a batch compile under
/// `to_fingerprint` would produce, because every derivation is a pure function of
/// `(family, fingerprint, content)` in which the fingerprint appears only as this scope.
///
/// A false positive would require the PATH portion to contain the literal text
/// `mettail-langdef-v1:{16 hex}`. Paths are built from rule labels, category names,
/// declaration indices, and FNV hex fragments; a Rust identifier admits neither `-` nor
/// `:`, so no label can spell it. The absence of a residual occurrence is nevertheless
/// CHECKED by the caller rather than assumed, and the debug cross-check against the full
/// batch derivation is the final arbiter.
pub fn rescope_channel_fingerprint(
    name: &str,
    from_fingerprint: &str,
    to_fingerprint: &str,
) -> String {
    name.replace(from_fingerprint, to_fingerprint)
}

fn fingerprint_fragment(prefix: &str, text: &str) -> String {
    format!("{prefix}:{:016x}", fnv1a64(text.as_bytes()))
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

pub(crate) fn behavioral_predicate_has_structural_component(pred: &BehavioralPred) -> bool {
    let mut work = vec![pred];
    while let Some(pred) = work.pop() {
        match pred {
            BehavioralPred::AcMatch { .. } => return true,
            BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
                work.push(body);
            },
            BehavioralPred::And(left, right)
            | BehavioralPred::Or(left, right)
            | BehavioralPred::Implies(left, right) => {
                work.push(right);
                work.push(left);
            },
            BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => {},
        }
    }
    false
}

#[cfg(test)]
#[path = "../tests/support/rho_net_recursive_oracle.rs"]
mod recursive_oracle;

fn semantic_predicate_quality(pred: &BehavioralPred) -> RhoNetSemanticPredicateQuality {
    match pred {
        BehavioralPred::Top => RhoNetSemanticPredicateQuality::ExactDecidable,
        BehavioralPred::Quantified { bound: None, .. } => {
            RhoNetSemanticPredicateQuality::RuntimeObservation
        },
        BehavioralPred::RelationQuery { .. }
        | BehavioralPred::Quantified { .. }
        | BehavioralPred::And(_, _)
        | BehavioralPred::Or(_, _)
        | BehavioralPred::Not(_)
        | BehavioralPred::Implies(_, _) => RhoNetSemanticPredicateQuality::RejectSafeApprox,
        BehavioralPred::AcMatch { .. } => RhoNetSemanticPredicateQuality::ExactDecidable,
    }
}

pub(crate) fn term_requires_native_system_process(term: &GrammarRule) -> bool {
    term.rust_code.is_some() || term.eval_mode.is_some() || rule_has_scalar_operator_shape(term)
}

fn rule_has_scalar_operator_shape(rule: &GrammarRule) -> bool {
    let Some(pattern) = &rule.syntax_pattern else {
        return false;
    };
    matches!(
        pattern.as_slice(),
        [SyntaxExpr::Param(_), SyntaxExpr::Literal(_), SyntaxExpr::Param(_)]
            | [SyntaxExpr::Literal(_), SyntaxExpr::Param(_)]
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use mettail_ast::language::{BehavioralPred, LanguageDef, PredArg, Premise, RewriteRule};
    use mettail_ast::pattern::{Pattern, PatternTerm};

    /// The INV-S6 scope these plan-level channel unit tests derive their names under.
    /// Any slash-free string serves: these tests assert plan structure (duplicate
    /// detection, dangling references), not the scope's value.
    const TEST_FP: &str = "mettail-langdef-v1:0000000000000000";

    const SCALAR_FRAGMENT: &str = r#"
        name: RhoNetScalarFrag,
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
        name: MiniRhoFor,
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

    const GUARDED_SCALAR_FRAGMENT: &str = r#"
        name: GuardedScalar,
        types {
            Proc
            Name
            ![i64] as Int
            ![bool] as Bool
        },
        guards {
            gt . x: Int, y: Int |- x ">" y ;
            theories {
                arithmetic = PresburgerAlgebra for [Int];
            }
            channels {
                channel Name;
                join PGuardedInput(ch: Name);
            }
        },
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
                |- "for" "(" x "<-" n "where" guard ")" "{" p "}" : Proc ;
        }
    "#;

    const NATIVE_PROCESS_FRAGMENT: &str = r#"
        name: NativeProcessFrag,
        types {
            ![i64] as Int
            ![mettail_runtime::CanonicalBigInt] as BigInt
        },
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            PowInt . a:Int, b:Int |- a "^" b : Int ;
            FactInt . a:Int |- a "!" : Int ![factorial(a)] step;
            AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ;
        }
    "#;

    fn ident(name: &str) -> syn::Ident {
        syn::parse_str(name).expect("test identifier must parse")
    }

    fn var_pattern(name: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(ident(name)))
    }

    #[test]
    fn valid_program_admits_only_rho_rules_with_semantic_predicate_guards() {
        let in_channel = RhoNetChannel::set_automaton_trace(TEST_FP, "root/f/0").name;
        let out_channel = RhoNetChannel::location(TEST_FP, "root").name;
        let mut program = RhoNetProgram::new("lang-fp");
        program.channels = vec![
            RhoNetChannel::set_automaton_trace(TEST_FP, "root/f/0"),
            RhoNetChannel::location(TEST_FP, "root"),
        ];
        program.semantic_predicates = vec![RhoNetSemanticPredicate::new(
            "guard:is-ground",
            RhoNetSemanticPredicateQuality::RejectSafeApprox,
        )];
        program.rhs_templates = vec![RhoNetRhsTemplate::new("rhs:add", "rhs-fp")];
        program.rules = vec![RhoNetRule::new(
            "rule:add",
            RhoNetRuleKind::NativeFold,
            vec![in_channel],
            out_channel,
            "rhs:add",
        )
        .with_label("AddInt")
        .with_semantic_predicate_guard("guard:is-ground")];

        assert_eq!(program.validate_rho_native_contract(), Ok(()));
    }

    #[test]
    fn scalar_lowering_derives_valid_rhonet_program() {
        let def =
            syn::parse_str::<LanguageDef>(SCALAR_FRAGMENT).expect("scalar fragment must parse");
        let lowering = lower_language_def(&def);
        assert_eq!(lowering.lowered, ["AddInt", "EqInt"]);
        assert!(lowering.rejected.is_empty());

        let rho_net = RhoNetProgram::from_scalar_lowering(&lowering);

        assert_eq!(rho_net.language_fingerprint, lowering.definition_fingerprint());
        assert_eq!(rho_net.rules.len(), 2);
        assert_eq!(rho_net.channels.len(), 4);
        assert_eq!(rho_net.rhs_templates.len(), 2);
        assert_eq!(rho_net.validate_rho_native_contract(), Ok(()));
        assert!(rho_net
            .rules
            .iter()
            .all(|rule| rule.kind == RhoNetRuleKind::NativeFold));
    }

    #[test]
    fn language_def_planning_derives_base_and_contextual_rewrite_rules() {
        let def = syn::parse_str::<LanguageDef>(MINIRHO_FOR_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let rho_net = RhoNetProgram::from_language_def(&def, &lowering);

        let rewrite_rules = rho_net
            .rules
            .iter()
            .filter(|rule| {
                matches!(rule.kind, RhoNetRuleKind::BaseRewrite | RhoNetRuleKind::ContextualRewrite)
            })
            .collect::<Vec<_>>();
        let constructor_rules = rho_net
            .rules
            .iter()
            .filter(|rule| rule.kind == RhoNetRuleKind::StructuralConstructor)
            .collect::<Vec<_>>();

        assert_eq!(constructor_rules.len(), 4);
        assert!(constructor_rules
            .iter()
            .any(|rule| rule.label.as_deref() == Some("PFor")
                && rule
                    .input_channels
                    .iter()
                    .any(|channel| channel.contains("/param/p"))));
        assert_eq!(rewrite_rules.len(), 2);
        assert!(rewrite_rules.iter().any(|rule| {
            rule.label.as_deref() == Some("Comm") && rule.kind == RhoNetRuleKind::BaseRewrite
        }));
        assert!(rewrite_rules.iter().any(|rule| {
            rule.label.as_deref() == Some("ParCong")
                && rule.kind == RhoNetRuleKind::ContextualRewrite
                && rule
                    .input_channels
                    .iter()
                    .any(|channel| channel.contains("contextual-premise"))
        }));
        assert_eq!(rho_net.validate_rho_native_contract(), Ok(()));
    }

    #[test]
    fn language_def_planning_derives_native_system_process_rules() {
        let def =
            syn::parse_str::<LanguageDef>(NATIVE_PROCESS_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        assert_eq!(lowering.lowered, vec!["AddInt"]);
        assert_eq!(lowering.rejected, vec!["PowInt", "FactInt", "AddBigInt"]);

        let rho_net = RhoNetProgram::from_language_def(&def, &lowering);
        let native_rules = rho_net
            .rules
            .iter()
            .filter(|rule| rule.kind == RhoNetRuleKind::NativeSystemProcess)
            .collect::<Vec<_>>();

        assert_eq!(native_rules.len(), 3);
        for label in ["PowInt", "FactInt", "AddBigInt"] {
            let rule = native_rules
                .iter()
                .find(|rule| rule.label.as_deref() == Some(label))
                .unwrap_or_else(|| panic!("{label} must have a Rho native system-process rule"));
            assert!(rule
                .input_channels
                .iter()
                .any(|channel| channel.contains("/dispatch")));
        }
        assert!(!rho_net.has_labeled_rule_kind("AddInt", RhoNetRuleKind::NativeSystemProcess));
        assert_eq!(rho_net.validate_rho_native_contract(), Ok(()));
    }

    #[test]
    fn language_def_planning_derives_declared_join_comm_rules() {
        let def =
            syn::parse_str::<LanguageDef>(GUARDED_SCALAR_FRAGMENT).expect("fragment must parse");
        let lowering = lower_language_def(&def);
        let rho_net = RhoNetProgram::from_language_def(&def, &lowering);

        let join_rule = rho_net
            .rules
            .iter()
            .find(|rule| rule.id == "rule:join:PGuardedInput")
            .expect("declared join must become a RhoNet COMM rule");

        assert_eq!(join_rule.kind, RhoNetRuleKind::Comm);
        assert_eq!(join_rule.input_channels.len(), 1);
        assert!(join_rule.input_channels[0].contains("join/PGuardedInput/input/ch:Name"));
        let predicate_quality = |id: &str| {
            rho_net
                .semantic_predicates
                .iter()
                .find(|predicate| predicate.id == id)
                .unwrap_or_else(|| panic!("missing semantic predicate {id}"))
                .quality
        };
        assert_eq!(
            predicate_quality("term:PGuardedInput:guard:guard"),
            RhoNetSemanticPredicateQuality::RuntimeObservation
        );
        assert_eq!(
            predicate_quality("predicate:gt"),
            RhoNetSemanticPredicateQuality::RejectSafeApprox
        );
        assert_eq!(
            predicate_quality("theory:arithmetic"),
            RhoNetSemanticPredicateQuality::ExactDecidable
        );
        assert_eq!(rho_net.validate_rho_native_contract(), Ok(()));
    }

    #[test]
    fn language_def_planning_splits_semantic_and_structural_behavioral_guards() {
        let mut def = syn::parse_str::<LanguageDef>(SCALAR_FRAGMENT).expect("fragment must parse");
        def.rewrites.push(RewriteRule {
            name: ident("SemanticGuarded"),
            type_context: Vec::new(),
            premises: vec![Premise::BehavioralGuard(BehavioralPred::RelationQuery {
                relation_name: ident("ok"),
                args: vec![PredArg::Var(ident("x"))],
                negated: false,
            })],
            left: var_pattern("x"),
            right: var_pattern("x"),
            is_auto_injected: false,
        });
        def.rewrites.push(RewriteRule {
            name: ident("StructuralGuarded"),
            type_context: Vec::new(),
            premises: vec![Premise::BehavioralGuard(BehavioralPred::AcMatch {
                bag: ident("xs"),
                elements: vec![ident("x")],
                rest: Some(ident("rest")),
            })],
            left: var_pattern("x"),
            right: var_pattern("x"),
            is_auto_injected: false,
        });
        let lowering = lower_language_def(&def);
        let rho_net = RhoNetProgram::from_language_def(&def, &lowering);

        let semantic_rule = rho_net
            .rules
            .iter()
            .find(|rule| rule.label.as_deref() == Some("SemanticGuarded"))
            .expect("semantic-guarded rewrite must be planned");
        let structural_rule = rho_net
            .rules
            .iter()
            .find(|rule| rule.label.as_deref() == Some("StructuralGuarded"))
            .expect("structural-guarded rewrite must be planned");

        assert_eq!(
            semantic_rule.semantic_predicate_guards,
            vec!["rewrite:SemanticGuarded:guard:0".to_string()]
        );
        assert!(rho_net
            .semantic_predicates
            .iter()
            .any(|predicate| predicate.id == "rewrite:SemanticGuarded:guard:0"));
        assert!(structural_rule.semantic_predicate_guards.is_empty());
        assert!(structural_rule
            .input_channels
            .iter()
            .any(|channel| channel.contains("structural-guard")));
        assert_eq!(rho_net.validate_rho_native_contract(), Ok(()));
    }

    #[test]
    fn validation_rejects_unknown_channels_templates_and_guards() {
        let mut program = RhoNetProgram::new("lang-fp");
        program.channels = vec![RhoNetChannel::location(TEST_FP, "root")];
        program.rhs_templates = vec![RhoNetRhsTemplate::new("rhs:ok", "rhs-fp")];
        program.rules = vec![RhoNetRule::new(
            "rule:bad",
            RhoNetRuleKind::BaseRewrite,
            vec!["sa:missing".to_string()],
            "loc:missing",
            "rhs:missing",
        )
        .with_semantic_predicate_guard("guard:missing")];

        let errors = program
            .validate_rho_native_contract()
            .expect_err("missing dependencies must reject");

        assert!(errors.contains(&RhoNetValidationError::UnknownInputChannel {
            rule: "rule:bad".to_string(),
            channel: "sa:missing".to_string(),
        }));
        assert!(errors.contains(&RhoNetValidationError::UnknownOutputChannel {
            rule: "rule:bad".to_string(),
            channel: "loc:missing".to_string(),
        }));
        assert!(errors.contains(&RhoNetValidationError::UnknownRhsTemplate {
            rule: "rule:bad".to_string(),
            template: "rhs:missing".to_string(),
        }));
        assert!(errors.contains(&RhoNetValidationError::UnknownSemanticPredicateGuard {
            rule: "rule:bad".to_string(),
            predicate: "guard:missing".to_string(),
        }));
    }

    #[test]
    fn validation_reports_duplicate_ids() {
        let mut program = RhoNetProgram::new("lang-fp");
        program.channels = vec![
            RhoNetChannel::location(TEST_FP, "root"),
            RhoNetChannel::location(TEST_FP, "root"),
        ];
        program.semantic_predicates = vec![
            RhoNetSemanticPredicate::new("guard", RhoNetSemanticPredicateQuality::ExactDecidable),
            RhoNetSemanticPredicate::new(
                "guard",
                RhoNetSemanticPredicateQuality::RuntimeObservation,
            ),
        ];
        program.rhs_templates =
            vec![RhoNetRhsTemplate::new("rhs", "fp1"), RhoNetRhsTemplate::new("rhs", "fp2")];
        program.rules = vec![
            RhoNetRule::new(
                "rule",
                RhoNetRuleKind::Comm,
                vec!["loc:root".to_string()],
                "loc:root",
                "rhs",
            ),
            RhoNetRule::new(
                "rule",
                RhoNetRuleKind::Comm,
                vec!["loc:root".to_string()],
                "loc:root",
                "rhs",
            ),
        ];

        let errors = program
            .validate_rho_native_contract()
            .expect_err("duplicates must reject");

        assert!(errors.contains(&RhoNetValidationError::DuplicateChannel(
            RhoNetChannel::location(TEST_FP, "root").name
        )));
        assert!(errors
            .contains(&RhoNetValidationError::DuplicateSemanticPredicate("guard".to_string())));
        assert!(errors.contains(&RhoNetValidationError::DuplicateRhsTemplate("rhs".to_string())));
        assert!(errors.contains(&RhoNetValidationError::DuplicateRule("rule".to_string())));
    }
}
