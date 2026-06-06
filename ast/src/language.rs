use proc_macro2::TokenStream;
use syn::{
    ext::IdentExt,
    parse::{Parse, ParseStream},
    GenericArgument, Ident, Result as SynResult, Token, Type,
};

use super::grammar::{parse_terms, GrammarRule};
use super::pattern::{Pattern, PatternTerm};
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;

/// A value in the `options { ... }` block of the `language!` macro.
#[derive(Debug, Clone)]
pub enum AttributeValue {
    /// Floating-point value (e.g., `beam_width: 1.5`).
    Float(f64),
    /// Integer value.
    Int(i64),
    /// Boolean value (e.g., `auto_hol: false`).
    Bool(bool),
    /// String value (e.g., `log_semiring_model_path: "path/to/model.json"`).
    Str(String),
    /// Keyword identifier (e.g., `beam_width: none`, `beam_width: auto`).
    Keyword(String),
}

// NOTE: HOL variant auto-generation is fully automatic — it scans the grammar
// for explicit `Lam{D}` / `Apply{D}` references and for multi-binder
// `TermParam::Abstraction` / `TermParam::MultiAbstraction` params, and only
// emits variants that are actually needed. There is no user-facing option
// for this — see `macros/src/logic/common.rs::compute_hol_domain_pairs`.

/// Top-level theory definition
/// theory! { name: Foo, params: ..., options { ... }, types { ... }, terms { ... }, equations { ... }, rewrites { ... }, logic { ... } }
#[derive(Debug, Clone)]
pub struct LanguageDef {
    pub name: Ident,
    /// Configuration options parsed from `options { ... }` block. Empty if block omitted.
    pub options: HashMap<String, AttributeValue>,
    /// Languages to fully inherit from (types + terms + equations + rewrites + logic).
    /// Parsed from `extends: [Base1, Base2]`. Uses `DuplicateStrategy::Error`.
    pub extends_names: Vec<Ident>,
    /// Languages to import grammar (types + terms) from.
    /// Parsed from `includes: [Calc, BoolLogic]`. Uses `DuplicateStrategy::Override`.
    pub include_names: Vec<Ident>,
    /// Fragments to mix in (types + terms only, from `language_fragment!`).
    /// Parsed from `mixins: [ArithOps, BoolOps]`. Uses `DuplicateStrategy::Override`.
    pub mixin_names: Vec<Ident>,
    pub types: Vec<LangType>,
    /// Refinement type definitions from `types { PosInt = { x: Int | x > 0 }; }`.
    pub refinement_types: Vec<RefinementTypeDef>,
    /// Custom token definitions from `tokens { ... }` (default mode).
    pub token_defs: Vec<TokenDef>,
    /// Named lexer modes from `tokens { mode name { ... } }`.
    pub mode_defs: Vec<ModeDef>,
    /// Cross-stream sync constraints from `tokens { sync { ... } }`.
    pub sync_constraints: Vec<SyncConstraint>,
    /// Tree structural invariants from `tokens { tree_invariants { ... } }`.
    pub tree_invariants: Vec<TreeInvariant>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
    /// Custom Ascent logic: additional relations and rules
    pub logic: Option<LogicBlock>,
    /// Guard configuration from the `guards { ... }` block (design doc §2A).
    /// `None` when the block is absent — backward compatible with existing
    /// language definitions, which retain the heuristic dispatch behavior.
    pub guard_config: Option<GuardConfig>,
}

/// Custom logic block containing relation declarations and rules
#[derive(Debug, Clone)]
pub struct LogicBlock {
    /// Custom relation declarations (parsed for code generation)
    pub relations: Vec<RelationDecl>,
    /// All content (relations + rules) as verbatim TokenStream for Ascent
    pub content: TokenStream,
}

/// A custom relation declaration
/// Syntax: relation name(Type1, Type2, ...);
#[derive(Debug, Clone)]
pub struct RelationDecl {
    /// Relation name (e.g., "path")
    pub name: Ident,
    /// Parameter type strings (e.g., ["Proc", "Proc"] or ["Vec<Proc>"])
    pub param_types: Vec<String>,
    /// Stage 3.27a (2026-05-04): doc-comment text (joined with `\n`)
    /// extracted from `#[doc = "..."]` attributes (typically lowered from
    /// `///` lines) preceding the relation. `None` when no doc comment is
    /// present. Surfaces in the generated `LogicRelationDef::description`
    /// field, displayed by the REPL `info` command.
    pub doc_comment: Option<String>,
}

/// A typed parameter in the type context
/// Example: `P:Proc` in `Rule . P:Proc | ... |- ...`
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TypedParam {
    pub name: Ident,
    pub ty: super::types::TypeExpr,
}

/// A premise in a propositional context (part of a conjunction)
/// Used in both equations and rewrites for unified judgement syntax
#[derive(Debug, Clone)]
pub enum Premise {
    /// Freshness: x # P (x is fresh in P)
    Freshness(FreshnessCondition),

    /// Congruence: S ~> T (if S rewrites to T)
    /// Only valid in rewrites, not equations
    Congruence { source: Ident, target: Ident },

    /// Relation query: rel(arg1, arg2, ...)
    /// Currently used for env_var(x, v), extensible to arbitrary relations
    RelationQuery { relation: Ident, args: Vec<Ident> },

    /// Universal quantification over a collection: xs.*map(|x| premise)
    /// Means "for all x in xs, premise holds"
    ForAll {
        collection: Ident,
        param: Ident,
        body: Box<Premise>,
    },

    /// Behavioral guard premise: `guard(pred_expr)`
    /// Embeds a full quantified behavioral predicate as a rule premise.
    /// Evaluated via `prattail::evaluate_quantified()` at runtime.
    BehavioralGuard(BehavioralPred),

    /// Phase A (2026-05-16): synthetic-injection-aware guard for
    /// auto-injected NormCast rewrite rules. Emitted exclusively by
    /// `make_cast_canonicalization_rule` in
    /// `macros/src/gen/runtime/wpda_codegen/auto_inject.rs`.
    ///
    /// Lowers at codegen to a literal pattern-rejection clause:
    /// ```ignore
    /// if !matches!(<inner_var>, <source_category>::<v1>(_)
    ///                         | <source_category>::<v2>(_) | ...)
    /// ```
    /// where the excluded variants are the labels of auto-injected
    /// `<X>To<source_category>` constructors. The guard rejects inputs
    /// where the inner field of a `Cast<source>` is already wrapped by
    /// an auto-injected injection variant — preventing unbounded
    /// re-canonicalization while preserving user-rewrite-produced
    /// casts (whose inner is NOT an auto-injection variant).
    ///
    /// Grammar-general: derives from `lossless_targets()` enumeration
    /// at codegen. Empty exclusion list = no guard emitted. Applies to
    /// any grammar declaring native-type lattices.
    SyntheticInjGuard {
        inner_var: Ident,
        source_category: Ident,
        excluded_variants: Vec<Ident>,
    },
}

/// Equation in unified judgement syntax
/// Syntax: Name . type_context | prop_context |- lhs = rhs ;
/// Example: ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Equation {
    /// Rule name (required)
    pub name: Ident,
    /// Explicit type bindings (optional)
    pub type_context: Vec<TypedParam>,
    /// Premises (freshness, relation queries - NOT congruence)
    pub premises: Vec<Premise>,
    pub left: Pattern,
    pub right: Pattern,
}

/// Freshness condition: x # Term means x is fresh in Term
#[derive(Debug, Clone)]
pub enum FreshnessTarget {
    /// Simple variable/term (e.g., `P`)
    Var(Ident),
    /// Collection rest binding (e.g., `...rest`)
    CollectionRest(Ident),
}

impl Display for FreshnessTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreshnessTarget::Var(v) => write!(f, "{}", v),
            FreshnessTarget::CollectionRest(v) => write!(f, "...{}", v),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FreshnessCondition {
    pub var: Ident,
    pub term: FreshnessTarget,
}

/// Condition types for rewrite rules
#[derive(Debug, Clone)]
pub enum Condition {
    /// Freshness condition: if x # Q then
    Freshness(FreshnessCondition),
    /// Environment query condition: if env_var(x, v) then
    EnvQuery {
        /// Relation name (e.g., "env_var")
        relation: Ident,
        /// Arguments to the relation (e.g., ["x", "v"])
        args: Vec<Ident>,
    },
    /// Universal quantification: for all x in collection, body holds
    ForAll {
        collection: Ident,
        param: Ident,
        body: Box<Condition>,
    },
    /// Behavioral guard condition: quantified predicate evaluated via LogicT.
    /// Generated from `Premise::BehavioralGuard` and evaluated at runtime
    /// by calling `prattail::evaluate_quantified()`.
    BehavioralGuard(BehavioralPred),

    /// Phase A (2026-05-16): synthetic-injection guard. Lowered from
    /// `Premise::SyntheticInjGuard` (see that variant's docs for full
    /// semantics). At codegen time, emits a literal `if !matches!(...)`
    /// clause excluding the listed variants. Grammar-general.
    SyntheticInjGuard {
        inner_var: Ident,
        source_category: Ident,
        excluded_variants: Vec<Ident>,
    },
}

// ══════════════════════════════════════════════════════════════════════════════
// Behavioral Predicates — Guard expressions for guarded Comm rules
// ══════════════════════════════════════════════════════════════════════════════

/// Quantifier type for behavioral predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Quantifier {
    /// Universal: ∀ (for all elements in domain)
    ForAll,
    /// Existential: ∃ (there exists an element in domain)
    Exists,
}

/// An argument to an atomic predicate in a behavioral guard.
#[derive(Debug, Clone)]
pub enum PredArg {
    /// A variable reference (bound by pattern matching or quantifier).
    Var(Ident),
    /// A literal constant (constructor name or value).
    Constant(Ident),
}

/// A behavioral predicate for guarded input (Comm rule guards).
///
/// Extends simple existential relation queries to full FOL with
/// universal/existential quantification:
///
/// ```text
/// for (@x : ∀y. (reachable(x,y) ⇒ safe(y)) <- ch) { P }
/// ```
///
/// Evaluated at runtime via LogicT (Strategy 3 from Gap 3):
/// - Simple `RelationQuery`: direct Ascent JOIN clause
/// - `Quantified`: closure calling `prattail::evaluate_quantified()`
/// - Boolean combinators: standard short-circuit evaluation
///
/// # References
///
/// - Gap 3 in `docs/design/predicated-types.md` §22
/// - `prattail::logict::evaluate_quantified()` for runtime evaluation
#[derive(Debug, Clone)]
pub enum BehavioralPred {
    /// Simple relation query: `R(args)` or `~R(args)`.
    /// Checks whether a tuple exists (or does not exist) in an Ascent relation.
    RelationQuery {
        relation_name: Ident,
        args: Vec<PredArg>,
        negated: bool,
    },
    /// Quantified predicate: `∀/∃ var [∈ domain] [bound]. body`
    Quantified {
        quantifier: Quantifier,
        var: Ident,
        /// Domain relation to iterate over (e.g., "nodes").
        /// If None, domain is inferred from the body's relation references.
        domain: Option<Ident>,
        /// Optional bound for semi-decidable (T3) domains.
        bound: Option<usize>,
        body: Box<BehavioralPred>,
    },
    /// Conjunction: `a /\ b`
    And(Box<BehavioralPred>, Box<BehavioralPred>),
    /// Disjunction: `a \/ b`
    Or(Box<BehavioralPred>, Box<BehavioralPred>),
    /// Negation: `~a`
    Not(Box<BehavioralPred>),
    /// Implication: `a => b`
    Implies(Box<BehavioralPred>, Box<BehavioralPred>),
    /// Associative-commutative match: `ac_match(bag, {x, y, ...rest})`
    ///
    /// Enumerates all ways to select `elements.len()` items from the multiset
    /// bound to `bag`, binding each to the corresponding element variable.
    /// If `rest` is present, the unmatched remainder is bound to it.
    AcMatch {
        /// Bag variable to match (must be bound by LHS pattern).
        bag: Ident,
        /// Element variables to bind from the bag.
        elements: Vec<Ident>,
        /// Optional rest variable for unmatched elements.
        rest: Option<Ident>,
    },
    /// Always-true identity predicate.
    ///
    /// Used by the guarded Comm rule generator at compile time when
    /// the actual predicate is per-instance runtime data (attached to
    /// the generated enum variant as a `mettail_runtime::BehavioralPred`
    /// field) rather than a language-spec-time fixed shape. The
    /// identity predicate lets the compile-time guard-set analysis continue
    /// to receive a consistent input shape without gating its emission
    /// on per-instance data that it cannot see.
    Top,
}

impl BehavioralPred {
    /// Convert this macro-level predicate to a `prattail::QuantifiedFormula`
    /// suitable for runtime evaluation.
    pub fn to_quantified_formula(&self) -> proc_macro2::TokenStream {
        use quote::quote;
        match self {
            BehavioralPred::RelationQuery { relation_name, args, negated } => {
                let rel_str = relation_name.to_string();
                let arg_exprs: Vec<_> = args
                    .iter()
                    .map(|a| match a {
                        PredArg::Var(v) => {
                            let v_str = v.to_string();
                            quote! { prattail::logict::QuantifiedArg::Var(#v_str.to_string()) }
                        },
                        PredArg::Constant(c) => {
                            let c_str = c.to_string();
                            quote! { prattail::logict::QuantifiedArg::Constant(#c_str.to_string()) }
                        },
                    })
                    .collect();
                let atom = quote! {
                    prattail::logict::QuantifiedFormula::atom(
                        #rel_str,
                        vec![#(#arg_exprs),*],
                    )
                };
                if *negated {
                    quote! { prattail::logict::QuantifiedFormula::not(#atom) }
                } else {
                    atom
                }
            },
            BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
                let var_str = var.to_string();
                let body_expr = body.to_quantified_formula();
                let domain_expr = if let Some(dom) = domain {
                    let dom_str = dom.to_string();
                    if let Some(b) = bound {
                        quote! {
                            prattail::logict::QuantifiedDomain::Bounded {
                                relation: #dom_str.to_string(),
                                limit: #b,
                            }
                        }
                    } else {
                        quote! {
                            prattail::logict::QuantifiedDomain::Relation(#dom_str.to_string())
                        }
                    }
                } else {
                    // No explicit domain — use var name as relation (convention)
                    let var_rel = var.to_string();
                    quote! {
                        prattail::logict::QuantifiedDomain::Relation(#var_rel.to_string())
                    }
                };
                match quantifier {
                    Quantifier::ForAll => quote! {
                        prattail::logict::QuantifiedFormula::forall(
                            #var_str,
                            #domain_expr,
                            #body_expr,
                        )
                    },
                    Quantifier::Exists => quote! {
                        prattail::logict::QuantifiedFormula::exists(
                            #var_str,
                            #domain_expr,
                            #body_expr,
                        )
                    },
                }
            },
            BehavioralPred::And(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::and(#a_expr, #b_expr)
                }
            },
            BehavioralPred::Or(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::or(#a_expr, #b_expr)
                }
            },
            BehavioralPred::Not(inner) => {
                let inner_expr = inner.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::not(#inner_expr)
                }
            },
            BehavioralPred::Implies(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::implies(#a_expr, #b_expr)
                }
            },
            BehavioralPred::AcMatch { .. } => {
                // AcMatch does not translate to QuantifiedFormula —
                // it generates specialized partition enumeration code
                // in the codegen layer (rules.rs). This arm should never
                // be reached; AcMatch is intercepted before this point.
                panic!("BUG: AcMatch should be handled by specialized codegen, not to_quantified_formula()")
            },
            BehavioralPred::Top => {
                // Top is the always-true identity predicate used when the guard
                // slot is declared at language-spec time but the actual
                // predicate is per-instance runtime data. The Ascent rule
                // body has no join clause for Top (the rule fires
                // unconditionally on its structural pattern).
                quote! {
                    prattail::logict::QuantifiedFormula::atom(
                        "__top__",
                        vec![],
                    )
                }
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Guard Configuration — the `guards { ... }` block (design doc §2A)
// ══════════════════════════════════════════════════════════════════════════════
//
// The `guards {}` block lets each `language!`-defined language declare its
// guard sublanguage explicitly: which logical connectives exist (and what
// keywords spell them), which built-in predicates are available, which
// constraint theories handle analysis, and which categories serve as
// communication channels for multi-channel guard dispatch.
//
// All sub-fields are optional. When omitted, the language gets the existing
// heuristic dispatch behavior (backward compatible).

/// The fixed set of logical connective roles the compiler recognizes.
///
/// Each role corresponds to a `BehavioralPred` variant. The mapping is
/// closed: a language may choose which roles it exposes (via `connectives {}`)
/// and what keywords spell them, but it cannot invent new roles.
///
/// | Role | BehavioralPred Variant |
/// |------|------------------------|
/// | `And` | `BehavioralPred::And` |
/// | `Or` | `BehavioralPred::Or` |
/// | `Not` | `BehavioralPred::Not` |
/// | `Entails` | `BehavioralPred::Implies(p, c)` |
/// | `ImpliedBy` | `BehavioralPred::Implies(c, p)` (args swapped) |
/// | `Iff` | `And(Implies(a,b), Implies(b,a))` |
/// | `Forall` | `BehavioralPred::Quantified { ForAll, ... }` |
/// | `Exists` | `BehavioralPred::Quantified { Exists, ... }` |
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConnectiveRole {
    And,
    Or,
    Not,
    Entails,
    ImpliedBy,
    Iff,
    Forall,
    Exists,
}

impl ConnectiveRole {
    /// Parse a role identifier string. Returns `None` if not a known role.
    pub fn from_ident(s: &str) -> Option<Self> {
        match s {
            "and" => Some(ConnectiveRole::And),
            "or" => Some(ConnectiveRole::Or),
            "not" => Some(ConnectiveRole::Not),
            "entails" => Some(ConnectiveRole::Entails),
            "implied_by" => Some(ConnectiveRole::ImpliedBy),
            "iff" => Some(ConnectiveRole::Iff),
            "forall" => Some(ConnectiveRole::Forall),
            "exists" => Some(ConnectiveRole::Exists),
            _ => None,
        }
    }

    /// Human-readable name of this role.
    pub fn as_str(&self) -> &'static str {
        match self {
            ConnectiveRole::And => "and",
            ConnectiveRole::Or => "or",
            ConnectiveRole::Not => "not",
            ConnectiveRole::Entails => "entails",
            ConnectiveRole::ImpliedBy => "implied_by",
            ConnectiveRole::Iff => "iff",
            ConnectiveRole::Forall => "forall",
            ConnectiveRole::Exists => "exists",
        }
    }
}

impl fmt::Display for ConnectiveRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A single connective declaration: `role = "kw1" | "kw2" ;`
///
/// Maps a fixed `ConnectiveRole` to one or more surface keywords. A language
/// like Rholang spells `and` as `"and"` or `"∧"`; MeTTa spells it as `"&&"`.
#[derive(Debug, Clone)]
pub struct ConnectiveDecl {
    pub role: ConnectiveRole,
    pub keywords: Vec<String>,
}

/// Type constraint on a predicate parameter.
///
/// Used in built-in predicate declarations like `gt . x: Int, y: Int |- ...`
/// or union-typed `comparable . xs: (Int|Str)+ |- ...`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamType {
    /// Single category: `x: Int`
    Single(Ident),
    /// Union of categories: `x: (Int|Float)` — argument may be any of these
    Union(Vec<Ident>),
}

/// Regex-style repetition quantifier on a variadic predicate parameter.
///
/// Examples:
/// - `xs+`     — `OneOrMore`
/// - `xs*`     — `ZeroOrMore`
/// - `xs{2,5}` — `Range { min: 2, max: Some(5) }`
/// - `xs{2,}`  — `Range { min: 2, max: None }`
/// - `xs{,3}`  — `Range { min: 0, max: Some(3) }`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamQuantifier {
    OneOrMore,
    ZeroOrMore,
    Range { min: usize, max: Option<usize> },
}

/// A single parameter in a built-in predicate declaration.
///
/// Examples:
/// - `x`           — name only
/// - `x: Int`      — typed
/// - `xs+`         — variadic
/// - `xs: Int+`    — typed variadic
/// - `xs: (Int|Float)+` — union-typed variadic
#[derive(Debug, Clone)]
pub struct PredicateParam {
    pub name: Ident,
    pub ty: Option<ParamType>,
    pub quantifier: Option<ParamQuantifier>,
}

/// Optional per-predicate hints that override the pipeline's heuristic
/// selectivity and cost estimates.
///
/// Both fields default to `None` (fall back to pipeline heuristics).
#[derive(Debug, Clone, Default)]
pub struct PredicateAnnotations {
    /// Selectivity ∈ [0.0, 1.0]: estimated fraction of inputs satisfying
    /// the predicate. Overrides `estimate_predicate_selectivity()`.
    pub selectivity: Option<f64>,
    /// Relative evaluation cost ∈ ℕ: lower = cheaper. Overrides
    /// `estimate_predicate_cost()` and `condition_cost()`.
    pub cost: Option<u32>,
}

/// A built-in predicate declaration: `Label . params |- syntax_forms @[anno]? ;`
///
/// Direct items of `guards {}`. The syntax template defines fixity (infix /
/// prefix / mixfix) by where parameters appear relative to keyword literals.
/// Multiple syntax forms for the same predicate are separated by `|`.
#[derive(Debug, Clone)]
pub struct BuiltinPredicate {
    pub name: Ident,
    pub params: Vec<PredicateParam>,
    /// Each inner `Vec<SyntaxExpr>` is one syntax form; multiple forms are
    /// separated by `|` in the surface syntax (e.g.,
    /// `gt . x, y |- x ">" y | "gt" "(" x "," y ")" ;`).
    pub syntax_forms: Vec<Vec<super::grammar::SyntaxExpr>>,
    /// Optional `@[selectivity(s), cost(c)]` annotations.
    pub annotations: PredicateAnnotations,
}

/// A constraint theory registration: `name = TheoryType for [Cat1, Cat2] ;`
///
/// Replaces heuristic keyword-based dispatch in `predicate_dispatch.rs`
/// with explicit, data-driven theory routing.
///
/// - `name` is a local identifier for the registration (e.g., `arithmetic`).
/// - `theory_type` is the Rust type implementing the theory's `BooleanAlgebra`
///   or `ConstraintTheory` trait (e.g., `PresburgerAlgebra`).
/// - `handled_types` lists the grammar categories the theory is responsible
///   for; `None` means "handles all categories" (omitted `for [...]` clause).
#[derive(Debug, Clone)]
pub struct TheoryRegistration {
    pub name: Ident,
    pub theory_type: syn::Type,
    pub handled_types: Option<Vec<Ident>>,
}

/// `channel <category> ;` — declares a category as a communication channel.
#[derive(Debug, Clone)]
pub struct ChannelDecl {
    pub category: Ident,
}

/// A channel-binding parameter in a join pattern: `<param>: <Category>`.
#[derive(Debug, Clone)]
pub struct ChannelParam {
    pub param_name: Ident,
    pub category: Ident,
}

/// `join <Label>(<param>: <Category>, ...) ;` — declares a constructor as a
/// join pattern that binds one or more channels.
#[derive(Debug, Clone)]
pub struct JoinPatternDecl {
    pub label: Ident,
    pub channel_params: Vec<ChannelParam>,
}

/// Channel configuration sub-block (`channels { ... }`).
///
/// Replaces heuristic M8 (Multi-Tape) and M11 (Two-Way Transducer) inference
/// with explicit channel and join pattern declarations.
#[derive(Debug, Clone)]
pub struct ChannelConfig {
    pub channel_categories: Vec<ChannelDecl>,
    pub join_patterns: Vec<JoinPatternDecl>,
}

/// Bidirectional mapping between connective roles and their surface keywords.
///
/// Built from `Vec<ConnectiveDecl>` via `from_decls()`. The constructor
/// validates lint CONN01 (no duplicate keywords across roles).
#[derive(Debug, Clone)]
pub struct ConnectiveMap {
    pub role_to_keywords: HashMap<ConnectiveRole, Vec<String>>,
    pub keyword_to_role: HashMap<String, ConnectiveRole>,
}

impl ConnectiveMap {
    /// Build a connective map from declarations, validating CONN01.
    ///
    /// Returns an error if the same keyword is mapped to multiple roles.
    pub fn from_decls(decls: &[ConnectiveDecl]) -> Result<Self, syn::Error> {
        let mut role_to_keywords: HashMap<ConnectiveRole, Vec<String>> = HashMap::new();
        let mut keyword_to_role: HashMap<String, ConnectiveRole> = HashMap::new();

        for decl in decls {
            for kw in &decl.keywords {
                if let Some(existing_role) = keyword_to_role.get(kw) {
                    if *existing_role != decl.role {
                        return Err(syn::Error::new(
                            proc_macro2::Span::call_site(),
                            format!(
                                "CONN01: keyword `{}` is mapped to multiple connective roles \
                                 ({} and {})",
                                kw, existing_role, decl.role
                            ),
                        ));
                    }
                }
                keyword_to_role.insert(kw.clone(), decl.role.clone());
                role_to_keywords
                    .entry(decl.role.clone())
                    .or_default()
                    .push(kw.clone());
            }
        }

        Ok(ConnectiveMap { role_to_keywords, keyword_to_role })
    }

    /// Whether the given role has any declared keywords.
    pub fn role_available(&self, role: &ConnectiveRole) -> bool {
        self.role_to_keywords
            .get(role)
            .map(|kws| !kws.is_empty())
            .unwrap_or(false)
    }

    /// Look up the role of a keyword string.
    pub fn role_of(&self, keyword: &str) -> Option<&ConnectiveRole> {
        self.keyword_to_role.get(keyword)
    }
}

/// Top-level guard configuration from the `guards { ... }` block.
///
/// All fields are optional. When the entire `guards {}` block is omitted,
/// `LanguageDef::guard_config` is `None` and the language gets the existing
/// heuristic dispatch behavior. When `guards {}` is present but a sub-block
/// is omitted, that sub-block defaults are applied (see design doc §2A
/// "Defaults (Block Omitted)").
#[derive(Debug, Clone, Default)]
pub struct GuardConfig {
    /// Built-in predicate definitions (direct items of `guards {}`).
    /// `None` → all standard built-ins enabled with default syntax.
    /// `Some(_)` → closed-world: only listed predicates available.
    pub builtin_predicates: Option<Vec<BuiltinPredicate>>,

    /// Connective role → keyword mappings (sub-block).
    /// `None` → all connectives with default keywords.
    /// `Some(_)` → closed-world: only listed connectives available.
    pub connectives: Option<Vec<ConnectiveDecl>>,

    /// Constraint theory registrations for predicate dispatch (sub-block).
    /// Empty → fall back to heuristic keyword dispatch.
    pub theories: Vec<TheoryRegistration>,

    /// Channel configuration for M8/M11 dispatch (sub-block).
    /// `None` → fall back to heuristic channel inference.
    pub channels: Option<ChannelConfig>,
}

/// Rewrite rule in unified judgement syntax
/// Syntax: Name . type_context | prop_context |- lhs ~> rhs ;
/// Example: ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct RewriteRule {
    /// Rule name (required)
    pub name: Ident,
    /// Explicit type bindings (optional)
    pub type_context: Vec<TypedParam>,
    /// Premises (freshness, congruence, relation queries)
    pub premises: Vec<Premise>,
    /// LHS pattern - can be Term or Collection (with metasyntax)
    pub left: Pattern,
    /// RHS pattern - the result of the rewrite (can use metasyntax)
    pub right: Pattern,
    /// Stage 3.13e (2026-05-01): provenance flag distinguishing user-written
    /// rewrites (false) from synthetic congruence rules emitted by
    /// `wpda_codegen/auto_inject.rs::make_injection_cong_rule` for
    /// auto-injected `<Source>To<Target>` cast constructors. Mirrors
    /// `GrammarRule.is_auto_injected` (Stage 3.13b). Used by future
    /// W05-rewrite-analog lints to distinguish synthetic-induced ambiguity
    /// from user-authored ambiguity. Default `false` for parsed rules;
    /// set `true` only by `make_injection_cong_rule`.
    pub is_auto_injected: bool,
}

impl RewriteRule {
    /// Extract the congruence premise (S ~> T), if any.
    /// For backward compatibility with code that expects `premise: Option<(Ident, Ident)>`.
    pub fn congruence_premise(&self) -> Option<(&Ident, &Ident)> {
        self.premises.iter().find_map(|p| {
            if let Premise::Congruence { source, target } = p {
                Some((source, target))
            } else {
                None
            }
        })
    }

    /// Check if this is a congruence rule (has a Premise::Congruence)
    pub fn is_congruence_rule(&self) -> bool {
        self.congruence_premise().is_some()
    }
}

/// Delimiter parameters for List/Bag/Map literal syntax (open, close, separator).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectionDelimiters {
    pub open: String,
    pub close: String,
    pub sep: String,
    /// Map-only separator between key and value (e.g., ":").
    /// `None` for List/Bag, `Some` for Map.
    pub key_val_sep: Option<String>,
}

/// Collection category kind (List, Bag, Map) with optional delimiters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CollectionCategory {
    List(CollectionDelimiters),
    Bag(CollectionDelimiters),
    Map(CollectionDelimiters),
}

impl CollectionCategory {
    /// Default delimiters for List: `list(`, `)`, `,`
    pub fn list_defaults() -> CollectionDelimiters {
        CollectionDelimiters {
            open: "list(".to_string(),
            close: ")".to_string(),
            sep: ",".to_string(),
            key_val_sep: None,
        }
    }
    /// Default delimiters for Bag: `bag(`, `)`, `,`
    pub fn bag_defaults() -> CollectionDelimiters {
        CollectionDelimiters {
            open: "bag(".to_string(),
            close: ")".to_string(),
            sep: ",".to_string(),
            key_val_sep: None,
        }
    }
    /// Default delimiters for Map: `map(`, `)`, `,`, `:`
    pub fn map_defaults() -> CollectionDelimiters {
        CollectionDelimiters {
            open: "map(".to_string(),
            close: ")".to_string(),
            sep: ",".to_string(),
            key_val_sep: Some(":".to_string()),
        }
    }
}

/// Export: category name, optionally with native Rust type or collection kind
/// types { Elem; Name; ![i32] as Int; List; Bag ["{", "}", ","]; }
#[derive(Debug, Clone)]
pub struct LangType {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
    /// Optional collection category (List, Bag, Map) with delimiters for literal syntax.
    pub collection_kind: Option<CollectionCategory>,
}

/// Typed classification of a category's native Rust type.
///
/// Drives the "shared token-family variant" mapping used when desugaring
/// `literals { ... }` entries: every category whose `NativeKind` returns the
/// same `standard_token_variant()` shares one `Token::<name>(payload)` enum
/// variant.
///
/// String comparisons are confined to the single `from_syn_type` constructor;
/// all downstream dispatch is by typed `match`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeKind {
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Isize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Usize,
    Float32,
    Float64,
    Bool,
    /// `str` or `String`.
    Str,
    /// Any wrapper whose last path segment ends with `"BigInt"` — treated
    /// as the arbitrary-precision integer category.
    CanonicalBigInt,
    /// `CanonicalBigRat` — arbitrary-precision rational.
    CanonicalBigRat,
    /// `CanonicalFixedPoint` — fixed-point decimal.
    CanonicalFixedPoint,
    /// Anything else (custom user wrapper, collection container, etc.).
    Other,
}

impl NativeKind {
    /// Classify a `syn::Type` by its last path segment. Returns `Other` for
    /// anything that doesn't fit a known family.
    pub fn from_syn_type(ty: &Type) -> Self {
        let seg = match ty {
            Type::Path(p) => match p.path.segments.last() {
                Some(s) => s.ident.to_string(),
                None => return Self::Other,
            },
            _ => return Self::Other,
        };
        match seg.as_str() {
            "i8" => Self::Int8,
            "i16" => Self::Int16,
            "i32" => Self::Int32,
            "i64" => Self::Int64,
            "i128" => Self::Int128,
            "isize" => Self::Isize,
            "u8" => Self::UInt8,
            "u16" => Self::UInt16,
            "u32" => Self::UInt32,
            "u64" => Self::UInt64,
            "u128" => Self::UInt128,
            "usize" => Self::Usize,
            "f32" => Self::Float32,
            "f64" => Self::Float64,
            "bool" => Self::Bool,
            "str" | "String" => Self::Str,
            "CanonicalBigRat" => Self::CanonicalBigRat,
            "CanonicalFixedPoint" => Self::CanonicalFixedPoint,
            other if other.ends_with("BigInt") => Self::CanonicalBigInt,
            _ => Self::Other,
        }
    }

    /// Whether this kind is one of the bounded-integer widths or
    /// `CanonicalBigInt` — i.e. shares `Token::Integer(IntLit)`.
    #[inline]
    pub const fn is_integer(self) -> bool {
        matches!(
            self,
            Self::Int8
                | Self::Int16
                | Self::Int32
                | Self::Int64
                | Self::Int128
                | Self::Isize
                | Self::UInt8
                | Self::UInt16
                | Self::UInt32
                | Self::UInt64
                | Self::UInt128
                | Self::Usize
                | Self::CanonicalBigInt
        )
    }

    /// Standard `Token::<name>` variant family for this native kind.
    ///
    /// Returns `None` for `Other` — caller keeps the user-facing
    /// category name in that case. Callers in `macros` should convert
    /// the result to `TokenFamily` via `TokenFamily::from_name()` for
    /// all subsequent dispatch (single string→enum gateway).
    pub const fn standard_token_variant(self) -> Option<&'static str> {
        match self {
            Self::Float32 | Self::Float64 => Some("Float"),
            Self::Bool => Some("Boolean"),
            Self::Str => Some("StringLit"),
            // CanonicalBigInt / CanonicalBigRat / CanonicalFixedPoint do NOT
            // collapse into a shared family variant — a shared `Token::Integer(i64)`
            // would clamp arbitrary-precision literals like
            // `32478132567813256718n` to i64::MAX. Returning None keeps the
            // declared category name (e.g. `BigInt`, `BigRat`, `Fixed`) as the
            // Token variant with a `&'a str` payload; the category's parse
            // arm then calls `parse_int_lit` / `parse_rational_lit` /
            // `parse_fixed_lit` on the full text — preserving precision.
            Self::CanonicalBigInt => None,
            Self::CanonicalBigRat => None,
            Self::CanonicalFixedPoint => None,
            // Fixed-width integer types collapse onto the shared
            // `Token::Integer(i64)` variant.
            Self::Int8
            | Self::Int16
            | Self::Int32
            | Self::Int64
            | Self::Int128
            | Self::Isize
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::UInt64
            | Self::UInt128
            | Self::Usize => Some("Integer"),
            Self::Other => None,
        }
    }

    // ─────────────────────────────────────────────────────────────────
    // Stage 3.13 — BuiltinTypeLattice (2026-04-30)
    //
    // Lossless / lossy promotion edges between built-in types. Used by:
    // - Stage 3.13 auto-injection codegen — emits cross-cat injection
    //   rules byte-identical to hand-written `IntToBigInt . i:Int |- i : BigInt`.
    // - Stage 3.27f G-INTEGER-OVERFLOW-FORK — emits promotion-Fork
    //   branches for every lossless edge declared in a grammar.
    //
    // Future-proof contract: adding a new built-in type (e.g. Decimal128)
    // only requires (a) a new variant here, (b) updates to `from_syn_type`
    // and `standard_token_variant`, (c) new rows in `lossless_targets` /
    // `lossy_targets`. No code change in binder.rs/prefix.rs/auto_inject.rs
    // is needed — the codegen consumes the lattice abstractly.
    // ─────────────────────────────────────────────────────────────────

    /// Return the lossless promotion targets for this kind.
    ///
    /// A lossless edge `Source → Target` means every `Source`-valued
    /// literal can be embedded in `Target` without loss (no truncation,
    /// no precision loss, no representable-range overflow).
    ///
    /// **Auto-emittable:** Stage 3.13 unconditionally emits cross-cat
    /// injection rules for every lossless edge declared in a grammar
    /// (i.e., when both source and target categories are present).
    ///
    /// **Lossless edges:**
    /// - `Bool → Int{8..128}`, `Bool → UInt{8..128}` (false→0, true→1).
    /// - `IntN → IntM` for N ≤ M (signed widening).
    /// - `UIntN → UIntM` for N ≤ M (unsigned widening).
    /// - `UIntN → IntM` for N < M (sign bit available).
    /// - `IntN/UIntN → CanonicalBigInt` (arbitrary precision).
    /// - `CanonicalBigInt → CanonicalBigRat` (Z ⊂ Q).
    /// - `Float32 → Float64` (IEEE 754 widen).
    /// - `Float64 → CanonicalBigRat` (exact via `f64_to_exact_rational`).
    /// - `CanonicalFixedPoint → CanonicalBigRat` (rational with bounded denom).
    ///
    /// Multi-step lossless chains (e.g., `Int32 → CanonicalBigInt →
    /// CanonicalBigRat`) are NOT enumerated explicitly — Stage 3.27f's
    /// promotion-target search is BFS over the direct-edge graph this
    /// function defines.
    pub const fn lossless_targets(self) -> &'static [NativeKind] {
        match self {
            // Bool → all integer widths (false=0, true=1 fits everywhere).
            Self::Bool => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],

            // Signed integer widening: IntN → IntM for N ≤ M, plus to CanonicalBigInt + CanonicalBigRat.
            Self::Int8 => &[
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::Int16 => &[
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::Int32 => {
                &[Self::Int64, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },
            Self::Int64 => &[Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat],
            Self::Int128 => &[Self::CanonicalBigInt, Self::CanonicalBigRat],
            // isize is 32-or-64-bit platform-dependent; treat as Int64-equivalent for lattice purposes.
            Self::Isize => &[Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat],

            // Unsigned integer widening: UIntN → UIntM (N ≤ M); UIntN → IntM (N < M, sign bit available).
            Self::UInt8 => &[
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt16 => &[
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt32 => &[
                Self::UInt64,
                Self::UInt128,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt64 => {
                &[Self::UInt128, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },
            Self::UInt128 => &[Self::CanonicalBigInt, Self::CanonicalBigRat],
            Self::Usize => {
                &[Self::UInt128, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },

            // Float widening + exact-to-BigRat.
            Self::Float32 => &[Self::Float64, Self::CanonicalBigRat],
            Self::Float64 => &[Self::CanonicalBigRat],

            // Canonical → CanonicalBigRat (Z ⊂ Q; FixedPoint ⊂ Q).
            Self::CanonicalBigInt => &[Self::CanonicalBigRat],
            Self::CanonicalFixedPoint => &[Self::CanonicalBigRat],

            // Terminal / non-numeric kinds: no lossless targets.
            Self::CanonicalBigRat | Self::Str | Self::Other => &[],
        }
    }

    /// Return the lossy promotion targets for this kind.
    ///
    /// A lossy edge `Source → Target` means SOME `Source` values cannot
    /// be embedded in `Target` without loss — overflow, truncation, or
    /// representable-range mismatch can occur.
    ///
    /// **Opt-in only:** Stage 3.13 auto-injection emits these only when
    /// the user grammar opts in via
    /// `options { auto_inject_lossy: true }` or per-edge
    /// `auto_inject_allow: [...]`.
    ///
    /// **Lossy edges:**
    /// - `IntN → UIntM` (negatives unrepresentable).
    /// - `Float* → IntN` / `Float* → UIntN` (truncation).
    /// - `IntN/UIntN → Float*` (precision loss for wide ints).
    /// - `CanonicalBigRat → CanonicalFixedPoint` (truncation at scale).
    /// - `CanonicalBigRat → IntN/UIntN/Float*` (truncation + range).
    /// - `Bool → Float*` (semantic, not numeric — false→0.0, true→1.0).
    /// - Any → Str / Str → any (format/parse asymmetry).
    pub const fn lossy_targets(self) -> &'static [NativeKind] {
        match self {
            Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64 | Self::Int128 | Self::Isize => &[
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
            ],
            Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::UInt64
            | Self::UInt128
            | Self::Usize => &[Self::Float32, Self::Float64],
            Self::Float32 | Self::Float64 => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::CanonicalFixedPoint,
            ],
            Self::Bool => &[Self::Float32, Self::Float64],
            Self::CanonicalBigInt => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
            ],
            Self::CanonicalBigRat => &[
                Self::CanonicalBigInt,
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
                Self::CanonicalFixedPoint,
            ],
            Self::CanonicalFixedPoint => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
                Self::CanonicalBigInt,
            ],
            Self::Str | Self::Other => &[],
        }
    }

    /// BFS over the lossless-edge graph from `self`, yielding
    /// `(reachable_kind, distance)` pairs in shortest-path order.
    ///
    /// **Used by:** Stage 3.27f G-INTEGER-OVERFLOW-FORK to enumerate all
    /// admissible promotion targets for a built-in literal (cost weighted
    /// by distance).
    pub fn lossless_promotion_chain(self) -> Vec<(NativeKind, u8)> {
        use std::collections::VecDeque;
        let mut seen: Vec<NativeKind> = vec![self];
        let mut out: Vec<(NativeKind, u8)> = Vec::new();
        let mut queue: VecDeque<(NativeKind, u8)> = VecDeque::new();
        queue.push_back((self, 0));
        while let Some((kind, distance)) = queue.pop_front() {
            for &target in kind.lossless_targets() {
                if seen.contains(&target) {
                    continue;
                }
                seen.push(target);
                let next_dist = distance.saturating_add(1);
                out.push((target, next_dist));
                queue.push_back((target, next_dist));
            }
        }
        out
    }
}

/// Extract the element type Ident from a collection native type (e.g. `Vec<Proc>` → `Proc`,
/// `HashBag<Proc>` → `Proc`). Returns None if the native type is not a generic container.
fn element_ident_from_native_type(native_type: &Type) -> Option<Ident> {
    let path = match native_type {
        Type::Path(t) => &t.path,
        _ => return None,
    };
    let segment = path.segments.last()?;
    let args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(a) => &a.args,
        _ => return None,
    };
    let first = args.first()?;
    match first {
        GenericArgument::Type(Type::Path(t)) => t
            .path
            .get_ident()
            .cloned()
            .or_else(|| t.path.segments.last().map(|s| s.ident.clone())),
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Refinement Types — `{ x: BaseType | predicate }` in the types block
// ══════════════════════════════════════════════════════════════════════════════

/// Comparison relation for linear arithmetic predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinearRelation {
    /// `<=`
    Le,
    /// `<`
    Lt,
    /// `>=`
    Ge,
    /// `>`
    Gt,
    /// `==`
    Eq,
    /// `!=`
    Neq,
}

impl std::fmt::Display for LinearRelation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearRelation::Le => write!(f, "<="),
            LinearRelation::Lt => write!(f, "<"),
            LinearRelation::Ge => write!(f, ">="),
            LinearRelation::Gt => write!(f, ">"),
            LinearRelation::Eq => write!(f, "=="),
            LinearRelation::Neq => write!(f, "!="),
        }
    }
}

/// A refinement predicate constraining values of a refinement type.
///
/// Used in refinement type definitions:
/// ```text
/// PosInt = { x: Int | x > 0 };
/// SafeProc = { p: Proc | forall y in nodes. (reachable(p, y) => safe(y)) };
/// ```
///
/// Supports the same operator precedence as `BehavioralPred`:
/// implies < or < and < not < atom.
#[derive(Debug, Clone)]
pub enum RefinementPredicate {
    /// Linear arithmetic: `a₁*x₁ + a₂*x₂ + ... ⊕ c`
    ///
    /// Example: `x > 0`, `3*x + 2*y <= 7`
    Linear {
        /// Coefficient-variable pairs. If the variable is the bound variable,
        /// its `Ident` matches the refinement type's `var`.
        terms: Vec<(Ident, i64)>,
        /// Comparison relation.
        relation: LinearRelation,
        /// Right-hand side constant.
        rhs: i64,
    },
    /// Relation query: `R(args)` or `~R(args)`.
    ///
    /// Delegates to the same Ascent relations as `BehavioralPred::RelationQuery`.
    Relation {
        name: Ident,
        args: Vec<PredArg>,
        negated: bool,
    },
    /// Quantified predicate: `forall`/`exists` var [in domain] [_{k=N}]. body
    Quantified {
        quantifier: Quantifier,
        var: Ident,
        domain: Option<Ident>,
        bound: Option<usize>,
        body: Box<RefinementPredicate>,
    },
    /// Conjunction: `a && b`
    And(Box<RefinementPredicate>, Box<RefinementPredicate>),
    /// Disjunction: `a || b`
    Or(Box<RefinementPredicate>, Box<RefinementPredicate>),
    /// Negation: `!a` or `~a`
    Not(Box<RefinementPredicate>),
    /// Implication: `a => b`
    Implies(Box<RefinementPredicate>, Box<RefinementPredicate>),
    /// Equality: `a == b`
    TermEq(PredArg, PredArg),
    /// Inequality: `a != b`
    TermNeq(PredArg, PredArg),
}

impl std::fmt::Display for RefinementPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RefinementPredicate::Linear { terms, relation, rhs } => {
                for (i, (var, coeff)) in terms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " + ")?;
                    }
                    if *coeff == 1 {
                        write!(f, "{}", var)?;
                    } else {
                        write!(f, "{}*{}", coeff, var)?;
                    }
                }
                write!(f, " {} {}", relation, rhs)
            },
            RefinementPredicate::Relation { name, args, negated } => {
                if *negated {
                    write!(f, "~")?;
                }
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    match arg {
                        PredArg::Var(v) => write!(f, "{}", v)?,
                        PredArg::Constant(c) => write!(f, "{}", c)?,
                    }
                }
                write!(f, ")")
            },
            RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
                match quantifier {
                    Quantifier::ForAll => write!(f, "forall")?,
                    Quantifier::Exists => write!(f, "exists")?,
                }
                if let Some(k) = bound {
                    write!(f, "_{{k={}}}", k)?;
                }
                write!(f, " {}", var)?;
                if let Some(d) = domain {
                    write!(f, " in {}", d)?;
                }
                write!(f, ". ({})", body)
            },
            RefinementPredicate::And(a, b) => write!(f, "({} && {})", a, b),
            RefinementPredicate::Or(a, b) => write!(f, "({} || {})", a, b),
            RefinementPredicate::Not(a) => write!(f, "~{}", a),
            RefinementPredicate::Implies(a, b) => write!(f, "({} => {})", a, b),
            RefinementPredicate::TermEq(a, b) => {
                let a_str = match a {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                };
                let b_str = match b {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                };
                write!(f, "{} == {}", a_str, b_str)
            },
            RefinementPredicate::TermNeq(a, b) => {
                let a_str = match a {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                };
                let b_str = match b {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                };
                write!(f, "{} != {}", a_str, b_str)
            },
        }
    }
}

/// Which constraint-solving domain a [`RefinementPredicate`] (or sub-tree)
/// belongs to.
///
/// The pipeline uses this to select the appropriate solver back-end:
///
/// | Domain        | Solver                                     |
/// |---------------|--------------------------------------------|
/// | `Presburger`  | Presburger arithmetic (linear constraints)  |
/// | `Lattice`     | Subtype lattice checks                      |
/// | `Behavioral`  | Relation queries / quantified formulas      |
/// | `Unification` | Structural term unification                 |
/// | `Product`     | ProductAlgebra composition of child domains |
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintDomain {
    /// Pure linear arithmetic (e.g., `x > 0`, `3*x + 2*y <= 7`).
    Presburger,
    /// Pure subtype lattice checks.
    Lattice,
    /// Relation queries or quantified formulas delegated to Ascent.
    Behavioral,
    /// Structural term patterns (equality / inequality on terms).
    Unification,
    /// Mixed: the predicate spans multiple domains. The children record
    /// which domains were encountered.
    Product(Vec<ConstraintDomain>),
}

impl std::fmt::Display for ConstraintDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintDomain::Presburger => write!(f, "Presburger"),
            ConstraintDomain::Lattice => write!(f, "Lattice"),
            ConstraintDomain::Behavioral => write!(f, "Behavioral"),
            ConstraintDomain::Unification => write!(f, "Unification"),
            ConstraintDomain::Product(children) => {
                write!(f, "Product(")?;
                for (i, c) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", c)?;
                }
                write!(f, ")")
            },
        }
    }
}

impl RefinementPredicate {
    /// Classify which [`ConstraintDomain`] this predicate (tree) belongs to.
    ///
    /// Leaf nodes map directly:
    /// - `Linear { .. }` -> `Presburger`
    /// - `Relation { .. }` / `Quantified { .. }` -> `Behavioral`
    /// - `TermEq` / `TermNeq` -> `Unification`
    ///
    /// Compound nodes (`And`, `Or`, `Implies`) merge children:
    /// - If both children have the same domain, return that domain.
    /// - If they differ, return `Product` containing both (flattened).
    ///
    /// `Not(inner)` delegates to its child.
    pub fn classify(&self) -> ConstraintDomain {
        match self {
            RefinementPredicate::Linear { .. } => ConstraintDomain::Presburger,
            RefinementPredicate::Relation { .. } => ConstraintDomain::Behavioral,
            RefinementPredicate::Quantified { .. } => ConstraintDomain::Behavioral,
            RefinementPredicate::TermEq(_, _) => ConstraintDomain::Unification,
            RefinementPredicate::TermNeq(_, _) => ConstraintDomain::Unification,
            RefinementPredicate::Not(inner) => inner.classify(),
            RefinementPredicate::And(a, b)
            | RefinementPredicate::Or(a, b)
            | RefinementPredicate::Implies(a, b) => Self::merge_domains(a.classify(), b.classify()),
        }
    }

    /// Return the pipeline-facing predicate kind string corresponding to
    /// this predicate's [`ConstraintDomain`].
    ///
    /// The returned string matches [`prattail::type_system::RefinementPredKind`]
    /// variant names:
    ///
    /// | Domain          | String         |
    /// |-----------------|----------------|
    /// | `Presburger`    | `"Presburger"` |
    /// | `Lattice`       | `"Lattice"`    |
    /// | `Behavioral`    | `"Behavioral"` |
    /// | `Unification`   | `"Structural"` |
    /// | `Product(_)`    | `"Mixed"`      |
    pub fn to_pred_kind_str(&self) -> &'static str {
        match self.classify() {
            ConstraintDomain::Presburger => "Presburger",
            ConstraintDomain::Lattice => "Lattice",
            ConstraintDomain::Behavioral => "Behavioral",
            ConstraintDomain::Unification => "Structural",
            ConstraintDomain::Product(_) => "Mixed",
        }
    }

    /// Merge two [`ConstraintDomain`] values, producing `Product` when they
    /// differ. Existing `Product` children are flattened.
    fn merge_domains(a: ConstraintDomain, b: ConstraintDomain) -> ConstraintDomain {
        if a == b {
            return a;
        }
        let mut children = Vec::new();
        Self::flatten_into(&a, &mut children);
        Self::flatten_into(&b, &mut children);
        // Deduplicate while preserving order.
        let mut seen = Vec::new();
        children.retain(|d| {
            if seen.contains(d) {
                false
            } else {
                seen.push(d.clone());
                true
            }
        });
        if children.len() == 1 {
            children.into_iter().next().expect("non-empty after dedup")
        } else {
            ConstraintDomain::Product(children)
        }
    }

    /// Flatten a `Product` into individual non-Product domains.
    fn flatten_into(domain: &ConstraintDomain, out: &mut Vec<ConstraintDomain>) {
        match domain {
            ConstraintDomain::Product(children) => {
                for c in children {
                    Self::flatten_into(c, out);
                }
            },
            other => out.push(other.clone()),
        }
    }
}

/// A refinement type definition in the `types { ... }` block.
///
/// Syntax: `PosInt = { x: Int | x > 0 };`
///
/// The `name` is the refinement type's name, `var` is the binding variable,
/// `base_type` is the underlying type, and `predicate` is the refinement
/// constraint.
#[derive(Debug, Clone)]
pub struct RefinementTypeDef {
    /// The refinement type name (e.g., `PosInt`).
    pub name: Ident,
    /// The binding variable name (e.g., `x`).
    pub var: Ident,
    /// The base type (e.g., `Int`).
    pub base_type: super::types::TypeExpr,
    /// The refinement predicate (e.g., `x > 0`).
    pub predicate: RefinementPredicate,
}

/// A token definition from the `tokens { ... }` block.
///
/// Specifies a custom or overridden lexer token kind with regex pattern,
/// optional category mapping, optional Rust constructor code, and
/// optional lexer mode transitions / stream routing.
#[derive(Debug, Clone)]
pub struct TokenDef {
    /// Token name (e.g., "Integer", "HexLiteral").
    pub name: Ident,
    /// Regex pattern for matching this token.
    pub pattern: String,
    /// Optional target category name (e.g., "Int").
    /// Determines payload type via the category's native type.
    pub category: Option<Ident>,
    /// Optional Rust code for constructing the payload from `text: &str`.
    pub rust_code: Option<TokenStream>,
    /// Optional explicit disambiguation priority (0–255).
    pub priority: Option<u8>,
    /// Push into a named mode after matching.
    pub push_mode: Option<Ident>,
    /// Pop the current mode after matching (return to caller).
    pub is_pop: bool,
    /// Output stream name (default: "main").
    pub stream: Option<Ident>,
    /// True if this TokenDef was produced by desugaring a `literals {}` block
    /// entry (main's surface syntax). False for entries declared directly in a
    /// `tokens {}` block. Literal-block tokens carry the raw lexed `&'a str`
    /// as payload and evaluate `rust_code` at parse time; `tokens{}` entries
    /// carry the category's native payload type directly.
    pub from_literals: bool,
}

/// A named lexer mode containing token definitions.
///
/// Each mode has its own DFA; at runtime the active DFA is determined
/// by the top of the mode stack.
#[derive(Debug, Clone)]
pub struct ModeDef {
    /// Mode name (e.g., "string_body", "comment_body").
    pub name: Ident,
    /// Token definitions within this mode.
    pub token_defs: Vec<TokenDef>,
}

/// A cross-stream synchronization constraint from `sync { ... }`.
#[derive(Debug, Clone)]
pub enum SyncConstraint {
    /// Align token positions in `stream_a` with `stream_b` at a regex boundary.
    Align {
        stream_a: Ident,
        stream_b: Ident,
        boundary_pattern: String,
    },
    /// Track `auxiliary` stream positions relative to `primary` stream.
    Track { auxiliary: Ident, primary: Ident },
}

/// A tree structural invariant from the `tree_invariants { ... }` block.
///
/// Compiled to mu-calculus formulas for PATA verification.
#[derive(Debug, Clone)]
pub struct TreeInvariant {
    /// Invariant name (e.g., "no_nested_braces").
    pub name: Ident,
    /// Constraint expression in the tree DSL.
    pub constraint: TreeConstraintExpr,
}

/// Tree constraint expression DSL.
///
/// Supports both keyword (`forall`, `exists`, `not`, `and`, `or`, `match`)
/// and Unicode operator (`∀`, `∃`, `¬`, `∧`, `∨`, `∈`, `↓`) forms.
#[derive(Debug, Clone)]
pub enum TreeConstraintExpr {
    /// `forall children of Symbol { body }` / `∀ ↓ Symbol { body }`
    ForallChildren {
        symbol: String,
        body: Box<TreeConstraintExpr>,
    },
    /// `exists child` / `∃ child`
    ExistsChild,
    /// `not expr` / `¬ expr`
    Not(Box<TreeConstraintExpr>),
    /// `match { A | B | C }` / `∈ { A | B | C }`
    Match(Vec<String>),
    /// Atomic symbol check (leaf).
    Atom(String),
    /// `expr and expr` / `expr ∧ expr`
    And(Box<TreeConstraintExpr>, Box<TreeConstraintExpr>),
    /// `expr or expr` / `expr ∨ expr`
    Or(Box<TreeConstraintExpr>, Box<TreeConstraintExpr>),
}

use super::grammar::GrammarItem;

impl LanguageDef {
    /// Get a grammar rule by constructor name
    pub fn get_constructor(&self, name: &Ident) -> Option<&GrammarRule> {
        self.terms.iter().find(|r| &r.label == name)
    }

    /// Get the category that a constructor produces
    pub fn category_of_constructor(&self, constructor: &Ident) -> Option<&Ident> {
        self.get_constructor(constructor).map(|r| &r.category)
    }

    /// Get the element type of a collection constructor
    pub fn collection_element_type(&self, name: &Ident) -> Option<&Ident> {
        self.get_constructor(name).and_then(|r| {
            r.items.iter().find_map(|i| {
                if let GrammarItem::Collection { element_type, .. } = i {
                    Some(element_type)
                } else {
                    None
                }
            })
        })
    }

    /// Get the type definition for a category
    pub fn get_type(&self, category: &Ident) -> Option<&LangType> {
        self.types.iter().find(|t| &t.name == category)
    }

    /// Element type for a collection category (e.g. `List` → `Proc`). First tries the type-based
    /// path (native_type + collection_kind) for List/Bag/Map; otherwise looks for a constructor
    /// whose grammar contains a Collection item.
    pub fn collection_element_type_for_category(&self, category: &Ident) -> Option<Ident> {
        let cat_str = category.to_string();
        if cat_str == "List" || cat_str == "Bag" || cat_str == "Map" {
            if let Some(lang_type) = self.types.iter().find(|t| &t.name == category) {
                if lang_type.collection_kind.is_some() {
                    // Map is implicitly HashMap<Proc, Proc> for Phase 1, so element type is always Proc.
                    if cat_str == "Map" {
                        return Some(quote::format_ident!("Proc"));
                    }
                    if let Some(native_type) = lang_type.native_type.as_ref() {
                        if let Some(elem) = element_ident_from_native_type(native_type) {
                            return Some(elem);
                        }
                    }
                    // Fallback: native_type parse failed; assume element type Proc.
                    return Some(quote::format_ident!("Proc"));
                }
            }
        }
        // Term-based: constructor whose category matches and whose grammar has a Collection item.
        self.terms
            .iter()
            .find(|r| &r.category == category)
            .and_then(|r| {
                r.items.iter().find_map(|i| {
                    if let GrammarItem::Collection { element_type, .. } = i {
                        Some(element_type.clone())
                    } else {
                        None
                    }
                })
            })
    }

    /// Type name for the List category (e.g. "List") if present.
    pub fn list_type_name(&self) -> Option<&Ident> {
        self.types
            .iter()
            .find(|t| matches!(t.collection_kind.as_ref(), Some(CollectionCategory::List(_))))
            .map(|t| &t.name)
    }

    /// Type name for the Bag category (e.g. "Bag") if present.
    pub fn bag_type_name(&self) -> Option<&Ident> {
        self.types
            .iter()
            .find(|t| matches!(t.collection_kind.as_ref(), Some(CollectionCategory::Bag(_))))
            .map(|t| &t.name)
    }

    /// Type name for the Map category (e.g. "Map") if present.
    #[allow(dead_code)]
    pub fn map_type_name(&self) -> Option<&Ident> {
        self.types
            .iter()
            .find(|t| matches!(t.collection_kind.as_ref(), Some(CollectionCategory::Map(_))))
            .map(|t| &t.name)
    }

    /// Standard `Token::<name>` variant for a literal-category, derived from the
    /// category's native type. Used when desugaring `literals { ... }` entries
    /// into `TokenDef`s so they share a single Token-enum variant per family
    /// (e.g. all integer-typed categories share `Token::Integer(IntLit)`).
    ///
    /// Returns `None` for categories whose native type doesn't fit a known
    /// family — those keep their user-facing `TypeName` as the Token variant.
    pub fn standard_token_variant_for_category(&self, category: &Ident) -> Option<&'static str> {
        let lt = self.types.iter().find(|t| t.name == *category)?;
        NativeKind::from_syn_type(lt.native_type.as_ref()?).standard_token_variant()
    }

    /// Label of the term that injects a collection type (List, Bag, Map) into the primary category.
    /// E.g. for RhoCalc with `CastList . l:List |- l : Proc`, returns `CastList` for "List".
    pub fn injection_term_label_for_collection(&self, collection_type: &str) -> Option<Ident> {
        use super::grammar::TermParam;
        use super::types::TypeExpr;
        let primary = self.types.first().map(|t| &t.name)?;
        for rule in &self.terms {
            if &rule.category != primary {
                continue;
            }
            let ctx = rule.term_context.as_ref()?;
            if ctx.len() != 1 {
                continue;
            }
            let param = &ctx[0];
            let TermParam::Simple { ty, .. } = param else {
                continue;
            };
            let TypeExpr::Base(cat) = ty else {
                continue;
            };
            if *cat == collection_type {
                return Some(rule.label.clone());
            }
        }
        None
    }
}

/// Parse a bracketed list of identifiers: `[Ident1, Ident2, ...]`
fn parse_ident_list(input: ParseStream) -> SynResult<Vec<Ident>> {
    let content;
    syn::bracketed!(content in input);
    let mut names = Vec::new();
    while !content.is_empty() {
        names.push(content.parse::<Ident>()?);
        if content.peek(Token![,]) {
            let _ = content.parse::<Token![,]>()?;
        }
    }
    // Optional trailing comma after the closing bracket
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }
    Ok(names)
}

/// Try to parse an optional `keyword: [Ident, ...]` clause.
/// Returns `Some(vec)` if the next token matches `keyword`, else `None`.
fn try_parse_keyword_list(input: ParseStream, keyword: &str) -> SynResult<Vec<Ident>> {
    if input.peek(Ident) {
        let fork = input.fork();
        let lookahead = fork.parse::<Ident>()?;
        if lookahead == keyword {
            // Consume the keyword
            let _ = input.parse::<Ident>()?;
            let _ = input.parse::<Token![:]>()?;
            return parse_ident_list(input);
        }
    }
    Ok(Vec::new())
}

// Implement Parse for LanguageDef
impl Parse for LanguageDef {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // Parse: name: Identifier
        let name_kw = input.parse::<Ident>()?;
        if name_kw != "name" {
            return Err(syn::Error::new(name_kw.span(), "expected 'name'"));
        }
        let _ = input.parse::<Token![:]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![,]>()?;

        // Parse: options { ... } (optional)
        let options = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "options" {
                parse_options(input)?
            } else {
                HashMap::new()
            }
        } else {
            HashMap::new()
        };

        // Parse: extends: [Base1, Base2] (optional)
        let extends_names = try_parse_keyword_list(input, "extends")?;

        // Parse: includes: [Calc, BoolLogic] (optional)
        let include_names = try_parse_keyword_list(input, "includes")?;

        // Parse: mixins: [ArithOps, BoolOps] (optional)
        let mixin_names = try_parse_keyword_list(input, "mixins")?;

        // Parse: types { ... } (may include refinement type definitions)
        let (types, refinement_types) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "types" {
                parse_types(input)?
            } else {
                (Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new())
        };

        // Parse: literals { ... } (optional; types{} must precede; desugars to TokenDef)
        let literals_defs: Vec<TokenDef> = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "literals" {
                parse_literals(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: tokens { ... } (optional)
        let (mut token_defs, mode_defs, sync_constraints, tree_invariants) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "tokens" {
                parse_tokens(input)?
            } else {
                (Vec::new(), Vec::new(), Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
        };

        // Validate every literals{} name is declared in types{}.
        // (Done before name-mapping so the diagnostic references the original name.)
        for ld in &literals_defs {
            if !types.iter().any(|t| t.name == ld.name) {
                return Err(syn::Error::new(
                    ld.name.span(),
                    format!(
                        "literals{{{}}} requires '{}' to be declared in types{{}}",
                        ld.name, ld.name
                    ),
                ));
            }
        }

        // Map each literals{} entry to its standard `Token::<name>` family
        // variant based on the category's native type. All integer-typed
        // categories share `Token::Integer(IntLit)`, all rational-typed
        // share `Token::Rational(RationalLit)`, etc. The original category
        // name is preserved in `TokenDef.category` so downstream codegen
        // can route per-category eval logic to the same variant.
        //
        // Categories whose native type doesn't fit a known family (or
        // categories with no native type) keep their user-facing
        // TypeName as the Token variant.
        let literals_defs: Vec<TokenDef> = literals_defs
            .into_iter()
            .map(|ld| {
                let original = ld.name.clone();
                let mapped_name = types
                    .iter()
                    .find(|t| t.name == original)
                    .and_then(|t| t.native_type.as_ref())
                    .and_then(|nt| NativeKind::from_syn_type(nt).standard_token_variant())
                    .map(|s| Ident::new(s, original.span()))
                    .unwrap_or_else(|| original.clone());
                TokenDef {
                    name: mapped_name,
                    pattern: ld.pattern,
                    // Preserve the original category so codegen can disambiguate
                    // shared-family variants per literal source.
                    category: Some(original),
                    rust_code: ld.rust_code,
                    priority: ld.priority,
                    push_mode: ld.push_mode,
                    is_pop: ld.is_pop,
                    stream: ld.stream,
                    from_literals: true,
                }
            })
            .collect();

        // Detect cross-block duplicates by `(name, pattern)` rather than name
        // alone — `literals { Int { ... } BigInt { ... } }` legitimately
        // produces two TokenDefs that share `name = Integer` (one Token
        // variant per family) but with distinct patterns.
        for ld in &literals_defs {
            if token_defs
                .iter()
                .any(|td| td.name == ld.name && td.pattern == ld.pattern)
            {
                return Err(syn::Error::new(
                    ld.name.span(),
                    format!(
                        "duplicate token (name '{}', identical pattern) declared in both \
                         literals{{}} and tokens{{}}",
                        ld.name
                    ),
                ));
            }
        }
        token_defs.extend(literals_defs);

        // Parse: guards { ... } (optional, design doc §2A)
        let guard_config = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "guards" {
                Some(parse_guards(input)?)
            } else {
                None
            }
        } else {
            None
        };

        // Build the active connective map (if `connectives {}` was declared)
        // and install it as a thread-local for the duration of the rest of
        // the parse, so behavioral predicate parsing inside rewrite/equation
        // premises recognizes the declared keywords.
        let active_map = guard_config
            .as_ref()
            .and_then(|gc| gc.connectives.as_ref())
            .and_then(|decls| ConnectiveMap::from_decls(decls).ok());

        let _guard = ConnectiveMapGuard::install(active_map);

        // Parse: terms { ... }
        let terms = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "terms" {
                parse_terms(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: equations { ... }
        let equations = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "equations" {
                parse_equations(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: rewrites { ... }
        let rewrites = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "rewrites" {
                parse_rewrites(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: logic { ... }
        let logic = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "logic" {
                Some(parse_logic(input)?)
            } else {
                None
            }
        } else {
            None
        };

        Ok(LanguageDef {
            name,
            options,
            extends_names,
            include_names,
            mixin_names,
            types,
            refinement_types,
            token_defs,
            mode_defs,
            sync_constraints,
            tree_invariants,
            terms,
            equations,
            rewrites,
            logic,
            guard_config,
        })
    }
}

fn parse_types(input: ParseStream) -> SynResult<(Vec<LangType>, Vec<RefinementTypeDef>)> {
    let types_ident = input.parse::<Ident>()?;
    if types_ident != "types" {
        return Err(syn::Error::new(types_ident.span(), "expected 'types'"));
    }

    let content;
    syn::braced!(content in input);

    let mut types = Vec::new();
    let mut refinement_types = Vec::new();
    while !content.is_empty() {
        // Check for native type syntax: ![Type] as Name
        if content.peek(Token![!]) {
            let _ = content.parse::<Token![!]>()?;

            // Parse [Type] - the brackets are part of the syntax, not the type
            let bracket_content;
            syn::bracketed!(bracket_content in content);
            let native_type_raw = bracket_content.parse::<Type>()?;

            let _ = content.parse::<Token![as]>()?;
            let name = content.parse::<Ident>()?;
            let name_str = name.to_string();

            // Special-case Map: `![HashMap] as Map` or `![HashMap<Proc, Proc>] as Map`
            // expand to the runtime wrapper (HashMapLit) so the engine's deterministic Hash/Ord apply.
            let native_type = if name_str == "Map" {
                let is_hashmap = match &native_type_raw {
                    Type::Path(tp) => tp.path.segments.last().is_some_and(|seg| {
                        seg.ident == "HashMap"
                            && matches!(
                                seg.arguments,
                                syn::PathArguments::None | syn::PathArguments::AngleBracketed(_)
                            )
                    }),
                    _ => false,
                };
                if is_hashmap {
                    syn::parse_str::<Type>("mettail_runtime::HashMapLit<Proc, Proc>")
                        .expect("parse Map native type")
                } else {
                    native_type_raw
                }
            } else {
                native_type_raw
            };

            // Optional (Param) legacy backward-compat and optional `[open, close, sep (, kv_sep)]`
            // custom delimiters for List/Bag/Map.
            let collection_kind = if name_str == "List" || name_str == "Bag" || name_str == "Map" {
                if content.peek(syn::token::Paren) {
                    let paren_content;
                    syn::parenthesized!(paren_content in content);
                    // Consume legacy params for backward compat: List(Proc), Bag(Proc), Map(Proc, Proc)
                    let _ = paren_content.parse::<Ident>()?;
                    if name_str == "Map" && paren_content.peek(Token![,]) {
                        let _ = paren_content.parse::<Token![,]>()?;
                        let _ = paren_content.parse::<Ident>()?;
                    }
                }
                let delimiters: CollectionDelimiters = if content.peek(syn::token::Bracket) {
                    let bracket_content;
                    syn::bracketed!(bracket_content in content);
                    let open: syn::LitStr = bracket_content.parse()?;
                    let _ = bracket_content.parse::<Token![,]>()?;
                    let close: syn::LitStr = bracket_content.parse()?;
                    let _ = bracket_content.parse::<Token![,]>()?;
                    let sep: syn::LitStr = bracket_content.parse()?;
                    if name_str == "Map" {
                        let _ = bracket_content.parse::<Token![,]>()?;
                        let key_val_sep: syn::LitStr = bracket_content.parse()?;
                        CollectionDelimiters {
                            open: open.value(),
                            close: close.value(),
                            sep: sep.value(),
                            key_val_sep: Some(key_val_sep.value()),
                        }
                    } else {
                        CollectionDelimiters {
                            open: open.value(),
                            close: close.value(),
                            sep: sep.value(),
                            key_val_sep: None,
                        }
                    }
                } else if name_str == "List" {
                    CollectionCategory::list_defaults()
                } else if name_str == "Bag" {
                    CollectionCategory::bag_defaults()
                } else {
                    CollectionCategory::map_defaults()
                };
                Some(if name_str == "List" {
                    CollectionCategory::List(delimiters)
                } else if name_str == "Bag" {
                    CollectionCategory::Bag(delimiters)
                } else {
                    CollectionCategory::Map(delimiters)
                })
            } else {
                None
            };

            types.push(LangType {
                name,
                native_type: Some(native_type),
                collection_kind,
            });
        } else {
            // Could be either:
            //   Name               — regular type (including bare `List`/`Bag`/`Map` with defaults)
            //   Name = { ... }     — refinement type
            let name = content.parse::<Ident>()?;

            if content.peek(Token![=]) {
                // Refinement type: Name = { var: BaseType | predicate };
                // Also push a LangType entry so the rest of the pipeline
                // (Ascent relation emission, rule validation, etc.) treats
                // PosInt as a first-class category.
                let _ = content.parse::<Token![=]>()?;
                let ref_def = parse_refinement_type_body(&content, name.clone())?;
                types.push(LangType {
                    name,
                    native_type: None,
                    collection_kind: None,
                });
                refinement_types.push(ref_def);
            } else {
                let name_str = name.to_string();
                let collection_kind = if name_str == "List" {
                    Some(CollectionCategory::List(CollectionCategory::list_defaults()))
                } else if name_str == "Bag" {
                    Some(CollectionCategory::Bag(CollectionCategory::bag_defaults()))
                } else if name_str == "Map" {
                    Some(CollectionCategory::Map(CollectionCategory::map_defaults()))
                } else {
                    None
                };
                types.push(LangType { name, native_type: None, collection_kind });
            }
        }

        if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok((types, refinement_types))
}

/// Parse a refinement type body: `{ var: BaseType | predicate }`
///
/// Called after `Name =` has been consumed. The `name` is the refinement
/// type's identifier (e.g., `PosInt`).
fn parse_refinement_type_body(input: ParseStream, name: Ident) -> SynResult<RefinementTypeDef> {
    let brace_content;
    syn::braced!(brace_content in input);

    // Parse: var : BaseType
    let var = brace_content.parse::<Ident>()?;
    brace_content.parse::<Token![:]>()?;
    let base_type = brace_content.parse::<super::types::TypeExpr>()?;

    // Parse: | predicate
    brace_content.parse::<Token![|]>()?;
    let predicate = parse_refinement_pred_implies(&brace_content)?;

    Ok(RefinementTypeDef { name, var, base_type, predicate })
}

// ── Refinement predicate parser (operator-precedence climbing) ──────────────
//
// Precedence (lowest to highest):
//   implies  =>
//   or       ||
//   and      &&
//   not      ~ / !
//   atom     variable, literal, relation, quantified, parenthesized, linear

/// Parse refinement predicate: entry point (lowest precedence = implies).
fn parse_refinement_pred_implies(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_or(input)?;
    while input.peek(Token![=>]) {
        input.parse::<Token![=>]>()?;
        let rhs = parse_refinement_pred_or(input)?;
        lhs = RefinementPredicate::Implies(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: disjunction (`||`).
fn parse_refinement_pred_or(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_and(input)?;
    while input.peek(Token![||]) {
        input.parse::<Token![||]>()?;
        let rhs = parse_refinement_pred_and(input)?;
        lhs = RefinementPredicate::Or(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: conjunction (`&&`).
fn parse_refinement_pred_and(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_not(input)?;
    while input.peek(Token![&&]) {
        input.parse::<Token![&&]>()?;
        let rhs = parse_refinement_pred_not(input)?;
        lhs = RefinementPredicate::And(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: negation (`~` or `!`).
fn parse_refinement_pred_not(input: ParseStream) -> SynResult<RefinementPredicate> {
    if input.peek(Token![~]) {
        input.parse::<Token![~]>()?;
        let inner = parse_refinement_pred_not(input)?;
        Ok(RefinementPredicate::Not(Box::new(inner)))
    } else if input.peek(Token![!]) && !input.peek(Token![!=]) {
        input.parse::<Token![!]>()?;
        let inner = parse_refinement_pred_not(input)?;
        Ok(RefinementPredicate::Not(Box::new(inner)))
    } else {
        parse_refinement_pred_atom(input)
    }
}

/// Parse refinement predicate: atomic term.
///
/// Handles:
/// - Parenthesized subexpressions: `(expr)`
/// - Quantifiers: `forall`/`exists` var [_{k=N}] [in domain]. body
/// - Relation queries: `rel(arg1, arg2, ...)`
/// - Linear comparisons: `var > 0`, `3*x + 2*y <= 7`
/// - Equality/inequality: `a == b`, `a != b`
fn parse_refinement_pred_atom(input: ParseStream) -> SynResult<RefinementPredicate> {
    // Parenthesized subexpression
    if input.peek(syn::token::Paren) {
        let paren_content;
        syn::parenthesized!(paren_content in input);
        return parse_refinement_pred_implies(&paren_content);
    }

    // Must be an identifier: could be quantifier, relation, or linear term
    let fork = input.fork();
    let ident: Ident = fork.parse()?;
    let ident_str = ident.to_string();

    // Quantifiers: forall / exists
    if ident_str == "forall" || ident_str == "exists" {
        input.parse::<Ident>()?; // consume the keyword
        let quantifier = if ident_str == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };

        // Optional bound: _{k=N}
        let bound = if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            let brace_content;
            syn::braced!(brace_content in input);
            let k_ident = brace_content.parse::<Ident>()?;
            if k_ident != "k" {
                return Err(syn::Error::new(k_ident.span(), "expected 'k'"));
            }
            brace_content.parse::<Token![=]>()?;
            let lit: syn::LitInt = brace_content.parse()?;
            Some(lit.base10_parse::<usize>()?)
        } else {
            None
        };

        // Quantified variable
        let var = input.parse::<Ident>()?;

        // Optional domain: `in relation`
        let domain = if input.peek(Ident) {
            let next_fork = input.fork();
            let next_ident: Ident = next_fork.parse()?;
            if next_ident == "in" {
                input.parse::<Ident>()?; // consume "in"
                Some(input.parse::<Ident>()?)
            } else {
                None
            }
        } else {
            None
        };

        // Dot separator
        input.parse::<Token![.]>()?;

        // Body (may be parenthesized)
        let body = parse_refinement_pred_atom(input)?;

        return Ok(RefinementPredicate::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }

    // Check if this is a relation query: ident(args)
    if fork.peek(syn::token::Paren) {
        input.parse::<Ident>()?; // consume the relation name
        let paren_content;
        syn::parenthesized!(paren_content in input);
        let mut args = Vec::new();
        while !paren_content.is_empty() {
            let arg_ident = paren_content.parse::<Ident>()?;
            let first_char = arg_ident.to_string().chars().next().unwrap_or('a');
            if first_char.is_uppercase() {
                args.push(PredArg::Constant(arg_ident));
            } else {
                args.push(PredArg::Var(arg_ident));
            }
            if paren_content.peek(Token![,]) {
                paren_content.parse::<Token![,]>()?;
            }
        }
        return Ok(RefinementPredicate::Relation { name: ident, args, negated: false });
    }

    // Linear arithmetic or simple variable comparison
    // Parse: ident followed by comparison operator
    // We need to handle: `x > 0`, `x >= 0`, `x == y`, etc.
    input.parse::<Ident>()?; // consume the first identifier

    // Check for comparison operators
    if input.peek(Token![>]) && input.peek2(Token![=]) {
        input.parse::<Token![>]>()?;
        input.parse::<Token![=]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Ge,
            rhs,
        });
    }
    if input.peek(Token![>]) {
        input.parse::<Token![>]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Gt,
            rhs,
        });
    }
    if input.peek(Token![<]) && input.peek2(Token![=]) {
        input.parse::<Token![<]>()?;
        input.parse::<Token![=]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Le,
            rhs,
        });
    }
    if input.peek(Token![<]) {
        input.parse::<Token![<]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Lt,
            rhs,
        });
    }
    if input.peek(Token![==]) {
        input.parse::<Token![==]>()?;
        // Could be term equality or linear equality
        if input.peek(syn::LitInt) {
            let rhs = parse_linear_rhs(input)?;
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: LinearRelation::Eq,
                rhs,
            });
        }
        let rhs_ident = input.parse::<Ident>()?;
        let first_char = rhs_ident.to_string().chars().next().unwrap_or('a');
        let rhs_arg = if first_char.is_uppercase() {
            PredArg::Constant(rhs_ident)
        } else {
            PredArg::Var(rhs_ident)
        };
        let first_char_lhs = ident.to_string().chars().next().unwrap_or('a');
        let lhs_arg = if first_char_lhs.is_uppercase() {
            PredArg::Constant(ident)
        } else {
            PredArg::Var(ident)
        };
        return Ok(RefinementPredicate::TermEq(lhs_arg, rhs_arg));
    }
    if input.peek(Token![!=]) {
        input.parse::<Token![!=]>()?;
        if input.peek(syn::LitInt) {
            let rhs = parse_linear_rhs(input)?;
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: LinearRelation::Neq,
                rhs,
            });
        }
        let rhs_ident = input.parse::<Ident>()?;
        let first_char = rhs_ident.to_string().chars().next().unwrap_or('a');
        let rhs_arg = if first_char.is_uppercase() {
            PredArg::Constant(rhs_ident)
        } else {
            PredArg::Var(rhs_ident)
        };
        let first_char_lhs = ident.to_string().chars().next().unwrap_or('a');
        let lhs_arg = if first_char_lhs.is_uppercase() {
            PredArg::Constant(ident)
        } else {
            PredArg::Var(ident)
        };
        return Ok(RefinementPredicate::TermNeq(lhs_arg, rhs_arg));
    }

    // Bare identifier — treat as zero-argument relation query
    Ok(RefinementPredicate::Relation {
        name: ident,
        args: vec![],
        negated: false,
    })
}

/// Parse the right-hand side of a linear comparison (integer literal).
fn parse_linear_rhs(input: ParseStream) -> SynResult<i64> {
    let negative = if input.peek(Token![-]) {
        input.parse::<Token![-]>()?;
        true
    } else {
        false
    };
    let lit: syn::LitInt = input.parse()?;
    let val = lit.base10_parse::<i64>()?;
    Ok(if negative { -val } else { val })
}

/// Public wrapper for `parse_types` for use by `fragment.rs`.
pub fn parse_types_public(
    input: ParseStream,
) -> SynResult<(Vec<LangType>, Vec<RefinementTypeDef>)> {
    parse_types(input)
}

/// Reconstruct a proc_macro2 token tree as a string without inserted whitespace.
///
/// Used for regex pattern reconstruction: proc_macro2 may add spaces between tokens
/// that are significant in regex patterns (e.g., `[0 - 9]` vs `[0-9]`), so we
/// concatenate without separators.
fn token_tree_to_string(tt: &proc_macro2::TokenTree) -> String {
    match tt {
        proc_macro2::TokenTree::Group(g) => {
            let (open, close) = match g.delimiter() {
                proc_macro2::Delimiter::Parenthesis => ("(", ")"),
                proc_macro2::Delimiter::Brace => ("{", "}"),
                proc_macro2::Delimiter::Bracket => ("[", "]"),
                proc_macro2::Delimiter::None => ("", ""),
            };
            let inner: String = g
                .stream()
                .into_iter()
                .map(|t| token_tree_to_string(&t))
                .collect();
            format!("{}{}{}", open, inner, close)
        },
        proc_macro2::TokenTree::Ident(i) => i.to_string(),
        proc_macro2::TokenTree::Punct(p) => p.as_char().to_string(),
        proc_macro2::TokenTree::Literal(l) => l.to_string(),
    }
}

/// Parse a regex pattern between `/` delimiters.
///
/// Collects all tokens between opening and closing `/`, reconstructing
/// the regex string without spaces. Handles `\/` escape (backslash before
/// `/` prevents it from being treated as the closing delimiter).
///
/// **Limitation**: Patterns containing unescaped `"` characters are tokenized
/// as string literals by proc_macro2 and may not reconstruct correctly. Use
/// the string literal form (`"pattern"` or `r"pattern"`) for such patterns.
fn parse_regex_pattern(input: ParseStream) -> SynResult<String> {
    // Parse opening /
    let _open_slash: Token![/] = input.parse()?;

    let mut tokens: Vec<proc_macro2::TokenTree> = Vec::new();
    let mut prev_was_backslash = false;

    loop {
        if input.is_empty() {
            return Err(input.error("unterminated regex pattern: expected closing '/'"));
        }

        // Check for closing / (not preceded by \)
        if !prev_was_backslash && input.peek(Token![/]) {
            break;
        }

        let tt: proc_macro2::TokenTree = input.parse()?;
        prev_was_backslash = matches!(&tt, proc_macro2::TokenTree::Punct(p) if p.as_char() == '\\');
        tokens.push(tt);
    }

    // Parse closing /
    let _: Token![/] = input.parse()?;

    // Reconstruct regex string without spaces
    let pattern: String = tokens.iter().map(token_tree_to_string).collect();
    Ok(pattern)
}

/// Parse a regex/pattern specifier: either `/regex/` or a string literal.
///
/// Supports both forms:
/// - `/[0-9]+/` — slash-delimited (convenient for simple patterns)
/// - `r"[0-9]+"` or `"[0-9]+"` — string literal (required for patterns with `"`)
fn parse_pattern_spec(input: ParseStream) -> SynResult<String> {
    if input.peek(Token![/]) {
        parse_regex_pattern(input)
    } else if input.peek(syn::LitStr) {
        let lit: syn::LitStr = input.parse()?;
        Ok(lit.value())
    } else {
        Err(input.error(
            "expected regex pattern: /pattern/ or \"pattern\" (use string literal for patterns containing '\"')",
        ))
    }
}

/// Parse a single token definition.
///
/// Grammar:
/// ```text
/// token_def ::= Name "=" pattern_spec [":" Category] ["!" "[" rust_code "]"]
///               ["push" "(" mode_name ")"] ["pop"]
///               ["->" stream_name] ["priority" "(" integer ")"] ";"
/// pattern_spec ::= "/" regex "/" | string_literal
/// ```
fn parse_token_def(input: ParseStream) -> SynResult<TokenDef> {
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![=]>()?;

    // Parse regex pattern (either /regex/ or "regex")
    let pattern = parse_pattern_spec(input)?;

    // Optional: : Category
    let category = if input.peek(Token![:]) {
        let _ = input.parse::<Token![:]>()?;
        Some(input.parse::<Ident>()?)
    } else {
        None
    };

    // Optional: ![code]
    let rust_code = if input.peek(Token![!]) {
        let _ = input.parse::<Token![!]>()?;
        let bracket_content;
        syn::bracketed!(bracket_content in input);
        let code: TokenStream = bracket_content.parse()?;
        Some(code)
    } else {
        None
    };

    // Parse modifiers in any order before ;
    let mut push_mode = None;
    let mut is_pop = false;
    let mut stream = None;
    let mut priority = None;

    while !input.peek(Token![;]) && !input.is_empty() {
        if input.peek(Ident) {
            let fork = input.fork();
            let kw = fork.parse::<Ident>()?;
            match kw.to_string().as_str() {
                "push" => {
                    let _ = input.parse::<Ident>()?; // consume "push"
                    let content;
                    syn::parenthesized!(content in input);
                    push_mode = Some(content.parse::<Ident>()?);
                },
                "pop" => {
                    let _ = input.parse::<Ident>()?; // consume "pop"
                    is_pop = true;
                },
                "priority" => {
                    let _ = input.parse::<Ident>()?; // consume "priority"
                    let content;
                    syn::parenthesized!(content in input);
                    let lit: syn::LitInt = content.parse()?;
                    priority = Some(lit.base10_parse::<u8>().map_err(|e| {
                        syn::Error::new(lit.span(), format!("invalid priority: {}", e))
                    })?);
                },
                _ => {
                    return Err(syn::Error::new(
                        kw.span(),
                        format!(
                            "unexpected modifier '{}' in token definition; \
                             expected 'push', 'pop', 'priority', or '->'",
                            kw
                        ),
                    ));
                },
            }
        } else if input.peek(Token![->]) {
            let _ = input.parse::<Token![->]>()?;
            stream = Some(input.parse::<Ident>()?);
        } else {
            return Err(input.error(
                "unexpected token in token definition; expected ';', \
                 a modifier (push, pop, priority), or '-> stream'",
            ));
        }
    }

    let _ = input.parse::<Token![;]>()?;

    Ok(TokenDef {
        name,
        pattern,
        category,
        rust_code,
        priority,
        push_mode,
        is_pop,
        stream,
        from_literals: false,
    })
}

/// Parse a `mode name { ... }` block containing token definitions.
fn parse_mode_def(input: ParseStream) -> SynResult<ModeDef> {
    let _ = input.parse::<Ident>()?; // consume "mode"
    let name = input.parse::<Ident>()?;

    let content;
    syn::braced!(content in input);

    let mut token_defs = Vec::new();
    while !content.is_empty() {
        token_defs.push(parse_token_def(&content)?);
    }

    Ok(ModeDef { name, token_defs })
}

/// Parse `sync { ... }` block with cross-stream synchronization constraints.
fn parse_sync_block(input: ParseStream) -> SynResult<Vec<SyncConstraint>> {
    let _ = input.parse::<Ident>()?; // consume "sync"

    let content;
    syn::braced!(content in input);

    let mut constraints = Vec::new();
    while !content.is_empty() {
        let kw = content.parse::<Ident>()?;
        match kw.to_string().as_str() {
            "align" => {
                let args;
                syn::parenthesized!(args in content);
                let stream_a = args.parse::<Ident>()?;
                let _ = args.parse::<Token![,]>()?;
                let stream_b = args.parse::<Ident>()?;

                let on_kw = content.parse::<Ident>()?;
                if on_kw != "on" {
                    return Err(syn::Error::new(
                        on_kw.span(),
                        "expected 'on' after align(stream_a, stream_b)",
                    ));
                }
                let boundary_pattern = parse_pattern_spec(&content)?;
                let _ = content.parse::<Token![;]>()?;

                constraints.push(SyncConstraint::Align { stream_a, stream_b, boundary_pattern });
            },
            "track" => {
                let args;
                syn::parenthesized!(args in content);
                let auxiliary = args.parse::<Ident>()?;
                let _ = args.parse::<Token![,]>()?;
                let primary = args.parse::<Ident>()?;
                let _ = content.parse::<Token![;]>()?;

                constraints.push(SyncConstraint::Track { auxiliary, primary });
            },
            _ => {
                return Err(syn::Error::new(
                    kw.span(),
                    format!("unknown sync constraint '{}'; expected 'align' or 'track'", kw),
                ));
            },
        }
    }

    Ok(constraints)
}

/// Parse a tree constraint expression.
///
/// Supports both keyword and Unicode operator forms at each position.
/// Grammar:
/// ```text
/// tree_expr ::= tree_atom (("and" | "∧" | "or" | "∨") tree_expr)?
/// tree_atom ::= ("forall" | "∀") children_of? Symbol "{" tree_expr "}"
///             | ("exists" | "∃") "child"
///             | ("not" | "¬") tree_atom
///             | ("match" | "∈") "{" symbol ("|" symbol)* "}"
///             | "(" tree_expr ")"
///             | Symbol
/// children_of ::= ("children" "of" | "↓")
/// ```
fn parse_tree_constraint_expr(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    let left = parse_tree_constraint_atom(input)?;

    // Check for binary operators: and/∧, or/∨
    if input.peek(Ident) {
        let fork = input.fork();
        if let Ok(kw) = fork.parse::<Ident>() {
            let kw_str = kw.to_string();
            if kw_str == "and" || kw_str == "\u{2227}" {
                // ∧ = U+2227
                let _ = input.parse::<Ident>()?;
                let right = parse_tree_constraint_expr(input)?;
                return Ok(TreeConstraintExpr::And(Box::new(left), Box::new(right)));
            } else if kw_str == "or" || kw_str == "\u{2228}" {
                // ∨ = U+2228
                let _ = input.parse::<Ident>()?;
                let right = parse_tree_constraint_expr(input)?;
                return Ok(TreeConstraintExpr::Or(Box::new(left), Box::new(right)));
            }
        }
    }

    Ok(left)
}

/// Parse an atomic tree constraint expression (unary/leaf).
fn parse_tree_constraint_atom(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    if input.peek(Ident) {
        let fork = input.fork();
        let kw = fork.parse::<Ident>()?;
        let kw_str = kw.to_string();

        match kw_str.as_str() {
            // forall / ∀
            "forall" | "\u{2200}" => {
                let _ = input.parse::<Ident>()?; // consume forall/∀

                // Check for "children of" / "↓"
                let fork2 = input.fork();
                let next = fork2.parse::<Ident>()?;
                let next_str = next.to_string();

                if next_str == "children" {
                    let _ = input.parse::<Ident>()?; // consume "children"
                    let of_kw = input.parse::<Ident>()?; // consume "of"
                    if of_kw != "of" {
                        return Err(syn::Error::new(
                            of_kw.span(),
                            "expected 'of' after 'children'",
                        ));
                    }
                    let symbol = input.parse::<Ident>()?;
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: symbol.to_string(),
                        body: Box::new(body),
                    })
                } else if next_str == "\u{2193}" {
                    // ↓ = U+2193
                    let _ = input.parse::<Ident>()?; // consume "↓"
                    let symbol = input.parse::<Ident>()?;
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: symbol.to_string(),
                        body: Box::new(body),
                    })
                } else {
                    // forall Symbol { body } (shorthand: symbol is next token)
                    let _ = input.parse::<Ident>()?; // consume symbol
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: next_str,
                        body: Box::new(body),
                    })
                }
            },
            // exists / ∃
            "exists" | "\u{2203}" => {
                let _ = input.parse::<Ident>()?; // consume exists/∃
                let next = input.parse::<Ident>()?;
                if next != "child" {
                    return Err(syn::Error::new(
                        next.span(),
                        "expected 'child' after 'exists'/'∃'",
                    ));
                }
                Ok(TreeConstraintExpr::ExistsChild)
            },
            // not / ¬
            "not" | "\u{00AC}" => {
                let _ = input.parse::<Ident>()?; // consume not/¬
                let inner = parse_tree_constraint_atom(input)?;
                Ok(TreeConstraintExpr::Not(Box::new(inner)))
            },
            // match / ∈
            "match" | "\u{2208}" => {
                let _ = input.parse::<Ident>()?; // consume match/∈
                let body_content;
                syn::braced!(body_content in input);
                let mut symbols = Vec::new();
                while !body_content.is_empty() {
                    symbols.push(body_content.parse::<Ident>()?.to_string());
                    if body_content.peek(Token![|]) {
                        let _ = body_content.parse::<Token![|]>()?;
                    }
                }
                Ok(TreeConstraintExpr::Match(symbols))
            },
            // Plain atom: symbol name
            _ => {
                let _ = input.parse::<Ident>()?;
                Ok(TreeConstraintExpr::Atom(kw_str))
            },
        }
    } else if input.peek(syn::token::Paren) {
        // Parenthesized sub-expression
        let paren_content;
        syn::parenthesized!(paren_content in input);
        parse_tree_constraint_expr(&paren_content)
    } else {
        Err(input.error("expected tree constraint expression"))
    }
}

/// Parse `tree_invariants { ... }` block with structural constraints.
fn parse_tree_invariants_block(input: ParseStream) -> SynResult<Vec<TreeInvariant>> {
    let _ = input.parse::<Ident>()?; // consume "tree_invariants"

    let content;
    syn::braced!(content in input);

    let mut invariants = Vec::new();
    while !content.is_empty() {
        let name = content.parse::<Ident>()?;
        let _ = content.parse::<Token![:]>()?;
        let constraint = parse_tree_constraint_expr(&content)?;
        let _ = content.parse::<Token![;]>()?;
        invariants.push(TreeInvariant { name, constraint });
    }

    Ok(invariants)
}

/// Parse the `tokens { ... }` block.
///
/// Contains token definitions (default mode), named mode blocks,
/// optional `sync { ... }` block, and optional `tree_invariants { ... }` block.
fn parse_tokens(
    input: ParseStream,
) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>, Vec<SyncConstraint>, Vec<TreeInvariant>)> {
    let tokens_ident = input.parse::<Ident>()?;
    if tokens_ident != "tokens" {
        return Err(syn::Error::new(tokens_ident.span(), "expected 'tokens'"));
    }

    let content;
    syn::braced!(content in input);

    let mut token_defs = Vec::new();
    let mut mode_defs = Vec::new();
    let mut sync_constraints = Vec::new();
    let mut tree_invariants_vec = Vec::new();

    while !content.is_empty() {
        // Peek at the next identifier to determine what to parse
        if content.peek(Ident) {
            let fork = content.fork();
            let kw = fork.parse::<Ident>()?;
            let kw_str = kw.to_string();

            match kw_str.as_str() {
                "mode" => {
                    mode_defs.push(parse_mode_def(&content)?);
                },
                "sync" => {
                    sync_constraints = parse_sync_block(&content)?;
                },
                "tree_invariants" => {
                    tree_invariants_vec = parse_tree_invariants_block(&content)?;
                },
                _ => {
                    // Token definition: Name = /regex/ ...
                    token_defs.push(parse_token_def(&content)?);
                },
            }
        } else {
            return Err(
                content.error("expected token definition, 'mode', 'sync', or 'tree_invariants'")
            );
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok((token_defs, mode_defs, sync_constraints, tree_invariants_vec))
}

/// Public wrapper for `parse_tokens` for use by `fragment.rs`.
pub fn parse_tokens_public(input: ParseStream) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>)> {
    let (token_defs, mode_defs, _, _) = parse_tokens(input)?;
    Ok((token_defs, mode_defs))
}

/// Parse the `literals { ... }` block and desugar each entry into a `TokenDef`.
///
/// Syntax (main-branch surface):
///
/// ```text
/// literals {
///     TypeName {
///         pattern: r"regex";
///         eval: ![ rust_expr ]
///     }
///     ...
/// }
/// ```
///
/// Each entry desugars to:
///
/// ```text
/// TokenDef {
///     name: TypeName,
///     pattern: <regex string>,
///     category: Some(TypeName),   // name auto-binds to category
///     rust_code: Some(<eval tokens>),
///     priority: None,             // default 2 at CustomTokenSpec level
///     push_mode: None, is_pop: false, stream: None,
/// }
/// ```
///
/// `TypeName` must be declared in `types { }` — enforced later during
/// semantic validation (parse-time only checks surface shape).
fn parse_literals(input: ParseStream) -> SynResult<Vec<TokenDef>> {
    let literals_ident = input.parse::<Ident>()?;
    if literals_ident != "literals" {
        return Err(syn::Error::new(literals_ident.span(), "expected 'literals'"));
    }
    let content;
    syn::braced!(content in input);

    let mut defs = Vec::new();
    while !content.is_empty() {
        let type_name = content.parse::<Ident>()?;
        let type_block;
        syn::braced!(type_block in content);

        // pattern: "..." or r"..."
        let pattern_kw = type_block.parse::<Ident>()?;
        if pattern_kw != "pattern" {
            return Err(syn::Error::new(pattern_kw.span(), "expected 'pattern'"));
        }
        let _ = type_block.parse::<Token![:]>()?;
        let pattern_lit: syn::LitStr = type_block.parse()?;
        let pattern = pattern_lit.value();
        let _ = type_block.parse::<Token![;]>()?;

        // eval: ![ ... ]
        let eval_kw = type_block.parse::<Ident>()?;
        if eval_kw != "eval" {
            return Err(syn::Error::new(eval_kw.span(), "expected 'eval'"));
        }
        let _ = type_block.parse::<Token![:]>()?;
        if !type_block.peek(Token![!]) || !type_block.peek2(syn::token::Bracket) {
            return Err(syn::Error::new(type_block.span(), "expected eval: ![ ... ]"));
        }
        let _ = type_block.parse::<Token![!]>()?;
        let eval_content;
        syn::bracketed!(eval_content in type_block);
        let eval: TokenStream = eval_content.parse()?;

        defs.push(TokenDef {
            name: type_name.clone(),
            pattern,
            category: Some(type_name),
            rust_code: Some(eval),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });

        if type_block.peek(Token![;]) {
            let _ = type_block.parse::<Token![;]>()?;
        }
    }

    // Optional trailing comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(defs)
}

// ══════════════════════════════════════════════════════════════════════════════
// Guard configuration parser — `guards { ... }` block (design doc §2A)
// ══════════════════════════════════════════════════════════════════════════════
//
// Architecture mirrors `parse_tokens`: direct items (built-in predicate
// declarations) coexist with named configuration sub-blocks (`connectives {}`,
// `theories {}`, `channels {}`).

/// Parse the `guards { ... }` block.
fn parse_guards(input: ParseStream) -> SynResult<GuardConfig> {
    let guards_ident = input.parse::<Ident>()?;
    if guards_ident != "guards" {
        return Err(syn::Error::new(guards_ident.span(), "expected 'guards'"));
    }

    let content;
    syn::braced!(content in input);

    let mut builtin_predicates: Vec<BuiltinPredicate> = Vec::new();
    let mut connectives: Option<Vec<ConnectiveDecl>> = None;
    let mut theories: Vec<TheoryRegistration> = Vec::new();
    let mut channels: Option<ChannelConfig> = None;
    let mut saw_explicit_predicates = false;

    while !content.is_empty() {
        if !content.peek(Ident) {
            return Err(content.error(
                "expected predicate declaration, 'connectives', 'theories', or 'channels'",
            ));
        }

        let fork = content.fork();
        let kw = fork.parse::<Ident>()?;
        let kw_str = kw.to_string();

        match kw_str.as_str() {
            "connectives" => {
                if connectives.is_some() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `connectives {}` sub-block in guards",
                    ));
                }
                connectives = Some(parse_connectives_block(&content)?);
            },
            "theories" => {
                if !theories.is_empty() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `theories {}` sub-block in guards",
                    ));
                }
                theories = parse_theories_block(&content)?;
            },
            "channels" => {
                if channels.is_some() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `channels {}` sub-block in guards",
                    ));
                }
                channels = Some(parse_channels_block(&content)?);
            },
            _ => {
                // Direct item: builtin predicate declaration
                builtin_predicates.push(parse_builtin_predicate(&content)?);
                saw_explicit_predicates = true;
            },
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(GuardConfig {
        builtin_predicates: if saw_explicit_predicates {
            Some(builtin_predicates)
        } else {
            None
        },
        connectives,
        theories,
        channels,
    })
}

/// Parse a single built-in predicate declaration:
///
/// ```ignore
/// Label . params |- syntax_form (| syntax_form)* @[anno1, anno2]? ;
/// ```
fn parse_builtin_predicate(input: ParseStream) -> SynResult<BuiltinPredicate> {
    // Predicate name (label)
    let name = input.parse::<Ident>()?;

    // `.` separator before params
    let _ = input.parse::<Token![.]>()?;

    // Parameter list (comma-separated)
    let params = parse_predicate_params(input)?;

    // `|-` (turnstile)
    let _ = input.parse::<Token![|]>()?;
    let _ = input.parse::<Token![-]>()?;

    // Syntax forms — at least one, alternatives separated by `|`
    let mut syntax_forms: Vec<Vec<super::grammar::SyntaxExpr>> = Vec::new();
    syntax_forms.push(parse_predicate_syntax_form(input)?);
    while input.peek(Token![|]) {
        // Bare `|` separates alternative forms (the `|-` turnstile already
        // consumed; here `|` always introduces another alternative).
        let _ = input.parse::<Token![|]>()?;
        syntax_forms.push(parse_predicate_syntax_form(input)?);
    }

    // Optional `@[...]` annotations
    let annotations = if input.peek(Token![@]) {
        parse_annotations(input)?
    } else {
        PredicateAnnotations::default()
    };

    // Required `;` terminator
    let _ = input.parse::<Token![;]>()?;

    Ok(BuiltinPredicate { name, params, syntax_forms, annotations })
}

/// Parse the parameter list of a built-in predicate.
///
/// Each parameter has the form: `name (: Type)? (Quantifier)?`
/// where `Type` is a single ident or `(Ident|Ident|...)` union, and
/// `Quantifier` is `+`, `*`, `{m,n}`, `{m,}`, or `{,n}`.
fn parse_predicate_params(input: ParseStream) -> SynResult<Vec<PredicateParam>> {
    let mut params = Vec::new();

    // Allow empty parameter list (some predicates have no params)
    if input.peek(Token![|]) && input.peek2(Token![-]) {
        return Ok(params);
    }

    loop {
        let name = input.parse::<Ident>()?;

        // Optional type annotation
        let ty = if input.peek(Token![:]) {
            let _ = input.parse::<Token![:]>()?;
            Some(parse_predicate_param_type(input)?)
        } else {
            None
        };

        // Optional quantifier suffix
        let quantifier = parse_optional_param_quantifier(input)?;

        params.push(PredicateParam { name, ty, quantifier });

        // Continue if comma; otherwise stop
        if input.peek(Token![,]) {
            // Don't consume the comma if it's part of the next item
            // (e.g., `|-` is next). Look ahead.
            let fork = input.fork();
            let _ = fork.parse::<Token![,]>()?;
            if fork.peek(Ident) {
                let _ = input.parse::<Token![,]>()?;
            } else {
                break;
            }
        } else {
            break;
        }
    }

    Ok(params)
}

/// Parse a parameter type: `Ident` or `(Ident|Ident|...)`
fn parse_predicate_param_type(input: ParseStream) -> SynResult<ParamType> {
    if input.peek(syn::token::Paren) {
        let inner;
        syn::parenthesized!(inner in input);
        let mut types = vec![inner.parse::<Ident>()?];
        while inner.peek(Token![|]) {
            let _ = inner.parse::<Token![|]>()?;
            types.push(inner.parse::<Ident>()?);
        }
        Ok(ParamType::Union(types))
    } else {
        Ok(ParamType::Single(input.parse::<Ident>()?))
    }
}

/// Parse an optional repetition quantifier suffix: `+`, `*`, or `{m,n}`.
fn parse_optional_param_quantifier(input: ParseStream) -> SynResult<Option<ParamQuantifier>> {
    if input.peek(Token![+]) {
        let _ = input.parse::<Token![+]>()?;
        Ok(Some(ParamQuantifier::OneOrMore))
    } else if input.peek(Token![*]) {
        let _ = input.parse::<Token![*]>()?;
        Ok(Some(ParamQuantifier::ZeroOrMore))
    } else if input.peek(syn::token::Brace) {
        let inner;
        syn::braced!(inner in input);
        // Parse `m`, `,`, optional `n`
        let min = if inner.peek(syn::LitInt) {
            let lit = inner.parse::<syn::LitInt>()?;
            lit.base10_parse::<usize>()?
        } else {
            0
        };
        let _ = inner.parse::<Token![,]>()?;
        let max = if inner.peek(syn::LitInt) {
            let lit = inner.parse::<syn::LitInt>()?;
            Some(lit.base10_parse::<usize>()?)
        } else {
            None
        };
        Ok(Some(ParamQuantifier::Range { min, max }))
    } else {
        Ok(None)
    }
}

/// Parse a single syntax form for a built-in predicate. Stops at `|` (next
/// alternative form), `@` (annotations), or `;` (terminator).
fn parse_predicate_syntax_form(input: ParseStream) -> SynResult<Vec<super::grammar::SyntaxExpr>> {
    let mut exprs = Vec::new();
    while !input.is_empty()
        && !input.peek(Token![;])
        && !input.peek(Token![@])
        && !input.peek(Token![|])
    {
        exprs.push(super::grammar::parse_syntax_expr(input)?);
    }
    if exprs.is_empty() {
        return Err(input.error("expected at least one syntax expression in predicate form"));
    }
    Ok(exprs)
}

/// Parse `@[selectivity(s), cost(c)]` annotations.
fn parse_annotations(input: ParseStream) -> SynResult<PredicateAnnotations> {
    let _ = input.parse::<Token![@]>()?;
    let inner;
    syn::bracketed!(inner in input);

    let mut annotations = PredicateAnnotations::default();

    while !inner.is_empty() {
        let name_ident = inner.parse::<Ident>()?;
        let name = name_ident.to_string();
        let arg;
        syn::parenthesized!(arg in inner);

        match name.as_str() {
            "selectivity" => {
                let lit = arg.parse::<syn::LitFloat>()?;
                let value: f64 = lit.base10_parse()?;
                if !(0.0..=1.0).contains(&value) {
                    return Err(syn::Error::new(lit.span(), "selectivity must be in [0.0, 1.0]"));
                }
                annotations.selectivity = Some(value);
            },
            "cost" => {
                let lit = arg.parse::<syn::LitInt>()?;
                let value: u32 = lit.base10_parse()?;
                annotations.cost = Some(value);
            },
            other => {
                return Err(syn::Error::new(
                    name_ident.span(),
                    format!("unknown annotation `{}` (expected `selectivity` or `cost`)", other),
                ));
            },
        }

        if inner.peek(Token![,]) {
            let _ = inner.parse::<Token![,]>()?;
        }
    }

    Ok(annotations)
}

/// Parse the `connectives { role = "kw1" | "kw2" ; ... }` sub-block.
fn parse_connectives_block(input: ParseStream) -> SynResult<Vec<ConnectiveDecl>> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "connectives" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'connectives'"));
    }
    let content;
    syn::braced!(content in input);

    let mut decls = Vec::new();
    while !content.is_empty() {
        let role_ident = content.parse::<Ident>()?;
        let role = ConnectiveRole::from_ident(&role_ident.to_string()).ok_or_else(|| {
            syn::Error::new(
                role_ident.span(),
                format!(
                    "unknown connective role `{}` (expected one of: and, or, not, \
                     entails, implied_by, iff, forall, exists)",
                    role_ident
                ),
            )
        })?;

        let _ = content.parse::<Token![=]>()?;

        // Parse one or more "keyword" string literals separated by `|`
        let first_lit = content.parse::<syn::LitStr>()?;
        let mut keywords = vec![first_lit.value()];
        while content.peek(Token![|]) {
            let _ = content.parse::<Token![|]>()?;
            let lit = content.parse::<syn::LitStr>()?;
            keywords.push(lit.value());
        }

        let _ = content.parse::<Token![;]>()?;

        decls.push(ConnectiveDecl { role, keywords });
    }

    Ok(decls)
}

/// Parse the `theories { name = TheoryType for [Cat1, Cat2]; ... }` sub-block.
fn parse_theories_block(input: ParseStream) -> SynResult<Vec<TheoryRegistration>> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "theories" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'theories'"));
    }
    let content;
    syn::braced!(content in input);

    let mut regs = Vec::new();
    while !content.is_empty() {
        let name = content.parse::<Ident>()?;
        let _ = content.parse::<Token![=]>()?;
        let theory_type = content.parse::<Type>()?;

        // Optional `for [Cat1, Cat2, ...]`
        let handled_types = if content.peek(Token![for]) {
            let _ = content.parse::<Token![for]>()?;
            let inner;
            syn::bracketed!(inner in content);
            let mut cats = Vec::new();
            while !inner.is_empty() {
                cats.push(inner.parse::<Ident>()?);
                if inner.peek(Token![,]) {
                    let _ = inner.parse::<Token![,]>()?;
                }
            }
            Some(cats)
        } else {
            None
        };

        let _ = content.parse::<Token![;]>()?;

        regs.push(TheoryRegistration { name, theory_type, handled_types });
    }

    Ok(regs)
}

/// Parse the `channels { channel Cat; join Label(p: Cat, ...); ... }` sub-block.
fn parse_channels_block(input: ParseStream) -> SynResult<ChannelConfig> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "channels" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'channels'"));
    }
    let content;
    syn::braced!(content in input);

    let mut channel_categories: Vec<ChannelDecl> = Vec::new();
    let mut join_patterns: Vec<JoinPatternDecl> = Vec::new();

    while !content.is_empty() {
        let item_kw = content.parse::<Ident>()?;
        let item_str = item_kw.to_string();
        match item_str.as_str() {
            "channel" => {
                let category = content.parse::<Ident>()?;
                let _ = content.parse::<Token![;]>()?;
                channel_categories.push(ChannelDecl { category });
            },
            "join" => {
                let label = content.parse::<Ident>()?;
                let inner;
                syn::parenthesized!(inner in content);
                let mut channel_params: Vec<ChannelParam> = Vec::new();
                while !inner.is_empty() {
                    let param_name = inner.parse::<Ident>()?;
                    let _ = inner.parse::<Token![:]>()?;
                    let category = inner.parse::<Ident>()?;
                    channel_params.push(ChannelParam { param_name, category });
                    if inner.peek(Token![,]) {
                        let _ = inner.parse::<Token![,]>()?;
                    }
                }
                let _ = content.parse::<Token![;]>()?;
                join_patterns.push(JoinPatternDecl { label, channel_params });
            },
            other => {
                return Err(syn::Error::new(
                    item_kw.span(),
                    format!("unknown channels item `{}` (expected `channel` or `join`)", other),
                ));
            },
        }
    }

    Ok(ChannelConfig { channel_categories, join_patterns })
}

fn parse_options(input: ParseStream) -> SynResult<HashMap<String, AttributeValue>> {
    let options_ident = input.parse::<Ident>()?;
    if options_ident != "options" {
        return Err(syn::Error::new(options_ident.span(), "expected 'options'"));
    }

    let content;
    syn::braced!(content in input);

    let mut options = HashMap::new();
    while !content.is_empty() {
        let key_ident = content.parse::<Ident>()?;
        let key = key_ident.to_string();
        let _ = content.parse::<Token![:]>()?;

        // Parse value: float, integer, boolean, string literal, or keyword identifier
        let value = if content.peek(syn::LitFloat) {
            let lit = content.parse::<syn::LitFloat>()?;
            let f: f64 = lit
                .base10_parse()
                .map_err(|e| syn::Error::new(lit.span(), format!("invalid float value: {}", e)))?;
            AttributeValue::Float(f)
        } else if content.peek(syn::LitInt) {
            let lit = content.parse::<syn::LitInt>()?;
            let i: i64 = lit.base10_parse().map_err(|e| {
                syn::Error::new(lit.span(), format!("invalid integer value: {}", e))
            })?;
            AttributeValue::Int(i)
        } else if content.peek(syn::LitBool) {
            let lit = content.parse::<syn::LitBool>()?;
            AttributeValue::Bool(lit.value)
        } else if content.peek(syn::LitStr) {
            let lit = content.parse::<syn::LitStr>()?;
            AttributeValue::Str(lit.value())
        } else if content.peek(Ident::peek_any) {
            let ident = content.call(Ident::parse_any)?;
            AttributeValue::Keyword(ident.to_string())
        } else {
            return Err(syn::Error::new(
                content.span(),
                "expected a float, integer, boolean, string literal, or keyword (none, disabled, auto)",
            ));
        };

        // Validate known keys
        match key.as_str() {
            "beam_width" => {
                match &value {
                    AttributeValue::Float(_) => {}, // explicit beam width
                    AttributeValue::Keyword(kw) => match kw.as_str() {
                        "none" | "disabled" => {}, // beam pruning disabled
                        "auto" => {},              // auto-select from trained model
                        _ => {
                            return Err(syn::Error::new(
                                key_ident.span(),
                                format!(
                                    "beam_width: invalid keyword '{}'. \
                                     Use a float (e.g., 1.5), 'none', 'disabled', or 'auto'",
                                    kw
                                ),
                            ));
                        },
                    },
                    _ => {
                        return Err(syn::Error::new(
                            key_ident.span(),
                            "beam_width must be a float (e.g., 1.5), 'none', 'disabled', or 'auto'",
                        ));
                    },
                }
            },
            "log_semiring_model_path" => {
                if !matches!(&value, AttributeValue::Str(_)) {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "log_semiring_model_path must be a string path (e.g., log_semiring_model_path: \"model.json\")",
                    ));
                }
            },
            "dispatch" => match &value {
                AttributeValue::Keyword(kw) => match kw.as_str() {
                    "static" | "weighted" | "auto" => {},
                    _ => {
                        return Err(syn::Error::new(
                            key_ident.span(),
                            format!(
                                "dispatch: invalid keyword '{}'. \
                                     Use 'static', 'weighted', or 'auto'",
                                kw
                            ),
                        ));
                    },
                },
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "dispatch must be a keyword: 'static', 'weighted', or 'auto'",
                    ));
                },
            },
            "emit_tests" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_tests must be a boolean (true or false)",
                    ));
                },
            },
            "emit_blockly" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_blockly must be a boolean (true or false)",
                    ));
                },
            },
            "emit_simulator" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_simulator must be a boolean (true or false)",
                    ));
                },
            },
            // L11 (2026-04-28): case_insensitive triggers ASCII case-folding
            // in NFA construction. Non-ASCII case folding requires per-locale
            // tables (Turkish dotless i, German ß) and emits compile_error!
            // when the grammar references non-ASCII keywords with
            // case_insensitive: true.
            "case_insensitive" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "case_insensitive must be a boolean (true or false)",
                    ));
                },
            },
            // L11 (2026-04-28): unicode_normalization runs a pre-pass on
            // input bytes before lexing. Accepts NFC, NFD, NFKC, NFKD, or
            // 'none' (the default).
            "unicode_normalization" => match &value {
                AttributeValue::Keyword(kw) => match kw.as_str() {
                    "NFC" | "NFD" | "NFKC" | "NFKD" | "none" => {},
                    _ => {
                        return Err(syn::Error::new(
                            key_ident.span(),
                            format!(
                                "unicode_normalization: invalid keyword '{}'. \
                                 Use 'NFC', 'NFD', 'NFKC', 'NFKD', or 'none'",
                                kw
                            ),
                        ));
                    },
                },
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "unicode_normalization must be a keyword: 'NFC', 'NFD', 'NFKC', 'NFKD', or 'none'",
                    ));
                },
            },
            unknown => {
                return Err(syn::Error::new(
                    key_ident.span(),
                    format!(
                        "unknown option '{}'. Valid options are: beam_width, log_semiring_model_path, dispatch, emit_tests, emit_blockly, emit_simulator, case_insensitive, unicode_normalization",
                        unknown
                    ),
                ));
            },
        }

        options.insert(key, value);

        // Optional trailing comma
        if content.peek(Token![,]) {
            let _ = content.parse::<Token![,]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(options)
}

fn parse_equations(input: ParseStream) -> SynResult<Vec<Equation>> {
    let eq_ident = input.parse::<Ident>()?;
    if eq_ident != "equations" {
        return Err(syn::Error::new(eq_ident.span(), "expected 'equations'"));
    }

    let content;
    syn::braced!(content in input);

    let mut equations = Vec::new();
    while !content.is_empty() {
        equations.push(parse_equation(&content)?);
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(equations)
}

/// Parse a single premise in the propositional context
/// Grammar: freshness | congruence | relation_query | forall
///   freshness  ::= ident "#" (ident | "..." ident)
///   congruence ::= ident "~>" ident
///   relation   ::= ident "(" (ident ("," ident)*)? ")"
///   forall     ::= ident "." "*" "map" "(" "|" ident "|" premise ")"
fn parse_premise(input: ParseStream) -> SynResult<Premise> {
    let first = input.parse::<Ident>()?;

    if input.peek(Token![#]) {
        // Freshness: x # target
        let _ = input.parse::<Token![#]>()?;
        let term = if input.peek(Token![...]) {
            let _ = input.parse::<Token![...]>()?;
            FreshnessTarget::CollectionRest(input.parse::<Ident>()?)
        } else {
            FreshnessTarget::Var(input.parse::<Ident>()?)
        };
        Ok(Premise::Freshness(FreshnessCondition { var: first, term }))
    } else if input.peek(Token![~]) && input.peek2(Token![>]) {
        // Congruence: S ~> T
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![>]>()?;
        let target = input.parse::<Ident>()?;
        Ok(Premise::Congruence { source: first, target })
    } else if input.peek(syn::token::Paren) {
        // Relation query: rel(args)
        let args_content;
        syn::parenthesized!(args_content in input);
        let mut args = Vec::new();
        while !args_content.is_empty() {
            args.push(args_content.parse::<Ident>()?);
            if args_content.peek(Token![,]) {
                let _ = args_content.parse::<Token![,]>()?;
            }
        }
        Ok(Premise::RelationQuery { relation: first, args })
    } else if input.peek(Token![.]) {
        // ForAll: xs.*map(|x| premise)
        let _ = input.parse::<Token![.]>()?;
        let _ = input.parse::<Token![*]>()?;
        let op = input.parse::<Ident>()?;
        if op != "map" {
            return Err(syn::Error::new(
                op.span(),
                "expected 'map' in quantified premise (xs.*map(|x| ...))",
            ));
        }
        let content;
        syn::parenthesized!(content in input);
        let _ = content.parse::<Token![|]>()?;
        let param = content.parse::<Ident>()?;
        let _ = content.parse::<Token![|]>()?;
        let body = parse_premise(&content)?;
        Ok(Premise::ForAll {
            collection: first,
            param,
            body: Box::new(body),
        })
    } else if first == "guard" && input.peek(syn::token::Paren) {
        // Behavioral guard premise: guard(pred_expr)
        let content;
        syn::parenthesized!(content in input);
        let pred = parse_behavioral_pred(&content)?;
        Ok(Premise::BehavioralGuard(pred))
    } else if first == "forall" || first == "exists" {
        // Quantified behavioral guard used directly as premise:
        // forall var in domain. body  /  exists var in domain. body
        let quantifier = if first == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let var = input.parse::<Ident>()?;

        // Optional bound: _{k=N}
        let bound = if input.peek(Token![_]) {
            let _ = input.parse::<Token![_]>()?;
            let bound_content;
            syn::braced!(bound_content in input);
            // Parse k=N inside braces
            let _k = bound_content.parse::<Ident>()?;
            let _ = bound_content.parse::<Token![=]>()?;
            let n: syn::LitInt = bound_content.parse()?;
            Some(n.base10_parse::<usize>()?)
        } else {
            None
        };

        // Optional domain: "in" relation_name
        let domain = if input.peek(Token![in]) {
            let _ = input.parse::<Token![in]>()?;
            Some(input.parse::<Ident>()?)
        } else {
            None
        };

        // "." separates quantifier header from body
        let _ = input.parse::<Token![.]>()?;
        let body = parse_behavioral_pred(input)?;

        Ok(Premise::BehavioralGuard(BehavioralPred::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        }))
    } else {
        Err(syn::Error::new(
            first.span(),
            "expected premise: 'x # term', 'S ~> T', 'rel(args)', 'guard(...)', \
             'forall ...', 'exists ...', or 'xs.*map(|x| ...)'",
        ))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Behavioral predicate parser — sublanguage for quantified guards
// ══════════════════════════════════════════════════════════════════════════════
//
// The parser chain (`parse_behavioral_pred` → `parse_pred_implies` → ... →
// `parse_pred_atom`) recognizes a fixed set of Rust tokens by default
// (`&&`, `||`, `~`, `!`, `=>`, plus the `forall`/`exists` identifiers).
// When the language declares a `guards { connectives { } }` sub-block,
// those defaults are augmented (not replaced) by the declared keywords:
// the parser also accepts each declared keyword as the corresponding
// connective. The active map is held in a thread-local so the parser
// functions need no signature changes — proc-macro expansion is
// single-threaded per crate, so the thread-local is safe.

thread_local! {
    /// Active ConnectiveMap during parsing of a `language!` invocation.
    /// Populated at the start of `Parse for LanguageDef` after `guards {}`
    /// is parsed; cleared on exit. Default `None` means: use only the
    /// hardcoded Rust-token connectives.
    static ACTIVE_CONNECTIVE_MAP: std::cell::RefCell<Option<ConnectiveMap>> =
        const { std::cell::RefCell::new(None) };
}

/// RAII guard that installs a `ConnectiveMap` into `ACTIVE_CONNECTIVE_MAP`
/// for the lifetime of the guard, restoring the previous value on drop.
///
/// This is used by `Parse for LanguageDef` to scope the active map to the
/// remainder of the parse after `guards {}` has been processed. Drop order
/// guarantees the previous value is restored even on early return / parse
/// errors / panics.
struct ConnectiveMapGuard {
    previous: Option<ConnectiveMap>,
}

impl ConnectiveMapGuard {
    /// Install `map` into the thread-local; the previous value is saved
    /// in the returned guard and restored on drop.
    fn install(map: Option<ConnectiveMap>) -> Self {
        let previous = ACTIVE_CONNECTIVE_MAP.with(|cell| cell.borrow_mut().take());
        ACTIVE_CONNECTIVE_MAP.with(|cell| {
            *cell.borrow_mut() = map;
        });
        ConnectiveMapGuard { previous }
    }
}

impl Drop for ConnectiveMapGuard {
    fn drop(&mut self) {
        ACTIVE_CONNECTIVE_MAP.with(|cell| {
            *cell.borrow_mut() = self.previous.take();
        });
    }
}

/// Look up the role of a connective keyword in the active map. Returns
/// `None` if no map is active or the keyword is not declared.
fn active_role_of(keyword: &str) -> Option<ConnectiveRole> {
    ACTIVE_CONNECTIVE_MAP.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|map| map.role_of(keyword).cloned())
    })
}

/// Whether the active map declares any keyword for the given role.
fn active_role_available(role: &ConnectiveRole) -> bool {
    ACTIVE_CONNECTIVE_MAP.with(|cell| {
        cell.borrow()
            .as_ref()
            .map(|map| map.role_available(role))
            .unwrap_or(false)
    })
}

/// Whether the active map exists (i.e., a `connectives {}` block was declared).
fn has_active_connective_map() -> bool {
    ACTIVE_CONNECTIVE_MAP.with(|cell| cell.borrow().is_some())
}

/// Whether a hardcoded Rust connective token (e.g., `&&`, `||`, `~`) is
/// allowed by the active `ConnectiveMap`.
///
/// Backward compatibility (no map active): always allowed. With an
/// active map: only allowed if the role is also declared in the map.
/// This implements the closed-world semantics described in design doc
/// §2A "Connective Parser Integration".
///
/// Layer D cleanup: when a language declares `connectives { and = "&&"; }`
/// but omits `or`, the `||` Rust token is rejected with CONN02 even though
/// `||` is "obviously" disjunction in Rust syntax. The grammar author opted
/// out of disjunction in their guard sublanguage; the parser respects that.
fn rust_token_allowed(role: ConnectiveRole) -> bool {
    if !has_active_connective_map() {
        return true;
    }
    active_role_available(&role)
}

/// Peek-and-consume any identifier in the active map that has the given role.
///
/// Returns `true` (and consumes the token) if successful; `false` otherwise.
fn try_consume_role_keyword(input: ParseStream, role: ConnectiveRole) -> bool {
    if !has_active_connective_map() {
        return false;
    }
    if !active_role_available(&role) {
        return false;
    }
    if !input.peek(Ident::peek_any) {
        return false;
    }
    // Peek the identifier without consuming
    let fork = input.fork();
    let id_result = fork.parse::<Ident>();
    if let Ok(id) = id_result {
        if let Some(kw_role) = active_role_of(&id.to_string()) {
            if kw_role == role {
                // Now actually consume from the real input
                let _ = input.parse::<Ident>();
                return true;
            }
        }
    }
    false
}

/// Parse a behavioral predicate expression (implication level).
///
/// Grammar (precedence low→high):
/// ```text
/// pred_implies  ::= pred_or ("=>" pred_implies)?
/// pred_or       ::= pred_and ("||" pred_and)*
/// pred_and      ::= pred_not ("&&" pred_not)*
/// pred_not      ::= "~" pred_atom | "!" pred_atom | pred_atom
/// pred_atom     ::= quantified | relation_query | "(" pred_implies ")"
/// quantified    ::= ("forall" | "exists") ident [bound] ["in" ident] "." pred_implies
/// bound         ::= "_{" ident "=" lit_int "}"
/// relation_query::= ident "(" (pred_arg ("," pred_arg)*)? ")"
/// pred_arg      ::= ident
/// ```
///
/// Default mode (no `connectives { }` block): `&&` for conjunction, `||`
/// for disjunction, `~`/`!` for negation, `=>` for implication. All valid
/// Rust tokens parseable by proc_macro2.
///
/// Closed-world mode (`connectives { }` declared): the active map's
/// declared keywords are recognized in addition to whichever Rust tokens
/// happen to correspond to declared roles. If the parse leaves a
/// hardcoded Rust connective token unconsumed, CONN02 fires — the user
/// opted out of that role and trying to use the Rust spelling is an error.
fn parse_behavioral_pred(input: ParseStream) -> SynResult<BehavioralPred> {
    let result = parse_pred_implies(input)?;
    check_conn02_unlisted_token(input)?;
    Ok(result)
}

/// Layer D cleanup: when an active `ConnectiveMap` is present, scan the
/// remaining input for stranded forbidden Rust connective tokens and emit
/// CONN02 if any is found.
///
/// This runs at the *trailing edge* of `parse_behavioral_pred`. By that
/// point, all tokens that the parser was willing to consume have been
/// consumed. Any leftover Rust connective is one the user wrote but the
/// active map does not declare.
fn check_conn02_unlisted_token(input: ParseStream) -> SynResult<()> {
    if !has_active_connective_map() {
        return Ok(());
    }
    if input.peek(Token![&&]) && !active_role_available(&ConnectiveRole::And) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `&&` (role `and`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![||]) && !active_role_available(&ConnectiveRole::Or) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `||` (role `or`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![~]) && !active_role_available(&ConnectiveRole::Not) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `~` (role `not`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![!]) && !active_role_available(&ConnectiveRole::Not) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `!` (role `not`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![=>]) && !active_role_available(&ConnectiveRole::Entails) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `=>` (role `entails`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    Ok(())
}

/// Implication (right-associative, lowest precedence).
fn parse_pred_implies(input: ParseStream) -> SynResult<BehavioralPred> {
    let lhs = parse_pred_or(input)?;

    // Check for "=>" (fat arrow — implication).
    // Only consume `=>` if either no connective map is active or the
    // active map declares `Entails` — otherwise CONN02 closed-world semantics.
    if input.peek(Token![=>]) && rust_token_allowed(ConnectiveRole::Entails) {
        let _ = input.parse::<Token![=>]>()?;
        let rhs = parse_pred_implies(input)?; // right-associative
        return Ok(BehavioralPred::Implies(Box::new(lhs), Box::new(rhs)));
    }

    // Custom keyword (e.g., `entails`, `implies`) from `connectives {}`.
    if try_consume_role_keyword(input, ConnectiveRole::Entails) {
        let rhs = parse_pred_implies(input)?; // right-associative
        return Ok(BehavioralPred::Implies(Box::new(lhs), Box::new(rhs)));
    }
    if try_consume_role_keyword(input, ConnectiveRole::ImpliedBy) {
        // Reverse implication: a implied_by b ≡ b => a
        let rhs = parse_pred_implies(input)?;
        return Ok(BehavioralPred::Implies(Box::new(rhs), Box::new(lhs)));
    }
    if try_consume_role_keyword(input, ConnectiveRole::Iff) {
        // Biconditional: a iff b ≡ (a => b) ∧ (b => a)
        let rhs = parse_pred_implies(input)?;
        let forward = BehavioralPred::Implies(Box::new(lhs.clone()), Box::new(rhs.clone()));
        let backward = BehavioralPred::Implies(Box::new(rhs), Box::new(lhs));
        return Ok(BehavioralPred::And(Box::new(forward), Box::new(backward)));
    }

    Ok(lhs)
}

/// Disjunction (`||` or declared `or` keyword).
///
/// Layer D cleanup: when an active `ConnectiveMap` is present, the
/// hardcoded `||` token is only accepted if the map also declares the
/// `Or` role. Otherwise the parser breaks the loop and the unconsumed
/// `||` later triggers a CONN02 diagnostic in `parse_behavioral_pred`.
fn parse_pred_or(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_and(input)?;

    loop {
        if input.peek(Token![||]) && rust_token_allowed(ConnectiveRole::Or) {
            let _ = input.parse::<Token![||]>()?;
        } else if try_consume_role_keyword(input, ConnectiveRole::Or) {
            // consumed
        } else {
            break;
        }
        let rhs = parse_pred_and(input)?;
        result = BehavioralPred::Or(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Conjunction (`&&` or declared `and` keyword).
///
/// Layer D cleanup: see `parse_pred_or` for the closed-world rationale.
fn parse_pred_and(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_not(input)?;

    loop {
        if input.peek(Token![&&]) && rust_token_allowed(ConnectiveRole::And) {
            let _ = input.parse::<Token![&&]>()?;
        } else if try_consume_role_keyword(input, ConnectiveRole::And) {
            // consumed
        } else {
            break;
        }
        let rhs = parse_pred_not(input)?;
        result = BehavioralPred::And(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Negation (`~`, `!`, or declared `not` keyword).
///
/// Layer D cleanup: when an active `ConnectiveMap` omits `Not`, the
/// hardcoded `~` and `!` tokens are not consumed; they later trigger a
/// CONN02 diagnostic in `parse_behavioral_pred`.
fn parse_pred_not(input: ParseStream) -> SynResult<BehavioralPred> {
    if input.peek(Token![~]) && rust_token_allowed(ConnectiveRole::Not) {
        let _ = input.parse::<Token![~]>()?;
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else if input.peek(Token![!]) && rust_token_allowed(ConnectiveRole::Not) {
        let _ = input.parse::<Token![!]>()?;
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else if try_consume_role_keyword(input, ConnectiveRole::Not) {
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else {
        parse_pred_atom(input)
    }
}

/// Atomic predicate: relation query, quantifier, or parenthesized expression.
fn parse_pred_atom(input: ParseStream) -> SynResult<BehavioralPred> {
    // Parenthesized subexpression
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        return parse_behavioral_pred(&content);
    }

    let ident = input.parse::<Ident>()?;

    // AC-match: ac_match(bag, {x, y, ...rest})
    if ident == "ac_match" {
        let content;
        syn::parenthesized!(content in input);
        let bag = content.parse::<Ident>()?;
        let _ = content.parse::<Token![,]>()?;

        // Parse the element set: { x, y, ...rest }
        let set_content;
        syn::braced!(set_content in content);
        let mut elements = Vec::new();
        let mut rest = None;

        while !set_content.is_empty() {
            // Check for "..." (rest pattern)
            if set_content.peek(Token![...]) {
                let _ = set_content.parse::<Token![...]>()?;
                rest = Some(set_content.parse::<Ident>()?);
                // Trailing comma is optional after rest
                if set_content.peek(Token![,]) {
                    let _ = set_content.parse::<Token![,]>()?;
                }
                break;
            }

            elements.push(set_content.parse::<Ident>()?);
            if set_content.peek(Token![,]) {
                let _ = set_content.parse::<Token![,]>()?;
            }
        }

        if elements.is_empty() {
            return Err(syn::Error::new(
                ident.span(),
                "ac_match requires at least one element variable",
            ));
        }

        return Ok(BehavioralPred::AcMatch { bag, elements, rest });
    }

    // Quantifier: forall/exists var [bound] [in domain]. body
    if ident == "forall" || ident == "exists" {
        let quantifier = if ident == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let var = input.parse::<Ident>()?;

        // Optional bound: _{k=N}
        let bound = if input.peek(Token![_]) {
            let _ = input.parse::<Token![_]>()?;
            let bound_content;
            syn::braced!(bound_content in input);
            let _k = bound_content.parse::<Ident>()?;
            let _ = bound_content.parse::<Token![=]>()?;
            let n: syn::LitInt = bound_content.parse()?;
            Some(n.base10_parse::<usize>()?)
        } else {
            None
        };

        // Optional domain: "in" relation_name
        let domain = if input.peek(Token![in]) {
            let _ = input.parse::<Token![in]>()?;
            Some(input.parse::<Ident>()?)
        } else {
            None
        };

        let _ = input.parse::<Token![.]>()?;
        let body = parse_behavioral_pred(input)?;

        return Ok(BehavioralPred::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }

    // Relation query: rel(args...)
    if input.peek(syn::token::Paren) {
        let args_content;
        syn::parenthesized!(args_content in input);
        let mut args = Vec::new();
        while !args_content.is_empty() {
            let arg = args_content.parse::<Ident>()?;
            // Lowercase first char → variable, uppercase → constant
            if arg.to_string().starts_with(|c: char| c.is_uppercase()) {
                args.push(PredArg::Constant(arg));
            } else {
                args.push(PredArg::Var(arg));
            }
            if args_content.peek(Token![,]) {
                let _ = args_content.parse::<Token![,]>()?;
            }
        }
        return Ok(BehavioralPred::RelationQuery {
            relation_name: ident,
            args,
            negated: false,
        });
    }

    // Bare identifier as nullary relation query (no args)
    Ok(BehavioralPred::RelationQuery {
        relation_name: ident,
        args: vec![],
        negated: false,
    })
}

/// Parse a typed parameter: name:Type
fn parse_typed_param(input: ParseStream) -> SynResult<TypedParam> {
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![:]>()?;
    let ty = input.parse::<super::types::TypeExpr>()?;
    Ok(TypedParam { name, ty })
}

/// Parse rule contexts in judgement form:
///   type_context | prop_context |-
///
/// Grammar:
///   contexts   ::= type_ctx? ("|" prop_ctx)? "|-"
///   type_ctx   ::= typed_param ("," typed_param)*
///   prop_ctx   ::= premise ("," premise)*
fn parse_rule_contexts(input: ParseStream) -> SynResult<(Vec<TypedParam>, Vec<Premise>)> {
    let mut type_context = Vec::new();
    let mut premises = Vec::new();

    let mut in_prop_context = false;

    loop {
        // Check for "|-" (end of contexts)
        if input.peek(Token![|]) && input.peek2(Token![-]) {
            break;
        }

        // Check for "|" (separator between type and prop contexts)
        if input.peek(Token![|]) && !input.peek2(Token![-]) {
            let _ = input.parse::<Token![|]>()?;
            in_prop_context = true;
            continue;
        }

        if in_prop_context {
            // Parse premise
            premises.push(parse_premise(input)?);
        } else {
            // Could be type_ctx param OR first premise (if no explicit type_ctx)
            // Disambiguate: type param has ":" after name, premise has "#", "~>", or "("
            let fork = input.fork();
            let _ = fork.parse::<Ident>()?;

            if fork.peek(Token![:]) && !fork.peek(Token![::]) {
                // Type parameter: name:Type
                type_context.push(parse_typed_param(input)?);
            } else {
                // Not a type param, switch to prop_context
                in_prop_context = true;
                premises.push(parse_premise(input)?);
            }
        }

        // Check for comma (more items) or end
        if input.peek(Token![,]) {
            let _ = input.parse::<Token![,]>()?;
        } else {
            break;
        }
    }

    // Consume "|-"
    if input.peek(Token![|]) && input.peek2(Token![-]) {
        let _ = input.parse::<Token![|]>()?;
        let _ = input.parse::<Token![-]>()?;
    } else {
        return Err(input.error("expected '|-' after contexts"));
    }

    Ok((type_context, premises))
}

fn parse_equation(input: ParseStream) -> SynResult<Equation> {
    // Parse: Name .
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;

    // Parse contexts and turnstile
    let (type_context, premises) = parse_rule_contexts(input)?;

    // Parse left-hand side as pattern
    let left = parse_pattern(input)?;

    // Parse =
    let _ = input.parse::<Token![=]>()?;

    // Parse right-hand side as pattern (symmetric with LHS)
    let right = parse_pattern(input)?;

    // Parse semicolon
    let _ = input.parse::<Token![;]>()?;

    Ok(Equation {
        name,
        type_context,
        premises,
        left,
        right,
    })
}

/// Parse a pattern (for LHS and RHS of rules)
/// Returns Pattern which can include Collection for {P, Q, ...rest} patterns
/// and nested patterns in constructor arguments
pub fn parse_pattern(input: ParseStream) -> SynResult<Pattern> {
    // Parse #zip or #map metasyntax: #zip(a, b) or #map(coll, |x| body)
    if input.peek(Token![*]) {
        return parse_metasyntax_pattern(input);
    }

    // Parse collection pattern: {P, Q, ...rest}
    if input.peek(syn::token::Brace) {
        let content;
        syn::braced!(content in input);

        let mut elements = Vec::new();
        let mut rest = None;

        // Parse elements and optional rest
        while !content.is_empty() {
            // Check for rest pattern: ...rest
            if content.peek(Token![...]) {
                let _ = content.parse::<Token![...]>()?;
                rest = Some(content.parse::<Ident>()?);

                // Optional trailing comma
                if content.peek(Token![,]) {
                    let _ = content.parse::<Token![,]>()?;
                }
                break;
            }

            // Parse regular element as a nested pattern
            elements.push(parse_pattern(&content)?);

            // Parse comma separator
            if content.peek(Token![,]) {
                let _ = content.parse::<Token![,]>()?;
            } else {
                break;
            }
        }

        return Ok(Pattern::Collection {
            coll_type: None, // Inferred from enclosing constructor's grammar
            elements,
            rest,
        });
    }

    // Parse parenthesized constructor pattern or just wrap expression
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);

        // Parse constructor name (or special keywords like 'subst', 'multisubst')
        let constructor = content.parse::<Ident>()?;

        // Check if this is a substitution (beta reduction)
        // New unified syntax: (subst lamterm repl) where lamterm is ^x.body or ^[xs].body or a variable
        // Old syntax (backward compat): (eval term var repl)
        if constructor == "eval" {
            let first = parse_pattern(&content)?;

            if content.is_empty() {
                return Err(syn::Error::new(
                    constructor.span(),
                    "eval requires at least 2 arguments",
                ));
            }

            let second = parse_pattern(&content)?;

            if content.is_empty() {
                // New syntax: (subst lamterm repl) - 2 args
                // lamterm can be ^x.body (Lambda), ^[xs].body (MultiLambda), or a variable
                match &first {
                    Pattern::Term(PatternTerm::Lambda { binder, body }) => {
                        // Single lambda: extract binder and body for Subst
                        return Ok(Pattern::Term(PatternTerm::Subst {
                            term: body.clone(),
                            var: binder.clone(),
                            replacement: Box::new(second),
                        }));
                    },
                    Pattern::Term(PatternTerm::MultiLambda { .. }) => {
                        // Multi-lambda: use MultiSubst with single replacement (will be collection)
                        return Ok(Pattern::Term(PatternTerm::MultiSubst {
                            scope: Box::new(first),
                            replacements: vec![second],
                        }));
                    },
                    _ => {
                        // Variable or other pattern: treat as scope, use MultiSubst
                        // This handles both single and multi at runtime via unbind
                        return Ok(Pattern::Term(PatternTerm::MultiSubst {
                            scope: Box::new(first),
                            replacements: vec![second],
                        }));
                    },
                }
            } else {
                // Old syntax: (subst term var repl) - 3 args (backward compatibility)
                let var = match &second {
                    Pattern::Term(PatternTerm::Var(v)) => v.clone(),
                    _ => return Err(syn::Error::new(
                        constructor.span(),
                        "In 3-arg eval syntax (subst term var repl), second argument must be a variable name"
                    )),
                };
                let replacement = parse_pattern(&content)?;

                if !content.is_empty() {
                    return Err(syn::Error::new(constructor.span(), "eval takes 2 or 3 arguments"));
                }

                return Ok(Pattern::Term(PatternTerm::Subst {
                    term: Box::new(first),
                    var,
                    replacement: Box::new(replacement),
                }));
            }
        }

        // Parse arguments as nested patterns
        // NOTE: Collections inside Apply are handled correctly - the Apply knows
        // its constructor and can look up the collection type from grammar
        let mut args = Vec::new();
        while !content.is_empty() {
            args.push(parse_pattern(&content)?);
        }

        // Create Apply PatternTerm with Pattern args
        Ok(Pattern::Term(PatternTerm::Apply { constructor, args }))
    } else if input.peek(Token![^]) {
        // Lambda patterns - parse directly to support collections in body
        input.parse::<Token![^]>()?;

        // Check for multi-binder: ^[x0, x1, ...].body
        if input.peek(syn::token::Bracket) {
            let content;
            syn::bracketed!(content in input);

            // Parse comma-separated list of binders
            let binders: syn::punctuated::Punctuated<Ident, Token![,]> =
                content.parse_terminated(Ident::parse, Token![,])?;
            let binders: Vec<Ident> = binders.into_iter().collect();

            // Expect dot
            input.parse::<Token![.]>()?;

            // Parse body as pattern (supports collections)
            let body = parse_pattern(input)?;

            return Ok(Pattern::Term(PatternTerm::MultiLambda { binders, body: Box::new(body) }));
        }

        // Single binder: ^x.body
        let binder = input.parse::<Ident>()?;
        input.parse::<Token![.]>()?;
        let body = parse_pattern(input)?;

        Ok(Pattern::Term(PatternTerm::Lambda { binder, body: Box::new(body) }))
    } else {
        // Just a variable - but check for chained metasyntax like `var.#map(...)`
        let var = input.parse::<Ident>()?;
        let base = Pattern::Term(PatternTerm::Var(var));

        // Check for chained method-style metasyntax: var.#map(...)
        if input.peek(Token![.]) && input.peek2(Token![*]) {
            return parse_chained_metasyntax(input, base);
        }

        Ok(base)
    }
}

/// Parse metasyntax patterns: #zip(a, b), #map(coll, |x| body), etc.
fn parse_metasyntax_pattern(input: ParseStream) -> SynResult<Pattern> {
    input.parse::<Token![*]>()?;
    let op_name = input.parse::<Ident>()?;
    let op_str = op_name.to_string();

    match op_str.as_str() {
        "zip" => {
            // #zip(coll1, coll2)
            let content;
            syn::parenthesized!(content in input);

            let coll1 = parse_pattern(&content)?;
            content.parse::<Token![,]>()?;
            let coll2 = parse_pattern(&content)?;

            let base = Pattern::Zip {
                first: Box::new(coll1),
                second: Box::new(coll2),
            };

            // Check for chained metasyntax: #zip(a, b).#map(|x, y| ...)
            if input.peek(Token![.]) && input.peek2(Token![*]) {
                parse_chained_metasyntax(input, base)
            } else {
                Ok(base)
            }
        },
        "map" => {
            // #map(coll, |params| body) - prefix form
            let content;
            syn::parenthesized!(content in input);

            let collection = parse_pattern(&content)?;
            content.parse::<Token![,]>()?;

            // Parse closure: |params| body
            let (params, body) = parse_closure(&content)?;

            Ok(Pattern::Map {
                collection: Box::new(collection),
                params,
                body: Box::new(body),
            })
        },
        _ => Err(syn::Error::new(
            op_name.span(),
            format!("Unknown metasyntax operator: #{}", op_str),
        )),
    }
}

/// Parse chained method-style metasyntax: base.#map(|x| body)
fn parse_chained_metasyntax(input: ParseStream, base: Pattern) -> SynResult<Pattern> {
    input.parse::<Token![.]>()?;
    input.parse::<Token![*]>()?;
    let op_name = input.parse::<Ident>()?;
    let op_str = op_name.to_string();

    match op_str.as_str() {
        "map" => {
            // base.#map(|params| body)
            let content;
            syn::parenthesized!(content in input);

            let (params, body) = parse_closure(&content)?;

            let result = Pattern::Map {
                collection: Box::new(base),
                params,
                body: Box::new(body),
            };

            // Check for more chaining
            if input.peek(Token![.]) && input.peek2(Token![*]) {
                parse_chained_metasyntax(input, result)
            } else {
                Ok(result)
            }
        },
        "zip" => {
            // base.#zip(other) - less common but supported
            let content;
            syn::parenthesized!(content in input);

            let other = parse_pattern(&content)?;

            let result = Pattern::Zip {
                first: Box::new(base),
                second: Box::new(other),
            };

            if input.peek(Token![.]) && input.peek2(Token![*]) {
                parse_chained_metasyntax(input, result)
            } else {
                Ok(result)
            }
        },
        _ => Err(syn::Error::new(
            op_name.span(),
            format!("Unknown chained metasyntax operator: #{}", op_str),
        )),
    }
}

/// Parse a closure: |params| body or |param1, param2| body
fn parse_closure(input: ParseStream) -> SynResult<(Vec<Ident>, Pattern)> {
    input.parse::<Token![|]>()?;

    // Parse comma-separated params
    let mut params = Vec::new();
    while !input.peek(Token![|]) {
        params.push(input.parse::<Ident>()?);
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
        } else {
            break;
        }
    }

    input.parse::<Token![|]>()?;

    // Parse body as pattern
    let body = parse_pattern(input)?;

    Ok((params, body))
}

fn parse_rewrites(input: ParseStream) -> SynResult<Vec<RewriteRule>> {
    let rewrites_ident = input.parse::<Ident>()?;
    if rewrites_ident != "rewrites" {
        return Err(syn::Error::new(rewrites_ident.span(), "expected 'rewrites'"));
    }

    let content;
    syn::braced!(content in input);

    let mut rewrites = Vec::new();
    while !content.is_empty() {
        // Skip comments (// ...)
        while content.peek(Token![/]) && content.peek2(Token![/]) {
            let _ = content.parse::<Token![/]>()?;
            let _ = content.parse::<Token![/]>()?;
            // Skip until end of line - consume tokens until we see an identifier (rule name)
            while !content.is_empty() && !content.peek(Ident) {
                let _ = content.parse::<proc_macro2::TokenTree>()?;
            }
        }

        if content.is_empty() {
            break;
        }

        rewrites.push(parse_rewrite_rule(&content)?);
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(rewrites)
}

fn parse_rewrite_rule(input: ParseStream) -> SynResult<RewriteRule> {
    // Parse: Name .
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;

    // Parse contexts and turnstile
    let (type_context, premises) = parse_rule_contexts(input)?;

    // Parse left-hand side pattern
    let left = parse_pattern(input)?;

    // Parse ~>
    let _ = input.parse::<Token![~]>()?;
    let _ = input.parse::<Token![>]>()?;

    // Parse right-hand side as pattern (can use metasyntax)
    let right = parse_pattern(input)?;

    // Optional semicolon
    if input.peek(Token![;]) {
        let _ = input.parse::<Token![;]>()?;
    }

    Ok(RewriteRule {
        name,
        type_context,
        premises,
        left,
        right,
        is_auto_injected: false,
    })
}

/// Parse logic block: custom Ascent relations and rules
/// Syntax: logic { <ascent-syntax> }
///
/// Extracts relation declarations for code generation while keeping
/// the full content as verbatim TokenStream for Ascent.
fn parse_logic(input: ParseStream) -> SynResult<LogicBlock> {
    let logic_ident = input.parse::<Ident>()?;
    if logic_ident != "logic" {
        return Err(syn::Error::new(logic_ident.span(), "expected 'logic'"));
    }

    let content;
    syn::braced!(content in input);

    // Capture the entire content as a TokenStream (passed through verbatim to Ascent)
    let tokens: TokenStream = content.parse()?;

    // Parse as an Ascent program to extract relation declarations with proper type handling
    let program = ascent_syntax_export::parse_ascent_program_tokens(tokens.clone())?;
    let relations = program
        .relations
        .into_iter()
        .map(|rel| {
            let param_types = rel
                .field_types
                .iter()
                .map(|ty| quote::quote!(#ty).to_string())
                .collect();
            // Stage 3.27a (2026-05-04): doc_comment is None for now —
            // ascent_syntax_export does not surface relation-level doc
            // comments. Future: extend ascent_syntax_export to capture
            // and forward `#[doc = "..."]` attributes per relation.
            RelationDecl {
                name: rel.name,
                param_types,
                doc_comment: None,
            }
        })
        .collect();

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(LogicBlock { relations, content: tokens })
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 1 smoke tests for `parse_guards()` (design doc §2A)
// ══════════════════════════════════════════════════════════════════════════════
//
// These tests verify the parser can handle the four sub-block forms (direct
// predicates, connectives, theories, channels) plus annotations and the
// variadic/typed parameter forms. Comprehensive tests live in Phase 9.

#[cfg(test)]
mod guards_parse_tests {
    use super::*;
    use syn::parse2;

    fn parse_lang(src: proc_macro2::TokenStream) -> LanguageDef {
        parse2::<LanguageDef>(src).expect("language parse failed")
    }

    #[test]
    fn empty_guards_block_parses() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards { },
            terms { }
        });
        assert!(lang.guard_config.is_some());
        let gc = lang.guard_config.as_ref().expect("just checked");
        assert!(gc.builtin_predicates.is_none(), "no direct items → None");
        assert!(gc.connectives.is_none());
        assert!(gc.theories.is_empty());
        assert!(gc.channels.is_none());
    }

    #[test]
    fn guards_block_absent() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            terms { }
        });
        assert!(lang.guard_config.is_none(), "absent block → None");
    }

    #[test]
    fn parse_simple_predicate_decl() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                eq . x, y |- x "==" y ;
            },
            terms { }
        });
        let gc = lang.guard_config.as_ref().expect("present");
        let preds = gc.builtin_predicates.as_ref().expect("explicit predicates");
        assert_eq!(preds.len(), 1);
        let p = &preds[0];
        assert_eq!(p.name.to_string(), "eq");
        assert_eq!(p.params.len(), 2);
        assert_eq!(p.params[0].name.to_string(), "x");
        assert_eq!(p.params[1].name.to_string(), "y");
        assert_eq!(p.syntax_forms.len(), 1);
    }

    #[test]
    fn parse_alternative_syntax_forms() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                gt . x, y |- x ">" y | "gt" "(" x "," y ")" ;
            },
            terms { }
        });
        let gc = lang.guard_config.as_ref().expect("present");
        let preds = gc.builtin_predicates.as_ref().expect("explicit");
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0].syntax_forms.len(), 2);
    }

    #[test]
    fn parse_annotations() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                eq . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
            },
            terms { }
        });
        let gc = lang.guard_config.as_ref().expect("present");
        let preds = gc.builtin_predicates.as_ref().expect("explicit");
        let p = &preds[0];
        assert_eq!(p.annotations.selectivity, Some(0.1));
        assert_eq!(p.annotations.cost, Some(2));
    }

    #[test]
    fn parse_variadic_params() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                eq_chain . xs+ |- "==" "(" xs ")" ;
                opt . xs* |- "opt" "(" xs ")" ;
                bounded . xs{2,5} |- "b" "(" xs ")" ;
            },
            terms { }
        });
        let preds = lang
            .guard_config
            .as_ref()
            .expect("present")
            .builtin_predicates
            .as_ref()
            .expect("explicit");
        assert_eq!(preds.len(), 3);
        assert_eq!(preds[0].params[0].quantifier, Some(ParamQuantifier::OneOrMore));
        assert_eq!(preds[1].params[0].quantifier, Some(ParamQuantifier::ZeroOrMore));
        match &preds[2].params[0].quantifier {
            Some(ParamQuantifier::Range { min, max }) => {
                assert_eq!(*min, 2);
                assert_eq!(*max, Some(5));
            },
            other => panic!("expected Range, got {:?}", other),
        }
    }

    #[test]
    fn parse_typed_params() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                gt . x: Int, y: Int |- x ">" y ;
                num . xs: (Int|Float) |- "num" "(" xs ")" ;
            },
            terms { }
        });
        let preds = lang
            .guard_config
            .as_ref()
            .expect("present")
            .builtin_predicates
            .as_ref()
            .expect("explicit");
        match &preds[0].params[0].ty {
            Some(ParamType::Single(id)) => assert_eq!(id.to_string(), "Int"),
            other => panic!("expected Single(Int), got {:?}", other),
        }
        match &preds[1].params[0].ty {
            Some(ParamType::Union(ids)) => {
                assert_eq!(ids.len(), 2);
                assert_eq!(ids[0].to_string(), "Int");
                assert_eq!(ids[1].to_string(), "Float");
            },
            other => panic!("expected Union, got {:?}", other),
        }
    }

    #[test]
    fn parse_connectives_block() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                connectives {
                    and = "and" | "∧";
                    or = "or" | "∨";
                    not = "not" | "¬";
                }
            },
            terms { }
        });
        let conns = lang
            .guard_config
            .as_ref()
            .expect("present")
            .connectives
            .as_ref()
            .expect("present");
        assert_eq!(conns.len(), 3);
        assert_eq!(conns[0].role, ConnectiveRole::And);
        assert_eq!(conns[0].keywords, vec!["and".to_string(), "∧".to_string()]);
        assert_eq!(conns[1].role, ConnectiveRole::Or);
        assert_eq!(conns[2].role, ConnectiveRole::Not);
    }

    #[test]
    fn parse_theories_block() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                theories {
                    arithmetic = PresburgerAlgebra for [Int];
                    patterns = UnificationTheory for [Proc, Name];
                    types_t = LatticeTheory;
                }
            },
            terms { }
        });
        let theories = &lang.guard_config.as_ref().expect("present").theories;
        assert_eq!(theories.len(), 3);
        assert_eq!(theories[0].name.to_string(), "arithmetic");
        assert_eq!(theories[0].handled_types.as_ref().map(|cs| cs.len()), Some(1));
        assert!(theories[2].handled_types.is_none(), "no `for [...]` → None");
    }

    #[test]
    fn parse_channels_block() {
        let lang = parse_lang(quote::quote! {
            name: Test,
            types { },
            guards {
                channels {
                    channel Name;
                    channel Place;
                    join PGuardedInput(ch: Name);
                    join PJoin(ch1: Name, ch2: Name, ch3: Name);
                }
            },
            terms { }
        });
        let ch = lang
            .guard_config
            .as_ref()
            .expect("present")
            .channels
            .as_ref()
            .expect("present");
        assert_eq!(ch.channel_categories.len(), 2);
        assert_eq!(ch.join_patterns.len(), 2);
        assert_eq!(ch.join_patterns[1].channel_params.len(), 3);
    }

    #[test]
    fn parse_full_guards_block() {
        let lang = parse_lang(quote::quote! {
            name: RhoCalc,
            types { },
            guards {
                eq . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
                neq . x, y |- x "!=" y ;
                connectives {
                    and = "and" | "∧";
                    not = "not";
                }
                theories {
                    arithmetic = PresburgerAlgebra for [Int];
                }
                channels {
                    channel Name;
                    join PGuardedInput(ch: Name);
                }
            },
            terms { }
        });
        let gc = lang.guard_config.as_ref().expect("present");
        assert_eq!(gc.builtin_predicates.as_ref().expect("present").len(), 2);
        assert_eq!(gc.connectives.as_ref().expect("present").len(), 2);
        assert_eq!(gc.theories.len(), 1);
        assert_eq!(
            gc.channels
                .as_ref()
                .expect("present")
                .channel_categories
                .len(),
            1
        );
    }

    #[test]
    fn connective_map_bidirectional_invariant() {
        let decls = vec![
            ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["and".into(), "∧".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Not,
                keywords: vec!["not".into(), "¬".into()],
            },
        ];
        let map = ConnectiveMap::from_decls(&decls).expect("valid map");
        // Forward
        assert!(map.role_to_keywords[&ConnectiveRole::And].contains(&"and".to_string()));
        assert!(map.role_to_keywords[&ConnectiveRole::And].contains(&"∧".to_string()));
        // Reverse
        assert_eq!(map.keyword_to_role.get("and"), Some(&ConnectiveRole::And));
        assert_eq!(map.keyword_to_role.get("¬"), Some(&ConnectiveRole::Not));
        // Cross-check bidirectionality
        for (kw, role) in &map.keyword_to_role {
            assert!(map.role_to_keywords[role].contains(kw));
        }
        for (role, kws) in &map.role_to_keywords {
            for kw in kws {
                assert_eq!(map.keyword_to_role[kw], *role);
            }
        }
    }

    #[test]
    fn connective_map_conn01_duplicate_keyword() {
        let decls = vec![
            ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["and".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Or,
                keywords: vec!["and".into()], // duplicate keyword across roles!
            },
        ];
        let result = ConnectiveMap::from_decls(&decls);
        assert!(result.is_err());
        let err = result.expect_err("should be CONN01");
        assert!(err.to_string().contains("CONN01"));
    }

    #[test]
    fn existing_languages_unchanged_no_guards_block() {
        // Verify a representative existing-style language still parses
        // without a guards block, producing guard_config: None.
        let lang = parse_lang(quote::quote! {
            name: SimpleCalc,
            types { Int },
            terms {
                Add . a:Int, b:Int |- a "+" b : Int ;
            },
            equations { },
            rewrites { }
        });
        assert!(lang.guard_config.is_none());
    }

    /// Phase 5: Direct test of the connective map thread-local without
    /// going through the full `Parse for LanguageDef`. Verifies that
    /// the parser functions correctly recognize declared keywords when
    /// the thread-local is active.
    ///
    /// This is a focused unit test for the ConnectiveMap → parser bridge,
    /// avoiding the complexity of constructing a full rewrite rule.
    #[test]
    fn connective_map_active_role_lookup() {
        // Default state: no map → all role lookups return None.
        assert!(active_role_of("and").is_none());
        assert!(!has_active_connective_map());

        // Install a custom map.
        let decls = vec![
            ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["all".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Or,
                keywords: vec!["any".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Not,
                keywords: vec!["neg".into()],
            },
        ];
        let map = ConnectiveMap::from_decls(&decls).expect("valid");
        let _guard = ConnectiveMapGuard::install(Some(map));

        // Now lookups succeed.
        assert!(has_active_connective_map());
        assert_eq!(active_role_of("all"), Some(ConnectiveRole::And));
        assert_eq!(active_role_of("any"), Some(ConnectiveRole::Or));
        assert_eq!(active_role_of("neg"), Some(ConnectiveRole::Not));
        assert_eq!(active_role_of("nonexistent"), None);
        assert!(active_role_available(&ConnectiveRole::And));
        assert!(!active_role_available(&ConnectiveRole::Forall));

        // Drop _guard at end of scope; map should be cleared.
    }

    /// Phase 5: After dropping the guard, the thread-local must be cleared.
    #[test]
    fn connective_map_guard_restores_on_drop() {
        // Pre-condition: empty
        assert!(!has_active_connective_map());

        {
            let decls = vec![ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["zzz".into()],
            }];
            let map = ConnectiveMap::from_decls(&decls).expect("valid");
            let _guard = ConnectiveMapGuard::install(Some(map));
            assert!(has_active_connective_map());
            assert_eq!(active_role_of("zzz"), Some(ConnectiveRole::And));
        }

        // After scope exit, the guard's Drop ran:
        assert!(!has_active_connective_map());
        assert_eq!(active_role_of("zzz"), None);
    }

    // (Phase R-fix 2026-04-08) The two unit tests
    // `guard_codegen_selectivity_uses_annotation` and
    // `guard_codegen_cost_uses_annotation` were moved from this file to
    // `crate::gen::runtime::guard_codegen::tests` so that the AST crate
    // (which will be extracted as `mettail-ast` in Phase R) does not
    // depend on `crate::gen::runtime::guard_codegen`. Without this move
    // the extraction would create an `ast → gen → ast` cycle.

    // ══════════════════════════════════════════════════════════════════════
    // Cleanup D: CONN02 enforcement (closed-world connectives)
    // ══════════════════════════════════════════════════════════════════════

    /// Cleanup D: when no connectives {} block is present, all standard
    /// Rust connective tokens are accepted (open-world / backward compat).
    #[test]
    fn cleanup_d_no_map_accepts_all_rust_tokens() {
        let _guard = ConnectiveMapGuard::install(None);
        assert!(rust_token_allowed(ConnectiveRole::And));
        assert!(rust_token_allowed(ConnectiveRole::Or));
        assert!(rust_token_allowed(ConnectiveRole::Not));
        assert!(rust_token_allowed(ConnectiveRole::Entails));
    }

    /// Cleanup D: when a connectives {} block declares only `and`, all
    /// other Rust connective tokens are rejected.
    #[test]
    fn cleanup_d_partial_map_rejects_unlisted_rust_tokens() {
        let decls = vec![ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["&&".into()],
        }];
        let map = ConnectiveMap::from_decls(&decls).expect("valid");
        let _guard = ConnectiveMapGuard::install(Some(map));

        assert!(rust_token_allowed(ConnectiveRole::And));
        assert!(!rust_token_allowed(ConnectiveRole::Or));
        assert!(!rust_token_allowed(ConnectiveRole::Not));
        assert!(!rust_token_allowed(ConnectiveRole::Entails));
    }

    /// Cleanup D: with a connectives {} block declaring all four roles,
    /// all corresponding Rust tokens are allowed.
    #[test]
    fn cleanup_d_full_map_accepts_all_listed_tokens() {
        let decls = vec![
            ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["&&".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Or,
                keywords: vec!["||".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Not,
                keywords: vec!["~".into()],
            },
            ConnectiveDecl {
                role: ConnectiveRole::Entails,
                keywords: vec!["=>".into()],
            },
        ];
        let map = ConnectiveMap::from_decls(&decls).expect("valid");
        let _guard = ConnectiveMapGuard::install(Some(map));

        assert!(rust_token_allowed(ConnectiveRole::And));
        assert!(rust_token_allowed(ConnectiveRole::Or));
        assert!(rust_token_allowed(ConnectiveRole::Not));
        assert!(rust_token_allowed(ConnectiveRole::Entails));
    }

    // (Phase R-fix 2026-04-08) See note above about
    // `guard_codegen_cost_uses_annotation` having moved to
    // `crate::gen::runtime::guard_codegen::tests`.

    /// Phase 5: Nested guards correctly stack and restore.
    #[test]
    fn connective_map_guard_nesting() {
        let outer_decls = vec![ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["outer_and".into()],
        }];
        let outer_map = ConnectiveMap::from_decls(&outer_decls).expect("valid");
        let _outer = ConnectiveMapGuard::install(Some(outer_map));
        assert_eq!(active_role_of("outer_and"), Some(ConnectiveRole::And));
        assert_eq!(active_role_of("inner_and"), None);

        {
            let inner_decls = vec![ConnectiveDecl {
                role: ConnectiveRole::And,
                keywords: vec!["inner_and".into()],
            }];
            let inner_map = ConnectiveMap::from_decls(&inner_decls).expect("valid");
            let _inner = ConnectiveMapGuard::install(Some(inner_map));
            // Inner active
            assert_eq!(active_role_of("inner_and"), Some(ConnectiveRole::And));
            // Outer keyword no longer visible
            assert_eq!(active_role_of("outer_and"), None);
        }

        // After inner drop, outer is restored
        assert_eq!(active_role_of("outer_and"), Some(ConnectiveRole::And));
        assert_eq!(active_role_of("inner_and"), None);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Phase 9: Property-based tests (proptest)
    // ══════════════════════════════════════════════════════════════════════

    use proptest::prelude::*;

    fn arb_role() -> impl Strategy<Value = ConnectiveRole> {
        prop::sample::select(vec![
            ConnectiveRole::And,
            ConnectiveRole::Or,
            ConnectiveRole::Not,
            ConnectiveRole::Entails,
            ConnectiveRole::ImpliedBy,
            ConnectiveRole::Iff,
            ConnectiveRole::Forall,
            ConnectiveRole::Exists,
        ])
    }

    proptest! {
        /// Property: For any list of declarations whose keywords are all
        /// distinct strings, `ConnectiveMap::from_decls` succeeds and the
        /// resulting bidirectional map satisfies the invariant:
        ///
        ///   ∀ (role, kws) ∈ role_to_keywords. ∀ kw ∈ kws.
        ///       keyword_to_role[kw] = role
        #[test]
        fn proptest_connective_map_bidirectional_invariant(
            decls in proptest::collection::vec(
                (arb_role(), "[a-z][a-z0-9_]{0,8}"),
                1..8,
            )
        ) {
            // Deduplicate keywords by tagging each with its index, so the
            // CONN01 invariant holds even when proptest generates the same
            // keyword string twice with different roles.
            let unique_decls: Vec<ConnectiveDecl> = decls
                .into_iter()
                .enumerate()
                .map(|(i, (role, kw))| ConnectiveDecl {
                    role,
                    keywords: vec![format!("{}_{}", kw, i)],
                })
                .collect();

            let map = ConnectiveMap::from_decls(&unique_decls).expect("unique kws");

            // Forward → Reverse
            for (role, kws) in &map.role_to_keywords {
                for kw in kws {
                    prop_assert_eq!(
                        map.keyword_to_role.get(kw),
                        Some(role)
                    );
                }
            }
            // Reverse → Forward
            for (kw, role) in &map.keyword_to_role {
                prop_assert!(map.role_to_keywords[role].contains(kw));
            }
        }

        /// Property: When the same keyword is declared for two distinct
        /// roles, `from_decls` always reports a CONN01 error.
        #[test]
        fn proptest_connective_map_conn01_on_duplicate(
            (role_a, role_b) in (arb_role(), arb_role()).prop_filter(
                "roles must differ",
                |(a, b)| a != b,
            )
        ) {
            let decls = vec![
                ConnectiveDecl {
                    role: role_a,
                    keywords: vec!["shared".into()],
                },
                ConnectiveDecl {
                    role: role_b,
                    keywords: vec!["shared".into()],
                },
            ];
            let result = ConnectiveMap::from_decls(&decls);
            prop_assert!(result.is_err());
        }

        /// Property: PredicateAnnotations override semantics — extension
        /// wins per-field. Encoded as a logical formula:
        ///
        ///   merged.selectivity = ext.selectivity OR base.selectivity
        ///   merged.cost        = ext.cost        OR base.cost
        ///
        /// where OR is `Option::or`.
        #[test]
        fn proptest_annotation_override_per_field(
            base_sel in proptest::option::of(0.0..=1.0_f64),
            ext_sel  in proptest::option::of(0.0..=1.0_f64),
            base_cost in proptest::option::of(0u32..1000),
            ext_cost  in proptest::option::of(0u32..1000),
        ) {
            let base = PredicateAnnotations {
                selectivity: base_sel,
                cost: base_cost,
            };
            let ext = PredicateAnnotations {
                selectivity: ext_sel,
                cost: ext_cost,
            };
            let merged = PredicateAnnotations {
                selectivity: ext.selectivity.or(base.selectivity),
                cost: ext.cost.or(base.cost),
            };

            // Extension's value wins if present
            if ext_sel.is_some() {
                prop_assert_eq!(merged.selectivity, ext_sel);
            } else {
                prop_assert_eq!(merged.selectivity, base_sel);
            }
            if ext_cost.is_some() {
                prop_assert_eq!(merged.cost, ext_cost);
            } else {
                prop_assert_eq!(merged.cost, base_cost);
            }
        }

        /// Property: Selectivity algebra for compound predicates obeys
        /// the standard inequalities under independence:
        ///
        ///   sel(P ∧ Q) ≤ min(sel(P), sel(Q))
        ///   sel(P ∨ Q) ≥ max(sel(P), sel(Q))
        ///   sel(¬P)   = 1 − sel(P)
        ///
        /// This is the foundation of selectivity-based query ordering
        /// (Selinger et al., 1979).
        #[test]
        fn proptest_selectivity_algebra(
            sa in 0.0..=1.0_f64,
            sb in 0.0..=1.0_f64,
        ) {
            // sel(P ∧ Q) = sa · sb
            let and_sel = sa * sb;
            prop_assert!(and_sel <= sa + 1e-12);
            prop_assert!(and_sel <= sb + 1e-12);

            // sel(P ∨ Q) = 1 − (1 − sa)(1 − sb)
            let or_sel = 1.0 - (1.0 - sa) * (1.0 - sb);
            prop_assert!(or_sel >= sa - 1e-12);
            prop_assert!(or_sel >= sb - 1e-12);

            // sel(¬P) = 1 − sa
            let not_sel = 1.0 - sa;
            prop_assert!((not_sel + sa - 1.0).abs() < 1e-12);
        }

        /// Cleanup D property: rust_token_allowed is the disjunction of
        /// "no map active" and "role available in active map". Equivalently:
        /// when a map is active, only declared roles' Rust tokens are allowed.
        ///
        /// This is the closed-world invariant for CONN02.
        #[test]
        fn proptest_cleanup_d_rust_token_gate_invariant(
            roles in proptest::collection::vec(
                prop::sample::select(vec![
                    ConnectiveRole::And,
                    ConnectiveRole::Or,
                    ConnectiveRole::Not,
                    ConnectiveRole::Entails,
                ]),
                0..4,
            )
        ) {
            // Build a map declaring only the chosen subset of roles.
            let decls: Vec<ConnectiveDecl> = roles
                .iter()
                .enumerate()
                .map(|(i, role)| ConnectiveDecl {
                    role: role.clone(),
                    keywords: vec![format!("kw_{}", i)],
                })
                .collect();
            let map = ConnectiveMap::from_decls(&decls).expect("unique kws");
            let _guard = ConnectiveMapGuard::install(Some(map));

            // Property: a Rust token is allowed iff its role is in the map.
            for role in [
                ConnectiveRole::And,
                ConnectiveRole::Or,
                ConnectiveRole::Not,
                ConnectiveRole::Entails,
            ] {
                let allowed = rust_token_allowed(role.clone());
                let in_map = roles.contains(&role);
                prop_assert_eq!(
                    allowed, in_map,
                    "role {:?} allowed-bit must match map membership",
                    role
                );
            }
        }

        /// Cleanup D property: with no active map, every Rust token is
        /// allowed (backward compatibility — open-world default).
        #[test]
        fn proptest_cleanup_d_no_map_open_world(
            role in prop::sample::select(vec![
                ConnectiveRole::And,
                ConnectiveRole::Or,
                ConnectiveRole::Not,
                ConnectiveRole::Entails,
            ])
        ) {
            // Ensure no map is active.
            let _guard = ConnectiveMapGuard::install(None);
            prop_assert!(rust_token_allowed(role));
        }
    }
}
