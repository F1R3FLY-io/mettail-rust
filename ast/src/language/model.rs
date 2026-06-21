use super::*;

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
    pub ty: crate::types::TypeExpr,
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
        match self.try_to_quantified_formula() {
            Ok(expr) => expr,
            Err(msg) => {
                let msg_lit = syn::LitStr::new(&msg, proc_macro2::Span::call_site());
                quote! {{
                    compile_error!(#msg_lit);
                    prattail::logict::QuantifiedFormula::atom(
                        "__unsupported_behavioral_pred__",
                        vec![],
                    )
                }}
            },
        }
    }

    /// Fallible variant of [`to_quantified_formula`](Self::to_quantified_formula).
    ///
    /// `AcMatch` is structural: it binds variables while enumerating multiset
    /// partitions and therefore has no faithful `QuantifiedFormula` encoding.
    /// Codegen paths that support it lower it through specialized Ascent
    /// clauses; callers that need a formula can use this method to reject
    /// unsupported shapes without a macro-expansion panic.
    pub fn try_to_quantified_formula(&self) -> Result<proc_macro2::TokenStream, String> {
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
                    Ok(quote! { prattail::logict::QuantifiedFormula::not(#atom) })
                } else {
                    Ok(atom)
                }
            },
            BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
                let var_str = var.to_string();
                let body_expr = body.try_to_quantified_formula()?;
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
                    Quantifier::ForAll => Ok(quote! {
                        prattail::logict::QuantifiedFormula::forall(
                            #var_str,
                            #domain_expr,
                            #body_expr,
                        )
                    }),
                    Quantifier::Exists => Ok(quote! {
                        prattail::logict::QuantifiedFormula::exists(
                            #var_str,
                            #domain_expr,
                            #body_expr,
                        )
                    }),
                }
            },
            BehavioralPred::And(a, b) => {
                let a_expr = a.try_to_quantified_formula()?;
                let b_expr = b.try_to_quantified_formula()?;
                Ok(quote! {
                    prattail::logict::QuantifiedFormula::and(#a_expr, #b_expr)
                })
            },
            BehavioralPred::Or(a, b) => {
                let a_expr = a.try_to_quantified_formula()?;
                let b_expr = b.try_to_quantified_formula()?;
                Ok(quote! {
                    prattail::logict::QuantifiedFormula::or(#a_expr, #b_expr)
                })
            },
            BehavioralPred::Not(inner) => {
                let inner_expr = inner.try_to_quantified_formula()?;
                Ok(quote! {
                    prattail::logict::QuantifiedFormula::not(#inner_expr)
                })
            },
            BehavioralPred::Implies(a, b) => {
                let a_expr = a.try_to_quantified_formula()?;
                let b_expr = b.try_to_quantified_formula()?;
                Ok(quote! {
                    prattail::logict::QuantifiedFormula::implies(#a_expr, #b_expr)
                })
            },
            BehavioralPred::AcMatch { .. } => {
                Err("ac_match behavioral predicates require specialized Ascent partition lowering and cannot be embedded in QuantifiedFormula".to_string())
            },
            BehavioralPred::Top => {
                // Top is the always-true identity predicate used when the guard
                // slot is declared at language-spec time but the actual
                // predicate is per-instance runtime data. The Ascent rule
                // body has no join clause for Top (the rule fires
                // unconditionally on its structural pattern).
                Ok(quote! {
                    prattail::logict::QuantifiedFormula::atom(
                        "__top__",
                        vec![],
                    )
                })
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
    pub syntax_forms: Vec<Vec<crate::grammar::SyntaxExpr>>,
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
    pub base_type: crate::types::TypeExpr,
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

use crate::grammar::GrammarItem;

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
        use crate::grammar::TermParam;
        use crate::types::TypeExpr;
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
