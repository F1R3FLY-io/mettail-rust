use proc_macro2::TokenStream;
use syn::{
    ext::IdentExt,
    parse::{Parse, ParseStream},
    Ident, Result as SynResult, Token, Type,
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
    #[expect(dead_code)] // Parsed from DSL, not yet consumed
    Int(i64),
    /// Boolean value.
    #[expect(dead_code)] // Parsed from DSL, not yet consumed
    Bool(bool),
    /// String value (e.g., `log_semiring_model_path: "path/to/model.json"`).
    Str(String),
    /// Keyword identifier (e.g., `beam_width: none`, `beam_width: auto`).
    Keyword(String),
}

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
}

impl BehavioralPred {
    /// Convert this macro-level predicate to a `prattail::QuantifiedFormula`
    /// suitable for runtime evaluation.
    pub fn to_quantified_formula(&self) -> proc_macro2::TokenStream {
        use quote::quote;
        match self {
            BehavioralPred::RelationQuery {
                relation_name,
                args,
                negated,
            } => {
                let rel_str = relation_name.to_string();
                let arg_exprs: Vec<_> = args
                    .iter()
                    .map(|a| match a {
                        PredArg::Var(v) => {
                            let v_str = v.to_string();
                            quote! { prattail::logict::QuantifiedArg::Var(#v_str.to_string()) }
                        }
                        PredArg::Constant(c) => {
                            let c_str = c.to_string();
                            quote! { prattail::logict::QuantifiedArg::Constant(#c_str.to_string()) }
                        }
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
            }
            BehavioralPred::Quantified {
                quantifier,
                var,
                domain,
                bound,
                body,
            } => {
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
            }
            BehavioralPred::And(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::and(#a_expr, #b_expr)
                }
            }
            BehavioralPred::Or(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::or(#a_expr, #b_expr)
                }
            }
            BehavioralPred::Not(inner) => {
                let inner_expr = inner.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::not(#inner_expr)
                }
            }
            BehavioralPred::Implies(a, b) => {
                let a_expr = a.to_quantified_formula();
                let b_expr = b.to_quantified_formula();
                quote! {
                    prattail::logict::QuantifiedFormula::implies(#a_expr, #b_expr)
                }
            }
            BehavioralPred::AcMatch { .. } => {
                // AcMatch does not translate to QuantifiedFormula —
                // it generates specialized partition enumeration code
                // in the codegen layer (rules.rs). This arm should never
                // be reached; AcMatch is intercepted before this point.
                panic!("BUG: AcMatch should be handled by specialized codegen, not to_quantified_formula()")
            }
        }
    }
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

/// Export: category name, optionally with native Rust type
/// types { Elem; Name; ![i32] as Int; }
#[derive(Debug, Clone)]
pub struct LangType {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
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
            }
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
            }
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
            }
            RefinementPredicate::And(a, b) => write!(f, "({} && {})", a, b),
            RefinementPredicate::Or(a, b) => write!(f, "({} || {})", a, b),
            RefinementPredicate::Not(a) => write!(f, "~{}", a),
            RefinementPredicate::Implies(a, b) => write!(f, "({} => {})", a, b),
            RefinementPredicate::TermEq(a, b) => {
                let a_str = match a { PredArg::Var(v) => v.to_string(), PredArg::Constant(c) => c.to_string() };
                let b_str = match b { PredArg::Var(v) => v.to_string(), PredArg::Constant(c) => c.to_string() };
                write!(f, "{} == {}", a_str, b_str)
            }
            RefinementPredicate::TermNeq(a, b) => {
                let a_str = match a { PredArg::Var(v) => v.to_string(), PredArg::Constant(c) => c.to_string() };
                let b_str = match b { PredArg::Var(v) => v.to_string(), PredArg::Constant(c) => c.to_string() };
                write!(f, "{} != {}", a_str, b_str)
            }
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
            }
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
            | RefinementPredicate::Implies(a, b) => {
                Self::merge_domains(a.classify(), b.classify())
            }
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
            }
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
    Track {
        auxiliary: Ident,
        primary: Ident,
    },
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
    ForallChildren { symbol: String, body: Box<TreeConstraintExpr> },
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

        // Parse: tokens { ... } (optional)
        let (token_defs, mode_defs, sync_constraints, tree_invariants) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "tokens" {
                parse_tokens(input)?
            } else {
                (Vec::new(), Vec::new(), Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
        };

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
            let native_type = bracket_content.parse::<Type>()?;

            let _ = content.parse::<Token![as]>()?;
            let name = content.parse::<Ident>()?;
            types.push(LangType { name, native_type: Some(native_type) });
        } else {
            // Could be either:
            //   Name               — regular type
            //   Name = { ... }     — refinement type
            let name = content.parse::<Ident>()?;

            if content.peek(Token![=]) {
                // Refinement type: Name = { var: BaseType | predicate };
                let _ = content.parse::<Token![=]>()?;
                let ref_def = parse_refinement_type_body(&content, name)?;
                refinement_types.push(ref_def);
            } else {
                types.push(LangType { name, native_type: None });
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
fn parse_refinement_type_body(
    input: ParseStream,
    name: Ident,
) -> SynResult<RefinementTypeDef> {
    let brace_content;
    syn::braced!(brace_content in input);

    // Parse: var : BaseType
    let var = brace_content.parse::<Ident>()?;
    brace_content.parse::<Token![:]>()?;
    let base_type = brace_content.parse::<super::types::TypeExpr>()?;

    // Parse: | predicate
    brace_content.parse::<Token![|]>()?;
    let predicate = parse_refinement_pred_implies(&brace_content)?;

    Ok(RefinementTypeDef {
        name,
        var,
        base_type,
        predicate,
    })
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
        return Ok(RefinementPredicate::Relation {
            name: ident,
            args,
            negated: false,
        });
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
pub fn parse_types_public(input: ParseStream) -> SynResult<(Vec<LangType>, Vec<RefinementTypeDef>)> {
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
        prev_was_backslash =
            matches!(&tt, proc_macro2::TokenTree::Punct(p) if p.as_char() == '\\');
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

                constraints.push(SyncConstraint::Align {
                    stream_a,
                    stream_b,
                    boundary_pattern,
                });
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
                    format!(
                        "unknown sync constraint '{}'; expected 'align' or 'track'",
                        kw
                    ),
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
            return Err(content.error(
                "expected token definition, 'mode', 'sync', or 'tree_invariants'",
            ));
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok((token_defs, mode_defs, sync_constraints, tree_invariants_vec))
}

/// Public wrapper for `parse_tokens` for use by `fragment.rs`.
pub fn parse_tokens_public(
    input: ParseStream,
) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>)> {
    let (token_defs, mode_defs, _, _) = parse_tokens(input)?;
    Ok((token_defs, mode_defs))
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
            unknown => {
                return Err(syn::Error::new(
                    key_ident.span(),
                    format!(
                        "unknown option '{}'. Valid options are: beam_width, log_semiring_model_path, dispatch",
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
/// Uses `&&` for conjunction, `||` for disjunction, `~`/`!` for negation,
/// and `=>` for implication. These are all valid Rust tokens parseable by
/// proc_macro2.
fn parse_behavioral_pred(input: ParseStream) -> SynResult<BehavioralPred> {
    parse_pred_implies(input)
}

/// Implication (right-associative, lowest precedence).
fn parse_pred_implies(input: ParseStream) -> SynResult<BehavioralPred> {
    let lhs = parse_pred_or(input)?;

    // Check for "=>" (fat arrow — implication)
    if input.peek(Token![=>]) {
        let _ = input.parse::<Token![=>]>()?;
        let rhs = parse_pred_implies(input)?; // right-associative
        Ok(BehavioralPred::Implies(Box::new(lhs), Box::new(rhs)))
    } else {
        Ok(lhs)
    }
}

/// Disjunction (`||`).
fn parse_pred_or(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_and(input)?;

    while input.peek(Token![||]) {
        let _ = input.parse::<Token![||]>()?;
        let rhs = parse_pred_and(input)?;
        result = BehavioralPred::Or(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Conjunction (`&&`).
fn parse_pred_and(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_not(input)?;

    while input.peek(Token![&&]) {
        let _ = input.parse::<Token![&&]>()?;
        let rhs = parse_pred_not(input)?;
        result = BehavioralPred::And(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Negation (`~` or `!`).
fn parse_pred_not(input: ParseStream) -> SynResult<BehavioralPred> {
    if input.peek(Token![~]) {
        let _ = input.parse::<Token![~]>()?;
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else if input.peek(Token![!]) {
        let _ = input.parse::<Token![!]>()?;
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
            RelationDecl { name: rel.name, param_types }
        })
        .collect();

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(LogicBlock { relations, content: tokens })
}
