use syn::{parse::ParseStream, Ident, Result as SynResult, Token};

use super::types::{CollectionType, EvalMode, RustCodeBlock, TypeExpr};

/// Classification of a nonterminal reference in a grammar rule.
///
/// Determined once at construction time based on the nonterminal name.
/// Replaces scattered string comparisons throughout code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NonTerminalKind {
    /// Variable reference (`Var`) — stored as `OrdVar`, not boxed
    Var,
    /// Integer literal (`Integer`) — stored as native int type, not boxed
    Integer,
    /// Boolean literal (`Boolean`) — stored as `bool`, not boxed
    Boolean,
    /// String literal (`StringLiteral`) — stored as `String`, not boxed
    StringLiteral,
    /// Float literal (`FloatLiteral`) — stored as canonical float, not boxed
    FloatLiteral,
    /// Identifier TEXT (`Ident`) — stored as a bare `std::string::String`, not boxed.
    ///
    /// The builtin `Ident` token class given a first-class mid-rule surface: a position
    /// that consumes ONE `Token::Ident` and carries its text INERTLY, with none of
    /// [`Self::Var`]'s binder semantics. The distinction is the whole point — `Var`
    /// lowers to `mettail_runtime::OrdVar`, which `subst` canonicalises under unify, so a
    /// `Var`-typed method name inside `new nth in { … }` would be CAPTURED by the binder.
    /// An `Ident`-typed field is a `String` and no substitution can see it.
    ///
    /// Both Rholang oracles spell the method name with their `var` TOKEN
    /// (BNFC `rholang_mercury.cf:41` `PMethod. Proc11 ::= Proc11 "." Var "(" [Proc] ")"`,
    /// tree-sitter `grammar.js:293-298` `field('name', $.var)`) — a lexical class, not a
    /// binding construct, which is exactly what this kind models.
    ///
    /// ⚠ MEASURED ALTERNATIVE, REJECTED. The other way to reach a mid-rule String is a
    /// declared `tokens { }` kind consumed by a `m@Kind` capture. For a kind co-extensive
    /// with `Ident` that is not free: measured on Rholang, declaring it alone moved the
    /// lexer's multi-accept DFA states from 4/474 (0.8 %) to 379/475 (79.8 %) and
    /// alt-accept edges from 482 to 1234 (×2.56), because `subset.rs`'s reservation
    /// `retain` deletes only `TokenKind::Ident` and cannot delete a `Custom` co-accept.
    /// Parse time over the shipped 11-input corpus regressed geomean ×2.49, worst ×8.59
    /// (`{p | q}`), with inputs containing no identifier flat at ×1.03 as the control.
    /// It is also LESS conformant: a `Custom` kind co-accepts at reserved-keyword states
    /// too, so `x.new()` would parse, where both oracles reject it.
    Ident,
    /// A reference to a user-defined category (e.g., `Proc`, `Name`, `Expr`)
    Category,
}

impl NonTerminalKind {
    /// Classify a nonterminal by its name string.
    #[inline]
    pub fn classify(name: &str) -> Self {
        match name {
            "Var" => Self::Var,
            "Integer" => Self::Integer,
            "Boolean" => Self::Boolean,
            "StringLiteral" => Self::StringLiteral,
            "FloatLiteral" => Self::FloatLiteral,
            "Ident" => Self::Ident,
            _ => Self::Category,
        }
    }

    /// Returns true if this is any literal kind (Integer, Boolean, StringLiteral, FloatLiteral).
    #[inline]
    pub fn is_literal(self) -> bool {
        matches!(self, Self::Integer | Self::Boolean | Self::StringLiteral | Self::FloatLiteral)
    }

    /// Returns true if this is a built-in type (Var or any literal) — not a user-defined category.
    #[inline]
    pub fn is_builtin(self) -> bool {
        self != Self::Category
    }
}

/// Item in a grammar rule
#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String), // "0"
    /// Nonterminal reference with pre-classified kind.
    NonTerminal {
        ident: Ident,
        kind: NonTerminalKind,
    },
    /// Binder: <Category> indicates this position binds a variable
    /// The bound variable is used in subsequent items
    Binder {
        category: Ident,
    }, // <Name>
    /// Collection: HashBag(Proc) sep "|" [delim "[" "]"]
    Collection {
        coll_type: CollectionType,
        element_type: Ident,
        separator: String,
        delimiters: Option<(String, String)>, // (open, close)
    },
}

impl GrammarItem {
    /// Construct a `NonTerminal` item, classifying the kind from the ident name.
    pub fn non_terminal(ident: Ident) -> Self {
        let kind = NonTerminalKind::classify(&ident.to_string());
        GrammarItem::NonTerminal { ident, kind }
    }

    /// Returns the `NonTerminalKind` if this is a `NonTerminal`, else `None`.
    #[inline]
    pub fn nonterminal_kind(&self) -> Option<NonTerminalKind> {
        match self {
            GrammarItem::NonTerminal { kind, .. } => Some(*kind),
            _ => None,
        }
    }

    /// Returns the ident if this is a `NonTerminal`, else `None`.
    #[inline]
    pub fn nonterminal_ident(&self) -> Option<&Ident> {
        match self {
            GrammarItem::NonTerminal { ident, .. } => Some(ident),
            _ => None,
        }
    }

    /// Returns true if this is a `NonTerminal` with kind `Var`.
    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self, GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. })
    }

    /// Returns true if this is a literal nonterminal (Integer, Boolean, StringLiteral, FloatLiteral).
    #[inline]
    pub fn is_literal(&self) -> bool {
        matches!(self, GrammarItem::NonTerminal { kind, .. } if kind.is_literal())
    }

    /// Returns true if this is a built-in (Var or any literal) — not a user-defined category.
    #[inline]
    pub fn is_builtin(&self) -> bool {
        matches!(self, GrammarItem::NonTerminal { kind, .. } if kind.is_builtin())
    }
}

/// Parameter in term context of a constructor declaration
///
/// Examples:
/// - `n:Name` → Simple parameter
/// - `^x.p:[Name -> Proc]` → Abstraction binding x in p
/// - `^[xs].p:[Name* -> Proc]` → Multi-binder abstraction
#[derive(Debug, Clone)]
pub enum TermParam {
    /// Simple typed parameter: `n:Name`
    Simple { name: Ident, ty: TypeExpr },
    /// Abstraction parameter: `^x.p:[Name -> Proc]`
    /// - `binder` is the bound variable (x)
    /// - `body` is the parameter name for the body (p)
    /// - `ty` is the function type [Name -> Proc]
    Abstraction { binder: Ident, body: Ident, ty: TypeExpr },
    /// Multi-binder abstraction: `^[xs].p:[Name* -> Proc]`
    /// - `binder` represents multiple bound variables (xs = x0, x1, ...)
    /// - `body` is the parameter name for the body (p)
    /// - `ty` is the function type [Name* -> Proc]
    MultiAbstraction { binder: Ident, body: Ident, ty: TypeExpr },
    /// Guard body parameter: `?<name>:Guard`
    ///
    /// The variant carries only the slot's name. The actual predicate
    /// data is per-instance — it lives on the generated enum variant
    /// as a `mettail_runtime::BehavioralPred` field, parsed by the
    /// language-generic
    /// `mettail_prattail::parser::predicate::PredicateParser` at
    /// source-parse time (Phase 1B/2G of the predicated-types
    /// implementation plan).
    GuardBody { name: Ident },
    /// Optional group parameter: `#opt(... e:T ...)`
    ///
    /// Mirrors `#opt(...)` in the syntax pattern. Inner params are
    /// captured ONLY when the syntax-pattern Opt block matches at parse
    /// time. Each inner Simple/Abstraction/MultiAbstraction param is
    /// wrapped as `Option<T>` in the generated AST variant and action
    /// signature. GuardBody and nested Optional inner params are
    /// supported by the same recursive treatment.
    Optional { params: Vec<TermParam> },
}

impl Drop for TermParam {
    fn drop(&mut self) {
        let mut work = Vec::new();
        if let TermParam::Optional { params } = self {
            work.append(params);
        }
        while let Some(mut param) = work.pop() {
            if let TermParam::Optional { params } = &mut param {
                work.append(params);
            }
        }
    }
}

/// Syntax expression in patterns (can include meta-operations)
///
/// Example: `"for" "(" #zip(ns,xs).#map(|n,x| x "<-" n).#sep(",") ")" "{" p "}"`
#[derive(Debug, Clone)]
pub enum SyntaxExpr {
    /// Quoted literal: "for", "(", "<-"
    Literal(String),
    /// Parameter reference: n, x, p
    Param(Ident),
    /// Pattern operation: #sep, #zip, #map, #opt
    Op(PatternOp),
    /// L9-3: reference a custom token KIND declared in a `tokens {}` block (or a
    /// named mode). `name` is the declared kind; `bind` is `Some(v)` for the
    /// `v@Tok` capture form (bind the matched token's text to `v`), or `None` to
    /// match the kind without capturing. Produced ONLY by the `@` bind-form
    /// parser and by parse-time classification (a bare `Param(x)` whose `x` is a
    /// declared token name and NOT a term-context param) — never written as a
    /// bare literal.
    TokenKind { name: Ident, bind: Option<Ident> },
    /// L9-4: a guest-body FLT capture, written `*flt(bind, open, close)`. The
    /// walker consumes the `open` opener token (a mode-pushing `FltOpen*` kind
    /// carrying the tag), then the guest body (`GuestChunk` / `${…}` `Hole`
    /// tokens), then the `close` closer token (a `pop` `FltClose*` kind), and
    /// ASSEMBLES a `mettail_runtime::FltNode` (tag, ONE verbatim `body_src`
    /// slice, holes, position) bound to `bind` as an `Arc<FltNode>` opaque
    /// leaf. Its variant field rides the L9-3 capture machinery
    /// (`capture_layout` → `OpaqueLeafKind::GuestBody`), NOT a term-context
    /// param — `bind` is bound by `*flt`, not declared before `|-`.
    GuestBody { open: Ident, close: Ident, bind: Ident },
}

/// Pattern operation (compile-time meta-syntax)
///
/// These operations generate grammar rules and display code at compile time.
#[derive(Debug, Clone)]
pub enum PatternOp {
    /// #sep(coll, "sep") or coll.#sep("sep") or chain.#sep(",")
    /// Generates: `(<elem> "sep")* <elem>?` in grammar
    ///
    /// For simple collections: source=None, collection=coll_name
    /// For chained operations: source=Some(Map/Zip), collection ignored
    Sep {
        collection: Ident,
        separator: String,
        /// Optional source for chained operations like #zip(...).#map(...).#sep(",")
        source: Option<Box<PatternOp>>,
    },
    /// #zip(a, b) - pairs corresponding elements
    /// Used with #map to generate paired patterns
    Zip { left: Ident, right: Ident },
    /// #map(source, |x| expr) or source.#map(|x| expr)
    /// Transforms each element according to the pattern
    Map {
        source: Box<PatternOp>, // Can be Zip result or collection ref
        params: Vec<Ident>,     // Closure parameters
        body: Vec<SyntaxExpr>,  // Pattern body
    },
    /// #opt(expr) - optional element
    /// Generates: `(expr)?` in grammar
    Opt { inner: Vec<SyntaxExpr> },
    /// Variable reference (for chaining: coll.#sep)
    Var(Ident),
}

/// Grammar rule - supports both old BNFC-style and new judgement-style syntax
///
/// Old style: `Label . Category ::= Item Item Item ;`
/// New style: `Label . context |- pattern : Type ;`
#[derive(Debug, Clone)]
pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident, // Result type

    // Old syntax (BNFC-style) - used when term_context is None
    pub items: Vec<GrammarItem>,
    /// Binding structure: (binder_index, vec![body_indices])
    /// e.g., (0, vec![1]) means item 0 binds in item 1
    pub bindings: Vec<(usize, Vec<usize>)>,

    // New syntax (judgement-style) - used when term_context is Some
    /// Term context with typed parameters: `n:Name, ^x.p:[Name -> Proc]`
    pub term_context: Option<Vec<TermParam>>,
    /// Concrete syntax pattern: `"for" "(" x "<-" n ")" "{" p "}"`
    /// Can include pattern operations like `ps.#sep("|")`
    pub syntax_pattern: Option<Vec<SyntaxExpr>>,

    /// HOL syntax: optional Rust code implementation, e.g. `![a + b]`
    pub rust_code: Option<RustCodeBlock>,
    /// HOL syntax: evaluation mode (fold / step)
    pub eval_mode: Option<EvalMode>,
    /// Whether this rule is right-associative (default: left).
    /// Annotated with `right` keyword after eval mode in the DSL.
    pub is_right_assoc: bool,
    /// ★ PRECEDENCE LEVELS (2026-07-28): this rule shares the PRECEDENCE LEVEL of the
    /// preceding non-postfix infix rule of the same category, instead of opening a new
    /// (tighter) one. Annotated with the bare `same` keyword after the eval mode,
    /// alongside `right`, `prefix(N)`, and `canonical`.
    ///
    /// # Why a marker and not a number
    ///
    /// Before this flag, `prattail::binding_power::analyze_binding_powers` advanced its
    /// precedence counter once per RULE, in both associativity arms. Rule `i` of a
    /// category therefore received `left_bp ∈ {2 + 2i, 3 + 2i}`, and two rules `i < j`
    /// could share a `left_bp` only if `3 + 2i = 2 + 2j`, i.e. `2(j − i) = 1` — impossible
    /// by parity. Declaration order was consequently a strict TOTAL order by construction:
    /// the grammar could not say that `*` and `/` bind equally tightly, so `6 * 3 / 2`
    /// parsed as `6 * (3 / 2)`.
    ///
    /// `same` restores the missing relation — "no tighter than the previous rule" — while
    /// keeping DECLARATION ORDER the single source of truth for the ordering itself. An
    /// absolute `@prec(n)` was rejected: it admits partial specifications, renumbering
    /// churn, and two rules that disagree about which level a number denotes, none of
    /// which a relative marker can express.
    ///
    /// # It is orthogonal to associativity
    ///
    /// `same` composes with `right` on the SAME rule, which is not a nicety but a hard
    /// requirement of the language being modelled: Rholang's normative tree-sitter grammar
    /// (`rholang-tree-sitter/grammar.js`) declares level 6 with MIXED associativity —
    /// `matches: prec.right(6, …)` beside `eq: prec.left(6, …)` and
    /// `neq: prec.left(6, …)`. A design that attached one associativity per level could
    /// not express Rholang's own grammar. Associativity is therefore per-OPERATOR and
    /// precedence is per-LEVEL, and the two never interact.
    ///
    /// # Meaning when there is no previous rule
    ///
    /// `same` on the first non-postfix infix rule of a category has nothing to share with
    /// and is ignored (the rule opens the category's first level). It is not an error,
    /// because rules reach the analyzer from several synthesis paths whose relative order
    /// is not author-visible; a hard failure there would be a trap rather than a guard.
    pub shares_level_with_previous: bool,
    /// Explicit prefix binding power for unary prefix operators.
    /// Annotated with `prefix(N)` after eval mode and `right` in the DSL.
    /// When `None`, falls back to `max_infix_bp + 2`.
    pub prefix_bp: Option<u8>,
    /// Phase 11 (predicated types): optional `#[tier(...)]` directive
    /// that overrides the auto-classified guard tier for this rule.
    /// `None` means use the analyzer's classification.
    pub tier_directive: Option<TierDirective>,
    /// Stage 3.13b (2026-05-01): provenance flag distinguishing user-written
    /// rules (false) from synthetic auto-injection rules emitted by
    /// `macros/src/gen/runtime/wpda_codegen/auto_inject.rs::make_injection_rule`
    /// (true). Used by:
    /// - Stage 3.13c routing filter (`pipeline.rs:1316`) to exclude synthetic
    ///   rules from legacy unified-trampoline cast_rules.
    /// - Stage 3.13b W05 lint refinement (future) to distinguish synthetic-
    ///   induced ambiguity (Note severity) from user-authored ambiguity
    ///   (Warning severity).
    ///
    /// Default `false` for parsed rules; set `true` only by `make_injection_rule`.
    pub is_auto_injected: bool,
    /// Stage 3.27a (2026-05-04): doc-comment text (joined with `\n`)
    /// extracted from `#[doc = "..."]` attributes (typically lowered from
    /// `///` lines) preceding the rule. `None` when no doc comment is
    /// present. Surfaces in the generated `TermDef::description` field,
    /// displayed by the REPL `info` command.
    pub doc_comment: Option<String>,
    /// ★ SURFACE SYNONYMY (2026-07-26): this rule is the DECLARED CANONICAL MEMBER of its
    /// surface-synonymy class. Annotated with the bare `canonical` keyword after the eval
    /// mode, alongside `right` and `prefix(N)`.
    ///
    /// A synonymy class is the set of rules of one category that denote the same term —
    /// derived, not declared, as the connected component of `alias ──▶ fold target`
    /// (`grammar_shapes::FoldAliasShape::target_label`). Rholang's `Name` class is
    /// `{ NQuote, NQuoteShort, NQuoteNil }`. Every member has its own SURFACE, and
    /// `Display` must emit ONE of them for the whole class, or `Display∘Parse` is not a
    /// fixpoint: the elected member is a function of the PARSE CONTEXT, not of the class,
    /// so the same denotation cascades through one surface per nesting layer
    /// (`(@(error)) <- @Nil` → `@(error) <- @Nil` → `@error <- @Nil`).
    ///
    /// ★ WHY DECLARED RATHER THAN INFERRED. Two candidate inference rules were REFUTED by
    /// measurement (2026-07-26): (a) *"prefer the member `parse_structured` falls back
    /// to"* — `parse` and `parse_via_wpda` agree exactly everywhere, so there is no such
    /// fallback; (b) *"prefer the explicit grouping"* — at `Name` level the election DOES
    /// prefer `NParen`, yet inside `InputBind` the same substring elects `NQuoteShort`.
    /// The election is CONTEXT-DEPENDENT, so it is not a function of the synonymy class
    /// and cannot name a canonical member. The grammar can, and this is where it does.
    ///
    /// A class whose members are mutually re-routable (see
    /// `FoldAliasShape::renaming_inverse`) and which declares no canonical member is a
    /// COMPILE ERROR naming the class — so a newly added surface synonym fails the build
    /// until the grammar says which member is canonical.
    pub is_canonical_synonym: bool,
}

/// ★ THE FIXTURE CONSTRUCTOR — a `GrammarRule` holding every field's DOCUMENTED DEFAULT,
/// with only the two fields that have no default supplied by the caller.
///
/// # Why this exists
///
/// `GrammarRule` has fourteen fields, and a test that exercises ONE of them still has to
/// name the other thirteen, because Rust struct literals are total. Before this
/// constructor, twenty-nine test fixtures across `ast` and `macros` each restated the
/// whole struct. Adding `is_canonical_synonym` (2026-07-26) therefore produced
/// thirty-nine compile errors, of which only ten carried information: the ten PRODUCTION
/// sites, where a real rule's canonicity genuinely had to be decided. The other
/// twenty-nine were fixtures that wanted the default and said so twenty-nine times.
///
/// That signal-to-noise ratio is what this fixes, and it fixes it WITHOUT weakening the
/// signal. Production constructors keep writing exhaustive struct literals, so a newly
/// added field still fails their compilation — exactly where somebody must decide what
/// the field means for a real rule. Fixtures route through here, so the same field is
/// decided ONCE, in this function, beside the field's own documentation.
///
/// ```text
///   a new field is added to GrammarRule
///            │
///            ├──▶ 10 production sites (exhaustive literals) ──▶ ✗ COMPILE ERROR
///            │      ast::grammar::parse_grammar_rule_{old,new}         ← decide here
///            │      ast::auto_inject::{make_injection_rule, reconstruct_language_def}
///            │      macros::gen::runtime::wpda_codegen::synthetic  (×6)
///            │
///            └──▶ 29 test fixtures (`..rule_fixture(l, c)`) ──▶ ✓ compile unchanged
///                   …once THIS function names the default, once.
/// ```
///
/// # Why not `#[derive(Default)]`
///
/// `syn::Ident` implements no `Default`, and a rule whose `label` and `category` were
/// defaulted would be a nonsense rule that nevertheless COMPILES — the failure would move
/// from the compiler to a confusing assertion in an unrelated test. Those two fields have
/// no meaningful default, so they stay parameters. Everything else does have one, and it
/// is written below.
///
/// # The defaults, and where each comes from
///
/// Each default is the value the DSL rule parser produces for a rule that declares nothing
/// on that axis — so a fixture is a rule the grammar *could* have written, not an
/// artificial one. `rule_fixture_matches_parser_defaults` (this module's tests) MEASURES
/// that correspondence against `parse_grammar_rule` rather than asserting it in prose.
///
/// | field | default | meaning of the default |
/// |---|---|---|
/// | `items`, `bindings` | empty | no BNFC-style items; judgement rules derive them |
/// | `term_context`, `syntax_pattern` | `None` | the old (BNFC) shape |
/// | `rust_code`, `eval_mode` | `None` | no HOL body, hence no fold/step mode |
/// | `is_right_assoc` | `false` | left-associative unless the rule says `right` |
/// | `shares_level_with_previous` | `false` | opens its own precedence level unless the rule says `same` |
/// | `prefix_bp` | `None` | prefix binding power falls back to `max_infix_bp + 2` |
/// | `tier_directive` | `None` | no `#[tier(…)]`; the analyzer's classification stands |
/// | `is_auto_injected` | `false` | user-written, not emitted by auto-injection |
/// | `doc_comment` | `None` | no `///` lines precede the rule |
/// | `is_canonical_synonym` | `false` | no `canonical` annotation (see below) |
///
/// The last one is the only default that is more than bookkeeping, so it is worth stating
/// twice. `is_canonical_synonym` marks the DECLARED canonical member of a surface-synonymy
/// class, and a class exists only where two or more rules of one category denote the same
/// term. A fixture built from this constructor declares no such class — it is a lone rule,
/// or one of a handful that share nothing but a test — so there is no class for it to be
/// canonical IN. `false` is therefore not a convenient placeholder but the only coherent
/// value, and it coincides with what the parser assigns a rule carrying no annotation.
///
/// # Usage
///
/// Override exactly the fields the test is about; inherit the rest.
///
/// ```
/// use mettail_ast::grammar::{rule_fixture, GrammarItem};
/// use proc_macro2::Span;
/// use syn::Ident;
///
/// let id = |s: &str| Ident::new(s, Span::call_site());
/// let rule = mettail_ast::grammar::GrammarRule {
///     items: vec![GrammarItem::Terminal("Nil".to_string())],
///     ..rule_fixture(id("PZero"), id("Proc"))
/// };
/// assert_eq!(rule.label.to_string(), "PZero");
/// assert!(!rule.is_canonical_synonym);
/// ```
///
/// This is a TEST FIXTURE constructor. Production code that builds a rule is deciding what
/// the rule MEANS, and must say so field by field; calling `rule_fixture` there would
/// silently adopt a default the author never considered, which is the failure mode this
/// whole design exists to keep loud.
pub fn rule_fixture(label: Ident, category: Ident) -> GrammarRule {
    GrammarRule {
        label,
        category,
        items: Vec::new(),
        bindings: Vec::new(),
        term_context: None,
        syntax_pattern: None,
        rust_code: None,
        eval_mode: None,
        is_right_assoc: false,
        shares_level_with_previous: false,
        prefix_bp: None,
        tier_directive: None,
        is_auto_injected: false,
        doc_comment: None,
        is_canonical_synonym: false,
    }
}

/// Phase 11 (predicated types): user-supplied tier override.
///
/// Parsed from `#[tier(t1|t2|t3|t4 [, bound = N] [, force])]`
/// attributes that may appear immediately before a guarded
/// constructor in the `terms { }` block.
///
/// The validator (`mettail_ast::validation::validator`) checks the
/// override against the auto-classified tier and emits TIER01 if
/// they disagree without `force = true`. With `force`, the override
/// is accepted as an explicit source annotation only; formal proof attribution
/// remains outside the implementation model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TierDirective {
    /// The requested tier (1, 2, 3, or 4).
    pub tier: TierRequest,
    /// Optional bound for T3 semi-decidable evaluation.
    pub bound: Option<usize>,
    /// `force = true` skips the TIER01 mismatch check.
    pub force: bool,
}

/// Tier identifier in a `#[tier(...)]` directive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TierRequest {
    /// T1 — statically eliminated (tautology / contradiction).
    T1,
    /// T2 — decidable at runtime via Ascent join clauses or finite
    /// SFA evaluation.
    T2,
    /// T3 — semi-decidable, bounded BFS over rewrite graph.
    T3,
    /// T4 — undecidable, requires user assertion (with optional cert).
    T4,
}

impl std::fmt::Display for TierRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TierRequest::T1 => write!(f, "t1"),
            TierRequest::T2 => write!(f, "t2"),
            TierRequest::T3 => write!(f, "t3"),
            TierRequest::T4 => write!(f, "t4"),
        }
    }
}

/// Parse a `#[tier(...)]` attribute from the input stream.
///
/// Expects to be called at the position of the `#` token. Returns
/// `Ok(None)` if the next token is not `#` (no tier directive
/// present), `Ok(Some(directive))` if a valid `#[tier(...)]` was
/// parsed, and `Err` for malformed input.
pub fn parse_tier_directive(input: ParseStream) -> SynResult<Option<TierDirective>> {
    if !input.peek(Token![#]) {
        return Ok(None);
    }
    let _ = input.parse::<Token![#]>()?;

    let bracketed;
    syn::bracketed!(bracketed in input);

    let attr_name: Ident = bracketed.parse()?;
    if attr_name != "tier" {
        return Err(syn::Error::new(
            attr_name.span(),
            format!("expected `tier` attribute, found `{}`", attr_name),
        ));
    }

    let parens;
    syn::parenthesized!(parens in bracketed);

    // First positional arg: the tier identifier (t1/t2/t3/t4).
    let tier_ident: Ident = parens.parse()?;
    let tier = match tier_ident.to_string().as_str() {
        "t1" | "T1" => TierRequest::T1,
        "t2" | "T2" => TierRequest::T2,
        "t3" | "T3" => TierRequest::T3,
        "t4" | "T4" => TierRequest::T4,
        other => {
            return Err(syn::Error::new(
                tier_ident.span(),
                format!("expected t1/t2/t3/t4, found `{}`", other),
            ));
        },
    };

    let mut bound: Option<usize> = None;
    let mut force = false;

    while parens.peek(Token![,]) {
        let _ = parens.parse::<Token![,]>()?;
        if parens.is_empty() {
            break;
        }
        let key: Ident = parens.parse()?;
        match key.to_string().as_str() {
            "bound" => {
                let _ = parens.parse::<Token![=]>()?;
                let lit: syn::LitInt = parens.parse()?;
                bound = Some(lit.base10_parse::<usize>()?);
            },
            "force" => {
                // `force` is a flag — no `= value` part required.
                force = true;
            },
            other => {
                return Err(syn::Error::new(
                    key.span(),
                    format!("unknown tier attribute key `{}`; expected one of bound/force", other),
                ));
            },
        }
    }

    Ok(Some(TierDirective { tier, bound, force }))
}

/// Stage 3.27a (2026-05-04): consume zero or more `#[doc = "..."]`
/// attributes (typically emitted by `///` doc-comment sugar) preceding
/// a grammar rule. Stops at the first non-`#[doc]` attribute or non-`#`
/// token, leaving the unconsumed attribute on the stream for the next
/// parser (e.g., `parse_tier_directive`). Returns the joined text
/// (with one canonical leading space stripped per Rust convention) or
/// `None` if no doc comments were present.
///
/// **MUST run before `parse_tier_directive`** since both peek for `#`.
/// Uses fork-peek with single-attribute granularity to ONLY consume
/// `#[doc = "..."]` attributes; `#[tier(...)]` and any other attribute
/// remain on the real stream.
pub fn parse_doc_comment(input: ParseStream) -> SynResult<Option<String>> {
    let mut lines: Vec<String> = Vec::new();
    while input.peek(Token![#]) {
        // Peek one attribute on a fork without consuming the real stream.
        let fork = input.fork();
        let attr = match parse_one_outer_attribute(&fork) {
            Ok(a) => a,
            Err(_) => break,
        };
        if !attr.path().is_ident("doc") {
            break; // not a doc attribute — leave on real stream for next parser
        }
        // Extract the string literal from `#[doc = "..."]`.
        let nv = match attr.meta.require_name_value() {
            Ok(nv) => nv,
            Err(_) => break, // `#[doc(...)]` form — skip without consuming
        };
        let lit_str = match &nv.value {
            syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => s.value(),
            _ => break,
        };
        // Confirmed `#[doc = "..."]`: advance the real stream by parsing
        // one outer attribute (the same one we just peeked).
        let _ = parse_one_outer_attribute(input)?;
        // Strip exactly one leading space (rustc's canonical form for `///`).
        let stripped = lit_str.strip_prefix(' ').unwrap_or(&lit_str).to_string();
        lines.push(stripped);
    }
    if lines.is_empty() {
        Ok(None)
    } else {
        Ok(Some(lines.join("\n")))
    }
}

/// Parse exactly ONE outer attribute (`#[...]`) — mirrors syn's internal
/// `single_parse_outer` which is not public. Used by `parse_doc_comment`
/// to inspect attributes one at a time without consuming all attributes
/// like `Attribute::parse_outer` would.
fn parse_one_outer_attribute(input: ParseStream) -> SynResult<syn::Attribute> {
    let pound_token: Token![#] = input.parse()?;
    let bracket_content;
    let bracket_token = syn::bracketed!(bracket_content in input);
    let meta: syn::Meta = bracket_content.parse()?;
    Ok(syn::Attribute {
        pound_token,
        style: syn::AttrStyle::Outer,
        bracket_token,
        meta,
    })
}

pub fn parse_terms(input: ParseStream) -> SynResult<Vec<GrammarRule>> {
    let terms_ident = input.parse::<Ident>()?;
    if terms_ident != "terms" {
        return Err(syn::Error::new(terms_ident.span(), "expected 'terms'"));
    }

    let content;
    syn::braced!(content in input);

    let mut rules = Vec::new();
    while !content.is_empty() {
        rules.push(parse_grammar_rule(&content)?);
    }

    //Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(rules)
}

fn parse_grammar_rule(input: ParseStream) -> SynResult<GrammarRule> {
    // Stage 3.27a (2026-05-04): consume `#[doc = "..."]` attributes
    // (typically lowered from `///` lines) BEFORE `parse_tier_directive`
    // since both peek for `#`. parse_doc_comment uses fork-peek to ONLY
    // consume `#[doc]` attributes, leaving `#[tier(...)]` for the next
    // parser.
    let doc_comment = parse_doc_comment(input)?;

    // Phase 11: optional `#[tier(...)]` directive precedes the rule.
    let tier_directive = parse_tier_directive(input)?;

    // Parse: Label .
    let label = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;

    // Look ahead to determine syntax style:
    // - Old: `Category ::= ...` (Ident followed by ::)
    // - New: `context |- pattern : Type` (Ident followed by :)
    //
    // Key difference: old uses `::=` (double colon), new uses `:` (single colon) for typing

    let is_old_syntax = {
        let fork = input.fork();
        // Parse the category/first-param identifier
        if fork.parse::<Ident>().is_ok() {
            // Old syntax has :: after category, new syntax has : after param name
            fork.peek(Token![::])
        } else {
            // If no identifier, check for ^ (abstraction in new syntax)
            false
        }
    };

    let mut rule = if is_old_syntax {
        // OLD SYNTAX: Label . Category ::= items ;
        parse_grammar_rule_old(label, input)?
    } else {
        // NEW SYNTAX: Label . context |- pattern : Type ;
        parse_grammar_rule_new(label, input)?
    };

    rule.tier_directive = tier_directive;
    rule.doc_comment = doc_comment;
    Ok(rule)
}

/// Parse old BNFC-style syntax: `Label . Category ::= items ;`
fn parse_grammar_rule_old(label: Ident, input: ParseStream) -> SynResult<GrammarRule> {
    let category = input.parse::<Ident>()?;

    // Parse ::= (as two colons followed by equals)
    let _ = input.parse::<Token![::]>()?;
    let _ = input.parse::<Token![=]>()?;

    // Parse items until semicolon
    let mut items = Vec::new();
    while !input.peek(Token![;]) {
        if input.peek(syn::LitStr) {
            // Terminal: string literal
            let lit = input.parse::<syn::LitStr>()?;
            items.push(GrammarItem::Terminal(lit.value()));
        } else if input.peek(Token![<]) {
            // Binder: <Category>
            let _ = input.parse::<Token![<]>()?;
            let cat = input.parse::<Ident>()?;
            let _ = input.parse::<Token![>]>()?;
            items.push(GrammarItem::Binder { category: cat });
        } else {
            // Check if this is a collection type (HashBag, HashSet, Vec)
            let ident = input.parse::<Ident>()?;
            let ident_str = ident.to_string();

            if (ident_str == "HashBag" || ident_str == "HashSet" || ident_str == "Vec")
                && input.peek(syn::token::Paren)
            {
                // Collection: HashBag(Proc) sep "|" [delim "[" "]"]
                items.push(parse_collection(ident, input)?);
            } else {
                // NonTerminal: identifier
                items.push(GrammarItem::non_terminal(ident));
            }
        }
    }

    let _ = input.parse::<Token![;]>()?;

    // Infer binding structure: each Binder binds in the next NonTerminal
    let bindings = infer_bindings(&items);

    Ok(GrammarRule {
        label,
        category,
        items,
        bindings,
        term_context: None,
        syntax_pattern: None,
        rust_code: None,
        eval_mode: None,
        is_right_assoc: false,
        shares_level_with_previous: false,
        prefix_bp: None,
        tier_directive: None,
        is_auto_injected: false,
        doc_comment: None,
        is_canonical_synonym: false,
    })
}

/// Parse new judgement-style syntax: `Label . context |- pattern : Type [ ![code] mode ] ;`
fn parse_grammar_rule_new(label: Ident, input: ParseStream) -> SynResult<GrammarRule> {
    // Parse term context: param, param, ...
    let term_context = parse_term_context(input)?;

    // Parse |- (as | followed by -)
    if !input.peek(Token![|]) {
        return Err(input.error("expected '|-' after term context"));
    }
    let _ = input.parse::<Token![|]>()?;
    let _ = input.parse::<Token![-]>()?;

    // Parse syntax pattern until : Type
    let syntax_pattern = parse_syntax_pattern(input)?;

    // Parse : Type
    let _ = input.parse::<Token![:]>()?;
    let category = input.parse::<Ident>()?;

    // Parse optional Rust code block: ![code]
    let rust_code = if input.peek(Token![!]) && input.peek2(syn::token::Bracket) {
        let _ = input.parse::<Token![!]>()?;
        let content;
        syn::bracketed!(content in input);
        let code = content.parse::<syn::Expr>()?;
        Some(RustCodeBlock { code })
    } else {
        None
    };

    // Parse optional evaluation mode: fold, step
    let eval_mode = if input.peek(syn::Ident) {
        let fork = input.fork();
        let kw = fork.parse::<syn::Ident>()?;
        match kw.to_string().as_str() {
            "fold" | "step" => {
                let mode_ident = input.parse::<syn::Ident>()?;
                // ★ #141 G5. The `unreachable!()` here was justified by the
                // OUTER match on a FORK of the same input having already
                // accepted only `fold` / `step` — a claim about two matches
                // staying in step, held by nothing. This is a `syn::Result`
                // parser, so the refusal is a spanned parse error: the idiom the
                // arm four lines below already uses.
                match mode_ident.to_string().as_str() {
                    "fold" => Some(EvalMode::Fold),
                    "step" => Some(EvalMode::Step),
                    other => {
                        return Err(syn::Error::new(
                            mode_ident.span(),
                            format!(
                                "mettail internal error: the evaluation-mode lookahead \
                                 accepted `{other}` but the parser admits only `fold` and \
                                 `step`, so the two have drifted apart. This is a macro \
                                 bug, not a grammar bug — please report it."
                            ),
                        ));
                    },
                }
            },
            "right" | "prefix" | "canonical" | "same" => None, // handled below
            _ => {
                let bad = input.parse::<syn::Ident>()?;
                return Err(syn::Error::new(
                    bad.span(),
                    "expected 'fold', 'step', 'right', 'prefix(N)', 'canonical', 'same', or ';'",
                ));
            },
        }
    } else {
        None
    };

    // Parse optional annotations after eval mode: `right`, `prefix(N)`, `canonical`, `same`
    let mut is_right_assoc = false;
    let mut prefix_bp = None;
    // ★ SURFACE SYNONYMY (2026-07-26) — see `GrammarRule::is_canonical_synonym` for what
    // this declares and why it cannot be inferred.
    let mut is_canonical_synonym = false;
    // ★ PRECEDENCE LEVELS (2026-07-28) — see `GrammarRule::shares_level_with_previous`.
    // Order-independent with respect to `right`: `same right` and `right same` are the same
    // declaration, because precedence and associativity are orthogonal.
    let mut shares_level_with_previous = false;

    while input.peek(syn::Ident) {
        let fork = input.fork();
        if let Ok(kw) = fork.parse::<syn::Ident>() {
            if kw == "right" {
                let _ = input.parse::<syn::Ident>()?; // consume
                is_right_assoc = true;
            } else if kw == "same" {
                let _ = input.parse::<syn::Ident>()?; // consume
                shares_level_with_previous = true;
            } else if kw == "prefix" {
                let _ = input.parse::<syn::Ident>()?; // consume "prefix"
                                                      // Parse (N)
                let content;
                syn::parenthesized!(content in input);
                let bp_lit: syn::LitInt = content.parse()?;
                let bp_val: u8 = bp_lit.base10_parse()?;
                prefix_bp = Some(bp_val);
            } else if kw == "canonical" {
                let _ = input.parse::<syn::Ident>()?; // consume
                is_canonical_synonym = true;
            } else {
                return Err(syn::Error::new(
                    kw.span(),
                    "expected 'right', 'prefix(N)', 'canonical', 'same', or ';' after \
                     evaluation mode",
                ));
            }
        } else {
            break;
        }
    }

    // Parse ;
    let _ = input.parse::<Token![;]>()?;

    // Convert term_context to items and bindings for backward compatibility
    let (items, bindings) = convert_term_context_to_items(&term_context);

    Ok(GrammarRule {
        label,
        category,
        items,
        bindings,
        term_context: Some(term_context),
        syntax_pattern: Some(syntax_pattern),
        rust_code,
        eval_mode,
        is_right_assoc,
        shares_level_with_previous,
        prefix_bp,
        tier_directive: None,
        is_auto_injected: false,
        doc_comment: None,
        is_canonical_synonym,
    })
}

/// Parse term context: `n:Name, ^x.p:[Name -> Proc]`
fn parse_term_context(input: ParseStream) -> SynResult<Vec<TermParam>> {
    let mut params = Vec::new();

    loop {
        // Check for end of context (|-)
        if input.peek(Token![|]) {
            break;
        }

        // Parse one top-level parameter token slice. Delimited groups are one
        // token tree, so even a deeply nested `*opt(...)` chain is transferred
        // to the explicit parser below without recursively materializing its
        // entire remainder through `syn::ParseBuffer`.
        let mut tokens = proc_macro2::TokenStream::new();
        while !input.is_empty() && !input.peek(Token![,]) && !input.peek(Token![|]) {
            tokens.extend(std::iter::once(input.parse::<proc_macro2::TokenTree>()?));
        }
        let param = parse_term_param(tokens)?;
        params.push(param);

        // Check for comma separator
        if input.peek(Token![,]) {
            let _ = input.parse::<Token![,]>()?;
        } else {
            break;
        }
    }

    Ok(params)
}

/// Parse a single term parameter
///
/// - `n:Name` → Simple
/// - `^x.p:[Name -> Proc]` → Abstraction
/// - `^[xs].p:[Name* -> Proc]` → MultiAbstraction
/// - `?guard:Guard` → GuardBody (Phase 2C — predicated types)
fn parse_term_param(tokens: proc_macro2::TokenStream) -> SynResult<TermParam> {
    parse_term_param_tokens(tokens)
}

/// Parse the non-recursive leaves of the term-parameter grammar.
fn parse_non_optional_term_param(input: ParseStream) -> SynResult<TermParam> {
    // Guard slot: `?<name>:Guard` (Phase 2C, predicated types)
    //
    // The slot name declares where in the syntax pattern the guard
    // expression appears. The actual `BehavioralPred` is per-instance
    // runtime data: it's parsed at source-parse time by
    // `mettail_prattail::parser::predicate::PredicateParser` (Phase 1B)
    // and stored as a field on the generated enum variant.
    //
    // The literal `Guard` type marker is the only type currently
    // accepted for the slot. Future revisions may introduce
    // `?<name>:GuardKind<...>` variants; the `Guard` marker keeps
    // the surface syntax forward-compatible.
    if input.peek(Token![?]) {
        let _ = input.parse::<Token![?]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let type_marker = input.parse::<Ident>()?;
        if type_marker != "Guard" {
            return Err(syn::Error::new(
                type_marker.span(),
                "expected `Guard` after `?<name>:` — only the `Guard` \
                 type marker is currently supported for guard slot parameters",
            ));
        }
        return Ok(TermParam::GuardBody { name });
    }

    if input.peek(Token![^]) {
        // Abstraction: ^x.p:Type or ^[xs].p:Type
        let _ = input.parse::<Token![^]>()?;

        let is_multi = input.peek(syn::token::Bracket);

        let binder = if is_multi {
            // ^[xs].p - multi-binder
            let content;
            syn::bracketed!(content in input);
            content.parse::<Ident>()?
        } else {
            // ^x.p - single binder
            input.parse::<Ident>()?
        };

        // Parse .
        let _ = input.parse::<Token![.]>()?;

        // Parse body name
        let body = input.parse::<Ident>()?;

        // Parse :Type
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<TypeExpr>()?;

        if is_multi {
            Ok(TermParam::MultiAbstraction { binder, body, ty })
        } else {
            Ok(TermParam::Abstraction { binder, body, ty })
        }
    } else {
        // Simple: n:Name
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<TypeExpr>()?;

        Ok(TermParam::Simple { name, ty })
    }
}

/// Split one optional group's token stream at top-level commas. Delimited
/// subgroups are single token trees, so commas inside types or nested `*opt`
/// groups never become separators here. A trailing comma is accepted exactly
/// as before; leading and repeated commas retain an empty segment which the
/// leaf parser rejects.
fn split_term_param_tokens(tokens: proc_macro2::TokenStream) -> Vec<proc_macro2::TokenStream> {
    let mut segments = Vec::new();
    let mut current = proc_macro2::TokenStream::new();
    for tree in tokens {
        if matches!(&tree, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ',') {
            segments.push(std::mem::take(&mut current));
        } else {
            current.extend(std::iter::once(tree));
        }
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

/// Parse a complete term parameter with an explicit task/value machine.
fn parse_term_param_tokens(tokens: proc_macro2::TokenStream) -> SynResult<TermParam> {
    enum Parsed {
        Leaf(TermParam),
        Optional(Vec<proc_macro2::TokenStream>),
    }

    enum Task {
        Parse(proc_macro2::TokenStream),
        AssembleOptional(usize),
    }

    fn parse_one(tokens: proc_macro2::TokenStream) -> SynResult<Parsed> {
        let trees: Vec<_> = tokens.clone().into_iter().collect();
        if trees.len() >= 2
            && matches!(&trees[0], proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '*')
            && matches!(&trees[1], proc_macro2::TokenTree::Ident(keyword) if keyword == "opt")
        {
            if trees.len() != 3 {
                return Err(syn::Error::new(
                    trees[1].span(),
                    "expected exactly one parenthesized parameter group after `*opt`",
                ));
            }
            let proc_macro2::TokenTree::Group(group) = &trees[2] else {
                return Err(syn::Error::new(trees[2].span(), "expected parentheses after `*opt`"));
            };
            if group.delimiter() != proc_macro2::Delimiter::Parenthesis {
                return Err(syn::Error::new(group.span(), "expected parentheses after `*opt`"));
            }
            Ok(Parsed::Optional(split_term_param_tokens(group.stream())))
        } else {
            syn::parse::Parser::parse2(parse_non_optional_term_param, tokens).map(Parsed::Leaf)
        }
    }

    let mut tasks = vec![Task::Parse(tokens)];
    let mut values = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            Task::Parse(tokens) => match parse_one(tokens)? {
                Parsed::Leaf(param) => values.push(param),
                Parsed::Optional(children) => {
                    tasks.push(Task::AssembleOptional(children.len()));
                    tasks.extend(children.into_iter().rev().map(Task::Parse));
                },
            },
            Task::AssembleOptional(child_count) => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("optional assembly must follow all child parses");
                let params = values.split_off(first_child);
                values.push(TermParam::Optional { params });
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("the root optional assembly always emits one value"))
}

/// Parse syntax pattern until we hit `:` followed by an identifier (the type)
///
/// Syntax patterns use quoted strings for all literals:
///   `"for" "(" x "<-" n ")" "{" p "}"`
///
/// Pattern operations:
///   - `#sep(coll, "sep")` or `coll.#sep("sep")` - separated list
///   - `#zip(a, b)` - pair collections
///   - `#map(source, |x| expr)` or `source.#map(|x| expr)` - transform
///   - `#opt(expr)` - optional
///
/// - Quoted strings become `Literal` tokens (keywords, punctuation, operators)
/// - Unquoted identifiers become `Param` tokens (parameter references only)
/// - `#name(...)` or `ident.#name(...)` become pattern operations
fn parse_syntax_pattern(input: ParseStream) -> SynResult<Vec<SyntaxExpr>> {
    let mut exprs = Vec::new();

    loop {
        // Check if we've reached `: Type` at the end
        if is_end_of_syntax_pattern(input) {
            break;
        }

        exprs.push(parse_syntax_expr(input)?);
    }

    Ok(exprs)
}

/// Check if we're at the end of a syntax pattern (`: Type` optionally followed by `;` or `![code]`)
fn is_end_of_syntax_pattern(input: ParseStream) -> bool {
    if input.peek(Token![:]) {
        let fork = input.fork();
        let _ = fork.parse::<Token![:]>();
        if fork.peek(Ident) {
            let _ = fork.parse::<Ident>();
            // End of pattern: `;`, `![code]`, or eval_mode/assoc keyword (Ident)
            return fork.peek(Token![;]) || fork.peek(Token![!]) || fork.peek(Ident);
        }
    }
    false
}

/// Parse a single syntax expression (literal, param, or pattern op)
pub(crate) fn parse_syntax_expr(input: ParseStream) -> SynResult<SyntaxExpr> {
    // Check for pattern operation: *name(...)
    if input.peek(Token![*]) {
        // L9-4: `*flt(bind, open, close)` routes to `SyntaxExpr::GuestBody`
        // (a guest-body capture), NOT the generic `SyntaxExpr::Op` wrapper the
        // other `*` meta-ops produce.
        let fork = input.fork();
        let _ = fork.parse::<Token![*]>();
        if fork.parse::<Ident>().map(|n| n == "flt").unwrap_or(false) {
            return parse_flt_op(input);
        }
        return parse_pattern_op_expr(input);
    }

    // Check for identifier (could be param or start of method chain)
    if input.peek(Ident) {
        let id = input.parse::<Ident>()?;

        // L9-3: `v@Tok` bind form — `v` binds the text of a token of the custom
        // KIND `Tok`. A bare `Tok` (no bind) is parsed as `Param(Tok)` below and
        // reclassified to `TokenKind{bind:None}` by the post-parse pass when
        // `Tok` is a declared token name (decision D-1; `v:Tok` is NOT supported
        // — a colon collides with the `:Category` rule terminator).
        //
        // The `peek2(Ident)` guard is LOAD-BEARING: the guards block's
        // per-predicate annotation form `<pattern> @[selectivity(..), cost(..)]`
        // ALSO follows a param with `@`, but with a `[` (not an identifier).
        // Without the guard, `y @[...]` consumed the `@` as a capture start and
        // then failed with "expected identifier" on the `[`. Requiring an
        // identifier after `@` keeps `v@Tok` a capture while leaving `@[...]`
        // for the annotation parser (the pre-L9-3 behavior).
        if input.peek(Token![@]) && input.peek2(Ident) {
            let _ = input.parse::<Token![@]>()?;
            let tok = input.parse::<Ident>()?;
            return Ok(SyntaxExpr::TokenKind { name: tok, bind: Some(id) });
        }

        // Check for method chain: ident.#name(...)
        if input.peek(Token![.]) && input.peek2(Token![*]) {
            let _ = input.parse::<Token![.]>()?;
            let op = parse_pattern_op_with_receiver(input, PatternOp::Var(id))?;
            return Ok(SyntaxExpr::Op(op));
        }

        // Just a parameter reference
        return Ok(SyntaxExpr::Param(id));
    }

    // String literal
    if input.peek(syn::LitStr) {
        let lit = input.parse::<syn::LitStr>()?;
        return Ok(SyntaxExpr::Literal(lit.value()));
    }

    Err(syn::Error::new(
        input.span(),
        "Expected parameter reference (identifier), quoted literal (string), or pattern operation (#sep, #map, etc.)",
    ))
}

/// Parse a pattern operation starting with #
fn parse_pattern_op_expr(input: ParseStream) -> SynResult<SyntaxExpr> {
    let op = parse_pattern_op(input)?;
    Ok(SyntaxExpr::Op(op))
}

/// Parse a pattern operation: #name(args)
fn parse_pattern_op(input: ParseStream) -> SynResult<PatternOp> {
    let _ = input.parse::<Token![*]>()?;
    let name = input.parse::<Ident>()?;
    let name_str = name.to_string();

    let content;
    syn::parenthesized!(content in input);

    let op = match name_str.as_str() {
        "sep" => parse_sep_op(&content)?,
        "zip" => parse_zip_op(&content)?,
        "map" => parse_map_op(&content)?,
        "opt" => parse_opt_op(&content)?,
        _ => {
            return Err(syn::Error::new(
                name.span(),
                format!(
                    "Unknown pattern operation: #{}. Expected #sep, #zip, #map, or #opt",
                    name_str
                ),
            ));
        },
    };

    // Check for method chain continuation: .#name(...)
    if input.peek(Token![.]) && input.peek2(Token![*]) {
        let _ = input.parse::<Token![.]>()?;
        return parse_pattern_op_with_receiver(input, op);
    }

    Ok(op)
}

/// Parse pattern operation with a receiver (method chain style)
fn parse_pattern_op_with_receiver(input: ParseStream, receiver: PatternOp) -> SynResult<PatternOp> {
    let _ = input.parse::<Token![*]>()?;
    let name = input.parse::<Ident>()?;
    let name_str = name.to_string();

    let content;
    syn::parenthesized!(content in input);

    let op = match name_str.as_str() {
        "sep" => {
            // receiver.#sep("sep") - receiver must be a collection or result of map
            let separator = content.parse::<syn::LitStr>()?.value();

            // Extract collection name from receiver
            let collection = match &receiver {
                PatternOp::Var(id) => id.clone(),
                PatternOp::Map { .. } | PatternOp::Zip { .. } => {
                    // For Map/Zip, preserve the chain as source
                    return Ok(PatternOp::Sep {
                        collection: Ident::new("__chain__", proc_macro2::Span::call_site()),
                        separator,
                        source: Some(Box::new(receiver)),
                    });
                },
                _ => {
                    return Err(syn::Error::new(
                        name.span(),
                        "#sep receiver must be a collection parameter or result of #map/#zip",
                    ));
                },
            };
            PatternOp::Sep { collection, separator, source: None }
        },
        "map" => {
            // receiver.#map(|x| expr)
            let (params, body) = parse_map_closure(&content)?;
            PatternOp::Map { source: Box::new(receiver), params, body }
        },
        _ => {
            return Err(syn::Error::new(
                name.span(),
                format!(
                    "Cannot chain #{} after pattern operation. Expected #sep or #map",
                    name_str
                ),
            ));
        },
    };

    // Check for further chaining
    if input.peek(Token![.]) && input.peek2(Token![*]) {
        let _ = input.parse::<Token![.]>()?;
        return parse_pattern_op_with_receiver(input, op);
    }

    Ok(op)
}

/// Parse #sep(coll, "sep")
fn parse_sep_op(content: ParseStream) -> SynResult<PatternOp> {
    let collection = content.parse::<Ident>()?;
    let _ = content.parse::<Token![,]>()?;
    let separator = content.parse::<syn::LitStr>()?.value();
    Ok(PatternOp::Sep { collection, separator, source: None })
}

/// L9-4: parse `*flt(bind, open, close)` → [`SyntaxExpr::GuestBody`]. `bind` is
/// the FltNode capture name; `open`/`close` are the opener/closer token KINDS
/// (e.g. `FltOpenBacktick` / `FltCloseBacktick`).
fn parse_flt_op(input: ParseStream) -> SynResult<SyntaxExpr> {
    let _ = input.parse::<Token![*]>()?; // *
    let _ = input.parse::<Ident>()?; // flt
    let content;
    syn::parenthesized!(content in input);
    let bind = content.parse::<Ident>()?;
    let _ = content.parse::<Token![,]>()?;
    let open = content.parse::<Ident>()?;
    let _ = content.parse::<Token![,]>()?;
    let close = content.parse::<Ident>()?;
    Ok(SyntaxExpr::GuestBody { open, close, bind })
}

/// Parse #zip(a, b)
fn parse_zip_op(content: ParseStream) -> SynResult<PatternOp> {
    let left = content.parse::<Ident>()?;
    let _ = content.parse::<Token![,]>()?;
    let right = content.parse::<Ident>()?;
    Ok(PatternOp::Zip { left, right })
}

/// Parse #map(source, |x| expr)
fn parse_map_op(content: ParseStream) -> SynResult<PatternOp> {
    // Source can be an identifier or a pattern op
    let source = if content.peek(Token![*]) {
        parse_pattern_op(content)?
    } else {
        let id = content.parse::<Ident>()?;
        PatternOp::Var(id)
    };

    let _ = content.parse::<Token![,]>()?;
    let (params, body) = parse_map_closure(content)?;

    Ok(PatternOp::Map { source: Box::new(source), params, body })
}

/// Parse |x| expr or |x, y| expr (closure in #map)
fn parse_map_closure(input: ParseStream) -> SynResult<(Vec<Ident>, Vec<SyntaxExpr>)> {
    let _ = input.parse::<Token![|]>()?;

    let mut params = Vec::new();
    params.push(input.parse::<Ident>()?);

    while input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
        if input.peek(Token![|]) {
            break;
        }
        params.push(input.parse::<Ident>()?);
    }

    let _ = input.parse::<Token![|]>()?;

    // Parse body - could be multiple syntax exprs
    let mut body = Vec::new();
    while !input.is_empty() {
        body.push(parse_syntax_expr(input)?);
    }

    Ok((params, body))
}

/// Parse #opt(expr)
fn parse_opt_op(content: ParseStream) -> SynResult<PatternOp> {
    let mut inner = Vec::new();
    while !content.is_empty() {
        inner.push(parse_syntax_expr(content)?);
    }
    Ok(PatternOp::Opt { inner })
}

/// Convert term context to old-style items and bindings for backward compatibility.
///
/// **Stage 3.13 (2026-04-30):** made `pub` so auto-injection codegen
/// (`macros/src/gen/runtime/wpda_codegen/auto_inject.rs::make_injection_rule`)
/// can synthesize judgement-style GrammarRules with both the new-style
/// `term_context` field AND the legacy `items` field populated identically
/// to how the DSL parser at `:589` does it. Without this, downstream
/// codegen paths that read `rule.items` (test-gen, lint, parser arm
/// emission) treat synthetic rules as nullary constructors and emit
/// type-mismatched code.
pub fn convert_term_context_to_items(
    term_context: &[TermParam],
) -> (Vec<GrammarItem>, Vec<(usize, Vec<usize>)>) {
    let mut items = Vec::new();
    let mut bindings = Vec::new();

    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                // Simple param becomes NonTerminal with the base type name
                if let TypeExpr::Base(type_name) = ty {
                    items.push(GrammarItem::non_terminal(type_name.clone()));
                } else if let TypeExpr::Collection { coll_type, element } = ty {
                    // Collection type
                    if let TypeExpr::Base(elem_name) = element.as_ref() {
                        items.push(GrammarItem::Collection {
                            coll_type: coll_type.clone(),
                            element_type: elem_name.clone(),
                            separator: "|".to_string(), // Default, should be specified in syntax
                            delimiters: None,
                        });
                    }
                } else if let TypeExpr::Map { key, value } = ty {
                    // Phase 4 #5b (2026-05-12): `HashMap(K, V)` Map type
                    // in a Class-2 binder slot. The downstream codegen
                    // (term_gen/random.rs) checks `rule.items` for
                    // `GrammarItem::Collection` to decide whether a rule
                    // has a collection field; without this case it would
                    // miss HashMap slots and emit a variant constructor
                    // with the wrong arity. Lower to
                    // `GrammarItem::Collection { coll_type: HashMap,
                    // element_type: value }` mirroring the K==V invariant
                    // enforced by `classify_binder`.
                    if let (TypeExpr::Base(k_name), TypeExpr::Base(v_name)) =
                        (key.as_ref(), value.as_ref())
                    {
                        if k_name == v_name {
                            items.push(GrammarItem::Collection {
                                coll_type: CollectionType::HashMap,
                                element_type: v_name.clone(),
                                separator: ",".to_string(),
                                delimiters: None,
                            });
                        }
                    }
                }
            },
            TermParam::Abstraction { ty, .. } => {
                // Abstraction: ^x.p:[Name -> Proc]
                // This becomes: Binder for Name, NonTerminal for Proc
                if let TypeExpr::Arrow { domain, codomain } = ty {
                    let binder_idx = items.len();

                    if let TypeExpr::Base(binder_type) = domain.as_ref() {
                        items.push(GrammarItem::Binder { category: binder_type.clone() });
                    }

                    let body_idx = items.len();
                    if let TypeExpr::Base(body_type) = codomain.as_ref() {
                        items.push(GrammarItem::non_terminal(body_type.clone()));
                    }

                    bindings.push((binder_idx, vec![body_idx]));
                }
            },
            TermParam::MultiAbstraction { ty, .. } => {
                // Multi-abstraction: ^[xs].p:[Name* -> Proc]
                // This needs special handling for multiple binders
                if let TypeExpr::Arrow { domain, codomain } = ty {
                    let binder_idx = items.len();

                    if let TypeExpr::MultiBinder(inner) = domain.as_ref() {
                        if let TypeExpr::Base(binder_type) = inner.as_ref() {
                            // Represent the multi-binder domain by its binder category.
                            items.push(GrammarItem::Binder { category: binder_type.clone() });
                        }
                    }

                    let body_idx = items.len();
                    if let TypeExpr::Base(body_type) = codomain.as_ref() {
                        items.push(GrammarItem::non_terminal(body_type.clone()));
                    }

                    bindings.push((binder_idx, vec![body_idx]));
                }
            },
            TermParam::GuardBody { .. } => {
                // Guard bodies are evaluated by the behavioral guard evaluator
                // and do not produce traditional grammar items or bindings.
            },
            TermParam::Optional { params: inner } => {
                // Opt-Group (2026-04-29 update): the runtime variant emits
                // ONE field per inner Simple/Abstraction (wrapped in
                // `Option<Box<T>>`). Downstream emitters that walk
                // `rule.items` (Ascent subterm pools, fold-rule generators,
                // pool-arm constructor patterns) need a matching item per
                // inner param so the destructure pattern length equals the
                // variant arity. Recursively flatten and emit synthetic
                // items mirroring the inner types.
                fn flatten_optional_items(inner: &[TermParam], items: &mut Vec<GrammarItem>) {
                    let mut frames = vec![inner.iter()];
                    while let Some(frame) = frames.last_mut() {
                        let Some(p) = frame.next() else {
                            frames.pop();
                            continue;
                        };
                        match p {
                            TermParam::Simple { ty, .. } => {
                                if let TypeExpr::Base(type_name) = ty {
                                    items.push(GrammarItem::non_terminal(type_name.clone()));
                                } else if let TypeExpr::Collection { coll_type, element } = ty {
                                    if let TypeExpr::Base(elem_name) = element.as_ref() {
                                        items.push(GrammarItem::Collection {
                                            coll_type: coll_type.clone(),
                                            element_type: elem_name.clone(),
                                            separator: "|".to_string(),
                                            delimiters: None,
                                        });
                                    }
                                } else if let TypeExpr::Map { key, value } = ty {
                                    // Phase 4 #5b (2026-05-12): HashMap(K, V)
                                    // inside *opt(...). Mirror the outer
                                    // Simple-param handling: lower to
                                    // GrammarItem::Collection {
                                    // coll_type: HashMap, element_type: V }
                                    // when K == V.
                                    if let (TypeExpr::Base(k_name), TypeExpr::Base(v_name)) =
                                        (key.as_ref(), value.as_ref())
                                    {
                                        if k_name == v_name {
                                            items.push(GrammarItem::Collection {
                                                coll_type: CollectionType::HashMap,
                                                element_type: v_name.clone(),
                                                separator: ",".to_string(),
                                                delimiters: None,
                                            });
                                        }
                                    }
                                }
                            },
                            TermParam::Abstraction { ty, .. }
                            | TermParam::MultiAbstraction { ty, .. } => {
                                if let TypeExpr::Arrow { codomain, .. } = ty {
                                    if let TypeExpr::Base(body_type) = codomain.as_ref() {
                                        items.push(GrammarItem::non_terminal(body_type.clone()));
                                    }
                                }
                            },
                            TermParam::GuardBody { .. } => {},
                            TermParam::Optional { params: nested } => {
                                frames.push(nested.iter());
                            },
                        }
                    }
                }
                flatten_optional_items(inner, &mut items);
            },
        }
    }

    (items, bindings)
}

/// F1 follow-up Plan 3 / Ambient cluster (2026-05-10): inverse of
/// `convert_term_context_to_items`. Synthesizes a judgement-style
/// `(term_context, syntax_pattern)` pair from a BNF-style `items`
/// representation, in-place. Used by `synthetic.rs::build_per_category_rules`
/// to normalize old-BNF rules so downstream classifiers (`classify_binder`,
/// `classify_postfix_mixfix`, `classify_collection`) — which read
/// `term_context` + `syntax_pattern` — can dispatch them.
///
/// Conversion rules:
/// - `GrammarItem::Terminal(text)` → `SyntaxExpr::Literal(text)` only.
/// - `GrammarItem::NonTerminal { ident, kind: Category }` → fresh `pN`
///   param: `TermParam::Simple { name: pN, ty: TypeExpr::Base(ident) }` +
///   `SyntaxExpr::Param(pN)`. If preceded by a pending `Binder`, instead
///   form an `Abstraction { binder, body, ty: Arrow{domain, codomain} }`.
/// - `GrammarItem::Binder { category }` → flag pending; pair with next
///   NonTerminal as Abstraction.
/// - `GrammarItem::Collection { coll_type, element_type, separator,
///   delimiters: Some((open, close)) }` →
///   `TermParam::Simple { name: "elems", ty: Collection {...} }` +
///   `[Literal(open), Op(Sep), Literal(close)]`. Collections without
///   delimiters are out-of-scope (rare; return early without modifying).
///
/// Early-return conditions (function leaves rule unchanged):
/// - `term_context` or `syntax_pattern` already set (rule is judgement-form).
/// - Items contain a non-Category `NonTerminal` (Var/Integer/Boolean/etc.):
///   these are atomic/literal-rule shapes handled by `classify_atomic`,
///   not the binder/mixfix/collection classifiers.
///
/// The synthesized parameter names are `p0`, `p1`, ... in declaration
/// order — old-BNF rules have no user param names, so there's no
/// collision risk.
pub fn convert_items_to_term_context(rule: &mut GrammarRule) {
    use proc_macro2::Span;

    // Skip if already judgement-form (e.g., PNew in ambient.rs).
    if rule.term_context.is_some() || rule.syntax_pattern.is_some() {
        return;
    }

    // Check: do all items qualify for conversion? If any NonTerminal is
    // non-Category (Var, Integer, etc.), defer to the existing atomic/Var
    // classifier paths — the rule isn't a binder/mixfix/collection shape.
    for item in &rule.items {
        if let GrammarItem::NonTerminal { kind, .. } = item {
            if *kind != NonTerminalKind::Category {
                return;
            }
        }
    }

    let mut tc: Vec<TermParam> = Vec::new();
    let mut sp: Vec<SyntaxExpr> = Vec::new();
    let mut next_param_id: usize = 0;
    let mut pending_binder: Option<Ident> = None;

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(text) => {
                sp.push(SyntaxExpr::Literal(text.clone()));
            },
            GrammarItem::NonTerminal { ident, kind: NonTerminalKind::Category } => {
                let pname = Ident::new(&format!("p{}", next_param_id), Span::call_site());
                next_param_id += 1;

                if let Some(binder_cat) = pending_binder.take() {
                    // Abstraction: binder_cat -> ident
                    let body_pname = Ident::new(&format!("p{}", next_param_id), Span::call_site());
                    next_param_id += 1;
                    tc.push(TermParam::Abstraction {
                        binder: pname.clone(),
                        body: body_pname.clone(),
                        ty: TypeExpr::Arrow {
                            domain: Box::new(TypeExpr::Base(binder_cat)),
                            codomain: Box::new(TypeExpr::Base(ident.clone())),
                        },
                    });
                    // Both binder name and body appear in syntax pattern.
                    sp.push(SyntaxExpr::Param(pname));
                    sp.push(SyntaxExpr::Param(body_pname));
                } else {
                    tc.push(TermParam::Simple {
                        name: pname.clone(),
                        ty: TypeExpr::Base(ident.clone()),
                    });
                    sp.push(SyntaxExpr::Param(pname));
                }
            },
            // ★ #141 G5. Non-Category NonTerminals (Var/Integer/Boolean/…) are
            // supposed to have caused the early-return above. That is a claim
            // about a gate twenty lines away, held by nothing, and this function
            // returns `()` — it has no channel to refuse through. So it does what
            // the gate would have done: LEAVES THE RULE UNCONVERTED (`return`,
            // not `unreachable!`), which is the same outcome as the early-return
            // the claim says already happened, and the one shape whose result is
            // identical whether the claim holds or not.
            GrammarItem::NonTerminal { .. } => return,
            GrammarItem::Binder { category } => {
                pending_binder = Some(category.clone());
            },
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => {
                if let Some((open, close)) = delimiters {
                    let elems_name = Ident::new("elems", Span::call_site());
                    tc.push(TermParam::Simple {
                        name: elems_name.clone(),
                        ty: TypeExpr::Collection {
                            coll_type: coll_type.clone(),
                            element: Box::new(TypeExpr::Base(element_type.clone())),
                        },
                    });
                    sp.push(SyntaxExpr::Literal(open.clone()));
                    sp.push(SyntaxExpr::Op(PatternOp::Sep {
                        collection: elems_name,
                        separator: separator.clone(),
                        source: None,
                    }));
                    sp.push(SyntaxExpr::Literal(close.clone()));
                } else {
                    // Sep-only collection (no delimiters): out of scope.
                    return;
                }
            },
        }
    }

    // Pending binder with no body NonTerminal: invalid grammar — defer.
    if pending_binder.is_some() {
        return;
    }

    // Skip pure-literal rules (no params): these are TerminalKeyword shapes
    // handled by the atomic classifier (e.g., `PZero . Proc ::= "0" ;`).
    if tc.is_empty() {
        return;
    }

    rule.term_context = Some(tc);
    rule.syntax_pattern = Some(sp);
}

/// Infer binding structure from items
/// Each Binder at position i binds in the next NonTerminal/Binder at position j > i
fn infer_bindings(items: &[GrammarItem]) -> Vec<(usize, Vec<usize>)> {
    let mut bindings = Vec::new();

    for (i, item) in items.iter().enumerate() {
        if matches!(item, GrammarItem::Binder { .. }) {
            // Find the next non-terminal item(s) that this binder binds in
            let mut bound_indices = Vec::new();

            for (j, next_item) in items.iter().enumerate().skip(i + 1) {
                match next_item {
                    GrammarItem::NonTerminal { .. } | GrammarItem::Binder { .. } => {
                        bound_indices.push(j);
                        break; // For now, bind only in the immediately following item
                    },
                    GrammarItem::Terminal(_) | GrammarItem::Collection { .. } => continue,
                }
            }

            if !bound_indices.is_empty() {
                bindings.push((i, bound_indices));
            }
        }
    }

    bindings
}

/// Parse a collection specification: HashBag(Proc) sep "|" [delim "[" "]"]
fn parse_collection(coll_type_ident: Ident, input: ParseStream) -> SynResult<GrammarItem> {
    // Determine collection type
    let coll_type = match coll_type_ident.to_string().as_str() {
        "HashBag" => CollectionType::HashBag,
        "HashSet" => CollectionType::HashSet,
        "Vec" => CollectionType::Vec,
        _ => {
            return Err(syn::Error::new(
                coll_type_ident.span(),
                "expected HashBag, HashSet, or Vec",
            ));
        },
    };

    // Parse (ElementType)
    let content;
    syn::parenthesized!(content in input);
    let element_type = content.parse::<Ident>()?;

    // Parse sep "separator"
    let sep_kw = input.parse::<Ident>()?;
    if sep_kw != "sep" {
        return Err(syn::Error::new(sep_kw.span(), "expected 'sep' after collection element type"));
    }
    let separator: syn::LitStr = input.parse()?;
    let separator_value = separator.value();

    // Validate separator is non-empty
    if separator_value.is_empty() {
        return Err(syn::Error::new(separator.span(), "separator cannot be empty"));
    }

    // Optional: delim "open" "close"
    let delimiters = if input.peek(Ident) {
        let lookahead = input.fork().parse::<Ident>()?;
        if lookahead == "delim" {
            let delim_kw = input.parse::<Ident>()?;
            if delim_kw != "delim" {
                return Err(syn::Error::new(delim_kw.span(), "expected 'delim'"));
            }
            let open: syn::LitStr = input.parse()?;
            let close: syn::LitStr = input.parse()?;

            let open_value = open.value();
            let close_value = close.value();

            // Validate delimiters are non-empty
            if open_value.is_empty() {
                return Err(syn::Error::new(open.span(), "open delimiter cannot be empty"));
            }
            if close_value.is_empty() {
                return Err(syn::Error::new(close.span(), "close delimiter cannot be empty"));
            }

            Some((open_value, close_value))
        } else {
            None
        }
    } else {
        None
    };

    Ok(GrammarItem::Collection {
        coll_type,
        element_type,
        separator: separator_value,
        delimiters,
    })
}

#[cfg(test)]
mod fixture_tests {
    use super::*;
    use syn::parse::Parser;

    /// ★ THE RECURRENCE GUARD.
    ///
    /// `rule_fixture` claims to hold "every field's documented default". That claim is only
    /// worth something if it is MEASURED, because the compiler cannot check a doc comment:
    /// when a field is added, `rule_fixture`'s struct literal fails to compile (good — the
    /// default must be chosen), but nothing would otherwise stop the chosen value from
    /// disagreeing with what the DSL parser actually produces for an unannotated rule. A
    /// fixture whose defaults have drifted from the parser's is a fixture that tests a
    /// grammar the language cannot express.
    ///
    /// So: parse a rule that declares NOTHING beyond its shape, transplant the six CONTENT
    /// fields (which carry the rule's identity and syntax, not a default) onto a fixture,
    /// and require the two to be indistinguishable.
    ///
    /// The comparison is on `Debug` output rather than field-by-field precisely so that it
    /// covers fields that do not exist yet — `GrammarRule` has no `PartialEq`, and a
    /// hand-written field-by-field comparison would silently ignore the fifteenth field the
    /// moment somebody adds it, which is the exact failure this guard is for. If a future
    /// field is CONTENT rather than an annotation, this test fails and the author must add
    /// it to the transplant list — a deliberate decision, made once, in the open.
    #[test]
    fn rule_fixture_matches_parser_defaults() {
        // `Proj . v:Int |- v : BigInt ;` — a judgement-style rule with no `![…]` body, no
        // `fold`/`step`, no `right`, no `prefix(N)`, no `canonical`, no `#[tier(…)]`, and no
        // doc comment. Every annotation field therefore takes the parser's own default.
        let parsed = Parser::parse_str(parse_grammar_rule, "Proj . v:Int |- v : BigInt ;")
            .expect("the unannotated judgement-style rule parses");

        // The six CONTENT fields: what this particular rule IS, as opposed to what it leaves
        // unsaid. They are transplanted, never defaulted.
        let expected = GrammarRule {
            items: parsed.items.clone(),
            bindings: parsed.bindings.clone(),
            term_context: parsed.term_context.clone(),
            syntax_pattern: parsed.syntax_pattern.clone(),
            ..rule_fixture(parsed.label.clone(), parsed.category.clone())
        };

        assert_eq!(
            format!("{:#?}", expected),
            format!("{:#?}", parsed),
            "`rule_fixture` no longer agrees with the DSL parser on some field's default. \
             Either the fixture default is wrong, or the newly added field is CONTENT (like \
             `items`/`syntax_pattern`) and belongs in this test's transplant list."
        );
    }

    /// The old (BNFC) rule shape defaults identically — `rule_fixture` is not specific to
    /// one of the two surface styles, and `term_context: None` is the shape it starts in.
    #[test]
    fn rule_fixture_matches_parser_defaults_for_old_style_rules() {
        let parsed = Parser::parse_str(parse_grammar_rule, "PZero . Proc ::= \"Nil\" ;")
            .expect("the unannotated BNFC-style rule parses");

        let expected = GrammarRule {
            items: parsed.items.clone(),
            bindings: parsed.bindings.clone(),
            ..rule_fixture(parsed.label.clone(), parsed.category.clone())
        };

        assert_eq!(format!("{:#?}", expected), format!("{:#?}", parsed));
        // The BNFC shape leaves both judgement-style fields unset, which is precisely the
        // fixture's own starting shape — so no transplant is needed for them.
        assert!(parsed.term_context.is_none());
        assert!(parsed.syntax_pattern.is_none());
    }

    /// The converse of the guard: the parser DOES set `is_canonical_synonym` when the rule
    /// says `canonical`, so `false` is a default rather than a constant. Without this, a
    /// fixture-side `false` and a parser-side hard-coded `false` would be indistinguishable.
    #[test]
    fn canonical_annotation_departs_from_the_default() {
        let annotated = Parser::parse_str(
            parse_grammar_rule,
            "NQuoteShort . p:Proc |- \"@\" p : Name fold prefix(220) canonical ;",
        )
        .expect("the `canonical`-annotated rule parses");

        assert!(annotated.is_canonical_synonym);
        assert!(
            !rule_fixture(annotated.label.clone(), annotated.category.clone()).is_canonical_synonym
        );
    }
}

#[cfg(test)]
#[path = "../tests/support/term_param_recursive_oracle.rs"]
mod term_param_recursive_oracle;
