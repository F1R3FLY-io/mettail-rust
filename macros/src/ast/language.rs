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

        // Parse: types { ... }
        let types = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "types" {
                parse_types(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
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

fn parse_types(input: ParseStream) -> SynResult<Vec<LangType>> {
    let types_ident = input.parse::<Ident>()?;
    if types_ident != "types" {
        return Err(syn::Error::new(types_ident.span(), "expected 'types'"));
    }

    let content;
    syn::braced!(content in input);

    let mut types = Vec::new();
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
            // Regular type: just a name
            let name = content.parse::<Ident>()?;
            types.push(LangType { name, native_type: None });
        }

        if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(types)
}

/// Public wrapper for `parse_types` for use by `fragment.rs`.
pub fn parse_types_public(input: ParseStream) -> SynResult<Vec<LangType>> {
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
    } else {
        Err(syn::Error::new(
            first.span(),
            "expected premise: 'x # term', 'S ~> T', 'rel(args)', or 'xs.*map(|x| ...)'",
        ))
    }
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
