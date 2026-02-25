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
pub struct LanguageDef {
    pub name: Ident,
    /// Configuration options parsed from `options { ... }` block. Empty if block omitted.
    pub options: HashMap<String, AttributeValue>,
    pub types: Vec<LangType>,
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
    /// Parameter types (e.g., [Proc, Proc])
    pub param_types: Vec<Ident>,
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
}

/// Equation in unified judgement syntax
/// Syntax: Name . type_context | prop_context |- lhs = rhs ;
/// Example: ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
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
}

/// Rewrite rule in unified judgement syntax
/// Syntax: Name . type_context | prop_context |- lhs ~> rhs ;
/// Example: ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
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

/// Delimiter parameters for List/Bag literal syntax (open, close, separator).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectionDelimiters {
    pub open: String,
    pub close: String,
    pub sep: String,
}

/// Collection category kind (List or Bag) with optional delimiters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CollectionCategory {
    List(CollectionDelimiters),
    Bag(CollectionDelimiters),
}

impl CollectionCategory {
    /// Default delimiters for List: `[`, `]`, `,`
    pub fn list_defaults() -> CollectionDelimiters {
        CollectionDelimiters {
            open: "[".to_string(),
            close: "]".to_string(),
            sep: ",".to_string(),
        }
    }
    /// Default delimiters for Bag: `{`, `}`, `,`
    pub fn bag_defaults() -> CollectionDelimiters {
        CollectionDelimiters {
            open: "{".to_string(),
            close: "}".to_string(),
            sep: ",".to_string(),
        }
    }
}

/// Export: category name, optionally with native Rust type or collection kind
/// types { Elem; Name; ![i32] as Int; List; Bag ["{", "}", ","]; }
pub struct LangType {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
    /// Optional collection category (List or Bag) with delimiters for literal syntax
    pub collection_kind: Option<CollectionCategory>,
}

use super::grammar::GrammarItem;

/// Extract the element type Ident from a collection native type (e.g. Vec<Proc> -> Proc, HashBag<Proc> -> Proc).
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

    /// True if this category has any constructor with a field of type List or Bag (e.g. Proc with ProcList/ProcBag).
    /// Used to force Debug display for types that contain Vec<Proc> or HashBag<Proc>.
    pub fn type_has_list_or_bag_fields(&self, category: &Ident) -> bool {
        self.terms
            .iter()
            .filter(|r| &r.category == category)
            .flat_map(|r| &r.items)
            .any(|i| {
                if let GrammarItem::NonTerminal(name) = i {
                    let s = name.to_string();
                    s == "List" || s == "Bag"
                } else {
                    false
                }
            })
    }

    /// Element type for a collection category (e.g. List -> Proc). First tries the type-based path
    /// for List/Bag (native_type + collection_kind); otherwise a constructor with a Collection grammar item.
    pub fn collection_element_type_for_category(&self, category: &Ident) -> Option<Ident> {
        // Type-based first: when category is a collection type (List/Bag) with native_type, extract element from e.g. Vec<Proc>, HashBag<Proc>
        let cat_str = category.to_string();
        if cat_str == "List" || cat_str == "Bag" {
            if let Some(lang_type) = self.types.iter().find(|t| t.name.to_string() == cat_str) {
                if lang_type.collection_kind.is_some() {
                    if let Some(native_type) = lang_type.native_type.as_ref() {
                        if let Some(elem) = element_ident_from_native_type(native_type) {
                            return Some(elem);
                        }
                    }
                    // Fallback: native_type parse failed (e.g. different Type shape from macro input); assume element type Proc
                    return Some(quote::format_ident!("Proc"));
                }
            }
        }
        // Term-based: constructor with Collection grammar item (e.g. Rhocalc PPar with Collection)
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

    /// Type name for the List category (e.g. "List") if present. Used when building Vec RHS without constructor context.
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
            types,
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
        // Check for native type syntax: ![Type] as Name or ![Type] as List(Proc) / Bag(Proc)
        if content.peek(Token![!]) {
            let _ = content.parse::<Token![!]>()?;

            // Parse [Type] - the brackets are part of the syntax, not the type
            let bracket_content;
            syn::bracketed!(bracket_content in content);
            let native_type = bracket_content.parse::<Type>()?;

            let _ = content.parse::<Token![as]>()?;
            let name = content.parse::<Ident>()?;
            let name_str = name.to_string();
            // Optional (Param) for collection: ![Vec<Proc>] as List(Proc) or ![HashBag<Proc>] as Bag(Proc)
            let collection_kind = if (name_str == "List" || name_str == "Bag") && content.peek(syn::token::Paren) {
                let _content;
                syn::parenthesized!(_content in content);
                let _ = _content.parse::<Ident>()?; // element type param, e.g. Proc
                Some(if name_str == "List" {
                    CollectionCategory::List(CollectionCategory::list_defaults())
                } else {
                    CollectionCategory::Bag(CollectionCategory::bag_defaults())
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
            // Regular type: name; List/Bag use default delimiters only (no custom delimiters)
            let name = content.parse::<Ident>()?;
            let name_str = name.to_string();
            let collection_kind = if name_str == "List" {
                Some(CollectionCategory::List(CollectionCategory::list_defaults()))
            } else if name_str == "Bag" {
                Some(CollectionCategory::Bag(CollectionCategory::bag_defaults()))
            } else {
                None
            };
            types.push(LangType {
                name,
                native_type: None,
                collection_kind,
            });
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
/// Grammar: freshness | congruence | relation_query
///   freshness  ::= ident "#" (ident | "..." ident)
///   congruence ::= ident "~>" ident
///   relation   ::= ident "(" (ident ("," ident)*)? ")"
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
    } else {
        Err(syn::Error::new(
            first.span(),
            "expected premise: 'x # term', 'S ~> T', or 'rel(args)'",
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

    // Capture the entire content as a TokenStream (passed through verbatim)
    let tokens: TokenStream = content.parse()?;

    // Extract relation declarations from the token stream
    let relations = extract_relation_decls(&tokens);

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(LogicBlock { relations, content: tokens })
}

/// Extract relation declarations from a token stream
/// Looks for patterns like: relation name(Type1, Type2, ...);
fn extract_relation_decls(tokens: &TokenStream) -> Vec<RelationDecl> {
    use proc_macro2::TokenTree;

    let mut relations = Vec::new();
    let token_vec: Vec<TokenTree> = tokens.clone().into_iter().collect();

    let mut i = 0;
    while i < token_vec.len() {
        // Look for "relation" keyword
        if let TokenTree::Ident(ident) = &token_vec[i] {
            if ident == "relation" && i + 2 < token_vec.len() {
                // Next should be the relation name
                if let TokenTree::Ident(name) = &token_vec[i + 1] {
                    // Then a group with parentheses containing types
                    if let TokenTree::Group(group) = &token_vec[i + 2] {
                        if group.delimiter() == proc_macro2::Delimiter::Parenthesis {
                            // Parse the types from the group
                            let param_types = parse_relation_params(group.stream());
                            relations.push(RelationDecl { name: name.clone(), param_types });
                        }
                    }
                }
            }
        }
        i += 1;
    }

    relations
}

/// Parse relation parameter types from a token stream like "Proc, Proc"
fn parse_relation_params(tokens: TokenStream) -> Vec<Ident> {
    use proc_macro2::TokenTree;

    let mut params = Vec::new();

    for token in tokens {
        if let TokenTree::Ident(ident) = token {
            params.push(ident);
        }
        // Skip punctuation (commas)
    }

    params
}
