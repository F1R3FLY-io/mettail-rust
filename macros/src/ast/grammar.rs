use syn::{
    parse::ParseStream,
    Ident, Result as SynResult, Token,
};

use super::types::{CollectionType, EvalMode, RustCodeBlock, TypeExpr};

/// Item in a grammar rule
#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),   // "0"
    NonTerminal(Ident), // Elem
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

/// Parameter in term context of a constructor declaration
/// 
/// Examples:
/// - `n:Name` → Simple parameter
/// - `^x.p:[Name -> Proc]` → Abstraction binding x in p
/// - `^[xs].p:[Name* -> Proc]` → Multi-binder abstraction
#[derive(Debug, Clone)]
pub enum TermParam {
    /// Simple typed parameter: `n:Name`
    Simple { 
        name: Ident, 
        ty: TypeExpr,
    },
    /// Abstraction parameter: `^x.p:[Name -> Proc]`
    /// - `binder` is the bound variable (x)
    /// - `body` is the parameter name for the body (p)
    /// - `ty` is the function type [Name -> Proc]
    Abstraction {
        binder: Ident,
        body: Ident,
        ty: TypeExpr,
    },
    /// Multi-binder abstraction: `^[xs].p:[Name* -> Proc]`
    /// - `binder` represents multiple bound variables (xs = x0, x1, ...)
    /// - `body` is the parameter name for the body (p)
    /// - `ty` is the function type [Name* -> Proc]
    MultiAbstraction {
        binder: Ident,
        body: Ident,
        ty: TypeExpr,
    },
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
    Zip {
        left: Ident,
        right: Ident,
    },
    /// #map(source, |x| expr) or source.#map(|x| expr)
    /// Transforms each element according to the pattern
    Map {
        source: Box<PatternOp>,  // Can be Zip result or collection ref
        params: Vec<Ident>,       // Closure parameters
        body: Vec<SyntaxExpr>,    // Pattern body
    },
    /// #opt(expr) - optional element
    /// Generates: `(expr)?` in grammar
    Opt {
        inner: Vec<SyntaxExpr>,
    },
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
    pub category: Ident,  // Result type
    
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
    /// HOL syntax: evaluation mode (fold / step / both)
    pub eval_mode: Option<EvalMode>,
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
    
    if is_old_syntax {
        // OLD SYNTAX: Label . Category ::= items ;
        parse_grammar_rule_old(label, input)
    } else {
        // NEW SYNTAX: Label . context |- pattern : Type ;
        parse_grammar_rule_new(label, input)
    }
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
                items.push(GrammarItem::NonTerminal(ident));
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

    // Parse optional evaluation mode: fold, step, both
    let eval_mode = if input.peek(syn::Ident) {
        let mode_ident = input.parse::<syn::Ident>()?;
        match mode_ident.to_string().as_str() {
            "fold" => Some(EvalMode::Fold),
            "step" => Some(EvalMode::Step),
            "both" => Some(EvalMode::Both),
            _ => {
                return Err(syn::Error::new(
                    mode_ident.span(),
                    "expected evaluation mode: fold, step, or both",
                ));
            }
        }
    } else {
        None
    };
    
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
        
        // Parse a parameter
        let param = parse_term_param(input)?;
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
fn parse_term_param(input: ParseStream) -> SynResult<TermParam> {
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

/// Check if we're at the end of a syntax pattern (`: Type ;`)
fn is_end_of_syntax_pattern(input: ParseStream) -> bool {
    if input.peek(Token![:]) {
        let fork = input.fork();
        let _ = fork.parse::<Token![:]>();
        if fork.peek(Ident) {
            let _ = fork.parse::<Ident>();
            return fork.peek(Token![;]);
        }
    }
    false
}

/// Parse a single syntax expression (literal, param, or pattern op)
fn parse_syntax_expr(input: ParseStream) -> SynResult<SyntaxExpr> {
    // Check for pattern operation: #name(...)
    if input.peek(Token![*]) {
        return parse_pattern_op_expr(input);
    }
    
    // Check for identifier (could be param or start of method chain)
    if input.peek(Ident) {
        let id = input.parse::<Ident>()?;
        
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
        "Expected parameter reference (identifier), quoted literal (string), or pattern operation (#sep, #map, etc.)"
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
        _ => return Err(syn::Error::new(
            name.span(),
            format!("Unknown pattern operation: #{}. Expected #sep, #zip, #map, or #opt", name_str)
        )),
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
                }
                _ => return Err(syn::Error::new(
                    name.span(),
                    "#sep receiver must be a collection parameter or result of #map/#zip"
                )),
            };
            PatternOp::Sep { collection, separator, source: None }
        }
        "map" => {
            // receiver.#map(|x| expr)
            let (params, body) = parse_map_closure(&content)?;
            PatternOp::Map {
                source: Box::new(receiver),
                params,
                body,
            }
        }
        _ => return Err(syn::Error::new(
            name.span(),
            format!("Cannot chain #{} after pattern operation. Expected #sep or #map", name_str)
        )),
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
    
    Ok(PatternOp::Map {
        source: Box::new(source),
        params,
        body,
    })
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

/// Convert term context to old-style items and bindings for backward compatibility
fn convert_term_context_to_items(term_context: &[TermParam]) -> (Vec<GrammarItem>, Vec<(usize, Vec<usize>)>) {
    let mut items = Vec::new();
    let mut bindings = Vec::new();
    
    for param in term_context {
        match param {
            TermParam::Simple { ty, .. } => {
                // Simple param becomes NonTerminal with the base type name
                if let TypeExpr::Base(type_name) = ty {
                    items.push(GrammarItem::NonTerminal(type_name.clone()));
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
                }
            }
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
                        items.push(GrammarItem::NonTerminal(body_type.clone()));
                    }
                    
                    bindings.push((binder_idx, vec![body_idx]));
                }
            }
            TermParam::MultiAbstraction { ty, .. } => {
                // Multi-abstraction: ^[xs].p:[Name* -> Proc]
                // This needs special handling for multiple binders
                if let TypeExpr::Arrow { domain, codomain } = ty {
                    let binder_idx = items.len();
                    
                    if let TypeExpr::MultiBinder(inner) = domain.as_ref() {
                        if let TypeExpr::Base(binder_type) = inner.as_ref() {
                            // For now, represent as a single Binder
                            // TODO: proper multi-binder support
                            items.push(GrammarItem::Binder { category: binder_type.clone() });
                        }
                    }
                    
                    let body_idx = items.len();
                    if let TypeExpr::Base(body_type) = codomain.as_ref() {
                        items.push(GrammarItem::NonTerminal(body_type.clone()));
                    }
                    
                    bindings.push((binder_idx, vec![body_idx]));
                }
            }
        }
    }
    
    (items, bindings)
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
                    GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. } => {
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
            ))
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