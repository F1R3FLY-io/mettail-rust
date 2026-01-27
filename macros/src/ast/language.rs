use syn::{Ident, Type, Token, parse::{Parse, ParseStream}, Result as SynResult};

use super::grammar::{GrammarRule, parse_terms};
use super::pattern::{Pattern, PatternTerm};

/// Top-level theory definition
/// theory! { name: Foo, params: ..., types { ... }, terms { ... }, equations { ... }, rewrites { ... }, semantics { ... } }
pub struct LanguageDef {
    pub name: Ident,
    pub types: Vec<LangType>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
    pub semantics: Vec<SemanticRule>,
}


/// Equation with optional freshness conditions
/// if x # Q then (LHS) == (RHS)
/// Both LHS and RHS are patterns (symmetric, can use metasyntax)
pub struct Equation {
    pub conditions: Vec<FreshnessCondition>,
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

/// Rewrite rule with optional freshness conditions and optional congruence premise
/// Base: (LHS) => (RHS) or if x # Q then (LHS) => (RHS)
/// Congruence: if S => T then (LHS) => (RHS)
/// Environment: if env_var(x, v) then (LHS) => (RHS)
/// Fact creation: (LHS) => (RHS) then env_var(x, v)
pub struct RewriteRule {
    pub conditions: Vec<Condition>,
    /// Optional congruence premise: (source_var, target_var)
    /// if S => T then ... represents Some(("S", "T"))
    pub premise: Option<(Ident, Ident)>,
    /// LHS pattern - can be Term or Collection (with metasyntax)
    pub left: Pattern,
    /// RHS pattern - the result of the rewrite (can use metasyntax)
    pub right: Pattern,
}

/// Semantic rule for operator evaluation
/// semantics { Add: +, Sub: -, ... }
#[derive(Debug, Clone)]
pub struct SemanticRule {
    pub constructor: Ident,
    pub operation: SemanticOperation,
}

/// Semantic operation type
#[derive(Debug, Clone)]
pub enum SemanticOperation {
    /// Built-in operations: Add, Sub, Mul, Div, etc.
    Builtin(BuiltinOp),
}

/// Built-in operator types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Rem,    // %
    BitAnd, // &
    BitOr,  // |
    BitXor, // ^
    Shl,    // <<
    Shr,    // >>
}


/// Export: category name, optionally with native Rust type
/// types { Elem; Name; ![i32] as Int; }
pub struct LangType {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
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

        // Parse: semantics { ... }
        let semantics = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "semantics" {
                parse_semantics(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        Ok(LanguageDef {
            name,
            types,
            terms,
            equations,
            rewrites,
            semantics,
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

fn parse_equation(input: ParseStream) -> SynResult<Equation> {
    // Parse optional freshness conditions: if x # Q then
    let mut conditions = Vec::new();

    if input.peek(Token![if]) {
        let _ = input.parse::<Token![if]>()?;

        // Support parenthesized freshness: if (x # ...rest) then
        if input.peek(syn::token::Paren) {
            let paren_content;
            syn::parenthesized!(paren_content in input);

            let var = paren_content.parse::<Ident>()?;
            let _ = paren_content.parse::<Token![#]>()?;

            let term = if paren_content.peek(Token![...]) {
                let _ = paren_content.parse::<Token![...]>()?;
                FreshnessTarget::CollectionRest(paren_content.parse::<Ident>()?)
            } else {
                FreshnessTarget::Var(paren_content.parse::<Ident>()?)
            };

            let then_kw = input.parse::<Ident>()?;
            if then_kw != "then" {
                return Err(syn::Error::new(then_kw.span(), "expected 'then'"));
            }

            conditions.push(FreshnessCondition { var, term });
        } else {
            // Non-parenthesized: allow multiple comma-separated freshness conditions
            loop {
                let var = input.parse::<Ident>()?;
                let _ = input.parse::<Token![#]>()?;

                let term = if input.peek(Token![...]) {
                    let _ = input.parse::<Token![...]>()?;
                    FreshnessTarget::CollectionRest(input.parse::<Ident>()?)
                } else {
                    FreshnessTarget::Var(input.parse::<Ident>()?)
                };

                conditions.push(FreshnessCondition { var, term });

                // Check for 'then' or continue with more conditions
                if input.peek(Ident) {
                    let lookahead = input.fork().parse::<Ident>()?;
                    if lookahead == "then" {
                        let _ = input.parse::<Ident>()?; // consume 'then'
                        break;
                    }
                }

                if input.peek(Token![,]) {
                    let _ = input.parse::<Token![,]>()?;
                    // Continue parsing more conditions
                } else {
                    return Err(syn::Error::new(
                        input.span(),
                        "expected 'then' or ',' after freshness condition",
                    ));
                }
            }
        }
    }

    // Parse left-hand side as pattern
    let left = parse_pattern(input)?;

    // Parse =
    let _ = input.parse::<Token![=]>()?;

    // Parse right-hand side as pattern (symmetric with LHS)
    let right = parse_pattern(input)?;

    // Parse semicolon
    let _ = input.parse::<Token![;]>()?;

    Ok(Equation { conditions, left, right })
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
                return Err(syn::Error::new(constructor.span(), "eval requires at least 2 arguments"));
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
                    }
                    Pattern::Term(PatternTerm::MultiLambda { .. }) => {
                        // Multi-lambda: use MultiSubst with single replacement (will be collection)
                        return Ok(Pattern::Term(PatternTerm::MultiSubst {
                            scope: Box::new(first),
                            replacements: vec![second],
                        }));
                    }
                    _ => {
                        // Variable or other pattern: treat as scope, use MultiSubst
                        // This handles both single and multi at runtime via unbind
                        return Ok(Pattern::Term(PatternTerm::MultiSubst {
                            scope: Box::new(first),
                            replacements: vec![second],
                        }));
                    }
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
        Ok(Pattern::Term(PatternTerm::Apply {
            constructor,
            args,
        }))
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

            return Ok(Pattern::Term(PatternTerm::MultiLambda {
                binders,
                body: Box::new(body),
            }));
        }

        // Single binder: ^x.body
        let binder = input.parse::<Ident>()?;
        input.parse::<Token![.]>()?;
        let body = parse_pattern(input)?;

        Ok(Pattern::Term(PatternTerm::Lambda {
            binder,
            body: Box::new(body),
        }))
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
        }
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
        }
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
        }
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
        }
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
            // Skip until end of line - consume tokens until we see something we recognize
            while !content.is_empty()
                && !content.peek(syn::token::Paren)
                && !content.peek(Token![if])
            {
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
    // Parse optional freshness conditions: if x # Q then
    // OR congruence premise: if S => T then
    let mut conditions = Vec::new();
    let mut premise = None;

    while input.peek(Token![if]) {
        let _ = input.parse::<Token![if]>()?;

        // Check if this is an environment query: if env_var(x, v) then
        if input.peek(Ident) && input.peek2(syn::token::Paren) {
            // Parse: env_var(x, v)
            let relation = input.parse::<Ident>()?;
            let args_content;
            syn::parenthesized!(args_content in input);

            let mut args = Vec::new();
            while !args_content.is_empty() {
                args.push(args_content.parse::<Ident>()?);
                if args_content.peek(Token![,]) {
                    let _ = args_content.parse::<Token![,]>()?;
                }
            }

            let then_kw = input.parse::<Ident>()?;
            if then_kw != "then" {
                return Err(syn::Error::new(then_kw.span(), "expected 'then'"));
            }

            conditions.push(Condition::EnvQuery { relation, args });
        }
        // Allow either parenthesized freshness clause: if (x # ...rest) then
        // or the original forms: if x # P then  OR congruence: if S => T then
        else if input.peek(syn::token::Paren) {
            let paren_content;
            syn::parenthesized!(paren_content in input);

            // Inside parentheses we expect a single freshness condition: var # term
            let var = paren_content.parse::<Ident>()?;
            let _ = paren_content.parse::<Token![#]>()?;

            let term = if paren_content.peek(Token![...]) {
                let _ = paren_content.parse::<Token![...]>()?;
                let rest_ident = paren_content.parse::<Ident>()?;
                FreshnessTarget::CollectionRest(rest_ident)
            } else {
                FreshnessTarget::Var(paren_content.parse::<Ident>()?)
            };

            // After parentheses we expect 'then'
            let then_kw = input.parse::<Ident>()?;
            if then_kw != "then" {
                return Err(syn::Error::new(then_kw.span(), "expected 'then'"));
            }

            conditions.push(Condition::Freshness(FreshnessCondition { var, term }));
        } else {
            // Not parenthesized - could be congruence premise or freshness
            let var = input.parse::<Ident>()?;

            // Check if this is a congruence premise (if S => T then) or freshness (if x # Q then)
            if input.peek(Token![~]) && input.peek2(Token![>]) {
                // Congruence premise: if S ~> T then
                let _ = input.parse::<Token![~]>()?;
                let _ = input.parse::<Token![>]>()?;
                let target = input.parse::<Ident>()?;
                let then_kw = input.parse::<Ident>()?;
                if then_kw != "then" {
                    return Err(syn::Error::new(then_kw.span(), "expected 'then'"));
                }

                premise = Some((var, target));
            } else {
                // Freshness condition: if x # Q then
                let _ = input.parse::<Token![#]>()?;

                let term = if input.peek(Token![...]) {
                    let _ = input.parse::<Token![...]>()?;
                    FreshnessTarget::CollectionRest(input.parse::<Ident>()?)
                } else {
                    FreshnessTarget::Var(input.parse::<Ident>()?)
                };

                let then_kw = input.parse::<Ident>()?;
                if then_kw != "then" {
                    return Err(syn::Error::new(then_kw.span(), "expected 'then'"));
                }

                conditions.push(Condition::Freshness(FreshnessCondition { var, term }));
            }
        }
    }

    // Parse left-hand side pattern
    let left = parse_pattern(input)?;

    // Parse =>
    let _ = input.parse::<Token![~]>()?;
    let _ = input.parse::<Token![>]>()?;

    // Parse right-hand side as pattern (can use metasyntax)
    let right = parse_pattern(input)?;

    while input.peek(Ident) {
        // Check if next token is "then"
        let lookahead = input.fork();
        if let Ok(then_kw) = lookahead.parse::<Ident>() {
            if then_kw == "then" {
                input.parse::<Ident>()?; // consume "then"

                // Parse relation name and arguments: env_var(x, v)
                let args_content;
                syn::parenthesized!(args_content in input);

                let mut args = Vec::new();
                while !args_content.is_empty() {
                    args.push(args_content.parse::<Ident>()?);
                    if args_content.peek(Token![,]) {
                        let _ = args_content.parse::<Token![,]>()?;
                    }
                }
            } else {
                break;
            }
        } else {
            break;
        }
    }

    // Optional semicolon
    if input.peek(Token![;]) {
        let _ = input.parse::<Token![;]>()?;
    }

    Ok(RewriteRule {
        conditions,
        premise,
        left,
        right,
    })
}

fn parse_semantics(input: ParseStream) -> SynResult<Vec<SemanticRule>> {
    let semantics_ident = input.parse::<Ident>()?;
    if semantics_ident != "semantics" {
        return Err(syn::Error::new(semantics_ident.span(), "expected 'semantics'"));
    }

    let content;
    syn::braced!(content in input);

    let mut rules = Vec::new();
    while !content.is_empty() {
        // Parse: Constructor: Operator
        let constructor = content.parse::<Ident>()?;
        let _ = content.parse::<Token![:]>()?;

        // Parse operator symbol
        let op = if content.peek(Token![+]) {
            let _ = content.parse::<Token![+]>()?;
            BuiltinOp::Add
        } else if content.peek(Token![-]) {
            let _ = content.parse::<Token![-]>()?;
            BuiltinOp::Sub
        } else if content.peek(Token![*]) {
            let _ = content.parse::<Token![*]>()?;
            BuiltinOp::Mul
        } else if content.peek(Token![/]) {
            let _ = content.parse::<Token![/]>()?;
            BuiltinOp::Div
        } else if content.peek(Token![%]) {
            let _ = content.parse::<Token![%]>()?;
            BuiltinOp::Rem
        } else if content.peek(Token![&]) {
            let _ = content.parse::<Token![&]>()?;
            BuiltinOp::BitAnd
        } else if content.peek(Token![|]) {
            let _ = content.parse::<Token![|]>()?;
            BuiltinOp::BitOr
        } else if content.peek(Token![^]) {
            let _ = content.parse::<Token![^]>()?;
            BuiltinOp::BitXor
        } else if content.peek(Token![<]) && content.peek2(Token![<]) {
            let _ = content.parse::<Token![<]>()?;
            let _ = content.parse::<Token![<]>()?;
            BuiltinOp::Shl
        } else if content.peek(Token![>]) && content.peek2(Token![>]) {
            let _ = content.parse::<Token![>]>()?;
            let _ = content.parse::<Token![>]>()?;
            BuiltinOp::Shr
        } else {
            return Err(syn::Error::new(
                content.span(),
                "expected operator symbol (+, -, *, /, %, &, |, ^, <<, >>)",
            ));
        };

        rules.push(SemanticRule {
            constructor,
            operation: SemanticOperation::Builtin(op),
        });

        // Optional comma or semicolon
        if content.peek(Token![,]) {
            let _ = content.parse::<Token![,]>()?;
        } else if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(rules)
}
