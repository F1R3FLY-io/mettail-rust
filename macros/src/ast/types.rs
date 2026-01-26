use syn::{
    parse::{Parse, ParseStream},
    Ident, Result as SynResult, Token, Type,
};

/// Top-level theory definition
/// theory! { name: Foo, params: ..., exports { ... }, terms { ... }, equations { ... }, rewrites { ... }, semantics { ... } }
pub struct TheoryDef {
    pub name: Ident,
    #[allow(dead_code)]
    pub params: Vec<TheoryParam>,
    pub exports: Vec<Export>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
    pub semantics: Vec<SemanticRule>,
}

/// Theory parameter (for generic theories)
/// params: (cm: CommutativeMonoid)
#[allow(dead_code)]
pub struct TheoryParam {
    pub name: Ident,
    pub ty: Type,
}

/// Equation with optional freshness conditions
/// if x # Q then (LHS) == (RHS)
pub struct Equation {
    pub conditions: Vec<FreshnessCondition>,
    pub left: Expr,
    pub right: Expr,
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

/// Environment action to create facts when a rewrite fires
#[derive(Debug, Clone)]
pub enum EnvAction {
    /// Create a fact: then env_var(x, v)
    CreateFact {
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
    pub left: Expr,
    pub right: Expr,
    /// Environment actions to create facts when rewrite fires
    pub env_actions: Vec<EnvAction>,
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

/// Expression in equations (AST patterns)
#[derive(Clone, Debug)]
pub enum Expr {
    Var(Ident),
    Apply {
        constructor: Ident,
        args: Vec<Expr>,
    },
    /// Substitution: subst(term, var, replacement)
    /// Represents term[replacement/var] - substitute replacement for var in term
    Subst {
        term: Box<Expr>,
        var: Ident,
        replacement: Box<Expr>,
    },
    /// Collection pattern with rest: {P, Q, ...rest}
    /// Used in rewrite rules to match collections partially
    CollectionPattern {
        /// Constructor label (e.g., PPar)
        /// Will be inferred during validation if not provided
        constructor: Option<Ident>,
        /// Specific elements to match (can be patterns)
        elements: Vec<Expr>,
        /// Optional rest variable to bind remaining elements
        rest: Option<Ident>,
    },
}

/// Export: category name, optionally with native Rust type
/// exports { Elem; Name; ![i32] as Int; }
pub struct Export {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
}

/// Grammar rule
/// Old syntax: Label . Category ::= Item Item Item ;
/// HOL syntax: Label . param:Type, ... |- Item Item Item:ReturnType ![code] mode;
pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident,
    pub items: Vec<GrammarItem>,
    /// Binding structure: (binder_index, vec![body_indices])
    /// e.g., (0, vec![1]) means item 0 binds in item 1
    pub bindings: Vec<(usize, Vec<usize>)>,
    /// HOL syntax: typed parameters
    pub parameters: Vec<TypedParameter>,
    /// HOL syntax: return type (category name)
    pub return_type: Option<Ident>,
    /// HOL syntax: Rust code implementation
    pub rust_code: Option<RustCodeBlock>,
    /// HOL syntax: evaluation mode (fold/step/both)
    pub eval_mode: Option<EvalMode>,
}

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

/// Collection type specifier
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CollectionType {
    HashBag,
    HashSet,
    Vec,
}

/// Typed parameter for HOL syntax
/// Example: a:Int, b:Float
#[derive(Debug, Clone)]
pub struct TypedParameter {
    pub name: Ident,
    /// Type can be either an exported category or a native Rust type
    pub param_type: Ident,
}

/// Rust code block for HOL syntax
/// Example: ![a + b]
#[derive(Debug, Clone)]
pub struct RustCodeBlock {
    /// Parsed Rust expression
    pub code: syn::Expr,
}

/// Evaluation mode for HOL syntax
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalMode {
    /// Only constant folding
    Fold,
    /// Only step-by-step (congruence rules)
    Step,
    /// Both folding and congruence (default)
    Both,
}

// Implement Parse for TheoryDef
impl Parse for TheoryDef {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // Parse: name: Identifier
        let name_kw = input.parse::<Ident>()?;
        if name_kw != "name" {
            return Err(syn::Error::new(name_kw.span(), "expected 'name'"));
        }
        let _ = input.parse::<Token![:]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![,]>()?;

        // Parse: params: (...) (optional)
        let params = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "params" {
                parse_params(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: exports { ... }
        let exports = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "exports" {
                parse_exports(input)?
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

        Ok(TheoryDef {
            name,
            params,
            exports,
            terms,
            equations,
            rewrites,
            semantics,
        })
    }
}

fn parse_params(input: ParseStream) -> SynResult<Vec<TheoryParam>> {
    let params_ident = input.parse::<Ident>()?;
    if params_ident != "params" {
        return Err(syn::Error::new(params_ident.span(), "expected 'params'"));
    }

    let _ = input.parse::<Token![:]>()?;

    let content;
    syn::parenthesized!(content in input);

    let mut params = Vec::new();
    while !content.is_empty() {
        let name = content.parse::<Ident>()?;
        let _ = content.parse::<Token![:]>()?;
        let ty = content.parse::<Type>()?;

        params.push(TheoryParam { name, ty });

        if content.peek(Token![,]) {
            let _ = content.parse::<Token![,]>()?;
        }
    }

    // Optional comma after closing paren
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(params)
}

fn parse_exports(input: ParseStream) -> SynResult<Vec<Export>> {
    let exports_ident = input.parse::<Ident>()?;
    if exports_ident != "exports" {
        return Err(syn::Error::new(exports_ident.span(), "expected 'exports'"));
    }

    let content;
    syn::braced!(content in input);

    let mut exports = Vec::new();
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
            exports.push(Export { name, native_type: Some(native_type) });
        } else {
            // Regular export: just a name
            let name = content.parse::<Ident>()?;
            exports.push(Export { name, native_type: None });
        }

        if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(exports)
}

fn parse_terms(input: ParseStream) -> SynResult<Vec<GrammarRule>> {
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
    // Parse: Label . (Category or parameters)
    let label = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;

    // Check if this is HOL syntax (has parameters) or old syntax
    // HOL:  Label . param:Type, ... |- ...
    // Old:  Label . Category ::= ...
    // The key difference: HOL has : after first identifier, old has ::
    let fork = input.fork();
    let _first_ident = fork.parse::<Ident>()?;
    // HOL syntax has single colon (not ::), so check peek(:) but NOT peek2(:)
    let is_hol_syntax = fork.peek(Token![:]) && !fork.peek2(Token![:]);

    if is_hol_syntax {
        // HOL syntax: Label . param1:Type1, param2:Type2 |- items:ReturnType ;
        parse_hol_grammar_rule(input, label)
    } else {
        // Old syntax: Label . Category ::= items ;
        parse_old_grammar_rule(input, label)
    }
}

/// Parse old-style grammar rule: Label . Category ::= Item Item Item ;
fn parse_old_grammar_rule(input: ParseStream, label: Ident) -> SynResult<GrammarRule> {
    let category = input.parse::<Ident>()?;

    // Parse ::= (as two colons followed by equals)
    let _ = input.parse::<Token![::]>()?;
    let _ = input.parse::<Token![=]>()?;

    // Parse items until semicolon
    let mut items = Vec::new();
    while !input.peek(Token![;]) {
        items.push(parse_grammar_item(input)?);
    }

    let _ = input.parse::<Token![;]>()?;

    // Infer binding structure: each Binder binds in the next NonTerminal
    let bindings = infer_bindings(&items);

    Ok(GrammarRule {
        label,
        category,
        items,
        bindings,
        parameters: Vec::new(),
        return_type: None,
        rust_code: None,
        eval_mode: None,
    })
}

/// Parse HOL-style grammar rule: Label . param:Type, ... |- Item Item:ReturnType ;
fn parse_hol_grammar_rule(input: ParseStream, label: Ident) -> SynResult<GrammarRule> {
    // Parse parameters: param1:Type1, param2:Type2, ...
    let mut parameters = Vec::new();
    loop {
        let param_name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let param_type = input.parse::<Ident>()?;
        parameters.push(TypedParameter {
            name: param_name,
            param_type,
        });

        // Check for comma (more parameters) or |- (start of grammar items)
        if input.peek(Token![,]) {
            let _ = input.parse::<Token![,]>()?;
        } else {
            break;
        }
    }

    // Parse |- separator
    let _ = input.parse::<Token![|]>()?;
    let _ = input.parse::<Token![-]>()?;

    // Parse grammar items until we hit colon (return type marker)
    let mut items = Vec::new();
    while !input.peek(Token![:]) || input.peek2(Token![:]) {
        // Keep parsing if we see :: (for old-style items we might still encounter)
        // But stop at single : which indicates return type
        items.push(parse_grammar_item(input)?);
    }

    // Parse :ReturnType
    let _ = input.parse::<Token![:]>()?;
    let return_type = input.parse::<Ident>()?;

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
    let eval_mode = if input.peek(Ident) {
        let mode_ident = input.parse::<Ident>()?;
        match mode_ident.to_string().as_str() {
            "fold" => Some(EvalMode::Fold),
            "step" => Some(EvalMode::Step),
            "both" => Some(EvalMode::Both),
            _ => {
                return Err(syn::Error::new(
                    mode_ident.span(),
                    "expected evaluation mode: fold, step, or both",
                ))
            },
        }
    } else {
        None
    };

    // Consume semicolon
    let _ = input.parse::<Token![;]>()?;

    // Infer binding structure
    let bindings = infer_bindings(&items);

    // Category is the return type for HOL syntax
    let category = return_type.clone();

    Ok(GrammarRule {
        label,
        category,
        items,
        bindings,
        parameters,
        return_type: Some(return_type),
        rust_code,
        eval_mode,
    })
}

/// Parse a single grammar item (terminal, non-terminal, binder, or collection)
fn parse_grammar_item(input: ParseStream) -> SynResult<GrammarItem> {
    if input.peek(syn::LitStr) {
        // Terminal: string literal
        let lit = input.parse::<syn::LitStr>()?;
        Ok(GrammarItem::Terminal(lit.value()))
    } else if input.peek(Token![<]) {
        // Binder: <Category>
        let _ = input.parse::<Token![<]>()?;
        let cat = input.parse::<Ident>()?;
        let _ = input.parse::<Token![>]>()?;
        Ok(GrammarItem::Binder { category: cat })
    } else {
        // Check if this is a collection type (HashBag, HashSet, Vec)
        let ident = input.parse::<Ident>()?;
        let ident_str = ident.to_string();

        if (ident_str == "HashBag" || ident_str == "HashSet" || ident_str == "Vec")
            && input.peek(syn::token::Paren)
        {
            // Collection: HashBag(Proc) sep "|" [delim "[" "]"]
            parse_collection(ident, input)
        } else {
            // NonTerminal: identifier
            Ok(GrammarItem::NonTerminal(ident))
        }
    }
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

    // Parse left-hand side
    let left = parse_expr(input)?;

    // Parse ==
    let _ = input.parse::<Token![==]>()?;

    // Parse right-hand side
    let right = parse_expr(input)?;

    // Parse semicolon
    let _ = input.parse::<Token![;]>()?;

    Ok(Equation { conditions, left, right })
}

fn parse_expr(input: ParseStream) -> SynResult<Expr> {
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

            // Parse regular element expression
            elements.push(parse_expr(&content)?);

            // Parse comma separator
            if content.peek(Token![,]) {
                let _ = content.parse::<Token![,]>()?;
            } else {
                break;
            }
        }

        return Ok(Expr::CollectionPattern {
            constructor: None, // Will be inferred during validation
            elements,
            rest,
        });
    }

    // Parse parenthesized expression or variable
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);

        // Parse constructor name or 'subst'
        let constructor = content.parse::<Ident>()?;

        // Check if this is a substitution
        if constructor == "subst" {
            // Parse: subst term var replacement
            // Where term and replacement are expressions, var is an identifier
            let term = parse_expr(&content)?;
            let var = content.parse::<Ident>()?;
            let replacement = parse_expr(&content)?;

            return Ok(Expr::Subst {
                term: Box::new(term),
                var,
                replacement: Box::new(replacement),
            });
        }

        // Parse arguments for regular constructor
        let mut args = Vec::new();
        while !content.is_empty() {
            args.push(parse_expr(&content)?);
        }

        Ok(Expr::Apply { constructor, args })
    } else {
        // Just a variable
        let var = input.parse::<Ident>()?;
        Ok(Expr::Var(var))
    }
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
            if input.peek(Token![=]) && input.peek2(Token![>]) {
                // Congruence premise: if S => T then
                let _ = input.parse::<Token![=]>()?;
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

    // Parse left-hand side
    let left = parse_expr(input)?;

    // Parse =>
    let _ = input.parse::<Token![=]>()?;
    let _ = input.parse::<Token![>]>()?;

    // Parse right-hand side
    let right = parse_expr(input)?;

    // Parse optional environment actions: then env_var(x, v)
    let mut env_actions = Vec::new();
    while input.peek(Ident) {
        // Check if next token is "then"
        let lookahead = input.fork();
        if let Ok(then_kw) = lookahead.parse::<Ident>() {
            if then_kw == "then" {
                input.parse::<Ident>()?; // consume "then"

                // Parse relation name and arguments: env_var(x, v)
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

                env_actions.push(EnvAction::CreateFact { relation, args });
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
        env_actions,
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

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    use syn::parse2;

    #[test]
    fn parse_hashbag_simple() {
        let input = quote! {
            name: TestBag,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "|" ;
                EZero . Elem ::= "0" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse HashBag: {:?}", result.err());

        let theory = result.unwrap();
        assert_eq!(theory.name.to_string(), "TestBag");
        assert_eq!(theory.terms.len(), 2);

        // Check EBag has a Collection item
        let ebag = &theory.terms[0];
        assert_eq!(ebag.label.to_string(), "EBag");
        assert_eq!(ebag.items.len(), 1);

        match &ebag.items[0] {
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => {
                assert_eq!(*coll_type, CollectionType::HashBag);
                assert_eq!(element_type.to_string(), "Elem");
                assert_eq!(separator, "|");
                assert!(delimiters.is_none());
            },
            _ => panic!("Expected Collection item"),
        }
    }

    #[test]
    fn parse_parenthesized_collection_freshness() {
        let input = quote! {
            name: TestFresh,
            exports { Proc Name }
            terms {
                PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                PNew . Proc ::= "new(" <Name> "," Proc ")" ;
                PVar . Proc ::= Var ;
                NVar . Name ::= Var ;
            }
            equations {
                if (x # ...rest) then (PPar {(PNew x P), ...rest}) == (PNew x (PPar {P, ...rest}));
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse parenthesized freshness: {:?}", result.err());
        let theory = result.unwrap();
        assert_eq!(theory.equations.len(), 1);
        let eq = &theory.equations[0];
        assert_eq!(eq.conditions.len(), 1);
        match &eq.conditions[0].term {
            FreshnessTarget::CollectionRest(id) => assert_eq!(id.to_string(), "rest"),
            other => panic!("Expected CollectionRest freshness target, got: {:?}", other),
        }
    }

    #[test]
    fn parse_collection_with_delimiters() {
        let input = quote! {
            name: TestList,
            exports { Elem }
            terms {
                EList . Elem ::= Vec(Elem) sep "," delim "[" "]" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse Vec with delimiters: {:?}", result.err());

        let theory = result.unwrap();
        let elist = &theory.terms[0];

        match &elist.items[0] {
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                assert_eq!(*coll_type, CollectionType::Vec);
                assert_eq!(separator, ",");
                assert_eq!(delimiters.as_ref().unwrap(), &("[".to_string(), "]".to_string()));
            },
            _ => panic!("Expected Collection item with delimiters"),
        }
    }

    #[test]
    fn parse_hashset_collection() {
        let input = quote! {
            name: TestSet,
            exports { Elem }
            terms {
                ESet . Elem ::= HashSet(Elem) sep "," delim "{" "}" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse HashSet: {:?}", result.err());

        let theory = result.unwrap();
        let eset = &theory.terms[0];

        match &eset.items[0] {
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                assert_eq!(*coll_type, CollectionType::HashSet);
                assert_eq!(separator, ",");
                assert_eq!(delimiters.as_ref().unwrap(), &("{".to_string(), "}".to_string()));
            },
            _ => panic!("Expected HashSet collection"),
        }
    }

    #[test]
    fn parse_collection_error_empty_separator() {
        let input = quote! {
            name: TestBad,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_err(), "Should reject empty separator");
        let err = result.err().unwrap();
        assert!(err.to_string().contains("separator cannot be empty"));
    }

    #[test]
    fn parse_collection_error_missing_sep() {
        let input = quote! {
            name: TestBad,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) "|" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_err(), "Should require 'sep' keyword");
        // The error will be about unexpected token, not specifically about 'sep'
        // Just verify it fails to parse
    }
}
