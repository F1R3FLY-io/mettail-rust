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
    /// Lambda abstraction: \x.body
    /// Meta-level function for use in definitions and term contexts
    /// Type annotation is external: \x.body:[A -> B]
    Lambda {
        /// Bound variable name
        binder: Ident,
        /// Lambda body
        body: Box<Expr>,
    },
    /// Multi-binder lambda: \[xs].body
    /// Binds a list of variables
    MultiLambda {
        /// Collective name for bound variables
        binder: Ident,
        /// Lambda body
        body: Box<Expr>,
    },
}

impl Expr {
    /// Collect free variables in this expression
    pub fn free_vars(&self) -> std::collections::HashSet<String> {
        use std::collections::HashSet;
        
        match self {
            Expr::Var(v) => {
                let mut set = HashSet::new();
                set.insert(v.to_string());
                set
            }
            Expr::Apply { args, .. } => {
                let mut vars = HashSet::new();
                for arg in args {
                    vars.extend(arg.free_vars());
                }
                vars
            }
            Expr::Subst { term, var, replacement } => {
                let mut vars = term.free_vars();
                vars.insert(var.to_string()); // The substitution variable is referenced
                vars.extend(replacement.free_vars());
                vars
            }
            Expr::CollectionPattern { elements, rest, .. } => {
                let mut vars = HashSet::new();
                for elem in elements {
                    vars.extend(elem.free_vars());
                }
                if let Some(r) = rest {
                    vars.insert(r.to_string());
                }
                vars
            }
            Expr::Lambda { binder, body } => {
                let mut vars = body.free_vars();
                vars.remove(&binder.to_string()); // binder is bound, not free
                vars
            }
            Expr::MultiLambda { binder, body } => {
                let mut vars = body.free_vars();
                vars.remove(&binder.to_string()); // binder is bound, not free
                vars
            }
        }
    }

    /// Capture-avoiding substitution: replace `var` with `replacement` in `self`
    /// 
    /// This handles:
    /// - Direct variable replacement
    /// - Shadowing (don't substitute in lambda body if binder matches var)
    /// - Capture detection (panic if replacement contains free var that would be captured)
    pub fn substitute(&self, var: &Ident, replacement: &Expr) -> Expr {
        let var_str = var.to_string();
        
        match self {
            Expr::Var(v) => {
                if v.to_string() == var_str {
                    replacement.clone()
                } else {
                    Expr::Var(v.clone())
                }
            }
            
            Expr::Apply { constructor, args } => Expr::Apply {
                constructor: constructor.clone(),
                args: args.iter().map(|a| a.substitute(var, replacement)).collect(),
            },
            
            Expr::Subst { term, var: v, replacement: r } => Expr::Subst {
                term: Box::new(term.substitute(var, replacement)),
                var: v.clone(),
                replacement: Box::new(r.substitute(var, replacement)),
            },
            
            Expr::CollectionPattern { constructor, elements, rest } => Expr::CollectionPattern {
                constructor: constructor.clone(),
                elements: elements.iter().map(|e| e.substitute(var, replacement)).collect(),
                rest: rest.clone(),
            },
            
            Expr::Lambda { binder, body } => {
                let binder_str = binder.to_string();
                
                if binder_str == var_str {
                    // Shadowed - binder hides var, don't substitute in body
                    self.clone()
                } else if replacement.free_vars().contains(&binder_str) {
                    // Would capture: replacement contains a free variable with same name as binder
                    // TODO: Implement alpha-renaming to handle this case
                    panic!(
                        "Capture-avoiding substitution: variable '{}' in replacement would be captured by binder '{}'",
                        binder_str, binder_str
                    )
                } else {
                    // Safe to substitute in body
                    Expr::Lambda {
                        binder: binder.clone(),
                        body: Box::new(body.substitute(var, replacement)),
                    }
                }
            }
            
            Expr::MultiLambda { binder, body } => {
                let binder_str = binder.to_string();
                
                if binder_str == var_str {
                    // Shadowed
                    self.clone()
                } else if replacement.free_vars().contains(&binder_str) {
                    // Would capture
                    panic!(
                        "Capture-avoiding substitution: variable '{}' in replacement would be captured by multi-binder '{}'",
                        binder_str, binder_str
                    )
                } else {
                    Expr::MultiLambda {
                        binder: binder.clone(),
                        body: Box::new(body.substitute(var, replacement)),
                    }
                }
            }
        }
    }
    
    /// Apply a lambda to an argument (beta reduction)
    /// Returns Err if self is not a lambda
    pub fn apply(&self, arg: &Expr) -> Result<Expr, String> {
        match self {
            Expr::Lambda { binder, body } => {
                Ok(body.substitute(binder, arg))
            }
            Expr::MultiLambda { binder, body } => {
                // For multi-lambda, arg should represent a list
                // Each element binds to the collective binder
                Ok(body.substitute(binder, arg))
            }
            _ => Err(format!("Cannot apply non-lambda expression: {:?}", self)),
        }
    }
}

/// Export: category name, optionally with native Rust type
/// exports { Elem; Name; ![i32] as Int; }
pub struct Export {
    pub name: Ident,
    /// Optional native Rust type (e.g., `i32` for `![i32] as Int`)
    pub native_type: Option<Type>,
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
    /// Concrete syntax pattern: `for(x<-n){p}`
    pub syntax_pattern: Option<Vec<SyntaxToken>>,
}

//=============================================================================
// TERM PARAMETERS (for new judgement-style syntax)
//=============================================================================

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

impl TermParam {
    /// Get the name(s) this parameter introduces
    pub fn names(&self) -> Vec<&Ident> {
        match self {
            TermParam::Simple { name, .. } => vec![name],
            TermParam::Abstraction { binder, body, .. } => vec![binder, body],
            TermParam::MultiAbstraction { binder, body, .. } => vec![binder, body],
        }
    }
    
    /// Get the type of this parameter
    pub fn ty(&self) -> &TypeExpr {
        match self {
            TermParam::Simple { ty, .. } => ty,
            TermParam::Abstraction { ty, .. } => ty,
            TermParam::MultiAbstraction { ty, .. } => ty,
        }
    }
}

/// Token in a syntax pattern
/// 
/// Syntax patterns use quoted strings for all literals and unquoted identifiers
/// for parameter references only.
/// 
/// Example: `"for" "(" x "<-" n ")" "{" p "}"`
/// - Literal("for"), Literal("("), Ident(x), Literal("<-"), Ident(n), 
///   Literal(")"), Literal("{"), Ident(p), Literal("}")
#[derive(Debug, Clone)]
pub enum SyntaxToken {
    /// Parameter reference - must match a parameter in term context
    Ident(Ident),
    /// Literal syntax element - keywords, punctuation, operators (all quoted)
    Literal(String),
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

//=============================================================================
// TYPE EXPRESSIONS (HOL Syntax)
//=============================================================================

/// Type expression for the judgement-style syntax
///
/// Examples:
/// - `Name` → `Base("Name")`
/// - `[Name -> Proc]` → `Arrow { domain: Name, codomain: Proc }`
/// - `[Name* -> Proc]` → `Arrow { domain: MultiBinder(Name), codomain: Proc }`
/// - `[[A -> B] -> C]` → `Arrow { domain: Arrow(A,B), codomain: C }`
/// - `Vec(Name)` → `Collection { coll_type: Vec, element: Name }`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    /// Base type: Name, Proc, etc.
    Base(Ident),

    /// Function type: [Domain -> Codomain]
    Arrow {
        domain: Box<TypeExpr>,
        codomain: Box<TypeExpr>,
    },

    /// Multi-binder domain: `Name*` means "list of binders of type Name"
    /// Used in `\[xs].p:[Name* -> Proc]`
    MultiBinder(Box<TypeExpr>),

    /// Collection type: Vec(T), HashBag(T), HashSet(T)
    Collection {
        coll_type: CollectionType,
        element: Box<TypeExpr>,
    },
}

impl std::fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpr::Base(ident) => write!(f, "{}", ident),
            TypeExpr::Arrow { domain, codomain } => write!(f, "[{} -> {}]", domain, codomain),
            TypeExpr::MultiBinder(inner) => write!(f, "{}*", inner),
            TypeExpr::Collection { coll_type, element } => {
                let coll_name = match coll_type {
                    CollectionType::Vec => "Vec",
                    CollectionType::HashBag => "HashBag",
                    CollectionType::HashSet => "HashSet",
                };
                write!(f, "{}({})", coll_name, element)
            }
        }
    }
}

impl TypeExpr {
    /// Create a base type from a string
    pub fn base(name: &str) -> Self {
        TypeExpr::Base(Ident::new(name, proc_macro2::Span::call_site()))
    }

    /// Create an arrow type
    pub fn arrow(domain: TypeExpr, codomain: TypeExpr) -> Self {
        TypeExpr::Arrow {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Create a multi-binder type
    pub fn multi_binder(element: TypeExpr) -> Self {
        TypeExpr::MultiBinder(Box::new(element))
    }

    /// Create a collection type
    pub fn collection(coll_type: CollectionType, element: TypeExpr) -> Self {
        TypeExpr::Collection {
            coll_type,
            element: Box::new(element),
        }
    }

    /// Check if this is a function type
    pub fn is_arrow(&self) -> bool {
        matches!(self, TypeExpr::Arrow { .. })
    }

    /// Check if this is a multi-binder type
    pub fn is_multi_binder(&self) -> bool {
        matches!(self, TypeExpr::MultiBinder(_))
    }

    /// Get the domain type if this is an Arrow type
    pub fn domain(&self) -> Option<&TypeExpr> {
        match self {
            TypeExpr::Arrow { domain, .. } => Some(domain),
            _ => None,
        }
    }

    /// Get the codomain type if this is an Arrow type
    pub fn codomain(&self) -> Option<&TypeExpr> {
        match self {
            TypeExpr::Arrow { codomain, .. } => Some(codomain),
            _ => None,
        }
    }
}

//=============================================================================
// TYPE CONTEXT (for lambda type inference)
//=============================================================================

/// A constructor signature: types of arguments and result type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorSig {
    /// Types of arguments
    pub arg_types: Vec<TypeExpr>,
    /// Result type
    pub result_type: TypeExpr,
}

impl ConstructorSig {
    pub fn new(arg_types: Vec<TypeExpr>, result_type: TypeExpr) -> Self {
        Self { arg_types, result_type }
    }
}

/// Type context for tracking variable types during inference
/// 
/// Used when type-checking lambdas: `^x.body:[A->B]` means x:A in the body
#[derive(Debug, Clone)]
pub struct TypeContext {
    /// Map from variable name to its type
    bindings: std::collections::HashMap<String, TypeExpr>,
    /// Map from constructor name to its signature
    constructors: std::collections::HashMap<String, ConstructorSig>,
}

impl TypeContext {
    /// Create an empty type context
    pub fn new() -> Self {
        Self {
            bindings: std::collections::HashMap::new(),
            constructors: std::collections::HashMap::new(),
        }
    }

    /// Extend context with a variable binding
    pub fn with_var(&self, var: &str, ty: TypeExpr) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.bindings.insert(var.to_string(), ty);
        new_ctx
    }

    /// Extend context with a constructor signature
    pub fn with_constructor(&self, name: &str, sig: ConstructorSig) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.constructors.insert(name.to_string(), sig);
        new_ctx
    }

    /// Look up a variable's type
    pub fn lookup(&self, var: &str) -> Option<&TypeExpr> {
        self.bindings.get(var)
    }

    /// Look up a constructor's signature
    pub fn lookup_constructor(&self, name: &str) -> Option<&ConstructorSig> {
        self.constructors.get(name)
    }

    /// Check if a variable is bound in this context
    pub fn contains(&self, var: &str) -> bool {
        self.bindings.contains_key(var)
    }
}

/// Error types for type inference
#[derive(Debug, Clone)]
pub enum TypeError {
    /// Variable not found in context
    UnboundVariable(String),
    /// Expected function type, got something else
    NotAFunction(TypeExpr),
    /// Type mismatch during application
    TypeMismatch {
        expected: TypeExpr,
        found: TypeExpr,
        context: String,
    },
    /// Cannot infer type without annotation
    CannotInfer(String),
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::UnboundVariable(v) => write!(f, "Unbound variable: {}", v),
            TypeError::NotAFunction(ty) => write!(f, "Expected function type, got: {}", ty),
            TypeError::TypeMismatch { expected, found, context } => {
                write!(f, "Type mismatch in {}: expected {}, found {}", context, expected, found)
            }
            TypeError::CannotInfer(msg) => write!(f, "Cannot infer type: {}", msg),
        }
    }
}

impl Expr {
    /// Infer the type of an expression given a type context
    /// 
    /// For lambdas, requires an expected type annotation since we don't store
    /// types in the Lambda itself.
    pub fn infer_type(&self, ctx: &TypeContext) -> Result<TypeExpr, TypeError> {
        match self {
            Expr::Var(v) => {
                ctx.lookup(&v.to_string())
                    .cloned()
                    .ok_or_else(|| TypeError::UnboundVariable(v.to_string()))
            }
            
            Expr::Apply { constructor, args } => {
                // Look up constructor signature
                if let Some(sig) = ctx.lookup_constructor(&constructor.to_string()) {
                    // Verify argument count matches
                    if args.len() != sig.arg_types.len() {
                        return Err(TypeError::CannotInfer(format!(
                            "Constructor {} expects {} arguments, got {}",
                            constructor, sig.arg_types.len(), args.len()
                        )));
                    }
                    // Type check each argument against expected type
                    for (arg, expected_type) in args.iter().zip(sig.arg_types.iter()) {
                        arg.check_type(expected_type, ctx)?;
                    }
                    // Return the result type
                    Ok(sig.result_type.clone())
                } else {
                    Err(TypeError::CannotInfer(format!(
                        "Constructor {} not found in context", 
                        constructor
                    )))
                }
            }
            
            Expr::Lambda { .. } | Expr::MultiLambda { .. } => {
                // Lambda types must be provided externally via annotation
                Err(TypeError::CannotInfer(
                    "Lambda types must be annotated: ^x.body:[A->B]".to_string()
                ))
            }
            
            Expr::Subst { term, .. } => {
                // Substitution preserves the term's type
                term.infer_type(ctx)
            }
            
            Expr::CollectionPattern { .. } => {
                Err(TypeError::CannotInfer(
                    "Collection pattern type needs context".to_string()
                ))
            }
        }
    }

    /// Check that this expression has a given type
    pub fn check_type(&self, expected: &TypeExpr, ctx: &TypeContext) -> Result<(), TypeError> {
        match (self, expected) {
            // Lambda checking: ^x.body : [A -> B] means body : B in context x:A
            (Expr::Lambda { binder, body }, TypeExpr::Arrow { domain, codomain }) => {
                let extended_ctx = ctx.with_var(&binder.to_string(), (**domain).clone());
                body.check_type(codomain, &extended_ctx)
            }
            
            // MultiLambda checking: ^[xs].body : [A* -> B]
            (Expr::MultiLambda { binder, body }, TypeExpr::Arrow { domain, codomain }) => {
                match domain.as_ref() {
                    TypeExpr::MultiBinder(elem_type) => {
                        // xs represents multiple variables of elem_type
                        let extended_ctx = ctx.with_var(&binder.to_string(), (**elem_type).clone());
                        body.check_type(codomain, &extended_ctx)
                    }
                    _ => Err(TypeError::CannotInfer(format!(
                        "MultiLambda ^[{}]._ requires a multi-binder domain type (T*), got {}",
                        binder, domain
                    )))
                }
            }
            
            // For other cases, try to infer and compare
            _ => {
                let inferred = self.infer_type(ctx)?;
                if &inferred == expected {
                    Ok(())
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: expected.clone(),
                        found: inferred,
                        context: format!("{:?}", self),
                    })
                }
            }
        }
    }

    /// Apply a typed lambda to an argument, checking types
    pub fn apply_typed(&self, arg: &Expr, ctx: &TypeContext, func_type: &TypeExpr) -> Result<Expr, TypeError> {
        match (self, func_type) {
            (Expr::Lambda { binder, body }, TypeExpr::Arrow { domain, codomain: _ }) => {
                // Check arg has the domain type
                arg.check_type(domain, ctx)?;
                // Substitute arg for binder in body
                Ok(body.substitute(binder, arg))
            }
            (Expr::Lambda { .. }, _) => {
                Err(TypeError::NotAFunction(func_type.clone()))
            }
            _ => {
                Err(TypeError::NotAFunction(func_type.clone()))
            }
        }
    }
}

/// Parse a TypeExpr from the input stream
///
/// Syntax:
/// - `Name` → Base type
/// - `Name*` → MultiBinder (list of binders)
/// - `[A -> B]` → Arrow type
/// - `[A* -> B]` → Arrow with MultiBinder domain
/// - `[[A -> B] -> C]` → Nested arrow (higher-order)
/// - `Vec(A)`, `HashBag(A)`, `HashSet(A)` → Collection types
impl Parse for TypeExpr {
    fn parse(input: ParseStream) -> SynResult<Self> {
        parse_type_expr(input)
    }
}

/// Parse a type expression, handling postfix `*` for multi-binder
fn parse_type_expr(input: ParseStream) -> SynResult<TypeExpr> {
    let base = parse_type_atom(input)?;

    // Check for multi-binder marker: Type*
    if input.peek(Token![*]) {
        input.parse::<Token![*]>()?;
        return Ok(TypeExpr::MultiBinder(Box::new(base)));
    }

    Ok(base)
}

/// Parse an atomic type (no postfix operators)
fn parse_type_atom(input: ParseStream) -> SynResult<TypeExpr> {
    // Check for collection types: Vec(...), HashBag(...), HashSet(...)
    if input.peek(Ident) {
        let fork = input.fork();
        let ident: Ident = fork.parse()?;
        let ident_str = ident.to_string();

        if matches!(ident_str.as_str(), "Vec" | "HashBag" | "HashSet") {
            // Check if followed by parentheses
            if fork.peek(syn::token::Paren) {
                // Commit to collection parse
                let _: Ident = input.parse()?;
                let content;
                syn::parenthesized!(content in input);
                let element: TypeExpr = parse_type_expr(&content)?;

                let coll_type = match ident_str.as_str() {
                    "Vec" => CollectionType::Vec,
                    "HashBag" => CollectionType::HashBag,
                    "HashSet" => CollectionType::HashSet,
                    _ => unreachable!(),
                };

                return Ok(TypeExpr::Collection {
                    coll_type,
                    element: Box::new(element),
                });
            }
        }
    }

    // Check for arrow type: [Domain -> Codomain]
    if input.peek(syn::token::Bracket) {
        let content;
        syn::bracketed!(content in input);

        // Parse domain (which may itself be a bracketed type or include *)
        let domain = parse_type_expr(&content)?;

        // Expect ->
        content.parse::<Token![->]>()?;

        // Parse codomain
        let codomain = parse_type_expr(&content)?;

        return Ok(TypeExpr::Arrow {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        });
    }

    // Base type: just an identifier
    let ident: Ident = input.parse()?;
    Ok(TypeExpr::Base(ident))
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
    })
}

/// Parse new judgement-style syntax: `Label . context |- pattern : Type ;`
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
/// - Quoted strings become `Literal` tokens (keywords, punctuation, operators)
/// - Unquoted identifiers become `Ident` tokens (parameter references only)
fn parse_syntax_pattern(input: ParseStream) -> SynResult<Vec<SyntaxToken>> {
    let mut tokens = Vec::new();
    
    loop {
        // Check if we've reached `: Type` at the end
        // We detect this by: `:` followed by identifier followed by `;`
        if input.peek(Token![:]) {
            let fork = input.fork();
            let _ = fork.parse::<Token![:]>();
            if fork.peek(Ident) {
                let _ = fork.parse::<Ident>();
                if fork.peek(Token![;]) {
                    break;
                }
            }
        }
        
        // Parse the next token - only identifiers and string literals allowed
        if input.peek(Ident) {
            // Parameter reference
            tokens.push(SyntaxToken::Ident(input.parse::<Ident>()?));
        } else if input.peek(syn::LitStr) {
            // Quoted literal (keyword, punctuation, operator)
            let lit = input.parse::<syn::LitStr>()?;
            tokens.push(SyntaxToken::Literal(lit.value()));
        } else {
            // Unexpected token - provide helpful error message
            return Err(syn::Error::new(
                input.span(),
                "Expected parameter reference (identifier) or quoted literal (string). \
                 All syntax literals must be quoted, e.g.: \"for\" \"(\" x \"<-\" n \")\" \"{\" p \"}\""
            ));
        }
    }
    
    Ok(tokens)
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

pub fn parse_expr(input: ParseStream) -> SynResult<Expr> {
    // Parse lambda: ^x.body or ^[xs].body
    // Using caret since backslash isn't valid Rust tokenization
    if input.peek(Token![^]) {
        input.parse::<Token![^]>()?;

        // Check for multi-binder: ^[xs].body
        if input.peek(syn::token::Bracket) {
            let content;
            syn::bracketed!(content in input);
            let binder = content.parse::<Ident>()?;

            // Expect dot
            input.parse::<Token![.]>()?;

            // Parse body
            let body = parse_expr(input)?;

            return Ok(Expr::MultiLambda {
                binder,
                body: Box::new(body),
            });
        }

        // Single binder: ^x.body
        let binder = input.parse::<Ident>()?;
        input.parse::<Token![.]>()?;
        let body = parse_expr(input)?;

        return Ok(Expr::Lambda {
            binder,
            body: Box::new(body),
        });
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

    // =========================================================================
    // TypeExpr Tests
    // =========================================================================

    #[test]
    fn parse_type_expr_base() {
        let input = quote! { Name };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse base type: {:?}", result.err());

        let ty = result.unwrap();
        assert!(matches!(ty, TypeExpr::Base(ident) if ident == "Name"));
    }

    #[test]
    fn parse_type_expr_arrow() {
        let input = quote! { [Name -> Proc] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse arrow type: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                assert!(matches!(*domain, TypeExpr::Base(ref id) if id == "Name"));
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "Proc"));
            }
            _ => panic!("Expected Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_nested_arrow() {
        // Higher-order: [[A -> B] -> C]
        let input = quote! { [[A -> B] -> C] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse nested arrow: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "C"));
                match *domain {
                    TypeExpr::Arrow { domain: inner_domain, codomain: inner_codomain } => {
                        assert!(matches!(*inner_domain, TypeExpr::Base(ref id) if id == "A"));
                        assert!(matches!(*inner_codomain, TypeExpr::Base(ref id) if id == "B"));
                    }
                    _ => panic!("Expected inner Arrow type"),
                }
            }
            _ => panic!("Expected outer Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_multi_binder() {
        // [Name* -> Proc] is an arrow with MultiBinder domain
        let input = quote! { [Name* -> Proc] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse multi-binder: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                match *domain {
                    TypeExpr::MultiBinder(inner) => {
                        assert!(matches!(*inner, TypeExpr::Base(ref id) if id == "Name"));
                    }
                    _ => panic!("Expected MultiBinder domain, got {:?}", domain),
                }
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "Proc"));
            }
            _ => panic!("Expected Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_standalone_multi_binder() {
        // Name* without arrow context
        let input = quote! { Name* };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse standalone multi-binder: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::MultiBinder(inner) => {
                assert!(matches!(*inner, TypeExpr::Base(ref id) if id == "Name"));
            }
            _ => panic!("Expected MultiBinder type, got {:?}", ty),
        }
    }

    #[test]
    fn parse_type_expr_collection_vec() {
        let input = quote! { Vec(Name) };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse Vec: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Collection { coll_type, element } => {
                assert_eq!(coll_type, CollectionType::Vec);
                assert!(matches!(*element, TypeExpr::Base(ref id) if id == "Name"));
            }
            _ => panic!("Expected Collection type"),
        }
    }

    #[test]
    fn parse_type_expr_collection_hashbag() {
        let input = quote! { HashBag(Proc) };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse HashBag: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Collection { coll_type, element } => {
                assert_eq!(coll_type, CollectionType::HashBag);
                assert!(matches!(*element, TypeExpr::Base(ref id) if id == "Proc"));
            }
            _ => panic!("Expected Collection type"),
        }
    }

    #[test]
    fn type_expr_equality() {
        // Same types should be equal
        let ty1 = TypeExpr::base("Name");
        let ty2 = TypeExpr::base("Name");
        assert_eq!(ty1, ty2);

        // Different base types should not be equal
        let ty3 = TypeExpr::base("Proc");
        assert_ne!(ty1, ty3);

        // Arrow types
        let arr1 = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        let arr2 = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        assert_eq!(arr1, arr2);

        // Different arrows should not be equal
        let arr3 = TypeExpr::arrow(TypeExpr::base("Proc"), TypeExpr::base("Name"));
        assert_ne!(arr1, arr3);
    }

    #[test]
    fn type_expr_display() {
        let base = TypeExpr::base("Name");
        assert_eq!(format!("{}", base), "Name");

        let arrow = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        assert_eq!(format!("{}", arrow), "[Name -> Proc]");

        let multi = TypeExpr::arrow(
            TypeExpr::multi_binder(TypeExpr::base("Name")),
            TypeExpr::base("Proc"),
        );
        assert_eq!(format!("{}", multi), "[Name* -> Proc]");

        let standalone_multi = TypeExpr::multi_binder(TypeExpr::base("Name"));
        assert_eq!(format!("{}", standalone_multi), "Name*");

        let coll = TypeExpr::collection(CollectionType::Vec, TypeExpr::base("Name"));
        assert_eq!(format!("{}", coll), "Vec(Name)");
    }

    // =========================================================================
    // Expr Lambda Tests
    // =========================================================================

    use syn::parse::Parser;

    #[test]
    fn parse_expr_lambda_simple() {
        // ^x.body where body is a variable
        let input = quote! { ^x.p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(ref v) if v == "p"));
            }
            _ => panic!("Expected Lambda, got {:?}", expr),
        }
    }

    #[test]
    fn parse_expr_lambda_nested() {
        // ^x.^y.body - nested lambdas
        let input = quote! { ^x.^y.p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse nested lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                match *body {
                    Expr::Lambda { binder: inner_binder, body: inner_body } => {
                        assert_eq!(inner_binder.to_string(), "y");
                        assert!(matches!(*inner_body, Expr::Var(ref v) if v == "p"));
                    }
                    _ => panic!("Expected nested Lambda"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn parse_expr_multi_lambda() {
        // ^[xs].body - multi-binder lambda
        let input = quote! { ^[xs].p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse multi-lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::MultiLambda { binder, body } => {
                assert_eq!(binder.to_string(), "xs");
                assert!(matches!(*body, Expr::Var(ref v) if v == "p"));
            }
            _ => panic!("Expected MultiLambda, got {:?}", expr),
        }
    }

    #[test]
    fn parse_expr_lambda_with_apply() {
        // ^x.(Constructor x y) - lambda with constructor application body
        let input = quote! { ^x.(PPar x y) };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse lambda with apply: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                match *body {
                    Expr::Apply { constructor, args } => {
                        assert_eq!(constructor.to_string(), "PPar");
                        assert_eq!(args.len(), 2);
                    }
                    _ => panic!("Expected Apply in body"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    // =========================================================================
    // Expr free_vars, substitute, apply Tests
    // =========================================================================

    fn make_var(name: &str) -> Expr {
        Expr::Var(Ident::new(name, proc_macro2::Span::call_site()))
    }

    fn make_lambda(binder: &str, body: Expr) -> Expr {
        Expr::Lambda {
            binder: Ident::new(binder, proc_macro2::Span::call_site()),
            body: Box::new(body),
        }
    }

    fn make_apply(constructor: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            constructor: Ident::new(constructor, proc_macro2::Span::call_site()),
            args,
        }
    }

    #[test]
    fn test_free_vars_var() {
        let expr = make_var("x");
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("x"));
    }

    #[test]
    fn test_free_vars_apply() {
        // PPar(x, y) has free vars {x, y}
        let expr = make_apply("PPar", vec![make_var("x"), make_var("y")]);
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 2);
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
    }

    #[test]
    fn test_free_vars_lambda() {
        // ^x.y has free vars {y} (x is bound)
        let expr = make_lambda("x", make_var("y"));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("y"));
        assert!(!fv.contains("x"));
    }

    #[test]
    fn test_free_vars_lambda_bound() {
        // ^x.x has no free vars (x is bound)
        let expr = make_lambda("x", make_var("x"));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 0);
    }

    #[test]
    fn test_free_vars_nested_lambda() {
        // ^x.^y.z has free vars {z}
        let expr = make_lambda("x", make_lambda("y", make_var("z")));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("z"));
    }

    #[test]
    fn test_substitute_var_match() {
        // x[y/x] = y
        let expr = make_var("x");
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("y");
        
        let result = expr.substitute(&var, &replacement);
        assert!(matches!(result, Expr::Var(v) if v == "y"));
    }

    #[test]
    fn test_substitute_var_no_match() {
        // x[z/y] = x
        let expr = make_var("x");
        let var = Ident::new("y", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        assert!(matches!(result, Expr::Var(v) if v == "x"));
    }

    #[test]
    fn test_substitute_apply() {
        // PPar(x, y)[z/x] = PPar(z, y)
        let expr = make_apply("PPar", vec![make_var("x"), make_var("y")]);
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Apply { constructor, args } => {
                assert_eq!(constructor.to_string(), "PPar");
                assert!(matches!(&args[0], Expr::Var(v) if v == "z"));
                assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_substitute_lambda_shadowing() {
        // (^x.x)[y/x] = ^x.x (x is shadowed by binder)
        let expr = make_lambda("x", make_var("x"));
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("y");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(v) if v == "x"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_substitute_lambda_body() {
        // (^x.y)[z/y] = ^x.z
        let expr = make_lambda("x", make_var("y"));
        let var = Ident::new("y", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(v) if v == "z"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_apply_lambda() {
        // (^x.PPar(x, y))(z) = PPar(z, y)
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("y")]));
        let arg = make_var("z");
        
        let result = lambda.apply(&arg).expect("apply should succeed");
        match result {
            Expr::Apply { constructor, args } => {
                assert_eq!(constructor.to_string(), "PPar");
                assert!(matches!(&args[0], Expr::Var(v) if v == "z"));
                assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_apply_nested_lambda() {
        // (^x.^y.PPar(x, y))(a) = ^y.PPar(a, y)
        let lambda = make_lambda("x", make_lambda("y", make_apply("PPar", vec![make_var("x"), make_var("y")])));
        let arg = make_var("a");
        
        let result = lambda.apply(&arg).expect("apply should succeed");
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "y");
                match *body {
                    Expr::Apply { ref args, .. } => {
                        assert!(matches!(&args[0], Expr::Var(v) if v == "a"));
                        assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
                    }
                    _ => panic!("Expected Apply in body"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_apply_non_lambda_fails() {
        let expr = make_var("x");
        let arg = make_var("y");
        
        let result = expr.apply(&arg);
        assert!(result.is_err());
    }

    // =========================================================================
    // TypeContext and Type Checking Tests
    // =========================================================================

    fn make_base_type(name: &str) -> TypeExpr {
        TypeExpr::Base(Ident::new(name, proc_macro2::Span::call_site()))
    }

    fn make_arrow_type(domain: TypeExpr, codomain: TypeExpr) -> TypeExpr {
        TypeExpr::Arrow {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    #[test]
    fn test_type_context_empty() {
        let ctx = TypeContext::new();
        assert!(!ctx.contains("x"));
        assert!(ctx.lookup("x").is_none());
    }

    #[test]
    fn test_type_context_with_var() {
        let ctx = TypeContext::new();
        let name_type = make_base_type("Name");
        let extended = ctx.with_var("x", name_type.clone());
        
        assert!(extended.contains("x"));
        assert_eq!(extended.lookup("x"), Some(&name_type));
        
        // Original context should be unchanged
        assert!(!ctx.contains("x"));
    }

    #[test]
    fn test_infer_type_var_bound() {
        let ctx = TypeContext::new().with_var("x", make_base_type("Name"));
        let expr = make_var("x");
        
        let result = expr.infer_type(&ctx);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), make_base_type("Name"));
    }

    #[test]
    fn test_infer_type_var_unbound() {
        let ctx = TypeContext::new();
        let expr = make_var("x");
        
        let result = expr.infer_type(&ctx);
        assert!(result.is_err());
        match result {
            Err(TypeError::UnboundVariable(v)) => assert_eq!(v, "x"),
            _ => panic!("Expected UnboundVariable error"),
        }
    }

    #[test]
    fn test_check_type_lambda() {
        // Check that ^x.x : [Name -> Name]
        let lambda = make_lambda("x", make_var("x"));
        let arrow_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new();
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_check_type_lambda_body_uses_binder() {
        // ^x.PPar(x, y) : [Name -> Proc] in context where y:Proc
        // But we can't fully check Apply yet, so this will fail with CannotInfer
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("y")]));
        let arrow_type = make_arrow_type(make_base_type("Name"), make_base_type("Proc"));
        let ctx = TypeContext::new().with_var("y", make_base_type("Proc"));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        // This will fail because Apply type inference isn't implemented yet
        assert!(result.is_err());
    }

    #[test]
    fn test_check_type_nested_lambda() {
        // Check that ^x.^y.y : [A -> [B -> B]]
        let inner = make_lambda("y", make_var("y"));
        let outer = make_lambda("x", inner);
        
        let inner_arrow = make_arrow_type(make_base_type("B"), make_base_type("B"));
        let outer_arrow = make_arrow_type(make_base_type("A"), inner_arrow);
        let ctx = TypeContext::new();
        
        let result = outer.check_type(&outer_arrow, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_apply_typed() {
        // Apply (^x.x : [Name -> Name]) to (n : Name) = n
        let lambda = make_lambda("x", make_var("x"));
        let arg = make_var("n");
        let func_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new().with_var("n", make_base_type("Name"));
        
        let result = lambda.apply_typed(&arg, &ctx, &func_type);
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Expr::Var(v) if v == "n"));
    }

    #[test]
    fn test_apply_typed_wrong_arg_type() {
        // Apply (^x.x : [Name -> Name]) to (p : Proc) should fail
        let lambda = make_lambda("x", make_var("x"));
        let arg = make_var("p");
        let func_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new().with_var("p", make_base_type("Proc")); // Wrong type!
        
        let result = lambda.apply_typed(&arg, &ctx, &func_type);
        assert!(result.is_err());
        match result {
            Err(TypeError::TypeMismatch { expected, found, .. }) => {
                assert_eq!(expected, make_base_type("Name"));
                assert_eq!(found, make_base_type("Proc"));
            }
            _ => panic!("Expected TypeMismatch error"),
        }
    }
}
