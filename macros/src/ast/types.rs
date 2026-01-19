use syn::{Ident, Token, parse::{Parse, ParseStream}, Result as SynResult};

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

