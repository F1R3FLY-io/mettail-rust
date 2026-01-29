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

//=============================================================================
// HOL RUST CODE BLOCKS AND EVAL MODE
//=============================================================================

/// Rust code block for HOL syntax in grammar rules
/// Example: `![a + b]` in `Add . a:Int, b:Int |- a "+" b:Int ![a + b] fold;`
#[derive(Debug, Clone)]
pub struct RustCodeBlock {
    /// Parsed Rust expression
    pub code: syn::Expr,
}

/// Evaluation mode for HOL syntax (when to apply constant folding vs congruence)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalMode {
    /// Only constant folding
    Fold,
    /// Only step-by-step (congruence rules)
    Step,
    /// Both folding and congruence (default)
    Both,
}

