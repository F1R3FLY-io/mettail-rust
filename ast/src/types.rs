use syn::{
    parse::{Parse, ParseStream},
    Ident, Result as SynResult, Token,
};

/// Collection type specifier
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CollectionType {
    HashBag,
    HashSet,
    Vec,
    HashMap,
    PathMap,
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

    /// Refinement type: `{ var: BaseType | predicate }`
    ///
    /// This variant is populated during refinement type lowering (Sprint RT5),
    /// not during initial parse — the parser produces `RefinementTypeDef`
    /// structs which are later lowered into `TypeExpr::Refined` nodes.
    Refined {
        /// The binding variable name.
        var: Ident,
        /// The base type being refined.
        base: Box<TypeExpr>,
        /// Serialized predicate representation (for display/debugging).
        predicate_repr: String,
    },

    /// Map type: `HashMap(K, V)`
    Map { key: Box<TypeExpr>, value: Box<TypeExpr> },
}

impl TypeExpr {
    /// True when this type is the builtin `Ident` — identifier TEXT, lowered to a bare
    /// `String`, NOT a grammar category.
    ///
    /// ★ THE PREDICATE EVERY CATEGORY-DRIVEN GENERATOR NEEDS, AND WHY IT EXISTS ONCE
    ///
    /// A generator that walks rule params to answer "which categories does this rule
    /// touch?" will, on seeing `m:Ident`, conclude `Ident` is a category and emit code
    /// naming a type that was never declared — `SubstOp::EnvIdent`,
    /// `into_term_arc::<Ident>()`, `Ident::parse(surface)`,
    /// `__mettail_dovetail_build_ident_d`. Each is a *correct* deduction from a *wrong*
    /// premise, which is why the failures are numerous, scattered, and identical in
    /// shape: they are one bug wearing eight coats.
    ///
    /// Naming the concept ONCE is what stops the ninth coat. Enumerating siblings by
    /// grepping for a symptom finds only the sites that happen to have been exercised;
    /// a named predicate makes the question "is this type a category?" answerable at
    /// every site that asks it, including sites written after this one.
    ///
    /// [`crate::grammar::NonTerminalKind::classify`] is the single source of truth for
    /// what the name `Ident` means; this method exists so callers holding a
    /// [`TypeExpr`] need not reach through it by hand.
    #[must_use]
    pub fn is_ident_text(&self) -> bool {
        matches!(
            self,
            TypeExpr::Base(id)
                if crate::grammar::NonTerminalKind::classify(&id.to_string())
                    == crate::grammar::NonTerminalKind::Ident
        )
    }
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
                    CollectionType::HashMap => "HashMap",
                    CollectionType::PathMap => "PathMap",
                };
                write!(f, "{}({})", coll_name, element)
            },
            TypeExpr::Refined { var, base, predicate_repr } => {
                write!(f, "{{ {}: {} | {} }}", var, base, predicate_repr)
            },
            TypeExpr::Map { key, value } => write!(f, "HashMap({}, {})", key, value),
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

        if matches!(ident_str.as_str(), "Vec" | "HashBag" | "HashSet" | "HashMap") {
            // Check if followed by parentheses
            if fork.peek(syn::token::Paren) {
                // Commit to collection parse
                let _: Ident = input.parse()?;
                let content;
                syn::parenthesized!(content in input);

                if ident_str == "HashMap" {
                    let key: TypeExpr = parse_type_expr(&content)?;
                    content.parse::<Token![,]>()?;
                    let value: TypeExpr = parse_type_expr(&content)?;
                    return Ok(TypeExpr::Map {
                        key: Box::new(key),
                        value: Box::new(value),
                    });
                }

                let element: TypeExpr = parse_type_expr(&content)?;
                // ★ #141 G5. The `unreachable!()` rested on the enclosing
                // `if` having already tested the same three names — a claim about
                // two lists staying in step, held by nothing. `parse_type_expr`
                // returns `syn::Result`, so the refusal is a spanned parse error.
                let coll_type = match ident_str.as_str() {
                    "Vec" => CollectionType::Vec,
                    "HashBag" => CollectionType::HashBag,
                    "HashSet" => CollectionType::HashSet,
                    other => {
                        return Err(syn::Error::new(
                            ident.span(),
                            format!(
                                "mettail internal error: the collection-type lookahead \
                                 accepted `{other}` but this parser builds a \
                                 `CollectionType` only for `Vec`, `HashBag` and \
                                 `HashSet`, so the two have drifted apart. This is a \
                                 macro bug, not a grammar bug — please report it."
                            ),
                        ));
                    },
                };

                return Ok(TypeExpr::Collection { coll_type, element: Box::new(element) });
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
}
