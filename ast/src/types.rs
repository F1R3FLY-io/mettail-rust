use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};
use syn::{
    Ident, Result as SynResult, Token,
    parse::{Parse, ParseStream},
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

impl Clone for TypeExpr {
    fn clone(&self) -> Self {
        enum Task<'ty> {
            Visit(&'ty TypeExpr),
            Arrow,
            MultiBinder,
            Collection(CollectionType),
            Refined { var: Ident, predicate_repr: String },
            Map,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypeExpr::Base(ident)) => values.push(TypeExpr::Base(ident.clone())),
                Task::Visit(TypeExpr::Arrow { domain, codomain }) => {
                    tasks.push(Task::Arrow);
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(TypeExpr::MultiBinder(inner)) => {
                    tasks.push(Task::MultiBinder);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(TypeExpr::Collection { coll_type, element }) => {
                    tasks.push(Task::Collection(coll_type.clone()));
                    tasks.push(Task::Visit(element));
                },
                Task::Visit(TypeExpr::Refined { var, base, predicate_repr }) => {
                    tasks.push(Task::Refined {
                        var: var.clone(),
                        predicate_repr: predicate_repr.clone(),
                    });
                    tasks.push(Task::Visit(base));
                },
                Task::Visit(TypeExpr::Map { key, value }) => {
                    tasks.push(Task::Map);
                    tasks.push(Task::Visit(value));
                    tasks.push(Task::Visit(key));
                },
                Task::Arrow => {
                    let codomain = values.pop().expect("TypeExpr clone PDA lost its codomain");
                    let domain = values.pop().expect("TypeExpr clone PDA lost its domain");
                    values.push(TypeExpr::Arrow {
                        domain: Box::new(domain),
                        codomain: Box::new(codomain),
                    });
                },
                Task::MultiBinder => {
                    let inner = values
                        .pop()
                        .expect("TypeExpr clone PDA lost its inner type");
                    values.push(TypeExpr::MultiBinder(Box::new(inner)));
                },
                Task::Collection(coll_type) => {
                    let element = values
                        .pop()
                        .expect("TypeExpr clone PDA lost its element type");
                    values.push(TypeExpr::Collection { coll_type, element: Box::new(element) });
                },
                Task::Refined { var, predicate_repr } => {
                    let base = values
                        .pop()
                        .expect("TypeExpr clone PDA lost its refined base");
                    values.push(TypeExpr::Refined {
                        var,
                        base: Box::new(base),
                        predicate_repr,
                    });
                },
                Task::Map => {
                    let value = values.pop().expect("TypeExpr clone PDA lost its map value");
                    let key = values.pop().expect("TypeExpr clone PDA lost its map key");
                    values.push(TypeExpr::Map {
                        key: Box::new(key),
                        value: Box::new(value),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("TypeExpr clone PDA produced no result")
    }
}

impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TypeExpr::Base(left), TypeExpr::Base(right)) if left == right => {},
                (
                    TypeExpr::Arrow {
                        domain: left_domain,
                        codomain: left_codomain,
                    },
                    TypeExpr::Arrow {
                        domain: right_domain,
                        codomain: right_codomain,
                    },
                ) => {
                    work.push((left_domain, right_domain));
                    work.push((left_codomain, right_codomain));
                },
                (TypeExpr::MultiBinder(left), TypeExpr::MultiBinder(right)) => {
                    work.push((left, right));
                },
                (
                    TypeExpr::Collection {
                        coll_type: left_kind,
                        element: left_element,
                    },
                    TypeExpr::Collection {
                        coll_type: right_kind,
                        element: right_element,
                    },
                ) if left_kind == right_kind => work.push((left_element, right_element)),
                (
                    TypeExpr::Refined {
                        var: left_var,
                        base: left_base,
                        predicate_repr: left_predicate,
                    },
                    TypeExpr::Refined {
                        var: right_var,
                        base: right_base,
                        predicate_repr: right_predicate,
                    },
                ) if left_var == right_var && left_predicate == right_predicate => {
                    work.push((left_base, right_base));
                },
                (
                    TypeExpr::Map { key: left_key, value: left_value },
                    TypeExpr::Map { key: right_key, value: right_value },
                ) => {
                    work.push((left_key, right_key));
                    work.push((left_value, right_value));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for TypeExpr {}

impl Drop for TypeExpr {
    fn drop(&mut self) {
        fn placeholder() -> TypeExpr {
            TypeExpr::Base(Ident::new("_", proc_macro2::Span::call_site()))
        }

        fn take_child(child: &mut Box<TypeExpr>) -> TypeExpr {
            *std::mem::replace(child, Box::new(placeholder()))
        }

        fn take_children(node: &mut TypeExpr, work: &mut Vec<TypeExpr>) {
            match node {
                TypeExpr::Arrow { domain, codomain } => {
                    work.push(take_child(domain));
                    work.push(take_child(codomain));
                },
                TypeExpr::MultiBinder(inner) => work.push(take_child(inner)),
                TypeExpr::Collection { element, .. } => work.push(take_child(element)),
                TypeExpr::Refined { base, .. } => work.push(take_child(base)),
                TypeExpr::Map { key, value } => {
                    work.push(take_child(key));
                    work.push(take_child(value));
                },
                TypeExpr::Base(_) => {},
            }
        }

        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut node) = work.pop() {
            take_children(&mut node, &mut work);
        }
    }
}

impl std::fmt::Debug for TypeExpr {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'ty> {
            Visit(&'ty TypeExpr),
            Text(&'static str),
            Predicate(&'ty str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypeExpr::Base(ident)) => write!(formatter, "Base({ident:?})")?,
                Task::Visit(TypeExpr::Arrow { domain, codomain }) => {
                    formatter.write_str("Arrow { domain: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Text(", codomain: "));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(TypeExpr::MultiBinder(inner)) => {
                    formatter.write_str("MultiBinder(")?;
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(TypeExpr::Collection { coll_type, element }) => {
                    write!(formatter, "Collection {{ coll_type: {coll_type:?}, element: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Visit(element));
                },
                Task::Visit(TypeExpr::Refined { var, base, predicate_repr }) => {
                    write!(formatter, "Refined {{ var: {var:?}, base: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Predicate(predicate_repr));
                    tasks.push(Task::Visit(base));
                },
                Task::Visit(TypeExpr::Map { key, value }) => {
                    formatter.write_str("Map { key: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Visit(value));
                    tasks.push(Task::Text(", value: "));
                    tasks.push(Task::Visit(key));
                },
                Task::Text(text) => formatter.write_str(text)?,
                Task::Predicate(predicate) => {
                    write!(formatter, ", predicate_repr: {predicate:?}")?;
                },
            }
        }
        Ok(())
    }
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
        enum Task<'ty> {
            Visit(&'ty TypeExpr),
            Text(&'static str),
            Predicate(&'ty str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypeExpr::Base(ident)) => write!(f, "{ident}")?,
                Task::Visit(TypeExpr::Arrow { domain, codomain }) => {
                    f.write_str("[")?;
                    tasks.push(Task::Text("]"));
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Text(" -> "));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(TypeExpr::MultiBinder(inner)) => {
                    tasks.push(Task::Text("*"));
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(TypeExpr::Collection { coll_type, element }) => {
                    f.write_str(match coll_type {
                        CollectionType::Vec => "Vec(",
                        CollectionType::HashBag => "HashBag(",
                        CollectionType::HashSet => "HashSet(",
                        CollectionType::HashMap => "HashMap(",
                        CollectionType::PathMap => "PathMap(",
                    })?;
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(element));
                },
                Task::Visit(TypeExpr::Refined { var, base, predicate_repr }) => {
                    write!(f, "{{ {var}: ")?;
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Predicate(predicate_repr));
                    tasks.push(Task::Text(" | "));
                    tasks.push(Task::Visit(base));
                },
                Task::Visit(TypeExpr::Map { key, value }) => {
                    f.write_str("HashMap(")?;
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(value));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(key));
                },
                Task::Text(text) => f.write_str(text)?,
                Task::Predicate(predicate) => f.write_str(predicate)?,
            }
        }
        Ok(())
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
    let mut atom = TokenStream::new();
    if input.peek(Ident) {
        let ident = input.parse::<Ident>()?;
        atom.extend([TokenTree::Ident(ident)]);
        if input.peek(syn::token::Paren) {
            let content;
            let delimiters = syn::parenthesized!(content in input);
            let mut group = Group::new(Delimiter::Parenthesis, content.parse()?);
            group.set_span(delimiters.span.open());
            atom.extend([TokenTree::Group(group)]);
        }
    } else if input.peek(syn::token::Bracket) {
        let content;
        let delimiters = syn::bracketed!(content in input);
        let mut group = Group::new(Delimiter::Bracket, content.parse()?);
        group.set_span(delimiters.span.open());
        atom.extend([TokenTree::Group(group)]);
    } else {
        return Err(input.error("expected a type name, collection, or `[domain -> codomain]`"));
    }

    let mut parsed = parse_type_tokens(atom)?;

    // Check for multi-binder marker: Type*
    if input.peek(Token![*]) {
        input.parse::<Token![*]>()?;
        parsed = TypeExpr::MultiBinder(Box::new(parsed));
    }

    Ok(parsed)
}

/// Parse an owned token-tree representation with an explicit reduce stack.
/// Nested delimiter groups are atomic `TokenTree::Group` values, so neither
/// arrows nor collection element types consume native call-stack depth.
fn parse_type_tokens(tokens: TokenStream) -> SynResult<TypeExpr> {
    enum ParseTask {
        Parse(TokenStream),
        MultiBinder,
        Collection(CollectionType),
        Map,
        Arrow,
    }

    fn split_once(
        tokens: Vec<TokenTree>,
        delimiter: impl Fn(&[TokenTree], usize) -> Option<usize>,
        expected: &str,
        span: proc_macro2::Span,
    ) -> SynResult<(TokenStream, TokenStream)> {
        let Some((index, width)) = tokens
            .iter()
            .enumerate()
            .find_map(|(index, _)| delimiter(&tokens, index).map(|width| (index, width)))
        else {
            return Err(syn::Error::new(span, expected));
        };
        let left = tokens[..index].iter().cloned().collect();
        let right = tokens[index + width..].iter().cloned().collect();
        Ok((left, right))
    }

    let mut tasks = vec![ParseTask::Parse(tokens)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ParseTask::Parse(tokens) => {
                let mut tokens = tokens.into_iter().collect::<Vec<_>>();
                let multi = matches!(tokens.last(), Some(TokenTree::Punct(punct)) if punct.as_char() == '*');
                if multi {
                    tokens.pop();
                    tasks.push(ParseTask::MultiBinder);
                }

                match tokens.as_slice() {
                    [TokenTree::Ident(ident)] => values.push(TypeExpr::Base(ident.clone())),
                    [TokenTree::Ident(ident), TokenTree::Group(group)]
                        if group.delimiter() == Delimiter::Parenthesis =>
                    {
                        let kind = ident.to_string();
                        if kind == "HashMap" {
                            let inner = group.stream().into_iter().collect::<Vec<_>>();
                            let (key, value) = split_once(
                                inner,
                                |tokens, index| match tokens.get(index) {
                                    Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => {
                                        Some(1)
                                    },
                                    _ => None,
                                },
                                "expected `,` between HashMap key and value types",
                                group.span(),
                            )?;
                            tasks.push(ParseTask::Map);
                            tasks.push(ParseTask::Parse(value));
                            tasks.push(ParseTask::Parse(key));
                        } else {
                            let coll_type = match kind.as_str() {
                                "Vec" => CollectionType::Vec,
                                "HashBag" => CollectionType::HashBag,
                                "HashSet" => CollectionType::HashSet,
                                "PathMap" => CollectionType::PathMap,
                                _ => {
                                    return Err(syn::Error::new(
                                        ident.span(),
                                        format!("unknown collection type `{kind}`"),
                                    ));
                                },
                            };
                            tasks.push(ParseTask::Collection(coll_type));
                            tasks.push(ParseTask::Parse(group.stream()));
                        }
                    },
                    [TokenTree::Group(group)] if group.delimiter() == Delimiter::Bracket => {
                        let inner = group.stream().into_iter().collect::<Vec<_>>();
                        let (domain, codomain) = split_once(
                            inner,
                            |tokens, index| match (tokens.get(index), tokens.get(index + 1)) {
                                (Some(TokenTree::Punct(left)), Some(TokenTree::Punct(right)))
                                    if left.as_char() == '-' && right.as_char() == '>' =>
                                {
                                    Some(2)
                                },
                                _ => None,
                            },
                            "expected `->` between arrow domain and codomain",
                            group.span(),
                        )?;
                        tasks.push(ParseTask::Arrow);
                        tasks.push(ParseTask::Parse(codomain));
                        tasks.push(ParseTask::Parse(domain));
                    },
                    _ => {
                        let span = tokens
                            .first()
                            .map(TokenTree::span)
                            .unwrap_or_else(proc_macro2::Span::call_site);
                        return Err(syn::Error::new(span, "malformed type expression"));
                    },
                }
            },
            ParseTask::MultiBinder => {
                let value = values.pop().expect("type parser PDA lost its operand");
                values.push(TypeExpr::MultiBinder(Box::new(value)));
            },
            ParseTask::Collection(coll_type) => {
                let element = values.pop().expect("type parser PDA lost its element type");
                values.push(TypeExpr::Collection { coll_type, element: Box::new(element) });
            },
            ParseTask::Map => {
                let value = values.pop().expect("type parser PDA lost its map value");
                let key = values.pop().expect("type parser PDA lost its map key");
                values.push(TypeExpr::Map {
                    key: Box::new(key),
                    value: Box::new(value),
                });
            },
            ParseTask::Arrow => {
                let codomain = values.pop().expect("type parser PDA lost its codomain");
                let domain = values.pop().expect("type parser PDA lost its domain");
                values.push(TypeExpr::Arrow {
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                });
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .ok_or_else(|| syn::Error::new(proc_macro2::Span::call_site(), "empty type expression"))
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
