use super::*;

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

        // Parse: types { ... } (may include refinement type definitions)
        let (types, refinement_types) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "types" {
                parse_types(input)?
            } else {
                (Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new())
        };

        // Parse: literals { ... } (optional; types{} must precede; desugars to TokenDef)
        let literals_defs: Vec<TokenDef> = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "literals" {
                parse_literals(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: tokens { ... } (optional)
        let TokensBlock {
            mut token_defs,
            mode_defs,
            sync_constraints,
            tree_invariants,
        } = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "tokens" {
                parse_tokens(input)?
            } else {
                TokensBlock::default()
            }
        } else {
            TokensBlock::default()
        };

        // Validate every literals{} name is declared in types{}.
        // (Done before name-mapping so the diagnostic references the original name.)
        for ld in &literals_defs {
            if !types.iter().any(|t| t.name == ld.name) {
                return Err(syn::Error::new(
                    ld.name.span(),
                    format!(
                        "literals{{{}}} requires '{}' to be declared in types{{}}",
                        ld.name, ld.name
                    ),
                ));
            }
        }

        // Map each literals{} entry to its standard `Token::<name>` family
        // variant based on the category's native type. All integer-typed
        // categories share `Token::Integer(IntLit)`, all rational-typed
        // share `Token::Rational(RationalLit)`, etc. The original category
        // name is preserved in `TokenDef.category` so downstream codegen
        // can route per-category eval logic to the same variant.
        //
        // Categories whose native type doesn't fit a known family (or
        // categories with no native type) keep their user-facing
        // TypeName as the Token variant.
        let literals_defs: Vec<TokenDef> = literals_defs
            .into_iter()
            .map(|ld| {
                let original = ld.name.clone();
                let mapped_name = types
                    .iter()
                    .find(|t| t.name == original)
                    .and_then(|t| t.native_type.as_ref())
                    .and_then(|nt| NativeKind::from_syn_type(nt).standard_token_variant())
                    .map(|s| Ident::new(s, original.span()))
                    .unwrap_or_else(|| original.clone());
                TokenDef {
                    name: mapped_name,
                    pattern: ld.pattern,
                    // Preserve the original category so codegen can disambiguate
                    // shared-family variants per literal source.
                    category: Some(original),
                    rust_code: ld.rust_code,
                    priority: ld.priority,
                    push_mode: ld.push_mode,
                    is_pop: ld.is_pop,
                    stream: ld.stream,
                    from_literals: true,
                }
            })
            .collect();

        // Detect cross-block duplicates by `(name, pattern)` rather than name
        // alone — `literals { Int { ... } BigInt { ... } }` legitimately
        // produces two TokenDefs that share `name = Integer` (one Token
        // variant per family) but with distinct patterns.
        for ld in &literals_defs {
            if token_defs
                .iter()
                .any(|td| td.name == ld.name && td.pattern == ld.pattern)
            {
                return Err(syn::Error::new(
                    ld.name.span(),
                    format!(
                        "duplicate token (name '{}', identical pattern) declared in both \
                         literals{{}} and tokens{{}}",
                        ld.name
                    ),
                ));
            }
        }
        token_defs.extend(literals_defs);

        // Parse: guards { ... } (optional, design doc §2A)
        let guard_config = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "guards" {
                Some(parse_guards(input)?)
            } else {
                None
            }
        } else {
            None
        };

        // Build the active connective map (if `connectives {}` was declared)
        // and install it as a thread-local for the duration of the rest of
        // the parse, so behavioral predicate parsing inside rewrite/equation
        // premises recognizes the declared keywords.
        let active_map = guard_config
            .as_ref()
            .and_then(|gc| gc.connectives.as_ref())
            .and_then(|decls| ConnectiveMap::from_decls(decls).ok());

        let _guard = ConnectiveMapGuard::install(active_map);

        // Parse: terms { ... }
        let mut terms = if input.peek(Ident) {
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

        // L9-3: post-parse token-kind classification. A bare `Param(x)` in a
        // rule's syntax pattern whose `x` is a DECLARED token kind (top-level
        // `tokens {}` or any mode) and is NOT a term-context param of that rule
        // is reclassified to `TokenKind{name:x, bind:None}` (match the kind, no
        // capture). This is the ONLY step that makes a `TokenKind` constructible
        // from source WITHOUT the `@` bind form. A genuine typed param shadows a
        // like-named token (decision D-3). Recurses into `#opt`/`#map` bodies.
        {
            let mut declared_kinds: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            for td in &token_defs {
                declared_kinds.insert(td.name.to_string());
            }
            for md in &mode_defs {
                for td in &md.token_defs {
                    declared_kinds.insert(td.name.to_string());
                }
            }
            if !declared_kinds.is_empty() {
                for rule in &mut terms {
                    let ctx_names = term_context_param_names(rule.term_context.as_ref());
                    if let Some(sp) = rule.syntax_pattern.as_mut() {
                        reclassify_token_kinds(sp, &declared_kinds, &ctx_names);
                    }
                }
            }
        }

        Ok(LanguageDef {
            name,
            options,
            extends_names,
            include_names,
            mixin_names,
            types,
            refinement_types,
            token_defs,
            mode_defs,
            sync_constraints,
            tree_invariants,
            terms,
            equations,
            rewrites,
            logic,
            guard_config,
        })
    }
}

/// L9-3: collect the names BOUND by a rule's term-context params, so a
/// like-named declared token does NOT shadow a genuine typed param (D-3).
fn term_context_param_names(
    tc: Option<&Vec<crate::grammar::TermParam>>,
) -> std::collections::HashSet<String> {
    use crate::grammar::TermParam;
    let mut out = std::collections::HashSet::new();
    let mut pending: Vec<&TermParam> = tc
        .into_iter()
        .flat_map(|params| params.iter().rev())
        .collect();
    while let Some(param) = pending.pop() {
        match param {
            TermParam::Simple { name, .. } | TermParam::GuardBody { name } => {
                out.insert(name.to_string());
            },
            TermParam::Abstraction { binder, body, .. }
            | TermParam::MultiAbstraction { binder, body, .. } => {
                out.insert(binder.to_string());
                out.insert(body.to_string());
            },
            TermParam::Optional { params } => pending.extend(params.iter().rev()),
        }
    }
    out
}

/// L9-3: reclassify a bare `Param(x)` → `TokenKind{name:x, bind:None}` when `x`
/// is a declared token kind and not a term-context param. Recurses into
/// `#opt`/`#map` bodies (a `#map` closure param shadows a like-named token
/// inside its body). The traversal is one explicit scoped worklist, so nesting
/// in `#opt`/`#map` follows heap capacity rather than the proc-macro stack.
fn reclassify_token_kinds(
    exprs: &mut [crate::grammar::SyntaxExpr],
    declared_kinds: &std::collections::HashSet<String>,
    ctx_names: &std::collections::HashSet<String>,
) {
    use crate::grammar::{PatternOp, SyntaxExpr};

    enum Task<'syntax> {
        Expr(&'syntax mut SyntaxExpr),
        Op(&'syntax mut PatternOp),
        Enter(Vec<String>),
        Exit(Vec<String>),
    }

    let mut active_names: std::collections::HashMap<String, usize> =
        ctx_names.iter().cloned().map(|name| (name, 1)).collect();
    let mut tasks: Vec<Task<'_>> = exprs.iter_mut().rev().map(Task::Expr).collect();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Expr(expr) => match expr {
                SyntaxExpr::Param(ident) => {
                    let name = ident.to_string();
                    if declared_kinds.contains(&name) && !active_names.contains_key(&name) {
                        *expr = SyntaxExpr::TokenKind { name: ident.clone(), bind: None };
                    }
                },
                SyntaxExpr::Op(op) => tasks.push(Task::Op(op)),
                // L9-4: a GuestBody's open/close are already token KINDS
                // (written explicitly in `*flt(bind, open, close)`).
                SyntaxExpr::Literal(_)
                | SyntaxExpr::TokenKind { .. }
                | SyntaxExpr::GuestBody { .. } => {},
            },
            Task::Op(PatternOp::Opt { inner }) => {
                tasks.extend(inner.iter_mut().rev().map(Task::Expr));
            },
            Task::Op(PatternOp::Map { source, params, body }) => {
                let names: Vec<String> = params.iter().map(ToString::to_string).collect();
                tasks.push(Task::Exit(names.clone()));
                tasks.extend(body.iter_mut().rev().map(Task::Expr));
                tasks.push(Task::Enter(names));
                tasks.push(Task::Op(source));
            },
            Task::Op(PatternOp::Sep { source: Some(inner), .. }) => {
                tasks.push(Task::Op(inner));
            },
            Task::Op(PatternOp::Sep { source: None, .. })
            | Task::Op(PatternOp::Zip { .. })
            | Task::Op(PatternOp::Var(_)) => {},
            Task::Enter(names) => {
                for name in names {
                    *active_names.entry(name).or_default() += 1;
                }
            },
            Task::Exit(names) => {
                for name in names {
                    let depth = active_names
                        .get_mut(&name)
                        .expect("entered map parameter must remain active");
                    *depth -= 1;
                    if *depth == 0 {
                        active_names.remove(&name);
                    }
                }
            },
        }
    }
}

/// Parse a non-empty array of string literals: `["a", "b", ...]`.
/// Used by the brace-dict collection-delimiter form (main / Rholang 1.4).
fn parse_string_lit_array(input: ParseStream) -> SynResult<Vec<String>> {
    let arr;
    syn::bracketed!(arr in input);
    let mut parts = Vec::new();
    while !arr.is_empty() {
        parts.push(arr.parse::<syn::LitStr>()?.value());
        if arr.peek(Token![,]) {
            let _ = arr.parse::<Token![,]>()?;
        }
    }
    if parts.is_empty() {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "collection delimiter array must be non-empty",
        ));
    }
    Ok(parts)
}

/// Parse the brace-dict collection-delimiter form (main / Rholang 1.4):
/// `{ open_parts: ["..."], close_parts: ["..."], sep: "...", key_val_sep: "..." }`.
/// Multi-element `open_parts`/`close_parts` arrays are concatenated into the single
/// `open`/`close` strings — feature's collection codegen uses single delimiter strings,
/// and every `language!` declaration that uses this form supplies single-element arrays.
fn parse_collection_delimiters_dict(
    input: ParseStream,
    allow_kv: bool,
    require_kv: bool,
) -> SynResult<CollectionDelimiters> {
    let dict;
    syn::braced!(dict in input);
    let mut open: Option<String> = None;
    let mut close: Option<String> = None;
    let mut sep: Option<String> = None;
    let mut key_val_sep: Option<String> = None;
    while !dict.is_empty() {
        let key: Ident = dict.parse()?;
        let _ = dict.parse::<Token![:]>()?;
        match key.to_string().as_str() {
            "open_parts" => open = Some(parse_string_lit_array(&dict)?.concat()),
            "close_parts" => close = Some(parse_string_lit_array(&dict)?.concat()),
            "sep" => sep = Some(dict.parse::<syn::LitStr>()?.value()),
            "key_val_sep" => key_val_sep = Some(dict.parse::<syn::LitStr>()?.value()),
            other => {
                return Err(syn::Error::new(
                    key.span(),
                    format!(
                        "unknown collection delimiter key `{other}` (expected open_parts/close_parts/sep/key_val_sep)"
                    ),
                ))
            },
        }
        if dict.peek(Token![,]) {
            let _ = dict.parse::<Token![,]>()?;
        }
    }
    let span = proc_macro2::Span::call_site();
    let open = open
        .ok_or_else(|| syn::Error::new(span, "collection delimiters dict requires `open_parts`"))?;
    let close = close.ok_or_else(|| {
        syn::Error::new(span, "collection delimiters dict requires `close_parts`")
    })?;
    let sep =
        sep.ok_or_else(|| syn::Error::new(span, "collection delimiters dict requires `sep`"))?;
    if !allow_kv && key_val_sep.is_some() {
        return Err(syn::Error::new(span, "this collection does not accept `key_val_sep`"));
    }
    if require_kv && key_val_sep.is_none() {
        return Err(syn::Error::new(span, "Map collection requires `key_val_sep`"));
    }
    // A key/value collection that accepts `key_val_sep` but omits it (e.g. `Pathmap`,
    // whose dict block need not restate `:`) defaults to `":"`, matching the no-block
    // `pathmap_defaults()`. Without this it would parse as a single-element collection
    // and reject `{| k: v |}` at the `:`.
    let key_val_sep = if allow_kv {
        key_val_sep.or_else(|| Some(":".to_string()))
    } else {
        key_val_sep
    };
    Ok(CollectionDelimiters { open, close, sep, key_val_sep })
}

fn parse_types(input: ParseStream) -> SynResult<(Vec<LangType>, Vec<RefinementTypeDef>)> {
    let types_ident = input.parse::<Ident>()?;
    if types_ident != "types" {
        return Err(syn::Error::new(types_ident.span(), "expected 'types'"));
    }

    let content;
    syn::braced!(content in input);

    let mut types = Vec::new();
    let mut refinement_types = Vec::new();
    while !content.is_empty() {
        // Check for native type syntax: ![Type] as Name
        if content.peek(Token![!]) {
            let _ = content.parse::<Token![!]>()?;

            // Parse [Type] - the brackets are part of the syntax, not the type
            let bracket_content;
            syn::bracketed!(bracket_content in content);
            let native_type_raw = bracket_content.parse::<Type>()?;

            let _ = content.parse::<Token![as]>()?;
            let name = content.parse::<Ident>()?;
            let name_str = name.to_string();

            // Special-case Map: `![HashMap] as Map` or `![HashMap<Proc, Proc>] as Map`
            // expand to the runtime wrapper (HashMapLit) so the engine's deterministic Hash/Ord apply.
            let native_type = if name_str == "Map" {
                let is_hashmap = match &native_type_raw {
                    Type::Path(tp) => tp.path.segments.last().is_some_and(|seg| {
                        seg.ident == "HashMap"
                            && matches!(
                                seg.arguments,
                                syn::PathArguments::None | syn::PathArguments::AngleBracketed(_)
                            )
                    }),
                    _ => false,
                };
                if is_hashmap {
                    syn::parse_str::<Type>("mettail_runtime::HashMapLit<Proc, Proc>")
                        .expect("parse Map native type")
                } else {
                    native_type_raw
                }
            } else {
                native_type_raw
            };

            // Optional (Param) legacy backward-compat, plus custom delimiters in either the
            // positional `[open, close, sep (, kv_sep)]` form (feature legacy) or the brace-dict
            // `{ open_parts: [...], close_parts: [...], sep: ..., key_val_sep: ... }` form
            // (main / Rholang 1.4). Applies to List/Bag/Map/Set/Pathmap.
            let is_collection =
                matches!(name_str.as_str(), "List" | "Bag" | "Map" | "Set" | "Pathmap");
            let collection_kind = if is_collection {
                if content.peek(syn::token::Paren) {
                    let paren_content;
                    syn::parenthesized!(paren_content in content);
                    // Consume legacy params: List(Proc), Bag(Proc), Set(Proc), Map(Proc, Proc), Pathmap(Proc, Proc)
                    let _ = paren_content.parse::<Ident>()?;
                    if (name_str == "Map" || name_str == "Pathmap") && paren_content.peek(Token![,])
                    {
                        let _ = paren_content.parse::<Token![,]>()?;
                        let _ = paren_content.parse::<Ident>()?;
                    }
                }
                let allow_kv = name_str == "Map" || name_str == "Pathmap";
                let require_kv = name_str == "Map";
                let delimiters: CollectionDelimiters = if content.peek(syn::token::Brace) {
                    parse_collection_delimiters_dict(&content, allow_kv, require_kv)?
                } else if content.peek(syn::token::Bracket) {
                    let bracket_content;
                    syn::bracketed!(bracket_content in content);
                    let open: syn::LitStr = bracket_content.parse()?;
                    let _ = bracket_content.parse::<Token![,]>()?;
                    let close: syn::LitStr = bracket_content.parse()?;
                    let _ = bracket_content.parse::<Token![,]>()?;
                    let sep: syn::LitStr = bracket_content.parse()?;
                    let key_val_sep = if allow_kv && bracket_content.peek(Token![,]) {
                        let _ = bracket_content.parse::<Token![,]>()?;
                        Some(bracket_content.parse::<syn::LitStr>()?.value())
                    } else {
                        None
                    };
                    CollectionDelimiters {
                        open: open.value(),
                        close: close.value(),
                        sep: sep.value(),
                        key_val_sep,
                    }
                } else {
                    match name_str.as_str() {
                        "List" => CollectionCategory::list_defaults(),
                        "Bag" => CollectionCategory::bag_defaults(),
                        "Map" => CollectionCategory::map_defaults(),
                        "Set" => CollectionCategory::set_defaults(),
                        _ => CollectionCategory::pathmap_defaults(),
                    }
                };
                Some(match name_str.as_str() {
                    "List" => CollectionCategory::List(delimiters),
                    "Bag" => CollectionCategory::Bag(delimiters),
                    "Map" => CollectionCategory::Map(delimiters),
                    "Set" => CollectionCategory::Set(delimiters),
                    _ => CollectionCategory::Pathmap(delimiters),
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
            // Could be either:
            //   Name               — regular type (including bare `List`/`Bag`/`Map` with defaults)
            //   Name = { ... }     — refinement type
            let name = content.parse::<Ident>()?;

            if content.peek(Token![=]) {
                // Refinement type: Name = { var: BaseType | predicate };
                // Also push a LangType entry so the rest of the pipeline
                // (Ascent relation emission, rule validation, etc.) treats
                // PosInt as a first-class category.
                let _ = content.parse::<Token![=]>()?;
                let ref_def = parse_refinement_type_body(&content, name.clone())?;
                types.push(LangType {
                    name,
                    native_type: None,
                    collection_kind: None,
                });
                refinement_types.push(ref_def);
            } else {
                let name_str = name.to_string();
                let collection_kind = if name_str == "List" {
                    Some(CollectionCategory::List(CollectionCategory::list_defaults()))
                } else if name_str == "Bag" {
                    Some(CollectionCategory::Bag(CollectionCategory::bag_defaults()))
                } else if name_str == "Map" {
                    Some(CollectionCategory::Map(CollectionCategory::map_defaults()))
                } else {
                    None
                };
                types.push(LangType { name, native_type: None, collection_kind });
            }
        }

        if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok((types, refinement_types))
}

/// Parse a refinement type body: `{ var: BaseType | predicate }`
///
/// Called after `Name =` has been consumed. The `name` is the refinement
/// type's identifier (e.g., `PosInt`).
fn parse_refinement_type_body(input: ParseStream, name: Ident) -> SynResult<RefinementTypeDef> {
    let brace_content;
    syn::braced!(brace_content in input);

    // Parse: var : BaseType
    let var = brace_content.parse::<Ident>()?;
    brace_content.parse::<Token![:]>()?;
    let base_type = brace_content.parse::<crate::types::TypeExpr>()?;

    // Parse: | predicate
    brace_content.parse::<Token![|]>()?;
    let predicate_tokens = brace_content.parse::<TokenStream>()?;
    let predicate = parse_refinement_predicate_tokens(predicate_tokens)?;

    Ok(RefinementTypeDef { name, var, base_type, predicate })
}

// ── Refinement predicate parser (operator-precedence climbing) ──────────────
//
// Precedence (lowest to highest):
//   implies  =>
//   or       ||
//   and      &&
//   not      ~ / !
//   atom     variable, literal, relation, quantified, parenthesized, linear

#[derive(Clone, Copy)]
enum RefinementBinaryOperator {
    Implies,
    Or,
    And,
}

enum RefinementOperator {
    Binary(RefinementBinaryOperator),
    Not,
    Quantified {
        quantifier: Quantifier,
        var: Ident,
        domain: Option<Ident>,
        bound: Option<usize>,
    },
}

struct RefinementParseState {
    input: std::collections::VecDeque<proc_macro2::TokenTree>,
    operators: Vec<RefinementOperator>,
    values: Vec<RefinementPredicate>,
    expects_operand: bool,
}

impl RefinementParseState {
    fn new(tokens: TokenStream) -> Self {
        Self {
            input: tokens.into_iter().collect(),
            operators: Vec::new(),
            values: Vec::new(),
            expects_operand: true,
        }
    }

    fn push_operand(&mut self, value: RefinementPredicate) -> SynResult<()> {
        self.values.push(value);
        self.expects_operand = false;
        while matches!(
            self.operators.last(),
            Some(RefinementOperator::Not | RefinementOperator::Quantified { .. })
        ) {
            self.reduce_one()?;
        }
        Ok(())
    }

    fn push_binary(&mut self, operator: RefinementBinaryOperator) -> SynResult<()> {
        let precedence = refinement_precedence(operator);
        while matches!(
            self.operators.last(),
            Some(RefinementOperator::Binary(previous))
                if refinement_precedence(*previous) >= precedence
        ) {
            self.reduce_one()?;
        }
        self.operators.push(RefinementOperator::Binary(operator));
        self.expects_operand = true;
        Ok(())
    }

    fn reduce_one(&mut self) -> SynResult<()> {
        let operator = self.operators.pop().ok_or_else(|| {
            syn::Error::new(proc_macro2::Span::call_site(), "missing refinement operator")
        })?;
        match operator {
            RefinementOperator::Not => {
                let inner = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing operand after refinement negation",
                    )
                })?;
                self.values.push(RefinementPredicate::Not(Box::new(inner)));
            },
            RefinementOperator::Quantified { quantifier, var, domain, bound } => {
                let body = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        var.span(),
                        "missing body after quantified refinement predicate",
                    )
                })?;
                self.values.push(RefinementPredicate::Quantified {
                    quantifier,
                    var,
                    domain,
                    bound,
                    body: Box::new(body),
                });
            },
            RefinementOperator::Binary(operator) => {
                let right = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing right refinement operand",
                    )
                })?;
                let left = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing left refinement operand",
                    )
                })?;
                self.values.push(match operator {
                    RefinementBinaryOperator::Implies => {
                        RefinementPredicate::Implies(Box::new(left), Box::new(right))
                    },
                    RefinementBinaryOperator::Or => {
                        RefinementPredicate::Or(Box::new(left), Box::new(right))
                    },
                    RefinementBinaryOperator::And => {
                        RefinementPredicate::And(Box::new(left), Box::new(right))
                    },
                });
            },
        }
        Ok(())
    }

    fn finish(mut self) -> SynResult<RefinementPredicate> {
        if self.expects_operand {
            return Err(syn::Error::new(
                refinement_front_span(&self.input),
                "expected refinement predicate operand",
            ));
        }
        while !self.operators.is_empty() {
            self.reduce_one()?;
        }
        if self.values.len() != 1 {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "malformed refinement predicate",
            ));
        }
        Ok(self
            .values
            .pop()
            .expect("one refinement root remains after reduction"))
    }
}

fn refinement_precedence(operator: RefinementBinaryOperator) -> u8 {
    match operator {
        RefinementBinaryOperator::Implies => 1,
        RefinementBinaryOperator::Or => 2,
        RefinementBinaryOperator::And => 3,
    }
}

fn refinement_front_span(
    input: &std::collections::VecDeque<proc_macro2::TokenTree>,
) -> proc_macro2::Span {
    input
        .front()
        .map(proc_macro2::TokenTree::span)
        .unwrap_or_else(proc_macro2::Span::call_site)
}

fn refinement_punct(tree: Option<&proc_macro2::TokenTree>, expected: char) -> bool {
    matches!(tree, Some(proc_macro2::TokenTree::Punct(punct)) if punct.as_char() == expected)
}

fn refinement_underscore(tree: Option<&proc_macro2::TokenTree>) -> bool {
    matches!(tree, Some(proc_macro2::TokenTree::Ident(ident)) if ident == "_")
        || refinement_punct(tree, '_')
}

fn refinement_punct_pair(
    input: &std::collections::VecDeque<proc_macro2::TokenTree>,
    first: char,
    second: char,
    require_joint: bool,
) -> bool {
    let Some(proc_macro2::TokenTree::Punct(first_punct)) = input.front() else {
        return false;
    };
    if first_punct.as_char() != first
        || (require_joint && first_punct.spacing() != proc_macro2::Spacing::Joint)
    {
        return false;
    }
    refinement_punct(input.get(1), second)
}

fn refinement_take_punct(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
    expected: char,
    message: &str,
) -> SynResult<()> {
    match input.pop_front() {
        Some(proc_macro2::TokenTree::Punct(punct)) if punct.as_char() == expected => Ok(()),
        Some(tree) => Err(syn::Error::new(tree.span(), message)),
        None => Err(syn::Error::new(proc_macro2::Span::call_site(), message)),
    }
}

fn refinement_take_ident(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
    message: &str,
) -> SynResult<Ident> {
    match input.pop_front() {
        Some(proc_macro2::TokenTree::Ident(ident)) => Ok(ident),
        Some(tree) => Err(syn::Error::new(tree.span(), message)),
        None => Err(syn::Error::new(proc_macro2::Span::call_site(), message)),
    }
}

fn refinement_take_pair(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
    first: char,
    second: char,
) {
    debug_assert!(refinement_punct(input.front(), first));
    debug_assert!(refinement_punct(input.get(1), second));
    input.pop_front();
    input.pop_front();
}

fn refinement_parse_bound(group: proc_macro2::Group) -> SynResult<usize> {
    let mut input: std::collections::VecDeque<_> = group.stream().into_iter().collect();
    let key = refinement_take_ident(&mut input, "expected 'k' in refinement bound")?;
    if key != "k" {
        return Err(syn::Error::new(key.span(), "expected 'k'"));
    }
    refinement_take_punct(&mut input, '=', "expected '=' after 'k'")?;
    let literal = match input.pop_front() {
        Some(proc_macro2::TokenTree::Literal(literal)) => literal,
        Some(tree) => return Err(syn::Error::new(tree.span(), "expected integer bound")),
        None => return Err(syn::Error::new(group.span(), "expected integer bound")),
    };
    if let Some(tree) = input.front() {
        return Err(syn::Error::new(tree.span(), "unexpected token after refinement bound"));
    }
    syn::parse2::<syn::LitInt>(TokenStream::from(proc_macro2::TokenTree::Literal(literal)))?
        .base10_parse::<usize>()
}

fn refinement_pred_arg(ident: Ident) -> PredArg {
    if ident
        .to_string()
        .chars()
        .next()
        .unwrap_or('a')
        .is_uppercase()
    {
        PredArg::Constant(ident)
    } else {
        PredArg::Var(ident)
    }
}

fn refinement_parse_relation_args(group: proc_macro2::Group) -> SynResult<Vec<PredArg>> {
    let mut input: std::collections::VecDeque<_> = group.stream().into_iter().collect();
    let mut arguments = Vec::new();
    while !input.is_empty() {
        arguments.push(refinement_pred_arg(refinement_take_ident(
            &mut input,
            "expected relation argument",
        )?));
        if refinement_punct(input.front(), ',') {
            input.pop_front();
        }
    }
    Ok(arguments)
}

fn refinement_parse_linear_rhs_tokens(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<i64> {
    let negative = refinement_punct(input.front(), '-');
    if negative {
        input.pop_front();
    }
    let literal = match input.pop_front() {
        Some(proc_macro2::TokenTree::Literal(literal)) => literal,
        Some(tree) => return Err(syn::Error::new(tree.span(), "expected integer literal")),
        None => {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected integer literal",
            ));
        },
    };
    let value =
        syn::parse2::<syn::LitInt>(TokenStream::from(proc_macro2::TokenTree::Literal(literal)))?
            .base10_parse::<i64>()?;
    Ok(if negative { -value } else { value })
}

fn refinement_parse_leaf(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<RefinementPredicate> {
    let ident = refinement_take_ident(input, "expected refinement predicate identifier")?;
    if matches!(input.front(), Some(proc_macro2::TokenTree::Group(group)) if group.delimiter() == proc_macro2::Delimiter::Parenthesis)
    {
        let Some(proc_macro2::TokenTree::Group(group)) = input.pop_front() else {
            unreachable!("relation lookahead requires a parenthesis group")
        };
        let arguments = refinement_parse_relation_args(group)?;
        return Ok(RefinementPredicate::Relation {
            name: ident,
            args: arguments,
            negated: false,
        });
    }

    let linear_relation = if refinement_punct_pair(input, '>', '=', false) {
        refinement_take_pair(input, '>', '=');
        Some(LinearRelation::Ge)
    } else if refinement_punct(input.front(), '>') {
        input.pop_front();
        Some(LinearRelation::Gt)
    } else if refinement_punct_pair(input, '<', '=', false) {
        refinement_take_pair(input, '<', '=');
        Some(LinearRelation::Le)
    } else if refinement_punct(input.front(), '<') {
        input.pop_front();
        Some(LinearRelation::Lt)
    } else {
        None
    };
    if let Some(relation) = linear_relation {
        let rhs = refinement_parse_linear_rhs_tokens(input)?;
        return Ok(RefinementPredicate::Linear { terms: vec![(ident, 1)], relation, rhs });
    }

    let equality = if refinement_punct_pair(input, '=', '=', true) {
        refinement_take_pair(input, '=', '=');
        Some(true)
    } else if refinement_punct_pair(input, '!', '=', true) {
        refinement_take_pair(input, '!', '=');
        Some(false)
    } else {
        None
    };
    if let Some(is_equal) = equality {
        if matches!(input.front(), Some(proc_macro2::TokenTree::Literal(_)))
            || (refinement_punct(input.front(), '-')
                && matches!(input.get(1), Some(proc_macro2::TokenTree::Literal(_))))
        {
            let rhs = refinement_parse_linear_rhs_tokens(input)?;
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: if is_equal {
                    LinearRelation::Eq
                } else {
                    LinearRelation::Neq
                },
                rhs,
            });
        }
        let right = refinement_pred_arg(refinement_take_ident(
            input,
            "expected term after equality operator",
        )?);
        let left = refinement_pred_arg(ident);
        return Ok(if is_equal {
            RefinementPredicate::TermEq(left, right)
        } else {
            RefinementPredicate::TermNeq(left, right)
        });
    }

    Ok(RefinementPredicate::Relation {
        name: ident,
        args: Vec::new(),
        negated: false,
    })
}

fn refinement_parse_binary(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> Option<RefinementBinaryOperator> {
    let operator = if refinement_punct_pair(input, '=', '>', true) {
        RefinementBinaryOperator::Implies
    } else if refinement_punct_pair(input, '|', '|', true) {
        RefinementBinaryOperator::Or
    } else if refinement_punct_pair(input, '&', '&', true) {
        RefinementBinaryOperator::And
    } else {
        return None;
    };
    input.pop_front();
    input.pop_front();
    Some(operator)
}

fn refinement_parse_quantifier(
    state: &mut RefinementParseState,
    quantifier: Quantifier,
) -> SynResult<()> {
    let bound = if refinement_underscore(state.input.front()) {
        state.input.pop_front();
        let group = match state.input.pop_front() {
            Some(proc_macro2::TokenTree::Group(group))
                if group.delimiter() == proc_macro2::Delimiter::Brace =>
            {
                group
            },
            Some(tree) => return Err(syn::Error::new(tree.span(), "expected bound braces")),
            None => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "expected bound braces",
                ));
            },
        };
        Some(refinement_parse_bound(group)?)
    } else {
        None
    };
    let var = refinement_take_ident(&mut state.input, "expected quantified variable")?;
    let domain = match state.input.front() {
        Some(proc_macro2::TokenTree::Ident(keyword)) if keyword == "in" => {
            state.input.pop_front();
            Some(refinement_take_ident(
                &mut state.input,
                "expected quantifier domain after 'in'",
            )?)
        },
        _ => None,
    };
    refinement_take_punct(&mut state.input, '.', "expected '.' after refinement quantifier")?;
    state
        .operators
        .push(RefinementOperator::Quantified { quantifier, var, domain, bound });
    Ok(())
}

fn parse_refinement_predicate_tokens(tokens: TokenStream) -> SynResult<RefinementPredicate> {
    enum Task {
        Run(RefinementParseState),
        ResumeGroup(RefinementParseState),
    }

    let mut tasks = vec![Task::Run(RefinementParseState::new(tokens))];
    let mut completed = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::ResumeGroup(mut state) => {
                let expression = completed
                    .pop()
                    .expect("group parse precedes its continuation");
                state.push_operand(expression)?;
                tasks.push(Task::Run(state));
            },
            Task::Run(mut state) => loop {
                if state.expects_operand {
                    if refinement_punct(state.input.front(), '~')
                        || (refinement_punct(state.input.front(), '!')
                            && !refinement_punct_pair(&state.input, '!', '=', true))
                    {
                        if matches!(
                            state.operators.last(),
                            Some(RefinementOperator::Quantified { .. })
                        ) {
                            return Err(syn::Error::new(
                                refinement_front_span(&state.input),
                                "expected atomic quantified refinement body",
                            ));
                        }
                        state.input.pop_front();
                        state.operators.push(RefinementOperator::Not);
                        continue;
                    }

                    if let Some(proc_macro2::TokenTree::Group(group)) = state.input.front() {
                        if group.delimiter() != proc_macro2::Delimiter::Parenthesis {
                            return Err(syn::Error::new(
                                group.span(),
                                "expected parenthesized refinement predicate",
                            ));
                        }
                        let Some(proc_macro2::TokenTree::Group(group)) = state.input.pop_front()
                        else {
                            unreachable!("group lookahead and removal agree")
                        };
                        tasks.push(Task::ResumeGroup(state));
                        tasks.push(Task::Run(RefinementParseState::new(group.stream())));
                        break;
                    }

                    let keyword = match state.input.front() {
                        Some(proc_macro2::TokenTree::Ident(ident)) => Some(ident.to_string()),
                        _ => None,
                    };
                    match keyword.as_deref() {
                        Some("forall") | Some("exists") => {
                            state.input.pop_front();
                            refinement_parse_quantifier(
                                &mut state,
                                if keyword.as_deref() == Some("forall") {
                                    Quantifier::ForAll
                                } else {
                                    Quantifier::Exists
                                },
                            )?;
                        },
                        Some(_) => {
                            let leaf = refinement_parse_leaf(&mut state.input)?;
                            state.push_operand(leaf)?;
                        },
                        None => {
                            return Err(syn::Error::new(
                                refinement_front_span(&state.input),
                                "expected refinement predicate",
                            ));
                        },
                    }
                } else if state.input.is_empty() {
                    completed.push(state.finish()?);
                    break;
                } else if let Some(operator) = refinement_parse_binary(&mut state.input) {
                    state.push_binary(operator)?;
                } else {
                    return Err(syn::Error::new(
                        refinement_front_span(&state.input),
                        "expected refinement predicate operator",
                    ));
                }
            },
        }
    }
    debug_assert_eq!(completed.len(), 1);
    completed.pop().ok_or_else(|| {
        syn::Error::new(proc_macro2::Span::call_site(), "empty refinement predicate")
    })
}

/// Public wrapper for `parse_types` for use by `fragment.rs`.
pub fn parse_types_public(
    input: ParseStream,
) -> SynResult<(Vec<LangType>, Vec<RefinementTypeDef>)> {
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
        prev_was_backslash = matches!(&tt, proc_macro2::TokenTree::Punct(p) if p.as_char() == '\\');
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
        from_literals: false,
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

    Ok(ModeDef { name, token_defs, raw: false })
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

                constraints.push(SyncConstraint::Align { stream_a, stream_b, boundary_pattern });
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
                    format!("unknown sync constraint '{}'; expected 'align' or 'track'", kw),
                ));
            },
        }
    }

    Ok(constraints)
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
        let mut constraint_tokens = TokenStream::new();
        while !content.is_empty() && !content.peek(Token![;]) {
            constraint_tokens.extend(std::iter::once(content.parse::<proc_macro2::TokenTree>()?));
        }
        let constraint = parse_tree_constraint_tokens(constraint_tokens)?;
        let _ = content.parse::<Token![;]>()?;
        invariants.push(TreeInvariant { name, constraint });
    }

    Ok(invariants)
}

#[derive(Clone, Copy)]
enum TreeConstraintOperator {
    And,
    Or,
    Not,
}

struct TreeConstraintParseState {
    input: std::collections::VecDeque<proc_macro2::TokenTree>,
    operators: Vec<TreeConstraintOperator>,
    values: Vec<TreeConstraintExpr>,
    expects_operand: bool,
}

impl TreeConstraintParseState {
    fn new(tokens: TokenStream) -> Self {
        Self {
            input: tokens.into_iter().collect(),
            operators: Vec::new(),
            values: Vec::new(),
            expects_operand: true,
        }
    }

    fn push_operand(&mut self, value: TreeConstraintExpr) -> SynResult<()> {
        self.values.push(value);
        self.expects_operand = false;
        while matches!(self.operators.last(), Some(TreeConstraintOperator::Not)) {
            self.reduce_one()?;
        }
        Ok(())
    }

    fn push_binary(&mut self, operator: TreeConstraintOperator) {
        debug_assert!(matches!(operator, TreeConstraintOperator::And | TreeConstraintOperator::Or));
        // The historical grammar recursed on the entire right-hand expression,
        // so both operators have equal precedence and associate to the right.
        self.operators.push(operator);
        self.expects_operand = true;
    }

    fn reduce_one(&mut self) -> SynResult<()> {
        let operator = self.operators.pop().ok_or_else(|| {
            syn::Error::new(proc_macro2::Span::call_site(), "missing tree-constraint operator")
        })?;
        match operator {
            TreeConstraintOperator::Not => {
                let inner = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing tree-constraint negation operand",
                    )
                })?;
                self.values.push(TreeConstraintExpr::Not(Box::new(inner)));
            },
            TreeConstraintOperator::And | TreeConstraintOperator::Or => {
                let right = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing right tree-constraint operand",
                    )
                })?;
                let left = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing left tree-constraint operand",
                    )
                })?;
                self.values.push(match operator {
                    TreeConstraintOperator::And => {
                        TreeConstraintExpr::And(Box::new(left), Box::new(right))
                    },
                    TreeConstraintOperator::Or => {
                        TreeConstraintExpr::Or(Box::new(left), Box::new(right))
                    },
                    TreeConstraintOperator::Not => unreachable!(),
                });
            },
        }
        Ok(())
    }

    fn finish(mut self) -> SynResult<TreeConstraintExpr> {
        if self.expects_operand {
            return Err(syn::Error::new(
                refinement_front_span(&self.input),
                "expected tree constraint expression",
            ));
        }
        while !self.operators.is_empty() {
            self.reduce_one()?;
        }
        if self.values.len() != 1 {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "malformed tree constraint expression",
            ));
        }
        Ok(self
            .values
            .pop()
            .expect("one tree-constraint root remains after reduction"))
    }
}

fn tree_constraint_parse_match(group: proc_macro2::Group) -> SynResult<Vec<String>> {
    let mut input: std::collections::VecDeque<_> = group.stream().into_iter().collect();
    let mut symbols = Vec::new();
    while !input.is_empty() {
        symbols
            .push(refinement_take_ident(&mut input, "expected symbol in tree match")?.to_string());
        if refinement_punct(input.front(), '|') {
            input.pop_front();
        }
    }
    Ok(symbols)
}

fn tree_constraint_take_group(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
    delimiter: proc_macro2::Delimiter,
    message: &str,
) -> SynResult<proc_macro2::Group> {
    match input.pop_front() {
        Some(proc_macro2::TokenTree::Group(group)) if group.delimiter() == delimiter => Ok(group),
        Some(tree) => Err(syn::Error::new(tree.span(), message)),
        None => Err(syn::Error::new(proc_macro2::Span::call_site(), message)),
    }
}

fn tree_constraint_parse_forall_header(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<(String, proc_macro2::Group)> {
    let next = refinement_take_ident(input, "expected symbol after tree forall")?;
    let symbol = if next == "children" {
        let of = refinement_take_ident(input, "expected 'of' after 'children'")?;
        if of != "of" {
            return Err(syn::Error::new(of.span(), "expected 'of' after 'children'"));
        }
        refinement_take_ident(input, "expected symbol after 'children of'")?.to_string()
    } else if next == "↓" {
        refinement_take_ident(input, "expected symbol after '↓'")?.to_string()
    } else {
        next.to_string()
    };
    let body = tree_constraint_take_group(
        input,
        proc_macro2::Delimiter::Brace,
        "expected braced tree forall body",
    )?;
    Ok((symbol, body))
}

fn parse_tree_constraint_tokens(tokens: TokenStream) -> SynResult<TreeConstraintExpr> {
    enum Task {
        Run(TreeConstraintParseState),
        ResumeGroup(TreeConstraintParseState),
        ResumeForall {
            state: TreeConstraintParseState,
            symbol: String,
        },
    }

    let mut tasks = vec![Task::Run(TreeConstraintParseState::new(tokens))];
    let mut completed = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::ResumeGroup(mut state) => {
                let expression = completed
                    .pop()
                    .expect("group parse precedes its continuation");
                state.push_operand(expression)?;
                tasks.push(Task::Run(state));
            },
            Task::ResumeForall { mut state, symbol } => {
                let body = completed
                    .pop()
                    .expect("forall body parse precedes its continuation");
                state.push_operand(TreeConstraintExpr::ForallChildren {
                    symbol,
                    body: Box::new(body),
                })?;
                tasks.push(Task::Run(state));
            },
            Task::Run(mut state) => loop {
                if state.expects_operand {
                    if let Some(proc_macro2::TokenTree::Group(group)) = state.input.front() {
                        if group.delimiter() != proc_macro2::Delimiter::Parenthesis {
                            return Err(syn::Error::new(
                                group.span(),
                                "expected parenthesized tree constraint",
                            ));
                        }
                        let group = tree_constraint_take_group(
                            &mut state.input,
                            proc_macro2::Delimiter::Parenthesis,
                            "expected parenthesized tree constraint",
                        )?;
                        tasks.push(Task::ResumeGroup(state));
                        tasks.push(Task::Run(TreeConstraintParseState::new(group.stream())));
                        break;
                    }

                    let keyword = refinement_take_ident(
                        &mut state.input,
                        "expected tree constraint expression",
                    )?;
                    match keyword.to_string().as_str() {
                        "forall" | "∀" => {
                            let (symbol, body) =
                                tree_constraint_parse_forall_header(&mut state.input)?;
                            tasks.push(Task::ResumeForall { state, symbol });
                            tasks.push(Task::Run(TreeConstraintParseState::new(body.stream())));
                            break;
                        },
                        "exists" | "∃" => {
                            let child = refinement_take_ident(
                                &mut state.input,
                                "expected 'child' after 'exists'/'∃'",
                            )?;
                            if child != "child" {
                                return Err(syn::Error::new(
                                    child.span(),
                                    "expected 'child' after 'exists'/'∃'",
                                ));
                            }
                            state.push_operand(TreeConstraintExpr::ExistsChild)?;
                        },
                        "not" | "¬" => {
                            state.operators.push(TreeConstraintOperator::Not);
                        },
                        "match" | "∈" => {
                            let group = tree_constraint_take_group(
                                &mut state.input,
                                proc_macro2::Delimiter::Brace,
                                "expected braced tree match set",
                            )?;
                            state.push_operand(TreeConstraintExpr::Match(
                                tree_constraint_parse_match(group)?,
                            ))?;
                        },
                        _ => state.push_operand(TreeConstraintExpr::Atom(keyword.to_string()))?,
                    }
                } else if state.input.is_empty() {
                    completed.push(state.finish()?);
                    break;
                } else {
                    let operator = refinement_take_ident(
                        &mut state.input,
                        "expected tree constraint operator",
                    )?;
                    match operator.to_string().as_str() {
                        "and" | "∧" => state.push_binary(TreeConstraintOperator::And),
                        "or" | "∨" => state.push_binary(TreeConstraintOperator::Or),
                        _ => {
                            return Err(syn::Error::new(
                                operator.span(),
                                "expected 'and'/'∧' or 'or'/'∨'",
                            ));
                        },
                    }
                }
            },
        }
    }
    debug_assert_eq!(completed.len(), 1);
    completed.pop().ok_or_else(|| {
        syn::Error::new(proc_macro2::Span::call_site(), "empty tree constraint expression")
    })
}

/// Everything a `tokens { … }` block contributes to the language definition.
///
/// Named rather than returned as a bare 4-tuple. The block began as
/// `(token_defs, mode_defs)` and grew two more parallel vectors; at that width a
/// positional tuple stops documenting itself, and `let (_, _, _, x) = …` at a call
/// site says nothing about what `x` is. `Default` gives the two "no `tokens` block
/// present" fall-throughs one spelling instead of a four-element `Vec::new()` litany
/// that has to be kept the right length by hand. This is also the factoring
/// `clippy::type_complexity` asks for.
#[derive(Default)]
struct TokensBlock {
    token_defs: Vec<TokenDef>,
    mode_defs: Vec<ModeDef>,
    sync_constraints: Vec<SyncConstraint>,
    tree_invariants: Vec<TreeInvariant>,
}

/// Parse the `tokens { ... }` block.
///
/// Contains token definitions (default mode), named mode blocks,
/// optional `sync { ... }` block, and optional `tree_invariants { ... }` block.
fn parse_tokens(input: ParseStream) -> SynResult<TokensBlock> {
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
                "raw" => {
                    // L9-4: `raw mode name { … }` — a RAW guest mode (whitespace
                    // is GuestChunk content, not skipped between tokens).
                    let _ = content.parse::<Ident>()?; // consume "raw"
                    let peeked = content.fork().parse::<Ident>()?;
                    if peeked != "mode" {
                        return Err(syn::Error::new(
                            peeked.span(),
                            "expected 'mode' after 'raw' (raw guest mode: `raw mode NAME { … }`)",
                        ));
                    }
                    let mut md = parse_mode_def(&content)?;
                    md.raw = true;
                    mode_defs.push(md);
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
            return Err(
                content.error("expected token definition, 'mode', 'sync', or 'tree_invariants'")
            );
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(TokensBlock {
        token_defs,
        mode_defs,
        sync_constraints,
        tree_invariants: tree_invariants_vec,
    })
}

/// Public wrapper for `parse_tokens` for use by `fragment.rs`.
pub fn parse_tokens_public(input: ParseStream) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>)> {
    let TokensBlock { token_defs, mode_defs, .. } = parse_tokens(input)?;
    Ok((token_defs, mode_defs))
}

/// Parse the `literals { ... }` block and desugar each entry into a `TokenDef`.
///
/// Syntax (main-branch surface):
///
/// ```text
/// literals {
///     TypeName {
///         pattern: r"regex";
///         eval: ![ rust_expr ]
///     }
///     ...
/// }
/// ```
///
/// Each entry desugars to:
///
/// ```text
/// TokenDef {
///     name: TypeName,
///     pattern: <regex string>,
///     category: Some(TypeName),   // name auto-binds to category
///     rust_code: Some(<eval tokens>),
///     priority: None,             // default 2 at CustomTokenSpec level
///     push_mode: None, is_pop: false, stream: None,
/// }
/// ```
///
/// `TypeName` must be declared in `types { }` — enforced later during
/// semantic validation (parse-time only checks surface shape).
fn parse_literals(input: ParseStream) -> SynResult<Vec<TokenDef>> {
    let literals_ident = input.parse::<Ident>()?;
    if literals_ident != "literals" {
        return Err(syn::Error::new(literals_ident.span(), "expected 'literals'"));
    }
    let content;
    syn::braced!(content in input);

    let mut defs = Vec::new();
    while !content.is_empty() {
        let type_name = content.parse::<Ident>()?;
        let type_block;
        syn::braced!(type_block in content);

        // pattern: "..." or r"..."
        let pattern_kw = type_block.parse::<Ident>()?;
        if pattern_kw != "pattern" {
            return Err(syn::Error::new(pattern_kw.span(), "expected 'pattern'"));
        }
        let _ = type_block.parse::<Token![:]>()?;
        let pattern_lit: syn::LitStr = type_block.parse()?;
        let pattern = pattern_lit.value();
        let _ = type_block.parse::<Token![;]>()?;

        // eval: ![ ... ]
        let eval_kw = type_block.parse::<Ident>()?;
        if eval_kw != "eval" {
            return Err(syn::Error::new(eval_kw.span(), "expected 'eval'"));
        }
        let _ = type_block.parse::<Token![:]>()?;
        if !type_block.peek(Token![!]) || !type_block.peek2(syn::token::Bracket) {
            return Err(syn::Error::new(type_block.span(), "expected eval: ![ ... ]"));
        }
        let _ = type_block.parse::<Token![!]>()?;
        let eval_content;
        syn::bracketed!(eval_content in type_block);
        let eval: TokenStream = eval_content.parse()?;

        defs.push(TokenDef {
            name: type_name.clone(),
            pattern,
            category: Some(type_name),
            rust_code: Some(eval),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });

        if type_block.peek(Token![;]) {
            let _ = type_block.parse::<Token![;]>()?;
        }
    }

    // Optional trailing comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(defs)
}

// ══════════════════════════════════════════════════════════════════════════════
// Guard configuration parser — `guards { ... }` block (design doc §2A)
// ══════════════════════════════════════════════════════════════════════════════
//
// Architecture mirrors `parse_tokens`: direct items (built-in predicate
// declarations) coexist with named configuration sub-blocks (`connectives {}`,
// `theories {}`, `channels {}`).

/// Parse the `guards { ... }` block.
fn parse_guards(input: ParseStream) -> SynResult<GuardConfig> {
    let guards_ident = input.parse::<Ident>()?;
    if guards_ident != "guards" {
        return Err(syn::Error::new(guards_ident.span(), "expected 'guards'"));
    }

    let content;
    syn::braced!(content in input);

    let mut builtin_predicates: Vec<BuiltinPredicate> = Vec::new();
    let mut connectives: Option<Vec<ConnectiveDecl>> = None;
    let mut theories: Vec<TheoryRegistration> = Vec::new();
    let mut channels: Option<ChannelConfig> = None;
    let mut guard_slots: Vec<GuardSlotDecl> = Vec::new();
    let mut saw_explicit_predicates = false;

    while !content.is_empty() {
        if !content.peek(Ident) {
            return Err(content.error(
                "expected predicate declaration, 'connectives', 'theories', 'channels', or \
                 'guard_slots'",
            ));
        }

        let fork = content.fork();
        let kw = fork.parse::<Ident>()?;
        let kw_str = kw.to_string();

        match kw_str.as_str() {
            "connectives" => {
                if connectives.is_some() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `connectives {}` sub-block in guards",
                    ));
                }
                connectives = Some(parse_connectives_block(&content)?);
            },
            "theories" => {
                if !theories.is_empty() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `theories {}` sub-block in guards",
                    ));
                }
                theories = parse_theories_block(&content)?;
            },
            "channels" => {
                if channels.is_some() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `channels {}` sub-block in guards",
                    ));
                }
                channels = Some(parse_channels_block(&content)?);
            },
            "guard_slots" => {
                if !guard_slots.is_empty() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "duplicate `guard_slots {}` sub-block in guards",
                    ));
                }
                guard_slots = parse_guard_slots_block(&content)?;
            },
            _ => {
                // Direct item: builtin predicate declaration
                builtin_predicates.push(parse_builtin_predicate(&content)?);
                saw_explicit_predicates = true;
            },
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(GuardConfig {
        builtin_predicates: if saw_explicit_predicates {
            Some(builtin_predicates)
        } else {
            None
        },
        connectives,
        theories,
        channels,
        guard_slots,
    })
}

/// Parse the `guard_slots { <Label>(<param>); ... }` sub-block.
///
/// ```text
/// guards {
///     guard_slots {
///         ForRowWhere(cond);
///         ForRowSingleWhere(cond);
///     }
/// }
/// ```
///
/// Each entry declares that the named term parameter of the named `terms { }` rule is a
/// **semantic predicate**, so the Rho backend induces a `term:<Label>:guard:<param>` obligation
/// for it — the same obligation a `?param:Guard` slot induces.
///
/// This exists for a language whose guard sublanguage is its own expression language and whose
/// guard parameter therefore has an ordinary category type rather than `Guard`. It is a
/// DECLARATION: nothing here inspects the rule's syntax form, so no `"where"` literal and no
/// parameter name is load-bearing.
fn parse_guard_slots_block(input: ParseStream) -> SynResult<Vec<GuardSlotDecl>> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "guard_slots" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'guard_slots'"));
    }
    let content;
    syn::braced!(content in input);

    let mut decls = Vec::new();
    while !content.is_empty() {
        let label = content.parse::<Ident>()?;
        let inner;
        syn::parenthesized!(inner in content);
        let param = inner.parse::<Ident>()?;
        if !inner.is_empty() {
            return Err(inner.error("a guard-slot declaration names exactly one parameter"));
        }
        let _ = content.parse::<Token![;]>()?;
        decls.push(GuardSlotDecl { label, param });
    }
    Ok(decls)
}

/// Parse a single built-in predicate declaration:
///
/// ```text
/// Label . params |- syntax_form (| syntax_form)* @[anno1, anno2]? ;
/// ```
fn parse_builtin_predicate(input: ParseStream) -> SynResult<BuiltinPredicate> {
    // Predicate name (label)
    let name = input.parse::<Ident>()?;

    // `.` separator before params
    let _ = input.parse::<Token![.]>()?;

    // Parameter list (comma-separated)
    let params = parse_predicate_params(input)?;

    // `|-` (turnstile)
    let _ = input.parse::<Token![|]>()?;
    let _ = input.parse::<Token![-]>()?;

    // Syntax forms — at least one, alternatives separated by `|`
    let mut syntax_forms: Vec<Vec<crate::grammar::SyntaxExpr>> = Vec::new();
    syntax_forms.push(parse_predicate_syntax_form(input)?);
    while input.peek(Token![|]) {
        // Bare `|` separates alternative forms (the `|-` turnstile already
        // consumed; here `|` always introduces another alternative).
        let _ = input.parse::<Token![|]>()?;
        syntax_forms.push(parse_predicate_syntax_form(input)?);
    }

    // Optional `@[...]` annotations
    let annotations = if input.peek(Token![@]) {
        parse_annotations(input)?
    } else {
        PredicateAnnotations::default()
    };

    // Required `;` terminator
    let _ = input.parse::<Token![;]>()?;

    Ok(BuiltinPredicate { name, params, syntax_forms, annotations })
}

/// Parse the parameter list of a built-in predicate.
///
/// Each parameter has the form: `name (: Type)? (Quantifier)?`
/// where `Type` is a single ident or `(Ident|Ident|...)` union, and
/// `Quantifier` is `+`, `*`, `{m,n}`, `{m,}`, or `{,n}`.
fn parse_predicate_params(input: ParseStream) -> SynResult<Vec<PredicateParam>> {
    let mut params = Vec::new();

    // Allow empty parameter list (some predicates have no params)
    if input.peek(Token![|]) && input.peek2(Token![-]) {
        return Ok(params);
    }

    loop {
        let name = input.parse::<Ident>()?;

        // Optional type annotation
        let ty = if input.peek(Token![:]) {
            let _ = input.parse::<Token![:]>()?;
            Some(parse_predicate_param_type(input)?)
        } else {
            None
        };

        // Optional quantifier suffix
        let quantifier = parse_optional_param_quantifier(input)?;

        params.push(PredicateParam { name, ty, quantifier });

        // Continue if comma; otherwise stop
        if input.peek(Token![,]) {
            // Don't consume the comma if it's part of the next item
            // (e.g., `|-` is next). Look ahead.
            let fork = input.fork();
            let _ = fork.parse::<Token![,]>()?;
            if fork.peek(Ident) {
                let _ = input.parse::<Token![,]>()?;
            } else {
                break;
            }
        } else {
            break;
        }
    }

    Ok(params)
}

/// Parse a parameter type: `Ident` or `(Ident|Ident|...)`
fn parse_predicate_param_type(input: ParseStream) -> SynResult<ParamType> {
    if input.peek(syn::token::Paren) {
        let inner;
        syn::parenthesized!(inner in input);
        let mut types = vec![inner.parse::<Ident>()?];
        while inner.peek(Token![|]) {
            let _ = inner.parse::<Token![|]>()?;
            types.push(inner.parse::<Ident>()?);
        }
        Ok(ParamType::Union(types))
    } else {
        Ok(ParamType::Single(input.parse::<Ident>()?))
    }
}

/// Parse an optional repetition quantifier suffix: `+`, `*`, or `{m,n}`.
fn parse_optional_param_quantifier(input: ParseStream) -> SynResult<Option<ParamQuantifier>> {
    if input.peek(Token![+]) {
        let _ = input.parse::<Token![+]>()?;
        Ok(Some(ParamQuantifier::OneOrMore))
    } else if input.peek(Token![*]) {
        let _ = input.parse::<Token![*]>()?;
        Ok(Some(ParamQuantifier::ZeroOrMore))
    } else if input.peek(syn::token::Brace) {
        let inner;
        syn::braced!(inner in input);
        // Parse `m`, `,`, optional `n`
        let min = if inner.peek(syn::LitInt) {
            let lit = inner.parse::<syn::LitInt>()?;
            lit.base10_parse::<usize>()?
        } else {
            0
        };
        let _ = inner.parse::<Token![,]>()?;
        let max = if inner.peek(syn::LitInt) {
            let lit = inner.parse::<syn::LitInt>()?;
            Some(lit.base10_parse::<usize>()?)
        } else {
            None
        };
        Ok(Some(ParamQuantifier::Range { min, max }))
    } else {
        Ok(None)
    }
}

/// Parse a single syntax form for a built-in predicate. Stops at `|` (next
/// alternative form), `@` (annotations), or `;` (terminator).
fn parse_predicate_syntax_form(input: ParseStream) -> SynResult<Vec<crate::grammar::SyntaxExpr>> {
    let mut exprs = Vec::new();
    while !input.is_empty()
        && !input.peek(Token![;])
        && !input.peek(Token![@])
        && !input.peek(Token![|])
    {
        exprs.push(crate::grammar::parse_syntax_expr(input)?);
    }
    if exprs.is_empty() {
        return Err(input.error("expected at least one syntax expression in predicate form"));
    }
    Ok(exprs)
}

/// Parse `@[selectivity(s), cost(c)]` annotations.
fn parse_annotations(input: ParseStream) -> SynResult<PredicateAnnotations> {
    let _ = input.parse::<Token![@]>()?;
    let inner;
    syn::bracketed!(inner in input);

    let mut annotations = PredicateAnnotations::default();

    while !inner.is_empty() {
        let name_ident = inner.parse::<Ident>()?;
        let name = name_ident.to_string();
        let arg;
        syn::parenthesized!(arg in inner);

        match name.as_str() {
            "selectivity" => {
                let lit = arg.parse::<syn::LitFloat>()?;
                let value: f64 = lit.base10_parse()?;
                if !(0.0..=1.0).contains(&value) {
                    return Err(syn::Error::new(lit.span(), "selectivity must be in [0.0, 1.0]"));
                }
                annotations.selectivity = Some(value);
            },
            "cost" => {
                let lit = arg.parse::<syn::LitInt>()?;
                let value: u32 = lit.base10_parse()?;
                annotations.cost = Some(value);
            },
            other => {
                return Err(syn::Error::new(
                    name_ident.span(),
                    format!("unknown annotation `{}` (expected `selectivity` or `cost`)", other),
                ));
            },
        }

        if inner.peek(Token![,]) {
            let _ = inner.parse::<Token![,]>()?;
        }
    }

    Ok(annotations)
}

/// Parse the `connectives { role = "kw1" | "kw2" ; ... }` sub-block.
fn parse_connectives_block(input: ParseStream) -> SynResult<Vec<ConnectiveDecl>> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "connectives" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'connectives'"));
    }
    let content;
    syn::braced!(content in input);

    let mut decls = Vec::new();
    while !content.is_empty() {
        let role_ident = content.parse::<Ident>()?;
        let role = ConnectiveRole::from_ident(&role_ident.to_string()).ok_or_else(|| {
            syn::Error::new(
                role_ident.span(),
                format!(
                    "unknown connective role `{}` (expected one of: and, or, not, \
                     entails, implied_by, iff, forall, exists)",
                    role_ident
                ),
            )
        })?;

        let _ = content.parse::<Token![=]>()?;

        // Parse one or more "keyword" string literals separated by `|`
        let first_lit = content.parse::<syn::LitStr>()?;
        let mut keywords = vec![first_lit.value()];
        while content.peek(Token![|]) {
            let _ = content.parse::<Token![|]>()?;
            let lit = content.parse::<syn::LitStr>()?;
            keywords.push(lit.value());
        }

        let _ = content.parse::<Token![;]>()?;

        decls.push(ConnectiveDecl { role, keywords });
    }

    Ok(decls)
}

/// Parse the `theories { name = TheoryType for [Cat1, Cat2]; ... }` sub-block.
fn parse_theories_block(input: ParseStream) -> SynResult<Vec<TheoryRegistration>> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "theories" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'theories'"));
    }
    let content;
    syn::braced!(content in input);

    let mut regs = Vec::new();
    while !content.is_empty() {
        let name = content.parse::<Ident>()?;
        let _ = content.parse::<Token![=]>()?;
        let theory_type = content.parse::<Type>()?;

        // Optional `for [Cat1, Cat2, ...]`
        let handled_types = if content.peek(Token![for]) {
            let _ = content.parse::<Token![for]>()?;
            let inner;
            syn::bracketed!(inner in content);
            let mut cats = Vec::new();
            while !inner.is_empty() {
                cats.push(inner.parse::<Ident>()?);
                if inner.peek(Token![,]) {
                    let _ = inner.parse::<Token![,]>()?;
                }
            }
            Some(cats)
        } else {
            None
        };

        let _ = content.parse::<Token![;]>()?;

        regs.push(TheoryRegistration { name, theory_type, handled_types });
    }

    Ok(regs)
}

/// Parse the `channels { channel Cat; join Label(p: Cat, ...); ... }` sub-block.
fn parse_channels_block(input: ParseStream) -> SynResult<ChannelConfig> {
    let kw_ident = input.parse::<Ident>()?;
    if kw_ident != "channels" {
        return Err(syn::Error::new(kw_ident.span(), "expected 'channels'"));
    }
    let content;
    syn::braced!(content in input);

    let mut channel_categories: Vec<ChannelDecl> = Vec::new();
    let mut join_patterns: Vec<JoinPatternDecl> = Vec::new();

    while !content.is_empty() {
        let item_kw = content.parse::<Ident>()?;
        let item_str = item_kw.to_string();
        match item_str.as_str() {
            "channel" => {
                let category = content.parse::<Ident>()?;
                let _ = content.parse::<Token![;]>()?;
                channel_categories.push(ChannelDecl { category });
            },
            "join" => {
                let label = content.parse::<Ident>()?;
                let inner;
                syn::parenthesized!(inner in content);
                let mut channel_params: Vec<ChannelParam> = Vec::new();
                while !inner.is_empty() {
                    let param_name = inner.parse::<Ident>()?;
                    let _ = inner.parse::<Token![:]>()?;
                    let category = inner.parse::<Ident>()?;
                    channel_params.push(ChannelParam { param_name, category });
                    if inner.peek(Token![,]) {
                        let _ = inner.parse::<Token![,]>()?;
                    }
                }
                let _ = content.parse::<Token![;]>()?;
                join_patterns.push(JoinPatternDecl { label, channel_params });
            },
            other => {
                return Err(syn::Error::new(
                    item_kw.span(),
                    format!("unknown channels item `{}` (expected `channel` or `join`)", other),
                ));
            },
        }
    }

    Ok(ChannelConfig { channel_categories, join_patterns })
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
            "emit_tests" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_tests must be a boolean (true or false)",
                    ));
                },
            },
            // `parse_only: true` declares a language as a syntax-only test/demo
            // fixture with no reduction semantics — it is excluded from the
            // production LanguageDefInventory (the dovetail/ast inventory
            // invariant tests). Fail-closed: a real language is inventoried
            // unless it explicitly opts out here, and the inventory tests guard
            // that a parse_only language carries no equations/rewrites/logic.
            "parse_only" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "parse_only must be a boolean (true or false)",
                    ));
                },
            },
            "emit_blockly" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_blockly must be a boolean (true or false)",
                    ));
                },
            },
            "emit_simulator" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "emit_simulator must be a boolean (true or false)",
                    ));
                },
            },
            // `hosted_in: "tests/definitions/<lang>.rs"` declares that this
            // `language!` is TEST-HOSTED: the definition does not live in the
            // `languages` LIBRARY (`languages/src/`) but in a file under
            // `languages/tests/definitions/`, which consuming test binaries pull in
            // with `#[path = "definitions/<lang>.rs"] mod <lang>;`.
            //
            // The value is the path to THE FILE CONTAINING THIS `language!`
            // INVOCATION, relative to the `languages` package root (the directory
            // holding `languages/Cargo.toml`). Two facts are derived from it, so a
            // single key cannot get them inconsistent:
            //
            //   1. the generated test suite is emitted INLINE (an opt-in
            //      `<lang>_generated_tests!` wrapper) instead of being written to
            //      `languages/tests/gen_<lang>_*.rs`, whose
            //      `use mettail_languages::<lang>::*;` header cannot resolve once
            //      the definition has left the library; and
            //   2. the generated simulation CLI's prologue becomes
            //      `#[path = "../../<hosted_in>"] mod <lang>;` (relative to
            //      `languages/src/bin/`) instead of that same library `use`.
            //
            // ABSENT this key every emission path is bit-for-bit what it was
            // before the key existed, so library-hosted (production) languages are
            // untouched by construction rather than by review.
            "hosted_in" => match &value {
                AttributeValue::Str(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "hosted_in must be a string: the path of the file containing this \
                         `language!`, relative to the `languages` package root \
                         (e.g. \"tests/definitions/acdemo.rs\")",
                    ));
                },
            },
            // L11 (2026-04-28): case_insensitive triggers ASCII case-folding
            // in NFA construction. Non-ASCII case folding requires per-locale
            // tables (Turkish dotless i, German ß) and emits compile_error!
            // when the grammar references non-ASCII keywords with
            // case_insensitive: true.
            "case_insensitive" => match &value {
                AttributeValue::Bool(_) => {},
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "case_insensitive must be a boolean (true or false)",
                    ));
                },
            },
            // L11 (2026-04-28): unicode_normalization runs a pre-pass on
            // input bytes before lexing. Accepts NFC, NFD, NFKC, NFKD, or
            // 'none' (the default).
            "unicode_normalization" => match &value {
                AttributeValue::Keyword(kw) => match kw.as_str() {
                    "NFC" | "NFD" | "NFKC" | "NFKD" | "none" => {},
                    _ => {
                        return Err(syn::Error::new(
                            key_ident.span(),
                            format!(
                                "unicode_normalization: invalid keyword '{}'. \
                                 Use 'NFC', 'NFD', 'NFKC', 'NFKD', or 'none'",
                                kw
                            ),
                        ));
                    },
                },
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "unicode_normalization must be a keyword: 'NFC', 'NFD', 'NFKC', 'NFKD', or 'none'",
                    ));
                },
            },
            // PIECE 3: keyword reservation. `auto` reserves every
            // identifier-shaped literal terminal as a keyword (the "reserved
            // words" modeling, e.g. `Nil`/`true`/`Map` cannot also be a
            // variable named after the keyword); `none` retains full
            // ambiguity (Fortran-style languages with no reserved words,
            // where `IF`/`DO`/`THEN` may double as identifiers). Grammar-
            // derived: the reserved set is exactly the identifier-shaped
            // terminals — no per-language hardcoded list.
            "reserved_keywords" => match &value {
                AttributeValue::Keyword(kw) => match kw.as_str() {
                    "auto" | "none" => {},
                    _ => {
                        return Err(syn::Error::new(
                            key_ident.span(),
                            format!(
                                "reserved_keywords: invalid keyword '{}'. \
                                 Use 'auto' (reserve identifier-shaped keywords) \
                                 or 'none' (retain full ambiguity)",
                                kw
                            ),
                        ));
                    },
                },
                _ => {
                    return Err(syn::Error::new(
                        key_ident.span(),
                        "reserved_keywords must be a keyword: 'auto' or 'none'",
                    ));
                },
            },
            unknown => {
                return Err(syn::Error::new(
                    key_ident.span(),
                    format!(
                        "unknown option '{}'. Valid options are: beam_width, log_semiring_model_path, dispatch, emit_tests, emit_blockly, emit_simulator, hosted_in, case_insensitive, unicode_normalization, reserved_keywords, parse_only",
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
///   withheld   ::= ident "~/>" ident      -- ★ (#195) a DENIED congruence
///   relation   ::= ident "(" (ident ("," ident)*)? ")"
///   forall     ::= ident "." "*" "map" "(" "|" ident "|" premise ")"
fn parse_premise(input: ParseStream) -> SynResult<Premise> {
    let mut tokens = TokenStream::new();
    while !input.is_empty()
        && !input.peek(Token![,])
        && !(input.peek(Token![|]) && input.peek2(Token![-]))
    {
        tokens.extend(std::iter::once(input.parse::<proc_macro2::TokenTree>()?));
    }
    parse_premise_tokens(tokens)
}

fn parse_non_forall_premise(input: ParseStream) -> SynResult<Premise> {
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
    } else if input.peek(Token![~]) && input.peek2(Token![/]) {
        // ★ (#195) WITHHELD congruence: S ~/> T — the slash-negated rewrite arrow
        // (`↛`). Peeked BEFORE the plain `~>` arm: `~/>` and `~>` share the leading
        // `~`, and `peek2` distinguishes them on the second token, so the order of
        // these two arms is load-bearing and `~/>` must come first.
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![/]>()?;
        let _ = input.parse::<Token![>]>()?;
        let target = input.parse::<Ident>()?;
        Ok(Premise::CongruenceWithheld { source: first, target })
    } else if input.peek(Token![~]) && input.peek2(Token![>]) {
        // Congruence: S ~> T
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![>]>()?;
        let target = input.parse::<Ident>()?;
        Ok(Premise::Congruence { source: first, target })
    } else if first == "guard" && input.peek(syn::token::Paren) {
        // Behavioral guard premise: guard(pred_expr). This must precede the
        // generic relation-query arm because both start with `ident(...)`.
        let content;
        syn::parenthesized!(content in input);
        let pred = parse_behavioral_pred(&content)?;
        if !content.is_empty() {
            return Err(content.error("unexpected trailing tokens in behavioral guard"));
        }
        Ok(Premise::BehavioralGuard(pred))
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
    } else if first == "forall" || first == "exists" {
        // Quantified behavioral guard used directly as premise:
        // forall var in domain. body  /  exists var in domain. body
        let quantifier = if first == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let var = input.parse::<Ident>()?;

        // Optional bound: _{k=N}
        let bound = if input.peek(Token![_]) {
            let _ = input.parse::<Token![_]>()?;
            let bound_content;
            syn::braced!(bound_content in input);
            // Parse k=N inside braces
            let _k = bound_content.parse::<Ident>()?;
            let _ = bound_content.parse::<Token![=]>()?;
            let n: syn::LitInt = bound_content.parse()?;
            Some(n.base10_parse::<usize>()?)
        } else {
            None
        };

        // Optional domain: "in" relation_name
        let domain = if input.peek(Token![in]) {
            let _ = input.parse::<Token![in]>()?;
            Some(input.parse::<Ident>()?)
        } else {
            None
        };

        // "." separates quantifier header from body
        let _ = input.parse::<Token![.]>()?;
        let body = parse_behavioral_pred(input)?;

        Ok(Premise::BehavioralGuard(BehavioralPred::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        }))
    } else {
        Err(syn::Error::new(
            first.span(),
            "expected premise: 'x # term', 'S ~> T', 'rel(args)', 'guard(...)', \
             'forall ...', 'exists ...', or 'xs.*map(|x| ...)'",
        ))
    }
}

fn parse_premise_tokens(tokens: TokenStream) -> SynResult<Premise> {
    enum Parsed {
        Leaf(Premise),
        ForAll {
            collection: Ident,
            param: Ident,
            body: TokenStream,
        },
    }

    enum Task {
        Parse(TokenStream),
        AssembleForAll { collection: Ident, param: Ident },
    }

    fn punct(tree: &proc_macro2::TokenTree, expected: char) -> bool {
        matches!(tree, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == expected)
    }

    fn parse_one(tokens: TokenStream) -> SynResult<Parsed> {
        let trees: Vec<_> = tokens.clone().into_iter().collect();
        let starts_method_quantifier = trees.len() >= 2
            && matches!(&trees[0], proc_macro2::TokenTree::Ident(_))
            && punct(&trees[1], '.');
        if !starts_method_quantifier {
            return syn::parse::Parser::parse2(parse_non_forall_premise, tokens).map(Parsed::Leaf);
        }

        if trees.len() != 5 || !punct(&trees[2], '*') {
            return Err(syn::Error::new(
                trees[1].span(),
                "expected quantified premise `collection.*map(|param| premise)`",
            ));
        }
        let proc_macro2::TokenTree::Ident(collection) = &trees[0] else {
            unreachable!("the prefix check requires an identifier")
        };
        let proc_macro2::TokenTree::Ident(operator) = &trees[3] else {
            return Err(syn::Error::new(trees[3].span(), "expected `map` after `.*`"));
        };
        if operator != "map" {
            return Err(syn::Error::new(
                operator.span(),
                "expected 'map' in quantified premise (xs.*map(|x| ...))",
            ));
        }
        let proc_macro2::TokenTree::Group(group) = &trees[4] else {
            return Err(syn::Error::new(trees[4].span(), "expected parentheses after `map`"));
        };
        if group.delimiter() != proc_macro2::Delimiter::Parenthesis {
            return Err(syn::Error::new(group.span(), "expected parentheses after `map`"));
        }

        let closure: Vec<_> = group.stream().into_iter().collect();
        if closure.len() < 4 || !punct(&closure[0], '|') || !punct(&closure[2], '|') {
            return Err(syn::Error::new(
                group.span(),
                "expected quantified premise closure `|param| premise`",
            ));
        }
        let proc_macro2::TokenTree::Ident(param) = &closure[1] else {
            return Err(syn::Error::new(closure[1].span(), "expected closure parameter"));
        };
        let param = param.clone();
        let body: TokenStream = closure.into_iter().skip(3).collect();
        if body.is_empty() {
            return Err(syn::Error::new(group.span(), "expected premise after closure parameter"));
        }
        Ok(Parsed::ForAll {
            collection: collection.clone(),
            param,
            body,
        })
    }

    let mut tasks = vec![Task::Parse(tokens)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Parse(tokens) => match parse_one(tokens)? {
                Parsed::Leaf(premise) => values.push(premise),
                Parsed::ForAll { collection, param, body } => {
                    tasks.push(Task::AssembleForAll { collection, param });
                    tasks.push(Task::Parse(body));
                },
            },
            Task::AssembleForAll { collection, param } => {
                let body = values
                    .pop()
                    .expect("forall assembly follows its body parse");
                values.push(Premise::ForAll { collection, param, body: Box::new(body) });
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values.pop().expect("one root premise is always emitted"))
}

// ══════════════════════════════════════════════════════════════════════════════
// Behavioral predicate parser — sublanguage for quantified guards
// ══════════════════════════════════════════════════════════════════════════════
//
// The parser chain (`parse_behavioral_pred` → `parse_pred_implies` → ... →
// `parse_pred_atom`) recognizes a fixed set of Rust tokens by default
// (`&&`, `||`, `~`, `!`, `=>`, plus the `forall`/`exists` identifiers).
// When the language declares a `guards { connectives { } }` sub-block,
// those defaults are augmented (not replaced) by the declared keywords:
// the parser also accepts each declared keyword as the corresponding
// connective. The active map is held in a thread-local so the parser
// functions need no signature changes — proc-macro expansion is
// single-threaded per crate, so the thread-local is safe.

thread_local! {
    /// Active ConnectiveMap during parsing of a `language!` invocation.
    /// Populated at the start of `Parse for LanguageDef` after `guards {}`
    /// is parsed; cleared on exit. Default `None` means: use only the
    /// hardcoded Rust-token connectives.
    static ACTIVE_CONNECTIVE_MAP: std::cell::RefCell<Option<ConnectiveMap>> =
        const { std::cell::RefCell::new(None) };
}

/// RAII guard that installs a `ConnectiveMap` into `ACTIVE_CONNECTIVE_MAP`
/// for the lifetime of the guard, restoring the previous value on drop.
///
/// This is used by `Parse for LanguageDef` to scope the active map to the
/// remainder of the parse after `guards {}` has been processed. Drop order
/// guarantees the previous value is restored even on early return / parse
/// errors / panics.
pub(crate) struct ConnectiveMapGuard {
    previous: Option<ConnectiveMap>,
}

impl ConnectiveMapGuard {
    /// Install `map` into the thread-local; the previous value is saved
    /// in the returned guard and restored on drop.
    pub(crate) fn install(map: Option<ConnectiveMap>) -> Self {
        let previous = ACTIVE_CONNECTIVE_MAP.with(|cell| cell.borrow_mut().take());
        ACTIVE_CONNECTIVE_MAP.with(|cell| {
            *cell.borrow_mut() = map;
        });
        ConnectiveMapGuard { previous }
    }
}

impl Drop for ConnectiveMapGuard {
    fn drop(&mut self) {
        ACTIVE_CONNECTIVE_MAP.with(|cell| {
            *cell.borrow_mut() = self.previous.take();
        });
    }
}

/// Look up the role of a connective keyword in the active map. Returns
/// `None` if no map is active or the keyword is not declared.
pub(crate) fn active_role_of(keyword: &str) -> Option<ConnectiveRole> {
    ACTIVE_CONNECTIVE_MAP.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|map| map.role_of(keyword).cloned())
    })
}

/// Whether the active map declares any keyword for the given role.
pub(crate) fn active_role_available(role: &ConnectiveRole) -> bool {
    ACTIVE_CONNECTIVE_MAP.with(|cell| {
        cell.borrow()
            .as_ref()
            .map(|map| map.role_available(role))
            .unwrap_or(false)
    })
}

/// Whether the active map exists (i.e., a `connectives {}` block was declared).
pub(crate) fn has_active_connective_map() -> bool {
    ACTIVE_CONNECTIVE_MAP.with(|cell| cell.borrow().is_some())
}

/// Whether a hardcoded Rust connective token (e.g., `&&`, `||`, `~`) is
/// allowed by the active `ConnectiveMap`.
///
/// Backward compatibility (no map active): always allowed. With an
/// active map: only allowed if the role is also declared in the map.
/// This implements the closed-world semantics described in design doc
/// §2A "Connective Parser Integration".
///
/// Layer D cleanup: when a language declares `connectives { and = "&&"; }`
/// but omits `or`, the `||` Rust token is rejected with CONN02 even though
/// `||` is "obviously" disjunction in Rust syntax. The grammar author opted
/// out of disjunction in their guard sublanguage; the parser respects that.
pub(crate) fn rust_token_allowed(role: ConnectiveRole) -> bool {
    if !has_active_connective_map() {
        return true;
    }
    active_role_available(&role)
}

/// Parse a behavioral predicate expression (implication level).
///
/// Grammar (precedence low→high):
/// ```text
/// pred_implies  ::= pred_or ("=>" pred_implies)?
/// pred_or       ::= pred_and ("||" pred_and)*
/// pred_and      ::= pred_not ("&&" pred_not)*
/// pred_not      ::= "~" pred_atom | "!" pred_atom | pred_atom
/// pred_atom     ::= quantified | relation_query | "(" pred_implies ")"
/// quantified    ::= ("forall" | "exists") ident [bound] ["in" ident] "." pred_implies
/// bound         ::= "_{" ident "=" lit_int "}"
/// relation_query::= ident "(" (pred_arg ("," pred_arg)*)? ")"
/// pred_arg      ::= ident
/// ```
///
/// Default mode (no `connectives { }` block): `&&` for conjunction, `||`
/// for disjunction, `~`/`!` for negation, `=>` for implication. All valid
/// Rust tokens parseable by proc_macro2.
///
/// Closed-world mode (`connectives { }` declared): the active map's
/// declared keywords are recognized in addition to whichever Rust tokens
/// happen to correspond to declared roles. If the parse leaves a
/// hardcoded Rust connective token unconsumed, CONN02 fires — the user
/// opted out of that role and trying to use the Rust spelling is an error.
fn parse_behavioral_pred(input: ParseStream) -> SynResult<BehavioralPred> {
    let tokens = input.parse::<TokenStream>()?;
    parse_behavioral_predicate_tokens(tokens)
}

#[derive(Clone, Copy)]
enum BehavioralBinaryOperator {
    Entails,
    ImpliedBy,
    Iff,
    Or,
    And,
}

enum BehavioralOperator {
    Binary(BehavioralBinaryOperator),
    Not,
    Quantified {
        quantifier: Quantifier,
        var: Ident,
        domain: Option<Ident>,
        bound: Option<usize>,
    },
}

struct BehavioralParseState {
    input: std::collections::VecDeque<proc_macro2::TokenTree>,
    operators: Vec<BehavioralOperator>,
    values: Vec<BehavioralPred>,
    expects_operand: bool,
}

impl BehavioralParseState {
    fn new(tokens: TokenStream) -> Self {
        Self {
            input: tokens.into_iter().collect(),
            operators: Vec::new(),
            values: Vec::new(),
            expects_operand: true,
        }
    }

    fn push_operand(&mut self, value: BehavioralPred) -> SynResult<()> {
        self.values.push(value);
        self.expects_operand = false;
        if matches!(self.operators.last(), Some(BehavioralOperator::Not)) {
            self.reduce_one()?;
        }
        Ok(())
    }

    fn push_binary(&mut self, operator: BehavioralBinaryOperator) -> SynResult<()> {
        let precedence = behavioral_precedence(operator);
        let left_associative =
            matches!(operator, BehavioralBinaryOperator::Or | BehavioralBinaryOperator::And);
        while matches!(
            self.operators.last(),
            Some(BehavioralOperator::Binary(previous))
                if behavioral_precedence(*previous) > precedence
                    || (left_associative && behavioral_precedence(*previous) == precedence)
        ) {
            self.reduce_one()?;
        }
        self.operators.push(BehavioralOperator::Binary(operator));
        self.expects_operand = true;
        Ok(())
    }

    fn reduce_one(&mut self) -> SynResult<()> {
        let operator = self.operators.pop().ok_or_else(|| {
            syn::Error::new(proc_macro2::Span::call_site(), "missing behavioral operator")
        })?;
        match operator {
            BehavioralOperator::Not => {
                let inner = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing behavioral negation operand",
                    )
                })?;
                self.values.push(BehavioralPred::Not(Box::new(inner)));
            },
            BehavioralOperator::Quantified { quantifier, var, domain, bound } => {
                let body = self.values.pop().ok_or_else(|| {
                    syn::Error::new(var.span(), "missing quantified behavioral body")
                })?;
                self.values.push(BehavioralPred::Quantified {
                    quantifier,
                    var,
                    domain,
                    bound,
                    body: Box::new(body),
                });
            },
            BehavioralOperator::Binary(operator) => {
                let right = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing right behavioral operand",
                    )
                })?;
                let left = self.values.pop().ok_or_else(|| {
                    syn::Error::new(
                        proc_macro2::Span::call_site(),
                        "missing left behavioral operand",
                    )
                })?;
                self.values.push(match operator {
                    BehavioralBinaryOperator::Entails => {
                        BehavioralPred::Implies(Box::new(left), Box::new(right))
                    },
                    BehavioralBinaryOperator::ImpliedBy => {
                        BehavioralPred::Implies(Box::new(right), Box::new(left))
                    },
                    BehavioralBinaryOperator::Iff => {
                        let forward = BehavioralPred::Implies(
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        );
                        let backward = BehavioralPred::Implies(Box::new(right), Box::new(left));
                        BehavioralPred::And(Box::new(forward), Box::new(backward))
                    },
                    BehavioralBinaryOperator::Or => {
                        BehavioralPred::Or(Box::new(left), Box::new(right))
                    },
                    BehavioralBinaryOperator::And => {
                        BehavioralPred::And(Box::new(left), Box::new(right))
                    },
                });
            },
        }
        Ok(())
    }

    fn finish(mut self) -> SynResult<BehavioralPred> {
        if self.expects_operand {
            return Err(syn::Error::new(
                refinement_front_span(&self.input),
                "expected behavioral predicate operand",
            ));
        }
        while !self.operators.is_empty() {
            self.reduce_one()?;
        }
        if self.values.len() != 1 {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "malformed behavioral predicate",
            ));
        }
        Ok(self
            .values
            .pop()
            .expect("one behavioral root remains after reduction"))
    }
}

fn behavioral_precedence(operator: BehavioralBinaryOperator) -> u8 {
    match operator {
        BehavioralBinaryOperator::Entails
        | BehavioralBinaryOperator::ImpliedBy
        | BehavioralBinaryOperator::Iff => 1,
        BehavioralBinaryOperator::Or => 2,
        BehavioralBinaryOperator::And => 3,
    }
}

fn behavioral_conn02(role: ConnectiveRole, span: proc_macro2::Span) -> syn::Error {
    let token = match role {
        ConnectiveRole::And => "&&",
        ConnectiveRole::Or => "||",
        ConnectiveRole::Not => "~",
        ConnectiveRole::Entails => "=>",
        _ => "connective",
    };
    let role_name = match role {
        ConnectiveRole::And => "and",
        ConnectiveRole::Or => "or",
        ConnectiveRole::Not => "not",
        ConnectiveRole::Entails => "entails",
        _ => "unknown",
    };
    syn::Error::new(
        span,
        format!(
            "CONN02: connective token `{token}` (role `{role_name}`) is not declared in the active `connectives {{}}` block"
        ),
    )
}

fn behavioral_parse_bound(group: proc_macro2::Group) -> SynResult<usize> {
    let mut input: std::collections::VecDeque<_> = group.stream().into_iter().collect();
    let _key = refinement_take_ident(&mut input, "expected bound key")?;
    refinement_take_punct(&mut input, '=', "expected '=' after bound key")?;
    let literal = match input.pop_front() {
        Some(proc_macro2::TokenTree::Literal(literal)) => literal,
        Some(tree) => return Err(syn::Error::new(tree.span(), "expected integer bound")),
        None => return Err(syn::Error::new(group.span(), "expected integer bound")),
    };
    if let Some(tree) = input.front() {
        return Err(syn::Error::new(tree.span(), "unexpected token after behavioral bound"));
    }
    syn::parse2::<syn::LitInt>(TokenStream::from(proc_macro2::TokenTree::Literal(literal)))?
        .base10_parse::<usize>()
}

fn behavioral_parse_quantifier(
    state: &mut BehavioralParseState,
    quantifier: Quantifier,
) -> SynResult<()> {
    let var = refinement_take_ident(&mut state.input, "expected quantified variable")?;
    let bound = if refinement_underscore(state.input.front()) {
        state.input.pop_front();
        let group = match state.input.pop_front() {
            Some(proc_macro2::TokenTree::Group(group))
                if group.delimiter() == proc_macro2::Delimiter::Brace =>
            {
                group
            },
            Some(tree) => return Err(syn::Error::new(tree.span(), "expected bound braces")),
            None => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "expected bound braces",
                ));
            },
        };
        Some(behavioral_parse_bound(group)?)
    } else {
        None
    };
    let domain = match state.input.front() {
        Some(proc_macro2::TokenTree::Ident(keyword)) if keyword == "in" => {
            state.input.pop_front();
            Some(refinement_take_ident(
                &mut state.input,
                "expected quantifier domain after 'in'",
            )?)
        },
        _ => None,
    };
    refinement_take_punct(&mut state.input, '.', "expected '.' after behavioral quantifier")?;
    state
        .operators
        .push(BehavioralOperator::Quantified { quantifier, var, domain, bound });
    Ok(())
}

fn behavioral_parse_ac_match(group: proc_macro2::Group) -> SynResult<BehavioralPred> {
    let mut input: std::collections::VecDeque<_> = group.stream().into_iter().collect();
    let bag = refinement_take_ident(&mut input, "expected AC-match bag variable")?;
    refinement_take_punct(&mut input, ',', "expected ',' after AC-match bag")?;
    let set = match input.pop_front() {
        Some(proc_macro2::TokenTree::Group(group))
            if group.delimiter() == proc_macro2::Delimiter::Brace =>
        {
            group
        },
        Some(tree) => return Err(syn::Error::new(tree.span(), "expected AC-match element set")),
        None => {
            return Err(syn::Error::new(group.span(), "expected AC-match element set"));
        },
    };
    if let Some(tree) = input.front() {
        return Err(syn::Error::new(tree.span(), "unexpected token after AC-match set"));
    }
    let mut set_input: std::collections::VecDeque<_> = set.stream().into_iter().collect();
    let mut elements = Vec::new();
    let mut rest = None;
    while !set_input.is_empty() {
        let ellipsis = refinement_punct(set_input.front(), '.')
            && refinement_punct(set_input.get(1), '.')
            && refinement_punct(set_input.get(2), '.');
        if ellipsis {
            set_input.pop_front();
            set_input.pop_front();
            set_input.pop_front();
            rest = Some(refinement_take_ident(&mut set_input, "expected AC-match rest variable")?);
            if refinement_punct(set_input.front(), ',') {
                set_input.pop_front();
            }
            if let Some(tree) = set_input.front() {
                return Err(syn::Error::new(tree.span(), "unexpected token after AC-match rest"));
            }
            break;
        }
        elements.push(refinement_take_ident(&mut set_input, "expected AC-match element variable")?);
        if refinement_punct(set_input.front(), ',') {
            set_input.pop_front();
        }
    }
    if elements.is_empty() {
        return Err(syn::Error::new(
            group.span(),
            "ac_match requires at least one element variable",
        ));
    }
    Ok(BehavioralPred::AcMatch { bag, elements, rest })
}

fn behavioral_parse_leaf(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<BehavioralPred> {
    let ident = refinement_take_ident(input, "expected behavioral predicate identifier")?;
    if ident == "ac_match" {
        let group = match input.pop_front() {
            Some(proc_macro2::TokenTree::Group(group))
                if group.delimiter() == proc_macro2::Delimiter::Parenthesis =>
            {
                group
            },
            Some(tree) => return Err(syn::Error::new(tree.span(), "expected AC-match arguments")),
            None => return Err(syn::Error::new(ident.span(), "expected AC-match arguments")),
        };
        return behavioral_parse_ac_match(group);
    }
    if matches!(input.front(), Some(proc_macro2::TokenTree::Group(group)) if group.delimiter() == proc_macro2::Delimiter::Parenthesis)
    {
        let Some(proc_macro2::TokenTree::Group(group)) = input.pop_front() else {
            unreachable!("relation lookahead requires a parenthesis group")
        };
        return Ok(BehavioralPred::RelationQuery {
            relation_name: ident,
            args: refinement_parse_relation_args(group)?,
            negated: false,
        });
    }
    Ok(BehavioralPred::RelationQuery {
        relation_name: ident,
        args: Vec::new(),
        negated: false,
    })
}

fn behavioral_keyword_role(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> Option<ConnectiveRole> {
    let Some(proc_macro2::TokenTree::Ident(keyword)) = input.front() else {
        return None;
    };
    let role = active_role_of(&keyword.to_string())?;
    input.pop_front();
    Some(role)
}

fn behavioral_parse_binary(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<Option<BehavioralBinaryOperator>> {
    let hardcoded = if refinement_punct_pair(input, '=', '>', true) {
        Some((ConnectiveRole::Entails, BehavioralBinaryOperator::Entails))
    } else if refinement_punct_pair(input, '|', '|', true) {
        Some((ConnectiveRole::Or, BehavioralBinaryOperator::Or))
    } else if refinement_punct_pair(input, '&', '&', true) {
        Some((ConnectiveRole::And, BehavioralBinaryOperator::And))
    } else {
        None
    };
    if let Some((role, operator)) = hardcoded {
        if !rust_token_allowed(role.clone()) {
            return Err(behavioral_conn02(role, refinement_front_span(input)));
        }
        input.pop_front();
        input.pop_front();
        return Ok(Some(operator));
    }
    Ok(match behavioral_keyword_role(input) {
        Some(ConnectiveRole::Entails) => Some(BehavioralBinaryOperator::Entails),
        Some(ConnectiveRole::ImpliedBy) => Some(BehavioralBinaryOperator::ImpliedBy),
        Some(ConnectiveRole::Iff) => Some(BehavioralBinaryOperator::Iff),
        Some(ConnectiveRole::Or) => Some(BehavioralBinaryOperator::Or),
        Some(ConnectiveRole::And) => Some(BehavioralBinaryOperator::And),
        Some(role) => {
            return Err(syn::Error::new(
                refinement_front_span(input),
                format!("connective role {role:?} is not binary"),
            ));
        },
        None => None,
    })
}

fn parse_behavioral_predicate_tokens(tokens: TokenStream) -> SynResult<BehavioralPred> {
    enum Task {
        Run(BehavioralParseState),
        ResumeGroup(BehavioralParseState),
    }

    let mut tasks = vec![Task::Run(BehavioralParseState::new(tokens))];
    let mut completed = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::ResumeGroup(mut state) => {
                let expression = completed
                    .pop()
                    .expect("group parse precedes its continuation");
                state.push_operand(expression)?;
                tasks.push(Task::Run(state));
            },
            Task::Run(mut state) => loop {
                if state.expects_operand {
                    let hardcoded_not = refinement_punct(state.input.front(), '~')
                        || refinement_punct(state.input.front(), '!');
                    if hardcoded_not {
                        if !rust_token_allowed(ConnectiveRole::Not) {
                            return Err(behavioral_conn02(
                                ConnectiveRole::Not,
                                refinement_front_span(&state.input),
                            ));
                        }
                        if matches!(state.operators.last(), Some(BehavioralOperator::Not)) {
                            return Err(syn::Error::new(
                                refinement_front_span(&state.input),
                                "expected atomic predicate after negation",
                            ));
                        }
                        state.input.pop_front();
                        state.operators.push(BehavioralOperator::Not);
                        continue;
                    }

                    if let Some(proc_macro2::TokenTree::Ident(keyword)) = state.input.front() {
                        if let Some(ConnectiveRole::Not) = active_role_of(&keyword.to_string()) {
                            if matches!(state.operators.last(), Some(BehavioralOperator::Not)) {
                                return Err(syn::Error::new(
                                    keyword.span(),
                                    "expected atomic predicate after negation",
                                ));
                            }
                            state.input.pop_front();
                            state.operators.push(BehavioralOperator::Not);
                            continue;
                        }
                    }

                    if let Some(proc_macro2::TokenTree::Group(group)) = state.input.front() {
                        if group.delimiter() != proc_macro2::Delimiter::Parenthesis {
                            return Err(syn::Error::new(
                                group.span(),
                                "expected parenthesized behavioral predicate",
                            ));
                        }
                        let Some(proc_macro2::TokenTree::Group(group)) = state.input.pop_front()
                        else {
                            unreachable!("group lookahead and removal agree")
                        };
                        tasks.push(Task::ResumeGroup(state));
                        tasks.push(Task::Run(BehavioralParseState::new(group.stream())));
                        break;
                    }

                    let keyword = match state.input.front() {
                        Some(proc_macro2::TokenTree::Ident(ident)) => Some(ident.to_string()),
                        _ => None,
                    };
                    match keyword.as_deref() {
                        Some("forall") | Some("exists") => {
                            state.input.pop_front();
                            behavioral_parse_quantifier(
                                &mut state,
                                if keyword.as_deref() == Some("forall") {
                                    Quantifier::ForAll
                                } else {
                                    Quantifier::Exists
                                },
                            )?;
                        },
                        Some(_) => {
                            let leaf = behavioral_parse_leaf(&mut state.input)?;
                            state.push_operand(leaf)?;
                        },
                        None => {
                            return Err(syn::Error::new(
                                refinement_front_span(&state.input),
                                "expected behavioral predicate",
                            ));
                        },
                    }
                } else if state.input.is_empty() {
                    completed.push(state.finish()?);
                    break;
                } else if let Some(operator) = behavioral_parse_binary(&mut state.input)? {
                    state.push_binary(operator)?;
                } else {
                    return Err(syn::Error::new(
                        refinement_front_span(&state.input),
                        "expected behavioral predicate operator",
                    ));
                }
            },
        }
    }
    debug_assert_eq!(completed.len(), 1);
    completed.pop().ok_or_else(|| {
        syn::Error::new(proc_macro2::Span::call_site(), "empty behavioral predicate")
    })
}

/// Parse a typed parameter: name:Type
fn parse_typed_param(input: ParseStream) -> SynResult<TypedParam> {
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![:]>()?;
    let ty = input.parse::<crate::types::TypeExpr>()?;
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
    parse_pattern_tokens(take_one_pattern_from_parse_stream(input)?)
}

fn pattern_punct(tree: &proc_macro2::TokenTree, expected: char) -> bool {
    matches!(tree, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == expected)
}

fn take_one_pattern_from_parse_stream(input: ParseStream) -> SynResult<TokenStream> {
    fn take_tree(
        input: ParseStream,
        output: &mut TokenStream,
    ) -> SynResult<proc_macro2::TokenTree> {
        let tree = input.parse::<proc_macro2::TokenTree>()?;
        output.extend(std::iter::once(tree.clone()));
        Ok(tree)
    }

    let mut output = TokenStream::new();
    while input.peek(Token![^]) {
        let _ = take_tree(input, &mut output)?;
        if input.peek(Ident) || input.peek(syn::token::Bracket) {
            let _ = take_tree(input, &mut output)?;
        } else {
            return Err(input.error("expected lambda binder"));
        }
        let dot = take_tree(input, &mut output)?;
        if !pattern_punct(&dot, '.') {
            return Err(syn::Error::new(dot.span(), "expected `.` after lambda binder"));
        }
    }

    let first = take_tree(input, &mut output)?;
    let chainable = match &first {
        proc_macro2::TokenTree::Group(group)
            if matches!(
                group.delimiter(),
                proc_macro2::Delimiter::Parenthesis | proc_macro2::Delimiter::Brace
            ) =>
        {
            false
        },
        proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '*' => {
            let operator = take_tree(input, &mut output)?;
            let proc_macro2::TokenTree::Ident(operator) = operator else {
                return Err(syn::Error::new(operator.span(), "expected metasyntax operator"));
            };
            let arguments = take_tree(input, &mut output)?;
            if !matches!(
                arguments,
                proc_macro2::TokenTree::Group(ref group)
                    if group.delimiter() == proc_macro2::Delimiter::Parenthesis
            ) {
                return Err(syn::Error::new(arguments.span(), "expected metasyntax arguments"));
            }
            operator == "zip"
        },
        proc_macro2::TokenTree::Ident(_) => {
            if input.peek(syn::token::Bracket) {
                let _ = take_tree(input, &mut output)?;
                false
            } else {
                true
            }
        },
        _ => return Err(syn::Error::new(first.span(), "expected pattern")),
    };

    if chainable {
        while input.peek(Token![.]) && input.peek2(Token![*]) {
            let _ = take_tree(input, &mut output)?;
            let _ = take_tree(input, &mut output)?;
            let operator = take_tree(input, &mut output)?;
            if !matches!(operator, proc_macro2::TokenTree::Ident(_)) {
                return Err(syn::Error::new(operator.span(), "expected chained operator"));
            }
            let arguments = take_tree(input, &mut output)?;
            if !matches!(
                arguments,
                proc_macro2::TokenTree::Group(ref group)
                    if group.delimiter() == proc_macro2::Delimiter::Parenthesis
            ) {
                return Err(syn::Error::new(arguments.span(), "expected chained arguments"));
            }
        }
    }

    Ok(output)
}

fn take_pattern_tree(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
    output: &mut TokenStream,
    expected: &str,
) -> SynResult<proc_macro2::TokenTree> {
    let tree = input.pop_front().ok_or_else(|| {
        syn::Error::new(proc_macro2::Span::call_site(), format!("expected {expected}"))
    })?;
    output.extend(std::iter::once(tree.clone()));
    Ok(tree)
}

/// Remove exactly one pattern's top-level token trees from `input`.
/// Delimited children stay opaque here; the PDA schedules their contents later.
fn take_one_pattern_tokens(
    input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
) -> SynResult<TokenStream> {
    let mut output = TokenStream::new();

    // Lambda prefixes are right-nested but flat at this token-tree level.
    while input.front().is_some_and(|tree| pattern_punct(tree, '^')) {
        let _ = take_pattern_tree(input, &mut output, "`^`")?;
        match input.front() {
            Some(proc_macro2::TokenTree::Ident(_)) => {
                let _ = take_pattern_tree(input, &mut output, "lambda binder")?;
            },
            Some(proc_macro2::TokenTree::Group(group))
                if group.delimiter() == proc_macro2::Delimiter::Bracket =>
            {
                let _ = take_pattern_tree(input, &mut output, "multi-lambda binders")?;
            },
            Some(tree) => return Err(syn::Error::new(tree.span(), "expected lambda binder")),
            None => {
                return Err(syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "expected lambda binder",
                ))
            },
        }
        let dot = take_pattern_tree(input, &mut output, "`.` after lambda binder")?;
        if !pattern_punct(&dot, '.') {
            return Err(syn::Error::new(dot.span(), "expected `.` after lambda binder"));
        }
    }

    let first = take_pattern_tree(input, &mut output, "pattern")?;
    let chainable = match &first {
        proc_macro2::TokenTree::Group(group)
            if matches!(
                group.delimiter(),
                proc_macro2::Delimiter::Parenthesis | proc_macro2::Delimiter::Brace
            ) =>
        {
            false
        },
        proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '*' => {
            let operator = take_pattern_tree(input, &mut output, "metasyntax operator")?;
            let proc_macro2::TokenTree::Ident(operator) = operator else {
                return Err(syn::Error::new(operator.span(), "expected metasyntax operator"));
            };
            let arguments = take_pattern_tree(input, &mut output, "metasyntax arguments")?;
            if !matches!(
                arguments,
                proc_macro2::TokenTree::Group(ref group)
                    if group.delimiter() == proc_macro2::Delimiter::Parenthesis
            ) {
                return Err(syn::Error::new(arguments.span(), "expected metasyntax arguments"));
            }
            operator == "zip"
        },
        proc_macro2::TokenTree::Ident(_) => {
            if matches!(
                input.front(),
                Some(proc_macro2::TokenTree::Group(group))
                    if group.delimiter() == proc_macro2::Delimiter::Bracket
            ) {
                let _ = take_pattern_tree(input, &mut output, "indexed pattern")?;
                false
            } else {
                true
            }
        },
        _ => return Err(syn::Error::new(first.span(), "expected pattern")),
    };

    if chainable {
        while input.front().is_some_and(|tree| pattern_punct(tree, '.'))
            && input.get(1).is_some_and(|tree| pattern_punct(tree, '*'))
        {
            let _ = take_pattern_tree(input, &mut output, "`.`")?;
            let _ = take_pattern_tree(input, &mut output, "`*`")?;
            let operator = take_pattern_tree(input, &mut output, "chained metasyntax operator")?;
            if !matches!(operator, proc_macro2::TokenTree::Ident(_)) {
                return Err(syn::Error::new(operator.span(), "expected chained operator"));
            }
            let arguments = take_pattern_tree(input, &mut output, "chained metasyntax arguments")?;
            if !matches!(
                arguments,
                proc_macro2::TokenTree::Group(ref group)
                    if group.delimiter() == proc_macro2::Delimiter::Parenthesis
            ) {
                return Err(syn::Error::new(arguments.span(), "expected chained arguments"));
            }
        }
    }

    Ok(output)
}

fn parse_pattern_tokens(tokens: TokenStream) -> SynResult<Pattern> {
    enum LambdaBinder {
        One(Ident),
        Many(Vec<Ident>),
    }

    enum Chain {
        Map { params: Vec<Ident>, body: TokenStream },
        Zip { other: TokenStream },
    }

    enum Task {
        Parse(std::collections::VecDeque<proc_macro2::TokenTree>),
        AssembleLambda(LambdaBinder),
        AssembleCollection {
            child_count: usize,
            rest: Option<Ident>,
        },
        AssembleApply {
            constructor: Ident,
            child_count: usize,
        },
        AssembleEval {
            span: proc_macro2::Span,
            child_count: usize,
        },
        AssembleMap {
            params: Vec<Ident>,
        },
        AssembleZip,
        AssembleIndexed {
            collection: Ident,
            index: Ident,
        },
        ProcessChains(std::collections::VecDeque<Chain>),
    }

    fn token_stream(input: impl IntoIterator<Item = proc_macro2::TokenTree>) -> TokenStream {
        input.into_iter().collect()
    }

    fn parse_task(stream: TokenStream) -> Task {
        Task::Parse(stream.into_iter().collect())
    }

    fn expect_punct(
        input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
        expected: char,
        description: &str,
    ) -> SynResult<()> {
        let tree = input.pop_front().ok_or_else(|| {
            syn::Error::new(proc_macro2::Span::call_site(), format!("expected {description}"))
        })?;
        if pattern_punct(&tree, expected) {
            Ok(())
        } else {
            Err(syn::Error::new(tree.span(), format!("expected {description}")))
        }
    }

    fn expect_ident(
        input: &mut std::collections::VecDeque<proc_macro2::TokenTree>,
        description: &str,
    ) -> SynResult<Ident> {
        let tree = input.pop_front().ok_or_else(|| {
            syn::Error::new(proc_macro2::Span::call_site(), format!("expected {description}"))
        })?;
        if let proc_macro2::TokenTree::Ident(ident) = tree {
            Ok(ident)
        } else {
            Err(syn::Error::new(tree.span(), format!("expected {description}")))
        }
    }

    fn parse_ident_list(stream: TokenStream) -> SynResult<Vec<Ident>> {
        let mut input: std::collections::VecDeque<_> = stream.into_iter().collect();
        let mut ids = Vec::new();
        while !input.is_empty() {
            ids.push(expect_ident(&mut input, "binder identifier")?);
            if input.is_empty() {
                break;
            }
            expect_punct(&mut input, ',', "`,` between binders")?;
        }
        Ok(ids)
    }

    fn parse_closure_tokens(stream: TokenStream) -> SynResult<(Vec<Ident>, TokenStream)> {
        let mut input: std::collections::VecDeque<_> = stream.into_iter().collect();
        expect_punct(&mut input, '|', "`|` before closure parameters")?;
        let mut params = Vec::new();
        while !input.front().is_some_and(|tree| pattern_punct(tree, '|')) {
            params.push(expect_ident(&mut input, "closure parameter")?);
            if input.front().is_some_and(|tree| pattern_punct(tree, ',')) {
                input.pop_front();
            } else if !input.front().is_some_and(|tree| pattern_punct(tree, '|')) {
                let span = input
                    .front()
                    .map(proc_macro2::TokenTree::span)
                    .unwrap_or_else(proc_macro2::Span::call_site);
                return Err(syn::Error::new(span, "expected `,` or `|` after closure parameter"));
            }
        }
        expect_punct(&mut input, '|', "`|` after closure parameters")?;
        if input.is_empty() {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected pattern after closure parameters",
            ));
        }
        let body = take_one_pattern_tokens(&mut input)?;
        if let Some(extra) = input.front() {
            return Err(syn::Error::new(
                extra.span(),
                "unexpected tokens after closure body pattern",
            ));
        }
        Ok((params, body))
    }

    fn parse_chains(
        mut input: std::collections::VecDeque<proc_macro2::TokenTree>,
    ) -> SynResult<std::collections::VecDeque<Chain>> {
        let mut chains = std::collections::VecDeque::new();
        while !input.is_empty() {
            expect_punct(&mut input, '.', "`.` before chained metasyntax")?;
            expect_punct(&mut input, '*', "`*` before chained metasyntax")?;
            let operator = expect_ident(&mut input, "chained metasyntax operator")?;
            let arguments = input.pop_front().ok_or_else(|| {
                syn::Error::new(operator.span(), "expected chained metasyntax arguments")
            })?;
            let proc_macro2::TokenTree::Group(arguments) = arguments else {
                return Err(syn::Error::new(arguments.span(), "expected parentheses"));
            };
            if arguments.delimiter() != proc_macro2::Delimiter::Parenthesis {
                return Err(syn::Error::new(arguments.span(), "expected parentheses"));
            }
            match operator.to_string().as_str() {
                "map" => {
                    let (params, body) = parse_closure_tokens(arguments.stream())?;
                    chains.push_back(Chain::Map { params, body });
                },
                "zip" => {
                    let mut contents: std::collections::VecDeque<_> =
                        arguments.stream().into_iter().collect();
                    let other = take_one_pattern_tokens(&mut contents)?;
                    if let Some(extra) = contents.front() {
                        return Err(syn::Error::new(
                            extra.span(),
                            "unexpected tokens after chained zip operand",
                        ));
                    }
                    chains.push_back(Chain::Zip { other });
                },
                name => {
                    return Err(syn::Error::new(
                        operator.span(),
                        format!("Unknown chained metasyntax operator: #{name}"),
                    ));
                },
            }
        }
        Ok(chains)
    }

    fn split_collection(stream: TokenStream) -> SynResult<(Vec<TokenStream>, Option<Ident>)> {
        let mut segments = Vec::new();
        let mut current = TokenStream::new();
        for tree in stream {
            if pattern_punct(&tree, ',') {
                segments.push(std::mem::take(&mut current));
            } else {
                current.extend(std::iter::once(tree));
            }
        }
        if !current.is_empty() {
            segments.push(current);
        }

        let mut elements = Vec::new();
        let mut rest = None;
        let segment_count = segments.len();
        for (index, segment) in segments.into_iter().enumerate() {
            let trees: Vec<_> = segment.clone().into_iter().collect();
            let is_rest = trees.len() == 4
                && trees[..3].iter().all(|tree| pattern_punct(tree, '.'))
                && matches!(&trees[3], proc_macro2::TokenTree::Ident(_));
            if is_rest {
                if index + 1 != segment_count {
                    return Err(syn::Error::new(
                        trees[0].span(),
                        "collection rest must be the final element",
                    ));
                }
                let proc_macro2::TokenTree::Ident(ident) = &trees[3] else {
                    unreachable!()
                };
                rest = Some(ident.clone());
            } else {
                let mut input: std::collections::VecDeque<_> = segment.into_iter().collect();
                let element = take_one_pattern_tokens(&mut input)?;
                if let Some(extra) = input.front() {
                    return Err(syn::Error::new(
                        extra.span(),
                        "unexpected tokens after collection element pattern",
                    ));
                }
                elements.push(element);
            }
        }
        Ok((elements, rest))
    }

    fn take_children(values: &mut Vec<Pattern>, child_count: usize) -> Vec<Pattern> {
        let first = values
            .len()
            .checked_sub(child_count)
            .expect("assembly follows all child parses");
        values.split_off(first)
    }

    // Establish the root boundary once. Every child producer below either
    // calls `take_one_pattern_tokens` or validates an exact delimited body, so
    // repeating this scan in every `Task::Parse` would make a flat Lambda
    // chain quadratic in its depth.
    let mut root: std::collections::VecDeque<_> = tokens.into_iter().collect();
    let root_pattern = take_one_pattern_tokens(&mut root)?;
    if let Some(extra) = root.front() {
        return Err(syn::Error::new(extra.span(), "unexpected tokens after pattern"));
    }
    let mut tasks = vec![parse_task(root_pattern)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Parse(mut input) => {
                if input.front().is_some_and(|tree| pattern_punct(tree, '^')) {
                    input.pop_front();
                    let binder = match input.pop_front() {
                        Some(proc_macro2::TokenTree::Ident(ident)) => LambdaBinder::One(ident),
                        Some(proc_macro2::TokenTree::Group(group))
                            if group.delimiter() == proc_macro2::Delimiter::Bracket =>
                        {
                            LambdaBinder::Many(parse_ident_list(group.stream())?)
                        },
                        Some(tree) => {
                            return Err(syn::Error::new(tree.span(), "expected lambda binder"));
                        },
                        None => {
                            return Err(syn::Error::new(
                                proc_macro2::Span::call_site(),
                                "expected lambda binder",
                            ));
                        },
                    };
                    expect_punct(&mut input, '.', "`.` after lambda binder")?;
                    tasks.push(Task::AssembleLambda(binder));
                    tasks.push(Task::Parse(input));
                    continue;
                }

                let first = input
                    .pop_front()
                    .expect("take_one_pattern_tokens found a pattern");
                match first {
                    proc_macro2::TokenTree::Group(group)
                        if group.delimiter() == proc_macro2::Delimiter::Brace =>
                    {
                        let (elements, rest) = split_collection(group.stream())?;
                        tasks.push(Task::AssembleCollection { child_count: elements.len(), rest });
                        tasks.extend(elements.into_iter().rev().map(parse_task));
                    },
                    proc_macro2::TokenTree::Group(group)
                        if group.delimiter() == proc_macro2::Delimiter::Parenthesis =>
                    {
                        let mut contents: std::collections::VecDeque<_> =
                            group.stream().into_iter().collect();
                        let constructor = expect_ident(&mut contents, "constructor name")?;
                        let mut arguments = Vec::new();
                        while !contents.is_empty() {
                            arguments.push(take_one_pattern_tokens(&mut contents)?);
                        }
                        if constructor == "eval" {
                            tasks.push(Task::AssembleEval {
                                span: constructor.span(),
                                child_count: arguments.len(),
                            });
                        } else {
                            tasks.push(Task::AssembleApply {
                                constructor,
                                child_count: arguments.len(),
                            });
                        }
                        tasks.extend(arguments.into_iter().rev().map(parse_task));
                    },
                    proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '*' => {
                        let operator = expect_ident(&mut input, "metasyntax operator")?;
                        let arguments = input.pop_front().ok_or_else(|| {
                            syn::Error::new(operator.span(), "expected metasyntax arguments")
                        })?;
                        let proc_macro2::TokenTree::Group(arguments) = arguments else {
                            return Err(syn::Error::new(arguments.span(), "expected parentheses"));
                        };
                        if arguments.delimiter() != proc_macro2::Delimiter::Parenthesis {
                            return Err(syn::Error::new(arguments.span(), "expected parentheses"));
                        }
                        match operator.to_string().as_str() {
                            "zip" => {
                                let mut contents: std::collections::VecDeque<_> =
                                    arguments.stream().into_iter().collect();
                                let left = take_one_pattern_tokens(&mut contents)?;
                                expect_punct(&mut contents, ',', "`,` between zip operands")?;
                                let right = take_one_pattern_tokens(&mut contents)?;
                                if let Some(extra) = contents.front() {
                                    return Err(syn::Error::new(
                                        extra.span(),
                                        "unexpected tokens after second zip operand",
                                    ));
                                }
                                let chains = parse_chains(input)?;
                                tasks.push(Task::ProcessChains(chains));
                                tasks.push(Task::AssembleZip);
                                tasks.push(parse_task(right));
                                tasks.push(parse_task(left));
                            },
                            "map" => {
                                let mut contents: std::collections::VecDeque<_> =
                                    arguments.stream().into_iter().collect();
                                let collection = take_one_pattern_tokens(&mut contents)?;
                                expect_punct(&mut contents, ',', "`,` before map closure")?;
                                let (params, body) = parse_closure_tokens(token_stream(contents))?;
                                tasks.push(Task::AssembleMap { params });
                                tasks.push(parse_task(body));
                                tasks.push(parse_task(collection));
                            },
                            name => {
                                return Err(syn::Error::new(
                                    operator.span(),
                                    format!("Unknown metasyntax operator: #{name}"),
                                ));
                            },
                        }
                    },
                    proc_macro2::TokenTree::Ident(collection) => {
                        if matches!(
                            input.front(),
                            Some(proc_macro2::TokenTree::Group(group))
                                if group.delimiter() == proc_macro2::Delimiter::Bracket
                        ) {
                            let proc_macro2::TokenTree::Group(indexed) =
                                input.pop_front().expect("the bracket group was peeked")
                            else {
                                unreachable!()
                            };
                            let mut indexed: std::collections::VecDeque<_> =
                                indexed.stream().into_iter().collect();
                            let index = expect_ident(&mut indexed, "index binder")?;
                            expect_punct(&mut indexed, ':', "`:=` after index binder")?;
                            expect_punct(&mut indexed, '=', "`:=` after index binder")?;
                            let element = take_one_pattern_tokens(&mut indexed)?;
                            if let Some(extra) = indexed.front() {
                                return Err(syn::Error::new(
                                    extra.span(),
                                    "unexpected tokens after indexed element pattern",
                                ));
                            }
                            tasks.push(Task::AssembleIndexed { collection, index });
                            tasks.push(parse_task(element));
                        } else {
                            values.push(Pattern::Term(PatternTerm::Var(collection)));
                            tasks.push(Task::ProcessChains(parse_chains(input)?));
                        }
                    },
                    tree => return Err(syn::Error::new(tree.span(), "expected pattern")),
                }
            },
            Task::AssembleLambda(binder) => {
                let body = Box::new(values.pop().expect("lambda assembly follows body parse"));
                values.push(Pattern::Term(match binder {
                    LambdaBinder::One(binder) => PatternTerm::Lambda { binder, body },
                    LambdaBinder::Many(binders) => PatternTerm::MultiLambda { binders, body },
                }));
            },
            Task::AssembleCollection { child_count, rest } => {
                let elements = take_children(&mut values, child_count);
                values.push(Pattern::Collection { coll_type: None, elements, rest });
            },
            Task::AssembleApply { constructor, child_count } => {
                let args = take_children(&mut values, child_count);
                values.push(Pattern::Term(PatternTerm::Apply { constructor, args }));
            },
            Task::AssembleEval { span, child_count } => {
                let mut args = take_children(&mut values, child_count).into_iter();
                let first = args
                    .next()
                    .ok_or_else(|| syn::Error::new(span, "eval requires at least 2 arguments"))?;
                let second = args
                    .next()
                    .ok_or_else(|| syn::Error::new(span, "eval requires at least 2 arguments"))?;
                let third = args.next();
                if args.next().is_some() {
                    return Err(syn::Error::new(span, "eval takes 2 or 3 arguments"));
                }
                let result = if let Some(replacement) = third {
                    let var = match &second {
                        Pattern::Term(PatternTerm::Var(var)) => var.clone(),
                        _ => {
                            return Err(syn::Error::new(
                                span,
                                "In 3-arg eval syntax (subst term var repl), second argument must be a variable name",
                            ));
                        },
                    };
                    Pattern::Term(PatternTerm::Subst {
                        term: Box::new(first),
                        var,
                        replacement: Box::new(replacement),
                    })
                } else {
                    match &first {
                        Pattern::Term(PatternTerm::Lambda { binder, body }) => {
                            Pattern::Term(PatternTerm::Subst {
                                term: body.clone(),
                                var: binder.clone(),
                                replacement: Box::new(second),
                            })
                        },
                        Pattern::Term(PatternTerm::MultiLambda { .. }) => {
                            Pattern::Term(PatternTerm::MultiSubst {
                                scope: Box::new(first),
                                replacements: vec![second],
                            })
                        },
                        _ => Pattern::Term(PatternTerm::MultiSubst {
                            scope: Box::new(first),
                            replacements: vec![second],
                        }),
                    }
                };
                values.push(result);
            },
            Task::AssembleMap { params } => {
                let body = Box::new(values.pop().expect("map assembly follows body parse"));
                let collection =
                    Box::new(values.pop().expect("map assembly follows collection parse"));
                values.push(Pattern::Map { collection, params, body });
            },
            Task::AssembleZip => {
                let second = Box::new(values.pop().expect("zip assembly follows right parse"));
                let first = Box::new(values.pop().expect("zip assembly follows left parse"));
                values.push(Pattern::Zip { first, second });
            },
            Task::AssembleIndexed { collection, index } => {
                let element = Box::new(
                    values
                        .pop()
                        .expect("indexed assembly follows element parse"),
                );
                values.push(Pattern::IndexedVec { collection, index, element });
            },
            Task::ProcessChains(mut chains) => {
                if let Some(chain) = chains.pop_front() {
                    tasks.push(Task::ProcessChains(chains));
                    match chain {
                        Chain::Map { params, body } => {
                            tasks.push(Task::AssembleMap { params });
                            tasks.push(parse_task(body));
                        },
                        Chain::Zip { other } => {
                            tasks.push(Task::AssembleZip);
                            tasks.push(parse_task(other));
                        },
                    }
                }
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values.pop().expect("one root pattern is always emitted"))
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
        is_auto_injected: false,
    })
}

/// E-3 T-INCR (red-team amendment EM-3): parse a bare REWRITE-RULE FRAGMENT — one or
/// more `Name . |- lhs ~> rhs ;` lines exactly as they appear inside a `language!`
/// body's `rewrites { … }` block — through the SAME private [`parse_rewrites`]
/// production parser (including its comment skipping and optional semicolons), by
/// wrapping the fragment in a synthetic `rewrites { … }` block.
///
/// This is the fragment-parse seam the incremental rule-append path
/// (`rholang-codegen::extend_in_rho_artifacts`) uses so a single-rewrite append never
/// re-parses the whole definition source. Every parsed rule carries
/// `is_auto_injected: false` (a user-authored fragment), exactly as a full-source
/// parse would. Trailing garbage after the last rule fails closed with the production
/// parser's own error (nothing is silently dropped).
pub fn parse_rewrite_fragment(fragment: &str) -> SynResult<Vec<RewriteRule>> {
    syn::parse::Parser::parse_str(parse_rewrites, &format!("rewrites {{ {fragment} }}"))
}

/// E-3 T-INCR (red-team amendment EM-3): splice a rewrite-rule fragment into a
/// `language!` definition source's `rewrites { … }` block, producing the EXTENDED
/// source string — the memo key of the extended artifacts AND the input of the
/// batch (full re-derive) arm, so both arms derive from one identical source.
///
/// The fragment is inserted immediately before the block's closing `}`; because
/// `LanguageDef` sources carry a SINGLE `rewrites` block per language, the splice
/// point is unambiguous — this function REQUIRES exactly one block and fails closed
/// otherwise (zero blocks: nothing to extend; multiple: ambiguous). The scan honors
/// `//` line comments and string literals (a `rewrites` keyword or brace inside
/// either never counts), and the block's braces are depth-matched (rewrite patterns
/// may contain `{…}` collection literals).
pub fn splice_rewrite_into_source(source: &str, fragment: &str) -> Result<String, String> {
    let block = find_sole_rewrites_block(source)?;
    let mut extended = String::with_capacity(source.len() + fragment.len() + 2);
    extended.push_str(&source[..block.close_index]);
    // Keep the appended rule on its own line — whitespace never enters the
    // span-independent definition identity, this is purely for readability.
    extended.push('\n');
    extended.push_str(fragment);
    extended.push('\n');
    extended.push_str(&source[block.close_index..]);
    Ok(extended)
}

/// The sole `rewrites { … }` block of a definition source: the byte index of its
/// opening `{` and of its matching closing `}` (the splice point).
struct RewritesBlock {
    close_index: usize,
}

/// Scan for the definition source's `rewrites` blocks (comment/string-aware) and
/// return the sole one; `Err` on zero or more than one (see
/// [`splice_rewrite_into_source`]).
fn find_sole_rewrites_block(source: &str) -> Result<RewritesBlock, String> {
    let bytes = source.as_bytes();
    let mut blocks: Vec<RewritesBlock> = Vec::with_capacity(1);
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            // `//` line comment: skip to end of line.
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            },
            // String literal: skip to the closing quote (honoring escapes).
            b'"' => {
                index += 1;
                while index < bytes.len() {
                    match bytes[index] {
                        b'\\' => index += 2,
                        b'"' => {
                            index += 1;
                            break;
                        },
                        _ => index += 1,
                    }
                }
            },
            // Candidate `rewrites` keyword at an identifier boundary.
            b'r' if source[index..].starts_with("rewrites")
                && !prev_is_ident_byte(bytes, index)
                && !next_is_ident_byte(bytes, index + "rewrites".len()) =>
            {
                let after_keyword = index + "rewrites".len();
                if let Some(open) =
                    next_non_ws(bytes, after_keyword).filter(|&at| bytes[at] == b'{')
                {
                    let close = matching_close_brace(source, open)?;
                    blocks.push(RewritesBlock { close_index: close });
                    index = close + 1;
                    continue;
                }
                index = after_keyword;
            },
            _ => index += 1,
        }
    }
    match blocks.len() {
        1 => Ok(blocks
            .pop()
            .expect("exactly one rewrites block was collected")),
        0 => Err("definition source has no `rewrites { … }` block to splice into".to_string()),
        n => Err(format!(
            "definition source has {n} `rewrites {{ … }}` blocks — the splice point is ambiguous"
        )),
    }
}

fn prev_is_ident_byte(bytes: &[u8], index: usize) -> bool {
    index
        .checked_sub(1)
        .is_some_and(|prev| bytes[prev].is_ascii_alphanumeric() || bytes[prev] == b'_')
}

fn next_is_ident_byte(bytes: &[u8], index: usize) -> bool {
    bytes
        .get(index)
        .is_some_and(|&byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

/// The index of the first non-whitespace byte at or after `from`.
fn next_non_ws(bytes: &[u8], from: usize) -> Option<usize> {
    (from..bytes.len()).find(|&at| !bytes[at].is_ascii_whitespace())
}

/// The index of the `}` matching the `{` at `open` (depth-matched, comment/string-aware).
fn matching_close_brace(source: &str, open: usize) -> Result<usize, String> {
    let bytes = source.as_bytes();
    debug_assert_eq!(bytes[open], b'{');
    let mut depth = 0usize;
    let mut index = open;
    while index < bytes.len() {
        match bytes[index] {
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
                continue;
            },
            b'"' => {
                index += 1;
                while index < bytes.len() {
                    match bytes[index] {
                        b'\\' => index += 2,
                        b'"' => {
                            index += 1;
                            break;
                        },
                        _ => index += 1,
                    }
                }
                continue;
            },
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(index);
                }
            },
            _ => {},
        }
        index += 1;
    }
    Err("unbalanced braces in the `rewrites { … }` block".to_string())
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
            // Stage 3.27a (2026-05-04): doc_comment is None for now —
            // ascent_syntax_export does not surface relation-level doc
            // comments. Future: extend ascent_syntax_export to capture
            // and forward `#[doc = "..."]` attributes per relation.
            RelationDecl {
                name: rel.name,
                param_types,
                doc_comment: None,
            }
        })
        .collect();

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(LogicBlock { relations, content: tokens })
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 1 smoke tests for `parse_guards()` (design doc §2A)
// ══════════════════════════════════════════════════════════════════════════════
//
// These tests verify the parser can handle the four sub-block forms (direct
// predicates, connectives, theories, channels) plus annotations and the
// variadic/typed parameter forms. Comprehensive tests live in Phase 9.

// ══════════════════════════════════════════════════════════════════════════════
// E-3 T-INCR (EM-3): fragment-parse + source-splice seam tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod rewrite_fragment_tests {
    use super::*;

    #[test]
    fn parses_a_single_base_rewrite_fragment() {
        let rules = parse_rewrite_fragment("MX0 . |- (R0 (S (S x))) ~> (Wrap x) ;")
            .expect("a base-shape rewrite line parses");
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].name.to_string(), "MX0");
        assert!(rules[0].premises.is_empty());
        assert!(rules[0].type_context.is_empty());
        assert!(!rules[0].is_auto_injected, "a user fragment is never auto-injected");
    }

    #[test]
    fn parses_a_congruence_fragment_with_its_premise() {
        let rules = parse_rewrite_fragment("WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;")
            .expect("a congruence rewrite line parses");
        assert_eq!(rules.len(), 1);
        assert!(rules[0].is_congruence_rule(), "the premise survives the fragment parse");
    }

    #[test]
    fn parses_multiple_rules_and_rejects_garbage() {
        let rules =
            parse_rewrite_fragment("A0 . |- (R0 x) ~> (Wrap x) ; A1 . |- (R1 x) ~> (Wrap x) ;")
                .expect("two rewrite lines parse");
        assert_eq!(rules.len(), 2);
        assert!(
            parse_rewrite_fragment("not a rewrite ~~~").is_err(),
            "garbage fails closed through the production parser"
        );
    }

    #[test]
    fn splice_extends_the_sole_rewrites_block_and_reparses() {
        let source = r#"
            name: SpliceSmoke,
            types { Proc }
            terms {
                Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
                R0 . x:Proc |- "r0" "(" x ")" : Proc ;
                S . x:Proc |- "s" "(" x ")" : Proc ;
            }
            equations {}
            rewrites {
                M0 . |- (R0 (S x)) ~> (Wrap x) ;
            }
        "#;
        let extended = splice_rewrite_into_source(source, "MX0 . |- (R0 (S (S x))) ~> (Wrap x) ;")
            .expect("the sole rewrites block splices");
        let def = syn::parse_str::<LanguageDef>(&extended).expect("the extended source parses");
        let names: Vec<String> = def.rewrites.iter().map(|r| r.name.to_string()).collect();
        assert_eq!(names, ["M0", "MX0"], "the spliced rule lands at the END of the block");
    }

    #[test]
    fn splice_is_comment_and_string_aware() {
        // A `rewrites` keyword inside a comment and a brace inside a display string
        // must not confuse the scanner.
        let source = r#"
            name: SpliceGuards,
            // the rewrites { of this comment is not a block
            types { Proc }
            terms {
                Brace . x:Proc |- "{" x "}" : Proc ;
            }
            equations {}
            rewrites {
                // rewrites } comment inside the block
                M0 . |- (Brace x) ~> (Brace x) ;
            }
        "#;
        let extended =
            splice_rewrite_into_source(source, "M1 . |- (Brace (Brace x)) ~> (Brace x) ;")
                .expect("comment/string guards hold");
        let def = syn::parse_str::<LanguageDef>(&extended).expect("the extended source parses");
        assert_eq!(def.rewrites.len(), 2);
    }

    #[test]
    fn splice_fails_closed_without_exactly_one_block() {
        assert!(splice_rewrite_into_source("name: NoBlock, types { Proc }", "M . |- x ~> x ;")
            .expect_err("zero blocks fail closed")
            .contains("no `rewrites"),);
        let two = "rewrites { } rewrites { }";
        assert!(splice_rewrite_into_source(two, "M . |- x ~> x ;")
            .expect_err("two blocks fail closed")
            .contains("ambiguous"),);
    }
}

#[cfg(test)]
#[path = "../../tests/support/premise_recursive_oracle.rs"]
mod premise_recursive_oracle;

#[cfg(test)]
#[path = "../../tests/support/pattern_parser_recursive_oracle.rs"]
mod pattern_parser_recursive_oracle;

#[cfg(test)]
#[path = "../../tests/support/refinement_parser_recursive_oracle.rs"]
mod refinement_parser_recursive_oracle;

#[cfg(test)]
#[path = "../../tests/support/behavioral_parser_recursive_oracle.rs"]
mod behavioral_parser_recursive_oracle;

#[cfg(test)]
#[path = "../../tests/support/tree_constraint_parser_recursive_oracle.rs"]
mod tree_constraint_parser_recursive_oracle;
