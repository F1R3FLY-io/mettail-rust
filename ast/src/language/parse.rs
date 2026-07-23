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
        let (mut token_defs, mode_defs, sync_constraints, tree_invariants) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "tokens" {
                parse_tokens(input)?
            } else {
                (Vec::new(), Vec::new(), Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
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
    fn collect(params: &[TermParam], out: &mut std::collections::HashSet<String>) {
        for p in params {
            match p {
                TermParam::Simple { name, .. } | TermParam::GuardBody { name } => {
                    out.insert(name.to_string());
                },
                TermParam::Abstraction { binder, body, .. }
                | TermParam::MultiAbstraction { binder, body, .. } => {
                    out.insert(binder.to_string());
                    out.insert(body.to_string());
                },
                TermParam::Optional { params } => collect(params, out),
            }
        }
    }
    let mut out = std::collections::HashSet::new();
    if let Some(params) = tc {
        collect(params, &mut out);
    }
    out
}

/// L9-3: reclassify a bare `Param(x)` → `TokenKind{name:x, bind:None}` when `x`
/// is a declared token kind and not a term-context param. Recurses into
/// `#opt`/`#map` bodies (a `#map` closure param shadows a like-named token
/// inside its body).
fn reclassify_token_kinds(
    exprs: &mut [crate::grammar::SyntaxExpr],
    declared_kinds: &std::collections::HashSet<String>,
    ctx_names: &std::collections::HashSet<String>,
) {
    use crate::grammar::SyntaxExpr;
    for e in exprs.iter_mut() {
        match e {
            SyntaxExpr::Param(id) => {
                let n = id.to_string();
                if declared_kinds.contains(&n) && !ctx_names.contains(&n) {
                    *e = SyntaxExpr::TokenKind { name: id.clone(), bind: None };
                }
            },
            SyntaxExpr::Op(op) => reclassify_op_token_kinds(op, declared_kinds, ctx_names),
            SyntaxExpr::Literal(_) | SyntaxExpr::TokenKind { .. } => {},
        }
    }
}

fn reclassify_op_token_kinds(
    op: &mut crate::grammar::PatternOp,
    declared_kinds: &std::collections::HashSet<String>,
    ctx_names: &std::collections::HashSet<String>,
) {
    use crate::grammar::PatternOp;
    match op {
        PatternOp::Opt { inner } => reclassify_token_kinds(inner, declared_kinds, ctx_names),
        PatternOp::Map { source, params, body } => {
            reclassify_op_token_kinds(source, declared_kinds, ctx_names);
            // A #map closure param shadows a like-named token inside the body.
            let mut extended = ctx_names.clone();
            for p in params.iter() {
                extended.insert(p.to_string());
            }
            reclassify_token_kinds(body, declared_kinds, &extended);
        },
        PatternOp::Sep { source: Some(inner), .. } => {
            reclassify_op_token_kinds(inner, declared_kinds, ctx_names)
        },
        PatternOp::Sep { .. } | PatternOp::Zip { .. } | PatternOp::Var(_) => {},
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
    let close = close
        .ok_or_else(|| syn::Error::new(span, "collection delimiters dict requires `close_parts`"))?;
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
    let key_val_sep = if allow_kv { key_val_sep.or_else(|| Some(":".to_string())) } else { key_val_sep };
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
                    if (name_str == "Map" || name_str == "Pathmap") && paren_content.peek(Token![,]) {
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
    let predicate = parse_refinement_pred_implies(&brace_content)?;

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

/// Parse refinement predicate: entry point (lowest precedence = implies).
fn parse_refinement_pred_implies(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_or(input)?;
    while input.peek(Token![=>]) {
        input.parse::<Token![=>]>()?;
        let rhs = parse_refinement_pred_or(input)?;
        lhs = RefinementPredicate::Implies(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: disjunction (`||`).
fn parse_refinement_pred_or(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_and(input)?;
    while input.peek(Token![||]) {
        input.parse::<Token![||]>()?;
        let rhs = parse_refinement_pred_and(input)?;
        lhs = RefinementPredicate::Or(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: conjunction (`&&`).
fn parse_refinement_pred_and(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut lhs = parse_refinement_pred_not(input)?;
    while input.peek(Token![&&]) {
        input.parse::<Token![&&]>()?;
        let rhs = parse_refinement_pred_not(input)?;
        lhs = RefinementPredicate::And(Box::new(lhs), Box::new(rhs));
    }
    Ok(lhs)
}

/// Parse refinement predicate: negation (`~` or `!`).
fn parse_refinement_pred_not(input: ParseStream) -> SynResult<RefinementPredicate> {
    if input.peek(Token![~]) {
        input.parse::<Token![~]>()?;
        let inner = parse_refinement_pred_not(input)?;
        Ok(RefinementPredicate::Not(Box::new(inner)))
    } else if input.peek(Token![!]) && !input.peek(Token![!=]) {
        input.parse::<Token![!]>()?;
        let inner = parse_refinement_pred_not(input)?;
        Ok(RefinementPredicate::Not(Box::new(inner)))
    } else {
        parse_refinement_pred_atom(input)
    }
}

/// Parse refinement predicate: atomic term.
///
/// Handles:
/// - Parenthesized subexpressions: `(expr)`
/// - Quantifiers: `forall`/`exists` var [_{k=N}] [in domain]. body
/// - Relation queries: `rel(arg1, arg2, ...)`
/// - Linear comparisons: `var > 0`, `3*x + 2*y <= 7`
/// - Equality/inequality: `a == b`, `a != b`
fn parse_refinement_pred_atom(input: ParseStream) -> SynResult<RefinementPredicate> {
    // Parenthesized subexpression
    if input.peek(syn::token::Paren) {
        let paren_content;
        syn::parenthesized!(paren_content in input);
        return parse_refinement_pred_implies(&paren_content);
    }

    // Must be an identifier: could be quantifier, relation, or linear term
    let fork = input.fork();
    let ident: Ident = fork.parse()?;
    let ident_str = ident.to_string();

    // Quantifiers: forall / exists
    if ident_str == "forall" || ident_str == "exists" {
        input.parse::<Ident>()?; // consume the keyword
        let quantifier = if ident_str == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };

        // Optional bound: _{k=N}
        let bound = if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            let brace_content;
            syn::braced!(brace_content in input);
            let k_ident = brace_content.parse::<Ident>()?;
            if k_ident != "k" {
                return Err(syn::Error::new(k_ident.span(), "expected 'k'"));
            }
            brace_content.parse::<Token![=]>()?;
            let lit: syn::LitInt = brace_content.parse()?;
            Some(lit.base10_parse::<usize>()?)
        } else {
            None
        };

        // Quantified variable
        let var = input.parse::<Ident>()?;

        // Optional domain: `in relation`
        let domain = if input.peek(Ident) {
            let next_fork = input.fork();
            let next_ident: Ident = next_fork.parse()?;
            if next_ident == "in" {
                input.parse::<Ident>()?; // consume "in"
                Some(input.parse::<Ident>()?)
            } else {
                None
            }
        } else {
            None
        };

        // Dot separator
        input.parse::<Token![.]>()?;

        // Body (may be parenthesized)
        let body = parse_refinement_pred_atom(input)?;

        return Ok(RefinementPredicate::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }

    // Check if this is a relation query: ident(args)
    if fork.peek(syn::token::Paren) {
        input.parse::<Ident>()?; // consume the relation name
        let paren_content;
        syn::parenthesized!(paren_content in input);
        let mut args = Vec::new();
        while !paren_content.is_empty() {
            let arg_ident = paren_content.parse::<Ident>()?;
            let first_char = arg_ident.to_string().chars().next().unwrap_or('a');
            if first_char.is_uppercase() {
                args.push(PredArg::Constant(arg_ident));
            } else {
                args.push(PredArg::Var(arg_ident));
            }
            if paren_content.peek(Token![,]) {
                paren_content.parse::<Token![,]>()?;
            }
        }
        return Ok(RefinementPredicate::Relation { name: ident, args, negated: false });
    }

    // Linear arithmetic or simple variable comparison
    // Parse: ident followed by comparison operator
    // We need to handle: `x > 0`, `x >= 0`, `x == y`, etc.
    input.parse::<Ident>()?; // consume the first identifier

    // Check for comparison operators
    if input.peek(Token![>]) && input.peek2(Token![=]) {
        input.parse::<Token![>]>()?;
        input.parse::<Token![=]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Ge,
            rhs,
        });
    }
    if input.peek(Token![>]) {
        input.parse::<Token![>]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Gt,
            rhs,
        });
    }
    if input.peek(Token![<]) && input.peek2(Token![=]) {
        input.parse::<Token![<]>()?;
        input.parse::<Token![=]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Le,
            rhs,
        });
    }
    if input.peek(Token![<]) {
        input.parse::<Token![<]>()?;
        let rhs = parse_linear_rhs(input)?;
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation: LinearRelation::Lt,
            rhs,
        });
    }
    if input.peek(Token![==]) {
        input.parse::<Token![==]>()?;
        // Could be term equality or linear equality
        if input.peek(syn::LitInt) {
            let rhs = parse_linear_rhs(input)?;
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: LinearRelation::Eq,
                rhs,
            });
        }
        let rhs_ident = input.parse::<Ident>()?;
        let first_char = rhs_ident.to_string().chars().next().unwrap_or('a');
        let rhs_arg = if first_char.is_uppercase() {
            PredArg::Constant(rhs_ident)
        } else {
            PredArg::Var(rhs_ident)
        };
        let first_char_lhs = ident.to_string().chars().next().unwrap_or('a');
        let lhs_arg = if first_char_lhs.is_uppercase() {
            PredArg::Constant(ident)
        } else {
            PredArg::Var(ident)
        };
        return Ok(RefinementPredicate::TermEq(lhs_arg, rhs_arg));
    }
    if input.peek(Token![!=]) {
        input.parse::<Token![!=]>()?;
        if input.peek(syn::LitInt) {
            let rhs = parse_linear_rhs(input)?;
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: LinearRelation::Neq,
                rhs,
            });
        }
        let rhs_ident = input.parse::<Ident>()?;
        let first_char = rhs_ident.to_string().chars().next().unwrap_or('a');
        let rhs_arg = if first_char.is_uppercase() {
            PredArg::Constant(rhs_ident)
        } else {
            PredArg::Var(rhs_ident)
        };
        let first_char_lhs = ident.to_string().chars().next().unwrap_or('a');
        let lhs_arg = if first_char_lhs.is_uppercase() {
            PredArg::Constant(ident)
        } else {
            PredArg::Var(ident)
        };
        return Ok(RefinementPredicate::TermNeq(lhs_arg, rhs_arg));
    }

    // Bare identifier — treat as zero-argument relation query
    Ok(RefinementPredicate::Relation {
        name: ident,
        args: vec![],
        negated: false,
    })
}

/// Parse the right-hand side of a linear comparison (integer literal).
fn parse_linear_rhs(input: ParseStream) -> SynResult<i64> {
    let negative = if input.peek(Token![-]) {
        input.parse::<Token![-]>()?;
        true
    } else {
        false
    };
    let lit: syn::LitInt = input.parse()?;
    let val = lit.base10_parse::<i64>()?;
    Ok(if negative { -val } else { val })
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

    Ok(ModeDef { name, token_defs })
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

/// Parse a tree constraint expression.
///
/// Supports both keyword and Unicode operator forms at each position.
/// Grammar:
/// ```text
/// tree_expr ::= tree_atom (("and" | "∧" | "or" | "∨") tree_expr)?
/// tree_atom ::= ("forall" | "∀") children_of? Symbol "{" tree_expr "}"
///             | ("exists" | "∃") "child"
///             | ("not" | "¬") tree_atom
///             | ("match" | "∈") "{" symbol ("|" symbol)* "}"
///             | "(" tree_expr ")"
///             | Symbol
/// children_of ::= ("children" "of" | "↓")
/// ```
fn parse_tree_constraint_expr(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    let left = parse_tree_constraint_atom(input)?;

    // Check for binary operators: and/∧, or/∨
    if input.peek(Ident) {
        let fork = input.fork();
        if let Ok(kw) = fork.parse::<Ident>() {
            let kw_str = kw.to_string();
            if kw_str == "and" || kw_str == "\u{2227}" {
                // ∧ = U+2227
                let _ = input.parse::<Ident>()?;
                let right = parse_tree_constraint_expr(input)?;
                return Ok(TreeConstraintExpr::And(Box::new(left), Box::new(right)));
            } else if kw_str == "or" || kw_str == "\u{2228}" {
                // ∨ = U+2228
                let _ = input.parse::<Ident>()?;
                let right = parse_tree_constraint_expr(input)?;
                return Ok(TreeConstraintExpr::Or(Box::new(left), Box::new(right)));
            }
        }
    }

    Ok(left)
}

/// Parse an atomic tree constraint expression (unary/leaf).
fn parse_tree_constraint_atom(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    if input.peek(Ident) {
        let fork = input.fork();
        let kw = fork.parse::<Ident>()?;
        let kw_str = kw.to_string();

        match kw_str.as_str() {
            // forall / ∀
            "forall" | "\u{2200}" => {
                let _ = input.parse::<Ident>()?; // consume forall/∀

                // Check for "children of" / "↓"
                let fork2 = input.fork();
                let next = fork2.parse::<Ident>()?;
                let next_str = next.to_string();

                if next_str == "children" {
                    let _ = input.parse::<Ident>()?; // consume "children"
                    let of_kw = input.parse::<Ident>()?; // consume "of"
                    if of_kw != "of" {
                        return Err(syn::Error::new(
                            of_kw.span(),
                            "expected 'of' after 'children'",
                        ));
                    }
                    let symbol = input.parse::<Ident>()?;
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: symbol.to_string(),
                        body: Box::new(body),
                    })
                } else if next_str == "\u{2193}" {
                    // ↓ = U+2193
                    let _ = input.parse::<Ident>()?; // consume "↓"
                    let symbol = input.parse::<Ident>()?;
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: symbol.to_string(),
                        body: Box::new(body),
                    })
                } else {
                    // forall Symbol { body } (shorthand: symbol is next token)
                    let _ = input.parse::<Ident>()?; // consume symbol
                    let body_content;
                    syn::braced!(body_content in input);
                    let body = parse_tree_constraint_expr(&body_content)?;
                    Ok(TreeConstraintExpr::ForallChildren {
                        symbol: next_str,
                        body: Box::new(body),
                    })
                }
            },
            // exists / ∃
            "exists" | "\u{2203}" => {
                let _ = input.parse::<Ident>()?; // consume exists/∃
                let next = input.parse::<Ident>()?;
                if next != "child" {
                    return Err(syn::Error::new(
                        next.span(),
                        "expected 'child' after 'exists'/'∃'",
                    ));
                }
                Ok(TreeConstraintExpr::ExistsChild)
            },
            // not / ¬
            "not" | "\u{00AC}" => {
                let _ = input.parse::<Ident>()?; // consume not/¬
                let inner = parse_tree_constraint_atom(input)?;
                Ok(TreeConstraintExpr::Not(Box::new(inner)))
            },
            // match / ∈
            "match" | "\u{2208}" => {
                let _ = input.parse::<Ident>()?; // consume match/∈
                let body_content;
                syn::braced!(body_content in input);
                let mut symbols = Vec::new();
                while !body_content.is_empty() {
                    symbols.push(body_content.parse::<Ident>()?.to_string());
                    if body_content.peek(Token![|]) {
                        let _ = body_content.parse::<Token![|]>()?;
                    }
                }
                Ok(TreeConstraintExpr::Match(symbols))
            },
            // Plain atom: symbol name
            _ => {
                let _ = input.parse::<Ident>()?;
                Ok(TreeConstraintExpr::Atom(kw_str))
            },
        }
    } else if input.peek(syn::token::Paren) {
        // Parenthesized sub-expression
        let paren_content;
        syn::parenthesized!(paren_content in input);
        parse_tree_constraint_expr(&paren_content)
    } else {
        Err(input.error("expected tree constraint expression"))
    }
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
        let constraint = parse_tree_constraint_expr(&content)?;
        let _ = content.parse::<Token![;]>()?;
        invariants.push(TreeInvariant { name, constraint });
    }

    Ok(invariants)
}

/// Parse the `tokens { ... }` block.
///
/// Contains token definitions (default mode), named mode blocks,
/// optional `sync { ... }` block, and optional `tree_invariants { ... }` block.
fn parse_tokens(
    input: ParseStream,
) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>, Vec<SyncConstraint>, Vec<TreeInvariant>)> {
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

    Ok((token_defs, mode_defs, sync_constraints, tree_invariants_vec))
}

/// Public wrapper for `parse_tokens` for use by `fragment.rs`.
pub fn parse_tokens_public(input: ParseStream) -> SynResult<(Vec<TokenDef>, Vec<ModeDef>)> {
    let (token_defs, mode_defs, _, _) = parse_tokens(input)?;
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
    let mut saw_explicit_predicates = false;

    while !content.is_empty() {
        if !content.peek(Ident) {
            return Err(content.error(
                "expected predicate declaration, 'connectives', 'theories', or 'channels'",
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
    })
}

/// Parse a single built-in predicate declaration:
///
/// ```ignore
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
                        "unknown option '{}'. Valid options are: beam_width, log_semiring_model_path, dispatch, emit_tests, emit_blockly, emit_simulator, case_insensitive, unicode_normalization, reserved_keywords, parse_only",
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
///   relation   ::= ident "(" (ident ("," ident)*)? ")"
///   forall     ::= ident "." "*" "map" "(" "|" ident "|" premise ")"
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
    } else if input.peek(Token![.]) {
        // ForAll: xs.*map(|x| premise)
        let _ = input.parse::<Token![.]>()?;
        let _ = input.parse::<Token![*]>()?;
        let op = input.parse::<Ident>()?;
        if op != "map" {
            return Err(syn::Error::new(
                op.span(),
                "expected 'map' in quantified premise (xs.*map(|x| ...))",
            ));
        }
        let content;
        syn::parenthesized!(content in input);
        let _ = content.parse::<Token![|]>()?;
        let param = content.parse::<Ident>()?;
        let _ = content.parse::<Token![|]>()?;
        let body = parse_premise(&content)?;
        Ok(Premise::ForAll {
            collection: first,
            param,
            body: Box::new(body),
        })
    } else if first == "guard" && input.peek(syn::token::Paren) {
        // Behavioral guard premise: guard(pred_expr)
        let content;
        syn::parenthesized!(content in input);
        let pred = parse_behavioral_pred(&content)?;
        Ok(Premise::BehavioralGuard(pred))
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

/// Peek-and-consume any identifier in the active map that has the given role.
///
/// Returns `true` (and consumes the token) if successful; `false` otherwise.
fn try_consume_role_keyword(input: ParseStream, role: ConnectiveRole) -> bool {
    if !has_active_connective_map() {
        return false;
    }
    if !active_role_available(&role) {
        return false;
    }
    if !input.peek(Ident::peek_any) {
        return false;
    }
    // Peek the identifier without consuming
    let fork = input.fork();
    let id_result = fork.parse::<Ident>();
    if let Ok(id) = id_result {
        if let Some(kw_role) = active_role_of(&id.to_string()) {
            if kw_role == role {
                // Now actually consume from the real input
                let _ = input.parse::<Ident>();
                return true;
            }
        }
    }
    false
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
    let result = parse_pred_implies(input)?;
    check_conn02_unlisted_token(input)?;
    Ok(result)
}

/// Layer D cleanup: when an active `ConnectiveMap` is present, scan the
/// remaining input for stranded forbidden Rust connective tokens and emit
/// CONN02 if any is found.
///
/// This runs at the *trailing edge* of `parse_behavioral_pred`. By that
/// point, all tokens that the parser was willing to consume have been
/// consumed. Any leftover Rust connective is one the user wrote but the
/// active map does not declare.
fn check_conn02_unlisted_token(input: ParseStream) -> SynResult<()> {
    if !has_active_connective_map() {
        return Ok(());
    }
    if input.peek(Token![&&]) && !active_role_available(&ConnectiveRole::And) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `&&` (role `and`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![||]) && !active_role_available(&ConnectiveRole::Or) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `||` (role `or`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![~]) && !active_role_available(&ConnectiveRole::Not) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `~` (role `not`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![!]) && !active_role_available(&ConnectiveRole::Not) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `!` (role `not`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    if input.peek(Token![=>]) && !active_role_available(&ConnectiveRole::Entails) {
        return Err(syn::Error::new(
            input.span(),
            "CONN02: connective token `=>` (role `entails`) is not declared in the \
             active `connectives {}` block",
        ));
    }
    Ok(())
}

/// Implication (right-associative, lowest precedence).
fn parse_pred_implies(input: ParseStream) -> SynResult<BehavioralPred> {
    let lhs = parse_pred_or(input)?;

    // Check for "=>" (fat arrow — implication).
    // Only consume `=>` if either no connective map is active or the
    // active map declares `Entails` — otherwise CONN02 closed-world semantics.
    if input.peek(Token![=>]) && rust_token_allowed(ConnectiveRole::Entails) {
        let _ = input.parse::<Token![=>]>()?;
        let rhs = parse_pred_implies(input)?; // right-associative
        return Ok(BehavioralPred::Implies(Box::new(lhs), Box::new(rhs)));
    }

    // Custom keyword (e.g., `entails`, `implies`) from `connectives {}`.
    if try_consume_role_keyword(input, ConnectiveRole::Entails) {
        let rhs = parse_pred_implies(input)?; // right-associative
        return Ok(BehavioralPred::Implies(Box::new(lhs), Box::new(rhs)));
    }
    if try_consume_role_keyword(input, ConnectiveRole::ImpliedBy) {
        // Reverse implication: a implied_by b ≡ b => a
        let rhs = parse_pred_implies(input)?;
        return Ok(BehavioralPred::Implies(Box::new(rhs), Box::new(lhs)));
    }
    if try_consume_role_keyword(input, ConnectiveRole::Iff) {
        // Biconditional: a iff b ≡ (a => b) ∧ (b => a)
        let rhs = parse_pred_implies(input)?;
        let forward = BehavioralPred::Implies(Box::new(lhs.clone()), Box::new(rhs.clone()));
        let backward = BehavioralPred::Implies(Box::new(rhs), Box::new(lhs));
        return Ok(BehavioralPred::And(Box::new(forward), Box::new(backward)));
    }

    Ok(lhs)
}

/// Disjunction (`||` or declared `or` keyword).
///
/// Layer D cleanup: when an active `ConnectiveMap` is present, the
/// hardcoded `||` token is only accepted if the map also declares the
/// `Or` role. Otherwise the parser breaks the loop and the unconsumed
/// `||` later triggers a CONN02 diagnostic in `parse_behavioral_pred`.
fn parse_pred_or(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_and(input)?;

    loop {
        if input.peek(Token![||]) && rust_token_allowed(ConnectiveRole::Or) {
            let _ = input.parse::<Token![||]>()?;
        } else if try_consume_role_keyword(input, ConnectiveRole::Or) {
            // consumed
        } else {
            break;
        }
        let rhs = parse_pred_and(input)?;
        result = BehavioralPred::Or(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Conjunction (`&&` or declared `and` keyword).
///
/// Layer D cleanup: see `parse_pred_or` for the closed-world rationale.
fn parse_pred_and(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = parse_pred_not(input)?;

    loop {
        if input.peek(Token![&&]) && rust_token_allowed(ConnectiveRole::And) {
            let _ = input.parse::<Token![&&]>()?;
        } else if try_consume_role_keyword(input, ConnectiveRole::And) {
            // consumed
        } else {
            break;
        }
        let rhs = parse_pred_not(input)?;
        result = BehavioralPred::And(Box::new(result), Box::new(rhs));
    }

    Ok(result)
}

/// Negation (`~`, `!`, or declared `not` keyword).
///
/// Layer D cleanup: when an active `ConnectiveMap` omits `Not`, the
/// hardcoded `~` and `!` tokens are not consumed; they later trigger a
/// CONN02 diagnostic in `parse_behavioral_pred`.
fn parse_pred_not(input: ParseStream) -> SynResult<BehavioralPred> {
    if input.peek(Token![~]) && rust_token_allowed(ConnectiveRole::Not) {
        let _ = input.parse::<Token![~]>()?;
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else if input.peek(Token![!]) && rust_token_allowed(ConnectiveRole::Not) {
        let _ = input.parse::<Token![!]>()?;
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else if try_consume_role_keyword(input, ConnectiveRole::Not) {
        let inner = parse_pred_atom(input)?;
        Ok(BehavioralPred::Not(Box::new(inner)))
    } else {
        parse_pred_atom(input)
    }
}

/// Atomic predicate: relation query, quantifier, or parenthesized expression.
fn parse_pred_atom(input: ParseStream) -> SynResult<BehavioralPred> {
    // Parenthesized subexpression
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        return parse_behavioral_pred(&content);
    }

    let ident = input.parse::<Ident>()?;

    // AC-match: ac_match(bag, {x, y, ...rest})
    if ident == "ac_match" {
        let content;
        syn::parenthesized!(content in input);
        let bag = content.parse::<Ident>()?;
        let _ = content.parse::<Token![,]>()?;

        // Parse the element set: { x, y, ...rest }
        let set_content;
        syn::braced!(set_content in content);
        let mut elements = Vec::new();
        let mut rest = None;

        while !set_content.is_empty() {
            // Check for "..." (rest pattern)
            if set_content.peek(Token![...]) {
                let _ = set_content.parse::<Token![...]>()?;
                rest = Some(set_content.parse::<Ident>()?);
                // Trailing comma is optional after rest
                if set_content.peek(Token![,]) {
                    let _ = set_content.parse::<Token![,]>()?;
                }
                break;
            }

            elements.push(set_content.parse::<Ident>()?);
            if set_content.peek(Token![,]) {
                let _ = set_content.parse::<Token![,]>()?;
            }
        }

        if elements.is_empty() {
            return Err(syn::Error::new(
                ident.span(),
                "ac_match requires at least one element variable",
            ));
        }

        return Ok(BehavioralPred::AcMatch { bag, elements, rest });
    }

    // Quantifier: forall/exists var [bound] [in domain]. body
    if ident == "forall" || ident == "exists" {
        let quantifier = if ident == "forall" {
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

        let _ = input.parse::<Token![.]>()?;
        let body = parse_behavioral_pred(input)?;

        return Ok(BehavioralPred::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }

    // Relation query: rel(args...)
    if input.peek(syn::token::Paren) {
        let args_content;
        syn::parenthesized!(args_content in input);
        let mut args = Vec::new();
        while !args_content.is_empty() {
            let arg = args_content.parse::<Ident>()?;
            // Lowercase first char → variable, uppercase → constant
            if arg.to_string().starts_with(|c: char| c.is_uppercase()) {
                args.push(PredArg::Constant(arg));
            } else {
                args.push(PredArg::Var(arg));
            }
            if args_content.peek(Token![,]) {
                let _ = args_content.parse::<Token![,]>()?;
            }
        }
        return Ok(BehavioralPred::RelationQuery {
            relation_name: ident,
            args,
            negated: false,
        });
    }

    // Bare identifier as nullary relation query (no args)
    Ok(BehavioralPred::RelationQuery {
        relation_name: ident,
        args: vec![],
        negated: false,
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
                if let Some(open) = next_non_ws(bytes, after_keyword).filter(|&at| bytes[at] == b'{')
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
        1 => Ok(blocks.pop().expect("exactly one rewrites block was collected")),
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
        let rules = parse_rewrite_fragment(
            "A0 . |- (R0 x) ~> (Wrap x) ; A1 . |- (R1 x) ~> (Wrap x) ;",
        )
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
        let extended = splice_rewrite_into_source(source, "M1 . |- (Brace (Brace x)) ~> (Brace x) ;")
            .expect("comment/string guards hold");
        let def = syn::parse_str::<LanguageDef>(&extended).expect("the extended source parses");
        assert_eq!(def.rewrites.len(), 2);
    }

    #[test]
    fn splice_fails_closed_without_exactly_one_block() {
        assert!(
            splice_rewrite_into_source("name: NoBlock, types { Proc }", "M . |- x ~> x ;")
                .expect_err("zero blocks fail closed")
                .contains("no `rewrites"),
        );
        let two = "rewrites { } rewrites { }";
        assert!(
            splice_rewrite_into_source(two, "M . |- x ~> x ;")
                .expect_err("two blocks fail closed")
                .contains("ambiguous"),
        );
    }
}
