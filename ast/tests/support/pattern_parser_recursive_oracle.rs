use super::*;
use crate::identity::pattern_identity;
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use syn::parse::Parser;
#[cfg(test)]
fn recursive_parse_pattern(input: ParseStream) -> SynResult<Pattern> {
    // Parse #zip or #map metasyntax: #zip(a, b) or #map(coll, |x| body)
    if input.peek(Token![*]) {
        return recursive_parse_metasyntax_pattern(input);
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
            elements.push(recursive_parse_pattern(&content)?);

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
            let first = recursive_parse_pattern(&content)?;

            if content.is_empty() {
                return Err(syn::Error::new(
                    constructor.span(),
                    "eval requires at least 2 arguments",
                ));
            }

            let second = recursive_parse_pattern(&content)?;

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
                let replacement = recursive_parse_pattern(&content)?;

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
            args.push(recursive_parse_pattern(&content)?);
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
            let body = recursive_parse_pattern(input)?;

            return Ok(Pattern::Term(PatternTerm::MultiLambda { binders, body: Box::new(body) }));
        }

        // Single binder: ^x.body
        let binder = input.parse::<Ident>()?;
        input.parse::<Token![.]>()?;
        let body = recursive_parse_pattern(input)?;

        Ok(Pattern::Term(PatternTerm::Lambda { binder, body: Box::new(body) }))
    } else {
        // Just a variable - but check for chained metasyntax like `var.#map(...)`
        let var = input.parse::<Ident>()?;

        // Indexed positional element: `args[i := S]`. Recognised HERE, immediately after
        // the collection's name, because `[` can follow a bare pattern variable in no
        // other position — the pattern grammar has no indexing and no array literal, so
        // there is nothing to disambiguate against and no existing rule changes meaning.
        if input.peek(syn::token::Bracket) {
            let idx_content;
            syn::bracketed!(idx_content in input);
            let index = idx_content.parse::<Ident>()?;
            // `:=` is two syn tokens; there is no `Token![:=]`. Spelling it as assignment
            // rather than `,` keeps the direction readable — the element is REPLACED at
            // that position, and on the LHS the same syntax reads as "binds at".
            idx_content.parse::<Token![:]>()?;
            idx_content.parse::<Token![=]>()?;
            let element = recursive_parse_pattern(&idx_content)?;
            if !idx_content.is_empty() {
                return Err(idx_content.error(
                    "expected `]` after `collection[index := pattern]` — the indexed form \
                     takes exactly one index binder and one element pattern",
                ));
            }
            return Ok(Pattern::IndexedVec {
                collection: var,
                index,
                element: Box::new(element),
            });
        }

        let base = Pattern::Term(PatternTerm::Var(var));

        // Check for chained method-style metasyntax: var.#map(...)
        if input.peek(Token![.]) && input.peek2(Token![*]) {
            return recursive_parse_chained_metasyntax(input, base);
        }

        Ok(base)
    }
}

/// Parse metasyntax patterns: #zip(a, b), #map(coll, |x| body), etc.
#[cfg(test)]
fn recursive_parse_metasyntax_pattern(input: ParseStream) -> SynResult<Pattern> {
    input.parse::<Token![*]>()?;
    let op_name = input.parse::<Ident>()?;
    let op_str = op_name.to_string();

    match op_str.as_str() {
        "zip" => {
            // #zip(coll1, coll2)
            let content;
            syn::parenthesized!(content in input);

            let coll1 = recursive_parse_pattern(&content)?;
            content.parse::<Token![,]>()?;
            let coll2 = recursive_parse_pattern(&content)?;

            let base = Pattern::Zip {
                first: Box::new(coll1),
                second: Box::new(coll2),
            };

            // Check for chained metasyntax: #zip(a, b).#map(|x, y| ...)
            if input.peek(Token![.]) && input.peek2(Token![*]) {
                recursive_parse_chained_metasyntax(input, base)
            } else {
                Ok(base)
            }
        },
        "map" => {
            // #map(coll, |params| body) - prefix form
            let content;
            syn::parenthesized!(content in input);

            let collection = recursive_parse_pattern(&content)?;
            content.parse::<Token![,]>()?;

            // Parse closure: |params| body
            let (params, body) = recursive_parse_closure(&content)?;

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
#[cfg(test)]
fn recursive_parse_chained_metasyntax(input: ParseStream, base: Pattern) -> SynResult<Pattern> {
    input.parse::<Token![.]>()?;
    input.parse::<Token![*]>()?;
    let op_name = input.parse::<Ident>()?;
    let op_str = op_name.to_string();

    match op_str.as_str() {
        "map" => {
            // base.#map(|params| body)
            let content;
            syn::parenthesized!(content in input);

            let (params, body) = recursive_parse_closure(&content)?;

            let result = Pattern::Map {
                collection: Box::new(base),
                params,
                body: Box::new(body),
            };

            // Check for more chaining
            if input.peek(Token![.]) && input.peek2(Token![*]) {
                recursive_parse_chained_metasyntax(input, result)
            } else {
                Ok(result)
            }
        },
        "zip" => {
            // base.#zip(other) - less common but supported
            let content;
            syn::parenthesized!(content in input);

            let other = recursive_parse_pattern(&content)?;

            let result = Pattern::Zip {
                first: Box::new(base),
                second: Box::new(other),
            };

            if input.peek(Token![.]) && input.peek2(Token![*]) {
                recursive_parse_chained_metasyntax(input, result)
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
#[cfg(test)]
fn recursive_parse_closure(input: ParseStream) -> SynResult<(Vec<Ident>, Pattern)> {
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
    let body = recursive_parse_pattern(input)?;

    Ok((params, body))
}

fn production(source: &str) -> SynResult<Pattern> {
    parse_pattern_tokens(source.parse().expect("pattern fixture must tokenize"))
}

#[test]
fn pattern_pda_matches_the_recursive_parser_oracle() {
    let fixtures = [
        "x",
        "(Leaf)",
        "(Node x (Leaf) {y, (Leaf), ...rest})",
        "^x.(Node x)",
        "^[x, y].(Pair x y)",
        "(eval ^x.(Node x) replacement)",
        "(eval ^[x, y].(Pair x y) {a, b})",
        "(eval term x replacement)",
        "args[i := (Node x)]",
        "*zip(left, right)",
        "*map(items, |item| (Node item))",
        "items.*map(|item| (Node item))",
        "items.*zip(other).*map(|left, right| (Pair left right)).*zip(tail)",
        "*zip(left, right).*map(|a, b| (Pair a b)).*zip(tail)",
    ];

    for source in fixtures {
        let actual = production(source)
            .unwrap_or_else(|error| panic!("production rejected {source:?}: {error}"));
        let expected = Parser::parse_str(recursive_parse_pattern, source)
            .unwrap_or_else(|error| panic!("oracle rejected {source:?}: {error}"));
        assert_eq!(pattern_identity(&actual), pattern_identity(&expected), "source {source:?}");
    }

    for source in [
        "(eval x)",
        "(eval x (Node y) z)",
        "*zip(left)",
        "*map(items |x| x)",
        "items.*unknown(|x| x)",
        "args[i = x]",
    ] {
        assert_eq!(
            production(source).is_err(),
            Parser::parse_str(recursive_parse_pattern, source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

fn nested_apply_tokens(depth: usize) -> TokenStream {
    let mut pattern = TokenStream::from(TokenTree::Ident(Ident::new("leaf", Span::call_site())));
    for _ in 0..depth {
        let contents = TokenStream::from_iter(
            [TokenTree::Ident(Ident::new("Node", Span::call_site()))]
                .into_iter()
                .chain(pattern),
        );
        pattern = TokenStream::from(TokenTree::Group(Group::new(Delimiter::Parenthesis, contents)));
    }
    pattern
}

fn nested_lambda_tokens(depth: usize) -> TokenStream {
    let mut pattern = Vec::with_capacity(depth * 3 + 1);
    for _ in 0..depth {
        pattern.extend([
            TokenTree::Punct(Punct::new('^', Spacing::Alone)),
            TokenTree::Ident(Ident::new("binder", Span::call_site())),
            TokenTree::Punct(Punct::new('.', Spacing::Alone)),
        ]);
    }
    pattern.push(TokenTree::Ident(Ident::new("leaf", Span::call_site())));
    pattern.into_iter().collect()
}

fn chained_map_tokens(depth: usize) -> TokenStream {
    let mut pattern = Vec::with_capacity(depth * 4 + 1);
    pattern.push(TokenTree::Ident(Ident::new("items", Span::call_site())));
    for _ in 0..depth {
        let closure = TokenStream::from_iter([
            TokenTree::Punct(Punct::new('|', Spacing::Alone)),
            TokenTree::Ident(Ident::new("item", Span::call_site())),
            TokenTree::Punct(Punct::new('|', Spacing::Alone)),
            TokenTree::Ident(Ident::new("item", Span::call_site())),
        ]);
        pattern.extend([
            TokenTree::Punct(Punct::new('.', Spacing::Alone)),
            TokenTree::Punct(Punct::new('*', Spacing::Alone)),
            TokenTree::Ident(Ident::new("map", Span::call_site())),
            TokenTree::Group(Group::new(Delimiter::Parenthesis, closure)),
        ]);
    }
    pattern.into_iter().collect()
}

fn unary_apply_depth(pattern: &Pattern) -> usize {
    let mut depth = 0;
    let mut pattern = pattern;
    loop {
        match pattern {
            Pattern::Term(PatternTerm::Apply { constructor, args }) => {
                assert_eq!(constructor, "Node");
                assert_eq!(args.len(), 1);
                depth += 1;
                pattern = &args[0];
            },
            Pattern::Term(PatternTerm::Var(leaf)) => {
                assert_eq!(leaf, "leaf");
                return depth;
            },
            _ => panic!("expected a unary Apply chain"),
        }
    }
}

fn lambda_depth(pattern: &Pattern) -> usize {
    let mut depth = 0;
    let mut pattern = pattern;
    loop {
        match pattern {
            Pattern::Term(PatternTerm::Lambda { body, .. }) => {
                depth += 1;
                pattern = body;
            },
            Pattern::Term(PatternTerm::Var(leaf)) => {
                assert_eq!(leaf, "leaf");
                return depth;
            },
            _ => panic!("expected a Lambda chain"),
        }
    }
}

fn map_depth(pattern: &Pattern) -> usize {
    let mut depth = 0;
    let mut pattern = pattern;
    loop {
        match pattern {
            Pattern::Map { collection, body, .. } => {
                assert!(matches!(
                    body.as_ref(),
                    Pattern::Term(PatternTerm::Var(item)) if item == "item"
                ));
                depth += 1;
                pattern = collection;
            },
            Pattern::Term(PatternTerm::Var(items)) => {
                assert_eq!(items, "items");
                return depth;
            },
            _ => panic!("expected a chained Map pattern"),
        }
    }
}

#[test]
fn deep_pattern_parser_paths_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("pattern-parser-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let pattern = parse_pattern_tokens(nested_apply_tokens(DEPTH))
                .expect("deep Apply pattern must parse");
            assert_eq!(unary_apply_depth(&pattern), DEPTH);
            drop(pattern);

            let pattern = parse_pattern_tokens(nested_lambda_tokens(DEPTH))
                .expect("deep Lambda pattern must parse");
            assert_eq!(lambda_depth(&pattern), DEPTH);
            drop(pattern);

            let pattern = parse_pattern_tokens(chained_map_tokens(DEPTH))
                .expect("deep chained Map pattern must parse");
            assert_eq!(map_depth(&pattern), DEPTH);
            drop(pattern);
        })
        .expect("small-stack Pattern parser thread must spawn");
    handle
        .join()
        .expect("Pattern parser PDA must not overflow the native stack");
}

#[test]
fn token_reclassification_and_term_context_walk_fit_on_a_small_native_stack() {
    use crate::grammar::{PatternOp, SyntaxExpr, TermParam};
    use crate::types::TypeExpr;

    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("syntax-reclassification-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut param = TermParam::Simple {
                name: Ident::new("bound", Span::call_site()),
                ty: TypeExpr::Base(Ident::new("Term", Span::call_site())),
            };
            for _ in 0..DEPTH {
                param = TermParam::Optional { params: vec![param] };
            }
            let params = vec![param];
            let context = term_context_param_names(Some(&params));
            assert_eq!(context.len(), 1);
            assert!(context.contains("bound"));

            let mut expr = SyntaxExpr::Param(Ident::new("TokenLeaf", Span::call_site()));
            for _ in 0..DEPTH {
                expr = SyntaxExpr::Op(PatternOp::Opt { inner: vec![expr] });
            }
            let mut exprs = vec![expr];
            let declared = std::collections::HashSet::from(["TokenLeaf".to_string()]);
            reclassify_token_kinds(&mut exprs, &declared, &context);

            let mut expr = &exprs[0];
            for _ in 0..DEPTH {
                let SyntaxExpr::Op(PatternOp::Opt { inner }) = expr else {
                    panic!("expected a nested Opt expression")
                };
                assert_eq!(inner.len(), 1);
                expr = &inner[0];
            }
            assert!(matches!(
                expr,
                SyntaxExpr::TokenKind { name, bind: None } if name == "TokenLeaf"
            ));

            let mut mapped = vec![SyntaxExpr::Op(PatternOp::Map {
                source: Box::new(PatternOp::Var(Ident::new("items", Span::call_site()))),
                params: vec![Ident::new("TokenLeaf", Span::call_site())],
                body: vec![SyntaxExpr::Param(Ident::new("TokenLeaf", Span::call_site()))],
            })];
            reclassify_token_kinds(&mut mapped, &declared, &context);
            assert!(matches!(
                &mapped[0],
                SyntaxExpr::Op(PatternOp::Map { body, .. })
                    if matches!(&body[..], [SyntaxExpr::Param(name)] if name == "TokenLeaf")
            ));
        })
        .expect("small-stack syntax reclassification thread must spawn")
        .join()
        .expect("syntax reclassification must not overflow the native stack");
}
