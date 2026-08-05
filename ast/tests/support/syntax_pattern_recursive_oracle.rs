//! Test-only copy of the pre-PDA syntax-pattern parser.

use super::*;
use syn::parse::{Parse, ParseStream};

struct Pda(SyntaxExpr);

impl Parse for Pda {
    fn parse(input: ParseStream) -> SynResult<Self> {
        parse_syntax_expr(input).map(Self)
    }
}

struct Recursive(SyntaxExpr);

impl Parse for Recursive {
    fn parse(input: ParseStream) -> SynResult<Self> {
        parse_syntax_expr_recursive(input).map(Self)
    }
}

fn parse_syntax_expr_recursive(input: ParseStream) -> SynResult<SyntaxExpr> {
    if input.peek(Token![*]) {
        let fork = input.fork();
        let _ = fork.parse::<Token![*]>();
        if fork
            .parse::<Ident>()
            .map(|name| name == "flt")
            .unwrap_or(false)
        {
            let _ = input.parse::<Token![*]>()?;
            let _ = input.parse::<Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            let bind = content.parse()?;
            let _ = content.parse::<Token![,]>()?;
            let open = content.parse()?;
            let _ = content.parse::<Token![,]>()?;
            return Ok(SyntaxExpr::GuestBody { open, close: content.parse()?, bind });
        }
        return Ok(SyntaxExpr::Op(parse_pattern_op_recursive(input)?));
    }
    if input.peek(Ident) {
        let id = input.parse::<Ident>()?;
        if input.peek(Token![@]) && input.peek2(Ident) {
            let _ = input.parse::<Token![@]>()?;
            return Ok(SyntaxExpr::TokenKind { name: input.parse()?, bind: Some(id) });
        }
        if input.peek(Token![.]) && input.peek2(Token![*]) {
            let _ = input.parse::<Token![.]>()?;
            return Ok(SyntaxExpr::Op(parse_chains_recursive(input, PatternOp::Var(id))?));
        }
        return Ok(SyntaxExpr::Param(id));
    }
    if input.peek(syn::LitStr) {
        return Ok(SyntaxExpr::Literal(input.parse::<syn::LitStr>()?.value()));
    }
    Err(syn::Error::new(input.span(), "expected syntax expression"))
}

fn parse_pattern_op_recursive(input: ParseStream) -> SynResult<PatternOp> {
    let _ = input.parse::<Token![*]>()?;
    let name = input.parse::<Ident>()?;
    let content;
    syn::parenthesized!(content in input);
    let op = match name.to_string().as_str() {
        "sep" => {
            let collection = content.parse()?;
            let _ = content.parse::<Token![,]>()?;
            PatternOp::Sep {
                collection,
                separator: content.parse::<syn::LitStr>()?.value(),
                source: None,
            }
        },
        "zip" => {
            let left = content.parse()?;
            let _ = content.parse::<Token![,]>()?;
            PatternOp::Zip { left, right: content.parse()? }
        },
        "map" => {
            let source = if content.peek(Token![*]) {
                parse_pattern_op_recursive(&content)?
            } else {
                PatternOp::Var(content.parse()?)
            };
            let _ = content.parse::<Token![,]>()?;
            let (params, body) = parse_map_closure_recursive(&content)?;
            PatternOp::Map { source: Box::new(source), params, body }
        },
        "opt" => {
            let mut inner = Vec::new();
            while !content.is_empty() {
                inner.push(parse_syntax_expr_recursive(&content)?);
            }
            PatternOp::Opt { inner }
        },
        _ => return Err(syn::Error::new(name.span(), "unknown pattern operation")),
    };
    if input.peek(Token![.]) && input.peek2(Token![*]) {
        let _ = input.parse::<Token![.]>()?;
        parse_chains_recursive(input, op)
    } else {
        Ok(op)
    }
}

fn parse_chains_recursive(input: ParseStream, receiver: PatternOp) -> SynResult<PatternOp> {
    let _ = input.parse::<Token![*]>()?;
    let name = input.parse::<Ident>()?;
    let content;
    syn::parenthesized!(content in input);
    let op = match name.to_string().as_str() {
        "sep" => {
            let separator = content.parse::<syn::LitStr>()?.value();
            match &receiver {
                PatternOp::Var(collection) => PatternOp::Sep {
                    collection: collection.clone(),
                    separator,
                    source: None,
                },
                PatternOp::Map { .. } | PatternOp::Zip { .. } => {
                    return Ok(PatternOp::Sep {
                        collection: Ident::new("__chain__", proc_macro2::Span::call_site()),
                        separator,
                        source: Some(Box::new(receiver)),
                    });
                },
                _ => return Err(syn::Error::new(name.span(), "invalid sep receiver")),
            }
        },
        "map" => {
            let (params, body) = parse_map_closure_recursive(&content)?;
            PatternOp::Map { source: Box::new(receiver), params, body }
        },
        _ => return Err(syn::Error::new(name.span(), "invalid chained operation")),
    };
    if input.peek(Token![.]) && input.peek2(Token![*]) {
        let _ = input.parse::<Token![.]>()?;
        parse_chains_recursive(input, op)
    } else {
        Ok(op)
    }
}

fn parse_map_closure_recursive(input: ParseStream) -> SynResult<(Vec<Ident>, Vec<SyntaxExpr>)> {
    let _ = input.parse::<Token![|]>()?;
    let mut params = vec![input.parse()?];
    while input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
        if input.peek(Token![|]) {
            break;
        }
        params.push(input.parse()?);
    }
    let _ = input.parse::<Token![|]>()?;
    let mut body = Vec::new();
    while !input.is_empty() {
        body.push(parse_syntax_expr_recursive(input)?);
    }
    Ok((params, body))
}

#[test]
fn syntax_pattern_pda_matches_recursive_oracle() {
    let cases = [
        "x",
        "\"literal\"",
        "text@IdentTok",
        "*flt(node, Open, Close)",
        "*sep(xs, \",\")",
        "*zip(xs, ys)",
        "*opt(x \";\")",
        "*map(xs, |x| x)",
        "*map(*zip(xs, ys), |x, y| *opt(x y))",
        "xs.*map(|x| x). *map(|y| *opt(y))",
        "*zip(xs, ys). *sep(\",\")",
    ];
    for source in cases {
        let pda = syn::parse_str::<Pda>(source)
            .map(|parsed| format!("{:?}", parsed.0))
            .map_err(|error| error.to_string());
        let oracle = syn::parse_str::<Recursive>(source)
            .map(|parsed| format!("{:?}", parsed.0))
            .map_err(|error| error.to_string());
        assert_eq!(pda, oracle, "syntax parser divergence for `{source}`");
    }
}

#[test]
fn syntax_pattern_pda_handles_chain_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("syntax-pattern-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut source = String::from("xs");
            for _ in 0..DEPTH {
                source.push_str(".*map(|x| x)");
            }
            let parsed = syn::parse_str::<Pda>(&source)
                .expect("deep method-chain syntax parses")
                .0;
            let mut cursor: &PatternOp = match &parsed {
                SyntaxExpr::Op(op) => op,
                _ => panic!("method chain must produce an operation"),
            };
            let mut depth = 0;
            while let PatternOp::Map { source, .. } = cursor {
                cursor = source.as_ref();
                depth += 1;
            }
            assert!(matches!(cursor, PatternOp::Var(name) if name == "xs"));
            assert_eq!(depth, DEPTH);
            drop(parsed);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("syntax PDA must not overflow the native stack");
}
