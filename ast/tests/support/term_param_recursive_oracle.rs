use super::*;
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use syn::parse::Parser;

fn recursive_parse_term_param(input: ParseStream) -> SynResult<TermParam> {
    if input.peek(Token![?]) {
        let _ = input.parse::<Token![?]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let type_marker = input.parse::<Ident>()?;
        if type_marker != "Guard" {
            return Err(syn::Error::new(
                type_marker.span(),
                "expected `Guard` after `?<name>:` — only the `Guard` type marker is currently supported for guard slot parameters",
            ));
        }
        return Ok(TermParam::GuardBody { name });
    }

    if input.peek(Token![*]) {
        let fork = input.fork();
        let _ = fork.parse::<Token![*]>()?;
        let keyword = fork.parse::<Ident>()?;
        if keyword == "opt" {
            let _ = input.parse::<Token![*]>()?;
            let _ = input.parse::<Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            let mut params = Vec::new();
            while !content.is_empty() {
                params.push(recursive_parse_term_param(&content)?);
                if content.peek(Token![,]) {
                    let _ = content.parse::<Token![,]>()?;
                } else {
                    break;
                }
            }
            return Ok(TermParam::Optional { params });
        }
    }

    if input.peek(Token![^]) {
        let _ = input.parse::<Token![^]>()?;
        let is_multi = input.peek(syn::token::Bracket);
        let binder = if is_multi {
            let content;
            syn::bracketed!(content in input);
            content.parse::<Ident>()?
        } else {
            input.parse::<Ident>()?
        };
        let _ = input.parse::<Token![.]>()?;
        let body = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<TypeExpr>()?;
        if is_multi {
            Ok(TermParam::MultiAbstraction { binder, body, ty })
        } else {
            Ok(TermParam::Abstraction { binder, body, ty })
        }
    } else {
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<TypeExpr>()?;
        Ok(TermParam::Simple { name, ty })
    }
}

fn nested_optional_tokens(depth: usize) -> TokenStream {
    let mut tokens: TokenStream = "leaf:PathMap(Proc)".parse().expect("leaf tokens");
    for _ in 0..depth {
        let group = Group::new(Delimiter::Parenthesis, tokens);
        tokens = TokenStream::from_iter([
            TokenTree::Punct(Punct::new('*', Spacing::Alone)),
            TokenTree::Ident(Ident::new("opt", Span::call_site())),
            TokenTree::Group(group),
        ]);
    }
    tokens
}

fn optional_depth(param: &TermParam) -> usize {
    let mut depth = 0;
    let mut param = param;
    loop {
        match param {
            TermParam::Optional { params } => {
                assert_eq!(params.len(), 1);
                depth += 1;
                param = &params[0];
            },
            TermParam::Simple { name, ty } => {
                assert_eq!(name, "leaf");
                assert!(matches!(
                    ty,
                    TypeExpr::Collection { coll_type: CollectionType::PathMap, .. }
                ));
                return depth;
            },
            _ => panic!("expected a nested optional chain ending in one simple parameter"),
        }
    }
}

fn equivalent(left: &TermParam, right: &TermParam) -> bool {
    match (left, right) {
        (
            TermParam::Simple { name: left_name, ty: left_ty },
            TermParam::Simple { name: right_name, ty: right_ty },
        ) => left_name.to_string() == right_name.to_string() && left_ty == right_ty,
        (
            TermParam::Abstraction {
                binder: left_binder,
                body: left_body,
                ty: left_ty,
            },
            TermParam::Abstraction {
                binder: right_binder,
                body: right_body,
                ty: right_ty,
            },
        )
        | (
            TermParam::MultiAbstraction {
                binder: left_binder,
                body: left_body,
                ty: left_ty,
            },
            TermParam::MultiAbstraction {
                binder: right_binder,
                body: right_body,
                ty: right_ty,
            },
        ) => {
            left_binder.to_string() == right_binder.to_string()
                && left_body.to_string() == right_body.to_string()
                && left_ty == right_ty
        },
        (TermParam::GuardBody { name: left_name }, TermParam::GuardBody { name: right_name }) => {
            left_name.to_string() == right_name.to_string()
        },
        (
            TermParam::Optional { params: left_params },
            TermParam::Optional { params: right_params },
        ) => {
            left_params.len() == right_params.len()
                && left_params
                    .iter()
                    .zip(right_params)
                    .all(|(left, right)| equivalent(left, right))
        },
        _ => false,
    }
}

#[test]
fn iterative_term_param_parser_matches_recursive_oracle() {
    let valid = [
        "x:Name",
        "^x.p:[Name -> Proc]",
        "^[xs].p:[Name* -> Proc]",
        "?guard:Guard",
        "*opt()",
        "*opt(x:Name,)",
        "*opt(x:HashMap(Name, Proc), ^y.p:[Name -> Proc], ?g:Guard)",
        "*opt(*opt(x:Name, y:Proc), *opt(?g:Guard, ^[xs].p:[Name* -> Proc]))",
    ];
    for source in valid {
        let actual = parse_term_param(source.parse().expect("valid token stream"))
            .unwrap_or_else(|error| panic!("production parser rejected {source:?}: {error}"));
        let expected = Parser::parse_str(recursive_parse_term_param, source)
            .unwrap_or_else(|error| panic!("oracle rejected {source:?}: {error}"));
        assert!(equivalent(&actual, &expected), "source {source:?}");
    }

    for source in ["?g:Proc", "*opt(,x:Name)", "*opt(x:Name,,y:Proc)", "*other(x:Name)"] {
        assert_eq!(
            parse_term_param(source.parse().expect("lexically valid error fixture")).is_err(),
            Parser::parse_str(recursive_parse_term_param, source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

#[test]
fn deeply_nested_optional_params_parse_and_drop_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("term-param-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let tokens = nested_optional_tokens(DEPTH);
            let parsed = parse_term_param(tokens).expect("deep optional parameter must parse");
            assert_eq!(optional_depth(&parsed), DEPTH);
            drop(parsed);
        })
        .expect("small-stack term-parameter parser thread must spawn");
    handle
        .join()
        .expect("term-parameter PDA must not overflow the native stack");
}
