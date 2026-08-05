use super::*;
use proc_macro2::{Delimiter, Group, TokenTree};
use syn::parse::Parser;

fn recursive_parse(input: ParseStream) -> SynResult<BehavioralPred> {
    let result = recursive_implies(input)?;
    recursive_check_conn02(input)?;
    Ok(result)
}

fn recursive_try_consume_role_keyword(input: ParseStream, role: ConnectiveRole) -> bool {
    if !has_active_connective_map() || !active_role_available(&role) || !input.peek(Ident::peek_any)
    {
        return false;
    }
    let fork = input.fork();
    if let Ok(identifier) = fork.parse::<Ident>() {
        if active_role_of(&identifier.to_string()).as_ref() == Some(&role) {
            let _ = input.parse::<Ident>();
            return true;
        }
    }
    false
}

fn recursive_check_conn02(input: ParseStream) -> SynResult<()> {
    if !has_active_connective_map() {
        return Ok(());
    }
    for (present, role, token) in [
        (input.peek(Token![&&]), ConnectiveRole::And, "&&"),
        (input.peek(Token![||]), ConnectiveRole::Or, "||"),
        (input.peek(Token![~]), ConnectiveRole::Not, "~"),
        (input.peek(Token![!]), ConnectiveRole::Not, "!"),
        (input.peek(Token![=>]), ConnectiveRole::Entails, "=>"),
    ] {
        if present && !active_role_available(&role) {
            return Err(syn::Error::new(
                input.span(),
                format!(
                    "CONN02: connective token `{token}` is not declared in the active `connectives {{}}` block"
                ),
            ));
        }
    }
    Ok(())
}

fn recursive_implies(input: ParseStream) -> SynResult<BehavioralPred> {
    let left = recursive_or(input)?;
    if input.peek(Token![=>]) && rust_token_allowed(ConnectiveRole::Entails) {
        input.parse::<Token![=>]>()?;
        let right = recursive_implies(input)?;
        return Ok(BehavioralPred::Implies(Box::new(left), Box::new(right)));
    }
    if recursive_try_consume_role_keyword(input, ConnectiveRole::Entails) {
        let right = recursive_implies(input)?;
        return Ok(BehavioralPred::Implies(Box::new(left), Box::new(right)));
    }
    if recursive_try_consume_role_keyword(input, ConnectiveRole::ImpliedBy) {
        let right = recursive_implies(input)?;
        return Ok(BehavioralPred::Implies(Box::new(right), Box::new(left)));
    }
    if recursive_try_consume_role_keyword(input, ConnectiveRole::Iff) {
        let right = recursive_implies(input)?;
        let forward = BehavioralPred::Implies(Box::new(left.clone()), Box::new(right.clone()));
        let backward = BehavioralPred::Implies(Box::new(right), Box::new(left));
        return Ok(BehavioralPred::And(Box::new(forward), Box::new(backward)));
    }
    Ok(left)
}

fn recursive_or(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = recursive_and(input)?;
    loop {
        if input.peek(Token![||]) && rust_token_allowed(ConnectiveRole::Or) {
            input.parse::<Token![||]>()?;
        } else if recursive_try_consume_role_keyword(input, ConnectiveRole::Or) {
        } else {
            break;
        }
        let right = recursive_and(input)?;
        result = BehavioralPred::Or(Box::new(result), Box::new(right));
    }
    Ok(result)
}

fn recursive_and(input: ParseStream) -> SynResult<BehavioralPred> {
    let mut result = recursive_not(input)?;
    loop {
        if input.peek(Token![&&]) && rust_token_allowed(ConnectiveRole::And) {
            input.parse::<Token![&&]>()?;
        } else if recursive_try_consume_role_keyword(input, ConnectiveRole::And) {
        } else {
            break;
        }
        let right = recursive_not(input)?;
        result = BehavioralPred::And(Box::new(result), Box::new(right));
    }
    Ok(result)
}

fn recursive_not(input: ParseStream) -> SynResult<BehavioralPred> {
    if input.peek(Token![~]) && rust_token_allowed(ConnectiveRole::Not) {
        input.parse::<Token![~]>()?;
        Ok(BehavioralPred::Not(Box::new(recursive_atom(input)?)))
    } else if input.peek(Token![!]) && rust_token_allowed(ConnectiveRole::Not) {
        input.parse::<Token![!]>()?;
        Ok(BehavioralPred::Not(Box::new(recursive_atom(input)?)))
    } else if recursive_try_consume_role_keyword(input, ConnectiveRole::Not) {
        Ok(BehavioralPred::Not(Box::new(recursive_atom(input)?)))
    } else {
        recursive_atom(input)
    }
}

fn recursive_atom(input: ParseStream) -> SynResult<BehavioralPred> {
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        return recursive_parse(&content);
    }
    let ident = input.parse::<Ident>()?;
    if ident == "ac_match" {
        let content;
        syn::parenthesized!(content in input);
        let bag = content.parse::<Ident>()?;
        content.parse::<Token![,]>()?;
        let set;
        syn::braced!(set in content);
        let mut elements = Vec::new();
        let mut rest = None;
        while !set.is_empty() {
            if set.peek(Token![...]) {
                set.parse::<Token![...]>()?;
                rest = Some(set.parse::<Ident>()?);
                if set.peek(Token![,]) {
                    set.parse::<Token![,]>()?;
                }
                break;
            }
            elements.push(set.parse::<Ident>()?);
            if set.peek(Token![,]) {
                set.parse::<Token![,]>()?;
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
    if ident == "forall" || ident == "exists" {
        let quantifier = if ident == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let var = input.parse::<Ident>()?;
        let bound = if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            let content;
            syn::braced!(content in input);
            let _key = content.parse::<Ident>()?;
            content.parse::<Token![=]>()?;
            Some(content.parse::<syn::LitInt>()?.base10_parse::<usize>()?)
        } else {
            None
        };
        let domain = if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            Some(input.parse::<Ident>()?)
        } else {
            None
        };
        input.parse::<Token![.]>()?;
        let body = recursive_parse(input)?;
        return Ok(BehavioralPred::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        let mut args = Vec::new();
        while !content.is_empty() {
            args.push(refinement_pred_arg(content.parse::<Ident>()?));
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
            }
        }
        return Ok(BehavioralPred::RelationQuery {
            relation_name: ident,
            args,
            negated: false,
        });
    }
    Ok(BehavioralPred::RelationQuery {
        relation_name: ident,
        args: Vec::new(),
        negated: false,
    })
}

fn parse_new(source: &str) -> SynResult<BehavioralPred> {
    Parser::parse_str(
        |input: ParseStream| {
            let tokens = input.parse::<TokenStream>()?;
            parse_behavioral_predicate_tokens(tokens)
        },
        source,
    )
}

fn parse_recursive(source: &str) -> SynResult<BehavioralPred> {
    Parser::parse_str(recursive_parse, source)
}

#[test]
fn behavioral_parser_pda_matches_the_recursive_oracle() {
    let fixtures = [
        "reachable(x, Root)",
        "reachable(x, Root) && safe(x) || permitted(x)",
        "a => b => c",
        "~blocked(x)",
        "forall x _{k=11} in nodes. (reachable(x, Root) => safe(x))",
        "exists x. forall y in nodes. reachable(x, y) && safe(y)",
        "(a || b) && !(c => d)",
        "ac_match(messages, {head, tail, ...rest})",
        "nullary",
    ];
    for source in fixtures {
        let actual = parse_new(source)
            .unwrap_or_else(|error| panic!("PDA fixture {source:?} must parse: {error}"));
        let expected = parse_recursive(source).unwrap_or_else(|error| {
            panic!("recursive oracle fixture {source:?} must parse: {error}")
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"), "fixture {source:?}");
    }
    for source in ["", "a &&", "~~a", "ac_match(xs, {...rest})", "(a"] {
        assert_eq!(
            parse_new(source).is_err(),
            parse_recursive(source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

fn implication_tokens(depth: usize) -> TokenStream {
    let mut tokens = TokenStream::new();
    for _ in 0..depth {
        tokens.extend("a =>".parse::<TokenStream>().expect("implication tokens"));
    }
    tokens.extend("z".parse::<TokenStream>().expect("leaf tokens"));
    tokens
}

fn quantified_tokens(depth: usize) -> TokenStream {
    let mut tokens = TokenStream::new();
    for _ in 0..depth {
        tokens.extend(
            "forall x ."
                .parse::<TokenStream>()
                .expect("quantifier tokens"),
        );
    }
    tokens.extend("leaf".parse::<TokenStream>().expect("leaf tokens"));
    tokens
}

fn parenthesized_tokens(depth: usize) -> TokenStream {
    let mut tokens = "leaf".parse::<TokenStream>().expect("leaf tokens");
    for _ in 0..depth {
        tokens = TokenStream::from(TokenTree::Group(Group::new(Delimiter::Parenthesis, tokens)));
    }
    tokens
}

#[test]
fn behavioral_parser_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("behavioral-parser-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            for tokens in
                [implication_tokens(DEPTH), quantified_tokens(DEPTH), parenthesized_tokens(DEPTH)]
            {
                let predicate = parse_behavioral_predicate_tokens(tokens)
                    .expect("deep behavioral predicate must parse");
                drop(predicate);
            }
        })
        .expect("small-stack behavioral parser thread must spawn")
        .join()
        .expect("behavioral parser PDA must not overflow the native stack");
}
