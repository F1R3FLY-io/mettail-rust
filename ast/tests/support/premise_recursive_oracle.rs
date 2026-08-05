use super::*;
use crate::identity::premises_identity;
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use syn::parse::Parser;

fn recursive_parse_premise(input: ParseStream) -> SynResult<Premise> {
    let first = input.parse::<Ident>()?;
    if input.peek(Token![#]) {
        let _ = input.parse::<Token![#]>()?;
        let term = if input.peek(Token![...]) {
            let _ = input.parse::<Token![...]>()?;
            FreshnessTarget::CollectionRest(input.parse::<Ident>()?)
        } else {
            FreshnessTarget::Var(input.parse::<Ident>()?)
        };
        Ok(Premise::Freshness(FreshnessCondition { var: first, term }))
    } else if input.peek(Token![~]) && input.peek2(Token![/]) {
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![/]>()?;
        let _ = input.parse::<Token![>]>()?;
        Ok(Premise::CongruenceWithheld { source: first, target: input.parse()? })
    } else if input.peek(Token![~]) && input.peek2(Token![>]) {
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![>]>()?;
        Ok(Premise::Congruence { source: first, target: input.parse()? })
    } else if input.peek(syn::token::Paren) {
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
        let _ = input.parse::<Token![.]>()?;
        let _ = input.parse::<Token![*]>()?;
        let operator = input.parse::<Ident>()?;
        if operator != "map" {
            return Err(syn::Error::new(
                operator.span(),
                "expected 'map' in quantified premise (xs.*map(|x| ...))",
            ));
        }
        let content;
        syn::parenthesized!(content in input);
        let _ = content.parse::<Token![|]>()?;
        let param = content.parse::<Ident>()?;
        let _ = content.parse::<Token![|]>()?;
        let body = recursive_parse_premise(&content)?;
        Ok(Premise::ForAll {
            collection: first,
            param,
            body: Box::new(body),
        })
    } else {
        Err(syn::Error::new(first.span(), "expected premise"))
    }
}

fn nested_forall_source(depth: usize) -> String {
    let mut source = "x # target".to_string();
    for level in 0..depth {
        source = format!("items{level}.*map(|item{level}| {source})");
    }
    source
}

fn nested_forall_tokens(depth: usize) -> TokenStream {
    let mut body: TokenStream = "x # target".parse().expect("leaf premise tokens");
    for _ in 0..depth {
        let closure = TokenStream::from_iter(
            [
                TokenTree::Punct(Punct::new('|', Spacing::Alone)),
                TokenTree::Ident(Ident::new("item", Span::call_site())),
                TokenTree::Punct(Punct::new('|', Spacing::Alone)),
            ]
            .into_iter()
            .chain(body),
        );
        body = TokenStream::from_iter([
            TokenTree::Ident(Ident::new("items", Span::call_site())),
            TokenTree::Punct(Punct::new('.', Spacing::Alone)),
            TokenTree::Punct(Punct::new('*', Spacing::Alone)),
            TokenTree::Ident(Ident::new("map", Span::call_site())),
            TokenTree::Group(Group::new(Delimiter::Parenthesis, closure)),
        ]);
    }
    body
}

fn forall_depth(premise: &Premise) -> usize {
    let mut depth = 0;
    let mut premise = premise;
    loop {
        match premise {
            Premise::ForAll { body, .. } => {
                depth += 1;
                premise = body;
            },
            Premise::Freshness(_) => return depth,
            _ => panic!("expected nested ForAll nodes ending in freshness"),
        }
    }
}

#[test]
fn iterative_premise_parser_matches_recursive_oracle() {
    let mut fixtures = vec![
        "x # target".to_string(),
        "x # ...rest".to_string(),
        "source ~> target".to_string(),
        "source ~/> target".to_string(),
        "reachable(x, Root)".to_string(),
    ];
    fixtures.extend((0..64).map(nested_forall_source));

    for source in fixtures {
        let actual = parse_premise_tokens(source.parse().expect("fixture tokenization"))
            .unwrap_or_else(|error| panic!("production rejected {source:?}: {error}"));
        let expected = Parser::parse_str(recursive_parse_premise, &source)
            .unwrap_or_else(|error| panic!("oracle rejected {source:?}: {error}"));
        assert_eq!(
            premises_identity(std::slice::from_ref(&actual)),
            premises_identity(std::slice::from_ref(&expected)),
            "source {source:?}",
        );
    }

    for source in ["items.*zip(|x| x # y)", "items.*map(x # y)", "items.*map(|x|)"] {
        assert_eq!(
            parse_premise_tokens(source.parse().expect("error fixture tokenization")).is_err(),
            Parser::parse_str(recursive_parse_premise, source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

#[test]
fn guard_syntax_reaches_the_behavioral_predicate_parser() {
    let premise = parse_premise_tokens(
        "guard(reachable(x, Root) && safe(x))"
            .parse()
            .expect("guard tokenization"),
    )
    .expect("guard premise must parse as a behavioral predicate");
    assert!(matches!(premise, Premise::BehavioralGuard(BehavioralPred::And(_, _))));
}

#[test]
fn deeply_nested_forall_premises_parse_and_drop_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("premise-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let premise = parse_premise_tokens(nested_forall_tokens(DEPTH))
                .expect("deep quantified premise must parse");
            assert_eq!(forall_depth(&premise), DEPTH);
            drop(premise);
        })
        .expect("small-stack premise parser thread must spawn");
    handle
        .join()
        .expect("premise PDA must not overflow the native stack");
}
