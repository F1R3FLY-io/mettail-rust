use super::*;
use proc_macro2::{Delimiter, Group, Punct, Spacing, TokenTree};
use syn::parse::Parser;

fn recursive_parse_implies(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut left = recursive_parse_or(input)?;
    while input.peek(Token![=>]) {
        input.parse::<Token![=>]>()?;
        let right = recursive_parse_or(input)?;
        left = RefinementPredicate::Implies(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn recursive_parse_or(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut left = recursive_parse_and(input)?;
    while input.peek(Token![||]) {
        input.parse::<Token![||]>()?;
        let right = recursive_parse_and(input)?;
        left = RefinementPredicate::Or(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn recursive_parse_and(input: ParseStream) -> SynResult<RefinementPredicate> {
    let mut left = recursive_parse_not(input)?;
    while input.peek(Token![&&]) {
        input.parse::<Token![&&]>()?;
        let right = recursive_parse_not(input)?;
        left = RefinementPredicate::And(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn recursive_parse_not(input: ParseStream) -> SynResult<RefinementPredicate> {
    if input.peek(Token![~]) {
        input.parse::<Token![~]>()?;
        Ok(RefinementPredicate::Not(Box::new(recursive_parse_not(input)?)))
    } else if input.peek(Token![!]) && !input.peek(Token![!=]) {
        input.parse::<Token![!]>()?;
        Ok(RefinementPredicate::Not(Box::new(recursive_parse_not(input)?)))
    } else {
        recursive_parse_atom(input)
    }
}

fn recursive_parse_linear_rhs(input: ParseStream) -> SynResult<i64> {
    let negative = if input.peek(Token![-]) {
        input.parse::<Token![-]>()?;
        true
    } else {
        false
    };
    let value = input.parse::<syn::LitInt>()?.base10_parse::<i64>()?;
    Ok(if negative { -value } else { value })
}

fn recursive_parse_atom(input: ParseStream) -> SynResult<RefinementPredicate> {
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        return recursive_parse_implies(&content);
    }

    let fork = input.fork();
    let ident: Ident = fork.parse()?;
    let ident_text = ident.to_string();
    if ident_text == "forall" || ident_text == "exists" {
        input.parse::<Ident>()?;
        let quantifier = if ident_text == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let bound = if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            let content;
            syn::braced!(content in input);
            let key = content.parse::<Ident>()?;
            if key != "k" {
                return Err(syn::Error::new(key.span(), "expected 'k'"));
            }
            content.parse::<Token![=]>()?;
            Some(content.parse::<syn::LitInt>()?.base10_parse::<usize>()?)
        } else {
            None
        };
        let var = input.parse::<Ident>()?;
        let domain = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "in" {
                input.parse::<Ident>()?;
                Some(input.parse::<Ident>()?)
            } else {
                None
            }
        } else {
            None
        };
        input.parse::<Token![.]>()?;
        let body = recursive_parse_atom(input)?;
        return Ok(RefinementPredicate::Quantified {
            quantifier,
            var,
            domain,
            bound,
            body: Box::new(body),
        });
    }

    if fork.peek(syn::token::Paren) {
        input.parse::<Ident>()?;
        let content;
        syn::parenthesized!(content in input);
        let mut args = Vec::new();
        while !content.is_empty() {
            args.push(refinement_pred_arg(content.parse::<Ident>()?));
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
            }
        }
        return Ok(RefinementPredicate::Relation { name: ident, args, negated: false });
    }

    input.parse::<Ident>()?;
    let linear = if input.peek(Token![>]) && input.peek2(Token![=]) {
        input.parse::<Token![>]>()?;
        input.parse::<Token![=]>()?;
        Some(LinearRelation::Ge)
    } else if input.peek(Token![>]) {
        input.parse::<Token![>]>()?;
        Some(LinearRelation::Gt)
    } else if input.peek(Token![<]) && input.peek2(Token![=]) {
        input.parse::<Token![<]>()?;
        input.parse::<Token![=]>()?;
        Some(LinearRelation::Le)
    } else if input.peek(Token![<]) {
        input.parse::<Token![<]>()?;
        Some(LinearRelation::Lt)
    } else {
        None
    };
    if let Some(relation) = linear {
        return Ok(RefinementPredicate::Linear {
            terms: vec![(ident, 1)],
            relation,
            rhs: recursive_parse_linear_rhs(input)?,
        });
    }

    let equality = if input.peek(Token![==]) {
        input.parse::<Token![==]>()?;
        Some(true)
    } else if input.peek(Token![!=]) {
        input.parse::<Token![!=]>()?;
        Some(false)
    } else {
        None
    };
    if let Some(is_equal) = equality {
        if input.peek(syn::LitInt) {
            return Ok(RefinementPredicate::Linear {
                terms: vec![(ident, 1)],
                relation: if is_equal {
                    LinearRelation::Eq
                } else {
                    LinearRelation::Neq
                },
                rhs: recursive_parse_linear_rhs(input)?,
            });
        }
        let right = refinement_pred_arg(input.parse::<Ident>()?);
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

fn parse_new(source: &str) -> SynResult<RefinementPredicate> {
    Parser::parse_str(
        |input: ParseStream| {
            let tokens = input.parse::<TokenStream>()?;
            parse_refinement_predicate_tokens(tokens)
        },
        source,
    )
}

fn parse_recursive(source: &str) -> SynResult<RefinementPredicate> {
    Parser::parse_str(recursive_parse_implies, source)
}

#[test]
fn refinement_parser_pda_matches_the_recursive_oracle() {
    let fixtures = [
        "x > 0",
        "x >= -7",
        "x < 9 && reachable(x, Root) || x != Nil => safe(x)",
        "x => y => z",
        "~~~blocked(x)",
        "forall _{k=12} x. (reachable(x, Root) => safe(x))",
        "exists x. forall y. (reachable(x, y) && x == y)",
        "((x > 0)) && (!(blocked(x) || failed(x)))",
        "relation_without_arguments",
    ];
    for source in fixtures {
        let actual = parse_new(source)
            .unwrap_or_else(|error| panic!("PDA fixture {source:?} must parse: {error}"));
        let expected = parse_recursive(source).unwrap_or_else(|error| {
            panic!("recursive oracle fixture {source:?} must parse: {error}")
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"), "fixture {source:?}");
    }

    let fixed_domain = parse_new("forall x in nodes. reachable(x, Root)")
        .expect("the PDA accepts the documented quantifier-domain syntax");
    assert!(matches!(
        fixed_domain,
        RefinementPredicate::Quantified { domain: Some(ref domain), .. } if domain == "nodes"
    ));
    assert!(
        parse_recursive("forall x in nodes. reachable(x, Root)").is_err(),
        "the old recursive parser incorrectly treated the `in` keyword as a non-identifier",
    );

    for source in ["", "x &&", "forall x. !blocked(x)", "(x > 0", "x == -1"] {
        assert_eq!(
            parse_new(source).is_err(),
            parse_recursive(source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

fn flat_negation_tokens(depth: usize) -> TokenStream {
    let mut tokens = TokenStream::new();
    for _ in 0..depth {
        tokens.extend(std::iter::once(TokenTree::Punct(Punct::new('~', Spacing::Alone))));
    }
    tokens.extend("x > 0".parse::<TokenStream>().expect("leaf tokens"));
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
    tokens.extend("x > 0".parse::<TokenStream>().expect("leaf tokens"));
    tokens
}

fn parenthesized_tokens(depth: usize) -> TokenStream {
    let mut tokens = "x > 0".parse::<TokenStream>().expect("leaf tokens");
    for _ in 0..depth {
        tokens = TokenStream::from(TokenTree::Group(Group::new(Delimiter::Parenthesis, tokens)));
    }
    tokens
}

#[test]
fn refinement_parser_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("refinement-parser-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            for tokens in [
                flat_negation_tokens(DEPTH),
                quantified_tokens(DEPTH),
                parenthesized_tokens(DEPTH),
            ] {
                let predicate = parse_refinement_predicate_tokens(tokens)
                    .expect("deep refinement predicate must parse");
                drop(predicate);
            }
        })
        .expect("small-stack refinement parser thread must spawn")
        .join()
        .expect("refinement parser PDA must not overflow the native stack");
}
