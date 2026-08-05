use super::*;
use proc_macro2::{Delimiter, Group, TokenTree};
use syn::parse::Parser;

fn recursive_expr(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    let left = recursive_atom(input)?;
    if input.peek(Ident) {
        let lookahead = input.fork().parse::<Ident>()?;
        match lookahead.to_string().as_str() {
            "and" | "∧" => {
                input.parse::<Ident>()?;
                let right = recursive_expr(input)?;
                return Ok(TreeConstraintExpr::And(Box::new(left), Box::new(right)));
            },
            "or" | "∨" => {
                input.parse::<Ident>()?;
                let right = recursive_expr(input)?;
                return Ok(TreeConstraintExpr::Or(Box::new(left), Box::new(right)));
            },
            _ => {},
        }
    }
    Ok(left)
}

fn recursive_atom(input: ParseStream) -> SynResult<TreeConstraintExpr> {
    if input.peek(Ident) {
        let lookahead = input.fork().parse::<Ident>()?;
        let keyword = lookahead.to_string();
        return match keyword.as_str() {
            "forall" | "∀" => {
                input.parse::<Ident>()?;
                let next = input.fork().parse::<Ident>()?;
                let next_text = next.to_string();
                let symbol = if next_text == "children" {
                    input.parse::<Ident>()?;
                    let of = input.parse::<Ident>()?;
                    if of != "of" {
                        return Err(syn::Error::new(of.span(), "expected 'of' after 'children'"));
                    }
                    input.parse::<Ident>()?.to_string()
                } else if next_text == "↓" {
                    input.parse::<Ident>()?;
                    input.parse::<Ident>()?.to_string()
                } else {
                    input.parse::<Ident>()?;
                    next_text
                };
                let content;
                syn::braced!(content in input);
                Ok(TreeConstraintExpr::ForallChildren {
                    symbol,
                    body: Box::new(recursive_expr(&content)?),
                })
            },
            "exists" | "∃" => {
                input.parse::<Ident>()?;
                let child = input.parse::<Ident>()?;
                if child != "child" {
                    return Err(syn::Error::new(
                        child.span(),
                        "expected 'child' after 'exists'/'∃'",
                    ));
                }
                Ok(TreeConstraintExpr::ExistsChild)
            },
            "not" | "¬" => {
                input.parse::<Ident>()?;
                Ok(TreeConstraintExpr::Not(Box::new(recursive_atom(input)?)))
            },
            "match" | "∈" => {
                input.parse::<Ident>()?;
                let content;
                syn::braced!(content in input);
                let mut symbols = Vec::new();
                while !content.is_empty() {
                    symbols.push(content.parse::<Ident>()?.to_string());
                    if content.peek(Token![|]) {
                        content.parse::<Token![|]>()?;
                    }
                }
                Ok(TreeConstraintExpr::Match(symbols))
            },
            _ => {
                input.parse::<Ident>()?;
                Ok(TreeConstraintExpr::Atom(keyword))
            },
        };
    }
    if input.peek(syn::token::Paren) {
        let content;
        syn::parenthesized!(content in input);
        recursive_expr(&content)
    } else {
        Err(input.error("expected tree constraint expression"))
    }
}

fn parse_new(source: &str) -> SynResult<TreeConstraintExpr> {
    Parser::parse_str(
        |input: ParseStream| {
            let tokens = input.parse::<TokenStream>()?;
            parse_tree_constraint_tokens(tokens)
        },
        source,
    )
}

fn parse_recursive(source: &str) -> SynResult<TreeConstraintExpr> {
    Parser::parse_str(recursive_expr, source)
}

#[test]
fn tree_constraint_parser_pda_matches_the_recursive_oracle() {
    let fixtures = [
        "Leaf",
        "exists child",
        "not not Leaf",
        "forall children of Branch { not Bad }",
        "forall Branch { exists child }",
        "a and b or c and d",
        "(a or b) and not c",
    ];
    for source in fixtures {
        let actual = parse_new(source)
            .unwrap_or_else(|error| panic!("PDA fixture {source:?} must parse: {error}"));
        let expected = parse_recursive(source).unwrap_or_else(|error| {
            panic!("recursive oracle fixture {source:?} must parse: {error}")
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"), "fixture {source:?}");
    }
    let fixed_match = parse_new("match { Leaf | Nil | Branch }")
        .expect("the PDA accepts the documented match expression");
    assert!(matches!(
        fixed_match,
        TreeConstraintExpr::Match(ref symbols)
            if symbols == &["Leaf".to_owned(), "Nil".to_owned(), "Branch".to_owned()]
    ));
    assert!(
        parse_recursive("match { Leaf | Nil | Branch }").is_err(),
        "the old recursive parser incorrectly rejected the Rust keyword `match` before dispatch",
    );
    for source in ["", "a and", "exists sibling", "forall children Branch { a }", "(a"] {
        assert_eq!(
            parse_new(source).is_err(),
            parse_recursive(source).is_err(),
            "error acceptance diverged for {source:?}",
        );
    }
}

fn binary_tokens(depth: usize) -> TokenStream {
    let mut tokens = TokenStream::new();
    for _ in 0..depth {
        tokens.extend("a and".parse::<TokenStream>().expect("binary tokens"));
    }
    tokens.extend("z".parse::<TokenStream>().expect("leaf tokens"));
    tokens
}

fn negation_tokens(depth: usize) -> TokenStream {
    let mut tokens = TokenStream::new();
    for _ in 0..depth {
        tokens.extend("not".parse::<TokenStream>().expect("negation token"));
    }
    tokens.extend("leaf".parse::<TokenStream>().expect("leaf token"));
    tokens
}

fn forall_tokens(depth: usize) -> TokenStream {
    let mut tokens = "leaf".parse::<TokenStream>().expect("leaf token");
    for _ in 0..depth {
        let mut outer = "forall Branch"
            .parse::<TokenStream>()
            .expect("forall header tokens");
        outer.extend(std::iter::once(TokenTree::Group(Group::new(Delimiter::Brace, tokens))));
        tokens = outer;
    }
    tokens
}

fn parenthesized_tokens(depth: usize) -> TokenStream {
    let mut tokens = "leaf".parse::<TokenStream>().expect("leaf token");
    for _ in 0..depth {
        tokens = TokenStream::from(TokenTree::Group(Group::new(Delimiter::Parenthesis, tokens)));
    }
    tokens
}

#[test]
fn tree_constraint_parser_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("tree-constraint-parser-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            for tokens in [
                binary_tokens(DEPTH),
                negation_tokens(DEPTH),
                forall_tokens(DEPTH),
                parenthesized_tokens(DEPTH),
            ] {
                let expression =
                    parse_tree_constraint_tokens(tokens).expect("deep tree constraint must parse");
                drop(expression);
            }
        })
        .expect("small-stack tree-constraint parser thread must spawn")
        .join()
        .expect("tree-constraint parser PDA must not overflow the native stack");
}
