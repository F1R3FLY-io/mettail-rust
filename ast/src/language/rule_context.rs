use super::RuleContextType;
use crate::types::TypeExpr;
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use syn::{
    parse::{discouraged::Speculative, Parse, ParseStream, Parser},
    Ident, Result, Token,
};

impl Parse for RuleContextType {
    fn parse(input: ParseStream) -> Result<Self> {
        let ordinary = input.fork();
        let ordinary_error = match ordinary.parse::<TypeExpr>() {
            Ok(ty) => {
                input.advance_to(&ordinary);
                return Ok(Self::Ordinary(ty));
            },
            Err(error) => error,
        };
        let family = input.fork();
        match parse_family(&family)? {
            Some(ty) => {
                input.advance_to(&family);
                Ok(ty)
            },
            None => Err(ordinary_error),
        }
    }
}

fn parse_family(input: ParseStream) -> Result<Option<RuleContextType>> {
    let mut tokens = if input.peek(syn::token::Bracket) {
        TokenStream::from(input.parse::<TokenTree>()?)
    } else if input.peek(Ident) && input.peek2(syn::token::Paren) {
        let name = input.parse::<Ident>()?;
        if name != "Rewrite" {
            return Ok(None);
        }
        let group = input.parse::<TokenTree>()?;
        [TokenTree::Ident(name), group].into_iter().collect()
    } else {
        return Ok(None);
    };
    let mut domains = Vec::new();
    loop {
        let parts = tokens.into_iter().collect::<Vec<_>>();
        match parts.as_slice() {
            [TokenTree::Ident(name), TokenTree::Group(group)]
                if name == "Rewrite" && group.delimiter() == Delimiter::Parenthesis =>
            {
                let result = syn::parse2::<TypeExpr>(group.stream())?;
                return Ok(Some(RuleContextType::RewriteFamily { domains, result }));
            },
            [TokenTree::Group(group)] if group.delimiter() == Delimiter::Bracket => {
                let arrow = |input: ParseStream| {
                    let domain = input.parse::<TypeExpr>()?;
                    input.parse::<Token![->]>()?;
                    Ok((domain, input.parse::<TokenStream>()?))
                };
                let Ok((domain, codomain)) = arrow.parse2(group.stream()) else {
                    return Ok(None);
                };
                domains.push(domain);
                tokens = codomain;
            },
            _ => return Ok(None),
        }
    }
}
