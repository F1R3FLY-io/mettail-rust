use proc_macro2::{TokenStream, TokenTree};

/// Owned depth-first, left-to-right traversal over the non-group leaves of a
/// token stream. Nested groups contribute their contents but are structural and
/// are not yielded themselves.
pub(crate) struct TokenTreeLeaves {
    streams: Vec<proc_macro2::token_stream::IntoIter>,
}

impl TokenTreeLeaves {
    pub(crate) fn new(tokens: TokenStream) -> Self {
        Self { streams: vec![tokens.into_iter()] }
    }
}

impl Iterator for TokenTreeLeaves {
    type Item = TokenTree;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(stream) = self.streams.last_mut() {
            match stream.next() {
                Some(TokenTree::Group(group)) => self.streams.push(group.stream().into_iter()),
                Some(leaf) => return Some(leaf),
                None => {
                    self.streams.pop();
                },
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "../../tests/support/token_tree_walk_recursive_oracle.rs"]
mod recursive_oracle;
