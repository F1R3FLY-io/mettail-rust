//! Original guest-mode nested-opener derivation over borrowed source objects.
//!
//! Token-name matching against the opener, mode-name equality, and output name
//! rendering remain separate observations. `GuestModeDescriptorProjection.v`
//! proves their pure source-field substitution, not arbitrary callback effects
//! or a correspondence inferred from qualified names in a lowered lexer image.

/// Execute the original first-token / first-mode / same-push iterator chains.
///
/// Readers must expose the same stable source observations. The first matching
/// token is chosen before its optional push is inspected, so a missing push
/// does not continue searching later duplicate token names. Mode comparison
/// uses original name equality; returned token names preserve order and duplicates.
/// No lexer graph or Rust syntax tree is rebuilt by this function.
#[allow(clippy::too_many_arguments)]
pub fn guest_body_nested_open_kinds<'source, T, M, N: PartialEq + ?Sized + 'source>(
    token_defs: &'source [T],
    mode_defs: &'source [M],
    open_kind: &str,
    token_name_matches: impl Fn(&T, &str) -> bool,
    token_push: impl Fn(&'source T) -> Option<&'source N>,
    mode_name: impl Fn(&'source M) -> &'source N,
    mode_tokens: impl Fn(&'source M) -> &'source [T],
    token_name: impl Fn(&T) -> String,
) -> Vec<String> {
    let Some(region_mode) = token_defs
        .iter()
        .find(|token| token_name_matches(token, open_kind))
        .and_then(&token_push)
    else {
        return Vec::new();
    };
    let Some(mode) = mode_defs.iter().find(|mode| mode_name(mode) == region_mode) else {
        return Vec::new();
    };
    mode_tokens(mode)
        .iter()
        .filter(|token| token_push(token) == Some(region_mode))
        .map(token_name)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::guest_body_nested_open_kinds;

    struct Name {
        spelling: &'static str,
        class: u8,
    }

    impl PartialEq for Name {
        fn eq(&self, other: &Self) -> bool {
            self.class == other.class
        }
    }

    struct Token {
        name: &'static str,
        push: Option<Name>,
    }

    struct Mode {
        name: Name,
        tokens: Vec<Token>,
    }

    #[test]
    fn owned_guest_names_keep_source_equality_separate_from_spelling() {
        let tokens = [Token {
            name: "Open",
            push: Some(Name { spelling: "Guest", class: 1 }),
        }];
        let modes = [
            Mode {
                name: Name { spelling: "Guest", class: 2 },
                tokens: vec![Token {
                    name: "WrongMode",
                    push: Some(Name { spelling: "Guest", class: 1 }),
                }],
            },
            Mode {
                name: Name { spelling: "Alias", class: 1 },
                tokens: vec![
                    Token {
                        name: "Kept",
                        push: Some(Name { spelling: "Different", class: 1 }),
                    },
                    Token {
                        name: "WrongPush",
                        push: Some(Name { spelling: "Guest", class: 2 }),
                    },
                    Token {
                        name: "Kept",
                        push: Some(Name { spelling: "Guest", class: 1 }),
                    },
                ],
            },
        ];
        assert_eq!(
            modes[0].name.spelling,
            tokens[0].push.as_ref().expect("declared push").spelling
        );
        assert_ne!(modes[1].name.spelling, modes[0].name.spelling);
        let output = guest_body_nested_open_kinds(
            &tokens,
            &modes,
            "Open",
            |token, open| token.name == open,
            |token| token.push.as_ref(),
            |mode| &mode.name,
            |mode| &mode.tokens,
            |token| token.name.to_owned(),
        );
        assert_eq!(output, ["Kept", "Kept"]);
    }
}
