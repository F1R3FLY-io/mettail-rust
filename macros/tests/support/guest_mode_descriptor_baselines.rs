//! Original guest-mode lookup snapshots, frozen before sharing its implementation.
use super::guest_body_nested_open_kinds;
use mettail_ast::language::{LanguageDef, ModeDef, TokenDef};
use proc_macro2::Span;
use syn::Ident;

fn ident(value: &str) -> Ident {
    Ident::new(value, Span::call_site())
}

fn token(name: &str, push: Option<&str>) -> TokenDef {
    TokenDef {
        name: ident(name),
        pattern: String::new(),
        category: None,
        rust_code: None,
        priority: None,
        push_mode: push.map(ident),
        is_pop: false,
        stream: None,
        from_literals: false,
    }
}

fn mode(name: &str, tokens: Vec<TokenDef>) -> ModeDef {
    ModeDef {
        name: ident(name),
        token_defs: tokens,
        raw: false,
    }
}

fn language(tokens: Vec<TokenDef>, modes: Vec<ModeDef>) -> LanguageDef {
    let mut source = crate::gen::empty_language_for_tests();
    source.token_defs = tokens;
    source.mode_defs = modes;
    source
}

#[test]
fn original_guest_missing_opener_push_or_mode_returns_empty() {
    let cases = [
        language(vec![], vec![]),
        language(vec![token("Other", Some("Guest"))], vec![mode("Guest", vec![])]),
        language(vec![token("Open", None)], vec![mode("Guest", vec![])]),
        language(vec![token("Open", Some("Missing"))], vec![mode("Guest", vec![])]),
    ];
    for source in &cases {
        assert!(guest_body_nested_open_kinds(source, "Open").is_empty());
    }
}

#[test]
fn original_guest_first_opener_without_push_does_not_search_later_duplicates() {
    let source = language(
        vec![token("Open", None), token("Open", Some("Guest"))],
        vec![mode("Guest", vec![token("Nested", Some("Guest"))])],
    );
    assert!(guest_body_nested_open_kinds(&source, "Open").is_empty());
}

#[test]
fn original_guest_first_matching_mode_and_opener_win() {
    let source = language(
        vec![token("Open", Some("First")), token("Open", Some("Second"))],
        vec![
            mode("Second", vec![token("WrongOpener", Some("Second"))]),
            mode("First", vec![token("Kept", Some("First"))]),
            mode("First", vec![token("WrongMode", Some("First"))]),
        ],
    );
    assert_eq!(guest_body_nested_open_kinds(&source, "Open"), vec!["Kept"]);
}

#[test]
fn original_guest_same_mode_push_preserves_order_duplicates_and_ignores_unread_flags() {
    let mut flagged = token("Flagged", Some("Guest"));
    flagged.is_pop = true;
    flagged.stream = Some(ident("comments"));
    flagged.from_literals = true;
    let source = language(
        vec![token("Open", Some("Guest"))],
        vec![mode(
            "Guest",
            vec![
                token("Z", Some("Guest")),
                token("Subregion", Some("Comment")),
                token("Plain", None),
                token("A", Some("Guest")),
                token("Z", Some("Guest")),
                flagged,
            ],
        )],
    );
    assert_eq!(guest_body_nested_open_kinds(&source, "Open"), vec!["Z", "A", "Z", "Flagged"]);
}
