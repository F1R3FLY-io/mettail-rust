//! Frozen tests of the original NonTerminalKind classifier before relocation.
use mettail_ast::grammar::{GrammarItem, NonTerminalKind};
use std::collections::HashSet;
use std::hash::Hash;

#[test]
fn original_exact_names_and_kind_queries() {
    for (name, kind, literal, builtin) in [
        ("Var", NonTerminalKind::Var, false, true),
        ("Integer", NonTerminalKind::Integer, true, true),
        ("Boolean", NonTerminalKind::Boolean, true, true),
        ("StringLiteral", NonTerminalKind::StringLiteral, true, true),
        ("FloatLiteral", NonTerminalKind::FloatLiteral, true, true),
        ("Ident", NonTerminalKind::Ident, false, true),
        ("Expr", NonTerminalKind::Category, false, false),
    ] {
        assert_eq!(NonTerminalKind::classify(name), kind);
        assert_eq!(kind.is_literal(), literal);
        assert_eq!(kind.is_builtin(), builtin);
    }
}

#[test]
fn original_fallback_is_exact_case_sensitive_untrimmed_string_match() {
    for name in [
        "",
        "Category",
        "var",
        "VAR",
        "integer",
        "Integer ",
        " Integer",
        "Boolean\n",
        "String",
        "Float",
        "Identifier",
        "IdentText",
        "Ident\0",
        "r#Ident",
        "Expr",
        "Name",
        "Proc",
        "Ｉdent",
        "Identλ",
        "λ",
        "Integer::Value",
    ] {
        assert_eq!(NonTerminalKind::classify(name), NonTerminalKind::Category, "{name:?}");
    }
}

#[test]
fn original_traits_debug_and_discriminant_order_are_retained() {
    fn original_traits<T: Copy + Clone + std::fmt::Debug + PartialEq + Eq + Hash>() {}
    original_traits::<NonTerminalKind>();
    let kinds = [
        NonTerminalKind::Var,
        NonTerminalKind::Integer,
        NonTerminalKind::Boolean,
        NonTerminalKind::StringLiteral,
        NonTerminalKind::FloatLiteral,
        NonTerminalKind::Ident,
        NonTerminalKind::Category,
    ];
    assert_eq!(kinds.into_iter().collect::<HashSet<_>>().len(), 7);
    assert_eq!(kinds.map(|kind| kind as usize), [0, 1, 2, 3, 4, 5, 6]);
    assert_eq!(
        kinds.map(|kind| format!("{kind:?}")),
        [
            "Var",
            "Integer",
            "Boolean",
            "StringLiteral",
            "FloatLiteral",
            "Ident",
            "Category",
        ]
    );
}

#[test]
fn original_grammar_item_constructor_keeps_preclassified_kind() {
    let plain = GrammarItem::non_terminal(syn::Ident::new("Ident", proc_macro2::Span::call_site()));
    let raw =
        GrammarItem::non_terminal(syn::Ident::new_raw("Ident", proc_macro2::Span::call_site()));
    assert_eq!(plain.nonterminal_kind(), Some(NonTerminalKind::Ident));
    assert_eq!(raw.nonterminal_kind(), Some(NonTerminalKind::Category));
}
