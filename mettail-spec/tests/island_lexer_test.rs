//! Island lexer and escape behavior (v1 §5.2, §7.3).

use std::path::PathBuf;

use mettail_spec::island::{decode_island_body, hole_count, split_template, TemplatePiece};
use mettail_spec::lexer::{Lexer, Token};

fn lex_island(source: &str) -> mettail_spec::lexer::Token {
    let tokens = Lexer::new(source, PathBuf::from("test.rho"))
        .tokenize()
        .expect("tokenize");
    tokens
        .into_iter()
        .find(|t| matches!(t, Token::Island { .. }))
        .expect("island token")
}

#[test]
fn v1_escape_table_backtick_dollar_backslash() {
    let tok = lex_island(r#"MyLang`expr with \`backticks\`, \${brace}, and \\slash\\`"#);
    let Token::Island { body, .. } = tok else {
        unreachable!()
    };
    assert!(body.contains(r"\`"));
    assert!(body.contains(r"\${"));
    assert!(body.contains(r"\\"));
    assert_eq!(hole_count(&body), 0);
}

#[test]
fn decode_island_body_matches_lexer() {
    let raw = r"line\`one\${two\\three";
    let decoded = decode_island_body(raw).expect("decode");
    assert_eq!(decoded.text, "line`one${two\\three");
    assert_eq!(hole_count(raw), 0);
}

#[test]
fn unescaped_hole_splits_template() {
    let body = "let x = ${42};";
    let tmpl = split_template(body);
    assert_eq!(tmpl.pieces.len(), 3);
    assert!(matches!(&tmpl.pieces[0], TemplatePiece::Text(_)));
    assert!(matches!(&tmpl.pieces[1], TemplatePiece::Hole(h) if h.source == "42"));
}

#[test]
fn escaped_dollar_brace_is_literal() {
    let body = r"literal \${not a hole}";
    assert_eq!(hole_count(body), 0);
    let decoded = decode_island_body(body).expect("decode");
    assert!(decoded.text.contains("${not"));
}

#[test]
fn triple_backtick_multiline_island() {
    let source = "Rust```\n  fn main() {}\n```";
    let tok = lex_island(source);
    let Token::Island { lang, triple, body } = tok else {
        unreachable!()
    };
    assert_eq!(lang, "Rust");
    assert!(triple);
    assert!(body.contains("fn main"));
}

#[test]
fn nested_lang_markers_stay_inside_body_when_escaped() {
    let tok = lex_island(r#"LangA`outer LangB\`inner\` tail`"#);
    let Token::Island { lang, body, .. } = tok else {
        unreachable!()
    };
    assert_eq!(lang, "LangA");
    assert!(body.contains("LangB"));
    assert!(body.contains("inner"));
}
