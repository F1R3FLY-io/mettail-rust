//! Tests for grammar warning detection.
//!
//! Validates that `detect_grammar_warnings` correctly identifies:
//! - Ambiguous prefix dispatch (same terminal, same category, multiple rules)
//! - Left-recursion in RD rules (first item is NonTerminal of same category)
//! - Unused categories (declared but never referenced in syntax)

use crate::prediction::{detect_grammar_warnings, FirstItem, GrammarWarning, RuleInfo};
use crate::SyntaxItemSpec;

/// Helper: create a basic RuleInfo for testing.
fn make_rule_info(
    label: &str,
    category: &str,
    first_items: Vec<FirstItem>,
    is_infix: bool,
) -> RuleInfo {
    RuleInfo {
        label: label.to_string(),
        category: category.to_string(),
        first_items,
        is_infix,
        is_var: false,
        is_literal: false,
        is_cross_category: false,
        is_cast: false,
    }
}

// ── Ambiguous prefix dispatch ──

#[test]
fn test_ambiguous_prefix_detected() {
    // Two non-infix rules in the same category starting with the same terminal
    let rules = vec![
        make_rule_info("Foo", "Int", vec![FirstItem::Terminal("!".to_string())], false),
        make_rule_info("Bar", "Int", vec![FirstItem::Terminal("!".to_string())], false),
    ];
    let categories = vec!["Int".to_string()];
    let syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        warnings.iter().any(|w| matches!(w,
            GrammarWarning::AmbiguousPrefix { token, category, rules }
            if token == "!" && category == "Int" && rules.len() == 2
        )),
        "should detect ambiguous prefix dispatch: {:?}",
        warnings
    );
}

#[test]
fn test_no_ambiguity_for_different_terminals() {
    let rules = vec![
        make_rule_info("Foo", "Int", vec![FirstItem::Terminal("!".to_string())], false),
        make_rule_info("Bar", "Int", vec![FirstItem::Terminal("#".to_string())], false),
    ];
    let categories = vec!["Int".to_string()];
    let syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::AmbiguousPrefix { .. })),
        "should not detect ambiguity for different terminals: {:?}",
        warnings
    );
}

#[test]
fn test_no_ambiguity_for_infix_rules() {
    // Infix rules should be excluded from prefix dispatch ambiguity check
    let rules = vec![
        make_rule_info("Add", "Int", vec![FirstItem::Terminal("+".to_string())], true),
        make_rule_info("Pos", "Int", vec![FirstItem::Terminal("+".to_string())], false),
    ];
    let categories = vec!["Int".to_string()];
    let syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::AmbiguousPrefix { .. })),
        "infix rules should not contribute to prefix ambiguity: {:?}",
        warnings
    );
}

#[test]
fn test_no_ambiguity_for_var_rules() {
    // Var rules should be excluded from ambiguity check
    let rules = vec![
        {
            let mut r = make_rule_info("IVar", "Int", vec![FirstItem::Ident], false);
            r.is_var = true;
            r
        },
        make_rule_info("Foo", "Int", vec![FirstItem::Ident], false),
    ];
    let categories = vec!["Int".to_string()];
    let syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    // Var rules are excluded, so only Foo matches Ident — no ambiguity
    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::AmbiguousPrefix { .. })),
        "var rules should not contribute to prefix ambiguity: {:?}",
        warnings
    );
}

// ── Left-recursion ──

#[test]
fn test_left_recursion_detected() {
    let rules = vec![];
    let categories = vec!["Int".to_string()];
    // A rule where the first item is NonTerminal of the same category
    // and it's NOT an infix/postfix/mixfix pattern
    let syntax = vec![(
        "BadRule".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("@".to_string()),
            SyntaxItemSpec::Terminal("#".to_string()),
        ],
    )];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        warnings.iter().any(|w| matches!(w,
            GrammarWarning::LeftRecursion { rule_label, category }
            if rule_label == "BadRule" && category == "Int"
        )),
        "should detect left recursion: {:?}",
        warnings
    );
}

#[test]
fn test_no_left_recursion_for_infix_pattern() {
    let rules = vec![];
    let categories = vec!["Int".to_string()];
    // Standard infix pattern: NT Terminal NT — handled by Pratt
    let syntax = vec![(
        "Add".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ],
    )];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::LeftRecursion { .. })),
        "infix pattern should not trigger left-recursion warning: {:?}",
        warnings
    );
}

#[test]
fn test_no_left_recursion_for_postfix_pattern() {
    let rules = vec![];
    let categories = vec!["Int".to_string()];
    // Postfix: NT Terminal — handled by Pratt
    let syntax = vec![(
        "Fact".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("!".to_string()),
        ],
    )];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::LeftRecursion { .. })),
        "postfix pattern should not trigger left-recursion warning: {:?}",
        warnings
    );
}

#[test]
fn test_no_left_recursion_for_different_category() {
    let rules = vec![];
    let categories = vec!["Int".to_string(), "Bool".to_string()];
    // First NT is a different category — not left-recursive
    let syntax = vec![(
        "IntToBool".to_string(),
        "Bool".to_string(),
        vec![SyntaxItemSpec::NonTerminal {
            category: "Int".to_string(),
            param_name: "a".to_string(),
        }],
    )];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::LeftRecursion { .. })),
        "cross-category first item should not trigger left-recursion: {:?}",
        warnings
    );
}

// ── Unused categories ──

#[test]
fn test_unused_category_detected() {
    let rules = vec![];
    let categories = vec!["Int".to_string(), "Unused".to_string()];
    // Only Int is referenced in syntax, Unused is never mentioned
    let syntax = vec![(
        "NumLit".to_string(),
        "Int".to_string(),
        vec![], // no syntax items
    )];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        warnings.iter().any(|w| matches!(w,
            GrammarWarning::UnusedCategory { category }
            if category == "Unused"
        )),
        "should detect unused category: {:?}",
        warnings
    );
}

#[test]
fn test_no_unused_category_when_referenced_in_syntax() {
    let rules = vec![];
    let categories = vec!["Int".to_string(), "Bool".to_string()];
    let syntax = vec![
        ("NumLit".to_string(), "Int".to_string(), vec![]),
        (
            "Eq".to_string(),
            "Bool".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("==".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        ),
    ];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::UnusedCategory { .. })),
        "referenced categories should not trigger unused warning: {:?}",
        warnings
    );
}

#[test]
fn test_no_unused_category_when_has_rules() {
    let rules = vec![];
    let categories = vec!["Int".to_string()];
    // Int has a rule targeting it — it's "used"
    let syntax = vec![("NumLit".to_string(), "Int".to_string(), vec![])];

    let warnings = detect_grammar_warnings(&rules, &categories, &syntax);

    assert!(
        !warnings
            .iter()
            .any(|w| matches!(w, GrammarWarning::UnusedCategory { .. })),
        "categories with rules should not be marked as unused: {:?}",
        warnings
    );
}

// ── Display formatting ──

#[test]
fn test_warning_display_format() {
    let w1 = GrammarWarning::AmbiguousPrefix {
        token: "!".to_string(),
        category: "Int".to_string(),
        rules: vec!["Foo".to_string(), "Bar".to_string()],
    };
    let s1 = format!("{}", w1);
    assert!(s1.contains("ambiguous prefix dispatch"));
    assert!(s1.contains("Int"));
    assert!(s1.contains("Foo, Bar"));

    let w2 = GrammarWarning::LeftRecursion {
        rule_label: "Bad".to_string(),
        category: "Proc".to_string(),
    };
    let s2 = format!("{}", w2);
    assert!(s2.contains("left-recursive"));
    assert!(s2.contains("Bad"));

    let w3 = GrammarWarning::UnusedCategory { category: "Orphan".to_string() };
    let s3 = format!("{}", w3);
    assert!(s3.contains("never referenced"));
    assert!(s3.contains("Orphan"));
}
