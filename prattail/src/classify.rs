//! Rule classification: derive boolean/enum flags from structural data.
//!
//! Moves semantic analysis (is_infix, is_postfix, is_cast, etc.) out of
//! the macros-crate bridge and into PraTTaIL, so that any `RuleSpec` can
//! be classified regardless of origin (macro bridge, tests, benchmarks,
//! or future non-macro frontends).
//!
//! All derivation logic pattern-matches on `SyntaxItemSpec`, the rule's
//! `category`, and the list of known category names. No access to the
//! macros-crate AST types (`GrammarRule`, `TermParam`, etc.) is needed.

use crate::recursive::CollectionKind;
use crate::SyntaxItemSpec;

/// All derived classification flags for a single rule.
#[derive(Debug, Clone)]
pub struct RuleClassification {
    pub is_infix: bool,
    pub is_postfix: bool,
    pub is_unary_prefix: bool,
    pub is_var: bool,
    pub is_literal: bool,
    pub has_binder: bool,
    pub has_multi_binder: bool,
    pub is_collection: bool,
    pub collection_type: Option<CollectionKind>,
    pub separator: Option<String>,
    pub is_cross_category: bool,
    pub cross_source_category: Option<String>,
    pub is_cast: bool,
    pub cast_source_category: Option<String>,
}

/// Classify a rule from its structural syntax items, category, and known category names.
///
/// This is the single source of truth for all derived boolean/enum flags.
/// The bridge provides only structural mapping; classification happens here.
pub fn classify_rule(
    syntax: &[SyntaxItemSpec],
    category: &str,
    category_names: &[String],
) -> RuleClassification {
    let is_var = classify_is_var(syntax);
    let is_literal = syntax.is_empty();

    let is_postfix = classify_is_postfix(syntax, category, category_names);
    let is_unary_prefix = classify_is_unary_prefix(syntax, category, category_names);

    let has_multi_binder = has_binder_recursive(syntax, true);
    let has_binder = !has_multi_binder && has_binder_recursive(syntax, false);

    let (is_collection, collection_type, separator) = classify_collection(syntax);

    let (is_cross_category, cross_source_category) =
        classify_cross_category(syntax, category, category_names);

    let (is_cast, cast_source_category) =
        classify_cast(syntax, category, category_names, is_var);

    // Infix: same-category leading NT + operator, OR postfix, OR cross-category.
    // Cross-category infix (e.g., `Int == Int` producing `Bool`) implies infix
    // but is NOT detected by classify_is_infix (which only checks same-category).
    let is_infix = classify_is_infix(syntax, category) || is_postfix || is_cross_category;

    RuleClassification {
        is_infix,
        is_postfix,
        is_unary_prefix,
        is_var,
        is_literal,
        has_binder,
        has_multi_binder,
        is_collection,
        collection_type,
        separator,
        is_cross_category,
        cross_source_category,
        is_cast,
        cast_source_category,
    }
}

/// Check for binders recursively, including inside `ZipMapSep::body_items`
/// and `Optional::inner`.
///
/// When `check_multi` is true, looks for `Binder { is_multi: true }`.
/// When false, looks for `Binder { is_multi: false }`.
fn has_binder_recursive(syntax: &[SyntaxItemSpec], check_multi: bool) -> bool {
    syntax.iter().any(|item| match item {
        SyntaxItemSpec::Binder { is_multi, .. } => *is_multi == check_multi,
        SyntaxItemSpec::ZipMapSep { body_items, .. } => {
            has_binder_recursive(body_items, check_multi)
        }
        SyntaxItemSpec::Optional { inner } => has_binder_recursive(inner, check_multi),
        _ => false,
    })
}

/// A rule is a variable rule if it is exactly one `IdentCapture`.
fn classify_is_var(syntax: &[SyntaxItemSpec]) -> bool {
    syntax.len() == 1 && matches!(&syntax[0], SyntaxItemSpec::IdentCapture { .. })
}

/// A rule is infix if its syntax starts with `NT(same_category)` followed by
/// a `Terminal` (the operator trigger), with 3+ total items.
///
/// This covers standard infix `a + b` and mixfix `a ? b : c`.
/// Cross-category infix (e.g., `Int == Int` producing `Bool`) is detected
/// separately by `classify_cross_category` and ORed into `is_infix` in
/// `classify_rule`. Rules like `PAmb . Proc ::= Name "[" Proc "]"` where the
/// first NT is a *different* category are NOT infix — they are prefix RD rules.
fn classify_is_infix(
    syntax: &[SyntaxItemSpec],
    category: &str,
) -> bool {
    if syntax.len() < 3 {
        return false;
    }

    // First item must be a NonTerminal of the same category (standard infix).
    let first_is_same_cat = matches!(
        &syntax[0],
        SyntaxItemSpec::NonTerminal { category: cat, .. } if cat == category
    );

    // Second item must be a Terminal (the operator)
    let second_is_terminal = matches!(&syntax[1], SyntaxItemSpec::Terminal(_));

    first_is_same_cat && second_is_terminal
}

/// A postfix rule has exactly `[NT(same_category), Terminal]`.
fn classify_is_postfix(
    syntax: &[SyntaxItemSpec],
    category: &str,
    _category_names: &[String],
) -> bool {
    if syntax.len() != 2 {
        return false;
    }
    let first_is_same_cat = matches!(
        &syntax[0],
        SyntaxItemSpec::NonTerminal { category: cat, .. } if cat == category
    );
    let second_is_terminal = matches!(&syntax[1], SyntaxItemSpec::Terminal(_));
    first_is_same_cat && second_is_terminal
}

/// A unary prefix rule has exactly `[Terminal, NT(same_category)]`.
fn classify_is_unary_prefix(
    syntax: &[SyntaxItemSpec],
    category: &str,
    _category_names: &[String],
) -> bool {
    if syntax.len() != 2 {
        return false;
    }
    let first_is_terminal = matches!(&syntax[0], SyntaxItemSpec::Terminal(_));
    let second_is_same_cat = matches!(
        &syntax[1],
        SyntaxItemSpec::NonTerminal { category: cat, .. } if cat == category
    );
    first_is_terminal && second_is_same_cat
}

/// Check if a rule is a collection rule. Returns (is_collection, kind, separator).
fn classify_collection(syntax: &[SyntaxItemSpec]) -> (bool, Option<CollectionKind>, Option<String>) {
    for item in syntax {
        if let SyntaxItemSpec::Collection {
            kind, separator, ..
        } = item
        {
            return (true, Some(*kind), Some(separator.clone()));
        }
    }
    (false, None, None)
}

/// A cross-category rule has `[NT(cat_A), Terminal, NT(cat_A)]` where
/// `cat_A != category` and `cat_A` is a known category. Both operand
/// categories must be the same (e.g., `Int == Int` producing `Bool`).
fn classify_cross_category(
    syntax: &[SyntaxItemSpec],
    category: &str,
    category_names: &[String],
) -> (bool, Option<String>) {
    if syntax.len() != 3 {
        return (false, None);
    }
    if let (
        SyntaxItemSpec::NonTerminal {
            category: left_cat, ..
        },
        SyntaxItemSpec::Terminal(_),
        SyntaxItemSpec::NonTerminal {
            category: right_cat,
            ..
        },
    ) = (&syntax[0], &syntax[1], &syntax[2])
    {
        if left_cat == right_cat
            && left_cat != category
            && category_names.contains(left_cat)
        {
            return (true, Some(left_cat.clone()));
        }
    }
    (false, None)
}

/// A cast rule has exactly `[NT(cat_B)]` where `cat_B != category`,
/// `cat_B` is a known category, and the rule is not a variable rule.
fn classify_cast(
    syntax: &[SyntaxItemSpec],
    category: &str,
    category_names: &[String],
    is_var: bool,
) -> (bool, Option<String>) {
    if is_var {
        return (false, None);
    }
    if syntax.len() != 1 {
        return (false, None);
    }
    if let SyntaxItemSpec::NonTerminal {
        category: source_cat,
        ..
    } = &syntax[0]
    {
        if source_cat != category && category_names.contains(source_cat) {
            return (true, Some(source_cat.clone()));
        }
    }
    (false, None)
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SyntaxItemSpec;

    fn cat_names() -> Vec<String> {
        vec![
            "Int".to_string(),
            "Bool".to_string(),
            "Proc".to_string(),
            "Name".to_string(),
        ]
    }

    #[test]
    fn test_infix_classification() {
        let syntax = vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_infix, "should be infix");
        assert!(!c.is_postfix, "should not be postfix");
        assert!(!c.is_unary_prefix, "should not be unary prefix");
    }

    #[test]
    fn test_postfix_classification() {
        let syntax = vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("!".to_string()),
        ];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_postfix, "should be postfix");
        assert!(c.is_infix, "postfix implies infix");
    }

    #[test]
    fn test_unary_prefix_classification() {
        let syntax = vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
        ];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_unary_prefix, "should be unary prefix");
        assert!(!c.is_infix, "should not be infix");
        assert!(!c.is_postfix, "should not be postfix");
    }

    #[test]
    fn test_var_classification() {
        let syntax = vec![SyntaxItemSpec::IdentCapture {
            param_name: "x".to_string(),
        }];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_var, "should be var");
        assert!(!c.is_cast, "var should not be cast");
    }

    #[test]
    fn test_literal_classification() {
        let syntax: Vec<SyntaxItemSpec> = vec![];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_literal, "empty syntax should be literal");
    }

    #[test]
    fn test_cast_classification() {
        let syntax = vec![SyntaxItemSpec::NonTerminal {
            category: "Int".to_string(),
            param_name: "x".to_string(),
        }];
        let c = classify_rule(&syntax, "Proc", &cat_names());
        assert!(c.is_cast, "single NT from different known category should be cast");
        assert_eq!(
            c.cast_source_category,
            Some("Int".to_string()),
            "cast source should be Int"
        );
    }

    #[test]
    fn test_cross_category_classification() {
        let syntax = vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("==".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ];
        let c = classify_rule(&syntax, "Bool", &cat_names());
        assert!(c.is_cross_category, "should be cross-category");
        assert_eq!(
            c.cross_source_category,
            Some("Int".to_string()),
            "cross source should be Int"
        );
        assert!(c.is_infix, "cross-category should also be infix");
    }

    #[test]
    fn test_binder_classification() {
        let syntax = vec![
            SyntaxItemSpec::Terminal("lam ".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Term".to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "body".to_string(),
            },
        ];
        let c = classify_rule(&syntax, "Proc", &cat_names());
        assert!(c.has_binder, "should have binder");
        assert!(!c.has_multi_binder, "should not have multi-binder");
    }

    #[test]
    fn test_multi_binder_classification() {
        let syntax = vec![
            SyntaxItemSpec::Terminal("lam ".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "xs".to_string(),
                category: "Term".to_string(),
                is_multi: true,
            },
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "body".to_string(),
            },
        ];
        let c = classify_rule(&syntax, "Proc", &cat_names());
        assert!(c.has_multi_binder, "should have multi-binder");
        assert!(!c.has_binder, "should not have single binder when multi-binder present");
    }

    #[test]
    fn test_collection_classification() {
        let syntax = vec![
            SyntaxItemSpec::Terminal("[".to_string()),
            SyntaxItemSpec::Collection {
                param_name: "elems".to_string(),
                element_category: "Int".to_string(),
                separator: ",".to_string(),
                kind: CollectionKind::Vec,
            },
            SyntaxItemSpec::Terminal("]".to_string()),
        ];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_collection, "should be collection");
        assert_eq!(c.collection_type, Some(CollectionKind::Vec));
        assert_eq!(c.separator, Some(",".to_string()));
    }

    #[test]
    fn test_postfix_implies_infix() {
        let syntax = vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("!".to_string()),
        ];
        let c = classify_rule(&syntax, "Int", &cat_names());
        assert!(c.is_postfix, "should be postfix");
        assert!(c.is_infix, "postfix must imply infix");
    }

    #[test]
    fn test_foreign_category_prefix_not_infix() {
        // PAmb-like rule: Name "[" Proc "]" for category Proc.
        // First NT is a foreign category — this is a prefix RD rule, NOT infix.
        let syntax = vec![
            SyntaxItemSpec::NonTerminal {
                category: "Name".to_string(),
                param_name: "n".to_string(),
            },
            SyntaxItemSpec::Terminal("[".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
            SyntaxItemSpec::Terminal("]".to_string()),
        ];
        let c = classify_rule(&syntax, "Proc", &cat_names());
        assert!(!c.is_infix, "foreign-category prefix should not be infix");
        assert!(!c.is_cross_category, "operands differ — not cross-category");
    }

    #[test]
    fn test_multi_binder_in_zipmapsep() {
        // PInputs-like rule: binder nested inside ZipMapSep body_items.
        let syntax = vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::ZipMapSep {
                left_name: "ns".to_string(),
                right_name: "xs".to_string(),
                left_category: "Name".to_string(),
                right_category: "Name".to_string(),
                body_items: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Name".to_string(),
                        param_name: "n".to_string(),
                    },
                    SyntaxItemSpec::Terminal("?".to_string()),
                    SyntaxItemSpec::Binder {
                        param_name: "x".to_string(),
                        category: "Name".to_string(),
                        is_multi: true,
                    },
                ],
                separator: ",".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::Terminal("{".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
            SyntaxItemSpec::Terminal("}".to_string()),
        ];
        let c = classify_rule(&syntax, "Proc", &cat_names());
        assert!(c.has_multi_binder, "should detect multi-binder inside ZipMapSep");
        assert!(!c.has_binder, "multi-binder present — has_binder should be false");
    }

    #[test]
    fn test_non_category_nonterminal_not_cast() {
        // NT("Unknown") where "Unknown" is not in category_names → not a cast
        let syntax = vec![SyntaxItemSpec::NonTerminal {
            category: "Unknown".to_string(),
            param_name: "x".to_string(),
        }];
        let cats = vec!["Int".to_string(), "Bool".to_string()];
        let c = classify_rule(&syntax, "Proc", &cats);
        assert!(!c.is_cast, "unknown category should not be cast");
    }
}
