//! Tests for grammar warning detection.
//!
//! Validates that `detect_grammar_warnings` correctly identifies:
//! - Ambiguous prefix dispatch (same terminal, same category, multiple rules)
//! - Left-recursion in RD rules (first item is NonTerminal of same category)
//! - Unused categories (declared but never referenced in syntax)
//!
//! Also validates `detect_dead_rules` (WFST-based dead-rule detection):
//! - Dead cast rules (WFST unreachable)
//! - Dead cross-category rules (WFST unreachable)
//! - Dead literal rules (no native_type)
//! - Dead infix/var rules (unreachable category)
//! - Reachable rules are NOT flagged

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

// ══════════════════════════════════════════════════════════════════════════════
// Dead-rule detection via WFST (pipeline::detect_dead_rules)
// ══════════════════════════════════════════════════════════════════════════════

mod dead_rule_tests {
    use std::collections::HashMap;

    use crate::automata::semiring::TropicalWeight;
    use crate::pipeline::{CategoryInfo, DeadRuleWarning, detect_dead_rules};
    use crate::prediction::{DispatchAction, FirstItem, FirstSet, RuleInfo};
    use crate::token_id::TokenIdMap;
    use crate::wfst::PredictionWfstBuilder;

    /// Helper: build a `PredictionWfst` for a category from a list of
    /// `(token, rule_label, weight)` triples using `DispatchAction::Direct`.
    fn build_wfst(
        category: &str,
        entries: &[(&str, &str, f64)],
    ) -> crate::wfst::PredictionWfst {
        let tokens: Vec<String> = entries.iter().map(|(t, _, _)| t.to_string()).collect();
        let token_map = TokenIdMap::from_names(tokens);
        let mut builder = PredictionWfstBuilder::new(category, token_map);
        for &(tok, label, w) in entries {
            builder.add_action(
                tok,
                DispatchAction::Direct {
                    rule_label: label.to_string(),
                    parse_fn: format!("parse_{}", label.to_lowercase()),
                },
                TropicalWeight::new(w),
            );
        }
        builder.build()
    }

    /// Helper: build a `PredictionWfst` with cast and cross-category entries.
    fn build_wfst_with_cast(
        category: &str,
        entries: &[(&str, DispatchAction, f64)],
    ) -> crate::wfst::PredictionWfst {
        let tokens: Vec<String> = entries.iter().map(|(t, _, _)| t.to_string()).collect();
        let token_map = TokenIdMap::from_names(tokens);
        let mut builder = PredictionWfstBuilder::new(category, token_map);
        for (tok, action, w) in entries {
            builder.add_action(tok, action.clone(), TropicalWeight::new(*w));
        }
        builder.build()
    }

    fn cat_info(name: &str, native_type: Option<&str>) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: native_type.map(|s| s.to_string()),
            is_primary: false,
        }
    }

    fn first_set_with(tokens: &[&str]) -> FirstSet {
        let mut fs = FirstSet::new();
        for tok in tokens {
            fs.insert(tok);
        }
        fs
    }

    // ── Tier 1: literal rules ──

    #[test]
    fn test_literal_rule_without_native_type_is_dead() {
        let rule_infos = vec![RuleInfo {
            label: "NumLit".to_string(),
            category: "Expr".to_string(),
            first_items: vec![],
            is_infix: false,
            is_var: false,
            is_literal: true,
            is_cross_category: false,
            is_cast: false,
        }];
        let categories = vec![cat_info("Expr", None)];
        let first_sets = HashMap::new();
        let wfsts = HashMap::new();

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert_eq!(warnings.len(), 1);
        assert!(matches!(
            &warnings[0],
            DeadRuleWarning::LiteralNoNativeType { rule_label, category }
            if rule_label == "NumLit" && category == "Expr"
        ));
    }

    #[test]
    fn test_literal_rule_with_native_type_is_not_dead() {
        let rule_infos = vec![RuleInfo {
            label: "NumLit".to_string(),
            category: "Int".to_string(),
            first_items: vec![],
            is_infix: false,
            is_var: false,
            is_literal: true,
            is_cross_category: false,
            is_cast: false,
        }];
        let categories = vec![cat_info("Int", Some("i32"))];
        let first_sets = HashMap::new();
        let wfsts = HashMap::new();

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert!(
            warnings.is_empty(),
            "literal rule with native_type should not be flagged: {:?}",
            warnings
        );
    }

    // ── Tier 2: infix/var in unreachable category ──

    #[test]
    fn test_infix_rule_in_unreachable_category_is_dead() {
        let rule_infos = vec![RuleInfo {
            label: "Add".to_string(),
            category: "Ghost".to_string(),
            first_items: vec![FirstItem::Terminal("+".to_string())],
            is_infix: true,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        }];
        let categories = vec![cat_info("Ghost", None)];
        // Ghost has empty FIRST set → unreachable
        let first_sets: HashMap<String, FirstSet> = HashMap::new();
        let wfsts = HashMap::new();

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert_eq!(warnings.len(), 1);
        assert!(matches!(
            &warnings[0],
            DeadRuleWarning::UnreachableCategory { rule_label, category }
            if rule_label == "Add" && category == "Ghost"
        ));
    }

    #[test]
    fn test_var_rule_in_unreachable_category_is_dead() {
        let rule_infos = vec![RuleInfo {
            label: "XVar".to_string(),
            category: "Ghost".to_string(),
            first_items: vec![FirstItem::Ident],
            is_infix: false,
            is_var: true,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        }];
        let categories = vec![cat_info("Ghost", None)];
        let first_sets: HashMap<String, FirstSet> = HashMap::new();
        let wfsts = HashMap::new();

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert_eq!(warnings.len(), 1);
        assert!(matches!(
            &warnings[0],
            DeadRuleWarning::UnreachableCategory { rule_label, category }
            if rule_label == "XVar" && category == "Ghost"
        ));
    }

    #[test]
    fn test_infix_rule_in_reachable_category_is_not_dead() {
        let rule_infos = vec![
            // A prefix rule that makes Int reachable
            RuleInfo {
                label: "NumLit".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Terminal("Integer".to_string())],
                is_infix: false,
                is_var: false,
                is_literal: true,
                is_cross_category: false,
                is_cast: false,
            },
            // The infix rule under test
            RuleInfo {
                label: "Add".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Terminal("+".to_string())],
                is_infix: true,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ];
        let categories = vec![cat_info("Int", Some("i32"))];
        let mut first_sets = HashMap::new();
        first_sets.insert("Int".to_string(), first_set_with(&["Integer", "Plus"]));
        let wfsts = HashMap::new();

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        // NumLit is literal with native_type → not dead
        // Add is infix in reachable category → not dead
        assert!(
            warnings.is_empty(),
            "rules in reachable category should not be flagged: {:?}",
            warnings
        );
    }

    #[test]
    fn test_var_rule_in_reachable_category_is_not_dead() {
        let rule_infos = vec![
            RuleInfo {
                label: "Neg".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Terminal("Minus".to_string())],
                is_infix: false,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "IVar".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: false,
                is_var: true,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ];
        let categories = vec![cat_info("Int", None)];
        let mut first_sets = HashMap::new();
        first_sets.insert("Int".to_string(), first_set_with(&["Minus", "Ident"]));
        // Build WFST with Neg dispatched by Minus
        let wfst = build_wfst("Int", &[("Minus", "Neg", 0.0), ("Ident", "IVar", 2.0)]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Int".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert!(
            warnings.is_empty(),
            "var rule in reachable category should not be flagged: {:?}",
            warnings
        );
    }

    // ── Tier 2 edge case: cross-category infix is NOT skipped as same-cat infix ──

    #[test]
    fn test_cross_category_infix_goes_through_wfst_check() {
        // Cross-category rules have is_infix=true AND is_cross_category=true.
        // They should NOT be handled by Tier 2 (same-cat infix), but by Tier 3
        // (WFST check). If the WFST doesn't route to them, they're dead.
        let rule_infos = vec![RuleInfo {
            label: "Eq".to_string(),
            category: "Bool".to_string(),
            first_items: vec![FirstItem::NonTerminal("Int".to_string())],
            is_infix: true,
            is_var: false,
            is_literal: false,
            is_cross_category: true,
            is_cast: false,
        }];
        let categories = vec![cat_info("Bool", Some("bool"))];
        let mut first_sets = HashMap::new();
        first_sets.insert("Bool".to_string(), first_set_with(&["Integer"]));
        // Empty WFST — no actions for Bool → Eq is dead
        let wfst = build_wfst("Bool", &[]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Bool".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert_eq!(warnings.len(), 1);
        assert!(matches!(
            &warnings[0],
            DeadRuleWarning::WfstUnreachable { rule_label, category }
            if rule_label == "Eq" && category == "Bool"
        ));
    }

    #[test]
    fn test_reachable_cross_category_not_flagged() {
        let rule_infos = vec![RuleInfo {
            label: "Eq".to_string(),
            category: "Bool".to_string(),
            first_items: vec![FirstItem::NonTerminal("Int".to_string())],
            is_infix: true,
            is_var: false,
            is_literal: false,
            is_cross_category: true,
            is_cast: false,
        }];
        let categories = vec![cat_info("Bool", Some("bool"))];
        let mut first_sets = HashMap::new();
        first_sets.insert("Bool".to_string(), first_set_with(&["Integer"]));
        // WFST routes Integer → Eq
        let wfst = build_wfst_with_cast("Bool", &[(
            "Integer",
            DispatchAction::CrossCategory {
                source_category: "Int".to_string(),
                operator_token: "EqEq".to_string(),
                rule_label: "Eq".to_string(),
                needs_backtrack: false,
            },
            0.5,
        )]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Bool".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert!(
            warnings.is_empty(),
            "reachable cross-category rule should not be flagged: {:?}",
            warnings
        );
    }

    // ── Tier 3: cast rules ──

    #[test]
    fn test_dead_cast_rule_flagged() {
        let rule_infos = vec![RuleInfo {
            label: "IntToFloat".to_string(),
            category: "Float".to_string(),
            first_items: vec![FirstItem::NonTerminal("Int".to_string())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: true,
        }];
        let categories = vec![cat_info("Float", Some("f64"))];
        let mut first_sets = HashMap::new();
        first_sets.insert("Float".to_string(), first_set_with(&["Integer"]));
        // WFST routes Integer to a different rule, not IntToFloat
        let wfst = build_wfst("Float", &[("Integer", "FloatLit", 0.0)]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Float".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert_eq!(warnings.len(), 1);
        assert!(matches!(
            &warnings[0],
            DeadRuleWarning::WfstUnreachable { rule_label, category }
            if rule_label == "IntToFloat" && category == "Float"
        ));
    }

    #[test]
    fn test_reachable_cast_rule_not_flagged() {
        let rule_infos = vec![RuleInfo {
            label: "IntToFloat".to_string(),
            category: "Float".to_string(),
            first_items: vec![FirstItem::NonTerminal("Int".to_string())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: true,
        }];
        let categories = vec![cat_info("Float", Some("f64"))];
        let mut first_sets = HashMap::new();
        first_sets.insert("Float".to_string(), first_set_with(&["Integer"]));
        // WFST routes Integer → IntToFloat (via Cast action)
        let wfst = build_wfst_with_cast("Float", &[(
            "Integer",
            DispatchAction::Cast {
                source_category: "Int".to_string(),
                wrapper_label: "IntToFloat".to_string(),
            },
            1.0,
        )]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Float".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        assert!(
            warnings.is_empty(),
            "reachable cast rule should not be flagged: {:?}",
            warnings
        );
    }

    // ── Tier 2: category reachability via transitive cross-cat/cast ──

    #[test]
    fn test_category_reachable_transitively_via_cast() {
        // Int is reachable (has FIRST set), Float is reachable via cast from Int
        let rule_infos = vec![
            RuleInfo {
                label: "IntToFloat".to_string(),
                category: "Float".to_string(),
                first_items: vec![FirstItem::NonTerminal("Int".to_string())],
                is_infix: false,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: true,
            },
            RuleInfo {
                label: "FAdd".to_string(),
                category: "Float".to_string(),
                first_items: vec![FirstItem::Terminal("Plus".to_string())],
                is_infix: true,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ];
        let categories = vec![
            cat_info("Int", Some("i32")),
            cat_info("Float", Some("f64")),
        ];
        let mut first_sets = HashMap::new();
        first_sets.insert("Int".to_string(), first_set_with(&["Integer"]));
        first_sets.insert("Float".to_string(), first_set_with(&["Integer"]));
        // WFST routes Integer → IntToFloat in Float category
        let wfst = build_wfst_with_cast("Float", &[(
            "Integer",
            DispatchAction::Cast {
                source_category: "Int".to_string(),
                wrapper_label: "IntToFloat".to_string(),
            },
            1.0,
        )]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Float".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        // Float is reachable via Int → IntToFloat cast, so FAdd should NOT be dead
        assert!(
            warnings.is_empty(),
            "infix rule in transitively reachable category should not be flagged: {:?}",
            warnings
        );
    }

    // ── Display formatting for DeadRuleWarning ──

    #[test]
    fn test_dead_rule_warning_display() {
        let w1 = DeadRuleWarning::LiteralNoNativeType {
            rule_label: "NumLit".to_string(),
            category: "Expr".to_string(),
        };
        let s1 = format!("{}", w1);
        assert!(s1.contains("literal rule NumLit"));
        assert!(s1.contains("no native_type"));

        let w2 = DeadRuleWarning::UnreachableCategory {
            rule_label: "Add".to_string(),
            category: "Ghost".to_string(),
        };
        let s2 = format!("{}", w2);
        assert!(s2.contains("rule Add"));
        assert!(s2.contains("no reachable prefix rules"));

        let w3 = DeadRuleWarning::WfstUnreachable {
            rule_label: "Eq".to_string(),
            category: "Bool".to_string(),
        };
        let s3 = format!("{}", w3);
        assert!(s3.contains("rule Eq"));
        assert!(s3.contains("no token in FIRST(Bool)"));
    }

    // ── Combined scenario: multiple rule types in one grammar ──

    #[test]
    fn test_mixed_grammar_dead_rules() {
        // Grammar with:
        // - Reachable Int category (has FIRST set)
        // - Unreachable Ghost category (empty FIRST set, no transitive reach)
        // - A dead literal in Ghost (no native_type)
        // - A dead var in Ghost (unreachable category)
        // - A dead infix in Ghost (unreachable category)
        // - A live prefix in Int
        let rule_infos = vec![
            RuleInfo {
                label: "Neg".to_string(),
                category: "Int".to_string(),
                first_items: vec![FirstItem::Terminal("Minus".to_string())],
                is_infix: false,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "GhostLit".to_string(),
                category: "Ghost".to_string(),
                first_items: vec![],
                is_infix: false,
                is_var: false,
                is_literal: true,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "GhostVar".to_string(),
                category: "Ghost".to_string(),
                first_items: vec![FirstItem::Ident],
                is_infix: false,
                is_var: true,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
            RuleInfo {
                label: "GhostAdd".to_string(),
                category: "Ghost".to_string(),
                first_items: vec![FirstItem::Terminal("Plus".to_string())],
                is_infix: true,
                is_var: false,
                is_literal: false,
                is_cross_category: false,
                is_cast: false,
            },
        ];
        let categories = vec![
            cat_info("Int", Some("i32")),
            cat_info("Ghost", None),
        ];
        let mut first_sets = HashMap::new();
        first_sets.insert("Int".to_string(), first_set_with(&["Minus"]));
        // Ghost has no FIRST set → unreachable
        let wfst = build_wfst("Int", &[("Minus", "Neg", 0.0)]);
        let mut wfsts = HashMap::new();
        wfsts.insert("Int".to_string(), wfst);

        let warnings = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);

        // Neg: reachable prefix in Int → not dead
        // GhostLit: literal without native_type → dead (Tier 1)
        // GhostVar: var in unreachable Ghost → dead (Tier 2)
        // GhostAdd: infix in unreachable Ghost → dead (Tier 2)
        assert_eq!(warnings.len(), 3, "expected 3 dead rules, got {:?}", warnings);

        assert!(warnings.iter().any(|w| matches!(w,
            DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            if rule_label == "GhostLit"
        )), "GhostLit should be dead: {:?}", warnings);

        assert!(warnings.iter().any(|w| matches!(w,
            DeadRuleWarning::UnreachableCategory { rule_label, .. }
            if rule_label == "GhostVar"
        )), "GhostVar should be dead: {:?}", warnings);

        assert!(warnings.iter().any(|w| matches!(w,
            DeadRuleWarning::UnreachableCategory { rule_label, .. }
            if rule_label == "GhostAdd"
        )), "GhostAdd should be dead: {:?}", warnings);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Tier 4: Transitive semantic liveness (compute_semantic_live_labels)
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn semantic_live_labels_transitive_closure() {
        use crate::pipeline::compute_semantic_live_labels;
        use std::collections::HashSet;

        // A is parsing-live. Group {A, B} resurrects B, then group {B, C} resurrects C.
        let parsing_live: HashSet<String> = ["A"].iter().map(|s| s.to_string()).collect();
        let groups = vec![
            ["A", "B"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
            ["B", "C"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
        ];
        let result = compute_semantic_live_labels(&parsing_live, &groups);
        assert!(result.contains("A"), "A should be live");
        assert!(result.contains("B"), "B should be live (resurrected by group {{A, B}})");
        assert!(result.contains("C"), "C should be live (resurrected by group {{B, C}})");
    }

    #[test]
    fn semantic_live_labels_no_overlap() {
        use crate::pipeline::compute_semantic_live_labels;
        use std::collections::HashSet;

        // A is parsing-live. Group {B, C} has no overlap → no resurrection.
        let parsing_live: HashSet<String> = ["A"].iter().map(|s| s.to_string()).collect();
        let groups = vec![
            ["B", "C"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
        ];
        let result = compute_semantic_live_labels(&parsing_live, &groups);
        assert!(result.contains("A"), "A should be live");
        assert!(!result.contains("B"), "B should NOT be live (no overlap)");
        assert!(!result.contains("C"), "C should NOT be live (no overlap)");
    }

    #[test]
    fn semantic_live_labels_multiple_seeds() {
        use crate::pipeline::compute_semantic_live_labels;
        use std::collections::HashSet;

        // A, D are parsing-live. Group {A, B} resurrects B; group {C, D} resurrects C.
        let parsing_live: HashSet<String> =
            ["A", "D"].iter().map(|s| s.to_string()).collect();
        let groups = vec![
            ["A", "B"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
            ["C", "D"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
        ];
        let result = compute_semantic_live_labels(&parsing_live, &groups);
        assert_eq!(result.len(), 4, "all 4 labels should be live: {:?}", result);
    }

    #[test]
    fn semantic_live_labels_empty_groups() {
        use crate::pipeline::compute_semantic_live_labels;
        use std::collections::HashSet;

        // No dependency groups → result equals parsing-live set.
        let parsing_live: HashSet<String> = ["A"].iter().map(|s| s.to_string()).collect();
        let result = compute_semantic_live_labels(&parsing_live, &[]);
        assert_eq!(result, parsing_live);
    }

    #[test]
    fn tier4_resurrects_wfst_unreachable_label() {
        use std::collections::HashSet;

        // Simulate a label that is WFST-unreachable (Tier 3) but referenced by an
        // equation alongside a live label. The dependency group should resurrect it.
        let categories = vec![cat_info("Proc", None)];

        // PNew: reachable prefix rule (dispatched by "new").
        let r_new = RuleInfo {
            label: "PNew".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Terminal("new".into())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        };

        // PIn: prefix rule but NOT dispatched by any FIRST-set token → Tier 3 dead.
        let r_in = RuleInfo {
            label: "PIn".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Terminal("in".into())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        };

        let rule_infos = vec![r_new, r_in];

        // Only "new" in the FIRST set — "in" absent, making PIn WFST-unreachable.
        let first_sets = {
            let mut fs = HashMap::new();
            fs.insert("Proc".to_string(), first_set_with(&["new"]));
            fs
        };

        // WFST dispatches only PNew from "new".
        let wfsts = {
            let mut w = HashMap::new();
            w.insert("Proc".to_string(), build_wfst("Proc", &[("new", "PNew", 0.0)]));
            w
        };

        // Without semantic groups: PIn is flagged as WfstUnreachable.
        let warnings_no_sem = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &[]);
        assert_eq!(warnings_no_sem.len(), 1, "PIn should be flagged without semantic groups");
        assert!(matches!(
            &warnings_no_sem[0],
            DeadRuleWarning::WfstUnreachable { rule_label, .. } if rule_label == "PIn"
        ));

        // With semantic group {PIn, PNew}: PIn is resurrected because PNew is parsing-live.
        let groups = vec![
            ["PIn", "PNew"].iter().map(|s| s.to_string()).collect::<HashSet<_>>(),
        ];
        let warnings_with_sem = detect_dead_rules(&rule_infos, &categories, &first_sets, &wfsts, &groups);
        assert!(
            warnings_with_sem.is_empty(),
            "PIn should be resurrected by semantic group: {:?}",
            warnings_with_sem,
        );
    }
}
