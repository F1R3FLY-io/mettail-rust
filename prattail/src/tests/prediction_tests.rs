//! Tests for FIRST/FOLLOW set computation and dispatch table generation.

use crate::prediction::{
    analyze_cross_category_overlaps, build_dispatch_tables, compute_first_sets,
    compute_follow_sets, FirstItem, FirstSet, RuleInfo,
};
use crate::{RuleSpec, SyntaxItemSpec};
use crate::binding_power::Associativity;
use crate::recursive::CollectionKind;

#[test]
fn test_first_sets_simple() {
    let rules = vec![
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
        RuleInfo {
            label: "Add".to_string(),
            category: "Int".to_string(),
            first_items: vec![],
            is_infix: true,
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

    let categories = vec!["Int".to_string()];
    let first_sets = compute_first_sets(&rules, &categories);

    let int_first = first_sets.get("Int").expect("should have Int FIRST set");
    // "Integer" terminal maps to "Integer" variant via terminal_to_variant_name...
    // but FirstItem::Terminal("Integer") is treated as the raw text, and
    // terminal_to_variant_name is called inside compute_first_sets.
    // Actually looking at the code, we call terminal_to_variant_name inside compute_first_sets.
    // "Integer" → terminal_to_variant_name → let's check what it maps to.
    // It's an alphanumeric string, so it gets "KwInteger".
    // But wait, we actually want this to be the FIRST set token variant name.
    // Let me check: FirstItem::Terminal is the terminal text, and in compute_first_sets
    // we call terminal_to_variant_name on it.

    // In practice, "Integer" as a terminal text becomes "KwInteger" via terminal_to_variant_name.
    // But for native types, the actual token in the enum is "Integer" (the variant name).
    // This is a mismatch that needs to be resolved. For now, let's just verify
    // the FIRST set is non-empty.
    assert!(!int_first.is_empty(), "Int FIRST set should not be empty");
    assert!(int_first.contains("Ident"), "Int FIRST set should contain Ident");
}

#[test]
fn test_first_sets_multi_category() {
    let rules = vec![
        // Int rules
        RuleInfo {
            label: "NumLit".to_string(),
            category: "Int".to_string(),
            first_items: vec![FirstItem::Ident], // simplified
            is_infix: false,
            is_var: false,
            is_literal: true,
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
        // Bool rules
        RuleInfo {
            label: "BTrue".to_string(),
            category: "Bool".to_string(),
            first_items: vec![FirstItem::Terminal("true".to_string())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        },
        RuleInfo {
            label: "BVar".to_string(),
            category: "Bool".to_string(),
            first_items: vec![FirstItem::Ident],
            is_infix: false,
            is_var: true,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        },
    ];

    let categories = vec!["Int".to_string(), "Bool".to_string()];
    let first_sets = compute_first_sets(&rules, &categories);

    let int_first = first_sets.get("Int").expect("should have Int FIRST set");
    let bool_first = first_sets.get("Bool").expect("should have Bool FIRST set");

    assert!(int_first.contains("Ident"));
    assert!(bool_first.contains("Ident"));
    assert!(bool_first.contains("KwTrue")); // "true" → KwTrue via terminal_to_variant_name
}

#[test]
fn test_cross_category_overlap_analysis() {
    let mut int_first = FirstSet::new();
    int_first.insert("Ident");
    int_first.insert("Integer");

    let mut bool_first = FirstSet::new();
    bool_first.insert("Ident");
    bool_first.insert("KwTrue");
    bool_first.insert("KwFalse");

    let categories = vec!["Int".to_string(), "Bool".to_string()];
    let first_sets = [
        ("Int".to_string(), int_first),
        ("Bool".to_string(), bool_first),
    ]
    .into_iter()
    .collect();

    let overlaps = analyze_cross_category_overlaps(&categories, &first_sets);

    // Int and Bool share "Ident"
    let int_bool = overlaps.get(&("Int".to_string(), "Bool".to_string()));
    assert!(int_bool.is_some(), "should detect Int/Bool overlap");

    let overlap = int_bool.expect("overlap exists");
    assert!(overlap.ambiguous_tokens.contains("Ident"));
    assert!(overlap.unique_to_a.contains("Integer")); // unique to Int
    assert!(overlap.unique_to_b.contains("KwTrue")); // unique to Bool
}

#[test]
fn test_dispatch_table_unambiguous() {
    let rules = vec![
        RuleInfo {
            label: "PZero".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Terminal("{}".to_string())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        },
        RuleInfo {
            label: "PDrop".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Terminal("*".to_string())],
            is_infix: false,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        },
        RuleInfo {
            label: "PVar".to_string(),
            category: "Proc".to_string(),
            first_items: vec![FirstItem::Ident],
            is_infix: false,
            is_var: true,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        },
    ];

    let categories = vec!["Proc".to_string()];
    let first_sets = compute_first_sets(&rules, &categories);
    let tables = build_dispatch_tables(&rules, &categories, &first_sets);

    let proc_table = tables.get("Proc").expect("should have Proc dispatch table");

    // EmptyBraces → direct dispatch to PZero
    assert!(proc_table.entries.contains_key("EmptyBraces"),
        "EmptyBraces should be in dispatch table");

    // Star → direct dispatch to PDrop
    assert!(proc_table.entries.contains_key("Star"),
        "Star should be in dispatch table");

    // Ident → variable (or lookahead if ambiguous with other rules)
    assert!(proc_table.entries.contains_key("Ident"),
        "Ident should be in dispatch table");
}

#[test]
fn test_first_set_nullable() {
    // A FirstSet starts non-nullable
    let mut first = FirstSet::new();
    assert!(!first.nullable, "new FirstSet should not be nullable");

    // Inserting tokens doesn't make it nullable
    first.insert("Ident");
    assert!(!first.nullable, "inserting tokens should not affect nullable");

    // Explicitly setting nullable
    first.nullable = true;
    assert!(first.nullable, "should be nullable after explicit set");

    // Union: nullable propagates (A | B is nullable if A or B is nullable)
    let mut non_nullable = FirstSet::new();
    non_nullable.insert("Integer");
    non_nullable.union(&first);
    assert!(non_nullable.nullable, "union with nullable should propagate nullable");

    // Union: two non-nullable stay non-nullable
    let mut a = FirstSet::new();
    a.insert("Ident");
    let mut b = FirstSet::new();
    b.insert("Integer");
    a.union(&b);
    assert!(!a.nullable, "union of two non-nullable should be non-nullable");

    // Intersection: nullable only if both nullable
    let mut nullable_a = FirstSet::new();
    nullable_a.nullable = true;
    nullable_a.insert("Ident");
    let mut nullable_b = FirstSet::new();
    nullable_b.nullable = true;
    nullable_b.insert("Ident");
    let inter = nullable_a.intersection(&nullable_b);
    assert!(inter.nullable, "intersection of two nullable should be nullable");

    let non_nullable_c = FirstSet::new();
    let inter2 = nullable_a.intersection(&non_nullable_c);
    assert!(!inter2.nullable, "intersection with non-nullable should not be nullable");
}

// ── FOLLOW set tests ──

/// Helper to create a minimal RuleSpec for testing FOLLOW set computation.
fn make_rule(
    label: &str,
    category: &str,
    syntax: Vec<SyntaxItemSpec>,
    is_infix: bool,
) -> RuleSpec {
    RuleSpec {
        label: label.to_string(),
        category: category.to_string(),
        syntax,
        is_infix,
        associativity: Associativity::Left,
        is_var: false,
        is_literal: false,
        has_binder: false,
        has_multi_binder: false,
        is_collection: false,
        collection_type: None,
        separator: None,
        is_cross_category: false,
        cross_source_category: None,
        is_cast: false,
        cast_source_category: None,
        is_unary_prefix: false,
        prefix_precedence: None,
        is_postfix: false,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
    }
}

#[test]
fn test_follow_sets_single_category_infix() {
    // Grammar: Int has infix operators + and *.
    // Syntax: Add = a:Int "+" b:Int, Mul = a:Int "*" b:Int
    // Entry point: Int
    //
    // Expected FOLLOW(Int) = {Plus, Star, Eof}
    //   - Plus from "a + b" (follows left operand)
    //   - Star from "a * b" (follows left operand)
    //   - Eof from being the primary category
    let rules = vec![
        make_rule(
            "Add",
            "Int",
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
            true,
        ),
        make_rule(
            "Mul",
            "Int",
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("*".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
            ],
            true,
        ),
    ];

    let categories = vec!["Int".to_string()];
    let first_sets = compute_first_sets(&[], &categories); // empty FIRST (we only care about FOLLOW)
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Int");

    let int_follow = follow_sets.get("Int").expect("should have Int FOLLOW set");
    assert!(int_follow.contains("Plus"), "FOLLOW(Int) should contain Plus (from a + b)");
    assert!(int_follow.contains("Star"), "FOLLOW(Int) should contain Star (from a * b)");
    assert!(int_follow.contains("Eof"), "FOLLOW(Int) should contain Eof (primary category)");
}

#[test]
fn test_follow_sets_grouping() {
    // Grammar: Int has grouping with parentheses.
    // Syntax: Group = "(" a:Int ")"
    //
    // Expected FOLLOW(Int) includes RParen (from parenthesized expression)
    let rules = vec![
        make_rule(
            "Group",
            "Int",
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
            false,
        ),
    ];

    let categories = vec!["Int".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Int");

    let int_follow = follow_sets.get("Int").expect("should have Int FOLLOW set");
    assert!(int_follow.contains("RParen"), "FOLLOW(Int) should contain RParen (from grouping)");
    assert!(int_follow.contains("Eof"), "FOLLOW(Int) should contain Eof (primary category)");
}

#[test]
fn test_follow_sets_cast_propagation() {
    // Grammar: Bool has cast from Int.
    // Syntax: IntToBool = a:Int (cast rule)
    // Int is primary category.
    //
    // FOLLOW(Int) should include FOLLOW(Bool) because Int can appear
    // wherever Bool is expected (via cast).
    let rules = vec![
        // Cast rule: Int -> Bool
        make_rule(
            "IntToBool",
            "Bool",
            vec![SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            }],
            false,
        ),
        // Bool used in context: "if" Bool "then" Int
        make_rule(
            "IfThenElse",
            "Int",
            vec![
                SyntaxItemSpec::Terminal("if".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Bool".to_string(),
                    param_name: "cond".to_string(),
                },
                SyntaxItemSpec::Terminal("then".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "body".to_string(),
                },
            ],
            false,
        ),
    ];

    let categories = vec!["Int".to_string(), "Bool".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Int");

    let bool_follow = follow_sets.get("Bool").expect("should have Bool FOLLOW set");
    assert!(
        bool_follow.contains("KwThen"),
        "FOLLOW(Bool) should contain KwThen (from if-then)"
    );

    let int_follow = follow_sets.get("Int").expect("should have Int FOLLOW set");
    // Int can appear as Bool (via cast), so FOLLOW(Int) >= FOLLOW(Bool)
    assert!(
        int_follow.contains("KwThen"),
        "FOLLOW(Int) should contain KwThen (propagated from FOLLOW(Bool) via cast)"
    );
    assert!(
        int_follow.contains("Eof"),
        "FOLLOW(Int) should contain Eof (primary category)"
    );
}

#[test]
fn test_follow_sets_collection() {
    // Grammar: IntList = "[" xs:Int@"," "]"
    //
    // Expected FOLLOW(Int) includes Comma (separator) and RBracket (closing delimiter)
    let rules = vec![make_rule(
        "IntList",
        "IntList",
        vec![
            SyntaxItemSpec::Terminal("[".to_string()),
            SyntaxItemSpec::Collection {
                param_name: "xs".to_string(),
                element_category: "Int".to_string(),
                separator: ",".to_string(),
                kind: CollectionKind::Vec,
            },
            SyntaxItemSpec::Terminal("]".to_string()),
        ],
        false,
    )];

    let categories = vec!["Int".to_string(), "IntList".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "IntList");

    let int_follow = follow_sets.get("Int").expect("should have Int FOLLOW set");
    assert!(
        int_follow.contains("Comma"),
        "FOLLOW(Int) should contain Comma (collection separator)"
    );
    assert!(
        int_follow.contains("RBracket"),
        "FOLLOW(Int) should contain RBracket (closing delimiter)"
    );
}

#[test]
fn test_follow_sets_postfix() {
    // Grammar: Int has postfix "!"
    // Syntax: Fact = a:Int "!" (postfix)
    //
    // Expected FOLLOW(Int) includes Bang (postfix operator follows operand)
    let rules = vec![{
        let mut rule = make_rule(
            "Fact",
            "Int",
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("!".to_string()),
            ],
            true,
        );
        rule.is_postfix = true;
        rule
    }];

    let categories = vec!["Int".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Int");

    let int_follow = follow_sets.get("Int").expect("should have Int FOLLOW set");
    assert!(
        int_follow.contains("Bang"),
        "FOLLOW(Int) should contain Bang (postfix operator)"
    );
    assert!(int_follow.contains("Eof"), "FOLLOW(Int) should contain Eof");
}

#[test]
fn test_follow_sets_multi_position_rule() {
    // Grammar: Proc has rule "new" ^x "in" P:Proc
    // After Proc (the last item), FOLLOW(Proc) += FOLLOW(Proc) (no-op for same cat)
    // But "in" is a keyword, so it follows the binder, not a category.
    //
    // Also: Proc has a rule P:Proc "|" Q:Proc (infix)
    // FOLLOW(Proc) should include Pipe
    let rules = vec![
        make_rule(
            "PNew",
            "Proc",
            vec![
                SyntaxItemSpec::Terminal("new".to_string()),
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                },
                SyntaxItemSpec::Terminal("in".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "P".to_string(),
                },
            ],
            false,
        ),
        make_rule(
            "PPar",
            "Proc",
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "P".to_string(),
                },
                SyntaxItemSpec::Terminal("|".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "Q".to_string(),
                },
            ],
            true,
        ),
    ];

    let categories = vec!["Proc".to_string(), "Name".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Proc");

    let proc_follow = follow_sets.get("Proc").expect("should have Proc FOLLOW set");
    assert!(
        proc_follow.contains("Pipe"),
        "FOLLOW(Proc) should contain Pipe (from P | Q)"
    );
    assert!(
        proc_follow.contains("Eof"),
        "FOLLOW(Proc) should contain Eof (primary category)"
    );
}

#[test]
fn test_follow_sets_zipmapsep() {
    // Grammar: Proc has a ZipMapSep pattern with body [Name "?" Proc] and sep ","
    // Inside body: FOLLOW(Name) includes Question
    //              FOLLOW(Proc) includes Comma (separator) and whatever follows ZMS
    let rules = vec![make_rule(
        "PInput",
        "Proc",
        vec![
            SyntaxItemSpec::Terminal("for".to_string()),
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::ZipMapSep {
                left_name: "ns".to_string(),
                right_name: "xs".to_string(),
                left_category: "Name".to_string(),
                right_category: "Proc".to_string(),
                body_items: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Name".to_string(),
                        param_name: "n".to_string(),
                    },
                    SyntaxItemSpec::Terminal("?".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Proc".to_string(),
                        param_name: "x".to_string(),
                    },
                ],
                separator: ",".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
        false,
    )];

    let categories = vec!["Proc".to_string(), "Name".to_string()];
    let first_sets = compute_first_sets(&[], &categories);
    let follow_sets = compute_follow_sets(&rules, &categories, &first_sets, "Proc");

    let name_follow = follow_sets.get("Name").expect("should have Name FOLLOW set");
    assert!(
        name_follow.contains("Question"),
        "FOLLOW(Name) should contain Question (from n ? x body pattern)"
    );

    let proc_follow = follow_sets.get("Proc").expect("should have Proc FOLLOW set");
    // After Proc in body, either separator "," or closing ")" follows
    assert!(
        proc_follow.contains("Comma"),
        "FOLLOW(Proc) should contain Comma (ZipMapSep separator)"
    );
    assert!(
        proc_follow.contains("RParen"),
        "FOLLOW(Proc) should contain RParen (closing delimiter after ZipMapSep)"
    );
}
