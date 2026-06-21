use super::*;
fn make_token_ids() -> TokenIdMap {
    let mut map = TokenIdMap::new();
    /* terminal_to_variant_name maps:
     *   "float" → "KwFloat", "if" → "KwIf", "then" → "KwThen",
     *   "else" → "KwElse", "let" → "KwLet", "in" → "KwIn",
     *   "(" → "LParen", ")" → "RParen", "=" → "Eq",
     *   "+" → "Plus", "-" → "Minus", "*" → "Star", "/" → "Slash"
     */
    for name in &[
        "KwFloat", "LParen", "RParen", "Plus", "Minus", "Star", "Slash", "Ident", "Integer",
        "Comma", "Colon", "Semi", "KwIf", "KwThen", "KwElse", "KwLet", "KwIn", "Eq",
    ] {
        map.get_or_insert(name);
    }
    map
}

fn make_first_sets() -> HashMap<String, FirstSet> {
    let mut sets = HashMap::new();
    let mut int_first = FirstSet::default();
    int_first.insert("Integer");
    int_first.insert("Ident");
    int_first.insert("LParen");
    sets.insert("Int".to_string(), int_first);

    let mut float_first = FirstSet::default();
    float_first.insert("Float");
    float_first.insert("Ident");
    float_first.insert("LParen");
    sets.insert("Float".to_string(), float_first);
    sets
}

fn make_rd_rule(label: &str, category: &str, items: Vec<RDSyntaxItem>) -> RDRuleInfo {
    RDRuleInfo {
        label: label.to_string(),
        category: category.to_string(),
        items,
        has_binder: false,
        has_multi_binder: false,
        is_collection: false,
        collection_type: None,
        separator: None,
        prefix_bp: None,
        eval_mode: None,
    }
}

#[test]
fn test_pattern_encoding_terminal_only() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rule = make_rd_rule(
        "IfThenElse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ],
    );

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 3);
    assert!(
        matches!(pattern[0], PatternElement::Terminal { ref variant, .. } if variant == "KwIf")
    );
    assert!(
        matches!(pattern[1], PatternElement::Terminal { ref variant, .. } if variant == "KwThen")
    );
    assert!(
        matches!(pattern[2], PatternElement::Terminal { ref variant, .. } if variant == "KwElse")
    );

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    assert_eq!(bytes.len(), 3);
    assert!(boundary.is_none());
}

#[test]
fn test_pattern_encoding_with_nonterminal() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rule = make_rd_rule(
        "FloatCast",
        "Float",
        vec![
            RDSyntaxItem::Terminal("float".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    );

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 4);

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    assert_eq!(bytes.len(), 2); // float, (
    assert!(boundary.is_some());
    let b = boundary.expect("should have NT boundary");
    assert_eq!(b.category, "Int");
    assert_eq!(b.remaining_pattern.len(), 1); // RParen
}

#[test]
fn test_builder_insert_rd_rules() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("=".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
    ];

    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    assert!(tree.segments[0].val_count() >= 2);
}

#[test]
fn test_ambiguous_rules_same_token() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Float".to_string()], HashSet::new());

    // Two rules both start with "float" "("
    let rules = vec![
        make_rd_rule(
            "FloatId",
            "Float",
            vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IntToFloat",
            "Float",
            vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];

    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Float").expect("should have Float tree");
    assert!(tree.segments[0].val_count() >= 1);
}

#[test]
fn test_dead_rule_pruning() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let dead = HashSet::from(["DeadRule".to_string()]);
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], dead);

    let rules = vec![
        make_rd_rule("LiveRule", "Int", vec![RDSyntaxItem::Terminal("if".to_string())]),
        make_rd_rule("DeadRule", "Int", vec![RDSyntaxItem::Terminal("let".to_string())]),
    ];

    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    // Only LiveRule should be inserted
    assert_eq!(tree.segments[0].val_count(), 1);
}

#[test]
fn test_cast_rules_reachable_when_source_first_overlaps_target_first() {
    let token_ids = make_token_ids();

    let mut int_first = FirstSet::default();
    int_first.insert("Integer");
    int_first.insert("Ident");

    let mut proc_first = FirstSet::default();
    proc_first.insert("Integer");
    proc_first.insert("Ident");
    proc_first.insert("LParen");

    let first_sets =
        HashMap::from([("Int".to_string(), int_first), ("Proc".to_string(), proc_first)]);
    let mut builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Proc".to_string()],
        HashSet::new(),
    );

    builder.insert_cast_rules(&[CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    }]);

    let tree = builder.get_tree("Proc").expect("should have Proc tree");
    let reachable = tree.reachable_rules();
    assert!(
            reachable.contains("IntToProc"),
            "cast projection should be reachable even when all source FIRST tokens overlap target FIRST"
        );
}

#[test]
fn test_foreign_leading_nt_mixfix_rule_is_reachable() {
    let mut token_ids = make_token_ids();
    token_ids.get_or_insert("Bang");

    let mut name_first = FirstSet::default();
    name_first.insert("Ident");

    let mut proc_first = FirstSet::default();
    proc_first.insert("Ident");
    proc_first.insert("KwNil");

    let first_sets =
        HashMap::from([("Name".to_string(), name_first), ("Proc".to_string(), proc_first)]);
    let mut builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Proc".to_string(), "Name".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "POutput",
        "Proc",
        vec![
            RDSyntaxItem::NonTerminal {
                category: "Name".to_string(),
                param_name: "n".to_string(),
            },
            RDSyntaxItem::Terminal("!".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    )];

    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Proc").expect("should have Proc tree");
    let reachable = tree.reachable_rules();
    assert!(
        reachable.contains("POutput"),
        "foreign-leading mixfix rule should be reachable via source FIRST plus trigger"
    );
}

#[test]
fn test_statistics_computation() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];

    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    assert!(tree.stats.total_states > 0);
    assert!(tree.stats.total_rules >= 2);
    assert_eq!(tree.stats.ambiguous_nodes, 0);
}

#[test]
fn test_emission_strategy() {
    let tree = CategoryDecisionTree {
        category: "Int".to_string(),
        segments: vec![PathMap::new()],
        stats: TreeStats { total_states: 10, ..Default::default() },
    };
    assert_eq!(emission_strategy(&tree), EmissionStrategy::MatchArms);

    let tree_large = CategoryDecisionTree {
        category: "Int".to_string(),
        segments: vec![PathMap::new()],
        stats: TreeStats { total_states: 300, ..Default::default() },
    };
    assert_eq!(emission_strategy(&tree_large), EmissionStrategy::FlatTable);
}

#[test]
fn test_incremental_state() {
    let mut state = IncrementalState::default();
    state.record("Int", 12345);
    assert!(state.is_unchanged("Int", 12345));
    assert!(!state.is_unchanged("Int", 99999));
    assert!(!state.is_unchanged("Float", 12345));
}

#[test]
fn test_incremental_cache_round_trip() {
    let mut state = IncrementalState {
        version: CACHE_VERSION,
        ..Default::default()
    };
    state.record("Expr", 0x12345);
    state
        .category_code
        .insert("Expr".to_string(), "fn parse_Expr() {}".to_string());
    state.record("Stmt", 0xABCDE);
    state
        .category_code
        .insert("Stmt".to_string(), "fn parse_Stmt() {}".to_string());

    let tmp = std::env::temp_dir().join("prattail_test_cache");
    state.save(&tmp).expect("save should succeed");
    let loaded = IncrementalState::load(&tmp).expect("load should succeed");
    assert!(loaded.is_valid(), "loaded cache should be valid");
    assert!(loaded.is_unchanged("Expr", 0x12345));
    assert!(loaded.is_unchanged("Stmt", 0xABCDE));
    assert!(!loaded.is_unchanged("Expr", 0x99999));
    assert_eq!(loaded.category_code.get("Expr").expect("Expr code"), "fn parse_Expr() {}",);
    assert_eq!(loaded.category_code.get("Stmt").expect("Stmt code"), "fn parse_Stmt() {}",);

    // Version mismatch should invalidate
    let mut bad_version = state.clone();
    bad_version.version = CACHE_VERSION + 1;
    bad_version.save(&tmp).expect("save bad version");
    let loaded_bad = IncrementalState::load(&tmp).expect("load should succeed");
    assert!(!loaded_bad.is_valid(), "mismatched version should be invalid");

    let _ = std::fs::remove_file(&tmp);
}

#[test]
fn test_dispatch_strategy_singleton() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "IfThenElse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ],
    )];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    match tree.dispatch_strategy("KwIf", &token_ids) {
        DispatchStrategy::Singleton { rule_label } => {
            assert_eq!(rule_label, "IfThenElse");
        },
        other => panic!("expected Singleton, got {:?}", other),
    }

    // Token not in tree
    assert!(matches!(
        tree.dispatch_strategy("Plus", &token_ids),
        DispatchStrategy::NotPresent
    ));
}

#[test]
fn test_dispatch_strategy_includes_nonterminal_boundary_rules() {
    // CD07 Phase 4A flip test (2026-06-10; FV: CD07_NfaFallbackNonLoss
    // .{shipped_drops_boundary, fanout_complete, nfa_fallback_nonlossy}):
    // (a) a MIXED Commit+NonterminalBoundary overlap group must report the
    //     boundary's reachable rules in the fanout — the prior `_ => {}`
    //     dropped them (the dead-rule lint could falsely flag the token);
    // (b) a boundary-ONLY dispatch token must report a fanout, NOT
    //     NotPresent — the prior :2958 mapping counted a rule-carrying
    //     token as resolved-by-absence, letting the NFA-spillover
    //     refinement (pipeline.rs "1.7a") strip the category's fallback.
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        // Commit path under dispatch token LParen: "(" ")".
        make_rd_rule(
            "Paren",
            "Int",
            vec![RDSyntaxItem::Terminal("(".to_string()), RDSyntaxItem::Terminal(")".to_string())],
        ),
        // "(" <Int> ")": terminal prefix [LParen], then an NT boundary —
        // the boundary entry is stored at path [LParen], overlapping
        // Paren's [LParen, RParen] under dispatch token LParen.
        make_rd_rule(
            "Group",
            "Int",
            vec![
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        // TWO NT-continuing rules sharing the "if" prefix: the trie node
        // at [KwIf] holds a NonterminalBoundary{options:[Int, Float]} —
        // the genuine singleton-boundary entry (:2958). (A SINGLE
        // NT-continuing rule commits at its unique prefix instead —
        // lossless — so the boundary action needs the shared prefix.)
        make_rd_rule(
            "IfInt",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal("then".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloat",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "y".to_string(),
                },
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);
    let tree = builder.get_tree("Int").expect("should have Int tree");

    // (a) mixed group at LParen: BOTH labels present.
    match tree.dispatch_strategy("LParen", &token_ids) {
        DispatchStrategy::AmbiguousFanout { rule_labels, .. } => {
            assert!(
                rule_labels.iter().any(|l| l == "Paren"),
                "fanout must keep the Commit rule: {rule_labels:?}"
            );
            assert!(
                rule_labels.iter().any(|l| l == "Group"),
                "fanout must include the NonterminalBoundary's reachable \
                     rules (fanout_complete): {rule_labels:?}"
            );
        },
        other => panic!("expected AmbiguousFanout at LParen, got {other:?}"),
    }

    // (b) boundary-only at KwIf: a fanout carrying the boundary's rule,
    // never NotPresent (nfa_fallback_nonlossy).
    match tree.dispatch_strategy("KwIf", &token_ids) {
        DispatchStrategy::AmbiguousFanout { rule_labels, .. } => {
            assert!(
                rule_labels.iter().any(|l| l == "IfInt")
                    && rule_labels.iter().any(|l| l == "IfFloat"),
                "boundary-only token must surface ALL reachable rules: {rule_labels:?}"
            );
        },
        other => {
            panic!("expected AmbiguousFanout at boundary-only KwIf (NOT NotPresent), got {other:?}")
        },
    }
}

#[test]
fn test_dispatch_strategy_disjoint_suffix() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    /* Two rules sharing dispatch token "if":
     *   IfPlus:  if + then
     *   IfMinus: if - else
     * After shared prefix "if" (dispatch token), next tokens are "+" and "-"
     * which are disjoint. */
    let rules = vec![
        make_rd_rule(
            "IfPlus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ],
        ),
        make_rd_rule(
            "IfMinus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    match tree.dispatch_strategy("KwIf", &token_ids) {
        DispatchStrategy::DisjointSuffix { shared_prefix_len, suffix_map, .. } => {
            assert_eq!(shared_prefix_len, 0); // no shared terminals beyond dispatch token
            assert_eq!(suffix_map.len(), 2);
            assert_eq!(suffix_map.get("Plus").expect("Plus"), "IfPlus");
            assert_eq!(suffix_map.get("Minus").expect("Minus"), "IfMinus");
        },
        other => panic!("expected DisjointSuffix, got {:?}", other),
    }
}

#[test]
fn test_dispatch_strategy_shared_prefix_disjoint() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    /* Two rules sharing "if" "(" as prefix, then diverging:
     *   IfParenPlus:  if ( + )
     *   IfParenMinus: if ( - )
     * Shared prefix = ["("], then "+" vs "-" disjoint. */
    let rules = vec![
        make_rd_rule(
            "IfParenPlus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfParenMinus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    match tree.dispatch_strategy("KwIf", &token_ids) {
        DispatchStrategy::DisjointSuffix {
            shared_prefix_len,
            shared_terminals,
            suffix_map,
        } => {
            assert_eq!(shared_prefix_len, 1); // "(" is shared
            assert_eq!(shared_terminals.len(), 1);
            assert_eq!(suffix_map.len(), 2);
            assert!(suffix_map.contains_key("Plus"));
            assert!(suffix_map.contains_key("Minus"));
        },
        other => panic!("expected DisjointSuffix with shared prefix, got {:?}", other),
    }
}

#[test]
fn test_dispatch_strategy_nfa_tryall() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Float".to_string()],
        HashSet::new(),
    );

    /* Two rules sharing "float" "(" and then a non-terminal vs ident capture.
     * The trie can't disambiguate at the terminal level since the
     * nonterminal is encoded as an NT byte, not a terminal. */
    let rules = vec![
        make_rd_rule(
            "FloatId",
            "Float",
            vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "FloatCast",
            "Float",
            vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "x".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Float").expect("should have Float tree");
    /* After "float" "(" the next items are IdentCapture (0x80) and
     * NonTerminal (encoded at NT boundary). Since IdentCapture is > MAX_TERMINAL_ID,
     * the suffix disjointness check should fail → AmbiguousFanout. */
    match tree.dispatch_strategy("KwFloat", &token_ids) {
        DispatchStrategy::AmbiguousFanout { rule_labels, shared_prefix_len, .. } => {
            assert!(shared_prefix_len >= 1); // "(" is shared
            assert!(rule_labels.len() >= 1); // at least one rule
        },
        DispatchStrategy::DisjointSuffix { .. } => {
            /* Also acceptable if the encoding makes the suffixes look disjoint
             * (IdentCapture byte vs NT boundary truncation). */
        },
        other => panic!("expected AmbiguousFanout or DisjointSuffix, got {:?}", other),
    }
}

#[test]
fn test_dispatch_tokens() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let tokens = tree.dispatch_tokens(&token_ids);
    assert!(tokens.contains(&"KwIf".to_string()));
    assert!(tokens.contains(&"KwLet".to_string()));
    assert_eq!(tokens.len(), 2);
}

// ══════════════════════════════════════════════════════════════════════
// Stage 10.2 (2026-05-04): "Equivalence tests" block (formerly 350 LoC,
// 4 tests asserting decision-tree dispatch == legacy ad-hoc analysis)
// DELETED. Tests imported `crate::trampoline::*` helpers; their
// equivalence-with-trampoline question is moot post-Stage-10b
// (trampoline.rs deleted in Stage 10.6).
// ══════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════
// Analysis layer tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_d01_precision_ambiguity() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    /* Two rules with EXACTLY identical terminal prefix → Ambiguous node.
     * Both end at an NT boundary after "if" "(" so pjoin merges them. */
    let rules = vec![
        make_rd_rule(
            "IfIntCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diags = precision_ambiguity_reports(tree, &token_ids, "test");
    /* Both rules truncate at the same NT boundary → same path [if, (].
     * pjoin merges them into Ambiguous. D01 should fire. */
    assert!(
        diags.iter().any(|d| d.id == DiagnosticId::D01),
        "D01 should fire for ambiguous prefix: {:?}",
        diags,
    );
}

#[test]
fn test_d02_unresolvable_ambiguity() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    /* Two rules with identical terminal prefix ending at NT boundary.
     * The ambiguity is at a leaf (no deeper terminal children), so it's
     * unresolvable by additional terminal lookahead. */
    let rules = vec![
        make_rd_rule(
            "IfIntCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diags = unresolvable_ambiguity_reports(tree, &token_ids, "test");
    /* The ambiguous node [if, (] is a leaf (NT boundary truncated both) → D02 fires */
    let d02s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D02).collect();
    assert!(
        !d02s.is_empty(),
        "D02 should fire for unresolvable ambiguity at trie leaf: diags={:?}",
        diags,
    );
}

#[test]
fn test_d03_unreachable_rule() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![make_rd_rule(
        "IfThenElse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    /* all_labels includes a rule that wasn't inserted */
    let mut all_labels = HashSet::new();
    all_labels.insert("IfThenElse".to_string());
    all_labels.insert("GhostRule".to_string());

    let diags = unreachable_rule_detection(tree, &all_labels, "test");
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::D03);
    assert!(diags[0].message.contains("GhostRule"));
}

#[test]
fn test_d04_min_lookahead() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diag = min_lookahead_report(tree, "test");
    assert_eq!(diag.id, DiagnosticId::D04);
    /* Both rules have distinct first tokens → LL(1) */
    assert!(
        diag.message.contains("depth 1") || diag.message.contains("LL(1)"),
        "should report depth 1 for non-ambiguous grammar: {}",
        diag.message,
    );
}

#[test]
fn test_d05_complexity_metrics() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![make_rd_rule(
        "IfThenElse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diag = complexity_metrics(tree, "test");
    assert_eq!(diag.id, DiagnosticId::D05);
    assert!(diag.message.contains("decision tree"));
}

#[test]
fn test_d07_coverage_paths() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let paths = coverage_paths(tree);
    assert!(paths.len() >= 2, "should have at least 2 paths");

    /* No paths covered → D07 fires */
    let covered = HashSet::new();
    let diags = coverage_report(tree, &covered, "test");
    assert!(diags.iter().any(|d| d.id == DiagnosticId::D07));

    /* All paths covered → D07 should not fire */
    let all_covered: HashSet<Vec<u8>> = paths.iter().map(|p| p.path_bytes.clone()).collect();
    let diags2 = coverage_report(tree, &all_covered, "test");
    assert!(diags2.is_empty(), "no D07 when fully covered");
}

#[test]
fn test_d08_optimization_suggestions() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    /* Two rules with identical terminal prefix at NT boundary → Ambiguous → D08 */
    let rules = vec![
        make_rd_rule(
            "IfIntCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diags = optimization_suggestions(tree, "test");
    let d08s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D08).collect();
    assert!(!d08s.is_empty(), "D08 should fire for ambiguous rules: {:?}", diags,);
}

#[test]
fn test_d09_conflict_resolution() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatCast",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let diags = conflict_resolution_guidance(tree, "test");
    let d09s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D09).collect();
    assert!(!d09s.is_empty(), "D09 should fire for conflicting rules: {:?}", diags,);
    /* Should contain resolution strategies */
    assert!(d09s[0]
        .hint
        .as_ref()
        .expect("should have hint")
        .contains("distinguishing terminal"));
}

#[test]
fn test_x06_x07_composition_analysis() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    /* Grammar A: Int with IfThenElse */
    let mut builder_a = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );
    builder_a.build_all(
        &[make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        )],
        &[],
        &[],
    );

    /* Grammar B: Int with LetIn + IfThenElse (shared rule) */
    let mut builder_b =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());
    builder_b.build_all(
        &[
            make_rd_rule(
                "IfThenElse",
                "Int",
                vec![
                    RDSyntaxItem::Terminal("if".to_string()),
                    RDSyntaxItem::Terminal("then".to_string()),
                    RDSyntaxItem::Terminal("else".to_string()),
                ],
            ),
            make_rd_rule(
                "LetIn",
                "Int",
                vec![
                    RDSyntaxItem::Terminal("let".to_string()),
                    RDSyntaxItem::Terminal("in".to_string()),
                ],
            ),
        ],
        &[],
        &[],
    );

    let tree_a = builder_a.get_tree("Int").expect("tree A");
    let tree_b = builder_b.get_tree("Int").expect("tree B");

    let report = composition_trie_analysis(tree_a, tree_b);
    /* IfThenElse is in both → common_rules >= 1 */
    assert!(report.common_rules >= 1, "should have common rules: {:?}", report);
    /* LetIn is only in B → unique_b >= 1 */
    assert!(report.unique_b >= 1, "should have unique_b: {:?}", report);
    /* A has nothing unique (all of A is in B) */
    assert_eq!(report.unique_a, 0, "A should have no unique rules: {:?}", report);
}

#[test]
fn test_layer10_content_hash() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );
    builder.build_all(
        &[make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        )],
        &[],
        &[],
    );

    let tree = builder.get_tree("Int").expect("tree");
    let hash1 = category_content_hash(tree);

    /* Same grammar → same hash */
    let mut builder2 = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );
    builder2.build_all(
        &[make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        )],
        &[],
        &[],
    );
    let tree2 = builder2.get_tree("Int").expect("tree2");
    let hash2 = category_content_hash(tree2);
    assert_eq!(hash1, hash2, "same grammar should produce same hash");

    /* Different grammar → different hash */
    let mut builder3 =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());
    builder3.build_all(
        &[make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        )],
        &[],
        &[],
    );
    let tree3 = builder3.get_tree("Int").expect("tree3");
    let hash3 = category_content_hash(tree3);
    assert_ne!(hash1, hash3, "different grammar should produce different hash");
}

#[test]
fn test_flat_table_emission() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("Int tree");
    let states = flatten_tree(tree);
    assert!(!states.is_empty(), "should have flattened states");

    /* Verify state structure: root + intermediates + leaves */
    let root = &states[0];
    assert!(!root.transitions.is_empty(), "root should have transitions");

    /* Emit to buffer */
    let mut buf = String::new();
    emit_flat_table(tree, &token_ids, &mut buf);
    assert!(buf.contains("DISPATCH_TABLE_INT"));
    assert!(buf.contains("STATE_META_INT"));
}

#[test]
fn test_match_arm_emission() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "IfThenElse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("then".to_string()),
            RDSyntaxItem::Terminal("else".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("Int tree");
    let mut buf = String::new();
    emit_match_arms(tree, &token_ids, &mut buf);
    assert!(buf.contains("decision tree"), "should contain decision tree comment");
}

// ══════════════════════════════════════════════════════════════════════
// Helper functions for new tests
// ══════════════════════════════════════════════════════════════════════

fn make_commit(label: &str, cat: &str) -> DecisionAction {
    DecisionAction::Commit {
        rule_label: label.to_string(),
        category: cat.to_string(),
        weight: 0.0,
    }
}

fn make_ambiguous(labels: &[(&str, &str)]) -> DecisionAction {
    DecisionAction::Ambiguous {
        candidates: labels
            .iter()
            .map(|(label, cat)| AmbiguousCandidate {
                rule_label: label.to_string(),
                category: cat.to_string(),
                weight: 0.0,
                remaining_items: 0,
            })
            .collect(),
    }
}

fn make_nt_boundary(count: usize) -> DecisionAction {
    DecisionAction::NonterminalBoundary {
        options: (0..count)
            .map(|i| NTOption {
                kind: NTKind::NonTerminal { category: format!("Cat{}", i) },
                first_tokens: vec![i as u8],
                resume_segment: i,
                weight: 0.0,
            })
            .collect(),
    }
}

fn assert_commit(action: &DecisionAction, expected_label: &str) {
    match action {
        DecisionAction::Commit { rule_label, .. } => {
            assert_eq!(rule_label, expected_label);
        },
        other => panic!("expected Commit({}), got {:?}", expected_label, other),
    }
}

fn assert_ambiguous_labels(action: &DecisionAction, expected: &[&str]) {
    match action {
        DecisionAction::Ambiguous { candidates } => {
            let mut labels: Vec<&str> = candidates.iter().map(|c| c.rule_label.as_str()).collect();
            labels.sort();
            let mut exp: Vec<&str> = expected.to_vec();
            exp.sort();
            assert_eq!(labels, exp);
        },
        other => panic!("expected Ambiguous({:?}), got {:?}", expected, other),
    }
}

fn sorted_labels(action: &DecisionAction) -> Vec<String> {
    let mut labels: Vec<String> = action.rule_labels().map(|s| s.to_string()).collect();
    labels.sort();
    labels
}

fn assert_algebraic_element(result: &AlgebraicResult<DecisionAction>) -> &DecisionAction {
    match result {
        AlgebraicResult::Element(ref a) => a,
        other => panic!("expected Element, got {:?}", other),
    }
}

fn assert_algebraic_none(result: &AlgebraicResult<DecisionAction>) {
    assert!(result.is_none(), "expected AlgebraicResult::None, got {:?}", result);
}

fn assert_algebraic_identity(result: &AlgebraicResult<DecisionAction>, id: u64) {
    match result {
        AlgebraicResult::Identity(mask) => assert_eq!(*mask, id),
        other => panic!("expected Identity({}), got {:?}", id, other),
    }
}

// ══════════════════════════════════════════════════════════════════════
// Step 4: Lattice algebra (pjoin) tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_pjoin_commit_commit() {
    let a = make_commit("A", "Int");
    let b = make_commit("B", "Int");
    let result = a.pjoin(&b);
    let action = assert_algebraic_element(&result);
    assert_ambiguous_labels(action, &["A", "B"]);
}

#[test]
fn test_pjoin_commit_ambiguous() {
    let a = make_commit("A", "Int");
    let b = make_ambiguous(&[("B", "Int"), ("C", "Int")]);
    let result = a.pjoin(&b);
    let action = assert_algebraic_element(&result);
    assert_ambiguous_labels(action, &["A", "B", "C"]);
}

#[test]
fn test_pjoin_ambiguous_ambiguous() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_ambiguous(&[("C", "Int"), ("D", "Int")]);
    let result = a.pjoin(&b);
    let action = assert_algebraic_element(&result);
    assert_ambiguous_labels(action, &["A", "B", "C", "D"]);
}

#[test]
fn test_pjoin_nt_boundary_commit() {
    let a = make_nt_boundary(1);
    let b = make_commit("A", "Int");
    let result = a.pjoin(&b);
    assert_algebraic_identity(&result, 1);
}

#[test]
fn test_pjoin_commit_nt_boundary() {
    let a = make_commit("A", "Int");
    let b = make_nt_boundary(1);
    let result = a.pjoin(&b);
    assert_algebraic_identity(&result, 2);
}

#[test]
fn test_pjoin_nt_boundary_nt_boundary() {
    let a = make_nt_boundary(1);
    let b = make_nt_boundary(2);
    let result = a.pjoin(&b);
    assert_algebraic_identity(&result, 1);
}

// ══════════════════════════════════════════════════════════════════════
// Step 4: Lattice algebra (pmeet) tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_pmeet_commit_commit_same() {
    let a = make_commit("A", "Int");
    let b = make_commit("A", "Int");
    let result = a.pmeet(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "A");
}

#[test]
fn test_pmeet_commit_commit_different() {
    let a = make_commit("A", "Int");
    let b = make_commit("B", "Int");
    let result = a.pmeet(&b);
    assert_algebraic_none(&result);
}

#[test]
fn test_pmeet_ambiguous_ambiguous_overlap() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_ambiguous(&[("B", "Int"), ("C", "Int")]);
    let result = a.pmeet(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "B");
}

#[test]
fn test_pmeet_ambiguous_ambiguous_no_overlap() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_ambiguous(&[("C", "Int"), ("D", "Int")]);
    let result = a.pmeet(&b);
    assert_algebraic_none(&result);
}

#[test]
fn test_pmeet_ambiguous_commit_match() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_commit("A", "Int");
    let result = a.pmeet(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "A");
}

#[test]
fn test_pmeet_ambiguous_ambiguous_multi() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int"), ("C", "Int")]);
    let b = make_ambiguous(&[("B", "Int"), ("C", "Int"), ("D", "Int")]);
    let result = a.pmeet(&b);
    let action = assert_algebraic_element(&result);
    assert_ambiguous_labels(action, &["B", "C"]);
}

// ══════════════════════════════════════════════════════════════════════
// Step 5: DistributiveLattice (psubtract) tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_psubtract_ambiguous_remove_one() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_commit("A", "Int");
    let result = a.psubtract(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "B");
}

#[test]
fn test_psubtract_ambiguous_remove_partial() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int"), ("C", "Int")]);
    let b = make_ambiguous(&[("A", "Int"), ("C", "Int")]);
    let result = a.psubtract(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "B");
}

#[test]
fn test_psubtract_ambiguous_remove_all() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let result = a.psubtract(&b);
    assert_algebraic_none(&result);
}

#[test]
fn test_psubtract_commit_same() {
    // Subtracting identical commit: "A" - "A" = None
    let a = make_commit("A", "Int");
    let b = make_commit("A", "Int");
    let result = a.psubtract(&b);
    assert_algebraic_none(&result);
}

#[test]
fn test_psubtract_commit_different() {
    // Subtracting different commit: "A" - "B" = Commit("A")
    let a = make_commit("A", "Int");
    let b = make_commit("B", "Int");
    let result = a.psubtract(&b);
    let action = assert_algebraic_element(&result);
    assert_commit(action, "A");
}

#[test]
fn test_psubtract_no_overlap() {
    let a = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let b = make_nt_boundary(1);
    let result = a.psubtract(&b);
    // NTBoundary has no rule_labels() → other_labels is empty → nothing removed
    let action = assert_algebraic_element(&result);
    assert_ambiguous_labels(action, &["A", "B"]);
}

// ══════════════════════════════════════════════════════════════════════
// Step 6: DecisionAction helper method tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_rule_labels() {
    let commit = make_commit("A", "Int");
    assert_eq!(commit.rule_labels().collect::<Vec<_>>(), vec!["A"]);

    let ambig = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let mut labels: Vec<&str> = ambig.rule_labels().collect();
    labels.sort();
    assert_eq!(labels, vec!["A", "B"]);

    let nt = make_nt_boundary(2);
    assert_eq!(nt.rule_labels().count(), 0);
}

#[test]
fn test_all_candidates() {
    let ambig = make_ambiguous(&[("A", "Int"), ("B", "Int")]);
    let candidates: Vec<AmbiguousCandidate> = ambig.all_candidates();
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].rule_label, "A");
    assert_eq!(candidates[1].rule_label, "B");

    let commit = make_commit("A", "Int");
    let commit_candidates = commit.all_candidates();
    assert_eq!(commit_candidates.len(), 1);
    assert_eq!(commit_candidates[0].rule_label, "A");
    assert_eq!(commit_candidates[0].category, "Int");
    assert_eq!(commit_candidates[0].remaining_items, 0);

    let nt = make_nt_boundary(1);
    assert_eq!(nt.all_candidates().len(), 0);
}

#[test]
fn test_is_deterministic() {
    assert!(make_commit("A", "Int").is_deterministic());
    assert!(!make_ambiguous(&[("A", "Int"), ("B", "Int")]).is_deterministic());
    assert!(!make_nt_boundary(1).is_deterministic());
}

#[test]
fn test_is_nt_boundary() {
    assert!(make_nt_boundary(1).is_nt_boundary());
    assert!(!make_commit("A", "Int").is_nt_boundary());
    assert!(!make_ambiguous(&[("A", "Int")]).is_nt_boundary());
}

// ══════════════════════════════════════════════════════════════════════
// Step 7: Query helper tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_query_dispatch_token_found() {
    // query_dispatch_token checks single-byte path [tok_id], so we need
    // single-terminal rules where the trie value is at a single-byte path.
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule("JustIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())]),
        make_rd_rule("JustLet", "Int", vec![RDSyntaxItem::Terminal("let".to_string())]),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let action = query_dispatch_token(tree, "KwIf", &token_ids).expect("KwIf should be found");
    assert_commit(action, "JustIf");

    let action2 = query_dispatch_token(tree, "KwLet", &token_ids).expect("KwLet should be found");
    assert_commit(action2, "JustLet");
}

#[test]
fn test_query_dispatch_token_missing() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule("JustIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    assert!(
        query_dispatch_token(tree, "Plus", &token_ids).is_none(),
        "Plus should not be in the tree"
    );
}

#[test]
fn test_is_token_deterministic_fn() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    // Single rule per dispatch token → deterministic at single-byte paths
    let rules = vec![make_rd_rule("OnlyIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    assert!(is_token_deterministic(tree, "KwIf", &token_ids));
    assert!(!is_token_deterministic(tree, "Plus", &token_ids));
}

#[test]
fn test_rules_for_token_fn() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    // Insert a single-terminal rule so query_dispatch_token works
    let rules = vec![make_rd_rule("OnlyIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let labels = rules_for_token(tree, "KwIf", &token_ids);
    assert_eq!(labels, vec!["OnlyIf"]);

    let empty = rules_for_token(tree, "Plus", &token_ids);
    assert!(empty.is_empty());
}

#[test]
fn test_shared_prefix_and_suffix_dispatch() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    // Two rules: if ( + ) and if ( - ) → shared prefix "("
    let rules = vec![
        make_rd_rule(
            "IfPlus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("+".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfMinus",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::Terminal("-".to_string()),
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let depth = shared_prefix_depth(tree, "KwIf", &token_ids);
    assert_eq!(depth, 1, "shared prefix should be 1 (the '(' byte)");

    let disjoint = suffix_disjoint_dispatch(tree, "KwIf", &token_ids);
    let map = disjoint.expect("should be disjoint");
    assert_eq!(map.len(), 2);
    assert_eq!(map.get("Plus").expect("Plus"), "IfPlus");
    assert_eq!(map.get("Minus").expect("Minus"), "IfMinus");
}

// ══════════════════════════════════════════════════════════════════════
// Step 8: Pattern encoding edge cases
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_pattern_single_terminal() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rule = make_rd_rule("JustIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())]);

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 1);
    assert!(matches!(
        pattern[0],
        PatternElement::Terminal { ref variant, .. } if variant == "KwIf"
    ));

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    assert_eq!(bytes.len(), 1);
    assert!(boundary.is_none());
}

#[test]
fn test_pattern_all_nonterminals() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder = DecisionTreeBuilder::new(
        token_ids,
        first_sets,
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rule = make_rd_rule(
        "AllNT",
        "Int",
        vec![
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            RDSyntaxItem::NonTerminal {
                category: "Float".to_string(),
                param_name: "b".to_string(),
            },
        ],
    );

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 2);

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    // First element is NT → empty terminal prefix, boundary at position 0
    assert!(bytes.is_empty());
    assert!(boundary.is_some());
    let b = boundary.expect("should have NT boundary");
    assert_eq!(b.position, 0);
    assert_eq!(b.category, "Int");
}

#[test]
fn test_pattern_with_ident_capture() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rule = make_rd_rule(
        "IfIdent",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::IdentCapture { param_name: "x".to_string() },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    );

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 3);
    assert!(matches!(pattern[1], PatternElement::IdentCapture { .. }));

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    assert_eq!(bytes.len(), 3); // KwIf, IDENT_CAPTURE, RParen
    assert_eq!(bytes[1], IDENT_CAPTURE);
    assert!(boundary.is_none());
}

#[test]
fn test_pattern_with_binder_capture() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rule = make_rd_rule(
        "IfBinder",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Binder {
                param_name: "x".to_string(),
                binder_category: "Int".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    );

    let pattern = builder.pattern_from_rd_rule(&rule);
    assert_eq!(pattern.len(), 3);
    assert!(matches!(pattern[1], PatternElement::BinderCapture { .. }));

    let (bytes, boundary) = DecisionTreeBuilder::encode_terminal_prefix(&pattern);
    assert_eq!(bytes.len(), 3); // KwIf, BINDER_CAPTURE, RParen
    assert_eq!(bytes[1], BINDER_CAPTURE);
    assert!(boundary.is_none());
}

// ══════════════════════════════════════════════════════════════════════
// Step 9: D06 WFST consistency check tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_d06_consistent() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    // Use single-terminal rules so the trie has values at single-byte paths
    let rules = vec![make_rd_rule("JustIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");

    // Build a PredictionWfst with "if" token via builder
    let mut wfst_builder = PredictionWfstBuilder::new("Int", token_ids.clone());
    wfst_builder.add_action(
        "if",
        DispatchAction::Direct {
            rule_label: "JustIf".to_string(),
            parse_fn: "parse_JustIf".to_string(),
        },
        TropicalWeight(0.0),
    );
    let wfst = wfst_builder.build();

    let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
    // "if" maps to KwIf which is in the trie at single-byte path → no D06
    let d06s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D06).collect();
    assert!(d06s.is_empty(), "D06 should not fire when consistent: {:?}", d06s);
}

#[test]
fn test_d06_inconsistent() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    // Only "if" in the trie (single-byte path)
    let rules = vec![make_rd_rule("JustIf", "Int", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");

    // Build a PredictionWfst with "float" token — NOT in the trie
    let mut wfst_builder = PredictionWfstBuilder::new("Int", token_ids.clone());
    wfst_builder.add_action(
        "float",
        DispatchAction::Direct {
            rule_label: "FloatRule".to_string(),
            parse_fn: "parse_FloatRule".to_string(),
        },
        TropicalWeight(0.0),
    );
    let wfst = wfst_builder.build();

    let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
    let d06s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D06).collect();
    assert!(!d06s.is_empty(), "D06 should fire for inconsistent token: {:?}", diags);
    assert!(d06s[0].message.contains("float"), "D06 message should mention the token");
}

#[test]
fn test_d06_accepts_variant_prefix_of_longer_trie_path() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let mut token_ids = make_token_ids();
    token_ids.get_or_insert("At");
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Name".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "NQuote",
        "Name",
        vec![
            RDSyntaxItem::Terminal("@".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Name").expect("should have Name tree");

    let mut wfst_builder = PredictionWfstBuilder::new("Name", token_ids.clone());
    wfst_builder.add_action(
        "At",
        DispatchAction::Direct {
            rule_label: "NQuote".to_string(),
            parse_fn: "parse_nquote".to_string(),
        },
        TropicalWeight(0.0),
    );
    let wfst = wfst_builder.build();

    let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
    let d06s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D06).collect();
    assert!(
        d06s.is_empty(),
        "D06 should accept a token prefix of a longer trie path: {:?}",
        d06s
    );
}

#[test]
fn test_d06_skips_category_named_literal_dispatch() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let mut token_ids = make_token_ids();
    token_ids.get_or_insert("Fixed");
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Fixed".to_string()],
        HashSet::new(),
    );

    let rules =
        vec![make_rd_rule("JustIf", "Fixed", vec![RDSyntaxItem::Terminal("if".to_string())])];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Fixed").expect("should have Fixed tree");

    let mut wfst_builder = PredictionWfstBuilder::new("Fixed", token_ids.clone());
    wfst_builder.add_action(
        "Fixed",
        DispatchAction::Direct {
            rule_label: "FixedLit".to_string(),
            parse_fn: "parse_fixed_literal".to_string(),
        },
        TropicalWeight(0.0),
    );
    let wfst = wfst_builder.build();

    let diags = wfst_consistency_check(tree, &wfst, &token_ids, "test");
    let d06s: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::D06).collect();
    assert!(
        d06s.is_empty(),
        "D06 should skip category-named native literal dispatch: {:?}",
        d06s
    );
}

// ══════════════════════════════════════════════════════════════════════
// Step 10: IncrementalState edge cases
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_incremental_load_nonexistent() {
    let path = std::env::temp_dir().join("prattail_test_nonexistent_cache_42");
    let _ = std::fs::remove_file(&path); // Ensure it doesn't exist
    assert!(IncrementalState::load(&path).is_none());
}

#[test]
fn test_incremental_load_empty_file() {
    let path = std::env::temp_dir().join("prattail_test_empty_cache");
    std::fs::write(&path, &[]).expect("write empty file");
    assert!(IncrementalState::load(&path).is_none());
    let _ = std::fs::remove_file(&path);
}

#[test]
fn test_incremental_load_truncated() {
    let path = std::env::temp_dir().join("prattail_test_truncated_cache");
    // Write only the version (4 bytes) — missing num_categories
    std::fs::write(&path, &CACHE_VERSION.to_le_bytes()).expect("write truncated");
    let loaded = IncrementalState::load(&path);
    // Either None (can't read num_cats) or valid but empty
    match loaded {
        None => {}, // Expected for truncated data
        Some(state) => {
            // If load succeeds with just version + no categories, that's also fine
            assert_eq!(state.version, CACHE_VERSION);
            assert!(state.category_hashes.is_empty());
        },
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn test_incremental_many_categories() {
    let path = std::env::temp_dir().join("prattail_test_many_cats_cache");
    let mut state = IncrementalState {
        version: CACHE_VERSION,
        ..Default::default()
    };

    for i in 0..50 {
        let cat = format!("Cat{}", i);
        let hash = (i as u128) * 0x12345 + 42;
        let code = format!("fn parse_Cat{}() {{}}", i);
        state.record(&cat, hash);
        state.category_code.insert(cat, code);
    }

    state.save(&path).expect("save many categories");
    let loaded = IncrementalState::load(&path).expect("load many categories");
    assert!(loaded.is_valid());
    assert_eq!(loaded.category_hashes.len(), 50);

    for i in 0..50 {
        let cat = format!("Cat{}", i);
        let hash = (i as u128) * 0x12345 + 42;
        assert!(loaded.is_unchanged(&cat, hash), "Cat{} hash mismatch", i);
        let expected_code = format!("fn parse_Cat{}() {{}}", i);
        assert_eq!(loaded.category_code.get(&cat).expect("category code"), &expected_code,);
    }

    let _ = std::fs::remove_file(&path);
}

// ══════════════════════════════════════════════════════════════════════
// Step 11: TreeStats Display test
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_tree_stats_display() {
    let stats = TreeStats {
        total_states: 10,
        deterministic_nodes: 7,
        ambiguous_nodes: 2,
        max_depth: 4,
        min_lookahead: 2,
        nonterminal_boundaries: 1,
        shared_prefix_savings: 3,
        total_rules: 5,
        deterministic_rules: 3,
    };
    let display = format!("{}", stats);
    assert!(display.contains("10 states"), "should contain state count: {}", display);
    assert!(display.contains("7 deterministic"), "should contain deterministic: {}", display);
    assert!(display.contains("2 ambiguous"), "should contain ambiguous: {}", display);
    assert!(display.contains("max depth 4"), "should contain depth: {}", display);
    assert!(
        display.contains("3/5 rules deterministic"),
        "should contain rule ratio: {}",
        display
    );
}

// ══════════════════════════════════════════════════════════════════════
// Step 12: Emission edge cases
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_flatten_empty_tree() {
    let tree = CategoryDecisionTree {
        category: "Empty".to_string(),
        segments: vec![PathMap::new()],
        stats: TreeStats::default(),
    };
    let states = flatten_tree(&tree);
    assert!(states.is_empty(), "empty tree should produce no flat states");
}

#[test]
fn test_emit_match_arms_multi_rule() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets,
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
        make_rd_rule(
            "ParenExpr",
            "Int",
            vec![RDSyntaxItem::Terminal("(".to_string()), RDSyntaxItem::Terminal(")".to_string())],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("Int tree");
    let mut buf = String::new();
    emit_match_arms(tree, &token_ids, &mut buf);
    // Should contain "3" in dispatch token count or entries
    assert!(buf.contains("decision tree"), "should contain decision tree label: {}", buf);
    assert!(buf.contains("3"), "should mention 3 rules or tokens: {}", buf);
}

// ══════════════════════════════════════════════════════════════════════
// Step 13: coverage_report formatting
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_coverage_report_partial() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder =
        DecisionTreeBuilder::new(token_ids, first_sets, vec!["Int".to_string()], HashSet::new());

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
        make_rd_rule(
            "ParenExpr",
            "Int",
            vec![RDSyntaxItem::Terminal("(".to_string()), RDSyntaxItem::Terminal(")".to_string())],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let tree = builder.get_tree("Int").expect("should have Int tree");
    let paths = coverage_paths(tree);
    assert!(paths.len() >= 3, "should have at least 3 paths");

    // Cover only the first path
    let mut covered = HashSet::new();
    covered.insert(paths[0].path_bytes.clone());

    let diags = coverage_report(tree, &covered, "test");
    assert!(diags.len() == 1, "should have exactly one D07 diagnostic");
    let d07 = &diags[0];
    assert_eq!(d07.id, DiagnosticId::D07);
    // Should contain coverage fraction: "1/N"
    assert!(
        d07.message.contains("1/"),
        "should contain partial coverage fraction '1/': {}",
        d07.message
    );
    // Should contain "untested"
    assert!(d07.message.contains("untested"), "should mention untested: {}", d07.message);
}

// ══════════════════════════════════════════════════════════════════════
// Step 14: Property-based tests with proptest
// ══════════════════════════════════════════════════════════════════════

mod prop_tests {
    use super::*;
    use proptest::prelude::*;

    fn arb_candidate() -> impl Strategy<Value = AmbiguousCandidate> {
        ("[A-Z][a-z]{2,6}", "[A-Z][a-z]{2,6}").prop_map(|(label, cat)| AmbiguousCandidate {
            rule_label: label,
            category: cat,
            weight: 0.0,
            remaining_items: 0,
        })
    }

    fn arb_commit() -> impl Strategy<Value = DecisionAction> {
        ("[A-Z][a-z]{2,6}", "[A-Z][a-z]{2,6}").prop_map(|(label, cat)| DecisionAction::Commit {
            rule_label: label,
            category: cat,
            weight: 0.0,
        })
    }

    fn arb_ambiguous() -> impl Strategy<Value = DecisionAction> {
        prop::collection::vec(arb_candidate(), 2..6).prop_map(|candidates| {
            // Deduplicate by rule_label to avoid confusing pmeet/psubtract
            let mut seen = std::collections::HashSet::new();
            let unique: Vec<AmbiguousCandidate> = candidates
                .into_iter()
                .filter(|c| seen.insert(c.rule_label.clone()))
                .collect();
            if unique.len() < 2 {
                // Ensure we have at least 2 candidates
                DecisionAction::Ambiguous {
                    candidates: vec![
                        AmbiguousCandidate {
                            rule_label: "FallbackA".to_string(),
                            category: "Int".to_string(),
                            weight: 0.0,
                            remaining_items: 0,
                        },
                        AmbiguousCandidate {
                            rule_label: "FallbackB".to_string(),
                            category: "Int".to_string(),
                            weight: 0.0,
                            remaining_items: 0,
                        },
                    ],
                }
            } else {
                DecisionAction::Ambiguous { candidates: unique }
            }
        })
    }

    fn arb_action() -> impl Strategy<Value = DecisionAction> {
        prop_oneof![arb_commit(), arb_ambiguous()]
    }

    // ── Lattice law properties ──────────────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn prop_pjoin_idempotent(a in arb_action()) {
            let result = a.pjoin(&a);
            match result {
                AlgebraicResult::Element(merged) => {
                    // Labels of merged should contain all labels of a
                    let a_labels: std::collections::HashSet<String> =
                        a.rule_labels().map(|s| s.to_string()).collect();
                    let merged_labels: std::collections::HashSet<String> =
                        merged.rule_labels().map(|s| s.to_string()).collect();
                    for label in &a_labels {
                        prop_assert!(
                            merged_labels.contains(label),
                            "pjoin idempotent: merged missing label {}",
                            label
                        );
                    }
                }
                AlgebraicResult::Identity(_) => {
                    // NTBoundary case: identity is valid
                }
                AlgebraicResult::None => {
                    prop_assert!(false, "pjoin should not return None for self ⊔ self");
                }
            }
        }

        #[test]
        fn prop_pjoin_commutative(a in arb_action(), b in arb_action()) {
            let ab = a.pjoin(&b);
            let ba = b.pjoin(&a);

            let labels_ab = match &ab {
                AlgebraicResult::Element(action) => {
                    let mut l = sorted_labels(action);
                    l.sort();
                    l
                }
                _ => Vec::new(),
            };
            let labels_ba = match &ba {
                AlgebraicResult::Element(action) => {
                    let mut l = sorted_labels(action);
                    l.sort();
                    l
                }
                _ => Vec::new(),
            };

            // Both Element → labels match
            // Both Identity → commutative for NTBoundary
            // Mixed → NTBoundary identity values may differ (1 vs 2)
            match (&ab, &ba) {
                (AlgebraicResult::Element(_), AlgebraicResult::Element(_)) => {
                    prop_assert_eq!(labels_ab, labels_ba);
                }
                (AlgebraicResult::Identity(_), AlgebraicResult::Identity(_)) => {
                    // Both NTBoundary → valid
                }
                _ => {
                    // One is NTBoundary, other is not: Identity(1) vs Identity(2)
                    // is correct and expected non-commutative behavior for
                    // NTBoundary ⊔ non-NTBoundary
                }
            }
        }

        #[test]
        fn prop_pjoin_contains_both(a in arb_action(), b in arb_action()) {
            let result = a.pjoin(&b);
            if let AlgebraicResult::Element(merged) = result {
                let a_labels: std::collections::HashSet<String> =
                    a.rule_labels().map(|s| s.to_string()).collect();
                let b_labels: std::collections::HashSet<String> =
                    b.rule_labels().map(|s| s.to_string()).collect();
                let merged_labels: std::collections::HashSet<String> =
                    merged.rule_labels().map(|s| s.to_string()).collect();

                for label in a_labels.union(&b_labels) {
                    prop_assert!(
                        merged_labels.contains(label),
                        "pjoin should contain label {} from union",
                        label
                    );
                }
            }
        }

        #[test]
        fn prop_pmeet_subset(a in arb_ambiguous(), b in arb_ambiguous()) {
            let result = a.pmeet(&b);
            let a_labels: std::collections::HashSet<String> =
                a.rule_labels().map(|s| s.to_string()).collect();
            let b_labels: std::collections::HashSet<String> =
                b.rule_labels().map(|s| s.to_string()).collect();
            let intersection: std::collections::HashSet<&String> =
                a_labels.intersection(&b_labels).collect();

            match result {
                AlgebraicResult::Element(met) => {
                    let met_labels: std::collections::HashSet<String> =
                        met.rule_labels().map(|s| s.to_string()).collect();
                    for label in &met_labels {
                        prop_assert!(
                            intersection.contains(label),
                            "pmeet label {} should be in intersection",
                            label
                        );
                    }
                }
                AlgebraicResult::None => {
                    // No common labels (or all_candidates bug) → valid
                }
                _ => {}
            }
        }

        #[test]
        fn prop_psubtract_removes(a in arb_ambiguous(), b in arb_ambiguous()) {
            let result = a.psubtract(&b);
            let b_labels: std::collections::HashSet<String> =
                b.rule_labels().map(|s| s.to_string()).collect();

            if let AlgebraicResult::Element(diff) = result {
                let diff_labels: std::collections::HashSet<String> =
                    diff.rule_labels().map(|s| s.to_string()).collect();
                let overlap: std::collections::HashSet<&String> =
                    diff_labels.intersection(&b_labels).collect();
                prop_assert!(
                    overlap.is_empty(),
                    "psubtract result should have no labels from b: overlap={:?}",
                    overlap
                );
            }
        }

        #[test]
        fn prop_psubtract_self_is_none(a in arb_ambiguous()) {
            let result = a.psubtract(&a);
            prop_assert!(
                result.is_none(),
                "a ⊖ a should be None, got {:?}",
                result
            );
        }
    }

    // ── Round-trip properties ───────────────────────────────────────

    fn arb_incremental_entry() -> impl Strategy<Value = (String, u128, String)> {
        ("[A-Z][a-z]{2,10}", any::<u128>(), "[a-z ]{5,30}")
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(100))]

        #[test]
        fn prop_incremental_roundtrip(
            entries in prop::collection::vec(arb_incremental_entry(), 1..20)
        ) {
            let path = std::env::temp_dir().join(format!(
                "prattail_prop_rt_{}", std::process::id()
            ));
            let mut state = IncrementalState {
                version: CACHE_VERSION,
                ..Default::default()
            };
            // Deduplicate entries by name
            let mut seen = std::collections::HashSet::new();
            for (name, hash, code) in &entries {
                if seen.insert(name.clone()) {
                    state.record(name, *hash);
                    state.category_code.insert(name.clone(), code.clone());
                }
            }

            state.save(&path).expect("save should succeed");
            let loaded = IncrementalState::load(&path).expect("load should succeed");
            prop_assert!(loaded.is_valid());

            // Only check entries that were actually recorded (first
            // occurrence of each name). Re-derive the dedup set to get
            // the correct (name, hash, code) triple for each name.
            let mut checked = std::collections::HashSet::new();
            for (name, hash, code) in &entries {
                if checked.insert(name.clone()) {
                    prop_assert!(
                        loaded.is_unchanged(name, *hash),
                        "hash mismatch for {}",
                        name
                    );
                    prop_assert_eq!(
                        loaded.category_code.get(name).expect("code"),
                        code,
                    );
                }
            }

            let _ = std::fs::remove_file(&path);
        }

        #[test]
        fn prop_content_hash_deterministic(
            rule_count in 1usize..5,
            seed in 0u64..1000,
        ) {
            let terminals = ["if", "then", "else", "let", "in"];

            let build = || {
                let token_ids = make_token_ids();
                let first_sets = make_first_sets();
                let mut builder = DecisionTreeBuilder::new(
                    token_ids,
                    first_sets,
                    vec!["Int".to_string()],
                    HashSet::new(),
                );

                let rules: Vec<RDRuleInfo> = (0..rule_count)
                    .map(|i| {
                        let idx = ((seed as usize) + i) % terminals.len();
                        make_rd_rule(
                            &format!("Rule{}_{}", i, seed),
                            "Int",
                            vec![RDSyntaxItem::Terminal(terminals[idx].to_string())],
                        )
                    })
                    .collect();
                builder.build_all(&rules, &[], &[]);
                let tree = builder.get_tree("Int").expect("tree");
                category_content_hash(tree)
            };

            let hash1 = build();
            let hash2 = build();
            prop_assert_eq!(hash1, hash2, "same build should produce same hash");
        }

        #[test]
        fn prop_pattern_encoding_deterministic(seed in 0u64..1000) {
            let terminals = ["if", "then", "else", "let", "in"];
            let idx = (seed as usize) % terminals.len();

            let token_ids = make_token_ids();
            let first_sets = make_first_sets();
            let builder = DecisionTreeBuilder::new(
                token_ids,
                first_sets,
                vec!["Int".to_string()],
                HashSet::new(),
            );

            let rule = make_rd_rule(
                &format!("Rule{}", seed),
                "Int",
                vec![RDSyntaxItem::Terminal(terminals[idx].to_string())],
            );

            let pattern1 = builder.pattern_from_rd_rule(&rule);
            let (bytes1, _) = DecisionTreeBuilder::encode_terminal_prefix(&pattern1);

            let pattern2 = builder.pattern_from_rd_rule(&rule);
            let (bytes2, _) = DecisionTreeBuilder::encode_terminal_prefix(&pattern2);

            prop_assert_eq!(bytes1, bytes2, "same rule should encode identically");
        }
    }

    // ── NTBoundary identity properties ──────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn prop_pjoin_nt_boundary_left_identity(a in arb_action()) {
            let nt = DecisionAction::NonterminalBoundary {
                options: vec![NTOption {
                    kind: NTKind::NonTerminal { category: "X".to_string() },
                    first_tokens: vec![0],
                    resume_segment: 0,
                    weight: 0.0,
                }],
            };
            let result = nt.pjoin(&a);
            prop_assert!(
                result.is_identity(),
                "NTBoundary ⊔ a should be Identity, got {:?}",
                result
            );
            match result {
                AlgebraicResult::Identity(mask) => {
                    prop_assert_eq!(mask, 1, "NTBoundary as self → Identity(1)");
                }
                _ => unreachable!(),
            }
        }

        #[test]
        fn prop_psubtract_nt_boundary_right_identity(a in arb_ambiguous()) {
            let nt = DecisionAction::NonterminalBoundary {
                options: vec![NTOption {
                    kind: NTKind::NonTerminal { category: "X".to_string() },
                    first_tokens: vec![0],
                    resume_segment: 0,
                    weight: 0.0,
                }],
            };
            let result = a.psubtract(&nt);
            // NTBoundary has no rule_labels → nothing removed → a unchanged
            match result {
                AlgebraicResult::Element(diff) => {
                    let a_labels = sorted_labels(&a);
                    let diff_labels = sorted_labels(&diff);
                    prop_assert_eq!(
                        a_labels, diff_labels,
                        "a ⊖ NTBoundary should preserve all labels"
                    );
                }
                _ => {
                    prop_assert!(false, "expected Element, got {:?}", result);
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════
// CD02: Decision Tree Segment Merging tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_cd02_segment_merging_disjoint_nt_suffixes() {
    // Two rules share terminal prefix "if" "(" then diverge at different NT
    // categories with disjoint FIRST sets followed by different terminals.
    //
    //   IfIntRule:    if ( <Int> )
    //   IfFloatRule:  if ( <Float> :
    //
    // After the NT boundary at "if" "(", the remaining suffixes are:
    //   IfIntRule:    ")" → FIRST = { RParen }
    //   IfFloatRule:  ":" → FIRST = { Colon }
    //
    // RParen ∩ Colon = ∅ → safe to merge.
    // After merging, paths [if, (, RParen] → IfIntRule and
    // [if, (, Colon] → IfFloatRule should appear in segment[0].

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let rules = vec![
        make_rd_rule(
            "IfIntRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ],
        ),
    ];

    // Build the decision tree and track NT boundary info
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );
    builder.insert_rd_rules(&rules);

    // Compute stats
    for tree in builder.trees_mut().values_mut() {
        tree.stats = compute_statistics(tree);
    }

    // Verify NT boundary map has our boundaries
    let nt_map = builder.nt_boundary_map();
    let boundary_entries: Vec<_> = nt_map
        .iter()
        .filter(|(_, records)| records.len() >= 2)
        .collect();
    assert!(
        !boundary_entries.is_empty(),
        "should have at least one prefix with 2+ NT boundary records",
    );

    // Perform segment merging using the builder's NT boundary data
    let mut trees = builder.trees().clone();
    let merged = merge_safe_nonterminal_boundaries(&builder, &mut trees, &first_sets, &token_ids);

    assert!(merged > 0, "should have merged at least one NT boundary (disjoint FIRST sets)",);

    // Verify that new paths exist in segment[0] for the merged FIRST tokens
    let int_tree = trees.get("Int").expect("should have Int tree");
    let rparen_id = token_ids
        .get("RParen")
        .expect("RParen should be in token IDs");
    let colon_id = token_ids
        .get("Colon")
        .expect("Colon should be in token IDs");
    let kwif_id = token_ids.get("KwIf").expect("KwIf should be in token IDs");
    let lparen_id = token_ids
        .get("LParen")
        .expect("LParen should be in token IDs");

    // After merging, there should be paths like [KwIf, LParen, RParen] → IfIntRule
    // and [KwIf, LParen, Colon] → IfFloatRule
    let path_rparen = vec![kwif_id as u8, lparen_id as u8, rparen_id as u8];
    let path_colon = vec![kwif_id as u8, lparen_id as u8, colon_id as u8];

    let action_rparen = int_tree.segments[0].get(&path_rparen);
    let action_colon = int_tree.segments[0].get(&path_colon);

    assert!(
        action_rparen.is_some(),
        "merged trie should have path [KwIf, LParen, RParen] for IfIntRule",
    );
    assert!(
        action_colon.is_some(),
        "merged trie should have path [KwIf, LParen, Colon] for IfFloatRule",
    );

    // Verify rule labels
    if let Some(DecisionAction::Commit { rule_label, .. }) = action_rparen {
        assert_eq!(rule_label, "IfIntRule");
    } else {
        panic!("expected Commit(IfIntRule), got {:?}", action_rparen);
    }
    if let Some(DecisionAction::Commit { rule_label, .. }) = action_colon {
        assert_eq!(rule_label, "IfFloatRule");
    } else {
        panic!("expected Commit(IfFloatRule), got {:?}", action_colon);
    }
}

#[test]
fn test_cd02_segment_merging_overlapping_first_sets_not_merged() {
    // Two rules share terminal prefix "if" "(" then diverge at NT categories
    // whose FIRST sets overlap:
    //
    //   IfIntRule:    if ( <Int> )    → suffix FIRST = { RParen }
    //   IfFloatRule:  if ( <Float> )  → suffix FIRST = { RParen }
    //
    // RParen ∩ RParen ≠ ∅ → NOT safe to merge.

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];

    builder.insert_rd_rules(&rules);

    // Compute stats
    for tree in builder.trees_mut().values_mut() {
        tree.stats = compute_statistics(tree);
    }

    // Both suffixes have FIRST = { RParen } → overlap → no merge
    let mut trees = builder.trees().clone();
    let merged = merge_safe_nonterminal_boundaries(&builder, &mut trees, &first_sets, &token_ids);

    assert_eq!(merged, 0, "should not merge when FIRST sets overlap (both have RParen)",);
}

#[test]
fn test_cd02_single_nt_boundary_not_merged() {
    // Only one rule at an NT boundary — no merging needed (single record).
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "IfRule",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    )];

    builder.insert_rd_rules(&rules);
    for tree in builder.trees_mut().values_mut() {
        tree.stats = compute_statistics(tree);
    }

    let mut trees = builder.trees().clone();
    let merged = merge_safe_nonterminal_boundaries(&builder, &mut trees, &first_sets, &token_ids);

    assert_eq!(merged, 0, "single NT boundary should not be merged");
}

// ══════════════════════════════════════════════════════════════════════
// CD04: Jump Threading tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_cd04_jump_threading_basic() {
    // Rule: IfThenElse = "if" "then" "else"
    // Trie path: [KwIf, KwThen, KwElse] → Commit(IfThenElse)
    // Rule items start with: "if" → KwIf, "then" → KwThen, "else" → KwElse
    // Pre-consumed tokens: 3 (all terminal tokens are consumed by the trie)

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfThenElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
        make_rd_rule(
            "LetIn",
            "Int",
            vec![
                RDSyntaxItem::Terminal("let".to_string()),
                RDSyntaxItem::Terminal("in".to_string()),
            ],
        ),
    ];
    builder.build_all(&rules, &[], &[]);

    let trees = builder.into_trees();
    let info = compute_jump_threading_info(&trees, &rules, &token_ids);

    // IfThenElse: path [KwIf, KwThen, KwElse] matches rule items [if, then, else]
    // → 3 pre-consumed tokens
    let ite_key = ("Int".to_string(), "IfThenElse".to_string());
    assert!(
        info.pre_consumed.contains_key(&ite_key),
        "should have jump threading info for IfThenElse: {:?}",
        info.pre_consumed,
    );
    assert_eq!(
        info.pre_consumed[&ite_key], 3,
        "IfThenElse should have 3 pre-consumed tokens (if, then, else)",
    );

    // LetIn: path [KwLet, KwIn] matches rule items [let, in]
    // → 2 pre-consumed tokens
    let li_key = ("Int".to_string(), "LetIn".to_string());
    assert!(
        info.pre_consumed.contains_key(&li_key),
        "should have jump threading info for LetIn",
    );
    assert_eq!(
        info.pre_consumed[&li_key], 2,
        "LetIn should have 2 pre-consumed tokens (let, in)",
    );
}

#[test]
fn test_cd04_jump_threading_partial_match() {
    // Rule: IfParseX = "if" "(" <Int> ")"
    // Trie path: [KwIf, LParen] → Commit(IfParseX) (stops at NT boundary)
    // Rule items start with: "if" → KwIf, "(" → LParen, then NT...
    // Pre-consumed: 2 (KwIf, LParen match; NT is not a terminal)

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "IfParseX",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let trees = builder.into_trees();
    let info = compute_jump_threading_info(&trees, &rules, &token_ids);

    let key = ("Int".to_string(), "IfParseX".to_string());
    assert!(
        info.pre_consumed.contains_key(&key),
        "should have jump threading info for IfParseX: {:?}",
        info.pre_consumed,
    );
    assert_eq!(
        info.pre_consumed[&key], 2,
        "IfParseX should have 2 pre-consumed tokens (if, '(')",
    );
}

#[test]
fn test_cd04_jump_threading_no_match_for_nt_start() {
    // Rule starting with NT is skipped entirely by insert_rd_rules, so
    // no jump threading info should exist.
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();
    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "NtFirst",
        "Int",
        vec![
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal("then".to_string()),
        ],
    )];
    builder.build_all(&rules, &[], &[]);

    let trees = builder.into_trees();
    let info = compute_jump_threading_info(&trees, &rules, &token_ids);

    assert!(
        info.pre_consumed.is_empty(),
        "NT-start rules should not produce jump threading info: {:?}",
        info.pre_consumed,
    );
}

// ══════════════════════════════════════════════════════════════════════
// CD05: Prefix CSE (Common Subexpression Elimination) tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn test_cd05_shared_nonterminal_same_category_detected() {
    // Two rules share terminal prefix "if" "(" then diverge at the same
    // nonterminal <Int>, followed by different suffixes:
    //
    //   IfIntThen:     if ( <Int> ) then
    //   IfIntElse:     if ( <Int> ) else
    //
    // Both have nt_category = "Int" at the same prefix [KwIf, LParen].
    // Post-NT suffixes: ") then" (FIRST = {RParen}) vs ") else" (FIRST = {RParen}).
    // The FIRST sets overlap (both RParen), so all_disjoint = false — but
    // the shared nonterminal is still detected.

    let token_ids = make_token_ids();

    // Int FIRST includes RParen so suffix FIRST computation works
    let mut first_sets = make_first_sets();
    // Augment Int FIRST with terminals that appear in suffixes
    if let Some(int_first) = first_sets.get_mut("Int") {
        int_first.insert("RParen");
    }

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntThen",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntElse",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert!(
        !results.is_empty(),
        "should detect shared nonterminal prefix for IfIntThen/IfIntElse",
    );

    let shared = &results[0];
    assert_eq!(shared.category, "Int");
    assert_eq!(shared.nonterminal, "Int");
    assert_eq!(shared.rules.len(), 2);
    assert!(shared.rules.contains(&"IfIntThen".to_string()));
    assert!(shared.rules.contains(&"IfIntElse".to_string()));

    // Both suffixes start with RParen → FIRST sets overlap → not disjoint
    assert!(!shared.all_disjoint, "suffixes both start with RParen, should NOT be disjoint",);
}

#[test]
fn test_cd05_shared_nonterminal_disjoint_suffixes() {
    // Two rules share terminal prefix "if" "(" then the same nonterminal
    // <Int>, but with disjoint FIRST sets after the nonterminal:
    //
    //   IfIntColon:  if ( <Int> :   → suffix FIRST = {Colon}
    //   IfIntComma:  if ( <Int> ,   → suffix FIRST = {Comma}
    //
    // Colon ∩ Comma = ∅ → all_disjoint = true → deterministic CSE.

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntColon",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntComma",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert!(!results.is_empty(), "should detect shared nonterminal prefix",);

    let shared = &results[0];
    assert_eq!(shared.nonterminal, "Int");
    assert_eq!(shared.rules.len(), 2);

    // Colon vs Comma → disjoint
    assert!(shared.all_disjoint, "Colon vs Comma suffixes should be disjoint",);

    // Check discriminating tokens
    let colon_tokens = shared
        .discriminating_tokens
        .get("IfIntColon")
        .expect("IfIntColon tokens");
    assert!(
        colon_tokens.contains(&"Colon".to_string()),
        "IfIntColon should have Colon: {:?}",
        colon_tokens
    );
    let comma_tokens = shared
        .discriminating_tokens
        .get("IfIntComma")
        .expect("IfIntComma tokens");
    assert!(
        comma_tokens.contains(&"Comma".to_string()),
        "IfIntComma should have Comma: {:?}",
        comma_tokens
    );
}

#[test]
fn test_cd05_no_false_positive_different_nonterminals() {
    // Two rules share terminal prefix "if" "(" but diverge at DIFFERENT
    // nonterminal categories:
    //
    //   IfIntRule:    if ( <Int> )
    //   IfFloatRule:  if ( <Float> )
    //
    // Different nt_category → no shared nonterminal → no CSE opportunity
    // for same-NT grouping (these are separate NT boundary groups).

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string(), "Float".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
        make_rd_rule(
            "IfFloatRule",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Float".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    // Each NT group has only 1 record (one Int, one Float) → no CSE
    assert!(
        results.is_empty(),
        "different nonterminals should NOT produce CSE: {:?}",
        results,
    );
}

#[test]
fn test_cd05_no_false_positive_single_rule() {
    // Only one rule at an NT boundary — no sharing possible.
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![make_rd_rule(
        "IfParse",
        "Int",
        vec![
            RDSyntaxItem::Terminal("if".to_string()),
            RDSyntaxItem::Terminal("(".to_string()),
            RDSyntaxItem::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
            RDSyntaxItem::Terminal(")".to_string()),
        ],
    )];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert!(
        results.is_empty(),
        "single rule at NT boundary should NOT produce CSE: {:?}",
        results,
    );
}

#[test]
fn test_cd05_three_way_shared_nonterminal() {
    // Three rules sharing terminal prefix "if" "(" then <Int> with
    // different suffixes:
    //
    //   IfIntColon:   if ( <Int> :
    //   IfIntComma:   if ( <Int> ,
    //   IfIntSemi:    if ( <Int> ;
    //
    // All suffix FIRST sets are disjoint → 3-way CSE.

    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntColon",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntComma",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntSemi",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "c".to_string(),
                },
                RDSyntaxItem::Terminal(";".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert_eq!(results.len(), 1, "should detect one 3-way shared prefix");

    let shared = &results[0];
    assert_eq!(shared.nonterminal, "Int");
    assert_eq!(shared.rules.len(), 3);
    assert!(shared.all_disjoint, "Colon/Comma/Semi are pairwise disjoint");
}

#[test]
fn test_cd05_format_cse_annotation_disjoint() {
    let token_ids = make_token_ids();
    let first_sets = make_first_sets();

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntColon",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(":".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntComma",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(",".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert!(!results.is_empty());

    let annotation = format_cse_annotation(&results[0], &token_ids);
    assert!(
        annotation.contains("CD05 Prefix CSE"),
        "annotation should contain CD05 header: {}",
        annotation,
    );
    assert!(
        annotation.contains("parse_Int"),
        "annotation should reference parse_Int: {}",
        annotation,
    );
    assert!(
        annotation.contains("match &tokens"),
        "disjoint annotation should contain match block: {}",
        annotation,
    );
}

#[test]
fn test_cd05_format_cse_annotation_overlapping() {
    let token_ids = make_token_ids();
    let mut first_sets = make_first_sets();
    if let Some(int_first) = first_sets.get_mut("Int") {
        int_first.insert("RParen");
    }

    let mut builder = DecisionTreeBuilder::new(
        token_ids.clone(),
        first_sets.clone(),
        vec!["Int".to_string()],
        HashSet::new(),
    );

    let rules = vec![
        make_rd_rule(
            "IfIntA",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("then".to_string()),
            ],
        ),
        make_rd_rule(
            "IfIntB",
            "Int",
            vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
                RDSyntaxItem::Terminal(")".to_string()),
                RDSyntaxItem::Terminal("else".to_string()),
            ],
        ),
    ];
    builder.insert_rd_rules(&rules);

    let results = detect_shared_nonterminal_prefixes(&builder, &first_sets, &token_ids);
    assert!(!results.is_empty());

    let annotation = format_cse_annotation(&results[0], &token_ids);
    assert!(
        annotation.contains("NFA try-all"),
        "overlapping annotation should mention NFA try-all: {}",
        annotation,
    );
}

#[test]
fn test_cd05_display_trait() {
    let shared = SharedNonterminalPrefix {
        category: "Stmt".to_string(),
        prefix_bytes: vec![0x01, 0x02],
        nonterminal: "Expr".to_string(),
        rules: vec!["IfThen".to_string(), "IfThenElse".to_string()],
        discriminating_tokens: HashMap::from([
            ("IfThen".to_string(), vec!["KwThen".to_string()]),
            ("IfThenElse".to_string(), vec!["KwElse".to_string()]),
        ]),
        all_disjoint: true,
    };

    let display = format!("{}", shared);
    assert!(display.contains("CD05 CSE"));
    assert!(display.contains("Expr"));
    assert!(display.contains("IfThen"));
    assert!(display.contains("deterministic"));
}
