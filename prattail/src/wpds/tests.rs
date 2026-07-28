use super::*;
use crate::automata::semiring::{BooleanWeight, CountingWeight, TropicalWeight};
use crate::binding_power::Associativity;
use crate::{CategorySpec, LanguageSpec, RuleSpecInput, SyntaxItemSpec};

/// Build a minimal calculator grammar: Expr = Int | Expr "+" Expr
fn calculator_spec() -> LanguageSpec {
    let types = vec![CategorySpec {
        name: "Expr".to_string(),
        native_type: Some("i64".to_string()),
        is_primary: true,
        has_var: true,
    }];

    let inputs = vec![
        RuleSpecInput {
            label: "Num".to_string(),
            category: "Expr".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "Add".to_string(),
            category: "Expr".to_string(),
            syntax: vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "lhs".to_string(),
                },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "rhs".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
    ];

    LanguageSpec::new("Calculator".to_string(), types, inputs)
}

/// Build a two-category grammar: Expr = Num | Expr "+" Expr | "(" Type ")" Expr
///                                Type = "int" | "float"
fn typed_grammar_spec() -> LanguageSpec {
    let types = vec![
        CategorySpec {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Type".to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        },
    ];

    let inputs = vec![
        RuleSpecInput {
            label: "Num".to_string(),
            category: "Expr".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "Add".to_string(),
            category: "Expr".to_string(),
            syntax: vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "lhs".to_string(),
                },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "rhs".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "Cast".to_string(),
            category: "Expr".to_string(),
            syntax: vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Type".to_string(),
                    param_name: "ty".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "expr".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "IntType".to_string(),
            category: "Type".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("int".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "FloatType".to_string(),
            category: "Type".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("float".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
    ];

    LanguageSpec::new("TypedCalc".to_string(), types, inputs)
}

/// Build a class-3 shaped grammar where Name is reachable only through a
/// nested Sep(Zip(Map(...))) collection body in a Proc rule.
fn nested_zip_collection_spec() -> LanguageSpec {
    let types = vec![
        CategorySpec {
            name: "Proc".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Name".to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        },
    ];

    let inputs = vec![
        RuleSpecInput {
            label: "PZero".to_string(),
            category: "Proc".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("0".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "TaggedInputs".to_string(),
            category: "Proc".to_string(),
            syntax: vec![
                SyntaxItemSpec::Terminal("with".to_string()),
                SyntaxItemSpec::Sep {
                    body: Box::new(SyntaxItemSpec::Zip {
                        left_name: "ns".to_string(),
                        right_name: "xs".to_string(),
                        left_category: "Name".to_string(),
                        right_category: "Proc".to_string(),
                        body: Box::new(SyntaxItemSpec::Map {
                            body_items: vec![
                                SyntaxItemSpec::NonTerminal {
                                    category: "Name".to_string(),
                                    param_name: "n".to_string(),
                                },
                                SyntaxItemSpec::Terminal("?".to_string()),
                                SyntaxItemSpec::Binder {
                                    param_name: "x".to_string(),
                                    category: "Proc".to_string(),
                                    is_multi: false,
                                },
                            ],
                        }),
                    }),
                    separator: ",".to_string(),
                    kind: crate::grammar::ir::CollectionKind::Vec,
                },
                SyntaxItemSpec::Terminal(".".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "body".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "NQuote".to_string(),
            category: "Name".to_string(),
            syntax: vec![
                SyntaxItemSpec::Terminal("@".to_string()),
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "p".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
    ];

    LanguageSpec::new("NestedZipCollection".to_string(), types, inputs)
}

/// Build a grammar with an unreachable category: Expr has rules, Orphan has rules
/// but nothing references Orphan.
fn orphan_grammar_spec() -> LanguageSpec {
    let types = vec![
        CategorySpec {
            name: "Expr".to_string(),
            native_type: Some("i64".to_string()),
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Orphan".to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        },
    ];

    let inputs = vec![
        RuleSpecInput {
            label: "Num".to_string(),
            category: "Expr".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("INTEGER".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "OrphanRule".to_string(),
            category: "Orphan".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("orphan".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
    ];

    LanguageSpec::new("OrphanGrammar".to_string(), types, inputs)
}

// ── Phase 1: WPDS construction ──

#[test]
fn test_build_wpds_calculator() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    // Should have stack symbols for: Expr entry, Num@0, Num@1, Add@0, Add@1, Add@2, Add@3
    assert!(
        wpds.num_symbols() >= 4,
        "calculator WPDS should have at least 4 symbols, got {}",
        wpds.num_symbols()
    );

    // Should have rules: dispatch + intraprocedural + pop
    assert!(
        wpds.num_rules() >= 4,
        "calculator WPDS should have at least 4 rules, got {}",
        wpds.num_rules()
    );

    // Initial symbol should be Expr entry
    assert_eq!(wpds.initial_symbol.category, "Expr");
    assert!(wpds.initial_symbol.rule_label.is_empty());
}

#[test]
fn test_build_wpds_cross_category() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    // Should have push rules for Expr→Type cross-category call
    let push_count = wpds
        .rules
        .iter()
        .filter(|r| matches!(r, WpdsRule::Push { .. }))
        .count();

    assert!(
        push_count >= 1,
        "typed grammar should have at least 1 push rule for cross-category call, got {}",
        push_count
    );

    // Should have both Expr and Type category entries
    assert!(
        wpds.symbol_index
            .contains_key(&StackSymbol::category_entry("Expr")),
        "should have Expr entry symbol"
    );
    assert!(
        wpds.symbol_index
            .contains_key(&StackSymbol::category_entry("Type")),
        "should have Type entry symbol"
    );
}

#[test]
fn test_build_wpds_orphan_category() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    // Orphan category should have rules but no cross-category calls TO it
    let push_to_orphan = wpds
        .rules
        .iter()
        .filter(|r| match r {
            WpdsRule::Push { to_gamma_top, .. } => to_gamma_top.category == "Orphan",
            _ => false,
        })
        .count();

    assert_eq!(push_to_orphan, 0, "no rule should push to Orphan category");
}

// ── Phase 2: poststar reachability ──

#[test]
fn test_poststar_calculator_reachability() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    let post = poststar(&wpds);

    // Expr entry should be reachable (it's the initial symbol)
    let expr_sym = StackSymbol::category_entry("Expr");
    assert!(
        !post.stack_top_weight(&expr_sym).is_zero(),
        "Expr entry should be reachable via poststar"
    );
}

#[test]
fn test_poststar_cross_category_reachability() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    let post = poststar(&wpds);

    // Both Expr and Type should be reachable
    let expr_sym = StackSymbol::category_entry("Expr");
    let type_sym = StackSymbol::category_entry("Type");

    assert!(!post.stack_top_weight(&expr_sym).is_zero(), "Expr should be reachable");
    assert!(
        !post.stack_top_weight(&type_sym).is_zero(),
        "Type should be reachable (called by Cast rule in Expr)"
    );
}

#[test]
fn test_poststar_orphan_unreachable() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());

    let post = poststar(&wpds);

    // Expr should be reachable
    let expr_sym = StackSymbol::category_entry("Expr");
    assert!(!post.stack_top_weight(&expr_sym).is_zero(), "Expr should be reachable");

    // Orphan should NOT be reachable (no rule calls it)
    let orphan_sym = StackSymbol::category_entry("Orphan");
    assert!(
        post.stack_top_weight(&orphan_sym).is_zero(),
        "Orphan should be unreachable via poststar"
    );
}

#[test]
fn test_poststar_tropical_weights() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<TropicalWeight> = build_wpds(&spec, &wfsts, TropicalWeight::new);

    let post = poststar(&wpds);

    // Expr should have finite weight
    let expr_sym = StackSymbol::category_entry("Expr");
    let w = post.stack_top_weight(&expr_sym);
    assert!(!w.is_zero(), "Expr should have non-zero tropical weight");
}

#[test]
fn test_poststar_counting_weight() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<CountingWeight> = build_wpds(&spec, &wfsts, |_| CountingWeight::one());

    let post = poststar(&wpds);

    // Expr should have counting weight >= 1 (at least one derivation path)
    let expr_sym = StackSymbol::category_entry("Expr");
    let w = post.stack_top_weight(&expr_sym);
    assert!(!w.is_zero(), "Expr should have non-zero counting weight, got {:?}", w);
}

// ── Phase 3: Stringsum ──

#[test]
fn test_stringsum_single_token() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<CountingWeight> = build_wpds(&spec, &wfsts, |_| CountingWeight::one());
    let post = poststar(&wpds);

    let input = StringsumInput { tokens: vec!["42".to_string()] };

    let result = stringsum(&wpds, &post, &input, &spec);

    // A single integer should match at least the Num rule
    // (the actual matching depends on whether "42" matches INTEGER pattern)
    assert_eq!(result.position_weights.len(), 1);
}

// ── Phase 4: Full analysis ──

#[test]
fn test_analyze_wpds_calculator() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();

    let analysis = analyze_wpds(&spec, &wfsts);

    assert_eq!(analysis.grammar_name, "Calculator");
    assert!(analysis.reachable_categories.contains("Expr"), "Expr should be reachable");
    assert!(
        analysis.unreachable_rules.is_empty(),
        "calculator should have no unreachable rules: {:?}",
        analysis.unreachable_rules
    );
}

#[test]
fn test_analyze_wpds_orphan_detection() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();

    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(analysis.reachable_categories.contains("Expr"), "Expr should be reachable");
    // Orphan category should not be reachable
    assert!(
        !analysis.reachable_categories.contains("Orphan"),
        "Orphan should not be reachable"
    );
    // The Orphan rule should be flagged as unreachable
    assert!(
        analysis
            .unreachable_rules
            .iter()
            .any(|r| r.rule_label == "OrphanRule"),
        "OrphanRule should be WPDS-unreachable: {:?}",
        analysis.unreachable_rules
    );
}

#[test]
fn test_analyze_wpds_typed_grammar() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();

    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(analysis.reachable_categories.contains("Expr"), "Expr should be reachable");
    assert!(
        analysis.reachable_categories.contains("Type"),
        "Type should be reachable (called from Cast rule)"
    );
    assert!(
        analysis.unreachable_rules.is_empty(),
        "typed grammar should have no unreachable rules: {:?}",
        analysis.unreachable_rules
    );
}

#[test]
fn test_analyze_wpds_nested_zip_collection_reaches_element_category() {
    let spec = nested_zip_collection_spec();
    let wfsts = HashMap::new();

    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(
        analysis.reachable_categories.contains("Name"),
        "Name should be reachable through nested Sep(Zip(Map(...))) body: {:?}",
        analysis.reachable_categories
    );
    assert!(
        !analysis
            .unreachable_rules
            .iter()
            .any(|rule| rule.rule_label == "NQuote"),
        "NQuote should not be WPDS-unreachable: {:?}",
        analysis.unreachable_rules
    );
}

// ── Stack symbol tests ──

#[test]
fn test_stack_symbol_display() {
    let entry = StackSymbol::category_entry("Expr");
    assert_eq!(format!("{}", entry), "⟨Expr⟩");

    let pos = StackSymbol::rule_position("Expr", "Add", 2);
    assert_eq!(format!("{}", pos), "⟨Expr.Add@2⟩");
}

#[test]
fn test_stack_symbol_equality() {
    let a = StackSymbol::category_entry("Expr");
    let b = StackSymbol::category_entry("Expr");
    let c = StackSymbol::category_entry("Type");

    assert_eq!(a, b);
    assert_ne!(a, c);
}

// ── WPDS rule display ──

#[test]
fn test_wpds_rule_display() {
    let pop: WpdsRule<BooleanWeight> = WpdsRule::Pop {
        from_gamma: StackSymbol::category_entry("Expr"),
        weight: BooleanWeight::one(),
    };
    let display = format!("{}", pop);
    assert!(display.contains("⟨Expr⟩"), "display should contain symbol: {}", display);
    assert!(display.contains("ε"), "pop should show epsilon: {}", display);
}

// ── P-automaton tests ──

#[test]
fn test_p_automaton_basic() {
    let mut pa = PAutomaton::<BooleanWeight>::new(0);
    let q1 = pa.add_state();
    pa.mark_final(q1);

    let sym = StackSymbol::category_entry("Expr");
    pa.add_transition(0, sym.clone(), q1, BooleanWeight::one());

    assert!(pa.is_symbol_accepted(&sym));
    assert!(!pa.symbol_weight(&sym).is_zero());
}

#[test]
fn test_p_automaton_no_accept() {
    let pa = PAutomaton::<BooleanWeight>::new(0);
    let sym = StackSymbol::category_entry("Expr");
    assert!(!pa.is_symbol_accepted(&sym));
    assert!(pa.symbol_weight(&sym).is_zero());
}

/// A transition to a NON-final state separates the two queries.
///
/// This is the configuration in which acceptance and liveness disagree, and the one
/// `symbol_weight` used to get wrong: `⟨p, γ⟩` is NOT accepted (the run ends outside
/// `F`) while `γ` is still live (a longer stack continues from `q`). The
/// poststar/prestar saturation loops manufacture exactly such transitions — prestar's
/// Pop phase seeds `(p, γ, p)` and poststar's Push case seeds `(p, γ_top, q_r)` — so
/// without this case the accessors could be interchanged and every test would pass.
#[test]
fn test_p_automaton_non_final_target_is_live_but_not_accepted() {
    let mut pa = PAutomaton::<BooleanWeight>::new(0);
    let q_final = pa.add_state();
    pa.mark_final(q_final);
    let q_middle = pa.add_state();

    let accepted = StackSymbol::category_entry("Expr");
    let live_only = StackSymbol::category_entry("Type");
    pa.add_transition(0, accepted.clone(), q_final, BooleanWeight::one());
    pa.add_transition(0, live_only.clone(), q_middle, BooleanWeight::one());

    // Accepted as a one-symbol configuration.
    assert!(pa.is_symbol_accepted(&accepted));
    assert!(!pa.symbol_weight(&accepted).is_zero());
    assert!(!pa.stack_top_weight(&accepted).is_zero());

    // Live, but NOT a one-symbol configuration.
    assert!(!pa.is_symbol_accepted(&live_only), "the run ends outside the final states");
    assert!(
        pa.symbol_weight(&live_only).is_zero(),
        "acceptance requires a final target; summing every out-transition regardless \
         of target is the over-count that made `check_safety` unsound"
    );
    assert!(
        !pa.stack_top_weight(&live_only).is_zero(),
        "liveness counts the symbol wherever it heads a stack"
    );
    assert!(pa.is_symbol_reachable(&live_only), "the boolean twin of stack_top_weight");
}

// ── G33: Call graph extraction ──

#[test]
fn test_call_graph_calculator_empty() {
    // Calculator has only one category (Expr) — no cross-category calls
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
    let cg = extract_call_graph(&wpds);

    assert!(
        cg.edges.is_empty(),
        "calculator should have no cross-category call edges, got {:?}",
        cg.edges
            .iter()
            .map(|e| format!("{}→{}", e.caller_cat, e.callee_cat))
            .collect::<Vec<_>>()
    );
    assert!(cg.categories.contains("Expr"), "Expr should be in the call graph categories");
}

#[test]
fn test_call_graph_cross_category() {
    // Expr → Type via Cast rule
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
    let cg = extract_call_graph(&wpds);

    assert!(!cg.edges.is_empty(), "typed grammar should have cross-category call edges");
    let expr_to_type = cg
        .edges
        .iter()
        .find(|e| e.caller_cat == "Expr" && e.callee_cat == "Type");
    assert!(
        expr_to_type.is_some(),
        "should have Expr→Type edge, got: {:?}",
        cg.edges
            .iter()
            .map(|e| format!("{}→{}", e.caller_cat, e.callee_cat))
            .collect::<Vec<_>>()
    );
    assert!(
        expr_to_type.expect("just checked").call_sites >= 1,
        "Expr→Type should have at least 1 call site"
    );
    assert_eq!(
        *cg.fan_out.get("Expr").unwrap_or(&0),
        1,
        "Expr fan-out should be 1 (calls only Type)"
    );
    assert_eq!(
        *cg.fan_in.get("Type").unwrap_or(&0),
        1,
        "Type fan-in should be 1 (called only by Expr)"
    );
}

#[test]
fn test_call_graph_orphan_disconnected() {
    // Orphan category has no incoming or outgoing cross-category edges from Expr
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
    let cg = extract_call_graph(&wpds);

    let orphan_edges: Vec<_> = cg
        .edges
        .iter()
        .filter(|e| e.caller_cat == "Orphan" || e.callee_cat == "Orphan")
        .collect();
    assert!(
        orphan_edges.is_empty(),
        "Orphan should have no call edges, got {:?}",
        orphan_edges
            .iter()
            .map(|e| format!("{}→{}", e.caller_cat, e.callee_cat))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_call_graph_sccs() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let wpds: Wpds<BooleanWeight> = build_wpds(&spec, &wfsts, |_| BooleanWeight::one());
    let cg = extract_call_graph(&wpds);

    // Expr→Type is a DAG edge (no cycle), so each SCC should be a singleton
    for scc in &cg.sccs {
        assert_eq!(
            scc.len(),
            1,
            "typed grammar has no cycles — each SCC should be a singleton, got {:?}",
            scc
        );
    }
}

// ── D15: Witness traces for dead rules ──

#[test]
fn test_witness_trace_orphan() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    let orphan_rule = analysis
        .unreachable_rules
        .iter()
        .find(|r| r.rule_label == "OrphanRule")
        .expect("OrphanRule should be unreachable");

    assert!(
        !orphan_rule.witness_trace.is_empty(),
        "witness trace for OrphanRule should not be empty"
    );
}

#[test]
fn test_analyze_wpds_call_graph_populated() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(
        !analysis.call_graph.edges.is_empty(),
        "WpdsAnalysis should include a populated call graph for cross-category grammars"
    );
    assert!(
        analysis.call_graph.categories.contains("Expr"),
        "call graph should include Expr"
    );
    assert!(
        analysis.call_graph.categories.contains("Type"),
        "call graph should include Type"
    );
}

// ── G34: Recursion depth bounds ──

#[test]
fn test_depth_bounds_single_category() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    let expr_bounds = analysis
        .depth_bounds
        .get("Expr")
        .expect("Expr should have depth bounds");
    assert_eq!(expr_bounds.min_depth, 0, "primary category should have min_depth=0");
}

#[test]
fn test_depth_bounds_cross_category() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    let expr_bounds = analysis
        .depth_bounds
        .get("Expr")
        .expect("Expr should have depth bounds");
    assert_eq!(expr_bounds.min_depth, 0, "primary Expr should have min_depth=0");

    let type_bounds = analysis
        .depth_bounds
        .get("Type")
        .expect("Type should have depth bounds");
    assert_eq!(type_bounds.min_depth, 1, "Type called from Expr should have min_depth=1");
    assert!(!type_bounds.is_recursive, "Type should not be recursive");
}

#[test]
fn test_depth_bounds_orphan() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Orphan has no incoming edges, so it should have max_depth = None (unreachable)
    if let Some(orphan_bounds) = analysis.depth_bounds.get("Orphan") {
        assert!(
            orphan_bounds.max_depth.is_none(),
            "Orphan should have unbounded max_depth (unreachable)"
        );
    }
}

// ── G35: Cycle classification ──

#[test]
fn test_cycle_classification_no_cycles() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(
        analysis.cycles.is_empty(),
        "typed grammar (Expr→Type DAG) should have no cycles, got {:?}",
        analysis
            .cycles
            .iter()
            .map(|c| format!("{:?}: {:?}", c.kind, c.categories))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_cycle_classification_calculator() {
    // Calculator has only Expr — no cross-category call graph cycles
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(analysis.cycles.is_empty(), "calculator should have no cross-category cycles");
}

/// Build a mutual-recursion grammar: Expr → "x" | Decl "in" Expr; Decl → "let" Expr
fn mutual_recursion_spec() -> LanguageSpec {
    let types = vec![
        CategorySpec {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Decl".to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        },
    ];

    let inputs = vec![
        RuleSpecInput {
            label: "Var".to_string(),
            category: "Expr".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("x".to_string())],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "LetIn".to_string(),
            category: "Expr".to_string(),
            syntax: vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Decl".to_string(),
                    param_name: "decl".to_string(),
                },
                SyntaxItemSpec::Terminal("in".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "body".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
        RuleSpecInput {
            label: "LetDecl".to_string(),
            category: "Decl".to_string(),
            syntax: vec![
                SyntaxItemSpec::Terminal("let".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "init".to_string(),
                },
            ],
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        },
    ];

    LanguageSpec::new("MutualRecursion".to_string(), types, inputs)
}

#[test]
fn test_cycle_classification_mutual_recursion() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Expr→Decl and Decl→Expr form a mutual recursion cycle
    assert!(
        !analysis.cycles.is_empty(),
        "mutual recursion grammar should have at least one cycle"
    );
    let mutual_cycle = analysis.cycles.iter().find(|c| c.kind == CycleKind::Mutual);
    assert!(mutual_cycle.is_some(), "should have a Mutual cycle, got: {:?}", analysis.cycles);
    let cycle = mutual_cycle.expect("just checked");
    assert!(
        cycle.categories.contains(&"Expr".to_string())
            && cycle.categories.contains(&"Decl".to_string()),
        "mutual cycle should contain both Expr and Decl, got {:?}",
        cycle.categories
    );
}

// ── G36: Calling contexts ──

#[test]
fn test_calling_contexts_calculator() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // No cross-category calls → no calling contexts
    assert!(
        analysis.calling_contexts.is_empty(),
        "calculator should have no calling contexts"
    );
}

#[test]
fn test_calling_contexts_typed_grammar() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Type is called from Expr.Cast
    let type_contexts = analysis.calling_contexts.get("Type");
    assert!(type_contexts.is_some(), "Type should have calling contexts");
    let contexts = type_contexts.expect("just checked");
    assert!(!contexts.is_empty(), "Type should have at least one caller");
    assert!(
        contexts.iter().any(|c| c.caller_category == "Expr"),
        "Type should be called from Expr"
    );
}

#[test]
fn test_calling_contexts_mutual_recursion() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Both Expr and Decl should have callers
    assert!(
        analysis.calling_contexts.get("Decl").is_some(),
        "Decl should have calling contexts (called from Expr)"
    );
    assert!(
        analysis.calling_contexts.get("Expr").is_some(),
        "Expr should have calling contexts (called from Decl)"
    );
}

// ── G34 + G35 combined: depth and recursion for mutual recursion ──

#[test]
fn test_depth_bounds_mutual_recursion() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    let expr_bounds = analysis
        .depth_bounds
        .get("Expr")
        .expect("Expr should have depth bounds");
    assert!(expr_bounds.is_recursive, "Expr in mutual recursion should be recursive");
    assert!(
        expr_bounds.max_depth.is_none(),
        "recursive Expr should have unbounded max_depth"
    );

    let decl_bounds = analysis
        .depth_bounds
        .get("Decl")
        .expect("Decl should have depth bounds");
    assert!(decl_bounds.is_recursive, "Decl in mutual recursion should be recursive");
}

// ── CS-01: Context-sensitive rule tables ──

#[test]
fn test_context_rule_table_typed_grammar() {
    let spec = typed_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Type is called from Expr, so it should have a context rule table
    let type_table = analysis.context_rule_tables.get("Type");
    assert!(type_table.is_some(), "Type should have a context rule table (called from Expr)");
    let table = type_table.expect("just checked");
    assert!(!table.entries.is_empty(), "Type context rule table should have entries");
    // Should have entries for "Expr" (caller) and "top-level"
    assert!(
        table.entries.iter().any(|e| e.context_tag == "Expr"),
        "Type table should have an Expr calling context entry"
    );
    assert!(
        table.entries.iter().any(|e| e.context_tag == "top-level"),
        "Type table should have a top-level entry"
    );
}

#[test]
fn test_context_rule_table_calculator_empty() {
    // Calculator has no cross-category calls → no context rule tables
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    assert!(
        analysis.context_rule_tables.is_empty(),
        "calculator should have no context rule tables"
    );
}

#[test]
fn test_context_rule_table_mutual_recursion() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Both Expr and Decl are called from each other
    assert!(
        analysis.context_rule_tables.get("Decl").is_some(),
        "Decl should have a context rule table"
    );
    assert!(
        analysis.context_rule_tables.get("Expr").is_some(),
        "Expr should have a context rule table (called from Decl)"
    );
}

// ── CS-04: Cross-Category BP Modulation Tests ────────────────────────

#[test]
fn test_cs04_calculator_no_cross_category_bp() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Calculator has a single category — no cross-category calls
    assert!(
        analysis.cross_category_bp.is_empty(),
        "single-category grammar should have no cross-category BP entries"
    );
}

#[test]
fn test_cs04_mutual_recursion_bp() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Mutual recursion grammar has Expr→Decl and Decl→Expr calls
    // At least one cross-category edge should exist
    assert!(
        !analysis.cross_category_bp.is_empty(),
        "mutual recursion grammar should have cross-category BP entries"
    );

    // Each edge should have BP hints (0 = prefix, 1 = non-prefix)
    for ((caller, callee), bp_values) in &analysis.cross_category_bp {
        assert!(!bp_values.is_empty(), "BP values for {caller}→{callee} should not be empty");
        for &bp in bp_values {
            assert!(bp <= 1, "BP hint should be 0 (prefix) or 1 (non-prefix), got {bp}");
        }
    }
}

#[test]
fn test_cs04_cross_category_bp_deduplication() {
    // Verify that BP values are deduplicated per edge
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    for ((_caller, _callee), bp_values) in &analysis.cross_category_bp {
        // After dedup, no adjacent duplicates
        for window in bp_values.windows(2) {
            assert_ne!(window[0], window[1], "BP values should be deduplicated");
        }
    }
}

// ── CS-05: Context-Aware Ambiguity Resolution Tests ──────────────────

#[test]
fn test_cs05_calculator_context_unambiguous() {
    let spec = calculator_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Calculator's single category "Expr" has no callers (top-level only)
    // → context_count = 0 → unambiguous
    let expr_unambiguous = analysis
        .context_unambiguous
        .get("Expr")
        .copied()
        .unwrap_or(false);
    assert!(expr_unambiguous, "top-level-only category should be context-unambiguous");
}

#[test]
fn test_cs05_mutual_recursion_ambiguity() {
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // In mutual recursion, each category is called from at least the other
    // Check that both are present in the map
    assert!(
        analysis.context_unambiguous.contains_key("Expr"),
        "Expr should have context ambiguity analysis"
    );
    assert!(
        analysis.context_unambiguous.contains_key("Decl"),
        "Decl should have context ambiguity analysis"
    );
}

#[test]
fn test_cs05_orphan_category_unambiguous() {
    let spec = orphan_grammar_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // Orphan is unreachable so it won't be in reachable_categories.
    // Only reachable categories get context ambiguity analysis.
    // Expr (the reachable one) has no callers → context_count = 0 → unambiguous
    if let Some(&unambiguous) = analysis.context_unambiguous.get("Expr") {
        assert!(unambiguous, "top-level category with no callers should be context-unambiguous");
    }

    // Orphan, if present, should also be unambiguous (no callers)
    if let Some(&unambiguous) = analysis.context_unambiguous.get("Orphan") {
        assert!(unambiguous, "orphan category with no callers should be context-unambiguous");
    }
}

#[test]
fn test_cs05_single_caller_unambiguous() {
    // A category called from exactly one other category should be unambiguous
    let spec = mutual_recursion_spec();
    let wfsts = HashMap::new();
    let analysis = analyze_wpds(&spec, &wfsts);

    // At least one category should have a defined ambiguity status
    assert!(
        !analysis.context_unambiguous.is_empty(),
        "context_unambiguous map should not be empty for multi-category grammar"
    );

    // Verify the invariant: categories with ≤1 unique caller are unambiguous
    for (cat, &is_unambiguous) in &analysis.context_unambiguous {
        let unique_callers = analysis
            .calling_contexts
            .get(cat)
            .map(|contexts| {
                contexts
                    .iter()
                    .map(|c| c.caller_category.as_str())
                    .collect::<HashSet<_>>()
                    .len()
            })
            .unwrap_or(0);

        if unique_callers <= 1 {
            assert!(
                is_unambiguous,
                "{cat} has {unique_callers} unique callers but is marked ambiguous"
            );
        } else {
            assert!(
                !is_unambiguous,
                "{cat} has {unique_callers} unique callers but is marked unambiguous"
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════
// CEK-3: WPDS ↔ Frame Bijection Tests
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn test_cek_bijection_roundtrip() {
    let mut bij = CekWpdsBijection::new();
    let sym = StackSymbol::rule_position("Expr", "Add", 1);
    bij.insert("RD_Add_0".to_string(), sym.clone());

    assert_eq!(bij.frame_variant_to_stack_symbol("RD_Add_0"), Some(&sym));
    assert_eq!(bij.stack_symbol_to_frame_variant(&sym), Some(&"RD_Add_0".to_string()));
    assert!(bij.is_complete());
}

#[test]
fn test_cek_bijection_empty() {
    let bij = CekWpdsBijection::new();
    assert!(bij.is_empty());
    assert_eq!(bij.len(), 0);
    assert!(bij.is_complete());
}

#[test]
fn test_cek_bijection_multiple_entries() {
    let mut bij = CekWpdsBijection::new();
    bij.insert("InfixRHS".to_string(), StackSymbol::rule_position("Expr", "__infix__", 1));
    bij.insert("GroupClose".to_string(), StackSymbol::rule_position("Expr", "__group__", 1));
    bij.insert("UnaryPrefix_Neg".to_string(), StackSymbol::rule_position("Expr", "Neg", 1));
    bij.insert("RD_Let_0".to_string(), StackSymbol::rule_position("Expr", "Let", 1));
    bij.insert("RD_Let_1".to_string(), StackSymbol::rule_position("Expr", "Let", 2));

    assert_eq!(bij.len(), 5);
    assert!(bij.is_complete());

    // Verify all round-trips
    assert_eq!(
        bij.frame_variant_to_stack_symbol("InfixRHS"),
        Some(&StackSymbol::rule_position("Expr", "__infix__", 1))
    );
    assert_eq!(
        bij.frame_variant_to_stack_symbol("RD_Let_1"),
        Some(&StackSymbol::rule_position("Expr", "Let", 2))
    );
}

#[test]
fn test_cek_bijection_missing_lookup() {
    let bij = CekWpdsBijection::new();
    assert_eq!(bij.frame_variant_to_stack_symbol("Nonexistent"), None);
    assert_eq!(
        bij.stack_symbol_to_frame_variant(&StackSymbol::rule_position("X", "Y", 1)),
        None
    );
}

#[test]
fn test_cek_bijection_from_calculator_spec() {
    // Use the existing calculator_spec() helper which has Expr = Int | Expr "+" Expr
    let spec = calculator_spec();
    let bij = build_cek_bijection(&spec);

    // Should have GroupClose for Expr
    assert!(bij
        .frame_variant_to_stack_symbol("Expr::GroupClose")
        .is_some());

    // The Add rule has syntax: [NT(Expr), Terminal("+"), NT(Expr)]
    // This is an infix rule (2 NTs, 1 terminal), so it should produce
    // InfixRHS mapping for the category
    assert!(bij
        .frame_variant_to_stack_symbol("Expr::InfixRHS")
        .is_some());

    // The bijection should be internally consistent
    assert!(bij.is_complete());
}

#[test]
fn test_cek_bijection_rd_position_tracking() {
    // Construct a rule with mixed items: Terminal, NT(same), Terminal, NT(same)
    // WPDS positions: 0=Terminal, 1=NT(same), 2=Terminal, 3=NT(same)
    // Trampoline segments: segment_index=0 at wpds_pos=1, segment_index=1 at wpds_pos=3
    // So: RD_LetIn_0 → rule_position("Expr", "LetIn", 2)
    //     RD_LetIn_1 → rule_position("Expr", "LetIn", 4)
    let types = vec![CategorySpec {
        name: "Expr".to_string(),
        native_type: Some("i64".to_string()),
        is_primary: true,
        has_var: true,
    }];

    let inputs = vec![RuleSpecInput {
        label: "LetIn".to_string(),
        category: "Expr".to_string(),
        syntax: vec![
            SyntaxItemSpec::Terminal("let".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "binding".to_string(),
            },
            SyntaxItemSpec::Terminal("in".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "body".to_string(),
            },
        ],
        associativity: Associativity::Left,
        shares_level_with_previous: false,
        prefix_precedence: None,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
        source_location: None,
        is_auto_injected: false,
    }];

    let spec = LanguageSpec::new("TestLang".to_string(), types, inputs);
    let bij = build_cek_bijection(&spec);

    // RD_LetIn_0: same-cat NT at wpds_pos=1, continuation at pos=2
    let sym0 = bij.frame_variant_to_stack_symbol("RD_LetIn_0");
    assert_eq!(
        sym0,
        Some(&StackSymbol::rule_position("Expr", "LetIn", 2)),
        "First same-category NT continuation should be at WPDS position 2"
    );

    // RD_LetIn_1: same-cat NT at wpds_pos=3, continuation at pos=4
    let sym1 = bij.frame_variant_to_stack_symbol("RD_LetIn_1");
    assert_eq!(
        sym1,
        Some(&StackSymbol::rule_position("Expr", "LetIn", 4)),
        "Second same-category NT continuation should be at WPDS position 4"
    );

    assert!(bij.is_complete());
}

#[test]
fn test_cek_bijection_cross_category_nt_skipped() {
    // Cross-category NTs increment WPDS position but do NOT create
    // trampoline split points. Verify the bijection accounts for this.
    //
    // Rule: Terminal("f"), NT(Type), NT(Expr)
    // WPDS positions: 0=Terminal, 1=NT(Type, cross-cat), 2=NT(Expr, same-cat)
    // Trampoline: only segment_index=0 at the same-cat NT
    // So: RD_Apply_0 → rule_position("Expr", "Apply", 3)
    let types = vec![
        CategorySpec {
            name: "Expr".to_string(),
            native_type: Some("i64".to_string()),
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Type".to_string(),
            native_type: Some("String".to_string()),
            is_primary: false,
            has_var: true,
        },
    ];

    let inputs = vec![RuleSpecInput {
        label: "Apply".to_string(),
        category: "Expr".to_string(),
        syntax: vec![
            SyntaxItemSpec::Terminal("apply".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Type".to_string(),
                param_name: "ty".to_string(),
            },
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "arg".to_string(),
            },
        ],
        associativity: Associativity::Left,
        shares_level_with_previous: false,
        prefix_precedence: None,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
        source_location: None,
        is_auto_injected: false,
    }];

    let spec = LanguageSpec::new("TestLang".to_string(), types, inputs);
    let bij = build_cek_bijection(&spec);

    // The same-cat NT (Expr) is at wpds_pos=2, continuation at pos=3
    let sym = bij.frame_variant_to_stack_symbol("RD_Apply_0");
    assert_eq!(
        sym,
        Some(&StackSymbol::rule_position("Expr", "Apply", 3)),
        "Same-category NT after cross-category NT should have correct WPDS position"
    );

    assert!(bij.is_complete());
}
