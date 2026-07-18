use super::*;
use crate::prediction::{FirstItem, FirstSet, RuleInfo};

/// Helper: create a RuleInfo with sensible defaults.
fn rule(label: &str, category: &str) -> RuleInfo {
    RuleInfo {
        label: label.to_string(),
        category: category.to_string(),
        first_items: Vec::new(),
        is_infix: false,
        is_var: false,
        is_literal: false,
        is_cross_category: false,
        is_cast: false,
    }
}

/// Helper: create a CategoryInfo.
fn category(name: &str, is_primary: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: None,
        is_primary,
        has_var: true,
    }
}

fn category_spec(name: &str, native_type: Option<&str>, is_primary: bool) -> crate::CategorySpec {
    crate::CategorySpec {
        name: name.to_string(),
        native_type: native_type.map(str::to_string),
        is_primary,
        has_var: true,
    }
}

fn refinement_spec(name: &str, base_category: &str) -> crate::RefinementTypeSpec {
    crate::RefinementTypeSpec {
        name: name.to_string(),
        base_category: base_category.to_string(),
        variable_name: "x".to_string(),
        predicate_kind: crate::RefinementPredKind::Presburger,
        predicate_repr: "x > 0".to_string(),
    }
}

/// Helper: create a FirstSet with given tokens.
fn first_set(tokens: &[&str]) -> FirstSet {
    FirstSet {
        tokens: tokens.iter().map(|s| s.to_string()).collect(),
        nullable: false,
    }
}

#[test]
fn test_dead_rules_ignore_auto_injected_labels() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WeightedTransition, WfstState};

    let mut token_map = TokenIdMap::new();
    let kw_not = token_map.get_or_insert("KwNot");
    let mut start = WfstState::new(0);
    start.transitions.push(WeightedTransition {
        from: 0,
        input: kw_not,
        action_idx: 0,
        to: 1,
        weight: TropicalWeight::new(0.0),
    });
    let wfst = PredictionWfst {
        category: "Int".to_string(),
        states: vec![start, WfstState::final_state(1, TropicalWeight::new(0.0))],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "Neg".to_string(),
                parse_fn: "parse_neg".to_string(),
            },
            weight: TropicalWeight::new(0.0),
        }],
        token_map,
        beam_width: None,
        context_labels: HashMap::new(),
    };

    let rule_infos = vec![RuleInfo {
        label: "BoolToInt".to_string(),
        category: "Int".to_string(),
        first_items: vec![FirstItem::NonTerminal("Bool".to_string())],
        is_infix: false,
        is_var: false,
        is_literal: false,
        is_cross_category: false,
        is_cast: true,
    }];
    let categories = vec![category("Int", true), category("Bool", false)];
    let first_sets = HashMap::from([("Int".to_string(), first_set(&["KwNot"]))]);
    let prediction_wfsts = HashMap::from([("Int".to_string(), wfst)]);

    let unignored = detect_dead_rules(
        &rule_infos,
        &categories,
        &first_sets,
        &prediction_wfsts,
        &[],
        &HashSet::new(),
        &[],
    );
    assert!(
            unignored
                .iter()
                .any(|w| matches!(w, DeadRuleWarning::WfstUnreachable { rule_label, .. } if rule_label == "BoolToInt")),
            "BoolToInt should be W01 without the synthetic ignore set: {:?}",
            unignored
        );

    let ignored_labels = HashSet::from(["BoolToInt".to_string()]);
    let ignored = detect_dead_rules_with_ignored(
        &rule_infos,
        &categories,
        &first_sets,
        &prediction_wfsts,
        &[],
        &HashSet::new(),
        &[],
        &ignored_labels,
    );
    assert!(ignored.is_empty(), "ignored synthetic labels should not warn: {:?}", ignored);
}

#[test]
fn test_dead_rule_wfst_warnings_require_trie_confirmation() {
    use crate::automata::codegen::terminal_to_variant_name;
    use crate::decision_tree::DecisionTreeBuilder;
    use crate::grammar::ir::{RDRuleInfo, RDSyntaxItem};
    use crate::token_id::TokenIdMap;

    let dispatch_token = terminal_to_variant_name("live");
    let token_map = TokenIdMap::from_names([dispatch_token]);
    let first_sets = HashMap::from([("Expr".to_string(), first_set(&["KwLive"]))]);
    let rd_rules = vec![RDRuleInfo {
        label: "TrieReachable".to_string(),
        category: "Expr".to_string(),
        items: vec![RDSyntaxItem::Terminal("live".to_string())],
        has_binder: false,
        has_multi_binder: false,
        is_collection: false,
        collection_type: None,
        separator: None,
        prefix_bp: None,
        eval_mode: None,
    }];
    let mut builder =
        DecisionTreeBuilder::new(token_map, first_sets, vec!["Expr".to_string()], HashSet::new());
    builder.build_all(&rd_rules, &[], &[]);

    let filtered = filter_dead_rule_warnings_with_decision_trees(
        vec![
            DeadRuleWarning::WfstUnreachable {
                rule_label: "TrieReachable".to_string(),
                category: "Expr".to_string(),
            },
            DeadRuleWarning::WfstUnreachable {
                rule_label: "TrulyDead".to_string(),
                category: "Expr".to_string(),
            },
        ],
        builder.trees(),
    );

    assert!(
            !filtered.iter().any(
                |w| matches!(w, DeadRuleWarning::WfstUnreachable { rule_label, .. } if rule_label == "TrieReachable")
            ),
            "trie-reachable rules should not be reported from WFST-only evidence: {:?}",
            filtered
        );
    assert!(
            filtered.iter().any(
                |w| matches!(w, DeadRuleWarning::WfstUnreachable { rule_label, .. } if rule_label == "TrulyDead")
            ),
            "rules absent from both WFST and trie should remain dead: {:?}",
            filtered
        );
}

#[test]
fn test_refinement_downcast_labels_are_dead_rule_ignored() {
    let mut spec = LanguageSpec::new(
        "RefinementSmoke".to_string(),
        vec![
            crate::CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
                has_var: true,
            },
            crate::CategorySpec {
                name: "PosInt".to_string(),
                native_type: None,
                is_primary: false,
                has_var: true,
            },
        ],
        vec![
            crate::RuleSpecInput {
                label: "IntToPosInt".to_string(),
                category: "PosInt".to_string(),
                syntax: vec![SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "i".to_string(),
                }],
                associativity: crate::binding_power::Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
                is_auto_injected: false,
            },
            crate::RuleSpecInput {
                label: "OtherToPosInt".to_string(),
                category: "PosInt".to_string(),
                syntax: vec![SyntaxItemSpec::NonTerminal {
                    category: "Other".to_string(),
                    param_name: "x".to_string(),
                }],
                associativity: crate::binding_power::Associativity::Left,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
                is_auto_injected: false,
            },
        ],
    );
    spec.refinement_types.push(crate::RefinementTypeSpec {
        name: "PosInt".to_string(),
        base_category: "Int".to_string(),
        variable_name: "x".to_string(),
        predicate_kind: crate::RefinementPredKind::Presburger,
        predicate_repr: "x > 0".to_string(),
    });

    let ignored = collect_refinement_downcast_rule_labels(&spec);

    assert!(ignored.contains("IntToPosInt"), "refinement downcast should be ignored");
    assert!(
        !ignored.contains("OtherToPosInt"),
        "only declared base-category downcasts should be ignored"
    );
}

#[test]
fn test_refinement_analysis_ignores_own_refinement_category_for_rt06() {
    let mut spec = LanguageSpec::new(
        "RefinementSmoke".to_string(),
        vec![category_spec("Int", Some("i32"), true), category_spec("PosInt", None, false)],
        Vec::new(),
    );
    spec.refinement_types.push(refinement_spec("PosInt", "Int"));

    let (_, bundle) = extract_from_spec(&spec);
    let analysis = analyze_refinement_types(&bundle);

    assert!(
        analysis.name_shadows.is_empty(),
        "normal refinement category should not trigger RT06: {:?}",
        analysis.name_shadows
    );
}

#[test]
fn test_refinement_analysis_reports_self_shadowing_rt06() {
    let mut spec = LanguageSpec::new(
        "ShadowSmoke".to_string(),
        vec![category_spec("Int", Some("i32"), true), category_spec("Int", None, false)],
        Vec::new(),
    );
    spec.refinement_types.push(refinement_spec("Int", "Int"));

    let (_, bundle) = extract_from_spec(&spec);
    let analysis = analyze_refinement_types(&bundle);

    assert_eq!(
        analysis.name_shadows,
        vec![("Int".to_string(), "Int".to_string())],
        "self-shadowing refinement should still trigger RT06"
    );
}

// ── A8: ProductWeight<BooleanWeight, CountingWeight> nearly-dead detection ──

#[test]
fn test_a8_nearly_dead_ratio_threshold() {
    // A8: NEARLY_DEAD_RATIO should be 0.01 (1%)
    assert_eq!(NEARLY_DEAD_RATIO, 0.01);
}

#[test]
fn test_a8_single_category_returns_empty() {
    // A8: With only one category, no inter-category analysis is possible.
    let cats = vec![category("Expr", true)];
    let rules = vec![rule("Add", "Expr")];
    let first_sets: HashMap<String, FirstSet> = [("Expr".to_string(), first_set(&["Plus"]))].into();
    let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
    assert!(warnings.is_empty(), "single category should produce no warnings");
}

#[test]
fn test_a8_well_connected_categories_no_warnings() {
    // A8: When all categories are well-connected via cast rules, no nearly-dead warnings.
    let cats = vec![category("Proc", true), category("Int", false)];
    let mut r1 = rule("IntToProc", "Proc");
    r1.is_cast = true;
    r1.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
    let mut r2 = rule("ProcToInt", "Int");
    r2.is_cast = true;
    r2.first_items = vec![FirstItem::NonTerminal("Proc".to_string())];
    let r3 = rule("Add", "Int");
    let r4 = rule("Par", "Proc");
    let rules = vec![r1, r2, r3, r4];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["Par"])),
        ("Int".to_string(), first_set(&["Plus"])),
    ]
    .into();

    let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
    assert!(
        warnings.is_empty(),
        "well-connected categories should not be nearly-dead: {:?}",
        warnings
    );
}

#[test]
fn test_a8_isolated_category_not_flagged_as_nearly_dead() {
    // A8: Completely unreachable categories should NOT be flagged by detect_nearly_dead_paths
    // (they are handled by the A4 detect_inter_category_dead_paths function).
    let cats = vec![category("Proc", true), category("Int", false), category("Orphan", false)];
    let mut r1 = rule("IntToProc", "Proc");
    r1.is_cast = true;
    r1.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
    let r2 = rule("Add", "Int");
    let r3 = rule("OrphanRule", "Orphan");
    let rules = vec![r1, r2, r3];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["Par"])),
        ("Int".to_string(), first_set(&["Plus"])),
        ("Orphan".to_string(), first_set(&["Bang"])),
    ]
    .into();

    let warnings = detect_nearly_dead_paths(&rules, &cats, &first_sets, &[]);
    // Orphan is completely unreachable (forward = zero), so it should NOT appear
    // in nearly-dead warnings (that's A4's job).
    let orphan_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::NearlyDeadPath { category, .. } if category == "Orphan")
        }).collect();
    assert!(
        orphan_warnings.is_empty(),
        "completely unreachable category should not be flagged as nearly-dead"
    );
}

#[test]
fn test_a8_product_weight_semiring_properties() {
    // A8: Verify ProductWeight<BooleanWeight, CountingWeight> semiring axioms.
    use crate::automata::semiring::{BooleanWeight, CountingWeight, ProductWeight, Semiring};

    type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;

    // zero
    let z = BoolCount::zero();
    assert!(z.left.is_zero());
    assert_eq!(z.right.count(), 0);

    // one
    let o = BoolCount::one();
    assert!(o.left.is_reachable());
    assert_eq!(o.right.count(), 1);

    // plus (Boolean OR, Counting add)
    let a = BoolCount::new(BooleanWeight::new(true), CountingWeight::new(3));
    let b = BoolCount::new(BooleanWeight::new(true), CountingWeight::new(5));
    let ab = a.plus(&b);
    assert!(ab.left.is_reachable());
    assert_eq!(ab.right.count(), 8);

    // times (Boolean AND, Counting multiply)
    let c = a.times(&b);
    assert!(c.left.is_reachable());
    assert_eq!(c.right.count(), 15);

    // zero annihilates
    let az = a.times(&z);
    assert!(az.left.is_zero());
    assert_eq!(az.right.count(), 0);
}

#[test]
fn test_a8_forward_backward_with_product_weight() {
    // A8: Verify forward-backward with ProductWeight produces correct counts.
    use crate::automata::semiring::{BooleanWeight, CountingWeight, ProductWeight, Semiring};
    use crate::forward_backward::{backward_scores, forward_scores};

    type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;

    // Diamond: 0 → 1, 0 → 2, 1 → 3, 2 → 3
    let w = BoolCount::new(BooleanWeight::one(), CountingWeight::one());
    let edges: Vec<Vec<(usize, BoolCount)>> = vec![
        vec![(1, w), (2, w)], // node 0 → 1, 2
        vec![(3, w)],         // node 1 → 3
        vec![(3, w)],         // node 2 → 3
        vec![],               // node 3: sink
    ];

    let fwd = forward_scores::<BoolCount>(&edges, 4);
    // fwd[0] = one() = (true, 1)
    assert!(fwd[0].left.is_reachable());
    assert_eq!(fwd[0].right.count(), 1);
    // fwd[1] = (true, 1) — one path from 0
    assert!(fwd[1].left.is_reachable());
    assert_eq!(fwd[1].right.count(), 1);
    // fwd[2] = (true, 1) — one path from 0
    assert!(fwd[2].left.is_reachable());
    assert_eq!(fwd[2].right.count(), 1);
    // fwd[3] = (true, 2) — two paths: 0→1→3, 0→2→3
    assert!(fwd[3].left.is_reachable());
    assert_eq!(fwd[3].right.count(), 2);

    let bwd = backward_scores::<BoolCount>(&edges, 4, 3);
    // bwd[3] = one() = (true, 1)
    assert!(bwd[3].left.is_reachable());
    assert_eq!(bwd[3].right.count(), 1);
    // bwd[0] should also be (true, 2)
    assert!(bwd[0].left.is_reachable());
    assert_eq!(bwd[0].right.count(), 2);
}

#[test]
fn test_a8_nearly_dead_warning_display() {
    // A8: Display format for NearlyDeadPath warning.
    let w = DeadRuleWarning::NearlyDeadPath {
        rule_label: "ObscureCast".to_string(),
        category: "Rare".to_string(),
        derivation_count: 1,
        total_count: 500,
    };
    let msg = format!("{}", w);
    assert!(msg.contains("nearly-dead"), "should mention nearly-dead: {}", msg);
    assert!(msg.contains("1/500"), "should mention 1/500: {}", msg);
    assert!(msg.contains("ObscureCast"), "should mention rule label: {}", msg);
    assert!(msg.contains("Rare"), "should mention category: {}", msg);
}

// ── A4: Inter-category dead-path detection ──

#[test]
fn test_a4_cyclic_graph_backward_reachable() {
    // Calculator pattern: Int(root), Float, Bool, Str.
    // Cross-cat edges: Int↔Bool, Float↔Bool, Str↔Bool (via comparison ops).
    // Str→Bool→Int is a valid path, so Str must NOT be flagged.
    let cats = vec![
        category("Int", true),
        category("Float", false),
        category("Bool", false),
        category("Str", false),
    ];
    // Cross-category infix rules creating bidirectional connections
    let mut eq_int = rule("EqInt", "Bool");
    eq_int.is_cross_category = true;
    eq_int.is_infix = true;
    eq_int.first_items = vec![FirstItem::NonTerminal("Int".to_string())];

    let mut eq_float = rule("EqFloat", "Bool");
    eq_float.is_cross_category = true;
    eq_float.is_infix = true;
    eq_float.first_items = vec![FirstItem::NonTerminal("Float".to_string())];

    let mut eq_str = rule("EqStr", "Bool");
    eq_str.is_cross_category = true;
    eq_str.is_infix = true;
    eq_str.first_items = vec![FirstItem::NonTerminal("Str".to_string())];

    let rules = vec![
        rule("NumLit", "Int"),
        rule("FltLit", "Float"),
        rule("True", "Bool"),
        rule("Concat", "Str"),
        eq_int,
        eq_float,
        eq_str,
    ];
    let first_sets: HashMap<String, FirstSet> = [
        ("Int".to_string(), first_set(&["Integer"])),
        ("Float".to_string(), first_set(&["Float"])),
        ("Bool".to_string(), first_set(&["true", "false"])),
        ("Str".to_string(), first_set(&["String"])),
    ]
    .into();

    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
    let str_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Str")
        }).collect();
    assert!(
        str_warnings.is_empty(),
        "Str should not be flagged as dead (Str→Bool→Int is valid): {:?}",
        str_warnings
    );

    // No categories should be flagged since all are connected through Bool
    assert!(
        warnings.is_empty(),
        "no categories should be flagged in well-connected cyclic graph: {:?}",
        warnings
    );
}

#[test]
fn test_a4_prefix_rule_with_cross_category_nonterminal() {
    // NQuote pattern: Name has rule `"@" "(" Proc ")"` — a regular prefix rule
    // that references Proc as a NonTerminal in its syntax (not as first item).
    // Also: Proc has `"*" Name` (PDrop). So Name↔Proc are connected.
    let cats = vec![category("Proc", true), category("Name", false)];
    let rules = vec![rule("PPar", "Proc"), rule("PDrop", "Proc"), rule("NQuote", "Name")];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["|", "*"])),
        ("Name".to_string(), first_set(&["@"])),
    ]
    .into();

    // NQuote syntax: "@" "(" Proc ")" — references Proc as NonTerminal
    // PDrop syntax: "*" Name — references Name as NonTerminal
    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![
        (
            "NQuote".to_string(),
            "Name".to_string(),
            vec![
                SyntaxItemSpec::Terminal("@".to_string()),
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "p".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ),
        (
            "PDrop".to_string(),
            "Proc".to_string(),
            vec![
                SyntaxItemSpec::Terminal("*".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Name".to_string(),
                    param_name: "n".to_string(),
                },
            ],
        ),
    ];

    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
    let name_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Name")
        }).collect();
    assert!(
        name_warnings.is_empty(),
        "Name should not be flagged as dead (connected to Proc via syntax): {:?}",
        name_warnings
    );
    assert!(warnings.is_empty(), "no categories should be flagged: {:?}", warnings);
}

#[test]
fn test_a4_truly_isolated_category_flagged() {
    // Orphan category with no cross-category references at all.
    let cats = vec![category("Proc", true), category("Int", false), category("Orphan", false)];
    let mut cast = rule("IntToProc", "Proc");
    cast.is_cast = true;
    cast.first_items = vec![FirstItem::NonTerminal("Int".to_string())];
    let rules = vec![rule("PPar", "Proc"), rule("Add", "Int"), cast, rule("OrphanRule", "Orphan")];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["|"])),
        ("Int".to_string(), first_set(&["Integer"])),
        ("Orphan".to_string(), first_set(&["!"])),
    ]
    .into();

    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
    let orphan_warnings: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category == "Orphan")
        }).collect();
    assert!(
        !orphan_warnings.is_empty(),
        "Orphan should be flagged as dead (no connections to root)"
    );
    // Non-orphan categories should NOT be flagged
    let non_orphan: Vec<_> = warnings.iter().filter(|w| {
            matches!(w, DeadRuleWarning::InterCategoryDeadPath { category, .. } if category != "Orphan")
        }).collect();
    assert!(non_orphan.is_empty(), "only Orphan should be flagged: {:?}", non_orphan);
}

#[test]
fn test_a4_single_category_no_warnings() {
    // With only one category, no inter-category analysis possible.
    let cats = vec![category("Expr", true)];
    let rules = vec![rule("Add", "Expr")];
    let first_sets: HashMap<String, FirstSet> = [("Expr".to_string(), first_set(&["Plus"]))].into();
    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &[]);
    assert!(warnings.is_empty(), "single category should produce no warnings");
}

#[test]
fn test_a4_syntax_binder_creates_edge() {
    // A Binder referencing a different category creates an inter-category edge.
    let cats = vec![category("Proc", true), category("Name", false)];
    let rules = vec![rule("PPar", "Proc"), rule("NVar", "Name")];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["|"])),
        ("Name".to_string(), first_set(&["Ident"])),
    ]
    .into();

    // Proc rule with a Binder from Name category
    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![(
        "PNew".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("new".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "n".to_string(),
                category: "Name".to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::Terminal("in".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
        ],
    )];

    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
    assert!(
        warnings.is_empty(),
        "Name should be reachable via Binder from Proc: {:?}",
        warnings
    );
}

#[test]
fn test_a4_syntax_collection_creates_edge() {
    // A Collection referencing a different category creates an inter-category edge.
    let cats = vec![category("Proc", true), category("Arg", false)];
    let rules = vec![rule("PPar", "Proc"), rule("ArgLit", "Arg")];
    let first_sets: HashMap<String, FirstSet> = [
        ("Proc".to_string(), first_set(&["|"])),
        ("Arg".to_string(), first_set(&["Integer"])),
    ]
    .into();

    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = vec![(
        "PCall".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("call".to_string()),
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::Collection {
                param_name: "args".to_string(),
                element_category: "Arg".to_string(),
                separator: ",".to_string(),
                key_val_separator: None,
                kind: crate::grammar::ir::CollectionKind::Vec,
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    )];

    let warnings = detect_inter_category_dead_paths(&rules, &cats, &first_sets, &all_syntax);
    assert!(
        warnings.is_empty(),
        "Arg should be reachable via Collection from Proc: {:?}",
        warnings
    );
}

// ── DB03: Parallel analysis phase execution tests ────────────────────

#[test]
fn test_db03_count_analysis_phases_baseline() {
    // count_analysis_phases() should return at least 3 (safety, cegar,
    // algebraic) even with no feature flags enabled.
    let count = super::count_analysis_phases();
    assert!(
        count >= 3,
        "count_analysis_phases should include at least 3 always-on phases, got {}",
        count
    );
}

#[test]
fn test_db03_sequential_ineligible_returns_none() {
    // When eligible=false, run_math_analyses_sequential should return
    // None for all result fields and phase_count=0.
    let bundle = ParserBundle {
        grammar_name: "Test".to_string(),
        categories: vec![category("Proc", true), category("Int", false)],
        bp_table: crate::binding_power::BindingPowerTable { operators: Vec::new() },
        rule_infos: vec![rule("Add", "Int")],
        follow_inputs: Vec::new(),
        rd_rules: Vec::new(),
        cross_rules: Vec::new(),
        cast_rules: Vec::new(),
        has_binders: false,
        beam_width: crate::BeamWidthConfig::default(),
        recovery_config: crate::recovery::RecoveryConfig::default(),
        all_syntax: Vec::new(),
        rule_locations: std::collections::HashMap::new(),
        dead_rule_ignore_labels: HashSet::new(),
        semantic_dependency_groups: Vec::new(),
        custom_tokens: Vec::new(),
        refinement_types: Vec::new(),
    };

    let results = super::run_math_analyses_sequential(&bundle, None, false);
    assert_eq!(results.phase_count, 0, "phase_count should be 0 for sequential path");
    assert!(results.safety_result.is_none(), "safety_result should be None when ineligible");
    assert!(results.cegar_result.is_none(), "cegar_result should be None when ineligible");
    assert!(
        results.algebraic_result.is_none(),
        "algebraic_result should be None when ineligible"
    );
}

#[test]
fn test_db03_parallel_returns_results() {
    // run_math_analyses_parallel should run without panicking and
    // return valid MathAnalysisResults with phase_count > 0.
    // With no WPDS analysis, WPDS-dependent results should be None,
    // but the function should still complete successfully.
    let bundle = ParserBundle {
        grammar_name: "TestParallel".to_string(),
        categories: vec![category("Proc", true), category("Int", false), category("Bool", false)],
        bp_table: crate::binding_power::BindingPowerTable { operators: Vec::new() },
        rule_infos: vec![rule("PPar", "Proc"), rule("Add", "Int"), rule("BTrue", "Bool")],
        follow_inputs: Vec::new(),
        rd_rules: Vec::new(),
        cross_rules: Vec::new(),
        cast_rules: Vec::new(),
        has_binders: false,
        beam_width: crate::BeamWidthConfig::default(),
        recovery_config: crate::recovery::RecoveryConfig::default(),
        all_syntax: vec![
            (
                "PPar".to_string(),
                "Proc".to_string(),
                vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Proc".to_string(),
                        param_name: "p".to_string(),
                    },
                    SyntaxItemSpec::Terminal("|".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Proc".to_string(),
                        param_name: "q".to_string(),
                    },
                ],
            ),
            (
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
            ),
        ],
        rule_locations: std::collections::HashMap::new(),
        dead_rule_ignore_labels: HashSet::new(),
        semantic_dependency_groups: Vec::new(),
        custom_tokens: Vec::new(),
        refinement_types: Vec::new(),
    };

    let results = super::run_math_analyses_parallel(&bundle, None);
    assert!(
        results.phase_count >= 3,
        "parallel phase_count should be >= 3, got {}",
        results.phase_count
    );
    // Without WPDS analysis, WPDS-dependent results should be None
    assert!(results.safety_result.is_none(), "safety_result should be None without WPDS");
    assert!(results.cegar_result.is_none(), "cegar_result should be None without WPDS");
    assert!(
        results.algebraic_result.is_none(),
        "algebraic_result should be None without WPDS"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Advanced automata codegen promotion tests
// ══════════════════════════════════════════════════════════════════════════

/// Helper: construct an empty AdvancedAnalysisBundle (all fields None).
fn empty_bundle<'a>() -> super::AdvancedAnalysisBundle<'a> {
    super::AdvancedAnalysisBundle {
        symbolic: None,
        alternating: None,
        bisimulation: None,
        vpa: None,
        register: None,
        probabilistic: None,
        multi_tape: None,
        buchi: None,
        _phantom: std::marker::PhantomData,
    }
}

/// Helper: call build_pipeline_analysis with minimal inputs and a given bundle.
fn run_build_pipeline(
    dead_rules: &HashSet<String>,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    categories: &[CategoryInfo],
    rule_infos: &[RuleInfo],
    bundle: &super::AdvancedAnalysisBundle<'_>,
) -> crate::PipelineAnalysis {
    super::build_pipeline_analysis(
        dead_rules,
        prediction_wfsts,
        categories,
        rule_infos,
        HashMap::new(), // decision_trees
        bundle,
    )
}

// ── Test 1: SYM01-DCE — unsatisfiable guards extend dead rules ──────────

#[test]
fn test_symbolic_dead_guard_extends_dead_rules() {
    let sym = crate::symbolic::SymbolicAnalysis {
        num_states: 2,
        num_transitions: 2,
        guard_satisfiability: vec![("guard_1".into(), false), ("guard_2".into(), false)],
        overlapping_guards: Vec::new(),
        subsumed_guards: Vec::new(),
        unsatisfiable_rule_labels: vec!["dead_guard_1".into(), "dead_guard_2".into()],
    };
    let mut bundle = empty_bundle();
    bundle.symbolic = Some(&sym);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![
        rule("dead_guard_1", "Expr"),
        rule("dead_guard_2", "Expr"),
        rule("alive_rule", "Expr"),
    ];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.dead_rule_labels.contains("dead_guard_1"),
        "dead_guard_1 should be in dead_rule_labels"
    );
    assert!(
        analysis.dead_rule_labels.contains("dead_guard_2"),
        "dead_guard_2 should be in dead_rule_labels"
    );
}

// ── Test 2: SYM01-DCE — satisfiable guards do not add dead rules ────────

#[test]
fn test_symbolic_satisfiable_guards_no_dead() {
    let sym = crate::symbolic::SymbolicAnalysis {
        num_states: 1,
        num_transitions: 1,
        guard_satisfiability: vec![("guard_ok".into(), true)],
        overlapping_guards: Vec::new(),
        subsumed_guards: Vec::new(),
        unsatisfiable_rule_labels: Vec::new(),
    };
    let mut bundle = empty_bundle();
    bundle.symbolic = Some(&sym);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("alive", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.dead_rule_labels.is_empty(),
        "no dead rules should be added when all guards are satisfiable"
    );
}

// ── Test 3: PR01-DCE — low-selectivity rules extend dead rules ──────────

#[test]
fn test_probabilistic_low_selectivity_extends_dead() {
    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 3,
        is_normalized: true,
        total_selectivity: 0.8,
        mean_entropy: 1.5,
        low_selectivity_rules: vec!["low_1".into(), "low_2".into()],
        rule_selectivities: HashMap::new(),
    };
    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("low_1", "Expr"), rule("low_2", "Expr"), rule("alive", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.dead_rule_labels.contains("low_1"),
        "low_1 should be in dead_rule_labels"
    );
    assert!(
        analysis.dead_rule_labels.contains("low_2"),
        "low_2 should be in dead_rule_labels"
    );
}

// ── Test 4: PR01-DCE — not-normalized PA does not extend dead rules ─────

#[test]
fn test_probabilistic_not_normalized_no_dead() {
    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 2,
        is_normalized: false,
        total_selectivity: 0.5,
        mean_entropy: 1.0,
        low_selectivity_rules: vec!["low_1".into()],
        rule_selectivities: HashMap::new(),
    };
    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("low_1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        !analysis.dead_rule_labels.contains("low_1"),
        "low_1 should NOT be in dead_rule_labels when not normalized"
    );
}

// ── Test 5: PR01-WEIGHT — probabilistic weight blending ─────────────────

#[test]
fn test_probabilistic_weight_blend() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    // Build a PredictionWfst with one action for "rule_1" at weight 1.0.
    let mut wfst = PredictionWfst {
        category: "Expr".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "rule_1".into(),
                parse_fn: "parse_rule_1".into(),
            },
            weight: TropicalWeight::new(1.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    // Make state 0 final so the WFST is well-formed.
    wfst.states[0].is_final = true;

    let mut prediction_wfsts = HashMap::new();
    prediction_wfsts.insert("Expr".into(), wfst);

    let selectivity = 0.5_f64;
    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 1,
        is_normalized: true,
        total_selectivity: 1.0,
        mean_entropy: 0.0,
        low_selectivity_rules: Vec::new(),
        rule_selectivities: {
            let mut m = HashMap::new();
            m.insert("rule_1".into(), selectivity);
            m
        },
    };
    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("rule_1", "Expr")];
    let dead_rules = HashSet::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Expected: (1.0 + (-ln(0.5))) / 2 = (1.0 + 0.6931...) / 2 = 0.8465...
    let expected = (1.0 + (-selectivity.ln())) / 2.0;
    let actual = analysis
        .constructor_weights
        .get("rule_1")
        .copied()
        .expect("rule_1 should have a constructor weight");
    assert!(
        (actual - expected).abs() < 1e-9,
        "blended weight should be {expected}, got {actual}"
    );
}

// ── Test 6: PR01-WEIGHT — zero selectivity does not panic ───────────────

#[test]
fn test_probabilistic_zero_selectivity_skipped() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    let mut wfst = PredictionWfst {
        category: "Expr".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "rule_z".into(),
                parse_fn: "parse_rule_z".into(),
            },
            weight: TropicalWeight::new(2.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    wfst.states[0].is_final = true;

    let mut prediction_wfsts = HashMap::new();
    prediction_wfsts.insert("Expr".into(), wfst);

    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 1,
        is_normalized: true,
        total_selectivity: 1.0,
        mean_entropy: 0.0,
        low_selectivity_rules: Vec::new(),
        rule_selectivities: {
            let mut m = HashMap::new();
            m.insert("rule_z".into(), 0.0); // zero selectivity
            m
        },
    };
    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("rule_z", "Expr")];
    let dead_rules = HashSet::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Zero selectivity is skipped (guard: *selectivity > 0.0), so the
    // weight should remain at the original WFST value (2.0).
    let actual = analysis
        .constructor_weights
        .get("rule_z")
        .copied()
        .expect("rule_z should have a constructor weight");
    assert!(
        (actual - 2.0).abs() < 1e-9,
        "weight should remain 2.0 when selectivity is 0.0, got {actual}"
    );
}

// ── Test 7: N06-ISO — bisimulation extends isomorphic groups ────────────

#[test]
fn test_alternating_bisimulation_extends_groups() {
    // All 3 categories are bisimilar (no non-bisimilar pairs),
    // so every pair (A,B), (A,C), (B,C) should be grouped.
    let alt = crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: Vec::new(),
        state_count: 3,
    };
    let mut bundle = empty_bundle();
    bundle.alternating = Some(&alt);

    let categories = vec![category("A", true), category("B", false), category("C", false)];
    let rule_infos = vec![rule("r1", "A"), rule("r2", "B"), rule("r3", "C")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // With empty prediction_wfsts (no De Bruijn groups), and no non-bisimilar
    // pairs, we expect new isomorphic groups for all 3 pairs: [A,B], [A,C], [B,C].
    let all_grouped: HashSet<String> = analysis
        .isomorphic_groups
        .iter()
        .flatten()
        .cloned()
        .collect();
    assert!(all_grouped.contains("A"), "A should appear in isomorphic groups");
    assert!(all_grouped.contains("B"), "B should appear in isomorphic groups");
    assert!(all_grouped.contains("C"), "C should appear in isomorphic groups");
    assert!(
        analysis.isomorphic_groups.len() >= 3,
        "should have at least 3 isomorphic groups (one per pair), got {}",
        analysis.isomorphic_groups.len()
    );
}

// ── Test 8: N06-ISO — all non-bisimilar → no new groups ─────────────────

#[test]
fn test_alternating_all_non_bisimilar_no_groups() {
    let alt = crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: vec![
            ("A".into(), "B".into()),
            ("A".into(), "C".into()),
            ("B".into(), "C".into()),
        ],
        state_count: 3,
    };
    let mut bundle = empty_bundle();
    bundle.alternating = Some(&alt);

    let categories = vec![category("A", true), category("B", false), category("C", false)];
    let rule_infos = vec![rule("r1", "A"), rule("r2", "B"), rule("r3", "C")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // With no prediction WFSTs there are no De Bruijn groups, and all pairs
    // are non-bisimilar, so no new isomorphic groups should be added.
    assert!(
        analysis.isomorphic_groups.is_empty(),
        "no isomorphic groups should be added when all pairs are non-bisimilar, got {:?}",
        analysis.isomorphic_groups
    );
}

// ── Test A3a: Bisimilar categories → weight discount ──────────────────

#[test]
fn test_bisimilar_categories_weight_discount() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    // Two categories: Alpha and Beta, both bisimilar (no non-bisimilar pairs).
    // Beta > Alpha lexicographically, so Beta should be deprioritized (+0.5).
    let alt = crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: Vec::new(),
        state_count: 2,
    };
    let mut bundle = empty_bundle();
    bundle.alternating = Some(&alt);

    // Build WFSTs with known weights so constructor_weights are populated.
    let mut wfst_alpha = PredictionWfst {
        category: "Alpha".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "r_alpha".into(),
                parse_fn: "parse_r_alpha".into(),
            },
            weight: TropicalWeight::new(1.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    wfst_alpha.states[0].is_final = true;

    let mut wfst_beta = PredictionWfst {
        category: "Beta".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "r_beta".into(),
                parse_fn: "parse_r_beta".into(),
            },
            weight: TropicalWeight::new(1.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    wfst_beta.states[0].is_final = true;

    let mut prediction_wfsts = HashMap::new();
    prediction_wfsts.insert("Alpha".into(), wfst_alpha);
    prediction_wfsts.insert("Beta".into(), wfst_beta);

    let categories = vec![category("Alpha", true), category("Beta", false)];
    let rule_infos = vec![rule("r_alpha", "Alpha"), rule("r_beta", "Beta")];
    let dead_rules = HashSet::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Alpha's rule should keep its original weight (1.0).
    let alpha_w = analysis
        .constructor_weights
        .get("r_alpha")
        .copied()
        .expect("r_alpha should have a constructor weight");
    assert!((alpha_w - 1.0).abs() < 1e-9, "Alpha's weight should remain 1.0, got {alpha_w}");

    // Beta's rule should be penalized by +0.5 (Beta > Alpha lexicographically).
    let beta_w = analysis
        .constructor_weights
        .get("r_beta")
        .copied()
        .expect("r_beta should have a constructor weight");
    assert!(
        (beta_w - 1.5).abs() < 1e-9,
        "Beta's weight should be 1.5 (1.0 + 0.5 penalty), got {beta_w}"
    );
}

// ── Test A3b: Non-bisimilar categories → no weight discount ─────────────

#[test]
fn test_non_bisimilar_categories_no_weight_discount() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    // Alpha and Beta are explicitly non-bisimilar → no penalty.
    let alt = crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: vec![("Alpha".into(), "Beta".into())],
        state_count: 2,
    };
    let mut bundle = empty_bundle();
    bundle.alternating = Some(&alt);

    let mut wfst_alpha = PredictionWfst {
        category: "Alpha".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "r_alpha".into(),
                parse_fn: "parse_r_alpha".into(),
            },
            weight: TropicalWeight::new(2.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    wfst_alpha.states[0].is_final = true;

    let mut wfst_beta = PredictionWfst {
        category: "Beta".into(),
        states: vec![WfstState::new(0)],
        start: 0,
        actions: vec![WeightedAction {
            action: DispatchAction::Direct {
                rule_label: "r_beta".into(),
                parse_fn: "parse_r_beta".into(),
            },
            weight: TropicalWeight::new(3.0),
        }],
        token_map: TokenIdMap::new(),
        beam_width: None,
        context_labels: HashMap::new(),
    };
    wfst_beta.states[0].is_final = true;

    let mut prediction_wfsts = HashMap::new();
    prediction_wfsts.insert("Alpha".into(), wfst_alpha);
    prediction_wfsts.insert("Beta".into(), wfst_beta);

    let categories = vec![category("Alpha", true), category("Beta", false)];
    let rule_infos = vec![rule("r_alpha", "Alpha"), rule("r_beta", "Beta")];
    let dead_rules = HashSet::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Both weights should remain unchanged (no bisimilar pair found).
    let alpha_w = analysis
        .constructor_weights
        .get("r_alpha")
        .copied()
        .expect("r_alpha should have a constructor weight");
    assert!(
        (alpha_w - 2.0).abs() < 1e-9,
        "Alpha's weight should remain 2.0 (non-bisimilar), got {alpha_w}"
    );

    let beta_w = analysis
        .constructor_weights
        .get("r_beta")
        .copied()
        .expect("r_beta should have a constructor weight");
    assert!(
        (beta_w - 3.0).abs() < 1e-9,
        "Beta's weight should remain 3.0 (non-bisimilar), got {beta_w}"
    );
}

// ── Test A3c: Three categories, partial bisimilarity → selective discount ─

#[test]
fn test_bisimilar_partial_three_categories() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WfstState};

    // Three categories: A, B, C.
    // A-B and A-C are bisimilar, but B-C is non-bisimilar.
    // Deprioritized: B (B > A), C (C > A). B-C non-bisimilar doesn't matter
    // because the penalty is based on *any* bisimilar pair.
    let alt = crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: vec![("B".into(), "C".into())],
        state_count: 3,
    };
    let mut bundle = empty_bundle();
    bundle.alternating = Some(&alt);

    let make_wfst = |cat: &str, rl: &str| {
        let mut w = PredictionWfst {
            category: cat.into(),
            states: vec![WfstState::new(0)],
            start: 0,
            actions: vec![WeightedAction {
                action: DispatchAction::Direct {
                    rule_label: rl.into(),
                    parse_fn: format!("parse_{rl}"),
                },
                weight: TropicalWeight::new(1.0),
            }],
            token_map: TokenIdMap::new(),
            beam_width: None,
            context_labels: HashMap::new(),
        };
        w.states[0].is_final = true;
        w
    };

    let mut prediction_wfsts = HashMap::new();
    prediction_wfsts.insert("A".into(), make_wfst("A", "rA"));
    prediction_wfsts.insert("B".into(), make_wfst("B", "rB"));
    prediction_wfsts.insert("C".into(), make_wfst("C", "rC"));

    let categories = vec![category("A", true), category("B", false), category("C", false)];
    let rule_infos = vec![rule("rA", "A"), rule("rB", "B"), rule("rC", "C")];
    let dead_rules = HashSet::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // A should keep original weight (always the lexicographically first in its pairs).
    let wa = analysis
        .constructor_weights
        .get("rA")
        .copied()
        .expect("rA should have a constructor weight");
    assert!((wa - 1.0).abs() < 1e-9, "A's weight should remain 1.0, got {wa}");

    // B should be penalized (B > A and they are bisimilar).
    let wb = analysis
        .constructor_weights
        .get("rB")
        .copied()
        .expect("rB should have a constructor weight");
    assert!(
        (wb - 1.5).abs() < 1e-9,
        "B's weight should be 1.5 (penalized via A-B bisimilarity), got {wb}"
    );

    // C should be penalized (C > A and they are bisimilar).
    let wc = analysis
        .constructor_weights
        .get("rC")
        .copied()
        .expect("rC should have a constructor weight");
    assert!(
        (wc - 1.5).abs() < 1e-9,
        "C's weight should be 1.5 (penalized via A-C bisimilarity), got {wc}"
    );
}

// ── Test 9: RA01-SKIP — dead registers populate dead_binder_categories ──

#[test]
fn test_register_dead_binders_populated() {
    let reg = crate::register_automata::RegisterAnalysis {
        num_states: 3,
        num_registers: 3,
        dead_registers: vec![0, 2],
        unbound_references: Vec::new(),
    };
    let mut bundle = empty_bundle();
    bundle.register = Some(&reg);

    let categories =
        vec![category("Alpha", true), category("Beta", false), category("Gamma", false)];
    let rule_infos = vec![rule("r1", "Alpha"), rule("r2", "Beta"), rule("r3", "Gamma")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Register index 0 → "Alpha", index 2 → "Gamma"
    assert!(
        analysis.dead_binder_categories.contains("Alpha"),
        "Alpha (register 0) should be in dead_binder_categories"
    );
    assert!(
        analysis.dead_binder_categories.contains("Gamma"),
        "Gamma (register 2) should be in dead_binder_categories"
    );
    assert!(
        !analysis.dead_binder_categories.contains("Beta"),
        "Beta (register 1) should NOT be in dead_binder_categories"
    );
}

// ── Test 10: RA01-SKIP — out-of-bounds register index is safely skipped ─

#[test]
fn test_register_out_of_bounds_skipped() {
    let reg = crate::register_automata::RegisterAnalysis {
        num_states: 3,
        num_registers: 3,
        dead_registers: vec![99], // out of bounds
        unbound_references: Vec::new(),
    };
    let mut bundle = empty_bundle();
    bundle.register = Some(&reg);

    let categories = vec![category("A", true), category("B", false), category("C", false)];
    let rule_infos = vec![rule("r1", "A"), rule("r2", "B"), rule("r3", "C")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.dead_binder_categories.is_empty(),
        "dead_binder_categories should be empty for out-of-bounds register index"
    );
}

// ── Test 11: V05-INFO — VPA determinizable + no mismatches → true ───────

#[test]
fn test_vpa_bracket_deterministic_true() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: Vec::new(),
        state_count: 5,
        max_nesting_bound: 5,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.bracket_deterministic,
        "bracket_deterministic should be true when is_determinizable and no mismatches"
    );
}

// ── Test 12: V05-INFO — VPA not determinizable → false ──────────────────

#[test]
fn test_vpa_bracket_not_deterministic() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: false,
        alphabet_mismatches: Vec::new(),
        state_count: 3,
        max_nesting_bound: 3,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        !analysis.bracket_deterministic,
        "bracket_deterministic should be false when not determinizable"
    );
}

// ── Test 13: V05-INFO — mismatches force non-deterministic ──────────────

#[test]
fn test_vpa_mismatches_not_deterministic() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: vec!["(".into()],
        state_count: 3,
        max_nesting_bound: 3,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        !analysis.bracket_deterministic,
        "bracket_deterministic should be false when alphabet_mismatches is non-empty"
    );
}

// ── Test A1: VPA nesting bound wired into PipelineAnalysis ──────────────

#[test]
fn test_vpa_nesting_bound_wired() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: Vec::new(),
        state_count: 7,
        max_nesting_bound: 7,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert_eq!(
        analysis.vpa_max_nesting_bound,
        Some(7),
        "vpa_max_nesting_bound should be Some(7) when VPA analysis is present"
    );
}

#[test]
fn test_vpa_nesting_bound_none_without_vpa() {
    let bundle = empty_bundle();
    // No VPA analysis → vpa_max_nesting_bound should be None

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert_eq!(
        analysis.vpa_max_nesting_bound, None,
        "vpa_max_nesting_bound should be None when no VPA analysis is available"
    );
}

// ── Test A2a: VPA bracket mismatch tokens wired into PipelineAnalysis ──

#[test]
fn test_vpa_bracket_mismatch_tokens_populated() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: vec!["|".into(), "`".into()],
        state_count: 4,
        max_nesting_bound: 4,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.bracket_mismatch_tokens.contains("|"),
        "bracket_mismatch_tokens should contain '|'"
    );
    assert!(
        analysis.bracket_mismatch_tokens.contains("`"),
        "bracket_mismatch_tokens should contain '`'"
    );
    assert_eq!(
        analysis.bracket_mismatch_tokens.len(),
        2,
        "bracket_mismatch_tokens should have exactly 2 entries"
    );
}

#[test]
fn test_vpa_bracket_mismatch_empty_when_no_mismatches() {
    let vpa = crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: Vec::new(),
        state_count: 3,
        max_nesting_bound: 3,
    };
    let mut bundle = empty_bundle();
    bundle.vpa = Some(&vpa);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.bracket_mismatch_tokens.is_empty(),
        "bracket_mismatch_tokens should be empty when no VPA mismatches"
    );
}

#[test]
fn test_vpa_bracket_mismatch_empty_when_no_vpa() {
    let bundle = empty_bundle();
    // No VPA analysis → bracket_mismatch_tokens should be empty

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("r1", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.bracket_mismatch_tokens.is_empty(),
        "bracket_mismatch_tokens should be empty when no VPA analysis"
    );
}

// ── Test 14: MT01-INFO — disconnected tapes → independent categories ────

#[test]
fn test_multi_tape_disconnected_mapped() {
    let mt = crate::multi_tape::MultiTapeAnalysis {
        num_states: 3,
        num_tapes: 3,
        disconnected_tapes: vec![1],
        overlapping_tapes: Vec::new(),
    };
    let mut bundle = empty_bundle();
    bundle.multi_tape = Some(&mt);

    let categories = vec![category("Proc", true), category("Int", false), category("Bool", false)];
    let rule_infos = vec![rule("r1", "Proc"), rule("r2", "Int"), rule("r3", "Bool")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    // Tape index 1 → "Int"
    assert!(
        analysis.independent_categories.contains("Int"),
        "Int (tape 1) should be in independent_categories"
    );
    assert_eq!(
        analysis.independent_categories.len(),
        1,
        "only 1 independent category expected, got {:?}",
        analysis.independent_categories
    );
}

// ── Test 15: MT01-INFO — out-of-bounds tape index is safely skipped ─────

#[test]
fn test_multi_tape_out_of_bounds_skipped() {
    let mt = crate::multi_tape::MultiTapeAnalysis {
        num_states: 3,
        num_tapes: 3,
        disconnected_tapes: vec![99], // out of bounds
        overlapping_tapes: Vec::new(),
    };
    let mut bundle = empty_bundle();
    bundle.multi_tape = Some(&mt);

    let categories = vec![category("Proc", true), category("Int", false), category("Bool", false)];
    let rule_infos = vec![rule("r1", "Proc"), rule("r2", "Int"), rule("r3", "Bool")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.independent_categories.is_empty(),
        "independent_categories should be empty for out-of-bounds tape index"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint C1: Guard-disambiguated tokens from symbolic subsumption
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn guard_disambiguated_tokens_from_subsumption() {
    let sym = crate::symbolic::SymbolicAnalysis {
        num_states: 1,
        num_transitions: 2,
        guard_satisfiability: vec![("Expr::A".to_string(), true), ("Expr::B".to_string(), true)],
        overlapping_guards: vec![],
        subsumed_guards: vec![("Expr::A".to_string(), "Expr::B".to_string())],
        unsatisfiable_rule_labels: vec![],
    };

    let mut bundle = empty_bundle();
    bundle.symbolic = Some(&sym);

    let categories = vec![category("Expr", true)];
    let rule_infos = vec![rule("A", "Expr")];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        !analysis.guard_disambiguated_tokens.is_empty(),
        "subsumed guards should produce disambiguated tokens"
    );
    assert!(
        analysis.guard_disambiguated_tokens.contains("Expr::A"),
        "subsumed guard 'Expr::A' should be in disambiguated set"
    );
}

#[test]
fn no_subsumption_no_disambiguated_tokens() {
    let sym = crate::symbolic::SymbolicAnalysis {
        num_states: 1,
        num_transitions: 0,
        guard_satisfiability: vec![],
        overlapping_guards: vec![],
        subsumed_guards: vec![],
        unsatisfiable_rule_labels: vec![],
    };

    let mut bundle = empty_bundle();
    bundle.symbolic = Some(&sym);

    let categories = vec![category("Expr", true)];
    let rule_infos: Vec<RuleInfo> = vec![];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.guard_disambiguated_tokens.is_empty(),
        "no subsumption should produce empty disambiguated set"
    );
}

#[test]
fn empty_symbolic_analysis_no_disambiguated_tokens() {
    let bundle = empty_bundle();

    let categories = vec![category("Expr", true)];
    let rule_infos: Vec<RuleInfo> = vec![];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.guard_disambiguated_tokens.is_empty(),
        "no symbolic analysis should produce empty disambiguated set"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint C3: Per-category entropy from probabilistic analysis
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn per_category_entropy_two_rules() {
    let mut rule_selectivities = HashMap::new();
    rule_selectivities.insert("Expr::A".to_string(), 0.7);
    rule_selectivities.insert("Expr::B".to_string(), 0.3);

    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 1,
        is_normalized: true,
        total_selectivity: 1.0,
        mean_entropy: 0.6,
        low_selectivity_rules: vec![],
        rule_selectivities,
    };

    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true)];
    let rule_infos: Vec<RuleInfo> = vec![];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.per_category_entropy.contains_key("Expr"),
        "should have entropy for Expr"
    );
    let e = analysis.per_category_entropy["Expr"];
    assert!(e > 0.0, "two rules with different weights should have positive entropy");
}

#[test]
fn per_category_entropy_no_analysis() {
    let bundle = empty_bundle();

    let categories = vec![category("Expr", true)];
    let rule_infos: Vec<RuleInfo> = vec![];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert!(
        analysis.per_category_entropy.is_empty(),
        "no probabilistic analysis should produce empty entropy"
    );
}

#[test]
fn per_category_entropy_multiple_categories() {
    let mut rule_selectivities = HashMap::new();
    // Expr has 2 rules with uniform distribution
    rule_selectivities.insert("Expr::A".to_string(), 0.5);
    rule_selectivities.insert("Expr::B".to_string(), 0.5);
    // Stmt has 1 rule → entropy = 0
    rule_selectivities.insert("Stmt::X".to_string(), 1.0);

    let prob = crate::probabilistic::ProbabilisticAnalysis {
        num_states: 2,
        is_normalized: true,
        total_selectivity: 2.0,
        mean_entropy: 0.3,
        low_selectivity_rules: vec![],
        rule_selectivities,
    };

    let mut bundle = empty_bundle();
    bundle.probabilistic = Some(&prob);

    let categories = vec![category("Expr", true), category("Stmt", false)];
    let rule_infos: Vec<RuleInfo> = vec![];
    let dead_rules = HashSet::new();
    let prediction_wfsts = HashMap::new();

    let analysis =
        run_build_pipeline(&dead_rules, &prediction_wfsts, &categories, &rule_infos, &bundle);

    assert_eq!(analysis.per_category_entropy.len(), 2);
    // Uniform distribution has max entropy: ln(2) ≈ 0.693
    let expr_entropy = analysis.per_category_entropy["Expr"];
    assert!(
        (expr_entropy - 2.0_f64.ln()).abs() < 0.01,
        "uniform 2-rule entropy should be ln(2), got {expr_entropy}"
    );
    // Single rule has zero entropy
    let stmt_entropy = analysis.per_category_entropy["Stmt"];
    assert!(
        stmt_entropy.abs() < 0.01,
        "single-rule entropy should be ~0, got {stmt_entropy}"
    );
}
