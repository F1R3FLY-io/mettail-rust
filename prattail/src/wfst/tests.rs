use super::*;

#[test]
fn test_prediction_wfst_builder_basic() {
    let token_map =
        TokenIdMap::from_names(vec!["Plus", "Minus", "Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);

    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );

    let wfst = builder.build();

    assert_eq!(wfst.num_actions(), 3);
    assert_eq!(wfst.num_states(), 4); // start + 3 final states
    assert_eq!(wfst.category, "Expr");
}

#[test]
fn test_prediction_wfst_predict_deterministic() {
    let token_map = TokenIdMap::from_names(vec!["Plus", "Minus"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();

    // Plus → exactly one result (Direct Add)
    let results = wfst.predict("Plus");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].weight, TropicalWeight::new(0.0));
    assert!(
        matches!(&results[0].action, DispatchAction::Direct { rule_label, .. } if rule_label == "Add")
    );

    // Unknown token → empty
    let results = wfst.predict("Star");
    assert!(results.is_empty());
}

#[test]
fn test_prediction_wfst_predict_ambiguous_ordered_by_weight() {
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);

    // Same token, two actions, different weights
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0), // higher weight = less preferred
    );
    builder.add_action(
        "Ident",
        DispatchAction::CrossCategory {
            source_category: "Name".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: true,
        },
        TropicalWeight::new(0.5), // lower weight = preferred
    );

    let wfst = builder.build();

    let results = wfst.predict("Ident");
    assert_eq!(results.len(), 2);
    // First result should be the lower-weight (preferred) one
    assert_eq!(results[0].weight, TropicalWeight::new(0.5));
    assert!(matches!(&results[0].action, DispatchAction::CrossCategory { .. }));
    assert_eq!(results[1].weight, TropicalWeight::new(2.0));
    assert!(matches!(&results[1].action, DispatchAction::Variable { .. }));
}

#[test]
fn test_confidence_gap_ambiguous() {
    // A5: Test confidence_gap with two alternatives of different weight
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::CrossCategory {
            source_category: "Name".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: true,
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();

    // confidence_gap = second_best - best = 2.0 - 0.5 = 1.5
    let gap = wfst.confidence_gap("Ident");
    assert!((gap - 1.5).abs() < 1e-9, "confidence gap should be 1.5, got {}", gap);
}

#[test]
fn test_confidence_gap_single_alternative() {
    // A5: Single alternative → infinite confidence
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "VarRef".to_string(),
            parse_fn: "parse_varref".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();
    assert_eq!(wfst.confidence_gap("Ident"), f64::INFINITY);
}

#[test]
fn test_confidence_gap_unknown_token() {
    // A5: Unknown token → infinite confidence (no alternatives)
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
    let builder = PredictionWfstBuilder::new("Expr", token_map);
    let wfst = builder.build();
    assert_eq!(wfst.confidence_gap("Plus"), f64::INFINITY);
}

#[test]
fn test_confidence_gap_equal_weights() {
    // A5: Equal weights → zero gap (fully ambiguous)
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(0.5),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "VarRef".to_string(),
            parse_fn: "parse_varref".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();
    assert!(
        (wfst.confidence_gap("Ident")).abs() < 1e-9,
        "equal weights should produce zero gap"
    );
}

#[test]
fn test_compute_action_weight() {
    let first_sets = HashMap::new();
    let overlaps = HashMap::new();

    // Direct → 0.0
    let w = super::compute_action_weight(
        "Plus",
        &DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        "Expr",
        &first_sets,
        &overlaps,
        0,
    );
    assert_eq!(w, TropicalWeight::new(0.0));

    // Variable → 2.0
    let w = super::compute_action_weight(
        "Ident",
        &DispatchAction::Variable { category: "Expr".to_string() },
        "Expr",
        &first_sets,
        &overlaps,
        0,
    );
    assert_eq!(w, TropicalWeight::new(2.0));

    // CrossCategory with backtrack → 0.5
    let w = super::compute_action_weight(
        "Ident",
        &DispatchAction::CrossCategory {
            source_category: "Int".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: true,
        },
        "Bool",
        &first_sets,
        &overlaps,
        0,
    );
    assert_eq!(w, TropicalWeight::new(0.5));

    // CrossCategory without backtrack → 0.0
    let w = super::compute_action_weight(
        "Integer",
        &DispatchAction::CrossCategory {
            source_category: "Int".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: false,
        },
        "Bool",
        &first_sets,
        &overlaps,
        0,
    );
    assert_eq!(w, TropicalWeight::new(0.0));

    // Grouping → 0.0
    let w = super::compute_action_weight(
        "LParen",
        &DispatchAction::Grouping {
            open: "(".to_string(),
            close: ")".to_string(),
        },
        "Expr",
        &first_sets,
        &overlaps,
        0,
    );
    assert_eq!(w, TropicalWeight::new(0.0));
}

#[test]
fn test_generate_weighted_dispatch_empty() {
    let token_map = TokenIdMap::new();
    let wfst = PredictionWfstBuilder::new("Expr", token_map).build();
    assert!(generate_weighted_dispatch(&wfst, "Expr").is_none());
}

#[test]
fn test_generate_weighted_dispatch_produces_comments() {
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "Var".to_string(),
            parse_fn: "parse_var".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();
    let code = generate_weighted_dispatch(&wfst, "Expr").expect("should produce code");
    assert!(code.contains("WFST prediction for Expr"));
    assert!(code.contains("ambiguous"));
}

// ── Beam pruning tests ────────────────────────────────────────────────

#[test]
fn test_beam_pruning_none_is_identity() {
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "Var".to_string(),
            parse_fn: "parse_var".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();
    // No beam → predict_pruned == predict
    let all = wfst.predict("Ident");
    let pruned = wfst.predict_pruned("Ident");
    assert_eq!(all.len(), pruned.len());
}

#[test]
fn test_beam_pruning_filters_high_weight() {
    let token_map = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "Var".to_string(),
            parse_fn: "parse_var".to_string(),
        },
        TropicalWeight::new(0.0), // best
    );
    builder.add_action(
        "Ident",
        DispatchAction::Cast {
            source_category: "Int".to_string(),
            wrapper_label: "IntToExpr".to_string(),
        },
        TropicalWeight::new(0.5), // within beam
    );
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(5.0), // beyond beam
    );

    let mut wfst = builder.build();
    wfst.set_beam_width(Some(TropicalWeight::new(1.0)));

    let pruned = wfst.predict_pruned("Ident");
    // beam=1.0, best=0.0, threshold=1.0: only 0.0 and 0.5 pass
    assert_eq!(pruned.len(), 2);
    assert_eq!(pruned[0].weight, TropicalWeight::new(0.0));
    assert_eq!(pruned[1].weight, TropicalWeight::new(0.5));
}

#[test]
fn test_beam_pruning_preserves_best() {
    let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(3.0),
    );

    let mut wfst = builder.build();
    wfst.set_beam_width(Some(TropicalWeight::new(0.1)));

    let pruned = wfst.predict_pruned("Plus");
    assert_eq!(pruned.len(), 1, "best action must never be pruned");
}

#[test]
fn test_beam_width_from_builder() {
    let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));

    let builder =
        PredictionWfstBuilder::new("Expr", token_map).with_beam_width(TropicalWeight::new(2.0));

    let wfst = builder.build();
    assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(2.0)));
}

// ── from_flat() / CSR deserialization tests ────────────────────────

#[test]
fn test_from_flat_roundtrip() {
    // Build a WFST via the builder, then verify from_flat() reconstructs
    // equivalent structure from the CSR representation.
    let token_map =
        TokenIdMap::from_names(vec!["Plus", "Minus", "Ident"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(1.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );

    let original = builder.build();

    // Flatten into CSR format (mirroring what emit_prediction_wfst_static does)
    let mut transitions_flat: Vec<(u16, u32, f64)> = Vec::new();
    let mut state_offsets: Vec<(usize, usize, bool, f64)> = Vec::new();
    for state in &original.states {
        let start = transitions_flat.len();
        let count = state.transitions.len();
        for t in &state.transitions {
            transitions_flat.push((t.input, t.to, t.weight.value()));
        }
        state_offsets.push((start, count, state.is_final, state.final_weight.value()));
    }

    let mut token_names: Vec<String> = Vec::new();
    for i in 0..original.token_map.len() {
        if let Some(name) = original.token_map.name(i as u16) {
            token_names.push(name.to_string());
        }
    }
    let token_name_refs: Vec<&str> = token_names.iter().map(|s| s.as_str()).collect();

    // Reconstruct from flat
    let reconstructed = PredictionWfst::from_flat(
        "Expr",
        &state_offsets,
        &transitions_flat,
        &token_name_refs,
        None,
    );

    // Verify structural equivalence
    assert_eq!(reconstructed.category, "Expr");
    assert_eq!(reconstructed.num_states(), original.num_states());
    assert_eq!(reconstructed.start, original.start);
    assert_eq!(reconstructed.beam_width, None);

    // Verify prediction still works (weights are preserved)
    let plus_results = reconstructed.predict("Plus");
    assert_eq!(plus_results.len(), 1);
    assert_eq!(plus_results[0].weight, TropicalWeight::new(0.0));

    let ident_results = reconstructed.predict("Ident");
    assert_eq!(ident_results.len(), 1);
    assert_eq!(ident_results[0].weight, TropicalWeight::new(2.0));
}

#[test]
fn test_from_flat_with_beam_width() {
    let state_offsets: &[(usize, usize, bool, f64)] = &[
        (0, 1, false, f64::INFINITY), // start state
        (1, 0, true, 0.0),            // final state
    ];
    let transitions: &[(u16, u32, f64)] = &[
        (0, 1, 0.5), // token 0 → state 1, weight 0.5
    ];
    let token_names: &[&str] = &["Plus"];

    let wfst = PredictionWfst::from_flat("Cat", state_offsets, transitions, token_names, Some(1.5));
    assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(1.5)));
    assert_eq!(wfst.num_states(), 2);
    assert_eq!(wfst.num_actions(), 1);
}

#[test]
fn test_from_flat_empty() {
    let wfst = PredictionWfst::from_flat("Empty", &[], &[], &[], None);
    assert_eq!(wfst.num_states(), 0);
    assert_eq!(wfst.num_actions(), 0);
    assert!(wfst.predict("Plus").is_empty());
}

// Stage 10.8 (2026-05-05): with_trained_weights tests DELETED. The method
// they exercised was removed alongside SpilloverTrainer (input signal source
// gone post-Stage-10.6 NFA spillover excision).

#[test]
fn test_beam_width_from_language_spec() {
    use crate::binding_power::Associativity;
    use crate::{BeamWidthConfig, CategorySpec, LanguageSpec, RuleSpecInput, SyntaxItemSpec};

    // Create a minimal LanguageSpec with beam_width set
    let spec = LanguageSpec::with_options(
        "TestLang".to_string(),
        vec![CategorySpec {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        }],
        vec![RuleSpecInput {
            label: "Lit".to_string(),
            category: "Expr".to_string(),
            syntax: vec![SyntaxItemSpec::Terminal("0".to_string())],
            associativity: Associativity::Left,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        }],
        BeamWidthConfig::Explicit(1.5),    // beam_width
        None,                              // log_semiring_model_path
        crate::LiteralPatterns::default(), // literal_patterns
    );

    assert_eq!(spec.beam_width, BeamWidthConfig::Explicit(1.5));
    assert!(spec.log_semiring_model_path.is_none());

    // Verify beam_width can be converted to TropicalWeight for WFST construction
    let beam = spec.beam_width.to_option().map(TropicalWeight::new);
    assert_eq!(beam, Some(TropicalWeight::new(1.5)));
}

// ── union() tests ─────────────────────────────────────────────────

#[test]
fn test_union_disjoint_tokens() {
    // WFST A: Plus → Add
    let token_map_a = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
    let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
    builder_a.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let mut wfst_a = builder_a.build();

    // WFST B: Minus → Sub
    let token_map_b = TokenIdMap::from_names(vec!["Minus"].into_iter().map(String::from));
    let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
    builder_b.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst_b = builder_b.build();

    assert_eq!(wfst_a.num_actions(), 1);
    assert_eq!(wfst_a.num_states(), 2);

    wfst_a.union(&wfst_b);

    // After union: should have both actions
    assert_eq!(wfst_a.num_actions(), 2);
    assert_eq!(wfst_a.num_states(), 3); // start + 2 final states

    // Both tokens should be predictable
    let plus_results = wfst_a.predict("Plus");
    assert_eq!(plus_results.len(), 1);
    assert_eq!(plus_results[0].weight, TropicalWeight::new(0.0));

    let minus_results = wfst_a.predict("Minus");
    assert_eq!(minus_results.len(), 1);
    assert_eq!(minus_results[0].weight, TropicalWeight::new(0.0));
}

#[test]
fn test_union_overlapping_tokens() {
    // WFST A: Ident → Variable (w=2.0)
    let token_map_a = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
    let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
    builder_a.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );
    let mut wfst_a = builder_a.build();

    // WFST B: Ident → CrossCategory (w=0.5)
    let token_map_b = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
    let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
    builder_b.add_action(
        "Ident",
        DispatchAction::CrossCategory {
            source_category: "Name".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: true,
        },
        TropicalWeight::new(0.5),
    );
    let wfst_b = builder_b.build();

    wfst_a.union(&wfst_b);

    // After union: Ident should have two alternatives, sorted by weight
    let results = wfst_a.predict("Ident");
    assert_eq!(results.len(), 2);
    // Lower weight first (0.5 < 2.0)
    assert_eq!(results[0].weight, TropicalWeight::new(0.5));
    assert!(matches!(&results[0].action, DispatchAction::CrossCategory { .. }));
    assert_eq!(results[1].weight, TropicalWeight::new(2.0));
    assert!(matches!(&results[1].action, DispatchAction::Variable { .. }));
}

#[test]
fn test_union_preserves_beam_width() {
    let token_map_a = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
    let builder_a =
        PredictionWfstBuilder::new("Expr", token_map_a).with_beam_width(TropicalWeight::new(1.5));
    let mut wfst_a = builder_a.build();

    let token_map_b = TokenIdMap::from_names(vec!["Minus"].into_iter().map(String::from));
    let builder_b =
        PredictionWfstBuilder::new("Expr", token_map_b).with_beam_width(TropicalWeight::new(2.0));
    let wfst_b = builder_b.build();

    wfst_a.union(&wfst_b);

    // Self's beam width is preserved
    assert_eq!(wfst_a.beam_width(), Some(TropicalWeight::new(1.5)));
}

#[test]
fn test_union_empty_other() {
    let token_map = TokenIdMap::from_names(vec!["Plus"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let mut wfst = builder.build();

    let empty_map = TokenIdMap::new();
    let empty_wfst = PredictionWfstBuilder::new("Expr", empty_map).build();

    let original_actions = wfst.num_actions();
    let original_states = wfst.num_states();

    wfst.union(&empty_wfst);

    // No change
    assert_eq!(wfst.num_actions(), original_actions);
    assert_eq!(wfst.num_states(), original_states);
}

// ── B3: minimize() tests ──────────────────────────────────────────

#[test]
fn test_minimize_merges_all_simple_finals() {
    // In the two-state architecture, transition weights live on edges from
    // start, not on final states. All final states have identical properties
    // (is_final=true, final_weight=0.0, no outgoing transitions), so they
    // all share the same signature and merge into one.
    let token_map =
        TokenIdMap::from_names(vec!["Plus", "Minus", "Star"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(1.0),
    );
    builder.add_action(
        "Star",
        DispatchAction::Direct {
            rule_label: "Mul".to_string(),
            parse_fn: "parse_mul".to_string(),
        },
        TropicalWeight::new(2.0),
    );

    let mut wfst = builder.build();
    assert_eq!(wfst.num_states(), 4); // start + 3 finals

    let removed = wfst.minimize();
    // All 3 finals have identical signatures → merge to 1
    assert_eq!(removed, 2);
    assert_eq!(wfst.num_states(), 2); // start + 1 merged final

    // Prediction still works — transition weights preserved
    assert_eq!(wfst.predict("Plus").len(), 1);
    assert_eq!(wfst.predict("Plus")[0].weight, TropicalWeight::new(0.0));
    assert_eq!(wfst.predict("Minus").len(), 1);
    assert_eq!(wfst.predict("Minus")[0].weight, TropicalWeight::new(1.0));
    assert_eq!(wfst.predict("Star").len(), 1);
    assert_eq!(wfst.predict("Star")[0].weight, TropicalWeight::new(2.0));
}

#[test]
fn test_minimize_merges_identical_finals_after_union() {
    // Two WFSTs with different tokens but same final-state properties.
    // After union, the final states are duplicated. They have different
    // action_idx values, so their signatures differ. However, if we
    // construct a scenario with truly identical signatures (same action_idx,
    // same target, same weight), they should merge.

    // Build a WFST with two disjoint tokens
    let token_map = TokenIdMap::from_names(vec!["Plus", "Minus"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Minus",
        DispatchAction::Direct {
            rule_label: "Sub".to_string(),
            parse_fn: "parse_sub".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let mut wfst = builder.build();

    // Before minimize: start + 2 final states (action_idx 0 and 1)
    assert_eq!(wfst.num_states(), 3);

    // The final states have the same (is_final, final_weight) but different
    // action_idx in their parent's transitions. The final states themselves
    // have no outgoing transitions, so their own signatures are:
    //   state 1: (true, 0.0_bits, [])
    //   state 2: (true, 0.0_bits, [])
    // These ARE identical → they should merge.
    let removed = wfst.minimize();
    assert_eq!(removed, 1, "one duplicate final state should be removed");
    assert_eq!(wfst.num_states(), 2); // start + 1 merged final

    // Prediction still works — both tokens point to the same final state
    let plus = wfst.predict("Plus");
    assert_eq!(plus.len(), 1);
    assert_eq!(plus[0].weight, TropicalWeight::new(0.0));

    let minus = wfst.predict("Minus");
    assert_eq!(minus.len(), 1);
    assert_eq!(minus[0].weight, TropicalWeight::new(0.0));
}

#[test]
fn test_minimize_after_union_with_overlapping_tokens() {
    // Union creates additional final states; minimize should merge equivalent ones
    let token_map_a = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
    let mut builder_a = PredictionWfstBuilder::new("Expr", token_map_a);
    builder_a.add_action(
        "Ident",
        DispatchAction::Variable { category: "Expr".to_string() },
        TropicalWeight::new(2.0),
    );
    let mut wfst = builder_a.build();
    assert_eq!(wfst.num_states(), 2); // start + 1 final

    // Union with another WFST that also maps Ident
    let token_map_b = TokenIdMap::from_names(vec!["Ident"].into_iter().map(String::from));
    let mut builder_b = PredictionWfstBuilder::new("Expr", token_map_b);
    builder_b.add_action(
        "Ident",
        DispatchAction::CrossCategory {
            source_category: "Name".to_string(),
            operator_token: "EqEq".to_string(),
            rule_label: "Eq".to_string(),
            needs_backtrack: true,
        },
        TropicalWeight::new(0.5),
    );
    let wfst_b = builder_b.build();
    wfst.union(&wfst_b);

    // After union: start + 2 final states (different weights: 2.0 and 0.5)
    assert_eq!(wfst.num_states(), 3);

    // Final state weights differ (one has final_weight from TropicalWeight::one()
    // which is 0.0, so they may actually share the same signature).
    // Both final states: is_final=true, final_weight=TropicalWeight::one()=0.0,
    // no outgoing transitions → identical signatures → merge to 1.
    let removed = wfst.minimize();
    assert_eq!(removed, 1);
    assert_eq!(wfst.num_states(), 2);

    // Prediction preserves both alternatives for Ident
    let results = wfst.predict("Ident");
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].weight, TropicalWeight::new(0.5));
    assert_eq!(results[1].weight, TropicalWeight::new(2.0));
}

#[test]
fn test_minimize_empty_wfst() {
    let token_map = TokenIdMap::new();
    let mut wfst = PredictionWfstBuilder::new("Empty", token_map).build();
    // Single start state, no finals
    let removed = wfst.minimize();
    assert_eq!(removed, 0);
}

#[test]
fn test_minimize_single_state() {
    // A WFST with only a start state and no actions
    let token_map = TokenIdMap::new();
    let mut wfst = PredictionWfstBuilder::new("Lone", token_map).build();
    assert_eq!(wfst.num_states(), 1);
    let removed = wfst.minimize();
    assert_eq!(removed, 0);
    assert_eq!(wfst.num_states(), 1);
}

#[test]
fn test_minimize_preserves_beam_width() {
    let token_map = TokenIdMap::from_names(vec!["A", "B"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Cat", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "B",
        DispatchAction::Direct {
            rule_label: "R2".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let mut wfst = builder.with_beam_width(TropicalWeight::new(1.5)).build();

    wfst.minimize();
    assert_eq!(wfst.beam_width(), Some(TropicalWeight::new(1.5)));
}

#[test]
fn test_minimize_large_union_many_duplicates() {
    // Simulate a larger scenario: 10 tokens all leading to final states
    // with the same weight — all 10 finals should merge to 1.
    let names: Vec<String> = (0..10).map(|i| format!("T{}", i)).collect();
    let token_map = TokenIdMap::from_names(names.iter().cloned());
    let mut builder = PredictionWfstBuilder::new("Big", token_map);

    for name in &names {
        builder.add_action(
            name,
            DispatchAction::Direct {
                rule_label: format!("R_{}", name),
                parse_fn: format!("p_{}", name.to_lowercase()),
            },
            TropicalWeight::new(0.0),
        );
    }

    let mut wfst = builder.build();
    assert_eq!(wfst.num_states(), 11); // start + 10 finals

    let removed = wfst.minimize();
    // All 10 finals have identical signatures → merge to 1
    assert_eq!(removed, 9);
    assert_eq!(wfst.num_states(), 2); // start + 1 merged final

    // All 10 tokens still predict correctly
    for name in &names {
        let results = wfst.predict(name);
        assert_eq!(results.len(), 1, "token {} should still predict", name);
        assert_eq!(results[0].weight, TropicalWeight::new(0.0));
    }
}

#[test]
fn test_minimize_mixed_weights_partial_merge() {
    // 4 tokens: 2 with weight 0.0, 2 with weight 1.0
    // Should merge to 2 final states
    let token_map = TokenIdMap::from_names(vec!["A", "B", "C", "D"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Mix", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "B",
        DispatchAction::Direct {
            rule_label: "R2".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(1.0),
    );
    builder.add_action(
        "C",
        DispatchAction::Direct {
            rule_label: "R3".to_string(),
            parse_fn: "p3".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "D",
        DispatchAction::Direct {
            rule_label: "R4".to_string(),
            parse_fn: "p4".to_string(),
        },
        TropicalWeight::new(1.0),
    );

    let mut wfst = builder.build();
    assert_eq!(wfst.num_states(), 5); // start + 4 finals

    let removed = wfst.minimize();
    // Finals: 2 groups (weight 0.0 and weight 1.0)
    // Wait — final_weight is TropicalWeight::one() (= 0.0) for all finals,
    // since the weight is on the *transition*, not the final state.
    // So all 4 finals have identical signatures → merge to 1
    assert_eq!(removed, 3);
    assert_eq!(wfst.num_states(), 2);

    // All tokens still work
    assert_eq!(wfst.predict("A")[0].weight, TropicalWeight::new(0.0));
    assert_eq!(wfst.predict("B")[0].weight, TropicalWeight::new(1.0));
    assert_eq!(wfst.predict("C")[0].weight, TropicalWeight::new(0.0));
    assert_eq!(wfst.predict("D")[0].weight, TropicalWeight::new(1.0));
}

// ── C1: WeightCorrection tests ──

#[test]
fn test_c1_weight_correction_delta_positive() {
    // C1: When a higher-weight (worse predicted rank) alternative is selected,
    // the delta should be positive.
    let c = WeightCorrection {
        category: "TestGrammar",
        primary_weight: 0.0,
        selected_weight: 1.5,
        alternatives_considered: 3,
    };
    assert_eq!(c.weight_delta(), 1.5);
}

#[test]
fn test_c1_weight_correction_delta_negative() {
    // C1: Negative delta when selected had lower weight than primary.
    // This can happen when the weight-best overall was rejected but a
    // lower-weight accepting alternative was found in the spillover.
    let c = WeightCorrection {
        category: "TestGrammar",
        primary_weight: 2.0,
        selected_weight: 0.5,
        alternatives_considered: 2,
    };
    assert_eq!(c.weight_delta(), -1.5);
}

#[test]
fn test_c1_weight_correction_delta_zero() {
    // C1: Zero delta means primary was also the selected (no correction needed).
    let c = WeightCorrection {
        category: "TestGrammar",
        primary_weight: 0.5,
        selected_weight: 0.5,
        alternatives_considered: 2,
    };
    assert_eq!(c.weight_delta(), 0.0);
}

#[test]
fn test_c1_primary_adjustment_clamped() {
    // C1: primary_adjustment should be clamped to [0, max_adjustment].
    let c = WeightCorrection {
        category: "TestGrammar",
        primary_weight: 0.0,
        selected_weight: 10.0,
        alternatives_considered: 5,
    };
    // learning_rate=0.1, max=0.5 → raw=1.0, clamped to 0.5
    assert_eq!(c.primary_adjustment(0.1, 0.5), 0.5);
    // learning_rate=0.01, max=0.5 → raw=0.1, unclamped
    assert!((c.primary_adjustment(0.01, 0.5) - 0.1).abs() < 1e-10);
}

#[test]
fn test_c1_primary_adjustment_zero_delta() {
    // C1: Zero delta → zero adjustment.
    let c = WeightCorrection {
        category: "TestGrammar",
        primary_weight: 1.0,
        selected_weight: 1.0,
        alternatives_considered: 2,
    };
    assert_eq!(c.primary_adjustment(0.1, 0.5), 0.0);
}

// ── C2: Position-aware NFA disambiguation tests ──

#[test]
fn test_c2_position_weight_penalty_value() {
    // C2: The position weight penalty constant should be positive.
    assert!(POSITION_WEIGHT_PENALTY > 0.0, "POSITION_WEIGHT_PENALTY should be positive");
}

#[test]
fn test_c2_position_weight_adjustment_same_position() {
    // C2: Same position → zero penalty, adjusted weight equals original.
    let pos_diff: usize = 0;
    let original_weight = 1.5;
    let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
    assert_eq!(adjusted, original_weight, "same position should have no penalty");
}

#[test]
fn test_c2_position_weight_adjustment_longer_match() {
    // C2: Longer match (positive pos_diff) → penalty added.
    let primary_pos: usize = 5;
    let alt_pos: usize = 7;
    let pos_diff = (alt_pos as isize - primary_pos as isize).unsigned_abs();
    let original_weight = 1.0;
    let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
    // pos_diff = 2, penalty = 2 * 0.5 = 1.0
    assert_eq!(adjusted, 2.0, "longer match penalty: 1.0 + 2*0.5 = 2.0");
}

#[test]
fn test_c2_position_weight_adjustment_shorter_match() {
    // C2: Shorter match (negative pos_diff) → penalty added symmetrically.
    let primary_pos: usize = 7;
    let alt_pos: usize = 5;
    let pos_diff = (alt_pos as isize - primary_pos as isize).unsigned_abs();
    let original_weight = 0.5;
    let adjusted = original_weight + pos_diff as f64 * POSITION_WEIGHT_PENALTY;
    // pos_diff = 2, penalty = 2 * 0.5 = 1.0
    assert_eq!(adjusted, 1.5, "shorter match penalty: 0.5 + 2*0.5 = 1.5");
}

// ── B6: Runtime WFST query tests ──

#[test]
fn test_b6_valid_continuations_basic() {
    // B6: valid_continuations returns all tokens with dispatch actions
    let token_map =
        TokenIdMap::from_names(vec!["A".to_string(), "B".to_string(), "C".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".into(),
            parse_fn: "p1".into(),
        },
        TropicalWeight::new(1.0),
    );
    builder.add_action(
        "B",
        DispatchAction::Direct {
            rule_label: "R2".into(),
            parse_fn: "p2".into(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();

    let conts = wfst.valid_continuations();
    assert_eq!(conts.len(), 2, "expected 2 valid continuations, got {}", conts.len());
    // Sorted by weight: B(0.0) before A(1.0)
    assert_eq!(conts[0].0, "B");
    assert_eq!(conts[0].1, TropicalWeight::new(0.0));
    assert_eq!(conts[1].0, "A");
    assert_eq!(conts[1].1, TropicalWeight::new(1.0));
}

#[test]
fn test_b6_valid_continuations_empty() {
    // B6: Empty WFST → no valid continuations
    let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
    let builder = PredictionWfstBuilder::new("X", token_map);
    let wfst = builder.build();

    let conts = wfst.valid_continuations();
    assert!(conts.is_empty());
}

#[test]
fn test_b6_has_valid_dispatch() {
    // B6: has_valid_dispatch checks if token is recognized
    let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".into(),
            parse_fn: "p1".into(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();

    assert!(wfst.has_valid_dispatch("A"), "A should have valid dispatch");
    assert!(!wfst.has_valid_dispatch("B"), "B should have no dispatch (no action added)");
    assert!(!wfst.has_valid_dispatch("C"), "C should have no dispatch (unknown token)");
}

#[test]
fn test_b6_parse_progress() {
    // B6: parse_progress returns 0.0 at start, 1.0 at final
    let token_map = TokenIdMap::from_names(vec!["A".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".into(),
            parse_fn: "p1".into(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();

    // Start state = 0
    assert_eq!(wfst.parse_progress(0), 0.0);
    // Final state = 1 (star-shaped: start → accept)
    assert_eq!(wfst.parse_progress(1), 1.0);
}

#[test]
fn test_b6_parse_progress_empty() {
    // B6: Empty WFST → progress = 0.0
    let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
    let builder = PredictionWfstBuilder::new("X", token_map);
    let wfst = builder.build();

    assert_eq!(wfst.parse_progress(0), 0.0);
}

// ── A7: Entropy-based beam width tests ──

#[test]
fn test_a7_entropy_to_beam_width_below_threshold() {
    // A7: Entropy below threshold → no beam (deterministic dispatch)
    let beam = entropy_to_beam_width(0.3, 1.0, 0.5, 0.5, 10.0);
    assert!(beam.is_none(), "entropy below threshold should produce no beam");
}

#[test]
fn test_a7_entropy_to_beam_width_at_threshold() {
    // A7: Entropy exactly at threshold → no beam
    let beam = entropy_to_beam_width(0.5, 1.0, 0.5, 0.5, 10.0);
    assert!(beam.is_none(), "entropy at threshold should produce no beam");
}

#[test]
fn test_a7_entropy_to_beam_width_above_threshold() {
    // A7: Entropy above threshold → base + scale * (entropy - threshold)
    let beam = entropy_to_beam_width(2.5, 1.0, 0.5, 0.5, 10.0);
    // beam = 1.0 + 0.5 * (2.5 - 0.5) = 1.0 + 1.0 = 2.0
    let expected = 2.0;
    assert!(
        (beam.expect("should have beam") - expected).abs() < 1e-10,
        "expected beam={}, got {:?}",
        expected,
        beam
    );
}

#[test]
fn test_a7_entropy_to_beam_width_capped() {
    // A7: Very high entropy → capped at max_beam
    let beam = entropy_to_beam_width(100.0, 1.0, 0.5, 0.5, 10.0);
    assert_eq!(beam, Some(10.0), "beam should be capped at max_beam");
}

#[test]
fn test_a7_entropy_to_beam_width_constants() {
    // A7: Default constants produce reasonable results
    let beam = entropy_to_beam_width(
        3.0,
        ENTROPY_BEAM_BASE,
        ENTROPY_BEAM_SCALE,
        ENTROPY_BEAM_LOW_THRESHOLD,
        ENTROPY_BEAM_MAX,
    );
    // beam = 1.0 + 0.5 * (3.0 - 0.5) = 1.0 + 1.25 = 2.25
    assert!((beam.expect("should have beam") - 2.25).abs() < 1e-10);
}

#[test]
fn test_a7_compute_entropy_single_action() {
    // A7: Single deterministic action → entropy = 0 (no uncertainty)
    let token_map = TokenIdMap::from_names(vec!["A".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("X", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();

    let (entropy_nats, entropy_bits) = wfst.compute_entropy();
    // Single action with weight 0 → deterministic, entropy ≈ 0
    assert!(
        entropy_nats.abs() < 0.1,
        "single action should have near-zero entropy, got {}",
        entropy_nats
    );
    assert!(
        entropy_bits.abs() < 0.1,
        "single action should have near-zero bits, got {}",
        entropy_bits
    );
}

#[test]
fn test_a7_compute_entropy_uniform_two_actions() {
    // A7: Two actions with equal weight → entropy = ln(2) nats ≈ 1 bit
    let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("X", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "B",
        DispatchAction::Direct {
            rule_label: "R2".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();

    let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
    // Two equal-weight paths: H = ln(2) ≈ 0.693 nats ≈ 1.0 bits
    assert!(
        (entropy_bits - 1.0).abs() < 0.15,
        "two equal actions should have ~1 bit entropy, got {}",
        entropy_bits
    );
}

#[test]
fn test_a7_compute_entropy_skewed_actions() {
    // A7: One dominant action (weight 0.0) vs one unlikely (weight 5.0)
    // → entropy should be low (near-deterministic)
    let token_map = TokenIdMap::from_names(vec!["A".to_string(), "B".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("X", token_map);
    builder.add_action(
        "A",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "B",
        DispatchAction::Direct {
            rule_label: "R2".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(5.0),
    );
    let wfst = builder.build();

    let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
    // Heavily skewed → entropy << 1 bit
    assert!(
        entropy_bits < 0.5,
        "skewed distribution should have low entropy, got {}",
        entropy_bits
    );
}

#[test]
fn test_a7_compute_entropy_empty_wfst() {
    // A7: Empty WFST → entropy = 0
    let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
    let builder = PredictionWfstBuilder::new("X", token_map);
    let wfst = builder.build();

    let (entropy_nats, _entropy_bits) = wfst.compute_entropy();
    assert!(entropy_nats.abs() < 1e-10, "empty WFST should have zero entropy");
}

// ── D3: DOT visualization tests ────────────────────────────────────

#[test]
fn test_d3_prediction_wfst_dot_basic() {
    // D3: A simple 2-action WFST should produce valid DOT with correct structure
    let token_map =
        TokenIdMap::from_names(vec!["Ident".to_string(), "LParen".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("Proc", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "PInput".to_string(),
            parse_fn: "parse_pinput".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "LParen",
        DispatchAction::Direct {
            rule_label: "PSend".to_string(),
            parse_fn: "parse_psend".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst = builder.build();
    let dot = wfst.to_dot();

    assert!(dot.contains("digraph PredictionWfst_Proc"), "should have digraph header");
    assert!(dot.contains("rankdir=LR"), "should be left-to-right layout");
    assert!(dot.contains("(start)"), "should mark start state");
    assert!(dot.contains("(final)"), "should mark final state(s)");
    assert!(dot.contains("Ident"), "should label Ident token");
    assert!(dot.contains("LParen"), "should label LParen token");
    assert!(dot.contains("PInput"), "should label PInput action");
    assert!(dot.contains("PSend"), "should label PSend action");
    assert!(dot.contains("color=black"), "weight=0.0 edges should be black");
    assert!(dot.ends_with("}\n"), "should end with closing brace");
}

#[test]
fn test_d3_prediction_wfst_dot_ambiguous_red_edges() {
    // D3: Ambiguous transitions (weight > 0.0) should be colored red
    let token_map = TokenIdMap::from_names(vec!["Ident".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "R1".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Ident",
        DispatchAction::Direct {
            rule_label: "R2".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(1.0),
    );
    let wfst = builder.build();
    let dot = wfst.to_dot();

    assert!(dot.contains("color=red"), "ambiguous edge (weight=1.0) should be red");
    assert!(dot.contains("color=black"), "deterministic edge (weight=0.0) should be black");
    assert!(dot.contains("R1"), "should contain first rule label");
    assert!(dot.contains("R2"), "should contain second rule label");
}

#[test]
fn test_d3_prediction_wfst_dot_empty() {
    // D3: Empty WFST should still produce valid DOT
    let token_map = TokenIdMap::from_names(std::iter::empty::<String>());
    let builder = PredictionWfstBuilder::new("Empty", token_map);
    let wfst = builder.build();
    let dot = wfst.to_dot();

    assert!(dot.contains("digraph PredictionWfst_Empty"));
    assert!(dot.contains("(start)"));
    // Should have at least the start state node
    assert!(dot.contains("S0"));
}

#[test]
fn test_d3_prediction_wfst_dot_weight_format() {
    // D3: Weights should be formatted with 2 decimal places
    let token_map = TokenIdMap::from_names(vec!["X".to_string()].into_iter());
    let mut builder = PredictionWfstBuilder::new("W", token_map);
    builder.add_action(
        "X",
        DispatchAction::Direct {
            rule_label: "Rx".to_string(),
            parse_fn: "px".to_string(),
        },
        TropicalWeight::new(2.5),
    );
    let wfst = builder.build();
    let dot = wfst.to_dot();

    assert!(dot.contains("[2.50]"), "weight should be formatted as [2.50], got:\n{}", dot);
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint 8: Canonical structure & isomorphism tests
// ══════════════════════════════════════════════════════════════════════════

/// Helper: build a WFST with the given token→action mapping.
fn build_test_wfst(
    category: &str,
    token_actions: &[(&str, &str, &str, f64)], // (token, rule_label, parse_fn, weight)
) -> PredictionWfst {
    let token_names: Vec<String> = token_actions
        .iter()
        .map(|(t, _, _, _)| t.to_string())
        .collect();
    let token_map = TokenIdMap::from_names(token_names.into_iter());
    let mut builder = PredictionWfstBuilder::new(category, token_map);
    for (tok, label, parse_fn, weight) in token_actions {
        builder.add_action(
            tok,
            DispatchAction::Direct {
                rule_label: label.to_string(),
                parse_fn: parse_fn.to_string(),
            },
            TropicalWeight::new(*weight),
        );
    }
    builder.build()
}

#[test]
fn test_canonical_structure_same_topology_different_labels() {
    // Two WFSTs with identical topology but different action labels
    // should produce identical canonical structures.
    let wfst_int = build_test_wfst(
        "Int",
        &[
            ("Plus", "AddInt", "parse_add_int", 0.0),
            ("Minus", "SubInt", "parse_sub_int", 0.0),
            ("Ident", "VarInt", "parse_var_int", 1.0),
        ],
    );
    let wfst_float = build_test_wfst(
        "Float",
        &[
            ("Plus", "AddFloat", "parse_add_float", 0.0),
            ("Minus", "SubFloat", "parse_sub_float", 0.0),
            ("Ident", "VarFloat", "parse_var_float", 1.0),
        ],
    );

    let canon_int = wfst_int.canonical_structure();
    let canon_float = wfst_float.canonical_structure();

    assert_eq!(
        canon_int, canon_float,
        "Isomorphic WFSTs should have equal canonical structures"
    );
    assert_eq!(
        wfst_int.canonical_hash(),
        wfst_float.canonical_hash(),
        "Isomorphic WFSTs should have equal canonical hashes"
    );
}

#[test]
fn test_canonical_structure_different_topology() {
    // Two WFSTs with different topologies should have different canonical structures.
    let wfst_a = build_test_wfst("A", &[("Plus", "Add", "pa", 0.0), ("Minus", "Sub", "ps", 0.0)]);
    let wfst_b = build_test_wfst(
        "B",
        &[
            ("Plus", "Add", "pa", 0.0),
            ("Star", "Mul", "pm", 0.0), // Different token
        ],
    );

    let canon_a = wfst_a.canonical_structure();
    let canon_b = wfst_b.canonical_structure();

    assert_ne!(
        canon_a, canon_b,
        "Different topologies should produce different canonical structures"
    );
}

#[test]
fn test_canonical_structure_different_weights() {
    // Same tokens and actions but different weights → different canonical structures.
    let wfst_a = build_test_wfst("A", &[("Plus", "Add", "pa", 0.0)]);
    let wfst_b = build_test_wfst(
        "B",
        &[
            ("Plus", "Add", "pa", 1.0), // Different weight
        ],
    );

    let canon_a = wfst_a.canonical_structure();
    let canon_b = wfst_b.canonical_structure();

    assert_ne!(
        canon_a, canon_b,
        "Different weights should produce different canonical structures"
    );
}

#[test]
fn test_canonical_structure_debruijn_indexing() {
    // Verify De Bruijn indices are assigned in encounter order.
    let wfst = build_test_wfst(
        "Test",
        &[
            ("Plus", "Add", "pa", 0.0),
            ("Minus", "Sub", "ps", 0.5),
            ("Star", "Mul", "pm", 1.0),
        ],
    );

    let canonical = wfst.canonical_structure();

    // Action shapes should all be Direct
    assert_eq!(canonical.action_shapes.len(), 3);
    for shape in &canonical.action_shapes {
        assert_eq!(*shape, CanonicalActionShape::Direct);
    }

    // Start state transitions should use De Bruijn indices 0, 1, 2
    let start = &canonical.states[0];
    let db_indices: Vec<u32> = start.transitions.iter().map(|(_, db, _, _)| *db).collect();
    // After sorting by token_id, the De Bruijn indices should cover {0, 1, 2}
    let mut sorted_indices = db_indices.clone();
    sorted_indices.sort();
    sorted_indices.dedup();
    assert_eq!(sorted_indices, vec![0, 1, 2], "De Bruijn indices should be 0, 1, 2");
}

#[test]
fn test_canonical_structure_action_shape_mismatch() {
    // Two WFSTs with same topology but different action shapes are NOT isomorphic.
    let token_map = TokenIdMap::from_names(vec!["X".to_string()].into_iter());

    let mut builder_a = PredictionWfstBuilder::new("A", token_map.clone());
    builder_a.add_action(
        "X",
        DispatchAction::Direct {
            rule_label: "RuleA".to_string(),
            parse_fn: "parse_a".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let wfst_a = builder_a.build();

    let mut builder_b = PredictionWfstBuilder::new("B", token_map);
    builder_b.add_action(
        "X",
        DispatchAction::Variable { category: "B".to_string() },
        TropicalWeight::new(0.0),
    );
    let wfst_b = builder_b.build();

    let canon_a = wfst_a.canonical_structure();
    let canon_b = wfst_b.canonical_structure();

    assert_ne!(canon_a, canon_b, "WFSTs with different action shapes should not be isomorphic");
}

#[test]
fn test_canonical_hash_deterministic() {
    // Same WFST should always produce the same hash.
    let wfst = build_test_wfst("Test", &[("A", "R1", "p1", 0.0), ("B", "R2", "p2", 1.0)]);
    let h1 = wfst.canonical_hash();
    let h2 = wfst.canonical_hash();
    assert_eq!(h1, h2, "Canonical hash should be deterministic");
}

// ══════════════════════════════════════════════════════════════════════════
// Two-token WFST tests (Sprint 1)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn test_two_token_builder_creates_intermediate_states() {
    // Two-token paths should create intermediate (non-final) states
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer", "Boolean"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);

    // Single-token action
    builder.add_action(
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntLit".to_string(),
            parse_fn: "parse_intlit".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    // Two-token actions: Float → ( → FloatId, Float → Boolean → BoolToFloat
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Boolean",
        DispatchAction::Direct {
            rule_label: "BoolToFloat".to_string(),
            parse_fn: "parse_booltofloat".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();

    // Should have: start(0) + 1 single-token final + 1 intermediate(Float) + 2 two-token finals
    assert_eq!(
        wfst.num_states(),
        5,
        "expected 5 states: start + 1 single final + 1 intermediate + 2 two-token finals"
    );

    // The intermediate state should NOT be final
    let intermediate = wfst.states.iter().find(|s| !s.is_final && s.id != 0);
    assert!(intermediate.is_some(), "should have a non-final intermediate state");

    // The intermediate should have 2 outgoing transitions (LParen, Boolean)
    let mid = intermediate.expect("intermediate exists");
    assert_eq!(mid.transitions.len(), 2, "intermediate should have 2 transitions");
}

#[test]
fn test_predict_two_token_resolves_ambiguity() {
    // predict_two_token should return narrowed results via intermediate states
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);

    // Two ambiguous rules sharing dispatch token "Float"
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "parse_inttofloat".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();

    // Two-token query: Float + LParen → FloatId only
    let results = wfst.predict_two_token("Float", "LParen");
    assert_eq!(results.len(), 1, "two-token query should resolve to single action");
    assert_eq!(results[0].action.rule_label(), "FloatId");

    // Two-token query: Float + Integer → IntToFloat only
    let results = wfst.predict_two_token("Float", "Integer");
    assert_eq!(results.len(), 1, "two-token query should resolve to single action");
    assert_eq!(results[0].action.rule_label(), "IntToFloat");
}

#[test]
fn test_predict_two_token_fallback_to_single() {
    // When no intermediate states exist for token1, fall back to single-token predict
    let token_map = TokenIdMap::from_names(vec!["Plus", "Minus"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Plus",
        DispatchAction::Direct {
            rule_label: "Add".to_string(),
            parse_fn: "parse_add".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();

    // No two-token paths for Plus — should fall back to single-token
    let results = wfst.predict_two_token("Plus", "Minus");
    assert_eq!(results.len(), 1, "should fall back to single-token predict");
    assert_eq!(results[0].action.rule_label(), "Add");
}

#[test]
fn test_predict_two_token_unknown_token2_fallback() {
    // When token2 is not found in intermediate transitions, fall back to single-token
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Unknown"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();

    // Float + Unknown → no match via intermediate, should fall back to single-token
    // But there's no single-token "Float" action either, so predict("Float") would
    // find the intermediate transition (non-final), skip it, and return empty.
    // Actually, predict() returns actions from final states, and intermediates are not final.
    // So it returns empty. predict_two_token should also handle this gracefully.
    let results = wfst.predict_two_token("Float", "Unknown");
    // Falls back to predict("Float"), which finds no actions via final states
    assert!(
        results.is_empty(),
        "unknown token2 should result in empty or single-token fallback"
    );
}

#[test]
fn test_is_deterministic_after_two_tokens() {
    // is_deterministic_after should return Some when two-token path yields singleton
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "parse_inttofloat".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();

    // Two-token: Float + LParen → FloatId (deterministic)
    assert_eq!(wfst.is_deterministic_after(&["Float", "LParen"]), Some("FloatId".to_string()),);
    // Two-token: Float + Integer → IntToFloat (deterministic)
    assert_eq!(
        wfst.is_deterministic_after(&["Float", "Integer"]),
        Some("IntToFloat".to_string()),
    );
    // Single-token: Integer → no action (empty)
    assert_eq!(wfst.is_deterministic_after(&["Integer"]), None);
    // Empty sequence
    assert_eq!(wfst.is_deterministic_after(&[]), None);
}

#[test]
fn test_live_actions_after_returns_narrowed_set() {
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "parse_inttofloat".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let wfst = builder.build();

    // Two tokens: narrowed to 1
    let actions = wfst.live_actions_after(&["Float", "LParen"]);
    assert_eq!(actions.len(), 1);
    assert_eq!(actions[0].action.rule_label(), "FloatId");

    // Single token with no single-token actions: empty
    let actions = wfst.live_actions_after(&["Float"]);
    assert!(actions.is_empty(), "no single-token Float action");

    // Empty sequence
    let actions = wfst.live_actions_after(&[]);
    assert!(actions.is_empty());
}

// ══════════════════════════════════════════════════════════════════════════
// FIRST-set expansion tests (Sprint 2)
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn test_enrich_terminal_second_items() {
    // enrich_with_two_token_paths should add paths when 2nd items are disjoint terminals
    use crate::grammar::ir::{RDRuleInfo, RDSyntaxItem};
    let rd_rules = vec![
        RDRuleInfo {
            label: "IfThen".to_string(),
            category: "Stmt".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
        RDRuleInfo {
            label: "IfNot".to_string(),
            category: "Stmt".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("if".to_string()),
                RDSyntaxItem::Terminal("!".to_string()),
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
    ];

    let token_map =
        TokenIdMap::from_names(vec!["KwIf", "LParen", "Bang"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
    builder.add_action(
        "KwIf",
        DispatchAction::Direct {
            rule_label: "IfThen".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "KwIf",
        DispatchAction::Direct {
            rule_label: "IfNot".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    let mut wfsts = HashMap::new();
    wfsts.insert("Stmt".to_string(), builder.build());

    let first_sets = HashMap::new(); // Not needed for terminal second items

    let added =
        enrich_with_two_token_paths(&mut wfsts, &rd_rules, &["Stmt".to_string()], &first_sets);

    assert!(added >= 2, "should add at least 2 two-token paths, got {}", added);

    let wfst = wfsts.get("Stmt").expect("Stmt WFST exists");
    // Should be able to resolve via two-token query
    let results = wfst.predict_two_token("KwIf", "LParen");
    assert_eq!(results.len(), 1, "KwIf + LParen should resolve to IfThen");
    assert_eq!(results[0].action.rule_label(), "IfThen");

    let results = wfst.predict_two_token("KwIf", "Bang");
    assert_eq!(results.len(), 1, "KwIf + Bang should resolve to IfNot");
    assert_eq!(results[0].action.rule_label(), "IfNot");
}

#[test]
fn test_enrich_nonterminal_first_set_expansion() {
    // Sprint 2: enrich should expand NonTerminal second items via FIRST sets
    use crate::grammar::ir::{RDRuleInfo, RDSyntaxItem};
    use crate::prediction::FirstSet;

    // Rule A: float ( Expr ) — FIRST(Expr) = {Integer, Ident}
    // Rule B: float [ List ] — FIRST(List) = {LBracket, Ident} — overlaps with Expr on Ident
    // Since Ident appears in both, this group should NOT be enriched (overlap)
    let rd_rules_overlapping = vec![
        RDRuleInfo {
            label: "FloatExpr".to_string(),
            category: "Val".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
        RDRuleInfo {
            label: "FloatList".to_string(),
            category: "Val".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "List".to_string(),
                    param_name: "l".to_string(),
                },
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
    ];

    let mut first_sets_overlapping = HashMap::new();
    let mut expr_first = FirstSet::new();
    expr_first.insert("Integer");
    expr_first.insert("Ident");
    first_sets_overlapping.insert("Expr".to_string(), expr_first);
    let mut list_first = FirstSet::new();
    list_first.insert("LBracket");
    list_first.insert("Ident"); // overlaps with Expr
    first_sets_overlapping.insert("List".to_string(), list_first);

    let token_map = TokenIdMap::from_names(vec!["KwFloat"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Val", token_map);
    builder.add_action(
        "KwFloat",
        DispatchAction::Direct {
            rule_label: "FloatExpr".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "KwFloat",
        DispatchAction::Direct {
            rule_label: "FloatList".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    let mut wfsts_overlap = HashMap::new();
    wfsts_overlap.insert("Val".to_string(), builder.build());

    let added = enrich_with_two_token_paths(
        &mut wfsts_overlap,
        &rd_rules_overlapping,
        &["Val".to_string()],
        &first_sets_overlapping,
    );
    assert_eq!(added, 0, "overlapping FIRST sets should NOT be enriched");

    // Now test disjoint case:
    // Rule A: float ( Expr ) — FIRST(Expr) = {Integer, LParen}
    // Rule B: float [ List ] — FIRST(List) = {LBracket, Ident}
    // Disjoint: no overlap → should add paths
    let rd_rules_disjoint = vec![
        RDRuleInfo {
            label: "FloatExpr".to_string(),
            category: "Val".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
        RDRuleInfo {
            label: "FloatList".to_string(),
            category: "Val".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("float".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "List".to_string(),
                    param_name: "l".to_string(),
                },
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
    ];

    let mut first_sets_disjoint = HashMap::new();
    let mut expr_first2 = FirstSet::new();
    expr_first2.insert("Integer");
    expr_first2.insert("LParen");
    first_sets_disjoint.insert("Expr".to_string(), expr_first2);
    let mut list_first2 = FirstSet::new();
    list_first2.insert("LBracket");
    list_first2.insert("Ident");
    first_sets_disjoint.insert("List".to_string(), list_first2);

    let token_map2 = TokenIdMap::from_names(vec!["KwFloat"].into_iter().map(String::from));
    let mut builder2 = PredictionWfstBuilder::new("Val", token_map2);
    builder2.add_action(
        "KwFloat",
        DispatchAction::Direct {
            rule_label: "FloatExpr".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder2.add_action(
        "KwFloat",
        DispatchAction::Direct {
            rule_label: "FloatList".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    let mut wfsts_disjoint = HashMap::new();
    wfsts_disjoint.insert("Val".to_string(), builder2.build());

    let added = enrich_with_two_token_paths(
        &mut wfsts_disjoint,
        &rd_rules_disjoint,
        &["Val".to_string()],
        &first_sets_disjoint,
    );
    assert_eq!(added, 4, "disjoint FIRST sets should add 4 two-token paths (2+2)");

    // Verify: Integer → FloatExpr, LParen → FloatExpr, LBracket → FloatList, Ident → FloatList
    let wfst = wfsts_disjoint.get("Val").expect("Val WFST exists");
    let r = wfst.predict_two_token("KwFloat", "Integer");
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].action.rule_label(), "FloatExpr");

    let r = wfst.predict_two_token("KwFloat", "LBracket");
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].action.rule_label(), "FloatList");
}

#[test]
fn test_enrich_mixed_terminal_nonterminal() {
    // Mix of terminal and nonterminal second items
    // terminal_to_variant_name("cmd") = "KwCmd"
    use crate::grammar::ir::{RDRuleInfo, RDSyntaxItem};
    use crate::prediction::FirstSet;

    // Rule A: cmd ( — terminal second item "("
    // Rule B: cmd Expr — nonterminal second item, FIRST(Expr) = {Integer}
    // Disjoint: "LParen" ≠ "Integer"
    let rd_rules = vec![
        RDRuleInfo {
            label: "CmdParen".to_string(),
            category: "Cmd".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("cmd".to_string()),
                RDSyntaxItem::Terminal("(".to_string()),
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
        RDRuleInfo {
            label: "CmdExpr".to_string(),
            category: "Cmd".to_string(),
            items: vec![
                RDSyntaxItem::Terminal("cmd".to_string()),
                RDSyntaxItem::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
            ],
            has_binder: false,
            has_multi_binder: false,
            is_collection: false,
            collection_type: None,
            separator: None,
            prefix_bp: None,
            eval_mode: None,
        },
    ];

    let mut first_sets = HashMap::new();
    let mut expr_first = FirstSet::new();
    expr_first.insert("Integer");
    first_sets.insert("Expr".to_string(), expr_first);

    // terminal_to_variant_name("cmd") = "KwCmd"
    let token_map = TokenIdMap::from_names(vec!["KwCmd"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Cmd", token_map);
    builder.add_action(
        "KwCmd",
        DispatchAction::Direct {
            rule_label: "CmdParen".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "KwCmd",
        DispatchAction::Direct {
            rule_label: "CmdExpr".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    let mut wfsts = HashMap::new();
    wfsts.insert("Cmd".to_string(), builder.build());

    let added =
        enrich_with_two_token_paths(&mut wfsts, &rd_rules, &["Cmd".to_string()], &first_sets);
    assert_eq!(added, 2, "mixed terminal+nonterminal should add 2 paths");

    let wfst = wfsts.get("Cmd").expect("Cmd WFST exists");
    let r = wfst.predict_two_token("KwCmd", "LParen");
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].action.rule_label(), "CmdParen");

    let r = wfst.predict_two_token("KwCmd", "Integer");
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].action.rule_label(), "CmdExpr");
}

#[test]
fn test_two_token_mixed_single_and_two_token_paths() {
    // WFST with both single-token and two-token paths for the same first token
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);

    // Single-token path: Float → Direct action (cast rule)
    builder.add_action(
        "Float",
        DispatchAction::Cast {
            source_category: "Float".to_string(),
            wrapper_label: "CastFloat".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    // Two-token path: Float + LParen → FloatId
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "parse_floatid".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();

    // Single-token query: Float → CastFloat (from single-token path)
    let results = wfst.predict("Float");
    assert_eq!(results.len(), 1, "single-token predict should find CastFloat");
    assert_eq!(results[0].action.rule_label(), "CastFloat");

    // Two-token query: Float + LParen → FloatId (from two-token path)
    let results = wfst.predict_two_token("Float", "LParen");
    assert_eq!(results.len(), 1, "two-token predict should find FloatId via intermediate");
    assert_eq!(results[0].action.rule_label(), "FloatId");

    // Two-token query with unmatched token2: Float + Integer → fallback to single-token
    let results = wfst.predict_two_token("Float", "Integer");
    assert_eq!(results.len(), 1, "unmatched token2 should fall back to single-token CastFloat");
    assert_eq!(results[0].action.rule_label(), "CastFloat");
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint 3: ContextWeight powerset query tests
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn test_context_labels_assignment() {
    // Assign context labels and verify bit positions
    let token_map = TokenIdMap::from_names(vec!["Float"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "BoolToFloat".to_string(),
            parse_fn: "p3".to_string(),
        },
        TropicalWeight::new(1.0),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat", "BoolToFloat"]);

    assert_eq!(wfst.context_labels.len(), 3);
    assert_eq!(wfst.context_labels["FloatId"], 0);
    assert_eq!(wfst.context_labels["IntToFloat"], 1);
    assert_eq!(wfst.context_labels["BoolToFloat"], 2);
}

#[test]
fn test_live_rules_context_all_alive() {
    // All rules alive when querying the shared dispatch token
    let token_map = TokenIdMap::from_names(vec!["Float"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    let ctx = wfst.live_rules_context_after(&["Float"]);
    assert_eq!(ctx.count(), 2, "both rules should be alive after dispatch token");
    assert!(ctx.contains(0), "FloatId (bit 0) should be alive");
    assert!(ctx.contains(1), "IntToFloat (bit 1) should be alive");
}

#[test]
fn test_live_rules_context_narrowed_by_two_token() {
    // Two-token paths narrow the live set to a singleton
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    // Two rules share dispatch token "Float"
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    // Two-token query narrows to singleton
    let ctx = wfst.live_rules_context_after(&["Float", "LParen"]);
    assert_eq!(ctx.count(), 1, "should narrow to FloatId");
    assert!(ctx.contains(0), "FloatId (bit 0) should survive");
    assert!(!ctx.contains(1), "IntToFloat (bit 1) should be eliminated");

    let ctx = wfst.live_rules_context_after(&["Float", "Integer"]);
    assert_eq!(ctx.count(), 1, "should narrow to IntToFloat");
    assert!(!ctx.contains(0), "FloatId should be eliminated");
    assert!(ctx.contains(1), "IntToFloat should survive");
}

#[test]
fn test_is_deterministic_context_singleton() {
    // is_deterministic_context returns Some when ContextWeight is singleton
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    assert_eq!(wfst.is_deterministic_context(&["Float", "LParen"]), Some("FloatId".to_string()),);
    assert_eq!(
        wfst.is_deterministic_context(&["Float", "Integer"]),
        Some("IntToFloat".to_string()),
    );
}

#[test]
fn test_is_deterministic_context_ambiguous() {
    // is_deterministic_context returns None when multiple rules survive
    let token_map = TokenIdMap::from_names(vec!["Float"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    // Single-token query: both rules alive → None
    assert_eq!(wfst.is_deterministic_context(&["Float"]), None);
}

#[test]
fn test_context_narrowing_reports_count() {
    // context_narrowing returns the correct count
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    let (ctx, count) = wfst.context_narrowing(&["Float", "LParen"]);
    assert_eq!(count, 1);
    assert!(ctx.contains(0));

    let (ctx, count) = wfst.context_narrowing(&["Float", "Integer"]);
    assert_eq!(count, 1);
    assert!(ctx.contains(1));
}

#[test]
fn test_context_labels_empty_no_crash() {
    // When no context labels are assigned, queries return zero ContextWeight
    let token_map = TokenIdMap::from_names(vec!["Float"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );

    let wfst = builder.build();

    // No context labels assigned — should return zero
    let ctx = wfst.live_rules_context_after(&["Float"]);
    assert_eq!(ctx.count(), 0, "no context labels → zero ContextWeight");
    assert_eq!(wfst.is_deterministic_context(&["Float"]), None);
}

#[test]
fn test_context_labels_unknown_token() {
    // Query with unknown token returns zero ContextWeight
    let token_map = TokenIdMap::from_names(vec!["Float"].into_iter().map(String::from));
    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    builder.add_action(
        "Float",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId"]);

    let ctx = wfst.live_rules_context_after(&["Unknown"]);
    assert_eq!(ctx.count(), 0, "unknown token → empty live set");
}

// ══════════════════════════════════════════════════════════════════════════
// Sprint 4: Narrowed NFA candidate filtering tests
// ══════════════════════════════════════════════════════════════════════════

#[test]
fn test_nfa_order_with_context_narrowing() {
    // Verify that nfa_alternative_order works correctly on a narrowed
    // candidate set (simulates what the trampoline does in Sprint 4).
    let token_map = TokenIdMap::from_names(
        vec!["Float", "LParen", "Integer"]
            .into_iter()
            .map(String::from),
    );

    let mut builder = PredictionWfstBuilder::new("Expr", token_map);
    // Three rules share "Float", but two-token paths narrow to singletons
    builder.add_two_token_action(
        "Float",
        "LParen",
        DispatchAction::Direct {
            rule_label: "FloatId".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_two_token_action(
        "Float",
        "Integer",
        DispatchAction::Direct {
            rule_label: "IntToFloat".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["FloatId", "IntToFloat"]);

    // Without narrowing: both rules alive at single-token level
    let all_labels = vec!["FloatId", "IntToFloat"];
    let order = wfst.nfa_alternative_order("Float", &all_labels);
    // Both rules should be orderable — the fallback to single-token returns both
    assert!(order.len() >= 1, "should return at least 1 alternative");

    // With narrowing (simulating trampoline Sprint 4 logic):
    // When only two-token actions exist (no single-token), predict("Float")
    // returns empty (no final states reachable in one hop), so
    // live_rules_context_after(&["Float"]) returns zero. The trampoline
    // code falls through to try-all in this case (ctx.count() == 0 → keep all).
    let ctx = wfst.live_rules_context_after(&["Float"]);
    assert_eq!(ctx.count(), 0, "no single-token paths → empty context");

    // At two-token level, narrowing gives singletons
    let ctx2 = wfst.live_rules_context_after(&["Float", "LParen"]);
    let narrowed2: Vec<&str> = all_labels
        .iter()
        .copied()
        .filter(|label| {
            wfst.context_labels
                .get(*label)
                .map_or(true, |&bit| ctx2.contains(bit))
        })
        .collect();
    assert_eq!(narrowed2.len(), 1, "two-token narrows to FloatId");
    assert_eq!(narrowed2[0], "FloatId");
}

#[test]
fn test_narrowed_candidate_excludes_dead_rules() {
    // Verify that ContextWeight filtering correctly excludes rules
    // not in the live set.
    let token_map = TokenIdMap::from_names(vec!["KwFn"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
    builder.add_action(
        "KwFn",
        DispatchAction::Direct {
            rule_label: "FnDecl".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "KwFn",
        DispatchAction::Direct {
            rule_label: "FnExpr".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.5),
    );
    builder.add_action(
        "KwFn",
        DispatchAction::Direct {
            rule_label: "FnType".to_string(),
            parse_fn: "p3".to_string(),
        },
        TropicalWeight::new(1.0),
    );

    let mut wfst = builder.build();
    // Only assign labels to 2 of 3 rules (simulating a partial group)
    wfst.assign_context_labels(&["FnDecl", "FnExpr", "FnType"]);

    let ctx = wfst.live_rules_context_after(&["KwFn"]);
    assert_eq!(ctx.count(), 3, "all three rules alive at dispatch token");

    // Simulate removing FnType from the live set (as if two-token narrowed it)
    // by manually constructing a narrowed context
    use crate::automata::semiring::ContextWeight;
    let narrowed_ctx = ContextWeight::singleton(0).plus(&ContextWeight::singleton(1));
    assert_eq!(narrowed_ctx.count(), 2);

    let all_labels = vec!["FnDecl", "FnExpr", "FnType"];
    let narrowed: Vec<&str> = all_labels
        .iter()
        .copied()
        .filter(|label| {
            wfst.context_labels
                .get(*label)
                .map_or(true, |&bit| narrowed_ctx.contains(bit))
        })
        .collect();
    assert_eq!(narrowed.len(), 2);
    assert!(narrowed.contains(&"FnDecl"));
    assert!(narrowed.contains(&"FnExpr"));
    assert!(!narrowed.contains(&"FnType"));
}

#[test]
fn test_narrowed_preserves_order() {
    // After narrowing, nfa_alternative_order on the narrowed set preserves
    // WFST weight ordering.
    let token_map = TokenIdMap::from_names(vec!["KwLet"].into_iter().map(String::from));

    let mut builder = PredictionWfstBuilder::new("Stmt", token_map);
    builder.add_action(
        "KwLet",
        DispatchAction::Direct {
            rule_label: "LetMut".to_string(),
            parse_fn: "p1".to_string(),
        },
        TropicalWeight::new(0.0),
    );
    builder.add_action(
        "KwLet",
        DispatchAction::Direct {
            rule_label: "LetConst".to_string(),
            parse_fn: "p2".to_string(),
        },
        TropicalWeight::new(0.3),
    );

    let mut wfst = builder.build();
    wfst.assign_context_labels(&["LetMut", "LetConst"]);

    let narrowed = vec!["LetMut", "LetConst"];
    let ordered = wfst.nfa_alternative_order("KwLet", &narrowed);

    // Should be ordered by weight: LetMut (0.0) before LetConst (0.3)
    assert_eq!(ordered.len(), 2);
    assert_eq!(ordered[0].0, 0, "LetMut at index 0 (lowest weight)");
    assert_eq!(ordered[1].0, 1, "LetConst at index 1 (higher weight)");
    assert!(ordered[0].1.value() < ordered[1].1.value(), "weights should be ordered");
}
