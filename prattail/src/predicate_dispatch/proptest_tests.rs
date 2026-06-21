use super::*;
use proptest::prelude::*;

// ── Arbitrary PredicateExpr generator ──────────────────────────────────

fn arb_var() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "x".to_string(),
        "y".to_string(),
        "z".to_string(),
        "w".to_string(),
        "v".to_string(),
    ])
}

fn arb_channel() -> impl Strategy<Value = String> {
    prop::sample::select(vec!["ch1".to_string(), "ch2".to_string(), "ch3".to_string()])
}

fn arb_relation_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "eq".to_string(),
        "neq".to_string(),
        "fresh".to_string(),
        "count".to_string(),
        "size".to_string(),
        "custom".to_string(),
        "related".to_string(),
        ">=".to_string(),
    ])
}

fn arb_predicate_expr(depth: u32) -> impl Strategy<Value = PredicateExpr> {
    let leaf = prop_oneof![
        Just(PredicateExpr::True),
        Just(PredicateExpr::False),
        arb_var().prop_map(PredicateExpr::Atom),
        (arb_relation_name(), prop::collection::vec(arb_var(), 1..=3))
            .prop_map(|(name, args)| PredicateExpr::Relation { name, args }),
    ];
    if depth == 0 {
        leaf.boxed()
    } else {
        prop_oneof![
            leaf,
            arb_predicate_expr(depth - 1).prop_map(|e| PredicateExpr::Not(Box::new(e))),
            (arb_predicate_expr(depth - 1), arb_predicate_expr(depth - 1))
                .prop_map(|(a, b)| PredicateExpr::And(Box::new(a), Box::new(b))),
            (arb_predicate_expr(depth - 1), arb_predicate_expr(depth - 1))
                .prop_map(|(a, b)| PredicateExpr::Or(Box::new(a), Box::new(b))),
            (arb_var(), arb_predicate_expr(depth - 1)).prop_map(|(var, body)| {
                PredicateExpr::ForallFinite {
                    var,
                    domain: vec!["a".to_string()],
                    body: Box::new(body),
                }
            }),
            (arb_var(), arb_predicate_expr(depth - 1)).prop_map(|(var, body)| {
                PredicateExpr::ExistsFinite {
                    var,
                    domain: vec!["a".to_string()],
                    body: Box::new(body),
                }
            }),
            (arb_var(), arb_predicate_expr(depth - 1)).prop_map(|(var, body)| {
                PredicateExpr::ForallInfinite { var, body: Box::new(body) }
            }),
            (arb_var(), arb_predicate_expr(depth - 1)).prop_map(|(var, body)| {
                PredicateExpr::ExistsInfinite { var, body: Box::new(body) }
            }),
            arb_predicate_expr(depth - 1)
                .prop_map(|body| PredicateExpr::Bounded { body: Box::new(body), bound: 100 }),
        ]
        .boxed()
    }
}

fn arb_channel_context() -> impl Strategy<Value = ChannelContext> {
    prop::collection::vec((arb_var(), arb_channel()), 0..=5).prop_flat_map(|bindings| {
        let ctx_bindings = bindings.clone();
        prop::option::of(arb_channel()).prop_map(move |current| {
            let mut ctx = ChannelContext::new();
            for (var, ch) in &ctx_bindings {
                ctx.bind(var.clone(), ch.clone());
            }
            if let Some(ch) = current {
                ctx.set_current_channel(ch);
            }
            ctx
        })
    })
}

// ── Arbitrary WeightedMsoFormula generator ────────────────────────────

fn arb_mso_formula(depth: u32) -> impl Strategy<Value = WeightedMsoFormula> {
    let leaf = prop_oneof![
        arb_var().prop_map(|v| WeightedMsoFormula::Constant(v)),
        (arb_var(), arb_var())
            .prop_map(|(label, var)| WeightedMsoFormula::AtomicPos { label, var }),
        (arb_var(), arb_var()).prop_map(|(x, y)| WeightedMsoFormula::Order { x, y }),
        (arb_var(), arb_var())
            .prop_map(|(var, set_var)| WeightedMsoFormula::InSet { var, set_var }),
        (arb_var(), arb_var())
            .prop_map(|(var, set_var)| WeightedMsoFormula::NotInSet { var, set_var }),
    ];
    if depth == 0 {
        leaf.boxed()
    } else {
        prop_oneof![
            leaf,
            (arb_mso_formula(depth - 1), arb_mso_formula(depth - 1))
                .prop_map(|(a, b)| WeightedMsoFormula::And(Box::new(a), Box::new(b))),
            (arb_mso_formula(depth - 1), arb_mso_formula(depth - 1))
                .prop_map(|(a, b)| WeightedMsoFormula::Or(Box::new(a), Box::new(b))),
            (arb_var(), arb_mso_formula(depth - 1)).prop_map(|(var, body)| {
                WeightedMsoFormula::ExistsFirst { var, body: Box::new(body) }
            }),
            (arb_var(), arb_mso_formula(depth - 1)).prop_map(|(var, body)| {
                WeightedMsoFormula::ForallFirst { var, body: Box::new(body) }
            }),
            (arb_var(), arb_mso_formula(depth - 1)).prop_map(|(var, body)| {
                WeightedMsoFormula::ExistsSecond { var, body: Box::new(body) }
            }),
            (arb_var(), arb_mso_formula(depth - 1)).prop_map(|(var, body)| {
                WeightedMsoFormula::ForallSecond { var, body: Box::new(body) }
            }),
        ]
        .boxed()
    }
}

// ── Arbitrary signature generator ─────────────────────────────────────

fn arb_signature() -> impl Strategy<Value = PredicateSignature> {
    (0u16..=PredicateSignature::ALL).prop_map(PredicateSignature::from_raw)
}

// ── Properties ────────────────────────────────────────────────────────

proptest! {
    /// P1: extract_features always includes base modules (Theorem 3.2).
    #[test]
    fn prop_extract_always_includes_base(
        expr in arb_predicate_expr(3),
        ctx in arb_channel_context(),
    ) {
        let profile = extract_features(&expr, &ctx);
        prop_assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC),
            "M1 (Symbolic) must always be present");
        prop_assert!(profile.signature.contains(PredicateSignature::M10_MSO),
            "M10 (MSO) must always be present");
    }

    /// P2: extract_features_mso always includes base modules.
    #[test]
    fn prop_extract_mso_always_includes_base(
        formula in arb_mso_formula(3),
        ctx in arb_channel_context(),
    ) {
        let profile = extract_features_mso(&formula, &ctx);
        prop_assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
        prop_assert!(profile.signature.contains(PredicateSignature::M10_MSO));
    }

    /// P3: Signature union is idempotent (a ∪ a = a).
    #[test]
    fn prop_signature_union_idempotent(sig in arb_signature()) {
        prop_assert_eq!(sig.union(sig), sig);
    }

    /// P4: Signature union is commutative (a ∪ b = b ∪ a).
    #[test]
    fn prop_signature_union_commutative(a in arb_signature(), b in arb_signature()) {
        prop_assert_eq!(a.union(b), b.union(a));
    }

    /// P5: Signature union is associative ((a ∪ b) ∪ c = a ∪ (b ∪ c)).
    #[test]
    fn prop_signature_union_associative(
        a in arb_signature(),
        b in arb_signature(),
        c in arb_signature(),
    ) {
        prop_assert_eq!(a.union(b).union(c), a.union(b.union(c)));
    }

    /// P6: count() = popcount of raw bits.
    #[test]
    fn prop_signature_count_is_popcount(sig in arb_signature()) {
        prop_assert_eq!(sig.count(), sig.raw().count_ones());
    }

    /// P7: contains() is consistent with raw bit test.
    #[test]
    fn prop_signature_contains_consistent(
        sig in arb_signature(),
        bit_idx in 0u32..PredicateSignature::NUM_MODULES,
    ) {
        let module_bit = PredicateSignature::module_bit(bit_idx);
        prop_assert_eq!(sig.contains(module_bit), sig.raw() & module_bit != 0);
    }

    /// P8: set() is monotonic — only adds bits, never removes.
    #[test]
    fn prop_signature_set_monotonic(
        initial in arb_signature(),
        bit_idx in 0u32..PredicateSignature::NUM_MODULES,
    ) {
        let mut sig = initial;
        sig.set(PredicateSignature::module_bit(bit_idx));
        // All bits from initial should still be set
        for i in 0..PredicateSignature::NUM_MODULES {
            if initial.contains(PredicateSignature::module_bit(i)) {
                prop_assert!(sig.contains(PredicateSignature::module_bit(i)),
                    "set() should not clear bit {}", i);
            }
        }
        // The new bit should be set
        prop_assert!(sig.contains(PredicateSignature::module_bit(bit_idx)));
    }

    /// P9: SFA accepts all non-zero signatures (completeness).
    #[test]
    fn prop_sfa_accepts_nonzero(bits in 1u16..=PredicateSignature::ALL) {
        let sfa = build_dispatch_sfa();
        let sig = PredicateSignature::from_raw(bits);
        prop_assert!(sfa.accepts(&[sig]),
            "SFA should accept non-zero signature 0x{:04X}", bits);
    }

    /// P10: SFA rejects zero signature.
    #[test]
    fn prop_sfa_rejects_zero(_dummy in 0u8..1u8) {
        let sfa = build_dispatch_sfa();
        prop_assert!(!sfa.accepts(&[PredicateSignature::from_raw(0)]));
    }

    /// P11: DispatchAlgebra evaluates HasBit correctly.
    #[test]
    fn prop_algebra_has_bit_eval(
        sig in arb_signature(),
        bit_idx in 0u32..PredicateSignature::NUM_MODULES,
    ) {
        let alg = DispatchAlgebra;
        let module_bit = PredicateSignature::module_bit(bit_idx);
        let pred = SignaturePred::HasBit(module_bit);
        prop_assert_eq!(
            alg.evaluate(&pred, &sig),
            sig.contains(module_bit)
        );
    }

    /// P12: DispatchAlgebra witness satisfies its predicate.
    #[test]
    fn prop_algebra_witness_satisfies(bit_idx in 0u32..PredicateSignature::NUM_MODULES) {
        let alg = DispatchAlgebra;
        let pred = SignaturePred::HasBit(PredicateSignature::module_bit(bit_idx));
        if let Some(w) = alg.witness(&pred) {
            prop_assert!(alg.evaluate(&pred, &w),
                "witness should satisfy the predicate");
        }
    }

    /// P13: GrammarDispatchPlan.requires() is consistent with aggregate signature.
    #[test]
    fn prop_plan_requires_consistent(bits in 0u16..=PredicateSignature::ALL) {
        let plan = GrammarDispatchPlan {
            aggregate_signature: PredicateSignature::from_raw(bits),
            predicate_profiles: Vec::new(),
            module_schedule: Vec::new(),
            modules_skipped: 0,
        };
        for module in &ModuleId::ALL {
            prop_assert_eq!(
                plan.requires(*module),
                PredicateSignature::from_raw(bits).contains(module.bit()),
                "requires() mismatch for {}", module
            );
        }
    }

    /// P14: Feature extraction is monotonic under formula growth.
    /// Adding a sub-formula can only add module bits, never remove them.
    #[test]
    fn prop_extract_monotonic_and(
        a in arb_predicate_expr(2),
        b in arb_predicate_expr(2),
        ctx in arb_channel_context(),
    ) {
        let profile_a = extract_features(&a, &ctx);
        let combined = PredicateExpr::And(Box::new(a), Box::new(b.clone()));
        let profile_combined = extract_features(&combined, &ctx);
        // Combined should have at least all bits of a
        let a_bits = profile_a.signature.raw();
        let combined_bits = profile_combined.signature.raw();
        prop_assert_eq!(
            combined_bits & a_bits, a_bits,
            "And should preserve all bits from left operand"
        );
    }

    /// P15: intersection(a, a) = a (idempotent).
    #[test]
    fn prop_signature_intersection_idempotent(sig in arb_signature()) {
        prop_assert_eq!(sig.intersection(sig), sig);
    }

    /// P16: union with BASE is superset of BASE.
    #[test]
    fn prop_union_with_base_includes_base(sig in arb_signature()) {
        let base = PredicateSignature::new();
        let result = sig.union(base);
        prop_assert!(result.contains(PredicateSignature::M1_SYMBOLIC));
        prop_assert!(result.contains(PredicateSignature::M10_MSO));
    }

    // ── Sprint 4e: Grammar heuristic proptest properties ────────────

    /// P17: Grammar dispatch always includes BASE (M1+M10).
    #[test]
    fn prop_classify_grammar_always_includes_base(
        grammar in arb_grammar(),
    ) {
        let plan = classify_grammar(&grammar, &[]);
        prop_assert!(plan.aggregate_signature.contains(PredicateSignature::M1_SYMBOLIC),
            "grammar dispatch must always include M1");
        prop_assert!(plan.aggregate_signature.contains(PredicateSignature::M10_MSO),
            "grammar dispatch must always include M10");
    }

    /// P18: Grammar dispatch is monotonic under rule addition.
    #[test]
    fn prop_classify_grammar_monotonic(
        base_grammar in arb_grammar(),
        extra_rule in arb_grammar_rule(),
    ) {
        let plan_base = classify_grammar(&base_grammar, &[]);
        let mut extended = base_grammar.clone();
        extended.push(extra_rule);
        let plan_extended = classify_grammar(&extended, &[]);
        let base_bits = plan_base.aggregate_signature.raw();
        let ext_bits = plan_extended.aggregate_signature.raw();
        prop_assert_eq!(ext_bits & base_bits, base_bits,
            "adding a rule must not remove module bits");
    }

    /// P19: Recursive grammar always activates M2 (Büchi).
    #[test]
    fn prop_recursive_implies_buchi(category in arb_category()) {
        let rule = (
            "r".to_string(),
            category.clone(),
            vec![SyntaxItemSpec::NonTerminal {
                category, param_name: "x".to_string(),
            }],
        );
        let plan = classify_grammar(&[rule], &[]);
        prop_assert!(plan.requires(ModuleId::Buchi),
            "recursive category must activate Büchi");
    }

    /// P20: Paired brackets always activate M4 (VPA).
    #[test]
    fn prop_brackets_implies_vpa(
        open_idx in 0usize..3,
        close_idx in 0usize..3,
    ) {
        let opens = ["(", "{", "["];
        let closes = [")", "}", "]"];
        let grammar = vec![
            ("R".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal(opens[open_idx].to_string()),
                SyntaxItemSpec::Terminal(closes[close_idx].to_string()),
            ]),
        ];
        let plan = classify_grammar(&grammar, &[]);
        prop_assert!(plan.requires(ModuleId::Vpa),
            "paired brackets must activate VPA");
    }

    /// P21: Binder items always activate M6 (Register).
    #[test]
    fn prop_binder_implies_register(cat in arb_category()) {
        let grammar = vec![
            ("R".to_string(), cat.clone(), vec![
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: cat,
                    is_multi: false,
                },
            ]),
        ];
        let plan = classify_grammar(&grammar, &[]);
        prop_assert!(plan.requires(ModuleId::Register),
            "binder must activate Register");
    }

    /// P22: ≥3 same-category rules always activate M7 (Probabilistic).
    #[test]
    fn prop_ambiguity_implies_probabilistic(cat in arb_category()) {
        let grammar = vec![
            ("R1".to_string(), cat.clone(), vec![SyntaxItemSpec::Terminal("a".to_string())]),
            ("R2".to_string(), cat.clone(), vec![SyntaxItemSpec::Terminal("b".to_string())]),
            ("R3".to_string(), cat, vec![SyntaxItemSpec::Terminal("c".to_string())]),
        ];
        let plan = classify_grammar(&grammar, &[]);
        prop_assert!(plan.requires(ModuleId::Probabilistic),
            "≥3 same-category rules must activate Probabilistic");
    }

    /// P23: Module schedule is sorted by cost.
    #[test]
    fn prop_schedule_ordered_by_cost(grammar in arb_grammar()) {
        let plan = classify_grammar(&grammar, &[]);
        for window in plan.module_schedule.windows(2) {
            prop_assert!(window[0].estimated_cost() <= window[1].estimated_cost(),
                "schedule must be sorted: {} vs {}", window[0], window[1]);
        }
    }

    /// P24: classify_grammar is deterministic.
    #[test]
    fn prop_classify_grammar_deterministic(grammar in arb_grammar()) {
        let plan1 = classify_grammar(&grammar, &[]);
        let plan2 = classify_grammar(&grammar, &[]);
        prop_assert_eq!(plan1.aggregate_signature, plan2.aggregate_signature,
            "same grammar must produce same signature");
    }

    /// P25: Conservative approximation — grammar dispatch activates a
    /// superset of predicate-level dispatch for base predicates.
    #[test]
    fn prop_grammar_superset_of_predicate(grammar in arb_grammar()) {
        let plan = classify_grammar(&grammar, &[]);
        let ctx = ChannelContext::new();
        let base_profile = extract_features(&PredicateExpr::True, &ctx);
        let grammar_bits = plan.aggregate_signature.raw();
        let predicate_bits = base_profile.signature.raw();
        prop_assert_eq!(grammar_bits & predicate_bits, predicate_bits,
            "grammar dispatch must be superset of predicate dispatch");
    }

    // ── Sprint 4f: Fixpoint detection proptest properties ───────────

    /// P26: Fixpoint relations always activate M4+M5.
    #[test]
    fn prop_fixpoint_activates_vpa_parity(
        name_idx in 0usize..6,
    ) {
        let names = ["letprop", "fixpoint", "mu", "nu", "letrec", "recursive"];
        let expr = PredicateExpr::Relation {
            name: names[name_idx].to_string(),
            args: vec!["x".to_string()],
        };
        let profile = extract_features(&expr, &ChannelContext::new());
        prop_assert!(profile.signature.contains(PredicateSignature::M4_VPA),
            "{} must activate M4", names[name_idx]);
        prop_assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
            "{} must activate M5", names[name_idx]);
        prop_assert!(profile.has_recursive_predicate,
            "{} must set has_recursive_predicate", names[name_idx]);
    }

    /// P27: Non-fixpoint relations never activate M4/M5.
    #[test]
    fn prop_non_fixpoint_no_vpa(
        name_idx in 0usize..5,
    ) {
        let names = ["eq", "neq", "count", "size", "custom_check"];
        let expr = PredicateExpr::Relation {
            name: names[name_idx].to_string(),
            args: vec!["x".to_string()],
        };
        let profile = extract_features(&expr, &ChannelContext::new());
        prop_assert!(!profile.signature.contains(PredicateSignature::M4_VPA),
            "{} must not activate M4", names[name_idx]);
        prop_assert!(!profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
            "{} must not activate M5", names[name_idx]);
    }

    // ── order_by_specificity properties ──────────────────────────────

    /// P28: order_by_specificity output is a permutation of the input
    /// (same elements, same count).
    #[test]
    fn prop_specificity_preserves_all_labels(
        n in 2usize..=6,
        pair_indices in prop::collection::vec((0usize..6, 0usize..6), 0..=10),
    ) {
        let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
        let subsumed_guards: Vec<(String, String)> = pair_indices
            .into_iter()
            .filter(|(a, b)| *a < n && *b < n && a != b)
            .map(|(a, b)| (format!("P{}", a), format!("P{}", b)))
            .collect();

        let result = order_by_specificity(&labels, &subsumed_guards);

        // Same length
        prop_assert_eq!(result.len(), labels.len(),
            "output length must match input length");

        // Same multiset of elements
        let mut sorted_input = labels.clone();
        sorted_input.sort();
        let mut sorted_output = result.clone();
        sorted_output.sort();
        prop_assert_eq!(sorted_output, sorted_input,
            "output must be a permutation of input");
    }

    /// P29: When subsumed_guards is empty, the output order is identical
    /// to the input order.
    #[test]
    fn prop_no_subsumption_preserves_order(n in 2usize..=6) {
        let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
        let result = order_by_specificity(&labels, &[]);
        prop_assert_eq!(result, labels,
            "empty subsumption must preserve original order");
    }

    /// P30: If (a,b) is in subsumed_guards and both a and b are in the
    /// input labels, then a appears before b in the output.
    #[test]
    fn prop_subsumed_before_subsumer(
        n in 2usize..=6,
        a_idx in 0usize..6,
        b_idx in 0usize..6,
    ) {
        prop_assume!(a_idx < n && b_idx < n && a_idx != b_idx);
        let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
        let a = format!("P{}", a_idx);
        let b = format!("P{}", b_idx);
        let subsumed_guards = vec![(a.clone(), b.clone())];

        let result = order_by_specificity(&labels, &subsumed_guards);
        let pos_a = result.iter().position(|l| *l == a)
            .expect("a must be in output");
        let pos_b = result.iter().position(|l| *l == b)
            .expect("b must be in output");
        prop_assert!(pos_a < pos_b,
            "subsumed label {} (pos {}) must appear before subsumer {} (pos {})",
            a, pos_a, b, pos_b);
    }

    /// P31: If (a,b), (b,c), and (a,c) are in subsumed_guards, then the
    /// output order is a, b, c (from most to least specific). The extra
    /// pair (a,c) ensures a has score 2 > b's score 1 > c's score 0,
    /// giving a strict specificity chain.
    #[test]
    fn prop_transitivity_ordering(
        n in 3usize..=6,
        a_idx in 0usize..6,
        b_idx in 0usize..6,
        c_idx in 0usize..6,
    ) {
        prop_assume!(a_idx < n && b_idx < n && c_idx < n);
        prop_assume!(a_idx != b_idx && b_idx != c_idx && a_idx != c_idx);
        let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
        let a = format!("P{}", a_idx);
        let b = format!("P{}", b_idx);
        let c = format!("P{}", c_idx);
        // (a,b) + (b,c) + (a,c): a has score 2, b has score 1, c has score 0
        let subsumed_guards = vec![
            (a.clone(), b.clone()),
            (b.clone(), c.clone()),
            (a.clone(), c.clone()),
        ];

        let result = order_by_specificity(&labels, &subsumed_guards);
        let pos_a = result.iter().position(|l| *l == a)
            .expect("a must be in output");
        let pos_b = result.iter().position(|l| *l == b)
            .expect("b must be in output");
        let pos_c = result.iter().position(|l| *l == c)
            .expect("c must be in output");
        prop_assert!(pos_a < pos_b,
            "a ({}) at {} must precede b ({}) at {}", a, pos_a, b, pos_b);
        prop_assert!(pos_b < pos_c,
            "b ({}) at {} must precede c ({}) at {}", b, pos_b, c, pos_c);
    }

    /// P32: Labels with higher specificity score (more subsumption pairs
    /// where they are the subsumed element) appear earlier in the output.
    #[test]
    fn prop_specificity_score_monotone(
        n in 2usize..=6,
        pair_indices in prop::collection::vec((0usize..6, 0usize..6), 0..=10),
    ) {
        let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
        let subsumed_guards: Vec<(String, String)> = pair_indices
            .into_iter()
            .filter(|(a, b)| *a < n && *b < n && a != b)
            .map(|(a, b)| (format!("P{}", a), format!("P{}", b)))
            .collect();

        // Compute specificity scores (same algorithm as the function)
        let mut scores: HashMap<String, usize> = HashMap::new();
        for label in &labels {
            scores.insert(label.clone(), 0);
        }
        for (subsumed, _) in &subsumed_guards {
            if let Some(count) = scores.get_mut(subsumed) {
                *count += 1;
            }
        }

        let result = order_by_specificity(&labels, &subsumed_guards);

        // For every pair of labels in the result, if one has a strictly
        // higher specificity score, it must appear earlier.
        for i in 0..result.len() {
            for j in (i + 1)..result.len() {
                let score_i = scores[&result[i]];
                let score_j = scores[&result[j]];
                prop_assert!(score_i >= score_j,
                    "label {} (score {}) at position {} must not follow \
                     label {} (score {}) at position {}",
                    result[i], score_i, i, result[j], score_j, j);
            }
        }
    }
}

// ── Grammar generators for proptest ──────────────────────────────────

fn arb_category() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "Expr".to_string(),
        "Term".to_string(),
        "Stmt".to_string(),
        "Type".to_string(),
    ])
}

fn arb_syntax_item() -> impl Strategy<Value = SyntaxItemSpec> {
    prop_oneof![
        prop::sample::select(vec!["(", ")", "{", "}", "[", "]", "+", "-", ";", "let", "in",])
            .prop_map(|s| SyntaxItemSpec::Terminal(s.to_string())),
        (arb_category(), arb_var()).prop_map(|(cat, param)| SyntaxItemSpec::NonTerminal {
            category: cat,
            param_name: param,
        }),
        (arb_var(), arb_category()).prop_map(|(param, cat)| SyntaxItemSpec::Binder {
            param_name: param,
            category: cat,
            is_multi: false,
        }),
        (arb_var(), arb_category()).prop_map(|(param, cat)| SyntaxItemSpec::Collection {
            param_name: param,
            element_category: cat,
            separator: ",".to_string(),
            kind: crate::grammar::ir::CollectionKind::Vec,
            key_val_separator: None,
        }),
    ]
}

fn arb_grammar_rule() -> impl Strategy<Value = (String, String, Vec<SyntaxItemSpec>)> {
    (arb_var(), arb_category(), prop::collection::vec(arb_syntax_item(), 1..=6))
        .prop_map(|(label, cat, items)| (label, cat, items))
}

fn arb_grammar() -> impl Strategy<Value = Vec<(String, String, Vec<SyntaxItemSpec>)>> {
    prop::collection::vec(arb_grammar_rule(), 1..=8)
}

// ══════════════════════════════════════════════════════════════════════
// Cleanup property tests (Phases A, B, C, F — bypass model invariants)
// ══════════════════════════════════════════════════════════════════════
//
// These properties formalize the soundness theorem from
// docs/design/dispatch/predicate-dispatch-integration.md §6.

use crate::{GuardConfigSpec, TheoryRegistrationSpec};

/// Build a `GuardConfigSpec` with a single theory registration of the
/// given type. Used to test bypass behavior.
fn make_theory_config(theory_type: &str) -> GuardConfigSpec {
    GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "test".to_string(),
            theory_type: theory_type.to_string(),
            handled_types: None,
        }],
        ..Default::default()
    }
}

proptest! {
    /// Cleanup F: Backward compatibility invariant.
    ///
    /// For any grammar G, classify_grammar_with_config(G, ∅, None) is
    /// identical to classify_grammar(G, ∅). The 2-arg form is a strict
    /// alias for the 3-arg form with `None`.
    #[test]
    fn prop_cleanup_backward_compat_invariant(grammar in arb_grammar()) {
        let plan_old = classify_grammar(&grammar, &[]);
        let plan_new = classify_grammar_with_config(&grammar, &[], None);
        prop_assert_eq!(plan_old.aggregate_signature, plan_new.aggregate_signature);
    }

    /// Cleanup F: Bypass monotonicity (theory side).
    ///
    /// For any grammar G and any theory of a known kind T,
    /// adding T to the guard config can only *remove* heuristic
    /// activations of the corresponding module — the explicit-theory
    /// block re-adds the same bit. The net effect on the bypassed
    /// module bit is "removed from heuristic side, added on explicit
    /// side" (a wash). All other bits are unchanged or differ only on
    /// other gated bits.
    ///
    /// Concrete property: for the three "always-explicit-active"
    /// theories (Presburger, Unification, Lattice), registering them
    /// always activates the corresponding bit.
    #[test]
    fn prop_cleanup_explicit_theory_always_activates_module(
        grammar in arb_grammar(),
    ) {
        // Presburger
        let gc = make_theory_config("PresburgerAlgebra");
        let plan = classify_grammar_with_config(&grammar, &[], Some(&gc));
        prop_assert!(
            plan.aggregate_signature.contains(PredicateSignature::M12_LINEAR_ARITHMETIC),
            "explicit Presburger registration must always activate M12"
        );

        // Unification
        let gc = make_theory_config("UnificationTheory");
        let plan = classify_grammar_with_config(&grammar, &[], Some(&gc));
        prop_assert!(
            plan.aggregate_signature.contains(PredicateSignature::M13_UNIFICATION),
            "explicit Unification registration must always activate M13"
        );

        // Lattice
        let gc = make_theory_config("LatticeTheory");
        let plan = classify_grammar_with_config(&grammar, &[], Some(&gc));
        prop_assert!(
            plan.aggregate_signature.contains(PredicateSignature::M14_SUBTYPE_LATTICE),
            "explicit Lattice registration must always activate M14"
        );
    }

    /// Cleanup F: Channel determinism.
    ///
    /// For any grammar G and any channel-config-only guard config C
    /// (no theories), the M8/M11 bits in
    /// classify_grammar_with_config(G, ∅, Some(C)) are determined
    /// entirely by C, not by G's structural shape. Specifically: an
    /// empty `channel_categories` declaration disables both M8 and
    /// M11 from the heuristic side.
    #[test]
    fn prop_cleanup_explicit_empty_channels_silences_structural_m8_m11(
        grammar in arb_grammar(),
    ) {
        let gc = GuardConfigSpec {
            channel_categories: Some(Vec::new()),
            join_patterns: Vec::new(),
            ..Default::default()
        };
        let plan = classify_grammar_with_config(&grammar, &[], Some(&gc));
        prop_assert!(
            !plan.aggregate_signature.contains(PredicateSignature::M8_MULTI_TAPE),
            "empty channels {{}} → M8 must not fire from cross-cat heuristic"
        );
        prop_assert!(
            !plan.aggregate_signature.contains(PredicateSignature::M11_TWO_WAY),
            "empty channels {{}} → M11 must not fire from cross-cat heuristic"
        );
    }

    /// Cleanup F: Theory bypass disables corresponding terminal heuristic.
    ///
    /// For any grammar G whose terminals contain `+` (which would
    /// otherwise trigger the M12 heuristic), registering Presburger
    /// must bypass the heuristic. The terminal scan no longer fires;
    /// M12 is set only by the explicit theory block.
    ///
    /// (We can't directly observe "M12 came from heuristic vs explicit,"
    /// but we can observe that: the configured signature has M12,
    /// AND the configured signature without theories does NOT have
    /// the additional bits the heuristic would set. Since the explicit
    /// theory is the only thing that adds M12 in the configured run,
    /// and the bit is present, the bypass+activation chain is correct.)
    #[test]
    fn prop_cleanup_extract_features_with_config_subset(
        relation_name in prop::sample::select(vec![
            "eq", "neq", "fresh", "count", "size", "letprop",
            "gt", "lt", "match", "unify", "subtype",
        ])
    ) {
        // For a single-relation predicate with a "named" relation,
        // registering all known theory kinds simultaneously must
        // produce a configured signature ⊆ unconfigured signature
        // (with respect to the gated bits).
        let expr = PredicateExpr::Relation {
            name: relation_name.to_string(),
            args: vec!["x".to_string(), "y".to_string()],
        };
        let ctx = ChannelContext::new();
        let unconfigured = extract_features(&expr, &ctx);

        let gc = GuardConfigSpec {
            theories: vec![
                TheoryRegistrationSpec {
                    name: "p".to_string(),
                    theory_type: "PresburgerAlgebra".to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "u".to_string(),
                    theory_type: "UnificationTheory".to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "l".to_string(),
                    theory_type: "LatticeTheory".to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "r".to_string(),
                    theory_type: "RegisterTheory".to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "m".to_string(),
                    theory_type: "MultisetTheory".to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "f".to_string(),
                    theory_type: "FixpointTheory".to_string(),
                    handled_types: None,
                },
            ],
            ..Default::default()
        };
        let configured = extract_features_with_config(&expr, &ctx, Some(&gc));

        // The bypassed bits — the ones each registered theory silences:
        // M6 (Register), M9 (Multiset), M4/M5 (Fixpoint), M12, M13, M14.
        let bypassed_bits = [
            PredicateSignature::M6_REGISTER,
            PredicateSignature::M9_MULTISET,
            PredicateSignature::M4_VPA,
            PredicateSignature::M5_PARITY_TREE,
            PredicateSignature::M12_LINEAR_ARITHMETIC,
            PredicateSignature::M13_UNIFICATION,
            PredicateSignature::M14_SUBTYPE_LATTICE,
        ];
        for bit in bypassed_bits {
            if unconfigured.signature.contains(bit) {
                // The configured run can EITHER not have this bit
                // (heuristic silenced) OR still have it from the
                // explicit theory block in classify_grammar_with_config
                // — but extract_features_with_config doesn't run that
                // block, so the bit must be SILENCED here.
                prop_assert!(
                    !configured.signature.contains(bit),
                    "bit {:?} should be silenced by full theory registration \
                     (was set heuristically for relation `{}`)",
                    bit, relation_name
                );
            }
        }
    }

    /// Cleanup F: theory_registered is monotone in the theory list.
    ///
    /// Adding a theory of any kind to a guard config can only
    /// transition `theory_registered(gc, K)` from false to true,
    /// never the reverse, for that K.
    #[test]
    fn prop_cleanup_theory_registered_monotone(
        base_theory in prop::sample::select(vec![
            "PresburgerAlgebra", "UnificationTheory", "LatticeTheory",
            "RegisterTheory", "MultisetTheory", "FixpointTheory",
        ]),
        added_theory in prop::sample::select(vec![
            "PresburgerAlgebra", "UnificationTheory", "LatticeTheory",
            "RegisterTheory", "MultisetTheory", "FixpointTheory",
        ]),
    ) {
        let gc_base = GuardConfigSpec {
            theories: vec![TheoryRegistrationSpec {
                name: "a".to_string(),
                theory_type: base_theory.to_string(),
                handled_types: None,
            }],
            ..Default::default()
        };
        let gc_extended = GuardConfigSpec {
            theories: vec![
                TheoryRegistrationSpec {
                    name: "a".to_string(),
                    theory_type: base_theory.to_string(),
                    handled_types: None,
                },
                TheoryRegistrationSpec {
                    name: "b".to_string(),
                    theory_type: added_theory.to_string(),
                    handled_types: None,
                },
            ],
            ..Default::default()
        };

        // Every kind that was registered in the base remains registered
        // in the extended config.
        for kind in [
            TheoryKind::Presburger,
            TheoryKind::Unification,
            TheoryKind::Lattice,
            TheoryKind::Register,
            TheoryKind::Multiset,
            TheoryKind::Fixpoint,
        ] {
            if theory_registered(Some(&gc_base), kind) {
                prop_assert!(
                    theory_registered(Some(&gc_extended), kind),
                    "theory_registered must be monotone: kind {:?} lost",
                    kind
                );
            }
        }
    }
}
