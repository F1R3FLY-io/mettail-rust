use super::*;

// ── PredicateSignature tests ──────────────────────────────────────────

#[test]
fn test_signature_base_contains_m1_and_m10() {
    let sig = PredicateSignature::new();
    assert!(sig.contains(PredicateSignature::M1_SYMBOLIC));
    assert!(sig.contains(PredicateSignature::M10_MSO));
    assert!(!sig.contains(PredicateSignature::M2_BUCHI));
    assert_eq!(sig.count(), 2);
}

#[test]
fn test_signature_union() {
    let a = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
    let b = PredicateSignature::from_raw(PredicateSignature::M6_REGISTER);
    let c = a.union(b);
    assert!(c.contains(PredicateSignature::M1_SYMBOLIC));
    assert!(c.contains(PredicateSignature::M6_REGISTER));
    assert_eq!(c.count(), 2);
}

#[test]
fn test_signature_is_base_only() {
    assert!(PredicateSignature::new().is_base_only());
    let mut sig = PredicateSignature::new();
    sig.set(PredicateSignature::M3_AWA);
    assert!(!sig.is_base_only());
}

#[test]
fn test_signature_is_full() {
    let sig = PredicateSignature::from_raw(PredicateSignature::ALL);
    assert!(sig.is_full());
    assert!(!PredicateSignature::new().is_full());
}

#[test]
fn test_signature_display() {
    let sig = PredicateSignature::new();
    let s = format!("{sig}");
    assert!(s.contains("M1:Sym"));
    assert!(s.contains("M10:MSO"));
}

// ── ModuleId tests ────────────────────────────────────────────────────

#[test]
fn test_module_id_bits_are_distinct() {
    let bits: Vec<u16> = ModuleId::ALL.iter().map(|m| m.bit()).collect();
    let unique: HashSet<u16> = bits.iter().copied().collect();
    assert_eq!(bits.len(), unique.len(), "all module bits should be distinct");
}

#[test]
fn test_module_id_count() {
    assert_eq!(ModuleId::ALL.len(), 15);
}

#[test]
fn test_module_id_new_modules_have_correct_bits() {
    assert_eq!(ModuleId::LinearArithmetic.bit(), PredicateSignature::M12_LINEAR_ARITHMETIC);
    assert_eq!(ModuleId::Unification.bit(), PredicateSignature::M13_UNIFICATION);
    assert_eq!(ModuleId::SubtypeLattice.bit(), PredicateSignature::M14_SUBTYPE_LATTICE);
}

#[test]
fn test_module_id_new_feature_gates() {
    assert_eq!(ModuleId::LinearArithmetic.feature_gate(), "presburger");
    assert_eq!(ModuleId::Unification.feature_gate(), "unification");
    assert_eq!(ModuleId::SubtypeLattice.feature_gate(), "lattice-theory");
}

#[test]
fn test_module_id_new_cost_tiers() {
    assert_eq!(ModuleId::LinearArithmetic.estimated_cost(), 3);
    assert_eq!(ModuleId::Unification.estimated_cost(), 3);
    assert_eq!(ModuleId::SubtypeLattice.estimated_cost(), 2);
}

// ── extract_features: PredicateExpr tests ─────────────────────────────

#[test]
fn test_extract_atom_base_only() {
    let expr = PredicateExpr::Atom("p".to_string());
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.is_base_only(), "Atom should activate only M1+M10");
    assert_eq!(profile.quantifier_depth, 0);
}

#[test]
fn test_extract_true_base_only() {
    let expr = PredicateExpr::True;
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.is_base_only());
}

#[test]
fn test_extract_false_base_only() {
    let expr = PredicateExpr::False;
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.is_base_only());
}

#[test]
fn test_extract_forall_infinite_triggers_m2_m3() {
    let expr = PredicateExpr::ForallInfinite {
        var: "x".to_string(),
        body: Box::new(PredicateExpr::Atom("p".to_string())),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI), "ForallInfinite → M2");
    assert!(profile.signature.contains(PredicateSignature::M3_AWA), "ForallInfinite → M3");
    assert_eq!(profile.quantifier_depth, 1);
}

#[test]
fn test_extract_exists_infinite_triggers_m2() {
    let expr = PredicateExpr::ExistsInfinite {
        var: "x".to_string(),
        body: Box::new(PredicateExpr::True),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI), "ExistsInfinite → M2");
    assert!(
        !profile.signature.contains(PredicateSignature::M3_AWA),
        "ExistsInfinite should NOT set M3"
    );
}

#[test]
fn test_extract_forall_finite_triggers_m3() {
    let expr = PredicateExpr::ForallFinite {
        var: "x".to_string(),
        domain: vec!["a".to_string(), "b".to_string()],
        body: Box::new(PredicateExpr::True),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M3_AWA), "ForallFinite → M3");
    assert!(
        !profile.signature.contains(PredicateSignature::M2_BUCHI),
        "ForallFinite should NOT set M2"
    );
}

#[test]
fn test_extract_exists_finite_no_extra_modules() {
    let expr = PredicateExpr::ExistsFinite {
        var: "x".to_string(),
        domain: vec!["a".to_string()],
        body: Box::new(PredicateExpr::True),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.is_base_only(), "ExistsFinite should only be base");
    assert_eq!(profile.quantifier_depth, 1);
}

#[test]
fn test_extract_equality_relation_triggers_m6() {
    let expr = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER), "eq relation → M6");
    assert_eq!(profile.register_count, 2);
}

#[test]
fn test_extract_cardinality_relation_triggers_m9() {
    let expr = PredicateExpr::Relation {
        name: "count".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M9_MULTISET), "count → M9");
    assert!(profile.has_cardinality);
}

#[test]
fn test_extract_cross_channel_triggers_m8_m11() {
    let expr = PredicateExpr::Relation {
        name: "related".to_string(),
        args: vec!["x".to_string()],
    };
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.set_current_channel("ch2".to_string());
    let profile = extract_features(&expr, &ctx);
    assert!(
        profile
            .signature
            .contains(PredicateSignature::M8_MULTI_TAPE),
        "cross-channel → M8"
    );
    assert!(
        profile.signature.contains(PredicateSignature::M11_TWO_WAY),
        "cross-channel → M11"
    );
    assert!(profile.has_backward_constraint);
}

#[test]
fn test_extract_multi_channel_triggers_m7() {
    // Create a conjunction referencing vars from two channels
    let expr = PredicateExpr::And(
        Box::new(PredicateExpr::Relation {
            name: "eq".to_string(),
            args: vec!["x".to_string()],
        }),
        Box::new(PredicateExpr::Relation {
            name: "eq".to_string(),
            args: vec!["y".to_string()],
        }),
    );
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.bind("y".to_string(), "ch2".to_string());
    let profile = extract_features(&expr, &ctx);
    assert!(
        profile
            .signature
            .contains(PredicateSignature::M7_PROBABILISTIC),
        "≥2 channels → M7"
    );
    assert_eq!(profile.channel_count, 2);
}

#[test]
fn test_extract_deeply_nested() {
    // ∀x. ∃y. ∀∞z. p(x, y, z)
    let expr = PredicateExpr::ForallFinite {
        var: "x".to_string(),
        domain: vec!["a".to_string()],
        body: Box::new(PredicateExpr::ExistsFinite {
            var: "y".to_string(),
            domain: vec!["b".to_string()],
            body: Box::new(PredicateExpr::ForallInfinite {
                var: "z".to_string(),
                body: Box::new(PredicateExpr::Atom("p".to_string())),
            }),
        }),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert_eq!(profile.quantifier_depth, 3);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
}

#[test]
fn test_extract_all_morphemes() {
    // A predicate combining all morpheme types
    let expr = PredicateExpr::ForallInfinite {
        var: "z".to_string(),
        body: Box::new(PredicateExpr::And(
            Box::new(PredicateExpr::Relation {
                name: "eq".to_string(),
                args: vec!["x".to_string()],
            }),
            Box::new(PredicateExpr::Relation {
                name: "count".to_string(),
                args: vec!["y".to_string()],
            }),
        )),
    };
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.bind("y".to_string(), "ch2".to_string());
    ctx.set_current_channel("ch3".to_string());
    let profile = extract_features(&expr, &ctx);

    assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    assert!(profile
        .signature
        .contains(PredicateSignature::M7_PROBABILISTIC));
    assert!(profile
        .signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
    assert!(profile.signature.contains(PredicateSignature::M9_MULTISET));
    assert!(profile.signature.contains(PredicateSignature::M10_MSO));
    assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
}

#[test]
fn test_extract_bounded_body() {
    let expr = PredicateExpr::Bounded {
        body: Box::new(PredicateExpr::ForallInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::Atom("p".to_string())),
        }),
        bound: 100,
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
}

#[test]
fn test_extract_not_propagates() {
    let expr = PredicateExpr::Not(Box::new(PredicateExpr::ForallInfinite {
        var: "x".to_string(),
        body: Box::new(PredicateExpr::True),
    }));
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
}

// ── M12/M13/M14 extraction tests ───────────────────────────────────

#[test]
fn test_extract_arithmetic_relation_triggers_m12() {
    for name in ["add", "sub", "gt", "le", "bounded", "range"] {
        let expr = PredicateExpr::Relation {
            name: name.to_string(),
            args: vec!["x".to_string(), "y".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(
            profile
                .signature
                .contains(PredicateSignature::M12_LINEAR_ARITHMETIC),
            "'{name}' should trigger M12"
        );
        assert!(profile.has_arithmetic, "'{name}' should set has_arithmetic");
    }
}

#[test]
fn test_extract_unification_relation_triggers_m13() {
    for name in ["match", "unify", "bind", "pattern", "instantiate"] {
        let expr = PredicateExpr::Relation {
            name: name.to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(
            profile
                .signature
                .contains(PredicateSignature::M13_UNIFICATION),
            "'{name}' should trigger M13"
        );
        assert!(profile.has_unification, "'{name}' should set has_unification");
    }
}

#[test]
fn test_extract_subtype_relation_triggers_m14() {
    for name in ["subtype", ":<", "join", "meet", "exhaustive"] {
        let expr = PredicateExpr::Relation {
            name: name.to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(
            profile
                .signature
                .contains(PredicateSignature::M14_SUBTYPE_LATTICE),
            "'{name}' should trigger M14"
        );
        assert!(profile.has_subtype, "'{name}' should set has_subtype");
    }
}

#[test]
fn test_extract_unknown_relation_does_not_trigger_m12_m13_m14() {
    let expr = PredicateExpr::Relation {
        name: "some_custom_predicate".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(!profile
        .signature
        .contains(PredicateSignature::M12_LINEAR_ARITHMETIC));
    assert!(!profile
        .signature
        .contains(PredicateSignature::M13_UNIFICATION));
    assert!(!profile
        .signature
        .contains(PredicateSignature::M14_SUBTYPE_LATTICE));
    // Falls through to default M6 (Register)
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
}

#[test]
fn test_extract_comparison_overlaps_m9_m12() {
    // ">=" appears in both cardinality and arithmetic classifiers
    let expr = PredicateExpr::Relation {
        name: ">=".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M9_MULTISET), ">= triggers M9");
    assert!(
        profile
            .signature
            .contains(PredicateSignature::M12_LINEAR_ARITHMETIC),
        ">= triggers M12"
    );
    assert!(profile.has_cardinality);
    assert!(profile.has_arithmetic);
}

#[test]
fn test_signature_display_includes_new_modules() {
    let mut sig = PredicateSignature::new();
    sig.set(PredicateSignature::M12_LINEAR_ARITHMETIC);
    sig.set(PredicateSignature::M13_UNIFICATION);
    sig.set(PredicateSignature::M14_SUBTYPE_LATTICE);
    let s = format!("{sig}");
    assert!(s.contains("M12:Presb"), "display should include M12");
    assert!(s.contains("M13:Unif"), "display should include M13");
    assert!(s.contains("M14:Lat"), "display should include M14");
}

// ── extract_features_mso: WeightedMsoFormula tests ────────────────────

#[test]
fn test_mso_constant_base_only() {
    let formula = WeightedMsoFormula::Constant("c".to_string());
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.is_base_only());
}

#[test]
fn test_mso_forall_first_triggers_m3() {
    let formula = WeightedMsoFormula::ForallFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    assert_eq!(profile.quantifier_depth, 1);
}

#[test]
fn test_mso_forall_second_triggers_m3() {
    let formula = WeightedMsoFormula::ForallSecond {
        var: "X".to_string(),
        body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
}

#[test]
fn test_mso_exists_first_no_extra() {
    let formula = WeightedMsoFormula::ExistsFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.is_base_only());
    assert_eq!(profile.quantifier_depth, 1);
}

#[test]
fn test_mso_exists_second_no_extra() {
    let formula = WeightedMsoFormula::ExistsSecond {
        var: "X".to_string(),
        body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.is_base_only());
}

#[test]
fn test_mso_letprop_triggers_m4_m5() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "letprop".to_string(),
        var: "x".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA));
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
    assert!(profile.has_recursive_predicate);
}

#[test]
fn test_mso_fixpoint_triggers_m4_m5() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "fixpoint".to_string(),
        var: "x".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA));
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
}

#[test]
fn test_mso_order_triggers_m6() {
    let formula = WeightedMsoFormula::Order { x: "a".to_string(), y: "b".to_string() };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    assert_eq!(profile.register_count, 2);
}

#[test]
fn test_mso_cross_channel() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "action".to_string(),
        var: "x".to_string(),
    };
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.set_current_channel("ch2".to_string());
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile
        .signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
    assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
}

#[test]
fn test_mso_in_set_cross_channel() {
    let formula = WeightedMsoFormula::InSet {
        var: "x".to_string(),
        set_var: "S".to_string(),
    };
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.set_current_channel("ch2".to_string());
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile
        .signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
    assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
}

#[test]
fn test_mso_and_or_propagate() {
    let formula = WeightedMsoFormula::And(
        Box::new(WeightedMsoFormula::ForallFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
        }),
        Box::new(WeightedMsoFormula::Order { x: "a".to_string(), y: "b".to_string() }),
    );
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
}

// ── GrammarDispatchPlan tests ─────────────────────────────────────────

#[test]
fn test_classify_empty_grammar() {
    let plan = classify_grammar(&[], &[]);
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M1_SYMBOLIC));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M10_MSO));
}

#[test]
fn test_plan_requires_base_modules() {
    let plan = classify_grammar(&[], &[]);
    assert!(plan.requires(ModuleId::Symbolic));
    assert!(plan.requires(ModuleId::Mso));
}

#[test]
fn test_plan_skipped_modules() {
    let plan = classify_grammar(&[], &[]);
    let skipped = plan.skipped_modules();
    assert!(skipped.contains(&ModuleId::Buchi));
    assert!(skipped.contains(&ModuleId::Register));
    assert!(!skipped.contains(&ModuleId::Symbolic));
}

// ── Dispatch Algebra / SFA tests ──────────────────────────────────────

#[test]
fn test_dispatch_algebra_true_false() {
    let alg = DispatchAlgebra;
    assert!(alg.is_satisfiable(&SignaturePred::True));
    assert!(!alg.is_satisfiable(&SignaturePred::False));
}

#[test]
fn test_dispatch_algebra_has_bit() {
    let alg = DispatchAlgebra;
    let pred = SignaturePred::HasBit(PredicateSignature::M6_REGISTER);
    assert!(alg.is_satisfiable(&pred));
    let w = alg.witness(&pred).expect("should have witness");
    assert!(w.contains(PredicateSignature::M6_REGISTER));
}

#[test]
fn test_dispatch_algebra_and() {
    let alg = DispatchAlgebra;
    let p = SignaturePred::HasBit(PredicateSignature::M2_BUCHI);
    let q = SignaturePred::HasBit(PredicateSignature::M3_AWA);
    let conj = alg.and(&p, &q);
    assert!(alg.is_satisfiable(&conj));
    let w = alg.witness(&conj).expect("should have witness");
    assert!(w.contains(PredicateSignature::M2_BUCHI));
    assert!(w.contains(PredicateSignature::M3_AWA));
}

#[test]
fn test_dispatch_algebra_not() {
    let alg = DispatchAlgebra;
    let p = SignaturePred::True;
    let np = alg.not(&p);
    assert!(!alg.is_satisfiable(&np));
}

#[test]
fn test_dispatch_algebra_evaluate() {
    let alg = DispatchAlgebra;
    let pred = SignaturePred::HasBit(PredicateSignature::M6_REGISTER);
    let sig_yes = PredicateSignature::from_raw(PredicateSignature::M6_REGISTER);
    let sig_no = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
    assert!(alg.evaluate(&pred, &sig_yes));
    assert!(!alg.evaluate(&pred, &sig_no));
}

#[test]
fn test_dispatch_sfa_state_count() {
    let sfa = build_dispatch_sfa();
    // 1 initial + 15 module + 1 reject = 17 states
    assert_eq!(sfa.num_states(), 17);
    // 16 module transitions + 1 reject transition = 17
    assert_eq!(sfa.num_transitions(), 16);
}

#[test]
fn test_dispatch_sfa_completeness() {
    let sfa = build_dispatch_sfa();
    assert!(verify_completeness(&sfa), "all non-zero signatures should be accepted");
}

#[test]
fn test_dispatch_sfa_zero_rejected() {
    let sfa = build_dispatch_sfa();
    assert!(verify_zero_rejected(&sfa), "zero signature should be rejected");
}

#[test]
fn test_dispatch_sfa_base_accepted() {
    let sfa = build_dispatch_sfa();
    assert!(sfa.accepts(&[PredicateSignature::new()]), "base signature should be accepted");
}

#[test]
fn test_dispatch_sfa_full_accepted() {
    let sfa = build_dispatch_sfa();
    assert!(sfa.accepts(&[PredicateSignature::from_raw(PredicateSignature::ALL)]));
}

#[test]
fn test_dispatch_sfa_single_module_accepted() {
    let sfa = build_dispatch_sfa();
    for module in &ModuleId::ALL {
        let sig = PredicateSignature::from_raw(module.bit());
        assert!(sfa.accepts(&[sig]), "single-module signature for {} should be accepted", module);
    }
}

#[test]
fn test_dispatch_sfa_witness_generation() {
    let alg = DispatchAlgebra;
    for module in &ModuleId::ALL {
        let pred = SignaturePred::HasBit(module.bit());
        let w = alg
            .witness(&pred)
            .expect(&format!("should have witness for {}", module));
        assert!(w.contains(module.bit()));
    }
}

// ── ChannelContext tests ──────────────────────────────────────────────

#[test]
fn test_channel_context_cross_channel() {
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.set_current_channel("ch2".to_string());
    assert!(ctx.is_cross_channel("x"));
    assert!(!ctx.is_cross_channel("y")); // unbound
}

#[test]
fn test_channel_context_same_channel() {
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.set_current_channel("ch1".to_string());
    assert!(!ctx.is_cross_channel("x"));
}

// ── DispatchDiagnostics tests ─────────────────────────────────────────

#[test]
fn test_diagnostics_from_empty_plan() {
    let plan = classify_grammar(&[], &[]);
    let diag = DispatchDiagnostics::from_plan(&plan);
    assert!(diag.profiles.is_empty());
    assert!(diag.degenerate_predicates.is_empty());
}

// ── Dispatch overlap pairs ────────────────────────────────────────────

#[test]
fn test_overlap_pairs_m1_m10() {
    let pairs = dispatch_overlap_pairs();
    assert!(pairs.contains(&(ModuleId::Symbolic, ModuleId::Mso)));
    assert!(pairs.contains(&(ModuleId::Mso, ModuleId::Symbolic)));
}

// ── PredicateCompiler and pipeline orchestration ──────────────────────

#[test]
fn test_compile_predicate_pipeline_returns_diagnostics() {
    let plan = classify_grammar(&[], &[]);
    let diag = compile_predicate_pipeline(&plan, &[], &[]);
    assert!(diag.profiles.is_empty());
}

// ── PredicateCompiler trait integration tests ────────────────────────
//
// Each test is gated on its module's feature since `predicate-dispatch`
// only implies `symbolic-automata` and `weighted-mso`.

#[test]
fn test_symbolic_compiler_produces_analysis() {
    use crate::symbolic::SymbolicCompiler;
    let compiler = SymbolicCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result: crate::symbolic::SymbolicAnalysis =
        compiler.compile_predicate(&pred, &profile, &[], &[]);
    // Empty categories → max(0, 1) = 1 state, 0 transitions
    assert_eq!(result.num_states, 1);
    assert_eq!(result.num_transitions, 0);
}

#[test]
fn test_buchi_compiler_produces_analysis() {
    use crate::buchi::BuchiCompiler;
    let compiler = BuchiCompiler;
    let pred = PredicateExpr::ExistsInfinite {
        var: "x".into(),
        body: Box::new(PredicateExpr::True),
    };
    let profile = extract_features(&pred, &ChannelContext::new());
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    // Trait call succeeds and returns valid analysis
    assert!(!result.has_accepting_cycle);
}

#[test]
fn test_alternating_compiler_produces_analysis() {
    use crate::alternating::AlternatingCompiler;
    let compiler = AlternatingCompiler;
    let pred = PredicateExpr::ForallFinite {
        var: "x".into(),
        domain: vec!["a".into(), "b".into()],
        body: Box::new(PredicateExpr::True),
    };
    let profile = extract_features(&pred, &ChannelContext::new());
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.non_bisimilar_pairs.is_empty());
}

#[test]
fn test_vpa_compiler_produces_analysis() {
    use crate::vpa::VpaCompiler;
    let compiler = VpaCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    // VPA returns Option<VpaAnalysis> — empty grammar yields None
    assert!(result.is_none());
}

#[test]
fn test_parity_tree_compiler_produces_analysis() {
    use crate::parity_tree::ParityTreeCompiler;
    let compiler = ParityTreeCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    // Parity tree on empty grammar: language is empty with 0 max priority
    assert!(result.is_empty);
}

#[test]
fn test_register_compiler_produces_analysis() {
    use crate::register_automata::RegisterCompiler;
    let compiler = RegisterCompiler;
    let pred = PredicateExpr::Relation {
        name: "eq".into(),
        args: vec!["x".into(), "y".into()],
    };
    let profile = extract_features(&pred, &ChannelContext::new());
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.dead_registers.is_empty());
}

#[test]
fn test_probabilistic_compiler_produces_analysis() {
    use crate::probabilistic::ProbabilisticCompiler;
    let compiler = ProbabilisticCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.low_selectivity_rules.is_empty());
}

#[test]
fn test_multi_tape_compiler_produces_analysis() {
    use crate::multi_tape::MultiTapeCompiler;
    let compiler = MultiTapeCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.disconnected_tapes.is_empty());
}

#[test]
fn test_multiset_compiler_produces_analysis() {
    use crate::multiset_automata::MultisetCompiler;
    let compiler = MultisetCompiler;
    let pred = PredicateExpr::Relation {
        name: "count".into(),
        args: vec!["x".into()],
    };
    let profile = extract_features(&pred, &ChannelContext::new());
    assert!(profile.signature.contains(PredicateSignature::M9_MULTISET));
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.unsatisfiable_constraints.is_empty());
}

#[test]
fn test_mso_compiler_produces_analysis() {
    use crate::weighted_mso::MsoCompiler;
    let compiler = MsoCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    // MSO on empty syntax classifies into one of the basic formula classes
    assert!(matches!(
        result.formula_class,
        crate::weighted_mso::MsoFormulaClass::Restricted
            | crate::weighted_mso::MsoFormulaClass::RestrictedExistential
            | crate::weighted_mso::MsoFormulaClass::FirstOrder
            | crate::weighted_mso::MsoFormulaClass::Full
    ));
}

#[test]
fn test_two_way_compiler_produces_analysis() {
    use crate::two_way_transducer::TwoWayCompiler;
    let compiler = TwoWayCompiler;
    let pred = PredicateExpr::True;
    let profile = extract_features(&pred, &ChannelContext::new());
    let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
    assert!(result.deadlock_cycles.is_empty());
}

// All 11 automata compilers are always compiled and dispatched at
// grammar-analysis time by the `predicate_dispatch/signature.rs` runtime
// registry — not by any Cargo feature — so this conformance check runs
// unconditionally. (It was formerly gated on nine inert `= []` capability-label
// features that gated nothing; those declarations were removed once confirmed
// dead, turning a never-built test into a real always-on conformance check.)
#[test]
fn test_all_compilers_implement_predicate_compiler() {
    fn assert_compiler<C: PredicateCompiler>(_c: &C) {}

    assert_compiler(&crate::symbolic::SymbolicCompiler);
    assert_compiler(&crate::buchi::BuchiCompiler);
    assert_compiler(&crate::alternating::AlternatingCompiler);
    assert_compiler(&crate::vpa::VpaCompiler);
    assert_compiler(&crate::parity_tree::ParityTreeCompiler);
    assert_compiler(&crate::register_automata::RegisterCompiler);
    assert_compiler(&crate::probabilistic::ProbabilisticCompiler);
    assert_compiler(&crate::multi_tape::MultiTapeCompiler);
    assert_compiler(&crate::multiset_automata::MultisetCompiler);
    assert_compiler(&crate::weighted_mso::MsoCompiler);
    assert_compiler(&crate::two_way_transducer::TwoWayCompiler);
}

// ── GrammarDispatchPlan with real grammar structure ───────────────────

#[test]
fn test_classify_grammar_cross_category_activates_m8() {
    let syntax = vec![(
        "PInput".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("for".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Name".to_string(),
                param_name: "ch".to_string(),
            },
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "body".to_string(),
            },
        ],
    )];
    let categories = vec![
        CategoryInfo {
            name: "Proc".to_string(),
            native_type: None,
            is_primary: true,
            has_var: true,
        },
        CategoryInfo {
            name: "Name".to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        },
    ];
    let plan = classify_grammar(&syntax, &categories);
    assert!(plan.requires(ModuleId::MultiTape), "cross-category should activate M8");
}

#[test]
fn test_classify_grammar_collection_activates_m9() {
    let syntax = vec![(
        "PList".to_string(),
        "Proc".to_string(),
        vec![SyntaxItemSpec::Collection {
            param_name: "elems".to_string(),
            element_category: "Proc".to_string(),
            separator: ",".to_string(),
            kind: crate::grammar::ir::CollectionKind::Vec,
            key_val_separator: None,
        }],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Multiset), "collection should activate M9");
}

#[test]
fn test_module_schedule_is_sorted_by_cost() {
    let plan = classify_grammar(&[], &[]);
    for window in plan.module_schedule.windows(2) {
        assert!(
            window[0].estimated_cost() <= window[1].estimated_cost(),
            "schedule should be sorted by cost: {} vs {}",
            window[0],
            window[1]
        );
    }
}

// ── DispatchDiagnostics tests ─────────────────────────────────────────

#[test]
fn test_diagnostics_detects_base_only_predicate() {
    let plan = GrammarDispatchPlan {
        aggregate_signature: PredicateSignature::new(),
        predicate_profiles: vec![PredicateProfile::base()],
        module_schedule: vec![ModuleId::Symbolic, ModuleId::Mso],
        modules_skipped: 9,
    };
    let diag = DispatchDiagnostics::from_plan(&plan);
    assert_eq!(diag.degenerate_predicates, vec![0], "base-only should be degenerate");
}

#[test]
fn test_diagnostics_detects_full_activation() {
    let mut profile = PredicateProfile::base();
    profile.signature = PredicateSignature::from_raw(PredicateSignature::ALL);
    let plan = GrammarDispatchPlan {
        aggregate_signature: PredicateSignature::from_raw(PredicateSignature::ALL),
        predicate_profiles: vec![profile],
        module_schedule: ModuleId::ALL.to_vec(),
        modules_skipped: 0,
    };
    let diag = DispatchDiagnostics::from_plan(&plan);
    assert_eq!(diag.full_activation_predicates, vec![0]);
}

// ── Signature arithmetic properties ───────────────────────────────────

#[test]
fn test_signature_union_is_commutative() {
    let a = PredicateSignature::from_raw(0b101);
    let b = PredicateSignature::from_raw(0b110);
    assert_eq!(a.union(b), b.union(a));
}

#[test]
fn test_signature_union_is_associative() {
    let a = PredicateSignature::from_raw(0b001);
    let b = PredicateSignature::from_raw(0b010);
    let c = PredicateSignature::from_raw(0b100);
    assert_eq!(a.union(b).union(c), a.union(b.union(c)));
}

#[test]
fn test_signature_intersection_complement() {
    let full = PredicateSignature::from_raw(PredicateSignature::ALL);
    let base = PredicateSignature::new();
    assert_eq!(full.intersection(base), base);
}

// ── ChannelContext edge cases ─────────────────────────────────────────

#[test]
fn test_channel_context_unbound_var_not_cross() {
    let mut ctx = ChannelContext::new();
    ctx.set_current_channel("ch1".to_string());
    assert!(!ctx.is_cross_channel("unbound"));
}

#[test]
fn test_channel_context_no_current_not_cross() {
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    // No current channel set
    assert!(!ctx.is_cross_channel("x"));
}

#[test]
fn test_channel_context_distinct_channels() {
    let mut ctx = ChannelContext::new();
    ctx.bind("x".to_string(), "ch1".to_string());
    ctx.bind("y".to_string(), "ch2".to_string());
    ctx.bind("z".to_string(), "ch1".to_string());
    let channels = ctx.distinct_channels();
    assert_eq!(channels.len(), 2);
    assert!(channels.contains("ch1"));
    assert!(channels.contains("ch2"));
}

// ── extract_features: OR/AND propagation and composition ──────────────

#[test]
fn test_extract_or_combines_signatures() {
    let expr = PredicateExpr::Or(
        Box::new(PredicateExpr::ForallInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::True),
        }),
        Box::new(PredicateExpr::Relation {
            name: "eq".to_string(),
            args: vec!["y".to_string()],
        }),
    );
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
}

#[test]
fn test_extract_unknown_relation_defaults_to_m6() {
    let expr = PredicateExpr::Relation {
        name: "custom_check".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(
        profile.signature.contains(PredicateSignature::M6_REGISTER),
        "unknown relation should default to M6 (register)"
    );
}

#[test]
fn test_extract_fresh_relation_triggers_m6() {
    let expr = PredicateExpr::Relation {
        name: "fresh".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
}

// ── MSO formula edge cases ────────────────────────────────────────────

#[test]
fn test_mso_neg_atomic_letprop() {
    let formula = WeightedMsoFormula::NegAtomicPos {
        label: "letprop".to_string(),
        var: "x".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA));
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
}

#[test]
fn test_mso_neg_order_triggers_m6() {
    let formula = WeightedMsoFormula::NegOrder { x: "a".to_string(), y: "b".to_string() };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
}

#[test]
fn test_mso_not_in_set() {
    let formula = WeightedMsoFormula::NotInSet {
        var: "x".to_string(),
        set_var: "S".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    // Should be base only (set membership is MSO-native)
    assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
    assert!(profile.signature.contains(PredicateSignature::M10_MSO));
}

#[test]
fn test_mso_deeply_nested_quantifiers() {
    // ∀x. ∃X. ∀²y. c
    let formula = WeightedMsoFormula::ForallFirst {
        var: "x".to_string(),
        body: Box::new(WeightedMsoFormula::ExistsSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::ForallSecond {
                var: "Y".to_string(),
                body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
            }),
        }),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert_eq!(profile.quantifier_depth, 3);
    assert!(profile.signature.contains(PredicateSignature::M3_AWA)); // ForallFirst + ForallSecond
}

#[test]
fn test_mso_mu_triggers_parity_tree() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "mu".to_string(),
        var: "x".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
}

#[test]
fn test_mso_nu_triggers_parity_tree() {
    let formula = WeightedMsoFormula::AtomicPos {
        label: "nu".to_string(),
        var: "x".to_string(),
    };
    let ctx = ChannelContext::new();
    let profile = extract_features_mso(&formula, &ctx);
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
}

// ── Dispatch SFA additional verification ──────────────────────────────

#[test]
fn test_dispatch_sfa_is_not_empty() {
    let sfa = build_dispatch_sfa();
    assert!(!sfa.is_empty(), "dispatch SFA should not be empty");
}

#[test]
fn test_dispatch_algebra_equivalence() {
    let alg = DispatchAlgebra;
    let p = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
    let q = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
    assert!(alg.equivalent(&p, &q));
}

#[test]
fn test_dispatch_algebra_implies() {
    let alg = DispatchAlgebra;
    let specific = SignaturePred::And(
        Box::new(SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC)),
        Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)),
    );
    let general = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
    assert!(alg.implies(&specific, &general));
}

#[test]
fn test_dispatch_algebra_or_satisfiability() {
    let alg = DispatchAlgebra;
    let p = SignaturePred::HasBit(PredicateSignature::M2_BUCHI);
    let q = SignaturePred::HasBit(PredicateSignature::M3_AWA);
    let disj = alg.or(&p, &q);
    assert!(alg.is_satisfiable(&disj));
    // Witness should satisfy at least one
    let w = alg.witness(&disj).expect("should have witness");
    assert!(w.contains(PredicateSignature::M2_BUCHI) || w.contains(PredicateSignature::M3_AWA));
}

#[test]
fn test_signature_pred_eval_and() {
    let pred = SignaturePred::And(
        Box::new(SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC)),
        Box::new(SignaturePred::HasBit(PredicateSignature::M6_REGISTER)),
    );
    let sig_both = PredicateSignature::from_raw(
        PredicateSignature::M1_SYMBOLIC | PredicateSignature::M6_REGISTER,
    );
    let sig_one = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
    assert!(pred.eval(sig_both));
    assert!(!pred.eval(sig_one));
}

#[test]
fn test_signature_pred_eval_or() {
    let pred = SignaturePred::Or(
        Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)),
        Box::new(SignaturePred::HasBit(PredicateSignature::M3_AWA)),
    );
    let sig_m2 = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
    let sig_m3 = PredicateSignature::from_raw(PredicateSignature::M3_AWA);
    let sig_neither = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
    assert!(pred.eval(sig_m2));
    assert!(pred.eval(sig_m3));
    assert!(!pred.eval(sig_neither));
}

#[test]
fn test_signature_pred_eval_not() {
    let pred = SignaturePred::Not(Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)));
    let sig_m2 = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
    let sig_m1 = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
    assert!(!pred.eval(sig_m2));
    assert!(pred.eval(sig_m1));
}

// ── Base module invariant (Theorem 3.2) ──────────────────────────────

#[test]
fn test_extract_features_always_includes_base() {
    // Various predicate shapes should all include M1 and M10
    let exprs = vec![
        PredicateExpr::True,
        PredicateExpr::False,
        PredicateExpr::Atom("p".to_string()),
        PredicateExpr::Not(Box::new(PredicateExpr::True)),
        PredicateExpr::And(Box::new(PredicateExpr::True), Box::new(PredicateExpr::False)),
        PredicateExpr::ForallInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::True),
        },
        PredicateExpr::ExistsInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::True),
        },
        PredicateExpr::Relation {
            name: "eq".to_string(),
            args: vec!["x".to_string()],
        },
    ];
    let ctx = ChannelContext::new();
    for (i, expr) in exprs.iter().enumerate() {
        let profile = extract_features(expr, &ctx);
        assert!(
            profile.signature.contains(PredicateSignature::M1_SYMBOLIC),
            "expr #{} should contain M1",
            i
        );
        assert!(
            profile.signature.contains(PredicateSignature::M10_MSO),
            "expr #{} should contain M10",
            i
        );
    }
}

// ── ModuleId coverage ─────────────────────────────────────────────────

#[test]
fn test_module_id_feature_gates_are_nonempty() {
    for module in &ModuleId::ALL {
        assert!(!module.feature_gate().is_empty(), "{} has empty feature gate", module);
    }
}

#[test]
fn test_module_id_names_are_nonempty() {
    for module in &ModuleId::ALL {
        assert!(!module.name().is_empty(), "{} has empty name", module);
    }
}

#[test]
fn test_module_id_estimated_costs_are_positive() {
    for module in &ModuleId::ALL {
        assert!(module.estimated_cost() > 0, "{} has zero cost", module);
    }
}

// ── Sprint 4a: Grammar-structure heuristic unit tests ───────────────

#[test]
fn test_classify_grammar_recursive_activates_buchi() {
    // Category "Expr" has a rule referencing itself → M2
    let syntax = vec![(
        "ExprAdd".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "left".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "right".to_string(),
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Buchi), "recursive category should activate M2 Büchi");
}

#[test]
fn test_classify_grammar_branching_activates_awa() {
    // Rule with ≥3 NonTerminal items → M3
    let syntax = vec![(
        "Ternary".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "cond".to_string(),
            },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "then".to_string(),
            },
            SyntaxItemSpec::Terminal(":".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "else_".to_string(),
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Awa), "≥3 non-terminals should activate M3 AWA");
}

#[test]
fn test_classify_grammar_brackets_activates_vpa() {
    // Terminals "(" and ")" → M4
    let syntax = vec![(
        "Paren".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "inner".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Vpa), "paired brackets should activate M4 VPA");
}

#[test]
fn test_classify_grammar_recursive_branching_activates_parity_tree() {
    // Recursive + ≥3 NTs → M5
    let syntax = vec![(
        "TreeNode".to_string(),
        "Tree".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Tree".to_string(),
                param_name: "left".to_string(),
            },
            SyntaxItemSpec::NonTerminal {
                category: "Tree".to_string(),
                param_name: "middle".to_string(),
            },
            SyntaxItemSpec::NonTerminal {
                category: "Tree".to_string(),
                param_name: "right".to_string(),
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(
        plan.requires(ModuleId::ParityTree),
        "recursive + branching should activate M5 Parity Tree"
    );
    // Also check M2 and M3 are set
    assert!(plan.requires(ModuleId::Buchi));
    assert!(plan.requires(ModuleId::Awa));
}

#[test]
fn test_classify_grammar_binders_activates_register() {
    // Binder item → M6
    let syntax = vec![(
        "Lambda".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("\\".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Expr".to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "body".to_string(),
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Register), "binder items should activate M6 Register");
}

#[test]
fn test_classify_grammar_ambiguous_activates_probabilistic() {
    // ≥3 rules in same category → M7
    let syntax = vec![
        (
            "Add".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ),
        (
            "Sub".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("-".to_string())],
        ),
        (
            "Mul".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("*".to_string())],
        ),
    ];
    let plan = classify_grammar(&syntax, &[]);
    assert!(
        plan.requires(ModuleId::Probabilistic),
        "≥3 rules in same category should activate M7 Probabilistic"
    );
}

#[test]
fn test_classify_grammar_base_only() {
    // Single terminal rule → only M1+M10
    let syntax = vec![(
        "Lit".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("42".to_string())],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Symbolic));
    assert!(plan.requires(ModuleId::Mso));
    assert!(!plan.requires(ModuleId::Buchi), "single terminal should not activate M2");
    assert!(!plan.requires(ModuleId::Awa), "single terminal should not activate M3");
    assert!(!plan.requires(ModuleId::Vpa), "single terminal should not activate M4");
}

#[test]
fn test_classify_grammar_no_brackets_no_vpa() {
    // Has "(" but no ")" → M4 NOT set
    let syntax = vec![(
        "Open".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "inner".to_string(),
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(!plan.requires(ModuleId::Vpa), "unpaired bracket should not activate M4");
}

#[test]
fn test_classify_grammar_non_recursive_no_buchi() {
    // Non-recursive categories → M2 NOT set
    let syntax = vec![
        (
            "Lit".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::NonTerminal {
                category: "Num".to_string(),
                param_name: "val".to_string(),
            }],
        ),
        (
            "Digit".to_string(),
            "Num".to_string(),
            vec![SyntaxItemSpec::Terminal("0".to_string())],
        ),
    ];
    let plan = classify_grammar(&syntax, &[]);
    assert!(
        !plan.requires(ModuleId::Buchi),
        "non-recursive categories should not activate M2"
    );
}

#[test]
fn test_classify_grammar_two_rules_no_probabilistic() {
    // Exactly 2 rules in same category → M7 NOT set
    let syntax = vec![
        (
            "Add".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ),
        (
            "Sub".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("-".to_string())],
        ),
    ];
    let plan = classify_grammar(&syntax, &[]);
    assert!(
        !plan.requires(ModuleId::Probabilistic),
        "2 rules in same category should not activate M7"
    );
}

// ── Sprint 4b: Predicate-level fixpoint detection tests ──────────────

#[test]
fn test_extract_features_fixpoint_activates_vpa_parity() {
    let expr = PredicateExpr::Relation {
        name: "fixpoint".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA), "fixpoint relation → M4");
    assert!(
        profile
            .signature
            .contains(PredicateSignature::M5_PARITY_TREE),
        "fixpoint relation → M5"
    );
    assert!(profile.has_recursive_predicate);
}

#[test]
fn test_extract_features_letrec_activates_vpa_parity() {
    let expr = PredicateExpr::Relation {
        name: "letrec".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA));
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
    assert!(profile.has_recursive_predicate);
}

#[test]
fn test_extract_features_mu_activates_vpa_parity() {
    let expr = PredicateExpr::Relation {
        name: "mu".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(profile.signature.contains(PredicateSignature::M4_VPA));
    assert!(profile
        .signature
        .contains(PredicateSignature::M5_PARITY_TREE));
}

#[test]
fn test_extract_features_regular_relation_no_vpa() {
    let expr = PredicateExpr::Relation {
        name: "custom".to_string(),
        args: vec!["x".to_string()],
    };
    let ctx = ChannelContext::new();
    let profile = extract_features(&expr, &ctx);
    assert!(
        !profile.signature.contains(PredicateSignature::M4_VPA),
        "custom relation should not trigger M4"
    );
    assert!(
        !profile
            .signature
            .contains(PredicateSignature::M5_PARITY_TREE),
        "custom relation should not trigger M5"
    );
}

// ── Sprint 4c: Dispatch gate consistency tests ───────────────────────

#[test]
fn test_dispatch_plan_requires_all_base_modules() {
    let plan = classify_grammar(&[], &[]);
    assert!(plan.requires(ModuleId::Symbolic), "any plan must require M1");
    assert!(plan.requires(ModuleId::Mso), "any plan must require M10");
}

#[test]
fn test_dispatch_plan_skipped_modules_complement() {
    let plan = classify_grammar(&[], &[]);
    let skipped: HashSet<ModuleId> = plan.skipped_modules().into_iter().collect();
    for module in &ModuleId::ALL {
        assert_eq!(
            plan.requires(*module),
            !skipped.contains(module),
            "skipped_modules() and requires() must be complementary for {}",
            module
        );
    }
}

#[test]
fn test_dispatch_plan_empty_grammar_base_only() {
    let plan = classify_grammar(&[], &[]);
    assert!(
        plan.aggregate_signature.is_base_only(),
        "empty grammar should have only base modules"
    );
}

#[test]
fn test_dispatch_plan_full_grammar_all_modules() {
    // Grammar triggering all heuristics: recursive + branching + brackets +
    // binders + collection + cross-category + ambiguity (≥3 same-cat rules)
    let syntax = vec![
        // Recursive + branching (3 NTs, self-ref) → M2+M3+M5
        (
            "TreeNode".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "b".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "c".to_string(),
                },
            ],
        ),
        // Brackets → M4
        (
            "Paren".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "inner".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ),
        // Binder → M6
        (
            "Lambda".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Expr".to_string(),
                is_multi: false,
            }],
        ),
        // 3rd rule in "Expr" already exists above, this is the 4th → M7
        (
            "Lit".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("42".to_string())],
        ),
        // Cross-category (≥2 distinct categories in one rule) → M8+M11
        (
            "Apply".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "fn_".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Type".to_string(),
                    param_name: "ty".to_string(),
                },
            ],
        ),
        // Collection → M9
        (
            "List".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Collection {
                param_name: "elems".to_string(),
                element_category: "Expr".to_string(),
                separator: ",".to_string(),
                kind: crate::grammar::ir::CollectionKind::Vec,
                key_val_separator: None,
            }],
        ),
        // Arithmetic terminal → M12
        (
            "Add".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ),
        // Pattern matching terminal → M13
        (
            "Match".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("match".to_string())],
        ),
        // Subtype terminal → M14
        (
            "Extends".to_string(),
            "Decl".to_string(),
            vec![SyntaxItemSpec::Terminal("extends".to_string())],
        ),
    ];
    let plan = classify_grammar(&syntax, &[]);
    for module in &ModuleId::ALL {
        assert!(plan.requires(*module), "full grammar should activate {}", module);
    }
}

// ── Sprint 4d: Combined grammar + predicate interaction tests ────────

#[test]
fn test_classify_grammar_collection_and_binder() {
    let syntax = vec![(
        "CollBind".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Collection {
                param_name: "items".to_string(),
                element_category: "Expr".to_string(),
                separator: ",".to_string(),
                kind: crate::grammar::ir::CollectionKind::Vec,
                key_val_separator: None,
            },
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Expr".to_string(),
                is_multi: false,
            },
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Register), "binder → M6");
    assert!(plan.requires(ModuleId::Multiset), "collection → M9");
}

#[test]
fn test_classify_grammar_all_heuristics_fire() {
    // Construct a grammar triggering all 6 new heuristics plus existing ones
    let syntax = vec![
        // Self-recursive + branching → M2+M3+M5
        (
            "Branch".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "b".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "c".to_string(),
                },
            ],
        ),
        // Brackets → M4
        (
            "Parens".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ),
        // Binder → M6
        (
            "Bind".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Binder {
                param_name: "v".to_string(),
                category: "Expr".to_string(),
                is_multi: false,
            }],
        ),
        // Collection → M9
        (
            "Coll".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Collection {
                param_name: "xs".to_string(),
                element_category: "Expr".to_string(),
                separator: ",".to_string(),
                kind: crate::grammar::ir::CollectionKind::Vec,
                key_val_separator: None,
            }],
        ),
        // Cross-category → M8+M11
        (
            "Cross".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "e".to_string(),
                },
                SyntaxItemSpec::NonTerminal {
                    category: "Type".to_string(),
                    param_name: "t".to_string(),
                },
            ],
        ),
        // 6th rule: already ≥3 rules in "Expr" → M7 (actually ≥6, threshold is 3)
    ];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Buchi), "M2");
    assert!(plan.requires(ModuleId::Awa), "M3");
    assert!(plan.requires(ModuleId::Vpa), "M4");
    assert!(plan.requires(ModuleId::ParityTree), "M5");
    assert!(plan.requires(ModuleId::Register), "M6");
    assert!(plan.requires(ModuleId::Probabilistic), "M7");
    assert!(plan.requires(ModuleId::MultiTape), "M8");
    assert!(plan.requires(ModuleId::Multiset), "M9");
    assert!(plan.requires(ModuleId::TwoWay), "M11");
}

// ── classify_grammar M12/M13/M14 tests ────────────────────────────

#[test]
fn test_classify_grammar_arithmetic_terminals_trigger_m12() {
    let syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::LinearArithmetic), "arithmetic terminal '+' → M12");
}

#[test]
fn test_classify_grammar_pattern_terminals_trigger_m13() {
    let syntax = vec![(
        "Match".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("match".to_string()),
            SyntaxItemSpec::Terminal("|".to_string()),
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::Unification), "pattern-match terminals → M13");
}

#[test]
fn test_classify_grammar_subtype_terminals_trigger_m14() {
    let syntax = vec![(
        "TypeDecl".to_string(),
        "Decl".to_string(),
        vec![SyntaxItemSpec::Terminal("extends".to_string())],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.requires(ModuleId::SubtypeLattice), "subtype terminal 'extends' → M14");
}

#[test]
fn test_classify_grammar_no_theory_terminals() {
    let syntax = vec![(
        "Lit".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("let".to_string()),
            SyntaxItemSpec::Terminal("in".to_string()),
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(!plan.requires(ModuleId::LinearArithmetic), "no arithmetic terminals → no M12");
    assert!(!plan.requires(ModuleId::Unification), "no pattern terminals → no M13");
    assert!(!plan.requires(ModuleId::SubtypeLattice), "no subtype terminals → no M14");
}

#[test]
fn test_classify_grammar_m12_m13_m14_in_schedule() {
    // Grammar with all three theory terminal patterns
    let syntax = vec![(
        "Arith".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::Terminal("match".to_string()),
            SyntaxItemSpec::Terminal("extends".to_string()),
        ],
    )];
    let plan = classify_grammar(&syntax, &[]);
    assert!(plan.module_schedule.contains(&ModuleId::LinearArithmetic));
    assert!(plan.module_schedule.contains(&ModuleId::Unification));
    assert!(plan.module_schedule.contains(&ModuleId::SubtypeLattice));
    // SubtypeLattice (cost 2) should come before LinearArithmetic/Unification (cost 3)
    let lat_pos = plan
        .module_schedule
        .iter()
        .position(|m| *m == ModuleId::SubtypeLattice)
        .expect("M14 in schedule");
    let arith_pos = plan
        .module_schedule
        .iter()
        .position(|m| *m == ModuleId::LinearArithmetic)
        .expect("M12 in schedule");
    assert!(lat_pos < arith_pos, "M14 (cost 2) should be scheduled before M12 (cost 3)");
}

// ── Sprint C4: order_by_specificity tests ────────────────────────────

#[test]
fn order_by_specificity_linear_chain() {
    // A ⊂ B ⊂ C — A is most specific
    let labels = vec!["Expr::C".to_string(), "Expr::B".to_string(), "Expr::A".to_string()];
    let subsumed = vec![
        ("Expr::A".to_string(), "Expr::B".to_string()), // A ⊂ B
        ("Expr::B".to_string(), "Expr::C".to_string()), // B ⊂ C
        ("Expr::A".to_string(), "Expr::C".to_string()), // A ⊂ C (transitive)
    ];

    let ordered = order_by_specificity(&labels, &subsumed);
    assert_eq!(ordered[0], "Expr::A", "most specific should be first");
    assert_eq!(ordered[1], "Expr::B");
    assert_eq!(ordered[2], "Expr::C", "most general should be last");
}

#[test]
fn order_by_specificity_no_subsumption() {
    let labels = vec!["Expr::X".to_string(), "Expr::Y".to_string(), "Expr::Z".to_string()];
    let subsumed: Vec<(String, String)> = vec![];

    let ordered = order_by_specificity(&labels, &subsumed);
    // Original order preserved
    assert_eq!(ordered[0], "Expr::X");
    assert_eq!(ordered[1], "Expr::Y");
    assert_eq!(ordered[2], "Expr::Z");
}

#[test]
fn order_by_specificity_tiebreak_grammar_order() {
    // A and B are both subsumed by C equally — break tie by grammar order
    let labels = vec!["Expr::A".to_string(), "Expr::B".to_string(), "Expr::C".to_string()];
    let subsumed = vec![
        ("Expr::A".to_string(), "Expr::C".to_string()),
        ("Expr::B".to_string(), "Expr::C".to_string()),
    ];

    let ordered = order_by_specificity(&labels, &subsumed);
    // A and B have same specificity (1), should be in grammar order
    assert_eq!(ordered[0], "Expr::A");
    assert_eq!(ordered[1], "Expr::B");
    // C has specificity 0 (most general)
    assert_eq!(ordered[2], "Expr::C");
}

// ══════════════════════════════════════════════════════════════════════
// Phase 6: GuardConfigSpec-driven dispatch tests (design doc §2A)
// ══════════════════════════════════════════════════════════════════════

use crate::{GuardConfigSpec, JoinPatternSpec, TheoryRegistrationSpec};
use std::collections::HashMap;

fn make_minimal_grammar() -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
    // Minimal grammar with no arithmetic terminals — should NOT activate
    // M12 heuristically.
    vec![("Var".to_string(), "Term".to_string(), vec![])]
}

#[test]
fn guard_config_none_preserves_heuristic() {
    // Without GuardConfigSpec, classify_grammar uses heuristics.
    let plan = classify_grammar(&make_minimal_grammar(), &[]);
    // Backward compat: M12 should NOT be set (no arithmetic terminals).
    assert!(!plan
        .aggregate_signature
        .contains(PredicateSignature::M12_LINEAR_ARITHMETIC));
}

#[test]
fn guard_config_theory_activates_m12_presburger() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "arithmetic".to_string(),
            theory_type: "PresburgerAlgebra".to_string(),
            handled_types: Some(vec!["Int".to_string()]),
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M12_LINEAR_ARITHMETIC));
}

#[test]
fn guard_config_theory_activates_m13_unification() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "patterns".to_string(),
            theory_type: "UnificationTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M13_UNIFICATION));
}

#[test]
fn guard_config_theory_activates_m14_lattice() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "types".to_string(),
            theory_type: "LatticeTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M14_SUBTYPE_LATTICE));
}

#[test]
fn guard_config_channels_activate_m8_when_two_params() {
    let gc = GuardConfigSpec {
        channel_categories: Some(vec!["Name".to_string()]),
        join_patterns: vec![JoinPatternSpec {
            label: "PJoin".to_string(),
            channel_categories: vec!["Name".to_string(), "Name".to_string()],
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
    // Same category twice → no M11 activation
    assert!(!plan
        .aggregate_signature
        .contains(PredicateSignature::M11_TWO_WAY));
}

#[test]
fn guard_config_channels_activate_m11_when_two_distinct_categories() {
    let gc = GuardConfigSpec {
        channel_categories: Some(vec!["Name".to_string(), "Place".to_string()]),
        join_patterns: vec![JoinPatternSpec {
            label: "PMixed".to_string(),
            channel_categories: vec!["Name".to_string(), "Place".to_string()],
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M11_TWO_WAY));
}

#[test]
fn guard_config_single_channel_join_no_m8() {
    let gc = GuardConfigSpec {
        channel_categories: Some(vec!["Name".to_string()]),
        join_patterns: vec![JoinPatternSpec {
            label: "PSingle".to_string(),
            channel_categories: vec!["Name".to_string()],
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_minimal_grammar(), &[], Some(&gc));
    // Single channel param → no multi-tape benefit
    assert!(!plan
        .aggregate_signature
        .contains(PredicateSignature::M8_MULTI_TAPE));
}

#[test]
fn resolve_selectivity_uses_override() {
    let mut sels = HashMap::new();
    sels.insert("eq".to_string(), 0.05_f64); // user says eq is 5% selective
    let gc = GuardConfigSpec {
        selectivity_overrides: sels,
        ..Default::default()
    };
    let expr = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    // Override wins over the heuristic (which would compute ~0.058).
    assert_eq!(resolve_selectivity(&expr, Some(&gc)), 0.05);
}

#[test]
fn resolve_selectivity_falls_through_when_no_override() {
    let gc = GuardConfigSpec::default();
    let expr = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    // No override → uses heuristic.
    let direct = estimate_predicate_selectivity(&expr);
    let resolved = resolve_selectivity(&expr, Some(&gc));
    assert_eq!(direct, resolved);
}

#[test]
fn resolve_cost_uses_override() {
    let mut costs = HashMap::new();
    costs.insert("expensive".to_string(), 100u32);
    let gc = GuardConfigSpec {
        cost_overrides: costs,
        ..Default::default()
    };
    let expr = PredicateExpr::Relation {
        name: "expensive".to_string(),
        args: vec!["x".to_string()],
    };
    assert_eq!(resolve_cost(&expr, Some(&gc)), 100);
}

#[test]
fn resolve_selectivity_compound_propagates_overrides() {
    // Test that overrides flow through And/Or/Not.
    // sel(eq) overridden to 0.1; sel(gt) heuristic (~0.5 * arity_factor)
    let mut sels = HashMap::new();
    sels.insert("eq".to_string(), 0.1_f64);
    let gc = GuardConfigSpec {
        selectivity_overrides: sels,
        ..Default::default()
    };
    let eq = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    let gt = PredicateExpr::Relation {
        name: "gt".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    let and = PredicateExpr::And(Box::new(eq.clone()), Box::new(gt.clone()));
    let or = PredicateExpr::Or(Box::new(eq.clone()), Box::new(gt.clone()));
    let not = PredicateExpr::Not(Box::new(eq.clone()));

    let gt_sel = estimate_predicate_selectivity(&gt);
    let and_sel = resolve_selectivity(&and, Some(&gc));
    let or_sel = resolve_selectivity(&or, Some(&gc));
    let not_sel = resolve_selectivity(&not, Some(&gc));

    // and_sel = 0.1 * gt_sel
    assert!((and_sel - 0.1 * gt_sel).abs() < 1e-9);
    // or_sel = 1 - (1 - 0.1)(1 - gt_sel)
    assert!((or_sel - (1.0 - (1.0 - 0.1) * (1.0 - gt_sel))).abs() < 1e-9);
    // not_sel = 1 - 0.1 = 0.9
    assert!((not_sel - 0.9).abs() < 1e-9);
}

// ══════════════════════════════════════════════════════════════════════
// Cleanup A: Bypass cross-category M8/M11 heuristic
// ══════════════════════════════════════════════════════════════════════

fn make_cross_category_grammar() -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
    // A grammar that has cross-category references — would activate
    // the structural M8/M11 heuristic in absence of `channels { }`.
    vec![(
        "Lam".to_string(),
        "Term".to_string(),
        vec![
            SyntaxItemSpec::Terminal("lam".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Type".to_string(),
                param_name: "ty".to_string(),
            },
            SyntaxItemSpec::NonTerminal {
                category: "Term".to_string(),
                param_name: "body".to_string(),
            },
        ],
    )]
}

#[test]
fn cleanup_a_no_guards_block_keeps_heuristic() {
    // Backward compat: without explicit channels, the cross-category
    // heuristic still fires.
    let plan = classify_grammar(&make_cross_category_grammar(), &[]);
    assert!(
        plan.aggregate_signature
            .contains(PredicateSignature::M8_MULTI_TAPE),
        "no guards block → cross-category heuristic activates M8"
    );
    assert!(
        plan.aggregate_signature
            .contains(PredicateSignature::M11_TWO_WAY),
        "no guards block → cross-category heuristic activates M11"
    );
}

#[test]
fn cleanup_a_explicit_empty_channels_bypasses_heuristic() {
    // With explicit (empty) channels, the structural heuristic is
    // bypassed: the language has explicitly declared "I have no
    // channels," so M8/M11 are not activated heuristically.
    let gc = GuardConfigSpec {
        channel_categories: Some(Vec::new()),
        join_patterns: Vec::new(),
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_cross_category_grammar(), &[], Some(&gc));
    assert!(
        !plan
            .aggregate_signature
            .contains(PredicateSignature::M8_MULTI_TAPE),
        "explicit empty channels → no M8 from heuristic"
    );
    assert!(
        !plan
            .aggregate_signature
            .contains(PredicateSignature::M11_TWO_WAY),
        "explicit empty channels → no M11 from heuristic"
    );
}

#[test]
fn cleanup_a_explicit_channels_drive_m8_only() {
    // With explicit channels and a single-channel join, only M8
    // (not M11) is activated, and only via the explicit declaration.
    let gc = GuardConfigSpec {
        channel_categories: Some(vec!["Name".to_string()]),
        join_patterns: vec![JoinPatternSpec {
            label: "PSingle".to_string(),
            channel_categories: vec!["Name".to_string()],
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_cross_category_grammar(), &[], Some(&gc));
    // Single-param join → no M8 even though structural would have set it
    assert!(
        !plan
            .aggregate_signature
            .contains(PredicateSignature::M8_MULTI_TAPE),
        "single-channel join → no M8 (heuristic bypassed; explicit single-arity)"
    );
}

// ══════════════════════════════════════════════════════════════════════
// Cleanup B: Bypass terminal scans when theory registered
// ══════════════════════════════════════════════════════════════════════

fn make_arith_terminal_grammar() -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
    vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )]
}

fn make_unif_terminal_grammar() -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
    vec![(
        "Match".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("match".to_string())],
    )]
}

fn make_subtype_terminal_grammar() -> Vec<(String, String, Vec<SyntaxItemSpec>)> {
    vec![(
        "Sub".to_string(),
        "Decl".to_string(),
        vec![SyntaxItemSpec::Terminal("extends".to_string())],
    )]
}

#[test]
fn cleanup_b_arith_terminal_no_theory_keeps_heuristic() {
    let plan = classify_grammar(&make_arith_terminal_grammar(), &[]);
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M12_LINEAR_ARITHMETIC));
}

#[test]
fn cleanup_b_arith_terminal_with_presburger_theory_bypassed() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "arithmetic".to_string(),
            theory_type: "PresburgerAlgebra".to_string(),
            handled_types: Some(vec!["Int".to_string()]),
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_arith_terminal_grammar(), &[], Some(&gc));
    // M12 still set — but only by the explicit theory block, not the
    // terminal heuristic.
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M12_LINEAR_ARITHMETIC));
}

#[test]
fn cleanup_b_unification_theory_bypasses_terminal_heuristic() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "patterns".to_string(),
            theory_type: "UnificationTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_unif_terminal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M13_UNIFICATION));
}

#[test]
fn cleanup_b_lattice_theory_bypasses_terminal_heuristic() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "types".to_string(),
            theory_type: "LatticeTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let plan = classify_grammar_with_config(&make_subtype_terminal_grammar(), &[], Some(&gc));
    assert!(plan
        .aggregate_signature
        .contains(PredicateSignature::M14_SUBTYPE_LATTICE));
}

// ══════════════════════════════════════════════════════════════════════
// Cleanup C: Configurable feature extraction (extract_features_with_config)
// ══════════════════════════════════════════════════════════════════════

#[test]
fn cleanup_c_extract_features_2arg_wrapper_unchanged() {
    // Backward compat: extract_features(expr, ctx) is identical to
    // extract_features_with_config(expr, ctx, None).
    let expr = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    let ctx = ChannelContext::new();
    let p1 = extract_features(&expr, &ctx);
    let p2 = extract_features_with_config(&expr, &ctx, None);
    assert_eq!(p1.signature, p2.signature);
}

#[test]
fn cleanup_c_register_theory_bypasses_equality_heuristic() {
    // With Register theory registered, is_equality_relation('eq')
    // is bypassed.
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "equality".to_string(),
            theory_type: "RegisterTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let expr = PredicateExpr::Relation {
        name: "eq".to_string(),
        args: vec!["x".to_string(), "y".to_string()],
    };
    let ctx = ChannelContext::new();
    let p_unconfigured = extract_features(&expr, &ctx);
    let p_configured = extract_features_with_config(&expr, &ctx, Some(&gc));

    // Unconfigured: M6 set by is_equality_relation heuristic.
    assert!(p_unconfigured
        .signature
        .contains(PredicateSignature::M6_REGISTER));
    // Configured: M6 NOT set from heuristic (the bypass silenced it).
    assert!(!p_configured
        .signature
        .contains(PredicateSignature::M6_REGISTER));
}

#[test]
fn cleanup_c_unification_theory_bypasses_match_heuristic() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "patterns".to_string(),
            theory_type: "UnificationTheory".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    let expr = PredicateExpr::Relation {
        name: "match".to_string(),
        args: vec!["t".to_string(), "p".to_string()],
    };
    let ctx = ChannelContext::new();
    let p_unconfigured = extract_features(&expr, &ctx);
    let p_configured = extract_features_with_config(&expr, &ctx, Some(&gc));

    assert!(p_unconfigured
        .signature
        .contains(PredicateSignature::M13_UNIFICATION));
    assert!(!p_configured
        .signature
        .contains(PredicateSignature::M13_UNIFICATION));
}

#[test]
fn cleanup_c_known_theory_kind_recognizes_aliases() {
    assert_eq!(known_theory_kind("PresburgerAlgebra"), Some(TheoryKind::Presburger));
    assert_eq!(known_theory_kind("Presburger"), Some(TheoryKind::Presburger));
    assert_eq!(known_theory_kind("PresburgerTheory"), Some(TheoryKind::Presburger));
    assert_eq!(known_theory_kind("UnificationTheory"), Some(TheoryKind::Unification));
    assert_eq!(known_theory_kind("LatticeTheory"), Some(TheoryKind::Lattice));
    assert_eq!(known_theory_kind("RegisterTheory"), Some(TheoryKind::Register));
    assert_eq!(known_theory_kind("EqualityTheory"), Some(TheoryKind::Register));
    assert_eq!(known_theory_kind("MultisetTheory"), Some(TheoryKind::Multiset));
    assert_eq!(known_theory_kind("CardinalityTheory"), Some(TheoryKind::Multiset));
    assert_eq!(known_theory_kind("FixpointTheory"), Some(TheoryKind::Fixpoint));
    assert_eq!(known_theory_kind("MyCustomTheory"), None);
}

#[test]
fn cleanup_c_theory_registered_returns_false_for_none() {
    assert!(!theory_registered(None, TheoryKind::Presburger));
    assert!(!theory_registered(None, TheoryKind::Unification));
    assert!(!theory_registered(None, TheoryKind::Lattice));
}

#[test]
fn cleanup_c_theory_registered_only_matches_registered_kind() {
    let gc = GuardConfigSpec {
        theories: vec![TheoryRegistrationSpec {
            name: "arithmetic".to_string(),
            theory_type: "PresburgerAlgebra".to_string(),
            handled_types: None,
        }],
        ..Default::default()
    };
    assert!(theory_registered(Some(&gc), TheoryKind::Presburger));
    assert!(!theory_registered(Some(&gc), TheoryKind::Unification));
    assert!(!theory_registered(Some(&gc), TheoryKind::Lattice));
    assert!(!theory_registered(Some(&gc), TheoryKind::Register));
    assert!(!theory_registered(Some(&gc), TheoryKind::Multiset));
    assert!(!theory_registered(Some(&gc), TheoryKind::Fixpoint));
}
