use super::*;
use proptest::prelude::*;
use std::collections::BTreeSet;

/// Reuse the same token map as the unit tests.
fn make_token_map() -> TokenIdMap {
    TokenIdMap::from_names(
        vec!["Plus", "Minus", "Star", "Integer", "Ident", "RParen", "Semi", "Eof"]
            .into_iter()
            .map(String::from),
    )
}

/// Helper: build a RecoveryWfst with the given sync token names.
fn make_wfst(sync_names: &[&str], token_map: &TokenIdMap) -> RecoveryWfst {
    let names: Vec<String> = sync_names.iter().map(|s| s.to_string()).collect();
    RecoveryWfst::new("Expr".to_string(), &names, token_map)
}

/// All token names in the default map.
const ALL_TOKEN_NAMES: &[&str] =
    &["Plus", "Minus", "Star", "Integer", "Ident", "RParen", "Semi", "Eof"];

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    // ── Sprint A1: VPA Nesting Ceiling ─────────────────────────────────────

    /// When depth > ceiling, the 0.3x VPA discount is applied, producing a
    /// multiplier strictly less than the baseline (same depth, no ceiling).
    #[test]
    fn prop_depth_exceeds_ceiling_multiplier_below_one(
        ceiling in 1..20usize,
        extra in 1..20usize,
    ) {
        let depth = ceiling + extra; // depth > ceiling guaranteed
        let mut config_with = RecoveryConfig::default();
        config_with.vpa_nesting_ceiling = Some(ceiling);

        let config_without = RecoveryConfig::default();

        let ctx = RecoveryContext { depth, ..Default::default() };
        let m_with = ctx.skip_multiplier_with(&config_with);
        let m_without = ctx.skip_multiplier_with(&config_without);

        // The 0.3x factor should make m_with strictly less than m_without.
        prop_assert!(
            m_with < m_without,
            "depth {} > ceiling {} should apply 0.3x discount: with={}, without={}",
            depth, ceiling, m_with, m_without
        );
        // Specifically, m_with == m_without * 0.3
        let expected = m_without * 0.3;
        prop_assert!(
            (m_with - expected).abs() < 1e-9,
            "expected m_with = {} * 0.3 = {}, got {}",
            m_without, expected, m_with
        );
    }

    /// When depth <= ceiling, the multiplier should be identical to ceiling = None.
    #[test]
    fn prop_depth_within_ceiling_no_extra_factor(
        ceiling in 1..20usize,
        depth in 0..20usize,
    ) {
        prop_assume!(depth <= ceiling);

        let mut config_with = RecoveryConfig::default();
        config_with.vpa_nesting_ceiling = Some(ceiling);

        let config_without = RecoveryConfig::default();

        let ctx = RecoveryContext { depth, ..Default::default() };
        let m_with = ctx.skip_multiplier_with(&config_with);
        let m_without = ctx.skip_multiplier_with(&config_without);

        prop_assert!(
            (m_with - m_without).abs() < 1e-9,
            "depth {} <= ceiling {} should have no VPA effect: with={}, without={}",
            depth, ceiling, m_with, m_without
        );
    }

    /// ceiling = None produces the same multiplier as any run without VPA config.
    #[test]
    fn prop_ceiling_none_idempotent(depth in 0..2000usize, bp in 0..20u8) {
        let config1 = RecoveryConfig::default(); // vpa_nesting_ceiling = None
        let mut config2 = RecoveryConfig::default();
        config2.vpa_nesting_ceiling = None; // explicitly None

        let ctx = RecoveryContext {
            depth,
            binding_power: bp,
            ..Default::default()
        };
        let m1 = ctx.skip_multiplier_with(&config1);
        let m2 = ctx.skip_multiplier_with(&config2);

        prop_assert!(
            (m1 - m2).abs() < 1e-9,
            "None ceiling should be idempotent: m1={}, m2={}", m1, m2
        );
    }

    /// Smaller ceiling triggers the VPA discount for more depth values.
    /// If ceiling1 < ceiling2, then for depth in (ceiling1, ceiling2],
    /// ceiling1 applies the 0.3x discount but ceiling2 does not.
    #[test]
    fn prop_ceiling_monotone(
        ceiling1 in 1..15usize,
        gap in 1..10usize,
    ) {
        let ceiling2 = ceiling1 + gap;
        // Pick depth in the gap: ceiling1 < depth <= ceiling2
        let depth = ceiling1 + 1;
        prop_assume!(depth <= ceiling2);

        let mut config1 = RecoveryConfig::default();
        config1.vpa_nesting_ceiling = Some(ceiling1);

        let mut config2 = RecoveryConfig::default();
        config2.vpa_nesting_ceiling = Some(ceiling2);

        let ctx = RecoveryContext { depth, ..Default::default() };
        let m1 = ctx.skip_multiplier_with(&config1);
        let m2 = ctx.skip_multiplier_with(&config2);

        // ceiling1 should apply discount (depth > ceiling1), ceiling2 should not
        prop_assert!(
            m1 < m2,
            "ceiling1={} < ceiling2={}, depth={}: m1={} should < m2={}",
            ceiling1, ceiling2, depth, m1, m2
        );
    }

    // ── Sprint A2: Bracket Mismatch Penalty ───────────────────────────────

    /// `bracket_mismatch_penalty` always returns exactly 1.0 or 2.0.
    #[test]
    fn prop_penalty_in_one_or_two(
        mismatch_subset in proptest::collection::btree_set(0..8usize, 0..8),
        query_idx in 0..8usize,
    ) {
        let token_map = make_token_map();
        let mut wfst = make_wfst(&["Eof", "Plus"], &token_map);

        // Convert subset indices to TokenIds
        let mismatch_ids: BTreeSet<TokenId> = mismatch_subset
            .iter()
            .filter_map(|&i| {
                ALL_TOKEN_NAMES.get(i).and_then(|name| token_map.get(name))
            })
            .collect();
        wfst.set_bracket_mismatch_ids(mismatch_ids);

        let query_name = ALL_TOKEN_NAMES[query_idx];
        if let Some(query_id) = token_map.get(query_name) {
            let p = wfst.bracket_mismatch_penalty(query_id);
            prop_assert!(
                (p - 1.0).abs() < 1e-9 || (p - 2.0).abs() < 1e-9,
                "penalty should be 1.0 or 2.0, got {}", p
            );
        }
    }

    /// `penalty(id) = 2.0` if and only if `id` is in the mismatch set.
    #[test]
    fn prop_penalty_2_iff_in_set(
        mismatch_subset in proptest::collection::btree_set(0..8usize, 0..8),
    ) {
        let token_map = make_token_map();
        let mut wfst = make_wfst(&["Eof", "Plus"], &token_map);

        let mismatch_ids: BTreeSet<TokenId> = mismatch_subset
            .iter()
            .filter_map(|&i| {
                ALL_TOKEN_NAMES.get(i).and_then(|name| token_map.get(name))
            })
            .collect();
        wfst.set_bracket_mismatch_ids(mismatch_ids.clone());

        for (idx, &name) in ALL_TOKEN_NAMES.iter().enumerate() {
            if let Some(tid) = token_map.get(name) {
                let p = wfst.bracket_mismatch_penalty(tid);
                let in_set = mismatch_ids.contains(&tid);
                if in_set {
                    prop_assert!(
                        (p - 2.0).abs() < 1e-9,
                        "token {} (idx={}) in mismatch set should get 2.0, got {}", name, idx, p
                    );
                } else {
                    prop_assert!(
                        (p - 1.0).abs() < 1e-9,
                        "token {} (idx={}) not in mismatch set should get 1.0, got {}", name, idx, p
                    );
                }
            }
        }
    }

    /// Empty mismatch set means all penalties are 1.0.
    #[test]
    fn prop_empty_mismatch_all_one(query_idx in 0..8usize) {
        let token_map = make_token_map();
        let wfst = make_wfst(&["Eof", "Plus"], &token_map);
        // Default: empty bracket_mismatch_ids

        let query_name = ALL_TOKEN_NAMES[query_idx];
        if let Some(query_id) = token_map.get(query_name) {
            let p = wfst.bracket_mismatch_penalty(query_id);
            prop_assert!(
                (p - 1.0).abs() < 1e-9,
                "empty mismatch set: token {} should get 1.0, got {}", query_name, p
            );
        }
    }

    /// If A is a subset of B, then every token penalized under A is also penalized under B.
    #[test]
    fn prop_superset_includes_subset_penalties(
        subset_a in proptest::collection::btree_set(0..8usize, 0..4),
        extra_b in proptest::collection::btree_set(0..8usize, 0..4),
    ) {
        let token_map = make_token_map();

        let ids_a: BTreeSet<TokenId> = subset_a
            .iter()
            .filter_map(|&i| ALL_TOKEN_NAMES.get(i).and_then(|name| token_map.get(name)))
            .collect();

        // B = A ∪ extra
        let mut ids_b = ids_a.clone();
        for &i in &extra_b {
            if let Some(name) = ALL_TOKEN_NAMES.get(i) {
                if let Some(tid) = token_map.get(name) {
                    ids_b.insert(tid);
                }
            }
        }

        let mut wfst_a = make_wfst(&["Eof", "Plus"], &token_map);
        wfst_a.set_bracket_mismatch_ids(ids_a);

        let mut wfst_b = make_wfst(&["Eof", "Plus"], &token_map);
        wfst_b.set_bracket_mismatch_ids(ids_b);

        for &name in ALL_TOKEN_NAMES {
            if let Some(tid) = token_map.get(name) {
                let pa = wfst_a.bracket_mismatch_penalty(tid);
                let pb = wfst_b.bracket_mismatch_penalty(tid);
                if (pa - 2.0).abs() < 1e-9 {
                    prop_assert!(
                        (pb - 2.0).abs() < 1e-9,
                        "token {} penalized in A should also be penalized in superset B: pa={}, pb={}",
                        name, pa, pb
                    );
                }
            }
        }
    }

    // ── Sprint C2: Liveness-Aware Recovery ─────────────────────────────────

    /// Round-trip: set_recursive_category(b) then is_recursive_category() == b.
    #[test]
    fn prop_recursive_flag_round_trip(b in proptest::bool::ANY) {
        let token_map = make_token_map();
        let mut wfst = make_wfst(&["Plus", "Eof"], &token_map);
        wfst.set_recursive_category(b);
        prop_assert_eq!(wfst.is_recursive_category(), b);
    }

    /// Default RecoveryWfst has is_recursive_category() == false.
    #[test]
    fn prop_default_not_recursive(
        sync_count in 1..8usize,
    ) {
        let token_map = make_token_map();
        let sync_names: Vec<&str> = ALL_TOKEN_NAMES.iter()
            .copied()
            .take(sync_count.min(ALL_TOKEN_NAMES.len()))
            .collect();
        let wfst = make_wfst(&sync_names, &token_map);
        prop_assert!(!wfst.is_recursive_category());
    }

    /// In a recursive category, InsertToken cost is multiplied by 0.7x.
    /// So for the same token stream and position, the recursive InsertToken
    /// cost should be <= the non-recursive InsertToken cost.
    #[test]
    fn prop_recursive_insert_le_nonrecursive(
        sync_idx in 0..8usize,
    ) {
        let token_map = make_token_map();
        let sync_name = ALL_TOKEN_NAMES[sync_idx];
        // Use a single sync token so InsertToken is the dominant strategy
        let mut wfst_rec = make_wfst(&[sync_name], &token_map);
        wfst_rec.set_recursive_category(true);

        let wfst_normal = make_wfst(&[sync_name], &token_map);

        let eof_id = token_map.get("Eof").expect("Eof should exist");
        let tokens = vec![eof_id];
        let ctx = RecoveryContext::default();

        let r_rec = wfst_rec.find_best_recovery_contextual(&tokens, 1, &ctx, None, "Expr");
        let r_normal = wfst_normal.find_best_recovery_contextual(&tokens, 1, &ctx, None, "Expr");

        if let (Some(rr), Some(rn)) = (r_rec, r_normal) {
            // Check that both produce InsertToken
            if matches!(rr.action, RepairAction::InsertToken { .. })
                && matches!(rn.action, RepairAction::InsertToken { .. })
            {
                prop_assert!(
                    rr.cost.left.value() <= rn.cost.left.value() + 1e-9,
                    "recursive InsertToken cost {} should be <= non-recursive {}",
                    rr.cost.left.value(), rn.cost.left.value()
                );
            }
        }
    }

    /// In a recursive category, SkipToSync cost is multiplied by 1.3x.
    /// So for the same token stream, the recursive SkipToSync cost should
    /// be >= the non-recursive SkipToSync cost.
    #[test]
    fn prop_recursive_skip_ge_nonrecursive(
        sync_idx in 0..8usize,
    ) {
        let token_map = make_token_map();
        let sync_name = ALL_TOKEN_NAMES[sync_idx];

        let mut wfst_rec = make_wfst(&[sync_name], &token_map);
        wfst_rec.set_recursive_category(true);

        let wfst_normal = make_wfst(&[sync_name], &token_map);

        // Build a token stream where the sync token appears after some non-sync tokens
        let integer_id = token_map.get("Integer").expect("Integer should exist");
        if let Some(sync_id) = token_map.get(sync_name) {
            // [Integer, sync_token] — SkipToSync should skip Integer to reach sync_token
            let tokens = vec![integer_id, sync_id];
            let ctx = RecoveryContext::default();

            let r_rec = wfst_rec.find_best_recovery_contextual(&tokens, 0, &ctx, None, "Expr");
            let r_normal = wfst_normal.find_best_recovery_contextual(&tokens, 0, &ctx, None, "Expr");

            if let (Some(rr), Some(rn)) = (r_rec, r_normal) {
                if matches!(rr.action, RepairAction::SkipToSync { .. })
                    && matches!(rn.action, RepairAction::SkipToSync { .. })
                {
                    prop_assert!(
                        rr.cost.left.value() >= rn.cost.left.value() - 1e-9,
                        "recursive SkipToSync cost {} should be >= non-recursive {}",
                        rr.cost.left.value(), rn.cost.left.value()
                    );
                }
            }
        }
    }
}

// ── Edge-case unit tests ───────────────────────────────────────────────

/// depth == ceiling: should NOT trigger the 0.3x VPA discount (strictly greater).
#[test]
fn vpa_nesting_ceiling_at_exact_boundary() {
    let mut config = RecoveryConfig::default();
    config.vpa_nesting_ceiling = Some(5);

    let ctx_at = RecoveryContext { depth: 5, ..Default::default() };
    let ctx_above = RecoveryContext { depth: 6, ..Default::default() };

    let no_vpa = RecoveryConfig::default();

    let m_at = ctx_at.skip_multiplier_with(&config);
    let m_baseline = ctx_at.skip_multiplier_with(&no_vpa);
    let m_above = ctx_above.skip_multiplier_with(&config);
    let m_above_baseline = ctx_above.skip_multiplier_with(&no_vpa);

    // At boundary: no discount
    assert!(
        (m_at - m_baseline).abs() < 1e-9,
        "depth == ceiling should NOT trigger discount: m_at={}, baseline={}",
        m_at,
        m_baseline
    );

    // Above boundary: discount applied
    let expected_above = m_above_baseline * 0.3;
    assert!(
        (m_above - expected_above).abs() < 1e-9,
        "depth > ceiling should trigger 0.3x discount: m_above={}, expected={}",
        m_above,
        expected_above
    );
}

/// ceiling = Some(0): every depth > 0 triggers the 0.3x discount.
#[test]
fn vpa_nesting_ceiling_zero() {
    let mut config = RecoveryConfig::default();
    config.vpa_nesting_ceiling = Some(0);
    let no_vpa = RecoveryConfig::default();

    // depth = 0: no discount (0 is not > 0)
    let ctx0 = RecoveryContext { depth: 0, ..Default::default() };
    let m0 = ctx0.skip_multiplier_with(&config);
    let m0_baseline = ctx0.skip_multiplier_with(&no_vpa);
    assert!(
        (m0 - m0_baseline).abs() < 1e-9,
        "depth 0, ceiling 0: no discount: m0={}, baseline={}",
        m0,
        m0_baseline
    );

    // depth = 1: discount applied
    let ctx1 = RecoveryContext { depth: 1, ..Default::default() };
    let m1 = ctx1.skip_multiplier_with(&config);
    let m1_baseline = ctx1.skip_multiplier_with(&no_vpa);
    let expected = m1_baseline * 0.3;
    assert!(
        (m1 - expected).abs() < 1e-9,
        "depth 1, ceiling 0: 0.3x discount: m1={}, expected={}",
        m1,
        expected
    );

    // depth = 10: discount applied
    let ctx10 = RecoveryContext { depth: 10, ..Default::default() };
    let m10 = ctx10.skip_multiplier_with(&config);
    let m10_baseline = ctx10.skip_multiplier_with(&no_vpa);
    let expected10 = m10_baseline * 0.3;
    assert!(
        (m10 - expected10).abs() < 1e-9,
        "depth 10, ceiling 0: 0.3x discount: m10={}, expected={}",
        m10,
        expected10
    );
}

/// Exactly one mismatch token: only that token gets 2.0x penalty.
#[test]
fn bracket_mismatch_singleton_set() {
    let token_map = make_token_map();
    let mut wfst = make_wfst(&["Eof", "Plus", "Semi"], &token_map);

    let plus_id = token_map.get("Plus").expect("Plus should exist");
    let mut ids = BTreeSet::new();
    ids.insert(plus_id);
    wfst.set_bracket_mismatch_ids(ids);

    // Plus is the only mismatch token
    assert!(
        (wfst.bracket_mismatch_penalty(plus_id) - 2.0).abs() < 1e-9,
        "singleton mismatch token should get 2.0"
    );

    // All others should get 1.0
    for &name in ALL_TOKEN_NAMES {
        if let Some(tid) = token_map.get(name) {
            if tid != plus_id {
                assert!(
                    (wfst.bracket_mismatch_penalty(tid) - 1.0).abs() < 1e-9,
                    "non-mismatch token {} should get 1.0, got {}",
                    name,
                    wfst.bracket_mismatch_penalty(tid)
                );
            }
        }
    }
}

/// Every sync token is a mismatch: all penalties are 2.0.
#[test]
fn bracket_mismatch_all_tokens_mismatch() {
    let token_map = make_token_map();
    let sync_names: Vec<&str> = ALL_TOKEN_NAMES.to_vec();
    let mut wfst = make_wfst(&sync_names, &token_map);

    // Put every token in the mismatch set
    let all_ids: BTreeSet<TokenId> = ALL_TOKEN_NAMES
        .iter()
        .filter_map(|name| token_map.get(name))
        .collect();
    wfst.set_bracket_mismatch_ids(all_ids);

    for &name in ALL_TOKEN_NAMES {
        if let Some(tid) = token_map.get(name) {
            assert!(
                (wfst.bracket_mismatch_penalty(tid) - 2.0).abs() < 1e-9,
                "all-mismatch: token {} should get 2.0, got {}",
                name,
                wfst.bracket_mismatch_penalty(tid)
            );
        }
    }
}
