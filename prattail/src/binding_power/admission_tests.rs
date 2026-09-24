//! Independent arithmetic-admission regressions.
//!
//! The original worker below is the exact a29f119a implementation, renamed only.
//! It is a test oracle, never a production fallback or alternate parser.
use super::*;
use std::convert::Infallible;

fn original_analyze_binding_powers(rules: &[InfixRuleInfo]) -> BindingPowerTable {
    let mut table = BindingPowerTable::new();

    // Group infix rules by category
    let mut by_category: std::collections::BTreeMap<String, Vec<&InfixRuleInfo>> =
        std::collections::BTreeMap::new();
    for rule in rules {
        by_category
            .entry(rule.category.clone())
            .or_default()
            .push(rule);
    }

    // Assign binding powers per category using two passes:
    // 1. Non-postfix (infix) operators in declaration order
    // 2. Postfix operators above the non-postfix range, leaving a gap for
    //    unary prefix (which gets max_non_postfix_bp + 2 in lib.rs)
    for cat_rules in by_category.values() {
        // The level of the rule currently being assigned. Starts at 2 to leave room for
        // 0 (entry) and 1. A level occupies exactly two binding-power slots — `p` and
        // `p + 1` — so the next level is `p + 2`.
        let mut precedence: u8 = 2;
        // Whether any non-postfix rule has been assigned yet in this category. `same` on
        // the FIRST such rule has no predecessor to share with, so it opens the first
        // level like an unmarked rule would; see `GrammarRule::shares_level_with_previous`
        // for why that is silently permitted rather than rejected.
        let mut level_is_open = false;

        // First pass: non-postfix operators (regular infix + mixfix), in declaration
        // order. The counter advances once per LEVEL — a `same`-marked rule joins the
        // level its predecessor opened instead of starting a tighter one.
        for rule in cat_rules.iter().filter(|r| !r.is_postfix) {
            if level_is_open && !rule.shares_level_with_previous {
                precedence += 2;
            }
            level_is_open = true;

            // Precedence selects the level; associativity only decides which end of the
            // level's two slots faces left. `min(left_bp, right_bp) == precedence` holds
            // for both arms, which is what lets operators of DIFFERENT associativity
            // share one level.
            let (left_bp, right_bp) = match rule.associativity {
                Associativity::Left => (precedence, precedence + 1),
                Associativity::Right => (precedence + 1, precedence),
            };

            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp,
                right_bp,
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: false,
                is_mixfix: rule.is_mixfix,
                mixfix_parts: rule.mixfix_parts.clone(),
                nullary_literals: rule.nullary_literals.clone(),
            });
        }

        // Second pass: postfix operators start above non-postfix + prefix gap.
        // Layout (Stage 3.27d-pre standardized 2026-04-30, PREFIX_BP_OFFSET=2):
        //   [infix at 2..max_infix_bp] [prefix at max_infix_bp+2] [postfix at max_infix_bp+4..]
        // Prefix BP is computed by `compute_prefix_bp()` and installed at codegen
        // time in WPDS binder.rs:708,1004 ParamParse arms (Stage 3.27d work).
        //
        // ★ The infix loop no longer leaves `precedence` one slot PAST the last level —
        // it advances lazily, before each new level, so that a `same`-marked rule can
        // join the level already assigned. `first_free_bp` reconstructs the value the
        // loop used to end on (`max_infix_bp + 1`, or the untouched initial 2 when the
        // category declares no non-postfix operator at all), keeping this layout — and
        // every prefix/postfix binding power derived from it — exactly as it was.
        let first_free_bp = if level_is_open {
            precedence + 2
        } else {
            precedence
        };
        let mut postfix_prec = first_free_bp + 2;
        // `same` has the same relative-level meaning in the postfix pass as it does in
        // the infix/mixfix pass. Keeping a separate open-level bit is essential: the
        // first postfix operator cannot share the final infix level, because postfix
        // lives above the reserved prefix gap.
        let mut postfix_level_is_open = false;
        for rule in cat_rules.iter().filter(|r| r.is_postfix) {
            if postfix_level_is_open && !rule.shares_level_with_previous {
                postfix_prec += 2;
            }
            postfix_level_is_open = true;
            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp: postfix_prec + 1,
                right_bp: 0, // unused for postfix (no right recursive call)
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: true,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
                nullary_literals: Vec::new(),
            });
        }
    }

    table
}

fn rule(index: usize, category: &str, postfix: bool, same: bool) -> InfixRuleInfo {
    InfixRuleInfo {
        label: format!("Operator{index}"),
        terminal: format!("terminal{index}"),
        category: category.into(),
        result_category: format!("Result{index}"),
        associativity: if index % 2 == 0 {
            Associativity::Left
        } else {
            Associativity::Right
        },
        shares_level_with_previous: same,
        is_cross_category: true,
        is_postfix: postfix,
        is_mixfix: true,
        mixfix_parts: vec![
            MixfixPart {
                operand_category: "Argument".into(),
                param_name: format!("operand{index}"),
                preceding_terminals: vec!["(".into(), "[".into()],
                following_terminals: vec!["]".into(), ")".into()],
                repetition: Some(MixfixRep {
                    separator: ",".into(),
                    min: 0,
                    close: vec!["end".into()],
                }),
                capture_kind: None,
            },
            MixfixPart {
                operand_category: "Ident".into(),
                param_name: "capture".into(),
                preceding_terminals: vec![".".into()],
                following_terminals: vec![],
                repetition: None,
                capture_kind: Some("Ident".into()),
            },
        ],
        nullary_literals: vec!["(".into(), ")".into()],
    }
}

fn checked(rules: &[InfixRuleInfo]) -> Result<BindingPowerTable, BindingPowerError<Infallible>> {
    try_analyze_binding_powers(rules, |_| Ok(()))
}

/// All fields participate through their derived Debug representations, including
/// nested repetition/capture descriptors; the oracle is independent old source.
fn assert_matches_original(rules: &[InfixRuleInfo]) -> BindingPowerTable {
    let actual = checked(rules).expect("representable fixture");
    let original = original_analyze_binding_powers(rules);
    assert_eq!(format!("{:?}", actual.operators), format!("{:?}", original.operators));
    actual
}

#[test]
fn admission_preserves_original_complete_payloads_category_order_and_fixity() {
    let rules = vec![
        rule(0, "Z", true, true),
        rule(1, "A", true, true),
        rule(2, "Z", false, true),
        rule(3, "A", false, false),
        rule(4, "A", false, true),
        rule(5, "A", true, true),
        rule(6, "Z", false, false),
        rule(7, "Z", true, false),
    ];
    let actual = assert_matches_original(&rules);
    assert_eq!(
        actual
            .operators
            .iter()
            .map(|op| op.label.as_str())
            .collect::<Vec<_>>(),
        [
            "Operator3",
            "Operator4",
            "Operator1",
            "Operator5",
            "Operator2",
            "Operator6",
            "Operator0",
            "Operator7"
        ]
    );
    assert_eq!(
        actual
            .operators
            .iter()
            .map(|op| (op.left_bp, op.right_bp))
            .collect::<Vec<_>>(),
        [(3, 2), (2, 3), (7, 0), (7, 0), (2, 3), (4, 5), (9, 0), (11, 0)]
    );
    for op in actual.operators.iter().filter(|op| op.is_postfix) {
        assert!(!op.is_mixfix);
        assert!(op.mixfix_parts.is_empty());
        assert!(op.nullary_literals.is_empty());
    }
}

#[test]
fn admission_checks_original_gap_even_without_postfix_rules() {
    let rules: Vec<_> = (0..125).map(|i| rule(i, "Expr", false, false)).collect();
    let actual = assert_matches_original(&rules);
    let last = actual.operators.last().expect("125 original operators");
    assert_eq!((last.left_bp, last.right_bp), (250, 251));
    for (count, site) in [
        (126, BindingPowerSite::PostfixStart),
        (127, BindingPowerSite::FirstFree),
        (128, BindingPowerSite::InfixAdvance),
    ] {
        let rules: Vec<_> = (0..count).map(|i| rule(i, "Expr", false, false)).collect();
        assert!(matches!(checked(&rules),
            Err(BindingPowerError::Overflow { category_index: 0, site: actual }) if actual == site));
    }
}

#[test]
fn admission_postfix_only_and_mixed_upper_boundaries_match_original() {
    let mut postfix: Vec<_> = (0..126).map(|i| rule(i, "Expr", true, false)).collect();
    let actual = assert_matches_original(&postfix);
    let last = actual.operators.last().expect("126 postfix levels");
    assert_eq!((last.left_bp, last.right_bp), (255, 0));
    postfix.push(rule(126, "Expr", true, false));
    assert!(matches!(
        checked(&postfix),
        Err(BindingPowerError::Overflow {
            category_index: 0,
            site: BindingPowerSite::PostfixAdvance
        })
    ));
    let mut mixed: Vec<_> = (0..125).map(|i| rule(i, "Expr", false, false)).collect();
    mixed.push(rule(125, "Expr", true, false));
    let actual = assert_matches_original(&mixed);
    assert_eq!(
        actual
            .operators
            .last()
            .expect("postfix after infix")
            .left_bp,
        255
    );
    mixed.push(rule(126, "Expr", true, false));
    assert!(matches!(
        checked(&mixed),
        Err(BindingPowerError::Overflow {
            category_index: 0,
            site: BindingPowerSite::PostfixAdvance
        })
    ));
}

#[test]
fn admission_does_not_replace_level_bounds_with_rule_count_caps() {
    for postfix in [false, true] {
        let rules: Vec<_> = (0..4096).map(|i| rule(i, "Expr", postfix, true)).collect();
        let actual = assert_matches_original(&rules);
        assert_eq!(actual.operators.len(), 4096);
        assert!(actual.operators.iter().all(|op| if postfix {
            (op.left_bp, op.right_bp) == (5, 0)
        } else {
            op.left_bp.min(op.right_bp) == 2 && op.left_bp.max(op.right_bp) == 3
        }));
    }
}

#[test]
fn admission_reports_sorted_group_ordinal_and_never_returns_partial_table() {
    let mut rules: Vec<_> = (0..126).map(|i| rule(i, "Z", false, false)).collect();
    rules.push(rule(126, "A", false, false));
    assert!(matches!(
        checked(&rules),
        Err(BindingPowerError::Overflow {
            category_index: 1,
            site: BindingPowerSite::PostfixStart
        })
    ));
}

#[test]
fn admission_runs_once_before_arithmetic_and_preserves_caller_error() {
    let rules: Vec<_> = (0..126).map(|i| rule(i, "Expr", false, false)).collect();
    let mut calls = 0;
    let result = try_analyze_binding_powers(&rules, |source| {
        calls += 1;
        assert!(std::ptr::eq(source, rules.as_slice()));
        Err("caller refused before overflowing source")
    });
    assert_eq!(calls, 1);
    assert!(matches!(
        result,
        Err(BindingPowerError::Admission("caller refused before overflowing source"))
    ));
    let empty = assert_matches_original(&[]);
    assert!(empty.operators.is_empty());
}

#[test]
fn admission_six_addition_sites_preserve_exact_sum_or_report_site() {
    for site in [
        BindingPowerSite::InfixAdvance,
        BindingPowerSite::InfixSlot,
        BindingPowerSite::FirstFree,
        BindingPowerSite::PostfixStart,
        BindingPowerSite::PostfixAdvance,
        BindingPowerSite::PostfixSlot,
    ] {
        assert_eq!(checked_binding_power_add::<Infallible>(253, 2, 7, site), Ok(255));
        assert_eq!(
            checked_binding_power_add::<Infallible>(254, 2, 7, site),
            Err(BindingPowerError::Overflow { category_index: 7, site })
        );
        assert_eq!(
            checked_binding_power_add::<Infallible>(255, 1, 7, site),
            Err(BindingPowerError::Overflow { category_index: 7, site })
        );
    }
}

#[test]
#[should_panic(expected = "binding power overflow in category 0 at PostfixStart")]
fn admission_static_wrapper_reports_overflow_instead_of_wrapping() {
    let rules: Vec<_> = (0..126).map(|i| rule(i, "Expr", false, false)).collect();
    let _ = analyze_binding_powers(&rules);
}
