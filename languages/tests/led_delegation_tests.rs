//! Tests for LED (Left-Denotation) delegation in sum-type categories.
//!
//! The LedTest language has operators on constituent categories (Num, Pred) but
//! NOT on the sum type Expr (except "|"). This forces the parser to use LED
//! delegation when parsing expressions like "1 + 2" at the Expr level.
//!
//! Phase 1 tests (P1.*): Known-variant delegation — LHS is a recognized cast
//! variant (CastNum, CastPred), so the parser unwraps, delegates to the
//! constituent's operators, and re-wraps.
//!
//! Phase 2 tests (P2.*): Auto-projection — LHS is an unknown variant (ExprVar),
//! so the parser auto-inserts a projection node (ExprToNum) and delegates.
//!
//! Edge case tests (E*): No delegation needed.
//!
//! Normalization tests (N*): Full Ascent round-trip.
//!
//! Run with: `cargo test -p mettail-languages --features led-test`

use mettail_languages::led_test::{self as lt, Expr, Num};
use std::sync::Arc;

// ============================================================================
// Phase 1: Known-Variant LED Delegation
// ============================================================================
// When the LHS is a recognized cast variant (e.g., Expr::CastNum(inner)),
// the LED chain unwraps inner, delegates to the constituent's operators,
// and re-wraps the result.

/// P1.1: Same-category infix delegation — "+" lives on Num, not Expr
#[test]
fn test_p1_1_same_cat_infix_delegation() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 + 2").expect("should parse 1 + 2 as Expr via LED delegation");
    if let Expr::CastNum(inner) = &result {
        assert!(
            matches!(inner.as_ref(), Num::AddNum(_, _)),
            "expected AddNum inside CastNum, got: {:?}",
            inner
        );
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.2: Left-associative chaining — "1 + 2 + 3" → CastNum(AddNum(AddNum(1, 2), 3))
#[test]
fn test_p1_2_left_associative_chaining() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 + 2 + 3").expect("should parse chained addition");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(left, _right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::AddNum(_, _)),
                "expected AddNum(AddNum(...), ...) for left-assoc, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.3: Precedence preserved — "1 + 2 * 3" → CastNum(AddNum(1, MulNum(2, 3)))
#[test]
fn test_p1_3_precedence_preserved() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 + 2 * 3").expect("should parse with correct precedence");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(_left, right) = inner.as_ref() {
            assert!(
                matches!(right.as_ref(), Num::MulNum(_, _)),
                "expected MulNum as right child of AddNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.4: Precedence reversed order — "2 * 3 + 1" → CastNum(AddNum(MulNum(2, 3), 1))
#[test]
fn test_p1_4_precedence_reversed_order() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("2 * 3 + 1").expect("should parse with correct precedence");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(left, _right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::MulNum(_, _)),
                "expected MulNum as left child of AddNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.5: Postfix delegation — "3!" → CastNum(FactNum(3))
#[test]
fn test_p1_5_postfix_delegation() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("3!").expect("should parse postfix ! via delegation");
    if let Expr::CastNum(inner) = &result {
        assert!(
            matches!(inner.as_ref(), Num::FactNum(_)),
            "expected FactNum inside CastNum, got: {:?}",
            inner
        );
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.6: Postfix + infix chain — "3! + 1" → CastNum(AddNum(FactNum(3), 1))
#[test]
fn test_p1_6_postfix_plus_infix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("3! + 1").expect("should parse postfix + infix chain");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(left, _right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::FactNum(_)),
                "expected FactNum as left of AddNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.7: Cross-category delegation — "1 == 2" → CastPred(EqNum(1, 2))
#[test]
fn test_p1_7_cross_cat_delegation() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 == 2").expect("should parse cross-cat == via delegation");
    if let Expr::CastPred(inner) = &result {
        assert!(
            matches!(inner.as_ref(), lt::Pred::EqNum(_, _)),
            "expected EqNum inside CastPred, got: {:?}",
            inner
        );
    } else {
        panic!("expected CastPred wrapper for cross-cat ==, got: {:?}", result);
    }
}

/// P1.8: Cross-category delegation — "1 != 2" → CastPred(NeNum(1, 2))
#[test]
fn test_p1_8_cross_cat_ne() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 != 2").expect("should parse cross-cat != via delegation");
    if let Expr::CastPred(inner) = &result {
        assert!(
            matches!(inner.as_ref(), lt::Pred::NeNum(_, _)),
            "expected NeNum inside CastPred, got: {:?}",
            inner
        );
    } else {
        panic!("expected CastPred wrapper for cross-cat !=, got: {:?}", result);
    }
}

/// P1.8b: Cross-category RHS projection keeps the pending Pred continuation.
#[test]
fn test_p1_8b_cross_cat_rhs_projection_continuation() {
    for input in ["1 != to_num(2)", "-1 != to_num(2)"] {
        mettail_runtime::clear_var_cache();
        let result = lt::Pred::parse(input)
            .unwrap_or_else(|err| panic!("should parse {input:?} as Pred: {err:?}"));
        if let lt::Pred::NeNum(left, right) = &result {
            assert!(
                matches!(right.as_ref(), Num::ExprToNum(_)),
                "expected projection on RHS for {input:?}, got: {:?}",
                right
            );
            if input.starts_with('-') {
                assert!(
                    matches!(left.as_ref(), Num::NegNum(_)),
                    "expected unary LHS to survive for {input:?}, got: {:?}",
                    left
                );
            }
        } else {
            panic!("expected NeNum for {input:?}, got: {:?}", result);
        }
    }
}

/// P1.8c: Postfix Num LHS remains available to a following Pred comparison.
#[test]
fn test_p1_8c_postfix_lhs_comparison_continuation() {
    for input in ["3! == to_num(a)", "3! == to_num(a) and -4 != to_num(true)"] {
        mettail_runtime::clear_var_cache();
        let result = lt::Pred::parse(input)
            .unwrap_or_else(|err| panic!("should parse {input:?} as Pred: {err:?}"));
        match &result {
            lt::Pred::EqNum(left, right) => {
                assert!(
                    matches!(left.as_ref(), Num::FactNum(_)),
                    "expected postfix LHS to survive for {input:?}, got: {:?}",
                    left
                );
                assert!(
                    matches!(right.as_ref(), Num::ExprToNum(_)),
                    "expected projected RHS for {input:?}, got: {:?}",
                    right
                );
            },
            lt::Pred::AndPred(left, _) => match left.as_ref() {
                lt::Pred::EqNum(eq_left, eq_right) => {
                    assert!(
                        matches!(eq_left.as_ref(), Num::FactNum(_)),
                        "expected postfix LHS inside conjunction for {input:?}, got: {:?}",
                        eq_left
                    );
                    assert!(
                        matches!(eq_right.as_ref(), Num::ExprToNum(_)),
                        "expected projected RHS inside conjunction for {input:?}, got: {:?}",
                        eq_right
                    );
                },
                other => panic!("expected EqNum left conjunct for {input:?}, got: {:?}", other),
            },
            other => panic!("expected EqNum/AndPred for {input:?}, got: {:?}", other),
        }
    }
}

/// P1.9: Own operator + delegation — "1 + 2 | 3 + 4" → EPar(CastNum(AddNum(1,2)), CastNum(AddNum(3,4)))
#[test]
fn test_p1_9_own_op_plus_delegation() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 + 2 | 3 + 4").expect("should parse delegation + own operator");
    if let Expr::EPar(left, right) = &result {
        assert!(
            matches!(left.as_ref(), Expr::CastNum(inner) if matches!(inner.as_ref(), Num::AddNum(_, _))),
            "expected CastNum(AddNum(...)) as left of EPar, got: {:?}",
            left
        );
        assert!(
            matches!(right.as_ref(), Expr::CastNum(inner) if matches!(inner.as_ref(), Num::AddNum(_, _))),
            "expected CastNum(AddNum(...)) as right of EPar, got: {:?}",
            right
        );
    } else {
        panic!("expected EPar at top, got: {:?}", result);
    }
}

/// P1.10: Parenthesized sub-expressions — "(1 + 2) * 3" → CastNum(MulNum(AddNum(1,2), 3))
#[test]
fn test_p1_10_parenthesized_sub_expressions() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("(1 + 2) * 3").expect("should parse parenthesized delegation");
    if let Expr::CastNum(inner) = &result {
        if let Num::MulNum(left, _right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::AddNum(_, _)),
                "expected AddNum as left child of MulNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected MulNum at top of Num, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.11: Own op wrapping cross-cat — "(1 == 2) | (3 == 4)" → EPar(CastPred(EqNum(1,2)), CastPred(EqNum(3,4)))
#[test]
fn test_p1_11_own_op_wrapping_cross_cat() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("(1 == 2) | (3 == 4)").expect("should parse");
    if let Expr::EPar(left, right) = &result {
        assert!(
            matches!(left.as_ref(), Expr::CastPred(inner) if matches!(inner.as_ref(), lt::Pred::EqNum(_, _))),
            "expected CastPred(EqNum(...)) as left of EPar, got: {:?}",
            left
        );
        assert!(
            matches!(right.as_ref(), Expr::CastPred(inner) if matches!(inner.as_ref(), lt::Pred::EqNum(_, _))),
            "expected CastPred(EqNum(...)) as right of EPar, got: {:?}",
            right
        );
    } else {
        panic!("expected EPar at top, got: {:?}", result);
    }
}

/// P1.12: Unary prefix delegation — "-3" → CastNum(NegNum(3))
#[test]
fn test_p1_12_unary_prefix_delegation() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("-3").expect("should parse unary prefix via delegation");
    if let Expr::CastNum(inner) = &result {
        assert!(
            matches!(inner.as_ref(), Num::NegNum(_)),
            "expected NegNum inside CastNum, got: {:?}",
            inner
        );
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.13: Unary prefix + infix chain — "-3 + 1" → CastNum(AddNum(NegNum(3), 1))
#[test]
fn test_p1_13_unary_prefix_plus_infix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("-3 + 1").expect("should parse unary prefix + infix chain");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(left, _right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::NegNum(_)),
                "expected NegNum as left of AddNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top of Num, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.14: Nested prefix + infix — "-(3 + 1)" → CastNum(NegNum(AddNum(3, 1)))
#[test]
fn test_p1_14_nested_prefix_plus_infix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("-(3 + 1)").expect("should parse nested prefix + infix");
    if let Expr::CastNum(inner) = &result {
        if let Num::NegNum(arg) = inner.as_ref() {
            assert!(
                matches!(arg.as_ref(), Num::AddNum(_, _)),
                "expected AddNum inside NegNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected NegNum at top of Num, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P1.15: Multiple postfix — "3! * 2!" → CastNum(MulNum(FactNum(3), FactNum(2)))
#[test]
fn test_p1_15_multiple_postfix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("3! * 2!").expect("should parse multiple postfix in expression");
    if let Expr::CastNum(inner) = &result {
        if let Num::MulNum(left, right) = inner.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::FactNum(_)),
                "expected FactNum as left of MulNum, got: {:?}",
                inner
            );
            assert!(
                matches!(right.as_ref(), Num::FactNum(_)),
                "expected FactNum as right of MulNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected MulNum at top of Num, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

// ============================================================================
// Phase 2: Auto-Projection for Unknown Variants
// ============================================================================
// Ident is NOT dispatched to cast sources (to avoid hijacking identifiers into
// a single constituent parser). Instead, "x" becomes ExprVar(x) at the sum-type
// level. When an LED operator follows, auto-projection inserts ExprToNum to
// delegate to the constituent's operators.

/// P2.1: Variable + infix — "x + 1" → CastNum(AddNum(ExprToNum(ExprVar(x)), 1))
#[test]
fn test_p2_1_variable_auto_project() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x + 1").expect("should parse x + 1 via auto-projection");
    if let Expr::CastNum(inner) = &result {
        if let Num::AddNum(left, _right) = inner.as_ref() {
            // After var-aware Phase 2 coercion, EVar(x) is converted directly
            // to NVar(x) instead of wrapping as ExprToNum(EVar(x)).
            // This preserves display roundtrip: display produces "x + 1"
            // which parses back identically.
            assert!(
                matches!(left.as_ref(), Num::NVar(_)),
                "expected NVar (var-aware projection) as left of AddNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected AddNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P2.2: Variable + cross-cat — "x == 1" → CastPred(EqNum(ExprToNum(ExprVar(x)), 1))
#[test]
fn test_p2_2_variable_cross_cat_auto_project() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x == 1").expect("should parse x == 1 via auto-projection");
    if let Expr::CastPred(inner) = &result {
        if let lt::Pred::EqNum(left, _right) = inner.as_ref() {
            // After var-aware Phase 2 coercion, EVar(x) → NVar(x) directly.
            assert!(
                matches!(left.as_ref(), Num::NVar(_)),
                "expected NVar (var-aware projection) as left of EqNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected EqNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastPred wrapper, got: {:?}", result);
    }
}

/// P2.4: Auto-projection + own operator — "x + 1 | y + 2"
#[test]
fn test_p2_4_auto_projection_plus_own_op() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x + 1 | y + 2").expect("should parse with auto-projection + own op");
    assert!(matches!(result, Expr::EPar(_, _)), "expected EPar at top, got: {:?}", result);
}

/// P2.5: Variable + postfix — "x!" → CastNum(FactNum(NVar(x)))
#[test]
fn test_p2_5_auto_project_postfix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x!").expect("should parse x! via auto-projection");
    if let Expr::CastNum(inner) = &result {
        if let Num::FactNum(arg) = inner.as_ref() {
            // After var-aware Phase 2 coercion, EVar(x) → NVar(x) directly.
            assert!(
                matches!(arg.as_ref(), Num::NVar(_)),
                "expected NVar (var-aware projection) inside FactNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected FactNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
}

/// P2.6: Explicit prefix cast remains available under keyword/identifier lex forks
#[test]
fn test_p2_6_explicit_prefix_cast_keyword() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("to_num(a)").expect("should parse explicit to_num prefix cast");
    match &result {
        Num::ExprToNum(expr) => {
            assert!(matches!(expr.as_ref(), Expr::EVar(_)), "expected EVar body, got: {:?}", expr);
        },
        other => panic!("expected ExprToNum at top, got: {:?}", other),
    }
}

/// P2.7: Explicit prefix cast can seed a cross-category LED comparison
#[test]
fn test_p2_7_prefix_cast_cross_category_comparison() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("to_num(a) != 1!")
        .expect("should parse to_num prefix cast followed by cross-category comparison");
    if let Expr::CastPred(pred) = &result {
        if let lt::Pred::NeNum(left, right) = pred.as_ref() {
            assert!(
                matches!(left.as_ref(), Num::ExprToNum(_)),
                "expected explicit ExprToNum on comparison lhs, got: {:?}",
                left
            );
            assert!(
                matches!(right.as_ref(), Num::FactNum(_)),
                "expected FactNum on comparison rhs, got: {:?}",
                right
            );
        } else {
            panic!("expected NeNum at top of predicate, got: {:?}", pred);
        }
    } else {
        panic!("expected CastPred wrapper, got: {:?}", result);
    }
}

/// P2.8: Pred comparison accepts displayed nested Num chains at EOI
#[test]
fn test_p2_8_pred_display_nested_num_comparison() {
    mettail_runtime::clear_var_cache();
    let result = lt::Pred::parse(
        "1391970874 + 1944498665 + 624576185 * 1972797575 != -(137741760 + 424548178)",
    )
    .expect("should parse nested numeric comparison as Pred");
    assert!(matches!(result, lt::Pred::NeNum(_, _)), "expected NeNum, got: {:?}", result);
}

/// P2.9: Display keeps transparent CastPred grouped under an Expr operator
#[test]
fn test_p2_9_expr_display_groups_transparent_cast_pred_operand() {
    mettail_runtime::clear_var_cache();
    let term = Expr::EPar(
        Arc::new(Expr::CastNum(Arc::new(Num::MulNum(
            Arc::new(Num::NumLit(1699326936)),
            Arc::new(Num::NumLit(682111741)),
        )))),
        Arc::new(Expr::CastPred(Arc::new(lt::Pred::EqNum(
            Arc::new(Num::NumLit(575184559)),
            Arc::new(Num::NumLit(1857751180)),
        )))),
    );
    let displayed = format!("{}", term);
    assert_eq!(displayed, "(1699326936 * 682111741) | (575184559 == 1857751180)");
    Expr::parse(&displayed).expect("displayed Expr should parse");
}

/// P2.10: Display keeps transparent PredToNum grouped under a Pred comparison
#[test]
fn test_p2_10_pred_display_groups_transparent_pred_to_num_operand() {
    mettail_runtime::clear_var_cache();
    let var = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        mettail_runtime::get_or_create_var("a"),
    ));
    let term = lt::Pred::NeNum(
        Arc::new(Num::NumLit(2065782020)),
        Arc::new(Num::PredToNum(Arc::new(lt::Pred::EqNum(
            Arc::new(Num::NumLit(65396207)),
            Arc::new(Num::MulNum(
                Arc::new(Num::ExprToNum(Arc::new(Expr::EVar(var)))),
                Arc::new(Num::NegNum(Arc::new(Num::NumLit(1426318814)))),
            )),
        )))),
    );
    let displayed = format!("{}", term);
    assert_eq!(displayed, "2065782020 != to_num(65396207 == to_num(a) * -1426318814)");
    lt::Pred::parse(&displayed).expect("displayed Pred should parse");
}

/// P2.11: Display keeps transparent PredToNum grouped under Num prefix
#[test]
fn test_p2_11_num_display_groups_transparent_pred_to_num_operand() {
    mettail_runtime::clear_var_cache();
    let term = Num::NegNum(Arc::new(Num::PredToNum(Arc::new(lt::Pred::AndPred(
        Arc::new(lt::Pred::BoolLit(true)),
        Arc::new(lt::Pred::BoolLit(false)),
    )))));
    let displayed = format!("{}", term);
    assert_eq!(displayed, "-to_num(true and false)");
    Num::parse(&displayed).expect("displayed Num should parse");
}

/// P2.12: Parenthesized Pred comparison accepts a postfix Num LHS
#[test]
fn test_p2_12_grouped_pred_comparison_accepts_postfix_num_lhs() {
    mettail_runtime::clear_var_cache();
    let result = lt::Pred::parse("(368158551! != 730148310) and (322479346 != -1467730788)")
        .expect("grouped Pred comparison with postfix Num LHS should parse");
    assert!(matches!(result, lt::Pred::AndPred(_, _)), "expected AndPred, got: {:?}", result);
}

/// P2.13: Explicit ExprToNum accepts an Expr body with its own operator
#[test]
fn test_p2_13_explicit_to_num_accepts_expr_operator_body() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("to_num(a | a) * (true and false)")
        .expect("explicit to_num body with Expr operator should parse");
    assert!(matches!(result, Num::MulNum(_, _)), "expected MulNum, got: {:?}", result);
}

/// P2.14: Grouped Num source can continue as a category-changing Pred comparison
#[test]
fn test_p2_14_grouped_num_source_pred_postfix_comparison() {
    mettail_runtime::clear_var_cache();
    let result = lt::Pred::parse("(-182258397)! != (-182258397)!")
        .expect("grouped Num source should feed postfix and Pred comparison");
    assert!(matches!(result, lt::Pred::NeNum(_, _)), "expected NeNum, got: {:?}", result);
}

/// P2.15: Grouped Num sources inside Expr can continue through Expr's own operator
#[test]
fn test_p2_15_expr_grouped_num_sources_continue_to_expr_operator() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("(1503349600 + 1117011807) | (605514027!)")
        .expect("grouped Num sources should parse as Expr operands around |");
    assert!(matches!(result, Expr::EPar(_, _)), "expected EPar, got: {:?}", result);
}

/// P2.16: Pred comparison RHS accepts Num chains ending in explicit PredToNum
#[test]
fn test_p2_16_pred_rhs_num_chain_ending_in_explicit_pred_to_num() {
    mettail_runtime::clear_var_cache();
    let result =
        lt::Pred::parse("-(900818811 + 776447971) != 1382488656 * 1779238132 * to_num(false)")
            .expect("Pred comparison should accept RHS Num chain ending in explicit to_num");
    assert!(matches!(result, lt::Pred::NeNum(_, _)), "expected NeNum, got: {:?}", result);
}

// ============================================================================
// Edge Case Tests
// ============================================================================

/// E1: Prefix only, no LED — delegation not invoked
#[test]
fn test_e1_prefix_only() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1").expect("should parse literal 1 as Expr");
    assert!(
        matches!(result, Expr::CastNum(_)),
        "expected CastNum wrapper for literal, got: {:?}",
        result
    );
}

/// E2: Variable only, no LED — delegation not invoked
#[test]
fn test_e2_variable_only() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x");
    assert!(result.is_ok(), "should parse bare variable x as Expr");
}

/// E3: Own operator only — "1 | 2", delegation not needed for "|"
#[test]
fn test_e3_own_operator_only() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("1 | 2").expect("should parse own operator |");
    assert!(matches!(result, Expr::EPar(_, _)), "expected EPar at top, got: {:?}", result);
}

/// E4: Parenthesized variable — "(x)"
#[test]
fn test_e4_parenthesized_variable() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("(x)");
    assert!(result.is_ok(), "should parse parenthesized variable (x)");
}

/// E5: Own operator with unknown variants — "x | y"
#[test]
fn test_e5_own_op_with_unknown_variants() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x | y").expect("should parse x | y using Expr's own operator");
    assert!(matches!(result, Expr::EPar(_, _)), "expected EPar for x | y, got: {:?}", result);
}

// ============================================================================
// Normalization Tests (via Ascent)
// ============================================================================

// ============================================================================
// Constituent-Level Parse Tests (verify Num::parse still works independently)
// ============================================================================

/// Num-level: "1 + 2" parses directly as Num (no delegation needed)
#[test]
fn test_num_level_infix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("1 + 2").expect("should parse 1 + 2 as Num");
    assert!(matches!(result, Num::AddNum(_, _)), "expected AddNum, got: {:?}", result);
}

/// Num-level: "3!" parses directly as Num
#[test]
fn test_num_level_postfix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("3!").expect("should parse 3! as Num");
    assert!(matches!(result, Num::FactNum(_)), "expected FactNum, got: {:?}", result);
}

/// Num-level: "-3" parses directly as Num
#[test]
fn test_num_level_unary_prefix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("-3").expect("should parse -3 as Num");
    assert!(matches!(result, Num::NegNum(_)), "expected NegNum, got: {:?}", result);
}

/// Num-level: eval works
#[test]
fn test_num_level_eval() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("3").expect("should parse 3");
    assert_eq!(result.eval(), 3);
}
