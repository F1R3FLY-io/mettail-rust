#![cfg(feature = "led-test")]
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
use mettail_runtime::Language;

/// Parse input as the LedTest language term, run Ascent, and check that
/// `expected_display` is among the normal forms.
fn led_normal_form(input: &str, expected_display: &str) {
    mettail_runtime::clear_var_cache();
    let lang = lt::LedTestLanguage;
    let term = lang.parse_term(input).unwrap_or_else(|e| panic!("parse {:?}: {}", input, e));
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<String> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect();
    assert!(
        displays.contains(&expected_display.to_string()),
        "expected normal form {:?} for {:?}, got: {:?}",
        expected_display,
        input,
        displays
    );
}

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
            assert!(
                matches!(left.as_ref(), Num::ExprToNum(_)),
                "expected ExprToNum (auto-projection) as left of AddNum, got: {:?}",
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
            assert!(
                matches!(left.as_ref(), Num::ExprToNum(_)),
                "expected ExprToNum as left of EqNum, got: {:?}",
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
    assert!(
        matches!(result, Expr::EPar(_, _)),
        "expected EPar at top, got: {:?}",
        result
    );
}

/// P2.5: Variable + postfix — "x!" → CastNum(FactNum(ExprToNum(ExprVar(x))))
#[test]
fn test_p2_5_auto_project_postfix() {
    mettail_runtime::clear_var_cache();
    let result = Expr::parse("x!").expect("should parse x! via auto-projection");
    if let Expr::CastNum(inner) = &result {
        if let Num::FactNum(arg) = inner.as_ref() {
            assert!(
                matches!(arg.as_ref(), Num::ExprToNum(_)),
                "expected ExprToNum inside FactNum, got: {:?}",
                inner
            );
        } else {
            panic!("expected FactNum at top, got: {:?}", inner);
        }
    } else {
        panic!("expected CastNum wrapper, got: {:?}", result);
    }
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
    assert!(
        matches!(result, Expr::EPar(_, _)),
        "expected EPar at top, got: {:?}",
        result
    );
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
    assert!(
        matches!(result, Expr::EPar(_, _)),
        "expected EPar for x | y, got: {:?}",
        result
    );
}

// ============================================================================
// Normalization Tests (via Ascent)
// ============================================================================

/// N1: "1 + 2" normalizes to "3" via AddNum's step native code
#[test]
fn test_n1_add_normalizes() {
    led_normal_form("1 + 2", "3");
}

/// N2: "3!" normalizes to "6" via FactNum's step native code
#[test]
fn test_n2_factorial_normalizes() {
    led_normal_form("3!", "6");
}

/// N3: "1 == 1" normalizes to "true" via EqNum's step native code
#[test]
fn test_n3_eq_normalizes() {
    led_normal_form("1 == 1", "true");
}

/// N4: "1 + 2 == 3" normalizes to "true" (chained delegation normalizes)
#[test]
fn test_n4_chained_normalizes() {
    led_normal_form("1 + 2 == 3", "true");
}

// ============================================================================
// Constituent-Level Parse Tests (verify Num::parse still works independently)
// ============================================================================

/// Num-level: "1 + 2" parses directly as Num (no delegation needed)
#[test]
fn test_num_level_infix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("1 + 2").expect("should parse 1 + 2 as Num");
    assert!(
        matches!(result, Num::AddNum(_, _)),
        "expected AddNum, got: {:?}",
        result
    );
}

/// Num-level: "3!" parses directly as Num
#[test]
fn test_num_level_postfix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("3!").expect("should parse 3! as Num");
    assert!(
        matches!(result, Num::FactNum(_)),
        "expected FactNum, got: {:?}",
        result
    );
}

/// Num-level: "-3" parses directly as Num
#[test]
fn test_num_level_unary_prefix() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("-3").expect("should parse -3 as Num");
    assert!(
        matches!(result, Num::NegNum(_)),
        "expected NegNum, got: {:?}",
        result
    );
}

/// Num-level: eval works
#[test]
fn test_num_level_eval() {
    mettail_runtime::clear_var_cache();
    let result = Num::parse("3").expect("should parse 3");
    assert_eq!(result.eval(), 3);
}
