//! Systematic test suite for the RhoCalc language.
//!
//! Organized by feature area:
//! - **comm**: Communication (single-input, multi-input, join patterns)
//! - **new_and_extrusion**: PNew binder and scope extrusion equation
//! - **congruence**: Rewrite propagation through constructors
//! - **native_ops**: Embedded Rust-native arithmetic, booleans, strings
//! - **parsing**: Basic parsing and round-trip tests
//! - **beta**: Lambda/dollar-syntax beta-reduction

use mettail_languages::rhocalc::*;
use mettail_runtime::Language;

// ════════════════════════════════════════════════════════════════════════════════
// Test helpers
// ════════════════════════════════════════════════════════════════════════════════

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{}`: {}", input, e))
}

fn fresh() {
    mettail_runtime::clear_var_cache();
}

// ════════════════════════════════════════════════════════════════════════════════
// Communication
// ════════════════════════════════════════════════════════════════════════════════

mod comm {
    use super::*;

    /// Reproduces REPL load_env parse error: PPar with a!(n) must not reduce "a" to variable.
    #[test]
    fn par_with_output_literal() {
        let _ = parse("{ a!(2) | b!(3) }");
    }

}

// ════════════════════════════════════════════════════════════════════════════════
// PNew binder and scope extrusion
// ════════════════════════════════════════════════════════════════════════════════

mod new_and_extrusion {
    use super::*;

    #[test]
    fn new_parses() {
        let _p = parse("new(x) in { x!(0) }");
    }

    #[test]
    fn new_multi_binder_parses() {
        let _p = parse("new(x, y) in { {x!(0) | y!(1)} }");
    }

}

// ════════════════════════════════════════════════════════════════════════════════
// Congruence (rewrite propagation)
// ════════════════════════════════════════════════════════════════════════════════

mod congruence {
    

}

// ════════════════════════════════════════════════════════════════════════════════
// Exec (drop-quote cancellation)
// ════════════════════════════════════════════════════════════════════════════════

mod exec {
    

}

// ════════════════════════════════════════════════════════════════════════════════
// Native operations (embedded Rust code)
// ════════════════════════════════════════════════════════════════════════════════

mod native_ops {
    

    mod arithmetic {
        

    }

    mod bitwise {
        

    }

    mod comparison {
        

    }

    mod boolean {
        

    }

    mod string {
        

    }

    mod bag {
        

    }

    mod map {
        

    }

    mod type_conversion {
        

    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Parsing
// ════════════════════════════════════════════════════════════════════════════════

mod parsing {
    use super::*;

    #[test]
    fn bare_variable_infers_as_proc() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("p").expect("parse");
        let term_type = lang.infer_term_type(term.as_ref());
        assert_eq!(format!("{}", term_type), "Proc");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Beta-reduction (lambda / dollar-syntax)
// ════════════════════════════════════════════════════════════════════════════════

mod beta {
    use super::*;

    #[test]
    fn dollar_name_reduces() {
        fresh();
        let term = parse("$name(^loc.{loc!(init)}, n)");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "n!(init)");
    }

    #[test]
    fn dollar_proc_reduces() {
        fresh();
        let term = parse("$proc(^f.{f}, {})");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "{}");
    }

    #[test]
    fn normalize_via_language_trait() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term("$name(^loc.{loc!(init)}, n)")
            .expect("parse");
        let normalized = lang.normalize_term(term.as_ref());
        assert_eq!(format!("{}", normalized), "n!(init)");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Numeric casts (`int`, `uint`, … on Proc)
// ════════════════════════════════════════════════════════════════════════════════

// ════════════════════════════════════════════════════════════════════════════════
// Type inference
// ════════════════════════════════════════════════════════════════════════════════

mod type_inference {
    use super::*;

    #[test]
    fn pinputs_infers_bound_var() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(x?y).{*(y)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        let y_info = var_types.iter().find(|v| v.name == "y");
        assert!(y_info.is_some(), "y should be found, got: {:?}", var_types);
        assert_eq!(format!("{}", y_info.unwrap().ty), "Name");
    }

    #[test]
    fn pinputs_lookup_by_name() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(x?y).{*(y)}").expect("parse");
        let y_type = lang.infer_var_type(term.as_ref(), "y");
        assert!(y_type.is_some());
        assert_eq!(format!("{}", y_type.unwrap()), "Name");
    }

    #[test]
    fn multi_input_infers_both_vars() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(c1?x, c2?y).{*(x)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        assert!(var_types.iter().any(|v| v.name == "x"));
        assert!(var_types.iter().any(|v| v.name == "y"));
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Collection-primary infix binding power (2026-06-18 fix)
// ════════════════════════════════════════════════════════════════════════════════
//
// Regression for the general defect where a collection primary that is NOT at
// the parse root (cast argument, list element, any mid-parse frame) could not
// attach any infix operator. Root cause: a collection finalized by popping its
// CollectionMarker to `Unwinding`, never re-entering the enclosing Pratt
// `InfixLoop` (unlike an atomic primary's `Return`-pop). Fix: the collection
// close resumes `InfixLoop { cur_bp: dispatch_bp }`, where dispatch_bp is the
// Pratt bp captured on the marker at open. See
// docs/design/collection-primary-infix-fix.md and
// formal/rocq/prattail_wpda_runtime/theories/CollectionPrimaryInfix.v.
mod collection_primary_infix {
    use super::*;

    #[test]
    fn ppar_lteq_in_cast() {
        // THE reported bug: `str({a} <= {a})` was `1:5 no accepting branch ...
        // Fixed({)`. A PPar collection primary as the LHS of `<=` inside a
        // same-category `str` cast (invisible to the cross-cat-LHS machinery).
        let p = parse("str({a} <= {a})");
        match &p {
            Proc::ToStr(inner) => assert!(
                matches!(inner.as_ref(), Proc::LtEq(_, _)),
                "expected ToStr(LtEq(..)), got ToStr({:?})",
                inner
            ),
            other => panic!("expected ToStr(LtEq(..)), got {:?}", other),
        }
    }

    #[test]
    fn collection_comparison_as_list_element() {
        // A collection-comparison as a list element: `[{a} <= {a}]` — the
        // collection primary is mid-parse (inside the list element), another
        // non-root position the fix covers.
        let p = parse("[{a} <= {a}]");
        assert!(
            matches!(&p, Proc::CastList(_)),
            "expected CastList([LtEq(..)]), got {:?}",
            p
        );
    }

    #[test]
    fn precedence_lock_collection_in_add_rhs() {
        // Precedence soundness: `+` binds tighter than `<=`, so the collection
        // primary {a} must associate with `+`:
        //   1 + {a} <= {b}  ==  LtEq(Add(1, {a}), {b})   (NOT Add(1, LtEq(..)))
        // The dispatch-bp threading (not the naive close-branch edit) is what
        // prevents the inversion: {a} closes at cur_bp = Add.r_bp, and
        // LtEq.l_bp <= Add.r_bp, so `<=` does NOT attach inside the Add RHS.
        let p = parse("1 + {a} <= {b}");
        match &p {
            Proc::LtEq(lhs, _rhs) => assert!(
                matches!(lhs.as_ref(), Proc::Add(_, _)),
                "precedence inversion: expected LtEq(Add(..), ..), got LtEq({:?}, ..)",
                lhs
            ),
            other => panic!("expected top-level LtEq, got {:?}", other),
        }
    }

    #[test]
    fn precedence_lock_inside_cast() {
        // Same precedence law nested in a cast: `str({a} + {b} <= {c})` must be
        // `str(LtEq(Add({a},{b}), {c}))`, NOT `str(Add({a}, LtEq({b},{c})))`.
        let p = parse("str({a} + {b} <= {c})");
        match &p {
            Proc::ToStr(inner) => match inner.as_ref() {
                Proc::LtEq(lhs, _) => assert!(
                    matches!(lhs.as_ref(), Proc::Add(_, _)),
                    "expected str(LtEq(Add(..), ..)), got str(LtEq({:?}, ..))",
                    lhs
                ),
                other => panic!("expected str(LtEq(..)), got str({:?})", other),
            },
            other => panic!("expected ToStr(LtEq(..)), got {:?}", other),
        }
    }
}
