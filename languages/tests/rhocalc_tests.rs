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
