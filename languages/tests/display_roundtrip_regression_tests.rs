//! Regression coverage for display strings that must remain parseable through
//! the WPDA pipeline.

// Task #11 (extended 2026-07-26): the FIXTURE grammars exercised here are not production
// languages, so their definitions live in `languages/tests/definitions/` and are
// `#[path]`-included rather than named through `mettail_languages::<lang>`. This binary is a
// CONSUMER of each: it deliberately does NOT invoke any `<lang>_generated_tests!` wrapper,
// because each definition's DESIGNATED HOST (its own smoke-test binary) is the sole invoker,
// so the generated suites stay single-instanced across the workspace.
//
// The per-test `#[cfg(feature = "<lang>")]` gates that used to guard these cases are removed
// with the features themselves. Keeping them would be the silent-failure mode this whole
// relocation has to avoid: an unsatisfiable `cfg` deletes the test rather than failing.
#[path = "definitions/class2multi.rs"]
mod class2multi;
#[path = "definitions/class3multi.rs"]
mod class3multi;
#[path = "definitions/class3opt.rs"]
mod class3opt;

macro_rules! assert_wpda_display_roundtrip {
    ($ty:ty, $term:expr) => {{
        let term: $ty = $term;
        let displayed = format!("{}", term);
        let parsed = <$ty>::parse_via_wpda(&displayed)
            .unwrap_or_else(|err| panic!("WPDA failed to parse `{}`: {:?}", displayed, err));
        assert_eq!(displayed, format!("{}", parsed));
    }};
}

#[test]
fn class2multi_pair_collection_display_roundtrips() {
    use crate::class2multi::Proc;

    assert_wpda_display_roundtrip!(
        Proc,
        Proc::Pair(vec![Proc::PZero], vec![Proc::PZero, Proc::PZero])
    );
}

#[test]
fn class3multi_tagged_inputs_display_roundtrips() {
    use crate::class3multi::{Name, Proc};
    use mettail_runtime::{get_or_create_var, Binder, Scope};
    use std::sync::Arc;

    mettail_runtime::clear_var_cache();
    let scope = Scope::from_parts_unsafe(
        vec![Binder(get_or_create_var("x"))],
        Arc::new(Proc::TaggedInputs(
            vec![Proc::PZero],
            vec![Name::NQuote(Arc::new(Proc::PZero))],
            Scope::from_parts_unsafe(vec![Binder(get_or_create_var("y"))], Arc::new(Proc::PZero)),
        )),
    );

    assert_wpda_display_roundtrip!(
        Proc,
        Proc::TaggedInputs(
            vec![Proc::PZero, Proc::PZero],
            vec![Name::NQuote(Arc::new(Proc::PZero))],
            scope
        )
    );
}

#[test]
fn class3multi_quoted_tagged_inputs_display_roundtrips() {
    use crate::class3multi::{Name, Proc};
    use mettail_runtime::{get_or_create_var, Binder, Scope};
    use std::sync::Arc;

    mettail_runtime::clear_var_cache();
    let scope =
        Scope::from_parts_unsafe(vec![Binder(get_or_create_var("x"))], Arc::new(Proc::PZero));
    let proc = Proc::TaggedInputs(vec![], vec![Name::NQuote(Arc::new(Proc::PZero))], scope);

    assert_wpda_display_roundtrip!(Name, Name::NQuote(Arc::new(proc)));
}

#[test]
fn class3opt_optional_collection_display_roundtrips() {
    use crate::class3opt::{Name, Proc};
    use mettail_runtime::{get_or_create_var, Binder, Scope};
    use std::sync::Arc;

    mettail_runtime::clear_var_cache();
    let scope =
        Scope::from_parts_unsafe(vec![Binder(get_or_create_var("x"))], Arc::new(Proc::PZero));

    assert_wpda_display_roundtrip!(
        Proc,
        Proc::PInputsOptTagged(
            vec![Name::NQuote(Arc::new(Proc::PZero))],
            Some(vec![Proc::PZero, Proc::PZero]),
            scope
        )
    );
}

#[test]
fn class3opt_quoted_optional_collection_display_roundtrips() {
    use crate::class3opt::{Name, Proc};
    use mettail_runtime::{get_or_create_var, Binder, Scope};
    use std::sync::Arc;

    mettail_runtime::clear_var_cache();
    let scope =
        Scope::from_parts_unsafe(vec![Binder(get_or_create_var("x"))], Arc::new(Proc::PZero));
    let proc = Proc::PInputsOptTagged(vec![], Some(vec![Proc::PZero]), scope);

    assert_wpda_display_roundtrip!(Name, Name::NQuote(Arc::new(proc)));
}

#[cfg(feature = "guarded-rho")]
#[test]
fn guardedrho_parallel_and_quote_display_roundtrip() {
    use mettail_languages::guardedrho::{Name, Proc};
    use mettail_runtime::{get_or_create_var, HashBag, OrdVar, Var};
    use std::sync::Arc;

    mettail_runtime::clear_var_cache();
    let var = Proc::PVar(OrdVar(Var::Free(get_or_create_var("a"))));
    let bag = HashBag::from_iter([var.clone(), var.clone()]);

    assert_wpda_display_roundtrip!(Proc, Proc::PPar(bag));
    assert_wpda_display_roundtrip!(Name, Name::NQuote(Arc::new(var)));
}

#[cfg(feature = "led-test")]
#[test]
fn ledtest_unary_and_cross_category_display_roundtrips() {
    use mettail_languages::ledtest::{Expr, Num, Pred};
    use std::sync::Arc;

    assert_wpda_display_roundtrip!(Num, Num::NegNum(Arc::new(Num::NumLit(1_296_911_694))));
    assert_wpda_display_roundtrip!(
        Num,
        Num::PredToNum(Arc::new(Pred::EqNum(
            Arc::new(Num::PredToNum(Arc::new(Pred::BoolLit(true)))),
            Arc::new(Num::PredToNum(Arc::new(Pred::BoolLit(true))))
        )))
    );
    assert_wpda_display_roundtrip!(
        Pred,
        Pred::AndPred(
            Arc::new(Pred::EqNum(
                Arc::new(Num::NegNum(Arc::new(Num::NumLit(0)))),
                Arc::new(Num::NumLit(0))
            )),
            Arc::new(Pred::BoolLit(false))
        )
    );
    assert_wpda_display_roundtrip!(
        Expr,
        Expr::CastNum(Arc::new(Num::AddNum(
            Arc::new(Num::PredToNum(Arc::new(Pred::BoolLit(true)))),
            Arc::new(Num::AddNum(
                Arc::new(Num::NumLit(1_275_159_884)),
                Arc::new(Num::NumLit(1_699_479_909))
            ))
        )))
    );
}

#[cfg(feature = "composition")]
#[test]
fn mixedmath_unary_and_cross_category_display_roundtrips() {
    use mettail_languages::mixedmath::{Bool, Int};
    use std::sync::Arc;

    assert_wpda_display_roundtrip!(Int, Int::Neg(Arc::new(Int::NumLit(1_280_068_684))));
    assert_wpda_display_roundtrip!(Bool, Bool::Not(Arc::new(Bool::BoolLit(true))));
    assert_wpda_display_roundtrip!(
        Int,
        Int::BoolToInt(Arc::new(Bool::Or(
            Arc::new(Bool::And(Arc::new(Bool::BoolLit(true)), Arc::new(Bool::BoolLit(false)))),
            Arc::new(Bool::And(Arc::new(Bool::BoolLit(true)), Arc::new(Bool::BoolLit(false))))
        )))
    );
}
