//! Bounded recursive references for the surface Rholang guard encoder.
//!
//! Production uses explicit pushdown drivers. These equations retain the superseded recursive
//! behavior only under `cfg(test)` so shallow equivalence can be checked independently.

use super::*;
use mettail_runtime::get_or_create_var;

fn formula_recursive(encoder: &mut Encoder, cond: &Proc) -> GuardFormula {
    match cond {
        Proc::CastBool(literal) => match literal.as_ref() {
            Bool::BoolLit(true) => GuardFormula::True,
            Bool::BoolLit(false) => GuardFormula::False,
            #[allow(unreachable_patterns)]
            _ => encoder.opaque_atom(cond, GuardAtomKind::Uncovered, OpaquePosition::Predicate),
        },
        Proc::And(left, right) => {
            GuardFormula::and(formula_recursive(encoder, left), formula_recursive(encoder, right))
        },
        Proc::Or(left, right) => {
            GuardFormula::or(formula_recursive(encoder, left), formula_recursive(encoder, right))
        },
        Proc::Not(inner) => GuardFormula::not(formula_recursive(encoder, inner)),
        Proc::Implies(left, right) => GuardFormula::implies(
            formula_recursive(encoder, left),
            formula_recursive(encoder, right),
        ),
        Proc::Eq(left, right) => encoder.comparison(CmpOp::Eq, left, right, cond),
        Proc::Ne(left, right) => encoder.comparison(CmpOp::Ne, left, right, cond),
        Proc::Lt(left, right) => encoder.comparison(CmpOp::Lt, left, right, cond),
        Proc::LtEq(left, right) => encoder.comparison(CmpOp::Le, left, right, cond),
        Proc::Gt(left, right) => encoder.comparison(CmpOp::Gt, left, right, cond),
        Proc::GtEq(left, right) => encoder.comparison(CmpOp::Ge, left, right, cond),
        Proc::Matches(_, _) => {
            encoder.opaque_atom(cond, GuardAtomKind::Spatial, OpaquePosition::Predicate)
        },
        Proc::PVar(var) => match var_key(var) {
            Some(key) => {
                encoder.vars.intern(&key);
                GuardFormula::Prop(prop_var(&key))
            },
            None => encoder.opaque_atom(cond, GuardAtomKind::Uncovered, OpaquePosition::Predicate),
        },
        other => {
            encoder.opaque_atom(cond, classify_uncovered(other), OpaquePosition::NotAPredicate)
        },
    }
}

fn operand_recursive(encoder: &mut Encoder, term: &Proc) -> Operand {
    match term {
        Proc::CastInt(value) => match value.as_ref() {
            Int::NumLit(value) => Operand::Int(LinearForm::constant(*value)),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastUInt32(value) => match value.as_ref() {
            UInt32::NumLit(value) => Operand::Int(LinearForm::constant(i64::from(*value))),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastBigInt(value) => match value.as_ref() {
            BigInt::NumLit(value) => Operand::Lit(GuardValue::BigInt(value.get().clone())),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastBool(value) => match value.as_ref() {
            Bool::BoolLit(value) => Operand::Lit(GuardValue::Bool(*value)),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastStr(value) => match value.as_ref() {
            Str::StringLit(value) => Operand::Lit(GuardValue::Str(value.clone())),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastBigRat(value) => match value.as_ref() {
            BigRat::RatLit(value) => Operand::Lit(GuardValue::BigRat(value.get().clone())),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastFixed(value) => match value.as_ref() {
            Fixed::FixedLit(value) => Operand::Lit(GuardValue::Fixed(fixed_to_rational(value))),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::CastFloat(value) => match value.as_ref() {
            Float::FloatLit(value) => Operand::Lit(GuardValue::Float(
                mettail_prattail::ordered_field::OrderedF64(value.get()),
            )),
            #[allow(unreachable_patterns)]
            _ => Operand::Uncovered,
        },
        Proc::PVar(var) => match var_key(var) {
            Some(key) => Operand::Var(encoder.vars.intern(&key)),
            None => Operand::Uncovered,
        },
        Proc::Add(left, right) => arithmetic_recursive(encoder, left, right, LinearForm::add),
        Proc::Sub(left, right) => arithmetic_recursive(encoder, left, right, LinearForm::sub),
        Proc::Mul(left, right) => {
            match (int_form_recursive(encoder, left), int_form_recursive(encoder, right)) {
                (Some(left), Some(right)) if left.is_constant() => scaled(&right, left.constant),
                (Some(left), Some(right)) if right.is_constant() => scaled(&left, right.constant),
                (Some(_), Some(_)) => Operand::NonLinear,
                _ => Operand::Uncovered,
            }
        },
        Proc::Div(left, right) => {
            integer_division_recursive(encoder, left, right, i64::checked_div)
        },
        Proc::Mod(left, right) => {
            integer_division_recursive(encoder, left, right, i64::checked_rem)
        },
        Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_) => {
            Operand::Structural
        },
        _ => Operand::Uncovered,
    }
}

fn arithmetic_recursive(
    encoder: &mut Encoder,
    left: &Proc,
    right: &Proc,
    combine: fn(&LinearForm, &LinearForm) -> Option<LinearForm>,
) -> Operand {
    match (int_form_recursive(encoder, left), int_form_recursive(encoder, right)) {
        (Some(left), Some(right)) => match combine(&left, &right) {
            Some(form) => Operand::Int(form),
            None => Operand::NonLinear,
        },
        _ => Operand::Uncovered,
    }
}

fn integer_division_recursive(
    encoder: &mut Encoder,
    left: &Proc,
    right: &Proc,
    combine: fn(i64, i64) -> Option<i64>,
) -> Operand {
    match (int_form_recursive(encoder, left), int_form_recursive(encoder, right)) {
        (Some(left), Some(right)) if left.is_constant() && right.is_constant() => {
            match combine(left.constant, right.constant) {
                Some(value) => Operand::Int(LinearForm::constant(value)),
                None => Operand::NonLinear,
            }
        },
        (Some(_), Some(_)) => Operand::NonLinear,
        _ => Operand::Uncovered,
    }
}

fn int_form_recursive(encoder: &mut Encoder, term: &Proc) -> Option<LinearForm> {
    match operand_recursive(encoder, term) {
        Operand::Int(form) => Some(form),
        Operand::Var(index) => Some(LinearForm::var(index)),
        _ => None,
    }
}

fn int(value: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(value)))
}

fn boolean(value: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(value)))
}

fn string(value: &str) -> Proc {
    Proc::CastStr(Arc::new(Str::StringLit(value.to_string())))
}

fn var(name: &str) -> Proc {
    Proc::PVar(OrdVar(Var::Free(get_or_create_var(name))))
}

fn arc(proc: Proc) -> Arc<Proc> {
    Arc::new(proc)
}

fn encoder() -> Encoder {
    Encoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    }
}

#[test]
fn surface_guard_drivers_match_the_bounded_recursive_oracles() {
    let formula_corpus = vec![
        boolean(true),
        boolean(false),
        Proc::Not(arc(boolean(true))),
        Proc::And(arc(Proc::PZero), arc(Proc::Matches(arc(int(1)), arc(int(1))))),
        Proc::Or(arc(var("left")), arc(var("right"))),
        Proc::Implies(
            arc(Proc::Eq(arc(var("x")), arc(int(1)))),
            arc(Proc::Lt(arc(var("x")), arc(int(2)))),
        ),
        Proc::PZero,
    ];
    for (index, proc) in formula_corpus.iter().enumerate() {
        let mut driven = encoder();
        let mut recursive = encoder();
        let driven_formula = driven.formula(proc);
        let recursive_formula = formula_recursive(&mut recursive, proc);
        assert_eq!(
            format!("{driven_formula:?}"),
            format!("{recursive_formula:?}"),
            "formula traversal differs at corpus index {index}"
        );
        assert_eq!(format!("{:?}", driven.vars), format!("{:?}", recursive.vars));
        assert_eq!(format!("{:?}", driven.opaque), format!("{:?}", recursive.opaque));
    }

    let operand_corpus = vec![
        int(0),
        int(i64::MIN),
        Proc::CastUInt32(Arc::new(UInt32::NumLit(7))),
        boolean(true),
        string("text"),
        var("x"),
        Proc::Add(arc(var("x")), arc(var("y"))),
        Proc::Add(arc(int(i64::MAX)), arc(int(1))),
        Proc::Sub(arc(var("x")), arc(int(1))),
        Proc::Mul(arc(int(3)), arc(var("x"))),
        Proc::Mul(arc(var("x")), arc(var("y"))),
        Proc::Div(arc(int(12)), arc(int(3))),
        Proc::Div(arc(int(1)), arc(int(0))),
        Proc::Div(arc(var("x")), arc(int(2))),
        Proc::Mod(arc(int(13)), arc(int(5))),
        Proc::PZero,
    ];
    for (index, proc) in operand_corpus.iter().enumerate() {
        let mut driven = encoder();
        let mut recursive = encoder();
        let driven_operand = driven.operand(proc);
        let recursive_operand = operand_recursive(&mut recursive, proc);
        assert_eq!(
            format!("{driven_operand:?}"),
            format!("{recursive_operand:?}"),
            "operand traversal differs at corpus index {index}"
        );
        assert_eq!(format!("{:?}", driven.vars), format!("{:?}", recursive.vars));
    }
}

#[test]
fn surface_guard_drivers_are_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("surface-guard-drivers-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut formula = boolean(true);
            for _ in 0..DEPTH {
                formula = Proc::Not(arc(formula));
            }
            assert!(matches!(
                encode_guard(&formula).formula,
                GuardFormula::True | GuardFormula::False
            ));

            let mut operand = var("deep");
            for _ in 0..DEPTH {
                operand = Proc::Add(arc(operand), arc(int(1)));
            }
            let mut encoder = encoder();
            assert!(matches!(encoder.operand(&operand), Operand::Int(_)));
        })
        .expect("spawn surface guard depth gate")
        .join()
        .expect("surface guard drivers must not overflow or panic");
}
