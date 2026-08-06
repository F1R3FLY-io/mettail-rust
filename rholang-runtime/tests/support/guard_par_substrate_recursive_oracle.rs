//! Bounded recursive references for the lowered guard encoder.
//!
//! Production uses explicit pushdown drivers. These functions preserve the superseded recursive
//! equations only under `cfg(test)`, so shallow equivalence can be checked without retaining a
//! recursive fallback in the runtime.

use super::*;

fn substitute_atoms_recursive(
    formula: &GuardFormula,
    atoms: &[GuardAtom],
    resolved: &[Option<bool>],
) -> Option<GuardFormula> {
    Some(match formula {
        GuardFormula::Atom(atom) => {
            let index = atoms.iter().position(|candidate| candidate == atom)?;
            match resolved.get(index).copied().flatten()? {
                true => GuardFormula::True,
                false => GuardFormula::False,
            }
        },
        GuardFormula::And(left, right) => GuardFormula::and(
            substitute_atoms_recursive(left, atoms, resolved)?,
            substitute_atoms_recursive(right, atoms, resolved)?,
        ),
        GuardFormula::Or(left, right) => GuardFormula::or(
            substitute_atoms_recursive(left, atoms, resolved)?,
            substitute_atoms_recursive(right, atoms, resolved)?,
        ),
        GuardFormula::Not(inner) => {
            GuardFormula::not(substitute_atoms_recursive(inner, atoms, resolved)?)
        },
        GuardFormula::Implies(left, right) => GuardFormula::implies(
            substitute_atoms_recursive(left, atoms, resolved)?,
            substitute_atoms_recursive(right, atoms, resolved)?,
        ),
        other => other.clone(),
    })
}

fn par_formula_recursive(encoder: &mut ParEncoder, par: &Par) -> GuardFormula {
    match sole_expr_of(par) {
        Some(expr) => expr_formula_recursive(encoder, expr, par),
        None => encoder.atom_for(par, GuardAtomKind::ProcessShaped),
    }
}

fn opt_par_formula_recursive(encoder: &mut ParEncoder, par: Option<&Par>) -> GuardFormula {
    match par {
        Some(par) => par_formula_recursive(encoder, par),
        None => encoder.atom_for(&Par::default(), GuardAtomKind::Uncovered),
    }
}

fn expr_formula_recursive(encoder: &mut ParEncoder, expr: &Expr, whole: &Par) -> GuardFormula {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return encoder.atom_for(whole, GuardAtomKind::Uncovered);
    };
    match instance {
        ExprInstance::GBool(true) => GuardFormula::True,
        ExprInstance::GBool(false) => GuardFormula::False,
        ExprInstance::EAndBody(EAnd { p1, p2 }) => GuardFormula::and(
            opt_par_formula_recursive(encoder, p1.as_ref()),
            opt_par_formula_recursive(encoder, p2.as_ref()),
        ),
        ExprInstance::EOrBody(EOr { p1, p2 }) => GuardFormula::or(
            opt_par_formula_recursive(encoder, p1.as_ref()),
            opt_par_formula_recursive(encoder, p2.as_ref()),
        ),
        ExprInstance::ENotBody(ENot { p }) => {
            GuardFormula::not(opt_par_formula_recursive(encoder, p.as_ref()))
        },
        _ => encoder.expr_formula(expr, whole),
    }
}

fn opt_operand_recursive(encoder: &mut ParEncoder, par: Option<&Par>) -> Operand {
    match par {
        Some(par) => operand_recursive(encoder, par),
        None => Operand::Uncovered,
    }
}

fn operand_recursive(encoder: &mut ParEncoder, par: &Par) -> Operand {
    let Some(expr) = encoder.sole_expr(par) else {
        return Operand::Uncovered;
    };
    let Some(instance) = expr.expr_instance.as_ref() else {
        return Operand::Uncovered;
    };
    match instance {
        ExprInstance::GInt(n) => Operand::Int(LinearForm::constant(*n)),
        ExprInstance::GBool(b) => Operand::Lit(GuardValue::Bool(*b)),
        ExprInstance::GString(s) => Operand::Lit(GuardValue::Str(s.clone())),
        ExprInstance::GDouble(bits) => {
            Operand::Lit(GuardValue::Float(OrderedF64(f64::from_bits(*bits))))
        },
        ExprInstance::EVarBody(EVar { v }) => match encoder.var_index(v.as_ref()) {
            Some(index) => Operand::Var(index),
            None => Operand::Uncovered,
        },
        ExprInstance::EPlusBody(EPlus { p1, p2 }) => {
            arithmetic_recursive(encoder, p1.as_ref(), p2.as_ref(), LinearForm::add)
        },
        ExprInstance::EMinusBody(EMinus { p1, p2 }) => {
            arithmetic_recursive(encoder, p1.as_ref(), p2.as_ref(), LinearForm::sub)
        },
        ExprInstance::ENegBody(ENeg { p }) => match int_form_recursive(encoder, p.as_ref()) {
            Some(form) => match form.negate() {
                Some(negated) => Operand::Int(negated),
                None => Operand::NonLinear,
            },
            None => Operand::Uncovered,
        },
        ExprInstance::EMultBody(EMult { p1, p2 }) => match (
            int_form_recursive(encoder, p1.as_ref()),
            int_form_recursive(encoder, p2.as_ref()),
        ) {
            (Some(left), Some(right)) if left.is_constant() => scaled(&right, left.constant),
            (Some(left), Some(right)) if right.is_constant() => scaled(&left, right.constant),
            (Some(_), Some(_)) => Operand::NonLinear,
            _ => Operand::Uncovered,
        },
        ExprInstance::EDivBody(EDiv { p1, p2 }) => {
            integer_division_recursive(encoder, p1.as_ref(), p2.as_ref(), i64::checked_div)
        },
        ExprInstance::EModBody(EMod { p1, p2 }) => {
            integer_division_recursive(encoder, p1.as_ref(), p2.as_ref(), i64::checked_rem)
        },
        ExprInstance::EListBody(_)
        | ExprInstance::ESetBody(_)
        | ExprInstance::EMapBody(_)
        | ExprInstance::ETupleBody(_) => Operand::Structural,
        ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_)
        | ExprInstance::ENotBody(_)
        | ExprInstance::EAndBody(_)
        | ExprInstance::EOrBody(_)
        | ExprInstance::EEqBody(_)
        | ExprInstance::ENeqBody(_)
        | ExprInstance::ELtBody(_)
        | ExprInstance::ELteBody(_)
        | ExprInstance::EGtBody(_)
        | ExprInstance::EGteBody(_)
        | ExprInstance::EMatchesBody(_)
        | ExprInstance::EPercentPercentBody(_)
        | ExprInstance::EPlusPlusBody(_)
        | ExprInstance::EMinusMinusBody(_)
        | ExprInstance::EMethodBody(_)
        | ExprInstance::EPathmapBody(_)
        | ExprInstance::EZipperBody(_) => Operand::Uncovered,
    }
}

fn arithmetic_recursive(
    encoder: &mut ParEncoder,
    left: Option<&Par>,
    right: Option<&Par>,
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
    encoder: &mut ParEncoder,
    left: Option<&Par>,
    right: Option<&Par>,
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

fn int_form_recursive(encoder: &mut ParEncoder, par: Option<&Par>) -> Option<LinearForm> {
    match opt_operand_recursive(encoder, par) {
        Operand::Int(form) => Some(form),
        Operand::Var(index) => Some(LinearForm::var(index)),
        _ => None,
    }
}

fn substitute_bound_pars_recursive(par: &Par, bindings: &[Par]) -> Par {
    match bound_var_reference(par).and_then(|index| binding_for(index, bindings)) {
        Some(value) => value.clone(),
        None => match par.exprs.is_empty() {
            true => par.clone(),
            false => {
                let mut exprs = Vec::with_capacity(par.exprs.len());
                for expr in &par.exprs {
                    exprs.push(substitute_expr_recursive(expr, bindings));
                }
                Par {
                    exprs,
                    sends: par.sends.clone(),
                    receives: par.receives.clone(),
                    news: par.news.clone(),
                    matches: par.matches.clone(),
                    unforgeables: par.unforgeables.clone(),
                    bundles: par.bundles.clone(),
                    connectives: par.connectives.clone(),
                    conditionals: par.conditionals.clone(),
                    locally_free: par.locally_free.clone(),
                    connective_used: par.connective_used,
                }
            },
        },
    }
}

fn substitute_opt_par_recursive(par: &Option<Par>, bindings: &[Par]) -> Option<Par> {
    par.as_ref()
        .map(|par| substitute_bound_pars_recursive(par, bindings))
}

fn substitute_expr_recursive(expr: &Expr, bindings: &[Par]) -> Expr {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return expr.clone();
    };
    let substituted = match instance {
        ExprInstance::EAndBody(EAnd { p1, p2 }) => ExprInstance::EAndBody(EAnd {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EOrBody(EOr { p1, p2 }) => ExprInstance::EOrBody(EOr {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::ENotBody(ENot { p }) => ExprInstance::ENotBody(ENot {
            p: substitute_opt_par_recursive(p, bindings),
        }),
        ExprInstance::EEqBody(EEq { p1, p2 }) => ExprInstance::EEqBody(EEq {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::ENeqBody(ENeq { p1, p2 }) => ExprInstance::ENeqBody(ENeq {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::ELtBody(ELt { p1, p2 }) => ExprInstance::ELtBody(ELt {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::ELteBody(ELte { p1, p2 }) => ExprInstance::ELteBody(ELte {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EGtBody(EGt { p1, p2 }) => ExprInstance::EGtBody(EGt {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EGteBody(EGte { p1, p2 }) => ExprInstance::EGteBody(EGte {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EPlusBody(EPlus { p1, p2 }) => ExprInstance::EPlusBody(EPlus {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EMinusBody(EMinus { p1, p2 }) => ExprInstance::EMinusBody(EMinus {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EMultBody(EMult { p1, p2 }) => ExprInstance::EMultBody(EMult {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EDivBody(EDiv { p1, p2 }) => ExprInstance::EDivBody(EDiv {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::EModBody(EMod { p1, p2 }) => ExprInstance::EModBody(EMod {
            p1: substitute_opt_par_recursive(p1, bindings),
            p2: substitute_opt_par_recursive(p2, bindings),
        }),
        ExprInstance::ENegBody(ENeg { p }) => ExprInstance::ENegBody(ENeg {
            p: substitute_opt_par_recursive(p, bindings),
        }),
        ExprInstance::EMatchesBody(EMatches { target, pattern }) => {
            ExprInstance::EMatchesBody(EMatches {
                target: substitute_opt_par_recursive(target, bindings),
                pattern: pattern.clone(),
            })
        },
        ExprInstance::EVarBody(_)
        | ExprInstance::EListBody(_)
        | ExprInstance::ESetBody(_)
        | ExprInstance::EMapBody(_)
        | ExprInstance::ETupleBody(_)
        | ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_)
        | ExprInstance::EPercentPercentBody(_)
        | ExprInstance::EPlusPlusBody(_)
        | ExprInstance::EMinusMinusBody(_)
        | ExprInstance::EMethodBody(_)
        | ExprInstance::EPathmapBody(_)
        | ExprInstance::EZipperBody(_) => return expr.clone(),
    };
    Expr { expr_instance: Some(substituted) }
}

fn expr(instance: ExprInstance) -> Par {
    let mut par = Par::default();
    par.exprs.push(Expr { expr_instance: Some(instance) });
    par
}

fn bool_par(value: bool) -> Par {
    expr(ExprInstance::GBool(value))
}

fn not_par(inner: Option<Par>) -> Par {
    expr(ExprInstance::ENotBody(ENot { p: inner }))
}

fn and_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EAndBody(EAnd { p1: left, p2: right }))
}

fn or_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EOrBody(EOr { p1: left, p2: right }))
}

fn int_par(value: i64) -> Par {
    expr(ExprInstance::GInt(value))
}

fn bound_par(index: i32) -> Par {
    expr(ExprInstance::EVarBody(EVar {
        v: Some(Var {
            var_instance: Some(VarInstance::BoundVar(index)),
        }),
    }))
}

fn free_par(index: i32) -> Par {
    expr(ExprInstance::EVarBody(EVar {
        v: Some(Var {
            var_instance: Some(VarInstance::FreeVar(index)),
        }),
    }))
}

fn plus_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EPlusBody(EPlus { p1: left, p2: right }))
}

fn minus_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EMinusBody(EMinus { p1: left, p2: right }))
}

fn neg_par(inner: Option<Par>) -> Par {
    expr(ExprInstance::ENegBody(ENeg { p: inner }))
}

fn mult_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EMultBody(EMult { p1: left, p2: right }))
}

fn div_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EDivBody(EDiv { p1: left, p2: right }))
}

fn mod_par(left: Option<Par>, right: Option<Par>) -> Par {
    expr(ExprInstance::EModBody(EMod { p1: left, p2: right }))
}

fn encode_recursive(par: &Par) -> ParGuardEncoding {
    let mut encoder = ParEncoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    };
    let formula = par_formula_recursive(&mut encoder, par);
    ParGuardEncoding {
        formula,
        vars: encoder.vars,
        opaque: encoder.opaque,
    }
}

#[test]
fn formula_drivers_match_the_bounded_recursive_oracles() {
    let corpus = vec![
        bool_par(true),
        bool_par(false),
        not_par(Some(bool_par(true))),
        not_par(None),
        and_par(Some(bool_par(true)), Some(not_par(Some(bool_par(false))))),
        and_par(None, Some(bool_par(true))),
        or_par(Some(not_par(Some(bool_par(true)))), None),
        Par::default(),
    ];
    for (index, par) in corpus.iter().enumerate() {
        let driven = encode_par_guard(par);
        let recursive = encode_recursive(par);
        assert_eq!(
            format!("{:?}", driven.formula),
            format!("{:?}", recursive.formula),
            "formula traversal differs at corpus index {index}"
        );
        assert_eq!(format!("{:?}", driven.vars), format!("{:?}", recursive.vars));
        assert_eq!(format!("{:?}", driven.opaque), format!("{:?}", recursive.opaque));
    }

    let atom = GuardAtom { id: 0, kind: GuardAtomKind::Uncovered };
    let formulas = [
        GuardFormula::Atom(atom),
        GuardFormula::And(
            Box::new(GuardFormula::Atom(atom)),
            Box::new(GuardFormula::Not(Box::new(GuardFormula::Atom(atom)))),
        ),
        GuardFormula::Implies(
            Box::new(GuardFormula::Atom(atom)),
            Box::new(GuardFormula::Or(
                Box::new(GuardFormula::False),
                Box::new(GuardFormula::Atom(atom)),
            )),
        ),
    ];
    for formula in formulas {
        let driven = substitute_atoms(&formula, &[atom], &[Some(true)]);
        let recursive = substitute_atoms_recursive(&formula, &[atom], &[Some(true)]);
        assert_eq!(format!("{driven:?}"), format!("{recursive:?}"));
    }
}

#[test]
fn operand_driver_matches_the_bounded_recursive_oracle() {
    let corpus = vec![
        Par::default(),
        int_par(0),
        int_par(i64::MIN),
        bool_par(true),
        expr(ExprInstance::GString("text".to_string())),
        expr(ExprInstance::GDouble(1.5_f64.to_bits())),
        bound_par(7),
        free_par(2),
        plus_par(Some(bound_par(7)), Some(free_par(2))),
        plus_par(Some(int_par(i64::MAX)), Some(int_par(1))),
        plus_par(None, Some(int_par(1))),
        minus_par(Some(bound_par(1)), Some(bound_par(0))),
        neg_par(Some(int_par(i64::MIN))),
        neg_par(None),
        mult_par(Some(int_par(3)), Some(bound_par(0))),
        mult_par(Some(bound_par(1)), Some(bound_par(0))),
        mult_par(Some(bool_par(true)), Some(int_par(2))),
        div_par(Some(int_par(12)), Some(int_par(3))),
        div_par(Some(int_par(1)), Some(int_par(0))),
        div_par(Some(bound_par(0)), Some(int_par(2))),
        mod_par(Some(int_par(13)), Some(int_par(5))),
        expr(ExprInstance::EListBody(Default::default())),
        not_par(Some(bool_par(false))),
    ];

    for (index, par) in corpus.iter().enumerate() {
        let mut driven = ParEncoder {
            vars: GuardVarMap::new(),
            opaque: Vec::new(),
        };
        let mut recursive = ParEncoder {
            vars: GuardVarMap::new(),
            opaque: Vec::new(),
        };
        let driven_operand = driven.opt_operand(Some(par));
        let recursive_operand = opt_operand_recursive(&mut recursive, Some(par));
        assert_eq!(
            format!("{driven_operand:?}"),
            format!("{recursive_operand:?}"),
            "operand traversal differs at corpus index {index}"
        );
        assert_eq!(format!("{:?}", driven.vars), format!("{:?}", recursive.vars));
    }

    let mut driven = ParEncoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    };
    let mut recursive = ParEncoder {
        vars: GuardVarMap::new(),
        opaque: Vec::new(),
    };
    assert_eq!(
        format!("{:?}", driven.opt_operand(None)),
        format!("{:?}", opt_operand_recursive(&mut recursive, None))
    );
}

#[test]
fn bound_substitution_driver_matches_the_bounded_recursive_oracle() {
    let bindings = vec![int_par(41), int_par(7)];
    let binary = |build: fn(Option<Par>, Option<Par>) -> ExprInstance| {
        expr(build(Some(bound_par(1)), Some(bound_par(0))))
    };
    let mut multi_expr = Par::default();
    multi_expr.exprs = vec![
        Expr {
            expr_instance: Some(ExprInstance::EVarBody(EVar {
                v: Some(Var {
                    var_instance: Some(VarInstance::BoundVar(0)),
                }),
            })),
        },
        plus_par(Some(bound_par(1)), Some(bound_par(0)))
            .exprs
            .pop()
            .expect("plus expression"),
    ];
    let corpus = vec![
        Par::default(),
        bound_par(0),
        bound_par(1),
        bound_par(3),
        free_par(0),
        and_par(Some(bound_par(1)), Some(bound_par(0))),
        or_par(Some(bound_par(1)), None),
        not_par(Some(bound_par(0))),
        binary(|p1, p2| ExprInstance::EEqBody(EEq { p1, p2 })),
        binary(|p1, p2| ExprInstance::ENeqBody(ENeq { p1, p2 })),
        binary(|p1, p2| ExprInstance::ELtBody(ELt { p1, p2 })),
        binary(|p1, p2| ExprInstance::ELteBody(ELte { p1, p2 })),
        binary(|p1, p2| ExprInstance::EGtBody(EGt { p1, p2 })),
        binary(|p1, p2| ExprInstance::EGteBody(EGte { p1, p2 })),
        plus_par(Some(bound_par(1)), Some(bound_par(0))),
        minus_par(Some(bound_par(1)), Some(bound_par(0))),
        mult_par(Some(bound_par(1)), Some(bound_par(0))),
        div_par(Some(bound_par(1)), Some(bound_par(0))),
        mod_par(Some(bound_par(1)), Some(bound_par(0))),
        neg_par(Some(bound_par(0))),
        expr(ExprInstance::EMatchesBody(EMatches {
            target: Some(bound_par(0)),
            pattern: Some(bound_par(1)),
        })),
        expr(ExprInstance::EListBody(Default::default())),
        multi_expr,
    ];

    for (index, par) in corpus.iter().enumerate() {
        assert_eq!(
            substitute_bound_pars(par, &bindings),
            substitute_bound_pars_recursive(par, &bindings),
            "bound substitution differs at corpus index {index}"
        );
    }
}

#[test]
fn formula_drivers_are_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("guard-formula-drivers-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut par = bool_par(true);
            for _ in 0..DEPTH {
                par = not_par(Some(par));
            }
            let encoded = encode_par_guard(&par);
            assert!(matches!(encoded.formula, GuardFormula::True | GuardFormula::False));

            let atom = GuardAtom { id: 0, kind: GuardAtomKind::Uncovered };
            let mut formula = GuardFormula::Atom(atom);
            for _ in 0..DEPTH {
                formula = GuardFormula::Not(Box::new(formula));
            }
            assert!(substitute_atoms(&formula, &[atom], &[Some(true)]).is_some());
        })
        .expect("spawn guard formula depth gate")
        .join()
        .expect("guard formula depth gate must not overflow or panic");
}

#[test]
fn operand_driver_is_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("guard-operand-driver-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut par = bound_par(0);
            for _ in 0..DEPTH {
                par = plus_par(Some(par), Some(int_par(1)));
            }
            let mut encoder = ParEncoder {
                vars: GuardVarMap::new(),
                opaque: Vec::new(),
            };
            assert!(matches!(encoder.opt_operand(Some(&par)), Operand::Int(_)));
        })
        .expect("spawn guard operand depth gate")
        .join()
        .expect("guard operand depth gate must not overflow or panic");
}

#[test]
fn bound_substitution_driver_is_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("guard-bound-substitution-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut par = bound_par(0);
            for _ in 0..DEPTH {
                par = plus_par(Some(par), Some(int_par(1)));
            }
            let substituted = substitute_bound_pars(&par, &[int_par(9)]);
            let mut cursor = &substituted;
            for _ in 0..DEPTH {
                let Some(ExprInstance::EPlusBody(EPlus { p1, .. })) =
                    sole_expr_of(cursor).and_then(|expr| expr.expr_instance.as_ref())
                else {
                    panic!("substitution changed the deep arithmetic spine")
                };
                cursor = p1.as_ref().expect("deep plus left operand");
            }
            assert_eq!(cursor, &int_par(9));
        })
        .expect("spawn guard bound-substitution depth gate")
        .join()
        .expect("guard bound-substitution depth gate must not overflow or panic");
}
