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
