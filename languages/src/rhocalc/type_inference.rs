use super::{
    Bag, Bool, ForRow, InputBind, List, Map, Name, Proc, RhoCalcLanguage, RhoCalcTerm,
    RhoCalcTermInner,
};
use crate::rhocalc::receive;
use mettail_runtime::{Language, Term, TermType, VarTypeInfo};

fn infer_receive_pattern_names(pat: &Proc, out: &mut Vec<String>) {
    match pat {
        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
            if let Some(name) = &fv.pretty_name {
                out.push(name.clone());
            }
        },
        Proc::CastList(xs) => {
            if let List::ListLit(items) = xs.as_ref() {
                for item in items {
                    infer_receive_pattern_names(item, out);
                }
            }
        },
        Proc::CastBag(xs) => {
            if let Bag::BagLit(items) = xs.as_ref() {
                for (item, count) in items.iter() {
                    for _ in 0..count {
                        infer_receive_pattern_names(item, out);
                    }
                }
            }
        },
        Proc::CastMap(m) => {
            if let Map::MapLit(items) = m.as_ref() {
                for (_, value) in items.iter() {
                    infer_receive_pattern_names(value, out);
                }
            }
        },
        _ => {},
    }
}

fn name_uses_var(name: &Name, var_name: &str) -> bool {
    match name {
        Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
            fv.pretty_name.as_deref() == Some(var_name)
        },
        Name::NQuote(p) => proc_uses_name_var(p, var_name) || proc_uses_proc_var(p, var_name),
        _ => false,
    }
}

fn input_bind_uses_name_var(bind: &InputBind, var_name: &str) -> bool {
    match bind {
        InputBind::InputBind(lhs, n) => {
            let pat = receive::name_pattern_to_proc(lhs.as_ref());
            proc_uses_name_var(&pat, var_name) || name_uses_var(n, var_name)
        },
        InputBind::InputBindQuoted(pat, n) => {
            proc_uses_name_var(pat, var_name) || name_uses_var(n, var_name)
        },
        InputBind::InputBindQuery(lhs, n, args) => {
            let pat = receive::name_pattern_to_proc(lhs.as_ref());
            proc_uses_name_var(&pat, var_name)
                || name_uses_var(n, var_name)
                || args.iter().any(|a| proc_uses_name_var(a, var_name))
        },
        InputBind::InputBindQuotedQuery(pat, n, args) => {
            proc_uses_name_var(pat, var_name)
                || name_uses_var(n, var_name)
                || args.iter().any(|a| proc_uses_name_var(a, var_name))
        },
        _ => false,
    }
}

fn input_bind_uses_proc_var(bind: &InputBind, var_name: &str) -> bool {
    match bind {
        InputBind::InputBind(lhs, n) => {
            let pat = receive::name_pattern_to_proc(lhs.as_ref());
            proc_uses_proc_var(&pat, var_name) || name_uses_var(n, var_name)
        },
        InputBind::InputBindQuoted(pat, n) => {
            proc_uses_proc_var(pat, var_name) || name_uses_var(n, var_name)
        },
        InputBind::InputBindQuery(lhs, n, args) => {
            let pat = receive::name_pattern_to_proc(lhs.as_ref());
            proc_uses_proc_var(&pat, var_name)
                || name_uses_var(n, var_name)
                || args.iter().any(|a| proc_uses_proc_var(a, var_name))
        },
        InputBind::InputBindQuotedQuery(pat, n, args) => {
            proc_uses_proc_var(pat, var_name)
                || name_uses_var(n, var_name)
                || args.iter().any(|a| proc_uses_proc_var(a, var_name))
        },
        _ => false,
    }
}

fn for_row_uses_name_var(row: &ForRow, var_name: &str) -> bool {
    match row {
        ForRow::ForRowSingleNoWhere(b) => input_bind_uses_name_var(b.as_ref(), var_name),
        ForRow::ForRowSingleWhere(b, cond) => {
            input_bind_uses_name_var(b.as_ref(), var_name) || proc_uses_name_var(cond, var_name)
        },
        ForRow::ForRowNoWhere(b, bs) => {
            input_bind_uses_name_var(b.as_ref(), var_name)
                || bs.iter()
                    .any(|ib| input_bind_uses_name_var(ib, var_name))
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            input_bind_uses_name_var(b.as_ref(), var_name)
                || bs
                    .iter()
                    .any(|ib| input_bind_uses_name_var(ib, var_name))
                || proc_uses_name_var(cond, var_name)
        },
        _ => false,
    }
}

fn for_row_uses_proc_var(row: &ForRow, var_name: &str) -> bool {
    match row {
        ForRow::ForRowSingleNoWhere(b) => input_bind_uses_proc_var(b.as_ref(), var_name),
        ForRow::ForRowSingleWhere(b, cond) => {
            input_bind_uses_proc_var(b.as_ref(), var_name) || proc_uses_proc_var(cond, var_name)
        },
        ForRow::ForRowNoWhere(b, bs) => {
            input_bind_uses_proc_var(b.as_ref(), var_name)
                || bs
                    .iter()
                    .any(|ib| input_bind_uses_proc_var(ib, var_name))
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            input_bind_uses_proc_var(b.as_ref(), var_name)
                || bs
                    .iter()
                    .any(|ib| input_bind_uses_proc_var(ib, var_name))
                || proc_uses_proc_var(cond, var_name)
        },
        _ => false,
    }
}

fn proc_uses_name_var(term: &Proc, var_name: &str) -> bool {
    match term {
        Proc::PPar(ps) => ps.iter().any(|(p, _)| proc_uses_name_var(p, var_name)),
        Proc::POutput(n, q) => name_uses_var(n, var_name) || proc_uses_name_var(q, var_name),
        Proc::PDrop(n) => name_uses_var(n, var_name),
        Proc::PForUser(rows, body) => {
            rows.iter()
                .any(|r| for_row_uses_name_var(r, var_name))
                || proc_uses_name_var(body, var_name)
        },
        Proc::GuardThen(cond, body) => {
            proc_uses_name_var(cond, var_name) || proc_uses_name_var(body, var_name)
        },
        Proc::PNew(scope) => proc_uses_name_var(scope.unsafe_body(), var_name),
        _ => false,
    }
}

fn proc_uses_proc_var(term: &Proc, var_name: &str) -> bool {
    match term {
        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
            fv.pretty_name.as_deref() == Some(var_name)
        },
        Proc::PPar(ps) => ps.iter().any(|(p, _)| proc_uses_proc_var(p, var_name)),
        Proc::POutput(n, q) => name_uses_var(n, var_name) || proc_uses_proc_var(q, var_name),
        Proc::PDrop(n) => name_uses_var(n, var_name),
        Proc::PForUser(rows, body) => {
            rows.iter()
                .any(|r| for_row_uses_proc_var(r, var_name))
                || proc_uses_proc_var(body, var_name)
        },
        Proc::GuardThen(cond, body) => {
            proc_uses_proc_var(cond, var_name) || proc_uses_proc_var(body, var_name)
        },
        Proc::PNew(scope) => proc_uses_proc_var(scope.unsafe_body(), var_name),
        _ => false,
    }
}

fn infer_var_type_pfor_user(proc: &Proc, var_name: &str) -> Option<TermType> {
    let Proc::PForUser(rows, body) = proc else {
        return None;
    };
    infer_var_type_in_receive_rows(rows, body, var_name)
}

fn infer_var_type_in_receive_rows(rows: &[ForRow], body: &Proc, var_name: &str) -> Option<TermType> {
    if rows.is_empty() {
        return None;
    }
    let cont = receive::pfor_continuation_after_first_row(rows, body);
    match &rows[0] {
        ForRow::ForRowSingleNoWhere(b) => {
            if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pat, &mut names);
                if names.iter().any(|n| n == var_name) {
                    return Some(infer_receive_var_type(&cont, None, var_name));
                }
            }
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pat, &mut names);
                if names.iter().any(|n| n == var_name) {
                    return Some(infer_receive_var_type(
                        &cont,
                        Some(cond.as_ref()),
                        var_name,
                    ));
                }
            }
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut names = Vec::new();
            names_from_binds(b.as_ref(), bs, &mut names);
            if names.iter().any(|n| n == var_name) {
                let true_lit = Proc::CastBool(Box::new(Bool::BoolLit(true)));
                return Some(infer_receive_var_type(&cont, Some(&true_lit), var_name));
            }
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut names = Vec::new();
            names_from_binds(b.as_ref(), bs, &mut names);
            if names.iter().any(|n| n == var_name) {
                return Some(infer_receive_var_type(
                    &cont,
                    Some(cond.as_ref()),
                    var_name,
                ));
            }
        },
        _ => {},
    }
    infer_var_type_in_receive_rows(&rows[1..], body, var_name)
}

fn infer_receive_var_type(body: &Proc, cond: Option<&Proc>, var_name: &str) -> TermType {
    let uses_name =
        proc_uses_name_var(body, var_name) || cond.is_some_and(|c| proc_uses_name_var(c, var_name));
    let uses_proc =
        proc_uses_proc_var(body, var_name) || cond.is_some_and(|c| proc_uses_proc_var(c, var_name));
    if uses_name {
        TermType::Base("Name".to_string())
    } else if uses_proc {
        TermType::Base("Proc".to_string())
    } else {
        TermType::Base("Name".to_string())
    }
}

fn names_from_binds(b: &InputBind, bs: &[InputBind], out: &mut Vec<String>) {
    if let Some(pat) = receive::bind_pattern_proc(b) {
        infer_receive_pattern_names(&pat, out);
    }
    for bind in bs {
        if let Some(pat) = receive::bind_pattern_proc(bind) {
            infer_receive_pattern_names(&pat, out);
        }
    }
}

/// Collect receive-bound names from a `PForUser` the same way we did for nested `PFor*`.
fn collect_pfor_user_receive_vars(
    rows: &[ForRow],
    body: &Proc,
    result: &mut Vec<VarTypeInfo>,
    seen: &mut std::collections::HashSet<String>,
) {
    if rows.is_empty() {
        collect_rhocalc_var_types(body, result, seen);
        return;
    }
    let cont = receive::pfor_continuation_after_first_row(rows, body);
    match &rows[0] {
        ForRow::ForRowSingleNoWhere(b) => {
            if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pat, &mut names);
                for name in names {
                    if seen.insert(name.clone()) {
                        result.push(VarTypeInfo {
                            name: name.clone(),
                            ty: infer_receive_var_type(&cont, None, &name),
                        });
                    }
                }
            }
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pat, &mut names);
                for name in names {
                    if seen.insert(name.clone()) {
                        result.push(VarTypeInfo {
                            name: name.clone(),
                            ty: infer_receive_var_type(&cont, Some(cond.as_ref()), &name),
                        });
                    }
                }
            }
            collect_rhocalc_var_types(cond.as_ref(), result, seen);
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut names = Vec::new();
            names_from_binds(b.as_ref(), bs, &mut names);
            let true_lit = Proc::CastBool(Box::new(Bool::BoolLit(true)));
            for name in names {
                if seen.insert(name.clone()) {
                    result.push(VarTypeInfo {
                        name: name.clone(),
                        ty: infer_receive_var_type(&cont, Some(&true_lit), &name),
                    });
                }
            }
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut names = Vec::new();
            names_from_binds(b.as_ref(), bs, &mut names);
            for name in names {
                if seen.insert(name.clone()) {
                    result.push(VarTypeInfo {
                        name: name.clone(),
                        ty: infer_receive_var_type(&cont, Some(cond.as_ref()), &name),
                    });
                }
            }
            collect_rhocalc_var_types(cond.as_ref(), result, seen);
        },
        _ => {},
    }
    collect_pfor_user_receive_vars(&rows[1..], body, result, seen);
}

fn collect_rhocalc_var_types(
    term: &Proc,
    result: &mut Vec<VarTypeInfo>,
    seen: &mut std::collections::HashSet<String>,
) {
    match term {
        Proc::PForUser(rows, body) => {
            collect_pfor_user_receive_vars(rows, body, result, seen);
        },
        Proc::PPar(ps) => {
            for (p, _) in ps.iter() {
                collect_rhocalc_var_types(p, result, seen);
            }
        },
        Proc::GuardThen(cond, body) => {
            collect_rhocalc_var_types(cond, result, seen);
            collect_rhocalc_var_types(body, result, seen);
        },
        Proc::POutput(_, q) => collect_rhocalc_var_types(q, result, seen),
        Proc::PNew(scope) => collect_rhocalc_var_types(scope.unsafe_body(), result, seen),
        _ => {},
    }
}

impl RhoCalcLanguage {
    pub fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        let Some(typed_term) = term.as_any().downcast_ref::<RhoCalcTerm>() else {
            return <RhoCalcLanguage as Language>::infer_var_types(self, term);
        };
        match &typed_term.0 {
            RhoCalcTermInner::Proc(p) => {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                collect_rhocalc_var_types(p, &mut result, &mut seen);
                RhoCalcLanguage::collect_all_proc_vars(p, p, &mut result, &mut seen);
                result
            },
            _ => <RhoCalcLanguage as Language>::infer_var_types(self, term),
        }
    }

    pub fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        let Some(typed_term) = term.as_any().downcast_ref::<RhoCalcTerm>() else {
            return <RhoCalcLanguage as Language>::infer_var_type(self, term, var_name);
        };
        if let RhoCalcTermInner::Proc(proc) = &typed_term.0 {
            if let Some(t) = infer_var_type_pfor_user(proc, var_name) {
                return Some(t);
            }
            if let Some(t) = proc.infer_var_type(var_name) {
                return Some(RhoCalcLanguage::inferred_to_term_type(&t));
            }
            let mut result = Vec::new();
            let mut seen = std::collections::HashSet::new();
            RhoCalcLanguage::collect_all_proc_vars(proc, proc, &mut result, &mut seen);
            return result
                .into_iter()
                .find(|v| v.name == var_name)
                .map(|v| v.ty);
        }
        <RhoCalcLanguage as Language>::infer_var_type(self, term, var_name)
    }
}
