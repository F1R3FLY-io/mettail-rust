//! Test-only recursive oracle for the pre-PDA Rholang type-inference traversal.
//!
//! Keep this deliberately direct: production code must remain iterative, while shallow corpus
//! tests use this implementation to pin visitation order and inferred types.

use std::collections::HashSet;
use std::sync::Arc;

use mettail_languages::rholang::{
    Bag, Bool, ForRow, InputBind, List, Map, Name, Pathmap, Proc, ReadZipper, RholangLanguage,
    RholangTerm, RholangTermInner, Set, WriteZipper,
};
use mettail_runtime::{Language, TermType, VarTypeInfo};

fn mk_proc_list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

fn name_pattern_to_proc(name: &Name) -> Proc {
    match name {
        Name::NVar(var) => Proc::PVar(var.clone()),
        Name::NQuote(proc) | Name::NQuoteShort(proc) => proc.as_ref().clone(),
        Name::NQuoteNil => Proc::PZero,
        Name::NParen(inner) => name_pattern_to_proc(inner),
        _ => Proc::Err,
    }
}

fn canonicalize_arity_pattern(pattern: &Proc) -> Proc {
    match pattern {
        Proc::CastList(_) | Proc::PVar(_) => pattern.clone(),
        _ => mk_proc_list(vec![pattern.clone()]),
    }
}

fn bind_pattern_proc(bind: &InputBind) -> Option<Proc> {
    match bind {
        InputBind::InputBind(lhs, _)
        | InputBind::InputBindPersistent(lhs, _)
        | InputBind::InputBindQuery(lhs, _, _) => {
            let pattern = name_pattern_to_proc(lhs);
            Some(if matches!(lhs.as_ref(), Name::NVar(_)) {
                pattern
            } else {
                mk_proc_list(vec![pattern])
            })
        },
        InputBind::InputBindPolyadic(lhs, rest, _)
        | InputBind::InputBindPersistentPolyadic(lhs, rest, _) => {
            let mut items = Vec::with_capacity(rest.len() + 1);
            items.push(name_pattern_to_proc(lhs));
            items.extend(rest.iter().map(name_pattern_to_proc));
            Some(mk_proc_list(items))
        },
        InputBind::InputBindEmpty(_)
        | InputBind::InputBindEmptyPersistent(_)
        | InputBind::InputBindEmptyQuery(_, _) => Some(mk_proc_list(Vec::new())),
        InputBind::InputBindQuoted(pattern, _)
        | InputBind::InputBindQuotedPersistent(pattern, _)
        | InputBind::InputBindQuotedQuery(pattern, _, _) => {
            Some(canonicalize_arity_pattern(pattern))
        },
        _ => None,
    }
}

fn continuation_after_first_row(rows: &[ForRow], body: &Proc) -> Proc {
    if rows.len() > 1 {
        Proc::PForUser(rows[1..].to_vec(), Arc::new(body.clone()))
    } else {
        body.clone()
    }
}

fn infer_receive_pattern_names(pattern: &Proc, out: &mut Vec<String>) {
    match pattern {
        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(var))) => {
            if let Some(name) = &var.pretty_name {
                out.push(name.clone());
            }
        },
        Proc::CastList(list) => {
            let List::ListLit(items) = list.as_ref() else {
                return;
            };
            for item in items {
                infer_receive_pattern_names(item, out);
            }
        },
        Proc::CastBag(bag) => {
            let Bag::BagLit(items) = bag.as_ref() else {
                return;
            };
            for (item, count) in items.iter() {
                for _ in 0..count {
                    infer_receive_pattern_names(item, out);
                }
            }
        },
        Proc::CastMap(map) => {
            let Map::MapLit(items) = map.as_ref() else {
                return;
            };
            for (_, value) in items.iter() {
                infer_receive_pattern_names(value, out);
            }
        },
        Proc::CastPathmap(pathmap) => {
            let Pathmap::PathmapLit(items) = pathmap.as_ref() else {
                return;
            };
            for entry in items.iter() {
                if let Some(value) = entry.value() {
                    infer_receive_pattern_names(value, out);
                }
            }
        },
        Proc::CastReadZipper(zipper) => {
            let ReadZipper::Lit(inner) = zipper.as_ref() else {
                return;
            };
            for entry in inner.as_ref().0.iter() {
                if let Some(value) = entry.value() {
                    infer_receive_pattern_names(value, out);
                }
            }
        },
        Proc::CastWriteZipper(zipper) => {
            let WriteZipper::Lit(inner) = zipper.as_ref() else {
                return;
            };
            for entry in inner.as_ref().0.iter() {
                if let Some(value) = entry.value() {
                    infer_receive_pattern_names(value, out);
                }
            }
        },
        Proc::CastSet(set) => {
            let Set::SetLit(items) = set.as_ref() else {
                return;
            };
            for item in items.iter() {
                infer_receive_pattern_names(item, out);
            }
        },
        _ => {},
    }
}

fn name_uses_var(name: &Name, var_name: &str) -> bool {
    match name {
        Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(var))) => {
            var.pretty_name.as_deref() == Some(var_name)
        },
        Name::NQuote(proc) => {
            proc_uses_name_var(proc, var_name) || proc_uses_proc_var(proc, var_name)
        },
        _ => false,
    }
}

fn input_bind_uses_name_var(bind: &InputBind, var_name: &str) -> bool {
    match bind {
        InputBind::InputBind(lhs, name) => {
            proc_uses_name_var(&name_pattern_to_proc(lhs), var_name)
                || name_uses_var(name, var_name)
        },
        InputBind::InputBindQuoted(pattern, name) => {
            proc_uses_name_var(pattern, var_name) || name_uses_var(name, var_name)
        },
        InputBind::InputBindQuery(lhs, name, args) => {
            proc_uses_name_var(&name_pattern_to_proc(lhs), var_name)
                || name_uses_var(name, var_name)
                || args.iter().any(|arg| proc_uses_name_var(arg, var_name))
        },
        InputBind::InputBindQuotedQuery(pattern, name, args) => {
            proc_uses_name_var(pattern, var_name)
                || name_uses_var(name, var_name)
                || args.iter().any(|arg| proc_uses_name_var(arg, var_name))
        },
        _ => false,
    }
}

fn input_bind_uses_proc_var(bind: &InputBind, var_name: &str) -> bool {
    match bind {
        InputBind::InputBind(lhs, name) => {
            proc_uses_proc_var(&name_pattern_to_proc(lhs), var_name)
                || name_uses_var(name, var_name)
        },
        InputBind::InputBindQuoted(pattern, name) => {
            proc_uses_proc_var(pattern, var_name) || name_uses_var(name, var_name)
        },
        InputBind::InputBindQuery(lhs, name, args) => {
            proc_uses_proc_var(&name_pattern_to_proc(lhs), var_name)
                || name_uses_var(name, var_name)
                || args.iter().any(|arg| proc_uses_proc_var(arg, var_name))
        },
        InputBind::InputBindQuotedQuery(pattern, name, args) => {
            proc_uses_proc_var(pattern, var_name)
                || name_uses_var(name, var_name)
                || args.iter().any(|arg| proc_uses_proc_var(arg, var_name))
        },
        _ => false,
    }
}

fn for_row_uses_name_var(row: &ForRow, var_name: &str) -> bool {
    match row {
        ForRow::ForRowSingleNoWhere(bind) => input_bind_uses_name_var(bind, var_name),
        ForRow::ForRowSingleWhere(bind, cond) => {
            input_bind_uses_name_var(bind, var_name) || proc_uses_name_var(cond, var_name)
        },
        ForRow::ForRowNoWhere(bind, binds) => {
            input_bind_uses_name_var(bind, var_name)
                || binds
                    .iter()
                    .any(|bind| input_bind_uses_name_var(bind, var_name))
        },
        ForRow::ForRowWhere(bind, binds, cond) => {
            input_bind_uses_name_var(bind, var_name)
                || binds
                    .iter()
                    .any(|bind| input_bind_uses_name_var(bind, var_name))
                || proc_uses_name_var(cond, var_name)
        },
        _ => false,
    }
}

fn for_row_uses_proc_var(row: &ForRow, var_name: &str) -> bool {
    match row {
        ForRow::ForRowSingleNoWhere(bind) => input_bind_uses_proc_var(bind, var_name),
        ForRow::ForRowSingleWhere(bind, cond) => {
            input_bind_uses_proc_var(bind, var_name) || proc_uses_proc_var(cond, var_name)
        },
        ForRow::ForRowNoWhere(bind, binds) => {
            input_bind_uses_proc_var(bind, var_name)
                || binds
                    .iter()
                    .any(|bind| input_bind_uses_proc_var(bind, var_name))
        },
        ForRow::ForRowWhere(bind, binds, cond) => {
            input_bind_uses_proc_var(bind, var_name)
                || binds
                    .iter()
                    .any(|bind| input_bind_uses_proc_var(bind, var_name))
                || proc_uses_proc_var(cond, var_name)
        },
        _ => false,
    }
}

fn proc_uses_name_var(proc: &Proc, var_name: &str) -> bool {
    match proc {
        Proc::PPar(procs) => procs
            .iter()
            .any(|(proc, _)| proc_uses_name_var(proc, var_name)),
        Proc::POutput(name, payload) => {
            name_uses_var(name, var_name) || proc_uses_name_var(payload, var_name)
        },
        Proc::PDrop(name) => name_uses_var(name, var_name),
        Proc::PForUser(rows, body) => {
            rows.iter().any(|row| for_row_uses_name_var(row, var_name))
                || proc_uses_name_var(body, var_name)
        },
        Proc::GuardThen(cond, body) => {
            proc_uses_name_var(cond, var_name) || proc_uses_name_var(body, var_name)
        },
        Proc::PNew(scope) => proc_uses_name_var(scope.unsafe_body(), var_name),
        _ => false,
    }
}

fn proc_uses_proc_var(proc: &Proc, var_name: &str) -> bool {
    match proc {
        Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(var))) => {
            var.pretty_name.as_deref() == Some(var_name)
        },
        Proc::PPar(procs) => procs
            .iter()
            .any(|(proc, _)| proc_uses_proc_var(proc, var_name)),
        Proc::POutput(name, payload) => {
            name_uses_var(name, var_name) || proc_uses_proc_var(payload, var_name)
        },
        Proc::PDrop(name) => name_uses_var(name, var_name),
        Proc::PForUser(rows, body) => {
            rows.iter().any(|row| for_row_uses_proc_var(row, var_name))
                || proc_uses_proc_var(body, var_name)
        },
        Proc::GuardThen(cond, body) => {
            proc_uses_proc_var(cond, var_name) || proc_uses_proc_var(body, var_name)
        },
        Proc::PNew(scope) => proc_uses_proc_var(scope.unsafe_body(), var_name),
        _ => false,
    }
}

fn infer_receive_var_type(body: &Proc, cond: Option<&Proc>, var_name: &str) -> TermType {
    let uses_name = proc_uses_name_var(body, var_name)
        || cond.is_some_and(|cond| proc_uses_name_var(cond, var_name));
    let uses_proc = proc_uses_proc_var(body, var_name)
        || cond.is_some_and(|cond| proc_uses_proc_var(cond, var_name));
    if uses_name {
        TermType::Base("Name".into())
    } else if uses_proc {
        TermType::Base("Proc".into())
    } else {
        TermType::Base("Name".into())
    }
}

fn names_from_binds(bind: &InputBind, binds: &[InputBind], out: &mut Vec<String>) {
    if let Some(pattern) = bind_pattern_proc(bind) {
        infer_receive_pattern_names(&pattern, out);
    }
    for bind in binds {
        if let Some(pattern) = bind_pattern_proc(bind) {
            infer_receive_pattern_names(&pattern, out);
        }
    }
}

fn collect_receive_vars(
    rows: &[ForRow],
    body: &Proc,
    result: &mut Vec<VarTypeInfo>,
    seen: &mut HashSet<String>,
) {
    if rows.is_empty() {
        collect_custom_vars(body, result, seen);
        return;
    }
    let continuation = continuation_after_first_row(rows, body);
    match &rows[0] {
        ForRow::ForRowSingleNoWhere(bind) => {
            if let Some(pattern) = bind_pattern_proc(bind) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pattern, &mut names);
                for name in names {
                    if seen.insert(name.clone()) {
                        result.push(VarTypeInfo {
                            ty: infer_receive_var_type(&continuation, None, &name),
                            name,
                        });
                    }
                }
            }
        },
        ForRow::ForRowSingleWhere(bind, cond) => {
            if let Some(pattern) = bind_pattern_proc(bind) {
                let mut names = Vec::new();
                infer_receive_pattern_names(&pattern, &mut names);
                for name in names {
                    if seen.insert(name.clone()) {
                        result.push(VarTypeInfo {
                            ty: infer_receive_var_type(&continuation, Some(cond), &name),
                            name,
                        });
                    }
                }
            }
            collect_custom_vars(cond, result, seen);
        },
        ForRow::ForRowNoWhere(bind, binds) => {
            let mut names = Vec::new();
            names_from_binds(bind, binds, &mut names);
            let true_lit = Proc::CastBool(Arc::new(Bool::BoolLit(true)));
            for name in names {
                if seen.insert(name.clone()) {
                    result.push(VarTypeInfo {
                        ty: infer_receive_var_type(&continuation, Some(&true_lit), &name),
                        name,
                    });
                }
            }
        },
        ForRow::ForRowWhere(bind, binds, cond) => {
            let mut names = Vec::new();
            names_from_binds(bind, binds, &mut names);
            for name in names {
                if seen.insert(name.clone()) {
                    result.push(VarTypeInfo {
                        ty: infer_receive_var_type(&continuation, Some(cond), &name),
                        name,
                    });
                }
            }
            collect_custom_vars(cond, result, seen);
        },
        _ => {},
    }
    collect_receive_vars(&rows[1..], body, result, seen);
}

fn collect_custom_vars(proc: &Proc, result: &mut Vec<VarTypeInfo>, seen: &mut HashSet<String>) {
    match proc {
        Proc::PForUser(rows, body) => collect_receive_vars(rows, body, result, seen),
        Proc::PPar(procs) => {
            for (proc, _) in procs.iter() {
                collect_custom_vars(proc, result, seen);
            }
        },
        Proc::GuardThen(cond, body) => {
            collect_custom_vars(cond, result, seen);
            collect_custom_vars(body, result, seen);
        },
        Proc::POutput(_, payload) => collect_custom_vars(payload, result, seen),
        Proc::PNew(scope) => collect_custom_vars(scope.unsafe_body(), result, seen),
        _ => {},
    }
}

pub fn infer_var_types(proc: &Proc) -> Vec<VarTypeInfo> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    collect_custom_vars(proc, &mut result, &mut seen);

    let term = RholangTerm(RholangTermInner::Proc(proc.clone()));
    for info in <RholangLanguage as Language>::infer_var_types(&RholangLanguage, &term) {
        if seen.insert(info.name.clone()) {
            result.push(info);
        }
    }
    result
}
