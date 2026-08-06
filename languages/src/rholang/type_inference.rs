use super::{
    Bag, Bool, ForRow, InputBind, List, Map, Name, Pathmap, Proc, ReadZipper, RholangLanguage,
    RholangTerm, RholangTermInner, Set, WriteZipper,
};
use crate::rholang::receive;
use mettail_runtime::{Language, Term, TermType, VarTypeInfo};

fn infer_receive_pattern_names(pat: &Proc, out: &mut Vec<String>) {
    let mut work = vec![pat];
    while let Some(pat) = work.pop() {
        let first_child = work.len();
        match pat {
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
                if let Some(name) = &fv.pretty_name {
                    out.push(name.clone());
                }
            },
            Proc::CastList(xs) => {
                if let List::ListLit(items) = xs.as_ref() {
                    work.extend(items);
                }
            },
            Proc::CastBag(xs) => {
                if let Bag::BagLit(items) = xs.as_ref() {
                    for (item, count) in items.iter() {
                        work.extend(std::iter::repeat_n(item, count));
                    }
                }
            },
            Proc::CastMap(m) => {
                if let Map::MapLit(items) = m.as_ref() {
                    work.extend(items.iter().map(|(_, value)| value));
                }
            },
            Proc::CastPathmap(m) => {
                if let Pathmap::PathmapLit(items) = m.as_ref() {
                    work.extend(items.iter().filter_map(|entry| entry.value()));
                }
            },
            Proc::CastReadZipper(z) => {
                if let ReadZipper::Lit(inner) = z.as_ref() {
                    work.extend(inner.as_ref().0.iter().filter_map(|entry| entry.value()));
                }
            },
            Proc::CastWriteZipper(z) => {
                if let WriteZipper::Lit(inner) = z.as_ref() {
                    work.extend(inner.as_ref().0.iter().filter_map(|entry| entry.value()));
                }
            },
            Proc::CastSet(s) => {
                if let Set::SetLit(items) = s.as_ref() {
                    work.extend(items.iter());
                }
            },
            _ => {},
        }
        work[first_child..].reverse();
    }
}

#[derive(Clone, Copy)]
enum VarUseKind {
    Name,
    Proc,
}

enum VarUseWork<'a> {
    Proc(&'a Proc, VarUseKind),
    Name(&'a Name),
    PatternName(&'a Name, VarUseKind),
    InputBind(&'a InputBind, VarUseKind),
    ForRow(&'a ForRow, VarUseKind),
}

/// Stack-safe executor for the mutually recursive `Proc`/`Name`/receive-row variable-use
/// predicates. Work is pushed in reverse source order so short-circuit behavior matches the
/// former recursive implementation exactly.
fn proc_uses_var(term: &Proc, var_name: &str, root_kind: VarUseKind) -> bool {
    var_use_work_contains(vec![VarUseWork::Proc(term, root_kind)], var_name)
}

fn receive_continuation_uses_var(
    rows: &[ForRow],
    body: &Proc,
    var_name: &str,
    kind: VarUseKind,
) -> bool {
    let mut work = Vec::with_capacity(rows.len().saturating_add(1));
    work.push(VarUseWork::Proc(body, kind));
    work.extend(rows.iter().rev().map(|row| VarUseWork::ForRow(row, kind)));
    var_use_work_contains(work, var_name)
}

fn var_use_work_contains(mut work: Vec<VarUseWork<'_>>, var_name: &str) -> bool {
    while let Some(task) = work.pop() {
        match task {
            VarUseWork::Proc(term, kind) => match term {
                Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)))
                    if matches!(kind, VarUseKind::Proc)
                        && fv.pretty_name.as_deref() == Some(var_name) =>
                {
                    return true;
                },
                Proc::PPar(ps) => {
                    let first_child = work.len();
                    work.extend(ps.iter().map(|(proc, _)| VarUseWork::Proc(proc, kind)));
                    work[first_child..].reverse();
                },
                Proc::POutput(name, payload) => {
                    work.push(VarUseWork::Proc(payload, kind));
                    work.push(VarUseWork::Name(name));
                },
                Proc::PDrop(name) => work.push(VarUseWork::Name(name)),
                Proc::PForUser(rows, body) => {
                    work.push(VarUseWork::Proc(body, kind));
                    work.extend(rows.iter().rev().map(|row| VarUseWork::ForRow(row, kind)));
                },
                Proc::GuardThen(cond, body) => {
                    work.push(VarUseWork::Proc(body, kind));
                    work.push(VarUseWork::Proc(cond, kind));
                },
                Proc::PNew(scope) => work.push(VarUseWork::Proc(scope.unsafe_body(), kind)),
                _ => {},
            },
            // `receive::name_pattern_to_proc` expressed as borrowed work: this preserves its
            // exact conversion semantics without cloning a quoted subtree merely to inspect it.
            VarUseWork::PatternName(name, kind) => match name {
                Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)))
                    if matches!(kind, VarUseKind::Proc)
                        && fv.pretty_name.as_deref() == Some(var_name) =>
                {
                    return true;
                },
                Name::NQuote(proc) | Name::NQuoteShort(proc) => {
                    work.push(VarUseWork::Proc(proc, kind));
                },
                Name::NParen(inner) => work.push(VarUseWork::PatternName(inner, kind)),
                _ => {},
            },
            VarUseWork::Name(name) => match name {
                Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)))
                    if fv.pretty_name.as_deref() == Some(var_name) =>
                {
                    return true;
                },
                Name::NQuote(proc) => {
                    work.push(VarUseWork::Proc(proc, VarUseKind::Proc));
                    work.push(VarUseWork::Proc(proc, VarUseKind::Name));
                },
                _ => {},
            },
            VarUseWork::InputBind(bind, kind) => match bind {
                InputBind::InputBind(lhs, name) => {
                    work.push(VarUseWork::Name(name));
                    work.push(VarUseWork::PatternName(lhs, kind));
                },
                InputBind::InputBindQuoted(pattern, name) => {
                    work.push(VarUseWork::Name(name));
                    work.push(VarUseWork::Proc(pattern, kind));
                },
                InputBind::InputBindQuery(lhs, name, args) => {
                    work.extend(args.iter().rev().map(|arg| VarUseWork::Proc(arg, kind)));
                    work.push(VarUseWork::Name(name));
                    work.push(VarUseWork::PatternName(lhs, kind));
                },
                InputBind::InputBindQuotedQuery(pattern, name, args) => {
                    work.extend(args.iter().rev().map(|arg| VarUseWork::Proc(arg, kind)));
                    work.push(VarUseWork::Name(name));
                    work.push(VarUseWork::Proc(pattern, kind));
                },
                _ => {},
            },
            VarUseWork::ForRow(row, kind) => match row {
                ForRow::ForRowSingleNoWhere(bind) => {
                    work.push(VarUseWork::InputBind(bind, kind));
                },
                ForRow::ForRowSingleWhere(bind, cond) => {
                    work.push(VarUseWork::Proc(cond, kind));
                    work.push(VarUseWork::InputBind(bind, kind));
                },
                ForRow::ForRowNoWhere(bind, binds) => {
                    work.extend(
                        binds
                            .iter()
                            .rev()
                            .map(|bind| VarUseWork::InputBind(bind, kind)),
                    );
                    work.push(VarUseWork::InputBind(bind, kind));
                },
                ForRow::ForRowWhere(bind, binds, cond) => {
                    work.push(VarUseWork::Proc(cond, kind));
                    work.extend(
                        binds
                            .iter()
                            .rev()
                            .map(|bind| VarUseWork::InputBind(bind, kind)),
                    );
                    work.push(VarUseWork::InputBind(bind, kind));
                },
                _ => {},
            },
        }
    }
    false
}

fn proc_uses_name_var(term: &Proc, var_name: &str) -> bool {
    proc_uses_var(term, var_name, VarUseKind::Name)
}

fn proc_uses_proc_var(term: &Proc, var_name: &str) -> bool {
    proc_uses_var(term, var_name, VarUseKind::Proc)
}

fn infer_var_type_pfor_user(proc: &Proc, var_name: &str) -> Option<TermType> {
    let Proc::PForUser(rows, body) = proc else {
        return None;
    };
    infer_var_type_in_receive_rows(rows, body, var_name)
}

fn infer_var_type_in_receive_rows(
    rows: &[ForRow],
    body: &Proc,
    var_name: &str,
) -> Option<TermType> {
    for row_index in 0..rows.len() {
        let remaining_rows = &rows[row_index..];
        match &remaining_rows[0] {
            ForRow::ForRowSingleNoWhere(b) => {
                if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                    let mut names = Vec::new();
                    infer_receive_pattern_names(&pat, &mut names);
                    if names.iter().any(|n| n == var_name) {
                        return Some(infer_receive_var_type(
                            &remaining_rows[1..],
                            body,
                            None,
                            var_name,
                        ));
                    }
                }
            },
            ForRow::ForRowSingleWhere(b, cond) => {
                if let Some(pat) = receive::bind_pattern_proc(b.as_ref()) {
                    let mut names = Vec::new();
                    infer_receive_pattern_names(&pat, &mut names);
                    if names.iter().any(|n| n == var_name) {
                        return Some(infer_receive_var_type(
                            &remaining_rows[1..],
                            body,
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
                    let true_lit = Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(true)));
                    return Some(infer_receive_var_type(
                        &remaining_rows[1..],
                        body,
                        Some(&true_lit),
                        var_name,
                    ));
                }
            },
            ForRow::ForRowWhere(b, bs, cond) => {
                let mut names = Vec::new();
                names_from_binds(b.as_ref(), bs, &mut names);
                if names.iter().any(|n| n == var_name) {
                    return Some(infer_receive_var_type(
                        &remaining_rows[1..],
                        body,
                        Some(cond.as_ref()),
                        var_name,
                    ));
                }
            },
            _ => {},
        }
    }
    None
}

fn infer_receive_var_type(
    remaining_rows: &[ForRow],
    body: &Proc,
    cond: Option<&Proc>,
    var_name: &str,
) -> TermType {
    let uses_name = receive_continuation_uses_var(remaining_rows, body, var_name, VarUseKind::Name)
        || cond.is_some_and(|c| proc_uses_name_var(c, var_name));
    let uses_proc = receive_continuation_uses_var(remaining_rows, body, var_name, VarUseKind::Proc)
        || cond.is_some_and(|c| proc_uses_proc_var(c, var_name));
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

fn collect_rholang_var_types(
    term: &Proc,
    result: &mut Vec<VarTypeInfo>,
    seen: &mut std::collections::HashSet<String>,
) {
    enum CollectWork<'a> {
        Proc(&'a Proc),
        ReceiveRows(&'a [ForRow], &'a Proc),
    }

    let mut work = vec![CollectWork::Proc(term)];
    while let Some(task) = work.pop() {
        match task {
            CollectWork::Proc(term) => match term {
                Proc::PForUser(rows, body) => {
                    work.push(CollectWork::ReceiveRows(rows, body));
                },
                Proc::PPar(procs) => {
                    let first_child = work.len();
                    work.extend(procs.iter().map(|(proc, _)| CollectWork::Proc(proc)));
                    work[first_child..].reverse();
                },
                Proc::GuardThen(cond, body) => {
                    work.push(CollectWork::Proc(body));
                    work.push(CollectWork::Proc(cond));
                },
                Proc::POutput(_, payload) => work.push(CollectWork::Proc(payload)),
                Proc::PNew(scope) => work.push(CollectWork::Proc(scope.unsafe_body())),
                _ => {},
            },
            CollectWork::ReceiveRows([], body) => work.push(CollectWork::Proc(body)),
            CollectWork::ReceiveRows(rows, body) => {
                let mut condition = None;
                match &rows[0] {
                    ForRow::ForRowSingleNoWhere(bind) => {
                        if let Some(pattern) = receive::bind_pattern_proc(bind.as_ref()) {
                            let mut names = Vec::new();
                            infer_receive_pattern_names(&pattern, &mut names);
                            for name in names {
                                if seen.insert(name.clone()) {
                                    result.push(VarTypeInfo {
                                        ty: infer_receive_var_type(&rows[1..], body, None, &name),
                                        name,
                                    });
                                }
                            }
                        }
                    },
                    ForRow::ForRowSingleWhere(bind, cond) => {
                        if let Some(pattern) = receive::bind_pattern_proc(bind.as_ref()) {
                            let mut names = Vec::new();
                            infer_receive_pattern_names(&pattern, &mut names);
                            for name in names {
                                if seen.insert(name.clone()) {
                                    result.push(VarTypeInfo {
                                        ty: infer_receive_var_type(
                                            &rows[1..],
                                            body,
                                            Some(cond.as_ref()),
                                            &name,
                                        ),
                                        name,
                                    });
                                }
                            }
                        }
                        condition = Some(cond.as_ref());
                    },
                    ForRow::ForRowNoWhere(bind, binds) => {
                        let mut names = Vec::new();
                        names_from_binds(bind.as_ref(), binds, &mut names);
                        let true_lit = Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(true)));
                        for name in names {
                            if seen.insert(name.clone()) {
                                result.push(VarTypeInfo {
                                    ty: infer_receive_var_type(
                                        &rows[1..],
                                        body,
                                        Some(&true_lit),
                                        &name,
                                    ),
                                    name,
                                });
                            }
                        }
                    },
                    ForRow::ForRowWhere(bind, binds, cond) => {
                        let mut names = Vec::new();
                        names_from_binds(bind.as_ref(), binds, &mut names);
                        for name in names {
                            if seen.insert(name.clone()) {
                                result.push(VarTypeInfo {
                                    ty: infer_receive_var_type(
                                        &rows[1..],
                                        body,
                                        Some(cond.as_ref()),
                                        &name,
                                    ),
                                    name,
                                });
                            }
                        }
                        condition = Some(cond.as_ref());
                    },
                    _ => {},
                }

                // The recursive traversal visited a row's condition before the next row, then
                // visited the receive body after all rows. LIFO insertion keeps that order.
                work.push(CollectWork::ReceiveRows(&rows[1..], body));
                if let Some(condition) = condition {
                    work.push(CollectWork::Proc(condition));
                }
            },
        }
    }
}

impl RholangLanguage {
    pub fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        let Some(typed_term) = term.as_any().downcast_ref::<RholangTerm>() else {
            return <RholangLanguage as Language>::infer_var_types(self, term);
        };
        match &typed_term.0 {
            RholangTermInner::Proc(p) => {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                collect_rholang_var_types(p, &mut result, &mut seen);
                RholangLanguage::collect_all_proc_vars(p, p, &mut result, &mut seen);
                result
            },
            _ => <RholangLanguage as Language>::infer_var_types(self, term),
        }
    }

    pub fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        let Some(typed_term) = term.as_any().downcast_ref::<RholangTerm>() else {
            return <RholangLanguage as Language>::infer_var_type(self, term, var_name);
        };
        if let RholangTermInner::Proc(proc) = &typed_term.0 {
            if let Some(t) = infer_var_type_pfor_user(proc, var_name) {
                return Some(t);
            }
            if let Some(t) = proc.infer_var_type(var_name) {
                return Some(RholangLanguage::inferred_to_term_type(&t));
            }
            let mut result = Vec::new();
            let mut seen = std::collections::HashSet::new();
            RholangLanguage::collect_all_proc_vars(proc, proc, &mut result, &mut seen);
            return result
                .into_iter()
                .find(|v| v.name == var_name)
                .map(|v| v.ty);
        }
        <RholangLanguage as Language>::infer_var_type(self, term, var_name)
    }
}
