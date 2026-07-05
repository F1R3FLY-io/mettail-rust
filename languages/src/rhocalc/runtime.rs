use super::{Bag, Int, List, Map, Proc, Set, Str};
use mettail_runtime::{BoundTerm, HashBag};

fn is_collection_cast(proc: &Proc) -> bool {
    matches!(proc, Proc::CastList(_) | Proc::CastBag(_) | Proc::CastMap(_) | Proc::CastSet(_))
}

fn compare_same_kind_collection_equality(lhs: &Proc, rhs: &Proc) -> Option<bool> {
    match (lhs, rhs) {
        (Proc::CastList(la), Proc::CastList(lb)) => match (la.as_ref(), lb.as_ref()) {
            (List::ListLit(_), List::ListLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        (Proc::CastBag(ba), Proc::CastBag(bb)) => match (ba.as_ref(), bb.as_ref()) {
            (Bag::BagLit(ha), Bag::BagLit(hb)) => {
                let na = normalize_bag_elements(ha);
                let nb = normalize_bag_elements(hb);
                Some(BoundTerm::term_eq(&na, &nb))
            },
            _ => None,
        },
        (Proc::CastMap(ma), Proc::CastMap(mb)) => match (ma.as_ref(), mb.as_ref()) {
            (Map::MapLit(_), Map::MapLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        (Proc::CastSet(sa), Proc::CastSet(sb)) => match (sa.as_ref(), sb.as_ref()) {
            (Set::SetLit(_), Set::SetLit(_)) => Some(lhs.term_eq(rhs)),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn compare_collection_equality(lhs: &Proc, rhs: &Proc) -> Option<bool> {
    match (lhs, rhs) {
        (Proc::CastList(_), Proc::CastList(_))
        | (Proc::CastBag(_), Proc::CastBag(_))
        | (Proc::CastMap(_), Proc::CastMap(_))
        | (Proc::CastSet(_), Proc::CastSet(_)) => compare_same_kind_collection_equality(lhs, rhs),
        (a, b) if is_collection_cast(a) || is_collection_cast(b) => Some(false),
        _ => None,
    }
}

pub(crate) fn mk_proc_list(items: Vec<Proc>) -> Proc {
    Proc::CastList(std::sync::Arc::new(List::ListLit(items)))
}

pub(crate) fn mk_proc_set(items: impl IntoIterator<Item = Proc>) -> Proc {
    let mut set = mettail_runtime::HashSetLit::new();
    for item in items {
        set.insert(item);
    }
    Proc::CastSet(std::sync::Arc::new(Set::SetLit(set)))
}

pub(crate) fn normalize_collection_element(elem: &Proc) -> Proc {
    match elem {
        Proc::PDrop(n) => match n.as_ref() {
            super::Name::NQuote(p) => p.as_ref().clone(),
            super::Name::NParen(inner) => match inner.as_ref() {
                super::Name::NQuote(p) => p.as_ref().clone(),
                _ => elem.clone(),
            },
            _ => elem.clone(),
        },
        _ => elem.clone(),
    }
}

pub(crate) fn mk_output(name: &super::Name, items: Vec<Proc>, persistent: bool) -> Proc {
    let payload = std::sync::Arc::new(mk_proc_list(items));
    if persistent {
        Proc::PPersistOutput(std::sync::Arc::new(name.clone()), payload)
    } else {
        Proc::POutput(std::sync::Arc::new(name.clone()), payload)
    }
}

pub(crate) fn merge_pp_parallel(lhs: Proc, rhs: Proc) -> Proc {
    let mut bag = mettail_runtime::HashBag::new();
    fn flatten(bag: &mut mettail_runtime::HashBag<Proc>, p: Proc) {
        // `Proc` implements `Drop`; match by reference so we don't move `ps` out of
        // it. The catch-all still owns `p` (the borrow ends before the arm body).
        match &p {
            Proc::PPar(ps) => {
                for (elem, count) in ps.iter() {
                    for _ in 0..count {
                        flatten(bag, elem.clone());
                    }
                }
            },
            _ => bag.insert(p),
        }
    }
    flatten(&mut bag, lhs);
    flatten(&mut bag, rhs);
    Proc::PPar(bag)
}

pub(crate) fn normalize_bag_elements(bag: &HashBag<Proc>) -> HashBag<Proc> {
    fn flatten_proc_into_bag(out: &mut HashBag<Proc>, p: &Proc) {
        match p {
            Proc::PPar(ps) => {
                for (elem, count) in ps.iter() {
                    for _ in 0..count {
                        flatten_proc_into_bag(out, elem);
                    }
                }
            },
            Proc::PParInfix(a, b) => {
                flatten_proc_into_bag(out, a);
                flatten_proc_into_bag(out, b);
            },
            other => {
                out.insert(other.clone());
            },
        }
    }

    let mut out = HashBag::new();
    for (elem, count) in bag.iter() {
        for _ in 0..count {
            flatten_proc_into_bag(&mut out, elem);
        }
    }
    out
}

/// Length of a folded `CastStr` / `CastList` / `CastMap` / `CastBag` / `CastSet` literal.
pub(crate) fn fold_proc_length(p: &Proc) -> Proc {
    match p {
        Proc::CastStr(inner) => match &**inner {
            Str::StringLit(x) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(x.len() as i64))),
            _ => Proc::Err,
        },
        Proc::CastList(l) => match l.as_ref() {
            List::ListLit(v) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(v.len() as i64))),
            _ => Proc::Err,
        },
        Proc::CastMap(m) => match m.as_ref() {
            Map::MapLit(ref payload) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(payload.len() as i64))),
            _ => Proc::Err,
        },
        Proc::CastBag(b) => match b.as_ref() {
            Bag::BagLit(h) => {
                let normalized = normalize_bag_elements(h);
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(normalized.len() as i64)))
            },
            _ => Proc::Err,
        },
        Proc::CastSet(s) => match s.as_ref() {
            Set::SetLit(ref payload) => Proc::CastInt(std::sync::Arc::new(Int::NumLit(payload.len() as i64))),
            _ => Proc::Err,
        },
        _ => Proc::Err,
    }
}

fn normalize_query_send_sugar_proc(p: &Proc) -> Proc {
    match p {
        Proc::PParInfix(a, b) => {
            let a_norm = normalize_query_send_sugar_proc(a.as_ref());
            let b_norm = normalize_query_send_sugar_proc(b.as_ref());
            merge_pp_parallel(a_norm, b_norm)
        },
        Proc::POutputEmpty(n) => {
            Proc::POutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(mk_proc_list(vec![])))
        },
        Proc::PPersistOutputEmpty(n) => {
            Proc::PPersistOutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(mk_proc_list(vec![])))
        },
        Proc::POutput2Plus(n, a, bs) => {
            let a_norm = normalize_query_send_sugar_proc(a.as_ref());
            let bs_norm: Vec<Proc> = bs.iter().map(normalize_query_send_sugar_proc).collect();
            let mut items = Vec::with_capacity(1 + bs_norm.len());
            items.push(a_norm);
            items.extend(bs_norm);
            Proc::POutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(mk_proc_list(items)))
        },
        Proc::PPersistOutput2Plus(n, a, bs) => {
            let a_norm = normalize_query_send_sugar_proc(a.as_ref());
            let bs_norm: Vec<Proc> = bs.iter().map(normalize_query_send_sugar_proc).collect();
            let mut items = Vec::with_capacity(1 + bs_norm.len());
            items.push(a_norm);
            items.extend(bs_norm);
            Proc::PPersistOutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(mk_proc_list(items)))
        },
        Proc::POutput(n, q) => {
            let q_norm = crate::rhocalc::receive::canonicalize_arity_payload(q.as_ref());
            Proc::POutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(q_norm))
        },
        Proc::PPersistOutput(n, q) => {
            let q_norm = crate::rhocalc::receive::canonicalize_arity_payload(q.as_ref());
            Proc::PPersistOutput(std::sync::Arc::new(n.as_ref().clone()), std::sync::Arc::new(q_norm))
        },
        Proc::PForUser(rows, body) => {
            let body_norm = normalize_query_send_sugar_proc(body.as_ref());
            if crate::rhocalc::receive::pfor_user_still_has_query_rows(rows) {
                normalize_query_send_sugar_proc(&crate::rhocalc::receive::desugar_for_rows(
                    rows.clone(),
                    &body_norm,
                ))
            } else {
                Proc::PForUser(rows.clone(), std::sync::Arc::new(body_norm))
            }
        },
        Proc::PPar(ps) => {
            let mut out = mettail_runtime::HashBag::new();
            for (elem, count) in ps.iter() {
                let norm_elem = normalize_query_send_sugar_proc(elem);
                for _ in 0..count {
                    Proc::insert_into_ppar(&mut out, norm_elem.clone());
                }
            }
            Proc::PPar(out)
        },
        Proc::PNew(scope) => {
            let (binders, body) = scope.clone().unbind();
            let norm_body = normalize_query_send_sugar_proc(&body);
            Proc::PNew(mettail_runtime::Scope::new(binders, std::sync::Arc::new(norm_body)))
        },
        _ => p.clone(),
    }
}

impl Proc {
    pub fn term_eq(&self, other: &Self) -> bool {
        let lhs = normalize_query_send_sugar_proc(self);
        let rhs = normalize_query_send_sugar_proc(other);
        mettail_runtime::BoundTerm::term_eq(&lhs, &rhs)
    }

    /// Try exactly one custom COMM rewrite step for `PForUser` receives inside a `PPar`.
    ///
    /// This is useful for bounded semantic assertions in tests where full fixpoint search may diverge
    /// (e.g. persistent receive + persistent send loops).
    pub fn try_comm_once(&self) -> Option<Self> {
        let normalized = normalize_query_send_sugar_proc(self);
        crate::rhocalc::receive::try_comm_rw_proc(&normalized)
    }
}
