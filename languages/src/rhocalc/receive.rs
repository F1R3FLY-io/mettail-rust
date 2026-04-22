use super::{
    Bag, BigInt, BigRat, Bool, Fixed, Float, ForRow, InputBind, Int, List, Map, Name, Proc, Str,
    UInt32,
};
use mettail_runtime::{FreeVar, HashBag, OrdVar, Var};
use std::cmp::Ordering;
use std::collections::HashMap;

pub fn guard_then(cond: &Proc, body: &Proc) -> Proc {
    match cond {
        Proc::CastBool(b) => match b.as_ref() {
            Bool::BoolLit(true) => body.clone(),
            Bool::BoolLit(false) => Proc::PZero,
            _ => Proc::PZero,
        },
        _ => Proc::PZero,
    }
}

fn eval_cmp_order(lhs: &Proc, rhs: &Proc) -> Option<Ordering> {
    match (lhs, rhs) {
        (Proc::CastInt(a), Proc::CastInt(b)) => match (a.as_ref(), b.as_ref()) {
            (Int::NumLit(x), Int::NumLit(y)) => Some(x.cmp(y)),
            _ => None,
        },
        (Proc::CastUInt32(a), Proc::CastUInt32(b)) => match (a.as_ref(), b.as_ref()) {
            (UInt32::NumLit(x), UInt32::NumLit(y)) => Some(x.cmp(y)),
            _ => None,
        },
        (Proc::CastBigInt(a), Proc::CastBigInt(b)) => match (a.as_ref(), b.as_ref()) {
            (BigInt::NumLit(x), BigInt::NumLit(y)) => Some(x.get().cmp(y.get())),
            _ => None,
        },
        (Proc::CastBigRat(a), Proc::CastBigRat(b)) => match (a.as_ref(), b.as_ref()) {
            (BigRat::RatLit(x), BigRat::RatLit(y)) => x.partial_cmp(y),
            _ => None,
        },
        (Proc::CastFloat(a), Proc::CastFloat(b)) => match (a.as_ref(), b.as_ref()) {
            (Float::FloatLit(x), Float::FloatLit(y)) => x.get().partial_cmp(&y.get()),
            _ => None,
        },
        (Proc::CastFixed(a), Proc::CastFixed(b)) => match (a.as_ref(), b.as_ref()) {
            (Fixed::FixedLit(x), Fixed::FixedLit(y)) => Some(x.cmp(y)),
            _ => None,
        },
        (Proc::CastStr(a), Proc::CastStr(b)) => match (a.as_ref(), b.as_ref()) {
            (Str::StringLit(x), Str::StringLit(y)) => Some(x.cmp(y)),
            _ => None,
        },
        _ => None,
    }
}

fn eval_guard_bool(cond: &Proc) -> Option<bool> {
    match cond {
        Proc::CastBool(b) => match b.as_ref() {
            Bool::BoolLit(v) => Some(*v),
            _ => None,
        },
        Proc::And(a, b) => Some(eval_guard_bool(a)? && eval_guard_bool(b)?),
        Proc::Or(a, b) => Some(eval_guard_bool(a)? || eval_guard_bool(b)?),
        Proc::Not(a) => Some(!eval_guard_bool(a)?),
        Proc::Eq(a, b) => Some(eval_cmp_order(a, b)? == Ordering::Equal),
        Proc::Ne(a, b) => Some(eval_cmp_order(a, b)? != Ordering::Equal),
        Proc::Gt(a, b) => Some(eval_cmp_order(a, b)? == Ordering::Greater),
        Proc::Lt(a, b) => Some(eval_cmp_order(a, b)? == Ordering::Less),
        Proc::GtEq(a, b) => {
            let o = eval_cmp_order(a, b)?;
            Some(o == Ordering::Greater || o == Ordering::Equal)
        },
        Proc::LtEq(a, b) => {
            let o = eval_cmp_order(a, b)?;
            Some(o == Ordering::Less || o == Ordering::Equal)
        },
        _ => None,
    }
}

fn collect_pattern_bindings(
    pattern: &Proc,
    value: &Proc,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    match (pattern, value) {
        (Proc::PVar(OrdVar(Var::Free(fv))), v) => {
            if let Some(bound) = env.get(fv) {
                bound == v
            } else {
                env.insert(fv.clone(), v.clone());
                true
            }
        },
        (Proc::CastList(p), Proc::CastList(v)) => match (p.as_ref(), v.as_ref()) {
            (List::ListLit(ps), List::ListLit(vs)) => {
                ps.len() == vs.len()
                    && ps
                        .iter()
                        .zip(vs.iter())
                        .all(|(pp, vv)| collect_pattern_bindings(pp, vv, env))
            },
            _ => pattern == value,
        },
        (Proc::CastBag(p), Proc::CastBag(v)) => match (p.as_ref(), v.as_ref()) {
            (Bag::BagLit(pb), Bag::BagLit(vb)) => match_bag_pattern(pb, vb, env),
            _ => pattern == value,
        },
        (Proc::CastMap(p), Proc::CastMap(v)) => match (p.as_ref(), v.as_ref()) {
            (Map::MapLit(pm), Map::MapLit(vm)) => {
                pm.len() == vm.len()
                    && pm.iter().all(|(k, pv)| {
                        vm.get(k)
                            .map(|vv| collect_pattern_bindings(pv, vv, env))
                            .unwrap_or(false)
                    })
            },
            _ => pattern == value,
        },
        _ => pattern == value,
    }
}

fn match_bag_pattern(
    pat: &HashBag<Proc>,
    val: &HashBag<Proc>,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    let pats: Vec<Proc> = pat
        .iter()
        .flat_map(|(p, c)| std::iter::repeat_n(p.clone(), c))
        .collect();
    let vals: Vec<Proc> = val
        .iter()
        .flat_map(|(v, c)| std::iter::repeat_n(v.clone(), c))
        .collect();
    if pats.len() != vals.len() {
        return false;
    }

    fn bt(
        idx: usize,
        pats: &[Proc],
        vals: &[Proc],
        used: &mut [bool],
        env: &mut HashMap<FreeVar<String>, Proc>,
    ) -> bool {
        if idx == pats.len() {
            return true;
        }
        for j in 0..vals.len() {
            if used[j] {
                continue;
            }
            let mut env_try = env.clone();
            if collect_pattern_bindings(&pats[idx], &vals[j], &mut env_try) {
                used[j] = true;
                if bt(idx + 1, pats, vals, used, &mut env_try) {
                    *env = env_try;
                    return true;
                }
                used[j] = false;
            }
        }
        false
    }

    let mut used = vec![false; vals.len()];
    bt(0, &pats, &vals, &mut used, env)
}

pub(crate) fn receive_apply(pattern: &Proc, value: &Proc, body: &Proc) -> Option<Proc> {
    let mut env: HashMap<FreeVar<String>, Proc> = HashMap::new();
    if !collect_pattern_bindings(pattern, value, &mut env) {
        return None;
    }

    let vars_owned: Vec<FreeVar<String>> = env.keys().cloned().collect();
    let vars_refs: Vec<&FreeVar<String>> = vars_owned.iter().collect();
    let proc_repls: Vec<Proc> = vars_owned
        .iter()
        .map(|v| env.get(v).cloned().expect("binding exists"))
        .collect();
    let name_repls: Vec<Name> = proc_repls
        .iter()
        .map(|p| Name::NQuote(Box::new(p.clone())))
        .collect();

    let proc_substituted = body.subst(&vars_refs, &proc_repls);
    Some(proc_substituted.subst_name(&vars_refs, &name_repls))
}

pub fn comm_pforwhere_subst(pat: &Proc, n: &Name, q: &Proc, cond: &Proc, body: &Proc) -> Proc {
    let blocked = || {
        Proc::CommWhere(
            Box::new(pat.clone()),
            Box::new(n.clone()),
            Box::new(q.clone()),
            Box::new(cond.clone()),
            Box::new(body.clone()),
        )
    };

    let Some(sub_body) = receive_apply(pat, q, body) else {
        return blocked();
    };
    let Some(sub_cond) = receive_apply(pat, q, cond) else {
        return blocked();
    };

    match eval_guard_bool(&sub_cond) {
        Some(true) => sub_body,
        _ => blocked(),
    }
}

fn apply_row(row: ForRow, inner: Proc) -> Proc {
    match row {
        ForRow::ForRowSingleNoWhere(b) => match *b {
            InputBind::InputBind(pat, n) => Proc::PFor(pat, n, Box::new(inner)),
            _ => Proc::Err,
        },
        ForRow::ForRowSingleWhere(b, cond) => match *b {
            InputBind::InputBind(pat, n) => Proc::PForWhere(pat, n, cond, Box::new(inner)),
            _ => Proc::Err,
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let true_cond = Box::new(Proc::CastBool(Box::new(Bool::BoolLit(true))));
            Proc::PForJoin(b, bs, true_cond, Box::new(inner))
        },
        ForRow::ForRowWhere(b, bs, cond) => Proc::PForJoin(b, bs, cond, Box::new(inner)),
        _ => Proc::Err,
    }
}

/// Desugar a list of ForRows into nested `for` calls (right-to-left folding so
/// the first row becomes the outermost receive).
///
/// The `body` parameter is taken by reference because Ascent binds fold-relation
/// results as references in its generated rule code.
pub fn desugar_for_rows(rows: Vec<ForRow>, body: &Proc) -> Proc {
    rows.into_iter()
        .rev()
        .fold((*body).clone(), |inner, row| apply_row(row, inner))
}

pub(crate) fn channel_names_from_row(b: &InputBind, bs: &[InputBind]) -> Option<Vec<Name>> {
    let mut out = Vec::with_capacity(1 + bs.len());
    match b {
        InputBind::InputBind(_, n) => out.push(n.as_ref().clone()),
        _ => return None,
    }
    for x in bs {
        match x {
            InputBind::InputBind(_, n) => out.push(n.as_ref().clone()),
            _ => return None,
        }
    }
    Some(out)
}

/// Multi-channel COMM reduction for `PForJoin` (replaces old `PInputs` + `eval` on scopes).
///
/// `ns` / `qs` come from the same `zip` as the `POutput` premises; we require they align with
/// the channel names in `b` / `bs`. Applies each `(pattern, payload)` like `CommPatternWhere`.
pub fn comm_pforjoin_subst(
    b: &InputBind,
    bs: &[InputBind],
    ns: &[Name],
    qs: &[Proc],
    cond: &Proc,
    body: &Proc,
) -> Proc {
    let blocked = || {
        let mut bag = HashBag::new();
        Proc::insert_into_ppar(
            &mut bag,
            Proc::PForJoin(
                Box::new(b.clone()),
                bs.to_vec(),
                Box::new(cond.clone()),
                Box::new(body.clone()),
            ),
        );
        for (n, q) in ns.iter().zip(qs.iter()) {
            Proc::insert_into_ppar(
                &mut bag,
                Proc::POutput(Box::new(n.clone()), Box::new(q.clone())),
            );
        }
        Proc::PPar(bag)
    };

    let Some(expected_ns) = channel_names_from_row(b, bs) else {
        return blocked();
    };
    if expected_ns.len() != ns.len() || expected_ns.len() != qs.len() {
        return blocked();
    }
    // PPar is a bag; output order in `ns/qs` is not stable. Align payloads to expected channels.
    let mut used = vec![false; ns.len()];
    let mut aligned_qs: Vec<&Proc> = Vec::with_capacity(expected_ns.len());
    for expected in &expected_ns {
        let mut found = None;
        for (idx, seen_n) in ns.iter().enumerate() {
            if !used[idx] && seen_n == expected {
                found = Some(idx);
                break;
            }
        }
        let Some(idx) = found else {
            return blocked();
        };
        used[idx] = true;
        aligned_qs.push(&qs[idx]);
    }
    let binds: Vec<&InputBind> = std::iter::once(b).chain(bs.iter()).collect();
    let mut acc_body = body.clone();
    let mut acc_cond = cond.clone();
    for (ib, q) in binds.iter().zip(aligned_qs.iter()) {
        let InputBind::InputBind(pat, _) = ib else {
            return blocked();
        };
        let Some(nb) = receive_apply(pat.as_ref(), q, &acc_body) else {
            return blocked();
        };
        acc_body = nb;
        let Some(nc) = receive_apply(pat.as_ref(), q, &acc_cond) else {
            return blocked();
        };
        acc_cond = nc;
    }

    match eval_guard_bool(&acc_cond) {
        Some(true) => acc_body,
        _ => blocked(),
    }
}
