use super::{
    Bag, BigInt, BigRat, Bool, Fixed, Float, ForRow, InputBind, Int, List, Map, Name, Proc, Str,
    UInt32,
};
use mettail_runtime::{Binder, FreeVar, HashBag, OrdVar, Scope, Var};
use std::cmp::Ordering;
use std::collections::HashMap;

pub(crate) fn name_pattern_to_proc(name_pat: &Name) -> Proc {
    match name_pat {
        Name::NVar(v) => Proc::PVar(v.clone()),
        Name::NQuote(p) => p.as_ref().clone(),
        _ => Proc::Err,
    }
}

pub(crate) fn bind_pattern_proc(bind: &InputBind) -> Option<Proc> {
    match bind {
        InputBind::InputBind(lhs, _) => Some(name_pattern_to_proc(lhs.as_ref())),
        InputBind::InputBindQuery(lhs, _, _) => Some(name_pattern_to_proc(lhs.as_ref())),
        InputBind::InputBindQuoted(pat, _) => Some(pat.as_ref().clone()),
        InputBind::InputBindQuotedQuery(pat, _, _) => Some(pat.as_ref().clone()),
        _ => None,
    }
}

fn bind_channel_name(bind: &InputBind) -> Option<&Name> {
    match bind {
        InputBind::InputBind(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuery(_, n, _) => Some(n.as_ref()),
        InputBind::InputBindQuoted(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuotedQuery(_, n, _) => Some(n.as_ref()),
        _ => None,
    }
}

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

fn fresh_query_return(counter: &mut usize) -> (Binder<String>, Name) {
    let idx = *counter;
    *counter += 1;
    let fv: FreeVar<String> = FreeVar::fresh_named(format!("__r{}", idx));
    let binder = Binder(fv.clone());
    let name = Name::NVar(OrdVar(Var::Free(fv)));
    (binder, name)
}

fn mk_query_send(channel: &Name, ret: &Name, args: &[Proc]) -> Proc {
    if args.is_empty() {
        return Proc::POutput(
            Box::new(channel.clone()),
            Box::new(Proc::PDrop(Box::new(ret.clone()))),
        );
    }
    Proc::POutput2Plus(
        Box::new(channel.clone()),
        Box::new(Proc::PDrop(Box::new(ret.clone()))),
        args.to_vec(),
    )
}

fn desugar_query_bind(
    bind: InputBind,
    counter: &mut usize,
) -> (InputBind, Vec<(Binder<String>, Proc)>) {
    match bind {
        InputBind::InputBindQuery(lhs, channel, args) => {
            let (binder, ret_name) = fresh_query_return(counter);
            let recv_bind = InputBind::InputBind(lhs, Box::new(ret_name.clone()));
            let send = mk_query_send(channel.as_ref(), &ret_name, &args);
            (recv_bind, vec![(binder, send)])
        },
        other => (other, vec![]),
    }
}

fn desugar_row_query_binds(
    row: ForRow,
    counter: &mut usize,
) -> (ForRow, Vec<(Binder<String>, Proc)>) {
    match row {
        ForRow::ForRowSingleNoWhere(b) => {
            let (b2, sends) = desugar_query_bind(*b, counter);
            (ForRow::ForRowSingleNoWhere(Box::new(b2)), sends)
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            let (b2, sends) = desugar_query_bind(*b, counter);
            (ForRow::ForRowSingleWhere(Box::new(b2), cond), sends)
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut acc_sends = Vec::new();
            let (b2, mut sends0) = desugar_query_bind(*b, counter);
            acc_sends.append(&mut sends0);
            let mut bs2 = Vec::with_capacity(bs.len());
            for ib in bs {
                let (ib2, mut sends_i) = desugar_query_bind(ib, counter);
                acc_sends.append(&mut sends_i);
                bs2.push(ib2);
            }
            (ForRow::ForRowNoWhere(Box::new(b2), bs2), acc_sends)
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut acc_sends = Vec::new();
            let (b2, mut sends0) = desugar_query_bind(*b, counter);
            acc_sends.append(&mut sends0);
            let mut bs2 = Vec::with_capacity(bs.len());
            for ib in bs {
                let (ib2, mut sends_i) = desugar_query_bind(ib, counter);
                acc_sends.append(&mut sends_i);
                bs2.push(ib2);
            }
            (ForRow::ForRowWhere(Box::new(b2), bs2, cond), acc_sends)
        },
        _ => (row, vec![]),
    }
}

/// True if any `ForRow` still uses `InputBindQuery` / `InputBindQuotedQuery` (parse-time
/// fold should have removed these; this supports a `fold_proc` idempotent pass).
pub fn pfor_user_still_has_query_rows(rows: &[ForRow]) -> bool {
    rows.iter().any(|row| match row {
        ForRow::ForRowSingleNoWhere(b) => matches!(b.as_ref(), InputBind::InputBindQuery(_, _, _)),
        ForRow::ForRowSingleWhere(b, _) => matches!(b.as_ref(), InputBind::InputBindQuery(_, _, _)),
        ForRow::ForRowNoWhere(b, bs) => {
            matches!(b.as_ref(), InputBind::InputBindQuery(_, _, _))
                || bs
                    .iter()
                    .any(|ib| matches!(ib, InputBind::InputBindQuery(_, _, _)))
        },
        ForRow::ForRowWhere(b, bs, _) => {
            matches!(b.as_ref(), InputBind::InputBindQuery(_, _, _))
                || bs
                    .iter()
                    .any(|ib| matches!(ib, InputBind::InputBindQuery(_, _, _)))
        },
        _ => false,
    })
}

/// Desugar a list of ForRows into nested `for` calls (right-to-left folding so
/// the first row becomes the outermost receive).
///
/// The `body` parameter is taken by reference because Ascent binds fold-relation
/// results as references in its generated rule code.
pub fn desugar_for_rows(rows: Vec<ForRow>, body: &Proc) -> Proc {
    let mut counter = 0usize;
    let mut rewritten_rows = Vec::with_capacity(rows.len());
    let mut query_binders_and_sends: Vec<(Binder<String>, Proc)> = Vec::new();
    for row in rows {
        let (rewritten_row, mut sends) = desugar_row_query_binds(row, &mut counter);
        rewritten_rows.push(rewritten_row);
        query_binders_and_sends.append(&mut sends);
    }

    let receive_proc = Proc::PForUser(rewritten_rows, Box::new((*body).clone()));
    if query_binders_and_sends.is_empty() {
        return receive_proc;
    }

    let mut bag = HashBag::new();
    for (_, send) in &query_binders_and_sends {
        Proc::insert_into_ppar(&mut bag, send.clone());
    }
    Proc::insert_into_ppar(&mut bag, receive_proc);

    let binders: Vec<Binder<String>> = query_binders_and_sends
        .into_iter()
        .map(|(b, _)| b)
        .collect();
    Proc::PNew(Scope::new(binders, Box::new(Proc::PPar(bag))))
}

pub(crate) fn channel_names_from_row(b: &InputBind, bs: &[InputBind]) -> Option<Vec<Name>> {
    let mut out = Vec::with_capacity(1 + bs.len());
    out.push(bind_channel_name(b)?.clone());
    for x in bs {
        out.push(bind_channel_name(x)?.clone());
    }
    Some(out)
}

/// Multi-channel COMM reduction for a single join row inside `PForUser` (replaces old
/// `PInputs` + `eval` on scopes).
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
) -> Option<Proc> {
    let expected_ns = channel_names_from_row(b, bs)?;
    if expected_ns.len() != ns.len() || expected_ns.len() != qs.len() {
        return None;
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
        let idx = found?;
        used[idx] = true;
        aligned_qs.push(&qs[idx]);
    }
    let binds: Vec<&InputBind> = std::iter::once(b).chain(bs.iter()).collect();
    let mut acc_body = body.clone();
    let mut acc_cond = cond.clone();
    for (ib, q) in binds.iter().zip(aligned_qs.iter()) {
        let pat = bind_pattern_proc(ib)?;
        let nb = receive_apply(&pat, q, &acc_body)?;
        acc_body = nb;
        let nc = receive_apply(&pat, q, &acc_cond)?;
        acc_cond = nc;
    }

    match eval_guard_bool(&acc_cond) {
        Some(true) => Some(acc_body),
        _ => None,
    }
}

/// Continuation process inside the outer `for` row: either the parsed body or
/// a `PForUser` for the remaining rows. Used for COMM, type inference, and analysis.
pub(crate) fn pfor_continuation_after_first_row(rows: &[ForRow], body: &Proc) -> Proc {
    if rows.len() <= 1 {
        body.clone()
    } else {
        Proc::PForUser(rows[1..].to_vec(), Box::new(body.clone()))
    }
}

/// One-step `PForUser` communication reduction on a `PPar`, mirroring the former
/// `CommPattern` / `CommPatternWhere` / `Comm` rewrite rules.
pub fn try_comm_rw_proc(s: &Proc) -> Option<Proc> {
    let Proc::PPar(bag) = s else {
        return None;
    };
    for (cand, _) in bag.iter() {
        if let Proc::PForUser(rows, body) = cand {
            if !rows.is_empty() {
                if let Some(p) = try_comm_on_pfor_user(bag, cand, rows, body.as_ref()) {
                    return Some(p);
                }
            }
        }
    }
    None
}

fn try_comm_on_pfor_user(
    whole_bag: &HashBag<Proc>,
    for_key: &Proc,
    rows: &[ForRow],
    body: &Proc,
) -> Option<Proc> {
    if rows.is_empty() {
        return None;
    }
    let cont = pfor_continuation_after_first_row(rows, body);
    match &rows[0] {
        ForRow::ForRowSingleNoWhere(b) => {
            try_comm_single(b.as_ref(), whole_bag, for_key, &cont, None)
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            try_comm_single(b.as_ref(), whole_bag, for_key, &cont, Some(cond.as_ref()))
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let true_c = Proc::CastBool(Box::new(Bool::BoolLit(true)));
            try_comm_join(b.as_ref(), bs, &true_c, whole_bag, for_key, &cont)
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            try_comm_join(b.as_ref(), bs, cond.as_ref(), whole_bag, for_key, &cont)
        },
        _ => None,
    }
}

fn try_comm_single(
    b: &InputBind,
    whole_bag: &HashBag<Proc>,
    for_key: &Proc,
    cont: &Proc,
    where_cond: Option<&Proc>,
) -> Option<Proc> {
    let n_for_output = bind_channel_name(b)?;
    let pat = bind_pattern_proc(b)?;
    for (cand, _) in whole_bag.iter() {
        if let Proc::POutput(n_out, _) = cand {
            if n_out.as_ref() == n_for_output {
                return finish_single_comm(whole_bag, for_key, cand, &pat, cont, where_cond);
            }
        }
    }
    None
}

fn finish_single_comm(
    whole_bag: &HashBag<Proc>,
    for_key: &Proc,
    output_key: &Proc,
    pat: &Proc,
    cont: &Proc,
    where_cond: Option<&Proc>,
) -> Option<Proc> {
    let Proc::POutput(n_out, q) = output_key else {
        return None;
    };
    if !pat.pattern_matches(q) {
        return None;
    }
    let new_center = if let Some(c) = where_cond {
        Proc::CommWhere(
            Box::new(pat.clone()),
            Box::new(n_out.as_ref().clone()),
            Box::new(q.as_ref().clone()),
            Box::new(c.clone()),
            Box::new(cont.clone()),
        )
    } else {
        cont.apply_pattern(pat, q.as_ref())?
    };
    ppar_remove_two_insert(whole_bag, for_key, output_key, new_center)
}

/// Remove exactly one `key1`, one `key2`, and insert one `ins` in a new `PPar`.
fn ppar_remove_two_insert(
    whole_bag: &HashBag<Proc>,
    key1: &Proc,
    key2: &Proc,
    ins: Proc,
) -> Option<Proc> {
    let mut b = whole_bag.clone();
    if !b.remove(key1) || !b.remove(key2) {
        return None;
    }
    b.insert(ins);
    Some(Proc::PPar(b))
}

fn try_comm_join(
    b: &InputBind,
    bs: &[InputBind],
    cond: &Proc,
    whole_bag: &HashBag<Proc>,
    for_key: &Proc,
    cont: &Proc,
) -> Option<Proc> {
    let expected_ns = channel_names_from_row(b, bs)?;
    let mut work = whole_bag.clone();
    if !work.remove(for_key) {
        return None;
    }
    let mut ns_collected: Vec<Name> = Vec::new();
    let mut qs: Vec<Proc> = Vec::new();
    for n in expected_ns {
        let to_remove = work.iter().find_map(|(p, _)| {
            if let Proc::POutput(n_out, _q) = p {
                if n_out.as_ref() == &n {
                    return Some(p.clone());
                }
            }
            None
        })?;
        if !work.remove(&to_remove) {
            return None;
        }
        if let Proc::POutput(n_out, q) = &to_remove {
            ns_collected.push(n_out.as_ref().clone());
            qs.push(q.as_ref().clone());
        } else {
            return None;
        }
    }
    let res = comm_pforjoin_subst(b, bs, &ns_collected, &qs, cond, cont)?;
    work.insert(res);
    Some(Proc::PPar(work))
}
