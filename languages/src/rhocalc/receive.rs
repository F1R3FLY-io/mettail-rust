use super::{
    Bag, BigInt, BigRat, Bool, Fixed, Float, ForRow, InputBind, Int, List, Map, Name, Pathmap,
    Proc, ReadZipper, Set, Str, UInt32, WriteZipper,
};
use mettail_runtime::{Binder, FreeVar, HashBag, OrdVar, Scope, Var};
use std::cmp::Ordering;
use std::collections::HashMap;

pub(crate) fn canonicalize_arity_payload(payload: &Proc) -> Proc {
    match payload {
        Proc::CastList(_) => payload.clone(),
        Proc::PZero => crate::rhocalc::runtime::mk_proc_list(vec![]),
        _ => crate::rhocalc::runtime::mk_proc_list(vec![payload.clone()]),
    }
}

pub(crate) fn canonicalize_arity_pattern(pattern: &Proc) -> Proc {
    match pattern {
        Proc::CastList(_) | Proc::PVar(_) => pattern.clone(),
        _ => crate::rhocalc::runtime::mk_proc_list(vec![pattern.clone()]),
    }
}

/// For `x <- c` with a simple variable, bind `x` to the whole message. Scalar
/// sends are arity-normalized to a one-element list before COMM; unwrap that so
/// `c!(p)` and `c!([1, 2])` bind `p` and `[1, 2]` respectively.
fn payload_for_simple_var_bind(q: &Proc) -> Proc {
    match q {
        Proc::CastList(list) => {
            if let List::ListLit(items) = list.as_ref() {
                if items.len() == 1 {
                    return items[0].clone();
                }
            }
            q.clone()
        },
        _ => q.clone(),
    }
}

fn is_simple_var_bind(bind: &InputBind) -> bool {
    matches!(
        bind,
        InputBind::InputBind(lhs, _)
            | InputBind::InputBindPersistent(lhs, _)
            | InputBind::InputBindQuery(lhs, _, _)
        if matches!(lhs.as_ref(), Name::NVar(_))
    )
}

fn bind_to_arity_pattern(bind: &InputBind) -> Option<Proc> {
    match bind {
        InputBind::InputBind(lhs, _)
        | InputBind::InputBindPersistent(lhs, _)
        | InputBind::InputBindQuery(lhs, _, _) => {
            if matches!(lhs.as_ref(), Name::NVar(_)) {
                Some(name_pattern_to_proc(lhs.as_ref()))
            } else {
                Some(crate::rhocalc::runtime::mk_proc_list(vec![name_pattern_to_proc(
                    lhs.as_ref(),
                )]))
            }
        },
        InputBind::InputBindPolyadic(lhs, lhss, _)
        | InputBind::InputBindPersistentPolyadic(lhs, lhss, _) => {
            let mut items = Vec::with_capacity(1 + lhss.len());
            items.push(name_pattern_to_proc(lhs.as_ref()));
            items.extend(lhss.iter().map(name_pattern_to_proc));
            Some(crate::rhocalc::runtime::mk_proc_list(items))
        },
        InputBind::InputBindEmpty(_)
        | InputBind::InputBindEmptyPersistent(_)
        | InputBind::InputBindEmptyQuery(_, _) => {
            Some(crate::rhocalc::runtime::mk_proc_list(vec![]))
        },
        InputBind::InputBindQuoted(pat, _)
        | InputBind::InputBindQuotedPersistent(pat, _)
        | InputBind::InputBindQuotedQuery(pat, _, _) => {
            Some(canonicalize_arity_pattern(pat.as_ref()))
        },
        _ => None,
    }
}

pub(crate) fn name_pattern_to_proc(name_pat: &Name) -> Proc {
    match name_pat {
        Name::NVar(v) => Proc::PVar(v.clone()),
        Name::NQuote(p) => p.as_ref().clone(),
        Name::NQuoteShort(p) => p.as_ref().clone(),
        Name::NQuoteNil => Proc::PZero,
        _ => Proc::Err,
    }
}

/// Lower `@P` / `@Nil` name sugar to the canonical `NQuote` channel shape used
/// by send/receive matching and `Exec` rewrites.
pub(crate) fn normalize_quote_name(name: &Name) -> Name {
    match name {
        Name::NQuoteNil => Name::NQuote(Box::new(Proc::PZero)),
        Name::NQuoteShort(p) => Name::NQuote(Box::new(p.as_ref().clone())),
        Name::NParen(inner) => Name::NParen(Box::new(normalize_quote_name(inner.as_ref()))),
        other => other.clone(),
    }
}

pub(crate) fn bind_pattern_proc(bind: &InputBind) -> Option<Proc> {
    bind_to_arity_pattern(bind)
}

fn bind_channel_name(bind: &InputBind) -> Option<&Name> {
    match bind {
        InputBind::InputBind(_, n) => Some(n.as_ref()),
        InputBind::InputBindPersistent(_, n) => Some(n.as_ref()),
        InputBind::InputBindPolyadic(_, _, n) => Some(n.as_ref()),
        InputBind::InputBindPersistentPolyadic(_, _, n) => Some(n.as_ref()),
        InputBind::InputBindQuery(_, n, _) => Some(n.as_ref()),
        InputBind::InputBindEmpty(n) => Some(n.as_ref()),
        InputBind::InputBindEmptyPersistent(n) => Some(n.as_ref()),
        InputBind::InputBindEmptyQuery(n, _) => Some(n.as_ref()),
        InputBind::InputBindQuoted(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuotedPersistent(_, n) => Some(n.as_ref()),
        InputBind::InputBindQuotedQuery(_, n, _) => Some(n.as_ref()),
        _ => None,
    }
}

fn is_persistent_bind(bind: &InputBind) -> bool {
    matches!(
        bind,
        InputBind::InputBindPersistent(_, _)
            | InputBind::InputBindPersistentPolyadic(_, _, _)
            | InputBind::InputBindEmptyPersistent(_)
            | InputBind::InputBindQuotedPersistent(_, _)
    )
}

fn is_empty_bind(bind: &InputBind) -> bool {
    matches!(
        bind,
        InputBind::InputBindEmpty(_)
            | InputBind::InputBindEmptyPersistent(_)
            | InputBind::InputBindEmptyQuery(_, _)
    )
}

fn empty_bind_matches_payload(q: &Proc) -> bool {
    let q_norm = canonicalize_arity_payload(q);
    match q_norm {
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => !items.is_empty(),
            _ => false,
        },
        _ => false,
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
        Proc::Eq(a, b) => {
            if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(a, b) {
                Some(v)
            } else {
                Some(eval_cmp_order(a, b)? == Ordering::Equal)
            }
        },
        Proc::Ne(a, b) => {
            if let Some(v) = crate::rhocalc::runtime::compare_collection_equality(a, b) {
                Some(!v)
            } else {
                Some(eval_cmp_order(a, b)? != Ordering::Equal)
            }
        },
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
                bound.term_eq(v)
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
            _ => pattern.term_eq(value),
        },
        (Proc::CastBag(p), Proc::CastBag(v)) => match (p.as_ref(), v.as_ref()) {
            (Bag::BagLit(pb), Bag::BagLit(vb)) => match_bag_pattern(pb, vb, env),
            _ => pattern.term_eq(value),
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
            _ => pattern.term_eq(value),
        },
        (Proc::CastPathmap(p), Proc::CastPathmap(v)) => match (p.as_ref(), v.as_ref()) {
            (Pathmap::PathmapLit(pm), Pathmap::PathmapLit(vm)) => {
                pm.len() == vm.len()
                    && pm.iter().all(|(k, pv)| {
                        vm.get(k)
                            .map(|vv| collect_pattern_bindings(pv, vv, env))
                            .unwrap_or(false)
                    })
            },
            _ => pattern.term_eq(value),
        },
        (Proc::CastReadZipper(p), Proc::CastReadZipper(v)) => match (p.as_ref(), v.as_ref()) {
            (ReadZipper::Lit(pz), ReadZipper::Lit(vz)) => {
                let pl = pz.as_ref();
                let vl = vz.as_ref();
                pl.1 == vl.1
                    && pl.0.len() == vl.0.len()
                    && pl.0.iter().all(|(k, pv)| {
                        vl.0.get(k)
                            .map(|vv| collect_pattern_bindings(pv, vv, env))
                            .unwrap_or(false)
                    })
            },
            _ => pattern.term_eq(value),
        },
        (Proc::CastWriteZipper(p), Proc::CastWriteZipper(v)) => match (p.as_ref(), v.as_ref()) {
            (WriteZipper::Lit(pz), WriteZipper::Lit(vz)) => {
                let pl = pz.as_ref();
                let vl = vz.as_ref();
                pl.1 == vl.1
                    && pl.0.len() == vl.0.len()
                    && pl.0.iter().all(|(k, pv)| {
                        vl.0.get(k)
                            .map(|vv| collect_pattern_bindings(pv, vv, env))
                            .unwrap_or(false)
                    })
            },
            _ => pattern.term_eq(value),
        },
        (Proc::CastSet(p), Proc::CastSet(v)) => match (p.as_ref(), v.as_ref()) {
            (Set::SetLit(ps), Set::SetLit(vs)) => match_set_pattern(ps, vs, env),
            _ => pattern.term_eq(value),
        },
        _ => pattern.term_eq(value),
    }
}

fn match_set_pattern(
    pat: &mettail_runtime::HashSetLit<Proc>,
    val: &mettail_runtime::HashSetLit<Proc>,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    if pat.len() != val.len() {
        return false;
    }
    let mut remaining: Vec<Proc> = val.iter().cloned().collect();
    for p_elem in pat.iter() {
        let mut matched = false;
        for (idx, v_elem) in remaining.iter().enumerate() {
            let mut trial = env.clone();
            if collect_pattern_bindings(p_elem, v_elem, &mut trial) {
                *env = trial;
                remaining.remove(idx);
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
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
    let matched = if matches!(pattern, Proc::PVar(OrdVar(Var::Free(_)))) {
        collect_pattern_bindings(pattern, &payload_for_simple_var_bind(value), &mut env)
    } else {
        let norm_pattern = canonicalize_arity_pattern(pattern);
        let norm_value = canonicalize_arity_payload(value);
        collect_pattern_bindings(&norm_pattern, &norm_value, &mut env)
    };
    if !matched {
        return None;
    }
    Some(apply_pattern_env(body, &env))
}

fn apply_pattern_env(body: &Proc, env: &HashMap<FreeVar<String>, Proc>) -> Proc {
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
    proc_substituted.subst_name(&vars_refs, &name_repls)
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
    let mut items = Vec::with_capacity(1 + args.len());
    items.push(Proc::PDrop(Box::new(ret.clone())));
    items.extend(args.iter().cloned());
    crate::rhocalc::runtime::mk_output(channel, items, false)
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
        InputBind::InputBindEmptyQuery(channel, args) => {
            let (binder, ret_name) = fresh_query_return(counter);
            let recv_bind = InputBind::InputBindEmpty(Box::new(ret_name.clone()));
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
        ForRow::ForRowSingleNoWhere(b) => matches!(
            b.as_ref(),
            InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
        ),
        ForRow::ForRowSingleWhere(b, _) => matches!(
            b.as_ref(),
            InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
        ),
        ForRow::ForRowNoWhere(b, bs) => {
            matches!(
                b.as_ref(),
                InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
            ) || bs.iter().any(|ib| {
                matches!(
                    ib,
                    InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
                )
            })
        },
        ForRow::ForRowWhere(b, bs, _) => {
            matches!(
                b.as_ref(),
                InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
            ) || bs.iter().any(|ib| {
                matches!(
                    ib,
                    InputBind::InputBindQuery(_, _, _) | InputBind::InputBindEmptyQuery(_, _)
                )
            })
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
    let mut env: HashMap<FreeVar<String>, Proc> = HashMap::new();
    for (ib, q) in binds.iter().zip(aligned_qs.iter()) {
        if !collect_input_bindings(ib, q, &mut env) {
            return None;
        }
    }
    let acc_body = apply_pattern_env(body, &env);
    let acc_cond = apply_pattern_env(cond, &env);

    match eval_guard_bool(&acc_cond) {
        Some(true) => Some(acc_body),
        _ => None,
    }
}

fn collect_input_bindings(
    ib: &InputBind,
    q: &Proc,
    env: &mut HashMap<FreeVar<String>, Proc>,
) -> bool {
    if is_empty_bind(ib) {
        return empty_bind_matches_payload(q);
    }
    let pat = match bind_to_arity_pattern(ib) {
        Some(p) => p,
        None => return false,
    };
    if is_simple_var_bind(ib) {
        collect_pattern_bindings(&pat, &payload_for_simple_var_bind(q), env)
    } else {
        let q_norm = canonicalize_arity_payload(q);
        collect_pattern_bindings(&pat, &q_norm, env)
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
    let mut flat_bag = HashBag::new();
    fn flatten_into(bag: &mut HashBag<Proc>, p: &Proc) {
        match p {
            Proc::PPar(ps) => {
                for (elem, count) in ps.iter() {
                    for _ in 0..count {
                        flatten_into(bag, elem);
                    }
                }
            },
            Proc::PParInfix(a, b) => {
                flatten_into(bag, a);
                flatten_into(bag, b);
            },
            other => bag.insert(other.clone()),
        }
    }
    for (elem, count) in bag.iter() {
        for _ in 0..count {
            flatten_into(&mut flat_bag, elem);
        }
    }
    for (cand, _) in flat_bag.iter() {
        if let Proc::PForUser(rows, body) = cand {
            if !rows.is_empty() {
                if let Some(p) = try_comm_on_pfor_user(&flat_bag, cand, rows, body.as_ref()) {
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
        ForRow::ForRowSinglePersistentNoWhere(lhs, n) => {
            let b = InputBind::InputBindPersistent(
                Box::new(lhs.as_ref().clone()),
                Box::new(n.as_ref().clone()),
            );
            try_comm_single(&b, whole_bag, for_key, &cont, None)
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            try_comm_single(b.as_ref(), whole_bag, for_key, &cont, Some(cond.as_ref()))
        },
        ForRow::ForRowSinglePersistentWhere(lhs, n, cond) => {
            let b = InputBind::InputBindPersistent(
                Box::new(lhs.as_ref().clone()),
                Box::new(n.as_ref().clone()),
            );
            try_comm_single(&b, whole_bag, for_key, &cont, Some(cond.as_ref()))
        },
        ForRow::ForRowSingleEmptyPersistentNoWhere(n) => {
            let b = InputBind::InputBindEmptyPersistent(Box::new(n.as_ref().clone()));
            try_comm_single(&b, whole_bag, for_key, &cont, None)
        },
        ForRow::ForRowSingleEmptyPersistentWhere(n, cond) => {
            let b = InputBind::InputBindEmptyPersistent(Box::new(n.as_ref().clone()));
            try_comm_single(&b, whole_bag, for_key, &cont, Some(cond.as_ref()))
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let true_c = Proc::CastBool(Box::new(Bool::BoolLit(true)));
            try_comm_join(b.as_ref(), bs, &true_c, whole_bag, for_key, &cont)
        },
        ForRow::ForRowPersistentNoWhere(lhs, n, bs) => {
            let true_c = Proc::CastBool(Box::new(Bool::BoolLit(true)));
            let b = InputBind::InputBindPersistent(
                Box::new(lhs.as_ref().clone()),
                Box::new(n.as_ref().clone()),
            );
            try_comm_join(&b, bs, &true_c, whole_bag, for_key, &cont)
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            try_comm_join(b.as_ref(), bs, cond.as_ref(), whole_bag, for_key, &cont)
        },
        ForRow::ForRowPersistentWhere(lhs, n, bs, cond) => {
            let b = InputBind::InputBindPersistent(
                Box::new(lhs.as_ref().clone()),
                Box::new(n.as_ref().clone()),
            );
            try_comm_join(&b, bs, cond.as_ref(), whole_bag, for_key, &cont)
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
    let recv_ctx = SingleReceiveCtx {
        pat: bind_pattern_proc(b)?,
        cont,
        where_cond,
        persistent_recv: is_persistent_bind(b),
        empty_bind: is_empty_bind(b),
    };
    for (cand, _) in whole_bag.iter() {
        if let Some((n_out, q)) = output_parts(cand) {
            if recv_ctx.empty_bind && !empty_bind_matches_payload(&q) {
                continue;
            }
            if normalize_quote_name(&n_out) == normalize_quote_name(n_for_output) {
                if let Some(next) = finish_single_comm(whole_bag, for_key, cand, &recv_ctx) {
                    return Some(next);
                }
            }
        }
    }
    None
}

struct SingleReceiveCtx<'a> {
    pat: Proc,
    cont: &'a Proc,
    where_cond: Option<&'a Proc>,
    persistent_recv: bool,
    empty_bind: bool,
}

fn finish_single_comm(
    whole_bag: &HashBag<Proc>,
    for_key: &Proc,
    output_key: &Proc,
    recv_ctx: &SingleReceiveCtx<'_>,
) -> Option<Proc> {
    let (n_out, q) = output_parts(output_key)?;
    let new_center = if recv_ctx.empty_bind {
        if !empty_bind_matches_payload(&q) {
            return None;
        }
        if let Some(c) = recv_ctx.where_cond {
            match eval_guard_bool(c) {
                Some(true) => recv_ctx.cont.clone(),
                _ => return None,
            }
        } else {
            recv_ctx.cont.clone()
        }
    } else {
        if let Some(c) = recv_ctx.where_cond {
            Proc::CommWhere(
                Box::new(recv_ctx.pat.clone()),
                Box::new(n_out.clone()),
                Box::new(q.clone()),
                Box::new(c.clone()),
                Box::new(recv_ctx.cont.clone()),
            )
        } else {
            receive_apply(&recv_ctx.pat, &q, recv_ctx.cont)?
        }
    };
    let persistent_send = is_persistent_output(output_key);
    match (recv_ctx.persistent_recv, persistent_send) {
        (false, false) => ppar_remove_two_insert(whole_bag, for_key, output_key, new_center),
        (false, true) => ppar_remove_one_insert(whole_bag, for_key, new_center),
        (true, false) => ppar_remove_one_insert(whole_bag, output_key, new_center),
        (true, true) => {
            let mut b = whole_bag.clone();
            if b.iter().any(|(p, _)| p.term_eq(&new_center)) {
                return None;
            }
            b.insert(new_center);
            Some(Proc::PPar(b))
        },
    }
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

/// Remove exactly one `key` and insert one `ins` in a new `PPar`.
fn ppar_remove_one_insert(whole_bag: &HashBag<Proc>, key: &Proc, ins: Proc) -> Option<Proc> {
    let mut b = whole_bag.clone();
    if !b.remove(key) {
        return None;
    }
    b.insert(ins);
    Some(Proc::PPar(b))
}

fn output_parts(p: &Proc) -> Option<(Name, Proc)> {
    match p {
        Proc::POutput(n, q) | Proc::PPersistOutput(n, q) => {
            Some((n.as_ref().clone(), q.as_ref().clone()))
        },
        Proc::POutputShort(p, q) => {
            Some((Name::NQuote(Box::new(p.as_ref().clone())), q.as_ref().clone()))
        },
        Proc::PPersistOutputShort(p, q) => {
            Some((Name::NQuote(Box::new(p.as_ref().clone())), q.as_ref().clone()))
        },
        Proc::POutputEmpty(n) | Proc::PPersistOutputEmpty(n) => {
            Some((n.as_ref().clone(), crate::rhocalc::runtime::mk_proc_list(vec![])))
        },
        Proc::POutput2Plus(n, a, bs) | Proc::PPersistOutput2Plus(n, a, bs) => {
            let mut items = Vec::with_capacity(1 + bs.len());
            items.push(a.as_ref().clone());
            items.extend(bs.iter().cloned());
            Some((n.as_ref().clone(), crate::rhocalc::runtime::mk_proc_list(items)))
        },
        _ => None,
    }
}

fn is_persistent_output(p: &Proc) -> bool {
    matches!(
        p,
        Proc::PPersistOutput(_, _)
            | Proc::PPersistOutputShort(_, _)
            | Proc::PPersistOutputEmpty(_)
            | Proc::PPersistOutput2Plus(_, _, _)
    )
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
    let persistent_recv = is_persistent_bind(b);
    let mut work = whole_bag.clone();
    if !persistent_recv && !work.remove(for_key) {
        return None;
    }
    let mut ns_collected: Vec<Name> = Vec::new();
    let mut qs: Vec<Proc> = Vec::new();
    let mut matched_outputs: Vec<Proc> = Vec::new();
    for n in expected_ns {
        let to_remove = work.iter().find_map(|(p, _)| {
            if let Some((n_out, _q)) = output_parts(p) {
                if n_out == n {
                    return Some(p.clone());
                }
            }
            None
        })?;
        let (n_out, q) = output_parts(&to_remove)?;
        let is_persistent = is_persistent_output(&to_remove);
        if !is_persistent && !work.remove(&to_remove) {
            return None;
        }
        ns_collected.push(n_out);
        qs.push(q);
        matched_outputs.push(to_remove);
    }
    let res = comm_pforjoin_subst(b, bs, &ns_collected, &qs, cond, cont)?;
    // Reinsert persistent outputs: they matched but must remain available.
    for p in matched_outputs {
        if is_persistent_output(&p) {
            work.insert(p);
        }
    }
    work.insert(res);
    Some(Proc::PPar(work))
}

#[cfg(test)]
mod comm_tests {
    use super::*;
    use crate::rhocalc::runtime::merge_pp_parallel;

    fn to_ppar(parsed: Proc) -> Proc {
        match parsed {
            Proc::PParInfix(a, b) => merge_pp_parallel(*a, *b),
            other => other,
        }
    }

    #[test]
    fn join_comm_list_concat_body() {
        mettail_runtime::clear_var_cache();
        let input = "a!([ 1, 2 ]) | b!([ 3, 4 ]) | for(x <- a & y <- b){ (*(x)).concat(*(y)) }";
        let parsed = Proc::parse(input).expect("parse");
        let ppar = to_ppar(to_ppar(parsed));
        let reduced = try_comm_rw_proc(&ppar).expect("comm should fire on canonical PPar");
        assert!(
            reduced.to_string().contains("concat"),
            "expected substituted concat body, got {reduced}"
        );
    }

    #[test]
    fn join_comm_multi_input_body() {
        mettail_runtime::clear_var_cache();
        let input = "for(x <- c1 & y <- c2){*(x)} | c1!(p) | c2!(q)";
        let parsed = Proc::parse(input).expect("parse");
        let ppar = to_ppar(to_ppar(parsed));
        try_comm_rw_proc(&ppar).expect("comm should fire on canonical PPar");
    }
}

#[cfg(test)]
mod zipper_pattern_tests {
    use super::*;
    use crate::rhocalc::zipper::{ReadZipperLit, WriteZipperLit};
    use mettail_runtime::PathMapLit;

    fn int(n: i64) -> Proc {
        Proc::CastInt(Box::new(Int::NumLit(n)))
    }

    fn path_key(segments: &[i64]) -> Proc {
        Proc::CastList(Box::new(List::ListLit(segments.iter().copied().map(int).collect())))
    }

    fn pathmap_with_value(key: Proc, val: Proc) -> PathMapLit<Proc, Proc> {
        let mut lit = PathMapLit::new();
        lit.insert(key, val);
        lit
    }

    fn read_zipper_proc(lit: PathMapLit<Proc, Proc>, focus: Vec<u8>) -> Proc {
        Proc::CastReadZipper(Box::new(ReadZipper::Lit(Box::new(ReadZipperLit(lit, focus)))))
    }

    fn write_zipper_proc(lit: PathMapLit<Proc, Proc>, focus: Vec<u8>) -> Proc {
        Proc::CastWriteZipper(Box::new(WriteZipper::Lit(Box::new(WriteZipperLit(lit, focus)))))
    }

    #[test]
    fn read_zipper_pattern_binds_matching_payload() {
        mettail_runtime::clear_var_cache();
        let key = path_key(&[1]);
        let y_pat = Proc::parse("y").expect("pattern var");
        let lit_pat = pathmap_with_value(key.clone(), y_pat);
        let focus = crate::rhocalc::pathmap::encode_proc_path_entry(&key).expect("focus");
        let pattern = read_zipper_proc(lit_pat, focus.clone());
        let lit_val = pathmap_with_value(key, int(42));
        let value = read_zipper_proc(lit_val, focus);
        let body = Proc::parse("y").expect("body var");
        let out = receive_apply(&pattern, &value, &body).expect("bindings");
        assert_eq!(out, int(42));
    }

    #[test]
    fn read_zipper_pattern_blocks_focus_mismatch() {
        let key = path_key(&[1]);
        let lit = pathmap_with_value(key.clone(), int(1));
        let focus_a = crate::rhocalc::pathmap::encode_proc_path_entry(&key).expect("focus");
        let focus_b =
            crate::rhocalc::pathmap::encode_proc_path_entry(&path_key(&[2])).expect("focus");
        let pattern = read_zipper_proc(lit.clone(), focus_a);
        let value = read_zipper_proc(lit, focus_b);
        let body = int(0);
        assert!(receive_apply(&pattern, &value, &body).is_none());
    }

    #[test]
    fn write_zipper_pattern_binds_matching_payload() {
        mettail_runtime::clear_var_cache();
        let key = path_key(&[1]);
        let y_pat = Proc::parse("y").expect("pattern var");
        let lit_pat = pathmap_with_value(key.clone(), y_pat);
        let focus = crate::rhocalc::pathmap::encode_proc_path_entry(&key).expect("focus");
        let pattern = write_zipper_proc(lit_pat, focus.clone());
        let lit_val = pathmap_with_value(key, int(42));
        let value = write_zipper_proc(lit_val, focus);
        let body = Proc::parse("y").expect("body var");
        let out = receive_apply(&pattern, &value, &body).expect("bindings");
        assert_eq!(out, int(42));
    }
}
