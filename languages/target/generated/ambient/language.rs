/// Inner term enum for multi-category languages (one variant per type in the language).
/// The `Ambiguous` variant holds multiple parse alternatives that will be resolved
/// during substitution or Ascent evaluation.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum AmbientTermInner {
    Proc(Proc),
    Name(Name),
    /// Multiple parse alternatives (2+, flat — no nested Ambiguous).
    Ambiguous(Vec<AmbientTermInner>),
}
impl AmbientTermInner {
    /// Check if this alternative is "accepting" — i.e., fully resolved to a
    /// concrete/ground term (no free variables, evaluable for native types).
    fn is_accepting(&self) -> bool {
        match self {
            AmbientTermInner::Proc(inner) => inner.is_ground(),
            AmbientTermInner::Name(inner) => inner.is_ground(),
            AmbientTermInner::Ambiguous(_) => false,
        }
    }
    /// Collapse a vec of alternatives into a single term.
    /// Invariants: flattens nested Ambiguous, panics on empty, unwraps singletons.
    /// Final disambiguation: if only one alternative is "accepting" (concrete/ground),
    /// choose it even if more candidates exist.
    fn from_alternatives(alts: Vec<Self>) -> Self {
        let n_alts = alts.len();
        let flat: Vec<Self> = alts
            .into_iter()
            .flat_map(|a| match a {
                Self::Ambiguous(inner) => inner,
                other => vec![other],
            })
            .collect();
        match flat.len() {
            0 => panic!("from_alternatives: empty alternatives"),
            1 => flat.into_iter().next().expect("checked len == 1"),
            _ => {
                let accepting: Vec<(usize, &Self)> = flat
                    .iter()
                    .enumerate()
                    .filter(|(_, a)| a.is_accepting())
                    .collect();
                match accepting.len() {
                    1 => {
                        let weights = AMBIGUOUS_WEIGHTS.with(|cell| cell.take());
                        if weights.len() == n_alts && flat.len() == n_alts {
                            let accepted_idx = accepting[0].0;
                            let primary_idx = weights
                                .iter()
                                .enumerate()
                                .min_by(|(_, a), (_, b)| {
                                    a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal)
                                })
                                .map(|(i, _)| i)
                                .unwrap_or(0);
                            if accepted_idx != primary_idx {
                                WEIGHT_CORRECTIONS
                                    .with(|cell| {
                                        let mut corrections = cell.take();
                                        corrections
                                            .push(mettail_prattail::wfst::WeightCorrection {
                                                category: "Ambient",
                                                primary_weight: weights[primary_idx],
                                                selected_weight: weights[accepted_idx],
                                                alternatives_considered: n_alts,
                                            });
                                        cell.set(corrections);
                                    });
                            }
                        }
                        accepting[0].1.clone()
                    }
                    n if n > 1 => {
                        let weights = AMBIGUOUS_WEIGHTS.with(|cell| cell.take());
                        if weights.len() == n_alts && flat.len() == n_alts {
                            let best_idx = accepting
                                .iter()
                                .min_by(|(i, _), (j, _)| {
                                    weights[*i]
                                        .partial_cmp(&weights[*j])
                                        .unwrap_or(std::cmp::Ordering::Equal)
                                })
                                .map(|(i, _)| *i)
                                .expect("accepting non-empty");
                            let overall_primary_idx = weights
                                .iter()
                                .enumerate()
                                .min_by(|(_, a), (_, b)| {
                                    a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal)
                                })
                                .map(|(i, _)| i)
                                .unwrap_or(0);
                            if best_idx != overall_primary_idx {
                                WEIGHT_CORRECTIONS
                                    .with(|cell| {
                                        let mut corrections = cell.take();
                                        corrections
                                            .push(mettail_prattail::wfst::WeightCorrection {
                                                category: "Ambient",
                                                primary_weight: weights[overall_primary_idx],
                                                selected_weight: weights[best_idx],
                                                alternatives_considered: n_alts,
                                            });
                                        cell.set(corrections);
                                    });
                            }
                            flat.into_iter().nth(best_idx).expect("valid index")
                        } else {
                            accepting[0].1.clone()
                        }
                    }
                    _ => Self::Ambiguous(flat),
                }
            }
        }
    }
    /// Substitute environment bindings into the term.
    /// For Ambiguous terms, substitutes each alternative independently and
    /// keeps only those that made progress (Display changed). Deduplicates by Display.
    pub fn substitute_env(&self, env: &AmbientEnv) -> Self {
        match self {
            AmbientTermInner::Ambiguous(alts) => {
                let orig_displays: Vec<std::string::String> = alts
                    .iter()
                    .map(|a| format!("{}", a))
                    .collect();
                let results: Vec<Self> = alts
                    .iter()
                    .map(|alt| {
                        let substituted = match alt {
                            AmbientTermInner::Proc(t) => {
                                AmbientTermInner::Proc(t.substitute_env(env))
                            }
                            AmbientTermInner::Name(t) => {
                                AmbientTermInner::Name(t.substitute_env(env))
                            }
                            AmbientTermInner::Ambiguous(_) => {
                                unreachable!("nested Ambiguous")
                            }
                        };
                        let cross_resolved = (|| -> Self {
                            match &substituted {
                                AmbientTermInner::Proc(Proc::PVar(v)) => {
                                    let name = match &v.0 {
                                        mettail_runtime::Var::Free(fv) => {
                                            fv.pretty_name.as_ref().map(|s| s.to_string())
                                        }
                                        mettail_runtime::Var::Bound(bv) => {
                                            bv.pretty_name.as_ref().map(|s| s.to_string())
                                        }
                                    };
                                    if let Some(name) = name {
                                        if let Some(val) = env.name.get(&name) {
                                            return AmbientTermInner::Name(val.clone());
                                        }
                                    }
                                }
                                AmbientTermInner::Name(Name::NVar(v)) => {
                                    let name = match &v.0 {
                                        mettail_runtime::Var::Free(fv) => {
                                            fv.pretty_name.as_ref().map(|s| s.to_string())
                                        }
                                        mettail_runtime::Var::Bound(bv) => {
                                            bv.pretty_name.as_ref().map(|s| s.to_string())
                                        }
                                    };
                                    if let Some(name) = name {
                                        if let Some(val) = env.proc.get(&name) {
                                            return AmbientTermInner::Proc(val.clone());
                                        }
                                    }
                                }
                                _ => {}
                            }
                            substituted.clone()
                        })();
                        cross_resolved
                    })
                    .collect();
                let result_displays: Vec<std::string::String> = results
                    .iter()
                    .map(|r| format!("{}", r))
                    .collect();
                let progressed: Vec<usize> = (0..results.len())
                    .filter(|&i| result_displays[i] != orig_displays[i])
                    .collect();
                let kept: Vec<Self> = if progressed.is_empty() {
                    results
                } else {
                    progressed.into_iter().map(|i| results[i].clone()).collect()
                };
                let mut seen = std::collections::HashSet::new();
                let unique: Vec<Self> = kept
                    .into_iter()
                    .filter(|a| seen.insert(format!("{}", a)))
                    .collect();
                Self::from_alternatives(unique)
            }
            _ => {
                let substituted = match self {
                    AmbientTermInner::Proc(t) => {
                        AmbientTermInner::Proc(t.substitute_env(env))
                    }
                    AmbientTermInner::Name(t) => {
                        AmbientTermInner::Name(t.substitute_env(env))
                    }
                    AmbientTermInner::Ambiguous(_) => unreachable!(),
                };
                match &substituted {
                    AmbientTermInner::Proc(Proc::PVar(v)) => {
                        let name = match &v.0 {
                            mettail_runtime::Var::Free(fv) => {
                                fv.pretty_name.as_ref().map(|s| s.to_string())
                            }
                            mettail_runtime::Var::Bound(bv) => {
                                bv.pretty_name.as_ref().map(|s| s.to_string())
                            }
                        };
                        if let Some(name) = name {
                            if let Some(val) = env.name.get(&name) {
                                return AmbientTermInner::Name(val.clone());
                            }
                        }
                    }
                    AmbientTermInner::Name(Name::NVar(v)) => {
                        let name = match &v.0 {
                            mettail_runtime::Var::Free(fv) => {
                                fv.pretty_name.as_ref().map(|s| s.to_string())
                            }
                            mettail_runtime::Var::Bound(bv) => {
                                bv.pretty_name.as_ref().map(|s| s.to_string())
                            }
                        };
                        if let Some(name) = name {
                            if let Some(val) = env.proc.get(&name) {
                                return AmbientTermInner::Proc(val.clone());
                            }
                        }
                    }
                    _ => {}
                }
                substituted
            }
        }
    }
}
impl std::fmt::Display for AmbientTermInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AmbientTermInner::Proc(v) => write!(f, "{}", v),
            AmbientTermInner::Name(v) => write!(f, "{}", v),
            AmbientTermInner::Ambiguous(alts) => write!(f, "{}", alts[0]),
        }
    }
}
impl std::fmt::Debug for AmbientTermInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AmbientTermInner::Proc(v) => write!(f, "{:?}", v),
            AmbientTermInner::Name(v) => write!(f, "{:?}", v),
            AmbientTermInner::Ambiguous(alts) => write!(f, "Ambiguous({:?})", alts),
        }
    }
}
/// Wrapper for the term that implements `mettail_runtime::Term`
#[derive(Clone)]
pub struct AmbientTerm(pub AmbientTermInner);
impl mettail_runtime::Term for AmbientTerm {
    fn clone_box(&self) -> Box<dyn mettail_runtime::Term> {
        Box::new(self.clone())
    }
    fn term_id(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        self.0.hash(&mut hasher);
        hasher.finish()
    }
    fn term_eq(&self, other: &dyn mettail_runtime::Term) -> bool {
        if let Some(other_term) = other.as_any().downcast_ref::<AmbientTerm>() {
            self.0 == other_term.0
        } else {
            false
        }
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}
impl std::fmt::Display for AmbientTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::fmt::Debug for AmbientTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}
#[cfg(not(feature = "ascent-parallel"))]
ascent::ascent! {
    struct AmbientAscentProg; relation proc(Proc); #[ds(crate ::eqrel)] relation
    eq_proc(Proc, Proc); #[ds(crate ::dual_indexed)] relation rw_proc(Proc, Proc);
    relation name(Name); #[ds(crate ::eqrel)] relation eq_name(Name, Name); #[ds(crate
    ::dual_indexed)] relation rw_name(Name, Name); relation step_term(Proc); #[ds(crate
    ::dual_indexed)] relation ppar_contains(Proc, Proc); proc(sub.clone()) <- - proc(t),
    for sub in { std::thread_local! { static POOL_PROC_PROC : std::cell::Cell < Vec <
    Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_PROC
    .with(| p | p.take()); buf.clear(); match t { Proc::PIn(_, f1) => { buf.push(f1
    .as_ref().clone()); }, Proc::POut(_, f1) => { buf.push(f1.as_ref().clone()); },
    Proc::POpen(_, f1) => { buf.push(f1.as_ref().clone()); }, Proc::PAmb(_, f1) => { buf
    .push(f1.as_ref().clone()); }, Proc::PNew(scope) => { buf.push(scope.inner()
    .unsafe_body.as_ref().clone()); }, Proc::ApplyProc(lam, arg) => { buf.push(lam
    .as_ref().clone()); buf.push(arg.as_ref().clone()); }, Proc::MApplyProc(lam, args) =>
    { buf.push(lam.as_ref().clone()); buf.extend(args.iter().cloned()); },
    Proc::LamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::MLamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::LamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, Proc::MLamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(); name(sub
    .clone()) <- - proc(t), for sub in { std::thread_local! { static POOL_PROC_NAME :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_NAME.with(| p | p.take()); buf.clear(); match t { Proc::PIn(f0,
    _) => { buf.push(f0.as_ref().clone()); }, Proc::POut(f0, _) => { buf.push(f0.as_ref()
    .clone()); }, Proc::POpen(f0, _) => { buf.push(f0.as_ref().clone()); },
    Proc::PAmb(f0, _) => { buf.push(f0.as_ref().clone()); }, Proc::ApplyName(_, arg) => {
    buf.push(arg.as_ref().clone()); }, Proc::MApplyName(_, args) => { buf.extend(args
    .iter().cloned()); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_NAME.with(| p | p.set(buf)); iter_buf } .into_iter(); name(sub.clone()) <-
    - name(t), for sub in { std::thread_local! { static POOL_NAME_NAME : std::cell::Cell
    < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_NAME_NAME.with(| p | p.take()); buf.clear(); match t { Name::ApplyProc(lam, _)
    => { buf.push(lam.as_ref().clone()); }, Name::MApplyProc(lam, _) => { buf.push(lam
    .as_ref().clone()); }, Name::LamProc(scope) => { buf.push(scope.inner().unsafe_body
    .as_ref().clone()); }, Name::MLamProc(scope) => { buf.push(scope.inner().unsafe_body
    .as_ref().clone()); }, Name::ApplyName(lam, arg) => { buf.push(lam.as_ref().clone());
    buf.push(arg.as_ref().clone()); }, Name::MApplyName(lam, args) => { buf.push(lam
    .as_ref().clone()); buf.extend(args.iter().cloned()); }, Name::LamName(scope) => {
    buf.push(scope.inner().unsafe_body.as_ref().clone()); }, Name::MLamName(scope) => {
    buf.push(scope.inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_NAME_NAME.with(| p | p.set(buf)); iter_buf }
    .into_iter(); proc(c1.clone().normalize()) <- - proc(c0), rw_proc(c0, c1), if { use
    std::hash:: { Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); c1
    .hash(& mut __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_EXPAND : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_EXPAND.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }; ppar_contains(parent.clone(), elem.clone()) <- -
    proc(parent), if let Proc::PPar(ref coll_field) = parent, for (elem, _count) in
    coll_field.iter(); proc(elem.clone()) <- - ppar_contains(_parent, elem); rw_proc(t
    .clone(), match t { Proc::ApplyProc(_, arg) => Proc::ApplyProc(Box::new(new_lam
    .clone()), arg.clone()), Proc::MApplyProc(_, args) =>
    Proc::MApplyProc(Box::new(new_lam.clone()), args.clone()), Proc::ApplyName(_, arg) =>
    Proc::ApplyName(Box::new(new_lam.clone()), arg.clone()), Proc::MApplyName(_, args) =>
    Proc::MApplyName(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - proc(t), for lam in { std::thread_local! { static POOL_PROC_CONG_LAM :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyProc(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::ApplyName(lam, _) => { buf.push(lam
    .as_ref().clone()); }, Proc::MApplyName(lam, _) => { buf.push(lam.as_ref().clone());
    }, _ => {}, } let iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_LAM.with(| p |
    p.set(buf)); iter_buf } .into_iter(), rw_proc(lam, new_lam); rw_proc(t.clone(), match
    t { Proc::ApplyProc(lam, _) => Proc::ApplyProc(lam.clone(), Box::new(new_arg
    .clone())), _ => unreachable!(), }) <- - proc(t), for arg in { std::thread_local! {
    static POOL_PROC_CONG_ARG_PROC : std::cell::Cell < Vec < Proc >> = const {
    std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_CONG_ARG_PROC.with(| p
    | p.take()); buf.clear(); match t { Proc::ApplyProc(_, arg) => { buf.push(arg
    .as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_CONG_ARG_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(), rw_proc(arg,
    new_arg); rw_proc(t.clone(), match t { Proc::ApplyName(lam, _) => Proc::ApplyName(lam
    .clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- - proc(t), for arg
    in { std::thread_local! { static POOL_PROC_CONG_ARG_NAME : std::cell::Cell < Vec <
    Name >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_CONG_ARG_NAME.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyName(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_ARG_NAME.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_name(arg, new_arg); name(c1.clone().normalize()) <- -
    name(c0), rw_name(c0, c1), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); c1.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_EXPAND : std::cell::RefCell <
    (u64, std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_EXPAND.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }; rw_name(t
    .clone(), match t { Name::ApplyName(_, arg) => Name::ApplyName(Box::new(new_lam
    .clone()), arg.clone()), Name::MApplyName(_, args) =>
    Name::MApplyName(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - name(t), for lam in { std::thread_local! { static POOL_NAME_CONG_LAM :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_NAME_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Name::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Name::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_NAME_CONG_LAM.with(| p | p.set(buf)); iter_buf } .into_iter(),
    rw_name(lam, new_lam); rw_name(t.clone(), match t { Name::ApplyName(lam, _) =>
    Name::ApplyName(lam.clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- -
    name(t), for arg in { std::thread_local! { static POOL_NAME_CONG_ARG_NAME :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_NAME_CONG_ARG_NAME.with(| p | p.take()); buf.clear(); match t {
    Name::ApplyName(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_NAME_CONG_ARG_NAME.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_name(arg, new_arg); eq_proc(t.clone(), t.clone()) <- -
    proc(t); eq_name(t.clone(), t.clone()) <- - name(t); eq_proc(s.clone(), t.clone()) <-
    - proc(s), proc(t), if std::mem::discriminant(s) == std::mem::discriminant(t), if
    matches!(s, Proc::PIn(..) | Proc::POut(..) | Proc::POpen(..) | Proc::PAmb(..)), for
    (s_f0, s_f1, t_f0, t_f1) in { std::thread_local! { static POOL_PROC_EQ_CONG_0 :
    std::cell::Cell < Vec < (Name, Proc, Name, Proc) >> = const {
    std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_EQ_CONG_0.with(| p | p
    .take()); buf.clear(); match (s, t) { (Proc::PIn(sf0, sf1), Proc::PIn(tf0, tf1)) => {
    buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1
    .as_ref().clone())); }, (Proc::POut(sf0, sf1), Proc::POut(tf0, tf1)) => { buf
    .push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, (Proc::POpen(sf0, sf1), Proc::POpen(tf0, tf1)) => { buf.push((sf0
    .as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, (Proc::PAmb(sf0, sf1), Proc::PAmb(tf0, tf1)) => { buf.push((sf0
    .as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_EQ_CONG_0.with(| p | p.set(buf)); iter_buf } .into_iter(),
    eq_name(__eqcong_s_f0, __eqcong_t_f0), if s_f0 == __eqcong_s_f0.clone(), if t_f0 ==
    __eqcong_t_f0.clone(), eq_proc(__eqcong_s_f1, __eqcong_t_f1), if s_f1 ==
    __eqcong_s_f1.clone(), if t_f1 == __eqcong_t_f1.clone(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref
    s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed =
    s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PPar(ref
    s_f0) = s, for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PNew(ref s_f0_e0_f0)
    = s_f0_e0, let s_f0_e0_f0_binder = s_f0_e0_f0.unsafe_pattern().clone(), let
    s_f0_e0_f0_body_boxed = s_f0_e0_f0.unsafe_body(), let s_f0_e0_f0_body = & * *
    s_f0_e0_f0_body_boxed, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag }, if s_f0_rest.clone().clone().iter().all(| (elem, _) | !
    mettail_runtime::BoundTerm::free_vars(elem).contains(& s_f0_e0_f0_binder.0.clone())),
    if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_e0_f0_binder.clone()
    .clone(), Box::new(Proc::PPar({ let mut bag = (s_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag, (s_f0_e0_f0_body.clone()).clone()); bag })))))
    .normalize(); eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let
    Proc::PNew(ref s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let
    s_f0_body_boxed = s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let
    Proc::PPar(ref s_f0_body_f0) = s_f0_body, for (s_f0_body_f0_e0, _count_0) in
    s_f0_body_f0.iter(), let s_f0_body_f0_rest = { let mut bag = s_f0_body_f0.clone();
    bag.remove(& s_f0_body_f0_e0); bag }, if s_f0_body_f0_rest.clone().clone().iter()
    .all(| (elem, _) | ! mettail_runtime::BoundTerm::free_vars(elem).contains(&
    s_f0_binder.0.clone())), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PPar({ let mut bag = (s_f0_body_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag,
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone().clone(),
    Box::new((s_f0_body_f0_e0.clone()).clone())))); bag })).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PIn(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PIn(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PIn(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PIn(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POut(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POut(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POut(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POut(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POpen(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POpen(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POpen(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POpen(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PAmb(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PAmb(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PAmb(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PAmb(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize();
    rw_proc(s_orig.clone(), t) <- - eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig =
    __eqrel_s_orig.clone(), let s = __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s,
    for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PAmb(ref s_f0_e0_f0, ref
    s_f0_e0_f1) = s_f0_e0, let s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref
    = & * * s_f0_e0_f1, if let Proc::PPar(ref s_f0_e0_f1_deref_f0) = s_f0_e0_f1_deref,
    for (s_f0_e0_f1_deref_f0_e0, _count_1) in s_f0_e0_f1_deref_f0.iter(), if let
    Proc::PIn(ref s_f0_e0_f1_deref_f0_e0_f0, ref s_f0_e0_f1_deref_f0_e0_f1) =
    s_f0_e0_f1_deref_f0_e0, let s_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f0, let s_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f1, let s_f0_e0_f1_deref_f0_rest = { let mut bag =
    s_f0_e0_f1_deref_f0.clone(); bag.remove(& s_f0_e0_f1_deref_f0_e0); bag }, for
    (s_f0_e1, _count_2) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_e0_f1_deref_f0_e0_f0_deref.clone() ==
    __eqpat_a_M.clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_M.clone(), let
    s_f0_e1_f1_deref = & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone();
    bag.remove(& s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_e0_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = mettail_runtime::HashBag::new();
    Proc::insert_into_ppar(& mut bag, Proc::PAmb(Box::new((s_f0_e0_f0_deref.clone())
    .clone()), Box::new(Proc::PPar({ let mut bag = (s_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref_f0_e0_f1_deref.clone())
    .clone()); bag })))); Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone())
    .clone()); bag })))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PAmb(ref s_f0, ref s_f1) = s, let s_f0_deref = & * *
    s_f0, let s_f1_deref = & * * s_f1, if let Proc::PPar(ref s_f1_deref_f0) = s_f1_deref,
    for (s_f1_deref_f0_e0, _count_0) in s_f1_deref_f0.iter(), if let Proc::PAmb(ref
    s_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1) = s_f1_deref_f0_e0, let
    s_f1_deref_f0_e0_f0_deref = & * * s_f1_deref_f0_e0_f0, let s_f1_deref_f0_e0_f1_deref
    = & * * s_f1_deref_f0_e0_f1, if let Proc::PPar(ref s_f1_deref_f0_e0_f1_deref_f0) =
    s_f1_deref_f0_e0_f1_deref, for (s_f1_deref_f0_e0_f1_deref_f0_e0, _count_1) in
    s_f1_deref_f0_e0_f1_deref_f0.iter(), if let Proc::POut(ref
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1_deref_f0_e0_f1) =
    s_f1_deref_f0_e0_f1_deref_f0_e0, let s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_deref
    .clone() == __eqpat_a_M.clone(), if s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref.clone()
    == __eqpat_b_M.clone(), let s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f1, let s_f1_deref_f0_e0_f1_deref_f0_rest = { let mut
    bag = s_f1_deref_f0_e0_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0_f1_deref_f0_e0); bag }, for (s_f1_deref_f0_e1, _count_2) in
    s_f1_deref_f0.iter(), if & s_f1_deref_f0_e1 != & s_f1_deref_f0_e0, let
    s_f1_deref_f0_rest = { let mut bag = s_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0); bag.remove(& s_f1_deref_f0_e1); bag }, if { use std::hash:: {
    Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f1_deref_f0_rest
    .clone()).clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = (s_f1_deref_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref
    .clone()).clone()); bag })))); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_deref.clone()).clone()), Box::new((s_f1_deref_f0_e1
    .clone()).clone()))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s, for (s_f0_e0, _count_0) in s_f0
    .iter(), if let Proc::POpen(ref s_f0_e0_f0, ref s_f0_e0_f1) = s_f0_e0, let
    s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref = & * * s_f0_e0_f1, for
    (s_f0_e1, _count_1) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_N, __eqpat_b_N), if s_f0_e0_f0_deref.clone() == __eqpat_a_N
    .clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_N.clone(), let s_f0_e1_f1_deref =
    & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash, Hasher }; let
    mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref.clone()).clone());
    Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone()).clone()); bag }))
    .normalize(); rw_proc(parent.clone(), result) <- - proc(parent), if let
    Proc::PPar(ref bag) = parent, for (elem, _count) in bag.iter(), rw_proc(elem.clone(),
    elem_rewritten), let result = Proc::PPar({ let mut new_bag = bag.clone(); new_bag
    .remove(elem); Proc::insert_into_ppar(& mut new_bag, elem_rewritten.clone()); new_bag
    }); rw_proc(lhs.clone(), rhs) <- - proc(lhs), if let Proc::PNew(ref scope) = lhs, let
    binder = scope.unsafe_pattern().clone(), let body = scope.unsafe_body(), rw_proc((* *
    body).clone(), body_rewritten), let rhs =
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(binder.clone(),
    Box::new(body_rewritten.clone()))); rw_proc(lhs.clone(), match (lhs, vi) {
    (Proc::PAmb(x0, _), 0usize) => Proc::PAmb(x0.clone(), Box::new(t.clone())), _ =>
    unreachable!(), }) <- - proc(lhs), if matches!(lhs, Proc::PAmb(..)), for (field_val,
    vi) in { std::thread_local! { static POOL_PROC_SCONG_PROC : std::cell::Cell < Vec <
    (Proc, usize) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_SCONG_PROC.with(| p | p.take()); buf.clear(); match lhs { Proc::PAmb(_, x1)
    => { buf.push(((* * x1).clone(), 0usize)); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_PROC_SCONG_PROC.with(| p | p.set(buf)); iter_buf }
    .into_iter(), rw_proc(field_val, t); rw_proc(__eqrel_closure_a.clone(), c.clone()) <-
    - eq_proc(__eqrel_a, __eqrel_b), let __eqrel_closure_a = __eqrel_a.clone(), let
    __eqrel_closure_b = __eqrel_b.clone(), rw_proc(__eqrel_closure_b, c);
    rw_name(__eqrel_closure_a.clone(), c.clone()) <- - eq_name(__eqrel_a, __eqrel_b), let
    __eqrel_closure_a = __eqrel_a.clone(), let __eqrel_closure_b = __eqrel_b.clone(),
    rw_name(__eqrel_closure_b, c);
}
#[cfg(feature = "ascent-parallel")]
ascent::ascent_par! {
    struct AmbientAscentProg; relation proc(Proc); #[ds(crate ::eqrel)] relation
    eq_proc(Proc, Proc); #[ds(crate ::dual_indexed)] relation rw_proc(Proc, Proc);
    relation name(Name); #[ds(crate ::eqrel)] relation eq_name(Name, Name); #[ds(crate
    ::dual_indexed)] relation rw_name(Name, Name); relation step_term(Proc); #[ds(crate
    ::dual_indexed)] relation ppar_contains(Proc, Proc); proc(sub.clone()) <- - proc(t),
    for sub in { std::thread_local! { static POOL_PROC_PROC : std::cell::Cell < Vec <
    Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_PROC
    .with(| p | p.take()); buf.clear(); match t { Proc::PIn(_, f1) => { buf.push(f1
    .as_ref().clone()); }, Proc::POut(_, f1) => { buf.push(f1.as_ref().clone()); },
    Proc::POpen(_, f1) => { buf.push(f1.as_ref().clone()); }, Proc::PAmb(_, f1) => { buf
    .push(f1.as_ref().clone()); }, Proc::PNew(scope) => { buf.push(scope.inner()
    .unsafe_body.as_ref().clone()); }, Proc::ApplyProc(lam, arg) => { buf.push(lam
    .as_ref().clone()); buf.push(arg.as_ref().clone()); }, Proc::MApplyProc(lam, args) =>
    { buf.push(lam.as_ref().clone()); buf.extend(args.iter().cloned()); },
    Proc::LamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::MLamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::LamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, Proc::MLamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(); name(sub
    .clone()) <- - proc(t), for sub in { std::thread_local! { static POOL_PROC_NAME :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_NAME.with(| p | p.take()); buf.clear(); match t { Proc::PIn(f0,
    _) => { buf.push(f0.as_ref().clone()); }, Proc::POut(f0, _) => { buf.push(f0.as_ref()
    .clone()); }, Proc::POpen(f0, _) => { buf.push(f0.as_ref().clone()); },
    Proc::PAmb(f0, _) => { buf.push(f0.as_ref().clone()); }, Proc::ApplyName(_, arg) => {
    buf.push(arg.as_ref().clone()); }, Proc::MApplyName(_, args) => { buf.extend(args
    .iter().cloned()); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_NAME.with(| p | p.set(buf)); iter_buf } .into_iter(); name(sub.clone()) <-
    - name(t), for sub in { std::thread_local! { static POOL_NAME_NAME : std::cell::Cell
    < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_NAME_NAME.with(| p | p.take()); buf.clear(); match t { Name::ApplyProc(lam, _)
    => { buf.push(lam.as_ref().clone()); }, Name::MApplyProc(lam, _) => { buf.push(lam
    .as_ref().clone()); }, Name::LamProc(scope) => { buf.push(scope.inner().unsafe_body
    .as_ref().clone()); }, Name::MLamProc(scope) => { buf.push(scope.inner().unsafe_body
    .as_ref().clone()); }, Name::ApplyName(lam, arg) => { buf.push(lam.as_ref().clone());
    buf.push(arg.as_ref().clone()); }, Name::MApplyName(lam, args) => { buf.push(lam
    .as_ref().clone()); buf.extend(args.iter().cloned()); }, Name::LamName(scope) => {
    buf.push(scope.inner().unsafe_body.as_ref().clone()); }, Name::MLamName(scope) => {
    buf.push(scope.inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_NAME_NAME.with(| p | p.set(buf)); iter_buf }
    .into_iter(); proc(c1.clone().normalize()) <- - proc(c0), rw_proc(c0, c1), if { use
    std::hash:: { Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); c1
    .hash(& mut __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_EXPAND : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_EXPAND.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }; ppar_contains(parent.clone(), elem.clone()) <- -
    proc(parent), if let Proc::PPar(ref coll_field) = parent, for (elem, _count) in
    coll_field.iter(); proc(elem.clone()) <- - ppar_contains(_parent, elem); rw_proc(t
    .clone(), match t { Proc::ApplyProc(_, arg) => Proc::ApplyProc(Box::new(new_lam
    .clone()), arg.clone()), Proc::MApplyProc(_, args) =>
    Proc::MApplyProc(Box::new(new_lam.clone()), args.clone()), Proc::ApplyName(_, arg) =>
    Proc::ApplyName(Box::new(new_lam.clone()), arg.clone()), Proc::MApplyName(_, args) =>
    Proc::MApplyName(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - proc(t), for lam in { std::thread_local! { static POOL_PROC_CONG_LAM :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyProc(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::ApplyName(lam, _) => { buf.push(lam
    .as_ref().clone()); }, Proc::MApplyName(lam, _) => { buf.push(lam.as_ref().clone());
    }, _ => {}, } let iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_LAM.with(| p |
    p.set(buf)); iter_buf } .into_iter(), rw_proc(lam, new_lam); rw_proc(t.clone(), match
    t { Proc::ApplyProc(lam, _) => Proc::ApplyProc(lam.clone(), Box::new(new_arg
    .clone())), _ => unreachable!(), }) <- - proc(t), for arg in { std::thread_local! {
    static POOL_PROC_CONG_ARG_PROC : std::cell::Cell < Vec < Proc >> = const {
    std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_CONG_ARG_PROC.with(| p
    | p.take()); buf.clear(); match t { Proc::ApplyProc(_, arg) => { buf.push(arg
    .as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_CONG_ARG_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(), rw_proc(arg,
    new_arg); rw_proc(t.clone(), match t { Proc::ApplyName(lam, _) => Proc::ApplyName(lam
    .clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- - proc(t), for arg
    in { std::thread_local! { static POOL_PROC_CONG_ARG_NAME : std::cell::Cell < Vec <
    Name >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_CONG_ARG_NAME.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyName(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_ARG_NAME.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_name(arg, new_arg); name(c1.clone().normalize()) <- -
    name(c0), rw_name(c0, c1), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); c1.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_EXPAND : std::cell::RefCell <
    (u64, std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_EXPAND.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }; rw_name(t
    .clone(), match t { Name::ApplyName(_, arg) => Name::ApplyName(Box::new(new_lam
    .clone()), arg.clone()), Name::MApplyName(_, args) =>
    Name::MApplyName(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - name(t), for lam in { std::thread_local! { static POOL_NAME_CONG_LAM :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_NAME_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Name::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Name::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_NAME_CONG_LAM.with(| p | p.set(buf)); iter_buf } .into_iter(),
    rw_name(lam, new_lam); rw_name(t.clone(), match t { Name::ApplyName(lam, _) =>
    Name::ApplyName(lam.clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- -
    name(t), for arg in { std::thread_local! { static POOL_NAME_CONG_ARG_NAME :
    std::cell::Cell < Vec < Name >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_NAME_CONG_ARG_NAME.with(| p | p.take()); buf.clear(); match t {
    Name::ApplyName(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_NAME_CONG_ARG_NAME.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_name(arg, new_arg); eq_proc(t.clone(), t.clone()) <- -
    proc(t); eq_name(t.clone(), t.clone()) <- - name(t); eq_proc(s.clone(), t.clone()) <-
    - proc(s), proc(t), if std::mem::discriminant(s) == std::mem::discriminant(t), if
    matches!(s, Proc::PIn(..) | Proc::POut(..) | Proc::POpen(..) | Proc::PAmb(..)), for
    (s_f0, s_f1, t_f0, t_f1) in { std::thread_local! { static POOL_PROC_EQ_CONG_0 :
    std::cell::Cell < Vec < (Name, Proc, Name, Proc) >> = const {
    std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_EQ_CONG_0.with(| p | p
    .take()); buf.clear(); match (s, t) { (Proc::PIn(sf0, sf1), Proc::PIn(tf0, tf1)) => {
    buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1
    .as_ref().clone())); }, (Proc::POut(sf0, sf1), Proc::POut(tf0, tf1)) => { buf
    .push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, (Proc::POpen(sf0, sf1), Proc::POpen(tf0, tf1)) => { buf.push((sf0
    .as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, (Proc::PAmb(sf0, sf1), Proc::PAmb(tf0, tf1)) => { buf.push((sf0
    .as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref()
    .clone())); }, _ => {}, } let iter_buf = std::mem::take(& mut buf);
    POOL_PROC_EQ_CONG_0.with(| p | p.set(buf)); iter_buf } .into_iter(),
    eq_name(__eqcong_s_f0, __eqcong_t_f0), if s_f0 == __eqcong_s_f0.clone(), if t_f0 ==
    __eqcong_t_f0.clone(), eq_proc(__eqcong_s_f1, __eqcong_t_f1), if s_f1 ==
    __eqcong_s_f1.clone(), if t_f1 == __eqcong_t_f1.clone(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref
    s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed =
    s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PPar(ref
    s_f0) = s, for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PNew(ref s_f0_e0_f0)
    = s_f0_e0, let s_f0_e0_f0_binder = s_f0_e0_f0.unsafe_pattern().clone(), let
    s_f0_e0_f0_body_boxed = s_f0_e0_f0.unsafe_body(), let s_f0_e0_f0_body = & * *
    s_f0_e0_f0_body_boxed, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag }, if s_f0_rest.clone().clone().iter().all(| (elem, _) | !
    mettail_runtime::BoundTerm::free_vars(elem).contains(& s_f0_e0_f0_binder.0.clone())),
    if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_e0_f0_binder.clone()
    .clone(), Box::new(Proc::PPar({ let mut bag = (s_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag, (s_f0_e0_f0_body.clone()).clone()); bag })))))
    .normalize(); eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let
    Proc::PNew(ref s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let
    s_f0_body_boxed = s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let
    Proc::PPar(ref s_f0_body_f0) = s_f0_body, for (s_f0_body_f0_e0, _count_0) in
    s_f0_body_f0.iter(), let s_f0_body_f0_rest = { let mut bag = s_f0_body_f0.clone();
    bag.remove(& s_f0_body_f0_e0); bag }, if s_f0_body_f0_rest.clone().clone().iter()
    .all(| (elem, _) | ! mettail_runtime::BoundTerm::free_vars(elem).contains(&
    s_f0_binder.0.clone())), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PPar({ let mut bag = (s_f0_body_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag,
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone().clone(),
    Box::new((s_f0_body_f0_e0.clone()).clone())))); bag })).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PIn(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PIn(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PIn(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PIn(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POut(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POut(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POut(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POut(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POpen(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POpen(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POpen(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POpen(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PAmb(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PAmb(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PAmb(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PAmb(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize();
    rw_proc(s_orig.clone(), t) <- - eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig =
    __eqrel_s_orig.clone(), let s = __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s,
    for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PAmb(ref s_f0_e0_f0, ref
    s_f0_e0_f1) = s_f0_e0, let s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref
    = & * * s_f0_e0_f1, if let Proc::PPar(ref s_f0_e0_f1_deref_f0) = s_f0_e0_f1_deref,
    for (s_f0_e0_f1_deref_f0_e0, _count_1) in s_f0_e0_f1_deref_f0.iter(), if let
    Proc::PIn(ref s_f0_e0_f1_deref_f0_e0_f0, ref s_f0_e0_f1_deref_f0_e0_f1) =
    s_f0_e0_f1_deref_f0_e0, let s_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f0, let s_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f1, let s_f0_e0_f1_deref_f0_rest = { let mut bag =
    s_f0_e0_f1_deref_f0.clone(); bag.remove(& s_f0_e0_f1_deref_f0_e0); bag }, for
    (s_f0_e1, _count_2) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_e0_f1_deref_f0_e0_f0_deref.clone() ==
    __eqpat_a_M.clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_M.clone(), let
    s_f0_e1_f1_deref = & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone();
    bag.remove(& s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_e0_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = mettail_runtime::HashBag::new();
    Proc::insert_into_ppar(& mut bag, Proc::PAmb(Box::new((s_f0_e0_f0_deref.clone())
    .clone()), Box::new(Proc::PPar({ let mut bag = (s_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref_f0_e0_f1_deref.clone())
    .clone()); bag })))); Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone())
    .clone()); bag })))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PAmb(ref s_f0, ref s_f1) = s, let s_f0_deref = & * *
    s_f0, let s_f1_deref = & * * s_f1, if let Proc::PPar(ref s_f1_deref_f0) = s_f1_deref,
    for (s_f1_deref_f0_e0, _count_0) in s_f1_deref_f0.iter(), if let Proc::PAmb(ref
    s_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1) = s_f1_deref_f0_e0, let
    s_f1_deref_f0_e0_f0_deref = & * * s_f1_deref_f0_e0_f0, let s_f1_deref_f0_e0_f1_deref
    = & * * s_f1_deref_f0_e0_f1, if let Proc::PPar(ref s_f1_deref_f0_e0_f1_deref_f0) =
    s_f1_deref_f0_e0_f1_deref, for (s_f1_deref_f0_e0_f1_deref_f0_e0, _count_1) in
    s_f1_deref_f0_e0_f1_deref_f0.iter(), if let Proc::POut(ref
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1_deref_f0_e0_f1) =
    s_f1_deref_f0_e0_f1_deref_f0_e0, let s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_deref
    .clone() == __eqpat_a_M.clone(), if s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref.clone()
    == __eqpat_b_M.clone(), let s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f1, let s_f1_deref_f0_e0_f1_deref_f0_rest = { let mut
    bag = s_f1_deref_f0_e0_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0_f1_deref_f0_e0); bag }, for (s_f1_deref_f0_e1, _count_2) in
    s_f1_deref_f0.iter(), if & s_f1_deref_f0_e1 != & s_f1_deref_f0_e0, let
    s_f1_deref_f0_rest = { let mut bag = s_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0); bag.remove(& s_f1_deref_f0_e1); bag }, if { use std::hash:: {
    Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f1_deref_f0_rest
    .clone()).clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = (s_f1_deref_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref
    .clone()).clone()); bag })))); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_deref.clone()).clone()), Box::new((s_f1_deref_f0_e1
    .clone()).clone()))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s, for (s_f0_e0, _count_0) in s_f0
    .iter(), if let Proc::POpen(ref s_f0_e0_f0, ref s_f0_e0_f1) = s_f0_e0, let
    s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref = & * * s_f0_e0_f1, for
    (s_f0_e1, _count_1) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_N, __eqpat_b_N), if s_f0_e0_f0_deref.clone() == __eqpat_a_N
    .clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_N.clone(), let s_f0_e1_f1_deref =
    & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash, Hasher }; let
    mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref.clone()).clone());
    Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone()).clone()); bag }))
    .normalize(); rw_proc(parent.clone(), result) <- - proc(parent), if let
    Proc::PPar(ref bag) = parent, for (elem, _count) in bag.iter(), rw_proc(elem.clone(),
    elem_rewritten), let result = Proc::PPar({ let mut new_bag = bag.clone(); new_bag
    .remove(elem); Proc::insert_into_ppar(& mut new_bag, elem_rewritten.clone()); new_bag
    }); rw_proc(lhs.clone(), rhs) <- - proc(lhs), if let Proc::PNew(ref scope) = lhs, let
    binder = scope.unsafe_pattern().clone(), let body = scope.unsafe_body(), rw_proc((* *
    body).clone(), body_rewritten), let rhs =
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(binder.clone(),
    Box::new(body_rewritten.clone()))); rw_proc(lhs.clone(), match (lhs, vi) {
    (Proc::PAmb(x0, _), 0usize) => Proc::PAmb(x0.clone(), Box::new(t.clone())), _ =>
    unreachable!(), }) <- - proc(lhs), if matches!(lhs, Proc::PAmb(..)), for (field_val,
    vi) in { std::thread_local! { static POOL_PROC_SCONG_PROC : std::cell::Cell < Vec <
    (Proc, usize) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_SCONG_PROC.with(| p | p.take()); buf.clear(); match lhs { Proc::PAmb(_, x1)
    => { buf.push(((* * x1).clone(), 0usize)); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_PROC_SCONG_PROC.with(| p | p.set(buf)); iter_buf }
    .into_iter(), rw_proc(field_val, t); rw_proc(__eqrel_closure_a.clone(), c.clone()) <-
    - eq_proc(__eqrel_a, __eqrel_b), let __eqrel_closure_a = __eqrel_a.clone(), let
    __eqrel_closure_b = __eqrel_b.clone(), rw_proc(__eqrel_closure_b, c);
    rw_name(__eqrel_closure_a.clone(), c.clone()) <- - eq_name(__eqrel_a, __eqrel_b), let
    __eqrel_closure_a = __eqrel_a.clone(), let __eqrel_closure_b = __eqrel_b.clone(),
    rw_name(__eqrel_closure_b, c);
}
#[cfg(not(feature = "ascent-parallel"))]
ascent::ascent! {
    struct AmbientAscentProgCore; relation proc(Proc); #[ds(crate ::eqrel)] relation
    eq_proc(Proc, Proc); #[ds(crate ::dual_indexed)] relation rw_proc(Proc, Proc);
    relation name(Name); #[ds(crate ::eqrel)] relation eq_name(Name, Name); #[ds(crate
    ::dual_indexed)] relation rw_name(Name, Name); relation step_term(Proc); #[ds(crate
    ::dual_indexed)] relation ppar_contains(Proc, Proc); proc(sub.clone()) <- - proc(t),
    for sub in { std::thread_local! { static POOL_PROC_PROC : std::cell::Cell < Vec <
    Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_PROC
    .with(| p | p.take()); buf.clear(); match t { Proc::PIn(_, f1) => { buf.push(f1
    .as_ref().clone()); }, Proc::POut(_, f1) => { buf.push(f1.as_ref().clone()); },
    Proc::POpen(_, f1) => { buf.push(f1.as_ref().clone()); }, Proc::PAmb(_, f1) => { buf
    .push(f1.as_ref().clone()); }, Proc::PNew(scope) => { buf.push(scope.inner()
    .unsafe_body.as_ref().clone()); }, Proc::ApplyProc(lam, arg) => { buf.push(lam
    .as_ref().clone()); buf.push(arg.as_ref().clone()); }, Proc::MApplyProc(lam, args) =>
    { buf.push(lam.as_ref().clone()); buf.extend(args.iter().cloned()); },
    Proc::LamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::MLamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::LamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, Proc::MLamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(); proc(c1
    .clone().normalize()) <- - proc(c0), rw_proc(c0, c1), if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); c1.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_EXPAND : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_EXPAND.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }; ppar_contains(parent.clone(), elem.clone()) <- -
    proc(parent), if let Proc::PPar(ref coll_field) = parent, for (elem, _count) in
    coll_field.iter(); proc(elem.clone()) <- - ppar_contains(_parent, elem); rw_proc(t
    .clone(), match t { Proc::ApplyProc(_, arg) => Proc::ApplyProc(Box::new(new_lam
    .clone()), arg.clone()), Proc::MApplyProc(_, args) =>
    Proc::MApplyProc(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - proc(t), for lam in { std::thread_local! { static POOL_PROC_CONG_LAM :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyProc(lam,
    _) => { buf.push(lam.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_CONG_LAM.with(| p | p.set(buf)); iter_buf } .into_iter(),
    rw_proc(lam, new_lam); rw_proc(t.clone(), match t { Proc::ApplyProc(lam, _) =>
    Proc::ApplyProc(lam.clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- -
    proc(t), for arg in { std::thread_local! { static POOL_PROC_CONG_ARG_PROC :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_ARG_PROC.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_ARG_PROC.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_proc(arg, new_arg); eq_proc(t.clone(), t.clone()) <- -
    proc(t); eq_proc(s.clone(), t.clone()) <- - proc(s), proc(t), if
    std::mem::discriminant(s) == std::mem::discriminant(t), if matches!(s, Proc::PIn(..)
    | Proc::POut(..) | Proc::POpen(..) | Proc::PAmb(..)), for (s_f0, s_f1, t_f0, t_f1) in
    { std::thread_local! { static POOL_PROC_EQ_CONG_0 : std::cell::Cell < Vec < (Name,
    Proc, Name, Proc) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_EQ_CONG_0.with(| p | p.take()); buf.clear(); match (s, t) { (Proc::PIn(sf0,
    sf1), Proc::PIn(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(),
    tf0.as_ref().clone(), tf1.as_ref().clone())); }, (Proc::POut(sf0, sf1),
    Proc::POut(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0
    .as_ref().clone(), tf1.as_ref().clone())); }, (Proc::POpen(sf0, sf1),
    Proc::POpen(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0
    .as_ref().clone(), tf1.as_ref().clone())); }, (Proc::PAmb(sf0, sf1), Proc::PAmb(tf0,
    tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref()
    .clone(), tf1.as_ref().clone())); }, _ => {}, } let iter_buf = std::mem::take(& mut
    buf); POOL_PROC_EQ_CONG_0.with(| p | p.set(buf)); iter_buf } .into_iter(),
    eq_name(__eqcong_s_f0, __eqcong_t_f0), if s_f0 == __eqcong_s_f0.clone(), if t_f0 ==
    __eqcong_t_f0.clone(), eq_proc(__eqcong_s_f1, __eqcong_t_f1), if s_f1 ==
    __eqcong_s_f1.clone(), if t_f1 == __eqcong_t_f1.clone(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref
    s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed =
    s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PPar(ref
    s_f0) = s, for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PNew(ref s_f0_e0_f0)
    = s_f0_e0, let s_f0_e0_f0_binder = s_f0_e0_f0.unsafe_pattern().clone(), let
    s_f0_e0_f0_body_boxed = s_f0_e0_f0.unsafe_body(), let s_f0_e0_f0_body = & * *
    s_f0_e0_f0_body_boxed, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag }, if s_f0_rest.clone().clone().iter().all(| (elem, _) | !
    mettail_runtime::BoundTerm::free_vars(elem).contains(& s_f0_e0_f0_binder.0.clone())),
    if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_e0_f0_binder.clone()
    .clone(), Box::new(Proc::PPar({ let mut bag = (s_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag, (s_f0_e0_f0_body.clone()).clone()); bag })))))
    .normalize(); eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let
    Proc::PNew(ref s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let
    s_f0_body_boxed = s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let
    Proc::PPar(ref s_f0_body_f0) = s_f0_body, for (s_f0_body_f0_e0, _count_0) in
    s_f0_body_f0.iter(), let s_f0_body_f0_rest = { let mut bag = s_f0_body_f0.clone();
    bag.remove(& s_f0_body_f0_e0); bag }, if s_f0_body_f0_rest.clone().clone().iter()
    .all(| (elem, _) | ! mettail_runtime::BoundTerm::free_vars(elem).contains(&
    s_f0_binder.0.clone())), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PPar({ let mut bag = (s_f0_body_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag,
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone().clone(),
    Box::new((s_f0_body_f0_e0.clone()).clone())))); bag })).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PIn(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PIn(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PIn(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PIn(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POut(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POut(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POut(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POut(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POpen(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POpen(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POpen(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POpen(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PAmb(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PAmb(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PAmb(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PAmb(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize();
    rw_proc(s_orig.clone(), t) <- - eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig =
    __eqrel_s_orig.clone(), let s = __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s,
    for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PAmb(ref s_f0_e0_f0, ref
    s_f0_e0_f1) = s_f0_e0, let s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref
    = & * * s_f0_e0_f1, if let Proc::PPar(ref s_f0_e0_f1_deref_f0) = s_f0_e0_f1_deref,
    for (s_f0_e0_f1_deref_f0_e0, _count_1) in s_f0_e0_f1_deref_f0.iter(), if let
    Proc::PIn(ref s_f0_e0_f1_deref_f0_e0_f0, ref s_f0_e0_f1_deref_f0_e0_f1) =
    s_f0_e0_f1_deref_f0_e0, let s_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f0, let s_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f1, let s_f0_e0_f1_deref_f0_rest = { let mut bag =
    s_f0_e0_f1_deref_f0.clone(); bag.remove(& s_f0_e0_f1_deref_f0_e0); bag }, for
    (s_f0_e1, _count_2) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_e0_f1_deref_f0_e0_f0_deref.clone() ==
    __eqpat_a_M.clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_M.clone(), let
    s_f0_e1_f1_deref = & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone();
    bag.remove(& s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_e0_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = mettail_runtime::HashBag::new();
    Proc::insert_into_ppar(& mut bag, Proc::PAmb(Box::new((s_f0_e0_f0_deref.clone())
    .clone()), Box::new(Proc::PPar({ let mut bag = (s_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref_f0_e0_f1_deref.clone())
    .clone()); bag })))); Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone())
    .clone()); bag })))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PAmb(ref s_f0, ref s_f1) = s, let s_f0_deref = & * *
    s_f0, let s_f1_deref = & * * s_f1, if let Proc::PPar(ref s_f1_deref_f0) = s_f1_deref,
    for (s_f1_deref_f0_e0, _count_0) in s_f1_deref_f0.iter(), if let Proc::PAmb(ref
    s_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1) = s_f1_deref_f0_e0, let
    s_f1_deref_f0_e0_f0_deref = & * * s_f1_deref_f0_e0_f0, let s_f1_deref_f0_e0_f1_deref
    = & * * s_f1_deref_f0_e0_f1, if let Proc::PPar(ref s_f1_deref_f0_e0_f1_deref_f0) =
    s_f1_deref_f0_e0_f1_deref, for (s_f1_deref_f0_e0_f1_deref_f0_e0, _count_1) in
    s_f1_deref_f0_e0_f1_deref_f0.iter(), if let Proc::POut(ref
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1_deref_f0_e0_f1) =
    s_f1_deref_f0_e0_f1_deref_f0_e0, let s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_deref
    .clone() == __eqpat_a_M.clone(), if s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref.clone()
    == __eqpat_b_M.clone(), let s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f1, let s_f1_deref_f0_e0_f1_deref_f0_rest = { let mut
    bag = s_f1_deref_f0_e0_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0_f1_deref_f0_e0); bag }, for (s_f1_deref_f0_e1, _count_2) in
    s_f1_deref_f0.iter(), if & s_f1_deref_f0_e1 != & s_f1_deref_f0_e0, let
    s_f1_deref_f0_rest = { let mut bag = s_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0); bag.remove(& s_f1_deref_f0_e1); bag }, if { use std::hash:: {
    Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f1_deref_f0_rest
    .clone()).clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = (s_f1_deref_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref
    .clone()).clone()); bag })))); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_deref.clone()).clone()), Box::new((s_f1_deref_f0_e1
    .clone()).clone()))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s, for (s_f0_e0, _count_0) in s_f0
    .iter(), if let Proc::POpen(ref s_f0_e0_f0, ref s_f0_e0_f1) = s_f0_e0, let
    s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref = & * * s_f0_e0_f1, for
    (s_f0_e1, _count_1) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_N, __eqpat_b_N), if s_f0_e0_f0_deref.clone() == __eqpat_a_N
    .clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_N.clone(), let s_f0_e1_f1_deref =
    & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash, Hasher }; let
    mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref.clone()).clone());
    Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone()).clone()); bag }))
    .normalize(); rw_proc(parent.clone(), result) <- - proc(parent), if let
    Proc::PPar(ref bag) = parent, for (elem, _count) in bag.iter(), rw_proc(elem.clone(),
    elem_rewritten), let result = Proc::PPar({ let mut new_bag = bag.clone(); new_bag
    .remove(elem); Proc::insert_into_ppar(& mut new_bag, elem_rewritten.clone()); new_bag
    }); rw_proc(lhs.clone(), rhs) <- - proc(lhs), if let Proc::PNew(ref scope) = lhs, let
    binder = scope.unsafe_pattern().clone(), let body = scope.unsafe_body(), rw_proc((* *
    body).clone(), body_rewritten), let rhs =
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(binder.clone(),
    Box::new(body_rewritten.clone()))); rw_proc(lhs.clone(), match (lhs, vi) {
    (Proc::PAmb(x0, _), 0usize) => Proc::PAmb(x0.clone(), Box::new(t.clone())), _ =>
    unreachable!(), }) <- - proc(lhs), if matches!(lhs, Proc::PAmb(..)), for (field_val,
    vi) in { std::thread_local! { static POOL_PROC_SCONG_PROC : std::cell::Cell < Vec <
    (Proc, usize) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_SCONG_PROC.with(| p | p.take()); buf.clear(); match lhs { Proc::PAmb(_, x1)
    => { buf.push(((* * x1).clone(), 0usize)); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_PROC_SCONG_PROC.with(| p | p.set(buf)); iter_buf }
    .into_iter(), rw_proc(field_val, t); rw_proc(__eqrel_closure_a.clone(), c.clone()) <-
    - eq_proc(__eqrel_a, __eqrel_b), let __eqrel_closure_a = __eqrel_a.clone(), let
    __eqrel_closure_b = __eqrel_b.clone(), rw_proc(__eqrel_closure_b, c);
}
#[cfg(feature = "ascent-parallel")]
ascent::ascent_par! {
    struct AmbientAscentProgCore; relation proc(Proc); #[ds(crate ::eqrel)] relation
    eq_proc(Proc, Proc); #[ds(crate ::dual_indexed)] relation rw_proc(Proc, Proc);
    relation name(Name); #[ds(crate ::eqrel)] relation eq_name(Name, Name); #[ds(crate
    ::dual_indexed)] relation rw_name(Name, Name); relation step_term(Proc); #[ds(crate
    ::dual_indexed)] relation ppar_contains(Proc, Proc); proc(sub.clone()) <- - proc(t),
    for sub in { std::thread_local! { static POOL_PROC_PROC : std::cell::Cell < Vec <
    Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf = POOL_PROC_PROC
    .with(| p | p.take()); buf.clear(); match t { Proc::PIn(_, f1) => { buf.push(f1
    .as_ref().clone()); }, Proc::POut(_, f1) => { buf.push(f1.as_ref().clone()); },
    Proc::POpen(_, f1) => { buf.push(f1.as_ref().clone()); }, Proc::PAmb(_, f1) => { buf
    .push(f1.as_ref().clone()); }, Proc::PNew(scope) => { buf.push(scope.inner()
    .unsafe_body.as_ref().clone()); }, Proc::ApplyProc(lam, arg) => { buf.push(lam
    .as_ref().clone()); buf.push(arg.as_ref().clone()); }, Proc::MApplyProc(lam, args) =>
    { buf.push(lam.as_ref().clone()); buf.extend(args.iter().cloned()); },
    Proc::LamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::MLamProc(scope) => { buf.push(scope.inner().unsafe_body.as_ref().clone()); },
    Proc::ApplyName(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyName(lam,
    _) => { buf.push(lam.as_ref().clone()); }, Proc::LamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, Proc::MLamName(scope) => { buf.push(scope
    .inner().unsafe_body.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_PROC.with(| p | p.set(buf)); iter_buf } .into_iter(); proc(c1
    .clone().normalize()) <- - proc(c0), rw_proc(c0, c1), if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); c1.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_EXPAND : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_EXPAND.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }; ppar_contains(parent.clone(), elem.clone()) <- -
    proc(parent), if let Proc::PPar(ref coll_field) = parent, for (elem, _count) in
    coll_field.iter(); proc(elem.clone()) <- - ppar_contains(_parent, elem); rw_proc(t
    .clone(), match t { Proc::ApplyProc(_, arg) => Proc::ApplyProc(Box::new(new_lam
    .clone()), arg.clone()), Proc::MApplyProc(_, args) =>
    Proc::MApplyProc(Box::new(new_lam.clone()), args.clone()), _ => unreachable!(), }) <-
    - proc(t), for lam in { std::thread_local! { static POOL_PROC_CONG_LAM :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_LAM.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(lam, _) => { buf.push(lam.as_ref().clone()); }, Proc::MApplyProc(lam,
    _) => { buf.push(lam.as_ref().clone()); }, _ => {}, } let iter_buf = std::mem::take(&
    mut buf); POOL_PROC_CONG_LAM.with(| p | p.set(buf)); iter_buf } .into_iter(),
    rw_proc(lam, new_lam); rw_proc(t.clone(), match t { Proc::ApplyProc(lam, _) =>
    Proc::ApplyProc(lam.clone(), Box::new(new_arg.clone())), _ => unreachable!(), }) <- -
    proc(t), for arg in { std::thread_local! { static POOL_PROC_CONG_ARG_PROC :
    std::cell::Cell < Vec < Proc >> = const { std::cell::Cell::new(Vec::new()) }; } let
    mut buf = POOL_PROC_CONG_ARG_PROC.with(| p | p.take()); buf.clear(); match t {
    Proc::ApplyProc(_, arg) => { buf.push(arg.as_ref().clone()); }, _ => {}, } let
    iter_buf = std::mem::take(& mut buf); POOL_PROC_CONG_ARG_PROC.with(| p | p.set(buf));
    iter_buf } .into_iter(), rw_proc(arg, new_arg); eq_proc(t.clone(), t.clone()) <- -
    proc(t); eq_proc(s.clone(), t.clone()) <- - proc(s), proc(t), if
    std::mem::discriminant(s) == std::mem::discriminant(t), if matches!(s, Proc::PIn(..)
    | Proc::POut(..) | Proc::POpen(..) | Proc::PAmb(..)), for (s_f0, s_f1, t_f0, t_f1) in
    { std::thread_local! { static POOL_PROC_EQ_CONG_0 : std::cell::Cell < Vec < (Name,
    Proc, Name, Proc) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_EQ_CONG_0.with(| p | p.take()); buf.clear(); match (s, t) { (Proc::PIn(sf0,
    sf1), Proc::PIn(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(),
    tf0.as_ref().clone(), tf1.as_ref().clone())); }, (Proc::POut(sf0, sf1),
    Proc::POut(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0
    .as_ref().clone(), tf1.as_ref().clone())); }, (Proc::POpen(sf0, sf1),
    Proc::POpen(tf0, tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0
    .as_ref().clone(), tf1.as_ref().clone())); }, (Proc::PAmb(sf0, sf1), Proc::PAmb(tf0,
    tf1)) => { buf.push((sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref()
    .clone(), tf1.as_ref().clone())); }, _ => {}, } let iter_buf = std::mem::take(& mut
    buf); POOL_PROC_EQ_CONG_0.with(| p | p.set(buf)); iter_buf } .into_iter(),
    eq_name(__eqcong_s_f0, __eqcong_t_f0), if s_f0 == __eqcong_s_f0.clone(), if t_f0 ==
    __eqcong_t_f0.clone(), eq_proc(__eqcong_s_f1, __eqcong_t_f1), if s_f1 ==
    __eqcong_s_f1.clone(), if t_f1 == __eqcong_t_f1.clone(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref
    s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed =
    s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PNew(ref
    s_f0_body_f0) = s_f0_body, let s_f0_body_f0_binder = s_f0_body_f0.unsafe_pattern()
    .clone(), let s_f0_body_f0_body_boxed = s_f0_body_f0.unsafe_body(), let
    s_f0_body_f0_body = & * * s_f0_body_f0_body_boxed, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_body_f0_binder.clone()
    .clone(), Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder
    .clone().clone(), Box::new((s_f0_body_f0_body.clone()).clone()))))))).normalize();
    eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PPar(ref
    s_f0) = s, for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PNew(ref s_f0_e0_f0)
    = s_f0_e0, let s_f0_e0_f0_binder = s_f0_e0_f0.unsafe_pattern().clone(), let
    s_f0_e0_f0_body_boxed = s_f0_e0_f0.unsafe_body(), let s_f0_e0_f0_body = & * *
    s_f0_e0_f0_body_boxed, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag }, if s_f0_rest.clone().clone().iter().all(| (elem, _) | !
    mettail_runtime::BoundTerm::free_vars(elem).contains(& s_f0_e0_f0_binder.0.clone())),
    if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_e0_f0_binder.clone()
    .clone(), Box::new(Proc::PPar({ let mut bag = (s_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag, (s_f0_e0_f0_body.clone()).clone()); bag })))))
    .normalize(); eq_proc(s.clone(), t.clone()), proc(t.clone()) <- - proc(s), if let
    Proc::PNew(ref s_f0) = s, let s_f0_binder = s_f0.unsafe_pattern().clone(), let
    s_f0_body_boxed = s_f0.unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let
    Proc::PPar(ref s_f0_body_f0) = s_f0_body, for (s_f0_body_f0_e0, _count_0) in
    s_f0_body_f0.iter(), let s_f0_body_f0_rest = { let mut bag = s_f0_body_f0.clone();
    bag.remove(& s_f0_body_f0_e0); bag }, if s_f0_body_f0_rest.clone().clone().iter()
    .all(| (elem, _) | ! mettail_runtime::BoundTerm::free_vars(elem).contains(&
    s_f0_binder.0.clone())), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PPar({ let mut bag = (s_f0_body_f0_rest.clone()).clone();
    Proc::insert_into_ppar(& mut bag,
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone().clone(),
    Box::new((s_f0_body_f0_e0.clone()).clone())))); bag })).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PIn(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PIn(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PIn(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PIn(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POut(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POut(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POut(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POut(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::POpen(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::POpen(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::POpen(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::POpen(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize(); eq_proc(s
    .clone(), t.clone()), proc(t.clone()) <- - proc(s), if let Proc::PAmb(ref s_f0, ref
    s_f1) = s, let s_f0_deref = & * * s_f0, let s_f1_deref = & * * s_f1, if let
    Proc::PNew(ref s_f1_deref_f0) = s_f1_deref, let s_f1_deref_f0_binder = s_f1_deref_f0
    .unsafe_pattern().clone(), let s_f1_deref_f0_body_boxed = s_f1_deref_f0
    .unsafe_body(), let s_f1_deref_f0_body = & * * s_f1_deref_f0_body_boxed, if !
    mettail_runtime::BoundTerm::free_vars(& s_f1_deref_f0_body.clone()).contains(&
    s_f1_deref_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut
    __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t =
    (Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f1_deref_f0_binder.clone()
    .clone(), Box::new(Proc::PAmb(Box::new((s_f0_deref.clone()).clone()),
    Box::new((s_f1_deref_f0_body.clone()).clone())))))).normalize(); eq_proc(s.clone(), t
    .clone()), proc(t.clone()) <- - proc(s), if let Proc::PNew(ref s_f0) = s, let
    s_f0_binder = s_f0.unsafe_pattern().clone(), let s_f0_body_boxed = s_f0
    .unsafe_body(), let s_f0_body = & * * s_f0_body_boxed, if let Proc::PAmb(ref
    s_f0_body_f0, ref s_f0_body_f1) = s_f0_body, let s_f0_body_f0_deref = & * *
    s_f0_body_f0, let s_f0_body_f1_deref = & * * s_f0_body_f1, if !
    mettail_runtime::BoundTerm::free_vars(& s_f0_body_f1_deref.clone()).contains(&
    s_f0_binder.0.clone()), if { use std::hash:: { Hash, Hasher }; let mut __bcg05_h =
    std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let __bcg05_hash =
    __bcg05_h.finish(); thread_local! { static __BCG05_RULE : std::cell::RefCell < (u64,
    std::collections::HashSet < u64 >) > = std::cell::RefCell::new((0,
    std::collections::HashSet::new())); } let __epoch = mettail_runtime::bcg05_epoch();
    __BCG05_RULE.with(| s | { let mut guard = s.borrow_mut(); if guard.0 != __epoch {
    guard.0 = __epoch; guard.1.clear(); } guard.1.insert(__bcg05_hash) }) }, let t =
    (Proc::PAmb(Box::new((s_f0_body_f0_deref.clone()).clone()),
    Box::new(Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(s_f0_binder.clone()
    .clone(), Box::new((s_f0_body_f1_deref.clone()).clone())))))).normalize();
    rw_proc(s_orig.clone(), t) <- - eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig =
    __eqrel_s_orig.clone(), let s = __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s,
    for (s_f0_e0, _count_0) in s_f0.iter(), if let Proc::PAmb(ref s_f0_e0_f0, ref
    s_f0_e0_f1) = s_f0_e0, let s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref
    = & * * s_f0_e0_f1, if let Proc::PPar(ref s_f0_e0_f1_deref_f0) = s_f0_e0_f1_deref,
    for (s_f0_e0_f1_deref_f0_e0, _count_1) in s_f0_e0_f1_deref_f0.iter(), if let
    Proc::PIn(ref s_f0_e0_f1_deref_f0_e0_f0, ref s_f0_e0_f1_deref_f0_e0_f1) =
    s_f0_e0_f1_deref_f0_e0, let s_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f0, let s_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f0_e0_f1_deref_f0_e0_f1, let s_f0_e0_f1_deref_f0_rest = { let mut bag =
    s_f0_e0_f1_deref_f0.clone(); bag.remove(& s_f0_e0_f1_deref_f0_e0); bag }, for
    (s_f0_e1, _count_2) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_e0_f1_deref_f0_e0_f0_deref.clone() ==
    __eqpat_a_M.clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_M.clone(), let
    s_f0_e1_f1_deref = & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone();
    bag.remove(& s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash,
    Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_e0_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = mettail_runtime::HashBag::new();
    Proc::insert_into_ppar(& mut bag, Proc::PAmb(Box::new((s_f0_e0_f0_deref.clone())
    .clone()), Box::new(Proc::PPar({ let mut bag = (s_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref_f0_e0_f1_deref.clone())
    .clone()); bag })))); Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone())
    .clone()); bag })))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PAmb(ref s_f0, ref s_f1) = s, let s_f0_deref = & * *
    s_f0, let s_f1_deref = & * * s_f1, if let Proc::PPar(ref s_f1_deref_f0) = s_f1_deref,
    for (s_f1_deref_f0_e0, _count_0) in s_f1_deref_f0.iter(), if let Proc::PAmb(ref
    s_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1) = s_f1_deref_f0_e0, let
    s_f1_deref_f0_e0_f0_deref = & * * s_f1_deref_f0_e0_f0, let s_f1_deref_f0_e0_f1_deref
    = & * * s_f1_deref_f0_e0_f1, if let Proc::PPar(ref s_f1_deref_f0_e0_f1_deref_f0) =
    s_f1_deref_f0_e0_f1_deref, for (s_f1_deref_f0_e0_f1_deref_f0_e0, _count_1) in
    s_f1_deref_f0_e0_f1_deref_f0.iter(), if let Proc::POut(ref
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, ref s_f1_deref_f0_e0_f1_deref_f0_e0_f1) =
    s_f1_deref_f0_e0_f1_deref_f0_e0, let s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f0, eq_name(__eqpat_a_M, __eqpat_b_M), if s_f0_deref
    .clone() == __eqpat_a_M.clone(), if s_f1_deref_f0_e0_f1_deref_f0_e0_f0_deref.clone()
    == __eqpat_b_M.clone(), let s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref = & * *
    s_f1_deref_f0_e0_f1_deref_f0_e0_f1, let s_f1_deref_f0_e0_f1_deref_f0_rest = { let mut
    bag = s_f1_deref_f0_e0_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0_f1_deref_f0_e0); bag }, for (s_f1_deref_f0_e1, _count_2) in
    s_f1_deref_f0.iter(), if & s_f1_deref_f0_e1 != & s_f1_deref_f0_e0, let
    s_f1_deref_f0_rest = { let mut bag = s_f1_deref_f0.clone(); bag.remove(&
    s_f1_deref_f0_e0); bag.remove(& s_f1_deref_f0_e1); bag }, if { use std::hash:: {
    Hash, Hasher }; let mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut
    __bcg05_h); let __bcg05_hash = __bcg05_h.finish(); thread_local! { static
    __BCG05_RULE : std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f1_deref_f0_rest
    .clone()).clone(); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f1_deref_f0_e0_f0_deref.clone()).clone()),
    Box::new(Proc::PPar({ let mut bag = (s_f1_deref_f0_e0_f1_deref_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f1_deref_f0_e0_f1_deref_f0_e0_f1_deref
    .clone()).clone()); bag })))); Proc::insert_into_ppar(& mut bag,
    Proc::PAmb(Box::new((s_f0_deref.clone()).clone()), Box::new((s_f1_deref_f0_e1
    .clone()).clone()))); bag })).normalize(); rw_proc(s_orig.clone(), t) <- -
    eq_proc(__eqrel_s_orig, __eqrel_s), let s_orig = __eqrel_s_orig.clone(), let s =
    __eqrel_s.clone(), if let Proc::PPar(ref s_f0) = s, for (s_f0_e0, _count_0) in s_f0
    .iter(), if let Proc::POpen(ref s_f0_e0_f0, ref s_f0_e0_f1) = s_f0_e0, let
    s_f0_e0_f0_deref = & * * s_f0_e0_f0, let s_f0_e0_f1_deref = & * * s_f0_e0_f1, for
    (s_f0_e1, _count_1) in s_f0.iter(), if & s_f0_e1 != & s_f0_e0, if let Proc::PAmb(ref
    s_f0_e1_f0, ref s_f0_e1_f1) = s_f0_e1, let s_f0_e1_f0_deref = & * * s_f0_e1_f0,
    eq_name(__eqpat_a_N, __eqpat_b_N), if s_f0_e0_f0_deref.clone() == __eqpat_a_N
    .clone(), if s_f0_e1_f0_deref.clone() == __eqpat_b_N.clone(), let s_f0_e1_f1_deref =
    & * * s_f0_e1_f1, let s_f0_rest = { let mut bag = s_f0.clone(); bag.remove(&
    s_f0_e0); bag.remove(& s_f0_e1); bag }, if { use std::hash:: { Hash, Hasher }; let
    mut __bcg05_h = std::hash::DefaultHasher::new(); s.hash(& mut __bcg05_h); let
    __bcg05_hash = __bcg05_h.finish(); thread_local! { static __BCG05_RULE :
    std::cell::RefCell < (u64, std::collections::HashSet < u64 >) > =
    std::cell::RefCell::new((0, std::collections::HashSet::new())); } let __epoch =
    mettail_runtime::bcg05_epoch(); __BCG05_RULE.with(| s | { let mut guard = s
    .borrow_mut(); if guard.0 != __epoch { guard.0 = __epoch; guard.1.clear(); } guard.1
    .insert(__bcg05_hash) }) }, let t = (Proc::PPar({ let mut bag = (s_f0_rest.clone())
    .clone(); Proc::insert_into_ppar(& mut bag, (s_f0_e0_f1_deref.clone()).clone());
    Proc::insert_into_ppar(& mut bag, (s_f0_e1_f1_deref.clone()).clone()); bag }))
    .normalize(); rw_proc(parent.clone(), result) <- - proc(parent), if let
    Proc::PPar(ref bag) = parent, for (elem, _count) in bag.iter(), rw_proc(elem.clone(),
    elem_rewritten), let result = Proc::PPar({ let mut new_bag = bag.clone(); new_bag
    .remove(elem); Proc::insert_into_ppar(& mut new_bag, elem_rewritten.clone()); new_bag
    }); rw_proc(lhs.clone(), rhs) <- - proc(lhs), if let Proc::PNew(ref scope) = lhs, let
    binder = scope.unsafe_pattern().clone(), let body = scope.unsafe_body(), rw_proc((* *
    body).clone(), body_rewritten), let rhs =
    Proc::PNew(mettail_runtime::Scope::from_parts_unsafe(binder.clone(),
    Box::new(body_rewritten.clone()))); rw_proc(lhs.clone(), match (lhs, vi) {
    (Proc::PAmb(x0, _), 0usize) => Proc::PAmb(x0.clone(), Box::new(t.clone())), _ =>
    unreachable!(), }) <- - proc(lhs), if matches!(lhs, Proc::PAmb(..)), for (field_val,
    vi) in { std::thread_local! { static POOL_PROC_SCONG_PROC : std::cell::Cell < Vec <
    (Proc, usize) >> = const { std::cell::Cell::new(Vec::new()) }; } let mut buf =
    POOL_PROC_SCONG_PROC.with(| p | p.take()); buf.clear(); match lhs { Proc::PAmb(_, x1)
    => { buf.push(((* * x1).clone(), 0usize)); }, _ => {}, } let iter_buf =
    std::mem::take(& mut buf); POOL_PROC_SCONG_PROC.with(| p | p.set(buf)); iter_buf }
    .into_iter(), rw_proc(field_val, t); rw_proc(__eqrel_closure_a.clone(), c.clone()) <-
    - eq_proc(__eqrel_a, __eqrel_b), let __eqrel_closure_a = __eqrel_a.clone(), let
    __eqrel_closure_b = __eqrel_b.clone(), rw_proc(__eqrel_closure_b, c);
}
/// Language implementation struct (multi-category: one parser/relation per type).
pub struct AmbientLanguage;
thread_local! {
    #[doc = r" WFST weights for NFA-ambiguous alternatives, parallel to the `successes`"]
    #[doc = r" vec in `parse_preserving_vars`. Set before `from_alternatives` so it can"]
    #[doc = r" use weights as tiebreaker when multiple alternatives are accepting."]
    static AMBIGUOUS_WEIGHTS : std::cell::Cell < Vec < f64 >> =
    std::cell::Cell::new(Vec::new()); #[doc =
    r" C1: Accumulated weight corrections from semantic disambiguation."] #[doc =
    r" When `from_alternatives` selects a non-weight-best alternative"] #[doc =
    r" (because only it was accepting or because semantic tiebreaking"] #[doc =
    r" overrode the WFST ordering), a `WeightCorrection` is recorded."] #[doc = r""]
    #[doc = r" Drain via `drain_weight_corrections()` after each parse to"] #[doc =
    r" collect feedback for offline weight training."] static WEIGHT_CORRECTIONS :
    std::cell::Cell < Vec < mettail_prattail::wfst::WeightCorrection >> =
    std::cell::Cell::new(Vec::new());
}
impl AmbientLanguage {
    /// A-RT05: Maximum term depth threshold for post-fixpoint convergence check.
    ///
    /// If any term in the fixpoint result exceeds this depth, a warning is
    /// emitted to stderr. This catches pathological grammars where depth-increasing
    /// rules cause unbounded term growth.
    const MAX_FIXPOINT_TERM_DEPTH: u32 = 100;
    /// Parse a term from a string (clears var cache). Tries all category parsers.
    pub fn parse(input: &str) -> Result<AmbientTerm, std::string::String> {
        mettail_runtime::clear_var_cache();
        Self::parse_preserving_vars(input)
    }
    /// Parse without clearing var cache. Tries ALL category parsers (NFA-style).
    /// If exactly 1 succeeds → unambiguous. If N succeed → `Ambiguous(Vec<Inner>)`.
    /// Reports the first parser's error when all fail.
    ///
    /// When the language has non-native categories (e.g. Proc, Name), a lexer probe
    /// classifies the first token: if it's an `Ident`, native-only categories (Float,
    /// Int, Bool, Str) are skipped since identifiers are not native literals. This
    /// reduces 6-way ambiguity to 2-way for bare variables in languages like rhocalc.
    pub fn parse_preserving_vars(
        input: &str,
    ) -> Result<AmbientTerm, std::string::String> {
        let probe_tokens = lex(input).map_err(|e| e.to_string())?;
        let first_tok = probe_tokens.first().map(|(t, _)| t);
        let mut successes = Vec::new();
        let mut success_weights: Vec<f64> = Vec::new();
        let mut first_err = None;
        match Proc::parse(input) {
            Ok(t) => {
                successes.push(AmbientTermInner::Proc(t));
                success_weights
                    .push(
                        NFA_PRIMARY_WEIGHT_PROC
                            .with(|cell| {
                                let w = cell.get();
                                cell.set(0.5);
                                w
                            }),
                    );
                let spilled: Vec<(Proc, usize, f64)> = NFA_PREFIX_SPILL_PROC
                    .with(|cell| cell.take());
                let primary_is_accepting = successes
                    .last()
                    .map_or(false, |s| s.is_accepting());
                if !primary_is_accepting {
                    let primary_w = NFA_PRIMARY_WEIGHT_PROC.with(|cell| cell.get());
                    const REPLAY_WEIGHT_SLACK: f64 = 2.0;
                    let weight_threshold = primary_w + REPLAY_WEIGHT_SLACK;
                    for (alt_prefix, alt_pos, alt_weight) in spilled {
                        if alt_weight > weight_threshold {
                            break;
                        }
                        NFA_FORCED_PREFIX_PROC
                            .with(|cell| {
                                cell.set(Some((alt_prefix, alt_pos, alt_weight)))
                            });
                        if let Ok(alt_term) = Proc::parse(input) {
                            let wrapped = AmbientTermInner::Proc(alt_term);
                            let alt_accepting = wrapped.is_accepting();
                            successes.push(wrapped);
                            success_weights.push(alt_weight);
                            if alt_accepting {
                                NFA_PREFIX_SPILL_PROC
                                    .with(|cell| {
                                        cell.take();
                                    });
                                break;
                            }
                        }
                        NFA_PREFIX_SPILL_PROC
                            .with(|cell| {
                                cell.take();
                            });
                    }
                }
            }
            Err(e) => {
                NFA_PREFIX_SPILL_PROC
                    .with(|cell| {
                        cell.take();
                    });
                if first_err.is_none() {
                    first_err = Some(e);
                }
            }
        }
        match Name::parse(input) {
            Ok(t) => {
                successes.push(AmbientTermInner::Name(t));
                success_weights
                    .push(
                        NFA_PRIMARY_WEIGHT_NAME
                            .with(|cell| {
                                let w = cell.get();
                                cell.set(0.5);
                                w
                            }),
                    );
                let spilled: Vec<(Name, usize, f64)> = NFA_PREFIX_SPILL_NAME
                    .with(|cell| cell.take());
                let primary_is_accepting = successes
                    .last()
                    .map_or(false, |s| s.is_accepting());
                if !primary_is_accepting {
                    let primary_w = NFA_PRIMARY_WEIGHT_NAME.with(|cell| cell.get());
                    const REPLAY_WEIGHT_SLACK: f64 = 2.0;
                    let weight_threshold = primary_w + REPLAY_WEIGHT_SLACK;
                    for (alt_prefix, alt_pos, alt_weight) in spilled {
                        if alt_weight > weight_threshold {
                            break;
                        }
                        NFA_FORCED_PREFIX_NAME
                            .with(|cell| {
                                cell.set(Some((alt_prefix, alt_pos, alt_weight)))
                            });
                        if let Ok(alt_term) = Name::parse(input) {
                            let wrapped = AmbientTermInner::Name(alt_term);
                            let alt_accepting = wrapped.is_accepting();
                            successes.push(wrapped);
                            success_weights.push(alt_weight);
                            if alt_accepting {
                                NFA_PREFIX_SPILL_NAME
                                    .with(|cell| {
                                        cell.take();
                                    });
                                break;
                            }
                        }
                        NFA_PREFIX_SPILL_NAME
                            .with(|cell| {
                                cell.take();
                            });
                    }
                }
            }
            Err(e) => {
                NFA_PREFIX_SPILL_NAME
                    .with(|cell| {
                        cell.take();
                    });
                if first_err.is_none() {
                    first_err = Some(e);
                }
            }
        }
        match successes.len() {
            0 => Err(first_err.unwrap_or_else(|| "Parse error".to_string())),
            1 => Ok(AmbientTerm(successes.into_iter().next().expect("checked len == 1"))),
            _ => {
                AMBIGUOUS_WEIGHTS.with(|cell| cell.set(success_weights));
                Ok(AmbientTerm(AmbientTermInner::from_alternatives(successes)))
            }
        }
    }
    /// C1: Drain accumulated weight corrections from semantic disambiguation.
    ///
    /// Returns all `WeightCorrection` events recorded since the last drain.
    /// Call after each `parse()` to collect feedback for weight training:
    ///
    /// ```ignore
    /// let term = MyLanguage::parse("input")?;
    /// let corrections = MyLanguage::drain_weight_corrections();
    /// for c in &corrections {
    ///     eprintln!("WFST correction in {}: primary_w={}, selected_w={}, delta={}",
    ///               c.category, c.primary_weight, c.selected_weight, c.weight_delta());
    /// }
    /// ```
    ///
    /// The returned vec is empty when the WFST's weight ordering was correct
    /// for all disambiguation decisions in the most recent parse.
    pub fn drain_weight_corrections() -> Vec<mettail_prattail::wfst::WeightCorrection> {
        WEIGHT_CORRECTIONS.with(|cell| cell.take())
    }
    /// Run Ascent on a typed term (seeds the relation for the term's category).
    /// For Ambiguous terms, evaluates only the first alternative by declaration
    /// order. All alternatives that reach Stage C are valid parses, so evaluating
    /// only the first-declared is deterministic and avoids redundant Ascent runs.
    ///
    /// SCC splitting: when available, core-category inputs (e.g., Proc, Name) use
    /// a smaller Ascent struct with fewer rules, reducing fixpoint iteration cost.
    /// Non-core inputs (e.g., Float, Bool, Str) fall back to the full struct.
    pub fn run_ascent_typed(term: &AmbientTerm) -> mettail_runtime::AscentResults {
        mettail_runtime::clear_term_eq_cache();
        mettail_runtime::bump_bcg05_epoch();
        match &term.0 {
            AmbientTermInner::Ambiguous(alts) => {
                let first = alts.first().expect("Ambiguous must have 2+ alternatives");
                let sub_term = AmbientTerm(first.clone());
                Self::run_ascent_typed(&sub_term)
            }
            AmbientTermInner::Proc(_) => {
                let mut prog = AmbientAscentProgCore::default();
                match &term.0 {
                    AmbientTermInner::Proc(inner) => {
                        let initial = inner.clone();
                        prog.proc.push((initial.clone(),));
                        prog.step_term.push((initial.clone(),));
                    }
                    _ => unreachable!(),
                }
                prog.run();
                {
                    let mut __rt05_max_depth: u32 = 0;
                    for (__t,) in prog.proc.iter() {
                        let __d = __t.term_depth();
                        if __d > __rt05_max_depth {
                            __rt05_max_depth = __d;
                        }
                    }
                    for (__t,) in prog.name.iter() {
                        let __d = __t.term_depth();
                        if __d > __rt05_max_depth {
                            __rt05_max_depth = __d;
                        }
                    }
                    if __rt05_max_depth > Self::MAX_FIXPOINT_TERM_DEPTH {
                        eprintln!(
                            "warning[A-RT05]: fixpoint produced term of depth {} (threshold: {}); \
                     possible non-convergence from depth-increasing rules",
                            __rt05_max_depth, Self::MAX_FIXPOINT_TERM_DEPTH,
                        );
                    }
                }
                match &term.0 {
                    AmbientTermInner::Proc(_) => {
                        let all_terms: Vec<Proc> = prog
                            .proc
                            .iter()
                            .map(|(p,)| p.clone())
                            .collect();
                        let rewrites: Vec<(Proc, Proc)> = prog
                            .rw_proc
                            .iter()
                            .map(|(from, to)| (from.clone(), to.clone()))
                            .collect();
                        let term_infos: Vec<mettail_runtime::TermInfo> = all_terms
                            .iter()
                            .map(|t| {
                                let wrapped = AmbientTermInner::Proc(t.clone());
                                let term_id = {
                                    use std::collections::hash_map::DefaultHasher;
                                    use std::hash::{Hash, Hasher};
                                    let mut hasher = DefaultHasher::new();
                                    wrapped.hash(&mut hasher);
                                    hasher.finish()
                                };
                                let has_rewrites = rewrites
                                    .iter()
                                    .any(|(from, _)| from == t);
                                mettail_runtime::TermInfo {
                                    term_id,
                                    display: format!("{}", t),
                                    is_normal_form: !has_rewrites,
                                }
                            })
                            .collect();
                        let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites
                            .iter()
                            .map(|(from, to)| {
                                use std::collections::hash_map::DefaultHasher;
                                use std::hash::{Hash, Hasher};
                                let w_from = AmbientTermInner::Proc(from.clone());
                                let w_to = AmbientTermInner::Proc(to.clone());
                                let mut h1 = DefaultHasher::new();
                                let mut h2 = DefaultHasher::new();
                                w_from.hash(&mut h1);
                                w_to.hash(&mut h2);
                                mettail_runtime::Rewrite {
                                    from_id: h1.finish(),
                                    to_id: h2.finish(),
                                    rule_name: Some("rewrite".to_string()),
                                }
                            })
                            .collect();
                        let equivalences = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::collections::{HashMap, HashSet};
                            use std::hash::{Hash, Hasher};
                            let hash_of = |t: &Proc| -> u64 {
                                let wrapped = AmbientTermInner::Proc(t.clone());
                                let mut h = DefaultHasher::new();
                                wrapped.hash(&mut h);
                                h.finish()
                            };
                            let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                            for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(
                                &prog.__eq_proc_ind_common,
                            ) {
                                let ha = hash_of(a);
                                let hb = hash_of(b);
                                if ha != hb {
                                    classes.entry(ha).or_default().insert(hb);
                                    classes.entry(hb).or_default().insert(ha);
                                }
                            }
                            let mut seen: HashSet<u64> = HashSet::new();
                            let mut result = Vec::new();
                            for (id, peers) in &classes {
                                if seen.contains(id) {
                                    continue;
                                }
                                let mut class: HashSet<u64> = peers.clone();
                                class.insert(*id);
                                for &member in &class {
                                    seen.insert(member);
                                }
                                if class.len() > 1 {
                                    result
                                        .push(mettail_runtime::EquivClass {
                                            term_ids: class.into_iter().collect(),
                                        });
                                }
                            }
                            result
                        };
                        let mut custom_relations = std::collections::HashMap::new();
                        custom_relations
                            .insert(
                                "proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .proc
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string()],
                                    tuples: prog
                                        .name
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .eq_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .eq_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .rw_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .rw_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "step_term".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .step_term
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "ppar_contains".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .ppar_contains
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        mettail_runtime::AscentResults {
                            all_terms: term_infos,
                            rewrites: rewrite_list,
                            equivalences,
                            custom_relations,
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => {
                let mut prog = AmbientAscentProg::default();
                match &term.0 {
                    AmbientTermInner::Proc(inner) => {
                        let initial = inner.clone();
                        prog.proc.push((initial.clone(),));
                        prog.step_term.push((initial.clone(),));
                    }
                    AmbientTermInner::Name(inner) => {
                        let initial = inner.clone();
                        prog.name.push((initial.clone(),));
                    }
                    AmbientTermInner::Ambiguous(_) => unreachable!(),
                }
                prog.run();
                {
                    let mut __rt05_max_depth: u32 = 0;
                    for (__t,) in prog.proc.iter() {
                        let __d = __t.term_depth();
                        if __d > __rt05_max_depth {
                            __rt05_max_depth = __d;
                        }
                    }
                    for (__t,) in prog.name.iter() {
                        let __d = __t.term_depth();
                        if __d > __rt05_max_depth {
                            __rt05_max_depth = __d;
                        }
                    }
                    if __rt05_max_depth > Self::MAX_FIXPOINT_TERM_DEPTH {
                        eprintln!(
                            "warning[A-RT05]: fixpoint produced term of depth {} (threshold: {}); \
                     possible non-convergence from depth-increasing rules",
                            __rt05_max_depth, Self::MAX_FIXPOINT_TERM_DEPTH,
                        );
                    }
                }
                match &term.0 {
                    AmbientTermInner::Proc(_) => {
                        let all_terms: Vec<Proc> = prog
                            .proc
                            .iter()
                            .map(|(p,)| p.clone())
                            .collect();
                        let rewrites: Vec<(Proc, Proc)> = prog
                            .rw_proc
                            .iter()
                            .map(|(from, to)| (from.clone(), to.clone()))
                            .collect();
                        let term_infos: Vec<mettail_runtime::TermInfo> = all_terms
                            .iter()
                            .map(|t| {
                                let wrapped = AmbientTermInner::Proc(t.clone());
                                let term_id = {
                                    use std::collections::hash_map::DefaultHasher;
                                    use std::hash::{Hash, Hasher};
                                    let mut hasher = DefaultHasher::new();
                                    wrapped.hash(&mut hasher);
                                    hasher.finish()
                                };
                                let has_rewrites = rewrites
                                    .iter()
                                    .any(|(from, _)| from == t);
                                mettail_runtime::TermInfo {
                                    term_id,
                                    display: format!("{}", t),
                                    is_normal_form: !has_rewrites,
                                }
                            })
                            .collect();
                        let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites
                            .iter()
                            .map(|(from, to)| {
                                use std::collections::hash_map::DefaultHasher;
                                use std::hash::{Hash, Hasher};
                                let w_from = AmbientTermInner::Proc(from.clone());
                                let w_to = AmbientTermInner::Proc(to.clone());
                                let mut h1 = DefaultHasher::new();
                                let mut h2 = DefaultHasher::new();
                                w_from.hash(&mut h1);
                                w_to.hash(&mut h2);
                                mettail_runtime::Rewrite {
                                    from_id: h1.finish(),
                                    to_id: h2.finish(),
                                    rule_name: Some("rewrite".to_string()),
                                }
                            })
                            .collect();
                        let equivalences = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::collections::{HashMap, HashSet};
                            use std::hash::{Hash, Hasher};
                            let hash_of = |t: &Proc| -> u64 {
                                let wrapped = AmbientTermInner::Proc(t.clone());
                                let mut h = DefaultHasher::new();
                                wrapped.hash(&mut h);
                                h.finish()
                            };
                            let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                            for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(
                                &prog.__eq_proc_ind_common,
                            ) {
                                let ha = hash_of(a);
                                let hb = hash_of(b);
                                if ha != hb {
                                    classes.entry(ha).or_default().insert(hb);
                                    classes.entry(hb).or_default().insert(ha);
                                }
                            }
                            let mut seen: HashSet<u64> = HashSet::new();
                            let mut result = Vec::new();
                            for (id, peers) in &classes {
                                if seen.contains(id) {
                                    continue;
                                }
                                let mut class: HashSet<u64> = peers.clone();
                                class.insert(*id);
                                for &member in &class {
                                    seen.insert(member);
                                }
                                if class.len() > 1 {
                                    result
                                        .push(mettail_runtime::EquivClass {
                                            term_ids: class.into_iter().collect(),
                                        });
                                }
                            }
                            result
                        };
                        let mut custom_relations = std::collections::HashMap::new();
                        custom_relations
                            .insert(
                                "proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .proc
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string()],
                                    tuples: prog
                                        .name
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .eq_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .eq_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .rw_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .rw_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "step_term".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .step_term
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "ppar_contains".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .ppar_contains
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        mettail_runtime::AscentResults {
                            all_terms: term_infos,
                            rewrites: rewrite_list,
                            equivalences,
                            custom_relations,
                        }
                    }
                    AmbientTermInner::Name(_) => {
                        let all_terms: Vec<Name> = prog
                            .name
                            .iter()
                            .map(|(p,)| p.clone())
                            .collect();
                        let rewrites: Vec<(Name, Name)> = prog
                            .rw_name
                            .iter()
                            .map(|(from, to)| (from.clone(), to.clone()))
                            .collect();
                        let term_infos: Vec<mettail_runtime::TermInfo> = all_terms
                            .iter()
                            .map(|t| {
                                let wrapped = AmbientTermInner::Name(t.clone());
                                let term_id = {
                                    use std::collections::hash_map::DefaultHasher;
                                    use std::hash::{Hash, Hasher};
                                    let mut hasher = DefaultHasher::new();
                                    wrapped.hash(&mut hasher);
                                    hasher.finish()
                                };
                                let has_rewrites = rewrites
                                    .iter()
                                    .any(|(from, _)| from == t);
                                mettail_runtime::TermInfo {
                                    term_id,
                                    display: format!("{}", t),
                                    is_normal_form: !has_rewrites,
                                }
                            })
                            .collect();
                        let rewrite_list: Vec<mettail_runtime::Rewrite> = rewrites
                            .iter()
                            .map(|(from, to)| {
                                use std::collections::hash_map::DefaultHasher;
                                use std::hash::{Hash, Hasher};
                                let w_from = AmbientTermInner::Name(from.clone());
                                let w_to = AmbientTermInner::Name(to.clone());
                                let mut h1 = DefaultHasher::new();
                                let mut h2 = DefaultHasher::new();
                                w_from.hash(&mut h1);
                                w_to.hash(&mut h2);
                                mettail_runtime::Rewrite {
                                    from_id: h1.finish(),
                                    to_id: h2.finish(),
                                    rule_name: Some("rewrite".to_string()),
                                }
                            })
                            .collect();
                        let equivalences = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::collections::{HashMap, HashSet};
                            use std::hash::{Hash, Hasher};
                            let hash_of = |t: &Name| -> u64 {
                                let wrapped = AmbientTermInner::Name(t.clone());
                                let mut h = DefaultHasher::new();
                                wrapped.hash(&mut h);
                                h.finish()
                            };
                            let mut classes: HashMap<u64, HashSet<u64>> = HashMap::new();
                            for ((a, b), _) in ascent::internal::RelIndexReadAll::iter_all(
                                &prog.__eq_name_ind_common,
                            ) {
                                let ha = hash_of(a);
                                let hb = hash_of(b);
                                if ha != hb {
                                    classes.entry(ha).or_default().insert(hb);
                                    classes.entry(hb).or_default().insert(ha);
                                }
                            }
                            let mut seen: HashSet<u64> = HashSet::new();
                            let mut result = Vec::new();
                            for (id, peers) in &classes {
                                if seen.contains(id) {
                                    continue;
                                }
                                let mut class: HashSet<u64> = peers.clone();
                                class.insert(*id);
                                for &member in &class {
                                    seen.insert(member);
                                }
                                if class.len() > 1 {
                                    result
                                        .push(mettail_runtime::EquivClass {
                                            term_ids: class.into_iter().collect(),
                                        });
                                }
                            }
                            result
                        };
                        let mut custom_relations = std::collections::HashMap::new();
                        custom_relations
                            .insert(
                                "proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .proc
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string()],
                                    tuples: prog
                                        .name
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .eq_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "eq_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .eq_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_proc".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .rw_proc
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "rw_name".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Name".to_string(), "Name".to_string()],
                                    tuples: prog
                                        .rw_name
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "step_term".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string()],
                                    tuples: prog
                                        .step_term
                                        .iter()
                                        .map(|(e0,)| vec![format!("{}", e0)])
                                        .collect(),
                                },
                            );
                        custom_relations
                            .insert(
                                "ppar_contains".to_string(),
                                mettail_runtime::RelationData {
                                    param_types: vec!["Proc".to_string(), "Proc".to_string()],
                                    tuples: prog
                                        .ppar_contains
                                        .iter()
                                        .map(|(e0, e1)| vec![format!("{}", e0), format!("{}", e1)])
                                        .collect(),
                                },
                            );
                        mettail_runtime::AscentResults {
                            all_terms: term_infos,
                            rewrites: rewrite_list,
                            equivalences,
                            custom_relations,
                        }
                    }
                    AmbientTermInner::Ambiguous(_) => unreachable!(),
                }
            }
        }
    }
    /// Create a new empty environment
    pub fn create_env() -> AmbientEnv {
        AmbientEnv::new()
    }
    fn inferred_to_term_type(t: &InferredType) -> mettail_runtime::TermType {
        match t {
            InferredType::Base(cat) => {
                mettail_runtime::TermType::Base(format!("{:?}", cat))
            }
            InferredType::Arrow(d, c) => {
                mettail_runtime::TermType::Arrow(
                    Box::new(Self::inferred_to_term_type(d)),
                    Box::new(Self::inferred_to_term_type(c)),
                )
            }
            InferredType::MultiArrow(d, c) => {
                mettail_runtime::TermType::MultiArrow(
                    Box::new(Self::inferred_to_term_type(d)),
                    Box::new(Self::inferred_to_term_type(c)),
                )
            }
        }
    }
    pub fn infer_proc_type(term: &Proc) -> mettail_runtime::TermType {
        match term {
            Proc::LamProc(scope) => {
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::infer_proc_type(&body);
                let binder_name = binder.0.pretty_name.as_ref();
                let domain_type = if let Some(name) = binder_name {
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(
                            "Proc".to_string(),
                        ))
                } else {
                    mettail_runtime::TermType::Base("Proc".to_string())
                };
                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
            Proc::MLamProc(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::infer_proc_type(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base("Proc".to_string())),
                    Box::new(body_type),
                )
            }
            Proc::LamName(scope) => {
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::infer_proc_type(&body);
                let binder_name = binder.0.pretty_name.as_ref();
                let domain_type = if let Some(name) = binder_name {
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(
                            "Name".to_string(),
                        ))
                } else {
                    mettail_runtime::TermType::Base("Name".to_string())
                };
                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
            Proc::MLamName(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::infer_proc_type(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base("Name".to_string())),
                    Box::new(body_type),
                )
            }
            _ => mettail_runtime::TermType::Base("Proc".to_string()),
        }
    }
    pub fn infer_name_type(term: &Name) -> mettail_runtime::TermType {
        match term {
            Name::LamProc(scope) => {
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::infer_name_type(&body);
                let binder_name = binder.0.pretty_name.as_ref();
                let domain_type = if let Some(name) = binder_name {
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(
                            "Proc".to_string(),
                        ))
                } else {
                    mettail_runtime::TermType::Base("Proc".to_string())
                };
                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
            Name::MLamProc(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::infer_name_type(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base("Proc".to_string())),
                    Box::new(body_type),
                )
            }
            Name::LamName(scope) => {
                let (binder, body) = scope.clone().unbind();
                let body_type = Self::infer_name_type(&body);
                let binder_name = binder.0.pretty_name.as_ref();
                let domain_type = if let Some(name) = binder_name {
                    body.infer_var_type(name)
                        .map(|t| Self::inferred_to_term_type(&t))
                        .unwrap_or_else(|| mettail_runtime::TermType::Base(
                            "Name".to_string(),
                        ))
                } else {
                    mettail_runtime::TermType::Base("Name".to_string())
                };
                mettail_runtime::TermType::Arrow(
                    Box::new(domain_type),
                    Box::new(body_type),
                )
            }
            Name::MLamName(scope) => {
                let (_binders, body) = scope.clone().unbind();
                let body_type = Self::infer_name_type(&body);
                mettail_runtime::TermType::MultiArrow(
                    Box::new(mettail_runtime::TermType::Base("Name".to_string())),
                    Box::new(body_type),
                )
            }
            _ => mettail_runtime::TermType::Base("Name".to_string()),
        }
    }
    /// B6: Access the prediction WFST for this category.
    ///
    /// Returns a reference to the lazily-initialized per-category WFST.
    /// Use for incremental parsing queries:
    /// - `valid_continuations()`: list valid next tokens (autocomplete)
    /// - `has_valid_dispatch(token)`: early error detection
    /// - `parse_progress(state)`: progress estimation
    pub fn prediction_wfst_proc() -> &'static mettail_prattail::wfst::PredictionWfst {
        &*PREDICTION_Proc
    }
    /// B6: Access the prediction WFST for this category.
    ///
    /// Returns a reference to the lazily-initialized per-category WFST.
    /// Use for incremental parsing queries:
    /// - `valid_continuations()`: list valid next tokens (autocomplete)
    /// - `has_valid_dispatch(token)`: early error detection
    /// - `parse_progress(state)`: progress estimation
    pub fn prediction_wfst_name() -> &'static mettail_prattail::wfst::PredictionWfst {
        &*PREDICTION_Name
    }
}
#[allow(unused_variables, unreachable_patterns)]
impl AmbientLanguage {
    fn collect_all_proc_vars(
        root_term: &Proc,
        term: &Proc,
        result: &mut Vec<mettail_runtime::VarTypeInfo>,
        seen: &mut std::collections::HashSet<std::string::String>,
    ) {
        match term {
            Proc::PVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
                if let Some(name) = &fv.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = root_term
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Proc".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
            }
            Proc::PVar(_) => {}
            Proc::LamProc(scope) => {
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = body
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Proc".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
                Self::collect_all_proc_vars(root_term, body.as_ref(), result, seen);
            }
            Proc::MLamProc(scope) => {
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            let var_type = body
                                .infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                    "Proc".to_string(),
                                ));
                            result
                                .push(mettail_runtime::VarTypeInfo {
                                    name: name.clone(),
                                    ty: var_type,
                                });
                        }
                    }
                }
                Self::collect_all_proc_vars(root_term, body.as_ref(), result, seen);
            }
            Proc::ApplyProc(lam, _arg) => {
                Self::collect_all_proc_vars(root_term, lam.as_ref(), result, seen);
            }
            Proc::MApplyProc(lam, _args) => {
                Self::collect_all_proc_vars(root_term, lam.as_ref(), result, seen);
            }
            Proc::LamName(scope) => {
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = body
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Name".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
                Self::collect_all_proc_vars(root_term, body.as_ref(), result, seen);
            }
            Proc::MLamName(scope) => {
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            let var_type = body
                                .infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                    "Name".to_string(),
                                ));
                            result
                                .push(mettail_runtime::VarTypeInfo {
                                    name: name.clone(),
                                    ty: var_type,
                                });
                        }
                    }
                }
                Self::collect_all_proc_vars(root_term, body.as_ref(), result, seen);
            }
            Proc::ApplyName(lam, _arg) => {
                Self::collect_all_proc_vars(root_term, lam.as_ref(), result, seen);
            }
            Proc::MApplyName(lam, _args) => {
                Self::collect_all_proc_vars(root_term, lam.as_ref(), result, seen);
            }
            Proc::PZero => {}
            Proc::PIn(ref f0, ref f1) => {
                Self::collect_all_proc_vars(root_term, f1.as_ref(), result, seen);
            }
            Proc::POut(ref f0, ref f1) => {
                Self::collect_all_proc_vars(root_term, f1.as_ref(), result, seen);
            }
            Proc::POpen(ref f0, ref f1) => {
                Self::collect_all_proc_vars(root_term, f1.as_ref(), result, seen);
            }
            Proc::PAmb(ref f0, ref f1) => {
                Self::collect_all_proc_vars(root_term, f1.as_ref(), result, seen);
            }
            Proc::PNew(ref f0) => {
                let (binder, body) = f0.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = body
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Name".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
                Self::collect_all_proc_vars(root_term, body.as_ref(), result, seen);
            }
            Proc::PPar(ref f0) => {
                for (elem, _) in f0.iter() {
                    Self::collect_all_proc_vars(root_term, elem, result, seen);
                }
            }
            _ => {}
        }
    }
    fn collect_all_name_vars(
        root_term: &Name,
        term: &Name,
        result: &mut Vec<mettail_runtime::VarTypeInfo>,
        seen: &mut std::collections::HashSet<std::string::String>,
    ) {
        match term {
            Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv))) => {
                if let Some(name) = &fv.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = root_term
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Name".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
            }
            Name::NVar(_) => {}
            Name::LamProc(scope) => {
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = body
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Proc".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
                Self::collect_all_name_vars(root_term, body.as_ref(), result, seen);
            }
            Name::MLamProc(scope) => {
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            let var_type = body
                                .infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                    "Proc".to_string(),
                                ));
                            result
                                .push(mettail_runtime::VarTypeInfo {
                                    name: name.clone(),
                                    ty: var_type,
                                });
                        }
                    }
                }
                Self::collect_all_name_vars(root_term, body.as_ref(), result, seen);
            }
            Name::ApplyProc(lam, _arg) => {
                Self::collect_all_name_vars(root_term, lam.as_ref(), result, seen);
            }
            Name::MApplyProc(lam, _args) => {
                Self::collect_all_name_vars(root_term, lam.as_ref(), result, seen);
            }
            Name::LamName(scope) => {
                let (binder, body) = scope.clone().unbind();
                if let Some(name) = &binder.0.pretty_name {
                    if !seen.contains(name) {
                        seen.insert(name.clone());
                        let var_type = body
                            .infer_var_type(name)
                            .map(|t| Self::inferred_to_term_type(&t))
                            .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                "Name".to_string(),
                            ));
                        result
                            .push(mettail_runtime::VarTypeInfo {
                                name: name.clone(),
                                ty: var_type,
                            });
                    }
                }
                Self::collect_all_name_vars(root_term, body.as_ref(), result, seen);
            }
            Name::MLamName(scope) => {
                let (binders, body) = scope.clone().unbind();
                for binder in &binders {
                    if let Some(name) = &binder.0.pretty_name {
                        if !seen.contains(name) {
                            seen.insert(name.clone());
                            let var_type = body
                                .infer_var_type(name)
                                .map(|t| Self::inferred_to_term_type(&t))
                                .unwrap_or_else(|| mettail_runtime::TermType::Base(
                                    "Name".to_string(),
                                ));
                            result
                                .push(mettail_runtime::VarTypeInfo {
                                    name: name.clone(),
                                    ty: var_type,
                                });
                        }
                    }
                }
                Self::collect_all_name_vars(root_term, body.as_ref(), result, seen);
            }
            Name::ApplyName(lam, _arg) => {
                Self::collect_all_name_vars(root_term, lam.as_ref(), result, seen);
            }
            Name::MApplyName(lam, _args) => {
                Self::collect_all_name_vars(root_term, lam.as_ref(), result, seen);
            }
            _ => {}
        }
    }
}
impl mettail_runtime::Language for AmbientLanguage {
    fn name(&self) -> &'static str {
        "Ambient"
    }
    fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
        &AmbientMetadata
    }
    fn parse_term(
        &self,
        input: &str,
    ) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
        AmbientLanguage::parse(input)
            .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
    }
    fn parse_term_for_env(
        &self,
        input: &str,
    ) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
        AmbientLanguage::parse_preserving_vars(input)
            .map(|t| Box::new(t) as Box<dyn mettail_runtime::Term>)
    }
    fn run_ascent(
        &self,
        term: &dyn mettail_runtime::Term,
    ) -> Result<mettail_runtime::AscentResults, std::string::String> {
        let typed_term = term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .ok_or_else(|| format!("Expected {}", stringify!(AmbientTerm)))?;
        Ok(AmbientLanguage::run_ascent_typed(typed_term))
    }
    fn run_ascent_with_facts(
        &self,
        term: &dyn mettail_runtime::Term,
        facts: &mettail_runtime::SeedFacts,
    ) -> Result<mettail_runtime::AscentResults, std::string::String> {
        let typed_term = term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .ok_or_else(|| format!("Expected {}", stringify!(AmbientTerm)))?;
        let mut __snapshot: std::collections::HashMap<
            String,
            std::collections::HashSet<Vec<String>>,
        > = std::collections::HashMap::new();
        for (rel_name, tuples) in facts {
            let mut set = std::collections::HashSet::new();
            for tuple in tuples {
                set.insert(tuple.clone());
            }
            __snapshot.insert(rel_name.clone(), set);
        }
        mettail_runtime::set_pred_fact_snapshot(__snapshot);
        let result = AmbientLanguage::run_ascent_typed(typed_term);
        mettail_runtime::clear_pred_fact_snapshot();
        Ok(result)
    }
    fn normalize_term(
        &self,
        term: &dyn mettail_runtime::Term,
    ) -> Box<dyn mettail_runtime::Term> {
        if let Some(typed) = term.as_any().downcast_ref::<AmbientTerm>() {
            let normalized = match &typed.0 {
                AmbientTermInner::Ambiguous(alts) => {
                    let normalized_alts: Vec<AmbientTermInner> = alts
                        .iter()
                        .map(|alt| match alt {
                            AmbientTermInner::Proc(inner) => {
                                AmbientTermInner::Proc(inner.normalize())
                            }
                            AmbientTermInner::Name(inner) => {
                                AmbientTermInner::Name(inner.normalize())
                            }
                            AmbientTermInner::Ambiguous(_) => {
                                unreachable!("nested Ambiguous")
                            }
                        })
                        .collect();
                    AmbientTermInner::from_alternatives(normalized_alts)
                }
                AmbientTermInner::Proc(inner) => {
                    AmbientTermInner::Proc(inner.normalize())
                }
                AmbientTermInner::Name(inner) => {
                    AmbientTermInner::Name(inner.normalize())
                }
            };
            Box::new(AmbientTerm(normalized))
        } else {
            term.clone_box()
        }
    }
    fn create_env(&self) -> Box<dyn std::any::Any + Send + Sync> {
        Box::new(AmbientLanguage::create_env())
    }
    fn add_to_env(
        &self,
        env: &mut dyn std::any::Any,
        name: &str,
        term: &dyn mettail_runtime::Term,
    ) -> Result<(), std::string::String> {
        let typed_env = env
            .downcast_mut::<AmbientEnv>()
            .ok_or_else(|| "Invalid environment type".to_string())?;
        let typed_term = term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .ok_or_else(|| format!("Expected {}", stringify!(AmbientTerm)))?;
        typed_env.proc.remove(name);
        typed_env.name.remove(name);
        match &typed_term.0 {
            AmbientTermInner::Ambiguous(alts) => {
                for alt in alts {
                    match alt {
                        AmbientTermInner::Proc(t) => {
                            typed_env.proc.set(name.to_string(), t.clone())
                        }
                        AmbientTermInner::Name(t) => {
                            typed_env.name.set(name.to_string(), t.clone())
                        }
                        AmbientTermInner::Ambiguous(_) => {}
                    }
                }
            }
            AmbientTermInner::Proc(t) => typed_env.proc.set(name.to_string(), t.clone()),
            AmbientTermInner::Name(t) => typed_env.name.set(name.to_string(), t.clone()),
        }
        Ok(())
    }
    fn remove_from_env(
        &self,
        env: &mut dyn std::any::Any,
        name: &str,
    ) -> Result<bool, std::string::String> {
        let typed_env = env
            .downcast_mut::<AmbientEnv>()
            .ok_or_else(|| "Invalid environment type".to_string())?;
        let removed = typed_env.proc.remove(name).is_some()
            || typed_env.name.remove(name).is_some();
        Ok(removed)
    }
    fn clear_env(&self, env: &mut dyn std::any::Any) {
        if let Some(typed_env) = env.downcast_mut::<AmbientEnv>() {
            typed_env.clear();
        }
    }
    fn substitute_env(
        &self,
        term: &dyn mettail_runtime::Term,
        env: &dyn std::any::Any,
    ) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
        let typed_env = env
            .downcast_ref::<AmbientEnv>()
            .ok_or_else(|| "Invalid environment type".to_string())?;
        let typed_term = term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .ok_or_else(|| format!("Expected {}", stringify!(AmbientTerm)))?;
        let substituted = typed_term.0.substitute_env(typed_env);
        Ok(Box::new(AmbientTerm(substituted)))
    }
    fn substitute_env_preserve_structure(
        &self,
        term: &dyn mettail_runtime::Term,
        env: &dyn std::any::Any,
    ) -> Result<Box<dyn mettail_runtime::Term>, std::string::String> {
        let typed_env = env
            .downcast_ref::<AmbientEnv>()
            .ok_or_else(|| "Invalid environment type".to_string())?;
        let typed_term = term
            .as_any()
            .downcast_ref::<AmbientTerm>()
            .ok_or_else(|| format!("Expected {}", stringify!(AmbientTerm)))?;
        let substituted = typed_term.0.substitute_env(typed_env);
        Ok(Box::new(AmbientTerm(substituted)))
    }
    fn list_env(
        &self,
        env: &dyn std::any::Any,
    ) -> Vec<(std::string::String, std::string::String, Option<std::string::String>)> {
        let typed_env = match env.downcast_ref::<AmbientEnv>() {
            Some(e) => e,
            None => return Vec::new(),
        };
        let mut result = Vec::new();
        for (name, val) in typed_env.proc.iter() {
            let comment = typed_env.comments.get(name).cloned();
            result.push((name.clone(), format!("{}", val), comment));
        }
        for (name, val) in typed_env.name.iter() {
            let comment = typed_env.comments.get(name).cloned();
            result.push((name.clone(), format!("{}", val), comment));
        }
        result
    }
    fn set_env_comment(
        &self,
        env: &mut dyn std::any::Any,
        name: &str,
        comment: std::string::String,
    ) -> Result<(), std::string::String> {
        let typed_env = env
            .downcast_mut::<AmbientEnv>()
            .ok_or_else(|| "Invalid environment type".to_string())?;
        typed_env.set_comment(name, comment);
        Ok(())
    }
    fn is_env_empty(&self, env: &dyn std::any::Any) -> bool {
        env.downcast_ref::<AmbientEnv>().map(|e| e.is_empty()).unwrap_or(true)
    }
    fn infer_term_type(
        &self,
        term: &dyn mettail_runtime::Term,
    ) -> mettail_runtime::TermType {
        let typed_term = match term.as_any().downcast_ref::<AmbientTerm>() {
            Some(t) => t,
            None => return mettail_runtime::TermType::Unknown,
        };
        match &typed_term.0 {
            AmbientTermInner::Ambiguous(alts) => {
                for alt in alts {
                    if matches!(alt, AmbientTermInner::Proc(_)) {
                        return mettail_runtime::TermType::Base("Proc".to_string());
                    }
                }
                mettail_runtime::TermType::Base("Ambiguous".to_string())
            }
            AmbientTermInner::Proc(inner) => AmbientLanguage::infer_proc_type(inner),
            AmbientTermInner::Name(inner) => AmbientLanguage::infer_name_type(inner),
        }
    }
    fn infer_var_types(
        &self,
        term: &dyn mettail_runtime::Term,
    ) -> Vec<mettail_runtime::VarTypeInfo> {
        let typed_term = match term.as_any().downcast_ref::<AmbientTerm>() {
            Some(t) => t,
            None => return Vec::new(),
        };
        match &typed_term.0 {
            AmbientTermInner::Ambiguous(alts) => {
                if let Some(first) = alts.first() {
                    let sub = AmbientTerm(first.clone());
                    self.infer_var_types(&sub)
                } else {
                    Vec::new()
                }
            }
            AmbientTermInner::Proc(inner) => {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                AmbientLanguage::collect_all_proc_vars(
                    inner,
                    inner,
                    &mut result,
                    &mut seen,
                );
                result
            }
            AmbientTermInner::Name(inner) => {
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                AmbientLanguage::collect_all_name_vars(
                    inner,
                    inner,
                    &mut result,
                    &mut seen,
                );
                result
            }
        }
    }
    fn infer_var_type(
        &self,
        term: &dyn mettail_runtime::Term,
        var_name: &str,
    ) -> Option<mettail_runtime::TermType> {
        let typed_term = match term.as_any().downcast_ref::<AmbientTerm>() {
            Some(t) => t,
            None => return None,
        };
        match &typed_term.0 {
            AmbientTermInner::Ambiguous(alts) => {
                if let Some(first) = alts.first() {
                    let sub = AmbientTerm(first.clone());
                    self.infer_var_type(&sub, var_name)
                } else {
                    None
                }
            }
            AmbientTermInner::Proc(inner) => {
                if let Some(t) = inner.infer_var_type(var_name) {
                    return Some(AmbientLanguage::inferred_to_term_type(&t));
                }
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                AmbientLanguage::collect_all_proc_vars(
                    inner,
                    inner,
                    &mut result,
                    &mut seen,
                );
                result.into_iter().find(|v| v.name == var_name).map(|v| v.ty)
            }
            AmbientTermInner::Name(inner) => {
                if let Some(t) = inner.infer_var_type(var_name) {
                    return Some(AmbientLanguage::inferred_to_term_type(&t));
                }
                let mut result = Vec::new();
                let mut seen = std::collections::HashSet::new();
                AmbientLanguage::collect_all_name_vars(
                    inner,
                    inner,
                    &mut result,
                    &mut seen,
                );
                result.into_iter().find(|v| v.name == var_name).map(|v| v.ty)
            }
        }
    }
    fn decompose_into_cek(
        &self,
        term: &dyn mettail_runtime::Term,
        evaluator: &mut mettail_runtime::CekEvaluator,
    ) -> bool {
        let typed = match term.as_any().downcast_ref::<AmbientTerm>() {
            Some(t) => t,
            None => return false,
        };
        match &typed.0 {
            AmbientTermInner::Ambiguous(alts) => {
                if let Some(first) = alts.first() {
                    let sub = AmbientTerm(first.clone());
                    return self.decompose_into_cek(&sub, evaluator);
                }
                return false;
            }
            AmbientTermInner::Proc(term) => {
                match term {
                    Proc::PZero => {
                        evaluator.set_control(format!("{}", term));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::PIn(f0, f1) => {
                        evaluator
                            .push_frame(mettail_runtime::EvalFrame::BinOp {
                                operator: "in(".to_string(),
                                lhs_display: format!("{}", f0),
                            });
                        evaluator.set_control(format!("{}", f1));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::POut(f0, f1) => {
                        evaluator
                            .push_frame(mettail_runtime::EvalFrame::BinOp {
                                operator: "out(".to_string(),
                                lhs_display: format!("{}", f0),
                            });
                        evaluator.set_control(format!("{}", f1));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::POpen(f0, f1) => {
                        evaluator
                            .push_frame(mettail_runtime::EvalFrame::BinOp {
                                operator: "open(".to_string(),
                                lhs_display: format!("{}", f0),
                            });
                        evaluator.set_control(format!("{}", f1));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::PAmb(f0, f1) => {
                        evaluator
                            .push_frame(mettail_runtime::EvalFrame::BinOp {
                                operator: "[".to_string(),
                                lhs_display: format!("{}", f0),
                            });
                        evaluator.set_control(format!("{}", f1));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::PNew(..) => {
                        evaluator.set_control(format!("{}", term));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                    Proc::PPar(coll) => {
                        let items: Vec<String> = coll
                            .iter()
                            .flat_map(|(elem, count)| {
                                std::iter::repeat(format!("{}", elem)).take(count)
                            })
                            .collect();
                        if items.is_empty() {
                            evaluator.set_control(format!("{}", term));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        } else if items.len() == 1 {
                            evaluator
                                .set_control(items.into_iter().next().expect("len == 1"));
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        } else {
                            let mut remaining: Vec<String> = items;
                            let first = remaining.remove(0);
                            evaluator
                                .push_frame(mettail_runtime::EvalFrame::Parallel {
                                    remaining,
                                    completed: Vec::new(),
                                });
                            evaluator.set_control(first);
                            evaluator.set_state(mettail_runtime::EvalState::Reducing);
                        }
                    }
                    _ => {
                        evaluator.set_control(format!("{}", term));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                }
            }
            AmbientTermInner::Name(term) => {
                match term {
                    _ => {
                        evaluator.set_control(format!("{}", term));
                        evaluator.set_state(mettail_runtime::EvalState::Reducing);
                    }
                }
            }
        }
        true
    }
}
