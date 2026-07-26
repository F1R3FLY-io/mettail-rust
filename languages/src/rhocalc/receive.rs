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
        Name::NQuoteNil => Name::NQuote(std::sync::Arc::new(Proc::PZero)),
        Name::NQuoteShort(p) => Name::NQuote(std::sync::Arc::new(p.as_ref().clone())),
        Name::NParen(inner) => {
            Name::NParen(std::sync::Arc::new(normalize_quote_name(inner.as_ref())))
        },
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
    match &q_norm {
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => !items.is_empty(),
            _ => false,
        },
        _ => false,
    }
}

/// ⚠ ★ #33 LATENT CONFLATION SITE — and the DESTRUCTIVE one.
///
/// The two `_ => Proc::PZero` arms below fabricate a *result* for a condition the host could
/// not decide. That is strictly worse than the three live COMM sites: they merely decline to
/// rewrite, leaving the term for the machine, whereas this one **commits to an answer** — it
/// erases `body` and yields the null process, which is indistinguishable from the guard
/// having been decidably `false`.
///
/// It is also weaker than [`eval_guard_disposition`] on the deciding side: it only ever
/// recognizes a literal `CastBool(BoolLit(_))`, so `__guard_then(1 < 2, P)` discards `P`
/// even though the guard is trivially decidable. Both defects have the same root as the rest
/// of #33 — a total function forced to answer where the honest answer is "I cannot decide".
///
/// **NOT changed in stage A**, which is behaviourally inert by construction; repairing this
/// arm changes normal forms and belongs to stage C. Documented here so the site cannot be
/// re-derived as "obviously fine" by the next reader.
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
        // ★ #33 / divergence H, SECOND HALF. Divergence H — "Rholang's `==` is STRUCTURAL
        // equality on the whole `Par` (`reduce.rs::combine_eq`), which answers `true` for two
        // `GBool`s; RhoCalc conforms DOWN to Rholang" — was closed in the FOLD lane
        // (`rhocalc.rs`'s `Eq` arm) and NOT here, in the GUARD lane. There are two `Eq`
        // implementations and only one got the arm.
        //
        // The asymmetry is what made it survive: in the fold lane an unhandled shape yields
        // `Proc::Err`, which is LOUD and was caught same-day by the conformance differential.
        // Here an unhandled shape yields `None`, which the eager COMM sites treat identically
        // to a decided `false` — so the identical gap is SILENT. `_ => None` is a bug
        // concealer, which is the deeper point of #33.
        //
        // Concretely: `for(x <- c where x == true){*x} | c!(true)` built a `sub_cond` of
        // `Eq(CastBool(true), CastBool(true))`, `eval_cmp_order` had no `CastBool` arm,
        // `compare_collection_equality` declines when neither side is a collection, so the
        // guard evaluated to `None` and the host BLOCKED a COMM the machine fires. And because
        // `sub_cond` is a local value never registered as an Ascent `proc(…)` fact, the fold
        // lane's fix could not reach it.
        (Proc::CastBool(a), Proc::CastBool(b)) => match (a.as_ref(), b.as_ref()) {
            // `false < true`, matching `bool`'s own `Ord`, so `<`/`<=` on booleans agree with
            // Rust and with the structural comparison the machine performs.
            (Bool::BoolLit(x), Bool::BoolLit(y)) => Some(x.cmp(y)),
            _ => None,
        },
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

/// ★ #33 STAGE A — the HOST's disposition toward one `where` guard.
///
/// # Why this type exists
///
/// The host guard evaluator used to answer `Option<bool>`, and its `None` conflated two
/// facts that are not the same fact:
///
/// | fact | what it licenses |
/// |------|------------------|
/// | the guard is decidably **FALSE** | the COMM must not fire, and that is the final answer |
/// | the host **CANNOT DECIDE** the guard | the host must not fire it, but the MACHINE may |
///
/// Both produce "no rewrite" at every eager COMM site, so the conflation was invisible —
/// and that invisibility is the defect's real cost. It does not merely mis-handle genuinely
/// undecidable guards; it **conceals ordinary evaluator gaps**. Divergence H's second half
/// (`Eq(CastBool, CastBool)`, closed in stage B1) is the worked example: `eval_cmp_order`
/// had no `CastBool` arm, so `where x == true` answered `None`, every eager site read that
/// as `false`, and the host silently blocked a COMM the machine fires. The identical gap in
/// the FOLD lane yields `Proc::Err`, which is loud, and was caught the same day.
///
/// # Why these three names
///
/// They deliberately mirror `rholang-runtime::guard_discharge::GuardDischarge`
/// `{Discharged, Refuted, Residual}`, so there is ONE guard-disposition vocabulary across
/// both lanes rather than two:
///
/// ```text
///     guard lane (here)          compile-time discharge lane
///     ────────────────────       ───────────────────────────
///     Fires      ⟷              Discharged   (decided true)
///     Blocks     ⟷              Refuted      (decided false)
///     Declines   ⟷              Residual     (undecided — the machine decides)
/// ```
///
/// The discharge lane already separates these correctly, and its own test
/// `a_declining_host_leg_never_licenses_discharge` names this very defect as the thing it
/// is protecting the emitted artifact from. This type brings the guard lane's vocabulary up
/// to the discharge lane's.
///
/// # Scope of stage A
///
/// **Behaviourally inert.** `Blocks` and `Declines` both still produce no rewrite at every
/// call site, so no reduction, normal form, or golden moves. Stage A only makes the
/// distinction *representable and observable*; making the residue honest about which one
/// occurred is stage C.
///
/// Known sites that still conflate the two, retained here as the checklist stage C works
/// against:
///
/// * `eval_where_comm_single`, `finish_single_comm`'s empty-bind arm, and
///   `comm_pforjoin_subst` — the three LIVE eager sites, each marked inline below.
/// * [`guard_then`] — LATENT and **destructive**: it fabricates `Proc::PZero` for an
///   undecided condition, which is worse than blocking because it commits to an answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GuardDisposition {
    /// The host DECIDED the guard `true`. The COMM fires.
    Fires,
    /// The host DECIDED the guard `false`. The COMM must not fire, and the machine would
    /// agree — this is a verdict, not an abstention.
    Blocks,
    /// The host CANNOT DECIDE this guard. The host must not fire it, but this is **not** a
    /// verdict of `false`: the machine may well fire it at COMM time. Reaching this for a
    /// guard the host ought to be able to decide is an evaluator GAP, not an undecidable
    /// guard, and stage C is what makes the two distinguishable from the outside.
    Declines,
}

impl GuardDisposition {
    /// A decided verdict.
    pub const fn from_decided(verdict: bool) -> Self {
        if verdict {
            Self::Fires
        } else {
            Self::Blocks
        }
    }

    /// Lift the legacy `Option<bool>` encoding. `None` reads as "declined".
    pub const fn from_verdict(verdict: Option<bool>) -> Self {
        match verdict {
            Some(v) => Self::from_decided(v),
            None => Self::Declines,
        }
    }

    /// Project back to the legacy `Option<bool>` encoding. Total and lossless in this
    /// direction; the information lost is `Blocks` vs `Declines`, which is precisely the
    /// distinction this type exists to preserve.
    pub const fn verdict(self) -> Option<bool> {
        match self {
            Self::Fires => Some(true),
            Self::Blocks => Some(false),
            Self::Declines => None,
        }
    }

    /// `true` iff this disposition licenses the COMM to fire.
    pub const fn fires(self) -> bool {
        matches!(self, Self::Fires)
    }

    /// Three-valued negation: `Declines` is its own negation, because "unknown" negated is
    /// still "unknown".
    pub const fn negate(self) -> Self {
        match self {
            Self::Fires => Self::Blocks,
            Self::Blocks => Self::Fires,
            Self::Declines => Self::Declines,
        }
    }
}

/// The HOST `where`-guard evaluator, answering the three-way [`GuardDisposition`].
///
/// This is THE host guard evaluator — [`eval_guard_bool`] is a projection of it, not a
/// second implementation, so there is no dual path and no way for the two to drift.
///
/// ## Connective discipline (preserved EXACTLY from the `Option<bool>` original)
///
/// The original arms were written `Some(eval_guard_bool(a)? && eval_guard_bool(b)?)` and
/// friends. That expression is **left-strict** in `a` (the `?` runs first) and then
/// **short-circuiting** in `b` (Rust's `&&`/`||` do not evaluate their right operand once
/// the left settles the result). So `false and <undecided>` was already `Some(false)`, not
/// `None`. Each arm below reproduces that behaviour verbatim; the `match` simply makes the
/// discipline legible instead of leaving it implicit in operator semantics.
///
/// ★ It is NOT full Kleene, and stage B2's proposal to make it so is **not** obviously
/// sound — see the measurement recorded on [`GuardDisposition`]'s stage-C checklist and in
/// the `#33` report: f1r3node evaluates BOTH operands of `EAnd`/`EOr` unconditionally
/// (`reduce.rs` — the work-stack driver pushes `EBool(p2)` and `EBool(p1)` together, and the
/// recursive fallback binds `b1` and `b2` with `?` before combining), and `guard_passes`
/// maps any `Err` or non-boolean result to `false`. So `kleene_or(Some(true), None)` would
/// fire host-side while the machine does NOT fire — unsoundness in the FIRING direction.
pub fn eval_guard_disposition(cond: &Proc) -> GuardDisposition {
    use GuardDisposition::{Blocks, Declines, Fires};
    match cond {
        Proc::CastBool(b) => match b.as_ref() {
            Bool::BoolLit(v) => GuardDisposition::from_decided(*v),
            _ => Declines,
        },
        // `a and b`: left-strict, then short-circuit on a decided-FALSE left.
        Proc::And(a, b) => match eval_guard_disposition(a) {
            Declines => Declines,
            Blocks => Blocks,
            Fires => eval_guard_disposition(b),
        },
        // `a or b`: dual — short-circuit on a decided-TRUE left.
        Proc::Or(a, b) => match eval_guard_disposition(a) {
            Declines => Declines,
            Fires => Fires,
            Blocks => eval_guard_disposition(b),
        },
        // M-0: material implication `a implies b ≡ (not a) or b`, and therefore the `Or`
        // discipline applied to the NEGATED antecedent: a decided-FALSE antecedent
        // short-circuits to `Fires` (vacuous truth). The machine twin is
        // `EOrBody(ENotBody ⟦a⟧, ⟦b⟧)` in `rhocalc_ast::lower_proc`. On the four
        // ground-boolean rows the two paths agree by construction (see the truth table in
        // `rholang-runtime/tests/rho_implies_guard.rs`, which drives both).
        Proc::Implies(a, b) => match eval_guard_disposition(a) {
            Declines => Declines,
            Blocks => Fires,
            Fires => eval_guard_disposition(b),
        },
        // M-1b: the SPATIAL satisfaction operator `t matches φ`.
        //
        // Delegated to `formula::host_matches_verdict`, which decides the fragment
        // for which the generated first-order `Proc::match_pattern` is a faithful
        // model of the reducer's spatial matcher (the logical constants, the
        // propositional connectives, and a concrete term pattern) and DECLINES the
        // SEPARATING conjunction, whose AC-with-remainder semantics belongs to the
        // reducer alone.
        //
        // ★ This is the arm where `Declines` is a genuine, permanent abstention rather
        // than an evaluator gap: nothing is guessed and nothing is fabricated, and the
        // guard is decided where it can be decided soundly — on the machine, by
        // `rho_pure_eval` through the `SpatialMatch` oracle.
        Proc::Matches(target, formula) => GuardDisposition::from_verdict(
            crate::rhocalc::formula::host_matches_verdict(target, formula),
        ),
        Proc::Not(a) => eval_guard_disposition(a).negate(),
        Proc::Eq(a, b) => match crate::rhocalc::runtime::compare_collection_equality(a, b) {
            Some(v) => GuardDisposition::from_decided(v),
            None => {
                GuardDisposition::from_verdict(eval_cmp_order(a, b).map(|o| o == Ordering::Equal))
            },
        },
        Proc::Ne(a, b) => match crate::rhocalc::runtime::compare_collection_equality(a, b) {
            Some(v) => GuardDisposition::from_decided(!v),
            None => {
                GuardDisposition::from_verdict(eval_cmp_order(a, b).map(|o| o != Ordering::Equal))
            },
        },
        Proc::Gt(a, b) => {
            GuardDisposition::from_verdict(eval_cmp_order(a, b).map(|o| o == Ordering::Greater))
        },
        Proc::Lt(a, b) => {
            GuardDisposition::from_verdict(eval_cmp_order(a, b).map(|o| o == Ordering::Less))
        },
        Proc::GtEq(a, b) => GuardDisposition::from_verdict(
            eval_cmp_order(a, b).map(|o| o == Ordering::Greater || o == Ordering::Equal),
        ),
        Proc::LtEq(a, b) => GuardDisposition::from_verdict(
            eval_cmp_order(a, b).map(|o| o == Ordering::Less || o == Ordering::Equal),
        ),
        // ★ THE CONCEALER. Every shape the host has no arm for lands here. Under the old
        // `Option<bool>` encoding this was indistinguishable from a decided `false` at every
        // caller, which is how divergence H's second half stayed silent for as long as it
        // did. It is still `Declines` — but now it SAYS so.
        _ => Declines,
    }
}

/// The HOST `where`-guard evaluator in its legacy `Option<bool>` encoding: `Some(b)` iff
/// this guard decides to the ground boolean `b`, `None` if the host declines the fragment.
///
/// A thin projection of [`eval_guard_disposition`] — NOT a second implementation. Retained
/// with its exact original signature because it is the HOST leg of
/// `rholang-runtime::guard_discharge`'s anti-divergence fence, whose `classify` takes
/// `Option<bool>` and whose three-way `GuardDischarge` this crate must not depend on
/// (`languages` sits below `rholang-runtime`).
///
/// `pub` since S-D0. Compile-time discharge of a binder-closed guard requires this
/// evaluator AND the machine's (`rho_pure_eval` under the reducer's `SpatialMatcherOracle`)
/// to return the same verdict. The machine leg is the authority — it is what runs — so this
/// one costs nothing and buys a loud warning wherever the two readings of the same surface
/// guard would have diverged. A `None` here can never license a discharge; it falls to
/// `Residual` and the machine decides at COMM time, as today.
pub fn eval_guard_bool(cond: &Proc) -> Option<bool> {
    eval_guard_disposition(cond).verdict()
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
        .map(|p| Name::NQuote(std::sync::Arc::new(p.clone())))
        .collect();

    let proc_substituted = body.subst(&vars_refs, &proc_repls);
    proc_substituted.subst_name(&vars_refs, &name_repls)
}

/// Eager guarded single-receive: substitute the received payload `q` into both
/// `body` and `cond`, evaluate the guard, and return the substituted body ONLY
/// when the pattern matches AND the guard evaluates to `true`. Returns `None`
/// (a *block* — the COMM must not fire) on a pattern mismatch, an unevaluable
/// guard, or a `false` guard.
///
/// This is the semantic core shared by two call sites:
///   • `finish_single_comm` — evaluates the guard EAGERLY at COMM time, exactly
///     like the multi-channel join path (`comm_pforjoin_subst`). A blocked guard
///     yields no rewrite, so the receiver and the send both remain.
///   • `comm_pforwhere_subst` — the `CommWhere` fold/marker bridge, which wraps a
///     block back into a `CommWhere(...)` marker (the deferred-fold disposition).
pub(crate) fn eval_where_comm_single(
    pat: &Proc,
    q: &Proc,
    cond: &Proc,
    body: &Proc,
) -> Option<Proc> {
    let sub_body = receive_apply(pat, q, body)?;
    let sub_cond = receive_apply(pat, q, cond)?;
    match eval_guard_disposition(&sub_cond) {
        GuardDisposition::Fires => Some(sub_body),
        // ★ #33 CONFLATION SITE 1 of 3 (LIVE). `Blocks` is "the machine would agree the
        // guard is false"; `Declines` is "the host could not decide, and the machine may
        // still fire". Both yield no rewrite TODAY — that is what makes stage A inert —
        // but they are different facts, and only `Blocks` is a correct reason to leave the
        // COMM unfired for good. Stage C makes the residue say which one occurred.
        GuardDisposition::Blocks | GuardDisposition::Declines => None,
    }
}

pub fn comm_pforwhere_subst(pat: &Proc, n: &Name, q: &Proc, cond: &Proc, body: &Proc) -> Proc {
    match eval_where_comm_single(pat, q, cond, body) {
        Some(sub_body) => sub_body,
        None => Proc::CommWhere(
            std::sync::Arc::new(pat.clone()),
            std::sync::Arc::new(n.clone()),
            std::sync::Arc::new(q.clone()),
            std::sync::Arc::new(cond.clone()),
            std::sync::Arc::new(body.clone()),
        ),
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
    items.push(Proc::PDrop(std::sync::Arc::new(ret.clone())));
    items.extend(args.iter().cloned());
    crate::rhocalc::runtime::mk_output(channel, items, false)
}

fn desugar_query_bind(
    bind: InputBind,
    counter: &mut usize,
) -> (InputBind, Vec<(Binder<String>, Proc)>) {
    // `InputBind` implements `Drop` (generated), so we cannot move fields out by
    // destructuring; match by reference and clone the captured fields instead.
    match &bind {
        InputBind::InputBindQuery(lhs, channel, args) => {
            let (binder, ret_name) = fresh_query_return(counter);
            let recv_bind =
                InputBind::InputBind(lhs.clone(), std::sync::Arc::new(ret_name.clone()));
            let send = mk_query_send(channel.as_ref(), &ret_name, args);
            (recv_bind, vec![(binder, send)])
        },
        InputBind::InputBindEmptyQuery(channel, args) => {
            let (binder, ret_name) = fresh_query_return(counter);
            let recv_bind = InputBind::InputBindEmpty(std::sync::Arc::new(ret_name.clone()));
            let send = mk_query_send(channel.as_ref(), &ret_name, args);
            (recv_bind, vec![(binder, send)])
        },
        _ => (bind, vec![]),
    }
}

fn desugar_row_query_binds(
    row: ForRow,
    counter: &mut usize,
) -> (ForRow, Vec<(Binder<String>, Proc)>) {
    // `ForRow` implements `Drop` (generated); match by reference and clone the
    // captured fields. `b: &Arc<InputBind>` → `(**b).clone()` yields an owned
    // `InputBind` for `desugar_query_bind`; `bs: &Vec<InputBind>` iterates by ref.
    match &row {
        ForRow::ForRowSingleNoWhere(b) => {
            let (b2, sends) = desugar_query_bind((**b).clone(), counter);
            (ForRow::ForRowSingleNoWhere(std::sync::Arc::new(b2)), sends)
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            let (b2, sends) = desugar_query_bind((**b).clone(), counter);
            (ForRow::ForRowSingleWhere(std::sync::Arc::new(b2), cond.clone()), sends)
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let mut acc_sends = Vec::new();
            let (b2, mut sends0) = desugar_query_bind((**b).clone(), counter);
            acc_sends.append(&mut sends0);
            let mut bs2 = Vec::with_capacity(bs.len());
            for ib in bs {
                let (ib2, mut sends_i) = desugar_query_bind(ib.clone(), counter);
                acc_sends.append(&mut sends_i);
                bs2.push(ib2);
            }
            (ForRow::ForRowNoWhere(std::sync::Arc::new(b2), bs2), acc_sends)
        },
        ForRow::ForRowWhere(b, bs, cond) => {
            let mut acc_sends = Vec::new();
            let (b2, mut sends0) = desugar_query_bind((**b).clone(), counter);
            acc_sends.append(&mut sends0);
            let mut bs2 = Vec::with_capacity(bs.len());
            for ib in bs {
                let (ib2, mut sends_i) = desugar_query_bind(ib.clone(), counter);
                acc_sends.append(&mut sends_i);
                bs2.push(ib2);
            }
            (ForRow::ForRowWhere(std::sync::Arc::new(b2), bs2, cond.clone()), acc_sends)
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

    let receive_proc = Proc::PForUser(rewritten_rows, std::sync::Arc::new((*body).clone()));
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
    Proc::PNew(Scope::new(binders, std::sync::Arc::new(Proc::PPar(bag))))
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

    match eval_guard_disposition(&acc_cond) {
        GuardDisposition::Fires => Some(acc_body),
        // ★ #33 CONFLATION SITE 2 of 3 (LIVE) — the multi-channel join twin of the arm in
        // `eval_where_comm_single`. Inert in stage A; see `GuardDisposition`.
        GuardDisposition::Blocks | GuardDisposition::Declines => None,
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
    // A WHOLE-MESSAGE binder — `x <- c` (a `Name` variable) or `@x <- c` (a bare process
    // variable) — binds the message itself, so the arity-1 payload list is unwrapped exactly as
    // the single-row path does (`receive_apply`, which special-cases a bare `Proc::PVar` for the
    // same reason). Anything structured (`@[a, b] <- c`, `@0 <- c`, a polyadic row) matches
    // against the arity-normalized payload list.
    //
    // Before 2026-07-25 only `is_simple_var_bind` (the `Name`-variable form) unwrapped here, so a
    // QUOTED binder inside a `&`-join bound the payload LIST: measured,
    // `for(@x <- c1 & @y <- c2){x} | c1!(p) | c2!(q)` answered `[p]` while its single-row twin
    // `for(@x <- c){x} | c!(p)` answered `p`, and the `Name`-binder join
    // `for(x <- c1 & y <- c2){*x} | …` also answered `p`. One receive, two binding rules — this
    // makes the join path agree with the row path (`languages/tests/rhocalc_tests.rs::comm::
    // quoted_name_binder_form_is_equivalent`, whose very name asserts the equivalence).
    let binds_whole_message =
        is_simple_var_bind(ib) || matches!(pat, Proc::PVar(OrdVar(Var::Free(_))));
    if binds_whole_message {
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
        Proc::PForUser(rows[1..].to_vec(), std::sync::Arc::new(body.clone()))
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
        // ROOT-P Layer F: the persistent-SPECIFIC ForRow arms
        // (ForRowSinglePersistentNoWhere / ...Where / ...SingleEmptyPersistent... /
        // ForRowPersistentNoWhere / ...Where) were REMOVED together with their
        // now-deleted grammar rules (rhocalc.rs). A `<=` head now parses as the
        // general ForRow rules over a persistent InputBind (InputBindPersistent /
        // InputBindEmptyPersistent), so the arms below already cover it with
        // `b = InputBind::InputBind{Persistent,EmptyPersistent}(…)` — byte-
        // identical desugar (FV: ForRowPersistentRuleRedundancy.v T1).
        ForRow::ForRowSingleNoWhere(b) => {
            try_comm_single(b.as_ref(), whole_bag, for_key, &cont, None)
        },
        ForRow::ForRowSingleWhere(b, cond) => {
            try_comm_single(b.as_ref(), whole_bag, for_key, &cont, Some(cond.as_ref()))
        },
        ForRow::ForRowNoWhere(b, bs) => {
            let true_c = Proc::CastBool(std::sync::Arc::new(Bool::BoolLit(true)));
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
    let (_n_out, q) = output_parts(output_key)?;
    let new_center = if recv_ctx.empty_bind {
        if !empty_bind_matches_payload(&q) {
            return None;
        }
        if let Some(c) = recv_ctx.where_cond {
            match eval_guard_disposition(c) {
                GuardDisposition::Fires => recv_ctx.cont.clone(),
                // ★ #33 CONFLATION SITE 3 of 3 (LIVE) — the empty-bind arm. Inert in
                // stage A; see `GuardDisposition`.
                GuardDisposition::Blocks | GuardDisposition::Declines => return None,
            }
        } else {
            recv_ctx.cont.clone()
        }
    } else {
        if let Some(c) = recv_ctx.where_cond {
            // Evaluate the guard EAGERLY at COMM time (mirrors the multi-channel
            // join path `comm_pforjoin_subst`). A pattern mismatch or a
            // false/unevaluable guard blocks the COMM (`return None`), so the
            // receiver and the send both remain in the term. This replaces the
            // former deferred `CommWhere(...)` marker, which the Dovetail
            // normalizer never reduces: its `CommWhere` fold demands the `cond`
            // argument already be a fold-value, but `cond` (`x > 1`) carries the
            // free pattern variable `x` that is only bound *inside* the fold —
            // so the marker was left stuck in every normal form.
            eval_where_comm_single(&recv_ctx.pat, &q, c, recv_ctx.cont)?
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
            Some((Name::NQuote(std::sync::Arc::new(p.as_ref().clone())), q.as_ref().clone()))
        },
        Proc::PPersistOutputShort(p, q) => {
            Some((Name::NQuote(std::sync::Arc::new(p.as_ref().clone())), q.as_ref().clone()))
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

/// ★ #33 STAGE A — the separating tests for [`GuardDisposition`].
///
/// Each row here is a guard for which the old `Option<bool>` encoding answered `None`, and
/// therefore for which every eager COMM site behaved *exactly* as if the guard were
/// decidably `false`. The point of these tests is that the two are now distinguishable, and
/// that they are distinguished the RIGHT way round — `Declines`, not `Blocks`.
///
/// They are also the regression fence for stage A's inertness claim: every row additionally
/// asserts that the legacy projection `eval_guard_bool` is unchanged, so a future edit
/// cannot quietly turn a `Declines` into a decided verdict (or vice versa) without failing
/// here.
#[cfg(test)]
mod guard_disposition_tests {
    use super::*;
    use std::sync::Arc;

    fn bool_lit(v: bool) -> Proc {
        Proc::CastBool(Arc::new(Bool::BoolLit(v)))
    }

    fn int_lit(n: i64) -> Proc {
        Proc::CastInt(Arc::new(Int::NumLit(n)))
    }

    fn str_lit(s: &str) -> Proc {
        Proc::CastStr(Arc::new(Str::StringLit(s.to_string())))
    }

    /// `t matches { φ | ψ }` — the SEPARATING conjunction. `formula::classify` gives
    /// `PParInfix` the `FormulaShape::Separation` shape, and `host_matches_verdict` declines
    /// it on purpose: its semantics is AC matching with a remainder, which belongs to the
    /// reducer's spatial matcher alone.
    fn separating_guard() -> Proc {
        Proc::Matches(
            Arc::new(str_lit("hi")),
            Arc::new(Proc::PParInfix(Arc::new(str_lit("hi")), Arc::new(bool_lit(true)))),
        )
    }

    /// ── ROW 1: the separating conjunction ──
    ///
    /// A permanent, principled abstention: the host has no sound way to decide it and says
    /// so. Under `Option<bool>` this was `None` and read as `false` at every COMM site, so
    /// the host blocked a COMM the machine may well fire.
    #[test]
    fn a_separating_formula_declines_rather_than_blocks() {
        let guard = separating_guard();
        assert_eq!(
            eval_guard_disposition(&guard),
            GuardDisposition::Declines,
            "`t matches {{φ | ψ}}` must DECLINE — the separating conjunction is the \
             reducer's to decide. Answering `Blocks` would assert the machine agrees the \
             guard is false, which the host has no evidence for."
        );
        assert_ne!(
            eval_guard_disposition(&guard),
            GuardDisposition::Blocks,
            "declining must not be spelled as a false verdict"
        );
        // Inertness: the legacy projection is unchanged.
        assert_eq!(eval_guard_bool(&guard), None);
    }

    /// ── ROW 2a: `Eq(CastBool, CastBool)` — the stage-B1 regression pin ──
    ///
    /// This is divergence H's second half. Before B1, `eval_cmp_order` had no `CastBool`
    /// arm, so `where x == true` answered `None` and the host blocked a COMM the machine
    /// fires — a *silent evaluator gap* wearing a decline's clothing. It must now DECIDE.
    #[test]
    fn eq_on_two_bool_literals_decides_and_does_not_decline() {
        let t = Proc::Eq(Arc::new(bool_lit(true)), Arc::new(bool_lit(true)));
        assert_eq!(
            eval_guard_disposition(&t),
            GuardDisposition::Fires,
            "`true == true` is decidable and must FIRE (stage B1)"
        );
        let f = Proc::Eq(Arc::new(bool_lit(true)), Arc::new(bool_lit(false)));
        assert_eq!(
            eval_guard_disposition(&f),
            GuardDisposition::Blocks,
            "`true == false` is decidably FALSE — a genuine verdict, not an abstention"
        );
        assert_eq!(eval_guard_bool(&t), Some(true));
        assert_eq!(eval_guard_bool(&f), Some(false));
    }

    /// ── ROW 2b: `Eq` the host cannot decide ──
    ///
    /// The complement of 2a, and the row that shows `Blocks` and `Declines` are genuinely
    /// two different answers from the SAME constructor. Comparing a bare process variable
    /// has no `eval_cmp_order` arm and is not a collection, so the host must abstain — it
    /// must NOT report the `false` that `_ => None` used to be read as.
    #[test]
    fn eq_on_an_undecidable_shape_declines_rather_than_blocks() {
        let guard = Proc::Eq(Arc::new(Proc::PZero), Arc::new(int_lit(0)));
        assert_eq!(
            eval_guard_disposition(&guard),
            GuardDisposition::Declines,
            "`Nil == 0` is not decided by any `eval_cmp_order` arm and is not a collection \
             comparison, so the host must DECLINE. Reporting `Blocks` here is exactly the \
             #33 defect: a missing evaluator arm masquerading as a false verdict."
        );
        assert_eq!(eval_guard_bool(&guard), None);
    }

    /// ── ROW 3: `Or(<separating>, true)` ★ THE B2 ROW ──
    ///
    /// Left-strict: the undecided left operand makes the whole disjunction DECLINE, even
    /// though the right operand is literally `true`.
    ///
    /// ★ This is precisely the row stage B2 proposed to change, by making the connectives
    /// Kleene so that `kleene_or(unknown, true) = true`. **The measurement says do not.**
    /// f1r3node evaluates BOTH operands of `EOr` unconditionally — the work-stack driver
    /// pushes `EBool(p2)` and `EBool(p1)` together before `Combine(EvKont::Or)`, and the
    /// recursive fallback binds `b1` and `b2` with `?` before combining — and
    /// `guard_passes` maps any `Err` or non-boolean result to `false`. So a Kleene host
    /// would FIRE where the machine does NOT: unsoundness in the firing direction, which is
    /// the worst kind. This test therefore pins the CURRENT, sound behaviour, and its
    /// failure would mean B2 was applied without re-doing that measurement.
    #[test]
    fn or_of_a_declining_left_and_true_declines_and_must_not_fire() {
        let guard = Proc::Or(Arc::new(separating_guard()), Arc::new(bool_lit(true)));
        assert_eq!(
            eval_guard_disposition(&guard),
            GuardDisposition::Declines,
            "a declining left operand must make `or` DECLINE, not fire. Firing here would \
             diverge from f1r3node, whose `EOr` evaluates both operands and whose \
             `guard_passes` turns the resulting error into `false`."
        );
        assert!(!eval_guard_disposition(&guard).fires());
        assert_eq!(eval_guard_bool(&guard), None);
    }

    /// The short-circuit discipline the `Option<bool>` original had implicitly, pinned
    /// explicitly so the refactor's inertness is checkable rather than asserted.
    ///
    /// `Some(eval(a)? && eval(b)?)` is left-strict then short-circuiting, so a decided-FALSE
    /// left operand settles `and` WITHOUT looking at the right — `false and <undecided>` is
    /// `Blocks`, not `Declines`. The dual holds for `or`, and `implies` inherits it through
    /// `¬a ∨ b`.
    #[test]
    fn the_connectives_keep_their_original_short_circuit_discipline() {
        let undecided = separating_guard();

        let and_false = Proc::And(Arc::new(bool_lit(false)), Arc::new(undecided.clone()));
        assert_eq!(
            eval_guard_disposition(&and_false),
            GuardDisposition::Blocks,
            "`false and ?` is settled by the left operand alone"
        );

        let or_true = Proc::Or(Arc::new(bool_lit(true)), Arc::new(undecided.clone()));
        assert_eq!(
            eval_guard_disposition(&or_true),
            GuardDisposition::Fires,
            "`true or ?` is settled by the left operand alone"
        );

        let implies_false = Proc::Implies(Arc::new(bool_lit(false)), Arc::new(undecided.clone()));
        assert_eq!(
            eval_guard_disposition(&implies_false),
            GuardDisposition::Fires,
            "`false implies ?` is vacuously true, settled by the antecedent alone"
        );

        // …and the cases the left operand does NOT settle still propagate the decline.
        let and_true = Proc::And(Arc::new(bool_lit(true)), Arc::new(undecided.clone()));
        assert_eq!(eval_guard_disposition(&and_true), GuardDisposition::Declines);
        let or_false = Proc::Or(Arc::new(bool_lit(false)), Arc::new(undecided.clone()));
        assert_eq!(eval_guard_disposition(&or_false), GuardDisposition::Declines);
        let implies_true = Proc::Implies(Arc::new(bool_lit(true)), Arc::new(undecided));
        assert_eq!(eval_guard_disposition(&implies_true), GuardDisposition::Declines);
    }

    /// `Not` is three-valued: negating an abstention is still an abstention. A `Declines`
    /// that flipped to a verdict under `not` would let the defect manufacture one.
    #[test]
    fn negation_is_three_valued() {
        assert_eq!(
            eval_guard_disposition(&Proc::Not(Arc::new(separating_guard()))),
            GuardDisposition::Declines,
            "`not ?` is `?`"
        );
        assert_eq!(
            eval_guard_disposition(&Proc::Not(Arc::new(bool_lit(true)))),
            GuardDisposition::Blocks
        );
        assert_eq!(
            eval_guard_disposition(&Proc::Not(Arc::new(bool_lit(false)))),
            GuardDisposition::Fires
        );
    }

    /// The projection is total and lossless in the `Option<bool>` direction, which is what
    /// lets `eval_guard_bool` keep serving `guard_discharge::classify` unchanged.
    #[test]
    fn the_legacy_projection_round_trips() {
        for d in [GuardDisposition::Fires, GuardDisposition::Blocks, GuardDisposition::Declines] {
            assert_eq!(GuardDisposition::from_verdict(d.verdict()), d);
        }
        assert_eq!(GuardDisposition::from_decided(true), GuardDisposition::Fires);
        assert_eq!(GuardDisposition::from_decided(false), GuardDisposition::Blocks);
        assert!(GuardDisposition::Fires.fires());
        assert!(!GuardDisposition::Blocks.fires());
        assert!(!GuardDisposition::Declines.fires());
    }
}

#[cfg(test)]
mod comm_tests {
    use super::*;
    use crate::rhocalc::runtime::merge_pp_parallel;

    fn to_ppar(parsed: Proc) -> Proc {
        // `Proc` is `Drop`; match by reference and clone the `Arc`-wrapped children.
        match &parsed {
            Proc::PParInfix(a, b) => merge_pp_parallel((**a).clone(), (**b).clone()),
            _ => parsed,
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
        Proc::CastInt(std::sync::Arc::new(Int::NumLit(n)))
    }

    fn path_key(segments: &[i64]) -> Proc {
        Proc::CastList(std::sync::Arc::new(List::ListLit(
            segments.iter().copied().map(int).collect(),
        )))
    }

    fn pathmap_with_value(key: Proc, val: Proc) -> PathMapLit<Proc, Proc> {
        let mut lit = PathMapLit::new();
        lit.insert(key, val);
        lit
    }

    fn read_zipper_proc(lit: PathMapLit<Proc, Proc>, focus: Vec<u8>) -> Proc {
        Proc::CastReadZipper(std::sync::Arc::new(ReadZipper::Lit(std::sync::Arc::new(
            ReadZipperLit(lit, focus),
        ))))
    }

    fn write_zipper_proc(lit: PathMapLit<Proc, Proc>, focus: Vec<u8>) -> Proc {
        Proc::CastWriteZipper(std::sync::Arc::new(WriteZipper::Lit(std::sync::Arc::new(
            WriteZipperLit(lit, focus),
        ))))
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
