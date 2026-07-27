//! Systematic test suite for the RhoCalc language.
//!
//! Organized by feature area:
//! - **comm**: Communication (single-input, multi-input, join patterns)
//! - **new_and_extrusion**: PNew binder and scope extrusion equation
//! - **congruence**: Rewrite propagation through constructors
//! - **native_ops**: Embedded Rust-native arithmetic, booleans, strings
//! - **parsing**: Basic parsing and round-trip tests
//! - **beta**: Lambda/dollar-syntax beta-reduction

use mettail_languages::rhocalc::*;
use mettail_runtime::Language;

// ════════════════════════════════════════════════════════════════════════════════
// Test helpers
// ════════════════════════════════════════════════════════════════════════════════

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{}`: {}", input, e))
}

fn fresh() {
    mettail_runtime::clear_var_cache();
}

// ════════════════════════════════════════════════════════════════════════════════
// ForRow F3 `&`-join pin helpers (2026-06-28)
// ════════════════════════════════════════════════════════════════════════════════
//
// The F3 symmetric projection-suppression gate fixes the F2 multiplicative
// (`2^N`) `&`-join cursor-frontier explosion (root cause: the InputBind LHS of
// a `&`-join was parsed by BOTH a CrossCatProjection delegate and a CrossCatLhs
// EXTENSION delegate, each `@a<-a` being independently 2-way ambiguous). These
// helpers run a parse on a worker thread under a HARD wall-clock bound so a
// regression of that explosion surfaces as a FAST test failure instead of
// hanging the whole suite. Assertions are on the derived `Debug` (positive AST)
// — never `Display` — and every pin parses TWICE to pin determinism.

/// Run `body` on a worker thread, failing fast if it does not complete within
/// 30s (the F3 anti-hang guard). A panic inside `body` is re-surfaced on the
/// test thread; a timeout is the multiplicative-ambiguity tripwire.
fn run_within_30s<T: Send + 'static>(label: &str, body: impl FnOnce() -> T + Send + 'static) -> T {
    use std::sync::mpsc;
    use std::time::Duration;
    let (tx, rx) = mpsc::channel();
    let handle = std::thread::Builder::new()
        .name("forrow-f3-pin".into())
        .spawn(move || {
            let _ = tx.send(body());
        })
        .expect("spawn forrow-f3-pin worker thread");
    match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(value) => {
            let _ = handle.join();
            value
        },
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "`{}` did not finish within 30s — F3 multiplicative-ambiguity \
             (`&`-join projection-vs-extension) regression",
            label
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => match handle.join() {
            Ok(()) => panic!("`{}`: worker thread disconnected without a result", label),
            Err(panic_payload) => std::panic::resume_unwind(panic_payload),
        },
    }
}

/// Canonicalize the monotonic fresh-variable ids in a derived-`Debug` AST
/// rendering so two parses of the same source are structurally comparable.
/// `clear_var_cache()` resets the name→id MAP but not the process-global
/// monotonic id COUNTER, so successive parses embed `UniqueId(0)` vs
/// `UniqueId(101)` etc. for the same variable. Replacing every
/// `UniqueId(<digits>)` with `UniqueId(_)` isolates GENUINE parser
/// non-determinism (structure) from benign id allocation — while still
/// asserting on derived `Debug` (the positive AST), never `Display`.
fn normalize_var_ids(debug: &str) -> String {
    const MARK: &str = "UniqueId(";
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(idx) = rest.find(MARK) {
        out.push_str(&rest[..idx]);
        out.push_str(MARK);
        out.push('_');
        rest = &rest[idx + MARK.len()..];
        let after_digits = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        rest = &rest[after_digits..];
    }
    out.push_str(rest);
    out
}

/// Parse a bare `ForRow` surface string under the F3 anti-hang guard. Returns
/// `(debug, nowhere_bind_count)` where `nowhere_bind_count` is `Some(n)` iff
/// the parse is a `ForRowNoWhere` with `n` total binds (`b` + `bs`), else
/// `None`. `debug` is the derived `Debug` rendering with fresh-var ids
/// canonicalized (used for parse-twice determinism comparison — NOT `Display`).
fn parse_forrow_fast(input: &str) -> (String, Option<usize>) {
    let owned = input.to_string();
    let outcome: Result<(String, Option<usize>), String> = run_within_30s(input, move || {
        // Match the `forrow_parse_determinism` proptest convention; the
        // monotonic id counter still advances across parses, so the Debug is
        // canonicalized via `normalize_var_ids` below.
        mettail_runtime::clear_var_cache();
        ForRow::parse(&owned)
            .map(|forrow| {
                let debug = normalize_var_ids(&format!("{:?}", forrow));
                let binds = match forrow {
                    ForRow::ForRowNoWhere(_, ref bs) => Some(bs.len() + 1),
                    _ => None,
                };
                (debug, binds)
            })
            .map_err(|e| format!("{}", e))
    });
    outcome.unwrap_or_else(|e| panic!("ForRow::parse failed for `{}`: {}", input, e))
}

/// Parse a full `Proc` surface string (e.g. the `for(@a<-a & …){Nil}` hang
/// repro) under the F3 anti-hang guard, returning its derived `Debug`.
fn parse_proc_fast(input: &str) -> String {
    let owned = input.to_string();
    let outcome: Result<String, String> = run_within_30s(input, move || {
        // See `parse_forrow_fast`: clear the name→id map, then canonicalize
        // the monotonic ids so the derived-Debug AST is comparable across parses.
        mettail_runtime::clear_var_cache();
        Proc::parse(&owned)
            .map(|proc_term| normalize_var_ids(&format!("{:?}", proc_term)))
            .map_err(|e| format!("{}", e))
    });
    outcome.unwrap_or_else(|e| panic!("Proc::parse failed for `{}`: {}", input, e))
}

// ════════════════════════════════════════════════════════════════════════════════
// Path-B test oracle (replaces the retired `run_ascent` reference reducer)
// ════════════════════════════════════════════════════════════════════════════════
//
// `run_ascent` (main's f1r3node-independent reference reducer) is fail-closed on this
// branch. This module re-derives the same `AscentResults` shape the assert helpers
// expect by driving a BOUNDED fixpoint over the WORKING reduction primitives — the
// runtime stays the Rho machine; only the TEST ORACLE changes:
//
//   • COMM      — `Proc::try_comm_once()` → `receive::try_comm_rw_proc` (single/persistent/
//                 where/empty/`;`-rows/polyadic/patterns), made congruence-aware under `PNew`.
//   • non-COMM  — `RhoCalcLanguage::dovetail_normal_term` (native folds, casts, `Exec`/drop,
//                 `QuoteDrop`, congruence) — the same Dovetail normalizer used elsewhere.
//   • AMBIGUITY — `parse_term` returns an `Ambiguous` wrapper of alternative `Proc`s (the WPDA
//                 preserves parse ambiguity). Each Proc alternative is seeded and reduced; the
//                 union of reachable normal forms is reported (so all-alternatives assertions hold).
//
// Both reducers run in ONE fixpoint with a STEP BOUND (persistent `<=`/`!!` loops would
// otherwise diverge). The disambiguated `Proc` arithmetic form (`1 + 2` ⇒ `@Nil!(1) + @Nil!(2)`)
// does not constant-fold, so the whole-box Dovetail normal form is ALSO seeded — that branch
// folds the WPDA-typed (e.g. `Int`) alternative the single disambiguated `Proc` cannot.
mod oracle {
    use super::Proc;
    use mettail_languages::rhocalc::{RhoCalcLanguage, RhoCalcTerm, RhoCalcTermInner};
    use mettail_runtime::{AscentResults, Language, Rewrite, TermInfo};
    use std::collections::{HashMap, VecDeque};
    use std::sync::Arc;

    /// Max successor edges explored per run. Bounds persistent `<=`/`!!` loops (each fire grows
    /// the term, so structural dedup never halts them — only this cap does). Generous: every
    /// terminating test settles in well under a dozen steps.
    const STEP_BOUND: usize = 512;
    const DOVETAIL_ITERS: usize = 256;
    const DOVETAIL_NODES: usize = 4_000_000;

    fn to_term(p: &Proc) -> RhoCalcTerm {
        RhoCalcTerm(RhoCalcTermInner::Proc(p.clone()))
    }

    fn proc_from_inner(inner: &RhoCalcTermInner) -> Option<Proc> {
        match inner {
            RhoCalcTermInner::Proc(p) => Some(p.clone()),
            _ => None,
        }
    }

    fn proc_from_term(term: &dyn mettail_runtime::Term) -> Option<Proc> {
        term.as_any()
            .downcast_ref::<RhoCalcTerm>()
            .and_then(|t| proc_from_inner(&t.0))
    }

    /// Flatten the (flat) `Ambiguous` wrapper, collecting the `Proc`-category alternatives.
    fn collect_proc_alts(inner: &RhoCalcTermInner, out: &mut Vec<Proc>) {
        match inner {
            RhoCalcTermInner::Proc(p) => out.push(p.clone()),
            RhoCalcTermInner::Ambiguous(alts) => {
                for a in alts {
                    collect_proc_alts(a, out);
                }
            },
            _ => {},
        }
    }

    /// Recursively collapse a single-element PPar `{P}` to `P` (parallel-composition identity),
    /// so COMM residuals and nested-`new` bodies match the un-wrapped `expected` displays.
    fn canon(p: &Proc) -> Proc {
        match p {
            Proc::PPar(bag) => {
                let mut out = mettail_runtime::HashBag::new();
                for (elem, count) in bag.iter() {
                    let c = canon(elem);
                    for _ in 0..count {
                        Proc::insert_into_ppar(&mut out, c.clone());
                    }
                }
                if let Some((only, 1)) = out.iter().next() {
                    if out.len() == 1 {
                        return only.clone();
                    }
                }
                Proc::PPar(out)
            },
            Proc::PNew(scope) => {
                let (binders, body) = scope.clone().unbind();
                Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(canon(&body))))
            },
            _ => p.clone(),
        }
    }

    /// dovetail-normalize a `Proc` (folds/casts/`Exec`/drop). `None` on Dovetail `Err`
    /// (stuck reconstruction — e.g. a term still containing an un-fired COMM) or a non-`Proc` result.
    fn dovetail_proc(p: &Proc) -> Option<Proc> {
        let term = to_term(p);
        match RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES) {
            Ok(nf) => proc_from_term(nf.as_ref()),
            Err(_) => None,
        }
    }

    /// One COMM step anywhere: top-level `PPar`, else recurse into a `PNew` body (the `NewCong`
    /// congruence rule), rebuilding the binder so COMM under `new` fires while the scope is kept;
    /// else SCOPE-EXTRUDE and retry (the `Extrude` equation).
    fn try_comm_anywhere(p: &Proc) -> Option<Proc> {
        if let Some(c) = p.try_comm_once() {
            return Some(c);
        }
        if let Proc::PNew(scope) = p {
            let (binders, body) = scope.clone().unbind();
            if let Some(b2) = try_comm_anywhere(&body) {
                return Some(Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(b2))));
            }
        }
        try_extruded_comm(p)
    }

    /// The `Extrude` EQUATION, applied left-to-right when — and only when — it unblocks a COMM:
    ///
    /// ```text
    /// Extrude . xs.*map(|x| x # ...rest)
    ///     |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest})) ;
    /// ```
    ///
    /// `try_comm_once` only inspects the top-level `PPar`, so a receive nested under a `new` can
    /// never meet a send that sits OUTSIDE that `new` unless the scope is extruded first —
    /// `new x in { for(z <- a){*z} } | a!(0)` rested as a normal form even though `a` is free on
    /// both sides. Dovetail *does* carry the equation, but it only ever reports ONE extracted
    /// normal form and COMM is not one of its rules, so the extruded form was never handed back
    /// to the COMM step. This closes that gap in the oracle rather than in the language.
    ///
    /// The freshness side condition `xs # rest` is checked, not assumed: `Scope::new` BINDS every
    /// free occurrence of a binder inside the term it closes, and `unbind` re-opens bound
    /// variables as FRESH free variables. So closing `rest` over `binders` and re-opening it is
    /// the identity **iff** nothing was captured. `new a in { for(z <- a){*z} } | a!(0)` (the
    /// `extrusion_blocked_when_not_fresh` pin) fails that check and is left alone.
    fn try_extruded_comm(p: &Proc) -> Option<Proc> {
        // The surface `P | Q` parses as `PParInfix`, which only becomes a `PPar` bag once its
        // `merge_pp_parallel` fold has fired; accept both spellings so extrusion does not depend
        // on which one the extractor happened to surface.
        let bag = match p {
            Proc::PPar(bag) => bag.clone(),
            Proc::PParInfix(left, right) => {
                let mut bag = mettail_runtime::HashBag::new();
                Proc::insert_into_ppar(&mut bag, (**left).clone());
                Proc::insert_into_ppar(&mut bag, (**right).clone());
                bag
            },
            _ => return None,
        };
        let bag = &bag;
        for (target, _) in bag.iter() {
            let Proc::PNew(scope) = target else {
                continue;
            };
            // `rest` = the par with ONE occurrence of this `new` removed.
            let mut rest_bag = mettail_runtime::HashBag::new();
            for (element, count) in bag.iter() {
                let keep = if element.term_eq(target) {
                    count - 1
                } else {
                    count
                };
                for _ in 0..keep {
                    Proc::insert_into_ppar(&mut rest_bag, element.clone());
                }
            }
            if rest_bag.is_empty() {
                continue;
            }
            let rest = canon(&Proc::PPar(rest_bag.clone()));
            let (binders, body) = scope.clone().unbind();
            // Freshness: closing `rest` over the binders must capture nothing.
            let probe = mettail_runtime::Scope::new(binders.clone(), Arc::new(rest.clone()));
            let (_, reopened) = probe.unbind();
            if !reopened.term_eq(&rest) {
                continue;
            }
            let mut inner = rest_bag;
            Proc::insert_into_ppar(&mut inner, (*body).clone());
            let extruded = canon(&Proc::PPar(inner));
            if let Some(next) = try_comm_anywhere(&extruded) {
                return Some(Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(next))));
            }
        }
        None
    }

    /// One NON-COMM normalize move (folds/casts/drop), `PNew`-aware: recurse into the body and
    /// preserve the ORIGINAL binders — so the result displays as `new x in { … }` rather than
    /// Dovetail's freshly-reconstructed `new _ in { … }` (FIX-A erases binder identity).
    fn normalize_anywhere(p: &Proc) -> Option<Proc> {
        if let Proc::PNew(scope) = p {
            let (binders, body) = scope.clone().unbind();
            let b2 = normalize_anywhere(&body)?;
            // No real reduction inside the scope ⇒ no move (avoids a spurious self-rewrite from the
            // unbind→rebind round-trip, which would otherwise break `assert_no_rewrites`).
            if b2.term_eq(&body) {
                return None;
            }
            return Some(Proc::PNew(mettail_runtime::Scope::new(binders, Arc::new(b2))));
        }
        dovetail_proc(p)
    }

    /// Reduction-graph builder. Nodes are deduped by canonical display; each node optionally
    /// carries its `Proc` (display-only nodes — e.g. a scalar Dovetail normal form — are terminal).
    struct Builder {
        procs: Vec<Option<Proc>>,
        displays: Vec<String>,
        is_nf: Vec<bool>,
        expanded: Vec<bool>,
        by_display: HashMap<String, usize>,
        edges: Vec<(usize, usize)>,
    }

    impl Builder {
        fn new() -> Self {
            Self {
                procs: Vec::new(),
                displays: Vec::new(),
                is_nf: Vec::new(),
                expanded: Vec::new(),
                by_display: HashMap::new(),
                edges: Vec::new(),
            }
        }

        fn intern_proc(&mut self, p: &Proc) -> usize {
            let d = p.to_string();
            if let Some(&i) = self.by_display.get(&d) {
                return i;
            }
            let i = self.procs.len();
            self.procs.push(Some(p.clone()));
            self.displays.push(d.clone());
            self.is_nf.push(false);
            self.expanded.push(false);
            self.by_display.insert(d, i);
            i
        }

        /// A terminal display-only node (no further reduction): used for a scalar/string Dovetail
        /// normal form whose runtime category is not `Proc`.
        fn intern_terminal_display(&mut self, d: String) -> usize {
            if let Some(&i) = self.by_display.get(&d) {
                return i;
            }
            let i = self.procs.len();
            self.procs.push(None);
            self.displays.push(d.clone());
            self.is_nf.push(true);
            self.expanded.push(true);
            self.by_display.insert(d, i);
            i
        }

        fn add_edge(&mut self, from: usize, to: usize) {
            if from != to && !self.edges.contains(&(from, to)) {
                self.edges.push((from, to));
            }
        }
    }

    /// Drive the bounded fixpoint from `input`, synthesizing the `AscentResults` the assert
    /// helpers consume, plus the initial term id (the root node).
    pub fn run_fixpoint(input: &str) -> (AscentResults, u64) {
        let lang = RhoCalcLanguage;
        let box0 = lang
            .parse_term(input)
            .unwrap_or_else(|e| panic!("parse `{}`: {}", input, e));

        let mut proc_alts: Vec<Proc> = Vec::new();
        if let Some(t) = box0.as_any().downcast_ref::<RhoCalcTerm>() {
            collect_proc_alts(&t.0, &mut proc_alts);
        }

        let mut b = Builder::new();
        let mut queue: VecDeque<usize> = VecDeque::new();

        // Root = first Proc alternative (the term the assert helpers seed from). If the parse has
        // no Proc-category alternative (a pure scalar), root is a display-only node from the box.
        let root = match proc_alts.first() {
            Some(p0) => {
                let r = b.intern_proc(&canon(p0));
                queue.push_back(r);
                r
            },
            None => b.intern_terminal_display(box0.to_string()),
        };

        // Remaining ambiguity alternatives are reachable from the root (ambiguity-preserving):
        // assertions that scan ALL alternatives (`all_terms`) then see every parse.
        for p in proc_alts.iter().skip(1) {
            let ci = b.intern_proc(&canon(p));
            b.add_edge(root, ci);
            queue.push_back(ci);
        }

        // Whole-box Dovetail normal form. The single disambiguated `Proc` form of bare arithmetic
        // (`@Nil!(1) + @Nil!(2)`) does not fold; dovetailing the whole (possibly `Ambiguous`) box
        // folds the WPDA-typed alternative. Seeded as a reachable normal form of the root.
        //
        // Skipped when the root is a `PNew`: Dovetail reconstructs `new` with a FRESH binder
        // (`new(_)`), so its result is only α-equivalent (not display-equal) to the binder-preserving
        // `normalize_anywhere` form. The proc-fixpoint already covers `PNew` reductions faithfully, so
        // seeding the renamed box form would only add a duplicate (and a spurious rewrite edge).
        let root_is_pnew = matches!(&b.procs[root], Some(Proc::PNew(_)));
        if !root_is_pnew {
            if let Ok(nf) =
                RhoCalcLanguage::dovetail_normal_term(box0.as_ref(), DOVETAIL_ITERS, DOVETAIL_NODES)
            {
                match proc_from_term(nf.as_ref()).map(|p| canon(&p)) {
                    Some(np) => {
                        let progress = match &b.procs[root] {
                            Some(rp) => !np.term_eq(rp),
                            None => np.to_string() != b.displays[root],
                        };
                        if progress {
                            let bi = b.intern_proc(&np);
                            b.add_edge(root, bi);
                            queue.push_back(bi);
                        }
                    },
                    None => {
                        let d = nf.to_string();
                        if d != b.displays[root] {
                            let bi = b.intern_terminal_display(d);
                            b.add_edge(root, bi);
                        }
                    },
                }
            }
        }

        let mut steps = 0usize;
        while let Some(idx) = queue.pop_front() {
            if b.expanded[idx] {
                continue;
            }
            b.expanded[idx] = true;
            if steps >= STEP_BOUND {
                continue;
            }
            let p = match &b.procs[idx] {
                Some(p) => p.clone(),
                None => {
                    b.is_nf[idx] = true;
                    continue;
                },
            };
            let mut succ: Vec<Proc> = Vec::new();
            if let Some(c) = try_comm_anywhere(&p) {
                let c = canon(&c);
                if !c.term_eq(&p) {
                    succ.push(c);
                }
            }
            if let Some(n) = normalize_anywhere(&p) {
                let n = canon(&n);
                if !n.term_eq(&p) {
                    succ.push(n);
                }
            }
            b.is_nf[idx] = succ.is_empty();
            for s in succ {
                steps += 1;
                let sidx = b.intern_proc(&s);
                b.add_edge(idx, sidx);
                if !b.expanded[sidx] {
                    queue.push_back(sidx);
                }
            }
        }

        let all_terms = (0..b.procs.len())
            .map(|i| TermInfo {
                term_id: i as u64,
                exact_key: None,
                display: b.displays[i].clone(),
                is_normal_form: b.is_nf[i],
            })
            .collect();
        let rewrites = b
            .edges
            .iter()
            .map(|&(f, t)| Rewrite {
                from_id: f as u64,
                to_id: t as u64,
                from_key: None,
                to_key: None,
                rule_name: None,
            })
            .collect();
        let results = AscentResults {
            all_terms,
            rewrites,
            equivalences: Vec::new(),
            custom_relations: HashMap::new(),
        };
        (results, root as u64)
    }
}

fn run(input: &str) -> mettail_runtime::AscentResults {
    fresh();
    oracle::run_fixpoint(input).0
}

/// Stage 4 (Lever-1, "emit-both" delimiter precedence): the Pathmap KV-literal
/// **close residuals**. The Pathmap close `|}` is a lattice-prefix collision
/// with the `PParInfix` `|` operator, so the kv value's `InfixLoop` greedily
/// forked the operator and pre-empted the no-candidate `Advance(Unwinding)`
/// fall-through — the value never popped to the `CollectionMarker` and the close
/// never resumed. The InfixLoop emit-both yield (driven by the innermost-frame
/// `FrameCtx`) re-adds that yield ALONGSIDE the operator fork, so the value pops
/// and the close consumes. These inputs FAILED to parse before Stage 4.
///
/// (The whitespace-free `{|1:2|}` exercises the `|}`/`|` lattice ambiguity at the
/// close directly; `*@{|1:2|}` exercises it under a `PDrop` of a quoted Pathmap;
/// the list-key form exercises a cross-category key.)
#[test]
fn pathmap_kv_literal_close_residual_parses() {
    fresh();
    let lang = RhoCalcLanguage;
    // Pathmap literals now display with their DECLARED `{| |}` delimiters
    // (display.rs auto-literal arm fix, 2026-06-30) — previously they
    // mis-displayed with Map's `{ }` because `PathMapLit::fmt` delegated to
    // `HashMapLit::fmt`, an asymmetric parse(`{|…|}`)→display(`{…}`) bug.
    for (input, expect) in [
        ("{|1:2|}", "{|1:2|}"),
        ("{| 1:2 |}", "{|1:2|}"),
        ("{|[\"k\"]:1|}", "{|[\"k\"]:1|}"),
        ("*@{|1:2|}", "*@{|1:2|}"),
    ] {
        let term = lang.parse_term(input).unwrap_or_else(|e| {
            panic!("Stage-4 emit-both residual `{}` should parse: {}", input, e)
        });
        assert_eq!(
            term.to_string(),
            expect,
            "parsed Pathmap KV literal `{}` should display as `{}`",
            input,
            expect
        );
    }
}

fn run_with_initial(input: &str) -> (mettail_runtime::AscentResults, u64) {
    fresh();
    oracle::run_fixpoint(input)
}

fn normal_form_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
}

fn reachable_normal_form_displays(
    results: &mettail_runtime::AscentResults,
    initial_id: u64,
) -> Vec<String> {
    let mut out = Vec::new();
    let mut visited = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::from([initial_id]);
    visited.insert(initial_id);

    while let Some(id) = queue.pop_front() {
        if let Some(term) = results.all_terms.iter().find(|t| t.term_id == id) {
            if term.is_normal_form {
                out.push(term.display.clone());
                continue;
            }
        }
        for rw in results.rewrites.iter().filter(|rw| rw.from_id == id) {
            if visited.insert(rw.to_id) {
                queue.push_back(rw.to_id);
            }
        }
    }
    out
}

/// Assert that running `input` produces at least one normal form matching `expected`.
/// Comparison is by display string, handling PPar multiset ordering.
///
/// Every disjunct below must be a *decidable* comparison that answers `false` when it does not
/// apply — see the ⚠ note on [`bag_multiset_eq`] for the vacuity this helper used to inherit, and
/// [`comparator_integrity`] for the tests that pin the guarantee.
fn assert_reduces_to(input: &str, expected: &str) {
    let (results, initial_id) = run_with_initial(input);
    let nfs = reachable_normal_form_displays(&results, initial_id);

    // Parse expected in a fresh var context so variable IDs don't collide.
    fresh();
    let expected_proc = parse(expected);
    let expected_display = expected_proc.to_string();
    let expected_singleton_par = format!("{{{}}}", expected_display);
    let expected_no_ws: String = expected_display
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let expected_singleton_par_no_ws: String = expected_singleton_par
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();

    let found = nfs.iter().any(|nf| {
        let nf_no_ws: String = nf.chars().filter(|c| !c.is_whitespace()).collect();
        nf == &expected_display
            || nf == &expected_singleton_par
            || nf_no_ws == expected_no_ws
            || nf_no_ws == expected_singleton_par_no_ws
            || multiset_eq(nf, &expected_display)
            || multiset_eq(nf, &expected_singleton_par)
            || bag_multiset_eq(nf, &expected_display)
            || bag_multiset_eq(nf, &expected_singleton_par)
    });

    assert!(
        found,
        "Expected `{input}` to reduce to `{expected}`\n  \
         expected (parsed, rendered): `{expected_display}`\n  \
         reachable normal forms ({}): {nfs:#?}",
        nfs.len(),
    );
}

/// Assert that `input` has a reachable normal form whose DISPLAY is EXACTLY `expected_display`
/// (whitespace-insensitively, and modulo the singleton-`{…}` par wrapper the oracle may keep).
///
/// # When to use this instead of [`assert_reduces_to`]
///
/// [`assert_reduces_to`] PARSES its `expected` argument and compares against the parsed term's
/// display. That is the right thing whenever the value has a RhoCalc source spelling that parses
/// back to itself — but a few normal forms do NOT:
///
/// | value | canonical display | what that string PARSES to |
/// |---|---|---|
/// | the rational ⅔ | `2/3` | `Div(BigInt 2, BigInt 3)` — a redex (`BigRat` literals are whole-number-only: `[0-9]+r`) |
/// | the fixed-point −10.0 at scale 1 | `-10.0p1` | `NegProc(Fixed 10.0p1)` — a redex |
///
/// For those, this helper asserts the display EXACTLY, which is strictly stronger than
/// `assert_reduces_to`'s disjunction (no multiset/bag tolerance, no parse round-trip). The
/// display/parse asymmetry itself is a separate, real defect — recorded, not papered over.
fn assert_normal_form_display(input: &str, expected_display: &str) {
    let (results, initial_id) = run_with_initial(input);
    let nfs = reachable_normal_form_displays(&results, initial_id);
    let want: String = expected_display
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let want_singleton_par = format!("{{{}}}", want);
    let found = nfs.iter().any(|nf| {
        let got: String = nf.chars().filter(|c| !c.is_whitespace()).collect();
        got == want || got == want_singleton_par
    });
    assert!(
        found,
        "Expected `{input}` to have a normal form displaying exactly as `{expected_display}`\n  \
         reachable normal forms ({}): {nfs:#?}",
        nfs.len(),
    );
}

/// Assert that running `input` produces at least `min` rewrites.
fn assert_min_rewrites(input: &str, min: usize) {
    let results = run(input);
    assert!(
        results.rewrites.len() >= min,
        "`{}`: expected >= {} rewrites, got {}",
        input,
        min,
        results.rewrites.len()
    );
}

/// Assert that running `input` produces zero rewrites (already a normal form).
fn assert_no_rewrites(input: &str) {
    let results = run(input);
    assert!(
        results.rewrites.is_empty(),
        "`{}`: expected no rewrites, got {}",
        input,
        results.rewrites.len()
    );
}

/// Assert that no rewrite chain starting from the initial term reaches a term
/// whose display is `forbidden`. Subterms that appear in `all_terms` purely as
/// exploration side-effects (e.g. HOL/native bottom-up scans) are ignored —
/// only terms reachable via the rewrite graph from the initial parse count.
fn assert_never_reaches(input: &str, forbidden: &str) {
    let (results, initial_id) = run_with_initial(input);
    let mut visited = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::from([initial_id]);
    visited.insert(initial_id);
    while let Some(id) = queue.pop_front() {
        if let Some(term) = results.all_terms.iter().find(|t| t.term_id == id) {
            assert!(
                term.display != forbidden,
                "`{}` unexpectedly reached `{}` via rewrites",
                input,
                forbidden
            );
        }
        for rw in results.rewrites.iter().filter(|rw| rw.from_id == id) {
            if visited.insert(rw.to_id) {
                queue.push_back(rw.to_id);
            }
        }
    }
}

/// Normalize a RhoCalc normal-form *display* to the bare surface the pre-merge
/// `.contains(..)` assertions were written against, undoing two WFST-branch
/// display conventions that are canonical here but were bare on `main`:
///
///   1. **Projection-surface numeric operands.** A numeric literal used as an
///      operator operand (`x > 1`) renders through its cross-category projection
///      surface as `@Nil!(1)` (documented in the `oracle` module header:
///      `1 + 2 ⇒ @Nil!(1) + @Nil!(2)`). The AST is the integer; the wrapper is a
///      Display-only, round-trip-stable rendering. We strip `@Nil!(<int>)` back
///      to `<int>` so `x > 1` matches `x > @Nil!(1)`.
///   2. **Arity-list send payloads.** A scalar send `c!!(p)` arity-normalizes its
///      payload to a one-element list `[p]` before COMM, so a *remaining*
///      persistent send displays as `c!!([p])` (the sibling test
///      `persistent_receive_with_persistent_send_keeps_both` already accepts
///      both `c!!([p])` and `c!!(p)`). We unwrap `!(<x>)` / `!([<x>])` and
///      `!!(<x>)` / `!!([<x>])` single-element payloads.
///
/// Both are display-format differences only — the reduction semantics (guard
/// fires/blocks, persistent send/receive remains) are verified structurally by
/// the surrounding assertions, so this is faithful normalization, not a
/// weakening of the checks.
fn canon_display(nf: &str) -> String {
    // (1) `@Nil!(<digits>)` → `<digits>`.
    let mut out = String::with_capacity(nf.len());
    let bytes = nf.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if nf[i..].starts_with("@Nil!(") {
            let rest = &nf[i + "@Nil!(".len()..];
            let digits_end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            if digits_end > 0 && rest[digits_end..].starts_with(')') {
                out.push_str(&rest[..digits_end]);
                i += "@Nil!(".len() + digits_end + 1; // consume through ')'
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    // (2) unwrap single-element list payloads `([x])` → `(x)` (covers `!` and `!!`).
    out.replace("([", "(").replace("])", ")")
}

/// True if any reachable normal form contains `needle` once BOTH the NF and the
/// needle are run through [`canon_display`] and stripped of whitespace.
fn any_nf_contains(nfs: &[String], needle: &str) -> bool {
    let n_needle: String = canon_display(needle)
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    nfs.iter().any(|nf| {
        let n_nf: String = canon_display(nf)
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        n_nf.contains(&n_needle)
    })
}

/// Assert that `input` has a rewrite from the initial term (not stuck).
fn assert_initial_rewrites(input: &str) {
    fresh();
    let (results, initial_id) = oracle::run_fixpoint(input);
    let from_initial = results.rewrites_from(initial_id);
    assert!(
        !from_initial.is_empty(),
        "`{}`: expected rewrites from initial term, but none found.\n  \
         Total rewrites in system: {}\n  \
         Normal forms: {:?}",
        input,
        results.rewrites.len(),
        normal_form_displays(&results),
    );
}

/// Compare two display strings as PPar multisets (handles HashBag ordering).
fn multiset_eq(a: &str, b: &str) -> bool {
    fn to_sorted_elements(s: &str) -> Option<Vec<String>> {
        let s = s.trim();
        if !s.starts_with('{') || !s.ends_with('}') {
            return None;
        }
        let inner = &s[1..s.len() - 1];
        let mut elems: Vec<String> = inner.split('|').map(|e| e.trim().to_string()).collect();
        elems.sort();
        Some(elems)
    }
    match (to_sorted_elements(a), to_sorted_elements(b)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// Compare bag literal displays as multisets (handles HashBag ordering), including singleton-par
/// wrappers.
///
/// # ⚠ This comparator was VACUOUS until 2026-07-25
///
/// The body used to be `to_sorted_bag_elements(a) == to_sorted_bag_elements(b)`. Both sides return
/// `None` whenever the string is not a `#{…}#` bag literal, and `None == None` is **`true`** — so
/// for every pair in which neither side is a bag literal (i.e. the overwhelming majority of this
/// file's assertions) the comparator answered `true` unconditionally. Because
/// [`assert_reduces_to`] reaches its verdict through a *disjunction* that ends in this call, the
/// whole assertion collapsed to `true`. Measured: `assert_reduces_to("1 + 2", "999")` **passed**.
///
/// The guarded form below is the same shape [`multiset_eq`] already used: a comparator that is not
/// *applicable* to its arguments must answer `false` (defer to the earlier disjuncts), never
/// `true` (assert nothing).
fn bag_multiset_eq(a: &str, b: &str) -> bool {
    fn unwrap_singleton_par(s: &str) -> &str {
        let t = s.trim();
        if t.starts_with('{') && t.ends_with('}') {
            &t[1..t.len() - 1]
        } else {
            t
        }
    }
    fn to_sorted_bag_elements(s: &str) -> Option<Vec<String>> {
        let t = unwrap_singleton_par(s).trim();
        if !t.starts_with("#{") || !t.ends_with("}#") {
            return None;
        }
        let inner = &t[2..t.len() - 2];
        let mut elems: Vec<String> = inner.split('|').map(|e| e.trim().to_string()).collect();
        elems.sort();
        Some(elems)
    }
    match (to_sorted_bag_elements(a), to_sorted_bag_elements(b)) {
        (Some(a), Some(b)) => a == b,
        // Not a bag on both sides ⇒ this comparator is INAPPLICABLE, which is not the same thing
        // as "equal". Answering `true` here is what made every non-bag assertion vacuous.
        _ => false,
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Numeric-literal CARRIER — ★ divergence I, CLOSED 2026-07-25
// ════════════════════════════════════════════════════════════════════════════════

/// The `Proc`-level cast the WPDA picks for a numeric literal is **a function of the literal**,
/// and of nothing else — not of parentheses, not of the enclosing collection, not of the parse
/// entry point.
///
/// ### What this module used to pin (`mod carrier_asymmetry`)
///
/// | source | parsed `Proc` (BEFORE) | carrier |
/// |---|---|---|
/// | `@1` | `NQuoteShort(CastBigInt(NumLit(1)))` | arbitrary precision |
/// | `@(1)` | `NQuoteShort(CastInt(NumLit(1)))` | fixed width `i64` |
/// | `5u32` | `CastBigInt(NumLit(5))` | arbitrary precision — the `u32` suffix reached no `UInt32` |
///
/// Because `+`, `==`, … are carrier-EXACT (and so is f1r3node's `combine_plus`,
/// `rholang/src/rust/interpreter/reduce.rs:3112` — no mixed `GInt`/`GBigInt` arm), that asymmetry
/// leaked into semantics: `*(@(1)) + 2` answered `error`, `[1,2,3].length() == 3` was false, and a
/// receive PATTERN and a send PAYLOAD written from *identical* source text could land in different
/// carriers and fail to unify. Four tests that only ever "passed" because `assert_reduces_to` was
/// vacuous were tripping over it: `congruence::add_cong`, `congruence::comparison_cong`,
/// `comm::pattern_comm_exact_constructor_pattern_matches`, `native_ops::bitwise::u32_and_or_not`.
///
/// ### Why the old ⚠ ("the fix belongs in the WPDA cross-category projection") was half wrong
///
/// The election machinery behaved exactly as specified. What it was electing *between* was a set of
/// readings **the grammar should never have admitted**: `BigInt`'s `eval` was
/// `parse_int_lit(text, None)`, a universal acceptor of every integer spelling, contradicting its
/// own declared mandatory `…n` tail — so `CastBigInt` was a live reading of EVERY numeral and won
/// the lex-min tiebreak by grammar DECLARATION ORDER. Honouring never-disambiguate-early did not
/// require touching the tiebreak; it required making the evidence discriminate. The fix is in
/// `languages/src/rhocalc.rs`: the integer literal domains now PARTITION (`Int` = every ≤`i64`
/// spelling without an `n`; `BigInt` = exactly `…n`, plus unsuffixed values too big for `i64`;
/// `UInt32` = no literal surface at all), and `CastInt` is declared before `CastBigInt` so the
/// direct `Int ▸ Proc` projection — rather than the auto-injected `Int ▸ BigInt ▸ Proc` promotion
/// chain — is canonical at every election site.
///
/// The carrier assignment is f1r3node's: `normalize_ground` (`ground_normalize_matcher.rs:14-50`)
/// maps a bare numeral, `…i32`, `…i64` and `…u32` (≤ `i64::MAX`) to `GInt`, and only `…n` to
/// `GBigInt`.
mod numeral_carrier_is_context_independent {
    use super::*;

    /// Parenthesizing a numeral does not change which numeric category it lands in.
    ///
    /// ★ RE-BASELINED 2026-07-25 (#28 / G3), and this is the golden the tracked-item
    /// description did not predict. It is a TERM-SHAPE pin on a PRODUCTION-CONSUMED path
    /// — `parse_term` is the ambiguity-preserving box the reduction oracle and the
    /// AST-first lowering both consume — so its movement is worth more attention than a
    /// reading COUNT moving.
    ///
    /// Both spellings now come back as `Ambiguous([..])` rather than a single term,
    /// because closing G3 stopped the projection facade from dropping the
    /// transparent-grouping twin at the `_all` enumeration seam. `*(@1) + 2` gains
    /// `Add(PDrop(NQuoteShort(1)), 2)` alongside the `NParen`-kept reading it already had.
    ///
    /// ★ THE PROPERTY UNDER TEST IS UNCHANGED AND IS WHAT THE ASSERTIONS NOW SAY
    /// DIRECTLY. The claim was never "this surface has exactly one reading"; it was "the
    /// numeral's CARRIER does not depend on the syntax around it" (divergence I). So each
    /// spelling is asserted the way the claim is actually stated: every reading it admits
    /// carries `CastInt`, and none carries `CastBigInt`. That is strictly stronger than
    /// the old single-`Debug`-string pin, which would have been satisfied by one reading
    /// while a sibling reading silently carried the wrong type — and it no longer breaks
    /// when an unrelated change adds or removes a structurally-distinct twin.
    ///
    /// The exact reading sets are pinned underneath, so genuine drift is still caught.
    #[test]
    fn numeral_carrier_is_independent_of_parentheses() {
        // The two spellings that differ by exactly one pair of parentheses.
        for (source, expected_readings) in [
            (
                "*(@1) + 2",
                &[
                    "Add(PDrop(NParen(NQuoteShort(CastInt(NumLit(1))))), CastInt(NumLit(2)))",
                    "Add(PDrop(NQuoteShort(CastInt(NumLit(1)))), CastInt(NumLit(2)))",
                ][..],
            ),
            (
                // `NQuote` as well as `NQuoteShort`: `@(1)` elects the rule that LITERALLY
                // spells `"@" "(" p ")"`, which is what `NQuoteShort`'s own doc says should
                // happen ("more specific rules above continue to win where applicable").
                // The two are semantically identical — `NQuoteShort` is a `fold` whose body
                // is `Name::NQuote(p)` — so their coexistence is a structural-faithfulness
                // matter, not a meaning change. What matters HERE is the carrier.
                // Two readings, not three: `semantic_hash` folds the sugar≡canonical
                // alias `NQuoteShort` ≡ `NQuote`, so the facade's `NParen(NQuote(1))`
                // and the walker's `NParen(NQuoteShort(1))` share ONE semantic key and
                // the union keeps a single representative of that class.
                "*(@(1)) + 2",
                &[
                    "Add(PDrop(NParen(NQuote(CastInt(NumLit(1))))), CastInt(NumLit(2)))",
                    "Add(PDrop(NQuoteShort(CastInt(NumLit(1)))), CastInt(NumLit(2)))",
                ][..],
            ),
        ] {
            fresh();
            let parsed = RhoCalcLanguage
                .parse_term(source)
                .expect("the source parses");
            let rendered = format!("{parsed:?}");

            // ★ THE PROPERTY: the carrier is `CastInt` in EVERY reading, never `CastBigInt`.
            assert!(
                rendered.contains("CastInt(NumLit(1))"),
                "{source}: the numeral must take the `GInt` carrier `normalize_ground` \
                 gives it, in {rendered}"
            );
            assert!(
                !rendered.contains("CastBigInt"),
                "{source}: NO reading may put the numeral in the arbitrary-precision \
                 carrier — that is divergence I, and it must stay closed for every \
                 reading, not merely for the elected one. Got {rendered}"
            );

            // The exact reading set, so genuine drift is still caught.
            for reading in expected_readings {
                assert!(
                    rendered.contains(reading),
                    "{source}: expected reading {reading} missing from {rendered}"
                );
            }
            let comma_separated_readings = rendered.matches("Add(PDrop(").count();
            assert_eq!(
                comma_separated_readings,
                expected_readings.len(),
                "{source}: expected exactly {} readings, got {rendered}",
                expected_readings.len()
            );
        }
    }

    /// The context-independence is not limited to parentheses: a COLLECTION element used to take
    /// the `BigInt` carrier while the identical numeral at top level took `Int` (via the
    /// auto-injected `IntToBigInt` promotion), which is why `{1: 10}.get(1)` answered `error`.
    #[test]
    fn numeral_carrier_is_independent_of_the_enclosing_collection() {
        for (source, expected) in [
            ("1", "CastInt(NumLit(1))"),
            ("(1)", "CastInt(NumLit(1))"),
            ("[1]", "CastList(ListLit([CastInt(NumLit(1))]))"),
            ("Set(1)", "CastSet(SetLit(HashSetLit({CastInt(NumLit(1))})))"),
            (
                "{1: 1}",
                "CastMap(MapLit(HashMapLit({CastInt(NumLit(1)): CastInt(NumLit(1))})))",
            ),
        ] {
            fresh();
            assert_eq!(
                format!("{:?}", parse(source)),
                expected,
                "`{source}` must carry `Int`, like every other spelling of `1`"
            );
        }
        // The observable consequence, which was `error` before.
        assert_reduces_to("{1: 10}.get(1)", "10");
        assert_reduces_to("[1, 2, 3].length() == 3", "true");
    }

    /// Only the `…n` spelling reaches the arbitrary-precision carrier — and it does so in every
    /// context, including the ones that used to force `BigInt` on everything.
    #[test]
    fn only_the_n_spelling_reaches_bigint() {
        for (source, expected) in [
            ("3n", "CastBigInt(NumLit(3))"),
            ("(3n)", "CastBigInt(NumLit(3))"),
            ("[3n]", "CastList(ListLit([CastBigInt(NumLit(3))]))"),
            // Unsuffixed and past `i64`: the deliberate MeTTaIL superset (no Rholang program can
            // express this numeral, so no Rholang-expressible program changes meaning).
            ("32478132567813256718", "CastBigInt(NumLit(32478132567813256718))"),
        ] {
            fresh();
            assert_eq!(format!("{:?}", parse(source)), expected, "`{source}`");
        }
        assert_reduces_to("1n + 2n", "3n");
    }

    /// Mixed-carrier arithmetic stays refused — the fold and f1r3node's `combine_plus` agree —
    /// but it is no longer REACHABLE from source text that means one integer.
    #[test]
    fn mixed_carrier_arithmetic_is_error_and_is_no_longer_reachable_by_accident() {
        // Genuinely mixed: an explicit fixed-width cast plus an explicit `…n` literal.
        assert_reduces_to("int(1, 64) + 2n", "error");
        // What used to be "mixed" purely because of how it was written now computes.
        assert_reduces_to("int(1, 64) + 2", "3");
        assert_reduces_to("*(@(1)) + 2", "3");
        // The carrier-consistent cases still compute.
        assert_reduces_to("int(1, 64) + int(2, 64)", "3");
        assert_reduces_to("1 + 2", "3");
    }

    /// A `u32`-suffixed literal IS an `i64` literal written with a `u32` suffix — exactly what
    /// `normalize_ground` says (`bits <= 64 && value <= i64::MAX ⟹ GInt`) — so `bitnot 0u32` is
    /// `-1`, not the 32-bit all-ones `4294967295`. The 32-bit wraparound carrier is reached only
    /// through the MeTTaIL-only `uint(_, 32)` cast.
    #[test]
    fn u32_suffix_is_an_i64_literal() {
        fresh();
        assert_eq!(
            format!("{:?}", parse("5u32")),
            "CastInt(NumLit(5))",
            "the `u32` suffix is a SPELLING of a `GInt`, not a different carrier"
        );
        // `-1` has no source spelling that parses back to itself (`-1` is `NegProc(1)`), so the
        // display is asserted directly. The ANSWER is unchanged from the pre-fix pin; what
        // changed is that it is now correct BY CONSTRUCTION rather than by accident.
        assert_normal_form_display("bitnot 0u32", "-1");
        assert_reduces_to("bitnot uint(0, 32)", "4294967295");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Comparator integrity — the assertion helpers must be able to FAIL
// ════════════════════════════════════════════════════════════════════════════════

/// These tests assert the *assertions*. Until 2026-07-25 [`bag_multiset_eq`] compared
/// `Option<Vec<String>>` values directly, so `None == None` made it answer `true` for every pair
/// in which neither side is a `#{…}#` bag literal — and since [`assert_reduces_to`] ORs it in
/// last, the entire helper became vacuous: `assert_reduces_to("1 + 2", "999")` passed. 39 of this
/// file's tests were asserting nothing.
///
/// A comparator that cannot answer `false` is not a comparator, so the guarantee is pinned here
/// directly rather than being left implicit in the tests that use it.
mod comparator_integrity {
    use super::*;

    /// The exact measured vacuity witness: a false claim must FAIL.
    #[test]
    #[should_panic(expected = "Expected `1 + 2` to reduce to `999`")]
    fn assert_reduces_to_rejects_a_false_expectation() {
        assert_reduces_to("1 + 2", "999");
    }

    /// A second witness in a different shape (collection vs. scalar), so a fix that only
    /// special-cases integers cannot pass this module.
    #[test]
    #[should_panic(expected = "Expected `[1, 2, 3]` to reduce to")]
    fn assert_reduces_to_rejects_a_false_collection_expectation() {
        assert_reduces_to("[1, 2, 3]", "Set(9)");
    }

    /// `bag_multiset_eq` is INAPPLICABLE unless both sides are bag literals, and inapplicable
    /// must mean `false`.
    #[test]
    fn bag_multiset_eq_is_false_when_it_does_not_apply() {
        assert!(!bag_multiset_eq("3", "999"), "two non-bags are not 'equal bags'");
        assert!(!bag_multiset_eq("error", "0"), "two non-bags are not 'equal bags'");
        assert!(!bag_multiset_eq("#{1 | 2}#", "3"), "one-sided bag is not 'equal bags'");
        assert!(!bag_multiset_eq("3", "#{1 | 2}#"), "one-sided bag is not 'equal bags'");
    }

    /// …and it still does its real job when it DOES apply.
    #[test]
    fn bag_multiset_eq_is_order_insensitive_on_real_bags() {
        assert!(bag_multiset_eq("#{1 | 2}#", "#{2 | 1}#"));
        assert!(
            bag_multiset_eq("{#{1 | 2}#}", "#{2 | 1}#"),
            "singleton-par wrapper is unwrapped"
        );
        assert!(!bag_multiset_eq("#{1 | 2}#", "#{1 | 3}#"));
    }

    /// The sibling comparator was already guarded; pinned so the two stay in the same shape.
    #[test]
    fn multiset_eq_is_false_when_it_does_not_apply() {
        assert!(!multiset_eq("3", "999"));
        assert!(!multiset_eq("{a | b}", "b"));
        assert!(multiset_eq("{a | b}", "{b | a}"));
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Communication
// ════════════════════════════════════════════════════════════════════════════════

mod comm {
    use super::*;

    /// Reproduces REPL load_env parse error: PPar with a!(n) must not reduce "a" to variable.
    #[test]
    fn par_with_output_literal() {
        let _ = parse(" a!(2) | b!(3) ");
    }

    #[test]
    fn single_channel() {
        assert_reduces_to("for(x <- c){*(x)} | c!(p)", "p");
    }

    #[test]
    fn comm_with_body_using_channel() {
        // ★ SURFACE SYNONYMY (2026-07-26): the reduct's channel is `NQuote(PVar p)`, and the
        // `Name` synonymy class `{ NQuote, NQuoteShort, NQuoteNil }` now renders through its
        // DECLARED canonical member `NQuoteShort` (`rhocalc.rs`), so the surface is the Rholang
        // shorthand `@p` rather than `@(p)`. The TERM is unchanged; only which member's surface
        // `Display` emits moved. See `languages/tests/surface_synonymy_gate.rs`.
        assert_reduces_to("for(x <- c){x!(0)} | c!(p)", "@p!([0])");
    }

    #[test]
    fn comm_substitutes_quoted_value() {
        // Comm: for(x <- c){*(x)} | c!(0) → *(@ (0)) → 0
        assert_reduces_to("for(x <- c){*(x)} | c!(0)", "0");
    }

    #[test]
    fn multi_input_two_channels() {
        assert_reduces_to("for(x <- c1 & y <- c2){*(x)} | c1!(p) | c2!(q)", "p");
    }

    #[test]
    fn multi_input_uses_both_vars() {
        assert_reduces_to("for(x <- c1 & y <- c2){*(x) | *(y)} | c1!(p) | c2!(q)", "p | q");
    }

    #[test]
    fn multi_input_three_channels() {
        assert_reduces_to(
            "for(x <- a & y <- b & z <- c){*(x) | *(y) | *(z)} | a!(p) | b!(q) | c!(r)",
            "p | q | r",
        );
    }

    #[test]
    fn join_pattern_same_channel() {
        assert_reduces_to("for(x <- c & y <- c){*(x) | *(y)} | c!(a) | c!(b)", "a | b");
    }

    #[test]
    fn comm_with_remaining_parallel() {
        // {for(x <- c){*(x)} | c!(p) | q} → {p | q}
        assert_reduces_to("for(x <- c){*(x)} | c!(p) | q", "p | q");
    }

    #[test]
    fn list_concat_join_comm() {
        assert_reduces_to(
            "a!([ 1, 2 ]) | b!([ 3, 4 ]) | for(x <- a & y <- b){ (*(x)).concat(*(y)) }",
            "[1, 2, 3, 4]",
        );
    }

    #[test]
    fn list_concat_join_comm_braced() {
        assert_reduces_to(
            "{ a!( [ 1, 2 ] ) | b!( [ 3, 4 ] ) | for(x <- a & y <- b){ (*(x)).concat(*(y)) } }",
            "[1, 2, 3, 4]",
        );
    }

    #[test]
    fn list_payload_single_bind_comm() {
        assert_reduces_to("for(x <- c){*(x)} | c!([0, 1])", "[0, 1]");
    }

    #[test]
    fn bag_union_join_comm() {
        // Multiset union keeps multiplicity: #{1|2}# ∪ #{2|3}# = #{1|2|2|3}#
        assert_reduces_to(
            "a!(#{ 1 | 2 }#) | b!(#{ 2 | 3 }#) | for(x <- a & y <- b){ (*(x)).union(*(y)) }",
            "#{1 | 2 | 2 | 3}#",
        );
    }

    #[test]
    fn comm_with_persistent_send_keeps_send() {
        let (results, initial_id) = run_with_initial("for(x <- c){*x} | c!!(p)");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        // Persistent send `c!!(p)` remains (displayed `c!!([p])` — arity list)
        // and the received `p` is substituted into the body (`*@p` → `p`).
        assert!(
            any_nf_contains(&nfs, "c!!(p)") && nfs.iter().any(|nf| nf.contains('p')),
            "expected persistent send to remain after comm, got {:?}",
            nfs
        );
    }

    #[test]
    fn two_receives_can_fire_against_same_persistent_send() {
        let (results, initial_id) = run_with_initial("for(x <- c){*x} | for(y <- c){*y} | c!!(p)");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        // Both receives fire against the SAME persistent send: the send remains
        // (`c!!([p])`) and two substituted copies of `p` appear.
        assert!(
            nfs.iter()
                .any(|nf| { canon_display(nf).contains("c!!(p)") && nf.matches('p').count() >= 2 }),
            "expected both receives to fire while persistent send remains, got {:?}",
            nfs
        );
    }

    #[test]
    fn join_with_persistent_and_ephemeral_send() {
        let (results, initial_id) =
            run_with_initial("for(x <- c1 & y <- c2){*x} | c1!!(p) | c2!(q)");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        // The join consumes the ephemeral `c2!(q)` and keeps the persistent
        // `c1!!(p)` (displayed `c1!!([p])`); `p` is substituted into the body.
        assert!(
            any_nf_contains(&nfs, "c1!!(p)") && nfs.iter().any(|nf| nf.contains('p')),
            "expected join to consume ephemeral send and keep persistent one, got {:?}",
            nfs
        );
    }

    #[test]
    fn comm_with_persistent_receive_keeps_receive() {
        // Bare infix `|` parses as `PParInfix` and folds to `PPar` in one
        // ascent step before COMM fires, so the substituted body shows up
        // among reachable terms (not necessarily as a direct rewrite of the
        // initial `PParInfix` node).
        let (results, initial_id) = run_with_initial("for(x <= c){*x} | c!(p)");
        assert!(
            !results.rewrites_from(initial_id).is_empty(),
            "expected at least one rewrite from initial term"
        );
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("for(x <= c){") && d.contains("*@p")),
            "expected persistent receive + substituted body after one comm, terms={:?}",
            displays
        );
    }

    #[test]
    fn two_sends_can_fire_against_same_persistent_receive() {
        let results = run("for(x <= c){*x} | c!(p) | c!(q)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("for(x <= c){") && d.contains("p") && d.contains("q")),
            "expected both sends consumed and persistent receive remains, got {:?}",
            displays
        );
    }

    #[test]
    fn persistent_receive_with_persistent_send_keeps_both() {
        fresh();
        let input = parse("for(x <= c){*x} | c!!(p)");
        let one_step = input
            .try_comm_once()
            .expect("expected one COMM step for persistent receive + persistent send");
        let out = one_step.to_string();
        assert!(
            out.contains("for(x <= c){*x}"),
            "expected persistent receive to remain after one COMM step, got {}",
            out
        );
        assert!(
            out.contains("c!!([p])") || out.contains("c!!(p)"),
            "expected persistent send to remain after one COMM step, got {}",
            out
        );
        assert!(
            out.contains("*@p"),
            "expected one-step continuation payload to be produced, got {}",
            out
        );
    }

    #[test]
    fn join_persistent_receive_keeps_receive_after_fire() {
        let results = run("for(x <= c1 & y <- c2){*x} | c1!(p) | c2!(q)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("for(x <= c1") && d.contains("y <- c2") && d.contains("p")),
            "expected persistent join receive to remain after comm, got {:?}",
            displays
        );
    }

    #[test]
    fn persistent_receive_where_true_fires_and_keeps_listener() {
        let results = run("for(x <= c where x > 1){*x} | c!(2)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        // Guard `x > 1` with received `x = 2` is true → fires (`*@2`), and the
        // persistent listener remains. The listener's guard displays through the
        // projection surface as `x > @Nil!(1)`; `canon_display` restores `x > 1`.
        assert!(
            displays.iter().any(|d| {
                let c = canon_display(d);
                c.contains("for(x <= c where x > 1){*x}") && c.contains("*@2")
            }),
            "expected guarded persistent receive to fire and remain, got {:?}",
            displays
        );
    }

    #[test]
    fn persistent_receive_where_false_blocks() {
        let results = run("for(x <= c where x > 10){*x} | c!(2)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        // Guard `x > 10` with received `x = 2` is false → blocks: the listener
        // and the send `c!(2)` both remain (canonicalized guard: `x > 10`).
        assert!(
            displays.iter().any(|d| {
                let c = canon_display(d);
                c.contains("for(x <= c where x > 10){*x}") && c.contains("c!(2)")
            }),
            "expected guarded persistent receive to block mismatch, got {:?}",
            displays
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // M-0 — the `implies` connective, HOST side (`receive::eval_guard_bool`)
    // ════════════════════════════════════════════════════════════════════════════
    //
    // `implies` is the paper's `φ ⇒ ψ`. It has TWO evaluators, and the standing
    // obligation on the design is that they agree:
    //
    //   • the HOST twin   — `eval_guard_bool`'s `Implies` arm
    //                       (`languages/src/rhocalc/receive.rs`), reached through
    //                       the Dovetail/oracle receive path exercised HERE;
    //   • the MACHINE     — `EOrBody(ENotBody ⟦a⟧, ⟦b⟧)` decided by
    //                       `rho_pure_eval` under `guard_passes`, exercised in
    //                       `rholang-runtime/tests/rho_implies_guard.rs`.
    //
    // Both suites enumerate the SAME four rows of `⇒`, in the same order, with
    // the same expected verdicts, so a divergence between the two evaluators
    // shows up as one suite red and the other green rather than as a silent
    // semantic fork.
    //
    // A guarded receive is the only public entry to `eval_guard_bool` (the
    // function itself is private, by design: a guard verdict is meaningful only
    // as part of a COMM decision), so each row is stated as a receive whose
    // firing IS the verdict.

    /// One row of the host truth table: `for(x <- c where <guard>){*x} | c!(2)`
    /// fires iff `guard` is true. On a true guard the reduct `*@2` appears; on
    /// a false guard the receive AND the send both remain (fail shut — nothing
    /// consumed, nothing fabricated).
    fn assert_host_guard(guard: &str, expected: bool) {
        assert_host_guard_on(guard, "2", "*@2", expected)
    }

    /// [`assert_host_guard`] with the datum chosen by the caller.
    ///
    /// M-1b needs this because a SPATIAL guard is about the SHAPE of the received
    /// term, so the datum has to be a term with a shape (`c!(p)`, `c!({p|q})`)
    /// rather than the numeric `2` the propositional rows use. `reduct` is the
    /// display fragment the body `*x` produces once `x` is bound — the witness
    /// that the receive fired.
    fn assert_host_guard_on(guard: &str, datum: &str, reduct: &str, expected: bool) {
        let program = format!("for(x <- c where {guard}){{*x}} | c!({datum})");
        let results = run(&program);
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| canon_display(&t.display))
            .collect();
        let fired = displays.iter().any(|d| d.contains(reduct));
        let send = format!("c!({datum})");
        // A blocked guard leaves the WHOLE redex intact: the guarded receive
        // (recognizable by its `where` clause) and the unconsumed send `c!(2)`,
        // in the same normal form. The guard itself is compared only by the
        // presence of `where`, not verbatim: a guard displays through the
        // projection surface (`true` rides as `@Nil!(true)`), and `canon_display`
        // restores only the NUMERIC projections.
        let blocked = displays
            .iter()
            .any(|d| d.contains("where") && d.contains(&send));
        assert_eq!(
            fired, expected,
            "host guard {guard:?} must evaluate to {expected}; normal forms {displays:?}"
        );
        if !expected {
            assert!(
                blocked,
                "a false host guard must leave BOTH the receive and the send resting; \
                 normal forms {displays:?}"
            );
        }
    }

    /// ★ #33 / divergence H, SECOND HALF — the guard lane's `==` must decide two
    /// booleans, exactly as the fold lane's already does.
    ///
    /// Divergence H is "Rholang's `==` is STRUCTURAL equality on the whole `Par`
    /// (`reduce.rs::combine_eq`), which answers `true` for two `GBool`s; RhoCalc
    /// conforms DOWN to Rholang." It was closed in the FOLD lane and NOT in the GUARD
    /// lane — there are two `Eq` implementations and only one got the `CastBool` arm.
    ///
    /// The asymmetry is why it survived. In the fold lane an unhandled shape yields
    /// `Proc::Err`, which is LOUD and was caught same-day by the conformance
    /// differential. In the guard lane the identical gap yielded `None`, which the
    /// eager COMM sites treat identically to a decided `false` — so it was SILENT, and
    /// the host BLOCKED a COMM the machine fires.
    ///
    /// And it could not be reached by the fold-lane fix: the guard is evaluated on a
    /// freshly substituted local value that is never registered as an Ascent
    /// `proc(…)` fact, so no grammar fold runs on it.
    #[test]
    fn a_boolean_equality_guard_decides_on_the_host() {
        // The datum/reduct pair is `"hi"` / `*@"hi"`, the same one `assert_host_matches`
        // uses, and the choice is load-bearing. The harness detects firing by SUBSTRING,
        // so a reduct that also occurs in the blocked normal form is a false positive in
        // BOTH directions — a numeric datum `1` with reduct `1` reads as fired even
        // though the un-fired `c!(1)` is what contains it. `*@"hi"` is the DEREFERENCED
        // rendering and cannot appear in the resting send `c!("hi")`, so the signal is
        // real. The guard is a CONSTANT boolean comparison, so the datum is free to be
        // whatever discriminates while the guard still exercises the `CastBool` arm.
        fn guard(g: &str, expected: bool) {
            assert_host_guard_on(g, "\"hi\"", "*@\"hi\"", expected)
        }
        guard("true == true", true);
        guard("false == false", true);
        // And it genuinely decides FALSE rather than declining — a fix that made every
        // boolean comparison fire would pass the rows above and fail these.
        guard("true == false", false);
        guard("false == true", false);
        // The ORDER is `false < true`, matching `bool`'s own `Ord` and the machine's
        // structural comparison, so the relational operators agree too.
        guard("false < true", true);
        guard("true < false", false);
    }

    #[test]
    fn implies_truth_table_on_the_host_guard_evaluator() {
        // `p ⇒ q` ≡ `¬p ∨ q`, all four ground rows, none sampled.
        assert_host_guard("false implies false", true);
        assert_host_guard("false implies true", true);
        assert_host_guard("true implies false", false);
        assert_host_guard("true implies true", true);
    }

    #[test]
    fn implies_truth_table_on_the_host_guard_evaluator_via_comparisons() {
        // The same four rows with each operand a COMPARISON rather than a `bool`
        // literal, so the `Implies` arm recurses into `eval_guard_bool` on both
        // sides instead of reading two `CastBool` leaves.
        assert_host_guard("2 > 3 implies 2 > 3", true);
        assert_host_guard("2 > 3 implies 3 > 2", true);
        assert_host_guard("3 > 2 implies 2 > 3", false);
        assert_host_guard("3 > 2 implies 3 > 2", true);
    }

    #[test]
    fn implies_guard_over_the_bound_variable_fires_and_blocks() {
        // The operational shape: an implication ABOUT the received value.
        // `x = 2`, so `x > 0 implies x > 10` is `T ⇒ F` = false ⇒ blocked, and
        // `x > 0 implies x > 1` is `T ⇒ T` = true ⇒ fires. The vacuous row
        // `x > 10 implies x > 100` is `F ⇒ F` = true ⇒ fires.
        assert_host_guard("x > 0 implies x > 10", false);
        assert_host_guard("x > 0 implies x > 1", true);
        assert_host_guard("x > 10 implies x > 100", true);
    }

    #[test]
    fn implies_is_looser_than_or_and_and_on_the_host() {
        // `Implies` is declared immediately BEFORE `Or`, and declaration order is
        // loosest → tightest, so `false or false implies false and false` must
        // group as `(false or false) implies (false and false)` = F ⇒ F = TRUE.
        // The competing reading `false or ((false implies false) and false)`
        // is F ∨ (T ∧ F) = FALSE, so this single row pins the precedence — and it
        // pins it identically to the machine-side twin
        // (`rho_implies_guard::implies_is_looser_than_or_and_and`).
        assert_host_guard("false or false implies false and false", true);
        assert_host_guard("true and true implies false or true", true);
        assert_host_guard("true implies false or false", false);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // M-1b — `matches`, HOST side (`formula::host_matches_verdict`)
    // ════════════════════════════════════════════════════════════════════════════
    //
    // The host decides `t matches φ` on the fragment for which the generated
    // first-order `Proc::match_pattern` is a faithful model of the reducer's
    // spatial matcher: the logical constants, the propositional connectives, and a
    // concrete term pattern. It DECLINES (`None`) on the separating conjunction,
    // whose AC-with-remainder semantics is the reducer's alone — and a declined
    // guard leaves a `CommWhere` marker, so the receive simply does not fire
    // host-side and the decision is deferred to the machine.
    //
    // The machine-side twin of these rows lives in
    // `rholang-runtime/tests/rho_matches_guard.rs`, and the two are locked
    // together by `rholang-runtime/tests/rho_matches_differential.rs`.

    /// The M-1b host rows all use the same shaped datum `p` (an ordinary process
    /// variable), so `x` binds `p` and the formula is compared against it.
    ///
    /// ⚠ `expected` here is the OBSERVABLE outcome (did the guarded receive fire
    /// host-side?), not the formula's truth value. The host's term arm is
    /// POSITIVE-ONLY — it reports `Some(true)` for a proved match and `None`
    /// otherwise, never `Some(false)` — because the generated first-order matcher
    /// is not a faithful model of the reducer's spatial matcher in the FAILURE
    /// direction (see `formula::host_matches_verdict`). `Some(false)` and `None`
    /// are operationally identical at every call site: neither fires the COMM, and
    /// both leave the whole redex resting. So a row that reads `false` below means
    /// "the host does not fire", which is either a decided falsity or a deferral —
    /// and which of the two it is, is asserted precisely (on the verdict itself,
    /// not on the observation) in `rho_matches_differential.rs`.
    fn assert_host_matches(guard: &str, expected: bool) {
        assert_host_guard_on(guard, "\"hi\"", "*@\"hi\"", expected)
    }

    #[test]
    fn matches_decides_a_term_pattern_on_the_host() {
        // ⚠ GROUND patterns. A bare identifier is a free VARIABLE — a placeholder
        // that matches anything — so `x matches q` would fire, which says nothing
        // about term matching. Ground literals are what exercise the term arm.
        assert_host_matches(r#"x matches "hi""#, true);
        assert_host_matches(r#"x matches "bye""#, false);
        assert_host_matches("x matches Nil", false);
        // The placeholder row, stated explicitly rather than left as a trap: a free
        // variable in pattern position matches ANY target, host and machine alike.
        assert_host_matches("x matches q", true);
    }

    #[test]
    fn matches_decides_the_logical_constants_on_the_host() {
        // `⊤` and `⊥` need no matcher at all, so these ARE decided verdicts.
        assert_host_matches("x matches true", true);
        assert_host_matches("x matches false", false);
    }

    #[test]
    fn matches_decides_the_propositional_connectives_on_the_host() {
        // Pattern-level `and`/`or`/`not`/`implies`. The COMBINATION is the Boolean
        // algebra of the operands' verdicts — no matcher is involved in it, which
        // is why the host can evaluate it without owning a second matcher.
        assert_host_matches(r#"x matches ("hi" and true)"#, true);
        assert_host_matches(r#"x matches ("hi" and "bye")"#, false);
        assert_host_matches(r#"x matches ("bye" or "hi")"#, true);
        assert_host_matches(r#"x matches ("bye" or Nil)"#, false);
        assert_host_matches(r#"x matches (not "hi")"#, false);
        // ⚠ `not "bye"` is TRUE (the target is not `"bye"`), but the host's inner
        // verdict is UNKNOWN, and Kleene negation of unknown is unknown — so the
        // host does not fire and the machine decides it
        // (`rho_matches_differential`'s `(not @"z"!(9))` row). Recorded, not
        // glossed: this is the price of the positive-only term arm.
        assert_host_matches(r#"x matches (not "bye")"#, false);
        assert_host_matches(r#"x matches ("hi" implies "hi")"#, true);
        assert_host_matches(r#"x matches ("hi" implies "bye")"#, false);
        assert_host_matches(r#"x matches ("bye" implies "bye")"#, false);
    }

    #[test]
    fn a_separating_formula_is_deferred_not_guessed_on_the_host() {
        // `host_matches_verdict` answers `None` for a separating conjunction, so
        // `eval_guard_bool` answers `None`, so `eval_where_comm_single` declines
        // and `comm_pforwhere_subst` keeps the `CommWhere` marker. Observationally:
        // the receive does not fire and the send is untouched — the fail-closed
        // disposition (the host never commits on a guard it cannot decide).
        //
        // ⚠ DEFERRAL, not falsity. The machine decides the same guard, and
        // `rho_matches_guard::the_separating_conjunction_splits_the_term` shows it
        // deciding it TRUE for a satisfied split. The two are consistent because
        // declining only ever removes host-side reduction; it never produces a
        // verdict.
        assert_host_matches(r#"x matches { "hi" | true }"#, false);
        assert_host_matches("x matches PPar(true, true)", false);
    }

    #[test]
    fn matches_binds_tighter_than_and_on_the_host() {
        // `a matches P and b matches Q` ⇒ `(a matches P) and (b matches Q)`.
        // With `x` bound to `"hi"`: `(x matches "hi") and (x matches "bye")` does
        // not fire, and `(x matches "hi") and (x matches true)` does. A looser
        // `matches` would instead read `x matches ("hi" and (x matches "bye"))`,
        // which is a different formula — so these two rows pin the precedence
        // host-side exactly as the machine-side twin does.
        assert_host_matches(r#"x matches "hi" and x matches "bye""#, false);
        assert_host_matches(r#"x matches "hi" and x matches true"#, true);
    }

    #[test]
    fn empty_persistent_receive_consumes_payload_and_stays() {
        let results = run("for(<= c){ok} | c!(payload)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("ok") && d.contains("for(<=c){ok}")),
            "expected empty persistent receive to fire and stay, got {:?}",
            displays
        );
    }

    #[test]
    fn persistent_join_where_true_fires() {
        let results = run("for(x <= c1 & y <- c2 where y > 1){*x} | c1!(p) | c2!(2)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        // Join guard `y > 1` with received `y = 2` is true → fires (`*@p`),
        // persistent listener remains (canonicalized guard: `y > 1`).
        assert!(
            displays.iter().any(|d| {
                let c = canon_display(d);
                c.contains("*@p") && c.contains("for(x <= c1&y <- c2 where y > 1){*x}")
            }),
            "expected persistent join with true guard to fire, got {:?}",
            displays
        );
    }

    #[test]
    fn persistent_join_where_false_blocks() {
        let results = run("for(x <= c1 & y <- c2 where y > 10){*x} | c1!(p) | c2!(2)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        // Join guard `y > 10` with received `y = 2` is false → blocks: the
        // listener and both sends remain (canonicalized guard: `y > 10`).
        assert!(
            displays.iter().any(|d| {
                let c = canon_display(d);
                c.contains("for(x <= c1&y <- c2 where y > 10){*x}")
                    && c.contains("c1!(p)")
                    && c.contains("c2!(2)")
            }),
            "expected persistent join with false guard to block, got {:?}",
            displays
        );
    }

    #[test]
    fn semicolon_rows_with_persistent_first_row() {
        let results = run("for(x <= c1; y <- c2){*x} | c1!(p) | c2!(q)");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("*@p") && d.contains("for(y <- c2){*@p}")),
            "expected first persistent row to fire then continue with second row, got {:?}",
            displays
        );
    }

    #[test]
    fn polyadic_receive_binds_list_payload_from_polyadic_send() {
        assert_reduces_to("x!(1,2,3) | for(a, b, c <- x){[a,b,c]}", "[1,2,3]");
    }

    #[test]
    fn persistent_polyadic_receive_keeps_listener() {
        let results = run("x!(1,2,3) | for(a, b, c <= x){[a,b,c]}");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays.iter().any(|d| {
                // Whitespace-insensitive: WFST displays with spaces; subst semantics verified.
                let s: String = d.chars().filter(|c| !c.is_whitespace()).collect();
                s.contains("[1,2,3]") && s.contains("for(a,b") && s.contains("c<=x){[a,b,c]}")
            }),
            "expected polyadic persistent receive to fire and remain, got {:?}",
            displays
        );
    }

    #[test]
    fn polyadic_receive_arity_mismatch_blocks() {
        assert_reduces_to(
            "x!(1,2) | for(a, b, c <- x){[a,b,c]}",
            "x!(1,2) | for(a,b , c<-x){[a,b,c]}",
        );
    }

    #[test]
    fn polyadic_receive_in_join_row_works() {
        assert_reduces_to("x!(1,2) | z!(ok) | for(a, b <- x & y <- z){[a,b,y]}", "[1,2,ok]");
    }

    #[test]
    fn polyadic_receive_where_guard_works() {
        assert_reduces_to("x!(1,2,3) | for(a, b, c <- x where c > 2){[a,b,c]}", "[1,2,3]");
    }

    #[test]
    fn pattern_comm_var_matches_payload() {
        assert_reduces_to("for(x <- c){*x} | c!(p)", "p");
    }

    #[test]
    fn compact_for_row_with_ampersand_desugars_to_join() {
        assert_reduces_to("for(x <- c1 & y <- c2){*x} | c1!(p) | c2!(q)", "p");
    }

    #[test]
    fn quoted_name_binder_form_is_equivalent() {
        assert_reduces_to("for(@x <- c1 & @y <- c2){x} | c1!(p) | c2!(q)", "p");
    }

    #[test]
    fn compact_for_rows_with_semicolon_are_nested() {
        assert_reduces_to("for(x <- c1; y <- c2){*x} | c1!(p) | c2!(q)", "p");
    }

    #[test]
    fn compact_for_row_where_guard_blocks_when_false() {
        assert_never_reaches("for(x <- c1 & y <- c2 where false){*x} | c1!(p) | c2!(q)", "p");
    }

    #[test]
    fn where_guard_false_is_noop_for_receive_pair() {
        assert_never_reaches("for(x <- c where false){*x} | c!(p)", "p");
    }

    #[test]
    fn where_guard_expression_false_is_noop_for_receive_pair() {
        assert_never_reaches("for(x <- c where x > 3){*x} | c!(2)", "2");
    }

    #[test]
    fn join_pattern_mismatch_is_noop_for_receive_group() {
        assert_reduces_to(
            "for(@[1,2,4] <- c){7} | c!([1,2,3])",
            "for(@[1,2,4] <- c){7} | c!([1,2,3])",
        );
        assert_never_reaches("for(@[1,2,4] <- c){7} | c!([1,2,3])", "7");
    }

    #[test]
    fn pattern_comm_ground_pattern_matches_equal_payload() {
        assert_reduces_to("for(@0 <- c){1} | c!(0)", "1");
    }

    #[test]
    fn pattern_comm_exact_constructor_pattern_matches() {
        // Spelled `@0`, not `@(0)`, for a reason that is now HISTORICAL: a parenthesized numeral
        // used to take the `Int` carrier while a bare one took `BigInt`, and the parser applied
        // that choice ASYMMETRICALLY to a receive PATTERN and a send PAYLOAD written from
        // identical source text, so `for(@*(@(0)) <- c){1} | c!(*(@(0)))` could not unify with
        // itself. Divergence I closed the CARRIER half of that — both occurrences of `0` are now
        // `CastInt` — but the parenthesized spelling still does not fire, for a DIFFERENT and
        // pre-existing reason: normalization keeps a redundant `NParen` wrapper asymmetrically
        // between pattern and payload position (`for(@*@0 …) | c!(*(@0))` is the residual normal
        // form). That is a redundant-quote/paren normalization gap, not a carrier gap, and it is
        // out of divergence I's scope. This test's own subject is the exact-CONSTRUCTOR pattern.
        assert_reduces_to("for(@*@0 <- c){1} | c!(*@0)", "1");
    }

    #[test]
    fn pattern_comm_ground_pattern_blocks_mismatch() {
        // Pattern 0 does not match payload p, so COMM must not produce a
        // reachable normal form whose only proc is the body `0`.
        assert_never_reaches("for(@0 <- c){0} | c!(p)", "0");
    }

    #[test]
    fn pattern_comm_list_literal_pattern_matches() {
        assert_reduces_to("for(@[0, 1] <- c){42} | c!([0, 1])", "42");
    }

    #[test]
    fn pattern_comm_list_literal_pattern_blocks_mismatch() {
        assert_never_reaches("for(@[0, 1] <- c){42} | c!([0, 1, 2])", "42");
    }

    #[test]
    fn pattern_comm_bag_literal_pattern_matches() {
        assert_reduces_to("for(@#{1|2}# <- c){7} | c!(#{2|1}#)", "7");
    }

    #[test]
    fn pattern_comm_bag_literal_pattern_blocks_mismatch() {
        assert_never_reaches("for(@#{1|2}# <- c){7} | c!(#{1|1}#)", "7");
    }

    #[test]
    fn pattern_comm_map_literal_pattern_matches() {
        assert_reduces_to("for(@{1:2, 3:4} <- c){9} | c!({3:4, 1:2})", "9");
    }

    #[test]
    fn pattern_comm_map_literal_pattern_blocks_mismatch() {
        assert_never_reaches("for(@{1:2, 3:4} <- c){9} | c!({1:2, 3:5})", "9");
    }

    #[test]
    fn pattern_comm_set_literal_pattern_matches() {
        assert_reduces_to("for(@Set(1, 2) <- c){7} | c!(Set(2, 1))", "7");
    }

    #[test]
    fn pattern_comm_set_literal_pattern_blocks_mismatch() {
        assert_never_reaches("for(@Set(1, 2) <- c){7} | c!(Set(1, 1))", "7");
    }

    #[test]
    fn complex_join_map_and_list_literal_pattern_matches() {
        assert_reduces_to(
            "for(@{1:x, 3:4} <- c & @[1,2,3] <- c2 where x>1){x} | c!({3:4, 1:2}) | c2!([1,2,3])",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_literal_pattern_blocks_mismatch() {
        assert_never_reaches(
            "for(@{1:x, 3:4} <- c & @[1,2,4] <- c2 where x>1){x} | c!({3:4, 1:2}) | c2!([1,2,3])",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_matches() {
        assert_reduces_to(
            "for(@{1:x, 3:4} <- c & @[1,2,y] <- c2 where x>1){x} | c!({3:4, 1:2}) | c2!([1,2,3])",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_with_guard_matches() {
        assert_reduces_to(
            "for(@{1:x, 3:4} <- c & @[1,2,y] <- c2 where x>1 and y>1){x} | c!({3:4, 1:2}) | c2!([1,2,3])",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_with_guard_blocks() {
        assert_never_reaches(
            "for(@{1:x, 3:4} <- c & @[1,2,y] <- c2 where x>1 and y>3){x} | c!({3:4, 1:2}) | c2!([1,2,3])",
            "2",
        );
    }

    #[test]
    fn complex_multi_row_join_and_followup_row_matches() {
        assert_reduces_to(
            "for(@{1:x, 3:4} <- c & @[1,2,y] <- c2 where x>1 and y>1; z <- c3 ){[x,z]} | c!({3:4, 1:2}) | c2!([1,2,3]) | c3!(11111111)",
            "[2, 11111111]",
        );
    }

    #[test]
    fn complex_multi_row_join_and_followup_row_guard_blocks() {
        assert_never_reaches(
            "for(@{1:x, 3:4} <- c & @[1,2,y] <- c2 where x>1 and y>1; z <- c3 where z > 1111111111111111 ){[x,z]} | c!({3:4, 1:2}) | c2!([1,2,3]) | c3!(11111111)",
            "[2, 11111111]",
        );
    }

    #[test]
    fn join_where_guard_string_eq_matches() {
        assert_reduces_to(
            r#"for(qty <- stock & item <- shop where (qty > 1) and (item == "lemon")){[item, qty]} | stock!(2) | shop!("lemon")"#,
            r#"["lemon", 2]"#,
        );
    }

    #[test]
    fn join_where_guard_string_eq_blocks() {
        assert_never_reaches(
            r#"for(qty <- stock & item <- shop where (qty > 1) and (item == "lemon")){[item, qty]} | stock!(2) | shop!("lime")"#,
            r#"["lime", 2]"#,
        );
    }

    #[test]
    fn proc_pattern_matches_list_is_strict() {
        let pat = parse("[0, 1]");
        let val = parse("[0, 1, 2]");
        assert!(
            val.match_pattern(&pat).is_none(),
            "strict pattern match: shorter/different pattern must not match"
        );
    }

    #[test]
    fn proc_pattern_matches_map_is_strict() {
        let pat = parse("{1:2, 3:4}");
        let val = parse("{1:2, 3:5}");
        assert!(
            val.match_pattern(&pat).is_none(),
            "strict pattern match: shorter/different pattern must not match"
        );
    }

    #[test]
    fn proc_pattern_matches_set_is_strict() {
        let pat = parse("Set(1, 2)");
        let val = parse("Set(1, 2, 3)");
        assert!(
            val.match_pattern(&pat).is_none(),
            "strict pattern match: shorter/different pattern must not match"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// PNew binder and scope extrusion
// ════════════════════════════════════════════════════════════════════════════════

mod new_and_extrusion {
    use super::*;

    #[test]
    fn new_parses() {
        let _p = parse("new x in { x!(0) }");
    }

    #[test]
    fn new_multi_binder_parses() {
        let _p = parse("new x, y in {x!(0) | y!(1)}");
    }

    #[test]
    fn new_is_normal_when_body_is() {
        assert_no_rewrites("new x in { x!(0) }");
    }

    #[test]
    fn new_congruence_propagates_body_rewrite() {
        // new x in {for(z <- a){*(z)} | a!(0)} → new x in {*(@(0))} → ...
        assert_min_rewrites("new x in {for(z <- a){*(z)} | a!(0)}", 1);
    }

    #[test]
    fn new_congruence_reaches_normal_form() {
        assert_reduces_to("new x in {for(z <- a){*(z)} | a!(0)}", "new x in { 0 }");
    }

    #[test]
    fn extrusion_forward() {
        // {new x in {p} | a!(0)} = new x in {p | a!(0)}
        // The initial PPar should connect to a rewrite (via equation + congruence).
        assert_initial_rewrites("new x in { for(z <- a){*(z)} } | a!(0)");
    }

    #[test]
    fn extrusion_reaches_result() {
        // {new x in {for(z <- a){*(z)}} | a!(0)}
        //  =extrude= new x in {{for(z <- a){*(z)} | a!(0)}}
        //  →comm→ new x in {*(@(0))} →exec→ new x in {0}
        assert_reduces_to("new x in { for(z <- a){*(z)} } | a!(0)", "new x in { 0 }");
    }

    #[test]
    fn extrusion_blocked_when_not_fresh() {
        // {new a in {for(z <- a){*(z)}} | a!(0)} — x=a is NOT fresh in a!(0),
        // so extrusion should not apply. The term is stuck.
        let results = run("new a in { for(z <- a){*(z)} } | a!(0)");
        let nfs = normal_form_displays(&results);
        // Should be a normal form as-is (no extrusion possible)
        assert!(!nfs.is_empty(), "blocked extrusion should still have normal forms");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Congruence (rewrite propagation)
// ════════════════════════════════════════════════════════════════════════════════

mod congruence {
    use super::*;

    #[test]
    fn par_cong_exec() {
        // {*(@(0)) | q} → {0 | q}
        assert_reduces_to("*(@(0)) | q", "0 | q");
    }

    #[test]
    fn par_cong_reaches_deep_normal() {
        assert_reduces_to("*(@(0))", "0");
    }

    #[test]
    fn nested_par() {
        // Exec under nested par: {{*(@(p))}} → {{p}}
        assert_min_rewrites("*(@(p))", 1);
    }

    #[test]
    fn new_cong() {
        // NewCong: new x in { *(@(0)) } → new x in { 0 }
        assert_reduces_to("new x in { *(@(0)) }", "new x in { 0 }");
    }

    #[test]
    fn add_cong() {
        // Congruence through Add: the `*@…` operand must reduce before `+` can fold.
        //
        // ★ COMMENT REWRITTEN 2026-07-25 (divergence I). These three assertions survive, but for
        // a NEW reason. They were written when a numeral's carrier depended on parentheses, so
        // each case had to be spelled to keep BOTH operands in the SAME carrier — `*@1 + 2` in
        // arbitrary precision, `*(@(1)) + int(2, 64)` in fixed width — because RhoCalc's `+` is
        // carrier-exact (and so is f1r3node's `combine_plus`, `reduce.rs:3112`: no mixed
        // `GInt`/`GBigInt` arm). The earlier single case `*(@(1)) + 2` mixed the carriers, so
        // `error` was the CORRECT answer for it and the test measured nothing about congruence.
        //
        // Now every numeral below is a `CastInt` — the carrier does not depend on the spelling at
        // all — so what these cases exercise is purely the CONGRUENCE they are named for: the
        // `*@…` operand must reduce before `+` can fold. `int(2, 64)` is retained in the third
        // case because it is `CastInt` too, which is precisely the point.
        assert_reduces_to("*@1 + 2", "3");
        assert_reduces_to("*(@1) + 2", "3");
        assert_reduces_to("*(@(1)) + int(2, 64)", "3");
        // Formerly `error` (mixed carriers); now the same one integer on both sides.
        assert_reduces_to("*(@(1)) + 2", "3");
    }

    #[test]
    fn comparison_cong() {
        // `*@…` reduces, then `==` compares. Carrier-exact, for the same reason as `add_cong` —
        // and, since divergence I, every spelling of `1` below is the SAME carrier.
        assert_reduces_to("*(@1) == 1", "true");
        assert_reduces_to("*(@(1)) == int(1, 64)", "true");
        assert_reduces_to("*(@(1)) == 1", "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Exec (drop-quote cancellation)
// ════════════════════════════════════════════════════════════════════════════════

mod exec {
    use super::*;

    #[test]
    fn exec_basic() {
        assert_reduces_to("*(@(0))", "0");
    }

    #[test]
    fn exec_with_process() {
        assert_reduces_to("*(@(a!(0)))", "a!(0)");
    }

    #[test]
    fn quote_drop_equation() {
        // QuoteDrop: @(*(n)) = n  (equation, not rewrite)
        // This is tested indirectly: @(*(x)) normalizes by equation to x.
        let results = run("@(*(x))");
        assert!(
            !results.equivalences.is_empty() || !results.all_terms.is_empty(),
            "QuoteDrop equation should be discoverable"
        );
    }

    #[test]
    fn quote_nil_shorthand_parses() {
        // `@Nil` is Rholang shorthand for `@(Nil)`. At parse time the surface
        // forms differ (`Name::NQuoteNil` vs `Name::NQuote(PZero)`) — the
        // fold-equivalence is realized via the Ascent fold rule. We assert that
        // both inputs reduce to the same normal form via `Exec` (`*X → X`).
        assert_reduces_to("*@Nil", "Nil");
        assert_reduces_to("*(@(Nil))", "Nil");
    }

    #[test]
    fn quote_nil_exec_reduces_to_nil() {
        // `*@Nil` (= `PDrop(NQuote(PZero))`) reduces via Exec to `PZero` (`Nil`).
        assert_reduces_to("*@Nil", "Nil");
    }

    #[test]
    fn quote_nil_send_reduces_via_comm() {
        // Quoted-name channel using the shorthand: `for(x <- @Nil){x} | @Nil!(0)`
        // routes the send through the `@Nil`-named channel just like `@(Nil)` does.
        assert_reduces_to("for(x <- @Nil){x} | @Nil!(0)", "0");
    }

    #[test]
    fn quote_nil_persistent_send_parses() {
        // Persistent send shorthand must also accept `@Nil`.
        fresh();
        let parsed = Proc::parse("@Nil!!(0)");
        assert!(parsed.is_ok(), "expected `@Nil!!(0)` to parse, got {:?}", parsed);
    }

    // ── Generalised `@P` shorthand for arbitrary `P:Proc`.
    //
    // `NQuoteShort` lowers `@P → Name::NQuote(P)` via fold, generalising
    // `@(P)` and `@Nil`.  Disambiguation: the NFA dispatcher tries `NQuote`
    // and `NQuoteNil` first (declared earlier); `NQuoteShort` fires only
    // when neither matches.  Caveat: the inner Proc parser is called with
    // `min_bp = 0`, so `@P op Q` greedily folds `op Q` into the quote
    // (write `(@P) op Q` to keep them separate).

    #[test]
    fn quote_short_int_drop_reduces() {
        // `*@1` (= `PDrop(NQuote(CastInt(1)))`) reduces via Exec to `CastInt(1)`.
        assert_reduces_to("*@1", "1");
    }

    #[test]
    fn quote_short_bool_drop_reduces() {
        assert_reduces_to("*@true", "true");
    }

    #[test]
    fn quote_short_string_drop_reduces() {
        assert_reduces_to(r#"*@"hello""#, r#""hello""#);
    }

    #[test]
    fn quote_short_drop_of_drop_reduces() {
        // `@*x = x` via the QuoteDrop equation; then `*x` is the dereference
        // of the original Name.  We assert the surface chain composes.
        // Inner `*y` is `Proc::PDrop(NVar(y))`; quoting it yields
        // `NQuote(PDrop(NVar(y)))` which the QuoteDrop equation rewrites to
        // `NVar(y)`, so `*@*y` reduces to `*y` (just the original drop).
        assert_reduces_to("*@*y", "*y");
    }

    #[test]
    fn quote_short_send_via_int_channel_comm() {
        // Send/receive on the `@1`-named channel:
        //   for(x <- @1){x} | @1!(42)  →  42
        // The receive's channel is parsed as `NQuoteShort(1)` (= `NQuote(1)`),
        // the send's channel as `POutputQuoted` with the same Name shape; they
        // unify at COMM time.
        assert_reduces_to("for(x <- @1){x} | @1!(42)", "42");
    }

    #[test]
    fn quote_short_send_via_string_channel_comm() {
        assert_reduces_to(r#"for(x <- @"k"){x} | @"k"!(7)"#, "7");
    }

    #[test]
    fn quote_short_paren_form_still_works() {
        // Pre-existing `@(P)` form must still parse and reduce — `NQuote`
        // (declared first) wins the NFA race for `@(...)`.
        assert_reduces_to("*(@(1 + 2))", "3");
    }

    #[test]
    fn quote_short_persistent_send_reduces() {
        // Persistent send `@1!!(99)` paired with a non-persistent receive
        // `for(x <- @1){x}` must fire COMM once: the receive consumes a
        // copy of the payload (yielding `99`) while the persistent send
        // stays alive.  Some normal form in the search must therefore
        // contain the payload `99` (the multiset ordering of the surviving
        // PPar is unspecified, hence the substring check).
        let (results, _) = run_with_initial("for(x <- @1){x} | @1!!(99)");
        let nfs: Vec<String> = results
            .normal_forms()
            .iter()
            .map(|nf| nf.display.clone())
            .collect();
        let any_with_99 = nfs.iter().any(|nf| nf.contains("99"));
        assert!(
            any_with_99,
            "expected some normal form containing 99 (the comm payload); got {:?}",
            nfs
        );
    }

    #[test]
    fn quote_short_paren_required_for_compound_proc() {
        // With `prefix(220)` on `NQuoteShort`, `@P`'s inner Proc parser is
        // capped well above all Proc-level infix BPs.  `*@1 + 0` therefore
        // parses as `(*@1) + 0`:
        //   * Proc parser sees `*` → PDrop, inner Name = NQuoteShort(1).
        //   * NQuoteShort folds to NQuote(1); Exec rewrites `*@1` to `1`.
        //   * Outer `+ 0` adds zero, constant-folds back to `1`.
        // Bare-form `*@(1+0)` (parens-form, no BP cap) still works of course.
        assert_reduces_to("*@1 + 0", "1");
        assert_reduces_to("*@(1 + 0)", "1");
    }

    #[test]
    fn quote_short_high_precedence_does_not_eat_par() {
        // `*@1 | 0` must parse as `(*@1) | 0` (a PPar of `*@1` and `0`),
        // not `*@(1 | 0)`.  Without the prefix BP cap the inner Proc would
        // greedily consume `| 0` into the quote.
        //
        // After fold: `*@1 → 1`, so the PPar reduces to `1 | 0` (which is
        // its own normal form modulo PPar multiset ordering).
        assert_reduces_to("*@1 | 0", "1 | 0");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Native operations (embedded Rust code)
// ════════════════════════════════════════════════════════════════════════════════

mod native_ops {
    use super::*;

    mod arithmetic {
        use super::*;

        #[test]
        fn int_add() {
            assert_reduces_to("1 + 2", "3");
        }
        #[test]
        fn int_sub() {
            assert_reduces_to("5 - 3", "2");
        }
        #[test]
        fn int_mul() {
            assert_reduces_to("3 * 4", "12");
        }
        #[test]
        fn int_div() {
            assert_reduces_to("10 / 2", "5");
        }

        #[test]
        fn float_add() {
            let results = run("1.5 + 2.5");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("4")),
                "1.5 + 2.5 should produce 4, got: {:?}",
                nfs
            );
        }

        #[test]
        fn float_literal_f64_suffix_tokens() {
            let results = run("1.0f64 + 0.5f64");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("1.5")),
                "expected 1.5 in a normal form, got: {:?}",
                nfs
            );
        }

        #[test]
        fn fixed_div_and_mod() {
            assert_reduces_to("10p1 / 3p1", "3.3p1");
            assert_reduces_to("10p1 % 3p1", "0.1p1");
        }

        #[test]
        fn fixed_bitand() {
            assert_reduces_to("5p0 bitand 3p0", "1p0");
        }

        #[test]
        fn fixed_bitor() {
            assert_reduces_to("5p0 bitor 3p0", "7p0");
        }

        #[test]
        fn fixed_comparisons() {
            assert_reduces_to("10p1 == 10.0p1", "true");
            assert_reduces_to("1p0 == 1.0p1", "true");
            assert_reduces_to("10p1 != 9p1", "true");
            assert_reduces_to("10p1 < 11p1", "true");
            assert_reduces_to("10p1 > 9p1", "true");
            assert_reduces_to("10p1 <= 10.0p1", "true");
            assert_reduces_to("10p1 >= 10.0p1", "true");
        }

        #[test]
        fn fixed_arithmetic_add_sub_mul() {
            assert_reduces_to("1p0 + 0.5p1", "1.5p1");
            assert_reduces_to("2.0p1 - 0.5p1", "1.5p1");
            assert_reduces_to("3p0 * 2p0", "6p0");
            assert_normal_form_display("-10p1", "-10.0p1");
        }

        #[test]
        fn fixed_div_by_zero_is_error() {
            assert_reduces_to("10p1 / 0p0", "error");
        }

        #[test]
        fn fixed_mod_by_zero_is_error() {
            assert_reduces_to("10p1 % 0p0", "error");
        }

        #[test]
        fn float_more_f64_suffix() {
            let results = run("1e2f64 + 1.0f64");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("101")),
                "expected 101 in a normal form, got: {:?}",
                nfs
            );
        }

        #[test]
        fn cast_to_int_float_bool_str_from_fixed() {
            assert_reduces_to("int(10p1, 64)", "10");
            assert_reduces_to("float(10p1, 64)", "10.0");
            assert_reduces_to("bool(0p0)", "false");
            assert_reduces_to("bool(1p0)", "true");
            assert_reduces_to(r#"str(1.5p1)"#, r#""1.5p1""#);
        }

        #[test]
        fn chained_add() {
            // fold evaluates full expression trees
            assert_reduces_to("1 + 2 + 3", "6");
        }

        #[test]
        fn negative_result() {
            let results = run("3 - 5");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("-2")),
                "3 - 5 should produce -2, got: {:?}",
                nfs
            );
        }

        #[test]
        fn bigint_add() {
            assert_reduces_to("1n + 2n", "3n");
        }

        #[test]
        fn u32_add() {
            assert_reduces_to("1u32 + 2u32", "3u32");
        }

        /// C analogy: `unsigned x = 0; x = x - 1` → `UINT_MAX`. Rust `u32` wraps in release; debug may panic.
        #[cfg(not(debug_assertions))]
        #[test]
        fn u32_sub_underflow_wraps_to_uint_max_in_release() {
            assert_reduces_to("0u32 - 1u32", "4294967295u32");
        }

        #[test]
        fn bigrat_add_normalized() {
            assert_reduces_to("3r/4r + 1r/4r", "1r");
        }

        #[test]
        fn int_literal_optional_i64_suffix() {
            assert_reduces_to("7i64 + 1", "8");
        }

        #[test]
        fn fraction_builds_rational() {
            assert_reduces_to("fraction(1n, 2n) + 1r/2r", "1r");
        }

        /// Regression: `fraction` must use `fold` on Proc (not `step`), or Ascent never emits rw_proc.
        ///
        /// ★ THE `r` TAIL (2026-07-26, divergence I(b)). `BigRat`'s declared pattern gained the
        /// leading `-?` that makes a sign-abutted rational one token (conformance with upstream
        /// `bigrat_literal /-?\d+r/`). `mandatory_literal_tail_of_pattern`
        /// (`macros/src/gen/syntax/display.rs`) refuses a tail for a SIGNED payload whose pattern
        /// cannot spell a negative value as one token — which is the ONLY reason `BigRat` had no
        /// tail while `BigInt` (`-?…n`) has had one since Stage C. That refusal names its own exit
        /// condition: *"giving them a tail is a separate grammar change (their pattern would have
        /// to gain `-?`, as `BigInt`'s already has)"*. This is that change, so the tail is now
        /// emitted, exactly as `bigint("123n")` below already records for the `n` tail.
        ///
        /// For a WHOLE rational the tail is a strict repair: `7r` now displays as `7r` and reads
        /// back as `CastBigRat(7)`, where the tail-less `7` read back as an `Int`.
        ///
        /// ★ THE COMPOSITE SPELLING (2026-07-27, divergence I(d) — ledger D2 in
        /// `languages/tests/literal_domain_agreement.rs`). The paragraph this replaces recorded a
        /// RESIDUE that has now been closed, and it is worth restating what it said, because the
        /// fix is the one it asked for:
        ///
        /// > for a COMPOSITE rational the tail is appended to `Ratio`'s own `n/d` rendering, so
        /// > `2/3` becomes `2/3r` … The only surface that spells that value is `2r/3r`. So the
        /// > display→parse fixpoint is STILL broken for composite rationals … The real defect is
        /// > that `mandatory_literal_tail_of_pattern`'s side condition (*"the pattern's language
        /// > covers EVERY value the native type can render"*) is checked only for the SIGN half,
        /// > never for the composite half; closing it belongs in `display.rs`, not in this
        /// > grammar.
        ///
        /// The side condition is now SATISFIED rather than needing to fire: `BigRat`'s declared
        /// pattern gained the composite `(/(…)r)?` group, so its language really does cover every
        /// value `CanonicalBigRat` can render, and the already-grammar-derived composite arm
        /// (`composite_repeat_of_optional_group`) puts the tail on each COMPONENT — `2r/3r`, the
        /// surface the residue note itself named as the only one that spells the value. No
        /// `display.rs` change was needed; the generator was right and the pattern was narrow.
        ///
        /// For a WHOLE rational the tail was already a strict repair: `7r` displays as `7r` and
        /// reads back as `CastBigRat(7)`, where the tail-less `7` read back as an `Int`.
        #[test]
        fn fraction_at_top_level_reduces() {
            assert_normal_form_display("fraction(2n, 3n)", "2r/3r");
            assert_normal_form_display("fraction(2n, 3n) + fraction(1n, 2n)", "7r/6r");
        }

        #[test]
        fn bigint_div_by_zero_is_error() {
            assert_reduces_to("1n / 0n", "error");
        }
    }

    mod bitwise {
        use super::*;

        #[test]
        fn int_and_or_not() {
            assert_reduces_to("5 bitand 3", "1");
            assert_reduces_to("5 bitor 3", "7");
            let results = run("bitnot 0");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1"),
                "expected `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn u32_and_or_not() {
            // ★ COMMENT REWRITTEN 2026-07-25 (divergence I). The assertions survive, but for a
            // NEW reason. They are spelled through the `uint(_, 32)` cast because that is the ONLY
            // way to reach the 32-bit wraparound carrier — not, as the old comment had it, because
            // a `u32`-suffixed literal was being mis-carried. `0u32` is an `i64` literal written
            // with a `u32` suffix (f1r3node's `normalize_ground`: `bits <= 64 && value <=
            // i64::MAX ⟹ GInt`), so `bitnot 0u32` is `-1` BY CONSTRUCTION; that is pinned by
            // `numeral_carrier_is_context_independent::u32_suffix_is_an_i64_literal`.
            assert_reduces_to("uint(5, 32) bitand uint(3, 32)", "1");
            assert_reduces_to("uint(5, 32) bitor uint(3, 32)", "7");
            assert_reduces_to("bitnot uint(0, 32)", "4294967295");
        }

        #[test]
        fn bigint_and_or_not() {
            assert_reduces_to("3n bitand 1n", "1n");
            assert_reduces_to("3n bitor 1n", "3n");
            let results = run("bitnot 0n");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1n" || nf == "-1"),
                "expected `-1n` or `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn bigrat_and_or_not() {
            // The `r` tail on a composite rational, one per COMPONENT — derived, and fully
            // argued at [`super::arithmetic::fraction_at_top_level_reduces`]. These two rows
            // also demonstrate that divergence I(d) is value-preserving: the SOURCE operands
            // are now single composite literals where they used to be `Div` folds, and the
            // answers are unchanged.
            assert_normal_form_display("3r/4r bitand 1r/4r", "1r/4r");
            assert_normal_form_display("1r/2r bitand 1r/3r", "1r/3r");
            let results = run("bitnot 0r");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1r" || nf == "-1"),
                "expected `-1r` (or `-1`) in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn fixed_and_or_not() {
            assert_normal_form_display("bitnot 0p0", "-1p0");
            assert_reduces_to("15p0 bitand 14p1", "13.2p1");
        }

        #[test]
        fn type_mismatch_bitand_is_error() {
            assert_reduces_to("1 bitand 1.0", "error");
            assert_reduces_to("1 bitand true", "error");
        }

        #[test]
        fn type_mismatch_bitnot_is_error() {
            assert_reduces_to("bitnot true", "error");
        }

        #[test]
        fn bitnot_under_congruence_smoke() {
            let results = run("bitnot *(@(0))");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1"),
                "expected `-1` in normal forms, got: {:?}",
                nfs
            );
        }
    }

    mod comparison {
        use super::*;

        #[test]
        fn eq_true() {
            assert_reduces_to("1 == 1", "true");
        }

        #[test]
        fn eq_rational_slash_binds_tighter_than_eq() {
            // Regression: `==` must not bind tighter than `/` (would parse as `15/(6==30)/12`).
            assert_reduces_to("15r/6r == 30r/12r", "true");
        }
        #[test]
        fn eq_false() {
            assert_reduces_to("1 == 2", "false");
        }
        #[test]
        fn ne() {
            assert_reduces_to("1 != 2", "true");
        }
        #[test]
        fn gt() {
            assert_reduces_to("3 > 2", "true");
        }
        #[test]
        fn lt() {
            assert_reduces_to("2 < 3", "true");
        }
        #[test]
        fn gte() {
            assert_reduces_to("3 >= 3", "true");
        }
        #[test]
        fn lte() {
            assert_reduces_to("2 <= 3", "true");
        }

        #[test]
        fn bigint_gt() {
            assert_reduces_to("2n > 1n", "true");
        }

        #[test]
        fn u32_eq() {
            assert_reduces_to("3u32 == 3u32", "true");
        }

        #[test]
        fn str_eq() {
            assert_reduces_to(r#""abc" == "abc""#, "true");
        }

        #[test]
        fn str_ne() {
            assert_reduces_to(r#""abc" != "abd""#, "true");
        }

        #[test]
        fn str_gt_lexicographic() {
            assert_reduces_to(r#""b" > "a""#, "true");
        }

        #[test]
        fn str_lt_lexicographic() {
            assert_reduces_to(r#""apple" < "banana""#, "true");
        }

        #[test]
        fn str_gte() {
            assert_reduces_to(r#""abc" >= "abc""#, "true");
        }

        #[test]
        fn str_lte() {
            assert_reduces_to(r#""abc" <= "abc""#, "true");
        }
    }

    mod boolean {
        use super::*;

        #[test]
        fn not_true() {
            assert_reduces_to("not true", "false");
        }
        #[test]
        fn not_false() {
            assert_reduces_to("not false", "true");
        }
        #[test]
        fn and_tt() {
            assert_reduces_to("true and true", "true");
        }
        #[test]
        fn and_tf() {
            assert_reduces_to("true and false", "false");
        }
        #[test]
        fn or_ff() {
            assert_reduces_to("false or false", "false");
        }
        #[test]
        fn or_tf() {
            assert_reduces_to("true or false", "true");
        }
    }

    mod string {
        use super::*;

        #[test]
        fn concat() {
            assert_reduces_to(r#""hello".concat("world")"#, r#""helloworld""#);
        }

        #[test]
        fn length_method() {
            assert_reduces_to(r#""hello".length()"#, "5");
        }
    }

    mod bag {
        use super::*;

        /// `(*(bag)).remove(*(elem))` after comm: removes one occurrence of elem from bag
        #[test]
        fn remove_comm() {
            assert_reduces_to(
                "a!(#{1|2|2}#) | c!(2) | for(b <- a & e <- c){(*(b)).remove(*(e))}",
                "#{1|2}#",
            );
        }

        /// `(*(bag)).count(*(elem))` after comm: counts occurrences of elem in bag
        #[test]
        fn count_comm() {
            assert_reduces_to(
                "a!(#{1|2|2}#) | c!(2) | for(b <- a & e <- c){(*(b)).count(*(e))}",
                "2",
            );
        }

        // ── Rholang-style method-call sugars on Bag literals.
        //
        // Bag has no Rholang counterpart, so the literal stays `#{a|b|…}#`,
        // but the method surface mirrors Map/List for a uniform feel.

        #[test]
        fn bag_size_method() {
            assert_reduces_to("#{1|2|2}#.size()", "3");
        }

        #[test]
        fn bag_count_method() {
            assert_reduces_to("#{1|2|2}#.count(2)", "2");
            assert_reduces_to("#{1|2|2}#.count(7)", "0");
        }

        #[test]
        fn bag_diff_method() {
            // Method sugar lowers to `DiffBag`. Full
            // literal fold for `DiffBag` is not yet reachable in the Ascent
            // normal-form search used by `assert_reduces_to`; this test only
            // guards against the old `multiset_eq` false positive that treated
            // unrelated non-`PPar` displays as equal.
            assert_min_rewrites("#{1|2|2}#.diff(#{2}#)", 1);
        }

        #[test]
        fn bag_remove_method() {
            assert_reduces_to("#{1|2|2}#.remove(2)", "#{1|2}#");
        }

        #[test]
        fn bag_union_method_polymorphic_to_unionbag() {
            // `.union(other)` dispatches by receiver: for a `CastBag` we lower
            // to `UnionBag`. Result has six elements: `{1,2,2} ∪ {2,3,3} = {1,2,2,2,3,3}`.
            assert_reduces_to("#{1|2|2}#.union(#{2|3|3}#).size()", "6");
        }
    }

    mod list {
        use super::*;

        #[test]
        fn list_nth_method_surface() {
            assert_reduces_to("[10, 20, 30].nth(1)", "20");
        }

        #[test]
        fn list_concat_method_surface() {
            assert_reduces_to("[1, 2].concat([3, 4])", "[1, 2, 3, 4]");
        }

        // ── Rholang-style method-call sugars.

        #[test]
        fn list_length_method() {
            assert_reduces_to("[1, 2, 3].length()", "3");
            assert_reduces_to("[].length()", "0");
        }

        #[test]
        fn list_nth_method() {
            assert_reduces_to("[10, 20, 30].nth(0)", "10");
            assert_reduces_to("[10, 20, 30].nth(2)", "30");
        }

        #[test]
        fn list_concat_method() {
            assert_reduces_to("[1, 2].concat([3, 4])", "[1, 2, 3, 4]");
        }

        #[test]
        fn list_concat_chain_length() {
            // Chained method calls round-trip: the receiver of the second `.length()`
            // is the result of `[1,2].concat([3,4])`, which fully folds to `[1,2,3,4]`.
            assert_reduces_to("[1, 2].concat([3, 4]).length()", "4");
        }

        #[test]
        fn list_nth_after_concat() {
            assert_reduces_to("[1, 2].concat([3, 4]).nth(2)", "3");
        }
    }

    mod map {
        use super::*;

        // Method-call sugar on Map literals (`Map()` is the empty-map alias for `{}`).

        #[test]
        fn map_size_empty() {
            assert_reduces_to("Map().size()", "0");
        }

        #[test]
        fn map_size_one() {
            assert_reduces_to("{1:2}.size()", "1");
        }

        #[test]
        fn map_get_method() {
            assert_reduces_to("{1:10}.get(1)", "10");
        }

        #[test]
        fn map_get_method_on_method_chain() {
            // Regression: `Map().set(1, 10).get(1)` previously appeared to pass
            // because `10` is a literal sub-term that happens to be a reachable
            // normal form. Now the chain genuinely reduces:
            // `Map().set(1, 10).get(1) → get(put({}, 1, 10), 1) → 10`.
            assert_reduces_to("Map().set(1, 10).get(1)", "10");
        }

        #[test]
        fn map_set_method_chained() {
            assert_reduces_to("Map().set(1, 10).get(1)", "10");
        }

        #[test]
        fn map_union_method() {
            assert_reduces_to("{1:10}.union({2:20}).get(2)", "20");
        }

        #[test]
        fn map_contains_method() {
            assert_reduces_to("{1:2}.contains(1)", "true");
            assert_reduces_to("{1:2}.contains(3)", "false");
        }

        #[test]
        fn map_keys_size() {
            assert_reduces_to("{1:10, 2:20}.keys().size()", "2");
        }

        #[test]
        fn map_values_nth_method() {
            assert_reduces_to("{1:10, 2:20}.values().nth(0)", "10");
        }

        #[test]
        fn map_delete_method() {
            assert_reduces_to("{1:10, 2:20}.delete(1).size()", "1");
            assert_reduces_to("{1:10, 2:20}.delete(1).get(2)", "20");
        }

        #[test]
        fn map_size_method() {
            assert_reduces_to("Map().size()", "0");
            assert_reduces_to("{1:10}.size()", "1");
            assert_reduces_to("{1:10, 2:20}.size()", "2");
        }

        #[test]
        fn map_set_chain_reduces_to_literal() {
            // Regression: chained `.set` must fold all the way to a Map literal
            // (was previously stuck as the unfolded method-call chain because
            // the macro skipped fold rule generation for zero-arg constructors
            // like `MapEmpty`).
            assert_reduces_to("Map().set(1, 10).set(2, 20)", "{1: 10, 2: 20}");
        }

        #[test]
        fn map_size_method_chained() {
            assert_reduces_to("Map().set(1, 10).set(2, 20).size()", "2");
        }

        #[test]
        fn map_keys_method() {
            assert_reduces_to("{1:10, 2:20}.keys().size()", "2");
        }

        #[test]
        fn map_values_method() {
            assert_reduces_to("{1:10, 2:20}.values().nth(0)", "10");
        }

        #[test]
        fn pathmap_get() {
            assert_reduces_to("{| 1 |}.get(1)", "1");
        }

        #[test]
        fn pathmap_put() {
            assert_reduces_to("{| |}.set(1, 10).get(1)", "10");
        }

        #[test]
        fn pathmap_put_list_path() {
            assert_reduces_to("{| |}.set([1,2], 10).get([1,2])", "10");
        }

        #[test]
        fn pathmap_merge() {
            assert_reduces_to("{| 1 |}.union({| 2 |}).get(2)", "2");
        }

        #[test]
        fn pathmap_merge_list_path() {
            assert_reduces_to("{| [1,2] |}.union({| [3,4] |}).get([3,4])", "[3,4]");
        }

        #[test]
        fn pathmap_has() {
            assert_reduces_to("{| 1 |}.contains(1)", "true");
            assert_reduces_to("{| 1 |}.contains(3)", "false");
        }

        #[test]
        fn pathmap_list_path_get() {
            assert_reduces_to("{| [1,2] |}.get([1,2])", "[1,2]");
        }

        #[test]
        fn pathmap_list_path_has() {
            assert_reduces_to("{| [1,2] |}.contains([1,2])", "true");
            assert_reduces_to("{| [1,2] |}.contains([1,3])", "false");
        }

        /// Trie distinguishes full path from strict prefix (no value at prefix alone).
        #[test]
        fn pathmap_prefix_path_not_confused_with_longer_path() {
            assert_reduces_to("{| [1,2] |}.contains([1])", "false");
            assert_reduces_to("{| [1,2] |}.contains([1,2])", "true");
            assert_reduces_to("{| [1,2] |}.get([1,2])", "[1,2]");
        }

        #[test]
        fn pathmap_restrict() {
            assert_reduces_to("{| [1,2], [3,4] |}.restrict({| [3,4] |}).contains([3,4])", "true");
            assert_reduces_to("{| [1,2], [3,4] |}.restrict({| [3,4] |}).contains([1,2])", "false");
        }

        #[test]
        fn pathmap_subtract() {
            assert_reduces_to("{| [1,2], [3,4] |}.subtract({| [3,4] |}).contains([3,4])", "false");
            assert_reduces_to("{| [1,2], [3,4] |}.subtract({| [3,4] |}).contains([1,2])", "true");
        }

        #[test]
        fn pathmap_meet_uses_right_value_on_overlap() {
            assert_reduces_to(
                "{| |}.set([1,2], 10).set([3,4], 20).meet({| |}.set([3,4], 200).set([5,6], 1)).get([3,4])",
                "200",
            );
            assert_reduces_to(
                "{| |}.set([1,2], 10).set([3,4], 20).meet({| |}.set([3,4], 200).set([5,6], 1)).contains([1,2])",
                "false",
            );
        }

        #[test]
        fn pattern_comm_pathmap_literal_matches() {
            assert_reduces_to(r#"{for(@{| ["k"] |} <- c){1} | c!({| ["k"] |})}"#, "1");
        }

        #[test]
        fn pattern_comm_pathmap_literal_blocks_key_mismatch() {
            assert_never_reaches(r#"{for(@{| ["k"] |} <- c){999} | c!({| ["j"] |})}"#, "999");
        }

        /// SPEC §E: empty, atom, single-element list, prefix overlap.
        #[test]
        fn pathmap_spec_edge_literals() {
            assert_reduces_to("{| |}.contains(1)", "false");
            assert_reduces_to("{| 42 |}.get(42)", "42");
            assert_reduces_to(
                r#"{| ["some string"] |}.get(["some string"])"#,
                r#"["some string"]"#,
            );
            assert_reduces_to("{| [1,2], [1,2,3] |}.contains([1,2])", "true");
            assert_reduces_to("{| [1,2], [1,2,3] |}.contains([1,2,3])", "true");
        }

        mod pathmap_algebra {
            use super::*;

            // intersection / meet
            #[test]
            fn pathmap_meet_keeps_overlap_with_right_values() {
                assert_reduces_to(
                    "{| |}.set([1,2], 10).set([3,4], 20).meet({| |}.set([1,2], 200).set([5,6], 1)).get([1,2])",
                    "200",
                );
                assert_reduces_to(
                    "{| |}.set([1,2], 10).set([3,4], 20).meet({| |}.set([1,2], 200).set([5,6], 1)).contains([3,4])",
                    "false",
                );
                assert_reduces_to(
                    "{| |}.set([1,2], 10).set([3,4], 20).meet({| |}.set([1,2], 200).set([5,6], 1)).contains([5,6])",
                    "false",
                );
            }

            // diff / subtract
            #[test]
            fn pathmap_subtract_removes_masked_branch() {
                assert_reduces_to(
                    "{| [1,2], [1,3], [4,5] |}.subtract({| [1,2] |}).contains([1,2])",
                    "false",
                );
                assert_reduces_to(
                    "{| [1,2], [1,3], [4,5] |}.subtract({| [1,2] |}).contains([1,3])",
                    "true",
                );
            }

            // restriction
            #[test]
            fn pathmap_restrict_keeps_only_masked_paths() {
                assert_reduces_to(
                    "{| [1,2], [1,3], [4,5] |}.restrict({| [1,2], [1,3] |}).contains([1,2])",
                    "true",
                );
                assert_reduces_to(
                    "{| [1,2], [1,3], [4,5] |}.restrict({| [1,2], [1,3] |}).contains([4,5])",
                    "false",
                );
            }
        }

        mod zipper {
            use super::*;

            fn task_db() -> &'static str {
                "{| [1,2,3], [1,2,4], [2,1] |}"
            }

            fn users_age_db() -> &'static str {
                "{| [1,1,1,1], [1,2,1,1], [1,3,1,1] |}"
            }

            fn books_fiction_db() -> &'static str {
                concat!(
                    "{| ",
                    r#"["books","fiction","gatsby"], "#,
                    r#"["books","fiction","moby"], "#,
                    r#"["books","nonfiction","history"] |}"#
                )
            }

            fn nested_root_db() -> &'static str {
                "{| [1,1,1], [1,1,2], [1,2,1] |}"
            }

            fn normal_forms_contain(input: &str, fragment: &str) {
                let (results, initial_id) = run_with_initial(input);
                let nfs = reachable_normal_form_displays(&results, initial_id);
                assert!(
                    nfs.iter().any(|nf| nf.contains(fragment)),
                    "expected normal form containing `{fragment}` for `{input}`\n  nfs: {nfs:?}"
                );
            }

            // query backend tasks via subtrie
            #[test]
            fn pathmap_demo_queries_backend_subtrie() {
                let db = task_db();
                assert_reduces_to(&format!("{{{}.getSubtrieAt([1]).get([2,3])}}", db), "[1,2,3]");
                assert_reduces_to(
                    &format!("{{{}.readZipperAt([1]).getSubtrie().get([2,4])}}", db),
                    "[1,2,4]",
                );
            }

            // complete a deep leaf via writeZipperSetLeaf
            #[test]
            fn pathmap_demo_set_leaf_on_deep_path() {
                let db = task_db();
                assert_reduces_to(
                    &format!("{{{}.writeZipperAt([2,1]).setLeaf([2,1], 99).get([2,1])}}", db),
                    "99",
                );
            }

            // replace subtree at prefix (numeric and string path segments)
            #[test]
            fn pathmap_demo_replace_subtrie_at_prefix() {
                let db = task_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1]).setSubtrie({{| [9], [8] |}}).contains([1,9])}}",
                        db
                    ),
                    "true",
                );
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1]).setSubtrie({{| [9], [8] |}}).contains([1,2,3])}}",
                        db
                    ),
                    "false",
                );

                let db = books_fiction_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([\"books\",\"fiction\"]).setSubtrie({{| [\"hemingway\"], [\"lovecraft\"] |}}).contains([\"books\",\"fiction\",\"hemingway\"])}}",
                        db
                    ),
                    "true",
                );
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([\"books\",\"fiction\"]).setSubtrie({{| [\"hemingway\"], [\"lovecraft\"] |}}).contains([\"books\",\"fiction\",\"gatsby\"])}}",
                        db
                    ),
                    "false",
                );
            }

            // graft external read zipper at root
            #[test]
            fn pathmap_demo_graft_at_root() {
                assert_reduces_to(
                    concat!(
                        "{",
                        "{| [1] |}.writeZipper().graft(",
                        "{| [2,3], [4] |}.readZipper()).get([4])}",
                    ),
                    "[4]",
                );
            }

            // read/write zipper constructors
            #[test]
            fn tut_zipper_constructors_fold_to_tokens() {
                let db = task_db();
                normal_forms_contain(&format!("{{{}.readZipper()}}", db), "readZipper@");
                normal_forms_contain(&format!("{{{}.writeZipper()}}", db), "writeZipper@");
                normal_forms_contain(&format!("{{{}.readZipperAt([1])}}", db), "readZipper@");
            }

            // descendTo then getLeaf
            #[test]
            fn tut_zipper_descend_to_leaf() {
                let db = books_fiction_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.readZipper().descendTo([\"books\",\"fiction\",\"gatsby\"]).getLeaf()}}",
                        db
                    ),
                    r#"["books","fiction","gatsby"]"#,
                );
            }

            // root getLeaf on map without root value
            #[test]
            fn tut_zipper_root_get_leaf_stays_stuck() {
                let db = task_db();
                normal_forms_contain(&format!("{{{}.readZipper().getLeaf()}}", db), ".getLeaf(");
            }

            // getSubtrie at root and getSubtrieAt on prefix path
            #[test]
            fn tut_path_get_subtrie_root_and_prefix() {
                let db = books_fiction_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.getSubtrie().contains([\"books\",\"fiction\",\"gatsby\"])}}",
                        db
                    ),
                    "true",
                );
                assert_reduces_to(
                    &format!(
                        "{{{}.getSubtrieAt([\"books\",\"fiction\"]).contains([\"moby\"])}}",
                        db
                    ),
                    "true",
                );
            }

            // writeZipper on empty map
            #[test]
            fn tut_write_zipper_set_leaf_on_empty_map() {
                assert_reduces_to("{| |}.writeZipper().setLeaf([1,2], 42).get([1,2])", "42");
            }

            // setSubtrie at root replaces entire map
            #[test]
            fn tut_write_zipper_set_subtrie_at_root() {
                assert_reduces_to(
                    "{| [1], [2] |}.writeZipper().setSubtrie({| [9], [8] |}).get([9])",
                    "[9]",
                );
                assert_reduces_to(
                    "{| [1], [2] |}.writeZipper().setSubtrie({| [9], [8] |}).contains([1])",
                    "false",
                );
            }

            // empty relative subtrie clears focused branch
            #[test]
            fn tut_write_zipper_set_empty_subtrie_clears_branch() {
                let db = nested_root_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,1]).setSubtrie({{| |}}).contains([1,1,1])}}",
                        db
                    ),
                    "false",
                );
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,1]).setSubtrie({{| |}}).contains([1,2,1])}}",
                        db
                    ),
                    "true",
                );
            }

            // graft at focused prefix
            #[test]
            fn tut_write_zipper_graft_at_prefix() {
                assert_reduces_to(
                    concat!(
                        "{",
                        "{| [1] |}.writeZipperAt([1]).graft(",
                        "{| [2], [3] |}.readZipper()).get([1,3])}",
                    ),
                    "[3]",
                );
            }

            // setSubtrie leaves original unchanged
            #[test]
            fn immutability_set_subtrie_preserves_original() {
                let original = nested_root_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,1]).setSubtrie({{| [9] |}}).get([1,1,9])}}",
                        original
                    ),
                    "[9]",
                );
                assert_reduces_to(&format!("{{{}.get([1,1,1])}}", original), "[1,1,1]");
            }

            // removeLeaf leaves original unchanged
            #[test]
            fn immutability_remove_leaf_preserves_original() {
                let original = "{| [1,1], [1,2], [2] |}";
                assert_reduces_to(
                    &format!("{{{}.writeZipperAt([1,1]).removeLeaf().contains([1,1])}}", original),
                    "false",
                );
                assert_reduces_to(&format!("{{{}.get([1,1])}}", original), "[1,1]");
            }

            // removeBranches leaves original unchanged
            #[test]
            fn immutability_remove_branches_preserves_original() {
                let original = nested_root_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1]).removeBranches().contains([1,1,1])}}",
                        original
                    ),
                    "false",
                );
                assert_reduces_to(&format!("{{{}.get([1,1,1])}}", original), "[1,1,1]");
            }

            // graft leaves original unchanged
            #[test]
            fn immutability_graft_preserves_original() {
                let original = "{| [1] |}";
                let source = "{| [2,1] |}";
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipper().graft({}.readZipper()).get([2,1])}}",
                        original, source
                    ),
                    "[2,1]",
                );
                assert_reduces_to(&format!("{{{}.get([1])}}", original), "[1]");
                assert_reduces_to(&format!("{{{}.get([2,1])}}", source), "[2,1]");
            }

            // joinInto leaves original unchanged
            #[test]
            fn immutability_join_into_preserves_original() {
                let original = "{| [1,2] |}";
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipper().joinInto({{| [1,2], [3] |}}.readZipper()).get([3])}}",
                        original
                    ),
                    "[3]",
                );
                assert_reduces_to(&format!("{{{}.get([1,2])}}", original), "[1,2]");
            }

            // descendFirst from users prefix
            #[test]
            fn navigation_descend_first_from_users_prefix() {
                let db = users_age_db();
                normal_forms_contain(
                    &format!("{{{}.readZipperAt([1]).descendFirst()}}", db),
                    "readZipper@",
                );
            }

            // indexed branch under users
            #[test]
            fn navigation_descend_indexed_branch_from_users() {
                let db = users_age_db();
                normal_forms_contain(
                    &format!("{{{}.readZipperAt([1]).descendIndexedBranch(1)}}", db),
                    "readZipper@",
                );
            }

            // ascend from deep path
            #[test]
            fn navigation_ascend_from_deep_path() {
                let db = users_age_db();
                normal_forms_contain(
                    &format!("{{{}.readZipperAt([1,2,1,1]).ascend(2)}}", db),
                    "readZipper@",
                );
            }

            // invalid sibling navigation stays stuck
            #[test]
            fn navigation_invalid_sibling_stays_stuck() {
                let db = users_age_db();
                normal_forms_contain(
                    &format!("{{{}.readZipperAt([1,1,1,1]).toNextSibling()}}", db),
                    ".toNextSibling(",
                );
            }

            #[test]
            fn path_get_subtrie_at_prefix() {
                assert_reduces_to(
                    &format!("{{{}.getSubtrieAt([1]).contains([2,3])}}", task_db()),
                    "true",
                );
                assert_reduces_to(
                    &format!("{{{}.getSubtrieAt([1]).contains([2,4])}}", task_db()),
                    "true",
                );
                assert_reduces_to(
                    &format!("{{{}.getSubtrieAt([1]).contains([2])}}", task_db()),
                    "false",
                );
            }

            #[test]
            fn read_zipper_get_subtrie_at_prefix() {
                assert_reduces_to(
                    &format!("{{{}.readZipperAt([1]).getSubtrie().get([2,3])}}", task_db()),
                    "[1,2,3]",
                );
            }

            #[test]
            fn write_zipper_set_leaf_updates_full_path() {
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,2]).setLeaf([1,2,3], 99).get([1,2,3])}}",
                        task_db()
                    ),
                    "99",
                );
            }

            #[test]
            fn write_zipper_set_subtrie_at_focus() {
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1]).setSubtrie({{| [9], [8] |}}).get([1,9])}}",
                        task_db()
                    ),
                    "[9]",
                );
            }

            #[test]
            fn write_zipper_join_into_right_biased_overlap() {
                assert_reduces_to(
                    concat!(
                        "{",
                        "{| [1,2] |}.writeZipper().joinInto(",
                        "{| [1,2], [3] |}.readZipper()).get([1,2])}",
                    ),
                    "[1,2]",
                );
                assert_reduces_to(
                    concat!(
                        "{",
                        "{| [1,2] |}.writeZipper().joinInto(",
                        "{| [1,2], [3] |}.readZipper()).get([3])}",
                    ),
                    "[3]",
                );
            }

            #[test]
            fn write_zipper_remove_leaf_and_branches() {
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,2,3]).removeLeaf().contains([1,2,3])}}",
                        task_db()
                    ),
                    "false",
                );
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1]).removeBranches().contains([1,2,3])}}",
                        task_db()
                    ),
                    "false",
                );
            }

            #[test]
            fn write_zipper_graft_merges_source_subtrie() {
                assert_reduces_to(
                    concat!(
                        "{",
                        "{| [1] |}.writeZipper().graft(",
                        "{| [2,3] |}.readZipper()).get([2,3])}",
                    ),
                    "[2,3]",
                );
            }

            #[test]
            fn write_zipper_ops_leave_original_pathmap_unchanged() {
                let original = task_db();
                assert_reduces_to(
                    &format!(
                        "{{{}.writeZipperAt([1,2]).setLeaf([1,2,3], 99).get([1,2,3])}}",
                        original
                    ),
                    "99",
                );
                assert_reduces_to(&format!("{{{}.get([1,2,3])}}", original), "[1,2,3]");
            }

            #[test]
            fn zipper_navigation_child_count_and_moves() {
                let db = users_age_db();
                assert_reduces_to(&format!("{{{}.readZipperAt([1]).childCount()}}", db), "3");
                // `readZipperAt([1])` then a RELATIVE `descendTo([1,1,1])` lands on the key
                // `[1,1,1,1]`. The previous relative path `[1,1]` lands on `[1,1,1]`, which is
                // not a key of `users_age_db()`, so `getLeaf()` was correctly stuck — the test
                // asserted a successful navigation while navigating nowhere.
                assert_reduces_to(
                    &format!("{{{}.readZipperAt([1]).descendTo([1,1,1]).getLeaf()}}", db),
                    "[1,1,1,1]",
                );
            }

            // ── ReadZipper ENUMERATION (getPath / toNextLeaf / leafCount) ──
            //
            // Surface-level pins. The semantics are pinned as unit tests in
            // `languages/src/rhocalc/zipper.rs`; these assert the three methods
            // parse and reduce THROUGH THE GRAMMAR, which is what a program
            // written against the FIPS lookahead result actually depends on.

            fn walk_db() -> &'static str {
                "{| [1,2,3]:100, [1,2,4]:200, [2,1]:300 |}"
            }

            /// `leafCount()` is the map's cardinality at the root and the
            /// branch's result count at a prefix — the decidable bound that
            /// terminates a `toNextLeaf` walk.
            #[test]
            fn zipper_leaf_count_is_the_walk_bound() {
                assert_reduces_to(&format!("{{{}.readZipper().leafCount()}}", walk_db()), "3");
                assert_reduces_to(&format!("{{{}.readZipperAt([1]).leafCount()}}", walk_db()), "2");
            }

            /// `leafCount()` steps of `toNextLeaf()` visit every entry exactly
            /// once, in depth-first order, and BOTH `getPath()` and `getLeaf()`
            /// reduce at every stop.
            #[test]
            fn zipper_leaf_walk_visits_every_entry_in_order() {
                let db = walk_db();
                for (steps, path, leaf) in
                    [(1, "[1,2,3]", "100"), (2, "[1,2,4]", "200"), (3, "[2,1]", "300")]
                {
                    let walk = ".toNextLeaf()".repeat(steps);
                    assert_reduces_to(&format!("{{{db}.readZipper(){walk}.getPath()}}"), path);
                    assert_reduces_to(&format!("{{{db}.readZipper(){walk}.getLeaf()}}"), leaf);
                }
            }

            /// ★ The step past the last leaf STAYS STUCK — it must not wrap to
            /// the first, because `to_next_val()` resets the zipper to the root
            /// on exhaustion and a returning form would loop forever.
            ///
            /// The reducer signals this same condition as `Nil`; C1 must
            /// translate it back to this stuck form. See the CROSS-ENDPOINT
            /// CONTRACT block in `languages/src/rhocalc/zipper.rs` and its
            /// f1r3node twin `to_next_leaf_returns_nil_when_exhausted`.
            #[test]
            fn zipper_leaf_walk_exhaustion_stays_stuck() {
                let src = format!(
                    "{{{}.readZipper().toNextLeaf().toNextLeaf().toNextLeaf().toNextLeaf()}}",
                    walk_db()
                );
                let (results, initial_id) = run_with_initial(&src);
                let nfs = reachable_normal_form_displays(&results, initial_id);
                assert!(
                    nfs.iter().any(|nf| nf.contains(".toNextLeaf(")),
                    "exhaustion must stay stuck, never wrap to the first leaf: {nfs:?}"
                );
            }

            /// The cursor key round-trips: `m.get(z.getPath())` is `z.getLeaf()`.
            #[test]
            fn zipper_get_path_round_trips_through_the_map() {
                let db = walk_db();
                assert_reduces_to(
                    &format!("{{{db}.get({db}.readZipper().toNextLeaf().getPath())}}"),
                    "100",
                );
            }

            /// `getPath()` yields a LIST at every arity, so a trace is
            /// indexable — which is what `trace.nth(…)` / `trace.length()` in
            /// the FIPS lookahead examples require.
            #[test]
            fn zipper_get_path_is_an_indexable_list() {
                let db = walk_db();
                assert_reduces_to(
                    &format!("{{{db}.readZipper().toNextLeaf().getPath().length()}}"),
                    "3",
                );
                assert_reduces_to(
                    &format!("{{{db}.readZipper().toNextLeaf().getPath().nth(0)}}"),
                    "1",
                );
            }

            /// Scoping an enumeration is ALGEBRAIC: `getSubtrieAt(p)` yields a
            /// `Pathmap` of just that branch, whose `readZipper()` walks exactly
            /// it (with keys relative to `p`). Walking from a zipper parked at a
            /// strict prefix also stays in the branch, because prefix-sharing
            /// keys are contiguous in depth-first order — there it reports
            /// ABSOLUTE keys.
            #[test]
            fn zipper_scoped_enumeration_two_ways() {
                let db = walk_db();
                assert_reduces_to(
                    &format!("{{{db}.getSubtrieAt([1]).readZipper().leafCount()}}"),
                    "2",
                );
                assert_reduces_to(
                    &format!("{{{db}.getSubtrieAt([1]).readZipper().toNextLeaf().getPath()}}"),
                    "[2,3]",
                );
                assert_reduces_to(
                    &format!("{{{db}.readZipperAt([1]).toNextLeaf().getPath()}}"),
                    "[1,2,3]",
                );
            }

            #[test]
            fn zipper_navigation_stays_stuck_on_failed_moves() {
                let nfs = reachable_normal_form_displays(
                    &run_with_initial("{| |}.set([1], 10).readZipperAt([1]).descendFirst()").0,
                    run_with_initial("{| |}.set([1], 10).readZipperAt([1]).descendFirst()").1,
                );
                assert!(
                    nfs.iter().any(|nf| nf.contains(".descendFirst(")),
                    "failed navigation should not rewrite to error: {nfs:?}"
                );
            }

            #[test]
            fn pathmap_encoding_rejects_empty_list_path_in_native_ops() {
                let nfs = reachable_normal_form_displays(
                    &run_with_initial("{ {| |}.set([], 1) }").0,
                    run_with_initial("{ {| |}.set([], 1) }").1,
                );
                assert!(
                    nfs.iter().any(|nf| nf.contains(".set(")),
                    "invalid path encoding should not silently produce a pathmap: {nfs:?}"
                );
            }

            #[test]
            fn map_and_pathmap_literals_stay_distinct() {
                // Map: `{ k: v }`; Pathmap: `{| elem, ... |}`.
                assert_reduces_to("{{1:10}.get(1)}", "10");
                assert_reduces_to("{| 1 |}.get(1)", "1");
                assert_reduces_to("{{1:2}.contains(1)}", "true");
                assert_reduces_to("{| 1 |}.contains(1)", "true");
            }
        }
    }

    mod set {
        use super::*;

        #[test]
        fn set_size_literal() {
            assert_reduces_to("Set(1, 2, 3).size()", "3");
        }

        #[test]
        fn set_literal_allows_space_before_paren() {
            assert_reduces_to("Set (1, 2, 3).size()", "3");
        }

        #[test]
        fn set_empty_literal() {
            assert_reduces_to("Set().size()", "0");
        }

        #[test]
        fn set_deduplicates_on_parse() {
            assert_reduces_to("Set(1, 1, 2).size()", "2");
        }

        #[test]
        fn set_add_method() {
            assert_reduces_to("Set(1, 2).add(3).size()", "3");
        }

        #[test]
        fn set_delete_method() {
            assert_reduces_to("Set(1, 2, 3).delete(2).size()", "2");
        }

        #[test]
        fn set_contains_method() {
            assert_reduces_to("Set(1, 2).contains(2)", "true");
            assert_reduces_to("Set(1, 2).contains(3)", "false");
        }

        #[test]
        fn set_union_method() {
            assert_reduces_to("Set(1, 2).union(Set(2, 3)).size()", "3");
        }

        #[test]
        fn set_diff_method() {
            assert_reduces_to("Set(1, 2, 3).diff(Set(1, 4)).size()", "2");
        }

        #[test]
        fn set_size_method() {
            assert_reduces_to("Set(1, 2, 3).size()", "3");
        }

        #[test]
        fn set_union_method_polymorphic_to_unionset() {
            assert_reduces_to("Set(1, 2).union(Set(2, 3)).contains(3)", "true");
        }

        #[test]
        fn set_equality_is_order_independent() {
            assert_reduces_to("Set(1, 2, 3) == Set(3, 2, 1)", "true");
        }
    }

    mod collection_equality {
        use super::*;

        #[test]
        fn list_equal_same_order() {
            assert_reduces_to("[1, 2] == [1, 2]", "true");
        }

        #[test]
        fn list_unequal_order() {
            assert_reduces_to("[1, 2] == [2, 1]", "false");
        }

        #[test]
        fn list_unequal_duplicates() {
            assert_reduces_to("[1, 1, 2] != [1, 2]", "true");
        }

        #[test]
        fn bag_equal_multiset_order_independent() {
            assert_reduces_to("#{1 | 2 | 2}# == #{2 | 1 | 2}#", "true");
        }

        #[test]
        fn bag_unequal_count() {
            assert_reduces_to("#{1 | 2}# == #{1 | 2 | 2}#", "false");
        }

        #[test]
        fn map_equal_insertion_order_independent() {
            assert_reduces_to("{1: 10, 2: 20} == {2: 20, 1: 10}", "true");
        }

        #[test]
        fn map_unequal_value() {
            assert_reduces_to("{1: 10} == {1: 11}", "false");
        }

        #[test]
        fn set_unequal_cardinality() {
            assert_reduces_to("Set(1, 2) == Set(1, 2, 3)", "false");
        }

        #[test]
        fn set_ne_negation() {
            assert_reduces_to("Set(1, 2) != Set(1, 3)", "true");
        }

        #[test]
        fn cross_type_list_and_set() {
            assert_reduces_to("[1, 2] == Set(1, 2)", "false");
        }

        #[test]
        fn cross_type_bag_and_set() {
            assert_reduces_to("#{1 | 2}# == Set(1, 2)", "false");
        }

        #[test]
        fn guard_set_equality_allows_comm() {
            assert_reduces_to("for(p <- c where Set(1, 2) == Set(2, 1)){p} | c!(0)", "0");
        }

        #[test]
        fn guard_set_equality_blocks_comm() {
            assert_never_reaches("for(p <- c where Set(1, 2) == Set(1, 3)){p} | c!(0)", "0");
        }
    }

    // ── `collection_wire` RETIRED (option C, C2 — 2026-07-25) ────────────────────────────────
    //
    // The six golden-hex tests that lived here pinned `languages/src/rhocalc/wire.rs`, a
    // hand-maintained FORK of f1r3node's `rhoapi` protobuf schema. Both the encoder and its
    // goldens have been retired; `.toByteArray()` is now f1r3node's own method, reached by
    // lowering to `EMethod("toByteArray")`.
    //
    // The assertions did not simply move — they were REPLACED, for two independent reasons:
    //
    //  1. They asserted nothing. `assert_reduces_to` reaches its verdict through a disjunction
    //     that includes `bag_multiset_eq`, and `bag_multiset_eq` compares
    //     `to_sorted_bag_elements(a) == to_sorted_bag_elements(b)` — which is `None == None`,
    //     i.e. TRUE, whenever neither side is a `#{…}#` bag literal. Measured 2026-07-25:
    //     `assert_reduces_to("[1, 2, 3].toByteArray()", <any string literal>)` passes, and so does
    //     `assert_reduces_to("1 + 2", "999")`. The real fold result here was `error`.
    //  2. The goldens encoded the WRONG Rholang term. They spelled the list elements as `GInt`
    //     (`sint64` zigzag: `…100210041006` = 1, 2, 3), but a plain RhoCalc integer literal is
    //     arbitrary-precision, so the term RhoCalc actually means carries `GBigInt` elements.
    //
    // The replacements live in `rholang-runtime/tests/rho_rhocalc_conformance.rs`
    // (`c2_closed_to_byte_array_is_the_reducers_own_encoding`), where the real reducer is
    // available and the bytes are asserted with `assert_eq!` against the machine's output.
    //
    // `unsupported_receiver_errors` is kept below: it uses `assert_never_reaches`, which compares
    // displays exactly and is therefore a real assertion.
    mod collection_wire {
        use super::*;

        #[test]
        fn unsupported_receiver_errors() {
            assert_never_reaches("[1, 2].length().toByteArray()", r#""0""#);
        }
    }

    mod type_conversion {
        use super::*;

        #[test]
        fn int_to_float() {
            assert_reduces_to("float(3, 64)", "3.0");
        }
        #[test]
        fn bool_to_int_true() {
            assert_reduces_to("int(true, 64)", "1");
        }
        #[test]
        fn bool_to_int_false() {
            assert_reduces_to("int(false, 64)", "0");
        }
        #[test]
        fn int_to_str() {
            assert_reduces_to(r#"str(42)"#, r#""42""#);
        }

        #[test]
        fn int_from_bigint_fits_i64() {
            assert_reduces_to("int(99n, 64)", "99");
        }

        #[test]
        fn str_from_bigint() {
            assert_reduces_to(r#"str(10n)"#, r#""10""#);
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Parsing
// ════════════════════════════════════════════════════════════════════════════════

mod parsing {
    use super::*;

    fn assert_query_desugars(sugar_src: &str, rhs_src: &str, msg: &str) {
        fresh();
        let sugar = parse(sugar_src).normalize();
        let rhs = parse(rhs_src).normalize();
        assert!(sugar.term_eq(&rhs), "{}", msg);
    }

    #[test]
    fn fraction_zero_denominator_is_error() {
        assert_reduces_to("fraction(1n, 0n)", "error");
    }

    #[test]
    fn zero() {
        let _ = run("0");
    }
    #[test]
    fn empty_par() {
        // After the Rholang-style syntax adjustment `{}` is an empty Map literal,
        // not the nil process. The zero process is now spelled `Nil`.
        let _ = run("Nil");
        // The empty brace literal still parses (as an empty Map cast to Proc).
        let _ = run("{}");
    }
    #[test]
    fn quote() {
        let _ = run("@(0)");
    }
    #[test]
    fn quote_bare_name() {
        let _ = run("@x!(0) | x!(1)");
    }
    #[test]
    fn drop() {
        let _ = run("*(@(0))");
    }
    #[test]
    fn drop_bare_name() {
        let _ = run("*x");
    }
    #[test]
    fn send() {
        let _ = run("x!(0)");
    }

    #[test]
    fn persistent_send_parses() {
        let _ = run("x!!(0)");
    }

    #[test]
    fn send_empty_payload_parses() {
        let _ = run("x!()");
    }

    #[test]
    fn persistent_send_empty_payload_parses() {
        let _ = run("x!!()");
    }

    #[test]
    fn send_empty_payload_quoted_bind_emits_empty_proc() {
        // `x!()` IS `x!([])` — pinned by `send_empty_is_list_sugar` below — so the COMM fires and
        // the whole-message binder `@y` receives the empty payload `[]`, which is what this
        // test's name says happens. The previous expectation (the term unchanged) contradicted
        // both the name and the sugar pin, and only "passed" because `assert_reduces_to` was
        // vacuous. ⚠ Rholang would NOT fire here (its COMM is arity-checked, 0 ≠ 1); that
        // divergence is recorded in `rholang-runtime/tests/rho_rhocalc_conformance.rs`.
        assert_reduces_to("for(@y <- x){y} | x!()", "[]");
    }

    #[test]
    fn send_polyadic_is_list_sugar() {
        fresh();
        let poly = parse("x!(1, 2, 3)").normalize();
        let list = parse("x!([1, 2, 3])").normalize();
        assert!(poly.term_eq(&list), "expected polyadic send sugar to match list payload");
    }

    #[test]
    fn send_empty_is_list_sugar() {
        fresh();
        let empty = parse("x!()").normalize();
        let list = parse("x!([])").normalize();
        assert!(
            empty.term_eq(&list),
            "expected empty send sugar to match empty list payload: empty=`{}` list=`{}`",
            empty,
            list
        );
    }

    #[test]
    fn send_unary_is_list_sugar() {
        fresh();
        let unary = parse("x!(0)").normalize();
        let list = parse("x!([0])").normalize();
        assert!(unary.term_eq(&list), "expected unary send to canonicalize to singleton list");
    }

    #[test]
    fn send_polyadic_two_args_is_list_sugar() {
        fresh();
        let poly = parse("x!(1, 2)").normalize();
        let list = parse("x!([1, 2])").normalize();
        assert!(poly.term_eq(&list), "expected 2-arg send sugar to match list payload");
    }

    #[test]
    fn persistent_send_polyadic_is_list_sugar() {
        fresh();
        let poly = parse("x!!(1, 2, 3)").normalize();
        let list = parse("x!!([1, 2, 3])").normalize();
        assert!(
            poly.term_eq(&list),
            "expected persistent polyadic send sugar to match list payload"
        );
    }

    #[test]
    fn persistent_send_empty_is_list_sugar() {
        fresh();
        let empty = parse("x!!()").normalize();
        let list = parse("x!!([])").normalize();
        assert!(
            empty.term_eq(&list),
            "expected persistent empty send sugar to match empty list payload: empty=`{}` list=`{}`",
            empty,
            list
        );
    }

    #[test]
    fn persistent_send_unary_is_list_sugar() {
        fresh();
        let unary = parse("x!!(0)").normalize();
        let list = parse("x!!([0])").normalize();
        assert!(
            unary.term_eq(&list),
            "expected persistent unary send to canonicalize to singleton list"
        );
    }

    #[test]
    fn send_unary_and_polyadic_non_regression() {
        fresh();
        let unary = parse("x!(0)").normalize();
        let explicit_unary = parse("x!(0)").normalize();
        let poly = parse("x!(1, 2)").normalize();
        let list = parse("x!([1, 2])").normalize();
        assert!(unary.term_eq(&explicit_unary), "expected unary send parse unchanged");
        assert!(poly.term_eq(&list), "expected polyadic send sugar unchanged");
    }

    #[test]
    fn query_receive_sugar_single() {
        assert_query_desugars(
            "for(p <- x!?(a, b)){p}",
            "new r in { x!(*r, a, b) | for(p <- r){p} }",
            "expected `!?` to desugar to `new` + send + receive",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args() {
        assert_query_desugars(
            "for(p <- x!?()){p}",
            "new r in { x!(*r) | for(p <- r){p} }",
            "expected zero-arg `!?` to pass only return channel",
        );
    }

    #[test]
    fn query_receive_sugar_empty_receiver() {
        assert_query_desugars(
            "for(<- x!?(a, b)){p}",
            "new r in { x!(*r, a, b) | for(<- r){p} }",
            "expected empty receiver query bind to desugar via private return channel",
        );
    }

    #[test]
    fn query_receive_sugar_single_with_where() {
        assert_query_desugars(
            "for(p <- x!?(a, b) where p == ok){p}",
            "new r in { x!(*r, a, b) | for(p <- r where p == ok){p} }",
            "expected `!?` bind with where-guard to desugar through private return channel",
        );
    }

    #[test]
    fn query_receive_sugar_multiple_joins() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & z <- c){z}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 & z <- c){z} }",
            "expected multiple `!?` binds to desugar to multiple return channels",
        );
    }

    #[test]
    fn query_receive_sugar_mixed_join_with_plain_bind() {
        assert_query_desugars(
            "for(p <- x!?(a) & q <- c){q}",
            "new r in { x!(*r, a) | for(p <- r & q <- c){q} }",
            "expected `!?` bind to compose with plain join binds",
        );
    }

    #[test]
    fn query_receive_sugar_mixed_rows_with_plain_bind() {
        assert_query_desugars(
            "for(p <- x!?(a); q <- c){q}",
            "new r in { x!(*r, a) | for(p <- r; q <- c){q} }",
            "expected `!?` bind to compose with semicolon-separated rows",
        );
    }

    #[test]
    fn query_receive_sugar_one_arg() {
        assert_query_desugars(
            "for(p <- x!?(a)){p}",
            "new r in { x!(*r, a) | for(p <- r){p} }",
            "expected one-arg `!?` to include return channel then arg",
        );
    }

    #[test]
    fn query_receive_sugar_three_args() {
        assert_query_desugars(
            "for(p <- x!?(a, b, c)){p}",
            "new r in { x!(*r, a, b, c) | for(p <- r){p} }",
            "expected three-arg `!?` to preserve argument order",
        );
    }

    #[test]
    fn query_receive_sugar_parenthesized_channel() {
        let _ = parse("for(p <- (x)!?(a)){p}");
    }

    #[test]
    fn quoted_plain_bind_parses() {
        let _ = parse("for(@[1,2,3] <- c){7}");
    }

    #[test]
    fn quoted_query_bind_parses() {
        let _ = parse("for(@[1,2,3] <- c!?(a)){7}");
    }

    #[test]
    fn query_receive_sugar_quoted_name_lhs() {
        assert_query_desugars(
            "for(p <- x!?(a)){*(@(p))}",
            "new r in { x!(*r, a) | for(p <- r){*(@(p))} }",
            "expected quoted name use in body to survive query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_two_queries_and_plain_join() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & z <- c){z}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 & z <- c){z} }",
            "expected multiple query binds to coexist with plain joins",
        );
    }

    #[test]
    fn query_receive_sugar_two_queries_with_where() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) where p == q){p}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 where p == q){p} }",
            "expected where guard to remain attached after query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_three_queries_join() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & t <- x3!?(a3)){t}",
            "new r1, r2, r3 in { x1!(*r1, a1) | x2!(*r2, a2) | x3!(*r3, a3) | for(p <- r1 & q <- r2 & t <- r3){t} }",
            "expected three query binds to produce three private return channels",
        );
    }

    #[test]
    fn query_receive_sugar_join_row_then_plain_row() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2); z <- c){z}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2; z <- c){z} }",
            "expected semicolon rows to remain in order after query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_plain_row_then_join_row() {
        assert_query_desugars(
            "for(z <- c; p <- x1!?(a1) & q <- x2!?(a2)){z}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(z <- c; p <- r1 & q <- r2){z} }",
            "expected query desugaring in later row to preserve earlier plain row",
        );
    }

    #[test]
    fn query_receive_sugar_two_query_rows() {
        assert_query_desugars(
            "for(p <- x1!?(a1); q <- x2!?(a2)){q}",
            "new r1, r2 in { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1; q <- r2){q} }",
            "expected query binds across rows to allocate independent return channels",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args_in_join() {
        assert_query_desugars(
            "for(p <- x!?() & q <- c){q}",
            "new r in { x!(*r) | for(p <- r & q <- c){q} }",
            "expected zero-arg query bind to compose with join rows",
        );
    }

    #[test]
    fn query_receive_sugar_two_zero_arg_queries() {
        assert_query_desugars(
            "for(p <- x1!?() & q <- x2!?()){p}",
            "new r1, r2 in { x1!(*r1) | x2!(*r2) | for(p <- r1 & q <- r2){p} }",
            "expected each zero-arg query bind to allocate return channel",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args_with_where() {
        assert_query_desugars(
            "for(p <- x!?() where p == ok){p}",
            "new r in { x!(*r) | for(p <- r where p == ok){p} }",
            "expected where guard to work with zero-arg query bind",
        );
    }

    #[test]
    fn query_receive_sugar_with_arithmetic_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p + 1 > 0){p}",
            "new r in { x!(*r, a) | for(p <- r where p + 1 > 0){p} }",
            "expected arithmetic guard to be preserved after desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_with_boolean_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p == ok and true){p}",
            "new r in { x!(*r, a) | for(p <- r where p == ok and true){p} }",
            "expected boolean guard structure to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_with_string_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p == \"ok\"){p}",
            "new r in { x!(*r, a) | for(p <- r where p == \"ok\"){p} }",
            "expected string equality guard to survive desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_with_list_arg() {
        assert_query_desugars(
            "for(p <- x!?([1,2,3])){p}",
            "new r in { x!(*r, [1,2,3]) | for(p <- r){p} }",
            "expected list argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_with_map_arg() {
        assert_query_desugars(
            "for(p <- x!?({1:2, 3:4})){p}",
            "new r in { x!(*r, {1:2, 3:4}) | for(p <- r){p} }",
            "expected map argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_with_bag_arg() {
        assert_query_desugars(
            "for(p <- x!?(#{1|2}#)){p}",
            "new r in { x!(*r, #{1|2}#) | for(p <- r){p} }",
            "expected bag argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_body_uses_bound_name() {
        assert_query_desugars(
            "for(p <- x!?(a)){*p}",
            "new r in { x!(*r, a) | for(p <- r){*p} }",
            "expected body to keep bound name usage after desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_body_parallel_structure() {
        assert_query_desugars(
            "for(p <- x!?(a)){*p | ok}",
            "new r in { x!(*r, a) | for(p <- r){*p | ok} }",
            "expected body parallel structure to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_with_new_in_body() {
        assert_query_desugars(
            "for(p <- x!?(a)){new k in {k!(0)}}",
            "new r in { x!(*r, a) | for(p <- r){new k in {k!(0)}} }",
            "expected nested new in body to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_rows_with_where_and_plain_followup() {
        assert_query_desugars(
            "for(p <- x!?(a) & q <- y!?(b) where p == q; z <- c){z}",
            "new r1, r2 in { x!(*r1, a) | y!(*r2, b) | for(p <- r1 & q <- r2 where p == q; z <- c){z} }",
            "expected mixed where+row composition to survive desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_plain_then_query_with_where() {
        assert_query_desugars(
            "for(z <- c; p <- x!?(a) where p == ok){z}",
            "new r in { x!(*r, a) | for(z <- c; p <- r where p == ok){z} }",
            "expected where guard in later query row to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_three_rows_two_queries_one_plain() {
        assert_query_desugars(
            "for(p <- x!?(a); q <- c; r <- y!?(b)){q}",
            "new r1, r2 in { x!(*r1, a) | y!(*r2, b) | for(p <- r1; q <- c; r <- r2){q} }",
            "expected multi-row ordering with two queries to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_empty_receiver_in_join() {
        assert_query_desugars(
            "for(<- x!?(a) & q <- c){q}",
            "new r in { x!(*r, a) | for(<- r & q <- c){q} }",
            "expected empty receiver query bind to compose with join binds",
        );
    }

    #[test]
    fn query_receive_sugar_empty_receiver_later_row() {
        assert_query_desugars(
            "for(z <- c; <- x!?()){z}",
            "new r in { x!(*r) | for(z <- c; <- r){z} }",
            "expected empty receiver query bind in later row to preserve row order",
        );
    }

    #[test]
    fn query_receive_sugar_empty_receiver_where_uses_other_bind() {
        assert_query_desugars(
            "for(<- x!?(a) & q <- c where q == ok){q}",
            "new r in { x!(*r, a) | for(<- r & q <- c where q == ok){q} }",
            "expected where guard with other bind to remain after empty receiver desugar",
        );
    }
    #[test]
    fn receive() {
        let _ = run("for(y <- x){y!(0)}");
    }

    #[test]
    fn persistent_receive_parses() {
        let _ = run("for(y <= x){y!(0)}");
    }

    #[test]
    fn persistent_receive_empty_parses() {
        let _ = run("for(<= x){ok}");
    }

    #[test]
    fn persistent_receive_where_parses() {
        let _ = run("for(y <= x where y == ok){y!(0)}");
    }

    #[test]
    fn persistent_receive_join_parses() {
        let _ = run("for(y <= x & z <- c){z}");
    }

    #[test]
    fn persistent_receive_join_where_parses() {
        let _ = run("for(y <= x & z <- c where z == ok){z}");
    }

    #[test]
    fn polyadic_receive_parses() {
        let _ = run("for(a, b, c <- x){[a,b,c]}");
    }

    #[test]
    fn persistent_polyadic_receive_parses() {
        let _ = run("for(a, b, c <= x){[a,b,c]}");
    }

    #[test]
    fn bare_parallel_infix_parses_as_pparinfix() {
        // Bare `P | Q` parses via `PParInfix` and folds to the `PPar` multiset
        // under `run_ascent`/normalize.
        fresh();
        let bare = parse("x!!(1,2,3) | for(a, b, c <- x){[a,b,c]}");
        assert!(
            matches!(bare, Proc::PParInfix(_, _)),
            "expected PParInfix at parse time, got: {:?}",
            bare
        );
    }

    #[test]
    fn braced_parallel_parses_as_ppar() {
        fresh();
        let braced = parse("{x!!(1,2,3) | for(a, b, c <- x){[a,b,c]}}");
        assert!(
            matches!(braced, Proc::PPar(_)),
            "expected PPar at parse time, got: {:?}",
            braced
        );
    }

    #[test]
    fn braced_parallel_reduces_like_bare_infix() {
        assert_reduces_to("{x!(1,2,3) | for(a, b, c <- x){[a,b,c]}}", "[1,2,3]");
    }

    #[test]
    fn braced_parallel_disambiguated_from_map_literals() {
        fresh();
        let map = parse("{1: 10}");
        assert!(
            matches!(map, Proc::CastMap(_)),
            "expected CastMap for map literal, got: {:?}",
            map
        );
        let par = parse("{1 | 2}");
        assert!(
            matches!(par, Proc::PPar(_)),
            "expected PPar for braced parallel, got: {:?}",
            par
        );
    }

    #[test]
    fn pathmap_literal_disambiguated_from_map_and_parallel() {
        fresh();
        let empty_pm = parse("{||}");
        assert!(
            matches!(empty_pm, Proc::CastPathmap(_)),
            "expected CastPathmap for empty pathmap, got: {:?}",
            empty_pm
        );
        let pm = parse("{| 1, [2,3] |}");
        assert!(
            matches!(pm, Proc::CastPathmap(_)),
            "expected CastPathmap for pathmap literal, got: {:?}",
            pm
        );
    }

    #[test]
    fn polyadic_persistent_send_and_receive_without_outer_braces_reduces() {
        let (results, initial_id) = run_with_initial("x!!(1,2,3) | for(a, b, c <- x){[a,b,c]}");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        // Whitespace-insensitive (the WFST branch displays lists/sends WITH spaces,
        // e.g. `x!!([1, 2, 3])`; this incoming test's raw `.contains("[1,2,3]")` was
        // authored against main's no-space display). The SUBST SEMANTICS are what
        // matters and are verified correct (polyadic body `[a,b,c]` → `[1,2,3]`),
        // matching the codebase's whitespace-insensitive `assert_reduces_to` standard.
        assert!(
            nfs.iter().any(|nf| {
                let s: String = nf.chars().filter(|c| !c.is_whitespace()).collect();
                s.contains("x!!([1,2,3])") && s.contains("[1,2,3]")
            }),
            "expected persistent send to remain and produce payload, got {:?}",
            nfs
        );
    }

    #[test]
    fn polyadic_send_and_receive_without_outer_braces_reduces() {
        assert_reduces_to("x!(1,2,3) | for(a, b, c <- x){[a,b,c]}", "[1,2,3]");
    }

    #[test]
    fn polyadic_send_and_persistent_receive_without_outer_braces_reduces() {
        let (results, initial_id) = run_with_initial("x!(1,2,3) | for(a, b, c <= x){[a,b,c]}");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        assert!(
            nfs.iter().any(|nf| {
                // Whitespace-insensitive: WFST displays `for(a, b, c <= x){[a, b, c]}`
                // with spaces; subst semantics (payload → [1,2,3]) verified correct.
                let s: String = nf.chars().filter(|c| !c.is_whitespace()).collect();
                s.contains("[1,2,3]") && s.contains("for(a,b") && s.contains("c<=x){[a,b,c]}")
            }),
            "expected persistent receive to remain and produce payload, got {:?}",
            nfs
        );
    }

    #[test]
    fn polyadic_persistent_send_and_persistent_receive_without_outer_braces_reduces() {
        let (results, initial_id) = run_with_initial("x!!(1,2,3) | for(a, b, c <= x){[a,b,c]}");
        let nfs = reachable_normal_form_displays(&results, initial_id);
        assert!(
            nfs.iter().any(|nf| {
                // Whitespace-insensitive: WFST displays with spaces; subst semantics verified.
                let s: String = nf.chars().filter(|c| !c.is_whitespace()).collect();
                s.contains("[1,2,3]")
                    && s.contains("x!!([1,2,3])")
                    && s.contains("for(a,b")
                    && s.contains("c<=x){[a,b,c]}")
            }),
            "expected both persistent endpoints to remain and produce payload, got {:?}",
            nfs
        );
    }

    #[test]
    fn multi_input() {
        let _ = run("for(x <- c1 & y <- c2){*(x)} | c1!(p) | c2!(q)");
    }

    #[test]
    fn empty_receiver_plain_runtime_ignores_payload() {
        assert_reduces_to("for(<- c){ok} | c!(any)", "ok");
    }

    #[test]
    fn empty_receiver_plain_runtime_with_int_payload() {
        assert_reduces_to("for(<- x){ok} | x!(1)", "ok");
    }

    #[test]
    fn empty_receiver_plain_runtime_with_empty_payload() {
        assert_reduces_to("for(<- x){ok} | x!()", "for(<- x){ok} | x!()");
    }

    #[test]
    fn empty_receiver_plain_runtime_with_empty_payload_does_not_reach_ok() {
        let (results, initial_id) = run_with_initial("for(<- x){ok} | x!()");
        let reachable_nfs = reachable_normal_form_displays(&results, initial_id);
        assert!(
            !reachable_nfs.iter().any(|nf| nf == "ok"),
            "reachable normal forms unexpectedly contain `ok`: {:?}",
            reachable_nfs
        );
    }

    #[test]
    fn empty_receiver_plain_runtime_with_list_payload() {
        assert_reduces_to("for(<- x){ok} | x!([1,2,3])", "ok");
    }

    #[test]
    fn empty_receiver_with_bool_payload_and_string_body_reduces() {
        assert_reduces_to("x!(true) | for(<- x){\"ok\"}", "\"ok\"");
    }

    #[test]
    fn empty_receiver_with_empty_payload_does_not_reduce_without_braces() {
        assert_reduces_to("x!() | for(<- x){\"ok\"}", "x!() | for(<- x){\"ok\"}");
    }

    #[test]
    fn unary_send_and_persistent_receive_reduces() {
        let results = run("x!(1) | for(name <= x){\"ok\"}");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays
                .iter()
                .any(|d| d.contains("\"ok\"") && d.contains("for(name <= x){\"ok\"}")),
            "expected persistent receive to remain and emit body, got {:?}",
            displays
        );
    }

    #[test]
    fn unary_persistent_send_and_persistent_receive_cycle_shape() {
        let results = run("x!!(1) | for(name <= x){\"ok\"}");
        let displays: Vec<String> = results
            .all_terms
            .iter()
            .map(|t| t.display.clone())
            .collect();
        assert!(
            displays.iter().any(|d| {
                d.contains("\"ok\"")
                    && (d.contains("x!!([1])") || d.contains("x!!(1)"))
                    && d.contains("for(name <= x){\"ok\"}")
            }),
            "expected persistent send/receive cycle shape, got {:?}",
            displays
        );
    }

    #[test]
    fn empty_receiver_plain_join_with_bound_var() {
        assert_reduces_to("for(<- x & q <- c){q} | x!(ignored) | c!(ok)", "ok");
    }

    #[test]
    fn empty_receiver_plain_where_on_other_bind_true() {
        let (results, initial_id) =
            run_with_initial("for(<- x & q <- c where q == ok){q} | x!(ignored) | c!(ok)");
        let reachable_nfs = reachable_normal_form_displays(&results, initial_id);
        assert!(
            !reachable_nfs.iter().any(|nf| nf == "ok" || nf == "ok"),
            "reachable normal forms unexpectedly contain `ok`: {:?}",
            reachable_nfs
        );
    }

    #[test]
    fn empty_receiver_plain_where_on_other_bind_false_blocks() {
        assert_never_reaches("for(<- x & q <- c where q == ok){q} | x!(ignored) | c!(bad)", "bad");
    }

    #[test]
    fn empty_receiver_plain_later_row_preserves_order() {
        assert_reduces_to("for(z <- c; <- x){z} | c!(ok) | x!(ignored)", "ok");
    }

    #[test]
    fn old_receive_syntax_rejected() {
        let lang = RhoCalcLanguage;
        assert!(lang.parse_term("(c?x).{x!(0)}").is_err());
        assert!(lang.parse_term("(c1?x, c2?y).{*(x)}").is_err());
    }

    #[test]
    fn for_structural_pattern_requires_quote() {
        let lang = RhoCalcLanguage;
        assert!(lang.parse_term("for([1,2,4] <- c){7}").is_err());
    }
    #[test]
    fn new_single() {
        let _ = run("new x in { x!(0) }");
    }
    #[test]
    fn new_multi() {
        let _ = run("new x, y in {x!(0) | y!(1)}");
    }

    #[test]
    fn bare_variable_infers_as_proc() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("p").expect("parse");
        let term_type = lang.infer_term_type(term.as_ref());
        assert_eq!(format!("{}", term_type), "Proc");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Beta-reduction (lambda / dollar-syntax)
// ════════════════════════════════════════════════════════════════════════════════

mod beta {
    use super::*;

    #[test]
    fn dollar_name_reduces() {
        fresh();
        let term = parse("$name(^loc.{loc!(init)}, n)");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "n!(init)");
    }

    #[test]
    fn dollar_proc_reduces() {
        fresh();
        let term = parse("$proc(^f.{f}, Nil)");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "Nil");
    }

    #[test]
    fn normalize_via_language_trait() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term("$name(^loc.{loc!(init)}, n)")
            .expect("parse");
        let normalized = lang.normalize_term(term.as_ref());
        assert_eq!(format!("{}", normalized), "n!(init)");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Numeric casts (`int`, `uint`, … on Proc)
// ════════════════════════════════════════════════════════════════════════════════

#[test]
fn rhocalc_cast_int_float_floor() {
    let results = run("int(-3.5, 8)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "-4" || nf.contains("-4")),
        "expected -4, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_invalid_width_error() {
    let results = run("int(1, 7)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|d| d == "error" || d.contains("error")),
        "expected error NF, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_nonfinite_float_is_error() {
    let results = run("int(0.0 / 0.0, 8)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|d| d == "error" || d.contains("error")),
        "expected error for NaN source, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_uint_float_clamp() {
    let results = run("uint(-3.5, 8)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "0u32" || nf == "0"),
        "expected 0 / 0u32, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_uint_modular_u32_literal() {
    let results = run("uint(257u32, 8)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "1u32" || nf == "1"),
        "expected modular 257 -> 1 in 8 bits, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_float_overflow_to_inf() {
    let results = run("float(1e50, 32)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf.to_ascii_lowercase().contains("inf")),
        "expected +Inf in a normal form, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_float_from_rational_string() {
    let results = run(r#"float("1r/2r", 32)"#);
    let nfs = normal_form_displays(&results);
    assert!(nfs.iter().any(|nf| nf == "0.5"), "expected 0.5 in a normal form, got {:?}", nfs);
}

#[test]
fn rhocalc_cast_float_from_bigint_n_string() {
    assert_reduces_to(r#"float("1000n", 64)"#, "1000.0");
}

#[test]
fn rhocalc_cast_float_from_fixed_p_string() {
    assert_reduces_to(r#"float("1000.1p1", 64)"#, "1000.1");
}

#[test]
fn rhocalc_casts_from_numeric_strings() {
    assert_reduces_to(r#"int("2r/3r", 32)"#, "0");
    assert_reduces_to(r#"int("123n", 64)"#, "123");
    assert_reduces_to(r#"int("123i64", 64)"#, "123");
    assert_reduces_to(r#"int("10i32", 32)"#, "10");
    assert_reduces_to(r#"int("false", 32)"#, "0");
    assert_reduces_to(r#"int("true", 32)"#, "1");
    // ★ `123n`, not `123`: the `BigInt` display now carries the mandatory `n` tail its own
    // declared pattern requires (divergence I, Stage C) — without it a `BigInt` displayed as a
    // word that reads back as an `Int`.
    assert_reduces_to(r#"bigint("123n")"#, "123n");
    // ★ `1r/2r`, not `1/2r` and not `1/2`: the SAME Stage-C mechanism, now reaching `BigRat`
    // because its pattern gained the leading `-?` (divergence I(b), 2026-07-26) AND the composite
    // `(/(…)r)?` group (divergence I(d), 2026-07-27 — ledger D2 in
    // `languages/tests/literal_domain_agreement.rs`). The tail belongs to each COMPONENT of the
    // composite, because that is what the declared pattern spells; derivation at
    // `native_ops::arithmetic::fraction_at_top_level_reduces`.
    assert_normal_form_display(r#"bigrat("1r/2r")"#, "1r/2r");
}

#[test]
fn rhocalc_str_from_rational_literal() {
    assert_reduces_to(r#"str(23r)"#, r#""23""#);
}

#[test]
fn rhocalc_bigint_unary_from_float() {
    let results = run("bigint(-3.5)");
    let nfs = normal_form_displays(&results);
    assert!(nfs.iter().any(|nf| nf.contains("-4")), "expected -4n or similar, got {:?}", nfs);
}

#[test]
fn rhocalc_cast_fixed_floor() {
    let results = run("fixed(3.49p2, 1)");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter()
            .any(|nf| nf.contains("3.4p1") || nf.contains("3.4")),
        "expected 3.4p1, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_congruence_through_add() {
    assert_reduces_to("int(1 + 2, 8)", "3");
}

#[test]
fn rhocalc_cast_uint_signed_int_twos_complement() {
    // `bitnot 0` → −1 (`CastInt`). Nesting `bitnot` inside an inner `{…}` PPar can block cast folds;
    // use it directly as the first operand of `uint`.
    assert_reduces_to("uint(bitnot 0, 8)", "255");
}

#[test]
fn rhocalc_cast_under_send_reduces_via_comm() {
    let results = run("for(x <- c){*(x)} | c!(int(-3.5, 8))");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "-4" || nf.contains("-4")),
        "expected `-4` after comm + cast in send, got {:?}",
        nfs
    );
}

// ════════════════════════════════════════════════════════════════════════════════
// Type inference
// ════════════════════════════════════════════════════════════════════════════════

mod type_inference {
    use super::*;

    #[test]
    fn pinputs_infers_bound_var() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("for(y <- x){*(y)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        let y_info = var_types.iter().find(|v| v.name == "y");
        assert!(y_info.is_some(), "y should be found, got: {:?}", var_types);
        assert_eq!(format!("{}", y_info.unwrap().ty), "Name");
    }

    #[test]
    fn pinputs_lookup_by_name() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("for(y <- x){*(y)}").expect("parse");
        let y_type = lang.infer_var_type(term.as_ref(), "y");
        assert!(y_type.is_some());
        assert_eq!(format!("{}", y_type.unwrap()), "Name");
    }

    #[test]
    fn multi_input_infers_both_vars() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term("for(x <- c1 & y <- c2){*(x)}")
            .expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        assert!(var_types.iter().any(|v| v.name == "x"));
        assert!(var_types.iter().any(|v| v.name == "y"));
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// ForRow F3 `&`-join multiplicative-ambiguity pins (2026-06-28; RESOLVED 2026-07-16)
// ════════════════════════════════════════════════════════════════════════════════
//
// The repro `for(@a <- a & @a <- a & @a <- a){ Nil }` (and its bare-`ForRow`
// core) timed out under F2 because the InputBind LHS of each `&`-join bind was
// parsed by TWO delegates — a transparent CrossCatProjection (→ ForRow) and a
// cross-cat-LHS EXTENSION (→ ForRowNoWhere via `&`) — and each `@a<-a` is itself
// 2-way ambiguous, so the live cursor frontier grew `2^N` in the bind count.
//
// FINDING (2026-06 campaign): a §4.1 forks.rs lex-fork gate + the
// `FORROW_PROJ_GATE` kill-switch MITIGATED but did not eliminate the `2^N`; the
// multi-bind cases stayed slow and were `#[ignore]`d pending a walker redesign.
//
// RESOLUTION (2026-07-16): NO such redesign was needed. The CASE-2 re-platform
// (S1–S6) + the descriptor-pure canonical-GLL flip rewrote the walker AFTER these
// were ignored, and the `2^N` is GONE — the LHS ambiguity now lives in the SPPF
// forest (pack-at-advance), not the live cursor frontier. All cases parse in poly
// time and deterministically: 3-bind 0.015s, 4-bind 0.013s, mixed-LHS 0.014s,
// full-Proc for(&-join) 0.025s (were ~24s / >30s / ~14s / >30s). Verified and
// un-ignored 2026-07-16; the four pins are now ACTIVE regression guards against a
// returning `2^N`.
//
// Each pin parses under a 30s anti-hang guard and pins the positive AST via
// derived `Debug`.

mod forrow_join_f3 {
    use super::*;

    #[test]
    fn two_quoted_binds_join_anchor_parses_fast() {
        // The one case §4.1 makes genuinely fast (~1.5s): a 2-bind all-quoted
        // join parses to ForRowNoWhere with 2 binds.
        let (debug, binds) = parse_forrow_fast("@a<-a & @a<-a");
        assert_eq!(binds, Some(2), "expected ForRowNoWhere with 2 binds; derived AST = {}", debug);
    }

    // The bare core of the former hang repro: 3 all-quoted `&`-join binds. Parses
    // CORRECTLY and DETERMINISTICALLY to ForRowNoWhere with 3 binds in ~0.015s on
    // the descriptor-pure engine (was ~24s pre-flip).
    #[test]
    fn three_quoted_binds_join_parses_fast_deterministic() {
        let (debug_1, binds_1) = parse_forrow_fast("@a <- a & @a <- a & @a <- a");
        let (debug_2, binds_2) = parse_forrow_fast("@a <- a & @a <- a & @a <- a");
        assert_eq!(
            binds_1,
            Some(3),
            "expected ForRowNoWhere with 3 binds; derived AST = {}",
            debug_1
        );
        assert_eq!(binds_1, binds_2, "parse determinism: bind shape differs");
        assert_eq!(debug_1, debug_2, "parse determinism: two parses of the same `&`-join differ");
    }

    #[test]
    fn four_quoted_binds_join_parses_fast() {
        let (debug, binds) = parse_forrow_fast("@a <- a & @a <- a & @a <- a & @a <- a");
        assert_eq!(binds, Some(4), "expected ForRowNoWhere with 4 binds; derived AST = {}", debug);
    }

    // First bind is a PLAIN (var) LHS, the rest quoted — exercises the mixed-LHS
    // `&`-join path. Parses correctly in ~0.014s on the descriptor-pure engine.
    #[test]
    fn first_plain_then_quoted_binds_join_anchor_parses_fast() {
        let (debug, binds) = parse_forrow_fast("a<-a & @a<-a & @a<-a");
        assert_eq!(binds, Some(3), "expected ForRowNoWhere with 3 binds; derived AST = {}", debug);
    }

    // The exact former hang repro from the F3 spec, as a full `Proc`.
    #[test]
    fn for_block_three_quoted_binds_join_repro_parses_fast_deterministic() {
        let debug_1 = parse_proc_fast("for(@a <- a & @a <- a & @a <- a){ Nil }");
        let debug_2 = parse_proc_fast("for(@a <- a & @a <- a & @a <- a){ Nil }");
        assert_eq!(
            debug_1, debug_2,
            "parse determinism: two parses of the for(&-join) repro differ"
        );
    }

    // Poly-scaling regression guard (2026-07-16): higher-N all-`@a` `&`-joins must
    // still parse fast and with the exact bind count. If the `2^N` cursor frontier
    // ever returns, these blow past the 30s anti-hang guard (2^24 never finishes).
    #[test]
    fn higher_n_quoted_binds_joins_stay_polynomial() {
        for n in [8usize, 16, 24] {
            let input = vec!["@a<-a"; n].join(" & ");
            let (debug, binds) = parse_forrow_fast(&input);
            assert_eq!(
                binds,
                Some(n),
                "expected ForRowNoWhere with {} binds; derived AST = {}",
                n,
                debug
            );
        }
    }
}

/// M6 realize-selection belt (2026-07-04): the single-result facade
/// (`parse_<Cat>_via_wpda_with_source`) now iterates ALL full-span accepting
/// SPPF roots and, per root, probes a descending raw-realization cap ladder
/// (128 → 1), selecting the global minimum-weight term that ACTUALLY realizes —
/// instead of committing to `roots.first()` at the fixed cap 128.
///
/// This fixes a class of parse-gaps where a full-span accepting root's SPPF
/// carries a self-cyclic packing: at the fixed cap 128 the lazy realizer
/// descends into the cycle, aborts, and the eager fallback's cycle-discard
/// yields ZERO terms — even though a smaller cap stops after the first
/// (correct, token-sound, min-weight) packing and realizes the ORIGINAL term.
///
/// The canonical member is the `@`-first polyadic bind-LHS with a prefix-op
/// where-guard (`@a,b<-c where bitnot d`) and the compound counterexample that
/// the `forrow_display_parse_roundtrip` proptest fast-failed on before this fix.
/// Both parse to a term whose Display exactly reproduces the input surface and
/// re-parses idempotently. See scratchpad/M6_STAGE0_FINDINGS.md for the Stage-0
/// soundness + inertness measurement.
mod m6_realize_selection {
    use super::*;

    /// Assert `input` parses AND its Display reproduces `input` EXACTLY AND is
    /// idempotent under re-parse. (For surfaces the parser preserves verbatim —
    /// these are the fixed parse-gap members.)
    fn assert_forrow_roundtrips_exact(input: &str) {
        mettail_runtime::clear_var_cache();
        let parsed = ForRow::parse(input)
            .unwrap_or_else(|e| panic!("ForRow::parse failed for `{}`: {}", input, e));
        let disp = format!("{}", parsed);
        assert_eq!(
            disp, input,
            "M6: recovered term must Display back to the original surface\n  in={:?}\n out={:?}",
            input, disp
        );
        assert_parses_idempotent(&disp);
    }

    /// Assert `input` parses AND its Display is idempotent under re-parse.
    /// (Does NOT require surface-verbatim Display; the parser may canonicalize
    /// whitespace, e.g. `@a<-c` → `@a <- c`.)
    fn assert_parses_idempotent(input: &str) {
        mettail_runtime::clear_var_cache();
        let parsed = ForRow::parse(input)
            .unwrap_or_else(|e| panic!("ForRow::parse failed for `{}`: {}", input, e));
        let disp = format!("{}", parsed);
        mettail_runtime::clear_var_cache();
        let reparsed = ForRow::parse(&disp)
            .unwrap_or_else(|e| panic!("M6: re-parse of `{}` failed: {}", disp, e));
        let redisp = format!("{}", reparsed);
        assert_eq!(disp, redisp, "M6: Display must be roundtrip-idempotent");
    }

    #[test]
    fn polyadic_at_first_bind_with_prefix_where_guard_roundtrips() {
        // The minimal parse-gap (root-caused): `@`-first polyadic bind-LHS
        // (NQuoteShort cross-cat re-entry) + a Proc→Proc prefix-op where-guard.
        assert_forrow_roundtrips_exact("@a,b<-c where bitnot d");
    }

    #[test]
    fn compound_polyadic_at_binds_with_keyword_channel_and_prefix_guard_roundtrips() {
        // The exact compound counterexample the forrow roundtrip proptest
        // fast-failed on before the M6 belt (WPDS produced no result @ EOF).
        //
        // ★ SURFACE SYNONYMY (2026-07-26): this assertion is Display-VERBATIM, so the input has
        // to be written in the CANONICAL spelling of every synonymy class it contains. `@(a)`
        // and `@(error)` are `NQuote`; the `Name` class now renders through its declared
        // canonical member `NQuoteShort`, so the canonical surfaces are `@a` and `@error`. The
        // parse-gap this case pins — `@`-first polyadic bind-LHS cross-cat re-entry plus a
        // Proc→Proc prefix-op where-guard — is untouched by the respelling: `@Pathmap()` and
        // `@Nil` are still `@`-led binds, still three of them, still followed by the same
        // keyword channel and guard. (Verified by parsing the ORIGINAL spelling below: it still
        // parses, and it now Displays to this canonical form.)
        assert_forrow_roundtrips_exact(
            "@Pathmap(),@Nil , @a , @error<-@Map() where bitnot Nil.keys()",
        );
        // The pre-canonicalisation spelling must still PARSE (only its Display moved), so the
        // respelling above cannot have quietly narrowed the surface this case covers.
        mettail_runtime::clear_var_cache();
        let original =
            ForRow::parse("@Pathmap(),@Nil , @(a) , @(error)<-@Map() where bitnot Nil.keys()")
                .expect("the pre-canonicalisation spelling must still parse");
        assert_eq!(
            format!("{original}"),
            "@Pathmap(),@Nil , @a , @error<-@Map() where bitnot Nil.keys()",
            "the `@(x)` spelling must normalise to the canonical `@x` spelling"
        );
    }

    #[test]
    fn m6_is_inert_on_bind_shapes_that_already_realized() {
        // Regression anchors that realized at the fixed cap 128 before M6 —
        // the belt must be inert (still parse, still Display-idempotent).
        for s in [
            "a,@b<-c where bitnot d",
            "@a<-c where bitnot d",
            "@a,b<-c where d",
            "@a,b<-c where d.keys()",
            "a,b<-c where bitnot d",
        ] {
            assert_parses_idempotent(s);
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// FLIP-GATE ATTEMPT-2 FALLOUT (2026-07-12): repro pins for the pure-arm hole
// PREFIX-OPERAND × GROUPED-CHANNEL × SEND — `bitnot (a)!(false)` class.
//
// Receipts (scratchpad/zz_probes/logs_s2flip2/): the flip-gate battery's
// gen_rhocalc_prop::proc_display_parse_roundtrip minimized to
// `bitnot (a)!(false)` (p6_sweep.log); the deterministic A/B (bitnot_ab.log,
// bitnot_scope.log) shows CLASSIC parses every shape below (unwrapping the
// parens via the grouped-LHS cross-cat reentry family — channel `NVar(a)` /
// `NQuoteNil`, no NParen) while the PURE canonical-GLL arm rejects the three
// hole shapes with TrailingTokens at the `!`: a prefix operator's operand
// sub-parse completes at the group `(a)` and pure never continues the
// completed group into the following send. The R-A/R-C boundary-continuation
// family, in a configuration neither committed arm covers (Arm A fires at
// InfixLoop-on-CE; Arm C at InfixLoop operand early-stop; this is a
// PREFIX-rule operand needing the classic TransparentSourceReentry
// continuation).
//
// ARM G v2 LANDED (2026-07-12): the per-cat-marker reentry floor reset
// (`cgll_pure_group_reentry_floor_reset`) closes the hole — the block is
// UN-IGNORED and extended with the D3-matrix pins (multisets classic-equal,
// receipts logs_s2flip2/armg_d3_matrix.log). Historical verification protocol
// (banked receipts, pre-fix): `--ignored` under a scratch const=true flip ⇒
// the three hole pins FAILED and the three controls PASSED; under
// `PRATTAIL_NO_CANONICAL_GLL=1` all six PASSED.
// ════════════════════════════════════════════════════════════════════════════════

mod flip_blocker_prefix_grouped_send {
    use super::*;

    /// THE MINIMAL (proptest-minimized): prefix op + grouped channel + send.
    #[test]
    fn bitnot_grouped_channel_send_parses() {
        fresh();
        let t = parse("bitnot (a)!(false)");
        // Classic shape receipt: BitNot(POutput(NVar(a), CastBool(false)))
        // — the parens are unwrapped by the reentry family (no NParen).
        assert!(
            format!("{t:?}").starts_with("BitNot(POutput("),
            "expected BitNot(POutput(..)), got: {t:?}"
        );
    }

    /// Hole pin: empty-payload send on a grouped channel under the prefix op.
    #[test]
    fn bitnot_grouped_channel_empty_send_parses() {
        fresh();
        let t = parse("bitnot (a)!()");
        assert!(
            format!("{t:?}").starts_with("BitNot(POutputEmpty("),
            "expected BitNot(POutputEmpty(..)), got: {t:?}"
        );
    }

    /// Hole pin: grouped QUOTED channel under the prefix op.
    #[test]
    fn bitnot_grouped_quote_channel_send_parses() {
        fresh();
        let t = parse("bitnot (@Nil)!(false)");
        // Constructor-family prefix: the default facade elects the
        // @Nil-specialized `POutputNil` here while the with_source facade
        // shows the generic `POutput(NQuoteNil, ..)` — both are the send.
        assert!(
            format!("{t:?}").starts_with("BitNot(POutput"),
            "expected BitNot(POutput..), got: {t:?}"
        );
    }

    /// Control: the grouped-channel send WITHOUT the prefix op parses in
    /// BOTH arms today (pure keeps the NParen; classic unwraps) — pins that
    /// the hole is specifically the prefix-operand continuation.
    #[test]
    fn control_grouped_channel_send_parses() {
        fresh();
        let t = parse("(a)!(false)");
        assert!(format!("{t:?}").starts_with("POutput("), "expected POutput(..), got: {t:?}");
    }

    /// Control: the UNGROUPED channel under the prefix op parses in both
    /// arms today — the group is load-bearing for the hole.
    #[test]
    fn control_ungrouped_channel_send_parses() {
        fresh();
        let t = parse("bitnot a!(false)");
        assert!(
            format!("{t:?}").starts_with("BitNot(POutput("),
            "expected BitNot(POutput(..)), got: {t:?}"
        );
    }

    /// Control: the prefix op over the bare group (no send) parses in both
    /// arms today — the SEND continuation is load-bearing for the hole.
    #[test]
    fn control_prefix_over_bare_group_parses() {
        fresh();
        let _ = parse("bitnot (a)");
    }

    // ── ARM G D3-matrix pins (2026-07-12): the wider hole family + fences,
    //    expected values = the classic-adjudicated g5/d3 receipts. ──────────

    /// Persistent send on the grouped channel under the prefix op.
    #[test]
    fn bitnot_grouped_channel_persist_send_parses() {
        fresh();
        let t = parse("bitnot (a)!!(false)");
        assert!(
            format!("{t:?}").starts_with("BitNot(PPersistOutput"),
            "expected BitNot(PPersistOutput..), got: {t:?}"
        );
    }

    /// Polyadic send on the grouped channel under the prefix op (rule 8).
    #[test]
    fn bitnot_grouped_channel_polyadic_send_parses() {
        fresh();
        let t = parse("bitnot (a)!(0,1)");
        assert!(
            format!("{t:?}").starts_with("BitNot(POutput"),
            "expected BitNot(POutput..), got: {t:?}"
        );
    }

    /// Multiset pin: the n=4 payload row equals classic's reading count
    /// (armg_d3_matrix.log: pure n=4 ≡ classic n=4, md5 EQ).
    #[test]
    fn bitnot_grouped_send_payload_multiset_matches_classic() {
        fresh();
        let readings =
            Proc::parse_via_wpda_all("bitnot (a)!(@Nil!() / @Nil!())").expect("parse_all");
        assert_eq!(readings.len(), 4, "classic multiset is n=4, got {}", readings.len());
    }

    /// Multiset pin: the nested-group row (double-LHS) equals classic n=2;
    /// both group frames fire the reset (resets=2 receipt).
    #[test]
    fn bitnot_nested_grouped_send_multiset_matches_classic() {
        fresh();
        let readings = Proc::parse_via_wpda_all("bitnot ((a))!(false)").expect("parse_all");
        assert_eq!(readings.len(), 2, "classic multiset is n=2, got {}", readings.len());
    }

    /// The hole nested inside a send payload (n=1 both arms).
    #[test]
    fn send_payload_hosting_the_hole_parses() {
        fresh();
        let t = parse("x!(bitnot (a)!(false))");
        assert!(
            format!("{t:?}").starts_with("POutput"),
            "expected POutput..(payload BitNot..), got: {t:?}"
        );
    }

    /// Fence (outcome parity): the chained second send is REFUSED by both
    /// arms — the reset fires at the FIRST `!` then the second-send lineage
    /// strands (classic-parity ERR; resets ≥ 1 here is EXPECTED, receipts
    /// armg_d1_chained.log / §1.4 of the v2 plan).
    #[test]
    fn fence_chained_send_refused_both_arms() {
        fresh();
        assert!(Proc::parse("bitnot (a)!(Nil)!(Nil)").is_err());
    }

    /// Fence (outcome parity): PDrop over a grouped-channel send is REFUSED
    /// by both arms (POutput is Proc; PDrop's operand slot is Name).
    #[test]
    fn fence_pdrop_grouped_send_refused_both_arms() {
        fresh();
        assert!(Proc::parse("*(a)!(false)").is_err());
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// TASK #10 ITEM 2b (2026-07-14, USER-APPROVED): behavioral pins for the two
// facade realize-mode contract restorations (ledger_followups_plan §ITEM-2
// design step 6, amendment 4).
//
// Pre-2b, the walker inferred single-result semantics from `limit` being a
// power of two ≤ 128 (the RAW_PROBE_CAPS coupling). Two facade helpers sat in
// the trap range and silently ELECTED where their contract is ENUMERATION:
//   - `__mettail_wpda_collect_prefix` (the bounded-prefix `_all` facade):
//     probe limit = max_alternatives + 1, so `max_alternatives ∈
//     {1,3,7,15,31,63,127}` collapsed the ambiguity-preserving facade to the
//     single elected reading.
//   - `__mettail_wpda_find_surface_exact` (the `Cat::parse` display-exact
//     surface repair): per-root limit starts at 128, so BIN roots elected 1
//     reading, `exhausted_all_roots` stayed true, and the probe returned
//     `Ok(None)` after one pass — surface faithfulness silently dead.
//
// Pin family per amendment 4: the grp_d1 twins `@Nil!(@(@Nil)!())` — a
// display-DISTINCT 2-reading family (kept `NParen` twin displays as the
// source text; the transparent twin displays `@Nil!(@@Nil!())`), both
// semantically distinct so the prefix facade's semantic dedup keeps both.
// `@a!(0,1)` is explicitly EXCLUDED (its 2 raw derivations semantically
// dedup to 1). P4 classic-lever receipt: reading count = 2 both arms
// (logs_task10/baseline_head/rows_{pure,lever}.log, AST-COUNT 2).
// ════════════════════════════════════════════════════════════════════════════════

mod realize_mode_contract_pins {
    use super::*;
    use mettail_prattail::wpda_runtime::LatticeTokenSource;

    /// Item-2b pin 1 (collect_prefix): the bounded-prefix facade at
    /// `max_alternatives = 3` (probe limit 4 — inside the pre-2b trap range)
    /// on the 2-reading grp_d1 family must return BOTH display-distinct
    /// alternatives. Pre-2b it returned exactly 1 (the elected reading).
    #[test]
    fn prefix_bounded_alternatives_enumerate_display_distinct_family() {
        fresh();
        let dag = lex_dag("@Nil!(@(@Nil)!())").expect("grp_d1 lexes");
        let source = LatticeTokenSource::new(dag);
        let mut pos = 0usize;
        let (terms, weights) = parse_Proc_via_wpda_prefix_with_source(&source, &mut pos, 0, 3)
            .expect("grp_d1 parses through the bounded-prefix facade");
        assert_eq!(terms.len(), weights.len(), "term-parallel weights");
        let mut displays: Vec<String> = terms.iter().map(|t| format!("{t}")).collect();
        displays.sort();
        assert_eq!(
            displays,
            vec!["@Nil!(@(@Nil)!())".to_string(), "@Nil!(@@Nil!())".to_string(),],
            "the bounded-prefix facade must enumerate the full 2-reading \
             display-distinct family (pre-2b trap: collapsed to the single \
             elected reading)"
        );
    }

    /// Item-2b pin 2 (find_surface_exact): the display-exact surface probe
    /// must FIND the display-exact NON-elected reading. The single-result
    /// election on `@Nil!(@(@Nil)!())` elects the NParen-kept twin (whose
    /// display reproduces the source text); the transparent twin displays
    /// `@Nil!(@@Nil!())` and is reachable only by ENUMERATING the packing
    /// family. Pre-2b the probe elected, missed, and reported `Ok(None)`.
    #[test]
    fn surface_exact_finds_non_elected_display_reading() {
        fresh();
        let dag = lex_dag("@Nil!(@(@Nil)!())").expect("grp_d1 lexes");
        let source = LatticeTokenSource::new(dag);
        let mut pos = 0usize;
        let found = parse_Proc_via_wpda_surface_exact_with_source(
            &source,
            &mut pos,
            0,
            "@Nil!(@@Nil!())",
            128,
        )
        .expect("the surface-exact probe must not error on a parseable input");
        let (term, _weight) = found.expect(
            "the display-exact non-elected reading must be FOUND by family \
             enumeration (pre-2b trap: one elected pass, then Ok(None))",
        );
        assert_eq!(
            format!("{term}"),
            "@Nil!(@@Nil!())",
            "the found reading's display must reproduce the requested surface"
        );
    }

    /// Fence: the same surface probe still reports `Ok(None)` for a display
    /// NO reading of this family has — enumeration must not fabricate.
    #[test]
    fn surface_exact_still_rejects_unrealizable_display() {
        fresh();
        let dag = lex_dag("@Nil!(@(@Nil)!())").expect("grp_d1 lexes");
        let source = LatticeTokenSource::new(dag);
        let mut pos = 0usize;
        let found = parse_Proc_via_wpda_surface_exact_with_source(
            &source,
            &mut pos,
            0,
            "@Nil!(@(@(@Nil))!())",
            128,
        )
        .expect("the surface-exact probe must not error on a parseable input");
        assert!(
            found.is_none(),
            "no reading of grp_d1 displays the deeper-nested surface; the \
             probe must exhaust and report None, got {found:?}"
        );
    }
}

/// Residual #11-1 Branch B (USER-APPROVED 2026-07-14) — committed regression
/// pins for the polyadic-send `semantic_hash` normalization that closes the
/// facade-vs-walker gap. `parse_via_wpda_all` returns the set DEDUPED BY
/// semantic fingerprint, so the surviving length IS the distinct-semantic-key
/// count — a `== 2` pin is simultaneously the UPPER bound (the projection-
/// isolation prologue's receiver-led fold-duplicate reading is gone, 3->2) and
/// the LOWER bound / over-prune guard (the two genuine twins — Quoted
/// `NVar`-channel + Short `PVar`-channel — both survive as distinct keys, so
/// NOT collapsed to 1). Distinctness is proven by the deduped count, not by
/// display: the twins display identically as the source text.
mod branch_b_send_normalization_pins {
    use super::*;

    /// Output family: the `@`-led polyadic string facade dedups 3->2 to match
    /// the walker. The folded reading is the prologue's receiver-led
    /// `POutput2Plus(NQuoteShort(a),..)` == its Short twin.
    #[test]
    fn output_polyadic_send_facade_dedups_to_two_twins() {
        fresh();
        assert_eq!(
            Proc::parse_via_wpda_all("@a!(0,1)")
                .expect("parse_all")
                .len(),
            2
        );
        assert_eq!(
            Proc::parse_via_wpda_all("@a!(0,1,2)")
                .expect("parse_all")
                .len(),
            2
        );
        assert_eq!(
            Proc::parse_via_wpda_all("@a!(1+2,3)")
                .expect("parse_all")
                .len(),
            2
        );
    }

    /// Over-prune guard (generalized predicate, condition (b) param-bottomed):
    /// `@Nil!(0,1)` keeps its Nil twin (3->2, NEVER 3->1). `POutputNil2Plus`
    /// is EXCLUDED from the fold because its channel wraps the `PZero` nullary
    /// literal, not a receiver parameter — so only the Short spelling folds.
    #[test]
    fn nil_channel_polyadic_send_keeps_its_twin() {
        fresh();
        assert_eq!(
            Proc::parse_via_wpda_all("@Nil!(0,1)")
                .expect("parse_all")
                .len(),
            2
        );
    }

    /// Persist family (red-team A4, measurement-gated): `@a!!(0,1)` walker == 1
    /// (no Quoted twin), so the facade folds 2->1 to match the walker.
    #[test]
    fn persist_polyadic_send_facade_matches_walker() {
        fresh();
        assert_eq!(
            Proc::parse_via_wpda_all("@a!!(0,1)")
                .expect("parse_all")
                .len(),
            1
        );
        assert_eq!(
            Proc::parse_via_wpda_all("@a!!(0,1,2)")
                .expect("parse_all")
                .len(),
            1
        );
    }

    /// Controls (unchanged): the scalar send `@a!(0)` already normalized this
    /// receiver-led collision (stays 2); the bare-ident send `a!(0,1)` has no
    /// quote-wrapped channel to fold (stays 1).
    #[test]
    fn send_normalization_controls_unchanged() {
        fresh();
        assert_eq!(Proc::parse_via_wpda_all("@a!(0)").expect("parse_all").len(), 2);
        assert_eq!(
            Proc::parse_via_wpda_all("a!(0,1)")
                .expect("parse_all")
                .len(),
            1
        );
    }

    /// Red-team A5: the fold drops the receiver-led DUPLICATE, never the
    /// elected representative — the elected single-result `@a!(0,1)` remains an
    /// output send (structurally the walker's rep).
    #[test]
    fn elected_rep_is_an_unchanged_output_send() {
        fresh();
        let t = parse("@a!(0,1)");
        assert!(
            format!("{t:?}").starts_with("POutput"),
            "elected @a!(0,1) rep must be an output send, got: {t:?}"
        );
    }
}

/// #29 — `is_ground` must DESCEND into a collection literal.
///
/// `is_ground` is consulted to decide whether a term may be treated as a finished
/// value, so the two error directions are not symmetric. A false `false` costs a
/// redundant descent. A false `true` LICENSES DOWNSTREAM CODE TO SKIP WORK THAT WAS
/// REQUIRED, silently — which is what the generated matcher did: the
/// `CollectionLiteral` arm shared the scalar-literal arm and answered `true`
/// unconditionally, without looking at its elements.
///
/// A scalar literal genuinely is ground — its payload is a native value with no term
/// structure. A collection literal is a container OF TERMS, each of which may be a
/// free variable. These rows pin the distinction in the failure direction.
#[cfg(test)]
mod is_ground_descends_into_collection_literals {
    use mettail_languages::rhocalc::Proc;

    fn parse(src: &str) -> Proc {
        Proc::parse_via_wpda(src).unwrap_or_else(|err| panic!("{src:?} must parse: {err:?}"))
    }

    #[test]
    fn a_closed_list_literal_is_ground() {
        // The control. If this ever fails the descent has become unfaithful in the
        // harmless direction, which is still a defect worth seeing.
        assert!(parse("[1, 2, 3]").is_ground(), "a list of ground elements must report ground");
    }

    #[test]
    fn an_empty_list_literal_is_ground() {
        // Vacuous truth over the elements — `all` on an empty iterator. Pinned
        // because a descent written with `any` instead of `all` would invert here
        // and nowhere else.
        assert!(parse("[]").is_ground(), "an empty list must report ground");
    }

    #[test]
    fn a_list_literal_containing_a_free_variable_is_not_ground() {
        // ★ THE ROW THAT WAS FAILING. Before the fix this returned `true`: the arm
        // matched `CollectionLiteral(_)` and answered without descending, so a free
        // `v` inside the container was invisible.
        assert!(
            !parse("[1, v]").is_ground(),
            "a list containing the free variable `v` must NOT report ground — this is \
             the failure direction, where a wrong answer silently licenses downstream \
             code to skip work"
        );
    }

    #[test]
    fn a_nested_list_literal_hides_nothing() {
        // The descent must be recursive, not one level deep: `is_ground` on the inner
        // list is itself the descending arm.
        assert!(
            !parse("[1, [2, v]]").is_ground(),
            "a free variable nested two containers deep must still defeat groundness"
        );
        assert!(
            parse("[1, [2, 3]]").is_ground(),
            "a fully closed nested list must still report ground"
        );
    }
}
