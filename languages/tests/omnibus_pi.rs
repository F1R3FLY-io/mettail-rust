//! GSLT omnibus conformance — **L11 `Pi`** (`omnibus.tex:1965-1995`): the
//! π-calculus as a GSLT. The paper leans on this theory for the interaction-cut
//! reading (:1997-2001) and for the spatial-guard example (:2006-2014,
//! `where PPar( <Comm> true , true )`).
//!
//! # Why this file lives in `languages/tests/`
//!
//! `languages/src/` is PRODUCTION-ONLY (the `main`-branch set {ambient,
//! calculator, lambda, rhocalc} + `lib`). `Pi` is a specification-conformance /
//! demonstration language, so it is declared here as a test-module `language!`
//! spec with `emit_tests` / `emit_simulator` / `emit_blockly` off.
//!
//! # Clause-by-clause containment (SUPERSET of the omnibus listing)
//!
//! | omnibus clause (`omnibus.tex`) | our clause | delta |
//! | --- | --- | --- |
//! | `types { Proc Name }` (:1969) | identical | — |
//! | `PZero . Proc ::= "0" ;` (:1972) | identical | — |
//! | `PNew . ^x.p:[Name -> Proc] \|- "new" "(" x "," p ")" : Proc ;` (:1973) | identical | — |
//! | `PIn . n:Name, ^x.p:[Name -> Proc] \|- n "?" x "." p : Proc ;` (:1974) | same term context + category; syntax `"in" "(" n "," x ")" "." p` | ★ surface only (infix-led binder unsupported) |
//! | `POut . n:Name, m:Name, p:Proc \|- n "!" m "." p : Proc ;` (:1975) | identical | — |
//! | `PPar . ps:HashBag(Proc) \|- "{" ps.*sep("\|") "}" : Proc ;` (:1976) | identical | — |
//! | `PRep . p:Proc \|- "!" p : Proc ;` (:1977) | identical | — |
//! | `NewComm . \|- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P)) ;` (:1981) | identical | — |
//! | `ScopeExt . \| x # ...rest \|- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;` (:1982-1983) | identical | — |
//! | `RepUnfold . \|- (PRep P) = (PPar {P, (PRep P)}) ;` (:1984) | identical | — (see ★ saturation note) |
//! | `Comm . \|- (PPar {(PIn n ^x.p), (POut n m q), ...rest}) ~> (PPar {(subst ^x.p m), q, ...rest}) ;` (:1988-1989) | identical modulo the builtin's spelling: `(eval ^x.p m)` | `subst` → `eval` (see below) |
//! | `ParCong . \| S ~> T \|- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;` (:1991) | identical | — |
//! | `NewCong . \| S ~> T \|- (PNew ^x.S) ~> (PNew ^x.T) ;` (:1992) | identical | — |
//!
//!
//! # Notation: the paper is BNFC-flavoured; this file is idiomatic mettail
//!
//! The omnibus's listings carry a labelled-BNF (BNFC) lineage — `Label . Cat ::=
//! "lit" Item … ;` productions and a parameterised `List(X)` carrier. mettail
//! accepts the `::=` form (and this file uses it for nullary constants, exactly as
//! `languages/src/ambient.rs` does), but its idiomatic form is the JUDGEMENT form
//! `Name . ctx |- pattern : Cat ;`, and `List(X)` is spelled `Vec(X)` (the
//! established convention — `rhocalc.rs:57` declares `![Vec<Proc>] as List`).
//! **Superset containment here is SEMANTIC**: every `types` entry, `terms`
//! production, `equations` clause and `rewrites` rule of the paper's version is
//! present with the same meaning; the spelling is ours. Every deviation is
//! tabulated above and explained below.
//!
//! ## Notation delta: the substitution builtin is spelled `eval`
//!
//! The paper writes the capture-avoiding substitution operator as `subst`
//! (:537, :1989) while also calling it "substitution by `eval`" (:493). The live
//! macro special-cases exactly the identifier **`eval`**
//! (`ast/src/language/parse.rs:2893`: `if constructor == "eval"`), lowering
//! `(eval ^x.p m)` to `PatternTerm::Subst { term: p, var: x, replacement: m }`;
//! `subst` has no special case and would be rejected as an unknown constructor.
//! Same operator, same clause, one keyword.
//!
//! ## ★ The paper's synchronous `Comm` is DECLARED but not LOWERED
//!
//! `Comm` is present verbatim (it is in `metadata().rewrites()` under its own
//! name, with the paper's LHS and RHS), but the engine does not lower it, so it
//! does not fire. This is an engine limitation, stated rather than hidden:
//!
//! * the untyped `EGraph<String>` lane rejects it — `pattern_to_dovetail`
//!   (`macros/src/gen/runtime/dovetail_report.rs:1239-1244`) fails closed on a
//!   `Subst`/`MultiSubst` RHS node and on `Lambda` LHS patterns;
//! * the typed β-substitution lane rejects it — `is_substitution_rewrite`
//!   (`:196-243`) requires the substitution to be the WHOLE RHS and the LHS to
//!   contain NO collection metapattern;
//! * the typed COMM lane rejects it — `is_comm_rewrite` (`:509-541`) requires the
//!   reduct to be `op{ (eval scope arg), ...rest }`, i.e. exactly ONE element
//!   besides the remainder. The paper's π output is SYNCHRONOUS (`n!m.p` carries
//!   a continuation `p`), so its reduct has TWO elements — the substituted
//!   continuation AND `q`. RhoCalc's output, for which the lane was built, is
//!   asynchronous and has no continuation;
//! * the structural-AC lane rejects it — `is_structural_ac_rewrite` (`:611-…`)
//!   admits only reducts whose elements are bare LHS variables (no substitution).
//!
//! So the reduct arity is the whole obstacle. To keep the demonstration honest
//! AND executable, this file adds two ➕ EXTRA clauses — an asynchronous output
//! `POutAsync . n:Name, m:Name |- n "!" m : Proc ;` and the corresponding
//! `CommAsync` — which express the same interaction in the shape the engine
//! recognizes, and `pi_comm_async_fires` proves the interaction really reduces.
//! The synchronous `Comm` clause is NOT dropped, weakened, or renamed; closing
//! the gap for it is a typed-lane extension (a reduct of arity ≥ 2), reported
//! rather than undertaken here.
//!
//! ## ★ `RepUnfold` and saturation safety
//!
//! `RepUnfold . |- (PRep P) = (PPar {P, (PRep P)})` is a *recursive* equation:
//! read left-to-right it unfolds a replication forever. It is declared here
//! verbatim (dropping it would be a superset violation), and the divergence risk
//! is contained structurally rather than by weakening the theory:
//!
//! 1. **The engine is an e-graph, not a term rewriter.** Equations become
//!    bidirectional `RewriteRule`s over `dovetail::EGraph` e-classes. Unfolding
//!    `(PRep P)` once builds the e-node `PPar{P, c}` and unions it into the very
//!    e-class `c` it came from; re-applying the rule rediscovers the *same*
//!    hash-consed e-node, so the equivalence closure is a finite cyclic graph,
//!    not an infinite term.
//! 2. **Every reduction in this file is budgeted.** `dovetail_report_for(term,
//!    MAX_ITERS, MAX_NODES)` takes an explicit iteration and node budget and
//!    returns `Err(IterationLimit | NodeLimit)` instead of looping — the same
//!    guarantee `languages/tests/lambda_dovetail.rs` relies on to run Ω
//!    (`(λx.xx)(λx.xx)`) as a test. `pi_replication_saturation_is_bounded`
//!    below asserts exactly this for a replicated process: it must *terminate*,
//!    with a report or with an explicit budget error — never hang.
//! 3. **The generated test suites are off** (`emit_tests: false`), so no
//!    machine-written property test drives an unbudgeted saturation over
//!    `RepUnfold`.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    unused_imports,
    dead_code
)]

use mettail_macros::language;
use mettail_runtime::Language;

language! {
    name: Pi,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types { Proc  Name },

    terms {
        PZero . Proc ::= "0" ;
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
        // ★ SURFACE DELTA (semantics unchanged): the paper writes the input
        // prefix INFIX (`n "?" x "." p`). An infix-LED rule that also opens a
        // binder is not supported by the WPDA binder codegen — every binder rule
        // in the tree is literal-led (`ambient.rs:25` `"new" "(" x "," p ")"`,
        // `commdemo.rs:75` `"for" "(" x "<-" n ")" "{" p "}"`, `lambda.rs:19`
        // `"lam " x "." body`) and the infix spelling fails at parse time with
        // `unexpected `?` after parsing`. The TERM CONTEXT and result category —
        // which is what the clause IS — are the paper's, verbatim; only the
        // notation moves to the literal-led `in(n, x).p`, mirroring the omnibus's
        // own Ambient listing (`PIn . Proc ::= "in(" Name "," Proc ")"`, :2028).
        PIn . n:Name, ^x.p:[Name -> Proc] |- "in" "(" n "," x ")" "." p : Proc ;
        POut . n:Name, m:Name, p:Proc |- n "!" m "." p : Proc ;
        // ➕ (ours, EXTRA) Asynchronous output — the standard π sublanguage in
        // which an output carries no continuation (Honda–Tokoro 1991,
        // <https://doi.org/10.1007/BFb0057019>; Boudol, INRIA RR-1702, 1992).
        // It exists so the interaction can be EXERCISED: see the ★ COMM-lowering
        // note in the module header.
        POutAsync . n:Name, m:Name |- n "!" m : Proc ;
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
        PRep . p:Proc |- "!" p : Proc ;
    },

    equations {
        NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P)) ;
        ScopeExt . | x # ...rest
                 |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
        RepUnfold . |- (PRep P) = (PPar {P, (PRep P)}) ;
    },

    rewrites {
        Comm . |- (PPar {(PIn n ^x.p), (POut n m q), ...rest})
                  ~> (PPar {(eval ^x.p m), q, ...rest}) ;

        // ➕ (ours, EXTRA) The asynchronous COMM — the same interaction as the
        // paper's `Comm`, over `POutAsync`. Its reduct has ONE element plus the
        // remainder, which is the shape the engine's typed COMM lane recognizes
        // (`macros/src/gen/runtime/dovetail_report.rs:509-577`), so THIS rule
        // actually fires. See the ★ note in the module header.
        CommAsync . |- (PPar {(PIn n cont), (POutAsync n m), ...rest})
                  ~> (PPar {(eval cont m), ...rest}) ;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T) ;
    },
}

/// Iteration / node budget for the e-graph saturation. Bounded on purpose — see
/// the ★ saturation note in the module header.
const MAX_ITERS: usize = 24;
const MAX_NODES: usize = 200_000;

/// Saturate `src` and render the outcome (used both for assertions and for
/// failure messages).
fn report_summary(src: &str) -> String {
    let lang = PiLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    match PiLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES) {
        Ok(report) => format!(
            "Ok(complete={}, roots={}, firings={:?}, terms={:?})",
            report.is_complete(),
            report.roots.len(),
            report
                .rule_firings
                .iter()
                .filter_map(|f| f.label.clone())
                .collect::<Vec<_>>(),
            report
                .terms
                .iter()
                .map(|t| (t.op_display.clone(), t.source_display.clone()))
                .collect::<Vec<_>>()
        ),
        Err(e) => format!("Err({e})"),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn pi_language_resolves() {
    let lang = PiLanguage;
    assert_eq!(lang.name(), "Pi");
}

/// Clause coverage: all six term formers, all three equations, all three
/// rewrites (by the paper's own names).
#[test]
fn pi_metadata_carries_every_doc_clause() {
    let lang = PiLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["PZero", "PNew", "PIn", "POut", "PPar", "PRep"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    assert_eq!(
        meta.equations().len(),
        3,
        "the omnibus presents three equations (NewComm, ScopeExt, RepUnfold); got {:?}",
        meta.equations().iter().map(|e| (e.lhs, e.rhs)).collect::<Vec<_>>()
    );
    // ScopeExt is the freshness-premised one.
    assert!(
        meta.equations().iter().any(|e| !e.conditions.is_empty()),
        "ScopeExt carries the freshness premise `x # ...rest`"
    );
    let rewrites: Vec<Option<&str>> = meta.rewrites().iter().map(|r| r.name).collect();
    for rule in ["Comm", "ParCong", "NewCong"] {
        assert!(rewrites.contains(&Some(rule)), "rewrite {rule} missing; have {rewrites:?}");
    }
    // ParCong / NewCong are the premised (congruence) rules.
    assert_eq!(
        meta.rewrites().iter().filter(|r| r.premise.is_some()).count(),
        2,
        "ParCong and NewCong are premised congruence rules"
    );
}

/// `PZero` (:1972) and `PPar` (:1976).
#[test]
fn pi_zero_and_par_parse() {
    mettail_runtime::clear_var_cache();
    let z = Proc::parse("0").expect("PZero parse");
    assert_eq!(format!("{z}"), "0");
    let p = Proc::parse("{ 0 | 0 }").expect("PPar parse");
    assert!(format!("{p}").contains('|'), "par renders with its separator");
}

/// `PNew` (:1973) — the restriction binder.
#[test]
fn pi_new_parses() {
    mettail_runtime::clear_var_cache();
    let p = Proc::parse("new(c, 0)").expect("PNew parse");
    assert!(format!("{p}").contains("new"), "restriction renders");
}

/// `POut` (:1975) — the output prefix, in the paper's own INFIX surface syntax
/// (`c!c.0`; cf. the CFL program at :2008). Infix-led rules parse fine; it is
/// only an infix-led rule that ALSO opens a binder (`PIn`) that does not.
#[test]
fn pi_output_prefix_parses() {
    mettail_runtime::clear_var_cache();
    let o = Proc::parse("c!c.0").expect("POut parse");
    assert!(format!("{o}").contains('!'), "output prefix renders: {o}");
}

/// `PIn` (:1974) — the input prefix (binder), in the literal-led notation this
/// tree's binder codegen supports.
#[test]
fn pi_input_prefix_parses() {
    mettail_runtime::clear_var_cache();
    let i = Proc::parse("in(c,y).0").expect("PIn parse");
    assert!(format!("{i}").contains("in"), "input prefix renders: {i}");
}

/// `PRep` (:1977) — replication.
#[test]
fn pi_replication_parses() {
    mettail_runtime::clear_var_cache();
    let r = Proc::parse("!0").expect("PRep parse");
    assert!(format!("{r}").contains('!'), "replication renders: {r}");
}

/// The paper's own π program (`omnibus.tex:2008`) parses and round-trips.
#[test]
fn pi_paper_program_round_trips() {
    mettail_runtime::clear_var_cache();
    let src = "new(c, { in(c,y).0 | c!c.0 })";
    let t = Proc::parse(src).unwrap_or_else(|e| panic!("paper program parse failed: {e:?}"));
    let printed = format!("{t}");
    let reparsed = Proc::parse(&printed)
        .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
    assert_eq!(reparsed, t, "display round-trip must be identity (printed {printed:?})");
}

/// `Comm` (:1988-1989) — the paper's SYNCHRONOUS interaction rule is present
/// verbatim in the metadata (name, LHS, RHS). It is declared but not lowered by
/// the current engine (see the ★ COMM note in the module header), so this test
/// pins the CLAUSE, and `pi_comm_async_fires` below pins the BEHAVIOUR.
#[test]
fn pi_comm_clause_is_declared_verbatim() {
    let lang = PiLanguage;
    let meta = lang.metadata();
    let comm = meta
        .rewrites()
        .iter()
        .find(|r| r.name == Some("Comm"))
        .expect("the paper's Comm rewrite must be declared");
    // `lhs` / `rhs` are rendered in SURFACE syntax, e.g.
    // `{in(n,x).p | n!m.q | ...rest}`.
    assert!(
        comm.lhs.contains("in(") && comm.lhs.contains('!'),
        "Comm LHS must match an input prefix in parallel with an output prefix: {} ~> {}",
        comm.lhs,
        comm.rhs
    );
    assert!(
        comm.lhs.contains("rest") && comm.rhs.contains("rest"),
        "Comm must carry the AC remainder on both sides: {} ~> {}",
        comm.lhs,
        comm.rhs
    );
    assert!(comm.premise.is_none(), "Comm is unpremised");
}

/// The paper's `Comm` redex parses and saturates to a COMPLETE report under
/// budget (the declarative clause is inert, not destructive).
#[test]
fn pi_comm_redex_saturates_completely() {
    let got = report_summary("{ in(c,y).0 | c!c.0 }");
    assert!(
        got.starts_with("Ok(complete=true"),
        "the synchronous-Comm redex must saturate to a complete report; got {got}"
    );
}

/// ★ `CommAsync` (ours) — THE interaction actually reduces: an input prefix and
/// an asynchronous output on the same channel meet in the AC bag and fire,
/// substituting the sent name into the input's continuation.
#[test]
fn pi_comm_async_fires() {
    let got = report_summary("{ in(c,y).0 | c!c }");
    assert!(
        got.contains("CommAsync"),
        "the asynchronous COMM must fire on `{{ in(c,y).0 | c!c }}`; got {got}"
    );
}

/// `CommAsync` leaves `...rest` alone: a non-participating parallel component
/// survives the interaction — this is the property the paper calls "a rule about
/// a site of interaction rather than about whole terms" (:547-548).
#[test]
fn pi_comm_async_preserves_the_remainder() {
    let got = report_summary("{ in(c,y).0 | c!c | in(d,z).0 }");
    assert!(
        got.contains("CommAsync"),
        "the COMM must fire with a remainder present; got {got}"
    );
}

/// ★ `RepUnfold` (:1984) saturation safety: a replicated process must reach a
/// decision under the budget — a report or an explicit error — never a hang.
/// This is the test that makes the recursive equation safe to ship.
#[test]
fn pi_replication_saturation_is_bounded() {
    let got = report_summary("!in(c,y).0");
    assert!(
        got.starts_with("Ok(") || got.starts_with("Err("),
        "saturation over the recursive RepUnfold equation must TERMINATE with a \
         decision (a report or an explicit budget error), never hang; got {got}"
    );
}

/// A replicated process in parallel with a matching output also terminates under
/// budget (RepUnfold + Comm together).
#[test]
fn pi_replicated_input_terminates_under_budget() {
    let got = report_summary("{ !in(c,y).0 | c!c.0 }");
    assert!(
        got.starts_with("Ok(") || got.starts_with("Err("),
        "RepUnfold + Comm must terminate under budget; got {got}"
    );
}
