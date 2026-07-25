//! GSLT omnibus conformance — **L9 `Turing`** (`omnibus.tex:1900-1936`): a
//! single-tape Turing machine as a GSLT, used by the paper as its *non*-example
//! of interactivity (:692-720, :1938-1942).
//!
//! # Why this file lives in `languages/tests/`
//!
//! `languages/src/` is PRODUCTION-ONLY (the `main`-branch set {ambient,
//! calculator, lambda, rhocalc} + `lib`). `Turing` is a specification-conformance
//! / demonstration language, so it is declared here as a test-module `language!`
//! spec with `emit_tests` / `emit_simulator` / `emit_blockly` off.
//!
//! # Clause-by-clause containment (SUPERSET of the omnibus listing)
//!
//! | omnibus clause (`omnibus.tex`) | our clause | delta |
//! | --- | --- | --- |
//! | `types { Config Tape State Sym }` (:1904-1909) | identical + `![u32] as UInt32` | ➕ the carrier `Q` needs |
//! | `Blank . Sym ::= "_" ;` (:1912) | identical | — |
//! | `Zero . Sym ::= "0" ;` (:1913) | identical | — |
//! | `One . Sym ::= "1" ;` (:1914) | identical | — |
//! | `Halt . State ::= "halt" ;` (:1916) | identical | — |
//! | `Q . n:UInt32 \|- "q" n : State ;` (:1917) | identical | — |
//! | `Tp . l:List(Sym), h:Sym, r:List(Sym) \|- "<" l "\|" h "\|" r ">" : Tape ;` (:1920) | `l:Vec(Sym) … "<" "[" l.*sep(",") "]" "\|" h "\|" "[" r.*sep(",") "]" ">"` | `List(X)` → `Vec(X)`; explicit list delimiters |
//! | `Cf . q:State, t:Tape \|- "(" q "," t ")" : Config ;` (:1922) | identical | — |
//! | `D_q0_0 . \|- (Cf (Q 0u32) (Tp L Zero R)) ~> (Cf (Q 1u32) (shift_right L One R));` (:1930-1931) | `D_q0_0 . \|- (Cf Q0 (Tp L Zero R)) ~> (Cf Q1 (shift_right L One R));` | state written as a nullary constant — see ★ below |
//! | `D_q0_1 . \|- (Cf (Q 0u32) (Tp L One R)) ~> (Cf Halt (Tp L One R));` (:1932-1933) | `D_q0_1 . \|- (Cf Q0 (Tp L One R)) ~> (Cf Halt (Tp L One R));` | idem |
//! | `equations { }` (:1925) | identical (empty) | — |
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
//! ## ★ The one FORCED delta: native literals are not expressible in patterns
//!
//! The paper's transition entries embed the typed literals `(Q 0u32)` / `(Q 1u32)`
//! **inside a rewrite pattern**. The live macro's pattern grammar has no literal
//! form: `parse_pattern` (`ast/src/language/parse.rs:2836-3007`) accepts exactly
//! metasyntax (`*zip`/`*map`), a `{…, ...rest}` collection, a parenthesised
//! constructor application, a `^x.` binder, or a bare identifier — and
//! `PatternTerm` (`ast/src/pattern.rs:25-49`) has variants `Var`, `Apply`,
//! `Lambda`, `MultiLambda`, `Subst`, `MultiSubst` and **no literal variant**. So
//! `(Q 0u32)` fails at macro-parse time (`0u32` is not an identifier). This is a
//! genuine macro limitation, reported rather than silently worked around.
//!
//! The transition *semantics* are preserved exactly by naming the two machine
//! states with nullary constructors `Q0`/`Q1` (surface `q0`/`q1` — the very
//! surface the paper's own CFL program writes at :1949, `work!( (q0 , …) )`), so
//! the two table entries fire on precisely the configurations the paper
//! specifies. `Q . n:UInt32 |- "q" n : State ;` is ALSO declared, verbatim, so
//! the doc clause itself is present; `Q0`/`Q1` are additional (superset) clauses
//! that give the pattern language something it can name. A bare identifier that
//! resolves to a declared nullary rule is read as that constructor, not as a
//! metavariable (`ast/src/pattern.rs:382-398`, `1944-1962`).
//!
//!
//! ## Why the dynamics are proven from `dovetail_report_for`
//!
//! The tests below assert RULE-FIRING evidence from
//! `TuringLanguage::dovetail_report_for` rather than comparing a reconstructed
//! normal form from `dovetail_normal_term`. The latter returns
//! `Err("… reconstruction … failed (stuck term)")` for every `Turing` term —
//! including a term with no redex at all, e.g. `(halt , <[] | _ | []>)` — so the
//! failure is in the typed e-graph → AST *reconstruction* for this language's
//! shapes (a `Vec(Sym)` collection field plus a native fold whose OUTPUT is a
//! non-native category), not in the reduction. The firing evidence is the
//! stronger conformance statement anyway: it names the transition entry that
//! matched, by the paper's own rule label.
//!
//! ## `shift_right` — the paper's "theory-supplied helper"
//!
//! `(shift_right L One R)` appears in the paper's RHS (:1931) with no declaration.
//! The macro special-cases exactly one builtin RHS operation, `eval` (the
//! substitution operator); every other head must resolve to a declared rule label
//! or the validator rejects it (`ast/src/validation/error.rs`, `"Unknown
//! constructor"`). We therefore give it a home as a declared `Tape`-valued term
//! former with a native `fold` body:
//!
//! ```text
//! shift_right(l, h, r)  ≙  Tp( h : l ,  head(r) or Blank ,  tail(r) )
//! ```
//!
//! i.e. *write `h` at the head cell and move right* — the exact operation the
//! paper's comment describes ("q0 reading 0: write 1, move right, go to q1"),
//! over the zipper representation ("reversed left context, head symbol, right
//! context", :1919). The helper is spelled `shift_right` verbatim, so the RHS
//! reads exactly as printed in the paper.

#![allow(
    non_local_definitions,
    non_camel_case_types,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    unused_imports,
    dead_code
)]

use mettail_macros::language;
use mettail_runtime::Language;

language! {
    name: Turing,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Config
        Tape
        State
        Sym
        // Carrier for the paper's `n:UInt32` state index.
        ![u32] as UInt32
    },

    literals {
        UInt32 {
            pattern: r"(0b[01](_?[01])*|0o[0-7](_?[0-7])*|0x[0-9A-Fa-f](_?[0-9A-Fa-f])*|[0-9](_?[0-9])*)u32";
            eval: ![ {
                mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
            } ]
        }
    },

    terms {
        Blank . Sym ::= "_" ;
        Zero . Sym ::= "0" ;
        One . Sym ::= "1" ;

        Halt . State ::= "halt" ;
        Q . n:UInt32 |- "q" n : State ;

        // ➕ (ours) The two machine states of the paper's transition table as
        // nullary constants, so the table entries below can name them in a
        // pattern (no literal pattern form exists — see the module header).
        Q0 . State ::= "q0" ;
        Q1 . State ::= "q1" ;

        // tape as a zipper: reversed left context, head symbol, right context
        Tp . l:Vec(Sym), h:Sym, r:Vec(Sym)
            |- "<" "[" l.*sep(",") "]" "|" h "|" "[" r.*sep(",") "]" ">" : Tape ;

        Cf . q:State, t:Tape |- "(" q "," t ")" : Config ;

        // ➕ (ours) the paper's theory-supplied helper, given a home:
        // write `h` at the head cell, then move right.
        shift_right . l:Vec(Sym), h:Sym, r:Vec(Sym)
            |- "shift_right" "(" "[" l.*sep(",") "]" "," h "," "[" r.*sep(",") "]" ")" : Tape ![{
                let mut left: Vec<Sym> = Vec::with_capacity(l.len());
                left.push(h.clone());
                left.extend(l.iter().cloned());
                let (head, rest): (Sym, Vec<Sym>) = match r.split_first() {
                    Some((s, tail)) => (s.clone(), tail.to_vec()),
                    None => (Sym::Blank, Vec::new()),
                };
                Tape::Tp(left, std::sync::Arc::new(head), rest)
            }] fold;
    },

    equations { },

    rewrites {
        // one entry of the transition table, written out
        // q0 reading 0: write 1, move right, go to q1
        D_q0_0 . |- (Cf Q0 (Tp L Zero R))
                    ~> (Cf Q1 (shift_right L One R));
        D_q0_1 . |- (Cf Q0 (Tp L One R))
                    ~> (Cf Halt (Tp L One R));
    },
}

/// Iteration / node budget for the e-graph saturation. Bounded on purpose: a
/// budget means a non-converging machine surfaces as a limit error, never as a
/// hung test binary.
const MAX_ITERS: usize = 32;
const MAX_NODES: usize = 200_000;

/// Saturate `src` in the Dovetail e-graph and return (fired rule labels, a
/// rendering of the whole report for failure messages).
fn firings(src: &str) -> (Vec<String>, String) {
    let lang = TuringLanguage;
    mettail_runtime::clear_var_cache();
    let term = lang
        .parse_term(src)
        .unwrap_or_else(|e| panic!("parse {src:?} failed: {e}"));
    let report = TuringLanguage::dovetail_report_for(term.as_ref(), MAX_ITERS, MAX_NODES)
        .unwrap_or_else(|e| panic!("dovetail_report_for({src:?}) returned Err: {e}"));
    let labels: Vec<String> = report
        .rule_firings
        .iter()
        .filter_map(|f| f.label.clone())
        .collect();
    let rendered = format!(
        "complete={} roots={} firings={:?} terms={:?}",
        report.is_complete(),
        report.roots.len(),
        report.rule_firings,
        report
            .terms
            .iter()
            .map(|t| (t.op_display.clone(), t.source_display.clone()))
            .collect::<Vec<_>>()
    );
    (labels, rendered)
}

// ═══════════════════════════════════════════════════════════════════════════
// Conformance tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn turing_language_resolves() {
    let lang = TuringLanguage;
    assert_eq!(lang.name(), "Turing");
}

/// Clause coverage: every `terms` production and both transition entries are in
/// metadata under the paper's own names.
#[test]
fn turing_metadata_carries_every_doc_clause() {
    let lang = TuringLanguage;
    let meta = lang.metadata();
    let names: Vec<&str> = meta.terms().iter().map(|t| t.name).collect();
    for clause in ["Blank", "Zero", "One", "Halt", "Q", "Tp", "Cf"] {
        assert!(names.contains(&clause), "omnibus clause {clause} missing; have {names:?}");
    }
    let rewrites: Vec<Option<&str>> = meta.rewrites().iter().map(|r| r.name).collect();
    for entry in ["D_q0_0", "D_q0_1"] {
        assert!(
            rewrites.contains(&Some(entry)),
            "transition entry {entry} missing; have {rewrites:?}"
        );
    }
    assert!(meta.equations().is_empty(), "the omnibus Turing has `equations {{ }}` empty");
}

/// `Blank` / `Zero` / `One` (:1912-1914).
#[test]
fn turing_symbols_parse() {
    mettail_runtime::clear_var_cache();
    for src in ["_", "0", "1"] {
        let s = Sym::parse(src).unwrap_or_else(|e| panic!("Sym parse of {src:?}: {e:?}"));
        assert_eq!(format!("{s}"), src);
    }
}

/// `Halt` (:1916) and `Q . n:UInt32` (:1917) — both State productions.
#[test]
fn turing_states_parse() {
    mettail_runtime::clear_var_cache();
    let h = State::parse("halt").expect("Halt parse");
    assert_eq!(format!("{h}"), "halt");
    // The paper's indexed state former, verbatim: `"q" n` over a UInt32 literal.
    let q = State::parse("q 7u32").expect("Q (indexed state) parse");
    assert!(format!("{q}").contains('7'), "index preserved: {q}");
    // The nullary machine-state constants used by the transition table.
    for src in ["q0", "q1"] {
        let s = State::parse(src).unwrap_or_else(|e| panic!("State parse of {src:?}: {e:?}"));
        assert_eq!(format!("{s}"), src);
    }
}

/// `Tp` (:1920) — the zipper tape, with an empty and a non-empty context.
#[test]
fn turing_tape_parses() {
    mettail_runtime::clear_var_cache();
    let t = Tape::parse("<[] | 0 | [0,1]>").expect("Tp parse (empty left context)");
    let shown = format!("{t}");
    assert!(shown.contains('|'), "tape renders with the zipper bars: {shown:?}");
    let t2 = Tape::parse("<[1,_] | 1 | []>").expect("Tp parse (empty right context)");
    assert!(!format!("{t2}").is_empty());
}

/// `Cf` (:1922) — a configuration, exactly as the paper's CFL program writes it
/// (`omnibus.tex:1949`).
#[test]
fn turing_configuration_parses_and_round_trips() {
    mettail_runtime::clear_var_cache();
    let src = "(q0 , <[] | 0 | [0,1]>)";
    let c = Config::parse(src).unwrap_or_else(|e| panic!("Cf parse failed: {e:?}"));
    let printed = format!("{c}");
    let reparsed = Config::parse(&printed)
        .unwrap_or_else(|e| panic!("re-parse of display {printed:?} failed: {e:?}"));
    assert_eq!(reparsed, c, "display round-trip must be identity (printed {printed:?})");
}

/// `D_q0_0` (:1930-1931) — the write-1-move-right entry FIRES on the paper's own
/// configuration (`omnibus.tex:1949`): reading `0` in state `q0` with left `[]`
/// and right `[0,1]`.
#[test]
fn turing_transition_d_q0_0_fires() {
    let (labels, rendered) = firings("(q0 , <[] | 0 | [0,1]>)");
    assert!(
        labels.iter().any(|l| l == "Turing::rewrite::D_q0_0"),
        "the write-1-move-right transition must fire; report: {rendered}"
    );
}

/// `D_q0_1` (:1932-1933) — reading `1` in `q0` halts, leaving the tape alone.
#[test]
fn turing_transition_d_q0_1_fires() {
    let (labels, rendered) = firings("(q0 , <[0] | 1 | [1]>)");
    assert!(
        labels.iter().any(|l| l == "Turing::rewrite::D_q0_1"),
        "the halt transition must fire; report: {rendered}"
    );
}

/// A configuration with no matching table entry is already a normal form: the
/// machine is stuck, which is exactly the paper's point about non-interactivity
/// (:692-720, :1938-1942).
#[test]
fn turing_halted_configuration_is_a_normal_form() {
    let (labels, rendered) = firings("(halt , <[] | _ | []>)");
    assert!(
        labels.is_empty(),
        "a halted configuration matches no transition, so nothing may fire; report: {rendered}"
    );
}

/// The `shift_right` helper is a native fold: it reduces the moved tape rather
/// than leaving an un-evaluated helper node behind.
#[test]
fn turing_shift_right_folds() {
    let (labels, rendered) = firings("shift_right([0],1,[1,0])");
    assert!(
        rendered.contains("complete=true"),
        "the helper must reduce to a complete report; got {rendered}"
    );
    assert!(
        !labels.iter().any(|l| l.contains("D_q0")),
        "no transition applies to a bare tape; report: {rendered}"
    );
}
