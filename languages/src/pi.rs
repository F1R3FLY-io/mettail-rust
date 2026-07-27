//! GSLT omnibus conformance — **L11 `Pi`** (`omnibus.tex:1965-1995`): the
//! π-calculus as a GSLT. The paper leans on this theory for the interaction-cut
//! reading (:1997-2001) and for the spatial-guard example (:2006-2014,
//! `where PPar( <Comm> true , true )`).
//!
//! # Why this file lives in `languages/src/`
//!
//! The language specifications transcribed from the GSLT omnibus paper are
//! PRODUCTION specs (USER ruling, 2026-07-27), so they live beside the other
//! production languages in `languages/src/` and are reachable through the
//! crate's public surface as `mettail_languages::pi`. Its conformance suite is
//! `languages/tests/pi.rs` — the same spec/tests split every other production
//! spec uses (`languages/src/calculator.rs` ↔ `languages/tests/calculator.rs`).
//!
//! `emit_tests` / `emit_simulator` / `emit_blockly` stay OFF. Those three
//! options are the macro's file-writing switches, so with them off this spec
//! writes no `languages/tests/gen_pi_*.rs`, no `languages/src/bin/simulate_pi.rs`
//! and no `languages/src/generated/pi-*.ts`. For `Pi` the first of the three is
//! not merely a size decision but a SAFETY one — see the ★ saturation note
//! below.
//!
//! ⚠ Those three `false`s must STAY false, and not because production specs are
//! forbidden generated suites — `ambient`/`calculator`/`lambda`/`rhocalc` all
//! carry theirs. `emit_simulator: true` would make the macro write
//! `languages/src/bin/simulate_pi.rs` on every compile, and cargo's edition-2021
//! auto-discovery would pick that file up as a binary target with NO
//! `required-features = ["strategies"]` — every hand-declared `[[bin]]` in
//! `languages/Cargo.toml` carries that gate because the generated simulator names
//! `mettail_languages::pi::strategies::arb_*`, which exists only under the
//! `strategies` feature. A default `cargo build -p languages` would then fail to
//! compile a file nobody wrote. Flipping these on is a change to the macro's
//! emission contract, not a per-language switch.
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
//! ## ★★ The paper's synchronous `Comm` FIRES (delta D10 — CLOSED)
//!
//! `Comm` is present verbatim (it is in `metadata().rewrites()` under its own
//! name, with the paper's LHS and RHS) and it **reduces**:
//! `pi_comm_fires_verbatim` saturates the omnibus's own redex
//! `{ in(c,y).0 | c!c.0 }` and asserts the report names the rule `Comm`.
//!
//! It did not always. When this file was first written the typed COMM lane
//! (`is_comm_rewrite`, `macros/src/gen/runtime/dovetail_report.rs`) rejected the
//! clause on two counts, recorded as delta **D10**:
//!
//! 1. **reduct arity** — the lane required the reduct to be
//!    `op{ (eval scope arg), ...rest }`, i.e. exactly ONE element besides the
//!    remainder. The paper's π output is SYNCHRONOUS (`n!m.q` carries a
//!    continuation `q`), so its reduct has TWO: the substituted receive
//!    continuation AND `q`. RhoCalc's output — the shape the lane was first
//!    written for — is asynchronous and has no continuation;
//! 2. **binder spelling** — the lane required every structured LHS element
//!    argument to be a bare variable, while the paper writes the receive's scope
//!    as an EXPLICIT abstraction `(PIn n ^x.p)`.
//!
//! Neither was a semantic constraint. The reduct bag `op{…}` IS the AC parallel
//! operator the LHS matched over, so an `m`-element reduct simply denotes the
//! parallel composition `p[m/x] | q` — exactly π's `c!x.P | c?y.Q ⇒ P | Q{x/y}`;
//! and `^x.p` lowers to the same `[…, BinderArity(1), body]` element pattern a
//! bare scope variable does (the dispatch arm rebuilds a FRESH binder before
//! substituting, so the pattern's binder name is α-irrelevant). The lane now
//! admits reducts of arity `m ≥ 1` — exactly one host-computed substitution plus
//! `m - 1` σ-delivered LHS variables — and the explicit abstraction spelling in
//! the scope position of a single-`Binder` constructor. Both fail closed
//! otherwise; in particular a σ-delivered reduct element may never be a binder
//! SCOPE, which would let the bound variable escape.
//!
//! The other three lanes still decline, and correctly so — each has its own
//! family, and the COMM lane is the one that owns this shape:
//!
//! * the untyped `EGraph<String>` lane — `pattern_to_dovetail` fails closed on a
//!   `Subst`/`MultiSubst` RHS node and on `Lambda` LHS patterns (a Comm rewrite
//!   never reaches it: `needs_typed_dovetail_path` routes the language typed);
//! * the typed β-substitution lane — `is_substitution_rewrite` requires the
//!   substitution to be the WHOLE RHS and the LHS to contain NO collection
//!   metapattern;
//! * the structural-AC lane — `is_structural_ac_rewrite` admits only reducts
//!   whose elements are ALL bare LHS variables (no substitution), which is the
//!   exact complement of the COMM lane's "exactly one substitution".
//!
//! ## ➕ The asynchronous clauses `POutAsync` / `CommAsync` are KEPT
//!
//! This file also declares an asynchronous output `POutAsync . n:Name, m:Name |-
//! n "!" m : Proc ;` and its `CommAsync`. They were originally added because the
//! synchronous rule could not fire; they are **retained now that it can**,
//! deliberately, because asynchronous π is a calculus in its own right
//! (Honda–Tokoro 1991, <https://doi.org/10.1007/BFb0057019>; Boudol, INRIA
//! RR-1702, 1992) and a conformance spec is allowed to be a SUPERSET of the
//! paper's listing — which is precisely what the containment table above claims
//! ("13/13 + 2 extra"). Retiring them would shrink the demonstrated coverage and
//! delete the only in-tree exemplar of the arity-1 reduct in an omnibus spec.
//! `pi_comm_async_fires` continues to pin them; they are no longer a workaround,
//! and nothing in the synchronous path depends on them.
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
//! 2. **Every reduction in the conformance suite is budgeted.**
//!    `dovetail_report_for(term, MAX_ITERS, MAX_NODES)` takes an explicit
//!    iteration and node budget and returns `Err(IterationLimit | NodeLimit)`
//!    instead of looping — the same guarantee
//!    `languages/tests/lambda_dovetail.rs` relies on to run Ω
//!    (`(λx.xx)(λx.xx)`) as a test. `pi_replication_saturation_is_bounded`, in
//!    `languages/tests/pi.rs`, asserts exactly this for a replicated process: it
//!    must *terminate*, with a report or with an explicit budget error — never
//!    hang.
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
        // A deliberate SUPERSET clause, kept on its own merits: asynchronous π
        // is a calculus in its own right. (It predates D10's closure, when it
        // was also the only executable spelling; that is no longer why it is
        // here — see the ➕ note in the module header.)
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

        // ➕ (ours, EXTRA) The asynchronous COMM — the interaction of the
        // asynchronous π sublanguage, over `POutAsync`. Its reduct is the
        // ARITY-1 bag `{(eval cont m), ...rest}` (no output continuation to run
        // in parallel), the complementary case to the paper's synchronous
        // arity-2 `Comm` above; both are the SAME typed COMM lane, which admits
        // `m ≥ 1` reduct elements. Pinned by `pi_comm_async_fires`.
        CommAsync . |- (PPar {(PIn n cont), (POutAsync n m), ...rest})
                  ~> (PPar {(eval cont m), ...rest}) ;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T) ;
    },
}
