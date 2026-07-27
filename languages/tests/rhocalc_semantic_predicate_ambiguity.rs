//! Ambiguity goldens for the RhoCalc **semantic-predicate** surface.
//!
//! Every new production added to `rhocalc.rs` widens the grammar, and this
//! grammar has already demonstrated that a widening can be catastrophic rather
//! than incremental: the F3 `&`-join projection-vs-extension defect turned a
//! ~14 ms parse into a ~109 s one (a multiplicative `2^N` cursor-frontier
//! explosion, see `rhocalc_tests.rs`'s F3 pins). So each semantic-predicate form
//! is fenced here on **three** independent axes:
//!
//! | Axis | What it catches | How |
//! | --- | --- | --- |
//! | **Parse count** | a NEW ambiguity — the form now has ≥ 2 derivations | `Proc::parse_via_wpda_all(src).len()` vs an exact golden |
//! | **Elected shape** | a SILENT re-election — same count, different winner | the elected best-parse's constructor is asserted |
//! | **Parse time** | a frontier EXPLOSION — same count, exponential work | a hard wall-clock bound on a worker thread |
//!
//! ## Why an exact count and not "≤ N"
//!
//! `parse_via_wpda_all` is the ambiguity-PRESERVING entry: it returns the whole
//! forest, not the disambiguated representative. An upper bound would silently
//! accept an ambiguity that merely happens to be resolved today by tropical
//! weights; an exact golden forces the question to be re-answered whenever the
//! number changes. Every golden below was HARVESTED by running the code, never
//! invented — re-derive with
//! `cargo nextest run -p languages --test rhocalc_semantic_predicate_ambiguity`.
//!
//! ## The D02 companion fence (a build-time lint, recorded here)
//!
//! Parse counts fence the RUNTIME forest; the decision-tree lint `D02`
//! (`unresolvable-ambiguity`, `prattail/src/decision_tree/reports.rs`) fences the
//! COMPILE-TIME trie. `D02` is emitted to stderr during macro expansion, so it
//! cannot be asserted from a test; it is recorded here as a golden with its
//! re-derivation recipe:
//!
//! ```text
//!   touch languages/src/rhocalc.rs && cargo build -p languages --all-features 2>&1 \
//!     | awk '/warning\[D02\] \(RhoCalc\)/,/= hint: this is an inherent/'
//! ```
//!
//! ★ GOLDEN — **verified before M-0, after M-0, after M-1b, and after divergence I**:
//! **9 unresolvable ambiguities in 1 category**, all pre-existing and all in
//! `Proc`:
//!
//! ```text
//!   1  [At,     Bang]        POutput        vs POutputEmpty
//!   2  [At,     Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   3  [Ident,  Bang]        POutput        vs POutputEmpty
//!   4  [Ident,  Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   5  [Integer]             CastInt        vs CastUInt32
//!   6  [LParen, Bang]        POutput        vs POutputEmpty
//!   7  [LParen, Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   8  [Minus]               CastBigRat     vs CastInt vs CastBigInt
//!   9  [StringLit]           CastStr        vs CastBytes
//! ```
//!
//! ### The divergence-I delta, and why it is not a regression
//!
//! Divergence I (`12704fc1`) REORDERED the integer projections so the DIRECT
//! reading `Int ▸ Proc` is elected over the promote-then-project chain:
//!
//! ```text
//!   before (54531931)  CastBigRat  CastBigInt  CastUInt32  CastInt   CastStr CastBytes
//!   after  (HEAD)      CastBigRat  CastInt     CastBigInt  CastUInt32  CastStr CastBytes
//! ```
//!
//! `D02` enumerates a row's alternatives in DECLARATION ORDER, so rows 5 and 8 —
//! the only two rows whose alternatives are integer projections — re-order with
//! it, and nothing else moves. The measurement that matters is invariant:
//!
//! | quantity | before | after |
//! |---|---|---|
//! | unresolvable ambiguities | 9 | 9 |
//! | categories | 1 (`Proc`) | 1 (`Proc`) |
//! | conflict PREFIXES | `[At,Bang] [At,Tok_21_21] [Ident,Bang] [Ident,Tok_21_21] [Integer] [LParen,Bang] [LParen,Tok_21_21] [Minus] [StringLit]` | identical |
//! | constructor SET per prefix | — | identical at all 9 |
//!
//! So divergence I introduced no new grammar conflict and resolved none: it
//! permuted the alternatives WITHIN two existing conflicts, which is precisely
//! the intentional election change and is invisible to the conflict structure.
//! Compare SETS per prefix, not the printed sequence, when re-deriving this
//! golden — the sequence is a declaration-order artifact.
//!
//! `implies` and `matches` cannot add a row: `D02` reports conflicts at
//! TRIE-DISPATCH prefixes, and an infix operator declared `a "op" b` contributes
//! no leading terminal — it is handled by the Pratt LED loop, not the decision
//! trie. `PPar` DOES contribute a leading terminal, but as a RESERVED word
//! (`options { reserved_keywords: auto }`), so its `Ident` co-accept is dropped
//! and it cannot fork against the lowercase call-forms. Those are structural
//! arguments; the byte-identical `D02` block measured before M-0, after M-0 and
//! after M-1b is their confirmation.

use std::time::{Duration, Instant};

use mettail_languages::rhocalc::Proc;

/// The blow-up tripwire. Measured parses of these forms complete in ~5-15 ms; the
/// bound is set two orders of magnitude above that so it can only fire on a
/// genuine explosion (the F3 incident went to ~109 s), never on machine noise or
/// a cold static-initializer.
const PARSE_BUDGET: Duration = Duration::from_secs(2);

/// Hard wall-clock fence: run `body` on a worker thread and fail loudly if it has
/// not finished in time. A budget overrun that HANGS must fail as a test failure,
/// not as a stalled suite — the F3 lesson.
fn within_budget<T: Send + 'static>(label: &str, body: impl FnOnce() -> T + Send + 'static) -> T {
    use std::sync::mpsc;
    let (tx, rx) = mpsc::channel();
    let handle = std::thread::Builder::new()
        .name("semantic-predicate-ambiguity".into())
        .spawn(move || {
            let _ = tx.send(body());
        })
        .expect("spawn the ambiguity-golden worker thread");
    match rx.recv_timeout(PARSE_BUDGET) {
        Ok(value) => {
            let _ = handle.join();
            value
        },
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "parsing {label:?} exceeded the {PARSE_BUDGET:?} budget — a parse-frontier \
             explosion of the F3 (14 ms → 109 s) class"
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => match handle.join() {
            Ok(()) => panic!("{label:?}: the worker thread disconnected without a result"),
            Err(panic_payload) => std::panic::resume_unwind(panic_payload),
        },
    }
}

/// Parse `source` with the ambiguity-PRESERVING entry and assert the forest has
/// exactly `expected_alternatives` members, within the budget. Returns the
/// elected best-parse so callers can additionally pin the WINNER.
fn assert_parse_count(source: &'static str, expected_alternatives: usize) -> Proc {
    let (alternatives, elapsed, elected) = within_budget(source, move || {
        mettail_runtime::clear_var_cache();
        let started = Instant::now();
        let all = Proc::parse_via_wpda_all(source)
            .unwrap_or_else(|err| panic!("{source:?} must parse: {err:?}"));
        let elapsed = started.elapsed();
        mettail_runtime::clear_var_cache();
        let elected = Proc::parse_via_wpda(source)
            .unwrap_or_else(|err| panic!("{source:?} must have an elected best-parse: {err:?}"));
        (all.len(), elapsed, elected)
    });
    assert_eq!(
        alternatives, expected_alternatives,
        "parse-forest size for {source:?} changed: golden {expected_alternatives}, \
         observed {alternatives} (elapsed {elapsed:?})"
    );
    assert!(
        elapsed < PARSE_BUDGET,
        "parsing {source:?} took {elapsed:?}, over the {PARSE_BUDGET:?} budget"
    );
    elected
}

// ══════════════════════════════════════════════════════════════════════════════
// M-0 — `implies`
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn implies_forms_are_unambiguous() {
    // Each of these has exactly ONE derivation. The `1` is the strongest golden
    // available: it says the new connective introduces no fork at all.
    for source in [
        "true implies false",
        "1 > 0 implies 2 > 1",
        "true implies false implies true",
        "false or false implies false and false",
        "not true implies false",
        r#"@"OUT"!(true implies false)"#,
        r#"for(@x <- @"c" where x > 0 implies x > 10) { @"OUT"!(x) }"#,
    ] {
        assert_parse_count(source, 1);
    }
}

#[test]
fn the_pre_existing_propositional_forms_keep_their_parse_counts() {
    // The control arm: adding `implies` must not perturb the forms that were
    // already there. Same goldens as the `implies` rows — all 1 — so a widening
    // that forked `or`/`and`/`not` would show up here even if `implies` itself
    // stayed clean.
    for source in [
        "true or false",
        "true and false",
        "not true",
        r#"for(@x <- @"c" where x > 0) { @"OUT"!(x) }"#,
        r#"for(@x <- @"c" where x > 0 or x > 10) { @"OUT"!(x) }"#,
        r#"for(@x <- @"c" where x > 0 and x > 10) { @"OUT"!(x) }"#,
        "{ P | Q }",
    ] {
        assert_parse_count(source, 1);
    }
}

#[test]
fn the_elected_implies_parse_has_the_declared_precedence() {
    // Same count, different winner is a SILENT regression that a count golden
    // alone cannot see, so the elected shape is pinned structurally.
    //
    // `false or false implies false and false` must elect
    // `Implies(Or(_,_), And(_,_))` — `implies` at the ROOT, because it is the
    // loosest — and NOT `Or(_, And(Implies(_,_), _))`.
    let elected = assert_parse_count("false or false implies false and false", 1);
    let (antecedent, consequent) = match &elected {
        Proc::Implies(antecedent, consequent) => (antecedent.as_ref(), consequent.as_ref()),
        other => panic!("`implies` must be the ROOT of the elected parse, got {other:?}"),
    };
    assert!(
        matches!(antecedent, Proc::Or(..)),
        "the antecedent must be the whole `false or false`, got {antecedent:?}"
    );
    assert!(
        matches!(consequent, Proc::And(..)),
        "the consequent must be the whole `false and false`, got {consequent:?}"
    );
}

#[test]
fn a_chained_implies_elects_the_right_associative_reading() {
    // `implies` is declared `right`, so a chain reads `a implies (b implies c)` —
    // classical material implication, and the reading the Heyting `⇒` of
    // `prattail::algebra_tower::HeytingAlgebra::implies` has.
    //
    // This row previously pinned the LEFT-associative reading, which the rule
    // inherited by omitting the annotation. That was recorded as a divergence from
    // the paper rather than fixed, on the reasoning that an author could
    // parenthesize. The two readings are not notational variants — they disagree on
    // the VALUE. `false implies false implies false` is `true` read right and
    // `false` read left (`(false ⇒ false) ⇒ false` = `true ⇒ false` = `false`). So
    // the old shape let a three-term chain evaluate to the opposite truth value
    // from the one its author wrote, with no diagnostic. `right` costs one keyword.
    //
    // `a implies b implies c`  ⇒  `a implies (b implies c)`.
    //
    // This row pins the SHAPE only. The parse layer has no evaluator — `normalize()`
    // is the host PDA normalizer and does not run a `fold`, which is a machine
    // rewrite. The companion TRUTH-VALUE pin, on the reading where the two
    // associativities actually disagree, lives with the evaluator:
    // `rholang-runtime/tests/rho_implies_guard.rs::a_right_associative_chain_is_true`.
    let elected = assert_parse_count("true implies false implies true", 1);
    match &elected {
        Proc::Implies(antecedent, consequent) => {
            assert!(
                matches!(antecedent.as_ref(), Proc::CastBool(..)),
                "right-associative: the LEFT operand must be the leading atom, got {antecedent:?}"
            );
            assert!(
                matches!(consequent.as_ref(), Proc::Implies(..)),
                "right-associative: the RIGHT operand must be the nested implication, got {consequent:?}"
            );
        },
        other => panic!("a chained `implies` must elect an `Implies` root, got {other:?}"),
    }
}

#[test]
fn implies_parses_deterministically_across_repeated_parses() {
    // Determinism of the ELECTION, not just of the count: a weight tie broken by
    // iteration order would show up as two different winners for one source.
    for source in ["true implies false", "false or false implies false and false"] {
        let first = assert_parse_count(source, 1);
        let second = assert_parse_count(source, 1);
        assert_eq!(
            normalize_var_ids(&format!("{first:?}")),
            normalize_var_ids(&format!("{second:?}")),
            "repeated parses of {source:?} must elect the same AST"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// M-1b — `matches` and `PPar`
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn matches_forms_are_unambiguous() {
    // `matches` is an infix operator, so like `implies` it contributes no
    // trie-dispatch prefix. Every form has exactly ONE derivation.
    for source in [
        "x matches true",
        "x matches false",
        r#"x matches @"a"!(1)"#,
        r#"x matches { @"a"!(1) | true }"#,
        r#"x matches (not @"a"!(1))"#,
        r#"x matches (@"a"!(1) and true)"#,
        r#"x matches (@"a"!(1) implies true)"#,
        "x matches true and y matches false",
        r#"not (x matches @"a"!(1))"#,
        r#"for(@x <- @"c" where x matches { @"a"!(1) | true }) { @"OUT"!(x) }"#,
    ] {
        assert_parse_count(source, 1);
    }
}

#[test]
fn ppar_forms_are_unambiguous() {
    // ★ `PPar` is the interesting case for ambiguity: unlike `implies`/`matches`
    // it is a LEADING LITERAL, so it does enter the decision trie. It cannot fork
    // against the lowercase call-forms (`int(…)`, `bool(…)`, a method call)
    // because RhoCalc runs `options { reserved_keywords: auto }`, which reserves
    // every identifier-shaped literal terminal — so `PPar` is a keyword and can
    // no longer co-accept as an `Ident`. These goldens are the executable check on
    // that reasoning.
    for source in [
        "PPar(true, true)",
        "t matches PPar(true, true)",
        r#"t matches PPar(@"a"!(1), true)"#,
        r#"t matches PPar(@"a"!(1), @"b"!(2))"#,
        "t matches PPar(PPar(true, true), true)",
        r#"for(@x <- @"c" where x matches PPar(true, true)) { @"OUT"!(x) }"#,
    ] {
        assert_parse_count(source, 1);
    }
}

#[test]
fn the_pre_existing_call_forms_keep_their_parse_counts_after_ppar_is_reserved() {
    // The control arm for the reservation. `PPar` joining the keyword set must not
    // perturb the parenthesized call-forms it sits next to in the trie, nor the
    // ordinary identifier and method surfaces.
    for source in [
        "int(3, 8)",
        "uint(3, 8)",
        "bool(true)",
        "str(1)",
        "float(1, 32)",
        "PPar",
        "PParX",
        "xPPar",
    ] {
        // `PPar` alone is now a bare keyword in operand position and no longer
        // parses as a variable; the two neighbouring identifiers still do. Both
        // outcomes are pinned by the parse-count contract below rather than
        // asserted informally.
        match mettail_runtime::clear_var_cache() {
            () => {},
        }
        let parsed = Proc::parse_via_wpda_all(source);
        match source {
            "PPar" => assert!(
                parsed.is_err() || parsed.as_ref().map(Vec::len).unwrap_or(0) == 0,
                "the reserved keyword `PPar` must not parse as a bare variable, got {parsed:?}"
            ),
            _ => {
                let alternatives = parsed
                    .unwrap_or_else(|err| panic!("{source:?} must still parse: {err:?}"))
                    .len();
                assert_eq!(alternatives, 1, "parse-forest size for {source:?} changed");
            },
        }
    }
}

#[test]
fn the_elected_matches_parse_has_the_declared_precedence() {
    // `matches` sits at the loose edge of the comparison block — TIGHTER than
    // `and`/`or`/`implies`, which is the reading the paper's multi-subject guards
    // need and the same relative order official Rholang gives
    // (`rholang-tree-sitter/grammar.js`: `matches` prec 6 > `and` 5 > `or` 4).
    let elected = assert_parse_count("x matches true and y matches false", 1);
    match &elected {
        Proc::And(left, right) => {
            assert!(
                matches!(left.as_ref(), Proc::Matches(..)),
                "the left conjunct must be a whole `matches`, got {left:?}"
            );
            assert!(
                matches!(right.as_ref(), Proc::Matches(..)),
                "the right conjunct must be a whole `matches`, got {right:?}"
            );
        },
        other => panic!("`and` must be the ROOT of the elected parse, got {other:?}"),
    }

    // And looser than `implies`, so an implication of two matches groups the way
    // a reader expects.
    let elected = assert_parse_count("x matches true implies y matches false", 1);
    assert!(
        matches!(&elected, Proc::Implies(..)),
        "`implies` must be looser than `matches`, got {elected:?}"
    );
}

#[test]
fn ppar_and_the_braced_spelling_elect_their_own_constructors() {
    // Same parse count, different constructor is a SILENT regression a count
    // golden cannot see: `PPar(φ,ψ)` must elect `SpatialPPar` (the connective) and
    // `{ φ | ψ }` must elect `PPar` (the multiset literal). They compile to the
    // same pattern, but they are not the same node, and conflating them at parse
    // time would make `PPar(a, b)` silently lowerable in term position.
    let elected = assert_parse_count("PPar(true, true)", 1);
    assert!(
        matches!(&elected, Proc::SpatialPPar(..)),
        "`PPar(φ,ψ)` must elect the spatial connective, got {elected:?}"
    );

    let elected = assert_parse_count(r#"{ @"a"!(1) | true }"#, 1);
    assert!(
        matches!(&elected, Proc::PPar(_)),
        "`{{ φ | ψ }}` must elect the multiset literal, got {elected:?}"
    );
}

#[test]
fn matches_and_ppar_parse_deterministically_across_repeated_parses() {
    for source in [
        r#"x matches { @"a"!(1) | true }"#,
        "t matches PPar(true, true)",
        "x matches true and y matches false",
    ] {
        let first = assert_parse_count(source, 1);
        let second = assert_parse_count(source, 1);
        assert_eq!(
            normalize_var_ids(&format!("{first:?}")),
            normalize_var_ids(&format!("{second:?}")),
            "repeated parses of {source:?} must elect the same AST"
        );
    }
}

/// Canonicalize the monotonic fresh-variable ids in a derived-`Debug` rendering
/// so two parses of the same source are structurally comparable.
/// `clear_var_cache()` resets the name→id MAP but not the process-global
/// monotonic id COUNTER, so successive parses embed `UniqueId(0)` vs
/// `UniqueId(101)` for the same variable. Replacing every `UniqueId(<digits>)`
/// with `UniqueId(_)` isolates GENUINE parser non-determinism (structure) from
/// benign id allocation.
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
