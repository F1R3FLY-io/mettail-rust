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
//! ★ GOLDEN (unchanged by M-0, and by M-1b): **9 unresolvable ambiguities in 1
//! category**, all pre-existing and all in `Proc`:
//!
//! ```text
//!   1  [At,     Bang]        POutput        vs POutputEmpty
//!   2  [At,     Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   3  [Ident,  Bang]        POutput        vs POutputEmpty
//!   4  [Ident,  Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   5  [Integer]             CastUInt32     vs CastInt
//!   6  [LParen, Bang]        POutput        vs POutputEmpty
//!   7  [LParen, Tok_21_21]   PPersistOutput vs PPersistOutputEmpty
//!   8  [Minus]               CastBigRat     vs CastBigInt vs CastInt
//!   9  [StringLit]           CastStr        vs CastBytes
//! ```
//!
//! `implies` cannot add a row: `D02` reports conflicts at TRIE-DISPATCH prefixes,
//! and an infix operator declared `a "implies" b` contributes no leading
//! terminal — it is handled by the Pratt LED loop, not the decision trie. That is
//! a structural argument, and the byte-identical `D02` block before and after
//! M-0 is its confirmation.

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
fn a_chained_implies_elects_the_left_associative_reading() {
    // ⚠ Recorded, not merely observed. PraTTaIL derives associativity from the
    // binding-power pair it assigns in declaration order, and every same-category
    // infix rule declared this way is LEFT-associative
    // (`prattail/src/binding_power.rs::InfixOperator::associativity`,
    // `left_bp < right_bp`). Classical `⇒` is RIGHT-associative, so a chain reads
    // differently here than in the paper; the divergence is pinned so it is a
    // decision on the record rather than a surprise.
    //
    // `a implies b implies c`  ⇒  `(a implies b) implies c`.
    let elected = assert_parse_count("true implies false implies true", 1);
    match &elected {
        Proc::Implies(antecedent, consequent) => {
            assert!(
                matches!(antecedent.as_ref(), Proc::Implies(..)),
                "left-associative: the LEFT operand must be the nested implication, got {antecedent:?}"
            );
            assert!(
                matches!(consequent.as_ref(), Proc::CastBool(..)),
                "left-associative: the RIGHT operand must be the final atom, got {consequent:?}"
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
        let after_digits = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        rest = &rest[after_digits..];
    }
    out.push_str(rest);
    out
}
