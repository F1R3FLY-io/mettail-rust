//! **THE WIRE — the measurement and the differential.**
//!
//! Two gates plus the tally the campaign is scored on.
//!
//! ```text
//!  ┌──────────────────────────────────────────────────────────────────────────────────────┐
//!  │ GATE 1  THE TALLY                                                                    │
//!  │   for each of the 19 Rholang `where`-guard FORMS, does the guard reach Dovetail/SFT?  │
//!  │   Three axes are counted separately and all are printed, because they answer three    │
//!  │   different questions:                                                                │
//!  │     · SYMBOLIC  — the encoder produces a `GuardFormula` with NO opaque atom, so the   │
//!  │                   substrate's own procedures (Presburger / KAT / a scalar algebra)    │
//!  │                   decide it.                                                          │
//!  │     · DECIDED, own ground instance — ★ THE HONEST HEADLINE. The wire returns a        │
//!  │                   verdict on an instance OF THAT FORM, counting the DELEGATED          │
//!  │                   structural leg (Dovetail's structural core).                        │
//!  │     · DECIDED, all ground instances — the same, plus the rows whose ground instance   │
//!  │                   is a substitution RESIDUE rather than an instance of the form. See  │
//!  │                   `RESIDUE_GROUND_FORMS`: a bound variable is gone after substitution, │
//!  │                   so its "ground instance" is the payload's form, and crediting that  │
//!  │                   verdict to the bound-variable form would overstate the coverage.    │
//!  │   ★ The propositional content of the one residue row is measured directly instead, by │
//!  │     `every_propositional_atom_resolves_in_its_own_var_map`.                            │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ GATE 2  ★ THE DIFFERENTIAL                                                            │
//!  │   `eval_guard_disposition_via_substrate` must agree with `eval_guard_disposition` on   │
//!  │   EVERY corpus guard. This is what licenses swapping the three eager-COMM call sites   │
//!  │   from the Rust fold to the substrate: the swap is behaviour-preserving, proven row    │
//!  │   by row, not asserted.                                                                │
//!  └──────────────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # The 19 forms
//!
//! The enumeration is the Rholang grammar's, not an ad-hoc list: the **16 guard-expression
//! operator constructors** declared in `languages/src/rholang.rs` —
//! `Implies Or And Matches Eq Ne Gt Lt GtEq LtEq Add Sub Mul Div Mod Not` — plus the **3 atom
//! classes** a guard's leaves can be: a boolean literal, an integer literal, and a bound
//! variable.
//!
//! Each form is measured on two canonical instances:
//!
//! * an **open** instance (mentions a binder) for the SYMBOLIC axis — that is the compile-time
//!   question, *"can the substrate reason about this form at all?"*;
//! * a **ground** instance (fully substituted, as a guard is at COMM time) for the DECIDED
//!   axis — that is the run-time question, *"does the wire answer?"*.

#![cfg(feature = "rholang")]

use std::sync::Arc;

use mettail_languages::rholang::guard_substrate::{
    encode_guard, eval_guard_disposition_via_substrate,
};
use mettail_languages::rholang::receive::{eval_guard_disposition, GuardDisposition};
use mettail_languages::rholang::{Bag, Bool, Int, List, Proc, Str};
use mettail_runtime::{get_or_create_var, HashBag, OrdVar, Var};

// ════════════════════════════════════════════════════════════════════════════════════════════
// Builders
// ════════════════════════════════════════════════════════════════════════════════════════════

fn arc(p: Proc) -> Arc<Proc> {
    Arc::new(p)
}

fn int(n: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(n)))
}

fn boolean(b: bool) -> Proc {
    Proc::CastBool(Arc::new(Bool::BoolLit(b)))
}

fn text(s: &str) -> Proc {
    Proc::CastStr(Arc::new(Str::StringLit(s.to_string())))
}

fn var(name: &str) -> Proc {
    Proc::PVar(OrdVar(Var::Free(get_or_create_var(name))))
}

fn list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

fn bag(items: Vec<Proc>) -> Proc {
    Proc::CastBag(Arc::new(Bag::BagLit(items.into_iter().collect::<HashBag<Proc>>())))
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The 19 forms
// ════════════════════════════════════════════════════════════════════════════════════════════

/// One guard form, with an open instance (the compile-time question) and a ground instance
/// (the COMM-time question).
struct Form {
    name: &'static str,
    open: fn() -> Proc,
    ground: fn() -> Proc,
}

const FORMS: &[Form] = &[
    // ── The 3 atom classes ──────────────────────────────────────────────────────────────────
    Form {
        name: "atom: boolean literal",
        open: || boolean(true),
        ground: || boolean(true),
    },
    Form {
        name: "atom: integer literal",
        open: || Proc::Eq(arc(var("x")), arc(int(42))),
        ground: || Proc::Eq(arc(int(42)), arc(int(42))),
    },
    Form {
        name: "atom: bound variable",
        open: || var("b"),
        // ★ A bound variable is GONE after substitution, so this form has no ground instance of
        // its own: what a COMM faces where `where b` was written is the payload `b` was bound
        // to, and `true` is an instance of the BOOLEAN-LITERAL form. The row is therefore listed
        // in `RESIDUE_GROUND_FORMS` and the tally refuses to credit its verdict to this form.
        // The open instance is the one that carries this form's content, and it is measured by
        // `every_propositional_atom_resolves_in_its_own_var_map` below.
        ground: || boolean(true),
    },
    // ── The 4 connectives ───────────────────────────────────────────────────────────────────
    Form {
        name: "and",
        open: || Proc::And(arc(Proc::Lt(arc(var("x")), arc(int(9)))), arc(boolean(true))),
        ground: || Proc::And(arc(boolean(true)), arc(boolean(true))),
    },
    Form {
        name: "or",
        open: || Proc::Or(arc(Proc::Lt(arc(var("x")), arc(int(9)))), arc(boolean(false))),
        ground: || Proc::Or(arc(boolean(false)), arc(boolean(true))),
    },
    Form {
        name: "not",
        open: || Proc::Not(arc(Proc::Lt(arc(var("x")), arc(int(9))))),
        ground: || Proc::Not(arc(boolean(false))),
    },
    Form {
        name: "implies",
        open: || Proc::Implies(arc(Proc::Lt(arc(var("x")), arc(int(9)))), arc(boolean(true))),
        ground: || Proc::Implies(arc(boolean(true)), arc(boolean(true))),
    },
    // ── The 6 comparisons ───────────────────────────────────────────────────────────────────
    Form {
        name: "==",
        open: || Proc::Eq(arc(var("x")), arc(int(42))),
        ground: || Proc::Eq(arc(int(42)), arc(int(42))),
    },
    Form {
        name: "!=",
        open: || Proc::Ne(arc(var("x")), arc(int(42))),
        ground: || Proc::Ne(arc(int(42)), arc(int(41))),
    },
    Form {
        name: "<",
        open: || Proc::Lt(arc(var("x")), arc(int(46))),
        ground: || Proc::Lt(arc(int(42)), arc(int(46))),
    },
    Form {
        name: ">",
        open: || Proc::Gt(arc(var("x")), arc(int(1))),
        ground: || Proc::Gt(arc(int(42)), arc(int(1))),
    },
    Form {
        name: "<=",
        open: || Proc::LtEq(arc(var("x")), arc(int(46))),
        ground: || Proc::LtEq(arc(int(46)), arc(int(46))),
    },
    Form {
        name: ">=",
        open: || Proc::GtEq(arc(var("x")), arc(int(1))),
        ground: || Proc::GtEq(arc(int(1)), arc(int(1))),
    },
    // ── The spatial operator ────────────────────────────────────────────────────────────────
    Form {
        name: "matches",
        open: || Proc::Matches(arc(var("x")), arc(int(42))),
        ground: || Proc::Matches(arc(int(42)), arc(int(42))),
    },
    // ── The 5 arithmetic operators (in operand position) ────────────────────────────────────
    Form {
        name: "+",
        open: || Proc::Lt(arc(Proc::Add(arc(var("x")), arc(int(1)))), arc(int(10))),
        ground: || Proc::Lt(arc(Proc::Add(arc(int(2)), arc(int(1)))), arc(int(10))),
    },
    Form {
        name: "-",
        open: || Proc::Lt(arc(Proc::Sub(arc(var("x")), arc(int(1)))), arc(int(10))),
        ground: || Proc::Lt(arc(Proc::Sub(arc(int(4)), arc(int(1)))), arc(int(10))),
    },
    Form {
        name: "*",
        open: || Proc::Eq(arc(Proc::Mul(arc(int(2)), arc(var("x")))), arc(int(10))),
        ground: || Proc::Eq(arc(Proc::Mul(arc(int(2)), arc(int(5)))), arc(int(10))),
    },
    Form {
        name: "/",
        // `x / 2` is outside Presburger (division is not linear), so the OPEN instance is
        // honestly expected NOT to reach the substrate symbolically.
        open: || Proc::Eq(arc(Proc::Div(arc(var("x")), arc(int(2)))), arc(int(3))),
        ground: || Proc::Eq(arc(Proc::Div(arc(int(7)), arc(int(2)))), arc(int(3))),
    },
    Form {
        name: "%",
        open: || Proc::Eq(arc(Proc::Mod(arc(var("x")), arc(int(2)))), arc(int(1))),
        ground: || Proc::Eq(arc(Proc::Mod(arc(int(7)), arc(int(2)))), arc(int(1))),
    },
];

/// The count is a fact about the grammar, not about this file: 16 operator constructors + 3
/// atom classes.
const EXPECTED_FORM_COUNT: usize = 19;

/// ★ The forms whose GROUND instance is a substitution **residue** rather than an instance of
/// the form itself.
///
/// The DECIDED axis measures the ground instance, because that is what a COMM faces. For every
/// other form the ground instance still *contains* the form — `and` is measured on
/// `true and true`, `+` on `2 + 1 < 10`. A bound variable has no such instance: substitution
/// replaces it with its payload, so the guard the wire actually decides is the payload's form,
/// not this one.
///
/// Counting that verdict toward "the bound-variable form was decided" would attribute a decision
/// to a form the wire never saw. The tally therefore reports two numbers — the total over ground
/// instances, and the honest total over forms whose ground instance is their own — and
/// [`the_residue_rows_are_residues_because_the_form_itself_declines`] proves the residue is
/// necessary rather than convenient.
const RESIDUE_GROUND_FORMS: &[&str] = &["atom: bound variable"];

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 1 — the tally
// ════════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_form_enumeration_is_the_grammars_own() {
    assert_eq!(
        FORMS.len(),
        EXPECTED_FORM_COUNT,
        "the 19 forms are the 16 guard-expression operator constructors declared in \
         languages/src/rholang.rs (Implies Or And Matches Eq Ne Gt Lt GtEq LtEq Add Sub Mul Div \
         Mod Not) plus the 3 atom classes (boolean literal, integer literal, bound variable)"
    );
}

/// ★ THE TALLY. Prints one row per form so a drift is visible in the test log, not only in a diff.
#[test]
fn every_guard_form_reaches_dovetail_sft() {
    let mut symbolic = 0usize;
    let mut decided = 0usize;
    let mut decided_as_own_form = 0usize;
    let mut rows: Vec<String> = Vec::with_capacity(FORMS.len());

    for form in FORMS {
        let open = (form.open)();
        let ground = (form.ground)();

        let encoding = encode_guard(&open);
        let reaches_symbolically = encoding.reaches_substrate();
        let verdict = eval_guard_disposition_via_substrate(&ground);
        let is_decided = !matches!(verdict, GuardDisposition::Declines);
        // ★ Is the thing that was decided an instance of THIS form, or its substitution residue?
        let is_residue = RESIDUE_GROUND_FORMS.contains(&form.name);

        symbolic += usize::from(reaches_symbolically);
        decided += usize::from(is_decided);
        decided_as_own_form += usize::from(is_decided && !is_residue);

        rows.push(format!(
            "  {:<24} symbolic={:<5} decided={:<5} ground={:<8} verdict={:?}",
            form.name,
            reaches_symbolically,
            is_decided,
            match is_residue {
                true => "residue",
                false => "own",
            },
            verdict
        ));
    }

    let residues = RESIDUE_GROUND_FORMS.len();
    println!("\n★ THE WIRE — guard forms reaching Dovetail/SFT");
    for row in &rows {
        println!("{row}");
    }
    println!(
        "  ────────────────────────────────────────────────────────────────\n  \
         SYMBOLIC (substrate's own procedures decide it):                   {symbolic}/{total}\n  \
         DECIDED  (own ground instance — ★ THE HONEST HEADLINE):            {decided_as_own_form}/{total}\n  \
         DECIDED  (all ground instances, incl. {residues} substitution residue):  {decided}/{total}\n  \
         ─ the residue row(s): {RESIDUE_GROUND_FORMS:?} — substitution leaves no instance of the\n  \
         form behind, so the verdict belongs to the payload's form, not to this one.\n",
        total = FORMS.len()
    );

    // Every ground instance the wire is handed must be DECIDED. A `where` clause is a semantic
    // predicate, and the substrate (with its delegated structural leg) is what evaluates it.
    assert_eq!(
        decided,
        FORMS.len(),
        "every ground instance must be decided by the wire; {} of {} were not",
        FORMS.len() - decided,
        FORMS.len()
    );

    // ★ THE HONEST HEADLINE. `decided` above counts one row whose ground instance is not an
    // instance of its form at all, so it overstates by exactly the residue count. The number the
    // campaign may quote for "guard forms the wire decides" is this one.
    assert_eq!(
        decided_as_own_form,
        FORMS.len() - residues,
        "{} of {} forms are decided on a ground instance of their own; the other {} are \
         substitution residues ({:?}) and may not be counted as the form's own decision",
        decided_as_own_form,
        FORMS.len(),
        residues,
        RESIDUE_GROUND_FORMS
    );

    // The SYMBOLIC axis is honestly lower: `matches` is a structural question routed to the
    // structural core, and `/` and `%` over a VARIABLE are outside Presburger by definition
    // (linear arithmetic has no division). Those three are the only shortfall, and they are
    // theory facts rather than wiring gaps.
    assert_eq!(
        symbolic,
        FORMS.len() - 3,
        "exactly three forms are expected to be outside the substrate's SYMBOLIC fragment \
         (`matches` -> the structural core; `/` and `%` over a variable -> not linear arithmetic)"
    );
}

/// The three symbolic shortfalls are the ones named, not some other three.
#[test]
fn the_symbolic_shortfall_is_exactly_matches_div_and_mod() {
    let shortfall: Vec<&str> = FORMS
        .iter()
        .filter(|form| !encode_guard(&(form.open)()).reaches_substrate())
        .map(|form| form.name)
        .collect();
    assert_eq!(shortfall, vec!["matches", "/", "%"]);
}

/// ★ **THE ASSERTION THAT WOULD HAVE CAUGHT THE KEYSPACE DEFECT** — every propositional atom
/// this encoder emits must resolve in the very var map it ships alongside.
///
/// `GuardFormula::Prop`'s documentation fixes the keyspace in as many words: `BooleanTest::Atom`
/// names are *binder names*, not indices, because `GuardAssignment::truth_assignment` resolves
/// each required atom through `GuardVarMap::index_of` — a `BTreeMap<String, usize>` keyed by the
/// name that was interned. An atom written into the *index* keyspace (`"0"`) and read out of the
/// *name* keyspace (`"b$1"`) makes `index_of` return `None`, `?` short-circuit, and the whole
/// ground leg answer `DontKnow` — for a reason that has nothing to do with the payload.
///
/// Nothing else in this file catches that. `reaches_substrate()` returns `true` for
/// `GuardFormula::Prop(_)` unconditionally, and the DECIDED axis measures the ground instance,
/// which for the only propositional form is a substitution residue carrying no atom at all.
#[test]
fn every_propositional_atom_resolves_in_its_own_var_map() {
    let mut atoms_checked = 0usize;

    for form in FORMS {
        let encoding = encode_guard(&(form.open)());
        for name in encoding.formula.prop_names() {
            atoms_checked += 1;
            assert!(
                encoding.vars.index_of(&name).is_some(),
                "form {:?}: the propositional atom {:?} does not resolve in the encoding's own \
                 var map (which holds {:?}). `truth_assignment` looks atoms up by BINDER NAME, \
                 so an unresolvable atom is undecidable at the ground leg for every payload.",
                form.name,
                name,
                encoding.vars.names()
            );
        }
    }

    // The sweep above is only evidence if it swept something.
    assert!(
        atoms_checked > 0,
        "no form emitted a propositional atom — this gate would then prove nothing; the \
         bound-variable form must encode as GuardFormula::Prop"
    );
}

/// The residue rows in [`RESIDUE_GROUND_FORMS`] are residues out of necessity, not convenience:
/// the form's OWN instance is honestly undecidable at COMM time, which is precisely why the row
/// has to be measured on what substitution leaves behind.
#[test]
fn the_residue_rows_are_residues_because_the_form_itself_declines() {
    for form in FORMS
        .iter()
        .filter(|form| RESIDUE_GROUND_FORMS.contains(&form.name))
    {
        let open = (form.open)();
        assert_eq!(
            eval_guard_disposition_via_substrate(&open),
            GuardDisposition::Declines,
            "form {:?} is listed as having a residue ground instance, which is only honest if \
             its own instance cannot be decided — an unsubstituted binder has no value, so the \
             substrate must decline it (fail-closed) rather than answer",
            form.name
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 2 — the differential that licenses the call-site swap
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The corpus the three eager-COMM sites actually face: guards after the arrived payload has
/// been substituted in, plus the residual shapes that survive substitution.
fn differential_corpus() -> Vec<(&'static str, Proc)> {
    let mut corpus: Vec<(&'static str, Proc)> = Vec::with_capacity(48);

    corpus.push(("true", boolean(true)));
    corpus.push(("false", boolean(false)));

    // Integer comparisons, both verdicts, every operator.
    for (name, build) in [
        ("==", Proc::Eq as fn(Arc<Proc>, Arc<Proc>) -> Proc),
        ("!=", Proc::Ne),
        ("<", Proc::Lt),
        (">", Proc::Gt),
        ("<=", Proc::LtEq),
        (">=", Proc::GtEq),
    ] {
        corpus.push((name, build(arc(int(42)), arc(int(42)))));
        corpus.push((name, build(arc(int(1)), arc(int(2)))));
        corpus.push((name, build(arc(int(2)), arc(int(1)))));
    }

    // Boolean structural equality — divergence H's second half.
    corpus.push(("bool ==", Proc::Eq(arc(boolean(true)), arc(boolean(true)))));
    corpus.push(("bool ==", Proc::Eq(arc(boolean(true)), arc(boolean(false)))));
    corpus.push(("bool <", Proc::Lt(arc(boolean(false)), arc(boolean(true)))));

    // String comparisons.
    corpus.push(("str ==", Proc::Eq(arc(text("hi")), arc(text("hi")))));
    corpus.push(("str ==", Proc::Eq(arc(text("hi")), arc(text("bye")))));
    corpus.push(("str !=", Proc::Ne(arc(text("hi")), arc(text("bye")))));
    corpus.push(("str <", Proc::Lt(arc(text("bye")), arc(text("hi")))));

    // Connectives over decided and undecided operands.
    let undecided = || Proc::Eq(arc(var("x")), arc(int(0)));
    corpus.push(("and TT", Proc::And(arc(boolean(true)), arc(boolean(true)))));
    corpus.push(("and TF", Proc::And(arc(boolean(true)), arc(boolean(false)))));
    corpus.push(("and FT", Proc::And(arc(boolean(false)), arc(boolean(true)))));
    corpus.push(("and F?", Proc::And(arc(boolean(false)), arc(undecided()))));
    corpus.push(("and ?T", Proc::And(arc(undecided()), arc(boolean(true)))));
    corpus.push(("or TT", Proc::Or(arc(boolean(true)), arc(boolean(true)))));
    corpus.push(("or FF", Proc::Or(arc(boolean(false)), arc(boolean(false)))));
    corpus.push(("or T?", Proc::Or(arc(boolean(true)), arc(undecided()))));
    // ★ THE ROW THAT CAUGHT THE REAL BUG. `? or true` must DECLINE, not fire: the left-strict
    // discipline propagates the undecided left operand, and the classical absorption
    // `phi or true = true` would fire a COMM that neither the fold nor the reducer fires.
    corpus.push(("or ?T", Proc::Or(arc(undecided()), arc(boolean(true)))));
    corpus.push(("or ?F", Proc::Or(arc(undecided()), arc(boolean(false)))));
    // The `and` twin: `? and false` must DECLINE, not block.
    corpus.push(("and ?F", Proc::And(arc(undecided()), arc(boolean(false)))));
    corpus.push(("implies ?F", Proc::Implies(arc(undecided()), arc(boolean(false)))));
    corpus.push(("not T", Proc::Not(arc(boolean(true)))));
    corpus.push(("not F", Proc::Not(arc(boolean(false)))));
    corpus.push(("not ?", Proc::Not(arc(undecided()))));
    corpus.push(("implies FT", Proc::Implies(arc(boolean(false)), arc(boolean(true)))));
    corpus.push(("implies F?", Proc::Implies(arc(boolean(false)), arc(undecided()))));
    corpus.push(("implies TT", Proc::Implies(arc(boolean(true)), arc(boolean(true)))));
    corpus.push(("implies TF", Proc::Implies(arc(boolean(true)), arc(boolean(false)))));
    corpus.push(("implies ?T", Proc::Implies(arc(undecided()), arc(boolean(true)))));

    // Spatial — the delegated structural leg.
    corpus.push(("matches lit", Proc::Matches(arc(int(42)), arc(int(42)))));
    corpus.push(("matches miss", Proc::Matches(arc(int(42)), arc(int(41)))));
    corpus.push(("matches true", Proc::Matches(arc(int(42)), arc(boolean(true)))));
    corpus.push(("matches false", Proc::Matches(arc(int(42)), arc(boolean(false)))));

    // Structured equality — the delegated collection comparator.
    corpus.push((
        "list ==",
        Proc::Eq(arc(list(vec![int(1), int(2)])), arc(list(vec![int(1), int(2)]))),
    ));
    corpus.push(("list !=", Proc::Ne(arc(list(vec![int(1), int(2)])), arc(list(vec![int(1)])))));
    corpus.push((
        "bag ==",
        Proc::Eq(arc(bag(vec![int(1), int(2)])), arc(bag(vec![int(2), int(1)]))),
    ));

    // Shapes both deciders must decline.
    corpus.push(("process-shaped", Proc::PZero));
    corpus.push(("unsubstituted binder", undecided()));
    corpus.push((
        "nonlinear",
        Proc::Lt(arc(Proc::Mul(arc(var("x")), arc(var("y")))), arc(int(10))),
    ));

    corpus
}

/// ★ THE DIFFERENTIAL. The substrate-derived decider and the Rust fold must agree on every
/// corpus guard — which is what makes swapping the three eager-COMM call sites a
/// behaviour-preserving change rather than a semantics change.
#[test]
fn the_substrate_decider_agrees_with_the_rust_fold_on_the_whole_corpus() {
    let corpus = differential_corpus();
    let mut disagreements: Vec<String> = Vec::new();

    for (name, guard) in &corpus {
        let fold = eval_guard_disposition(guard);
        let substrate = eval_guard_disposition_via_substrate(guard);
        if fold != substrate {
            disagreements
                .push(format!("  {name:<22} fold={fold:?} substrate={substrate:?}  guard={guard}"));
        }
    }

    assert!(
        disagreements.is_empty(),
        "the substrate decider and the Rust fold disagree on {} of {} corpus guards:\n{}",
        disagreements.len(),
        corpus.len(),
        disagreements.join("\n")
    );
    println!(
        "\n★ DIFFERENTIAL: {} corpus guards, 0 disagreements between the Rust fold and the \
         substrate-derived decider.\n",
        corpus.len()
    );
}

/// The corpus is not trivially small, and it exercises all three dispositions — otherwise the
/// differential above could pass vacuously.
#[test]
fn the_differential_corpus_exercises_all_three_dispositions() {
    let corpus = differential_corpus();
    assert!(corpus.len() >= 40, "corpus too small to be evidence: {}", corpus.len());
    for expected in [GuardDisposition::Fires, GuardDisposition::Blocks, GuardDisposition::Declines]
    {
        assert!(
            corpus
                .iter()
                .any(|(_, g)| eval_guard_disposition_via_substrate(g) == expected),
            "the corpus must contain at least one {expected:?} row"
        );
    }
}
