//! **#128 — RHOLANG'S RESERVED SET, DERIVED ON BOTH SIDES AND DIFFED IN BOTH DIRECTIONS.**
//!
//! # The two defects, and why they are not one defect
//!
//! A word is *reserved* when the parser refuses it as an identifier. MeTTaIL's reserved set
//! is grammar-derived (`prattail::ReservationPolicy::reserved_kinds`: every terminal that is
//! lexically an identifier, minus the `contextual` opt-outs), and Rholang ships at
//! `options { reserved_keywords: auto }`. Upstream's is *declared*, in the normative
//! tree-sitter grammar. The two need not agree, and they do not.
//!
//! | direction | what it means | consequence |
//! |---|---|---|
//! | **over**-reserved — reserved here, free upstream | an upstream program using the word as an identifier parses upstream and is **rejected here** | a **superset breach**: MeTTaIL must accept everything upstream accepts |
//! | **under**-reserved — free here, reserved upstream | a program using the word as an identifier is **rejected upstream and accepted here** | not a breach of the superset standard, but it means MeTTaIL is *differently shaped*, not a superset ⇒ a portability hazard |
//!
//! The governing ruling is that **upstream is a floor on *semantics*, not a ceiling on
//! *diagnostics***: a program upstream accepts must be accepted here and compute the same
//! value; how a *failure* is reported is free. Over-reservation therefore matters and
//! under-reservation is classified separately, per word.
//!
//! # ★ The normative source, quoted verbatim
//!
//! `/home/dylon/Workspace/f1r3fly.io/rholang-rs/rholang-tree-sitter/grammar.js:21-49`
//!
//! ```js
//! reserved: {
//!     global: $ => [
//!         "new", "if", "else", "let", "match", "select", "contract", "for",
//!         "or", "and", "matches", "not", "bundle", "true", "false", "where"
//!         // NOTE: `agent`, `constructor`, `method`, `default`, and
//!         // `private` are NOT reserved globally. Tree-sitter's GLR
//!         // parser disambiguates these by context: … This preserves
//!         // backward compatibility with existing Rholang code …
//!     ],
//! },
//! ```
//!
//! ## ⚠ That is SIXTEEN words, and the filing said seventeen
//!
//! #128 recorded the oracle as *"exactly 17 words"* and listed `in` among them. `in` is
//! **not** in the `reserved.global` array at the oracle's HEAD — the array holds 16 words.
//! `in` appears in the grammar only as a positional terminal of the `new` production
//! (`new: prec(1, seq('new', $.name_decls, 'in', $._proc))`), which reserves nothing.
//! The count below is derived, not inherited, and it is 16.
//!
//! ### Reproducing the oracle count
//!
//! ```sh
//! cd /home/dylon/Workspace/f1r3fly.io/rholang-rs && python3 -c '
//! import re,sys
//! s=open("rholang-tree-sitter/grammar.js").read()
//! b=re.search(r"reserved:\s*\{\s*global:\s*\$\s*=>\s*\[(.*?)\]\s*,?\s*\}",s,re.S).group(1)
//! w=re.findall(r"\"([^\"]+)\"", re.sub(r"//.*","",b))
//! print(len(w), sorted(w))'
//! ```
//!
//! [`ORACLE_RESERVED`] is that measurement, dated below. It is a transcription **because the
//! oracle lives in another repository** and a workspace test cannot depend on a foreign
//! checkout; [`oracle_list_has_not_drifted`] closes the loop by re-deriving it from
//! `grammar.js` whenever that path is readable, and reports its own vacuity when it is not.
//!
//! # Why the MeTTaIL side is derived and probed rather than listed
//!
//! #122 was first reported as 2 divergent words when the true count was 44, because it was
//! sampled. So the domain here is **computed**: every identifier-shaped literal terminal in
//! the reconstructed `LanguageDef`, plus the identifier-shaped collection openers, unioned
//! with the oracle's own words so that a word MeTTaIL does not declare at all (`bundle`) is
//! still probed. Each word in that domain is then measured *behaviourally*, with the probe
//! #128 asks for — `new <word> in { Nil }` — so the verdict is the parser's, not a struct's.
//!
//! # ★★ THE MEASUREMENT — 2026-07-30, and the filing was off in both directions
//!
//! | quantity | filing | **derived** |
//! |---|---|---|
//! | oracle's reserved words | 17 (incl. `in`) | **16** — `in` is not in `reserved.global` |
//! | comparison domain | — | **85** |
//! | reserved by MeTTaIL over that domain | — | **78** |
//! | over-reserved (reserved here, free upstream) | 5 | **69** |
//! |   ⤷ dotted-method family, #122/#123's lane | 44 | **47** (derived, not listed) |
//! |   ⤷ residue, this item's own | 5 | **22** |
//! | under-reserved (free here, reserved upstream) | 1 (`bundle`) | **7** |
//!
//! ## Three premise inversions, each worth stating
//!
//! 1. **`in` is not an oracle keyword.** The filing counted it among the oracle's 17 and
//!    therefore recorded `in` as *conformant*. It is not reserved upstream and it **is**
//!    reserved here, so it is an over-reservation the miscount concealed.
//! 2. **The under-reserved direction is a MISSING-CONSTRUCT report, not a reservation one.**
//!    All seven words are declared as no terminal at all — MeTTaIL's Rholang has no `if`,
//!    `else`, `match`, `let`, `select`, `contract` or `bundle`. Reserving them would make
//!    MeTTaIL strictly worse. See
//!    [`under_reservation_is_a_missing_construct_not_a_missing_reservation`].
//! 3. **The dotted-method family is 47, not 44** — the same re-derivation
//!    `wpda_codegen/factoring.rs`'s `Proc` method-cohort census made on 2026-07-29 (44 → 47).
//!    It is *computed* here, so it cannot drift again.
//!
//! # What this file does NOT do
//!
//! It does not un-reserve anything. Every residue row is a superset breach and each un-
//! reservation changes the accepted language, so the repair is a per-word ruling; the
//! dotted-method family is #123's fix and lands there. This file makes the divergence a
//! MEASURED, DRIFT-DETECTING artifact instead of a sampled anecdote, and it goes red the
//! moment either side moves — including when #123 lands, which is the correct behaviour.

#![cfg(feature = "rholang")]

use std::collections::BTreeSet;

use mettail_ast::grammar::{GrammarItem, PatternOp, SyntaxExpr};
use mettail_ast::language::LanguageDef;
use mettail_languages::rholang::Proc;
use mettail_ast::auto_inject::reconstruct_language_def;
use mettail_runtime::Language;

// ══════════════════════════════════════════════════════════════════════════════
// The oracle
// ══════════════════════════════════════════════════════════════════════════════

/// The path the oracle list was measured from, and which [`oracle_list_has_not_drifted`]
/// re-derives it from when the checkout is present.
const ORACLE_GRAMMAR_PATH: &str =
    "/home/dylon/Workspace/f1r3fly.io/rholang-rs/rholang-tree-sitter/grammar.js";

/// `reserved.global` at the oracle's HEAD.
///
/// **Dated measurement: 2026-07-30**, derived by the command in the module docs. Sorted, so
/// the ordering carries no information and a diff against it is a set diff.
const ORACLE_RESERVED: &[&str] = &[
    "and", "bundle", "contract", "else", "false", "for", "if", "let", "match", "matches", "new",
    "not", "or", "select", "true", "where",
];

// ══════════════════════════════════════════════════════════════════════════════
// The MeTTaIL side, derived
// ══════════════════════════════════════════════════════════════════════════════

/// `prattail`'s own identifier-shape test, verbatim: `TerminalPattern::is_keyword` is
/// `text.chars().all(|c| c.is_alphanumeric() || c == '_')` (`prattail/src/lexer.rs`).
///
/// The extra `starts_with(alphabetic | '_')` here is not a second rule but the *name*
/// position's own constraint: a purely numeric terminal such as `"0"` passes prattail's
/// predicate yet can never collide with an identifier, and `new 0 in { Nil }` is
/// ill-formed for a reason that has nothing to do with reservation.
fn is_identifier_shaped(text: &str) -> bool {
    let mut chars = text.chars();
    match chars.next() {
        Some(first) if first.is_alphabetic() || first == '_' => {
            chars.all(|c| c.is_alphanumeric() || c == '_')
        },
        _ => false,
    }
}

/// Every literal terminal spelling the grammar declares, from both syntax shapes.
///
/// Mirrors `prattail::pipeline::state::collect_terminals_recursive` in reaching *through*
/// the pattern operations (`#sep`, `#map`, `#zip`, `#opt`), because a keyword nested in a
/// `#map` body is as reserved as a top-level one.
fn declared_literals(def: &LanguageDef) -> BTreeSet<String> {
    fn walk_exprs(exprs: &[SyntaxExpr], out: &mut BTreeSet<String>) {
        for expr in exprs {
            match expr {
                SyntaxExpr::Literal(text) => {
                    out.insert(text.clone());
                },
                SyntaxExpr::Op(op) => walk_op(op, out),
                _ => {},
            }
        }
    }

    fn walk_op(op: &PatternOp, out: &mut BTreeSet<String>) {
        match op {
            PatternOp::Sep { separator, source, .. } => {
                out.insert(separator.clone());
                if let Some(inner) = source {
                    walk_op(inner, out);
                }
            },
            PatternOp::Map { source, body, .. } => {
                walk_op(source, out);
                walk_exprs(body, out);
            },
            PatternOp::Opt { inner } => walk_exprs(inner, out),
            PatternOp::Zip { .. } | PatternOp::Var(_) => {},
        }
    }

    let mut literals = BTreeSet::new();
    for rule in &def.terms {
        if let Some(pattern) = &rule.syntax_pattern {
            walk_exprs(pattern, &mut literals);
        }
        for item in &rule.items {
            if let GrammarItem::Terminal(text) = item {
                literals.insert(text.clone());
            }
        }
    }
    literals
}

/// Identifier-shaped collection *openers*, which `auto` escalates to the `contextual`
/// opt-out so that `Set( … )` keeps parsing.
///
/// Derived the way `macros/src/gen/syntax/parser/prattail_bridge.rs` derives it: the opener
/// with a trailing `(` trimmed, kept only when what remains is identifier-shaped.
fn contextual_collection_openers(def: &LanguageDef) -> BTreeSet<String> {
    let mut openers = BTreeSet::new();
    for ty in &def.types {
        if let Some(kind) = &ty.collection_kind {
            let trimmed = kind.delimiters().open.trim_end_matches('(').to_string();
            if is_identifier_shaped(&trimmed) {
                openers.insert(trimmed);
            }
        }
    }
    openers
}

/// Identifier-shaped literals that occupy a METHOD position — the item immediately before
/// them in their rule's syntax pattern is the literal `"."`.
fn dotted_method_literals(def: &LanguageDef) -> BTreeSet<String> {
    let mut dotted = BTreeSet::new();
    for rule in &def.terms {
        if let Some(pattern) = &rule.syntax_pattern {
            for pair in pattern.windows(2) {
                match (&pair[0], &pair[1]) {
                    (SyntaxExpr::Literal(dot), SyntaxExpr::Literal(name))
                        if dot == "." && is_identifier_shaped(name) =>
                    {
                        dotted.insert(name.clone());
                    },
                    _ => {},
                }
            }
        }
    }
    dotted
}

/// The reconstructed Rholang `LanguageDef`, from the metadata's own definition source.
fn rholang_def() -> LanguageDef {
    let source = mettail_languages::rholang::RholangLanguage
        .metadata()
        .definition_source()
        .expect("the rholang metadata carries its own definition source");
    reconstruct_language_def(source).expect("the rholang definition source reconstructs")
}

/// The full comparison domain: every word either side could have an opinion about.
///
/// The union is what makes the **under**-reserved direction visible at all — `bundle` is not
/// a MeTTaIL terminal, so a domain derived from MeTTaIL alone would not contain it and the
/// probe would never ask about it.
fn comparison_domain(def: &LanguageDef) -> BTreeSet<String> {
    let mut domain: BTreeSet<String> = declared_literals(def)
        .into_iter()
        .filter(|text| is_identifier_shaped(text))
        .collect();
    // ★ Collection DELIMITERS are terminals too, and a first pass that harvested only rule
    // literals missed `Set` entirely — the very sampling error #128 warns about, reproduced
    // inside the fix for it. `prattail`'s own terminal harvest (`lexer.rs`) takes the
    // collection openers and separators alongside the rule literals, so this does too.
    domain.extend(contextual_collection_openers(def));
    domain.extend(ORACLE_RESERVED.iter().map(|w| w.to_string()));
    domain
}

// ══════════════════════════════════════════════════════════════════════════════
// The recorded divergence — a DERIVED family plus a typed exception table
// ══════════════════════════════════════════════════════════════════════════════

/// ★★ THE OVER-RESERVED SET SPLITS INTO ONE DERIVED FAMILY AND A RESIDUE.
///
/// The larger part is the **dotted-method family** — every identifier-shaped literal whose
/// predecessor in its rule's syntax pattern is `"."`. That family is #122's lane and #123's
/// fix, and it is *computed* by [`dotted_method_literals`]: adding `Proc.foo(…)` to the
/// grammar enrols `foo` automatically, with no edit here. Only the RESIDUE — the words that
/// are over-reserved for reasons that are **not** the method surface — is written down, and
/// each row carries its own reason.
///
/// # ⚠ The filing sampled, and the sample was off by 16
///
/// #128 named 5 residue words: `int`, `uint`, `fraction`, `error`, `Nil`. The derived residue
/// is **21**. That is precisely the failure #128 itself warns about — *"a sample is exactly
/// how #122 was first reported as 2 cases when the true count was 44"* — so the count here is
/// derived and the sample is recorded as having been a sample.
///
/// # The superset verdict per family
///
/// Every row is a word an upstream program may legally use as an identifier and cannot use
/// here, so every row is **DIVERGENT** under the superset standard until it is un-reserved.
/// The reason column says what un-reserving would cost, which is the input a per-word ruling
/// needs; it is not a justification for keeping the divergence.
struct OverReservation {
    word: &'static str,
    /// The rule whose syntax pattern declares the word as a literal — the site to edit.
    owner: &'static str,
    /// Why the word is a terminal at all, and what it would take to stop reserving it.
    reason: &'static str,
}

/// The residue: over-reserved words that are **not** dotted-method names.
///
/// Measured 2026-07-30 on this tree by [`the_reserved_set_diverges_from_the_oracle_exactly_as_recorded`].
const OVER_RESERVED_RESIDUE: &[OverReservation] = &[
    // ── Conversion / construction functions, written `f( … )`. All MeTTaIL extensions:
    //    upstream has no such surface, so the words are free identifiers there.
    OverReservation {
        word: "bigint",
        owner: "BigintCastProc",
        reason: "`bigint(p)` numeric-cast surface — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "bigrat",
        owner: "BigratCastProc",
        reason: "`bigrat(p)` numeric-cast surface — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "bool",
        owner: "ToBool",
        reason: "`bool(p)` conversion surface — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "fixed",
        owner: "FixedBinProc",
        reason: "`fixed(p, w)` width-annotated cast — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "float",
        owner: "FloatBinProc",
        reason: "`float(p, w)` width-annotated cast — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "fraction",
        owner: "FractionProc",
        reason: "`fraction(a, b)` rational constructor — a MeTTaIL extension; named by the filing",
    },
    OverReservation {
        word: "int",
        owner: "IntBinProc",
        reason: "`int(p, w)` width-annotated cast — a MeTTaIL extension; named by the filing",
    },
    OverReservation {
        word: "str",
        owner: "ToStr",
        reason: "`str(p)` conversion surface — a MeTTaIL extension with no upstream form",
    },
    OverReservation {
        word: "uint",
        owner: "UIntBinProc",
        reason: "`uint(p, w)` width-annotated cast — a MeTTaIL extension; named by the filing",
    },
    // ── Infix operator WORDS. Upstream spells these as symbols or not at all, so the words
    //    remain free identifiers there.
    OverReservation {
        word: "bitand",
        owner: "BitAnd",
        reason: "the infix `a bitand b` operator word — a MeTTaIL extension",
    },
    OverReservation {
        word: "bitnot",
        owner: "BitNot",
        reason: "the prefix `bitnot a` operator word — a MeTTaIL extension",
    },
    OverReservation {
        word: "bitor",
        owner: "BitOr",
        reason: "the infix `a bitor b` operator word — a MeTTaIL extension",
    },
    OverReservation {
        word: "implies",
        owner: "Implies",
        reason: "the infix `a implies b` operator word — a MeTTaIL extension",
    },
    // ── Capitalised call surfaces. Upstream reserves no capitalised word at all.
    OverReservation {
        word: "Map",
        owner: "MapEmpty",
        reason: "`Map()` — the empty-map literal, spelled as a rule literal and therefore NOT \
                 covered by the `contextual` collection-opener opt-out that protects `Set(`",
    },
    OverReservation {
        word: "PPar",
        owner: "SpatialPPar",
        reason: "`PPar(a, b)` — the spatial-matching constructor surface, a MeTTaIL extension",
    },
    OverReservation {
        word: "Pathmap",
        owner: "PathmapEmpty",
        reason: "`Pathmap()` — the empty-pathmap literal, same opt-out gap as `Map`",
    },
    // ── Ground / nullary literals.
    OverReservation {
        word: "Nil",
        owner: "PZero",
        reason: "the null process. ⚠ Reserving it is DELIBERATE and load-bearing: the \
                 2026-07-06 `auto` flip removed the spurious \
                 send-on-a-channel-named-`Nil` reading and collapsed the `@Nil!(q)` cohort \
                 2 → 1 (`keyword_reservation_tests::rholang_auto_reserved_unregressed`). \
                 Un-reserving restores an over-generation. Named by the filing.",
    },
    OverReservation {
        word: "error",
        owner: "Err",
        reason: "the `error` ground term. ⚠ The filing flags this as an ESPECIALLY likely \
                 upstream identifier name. Named by the filing.",
    },
    // ── A positional keyword of a construct BOTH sides have.
    OverReservation {
        word: "in",
        owner: "PNew",
        reason: "★ the `new xs in { p }` separator. Upstream has the SAME positional terminal \
                 (`new: prec(1, seq('new', $.name_decls, 'in', $._proc))`) and deliberately \
                 does NOT reserve it — tree-sitter disambiguates positionally. ⚠ #128 missed \
                 this row because it believed `in` was one of the oracle's reserved words; it \
                 is not, so `in` is an over-reservation rather than a match.",
    },
    // ── An identifier-shaped COLLECTION OPENER. The `contextual` opt-out applies and is
    //    still not enough, which is the finding rather than the assumption.
    OverReservation {
        word: "Set",
        owner: "<collection opener `Set(` of the `Set` category>",
        reason: "★ `auto` DOES escalate `Set` to `ReservationPolicy::contextual`, and \
                 `Set(1,2,3)` parses — but `new Set in { Nil }` still does not, because the \
                 word lexes as `Fixed(\"Set\")` and the name position wants an `Ident` with no \
                 lex-fork seeded for it. The opt-out is NECESSARY BUT NOT SUFFICIENT: it \
                 preserves the collection literal without restoring the identifier. ⚠ A first \
                 pass at this gate harvested only RULE literals and missed `Set` outright — \
                 the same sampling error #128 was filed about, reproduced inside its own fix.",
    },
    // ── MeTTaIL-internal rules with no user-facing surface (#147's two `__` terminals).
    OverReservation {
        word: "__comm_where",
        owner: "CommWhere",
        reason: "★ a MeTTaIL-INTERNAL rule terminal, one of the two surviving `__`-prefixed \
                 terminals (#147). It reserves a word no user would write, so the breach is \
                 theoretical — but it is a breach, and it is the concrete cost of encoding \
                 non-surface-ness in a SPELLING.",
    },
    OverReservation {
        word: "__guard_then",
        owner: "GuardThen",
        reason: "★ the second surviving `__`-prefixed terminal (#147); same shape as \
                 `__comm_where`.",
    },
];

/// ★ The UNDER-reserved direction needs no reason column, because the reason is DERIVED.
///
/// For each of these, MeTTaIL declares the word as **no terminal at all** — the construct is
/// absent from the grammar, so there is nothing to reserve. That is asserted in
/// [`under_reservation_is_a_missing_construct_not_a_missing_reservation`] rather than
/// written here, so a row whose construct later appears *without* reservation fails with a
/// different and much more interesting message.
///
/// Measured 2026-07-30: **7 words**, where #128 named one (`bundle`).
const UNDER_RESERVED: &[&str] =
    &["bundle", "contract", "else", "if", "let", "match", "select"];

// ══════════════════════════════════════════════════════════════════════════════
// The probe
// ══════════════════════════════════════════════════════════════════════════════

/// A name that no grammar declares and no oracle reserves. The control for every row.
const FREE_NAME: &str = "notamethod";

/// Whether `word` is usable as a bound name here, measured by parsing.
///
/// `new <word> in { Nil }` is #128's own probe: the `new` production's `name_decls` is a
/// pure name position, so a failure to parse there is a reservation and not a precedence or
/// arity accident.
fn parses_as_a_name(word: &str) -> bool {
    Proc::parse(&format!("new {word} in {{ Nil }}")).is_ok()
}

/// MeTTaIL's effective reserved set over the comparison domain.
fn mettail_reserved(domain: &BTreeSet<String>) -> BTreeSet<String> {
    domain
        .iter()
        .filter(|word| !parses_as_a_name(word))
        .cloned()
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Gates
// ══════════════════════════════════════════════════════════════════════════════

/// ★ The anti-vacuity floor for every row below.
///
/// Without it the whole diff would pass against a parser that rejected *everything* — the
/// failure mode twelve guards in this campaign had. Asserted as its own test so its failure
/// is not read as a divergence.
#[test]
fn the_probe_distinguishes_a_free_name_from_a_reserved_one() {
    assert!(
        parses_as_a_name(FREE_NAME),
        "`new {FREE_NAME} in {{ Nil }}` does not parse, so the probe cannot tell a reserved \
         word from a broken parser and every reservation verdict below is vacuous.",
    );
    assert!(
        !parses_as_a_name("new"),
        "`new new in {{ Nil }}` parses, so nothing at all is reserved on this tree and the \
         probe cannot detect over-reservation.",
    );
}

/// The comparison domain must be wide enough to contain the defect.
#[test]
fn the_derived_domain_reaches_the_grammar() {
    let def = rholang_def();
    let literals = declared_literals(&def);
    assert!(
        literals.len() > 100,
        "only {} literal terminals were harvested from the reconstructed grammar; the walk \
         is not reaching the syntax patterns, so every set below is a subset of nothing.",
        literals.len(),
    );

    let domain = comparison_domain(&def);
    for expected in ["new", "for", "contract", "bundle"] {
        assert!(
            domain.contains(expected),
            "`{expected}` is missing from the comparison domain, which is the union of the \
             grammar's identifier-shaped terminals, its identifier-shaped collection openers, \
             and the oracle's own words. A domain that \
             cannot ask about a word cannot report a divergence for it.",
        );
    }
}

/// ★★ THE DIVERGENCE, BOTH DIRECTIONS, DERIVED.
///
/// The expected content is a **typed exception table keyed on a derived domain**: what must
/// be explained is computed from the grammar and the oracle, and only the *reason* for each
/// row is written here. A word that stops diverging, or starts, fails this test — and the
/// message says which direction it moved.
#[test]
fn the_reserved_set_diverges_from_the_oracle_exactly_as_recorded() {
    let def = rholang_def();
    let domain = comparison_domain(&def);
    let reserved_here = mettail_reserved(&domain);
    let reserved_upstream: BTreeSet<String> =
        ORACLE_RESERVED.iter().map(|w| w.to_string()).collect();

    let over: BTreeSet<String> = reserved_here
        .difference(&reserved_upstream)
        .cloned()
        .collect();
    let under: BTreeSet<String> = reserved_upstream
        .difference(&reserved_here)
        .cloned()
        .collect();

    // ── The DERIVED family: dotted-method names. #122's lane, #123's fix.
    let dotted = dotted_method_literals(&def);
    let (over_dotted, over_residue): (BTreeSet<String>, BTreeSet<String>) =
        over.iter().cloned().partition(|word| dotted.contains(word));

    // Reporting affordance: the counts in the module docs are a MEASUREMENT, and this is how
    // a reader re-obtains them without having to make the gate fail first.
    //   MEttail RESERVED REPORT=1 cargo test -p languages --features rholang \
    //       --test reserved_set_oracle_conformance -- --nocapture
    if std::env::var("METTAIL_RESERVED_REPORT").is_ok() {
        println!("domain               = {}", domain.len());
        println!("reserved_here        = {}", reserved_here.len());
        println!("oracle               = {}", reserved_upstream.len());
        println!("over                 = {}", over.len());
        println!("over_dotted_family   = {}", over_dotted.len());
        println!("over_residue         = {} {:?}", over_residue.len(), over_residue);
        println!("under                = {} {:?}", under.len(), under);
    }

    assert!(
        !dotted.is_empty(),
        "no dotted-method literals were derived from the grammar, so the family split below \
         is vacuous and the whole over-reserved set would be reported as residue.",
    );
    assert_eq!(
        over_dotted,
        dotted.intersection(&domain).cloned().collect::<BTreeSet<String>>(),
        "\nsome dotted-method literal is NOT over-reserved, which means the method surface \
         has partly stopped being reserved. That is #123's fix landing: move the family \
         boundary rather than adding residue rows.",
    );

    // ── The RESIDUE: a typed exception table, diffed as a set.
    let recorded_residue: BTreeSet<String> = OVER_RESERVED_RESIDUE
        .iter()
        .map(|row| row.word.to_string())
        .collect();
    assert_eq!(
        recorded_residue.len(),
        OVER_RESERVED_RESIDUE.len(),
        "`OVER_RESERVED_RESIDUE` lists a word twice, so its length is not its cardinality.",
    );
    assert_eq!(
        over_residue,
        recorded_residue,
        "\nOVER-RESERVED RESIDUE (reserved here, free upstream, NOT a dotted method) has \
         drifted.\n  measured ({}): {:?}\n  recorded ({}): {:?}\n  newly over-reserved: \
         {:?}\n  no longer over-reserved: {:?}\n\
         Each residue word is a SUPERSET BREACH: an upstream program using it as an \
         identifier parses upstream and is rejected here. Add a row with its owning rule and \
         its reason, or un-reserve it. The dotted-method family is derived and excluded from \
         this diff — a new `Proc.foo(…)` method does NOT belong here.",
        over_residue.len(),
        over_residue,
        recorded_residue.len(),
        recorded_residue,
        over_residue.difference(&recorded_residue).collect::<Vec<_>>(),
        recorded_residue.difference(&over_residue).collect::<Vec<_>>(),
    );

    // Each residue row must name a rule that actually declares it — the owner column is a
    // pointer to the site to edit, and a stale pointer is worse than none.
    let owners: BTreeSet<String> = def.terms.iter().map(|r| r.label.to_string()).collect();
    for row in OVER_RESERVED_RESIDUE {
        // A `<…>` owner names a non-rule site (a collection delimiter, say); anything else
        // must be a rule the grammar really declares.
        assert!(
            row.owner.starts_with('<') || owners.contains(row.owner),
            "`OVER_RESERVED_RESIDUE` row `{}` names owner rule `{}`, which the grammar does \
             not declare. The owner column is the site to edit; a stale one misdirects the fix.",
            row.word,
            row.owner,
        );
        assert!(
            !row.reason.trim().is_empty(),
            "`OVER_RESERVED_RESIDUE` row `{}` carries no reason. \"It fell out of the literal \
             harvest\" is not one, and neither is silence.",
            row.word,
        );
    }

    // ── The UNDER direction.
    let recorded_under: BTreeSet<String> =
        UNDER_RESERVED.iter().map(|w| w.to_string()).collect();
    assert_eq!(
        under,
        recorded_under,
        "\nUNDER-RESERVED (free here, reserved upstream) has drifted.\n  measured ({}): \
         {:?}\n  recorded ({}): {:?}\n\
         An under-reserved word is accepted here and rejected upstream. That is NOT a \
         superset breach — but see \
         `under_reservation_is_a_missing_construct_not_a_missing_reservation` before treating \
         it as a reservation defect.",
        under.len(),
        under,
        recorded_under.len(),
        recorded_under,
    );

    // ── Non-vacuity. Emptying the tables to force a pass must trip here.
    assert!(
        !OVER_RESERVED_RESIDUE.is_empty() && !UNDER_RESERVED.is_empty(),
        "a divergence table is empty. If Rholang genuinely conforms to the oracle in that \
         direction, delete the table and say so in the module docs — do not leave a gate that \
         asserts two empty sets are equal.",
    );
}

/// ★★ THE `contextual` COLLECTION-OPENER OPT-OUT IS NECESSARY BUT NOT SUFFICIENT.
///
/// `prattail_bridge` escalates every identifier-shaped collection *opener* to
/// `ReservationPolicy::contextual` so that `Set( … )` keeps parsing under `auto`. Measured on
/// this tree:
///
/// | probe | result |
/// |---|---|
/// | `Set(1,2,3)` | parses — the opt-out does its job |
/// | `new x in { Set(1) }` | parses |
/// | `new Set in { Nil }` | **does not parse** |
///
/// So dropping the *reservation* is not the same as restoring the *identifier*: the word still
/// lexes as `Fixed("Set")`, and the name position wants an `Ident` for which nothing seeds a
/// lex-fork (contrast `Nil`, which keeps its nullary reading through
/// `NULLARY_KEYWORD_LEXFORK_SEED` while remaining reserved). `Set` is therefore an
/// over-reservation *in effect*, and it has a row in [`OVER_RESERVED_RESIDUE`].
///
/// This test pins all three cells, because the interesting regression is any one of them
/// moving independently.
#[test]
fn the_collection_opener_opt_out_preserves_the_literal_but_not_the_identifier() {
    let def = rholang_def();
    let openers = contextual_collection_openers(&def);
    assert!(
        openers.contains("Set"),
        "`Set` is not among the derived identifier-shaped collection openers ({openers:?}), so \
         this test no longer examines the opt-out at all.",
    );

    assert!(
        Proc::parse("Set(1,2,3)").is_ok(),
        "`Set(1,2,3)` no longer parses, so the `contextual` opt-out has stopped protecting the \
         collection literal — that is the regression the opt-out exists to prevent, and it is \
         a different defect from the reservation divergence.",
    );
    assert!(
        Proc::parse("new x in { Set(1) }").is_ok(),
        "`Set(1)` no longer parses inside a `new` body.",
    );
    assert!(
        !parses_as_a_name("Set"),
        "★ `new Set in {{ Nil }}` now PARSES. That is an improvement, not a failure: the \
         opt-out has become sufficient to restore the identifier. Remove the `Set` row from \
         `OVER_RESERVED_RESIDUE` and record how it was achieved — the same mechanism may \
         apply to the other capitalised rows (`Map`, `Pathmap`, `PPar`).",
    );
}

/// ★★ THE UNDER-RESERVED DIRECTION IS A PREMISE INVERSION, AND THIS IS THE PROOF.
///
/// #128 asks whether `bundle` *"needs a grammar rule, or an explanation of why MeTTaIL has no
/// bundle construct"*, and asks to *"establish whether a program can be written that means one
/// thing here and another upstream"*. This answers both, for all seven words, by derivation:
/// **MeTTaIL declares none of them as a terminal anywhere.** The construct is absent, so there
/// is no keyword to reserve.
///
/// # Why that inverts the repair
///
/// Reserving `if` in a grammar that has no `if` would make MeTTaIL **strictly worse**: it would
/// start rejecting `new if in { Nil }` — which it accepts today and which no upstream program
/// contains — while still not accepting `if (x) { P } else { Q }`, which is the actual superset
/// breach. Under-reservation is a *symptom*; the defect is the seven missing constructs, which
/// is a different (and much larger) item.
///
/// # And the "means one thing here, another upstream" question
///
/// No. For all seven, the only programs whose acceptance differs are ones that use the word as
/// an identifier, and those are *rejected upstream*. There is no program accepted by both sides
/// with two different meanings, because the word has no meaning at all here.
#[test]
fn under_reservation_is_a_missing_construct_not_a_missing_reservation() {
    let def = rholang_def();
    let literals = declared_literals(&def);
    for word in UNDER_RESERVED {
        assert!(
            !literals.contains(*word),
            "`{word}` IS declared as a terminal by the Rholang grammar and yet is not \
             reserved. That is a genuinely different defect from the six others in \
             `UNDER_RESERVED`, whose constructs are simply absent: a declared keyword that \
             fails to reserve means the terminal is spelled so that \
             `TerminalPattern::is_keyword` is false (glued to punctuation, e.g. `\"if (\"`), \
             and the fix is the SPELLING, not the reserved set.",
        );
    }

    // Non-vacuity: the derivation would be trivially true against an empty literal set.
    assert!(
        literals.contains("new") && literals.contains("for"),
        "the literal set does not contain `new` or `for`, so `declared_literals` is not \
         reaching the grammar and every absence asserted above is vacuous.",
    );
}

/// ★ Drift detection for the transcribed oracle.
///
/// [`ORACLE_RESERVED`] is a copy of a list in another repository, which is exactly the shape
/// this campaign has watched drift six times. It cannot be derived *in place* — a workspace
/// test may not require a foreign checkout — so it is derived *when it can be*, and says so
/// when it cannot rather than passing silently.
#[test]
fn oracle_list_has_not_drifted() {
    let source = match std::fs::read_to_string(ORACLE_GRAMMAR_PATH) {
        Ok(text) => text,
        Err(err) => {
            println!(
                "SKIPPED (vacuous): `{ORACLE_GRAMMAR_PATH}` is not readable ({err}), so the \
                 transcribed `ORACLE_RESERVED` could not be re-derived on this machine. The \
                 divergence test still runs, against the dated 2026-07-30 measurement."
            );
            return;
        },
    };

    let words = parse_oracle_reserved(&source);
    assert!(
        !words.is_empty(),
        "parsed ZERO words out of `{ORACLE_GRAMMAR_PATH}`'s `reserved.global` array. That is \
         a parse failure, not an empty list — the file is known to reserve at least `new` — \
         and it would make this whole test vacuous.",
    );
    let recorded: BTreeSet<String> = ORACLE_RESERVED.iter().map(|w| w.to_string()).collect();
    assert_eq!(
        words,
        recorded,
        "\nthe oracle's `reserved.global` array has drifted from the 2026-07-30 measurement \
         transcribed in `ORACLE_RESERVED`.\n  oracle now ({}): {:?}\n  recorded ({}): {:?}\n\
         Re-derive `ORACLE_RESERVED` from the oracle — do not adjust the diff tables to \
         absorb the change.",
        words.len(),
        words,
        recorded.len(),
        recorded,
    );
}

/// The `reserved: { global: $ => [ … ] }` array of a tree-sitter `grammar.js`, comments
/// stripped so the `NOTE:` block's back-ticked words cannot be mistaken for entries.
fn parse_oracle_reserved(source: &str) -> BTreeSet<String> {
    let anchor = match source.find("reserved:") {
        Some(index) => index,
        None => return BTreeSet::new(),
    };
    let open = match source[anchor..].find('[') {
        Some(index) => anchor + index + 1,
        None => return BTreeSet::new(),
    };
    let close = match source[open..].find(']') {
        Some(index) => open + index,
        None => return BTreeSet::new(),
    };
    source[open..close]
        .lines()
        .map(|line| match line.find("//") {
            Some(index) => &line[..index],
            None => line,
        })
        .flat_map(|line| {
            line.split('"')
                .skip(1)
                .step_by(2)
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .collect()
}
