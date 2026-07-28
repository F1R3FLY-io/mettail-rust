//! The generated binding-power ladders, asserted against their normative source.
//!
//! ## Why a table test and not only behavioural tests
//!
//! Behavioural fixtures (`languages/tests/operator_precedence_conformance.rs`) prove that
//! a particular reading is produced. They cannot prove that a level structure is the
//! RIGHT one, because most level distinctions have no behavioural witness:
//!
//! - Calculator's `Int`/`Float`/`Str`/`Fixed` comparisons are cross-category
//!   (`Int × Int → Bool`), so a chain like `1 < 2 == 3` is ill-typed. Whether those six
//!   operators sit on one level or six is invisible to any program.
//! - Two readings frequently coincide in value (`1 + 2 - 3` is 0 either way).
//!
//! This file therefore reads the ladder the `language!` macro actually emitted and
//! compares it to the table it is supposed to implement. That makes drift from the
//! normative grammar **detectable** rather than discoverable.
//!
//! ## Where the numbers come from
//!
//! The macro writes `target/generated/<lang>/wpda.rs`, which contains one
//! `infix_bp_<category>` function per category:
//!
//! ```text
//! fn infix_bp_proc(terminal: &str) -> &'static [(u8, u8, u16, u16)] {
//!     match terminal {
//!         "*" => &[(20u8, 21u8, 0u16, 70u16)],
//!         …
//! ```
//!
//! The first two components are `(left_bp, right_bp)`. From them:
//!
//! - the **level** is `min(left_bp, right_bp)` — the same reading every downstream
//!   consumer uses (`macros/src/gen/runtime/wpda_codegen/facade.rs`);
//! - the **associativity** is the ORDER of the pair: `left_bp < right_bp` is left,
//!   `left_bp > right_bp` is right.
//!
//! Levels are compared as a PARTITION and an ORDER, never as literal numbers: the
//! assertions below say "these operators share a level" and "this level is looser than
//! that one", so inserting a new operator renumbers the ladder without failing a single
//! assertion. Nothing here pins a magic constant.
//!
//! ## Rholang's normative source
//!
//! `/home/dylon/Workspace/f1r3fly.io/rholang-rs/rholang-tree-sitter/grammar.js`:
//!
//! ```js
//! par:     $ => prec.left(0,  seq($._proc, '|',       $._proc)),
//! or:      $ => prec.left(4,  seq($._proc, 'or',      $._proc)),
//! and:     $ => prec.left(5,  seq($._proc, 'and',     $._proc)),
//! matches: $ => prec.right(6, seq($._proc, 'matches', $._proc)),
//! eq:      $ => prec.left(6,  seq($._proc, '==',      $._proc)),
//! neq:     $ => prec.left(6,  seq($._proc, '!=',      $._proc)),
//! lt:      $ => prec.left(7,  seq($._proc, '<',       $._proc)),
//! lte:     $ => prec.left(7,  seq($._proc, '<=',      $._proc)),
//! gt:      $ => prec.left(7,  seq($._proc, '>',       $._proc)),
//! gte:     $ => prec.left(7,  seq($._proc, '>=',      $._proc)),
//! add:     $ => prec.left(8,  seq($._proc, '+',       $._proc)),
//! sub:     $ => prec.left(8,  seq($._proc, '-',       $._proc)),
//! mult:    $ => prec.left(9,  seq($._proc, '*',       $._proc)),
//! div:     $ => prec.left(9,  seq($._proc, '/',       $._proc)),
//! mod:     $ => prec.left(9,  seq($._proc, '%',       $._proc)),
//! ```
//!
//! Higher tree-sitter precedence binds tighter, so level 9 is the tightest above.
//!
//! **Level 6 carries MIXED associativity** — right-associative `matches` beside
//! left-associative `==` and `!=`. That is the shape which makes per-operator
//! associativity within a level mandatory rather than merely convenient, and it is
//! asserted explicitly below.

use std::collections::BTreeMap;
use std::path::PathBuf;

/// `(left_bp, right_bp)` for one operator, as emitted.
type Bp = (u8, u8);

/// Locate `target/generated/`, mirroring
/// `macros::logic::writer::lang_generated_dir`: walk up from this crate's manifest
/// directory to the `Cargo.toml` that declares `[workspace]`, then descend into
/// `target/generated/<lang>`. Duplicating the RULE rather than importing it keeps this
/// test independent of the macro crate's internals; the two are pinned together by the
/// fact that a wrong path yields no table and every assertion below fails loudly.
fn generated_wpda(lang: &str) -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let manifest = dir.join("Cargo.toml");
        if std::fs::read_to_string(&manifest)
            .map(|c| c.lines().any(|l| l.trim_start().starts_with("[workspace]")))
            .unwrap_or(false)
        {
            break;
        }
        if !dir.pop() {
            panic!("no [workspace] Cargo.toml above {}", env!("CARGO_MANIFEST_DIR"));
        }
    }
    dir.join("target")
        .join("generated")
        .join(lang)
        .join("wpda.rs")
}

/// Parse `infix_bp_<category>` out of a generated `wpda.rs`.
///
/// Returns `terminal -> (left_bp, right_bp)`. Panics with an explicit message when the
/// function is absent, so a renamed emitter surfaces as a failure rather than as an
/// empty map that vacuously satisfies every assertion.
fn infix_ladder(lang: &str, category: &str) -> BTreeMap<String, Bp> {
    let path = generated_wpda(lang);
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));

    let header = format!("fn infix_bp_{}(terminal: &str)", category.to_lowercase());
    let start = src.find(&header).unwrap_or_else(|| {
        panic!(
            "{} declares no `{}` — the emitter was renamed, or `{}` is not a category of `{}`",
            path.display(),
            header,
            category,
            lang
        )
    });
    let body = &src[start..];
    let end = body.find("\n}\n").expect("unterminated infix_bp function");
    let body = &body[..end];

    let mut out = BTreeMap::new();
    for line in body.lines() {
        // `        "*" => &[(20u8, 21u8, 0u16, 70u16)],`
        let Some(q1) = line.find('"') else { continue };
        let Some(q2) = line[q1 + 1..].find('"') else {
            continue;
        };
        let terminal = &line[q1 + 1..q1 + 1 + q2];
        let Some(paren) = line.find("[(") else {
            continue;
        };
        let nums: Vec<u8> = line[paren + 2..]
            .split(',')
            .take(2)
            .filter_map(|t| t.trim().trim_end_matches("u8").parse().ok())
            .collect();
        if nums.len() == 2 {
            out.insert(terminal.to_string(), (nums[0], nums[1]));
        }
    }
    assert!(
        !out.is_empty(),
        "parsed no operators out of `{}` in {} — the emitted shape changed",
        header,
        path.display()
    );
    out
}

/// The Pratt level of an operator: the lower of its two binding powers.
///
/// Left-associative `(p, p+1)` and right-associative `(p+1, p)` both have level `p`,
/// which is exactly what lets operators of different associativity share one level.
fn level(bp: Bp) -> u8 {
    bp.0.min(bp.1)
}

fn is_right_assoc(bp: Bp) -> bool {
    bp.0 > bp.1
}

/// Assert that `ops` all sit on ONE level, and return it.
fn shared_level(ladder: &BTreeMap<String, Bp>, ops: &[&str], context: &str) -> u8 {
    let levels: Vec<(String, u8)> = ops
        .iter()
        .map(|op| {
            let bp = ladder
                .get(*op)
                .unwrap_or_else(|| panic!("{context}: no operator `{op}` in the ladder"));
            ((*op).to_string(), level(*bp))
        })
        .collect();
    let first = levels[0].1;
    assert!(
        levels.iter().all(|(_, l)| *l == first),
        "{context}: these operators must share ONE precedence level, got {levels:?}"
    );
    first
}

/// Assert `looser` is strictly looser (binds less tightly) than `tighter`.
fn assert_looser(looser: u8, tighter: u8, context: &str) {
    assert!(
        looser < tighter,
        "{context}: expected level {looser} to be LOOSER than level {tighter}"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Rholang — the normative ladder, derived from the tree-sitter grammar
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "rholang")]
#[test]
fn rholang_proc_ladder_matches_the_tree_sitter_grammar() {
    let l = infix_ladder("rholang", "proc");

    // ── The grammar's levels, loosest first ──
    let par = shared_level(&l, &["|"], "rholang level 0 (par)");
    let equality = shared_level(&l, &["matches", "==", "!="], "rholang level 6 (equality)");
    let relational = shared_level(&l, &["<", "<=", ">", ">="], "rholang level 7 (relational)");
    let additive = shared_level(&l, &["+", "-"], "rholang level 8 (additive)");
    let multiplicative = shared_level(&l, &["*", "/", "%"], "rholang level 9 (multiplicative)");
    let or = shared_level(&l, &["or"], "rholang level 4");
    let and = shared_level(&l, &["and"], "rholang level 5");

    // ── The grammar's ORDER: par < or < and < equality < relational < additive < mult ──
    assert_looser(par, or, "par vs or");
    assert_looser(or, and, "or vs and (grammar levels 4 < 5)");
    assert_looser(and, equality, "and vs equality (grammar levels 5 < 6)");
    assert_looser(equality, relational, "equality vs relational (grammar levels 6 < 7)");
    assert_looser(relational, additive, "relational vs additive (grammar levels 7 < 8)");
    assert_looser(additive, multiplicative, "additive vs mult (grammar levels 8 < 9)");

    // ── ★ Level 6 carries MIXED associativity ──
    //
    // This is the assertion that makes per-operator associativity mandatory: three
    // operators, one level, two associativities. A design that attached one
    // associativity per level could not satisfy it.
    assert!(
        is_right_assoc(l["matches"]),
        "`matches` is `prec.right(6, …)` in the normative grammar, so it must be \
         right-associative; got {:?}",
        l["matches"]
    );
    assert!(
        !is_right_assoc(l["=="]) && !is_right_assoc(l["!="]),
        "`==` and `!=` are `prec.left(6, …)`; got {:?} and {:?}",
        l["=="],
        l["!="]
    );
    assert_eq!(
        level(l["matches"]),
        level(l["=="]),
        "right-associative `matches` must share level 6 with left-associative `==` — \
         grouping into a level must NOT flatten associativity"
    );

    // ── Every other operator is left-associative by default ──
    for op in ["|", "or", "and", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%"] {
        assert!(
            !is_right_assoc(l[op]),
            "`{op}` declares no associativity, so it must default to LEFT; got {:?}",
            l[op]
        );
    }

    // ── The grammar has no `^` and no bitwise operators in Rholang ──
    for absent in ["^", "&", "|&", "<<", ">>"] {
        assert!(
            !l.contains_key(absent),
            "`{absent}` is not a Rholang operator in the normative grammar, but the \
             ladder declares one"
        );
    }
}

/// MeTTaIL adds three `Proc` operators the tree-sitter grammar does not have:
/// `implies`, `bitor`, and `bitand`. They are pinned here so that "matches the grammar"
/// cannot be read as "has exactly the grammar's operators" — the extensions are
/// deliberate, and their placement is part of the contract.
#[cfg(feature = "rholang")]
#[test]
fn rholang_extension_operators_keep_their_declared_placement() {
    let l = infix_ladder("rholang", "proc");

    let implies = level(l["implies"]);
    let or = level(l["or"]);
    let and = level(l["and"]);
    let bitor = level(l["bitor"]);
    let bitand = level(l["bitand"]);
    let equality = level(l["=="]);

    // `implies` is material implication: looser than `or`, and RIGHT-associative so a
    // chain reads `a implies (b implies c)`.
    assert_looser(implies, or, "implies vs or");
    assert!(
        is_right_assoc(l["implies"]),
        "`implies` is declared `right`; got {:?}",
        l["implies"]
    );

    // Bitwise sits between the connectives and equality, with `bitand` TIGHTER than
    // `bitor` — the same nesting as `and`/`or`.
    assert_looser(and, bitor, "and vs bitor");
    assert_looser(bitor, bitand, "bitor vs bitand — `bitand` must bind tighter");
    assert_looser(bitand, equality, "bitand vs equality");
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — mathematical convention
// ══════════════════════════════════════════════════════════════════════════════

/// Calculator split its comparisons across SIX levels in every category. They belong on
/// one, and in the four cross-category categories that is only observable here.
#[cfg(feature = "calculator")]
#[test]
fn calculator_comparison_levels_are_collapsed() {
    for cat in ["int", "float", "bool", "str", "fixed"] {
        let l = infix_ladder("calculator", cat);
        shared_level(
            &l,
            &["==", "!=", "<", "<=", ">", ">="],
            &format!("calculator `{cat}` comparisons"),
        );
    }
}

/// `+`/`-` share a level, `*`//`/`%` share a level, and the multiplicative level binds
/// tighter — with `^` tighter still and right-associative.
#[cfg(feature = "calculator")]
#[test]
fn calculator_arithmetic_levels() {
    // Int: the full ladder.
    let l = infix_ladder("calculator", "int");
    let cmp = shared_level(&l, &["==", "!="], "int comparisons");
    let additive = shared_level(&l, &["+", "-"], "int additive");
    let multiplicative = shared_level(&l, &["*", "/", "%"], "int multiplicative");
    let pow = shared_level(&l, &["^"], "int power");
    assert_looser(cmp, additive, "comparisons vs additive");
    assert_looser(additive, multiplicative, "additive vs multiplicative");
    assert_looser(multiplicative, pow, "`^` must bind tighter than `*` and `/`");
    assert!(is_right_assoc(l["^"]), "`^` is declared `right`; got {:?}", l["^"]);

    // Float: same shape, without `%`.
    let l = infix_ladder("calculator", "float");
    let additive = shared_level(&l, &["+", "-"], "float additive");
    let multiplicative = shared_level(&l, &["*", "/"], "float multiplicative");
    let pow = shared_level(&l, &["^"], "float power");
    assert_looser(additive, multiplicative, "float additive vs multiplicative");
    assert_looser(multiplicative, pow, "float `^` tighter than `*`//");
    assert!(is_right_assoc(l["^"]), "float `^` is declared `right`");

    // Fixed: `+ -` and `* / %`.
    let l = infix_ladder("calculator", "fixed");
    let additive = shared_level(&l, &["+", "-"], "fixed additive");
    let multiplicative = shared_level(&l, &["*", "/", "%"], "fixed multiplicative");
    assert_looser(additive, multiplicative, "fixed additive vs multiplicative");

    // BigInt has `+` and `-` but no multiplicative operators at all.
    let l = infix_ladder("calculator", "bigint");
    shared_level(&l, &["+", "-"], "bigint additive");

    // BigRat has `*` and `/` but no `-`.
    let l = infix_ladder("calculator", "bigrat");
    let additive = shared_level(&l, &["+"], "bigrat additive");
    let multiplicative = shared_level(&l, &["*", "/"], "bigrat multiplicative");
    assert_looser(additive, multiplicative, "bigrat additive vs multiplicative");
}

/// `and` binds tighter than `or`, with `xor` between them, in every category and
/// fragment that declares the connectives.
#[cfg(feature = "calculator")]
#[test]
fn calculator_boolean_connectives_ladder() {
    let l = infix_ladder("calculator", "bool");
    let cmp = shared_level(&l, &["==", "<"], "bool comparisons");
    let or = shared_level(&l, &["or"], "bool or");
    let xor = shared_level(&l, &["xor"], "bool xor");
    let and = shared_level(&l, &["and"], "bool and");
    assert_looser(cmp, or, "comparisons vs or");
    assert_looser(or, xor, "`or` must be looser than `xor`");
    assert_looser(xor, and, "`xor` must be looser than `and`");
}

/// `bitand` binds tighter than `bitor`, mirroring `and`/`or`, in every category that
/// declares them.
///
/// Their position RELATIVE TO ARITHMETIC is deliberately NOT asserted here: it is an
/// open question (C places `&`/`|` looser than comparison, a choice widely regarded as a
/// mistake; Calculator places them tighter than all arithmetic). This test pins only the
/// inversion that was unambiguously wrong.
#[cfg(feature = "calculator")]
#[test]
fn calculator_bitwise_operators_nest_like_the_connectives() {
    for cat in ["int", "fixed", "bigint", "bigrat", "uint32"] {
        let l = infix_ladder("calculator", cat);
        let bitor = shared_level(&l, &["bitor"], &format!("{cat} bitor"));
        let bitand = shared_level(&l, &["bitand"], &format!("{cat} bitand"));
        assert_looser(
            bitor,
            bitand,
            &format!("calculator `{cat}`: `bitand` must bind TIGHTER than `bitor`"),
        );
    }
}

/// `++` and `+` on `Str` share a level, as they do in Rholang's grammar (both level 8).
#[cfg(feature = "calculator")]
#[test]
fn calculator_string_operators_share_a_level() {
    let l = infix_ladder("calculator", "str");
    let cmp = shared_level(&l, &["=="], "str comparisons");
    let concat = shared_level(&l, &["++", "+"], "str concatenation");
    assert_looser(cmp, concat, "str comparisons vs concatenation");
}

// ══════════════════════════════════════════════════════════════════════════════
// The composition fragments, and the language built from them
// ══════════════════════════════════════════════════════════════════════════════

/// `BoolOpsFragment` carried the same `and`/`or` inversion as Calculator and handed it
/// to every language that composes it. MixedMath is that language.
#[cfg(feature = "composition")]
#[test]
fn mixedmath_ladders() {
    let l = infix_ladder("mixedmath", "bool");
    let or = shared_level(&l, &["or"], "mixedmath or");
    let and = shared_level(&l, &["and"], "mixedmath and");
    assert_looser(or, and, "`and` must bind tighter than `or`");

    let l = infix_ladder("mixedmath", "int");
    let additive = shared_level(&l, &["+", "-"], "mixedmath additive");
    let multiplicative = shared_level(&l, &["*"], "mixedmath multiplicative");
    assert_looser(additive, multiplicative, "additive vs multiplicative");
}

/// `BaseMath` declares `+` and `-`; `ExtMath` and `ImportedMath` inherit them by
/// composition, so all three must show one additive level. This is also the regression
/// guard for the standing mandate that adding or removing a language spec must not
/// break anything: the three ladders are derived, never listed by hand.
#[cfg(feature = "composition")]
#[test]
fn composed_math_languages_share_one_additive_level() {
    for lang in ["basemath", "extmath", "importedmath"] {
        let l = infix_ladder(lang, "num");
        shared_level(&l, &["+", "-"], &format!("{lang} additive"));
    }

    // ImportedMath additionally imports `/`, which must bind tighter than `+`/`-`.
    let l = infix_ladder("importedmath", "num");
    let additive = shared_level(&l, &["+", "-"], "importedmath additive");
    let div = shared_level(&l, &["/"], "importedmath division");
    assert_looser(additive, div, "importedmath additive vs division");
}
