//! GSLT omnibus conformance — **L1 `Json`** (`omnibus.tex:393-415`), rung one
//! (types + terms only; `equations { }` and `rewrites { }` are empty).
//!
//! # Why this file lives in `languages/src/`
//!
//! The language specifications transcribed from the GSLT omnibus paper are
//! PRODUCTION specs (USER ruling, 2026-07-27), so they live beside the other
//! production languages in `languages/src/` and are reachable through the
//! crate's public surface as `mettail_languages::json`. Its conformance suite is
//! `languages/tests/json.rs` — the same spec/tests split every other production
//! spec uses (`languages/src/calculator.rs` ↔ `languages/tests/calculator.rs`).
//!
//! `emit_tests` / `emit_simulator` / `emit_blockly` stay OFF. Those three
//! options are the macro's file-writing switches, so with them off this spec
//! writes no `languages/tests/gen_json_*.rs`, no
//! `languages/src/bin/simulate_json.rs` and no
//! `languages/src/generated/json-*.ts`. What a rung-one presentation has to
//! demonstrate is that every doc clause PARSES and round-trips through its own
//! display, and that is stated exactly — and only — by the hand-written suite
//! next door.
//!
//! ⚠ Those three `false`s must STAY false, and not because production specs are
//! forbidden generated suites — `ambient`/`calculator`/`lambda`/`rhocalc` all
//! carry theirs. `emit_simulator: true` would make the macro write
//! `languages/src/bin/simulate_json.rs` on every compile, and cargo's edition-2021
//! auto-discovery would pick that file up as a binary target with NO
//! `required-features = ["strategies"]` — every hand-declared `[[bin]]` in
//! `languages/Cargo.toml` carries that gate because the generated simulator names
//! `mettail_languages::json::strategies::arb_*`, which exists only under the
//! `strategies` feature. A default `cargo build -p languages` would then fail to
//! compile a file nobody wrote. Flipping these on is a change to the macro's
//! emission contract, not a per-language switch.
//!
//! # Clause-by-clause containment (SUPERSET of the omnibus listing)
//!
//! | omnibus clause (`omnibus.tex`) | our clause | delta |
//! | --- | --- | --- |
//! | `types { Value Field }` (:397-400) | `types { Value Field ![bool] as Bool ![…BigRat] as BigRat ![str] as Str }` | ➕ three native literal carriers |
//! | `JNull . Value ::= "null" ;` (:403) | identical | — |
//! | `JBool . b:Bool \|- b : Value ;` (:404) | identical | — |
//! | `JNum . n:BigRat \|- n : Value ;` (:405) | identical | — |
//! | `JStr . s:Str \|- s : Value ;` (:406) | identical | — |
//! | `JArr . Value ::= "[" List(Value) "]" ;` (:407) | `JArrEmpty` + `JArr1` + `JArr` (three arity cases over an ordered `Vec(Value)`) | one production → three clauses (★ below) |
//! | `JObj . Value ::= "{" List(Field) "}" ;` (:408) | `JObjEmpty` + `JObj1` + `JObj` (three arity cases over an ordered `Vec(Field)`) | one production → three clauses (★ below) |
//! | `Field . k:Str, v:Value \|- k ":" v : Field ;` (:409) | identical | — |
//! | `equations { }` (:412) | identical (empty) | — |
//! | `rewrites { }` (:413) | identical (empty) | — |
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
//! ## ★ The documented delta: how `List(X)` is carried
//!
//! The live macro has no `List(X)` collection constructor: `parse_collection`
//! accepts exactly `HashBag` / `HashSet` / `Vec` (`ast/src/grammar.rs:1454-1466`,
//! error `"expected HashBag, HashSet, or Vec"`). `Vec` *is* the ordered,
//! duplicate-preserving carrier the paper's `List` denotes, so `Vec` is what we
//! use — but NOT as the sole parameter of the production, because that spelling
//! does not survive codegen. Four spellings were tried; here is each and its
//! exact failure, so the next reader need not repeat them:
//!
//! 1. `JArr . Value ::= Vec(Value) sep "," delim "[" "]" ;` (BNF form) and
//!    2. `JArr . vs:Vec(Value) |- "[" vs.*sep(",") "]" : Value ;` (judgement form)
//!    — both **miscompile**. A rule whose SOLE parameter is a collection takes the
//!    "collection-literal" codegen lane, and that lane hardcodes the `HashBag`
//!    carrier: `target/generated/json/term_generation.rs:86,93,107,128` build
//!    `Value::JArr(bag)` with `bag: HashBag<Value>` for a `Vec<Value>` field,
//!    `random_generation.rs:138` does the same for `JObj`, and `flatten.rs:15,39`
//!    iterates `for (e, count) in inner.iter()` (the `HashBag`
//!    (item, multiplicity) shape) over a `Vec` field. Every existing
//!    single-collection-param rule in the tree (`rhocalc` / `ambient` /
//!    `commdemo` `PPar`) is a `HashBag`, so the bug is latent — and it is an
//!    EMITTER bug (`macros/src/gen/…`), not a `grammar.rs` one. Reported, not
//!    fixed unilaterally.
//! 3. `JObj . Value ::= HashBag(Field) sep "," delim "{" "}" ;` — **miscompiles**
//!    for a second, independent reason: the collection-literal lane also assumes
//!    the element category IS the rule's own category (again, every existing use
//!    is `HashBag(Proc) : Proc`), so `flatten.rs:17` pushes a `Field` into a
//!    `Vec<Value>` and `normalize.rs:4181` calls
//!    `insert_into_jobj(&mut HashBag<Value>, Field)`.
//! 4. A native list carrier — `![Vec<Value>] as List { open_parts: ["["], … }`
//!    plus the injection `JArr . l:List |- l : Value ;` (the `rhocalc.rs:57`
//!    idiom) — compiles and parses **in isolation**, but a native collection
//!    alias may only be *named* `List` / `Bag` / `Map` / `Set` / `Pathmap`
//!    (`ast/src/language/parse.rs:509-511`), so the second instantiation
//!    (`List(Field)`) has no name left; `as Bag` with a `Vec` payload miscompiles
//!    (the literal-variant label is `ListLit` by payload type in some emitters and
//!    `BagLit` by alias name in others → `Bag::ListLit` is referenced but never
//!    declared); and the `List`-param injection is silently DROPPED from the AST
//!    altogether once a sibling `Vec`-tailed rule exists (with
//!    `JObj . f:Field, fs:Vec(Field)` present, `JArr` vanishes from
//!    `ast_enums.rs` and from `metadata().terms()` — the fold-alias/canonical
//!    pairing pass, `ast/src/grammar_shapes.rs`).
//!
//! **The spelling that works — and what we use — is the arity split**, i.e. the
//! `rhocalc.rs` `POutput` / `POutput2Plus` idiom, in which a `Vec(T)` slot is a
//! *non-sole* parameter (Class 2). Such a slot is fully supported and may be
//! heterogeneous (`rhocalc.rs:449-455` `InputBindQuery . … args:Vec(Proc) :
//! InputBind` is the precedent):
//!
//! ```text
//! JArrEmpty . |- "[" "]" : Value ;
//! JArr1     . v:Value |- "[" v "]" : Value ;
//! JArr      . v:Value, vs:Vec(Value) |- "[" v "," vs.*sep(",") "]" : Value ;
//! ```
//!
//! and symmetrically `JObjEmpty` / `JObj1` / `JObj` over `Vec(Field)`. The union
//! of each triple is exactly the language the paper's single production denotes —
//! zero, one, or n comma-separated elements between the delimiters — with source
//! ORDER and multiplicity preserved (a `Vec`, never a bag). The delta is therefore
//! purely presentational: one doc production is realized by three arity cases, two
//! of which are ➕ extra clauses. No clause is dropped and no semantics change.
//!
//! The three literal carriers (`Bool`, `BigRat`, `Str`) are *used* by the paper's
//! listing (`b:Bool`, `n:BigRat`, `s:Str`) but never declared in its `types {}`
//! block; mettail requires them to be declared as native-typed categories with
//! `literals {}` lexer patterns (`languages/src/calculator.rs:11-23, 24-30` is the
//! idiom). Declaring them is additive — a superset, not a deviation.

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr,
    unused_imports,
    dead_code
)]

use mettail_macros::language;

language! {
    name: Json,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Value
        Field
        // Native carriers for the paper's `b:Bool`, `n:BigRat`, `s:Str` params.
        ![bool] as Bool
        ![mettail_runtime::CanonicalBigRat] as BigRat
        ![str] as Str
    },

    literals {
        Bool {
            pattern: r"true|false";
            eval: ![ {
                match text {
                    "true" => Ok(true),
                    "false" => Ok(false),
                    _ => Err(()),
                }
            } ]
        }
        // The eval body must yield the prattail literal intermediate
        // `RationalLit(Ratio<BigInt>)` — the generated bridge finishes the job with
        // `CanonicalBigRat::from(intermediate.0)` (cf. `calculator.rs`'s
        // `parse_rational_lit`, which returns the same type).
        BigRat {
            // JSON's own number syntax `int[.frac]`, PLUS the exact-rational
            // surface `num/den` that the `BigRat` carrier DISPLAYS (`3.14` prints
            // as `157/50`). Accepting both is what makes
            // `parse(display(t)) == t` hold for every `Value` — a superset of
            // JSON's number grammar, never a restriction of it.
            pattern: r"-?(0|[1-9][0-9]*)(\.[0-9]+)?(/-?(0|[1-9][0-9]*))?";
            eval: ![ {
                match text.split_once('/') {
                    // Exact-rational form `num/den` (the carrier's display form).
                    Some((num_txt, den_txt)) => {
                        match (
                            num_bigint::BigInt::parse_bytes(num_txt.as_bytes(), 10),
                            num_bigint::BigInt::parse_bytes(den_txt.as_bytes(), 10),
                        ) {
                            (Some(n), Some(d)) if !num_traits::Zero::is_zero(&d) => {
                                Ok(mettail_prattail::RationalLit(num_rational::Ratio::new(n, d)))
                            },
                            _ => Err(()),
                        }
                    },
                    // JSON form: `int` or `int.frac`, read EXACTLY as
                    // `digits(int ++ frac) / 10^len(frac)` — no binary floating
                    // point ever enters the term algebra (`3.14` is exactly
                    // 157/50, not 3.140000000000000124…).
                    None => match text.split_once('.') {
                        None => match num_bigint::BigInt::parse_bytes(text.as_bytes(), 10) {
                            Some(n) => Ok(mettail_prattail::RationalLit(num_rational::Ratio::new(
                                n,
                                num_bigint::BigInt::from(1u8),
                            ))),
                            None => Err(()),
                        },
                        Some((int_part, frac)) => {
                            let mut digits = String::with_capacity(text.len());
                            digits.push_str(int_part);
                            digits.push_str(frac);
                            let mut den = String::with_capacity(text.len());
                            den.push('1');
                            for _ in 0..frac.len() {
                                den.push('0');
                            }
                            match (
                                num_bigint::BigInt::parse_bytes(digits.as_bytes(), 10),
                                num_bigint::BigInt::parse_bytes(den.as_bytes(), 10),
                            ) {
                                (Some(n), Some(d)) => Ok(mettail_prattail::RationalLit(
                                    num_rational::Ratio::new(n, d),
                                )),
                                _ => Err(()),
                            }
                        },
                    },
                }
            } ]
        }
        Str {
            pattern: r#""([^"\\]|\\.)*""#;
            eval: ![ {
                if text.len() < 2 {
                    Err(())
                } else {
                    let inner = &text[1..text.len() - 1];
                    Ok(inner.replace("\\\"", "\"").replace("\\\\", "\\"))
                }
            } ]
        }
    },

    terms {
        JNull . Value ::= "null" ;
        JBool . b:Bool |- b : Value ;
        JNum . n:BigRat |- n : Value ;
        JStr . s:Str |- s : Value ;
        // `"[" List(Value) "]"` and `"{" List(Field) "}"` — the delimited,
        // comma-separated, ORDERED collections, each realized as the three arity
        // cases of one production over a `Vec(…)` slot (the `rhocalc.rs:196-204`
        // `POutput` / `POutput2Plus` idiom). Each triple's union is exactly the
        // language the paper's production denotes: zero, one, or n elements
        // between the delimiters. See the module header for why the single-rule
        // spellings do not survive codegen.
        JArrEmpty . |- "[" "]" : Value ;
        JArr1 . v:Value |- "[" v "]" : Value ;
        JArr . v:Value, vs:Vec(Value) |- "[" v "," vs.*sep(",") "]" : Value ;
        JObjEmpty . |- "{" "}" : Value ;
        JObj1 . f:Field |- "{" f "}" : Value ;
        JObj . f:Field, fs:Vec(Field) |- "{" f "," fs.*sep(",") "}" : Value ;
        Field . k:Str, v:Value |- k ":" v : Field ;
    },

    equations { },

    rewrites { },
}
