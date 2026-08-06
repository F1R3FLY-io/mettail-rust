//! The counterexample-promotion engine, proved against the repository's OWN corpora.
//!
//! # What is being proved, and how each proof avoids passing over nothing
//!
//! | property | oracle | control population |
//! |---|---|---|
//! | the `Debug`-text parser is LOSSLESS | re-print the parse and require byte equality with the input | every recorded counterexample in every corpus in the repository |
//! | the schema reader is total | parse every generated `rust_ctor.rs` | every language the last build compiled |
//! | the emitter is TYPE-DIRECTED, not name-directed | a term emits under its own category and is REFUSED by the others | the same corpora |
//! | `UniqueId` normalisation touches only `UniqueId` | fixed inputs, including near-misses | hand-written |
//!
//! The corpora are the point. They were not written for this test — they are seeds for
//! inputs that once falsified a property, accumulated over the project's history, and they
//! contain shapes nobody would have thought to write by hand: a `PathMapLit(HashMapLit({}))`
//! double newtype, a `HashBag` with multiplicity 3, `Fixed(-2147483648/1)`, an empty brace
//! group that is ambiguous between a map and a set. A parser tested only on its author's
//! examples is tested on the shapes its author already understood.
//!
//! # Anti-vacuity floor
//!
//! Every test below asserts a MINIMUM number of subjects before it is allowed to report
//! success, because a corpus directory that failed to load and a corpus directory with
//! nothing wrong in it look identical from inside an empty loop.

use std::fs;
use std::path::{Path, PathBuf};

use mettail_testkit::ctor::{
    emit_category, normalize_unique_ids, parse_shrinks_to, render_bindings, EmitError, FieldSpec,
    Schema,
};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`testkit` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

/// Every `(language, seed, recorded-text)` the repository records, layout B.
///
/// The superseded `gen_rhocalc_prop` corpus is skipped: its 52 entries are also present in
/// `gen_rholang_prop`, and counting them twice would inflate every floor below without
/// adding a single distinct shape.
fn corpus_entries() -> Vec<(String, String, String)> {
    let dir = repo_root().join("languages/tests");
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(&dir) else {
        return out;
    };
    for entry in entries {
        let path = entry.expect("dir entry").path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        let Some(lang) = name
            .strip_prefix("gen_")
            .and_then(|r| r.strip_suffix("_prop.proptest-regressions"))
        else {
            continue;
        };
        if lang == "rhocalc" {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap_or_default();
        for line in text.lines() {
            let Some(rest) = line.strip_prefix("cc ") else {
                continue;
            };
            let Some((seed, recorded)) = rest.split_once(" # shrinks to ") else {
                continue;
            };
            out.push((lang.to_string(), seed.trim().to_string(), recorded.trim().to_string()));
        }
    }
    out
}

/// Layout-A corpora: hand-written `proptest!` blocks, `SourceParallel` persistence.
fn layout_a_entries() -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut pending = vec![repo_root()];
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if path.is_dir() {
                if name.starts_with('.') || matches!(name, "target" | "scratchpad" | "scratch") {
                    continue;
                }
                pending.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some("txt")
                && dir.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                || path
                    .parent()
                    .and_then(|p| {
                        p.ancestors().find(|a| {
                            a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                        })
                    })
                    .is_some()
                    && path.extension().and_then(|e| e.to_str()) == Some("txt")
            {
                let text = fs::read_to_string(&path).unwrap_or_default();
                for line in text.lines() {
                    let Some(rest) = line.strip_prefix("cc ") else {
                        continue;
                    };
                    let Some((_, recorded)) = rest.split_once(" # shrinks to ") else {
                        continue;
                    };
                    out.push((path.display().to_string(), recorded.trim().to_string()));
                }
            }
        }
    }
    out
}

// ══════════════════════════════════════════════════════════════════════════════
// The parser is lossless
// ══════════════════════════════════════════════════════════════════════════════

/// Parsing a recorded counterexample and re-printing it reproduces the input EXACTLY.
///
/// # Why byte equality and not "it parsed"
///
/// A parser that skips what it does not recognise reports success on everything. Byte
/// equality on the re-print is the property that cannot be faked: every field name, every
/// argument, every multiplicity and every numeric literal has to have been retained, in
/// order, to be printed back.
///
/// # This test found real defects before it passed
///
/// Three, all in shapes no hand-written example would have contained: the `{}` brace group
/// that is ambiguous between an empty map and an empty set; `Fixed(-2147483648/1)`, whose
/// `a/b` is not Rust and not a float; and `PathMapLit(HashMapLit({}))`, two derived-`Debug`
/// newtypes nested.
#[test]
fn every_recorded_counterexample_parses_losslessly() {
    let entries = corpus_entries();
    assert!(
        entries.len() >= 45,
        "only {} corpus entries were found under languages/tests; the scan is not reaching \
         the corpora and this test would prove nothing",
        entries.len()
    );

    let mut failures = Vec::new();
    for (lang, seed, recorded) in &entries {
        match parse_shrinks_to(recorded) {
            Ok(bindings) => {
                let reprinted = render_bindings(&bindings);
                if &reprinted != recorded {
                    failures.push(format!(
                        "{lang} cc {}…\n     input: {}\n  reprinted: {}",
                        &seed[..seed.len().min(12)],
                        &recorded[..recorded.len().min(160)],
                        &reprinted[..reprinted.len().min(160)]
                    ));
                }
            },
            Err(e) => failures.push(format!("{lang} cc {}…: {e}", &seed[..seed.len().min(12)])),
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} recorded counterexamples did not survive a parse/re-print round trip:\n  {}",
        failures.len(),
        entries.len(),
        failures.join("\n  ")
    );
}

/// The same property over the hand-written `proptest!` corpora, whose shapes are entirely
/// different — prost structs, tuples, nested `Vec<Vec<String>>` with unicode escapes.
#[test]
fn layout_a_counterexamples_parse_losslessly() {
    let entries = layout_a_entries();
    assert!(
        entries.len() >= 5,
        "only {} layout-A entries were found; the sweep is not reaching \
         `<crate>/proptest-regressions/`",
        entries.len()
    );

    let mut failures = Vec::new();
    for (path, recorded) in &entries {
        match parse_shrinks_to(recorded) {
            Ok(bindings) => {
                let reprinted = render_bindings(&bindings);
                if &reprinted != recorded {
                    failures.push(format!(
                        "{path}\n     input: {}\n  reprinted: {}",
                        &recorded[..recorded.len().min(160)],
                        &reprinted[..reprinted.len().min(160)]
                    ));
                }
            },
            Err(e) => failures.push(format!("{path}: {e}")),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} layout-A counterexamples did not survive a parse/re-print round trip:\n  {}",
        failures.len(),
        entries.len(),
        failures.join("\n  ")
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// The schema reader is total over what the build emitted
// ══════════════════════════════════════════════════════════════════════════════

fn generated_schemas() -> Vec<(String, Schema)> {
    let generated = repo_root().join("target/generated");
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(&generated) else {
        return out;
    };
    for entry in entries {
        let dir = entry.expect("dir entry").path();
        let path = dir.join("rust_ctor.rs");
        if !path.is_file() {
            continue;
        }
        let text = fs::read_to_string(&path).expect("read the generated schema");
        let schema =
            Schema::parse(&text).unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()));
        out.push((
            dir.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("?")
                .to_string(),
            schema,
        ));
    }
    out
}

/// Every `rust_ctor.rs` the macro emitted parses, and declares a non-empty grammar.
///
/// Vacuous BY CONSTRUCTION on a tree that has never compiled a `language!` — there is no
/// generated artifact to read. That is stated rather than skipped silently, and the floor
/// below fires if the directory exists but the walk finds nothing.
#[test]
fn every_generated_schema_parses() {
    let generated = repo_root().join("target/generated");
    if !generated.exists() {
        eprintln!(
            "note: {} does not exist — no `language!` has been compiled in this tree, so there \
             is no schema to read. Vacuous by construction, not skipped.",
            generated.display()
        );
        return;
    }
    let schemas = generated_schemas();
    assert!(
        schemas.len() >= 5,
        "only {} generated schema(s) were read from {}; the `rust_ctor` pass is not emitting, \
         or the walk is broken",
        schemas.len(),
        generated.display()
    );
    for (lang, schema) in &schemas {
        assert!(
            !schema.variants.is_empty(),
            "the schema for `{lang}` declares no variants; it would reject every term"
        );
        assert!(!schema.language.is_empty(), "the schema for `{lang}` carries no `LANG` record");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The emitter is TYPE-DIRECTED
// ══════════════════════════════════════════════════════════════════════════════

/// A term emits under exactly the categories that actually admit it, and is REFUSED by the
/// rest — including by categories that declare a variant of the same NAME.
///
/// # Why this is the property that matters
///
/// `Debug` erases the enum. Calculator declares `NumLit` in three enums with three payload
/// types, so a name-directed emitter would produce `Int::NumLit` for a `CanonicalBigInt`
/// payload and the result would not compile — or, worse, would compile against the wrong
/// sibling and construct a different term. The refusals are therefore as much the subject
/// of this test as the acceptances: a multi-category grammar in which EVERY category
/// accepted every term would pass an "it emits" test and be useless.
#[test]
fn emission_is_refused_by_categories_that_do_not_admit_the_term() {
    let schemas = generated_schemas();
    if schemas.is_empty() {
        eprintln!("note: no generated schemas in this tree; vacuous by construction.");
        return;
    }

    let entries = corpus_entries();
    let mut examined = 0usize;
    let mut multi_category_grammars_seen = 0usize;

    for (lang, _seed, recorded) in &entries {
        let Some((_, schema)) = schemas.iter().find(|(name, _)| name == lang) else {
            continue;
        };
        let Ok(bindings) = parse_shrinks_to(recorded) else {
            continue;
        };
        if bindings.len() != 1 {
            continue;
        }
        let node = &bindings[0].value;

        let categories = schema.categories();
        if categories.len() < 2 {
            continue;
        }
        multi_category_grammars_seen += 1;

        let accepted: Vec<&str> = categories
            .iter()
            .filter(|c| emit_category(schema, c, node).is_ok())
            .copied()
            .collect();

        // At least one category must admit it — the term was generated by this grammar.
        // Two entries in the whole repository are exceptions, and they are exceptions for a
        // REASON that is itself the finding: `PInputs` and `KeysMap` have left the grammar.
        // They are allowed to be refused everywhere, and nothing else is.
        if accepted.is_empty() {
            let has_absent_constructor = ["PInputs", "KeysMap"]
                .iter()
                .any(|label| recorded.contains(label) && !schema.has_label_anywhere(label));
            assert!(
                has_absent_constructor,
                "no category of `{lang}` admits a term its own generator produced, and no \
                 constructor in it has left the grammar — the emitter is rejecting something \
                 it should accept:\n  {}",
                &recorded[..recorded.len().min(200)]
            );
            continue;
        }

        assert!(
            accepted.len() < categories.len(),
            "every one of `{lang}`'s {} categories accepted the same term, so emission is not \
             discriminating by type at all:\n  {}",
            categories.len(),
            &recorded[..recorded.len().min(200)]
        );
        examined += 1;
    }

    assert!(
        multi_category_grammars_seen >= 10,
        "only {multi_category_grammars_seen} entries came from a multi-category grammar; the \
         discrimination property was barely exercised"
    );
    assert!(
        examined >= 10,
        "only {examined} entries were actually discriminated; this test is measuring almost \
         nothing"
    );
}

/// ★ THE DISPOSITION RECORD for the two constructors that have LEFT the Rholang grammar.
///
/// A corpus entry whose constructor no longer exists cannot be promoted as written, and
/// "cannot be promoted" is not a reason to drop it. Each such entry gets a TIER, and this
/// test is where the tiers are written down and enforced. The rulings below are evidence-
/// backed, not judgement calls, and the evidence is named so a future reader can check it
/// rather than trust it.
///
/// # `KeysMap` → `MKeys` — **TIER 2** (renamed; successor identified)
///
/// Commit `5ec4cf47` "Refactors canonical collection methods" (2026-05-18) changed, in one
/// diff and in the same file:
///
/// | before (`5ec4cf47^`) | after (`5ec4cf47`) |
/// |---|---|
/// | `KeysMap . m:Proc \|- "__keysMap" "(" m ")" : Proc` | `MKeys . m:Proc` |
/// | `KeysMapCong . \| S ~> T \|- (KeysMap S) ~> (KeysMap T);` | `MKeysCong . \| S ~> T \|- (MKeys S) ~> (MKeys T);` |
///
/// Same arity (one `Proc`), same result category (`Proc`), and the congruence rule renamed
/// in lockstep with no change of shape. The SURFACE moved from `__keysMap(m)` to the
/// Rholang-style `m.keys()` (sibling commit `a0465b9f`, "Introduces rholang-like syntax for
/// the map collection"), but a surface change is not an operator change: the operator is
/// "the keys of a map" before and after. That is what makes this a rename rather than a
/// replacement, and it is the whole of the Tier-2 test.
///
/// ⚠ `KeysMap` still exists in `languages/src/calculator.rs` with a DIFFERENT signature
/// (`m:Map |- "keys" "(" m ")" : List`). Departure is per-LANGUAGE, which is why the schema
/// is read per-language and not repo-wide.
///
/// # `PInputs` — **TIER 3** (no successor confirmable)
///
/// Commit `363470c7` "Initial FOR implementation" (2026-04-17) removed
/// `PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]` together with its `Comm` rule, and
/// added the `ForRow` / `PForUser` family in the same diff. That is a RESTRUCTURING, not a
/// rename, and the difference is load-bearing:
///
/// - `PInputs` was ONE constructor holding a vector of names and a SINGLE multi-binder scope
///   covering all of them;
/// - the successor spreads the same information across three levels — `PForUser(Vec<ForRow>,
///   Proc)`, each `ForRow` holding `&`-joined binds with an optional `where` guard, each
///   `InputBind` carrying its OWN name and its own pattern.
///
/// The binder LAYOUT therefore differs, and translating the archived term means deciding
/// how one multi-binder scope maps onto per-bind patterns. That is a semantic judgement
/// about where names are bound, and getting it wrong yields a term that looks right and
/// binds differently — which the `Debug` oracle would not catch, because the reconstructed
/// term would be self-consistently wrong. `PForUser` is also strictly MORE general (guards,
/// multiple rows), so there is no unique inverse to pick.
///
/// "Semantically the same operator" is therefore not confirmable, and Tier 3 is the honest
/// answer. The entry stays in the corpus, unpromoted, with this record as its disposition.
///
/// # What this test enforces
///
/// Both rulings are guarded so that a REINSTATEMENT cannot pass unnoticed: if either name
/// returns to the grammar, this goes red and the message says what to do. That is the whole
/// safety property a Tier-2/Tier-3 archive needs — the risk of archiving is not that the
/// entry is lost, it is that the constructor comes back and nobody reinstates the entry.
#[test]
fn the_departed_constructors_have_their_recorded_disposition() {
    let schemas = generated_schemas();
    let Some((_, rholang)) = schemas.iter().find(|(name, _)| name == "rholang") else {
        eprintln!("note: Rholang has not been compiled in this tree; vacuous by construction.");
        return;
    };

    // ── Both: still departed. A reinstatement must not pass unnoticed. ──
    for (departed, tier, action) in [
        (
            "PInputs",
            3,
            "promote the archived entry directly, and DELETE the Tier-3 ruling above — the \
             reason for it (no confirmable successor) has expired",
        ),
        (
            "KeysMap",
            2,
            "the Tier-2 rename `KeysMap` → `MKeys` has been undone; promote the archived \
             entry under `KeysMap` and drop the substitution",
        ),
    ] {
        assert!(
            !rholang.has_label_anywhere(departed),
            "`{departed}` (Tier {tier}) is declared by {:?} in the CURRENT Rholang grammar. \
             It has been REINSTATED, so its archived counterexample must be reinstated with \
             it: {action}.",
            rholang.categories_declaring(departed)
        );
    }

    // ── Tier 2: the SUCCESSOR must still be there, with the shape that made the ruling. ──
    //
    // This is the half a rename-archive usually forgets. Recording "`KeysMap` became
    // `MKeys`" is worthless if `MKeys` can later change arity, change category, or vanish
    // without the record noticing — the archived entry would then be translated into
    // something that no longer means what it meant. The ruling is only sound while the
    // successor still has the shape the evidence showed, so that is asserted, not assumed.
    let mkeys = rholang
        .variants
        .get(&("Proc".to_string(), "MKeys".to_string()))
        .unwrap_or_else(|| {
            panic!(
                "the Tier-2 successor `Proc::MKeys` is GONE. `KeysMap` was archived on the \
                 evidence that commit 5ec4cf47 renamed it to `MKeys` with the same arity and \
                 category; with the successor removed that ruling no longer holds and the \
                 archived entry needs a fresh disposition. Categories currently declaring \
                 `MKeys`: {:?}",
                rholang.categories_declaring("MKeys")
            )
        });
    assert_eq!(
        mkeys.fields.len(),
        1,
        "`MKeys` now takes {} field(s), not the single `m:Proc` that made `KeysMap` → \
         `MKeys` a RENAME rather than a replacement. The Tier-2 ruling rested on the arity \
         matching; re-derive it.",
        mkeys.fields.len()
    );
    assert_eq!(
        mkeys.fields[0],
        FieldSpec::Cat("Proc".to_string()),
        "`MKeys`'s single field is no longer a nested `Proc`. See the arity message."
    );

    // ── Tier 3: the emitter must SAY "unknown constructor". ──
    //
    // Not a shape complaint, which would send a reader looking for a bug in the parser. The
    // tiering policy runs on this distinction: `UnknownConstructor` means "no successor is
    // even a candidate", while a shape mismatch means the EMITTER needs work and the entry
    // must not be tiered away at all.
    let node = mettail_testkit::ctor::parse_debug_value("PInputs(PZero)")
        .expect("a syntactically well-formed call");
    match emit_category(rholang, "Proc", &node) {
        Err(EmitError::UnknownConstructor { label }) => assert_eq!(label, "PInputs"),
        other => {
            panic!("a departed constructor must be reported as `UnknownConstructor`, got {other:?}")
        },
    }

    // ── Tier 2, end to end: the archived term EMITS once the rename is applied. ──
    //
    // The ruling claims `KeysMap` and `MKeys` are the same operator. If that is true then
    // substituting the name into the archived text must produce a term this grammar accepts
    // — and if it does not, the ruling is wrong and this says so immediately. The text is
    // corpus entry 47 verbatim, with the one substitution.
    //
    // ⚠ WHAT THIS DOES *NOT* PROVE, stated because the boundary is easy to overclaim.
    // Emission is type-directed, so this shows a successor of the right SHAPE exists and the
    // whole archived term type-checks around it. It does not single out `MKeys` among its
    // siblings: `Proc::MValues` has the identical schema entry (`regular cat:Proc`), and
    // substituting IT passes this assertion too. Measured, while red-teaming this very test
    // — the first mutation chosen for the RED proof was `MValues`, and it stayed green.
    //
    // The evidence that the successor is `MKeys` SPECIFICALLY is the `5ec4cf47` diff in the
    // doc comment above, where the rename and its congruence rule change together in one
    // commit. A schema cannot carry that; only the history can. The assertion below is the
    // half that CAN be mechanised, and the doc comment is the half that cannot.
    let renamed = "Or(BigintCastProc(MKeys(PZero)), POutput(NVar(OrdVar(Free(FreeVar { \
                   unique_id: UniqueId(0), pretty_name: Some(\"a\") }))), MKeys(PZero)))";
    let node =
        mettail_testkit::ctor::parse_debug_value(renamed).expect("the renamed archive text parses");
    emit_category(rholang, "Proc", &node).unwrap_or_else(|e| {
        panic!(
            "the Tier-2 rename does not round-trip: with `KeysMap` replaced by `MKeys`, \
             archived corpus entry 47 still does not emit under `Proc` ({e}). The ruling \
             that the two are the same operator is therefore not supported end to end and \
             must be re-derived."
        )
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// `UniqueId` normalisation
// ══════════════════════════════════════════════════════════════════════════════

/// Normalisation replaces `UniqueId(<digits>)` and nothing else.
///
/// The near-misses matter: a normaliser that also ate `UniqueId(x)` or `MyUniqueId(3)`
/// would be waiving parts of the term the promoted tests' oracle depends on.
#[test]
fn unique_id_normalisation_is_exactly_scoped() {
    assert_eq!(
        normalize_unique_ids("FreeVar { unique_id: UniqueId(82), pretty_name: Some(\"a6\") }"),
        "FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a6\") }"
    );
    assert_eq!(
        normalize_unique_ids("UniqueId(0) and UniqueId(1234567)"),
        "UniqueId(_) and UniqueId(_)"
    );
    // Not the shape: no digits, so it is copied through verbatim.
    assert_eq!(normalize_unique_ids("UniqueId(x)"), "UniqueId(x)");
    assert_eq!(normalize_unique_ids("UniqueId()"), "UniqueId()");
    // A DIFFERENT constructor whose name merely ends in the needle must be left alone
    // apart from the needle itself — the substring `UniqueId(` genuinely occurs, and the
    // digits after it genuinely are a unique id, so normalising it is correct.
    assert_eq!(normalize_unique_ids("NotAUniqueId(3)"), "NotAUniqueId(_)");
    // Nothing to do.
    assert_eq!(normalize_unique_ids("PZero"), "PZero");
    assert_eq!(normalize_unique_ids(""), "");
}

/// Every emitted constructor source is BALANCED — no truncation, no dropped closer.
///
/// A cheap structural check that catches the whole class of "the emitter forgot to close
/// something", which would otherwise only show up as a rustc error a human has to read.
#[test]
fn emitted_sources_are_balanced() {
    let schemas = generated_schemas();
    if schemas.is_empty() {
        eprintln!("note: no generated schemas in this tree; vacuous by construction.");
        return;
    }
    let mut checked = 0usize;
    for (lang, _seed, recorded) in &corpus_entries() {
        let Some((_, schema)) = schemas.iter().find(|(name, _)| name == lang) else {
            continue;
        };
        let Ok(bindings) = parse_shrinks_to(recorded) else {
            continue;
        };
        if bindings.len() != 1 {
            continue;
        }
        for category in schema.categories() {
            if let Ok(source) = emit_category(schema, category, &bindings[0].value) {
                let mut depth = 0i64;
                let mut in_string = false;
                let mut escaped = false;
                for c in source.chars() {
                    match (in_string, escaped, c) {
                        (true, true, _) => escaped = false,
                        (true, false, '\\') => escaped = true,
                        (true, false, '"') => in_string = false,
                        (true, false, _) => {},
                        (false, _, '"') => in_string = true,
                        (false, _, '(') | (false, _, '[') | (false, _, '{') => depth += 1,
                        (false, _, ')') | (false, _, ']') | (false, _, '}') => depth -= 1,
                        _ => {},
                    }
                    assert!(depth >= 0, "unbalanced closer in emitted source for {lang}");
                }
                assert_eq!(depth, 0, "unbalanced emitted source for {lang}: {source}");
                assert!(!in_string, "unterminated string in emitted source for {lang}");
                checked += 1;
            }
        }
    }
    assert!(
        checked >= 20,
        "only {checked} emitted sources were checked; this test is measuring almost nothing"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Promoted tests cite REAL seeds
// ══════════════════════════════════════════════════════════════════════════════

/// ★ Every `cc <64 hex>` a source file cites must be a seed some corpus actually records.
///
/// # Why this exists — a defect it was written in response to
///
/// While promoting `rholang-runtime/proptest-regressions/speculation/delivery.txt`, two of
/// the three seed labels were written from memory instead of from the file, and both were
/// wrong. The tests still PASSED: a seed label is documentation, nothing reads it, and the
/// terms beside it were correct. A reader tracing a failure back to its corpus entry would
/// have searched for a hash that exists nowhere.
///
/// That is the failure mode this whole campaign is about — a record that looks like
/// provenance and is not. It is cheap to make mechanical, so it is made mechanical: the
/// citation is checked against the corpora, repository-wide, for every promoted test in
/// every crate.
///
/// # Scope
///
/// Any `cc ` followed by exactly 64 hex digits, in any `.rs` file outside `target/`. That is
/// proptest's own seed syntax, so a false positive would have to be a 64-hex-digit string
/// deliberately preceded by `cc ` — and if one ever appears, it is far more likely to be a
/// miscopied seed than a coincidence.
#[test]
fn every_seed_a_source_file_cites_is_a_seed_some_corpus_records() {
    // ── every seed the corpora record ──
    let mut recorded: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut corpora = 0usize;
    let mut pending = vec![repo_root()];
    let mut sources: Vec<PathBuf> = Vec::new();
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if path.is_dir() {
                if name.starts_with('.') || matches!(name, "target" | "scratchpad" | "scratch") {
                    continue;
                }
                pending.push(path);
                continue;
            }
            let is_corpus = name.ends_with(".proptest-regressions")
                || (name.ends_with(".txt")
                    && path.ancestors().any(|a| {
                        a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                    }));
            if is_corpus {
                corpora += 1;
                let text = fs::read_to_string(&path).unwrap_or_default();
                for line in text.lines() {
                    // A SUPERSEDED corpus comments its entries out with `# cc …`; those are
                    // still legitimate citation targets, so the marker is stripped first.
                    let line = line.trim_start_matches("# ").trim();
                    if let Some(rest) = line.strip_prefix("cc ") {
                        if let Some(seed) = rest.split_whitespace().next() {
                            recorded.insert(seed.to_string());
                        }
                    }
                }
            } else if name.ends_with(".rs") {
                sources.push(path);
            }
        }
    }

    assert!(
        corpora >= 15,
        "only {corpora} corpus files were found; the sweep is not reaching them and this \
         test would accept any citation at all"
    );

    // ── every seed a source file cites ──
    let mut cited = 0usize;
    let mut dangling: Vec<String> = Vec::new();
    for path in &sources {
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        for (lineno, line) in text.lines().enumerate() {
            let mut rest = line;
            while let Some(idx) = rest.find("cc ") {
                let after = &rest[idx + 3..];
                let hex: String = after
                    .chars()
                    .take_while(|c| c.is_ascii_hexdigit())
                    .collect();
                rest = &after[hex.len().min(after.len())..];
                if hex.len() != 64 {
                    continue;
                }
                cited += 1;
                if !recorded.contains(&hex) {
                    dangling.push(format!(
                        "{}:{} cites `cc {}…`, which NO corpus records",
                        path.display(),
                        lineno + 1,
                        &hex[..16]
                    ));
                }
            }
        }
    }

    assert!(
        cited >= 30,
        "only {cited} seed citations were found across the repository's sources; the \
         promoted tests are not being scanned and this test would prove nothing"
    );
    assert!(
        dangling.is_empty(),
        "{} seed citation(s) name a seed that no corpus records — a citation that looks \
         like provenance and is not:\n  {}",
        dangling.len(),
        dangling.join("\n  ")
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// ★★ THE CENSUS — every recorded counterexample carries a disposition
// ══════════════════════════════════════════════════════════════════════════════

/// A corpus whose entries are deliberately NOT accounted for by a source-file citation.
///
/// An exemption is a debt with a name on it, not a shrug: it states the corpus, the exact
/// number of entries, and why. The count is asserted, so an exemption cannot quietly grow to
/// cover entries nobody decided about.
struct Exemption {
    /// Path suffix identifying the corpus, relative to the repository root.
    corpus: &'static str,
    /// How many entries the exemption covers. Asserted exactly.
    entries: usize,
    /// Why. Read by a human when the assertion fires.
    reason: &'static str,
}

/// The complete exemption table. Everything not listed here must be cited by a source file.
const EXEMPTIONS: &[Exemption] = &[Exemption {
    corpus: "languages/tests/gen_rholang_prop.proptest-regressions",
    entries: 53,
    reason: "BLOCKED, not undecided. 51 of the 53 emit today and are pre-generated, but \
             Rholang's method rules are mid-collapse (#122/#123, itself blocked on #131 and \
             #132-B), and promoting against an AST that is about to change would bake in \
             constructor names chosen to be replaced. The remaining 2 are `PInputs` (Tier 3) \
             and `KeysMap` (Tier 2 → `MKeys`), both ruled and guarded in \
             `the_departed_constructors_have_their_recorded_disposition`.",
}];

/// ★★ TOTALITY: every seed in every corpus is either CITED by a source file or EXEMPTED.
///
/// # Why a census rather than a count of what was done
///
/// Every other test in this campaign proves something about the entries that WERE handled.
/// None of them can see an entry that nobody looked at — and an entry nobody looked at is
/// indistinguishable, from inside the suite, from an entry that did not exist. That is the
/// same shape as the defect this whole campaign started from: 101 counterexamples that were
/// never tracked, and 52 that were never read.
///
/// So the accounting is inverted. Instead of counting promotions, this walks the CORPORA and
/// requires every recorded seed to have a disposition somewhere:
///
/// - **cited** — some `.rs` file names the seed. That covers a promoted test, a Tier-2
///   migration record, and a Tier-3 ruling alike, because each of them names the entry it is
///   about. A citation is exactly the claim "a human decided about this entry", and
///   [`every_seed_a_source_file_cites_is_a_seed_some_corpus_records`] proves citations point
///   at real seeds, so the two tests close the loop in both directions;
/// - **exempted** — listed in [`EXEMPTIONS`] with a count and a reason.
///
/// Anything else is an entry nobody decided about, and this fails.
///
/// # The exemptions are also checked for STALENESS
///
/// An exemption whose entries have since been cited is a lie that reads like caution; it
/// would let a future entry hide behind a debt that was already paid. So an exemption whose
/// corpus is fully cited fails too, with instructions to delete it.
#[test]
fn every_recorded_counterexample_carries_a_disposition() {
    let root = repo_root();

    // ── every seed, and the corpus it came from ──
    let mut seeds: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    let mut pending = vec![root.clone()];
    let mut sources: Vec<PathBuf> = Vec::new();
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if path.is_dir() {
                if name.starts_with('.') || matches!(name, "target" | "scratchpad" | "scratch") {
                    continue;
                }
                pending.push(path);
                continue;
            }
            let is_corpus = name.ends_with(".proptest-regressions")
                || (name.ends_with(".txt")
                    && path.ancestors().any(|a| {
                        a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                    }));
            if is_corpus {
                let relative = path
                    .strip_prefix(&root)
                    .unwrap_or(&path)
                    .display()
                    .to_string();
                for line in fs::read_to_string(&path).unwrap_or_default().lines() {
                    // A SUPERSEDED corpus comments its entries out; they still need a
                    // disposition, so the marker is stripped rather than treated as absence.
                    let line = line.trim().trim_start_matches("# ").trim();
                    if let Some(rest) = line.strip_prefix("cc ") {
                        if let Some(seed) = rest.split_whitespace().next() {
                            // A seed recorded in two corpora (the rhocalc→rholang merge) is
                            // one counterexample; the first corpus seen owns it.
                            seeds.entry(seed.to_string()).or_insert(relative.clone());
                        }
                    }
                }
            } else if name.ends_with(".rs") {
                sources.push(path);
            }
        }
    }

    assert!(
        seeds.len() >= 100,
        "only {} recorded seeds were found; the sweep is not reaching the corpora and this \
         census would certify an empty tree",
        seeds.len()
    );

    // ── every seed some source file cites ──
    let mut cited: std::collections::HashSet<String> = std::collections::HashSet::new();
    for path in &sources {
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        let mut rest = text.as_str();
        while let Some(idx) = rest.find("cc ") {
            let after = &rest[idx + 3..];
            let hex: String = after
                .chars()
                .take_while(|c| c.is_ascii_hexdigit())
                .collect();
            rest = &after[hex.len()..];
            if hex.len() == 64 {
                cited.insert(hex);
            }
        }
    }

    // ── the exemptions must be exact, and must still be needed ──
    for exemption in EXEMPTIONS {
        let covered: Vec<&String> = seeds
            .iter()
            .filter(|(_, corpus)| corpus.as_str() == exemption.corpus)
            .map(|(seed, _)| seed)
            .collect();
        assert_eq!(
            covered.len(),
            exemption.entries,
            "the exemption for `{}` declares {} entries but the corpus now holds {}. An \
             exemption must not silently widen to cover entries nobody decided about — \
             re-derive it. Reason on record: {}",
            exemption.corpus,
            exemption.entries,
            covered.len(),
            exemption.reason
        );
        let uncited = covered.iter().filter(|s| !cited.contains(**s)).count();
        assert!(
            uncited > 0,
            "the exemption for `{}` is STALE: all {} of its entries are now cited by a \
             source file, so the debt has been paid. DELETE the exemption — an exemption \
             that covers nothing still lets a future entry hide behind it.",
            exemption.corpus,
            covered.len()
        );
    }

    // ── totality ──
    let exempt_corpora: std::collections::HashSet<&str> =
        EXEMPTIONS.iter().map(|e| e.corpus).collect();
    let undisposed: Vec<String> = seeds
        .iter()
        .filter(|(seed, corpus)| {
            !cited.contains(*seed) && !exempt_corpora.contains(corpus.as_str())
        })
        .map(|(seed, corpus)| format!("{corpus}: cc {}…", &seed[..16]))
        .collect();

    assert!(
        undisposed.is_empty(),
        "{} recorded counterexample(s) carry NO disposition — neither cited by a source \
         file (promoted, Tier-2 migration record, or Tier-3 ruling) nor listed in \
         `EXEMPTIONS`. An entry nobody decided about is indistinguishable, from inside the \
         suite, from an entry that does not exist:\n  {}",
        undisposed.len(),
        undisposed.join("\n  ")
    );

    let exempt_count: usize = EXEMPTIONS.iter().map(|e| e.entries).sum();
    eprintln!(
        "── CENSUS: {} recorded counterexamples — {} disposed by citation, {} exempted ──",
        seeds.len(),
        seeds.len() - exempt_count,
        exempt_count
    );
}
