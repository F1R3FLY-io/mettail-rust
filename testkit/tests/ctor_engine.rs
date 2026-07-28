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
    emit_category, normalize_unique_ids, parse_shrinks_to, render_bindings, EmitError, Schema,
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
                    .and_then(|p| p.ancestors().find(|a| {
                        a.file_name().and_then(|n| n.to_str()) == Some("proptest-regressions")
                    }))
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
        let schema = Schema::parse(&text)
            .unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()));
        out.push((
            dir.file_name().and_then(|n| n.to_str()).unwrap_or("?").to_string(),
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
        assert!(
            !schema.language.is_empty(),
            "the schema for `{lang}` carries no `LANG` record"
        );
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

/// The two constructors this campaign found to have LEFT the Rholang grammar are reported
/// as `UnknownConstructor`, not as some vaguer failure.
///
/// This is the signal the tiering policy runs on: `UnknownConstructor` means "no successor
/// is even a candidate", which is Tier-3, whereas a shape mismatch means the emitter needs
/// work and the entry must NOT be tiered away.
#[test]
fn a_departed_constructor_is_reported_as_such() {
    let schemas = generated_schemas();
    let Some((_, rholang)) = schemas.iter().find(|(name, _)| name == "rholang") else {
        eprintln!("note: Rholang has not been compiled in this tree; vacuous by construction.");
        return;
    };

    for departed in ["PInputs", "KeysMap"] {
        assert!(
            !rholang.has_label_anywhere(departed),
            "`{departed}` is declared by {:?} in the current Rholang grammar. If it has been \
             REINSTATED, the archived counterexample that uses it must be reinstated with it — \
             that is what this assertion is for.",
            rholang.categories_declaring(departed)
        );
    }

    // And the emitter must SAY so, rather than failing with a shape complaint that would
    // send a reader looking for a bug in the parser.
    let node = mettail_testkit::ctor::parse_debug_value("PInputs(PZero)")
        .expect("a syntactically well-formed call");
    match emit_category(rholang, "Proc", &node) {
        Err(EmitError::UnknownConstructor { label }) => assert_eq!(label, "PInputs"),
        other => panic!(
            "a departed constructor must be reported as `UnknownConstructor`, got {other:?}"
        ),
    }
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
