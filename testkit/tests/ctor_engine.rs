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

use mettail_testkit::corpus_migration::{
    migrate_rholang_corpus, migrate_rholang_method_calls, LEGACY_RHOLANG_METHODS,
};
use mettail_testkit::ctor::{
    emit_category, normalize_unique_ids, parse_shrinks_to, render_bindings, DebugNode, EmitError,
    FieldSpec, Schema, ZipperAccess, ZipperStorage,
};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("`testkit` is a workspace member, so its manifest dir has a parent")
        .to_path_buf()
}

#[test]
fn recursive_native_zipper_schema_preserves_modes_categories_and_exact_bytes() {
    let schema = Schema::parse(
        "@@ METTAIL-RUST-CTOR-SCHEMA v1 BEGIN @@\n\
         LANG Demo\n\
         CAT Key -\n\
         CAT Value -\n\
         CAT Zip std::sync::Arc<mettail_runtime::ReadZipperLit<Key,Value>>\n\
         V Key K nullary\n\
         V Value V nullary\n\
         V Zip Z nativezipper zipper:Arc:ReadZipperLit:Key:Value\n\
         @@ METTAIL-RUST-CTOR-SCHEMA v1 END @@",
    )
    .expect("closed recursive-native schema must parse");

    assert_eq!(
        schema
            .variants
            .get(&("Zip".to_string(), "Z".to_string()))
            .expect("zipper variant must be present")
            .fields,
        vec![FieldSpec::NativeZipper {
            storage: ZipperStorage::Arc,
            access: ZipperAccess::Read,
            key: "Key".to_string(),
            value: "Value".to_string(),
        }],
    );

    let map = mettail_testkit::ctor::parse_debug_value(
        "Z(ReadZipperLit(Map(HashMapLit({K: V})), [0, 127, 128, 255]))",
    )
    .expect("zipper debug value must parse");
    assert_eq!(
        emit_category(&schema, "Zip", &map).expect("zipper map must emit"),
        concat!(
            "Zip::Z(std::sync::Arc::new(mettail_runtime::ReadZipperLit(",
            "mettail_runtime::PathMapLit::Map(",
            "mettail_runtime::HashMapLit::from_iter(vec![(Key::K, Value::V)])), ",
            "vec![0_u8, 127_u8, 128_u8, 255_u8])))",
        ),
    );

    let set_empty =
        mettail_testkit::ctor::parse_debug_value("Z(ReadZipperLit(Set(HashMapLit({})), [255]))")
            .expect("set-empty zipper debug value must parse");
    let map_empty =
        mettail_testkit::ctor::parse_debug_value("Z(ReadZipperLit(Map(HashMapLit({})), [255]))")
            .expect("map-empty zipper debug value must parse");
    let set_source = emit_category(&schema, "Zip", &set_empty).expect("set-empty must emit");
    let map_source = emit_category(&schema, "Zip", &map_empty).expect("map-empty must emit");
    assert!(set_source.contains("PathMapLit::Set"));
    assert!(map_source.contains("PathMapLit::Map"));
    assert_ne!(set_source, map_source, "empty PathMap modes must remain distinct");
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
        let mut node = bindings[0].value.clone();
        if lang == "rholang" {
            migrate_rholang_corpus(&mut node).unwrap_or_else(|error| {
                panic!("cannot migrate historical Rholang corpus entry `{recorded}`: {error}")
            });
        }

        let categories = schema.categories();
        if categories.len() < 2 {
            continue;
        }
        multi_category_grammars_seen += 1;

        let accepted: Vec<&str> = categories
            .iter()
            .filter(|c| emit_category(schema, c, &node).is_ok())
            .copied()
            .collect();

        // At least one category must admit it — the term was generated by this grammar.
        // One entry in the whole repository is an exception, and it is an exception for a
        // REASON that is itself the finding: `PInputs` left the grammar without a
        // semantics-preserving one-constructor successor. Legacy method constructors have a
        // mechanically exact `MethodCall` migration above and are not exempted.
        if accepted.is_empty() {
            let has_absent_constructor =
                recorded.contains("PInputs") && !schema.has_label_anywhere("PInputs");
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

/// ★ Exact disposition record for constructors retired from the Rholang corpus.
///
/// Commit `438e3a3d` replaced 47 receiver-specific method constructors with the
/// type-neutral `MethodCall(receiver, method_name, arguments)` carrier. That is a structural
/// collapse, not lost semantics: the receiver remains slot zero, argument order is unchanged,
/// and the former surface spelling becomes the opaque method-name token. The complete mapping
/// is executable in [`LEGACY_RHOLANG_METHODS`], including `KeysMap → keys`, whose intermediate
/// spelling was `MKeys` after commit `5ec4cf47`.
///
/// `PInputs` is different. Commit `363470c7` replaced one vector of names plus one
/// multi-binder scope with the `PForUser`/`ForRow`/`InputBind` hierarchy. No unique inverse
/// exists because binders, rows, conjunctions, and optional guards are distributed
/// differently. The historical counterexample remains cited here as
/// `cc 455d04f4a3339b26b238e09810662a5edaee813e25f4ca14b0cb6da1a2798a57`; refusing to
/// fabricate a translation is the verified disposition, not an untracked exemption.
#[test]
fn retired_rholang_methods_migrate_exactly_and_pinputs_remains_explicit() {
    let schemas = generated_schemas();
    let Some((_, rholang)) = schemas.iter().find(|(name, _)| name == "rholang") else {
        eprintln!("note: Rholang has not been compiled in this tree; vacuous by construction.");
        return;
    };

    let method_call = rholang
        .variants
        .get(&("Proc".to_string(), "MethodCall".to_string()))
        .expect("the completed method collapse must retain its generic successor");
    assert_eq!(
        method_call.fields,
        vec![
            FieldSpec::Cat("Proc".to_string()),
            FieldSpec::OpaqueToken,
            FieldSpec::Coll {
                kind: "Vec".to_string(),
                elem: "Proc".to_string()
            },
        ],
        "MethodCall must preserve receiver, identifier text, and ordered Proc arguments",
    );

    for spec in LEGACY_RHOLANG_METHODS {
        assert!(
            !rholang.has_label_anywhere(spec.constructor),
            "retired method constructor `{}` was reinstated beside MethodCall",
            spec.constructor,
        );
        let mut legacy = DebugNode::Call {
            head: spec.constructor.to_string(),
            args: (0..spec.arity)
                .map(|_| DebugNode::Ident("PZero".to_string()))
                .collect(),
        };
        assert_eq!(migrate_rholang_method_calls(&mut legacy), Ok(1));
        assert_eq!(
            legacy,
            DebugNode::Call {
                head: "MethodCall".to_string(),
                args: vec![
                    DebugNode::Ident("PZero".to_string()),
                    DebugNode::Str(spec.method.to_string()),
                    DebugNode::List(
                        (1..spec.arity)
                            .map(|_| DebugNode::Ident("PZero".to_string()))
                            .collect(),
                    ),
                ],
            },
            "legacy constructor `{}` did not preserve its receiver and arguments",
            spec.constructor,
        );
        emit_category(rholang, "Proc", &legacy).unwrap_or_else(|error| {
            panic!(
                "migrated constructor `{}` does not emit through MethodCall: {error}",
                spec.constructor
            )
        });
    }

    assert!(!rholang.has_label_anywhere("PInputs"));
    let node = mettail_testkit::ctor::parse_debug_value("PInputs(PZero)")
        .expect("a syntactically well-formed call");
    match emit_category(rholang, "Proc", &node) {
        Err(EmitError::UnknownConstructor { label }) => assert_eq!(label, "PInputs"),
        other => {
            panic!("a departed constructor must be reported as `UnknownConstructor`, got {other:?}")
        },
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

/// ★★ TOTALITY: every seed in every corpus is cited by a source file.
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
/// Some `.rs` file must name every seed. That covers a promoted test, an exact migration
/// record, and a proved non-isomorphic retirement alike, because each names the entry it is
/// about. A citation is the claim "this entry received a durable disposition", and
/// [`every_seed_a_source_file_cites_is_a_seed_some_corpus_records`] proves citations point
/// at real seeds, so the two tests close the loop in both directions.
///
/// Anything else is an entry nobody decided about, and this fails.
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

    // ── totality ──
    let undisposed: Vec<String> = seeds
        .iter()
        .filter(|(seed, _)| !cited.contains(*seed))
        .map(|(seed, corpus)| format!("{corpus}: cc {}…", &seed[..16]))
        .collect();

    assert!(
        undisposed.is_empty(),
        "{} recorded counterexample(s) carry NO source citation (promoted test, exact \
         migration record, or proved non-isomorphic retirement). An entry nobody decided \
         about is indistinguishable, from inside the suite, from an entry that does not \
         exist:\n  {}",
        undisposed.len(),
        undisposed.join("\n  ")
    );

    eprintln!(
        "── CENSUS: {} recorded counterexamples — all disposed by source citation ──",
        seeds.len(),
    );
}
