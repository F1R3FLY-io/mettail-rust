//! **The corpus harvester** — turns a proptest counterexample corpus into promoted
//! `#[test]` source.
//!
//! # What it does
//!
//! For every `cc <seed> # shrinks to <text>` entry in a corpus it:
//!
//! 1. parses the `# shrinks to` text with [`mettail_testkit::ctor::parse_shrinks_to`];
//! 2. SEARCHES for the term's category — the corpus records no category and no test name,
//!    because `FileFailurePersistence::Direct` pins ONE corpus per LANGUAGE and all seven
//!    generated property tests of that language share it. The search tries every category
//!    the schema declares and keeps the ones under which the whole term emits without
//!    error;
//! 3. prints a `#[test]` carrying the constructor source, the recorded text as a literal
//!    oracle, and the property assertions.
//!
//! # Why the search has an exact oracle even though the corpus records nothing
//!
//! Emission is TYPE-DIRECTED: a category is accepted only if every constructor in the term,
//! at every depth, is declared by the category the schema says that position has. A wrong
//! guess fails at the first mismatched position, not silently. And whatever survives is
//! checked again, harder, by the emitted test itself — assertion 2 constructs the term and
//! requires its normalised `Debug` to equal the recorded text character for character. A
//! wrong category that somehow type-checked would still produce different text.
//!
//! # Usage
//!
//! ```text
//! harvest_proptest_corpus <schema.rs> <corpus> [--category C] [--module-doc TEXT]
//! ```
//!
//! `<schema.rs>` is `target/generated/<lang>/rust_ctor.rs`. Output goes to stdout, ready to
//! paste into a tracked test file under `languages/tests/`.
//!
//! # Why the output is pasted rather than written
//!
//! Task #69's G1 (`macros/tests/generated_output_locality.rs`) asserts that the set of
//! MACRO-authored files outside `target/` is empty. This tool is not the macro, and what it
//! prints is a proposal a human reads, edits and commits — a promoted regression test is a
//! deliberate, reviewed artifact, not build output. Writing it automatically would recreate
//! exactly the "the build mutates tracked files" problem G1 exists to prevent.

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;

use mettail_testkit::ctor::{canonicalize_debug, emit_category, parse_shrinks_to, Schema};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "usage: {} <target/generated/<lang>/rust_ctor.rs> <corpus.proptest-regressions> \
             [--category C]",
            args.first()
                .map(String::as_str)
                .unwrap_or("harvest_proptest_corpus")
        );
        return ExitCode::from(2);
    }

    let schema_path = &args[1];
    let corpus_path = &args[2];
    let forced_category = args
        .iter()
        .position(|a| a == "--category")
        .and_then(|i| args.get(i + 1))
        .cloned();

    let schema_text = match fs::read_to_string(schema_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read the schema at {schema_path}: {e}");
            eprintln!(
                "it is written by the `rust_ctor` pass during macro expansion; build the \
                 language once (`cargo build -p languages`) and it will be there"
            );
            return ExitCode::from(2);
        },
    };
    let schema = match Schema::parse(&schema_text) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot parse the schema at {schema_path}: {e}");
            return ExitCode::from(2);
        },
    };

    let corpus = match fs::read_to_string(corpus_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read the corpus at {corpus_path}: {e}");
            return ExitCode::from(2);
        },
    };

    let entries: Vec<(&str, &str)> = corpus
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("cc ")?;
            let (seed, comment) = rest.split_once(" # shrinks to ")?;
            Some((seed.trim(), comment.trim()))
        })
        .collect();

    println!(
        "// ── {} — {} corpus entr{} ──",
        schema.language,
        entries.len(),
        if entries.len() == 1 { "y" } else { "ies" }
    );
    println!("// schema: {schema_path}");
    println!("// corpus: {corpus_path}");
    println!();

    let mut resolved = 0usize;
    let mut unresolved: Vec<(usize, &str, Vec<String>)> = Vec::new();
    // Constructors that no category declares — the Tier-3 candidates.
    let mut absent_constructors: BTreeMap<String, usize> = BTreeMap::new();

    for (index, (seed, text)) in entries.iter().enumerate() {
        let bindings = match parse_shrinks_to(text) {
            Ok(b) => b,
            Err(e) => {
                unresolved.push((
                    index,
                    seed,
                    vec![format!("cannot parse the recorded text: {e}")],
                ));
                continue;
            },
        };

        // The single-binding case is the generated property tests' shape (`term = …`). A
        // multi-binding entry comes from a hand-written `proptest!` with several arguments
        // and is reported rather than guessed at.
        if bindings.len() != 1 || bindings[0].name != "term" {
            unresolved.push((
                index,
                seed,
                vec![format!(
                    "the entry binds {:?}, which is a hand-written multi-argument property \
                     rather than a generated `term in arb_<cat>(d)` — promote it by hand",
                    bindings.iter().map(|b| b.name.as_str()).collect::<Vec<_>>()
                )],
            ));
            continue;
        }
        let node = &bindings[0].value;

        let candidates: Vec<String> = match &forced_category {
            Some(c) => vec![c.clone()],
            None => schema
                .categories()
                .into_iter()
                .map(str::to_string)
                .collect(),
        };

        let mut hits: Vec<(String, String)> = Vec::new();
        let mut misses: Vec<String> = Vec::new();
        for category in &candidates {
            match emit_category(&schema, category, node) {
                Ok(source) => hits.push((category.clone(), source)),
                Err(e) => {
                    if let mettail_testkit::ctor::EmitError::UnknownConstructor { label } = &e {
                        *absent_constructors.entry(label.clone()).or_insert(0) += 1;
                    }
                    misses.push(format!("{category}: {e}"));
                },
            }
        }

        match hits.len() {
            0 => unresolved.push((index, seed, misses)),
            _ => {
                resolved += 1;
                emit_test(index, seed, text, &hits);
            },
        }
    }

    eprintln!(
        "── {} — {} of {} entries emitted, {} unresolved ──",
        schema.language,
        resolved,
        entries.len(),
        unresolved.len()
    );
    for (index, seed, reasons) in &unresolved {
        eprintln!("  entry {index} (cc {}…):", &seed[..seed.len().min(12)]);
        // Only the most informative few reasons: with a dozen categories the full list is
        // noise, and the informative failure is always the one that got furthest.
        for reason in reasons.iter().take(4) {
            eprintln!("      {reason}");
        }
    }
    if !absent_constructors.is_empty() {
        eprintln!(
            "── constructors that NO category declares (Tier-3 candidates: these have left \
             the grammar) ──"
        );
        for (label, count) in &absent_constructors {
            eprintln!("  {label} (blocked {count} category attempt(s))");
        }
    }

    ExitCode::SUCCESS
}

fn emit_test(index: usize, seed: &str, recorded: &str, hits: &[(String, String)]) {
    let (category, source) = &hits[0];
    // `term = ` is the proptest binding prefix; the ORACLE is the value text alone.
    let value_text = recorded.strip_prefix("term = ").unwrap_or(recorded);
    let oracle = canonicalize_debug(value_text);

    println!("/// Corpus entry {index} — seed `cc {seed}`.");
    println!("///");
    if hits.len() > 1 {
        println!(
            "/// ⚠ The term emits under {} categories: {}. `{category}` is used; the \
             others are listed so the choice is visible rather than silent.",
            hits.len(),
            hits.iter()
                .map(|(c, _)| c.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!("///");
    }
    println!("/// Recorded counterexample, verbatim from the corpus:");
    println!("/// ```text");
    for chunk in wrap(recorded, 92) {
        println!("/// {chunk}");
    }
    println!("/// ```");
    println!("#[test]");
    println!("fn corpus_{index}_{}() {{", category.to_lowercase());
    println!("    mettail_runtime::clear_var_cache();");
    println!("    // 1 — the term CONSTRUCTS.");
    println!("    let term: {category} = {source};");
    println!();
    println!("    // 2 — ANTI-VACUITY. The reconstructed term's normalised Debug must equal the");
    println!("    //     text the corpus recorded, character for character. This is what makes");
    println!("    //     \"passes because it built the wrong term\" impossible. Only");
    println!("    //     `UniqueId(n)` and the ORDER of hash-container entries are quotiented");
    println!("    //     out, and both are properties of the PROCESS rather than of the term:");
    println!("    //     `UniqueId` comes from a global counter (and `FreeVar` equality is by");
    println!("    //     unique_id alone, with the name fixing the identity through the var");
    println!("    //     cache), and a `HashBag` is a multiset whose `PartialEq` ignores order.");
    println!("    let recorded = {};", rust_str_literal(&oracle));
    println!("    assert_eq!(");
    println!("        canonicalize_debug(&format!(\"{{:?}}\", term)),");
    println!("        recorded,");
    println!("        \"the reconstructed term is not the recorded counterexample\"");
    println!("    );");
    println!();
    println!("    // 3 — the properties the corpus's generated suite checks for this category.");
    println!("    let _ = format!(\"{{:?}}\", term);            // <cat>_debug_does_not_panic");
    println!("    let _ = format!(\"{{}}\", term);              // <cat>_display_does_not_panic");
    println!("    assert_eq!(term.clone(), term);           // <cat>_clone_eq");
    println!("}}");
    println!();
}

/// A Rust string literal for `s`, escaped explicitly.
fn rust_str_literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Split `text` into chunks of at most `width` characters at whitespace, for doc comments.
fn wrap(text: &str, width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut current = String::with_capacity(width + 16);
    for word in text.split(' ') {
        if !current.is_empty() && current.chars().count() + 1 + word.chars().count() > width {
            lines.push(std::mem::take(&mut current));
        }
        if !current.is_empty() {
            current.push(' ');
        }
        current.push_str(word);
    }
    if !current.is_empty() {
        lines.push(current);
    }
    lines
}
