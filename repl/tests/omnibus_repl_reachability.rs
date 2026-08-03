//! Task #22 — the four GSLT omnibus specs are reachable **from the REPL binary**.
//!
//! `e1bfcd38` promoted `Json` (L1), `Monoid` (L2), `Turing` (L9) and `Pi` (L11) from their own
//! test binaries into `languages/src/`, but the shipped registry stayed
//! `{lambda, ambient, rhocalc, calculator}` — so four production specs were reachable from
//! nothing but one test binary each. The USER ruled (2026-07-27) that they become REPL
//! backends; `repl/src/rho_backends.rs` and `repl/src/registry.rs` implement that.
//!
//! ## Why this file exists alongside `registry_exec.rs`
//!
//! `registry_exec.rs` asserts at the LIBRARY boundary: the wrappers install, the registry keys
//! resolve, each language parses its own surface. That is necessary and not sufficient —
//! it is all in-process, through `build_registry()`, and would keep passing if the shipped
//! binary never called it or shadowed the key. This file spawns `CARGO_BIN_EXE_repl` with the
//! language as its startup argument and reads what a person would see, which is the only
//! evidence that the change reached the SHIPPED BINARY's behaviour — the thing the ruling
//! actually changed.
//!
//! Each language gets the same three beats a user performs first: the REPL starts in it,
//! `languages` lists it, and a term of its own concrete syntax round-trips through the prompt.
#![cfg(feature = "rho-languages")]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The workspace root — `CARGO_MANIFEST_DIR` is `repl/`.
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("repl/ has a parent")
        .to_path_buf()
}

/// Start the REPL in `language`, run `script`, and return stdout and stderr concatenated —
/// a typed refusal is printed on stderr and the user sees one stream.
///
/// `NO_COLOR` keeps the transcript free of ANSI escapes so the assertions compare the text a
/// person reads. Dropping the stdin pipe closes it, and the REPL's read loop exits on EOF.
fn run_repl_in(language: &str, script: &[&str]) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_repl"))
        .arg(language)
        .current_dir(workspace_root())
        .env("NO_COLOR", "1")
        .env_remove("RUST_MIN_STACK")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|err| panic!("the repl binary must start for {language}: {err}"));
    {
        let mut stdin = child.stdin.take().expect("the repl reads piped stdin");
        for line in script {
            writeln!(stdin, "{line}").expect("the repl accepts a scripted command line");
        }
    }
    let output = child.wait_with_output().expect("the repl must exit on EOF");
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// The four specs, each with the REPL key a user types and a program in its own syntax.
///
/// The key is the LOWERCASED language name, because `LanguageRegistry::register` inserts under
/// `language.name().to_lowercase()`.
const SUBJECTS: [(&str, &str); 4] = [
    ("json", r#"{"a": 1}"#),
    ("monoid", "(e * a)"),
    ("pi", "{ in(c,y).0 | c!c.0 }"),
    ("turing", "(q0 , <[] | 0 | [0,1]>)"),
];

/// Beat 1 — `repl <language>` STARTS in that language.
///
/// Before task #22 this printed a "Language '<name>' not found" style failure for all four,
/// because `build_registry` never registered them.
#[test]
fn the_repl_binary_starts_in_each_omnibus_language() {
    for (key, _) in SUBJECTS {
        let transcript = run_repl_in(key, &[]);
        assert!(
            transcript.contains("Language loaded successfully"),
            "`repl {key}` must load the language; transcript was:\n{transcript}"
        );
        assert!(
            !transcript.contains("not found"),
            "`repl {key}` must not report an unknown language; transcript was:\n{transcript}"
        );
    }
}

/// Beat 2 — the language is DISCOVERABLE: `languages` lists it by name.
///
/// Reachability is not only "the key resolves if you already know it"; a user finds a language
/// by asking the REPL what it has.
#[test]
fn the_languages_command_lists_every_omnibus_spec() {
    let transcript = run_repl_in("json", &["languages"]);
    for (key, _) in SUBJECTS {
        let mut chars = key.chars();
        let display = match chars.next() {
            Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
            None => unreachable!("no empty keys"),
        };
        assert!(
            transcript.contains(&display),
            "`languages` must list {display}; transcript was:\n{transcript}"
        );
    }
}

/// Beat 3 — the language is USABLE: a term of its own concrete syntax is accepted at the
/// prompt and rendered back.
///
/// This is the beat that distinguishes "registered" from "usable". It deliberately asserts on
/// PARSE-and-render rather than on `exec`: the four differ in their in-Rho admission (measured
/// in `rho_backends.rs`), so a shared exec assertion would either be vacuous or would pin one
/// language's deferral behaviour into a test about all four. Their execution semantics are
/// covered per language by `languages/tests/{json,monoid,pi,turing}.rs`.
#[test]
fn each_omnibus_language_accepts_a_term_of_its_own_syntax_at_the_prompt() {
    for (key, source) in SUBJECTS {
        let transcript = run_repl_in(key, &[source]);
        assert!(
            !transcript.contains("Parse error"),
            "`repl {key}` must parse {source:?}; transcript was:\n{transcript}"
        );
        assert!(
            !transcript.contains("does not advertise a default runtime backend"),
            "{key} must carry an installed backend — that error is the exact bug \
             `registry_exec.rs` was written for; transcript was:\n{transcript}"
        );
    }
}
