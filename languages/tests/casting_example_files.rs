//! Batch-check `repl/src/examples/*-casting.txt`: every `exec …` line must parse and run Ascent.
//!
//! Run (all tests in this file):
//!   cargo test -p mettail-languages --test casting_example_files -- --nocapture
//!
//! Or filter by name substring:
//!   cargo test -p mettail-languages casting_example_files_ -- --nocapture
//!
//! The interactive REPL has no batch mode for these files; use this test instead of piping to `mettail`.

use std::path::PathBuf;

use mettail_languages::{calculator as calc, rhocalc};
use mettail_runtime::{clear_var_cache, Language};

fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../repl/src/examples")
}

fn check_exec_lines(path: &std::path::Path, lang: &dyn Language, label: &str) {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let mut failures = Vec::new();
    for (idx, line) in text.lines().enumerate() {
        let line_no = idx + 1;
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        let Some(rest) = line.strip_prefix("exec ") else {
            continue;
        };
        let term_str = rest.trim();
        clear_var_cache();
        let term = match lang.parse_term(term_str) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!(
                    "{label} {}:{} parse failed: {term_str:?}\n  {e}",
                    path.display(),
                    line_no
                ));
                continue;
            }
        };
        if let Err(e) = lang.run_ascent(term.as_ref()) {
            failures.push(format!(
                "{label} {}:{} run_ascent failed: {term_str:?}\n  {e}",
                path.display(),
                line_no
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} exec line(s) failed:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
fn casting_example_files_calculator() {
    let path = examples_dir().join("calculator-casting.txt");
    check_exec_lines(&path, &calc::CalculatorLanguage, "calculator");
}

#[test]
fn casting_example_files_rhocalc() {
    let path = examples_dir().join("rhocalc-casting.txt");
    check_exec_lines(&path, &rhocalc::RhoCalcLanguage, "rhocalc");
}
