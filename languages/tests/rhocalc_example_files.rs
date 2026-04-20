//! Batch-check RhoCalc REPL example files.
//!
//! Focuses on `repl/src/examples/rhocalc.txt` (environment assignment format):
//! - every `name = term` definition must parse with `parse_term_for_env`
//! - each parsed definition must be insertable into language env
//! - each stored term must run through Ascent without runtime errors

use std::path::{Path, PathBuf};

use mettail_languages::rhocalc;
use mettail_runtime::{clear_var_cache, Language};

fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../repl/src/examples")
}

fn parse_assignment(line: &str) -> Option<(String, String)> {
    let (name, term) = line.split_once('=')?;
    let name = name.trim();
    let term = term.trim();
    if name.is_empty() || term.is_empty() {
        return None;
    }
    Some((name.to_string(), term.to_string()))
}

fn check_env_file(path: &Path, lang: &dyn Language, label: &str) {
    let text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let mut env = lang.create_env();
    let mut failures = Vec::new();
    let mut parsed_count = 0usize;

    // Mirror REPL behavior: preserve var cache across env lines.
    clear_var_cache();

    for (idx, raw_line) in text.lines().enumerate() {
        let line_no = idx + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") || line.starts_with('#') {
            continue;
        }

        let Some((name, term_str)) = parse_assignment(line) else {
            failures.push(format!(
                "{label} {}:{} invalid assignment syntax: {line:?}",
                path.display(),
                line_no,
            ));
            continue;
        };

        let term = match lang.parse_term_for_env(&term_str) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!(
                    "{label} {}:{} parse failed for '{name}':\n  {e}\n  term: {term_str}",
                    path.display(),
                    line_no,
                ));
                continue;
            },
        };

        if let Err(e) = lang.add_to_env(env.as_mut(), &name, term.as_ref()) {
            failures.push(format!(
                "{label} {}:{} add_to_env failed for '{name}':\n  {e}",
                path.display(),
                line_no,
            ));
            continue;
        }

        parsed_count += 1;
    }

    for (name, _, _) in lang.list_env(env.as_ref()) {
        let Some(term) = lang.get_env_term(env.as_ref(), &name) else {
            failures.push(format!(
                "{label} {}: missing env term for binding '{name}'",
                path.display(),
            ));
            continue;
        };
        if let Err(e) = lang.run_ascent(term.as_ref()) {
            failures.push(format!(
                "{label} {}: run_ascent failed for env binding '{name}':\n  {e}",
                path.display(),
            ));
        }
    }

    assert!(
        parsed_count > 0,
        "{} {}: expected at least one parsed definition",
        label,
        path.display()
    );
    assert!(
        failures.is_empty(),
        "{} issue(s) found in {}:\n\n{}",
        failures.len(),
        path.display(),
        failures.join("\n\n")
    );
}

#[test]
fn rhocalc_examples_env_file_loads_and_runs() {
    let path = examples_dir().join("rhocalc.txt");
    check_env_file(&path, &rhocalc::RhoCalcLanguage, "rhocalc");
}
