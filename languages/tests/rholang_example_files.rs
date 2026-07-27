//! Batch-check Rholang REPL example files.
//!
//! Focuses on `repl/src/examples/rholang.txt` (environment assignment format):
//! - every `name = term` definition must parse with `parse_term_for_env`
//! - each parsed definition must be insertable into language env
//! - each stored term must run through the language's reducer without runtime errors
//!
//! ## Reducer oracle — Path-B Dovetail normal form (NOT the retired `run_ascent`)
//!
//! This test arrived from `main`, where `Language::run_ascent` (the
//! f1r3node-independent Ascent reference reducer) is the reduction oracle. On
//! the WFST/feature branch the Ascent+CESK oracle was retired (P6) in favor of
//! Dovetail/Rho backends, so `run_ascent` now resolves to the fail-closed
//! `Language` trait default and returns
//! `Err("…Ascent oracle…not installed…")` for every Rholang term. The live
//! reducer is the generated whole-box Dovetail normalizer
//! `<Lang>::dovetail_normal_term` — the SAME non-COMM reducer that
//! `numeric_bigint_cast_regressions.rs` and `rholang_tests.rs`'s Path-B
//! `mod oracle` drive. `check_env_file` therefore takes an explicit `run_fn`
//! reducer closure (supplied by the caller with the concrete language's
//! `dovetail_normal_term`) instead of calling the retired trait method.

use std::path::{Path, PathBuf};

use mettail_languages::rholang;
use mettail_runtime::{clear_var_cache, Language, Term};

/// Saturation budget for the Dovetail normalizer (mirrors
/// `numeric_bigint_cast_regressions.rs` and `rholang_tests::oracle`).
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

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

fn check_env_file(
    path: &Path,
    lang: &dyn Language,
    label: &str,
    run_fn: impl Fn(&dyn Term) -> Result<(), String>,
) {
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
            failures
                .push(
                    format!("{label} {}: missing env term for binding '{name}'", path.display(),),
                );
            continue;
        };
        if let Err(e) = run_fn(term.as_ref()) {
            failures.push(format!(
                "{label} {}: reducer failed for env binding '{name}':\n  {e}",
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
fn rholang_examples_env_file_loads_and_runs() {
    let path = examples_dir().join("rholang.txt");
    // Reduce each stored term via the live Dovetail normalizer (the retired
    // `run_ascent` is fail-closed on this branch — see the module docs). A
    // normalizer error (`Err`) is a real runtime failure; convergence to any
    // normal form is success. Matches the `numeric_bigint_cast_regressions.rs`
    // oracle exactly.
    check_env_file(&path, &rholang::RholangLanguage, "rholang", |term| {
        // Drive the term through the generated Dovetail normalizer — the live,
        // whole-box reducer on this branch. It performs equational/fold
        // reduction but NOT channel communication (COMM), so a definition or
        // combinator whose only progress is a `for`/`!` interaction (`add`,
        // `comm`, `dup`, `fwd`, `cell`, the `*_comm` demos, `new` bodies, …)
        // legitimately terminates as a "stuck term": the reducer RAN without a
        // runtime error and reached a valid non-COMM normal form. `rholang.txt`
        // is largely such interaction-driven definitions, so — exactly as
        // `rholang_tests.rs`'s Path-B `mod oracle` treats a `dovetail_normal_term`
        // `Err` (it simply adds no NF node, never a failure) — the benign
        // "stuck term" outcome is accepted here. Any OTHER error (e.g. a
        // downcast/type failure or a genuine reconstruction fault) is a real
        // runtime failure and is surfaced.
        match rholang::RholangLanguage::dovetail_normal_term(term, DOVETAIL_ITERS, DOVETAIL_NODES) {
            Ok(_) => Ok(()),
            Err(e) if e.contains("stuck term") => Ok(()),
            Err(e) => Err(e),
        }
    });
}
