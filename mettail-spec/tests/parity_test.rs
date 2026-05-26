//! Modular `.rho` vs monolithic `language!` parity (v1 Phase 2).

use std::path::PathBuf;

use mettail_spec::{
    assemble::compile_entry, diff_snapshots, language_def_from_monolithic,
    parse_projected_language_def, project_rust_source, LanguageSnapshot,
};

mod mycalc_monolithic {
    include!("fixtures/mycalc_monolithic.rs");
}

fn fixtures_app() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/app.rho")
}

fn monolithic_snapshot() -> LanguageSnapshot {
    let def =
        language_def_from_monolithic(mycalc_monolithic::SOURCE).expect("parse monolithic MyCalc");
    LanguageSnapshot::from_language_def(&def)
}

#[test]
fn mycalc_modular_ntir_matches_monolithic() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    let modular = LanguageSnapshot::from_ntir(&ntir);
    let expected = monolithic_snapshot();
    let diffs = diff_snapshots(&expected, &modular);
    assert!(diffs.is_empty(), "modular NTIR mismatch: {diffs:?}");
}

#[test]
fn mycalc_projected_roundtrip_matches_monolithic() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    let projected = parse_projected_language_def(&ntir).expect("parse projected");
    let modular = LanguageSnapshot::from_language_def(&projected);
    let expected = monolithic_snapshot();
    let diffs = diff_snapshots(&expected, &modular);
    assert!(diffs.is_empty(), "projected round-trip mismatch: {diffs:?}");
}

#[test]
fn mycalc_ntir_hash_stable() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    assert_eq!(ntir.hash, "65f8f44ad3bef5234d9615378f224f347d891c191e2070d5882e4ecc0ba2ce85");
    let summary = ntir.summary();
    assert_eq!(summary.name, "MyCalc");
    let mut types = summary.types;
    types.sort();
    assert_eq!(types, vec!["Cmplx", "Float"]);
    let mut terms = summary.term_labels;
    terms.sort();
    assert_eq!(terms, vec!["CmplxAdd", "CmplxInj"]);
}

#[test]
fn mycalc_projected_source_parses() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    let src = project_rust_source(&ntir).expect("project");
    assert!(src.contains("language!"));
    assert!(src.contains("name: MyCalc"));
}
