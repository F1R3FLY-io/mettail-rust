//! Phase 2: NTIR → Rust projection and round-trip checks.

use std::path::PathBuf;

use mettail_spec::{
    assemble::compile_entry, parse_projected_language_def, project_rust_source, validate_ntir,
    verify_projection_sources,
};

fn fixtures_app() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/app.rho")
}

#[test]
fn project_mycalc_emits_language_macro() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    validate_ntir(&ntir).expect("validate");
    let src = project_rust_source(&ntir).expect("project");
    assert!(src.contains("language!"));
    assert!(
        !src.contains("#![allow"),
        "projected include file must not use inner attributes"
    );
    assert!(src.contains("name: MyCalc"));
    assert!(src.contains("Float"));
    assert!(src.contains("Cmplx"));
    assert!(src.contains("CmplxAdd"));
}

#[test]
fn projected_source_round_trips_language_def() {
    let ntir = compile_entry(fixtures_app(), Some("MyCalc")).expect("compile");
    verify_projection_sources(&ntir).expect("verify projection");
    let def = parse_projected_language_def(&ntir).expect("parse projected");
    assert_eq!(def.name.to_string(), "MyCalc");
    assert_eq!(def.types.len(), ntir.types.len());
    assert_eq!(def.terms.len(), ntir.terms.len());
}
