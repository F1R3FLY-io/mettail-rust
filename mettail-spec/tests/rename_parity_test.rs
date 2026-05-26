//! Rename/replacement parity: modular `.rho` vs monolithic `language!`.

use std::path::PathBuf;

use mettail_spec::{
    assemble::compile_entry, diff_snapshots, language_def_from_monolithic, LanguageSnapshot,
};

mod par_monoid_monolithic {
    include!("fixtures/par_monoid_monolithic.rs");
}

#[test]
fn par_monoid_rename_matches_monolithic() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/par_monoid_app.rho");
    let ntir = compile_entry(entry, Some("ParL")).expect("compile ParL");
    let modular = LanguageSnapshot::from_ntir(&ntir);
    let def = language_def_from_monolithic(par_monoid_monolithic::SOURCE).expect("monolithic");
    let expected = LanguageSnapshot::from_language_def(&def);
    let diffs = diff_snapshots(&expected, &modular);
    assert!(diffs.is_empty(), "ParMonoid parity mismatch: {diffs:?}");
}
