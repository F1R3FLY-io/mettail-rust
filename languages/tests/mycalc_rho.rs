//! Integration test: `.rho`-authored MyCalc builds through projected `language!`.

use mettail_languages::mycalc::MyCalcLanguage;
use mettail_runtime::Language;

#[test]
fn mycalc_from_rho_compiles_and_exposes_language() {
    let lang = MyCalcLanguage;
    assert_eq!(lang.name(), "MyCalc");
    // Parity snapshot: modular MyCalc has Float + Cmplx types.
    let types = lang.metadata().types();
    assert_eq!(types.len(), 2);
    let mut names: Vec<_> = types.iter().map(|t| t.name).collect();
    names.sort();
    assert_eq!(names, ["Cmplx", "Float"]);
}

#[test]
fn mycalc_exports_spaces_metadata() {
    let spaces = mettail_languages::mycalc::EXPORTED_SPACES;
    assert_eq!(spaces.len(), 1);
    assert_eq!(spaces[0].name, "s");
    assert_eq!(spaces[0].language, "MyCalc");
    assert!(!spaces[0].language_hash.is_empty());
}
