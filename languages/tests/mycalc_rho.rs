//! Integration test: `.rho`-authored MyCalc builds through projected `language!`.

use mettail_languages::mycalc::MyCalcLanguage;
use mettail_runtime::Language;

#[test]
fn mycalc_from_rho_compiles_and_exposes_language() {
    let lang = MyCalcLanguage;
    assert_eq!(lang.name(), "MyCalc");
}
