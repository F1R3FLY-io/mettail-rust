//! Helpers for including `.rho`-projected languages from `build.rs` output.

/// Include `{Name}_lang.rs` from the depending crate's `OUT_DIR` (written by `mettail-spec`).
///
/// Example in `languages/build.rs`:
/// `mettail_spec::project_rust_file("specs/mycalc/app.rho", Some("MyCalc"), out.join("mycalc_lang.rs"))`
#[macro_export]
macro_rules! mettail_modules {
    ($name:ident) => {
        ::core::include!(::core::concat!(
            ::core::env!("OUT_DIR"),
            "/",
            ::core::stringify!($name),
            "_lang.rs"
        ));
    };
}
