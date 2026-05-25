use std::path::PathBuf;

fn main() {
    std::env::set_var("PROTOC", protoc_bin_vendored::protoc_bin_path().expect("vendored protoc"));
    prost_build::Config::new()
        .compile_protos(&["proto/rhocalc_wire.proto"], &["proto/"])
        .expect("compile rhocalc_wire.proto");

    project_mycalc_from_rho();
}

/// Phase 2: lower `.rho` specs to `language!` Rust in `OUT_DIR`.
fn project_mycalc_from_rho() {
    let manifest_dir =
        PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let specs_dir = manifest_dir.join("specs/mycalc");
    let entry = specs_dir.join("app.rho");
    if !entry.exists() {
        return;
    }

    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR"));
    let out_path = out_dir.join("mycalc_lang.rs");
    mettail_spec::project_rust_file(&entry, Some("MyCalc"), &out_path)
        .expect("project MyCalc from specs/mycalc/app.rho");

    println!("cargo:rerun-if-changed={}", entry.display());
    for name in ["numbers.rho", "complex.rho", "app.rho"] {
        println!("cargo:rerun-if-changed={}", specs_dir.join(name).display());
    }
}
