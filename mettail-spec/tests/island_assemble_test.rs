//! Island plugin assembly (Rust holes, Rholang proc GST).

use std::path::PathBuf;

use mettail_spec::assemble::compile_entry;

#[test]
fn rholang_proc_island_compiles() {
    let entry =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/rholang_proc_island.rho");
    let ntir = compile_entry(entry, Some("Demo")).expect("compile with proc island");
    assert_eq!(ntir.proc_artifacts.len(), 1);
    let art = &ntir.proc_artifacts[0];
    assert_eq!(art.lang, "Rholang");
    let json = serde_json::to_string(&art.gst).expect("serialize gst");
    assert!(json.contains("Let") || json.contains("let"));
}

#[test]
fn rust_island_with_typed_hole_in_extender() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("rust_island.rho");
    std::fs::write(
        &path,
        r#"module M {
  export extender E() {
    Rust`let x = ${42};`
  }
  export language L = E()
}
"#,
    )
    .expect("write");
    let ntir = compile_entry(path, Some("L")).expect("compile rust island");
    assert_eq!(ntir.rust_island_snippets.len(), 1);
    assert!(ntir.rust_island_snippets[0].contains("let x"));
}

#[test]
fn rust_island_invalid_hole_errors() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("bad.rho");
    std::fs::write(
        &path,
        r#"module M {
  export extender E() { Rust`let x = ${fn (};` }
  export language L = E()
}
"#,
    )
    .expect("write");
    let msg = match compile_entry(path, Some("L")) {
        Err(e) => e.to_string(),
        Ok(_) => panic!("expected island parse error"),
    };
    assert!(msg.contains("island") || msg.contains("Rust"), "got: {msg}");
}

#[test]
fn rust_island_snippet_spliced_inside_context_insert_here() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("rust_island_ctx.rho");
    std::fs::write(
        &path,
        r#"module M {
  export extender E() {
    { Rust`let x = ${42};` }
    semantics Rust
    context {
      INSERT_HERE
    }
  }
  export language L = E()
}
"#,
    )
    .expect("write");
    let ntir = compile_entry(path, Some("L")).expect("compile rust island with context");
    let src = mettail_spec::project_rust_source(&ntir).expect("project");
    assert!(!src.contains("INSERT_HERE"));
    assert!(src.contains("let x"));
    assert!(src.contains("language!"));
    let island_pos = src.find("let x").expect("island snippet");
    let language_pos = src.find("language!").expect("language macro");
    assert!(
        island_pos < language_pos,
        "island snippet must precede language! inside spliced body"
    );
}
