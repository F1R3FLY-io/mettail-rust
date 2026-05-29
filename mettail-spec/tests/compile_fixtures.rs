//! Integration tests for `.rho` fixture chain: numbers → complex → app.

use std::path::PathBuf;

use mettail_spec::{
    assemble::{compile_entry, validate_ntir},
    parser::parse_file,
    resolve::resolve_graph,
};

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn read_fixture(name: &str) -> String {
    std::fs::read_to_string(fixtures_dir().join(name)).expect("read fixture")
}

#[test]
fn parse_numbers_fixture() {
    let path = fixtures_dir().join("numbers.rho");
    let source = read_fixture("numbers.rho");
    let file = parse_file(path, &source).expect("parse numbers.rho");
    assert_eq!(file.module.name, "Numbers");
    assert!(file.imports.is_empty());
    let has_float_base = file.module.items.iter().any(|item| {
        matches!(
            item,
            mettail_spec::surface::ContentItem::Extender(e)
                if e.exported && e.name == "FloatBase"
        )
    });
    assert!(has_float_base);
}

#[test]
fn parse_complex_fixture() {
    let path = fixtures_dir().join("complex.rho");
    let source = read_fixture("complex.rho");
    let file = parse_file(path, &source).expect("parse complex.rho");
    assert_eq!(file.module.name, "Math");
    assert_eq!(file.imports.len(), 1);
    assert_eq!(file.imports[0].alias.as_deref(), Some("N"));
}

#[test]
fn parse_app_fixture() {
    let path = fixtures_dir().join("app.rho");
    let source = read_fixture("app.rho");
    let file = parse_file(path, &source).expect("parse app.rho");
    assert_eq!(file.module.name, "App");
    assert_eq!(file.imports.len(), 2);
}

#[test]
fn resolve_app_dag_order() {
    let entry = fixtures_dir().join("app.rho");
    let graph = resolve_graph(entry).expect("resolve graph");
    assert_eq!(graph.vertices.len(), 3);
    assert_eq!(graph.order.len(), 3);

    let names: Vec<String> = graph
        .order
        .iter()
        .map(|id| {
            id.0.file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_string()
        })
        .collect();

    assert!(names.iter().any(|n| n == "numbers.rho"));
    assert!(names.iter().any(|n| n == "complex.rho"));
    assert!(names.iter().any(|n| n == "app.rho"));

    let numbers_pos = names.iter().position(|n| n == "numbers.rho").unwrap();
    let complex_pos = names.iter().position(|n| n == "complex.rho").unwrap();
    let app_pos = names.iter().position(|n| n == "app.rho").unwrap();
    assert!(numbers_pos < complex_pos);
    assert!(complex_pos < app_pos);
}

#[test]
fn assemble_and_validate_mycalc() {
    let entry = fixtures_dir().join("app.rho");
    let ntir = compile_entry(entry, Some("MyCalc")).expect("compile MyCalc");
    assert_eq!(ntir.name, "MyCalc");
    assert_eq!(ntir.semantics, mettail_spec::ntir::SemanticsTarget::Rust);

    let type_names: Vec<String> = ntir.types.iter().map(|t| t.name.to_string()).collect();
    assert!(type_names.iter().any(|n| n == "Float"));
    assert!(type_names.iter().any(|n| n == "Cmplx"));

    let term_labels: Vec<String> = ntir.terms.iter().map(|r| r.label.to_string()).collect();
    assert!(
        term_labels
            .iter()
            .any(|l| l == "CmplxAdd" || l.contains('+')),
        "expected addition term, got {term_labels:?}"
    );

    validate_ntir(&ntir).expect("validate composed NTIR");
    assert!(!ntir.hash.is_empty());
}

#[test]
fn cycle_detection_reports_trace() {
    let dir = tempfile::tempdir().expect("tempdir");
    let a = dir.path().join("a.rho");
    let b = dir.path().join("b.rho");
    std::fs::write(
        &a,
        r#"import "b.rho" as B
module A { export extender E() { empty } }
"#,
    )
    .expect("write a");
    std::fs::write(
        &b,
        r#"import "a.rho" as A
module B { export extender E() { empty } }
"#,
    )
    .expect("write b");
    let err = resolve_graph(a).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("cycle"), "expected cycle error, got: {msg}");
}

#[test]
fn island_capture_in_extender_body() {
    let path = fixtures_dir().join("island.rho");
    std::fs::write(
        &path,
        r#"module M {
  export extender E() {
    Rust`fn main() { println!("hi"); }`
  }
}
"#,
    )
    .expect("write island fixture");
    let source = std::fs::read_to_string(&path).expect("read");
    let file = parse_file(path, &source).expect("parse island");
    let island = file.module.items.iter().find_map(|item| match item {
        mettail_spec::surface::ContentItem::Extender(e) => Some(&e.body),
        _ => None,
    });
    let body = island.expect("extender");
    match body {
        mettail_spec::surface::ExtenderExpr::Island(tok) => {
            assert_eq!(tok.lang, "Rust");
            assert!(tok.body.contains("fn main"));
        },
        other => panic!("expected island expr, got {other:?}"),
    }
    let _ = std::fs::remove_file(fixtures_dir().join("island.rho"));
}

#[test]
fn context_insert_replaces_marker_with_theory_body() {
    use mettail_spec::semantics::insert_at_marker;
    use mettail_spec::surface::ContextTemplate;

    let template = ContextTemplate {
        raw: "use std::collections::HashMap;\nINSERT_HERE\n".to_string(),
        insert_offset: Some("use std::collections::HashMap;\n".len()),
    };
    let theory = "use mettail_macros::language;\n\nlanguage! { name: L }\n";
    let out = insert_at_marker(&template, theory, "INSERT_HERE").expect("splice");
    assert!(out.contains("use std::collections::HashMap;"));
    assert!(out.contains("language! { name: L }"));
    assert!(!out.contains("INSERT_HERE"));
    assert!(!out.contains("/* generated theory */"));
}

#[test]
fn disjointness_conflict_on_duplicate_term_label() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("dup.rho");
    std::fs::write(
        &path,
        r#"module Dup {
  export extender E() {
    empty
    terms { Foo . |- "a" : Proc ; }
    terms { Foo . |- "b" : Proc ; }
  }
  export language L = E()
}
"#,
    )
    .expect("write");
    let err = match compile_entry(path, Some("L")) {
        Err(e) => e,
        Ok(_) => panic!("expected duplicate term error"),
    };
    let msg = err.to_string();
    assert!(
        msg.contains("duplicate") || msg.contains("Foo"),
        "expected disjointness error, got: {msg}"
    );
}

#[test]
fn extender_union_compiles_and_merges() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_ok.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { ![i32] as LeftTy }
    terms { LeftTerm . LeftTy ::= "left" ; }
  }
  export extender Right() {
    empty
    types { ![i64] as RightTy }
    terms { RightTerm . RightTy ::= "right" ; }
  }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let ntir = compile_entry(path, Some("L")).expect("compile union");
    let type_names: Vec<String> = ntir.types.iter().map(|t| t.name.to_string()).collect();
    assert!(type_names.iter().any(|n| n == "LeftTy"));
    assert!(type_names.iter().any(|n| n == "RightTy"));
    let term_labels: Vec<String> = ntir.terms.iter().map(|r| r.label.to_string()).collect();
    assert!(term_labels.iter().any(|n| n == "LeftTerm"));
    assert!(term_labels.iter().any(|n| n == "RightTerm"));
}

#[test]
fn extender_union_conflict_requires_explicit_resolution() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_conflict.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { ![i32] as LeftNum }
    terms { Same . LeftNum ::= "left" ; }
  }
  export extender Right() {
    empty
    types { ![i64] as RightNum }
    terms { Same . RightNum ::= "right" ; }
  }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let err = match compile_entry(path, Some("L")) {
        Ok(_) => panic!("expected unresolved union conflict"),
        Err(err) => err,
    };
    let msg = err.to_string();
    assert!(msg.contains("overlapping term label"), "got: {msg}");
    assert!(msg.contains("replacements"), "got: {msg}");
}

#[test]
fn extender_union_conflict_resolved_with_replacement() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_conflict_replaced.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { ![i32] as LeftNum }
    terms { Same . LeftNum ::= "left" ; }
  }
  export extender Right() {
    empty
    types { ![i64] as RightNum }
    terms { Same . RightNum ::= "right" ; }
  }
  export extender Both(L, R) {
    { L /\ R }
    replacements { []Same => Same . LeftNum ::= "resolved" }
  }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let ntir = compile_entry(path, Some("L")).expect("compile resolved union conflict");
    assert_eq!(ntir.terms.len(), 1);
    assert_eq!(ntir.terms[0].label.to_string(), "Same");
}

#[test]
fn extender_union_conflict_on_duplicate_type_fails() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_type_conflict.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() { empty types { ![i32] as Num } }
  export extender Right() { empty types { ![i64] as Num } }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let err = match compile_entry(path, Some("L")) {
        Ok(_) => panic!("expected type conflict"),
        Err(err) => err,
    };
    assert!(err.to_string().contains("duplicate type"), "{}", err);
}

#[test]
fn extender_union_conflict_on_duplicate_literals_fails() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_literals_conflict.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { ![i32] as Num }
    literals { Num ::= Regex("[0-9]+") }
  }
  export extender Right() {
    empty
    types { ![i64] as Num2 }
    literals { Num2 ::= Regex("[0-9]+") }
  }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let err = match compile_entry(path, Some("L")) {
        Ok(_) => panic!("expected literals conflict"),
        Err(err) => err,
    };
    assert!(err.to_string().contains("literals"), "{}", err);
}

#[test]
fn extender_union_conflict_on_duplicate_equation_fails() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_equation_conflict.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { Elem }
    terms { T . Elem ::= "t" ; }
    equations { Eq . |- (T) = (T) ; }
  }
  export extender Right() {
    empty
    types { Elem2 }
    terms { U . Elem2 ::= "u" ; }
    equations { Eq . |- (U) = (U) ; }
  }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let err = match compile_entry(path, Some("L")) {
        Ok(_) => panic!("expected equation conflict"),
        Err(err) => err,
    };
    assert!(err.to_string().contains("duplicate equation"), "{}", err);
}

#[test]
fn extender_union_conflict_on_duplicate_rewrite_fails() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("union_rewrite_conflict.rho");
    std::fs::write(
        &path,
        r#"module U {
  export extender Left() {
    empty
    types { Elem }
    terms { T . Elem ::= "t" ; }
    rewrites { Rw . |- (T) ~> (T) ; }
  }
  export extender Right() {
    empty
    types { Elem2 }
    terms { U . Elem2 ::= "u" ; }
    rewrites { Rw . |- (U) ~> (U) ; }
  }
  export extender Both(L, R) { L /\ R }
  export language L = Both(Left(), Right())
}
"#,
    )
    .expect("write");

    let err = match compile_entry(path, Some("L")) {
        Ok(_) => panic!("expected rewrite conflict"),
        Err(err) => err,
    };
    assert!(err.to_string().contains("duplicate rewrite"), "{}", err);
}
