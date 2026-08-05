use mettail_testkit::ctor::{Schema, SCHEMA_BEGIN, SCHEMA_END};

#[test]
fn field_spec_parse_and_lifecycle_survive_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("field-spec-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let descriptor = format!("{}var", "opt:".repeat(DEPTH));
            let source = format!(
                "{SCHEMA_BEGIN}\nLANG Deep\nCAT C -\nV C Wrap tuple {descriptor}\n{SCHEMA_END}"
            );
            let schema = Schema::parse(&source).expect("deep option schema parses iteratively");
            let spec = &schema
                .variants
                .get(&("C".to_string(), "Wrap".to_string()))
                .expect("deep constructor is present")
                .fields[0];
            let cloned = spec.clone();
            assert_eq!(spec, &cloned);
            assert!(format!("{cloned:?}").ends_with(&")".repeat(DEPTH)));
            drop(cloned);
            drop(schema);
        })
        .expect("small-stack worker starts")
        .join()
        .expect("field-spec parsing and lifecycle must not overflow the native stack");
}
