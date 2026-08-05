use mettail_rholang_codegen::RhoAstLiteral;

#[test]
fn literal_lifecycle_and_lowering_survive_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("rho-ast-literal-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let sample = RhoAstLiteral::Map(vec![(
                RhoAstLiteral::String("key".into()),
                RhoAstLiteral::Bag(vec![(RhoAstLiteral::Int(7), 3)]),
            )]);
            assert_eq!(sample.annotation(), "{\"key\": Bag{7 * 3}}");
            assert_eq!(format!("{sample:?}"), "Map([(String(\"key\"), Bag([(Int(7), 3)]))])");
            assert_eq!(sample, sample.clone());
            drop(sample.try_to_par().expect("bounded sample lowers"));

            let mut literal = RhoAstLiteral::Int(1);
            for _ in 0..DEPTH {
                literal = RhoAstLiteral::List(vec![literal]);
            }
            let cloned = literal.clone();
            assert_eq!(literal, cloned);
            assert!(literal.annotation().ends_with(&"]".repeat(DEPTH)));
            assert!(format!("{literal:?}").ends_with(&"])".repeat(DEPTH)));
            drop(
                literal
                    .try_to_par()
                    .expect("deep literal lowers iteratively"),
            );
            drop(cloned);
            drop(literal);
        })
        .expect("small-stack worker starts")
        .join()
        .expect("literal lifecycle and lowering must not overflow the native stack");
}
