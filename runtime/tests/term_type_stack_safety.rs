use mettail_runtime::TermType;

#[test]
fn term_type_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("term-type-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut ty = TermType::base("Result");
            for _ in 0..DEPTH {
                ty = TermType::arrow(TermType::base("Arg"), ty);
            }
            let cloned = ty.clone();
            assert_eq!(ty, cloned);
            assert!(format!("{ty:?}").ends_with(&")".repeat(DEPTH)));
            assert!(ty.to_string().ends_with(&"]".repeat(DEPTH)));

            let union = TermType::union(vec![
                TermType::Ambiguous(vec![ty.clone(), TermType::Unknown]),
                TermType::Unknown,
            ]);
            assert!(matches!(&union, TermType::Ambiguous(types) if types.len() == 2));
            drop(union);
            drop(cloned);
            drop(ty);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("term-type lifecycle must not overflow the native stack");
}
