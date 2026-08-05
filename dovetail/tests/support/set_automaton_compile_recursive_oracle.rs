use super::*;

fn recursive_compile<L: Clone + Eq + Hash>(
    compiler: &mut PatternCompiler<L>,
    pattern: &Pattern<L>,
) -> StateId {
    match pattern {
        Pattern::Var(name) => compiler.intern(StateKey::Var(name.clone())),
        Pattern::App { op, args } => {
            let args = args
                .iter()
                .map(|arg| recursive_compile(compiler, arg))
                .collect();
            compiler.intern(StateKey::App { op: op.clone(), args })
        },
        Pattern::AcApp { .. } => unreachable!("oracle fixture contains no AcApp"),
    }
}

#[test]
fn iterative_pattern_compiler_matches_recursive_oracle() {
    let shared = Pattern::app("Pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]);
    let fixture = Pattern::app("Root".to_string(), vec![shared.clone(), shared]);
    let mut actual = PatternCompiler::default();
    let mut expected = PatternCompiler::default();
    let actual_root = actual.compile(&fixture);
    let expected_root = recursive_compile(&mut expected, &fixture);
    assert_eq!(actual_root, expected_root);
    assert_eq!(actual, expected);
}

#[test]
fn pattern_compiler_handles_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("dovetail-compiler-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut pattern = Pattern::var("x");
            for _ in 0..DEPTH {
                pattern = Pattern::app("N".to_string(), vec![pattern]);
            }
            let mut compiler = PatternCompiler::default();
            let root = compiler.compile(&pattern);
            assert_eq!(root.index(), DEPTH);
            assert_eq!(compiler.states.len(), DEPTH + 1);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("PatternCompiler PDA does not overflow a 256 KiB stack");
}
