use super::*;

fn recursive_compile<L: Clone + Eq + Hash>(
    compiler: &mut PatternCompiler<L>,
    pattern: &Pattern<L>,
) -> CompiledSubpattern {
    match pattern {
        Pattern::Var(name) => CompiledSubpattern {
            state: compiler.intern(StateKey::Var, 1),
            slot_names: vec![Rc::from(name.as_str())],
        },
        Pattern::App { op, args } => {
            let children: Vec<CompiledSubpattern> = args
                .iter()
                .map(|arg| recursive_compile(compiler, arg))
                .collect();
            let mut invocations = Vec::with_capacity(children.len());
            let mut slot_names: Vec<Rc<str>> = Vec::new();
            let mut slots_by_name: HashMap<Rc<str>, SlotId> = HashMap::default();
            for child in children {
                let mut slots = Vec::with_capacity(child.slot_names.len());
                for name in child.slot_names {
                    let slot = match slots_by_name.get(&name).copied() {
                        Some(slot) => slot,
                        None => {
                            let slot = SlotId(slot_names.len());
                            slot_names.push(Rc::clone(&name));
                            slots_by_name.insert(name, slot);
                            slot
                        },
                    };
                    slots.push(slot);
                }
                invocations.push(StateInvocation::new(child.state, slots));
            }
            CompiledSubpattern {
                state: compiler
                    .intern(StateKey::App { op: op.clone(), args: invocations }, slot_names.len()),
                slot_names,
            }
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
    assert_eq!(actual_root.0, expected_root.state);
    assert_eq!(
        actual_root.1,
        expected_root
            .slot_names
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
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
            let (root, slot_names) = compiler.compile(&pattern);
            assert_eq!(root.index(), DEPTH);
            assert_eq!(slot_names, ["x"]);
            assert_eq!(compiler.states.len(), DEPTH + 1);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("PatternCompiler PDA does not overflow a 256 KiB stack");
}
