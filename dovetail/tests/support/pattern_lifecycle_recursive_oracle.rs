use super::*;

fn recursive_clone<L: Clone>(pattern: &Pattern<L>) -> Pattern<L> {
    match pattern {
        Pattern::Var(name) => Pattern::Var(name.clone()),
        Pattern::App { op, args } => Pattern::App {
            op: op.clone(),
            args: args.iter().map(recursive_clone).collect(),
        },
        Pattern::AcApp { op, fixed, rest } => Pattern::AcApp {
            op: op.clone(),
            fixed: fixed.iter().map(recursive_clone).collect(),
            rest: rest.clone(),
        },
    }
}

fn recursive_eq<L: PartialEq>(left: &Pattern<L>, right: &Pattern<L>) -> bool {
    match (left, right) {
        (Pattern::Var(left), Pattern::Var(right)) => left == right,
        (
            Pattern::App { op: left_op, args: left_args },
            Pattern::App { op: right_op, args: right_args },
        ) => {
            left_op == right_op
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| recursive_eq(left, right))
        },
        (
            Pattern::AcApp {
                op: left_op,
                fixed: left_fixed,
                rest: left_rest,
            },
            Pattern::AcApp {
                op: right_op,
                fixed: right_fixed,
                rest: right_rest,
            },
        ) => {
            left_op == right_op
                && left_rest == right_rest
                && left_fixed.len() == right_fixed.len()
                && left_fixed
                    .iter()
                    .zip(right_fixed)
                    .all(|(left, right)| recursive_eq(left, right))
        },
        _ => false,
    }
}

fn recursive_debug<L: std::fmt::Debug>(pattern: &Pattern<L>) -> String {
    match pattern {
        Pattern::Var(name) => format!("Var({name:?})"),
        Pattern::App { op, args } => {
            let args = args
                .iter()
                .map(recursive_debug)
                .collect::<Vec<_>>()
                .join(", ");
            format!("App {{ op: {op:?}, args: [{args}] }}")
        },
        Pattern::AcApp { op, fixed, rest } => {
            let fixed = fixed
                .iter()
                .map(recursive_debug)
                .collect::<Vec<_>>()
                .join(", ");
            format!("AcApp {{ op: {op:?}, fixed: [{fixed}], rest: {rest:?} }}")
        },
    }
}

#[test]
fn iterative_pattern_lifecycle_matches_recursive_oracles() {
    let fixture = Pattern::app(
        "Root".to_string(),
        vec![
            Pattern::var("x"),
            Pattern::ac(
                "Bag".to_string(),
                vec![Pattern::app("Leaf".to_string(), Vec::new()), Pattern::var("y")],
                Some("rest".to_string()),
            ),
        ],
    );
    let actual = fixture.clone();
    let expected = recursive_clone(&fixture);
    assert!(recursive_eq(&actual, &expected));
    assert_eq!(actual, expected);
    assert_eq!(format!("{fixture:?}"), recursive_debug(&fixture));

    let different =
        Pattern::app("Root".to_string(), vec![Pattern::var("x"), Pattern::var("different")]);
    assert_eq!(fixture == different, recursive_eq(&fixture, &different));
}

#[test]
fn pattern_lifecycle_handles_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("dovetail-pattern-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut pattern = Pattern::var("x");
            for _ in 0..DEPTH {
                pattern = Pattern::app("N".to_string(), vec![pattern]);
            }
            let cloned = pattern.clone();
            assert_eq!(pattern, cloned);
            drop(cloned);

            // Debug is also iterative; a smaller prefix keeps the test artifact compact while
            // still exceeding a 256 KiB recursive formatter stack.
            let mut debug_pattern = Pattern::var("x");
            for _ in 0..2_000 {
                debug_pattern = Pattern::app("N".to_string(), vec![debug_pattern]);
            }
            let rendered = format!("{debug_pattern:?}");
            assert!(rendered.starts_with("App { op: \"N\""));
            drop(debug_pattern);
            drop(pattern);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("Pattern Clone/Eq/Debug/Drop do not overflow a 256 KiB stack");
}
