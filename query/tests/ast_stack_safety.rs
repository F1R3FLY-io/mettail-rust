use mettail_query::{BodyAtom, Term, Variable};

const DEPTH: usize = 16_384;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn deeply_negated_relation() -> BodyAtom {
    let mut atom = BodyAtom::Relation {
        name: "edge".to_owned(),
        terms: vec![Term::Variable(Variable::new("x"))],
    };
    for _ in 0..DEPTH {
        atom = BodyAtom::Negation(Box::new(atom));
    }
    atom
}

#[test]
fn nested_negation_queries_are_stack_safe() {
    let atom = std::thread::Builder::new()
        .name("query-nested-negation".to_owned())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let atom = deeply_negated_relation();
            assert_eq!(atom.relation_name(), Some("edge"));
            assert_eq!(
                atom.variables()
                    .into_iter()
                    .map(|variable| variable.name.as_str())
                    .collect::<Vec<_>>(),
                ["x"]
            );
            let cloned = atom.clone();
            assert_eq!(cloned.relation_name(), Some("edge"));
            assert!(format!("{cloned:?}").ends_with(&")".repeat(DEPTH)));
            drop(cloned);
            atom
        })
        .expect("small-stack query thread starts")
        .join()
        .expect("nested-negation queries do not overflow the small stack");

    drop(atom);
}
