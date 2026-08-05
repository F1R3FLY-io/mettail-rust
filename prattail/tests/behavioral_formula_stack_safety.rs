use mettail_prattail::algebra_tower::{RejectSafeAlgebra, Sat3};
use mettail_prattail::behavioral_algebra::{
    ActionPattern, Arg, BehavioralAlgebra, BehavioralFormula, BehavioralWorld, FactBase, HostTerm,
    QDomain,
};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LoopState;

impl HostTerm for LoopState {
    fn successors(&self) -> Vec<(String, Self)> {
        vec![("tick".into(), Self)]
    }

    fn label(&self) -> String {
        "ready".into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum WideState {
    Root,
    Good(u16),
    Bad,
}

impl HostTerm for WideState {
    fn successors(&self) -> Vec<(String, Self)> {
        match self {
            Self::Root => (0..9_999)
                .map(|index| ("step".into(), Self::Good(index)))
                .chain(std::iter::once(("step".into(), Self::Bad)))
                .collect(),
            Self::Good(_) | Self::Bad => Vec::new(),
        }
    }

    fn label(&self) -> String {
        match self {
            Self::Root | Self::Good(_) => "good".into(),
            Self::Bad => "bad".into(),
        }
    }
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn formula_lifecycle_and_evaluators_handle_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("behavioral-formula-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut facts = FactBase::new();
            facts.add_fact("ready", vec!["yes".into()]);
            let algebra = BehavioralAlgebra::<LoopState>::new(facts);

            let mut relational = BehavioralFormula::Relation {
                name: "ready".into(),
                args: vec![Arg::Lit("yes".into())],
            };
            for _ in 0..DEPTH {
                relational = BehavioralFormula::Not(Box::new(relational));
            }

            let cloned = relational.clone();
            assert_eq!(relational, cloned);
            assert_eq!(hash(&relational), hash(&cloned));
            assert!(format!("{relational:?}").ends_with(&")".repeat(DEPTH)));
            assert!(algebra.evaluate(&relational, &BehavioralWorld::new(LoopState)));
            assert_eq!(algebra.is_satisfiable_3v(&relational), Sat3::Sat);

            let mut modal = BehavioralFormula::Atom("ready".into());
            for _ in 0..DEPTH {
                modal = BehavioralFormula::Diamond(
                    ActionPattern::Named("tick".into()),
                    Box::new(modal),
                );
            }
            assert!(algebra.evaluate(&modal, &BehavioralWorld::new(LoopState)));

            let mut quantified = BehavioralFormula::Relation {
                name: "ready".into(),
                args: vec![Arg::Var("x".into())],
            };
            for index in 0..DEPTH {
                quantified = BehavioralFormula::Forall {
                    var: format!("unused_{index}"),
                    domain: QDomain::Values(vec!["yes".into()]),
                    body: Box::new(quantified),
                };
            }
            let world = BehavioralWorld::with_env(
                LoopState,
                [("x".to_owned(), "yes".to_owned())].into_iter().collect(),
            );
            assert!(algebra.evaluate(&quantified, &world));

            let mut domain = QDomain::Values(vec!["yes".into(), "no".into()]);
            for _ in 0..DEPTH {
                domain = QDomain::Bounded(Box::new(domain), 1);
            }
            let domain_clone = domain.clone();
            assert_eq!(domain, domain_clone);
            assert_eq!(hash(&domain), hash(&domain_clone));
            assert!(format!("{domain:?}").ends_with(&", 1)".repeat(DEPTH)));

            drop(domain_clone);
            drop(domain);
            drop(quantified);
            drop(modal);
            drop(cloned);
            drop(relational);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("formula lifecycle and evaluation must not overflow the native stack");
}

#[test]
fn universal_modal_check_does_not_hide_edges_after_the_old_state_cap() {
    let formula = BehavioralFormula::BoxAll(
        ActionPattern::Any,
        Box::new(BehavioralFormula::Atom("good".into())),
    );
    let algebra = BehavioralAlgebra::new(FactBase::new());
    assert!(
        !algebra.evaluate(&formula, &BehavioralWorld::new(WideState::Root)),
        "the complete LTS includes the bad successor that the old 10,000-state cap omitted"
    );
}
