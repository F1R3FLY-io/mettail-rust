use mettail_prattail::ltl::{ltl_to_buchi, LtlFormula};
use mettail_prattail::parity_tree::{try_mu_calculus_to_pata, MuCalculusFormula};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const DEEP_FORMULA_DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn on_small_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("temporal-formula-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(test)
        .expect("spawn temporal-formula small-stack gate")
        .join()
        .expect("temporal-formula small-stack gate panicked");
}

fn hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn ltl_lifecycle_and_structural_walkers_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = LtlFormula::atom("deep");
        for _ in 0..DEEP_FORMULA_DEPTH {
            formula = LtlFormula::Always(Box::new(formula));
        }

        let cloned = formula.clone();
        assert_eq!(formula, cloned);
        assert_eq!(hash(&formula), hash(&cloned));
        assert_eq!(formula.atoms().into_iter().collect::<Vec<_>>(), ["deep"]);

        let display = formula.to_string();
        assert_eq!(display.len(), DEEP_FORMULA_DEPTH + "deep".len());
        assert!(display.ends_with("deep"));
        let debug = format!("{formula:?}");
        assert!(debug.starts_with("Always(Always("));
        assert!(debug.ends_with(&")".repeat(DEEP_FORMULA_DEPTH)));

        let automaton = ltl_to_buchi(&formula);
        assert_eq!(automaton.num_states(), 1);
        assert_eq!(automaton.num_transitions(), 1);

        let mut eventual = LtlFormula::atom("eventual");
        for _ in 0..DEEP_FORMULA_DEPTH {
            eventual = LtlFormula::Eventually(Box::new(eventual));
        }
        let eventual_automaton = ltl_to_buchi(&eventual);
        assert_eq!(eventual_automaton.num_states(), 3);

        drop(cloned);
        drop(formula);
        drop(automaton);
        drop(eventual);
        drop(eventual_automaton);
    });
}

#[test]
fn mu_calculus_lifecycle_and_compiler_are_stack_safe_at_depth_20k() {
    on_small_stack(|| {
        let mut formula = MuCalculusFormula::Atom("deep".to_string());
        for _ in 0..DEEP_FORMULA_DEPTH {
            formula = MuCalculusFormula::Not(Box::new(formula));
        }

        let cloned = formula.clone();
        assert_eq!(formula, cloned);
        assert_eq!(hash(&formula), hash(&cloned));
        assert!(formula
            .to_string()
            .ends_with(&")".repeat(DEEP_FORMULA_DEPTH)));
        assert!(format!("{formula:?}").ends_with(&")".repeat(DEEP_FORMULA_DEPTH)));

        let automaton = try_mu_calculus_to_pata(&formula, 2).expect("compile deep formula");
        assert_eq!(automaton.num_states(), DEEP_FORMULA_DEPTH + 1);

        drop(cloned);
        drop(formula);
        drop(automaton);
    });
}

#[test]
fn temporal_formula_formatting_preserves_the_compact_contract() {
    let ltl = LtlFormula::WeakUntil(
        Box::new(LtlFormula::Not(Box::new(LtlFormula::atom("p")))),
        Box::new(LtlFormula::Release(Box::new(LtlFormula::atom("q")), Box::new(LtlFormula::True))),
    );
    assert_eq!(format!("{ltl:?}"), "WeakUntil(Not(Atom(\"p\")), Release(Atom(\"q\"), True))");
    assert_eq!(ltl.to_string(), "(!p W (q R true))");

    let mu = MuCalculusFormula::Mu {
        var: "X".to_string(),
        body: Box::new(MuCalculusFormula::And(
            Box::new(MuCalculusFormula::Diamond {
                child_idx: 2,
                body: Box::new(MuCalculusFormula::Var("X".to_string())),
            }),
            Box::new(MuCalculusFormula::Box {
                child_idx: 1,
                body: Box::new(MuCalculusFormula::Atom("leaf".to_string())),
            }),
        )),
    };
    assert_eq!(
        format!("{mu:?}"),
        "Mu { var: \"X\", body: And(Diamond { child_idx: 2, body: Var(\"X\") }, Box { child_idx: 1, body: Atom(\"leaf\") }) }"
    );
    assert_eq!(mu.to_string(), "mu X.(<2>.(X) /\\ [1].(\"leaf\"))");
}
