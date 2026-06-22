use super::*;
use crate::lattice_theory::{LatticeStore, LatticeTheory, TypeId};

/// Helper: build a simple type hierarchy for testing.
///
/// Hierarchy:
///   Top (0)
///   ├── Number (1)
///   │   ├── Int (2)
///   │   └── Float (3)
///   ├── String (4)
///   └── Bool (5)
///   Bottom (6)
fn test_lattice() -> (LatticeTheory, LatticeStore) {
    let top: TypeId = 0;
    let number: TypeId = 1;
    let int: TypeId = 2;
    let float: TypeId = 3;
    let string: TypeId = 4;
    let bool_ty: TypeId = 5;
    let bottom: TypeId = 6;

    let universe = vec![top, number, int, float, string, bool_ty, bottom];
    let mut names = HashMap::new();
    names.insert(top, "Top".to_string());
    names.insert(number, "Number".to_string());
    names.insert(int, "Int".to_string());
    names.insert(float, "Float".to_string());
    names.insert(string, "String".to_string());
    names.insert(bool_ty, "Bool".to_string());
    names.insert(bottom, "Bottom".to_string());

    let theory = LatticeTheory::new(universe, names);
    let mut store = LatticeStore::new();

    // Add subtype edges: Int <: Number, Float <: Number, Number <: Top, etc.
    let edges = vec![
        (int, number),
        (float, number),
        (number, top),
        (string, top),
        (bool_ty, top),
        (bottom, int),
        (bottom, float),
        (bottom, string),
        (bottom, bool_ty),
    ];
    for (sub, sup) in &edges {
        let ct = &theory;
        let constraint = SubtypeConstraint { sub: *sub, sup: *sup };
        store = ct
            .propagate(&store, &constraint)
            .expect("propagation should succeed");
    }

    (theory, store)
}

fn test_system() -> LatticeTypeSystem {
    let (theory, store) = test_lattice();
    let mut ctor_types = HashMap::new();
    // Constructor: int_lit(value) → Int
    ctor_types.insert("int_lit".to_string(), (vec![], 2)); // Int = 2
                                                           // Constructor: float_lit(value) → Float
    ctor_types.insert("float_lit".to_string(), (vec![], 3)); // Float = 3
                                                             // Constructor: add(Int, Int) → Int
    ctor_types.insert("add".to_string(), (vec![2, 2], 2));

    LatticeTypeSystem::with_bounds(theory, store, ctor_types, 0, 6)
}

// ── TypeSystem trait: reflexivity ──

#[test]
fn lattice_subtype_reflexive() {
    let sys = test_system();
    let env = sys.empty_env();
    for &ty in &[0usize, 1, 2, 3, 4, 5, 6] {
        assert!(
            sys.is_subtype(&env, &ty, &ty),
            "is_subtype({ty}, {ty}) should be true (reflexivity)"
        );
    }
}

// ── TypeSystem trait: transitivity ──

#[test]
fn lattice_subtype_transitive() {
    let sys = test_system();
    let env = sys.empty_env();
    // Int <: Number and Number <: Top, so Int <: Top
    assert!(sys.is_subtype(&env, &2, &1)); // Int <: Number
    assert!(sys.is_subtype(&env, &1, &0)); // Number <: Top
    assert!(sys.is_subtype(&env, &2, &0)); // Int <: Top (transitive)
}

// ── TypeSystem trait: antisymmetry (non-subtype) ──

#[test]
fn lattice_subtype_not_reverse() {
    let sys = test_system();
    let env = sys.empty_env();
    // Number is NOT a subtype of Int
    assert!(!sys.is_subtype(&env, &1, &2));
    // String is NOT a subtype of Number
    assert!(!sys.is_subtype(&env, &4, &1));
}

// ── Join (LUB) ──

#[test]
fn lattice_join() {
    let sys = test_system();
    let env = sys.empty_env();
    // join(Int, Float) = Number
    assert_eq!(sys.join(&env, &2, &3), Some(1));
    // join(Int, Int) = Int
    assert_eq!(sys.join(&env, &2, &2), Some(2));
    // join(Int, String) = Top
    assert_eq!(sys.join(&env, &2, &4), Some(0));
}

// ── Meet (GLB) ──

#[test]
fn lattice_meet() {
    let sys = test_system();
    let env = sys.empty_env();
    // meet(Int, Int) = Int
    assert_eq!(sys.meet(&env, &2, &2), Some(2));
    // meet(Number, Int) = Int (Int is subtype of Number)
    assert_eq!(sys.meet(&env, &1, &2), Some(2));
}

// ── Type checking ──

#[test]
fn lattice_check_const() {
    let sys = test_system();
    let env = sys.empty_env();
    let term = LatticeTerm::Const {
        name: "42".to_string(),
        ty: 2, // Int
    };
    assert!(sys.check(&env, &term, &2)); // Int <: Int
    assert!(sys.check(&env, &term, &1)); // Int <: Number
    assert!(sys.check(&env, &term, &0)); // Int <: Top
    assert!(!sys.check(&env, &term, &4)); // Int ≮: String
}

// ── Type inference ──

#[test]
fn lattice_infer_const() {
    let sys = test_system();
    let env = sys.empty_env();
    let term = LatticeTerm::Const { name: "42".to_string(), ty: 2 };
    assert_eq!(sys.infer(&env, &term), vec![2]);
}

#[test]
fn lattice_infer_var() {
    let sys = test_system();
    let env = sys.extend(&sys.empty_env(), "x", &2); // x: Int
    let term = LatticeTerm::Var("x".to_string());
    assert_eq!(sys.infer(&env, &term), vec![2]);
}

#[test]
fn lattice_infer_var_missing() {
    let sys = test_system();
    let env = sys.empty_env();
    let term = LatticeTerm::Var("y".to_string());
    assert_eq!(sys.infer(&env, &term), Vec::<usize>::new());
}

// ── Constructor application ──

#[test]
fn lattice_check_app() {
    let sys = test_system();
    let env = sys.empty_env();
    let term = LatticeTerm::App {
        head: "add".to_string(),
        args: vec![
            LatticeTerm::Const { name: "1".to_string(), ty: 2 },
            LatticeTerm::Const { name: "2".to_string(), ty: 2 },
        ],
    };
    assert!(sys.check(&env, &term, &2)); // add(Int, Int) : Int
    assert!(sys.check(&env, &term, &1)); // add(Int, Int) : Number
    assert!(!sys.check(&env, &term, &4)); // add(Int, Int) ≠ String
}

#[test]
fn lattice_check_app_wrong_arity() {
    let sys = test_system();
    let env = sys.empty_env();
    let term = LatticeTerm::App {
        head: "add".to_string(),
        args: vec![LatticeTerm::Const { name: "1".to_string(), ty: 2 }],
    };
    assert!(!sys.check(&env, &term, &2)); // wrong arity
}

// ── Inhabited ──

#[test]
fn lattice_inhabited() {
    let sys = test_system();
    let env = sys.empty_env();
    assert!(sys.is_inhabited(&env, &2)); // Int is inhabited
    assert!(!sys.is_inhabited(&env, &99)); // unknown type is not
}

// ── Top/Bottom ──

#[test]
fn lattice_top_bottom() {
    let sys = test_system();
    assert_eq!(sys.top(), Some(0));
    assert_eq!(sys.bottom(), Some(6));
}

// ── Environment extension ──

#[test]
fn lattice_extend_env() {
    let sys = test_system();
    let env = sys.empty_env();
    let env2 = sys.extend(&env, "x", &2);
    assert_eq!(env2.bindings.get("x"), Some(&2));
    assert!(env.bindings.get("x").is_none()); // original unchanged
}

// ── RT10: SFA dispatch analysis ──

#[test]
fn dispatch_analysis_empty() {
    let result = analyze_refinement_dispatch(&[]);
    assert!(result.disjoint_pairs.is_empty());
    assert!(result.subtype_pairs.is_empty());
    assert!(result.overlapping_pairs.is_empty());
    assert!(result.base_type_groups.is_empty());
}

#[test]
fn dispatch_analysis_different_bases() {
    let specs = vec![
        crate::RefinementTypeSpec {
            name: "PosInt".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x>0".to_string(),
        },
        crate::RefinementTypeSpec {
            name: "ShortStr".to_string(),
            base_category: "String".to_string(),
            variable_name: "s".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "len(s)<100".to_string(),
        },
    ];
    let result = analyze_refinement_dispatch(&specs);
    // Different bases → no pairwise analysis
    assert!(result.disjoint_pairs.is_empty());
    assert!(result.subtype_pairs.is_empty());
    assert_eq!(result.base_type_groups.len(), 2);
}

#[test]
fn dispatch_analysis_complement_predicates() {
    let specs = vec![
        crate::RefinementTypeSpec {
            name: "PosInt".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x>0".to_string(),
        },
        crate::RefinementTypeSpec {
            name: "NonPosInt".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x<=0".to_string(),
        },
    ];
    let result = analyze_refinement_dispatch(&specs);
    assert_eq!(result.disjoint_pairs.len(), 1, "complement predicates should be disjoint");
    assert_eq!(result.disjoint_pairs[0], ("PosInt".to_string(), "NonPosInt".to_string()));
}

#[test]
fn dispatch_analysis_identical_predicates() {
    let specs = vec![
        crate::RefinementTypeSpec {
            name: "PosA".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x>0".to_string(),
        },
        crate::RefinementTypeSpec {
            name: "PosB".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x>0".to_string(),
        },
    ];
    let result = analyze_refinement_dispatch(&specs);
    assert_eq!(result.subtype_pairs.len(), 1, "identical predicates should be mutual subtypes");
}

#[test]
fn dispatch_analysis_overlapping() {
    let specs = vec![
        crate::RefinementTypeSpec {
            name: "Positive".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x>0".to_string(),
        },
        crate::RefinementTypeSpec {
            name: "Small".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x<10".to_string(),
        },
    ];
    let result = analyze_refinement_dispatch(&specs);
    assert_eq!(
        result.overlapping_pairs.len(),
        1,
        "non-complementary predicates should be overlapping"
    );
}

#[test]
fn complement_predicate_detection() {
    assert!(is_complement_predicate("x>0", "x<=0"));
    assert!(is_complement_predicate("x>=0", "x<0"));
    assert!(is_complement_predicate("x==0", "x!=0"));
    assert!(!is_complement_predicate("x>0", "x>1"));
    assert!(!is_complement_predicate("x>0", "y<=0")); // different vars
}

// ── TypeSystemAlgebra ──

#[test]
fn type_algebra_evaluate() {
    let sys = test_system();
    let algebra = TypeSystemAlgebra::new(sys);

    assert!(algebra.evaluate_pred(&TypePred::True));
    assert!(!algebra.evaluate_pred(&TypePred::False));
    assert!(algebra.evaluate_pred(&TypePred::HasType(2))); // Int is inhabited
    assert!(algebra.evaluate_pred(&TypePred::Subtype { sub: 2, sup: 1 })); // Int <: Number
    assert!(!algebra.evaluate_pred(&TypePred::Subtype { sub: 1, sup: 2 })); // Number ≮: Int
}

#[test]
fn type_algebra_satisfiable() {
    let sys = test_system();
    let algebra = TypeSystemAlgebra::new(sys);

    assert!(algebra.is_satisfiable_pred(&TypePred::True));
    assert!(!algebra.is_satisfiable_pred(&TypePred::False));
    assert!(algebra.is_satisfiable_pred(&TypePred::HasType(2)));
    assert!(!algebra.is_satisfiable_pred(&TypePred::HasType(99))); // unknown type
}

#[test]
fn type_algebra_implies() {
    let sys = test_system();
    let algebra = TypeSystemAlgebra::new(sys);

    // Int <: Number implies Int <: Top (transitivity)
    let p = TypePred::Subtype { sub: 2, sup: 1 };
    let q = TypePred::Subtype { sub: 2, sup: 0 };
    assert!(algebra.implies_pred(&p, &q));

    // Int <: Number does NOT imply String <: Number
    let r = TypePred::Subtype { sub: 4, sup: 1 };
    assert!(!algebra.implies_pred(&p, &r));
}

#[test]
fn type_algebra_and_or_not() {
    let sys = test_system();
    let algebra = TypeSystemAlgebra::new(sys);

    let int_inhabited = TypePred::HasType(2);
    let string_inhabited = TypePred::HasType(4);

    // And: both inhabited
    let both = TypePred::And(Box::new(int_inhabited.clone()), Box::new(string_inhabited.clone()));
    assert!(algebra.evaluate_pred(&both));

    // Or: at least one
    let either = TypePred::Or(Box::new(int_inhabited.clone()), Box::new(TypePred::False));
    assert!(algebra.evaluate_pred(&either));

    // Not: negation
    let not_false = TypePred::Not(Box::new(TypePred::False));
    assert!(algebra.evaluate_pred(&not_false));
}

// ── RefinementTypeSystem ──

#[test]
fn refinement_base_subtype() {
    let (theory, store) = test_lattice();
    let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let env = ref_sys.empty_env();
    let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
    let number_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(1);

    // Base <: Base: Int <: Number
    assert!(ref_sys.is_subtype(&env, &int_base, &number_base));
    // Not reverse
    assert!(!ref_sys.is_subtype(&env, &number_base, &int_base));
}

#[test]
fn refinement_refined_to_base() {
    let (theory, store) = test_lattice();
    let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let env = ref_sys.empty_env();
    // { x: Int | Int <: Number } — a satisfied predicate
    let refined_int = RefType::Refined(RefinedType {
        base: 2,
        var: "x".to_string(),
        predicate: SubtypeConstraint { sub: 2, sup: 1 },
    });
    let number_base = RefType::Base(1);

    // Refined(Int, pred) <: Base(Number) — should succeed since Int <: Number
    assert!(ref_sys.is_subtype(&env, &refined_int, &number_base));
}

#[test]
fn refinement_inhabited() {
    let (theory, store) = test_lattice();
    let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let env = ref_sys.empty_env();

    // Base type: inhabited
    let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
    assert!(ref_sys.is_inhabited(&env, &int_base));

    // Refined with satisfiable predicate: inhabited
    let refined_ok = RefType::Refined(RefinedType {
        base: 2,
        var: "x".to_string(),
        predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number (true)
    });
    assert!(ref_sys.is_inhabited(&env, &refined_ok));
}

#[test]
fn refinement_join_drops_predicate() {
    let (theory, store) = test_lattice();
    let base_sys = LatticeTypeSystem::new(theory.clone(), store.clone(), HashMap::new());
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let env = ref_sys.empty_env();
    let int_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
    let float_base: RefType<TypeId, SubtypeConstraint> = RefType::Base(3);

    // join(Int, Float) = Number (as base type)
    let result = ref_sys.join(&env, &int_base, &float_base);
    assert_eq!(result, Some(RefType::Base(1))); // Number
}

#[test]
fn refinement_top_bottom() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    assert_eq!(ref_sys.top(), Some(RefType::Base(0))); // Top
    assert_eq!(ref_sys.bottom(), Some(RefType::Base(6))); // Bottom
}

// ── RT9: Substitution propagation ──

#[test]
fn apply_substitution_base_type_passthrough() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let base_ty: RefType<TypeId, SubtypeConstraint> = RefType::Base(2); // Int
    let constraint = SubtypeConstraint { sub: 2, sup: 1 }; // Int <: Number

    let result = ref_sys.apply_substitution(&base_ty, "x", &constraint);
    assert_eq!(result, Some(RefType::Base(2)), "base type should pass through unchanged");
}

#[test]
fn apply_substitution_mismatched_var() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let refined = RefType::Refined(RefinedType {
        base: 2, // Int
        var: "x".to_string(),
        predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number
    });
    let constraint = SubtypeConstraint { sub: 3, sup: 1 }; // Float <: Number

    // Substituting "y" when binding is "x" → pass through
    let result = ref_sys.apply_substitution(&refined, "y", &constraint);
    assert_eq!(result, Some(refined), "mismatched var should pass through");
}

#[test]
fn apply_substitution_matching_var_satisfiable() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let refined = RefType::Refined(RefinedType {
        base: 2, // Int
        var: "x".to_string(),
        predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number (always true)
    });
    // The value constraint is consistent with the predicate
    let value_constraint = SubtypeConstraint { sub: 2, sup: 0 }; // Int <: Top

    let result = ref_sys.apply_substitution(&refined, "x", &value_constraint);
    assert!(result.is_some(), "satisfiable substitution should succeed");
    assert_eq!(result, Some(RefType::Base(2)), "should reduce to base type");
}

#[test]
fn value_satisfies_refinement_base_always_true() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let base_ty: RefType<TypeId, SubtypeConstraint> = RefType::Base(2);
    let constraint = SubtypeConstraint { sub: 999, sup: 888 };

    assert!(
        ref_sys.value_satisfies_refinement(&base_ty, &constraint),
        "base type has no predicate — always satisfied"
    );
}

#[test]
fn value_satisfies_refinement_consistent() {
    let (theory, store) = test_lattice();
    let base_sys =
        LatticeTypeSystem::with_bounds(theory.clone(), store.clone(), HashMap::new(), 0, 6);
    let ref_sys = RefinementTypeSystem::new(base_sys, theory.clone(), 100);

    let refined = RefType::Refined(RefinedType {
        base: 2,
        var: "x".to_string(),
        predicate: SubtypeConstraint { sub: 2, sup: 1 }, // Int <: Number
    });
    let consistent = SubtypeConstraint { sub: 2, sup: 0 }; // Int <: Top

    assert!(
        ref_sys.value_satisfies_refinement(&refined, &consistent),
        "consistent constraint should satisfy refinement"
    );
}

// ── BooleanAlgebra integration ──

mod boolean_algebra_tests {
    use super::*;
    use crate::symbolic::BooleanAlgebra;

    #[test]
    fn type_algebra_boolean_algebra_contract() {
        let sys = test_system();
        let algebra = TypeSystemAlgebra::new(sys);

        let t = algebra.true_pred();
        let f = algebra.false_pred();

        // true ∧ false = false
        let tf = algebra.and(&t, &f);
        assert!(!algebra.is_satisfiable(&tf));

        // true ∨ false = true
        let t_or_f = algebra.or(&t, &f);
        assert!(algebra.is_satisfiable(&t_or_f));

        // ¬false = true
        let not_f = algebra.not(&f);
        assert!(algebra.is_satisfiable(&not_f));

        // witness(HasType(Int)) = Some(Int)
        let has_int = TypePred::HasType(2);
        assert_eq!(algebra.witness(&has_int), Some(2));

        // witness(false) = None
        assert_eq!(algebra.witness(&f), None);
    }
}

// ══════════════════════════════════════════════════════════════════════════
// SetTheoreticTypeSystem tests (Sprint RT3)
// ══════════════════════════════════════════════════════════════════════════

mod set_theoretic_tests {
    use super::*;
    use crate::automata::semiring::BooleanWeight;
    use crate::tree_automaton::{Term, TreeAutomaton, TreeTransition};

    /// Build a simple type system with constructors and type definitions:
    ///
    /// Constructors:
    ///   Zero : () → Nat          (arity 0)
    ///   Succ : (Nat) → Nat       (arity 1)
    ///   True : () → Bool         (arity 0)
    ///   False : () → Bool        (arity 0)
    ///   Pair : (Any, Any) → Pair (arity 2)
    ///
    /// Named types:
    ///   Nat  — accepts Zero and Succ(Nat)
    ///   Bool — accepts True and False
    ///   Any  — accepts everything (Top)
    fn test_set_system() -> SetTheoreticTypeSystem {
        let mut ctors = HashMap::new();
        ctors.insert("Zero".to_string(), 0);
        ctors.insert("Succ".to_string(), 1);
        ctors.insert("True".to_string(), 0);
        ctors.insert("False".to_string(), 0);
        ctors.insert("Pair".to_string(), 2);

        let mut sys = SetTheoreticTypeSystem::new(ctors);

        // Nat automaton: state 0 = Nat (accepting)
        //   Zero → q0, Succ(q0) → q0
        let mut nat_aut = TreeAutomaton::new();
        let q0 = nat_aut.add_state(true);
        nat_aut.add_transition(TreeTransition::leaf("Zero", q0, BooleanWeight(true)));
        nat_aut.add_transition(TreeTransition::unary("Succ", q0, q0, BooleanWeight(true)));
        sys.define_type("Nat", nat_aut);

        // Bool automaton: state 0 = Bool (accepting)
        //   True → q0, False → q0
        let mut bool_aut = TreeAutomaton::new();
        let q0 = bool_aut.add_state(true);
        bool_aut.add_transition(TreeTransition::leaf("True", q0, BooleanWeight(true)));
        bool_aut.add_transition(TreeTransition::leaf("False", q0, BooleanWeight(true)));
        sys.define_type("Bool", bool_aut);

        sys
    }

    // ── Emptiness check ──

    #[test]
    fn set_empty_automaton_is_empty() {
        let aut: TreeAutomaton<BooleanWeight> = TreeAutomaton::new();
        assert!(SetTheoreticTypeSystem::is_empty(&aut));
    }

    #[test]
    fn set_nat_automaton_not_empty() {
        let sys = test_set_system();
        let nat_aut = sys.type_to_automaton(&SetType::Atom("Nat".to_string()));
        assert!(!SetTheoreticTypeSystem::is_empty(&nat_aut));
    }

    // ── Basic subtyping ──

    #[test]
    fn set_reflexive_subtype() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        assert!(sys.is_subtype(&env, &nat, &nat));
    }

    #[test]
    fn set_nat_subtype_top() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        // Nat <: Top (all Nat values are values)
        assert!(sys.is_subtype(&env, &nat, &SetType::Top));
    }

    #[test]
    fn set_bottom_subtype_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        // Bottom <: Nat (empty set ⊆ any set)
        assert!(sys.is_subtype(&env, &SetType::Bottom, &nat));
    }

    #[test]
    fn set_nat_not_subtype_bool() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        // Nat ⊄ Bool (Zero is a Nat but not a Bool)
        assert!(!sys.is_subtype(&env, &nat, &bool_ty));
    }

    #[test]
    fn set_bool_not_subtype_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        // Bool ⊄ Nat (True is a Bool but not a Nat)
        assert!(!sys.is_subtype(&env, &bool_ty, &nat));
    }

    // ── Union types ──

    #[test]
    fn set_nat_subtype_nat_union_bool() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        let union = SetType::Union(Box::new(nat.clone()), Box::new(bool_ty));
        // Nat <: (Nat | Bool)
        assert!(sys.is_subtype(&env, &nat, &union));
    }

    #[test]
    fn set_union_not_subtype_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        let union = SetType::Union(Box::new(nat.clone()), Box::new(bool_ty));
        // (Nat | Bool) ⊄ Nat (True ∈ (Nat|Bool) but True ∉ Nat)
        assert!(!sys.is_subtype(&env, &union, &nat));
    }

    // ── Intersection types ──

    #[test]
    fn set_intersection_of_disjoint_is_empty() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        let intersection = SetType::Intersection(Box::new(nat), Box::new(bool_ty));
        // Nat ∩ Bool = ∅ (no value is both a Nat and a Bool)
        assert!(!sys.is_inhabited(&env, &intersection));
    }

    #[test]
    fn set_nat_intersection_top_is_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let intersection = SetType::Intersection(Box::new(nat.clone()), Box::new(SetType::Top));
        // Nat ∩ Top = Nat (subtype equivalence)
        assert!(sys.is_subtype(&env, &intersection, &nat));
        assert!(sys.is_subtype(&env, &nat, &intersection));
    }

    // ── Negation types ──

    #[test]
    fn set_negation_top_is_bottom() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let not_top = SetType::Negation(Box::new(SetType::Top));
        // ¬Top = ∅ (Bottom)
        assert!(!sys.is_inhabited(&env, &not_top));
    }

    // ── Type checking with terms ──

    #[test]
    fn set_check_zero_is_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let zero = Term::leaf("Zero");
        assert!(sys.check(&env, &zero, &nat));
    }

    #[test]
    fn set_check_succ_zero_is_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let succ_zero = Term::new("Succ", vec![Term::leaf("Zero")]);
        assert!(sys.check(&env, &succ_zero, &nat));
    }

    #[test]
    fn set_check_true_is_bool() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let bool_ty = SetType::Atom("Bool".to_string());
        let true_term = Term::leaf("True");
        assert!(sys.check(&env, &true_term, &bool_ty));
    }

    #[test]
    fn set_check_true_not_nat() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let true_term = Term::leaf("True");
        assert!(!sys.check(&env, &true_term, &nat));
    }

    // ── Inference ──

    #[test]
    fn set_infer_zero() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let zero = Term::leaf("Zero");
        let types = sys.infer(&env, &zero);
        // Zero should be inferred as Nat (not Bool)
        assert!(types.contains(&SetType::Atom("Nat".to_string())));
        assert!(!types.contains(&SetType::Atom("Bool".to_string())));
    }

    // ── Join / Meet ──

    #[test]
    fn set_join_is_union() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        let joined = sys.join(&env, &nat, &bool_ty);
        assert_eq!(joined, Some(SetType::Union(Box::new(nat.clone()), Box::new(bool_ty.clone()),)));
    }

    #[test]
    fn set_meet_is_intersection() {
        let sys = test_set_system();
        let env = sys.empty_env();
        let nat = SetType::Atom("Nat".to_string());
        let bool_ty = SetType::Atom("Bool".to_string());
        let met = sys.meet(&env, &nat, &bool_ty);
        assert_eq!(
            met,
            Some(SetType::Intersection(Box::new(nat.clone()), Box::new(bool_ty.clone()),))
        );
    }

    // ── Top / Bottom ──

    #[test]
    fn set_top_bottom() {
        let sys = test_set_system();
        assert_eq!(sys.top(), Some(SetType::Top));
        assert_eq!(sys.bottom(), Some(SetType::Bottom));
    }

    // ── Display ──

    #[test]
    fn set_type_display() {
        let ty = SetType::Union(
            Box::new(SetType::Atom("Nat".to_string())),
            Box::new(SetType::Negation(Box::new(SetType::Atom("Bool".to_string())))),
        );
        assert_eq!(format!("{ty}"), "(Nat | ~Bool)");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RT10 `.1`: structural refinement dispatch via the sym_tree recognizer
// ══════════════════════════════════════════════════════════════════════════════
//
// These prove structural disjointness / subtype that the string heuristic
// (`classify_predicate_overlap`) MISSES: two `Structural` refinements with
// distinct `predicate_repr`s fall through the heuristic to `Overlapping`, but the
// precise tree-automaton recognizer decides them. The grammar is the classic
// `List = Nil | Cons(Int, List)` cons-list.

#[cfg(feature = "sym-tree-structural")]
mod structural_dispatch_tests {
    use super::*;

    fn term(s: &str) -> crate::SyntaxItemSpec {
        crate::SyntaxItemSpec::Terminal(s.to_string())
    }
    fn nonterm(cat: &str, name: &str) -> crate::SyntaxItemSpec {
        crate::SyntaxItemSpec::NonTerminal {
            category: cat.to_string(),
            param_name: name.to_string(),
        }
    }
    fn ident(name: &str) -> crate::SyntaxItemSpec {
        crate::SyntaxItemSpec::IdentCapture { param_name: name.to_string() }
    }
    fn scalar_cat(name: &str, native: &str) -> crate::pipeline::CategoryInfo {
        crate::pipeline::CategoryInfo {
            name: name.to_string(),
            native_type: Some(native.to_string()),
            is_primary: false,
            has_var: true,
        }
    }
    fn struct_cat(name: &str, native: Option<&str>, primary: bool) -> crate::pipeline::CategoryInfo {
        crate::pipeline::CategoryInfo {
            name: name.to_string(),
            native_type: native.map(|s| s.to_string()),
            is_primary: primary,
            has_var: true,
        }
    }
    fn rule(
        label: &str,
        cat: &str,
        syntax: Vec<crate::SyntaxItemSpec>,
    ) -> (String, String, Vec<crate::SyntaxItemSpec>) {
        (label.to_string(), cat.to_string(), syntax)
    }

    /// The cons-list grammar: `List = Nil | Cons(Int, List)`, `Int` scalar.
    fn cons_list_grammar() -> (
        Vec<(String, String, Vec<crate::SyntaxItemSpec>)>,
        Vec<crate::pipeline::CategoryInfo>,
    ) {
        let categories = vec![
            struct_cat("Proc", None, true),
            scalar_cat("Int", "i64"),
            struct_cat("List", Some("Vec < Int >"), false),
        ];
        let all_syntax = vec![
            rule("IVar", "Int", vec![ident("x")]),
            rule("ProcList", "Proc", vec![nonterm("List", "l")]),
            rule("Nil", "List", vec![term("nil")]),
            rule("Cons", "List", vec![nonterm("Int", "h"), nonterm("List", "t")]),
        ];
        (all_syntax, categories)
    }

    fn structural_refinement(name: &str, base: &str, repr: &str) -> crate::RefinementTypeSpec {
        crate::RefinementTypeSpec {
            name: name.to_string(),
            base_category: base.to_string(),
            variable_name: "l".to_string(),
            predicate_kind: crate::RefinementPredKind::Structural,
            predicate_repr: repr.to_string(),
        }
    }

    /// `cons(x, nil)` (exactly-one-element lists) is DISJOINT from
    /// `cons(x, cons(y, t))` (≥2-element lists): the tree automaton proves their
    /// intersection empty. The string heuristic returns `Overlapping` (both are
    /// `Structural` with distinct reprs → falls through to the default), so this
    /// is a finding the heuristic MISSES.
    #[test]
    fn cons_nil_disjoint_from_cons_cons() {
        let (all_syntax, categories) = cons_list_grammar();
        let specs = vec![
            structural_refinement("One", "List", "l == cons(x, nil)"),
            structural_refinement("TwoPlus", "List", "l == cons(x, cons(y, t))"),
        ];

        // Heuristic baseline: distinct Structural reprs ⇒ Overlapping (MISS).
        let heuristic = analyze_refinement_dispatch(&specs);
        assert!(
            heuristic.disjoint_pairs.is_empty(),
            "string heuristic must NOT find these disjoint (it returns Overlapping): {:?}",
            heuristic.disjoint_pairs
        );
        assert_eq!(
            heuristic.overlapping_pairs.len(),
            1,
            "heuristic classifies the pair as Overlapping"
        );

        // Structural recognizer: PRECISE Disjoint.
        let structural =
            analyze_refinement_dispatch_structural(&specs, &all_syntax, &categories);
        assert_eq!(
            structural.disjoint_pairs,
            vec![("One".to_string(), "TwoPlus".to_string())],
            "tree automaton must prove cons(x,nil) ∩ cons(x,cons(y,t)) = ∅"
        );
        assert!(
            structural.overlapping_pairs.is_empty(),
            "the disjoint pair must not also be reported overlapping"
        );
        assert!(
            structural.subtype_pairs.is_empty(),
            "disjoint patterns are not in a subtype relation"
        );
    }

    /// `cons(x, cons(y, t))` (≥2-element lists) is a SUBTYPE of `cons(x, t)`
    /// (≥1-element lists): every ≥2-element list is a ≥1-element list, so
    /// `A ∩ ¬B = ∅`. The string heuristic returns `Overlapping` (the
    /// repr-containment subtype check only runs for `Presburger`), so this
    /// subtyping is a finding the heuristic MISSES.
    #[test]
    fn cons_cons_subtype_of_cons() {
        let (all_syntax, categories) = cons_list_grammar();
        let specs = vec![
            structural_refinement("TwoPlus", "List", "l == cons(x, cons(y, t))"),
            structural_refinement("OnePlus", "List", "l == cons(x, t)"),
        ];

        // Heuristic baseline: Overlapping (MISS — no Structural subtype rule).
        let heuristic = analyze_refinement_dispatch(&specs);
        assert!(
            heuristic.subtype_pairs.is_empty(),
            "string heuristic must NOT find the subtype: {:?}",
            heuristic.subtype_pairs
        );

        // Structural recognizer: PRECISE Subtype (TwoPlus <: OnePlus).
        let structural =
            analyze_refinement_dispatch_structural(&specs, &all_syntax, &categories);
        assert_eq!(
            structural.subtype_pairs,
            vec![("TwoPlus".to_string(), "OnePlus".to_string())],
            "tree automaton must prove cons(x,cons(y,t)) <: cons(x,t)"
        );
        assert!(
            structural.disjoint_pairs.is_empty(),
            "a subtype pair is not disjoint (the smaller is inhabited inside the larger)"
        );
    }

    /// The Supertype direction (operands swapped): `cons(x, t)` is a SUPERTYPE of
    /// `cons(x, cons(y, t))`, which the dispatch records as the (sub, super)
    /// `(TwoPlus, OnePlus)` pair via the `Supertype` arm.
    #[test]
    fn cons_supertype_direction() {
        let (all_syntax, categories) = cons_list_grammar();
        let specs = vec![
            // OnePlus first this time ⇒ the precise relation is Supertype(a,b),
            // recorded as subtype (b, a) = (TwoPlus, OnePlus).
            structural_refinement("OnePlus", "List", "l == cons(x, t)"),
            structural_refinement("TwoPlus", "List", "l == cons(x, cons(y, t))"),
        ];
        let structural =
            analyze_refinement_dispatch_structural(&specs, &all_syntax, &categories);
        assert_eq!(
            structural.subtype_pairs,
            vec![("TwoPlus".to_string(), "OnePlus".to_string())],
            "Supertype(OnePlus, TwoPlus) is recorded as subtype (TwoPlus, OnePlus)"
        );
    }

    /// Defensive fallback: a `Structural` refinement whose `predicate_repr` does
    /// not parse into a tree pattern (no relation token) must fall back to the
    /// heuristic — never worse than the status quo (here: Overlapping).
    #[test]
    fn unparseable_structural_falls_back_to_heuristic() {
        let (all_syntax, categories) = cons_list_grammar();
        let specs = vec![
            structural_refinement("Weird", "List", "some_relation(l)"),
            structural_refinement("AlsoWeird", "List", "other_relation(l)"),
        ];
        let structural =
            analyze_refinement_dispatch_structural(&specs, &all_syntax, &categories);
        // No parse ⇒ no precise disjoint/subtype; the heuristic's Overlapping
        // verdict is used, so the pair is Overlapping (not disjoint, not subtype).
        assert!(structural.disjoint_pairs.is_empty());
        assert!(structural.subtype_pairs.is_empty());
        assert_eq!(structural.overlapping_pairs.len(), 1);
    }

    /// Non-structural pairs (`Presburger`) are left entirely on the heuristic:
    /// the structural dispatch must reproduce the heuristic's verdict for them.
    #[test]
    fn presburger_pairs_unchanged() {
        let (all_syntax, categories) = cons_list_grammar();
        let pos = crate::RefinementTypeSpec {
            name: "Pos".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x > 0".to_string(),
        };
        let nonpos = crate::RefinementTypeSpec {
            name: "NonPos".to_string(),
            base_category: "Int".to_string(),
            variable_name: "x".to_string(),
            predicate_kind: crate::RefinementPredKind::Presburger,
            predicate_repr: "x <= 0".to_string(),
        };
        let specs = vec![pos, nonpos];
        let heuristic = analyze_refinement_dispatch(&specs);
        let structural =
            analyze_refinement_dispatch_structural(&specs, &all_syntax, &categories);
        // Identical disjoint/subtype/overlapping verdicts for the Presburger pair.
        assert_eq!(heuristic.disjoint_pairs, structural.disjoint_pairs);
        assert_eq!(heuristic.subtype_pairs, structural.subtype_pairs);
        assert_eq!(heuristic.overlapping_pairs, structural.overlapping_pairs);
        // And the heuristic genuinely finds these disjoint (x>0 vs x<=0).
        assert_eq!(
            structural.disjoint_pairs,
            vec![("Pos".to_string(), "NonPos".to_string())]
        );
    }
}
