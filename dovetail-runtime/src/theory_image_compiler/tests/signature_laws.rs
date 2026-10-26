// An absent certificate means these sufficient source schemas were not found;
// it does not assert that an algebraic law is false in every model.
use super::*;
use mettail_grammar_core::{CostImageV1, SourceSignatureLawV1, VerifiedCostImageV1};

#[derive(Clone, Copy, Debug, Default)]
struct LawCase {
    salt: u16,
    permutation: usize,
    shared_variables: bool,
    right_unit: bool,
    reversed: [bool; 3],
    rotation: usize,
    empty_roster: bool,
}

struct LawFixture {
    language: LanguageCoreV1,
    equations: [usize; 3],
    variables: [TheoryVariableId; 3],
}

struct LawArena<'a> {
    sort: &'a str,
    product: &'a str,
    unit: &'a str,
    shared: bool,
    variables: [Option<TheoryTermId>; 3],
    terms: Vec<TheoryTermNodeV1>,
}

impl LawArena<'_> {
    fn push(&mut self, form: TheoryTermFormV1) -> TheoryTermId {
        let id = TheoryTermId(self.terms.len() as u32);
        self.terms
            .push(TheoryTermNodeV1 { sort: self.sort.into(), form });
        id
    }

    fn variable(&mut self, variable: TheoryVariableId) -> TheoryTermId {
        if self.shared {
            if let Some(term) = self.variables[variable.0 as usize] {
                return term;
            }
        }
        let term = self.push(TheoryTermFormV1::Variable(variable));
        self.variables[variable.0 as usize] = Some(term);
        term
    }

    fn product(&mut self, left: TheoryTermId, right: TheoryTermId) -> TheoryTermId {
        self.push(TheoryTermFormV1::Constructor {
            constructor: self.product.into(),
            arguments: vec![left, right],
        })
    }

    fn unit(&mut self) -> TheoryTermId {
        self.push(TheoryTermFormV1::Constructor {
            constructor: self.unit.into(),
            arguments: Vec::new(),
        })
    }
}

fn law_fixture(case: LawCase) -> LawFixture {
    let mut language = costed_fixture();
    let sort = format!("Resource_{}", case.salt);
    let product = format!("Combine_{}", case.salt);
    let unit = format!("Identity_{}", case.salt);
    for declaration in &mut language.theory.sorts {
        if declaration.name == "Sig" {
            declaration.name = sort.clone();
        }
    }
    for constructor in &mut language.theory.constructors {
        for domain in &mut constructor.domain {
            if domain == "Sig" {
                *domain = sort.clone();
            }
        }
        if constructor.codomain == "Sig" {
            constructor.codomain = sort.clone();
        }
        if constructor.name == "SigUnit" {
            constructor.name = unit.clone();
        } else if constructor.name == "SigProduct" {
            constructor.name = product.clone();
        }
    }
    for rewrite in &mut language.theory.rewrites {
        for term in &mut rewrite.arena.terms {
            if term.sort == "Sig" {
                term.sort = sort.clone();
            }
            if let TheoryTermFormV1::Constructor { constructor, .. } = &mut term.form {
                if constructor == "SigUnit" {
                    *constructor = unit.clone();
                } else if constructor == "SigProduct" {
                    *constructor = product.clone();
                }
            }
        }
    }
    for action in &mut language.theory.actions {
        action.grade = sort.clone();
    }
    let cost = language.theory.cost.as_mut().unwrap();
    cost.signature_sort = sort.clone();
    cost.product = product.clone();
    cost.unit = unit.clone();
    // These labels and the inherited continued/interactive placeholders are
    // untrusted metadata, not evidence for these equations or those profiles.
    cost.laws = vec!["associativity".into(), "commutativity".into(), "unit".into()];
    if case.empty_roster {
        cost.grade_rules.clear();
        language.theory.rewrites.clear();
        language.theory.actions.clear();
    }
    // Role recognition must follow the admitted IDs after declaration reordering.
    language.theory.sorts.rotate_left(case.rotation);
    language.theory.constructors.rotate_left(case.permutation);
    let permutations = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    let variables = permutations[case.permutation].map(TheoryVariableId);
    let mut laws = Vec::new();
    let names: [String; 3] = std::array::from_fn(|index| format!("e_{}_{index}", case.salt));
    for (index, name) in names.iter().enumerate() {
        let mut arena = LawArena {
            sort: &sort,
            product: &product,
            unit: &unit,
            shared: case.shared_variables,
            variables: [None; 3],
            terms: Vec::new(),
        };
        let x = arena.variable(variables[0]);
        let (mut left, mut right) = match index {
            0 => {
                let y = arena.variable(variables[1]);
                let xy = arena.product(x, y);
                let z = arena.variable(variables[2]);
                let left = arena.product(xy, z);
                let x = arena.variable(variables[0]);
                let y = arena.variable(variables[1]);
                let z = arena.variable(variables[2]);
                let yz = arena.product(y, z);
                (left, arena.product(x, yz))
            },
            1 => {
                let y = arena.variable(variables[1]);
                let left = arena.product(x, y);
                let y = arena.variable(variables[1]);
                let x = arena.variable(variables[0]);
                (left, arena.product(y, x))
            },
            _ => {
                let unit = arena.unit();
                let left = if case.right_unit {
                    arena.product(x, unit)
                } else {
                    arena.product(unit, x)
                };
                (left, arena.variable(variables[0]))
            },
        };
        if case.reversed[index] {
            std::mem::swap(&mut left, &mut right);
        }
        laws.push(TheoryEquationV1 {
            name: name.clone(),
            arena: TheoryRuleArenaV1 {
                variables: (0..3)
                    .map(|id| TheoryVariableV1 {
                        id: TheoryVariableId(id),
                        name: format!("parameter_{}_{id}", case.salt),
                        sort: sort.clone(),
                        role: TheoryVariableRoleV1::Input,
                    })
                    .collect(),
                terms: arena.terms,
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left,
            right,
        });
    }
    laws.rotate_left(case.rotation);
    // Keep the unrelated Expr commutativity equation before the signature laws.
    language.theory.equations.extend(laws);
    let equations = names.map(|name| {
        language
            .theory
            .equations
            .iter()
            .position(|equation| equation.name == name)
            .unwrap()
    });
    LawFixture { language, equations, variables }
}

fn with_verified<T>(
    language: &LanguageCoreV1,
    check: impl FnOnce(VerifiedCostImageV1<'_>) -> T,
) -> T {
    language
        .validate()
        .expect("the recognizer fixture must first be valid source");
    let limits = TheoryImageAdmissionLimits::default();
    let semantic =
        compile_theory_semantic_image(language, limits).expect("source-exact semantic image");
    let cost = CostImageV1::compile(language, &semantic, limits)
        .expect("source-exact cost image")
        .expect("fixture retains its cost declaration");
    check(
        cost.verified(language, &semantic, limits)
            .expect("admitted cost image"),
    )
}

fn assert_laws(fixture: &LawFixture, case: LawCase) {
    with_verified(&fixture.language, |verified| {
        let certificate = verified
            .check_source_signature_acu()
            .expect("all three source laws");
        let retained = certificate.cost_image();
        assert_eq!(retained.fingerprint(), verified.fingerprint());
        assert!(std::ptr::eq(retained.language(), verified.language()));
        assert!(std::ptr::eq(retained.semantic_image(), verified.semantic_image()));
        assert_eq!(retained.grade_sort(), verified.grade_sort());
        assert_eq!(retained.unit_constructor(), verified.unit_constructor());
        assert_eq!(retained.product_constructor(), verified.product_constructor());
        let association = certificate.associativity();
        assert_eq!(association.equation as usize, fixture.equations[0]);
        assert_eq!(association.direction == TheoryRuleDirectionV1::Reverse, case.reversed[0]);
        let SourceSignatureLawV1::Associativity { variables } = association.law else {
            panic!("association witness must identify its schema");
        };
        assert_eq!(variables, fixture.variables);
        let commutation = certificate.commutativity();
        assert_eq!(commutation.equation as usize, fixture.equations[1]);
        let SourceSignatureLawV1::Commutativity { variables } = commutation.law else {
            panic!("commutation witness must identify its schema");
        };
        let [x, y, _] = fixture.variables;
        let flipped = case.reversed[1] ^ (commutation.direction == TheoryRuleDirectionV1::Reverse);
        assert_eq!(variables, if flipped { [y, x] } else { [x, y] });
        let unit = certificate.unit();
        assert_eq!(unit.equation as usize, fixture.equations[2]);
        assert_eq!(unit.direction == TheoryRuleDirectionV1::Reverse, case.reversed[2]);
        match unit.law {
            SourceSignatureLawV1::LeftUnit { variable } => {
                assert!(!case.right_unit);
                assert_eq!(variable, fixture.variables[0]);
            },
            SourceSignatureLawV1::RightUnit { variable } => {
                assert!(case.right_unit);
                assert_eq!(variable, fixture.variables[0]);
            },
            _ => panic!("unit witness must identify the authored side"),
        }
    });
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn signature_acu_survives_renaming_order_reversal_and_variable_sharing(
        salt in any::<u16>(),
        permutation in 0usize..6,
        shared_variables in any::<bool>(),
        right_unit in any::<bool>(),
        reversed in any::<[bool; 3]>(),
        rotation in 0usize..3,
        empty_roster in any::<bool>(),
    ) {
        let case = LawCase { salt, permutation, shared_variables, right_unit, reversed, rotation, empty_roster };
        assert_laws(&law_fixture(case), case);
    }

    #[test]
    fn signature_acu_requires_every_source_law_despite_metadata_labels(missing in 0usize..3) {
        let mut fixture = law_fixture(LawCase::default());
        fixture.language.theory.equations.remove(fixture.equations[missing]);
        with_verified(&fixture.language, |verified| assert!(verified.check_source_signature_acu().is_none()));
    }

    #[test]
    fn signature_acu_rejects_repeated_variable_ids_even_with_distinct_term_nodes(
        permutation in 0usize..6,
        reversed in any::<bool>(),
    ) {
        let mut fixture = law_fixture(LawCase { permutation, reversed: [reversed, false, false], ..LawCase::default() });
        let [x, _, z] = fixture.variables;
        for term in &mut fixture.language.theory.equations[fixture.equations[0]].arena.terms {
            if let TheoryTermFormV1::Variable(variable) = &mut term.form {
                if *variable == z { *variable = x; }
            }
        }
        with_verified(&fixture.language, |verified| assert!(verified.check_source_signature_acu().is_none()));
    }

    #[test]
    fn signature_acu_schema_depth_does_not_limit_unrelated_terms_or_constructor_arity(
        depth in 4usize..=12,
        arity in 3usize..=7,
    ) {
        let case = LawCase::default();
        let mut fixture = law_fixture(case);
        let mut terms = vec![term_variable(0)];
        for index in 0..depth {
            terms.push(term_constructor("Wrap", vec![TheoryTermId(index as u32)]));
        }
        fixture.language.theory.equations.push(TheoryEquationV1 {
            name: "unrelated-deep-equation".into(),
            arena: TheoryRuleArenaV1 {
                variables: vec![variable(0, "deep-value")],
                terms,
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left: TheoryTermId(depth as u32),
            right: TheoryTermId((depth - 1) as u32),
        });
        let sort = fixture.language.theory.cost.as_ref().unwrap().signature_sort.clone();
        fixture.language.theory.constructors.push(TheoryConstructorV1 {
            name: "UnrelatedWide".into(), domain: vec![sort.clone(); arity], codomain: sort.clone(),
        });
        let mut terms: Vec<_> = (0..3).map(|id| TheoryTermNodeV1 {
            sort: sort.clone(), form: TheoryTermFormV1::Variable(TheoryVariableId(id)),
        }).collect();
        terms.push(TheoryTermNodeV1 {
            sort: sort.clone(),
            form: TheoryTermFormV1::Constructor {
                constructor: "UnrelatedWide".into(),
                arguments: (0..arity).map(|index| TheoryTermId((index % 3) as u32)).collect(),
            },
        });
        fixture.language.theory.equations.push(TheoryEquationV1 {
            name: "unrelated-wide-equation".into(),
            arena: TheoryRuleArenaV1 {
                variables: (0..3).map(|id| TheoryVariableV1 {
                    id: TheoryVariableId(id), name: format!("wide-{id}"), sort: sort.clone(), role: TheoryVariableRoleV1::Input,
                }).collect(),
                terms,
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left: TheoryTermId(3), right: TheoryTermId(0),
        });
        assert_laws(&fixture, case);
    }
}

#[test]
fn signature_acu_accepts_both_unit_sides_and_orientations_with_an_empty_roster() {
    for right_unit in [false, true] {
        for reverse in [false, true] {
            for shared_variables in [false, true] {
                let case = LawCase {
                    right_unit,
                    reversed: [reverse; 3],
                    shared_variables,
                    empty_roster: true,
                    permutation: 5,
                    ..LawCase::default()
                };
                assert_laws(&law_fixture(case), case);
            }
        }
    }
}

#[test]
fn signature_acu_rejects_another_product_with_the_same_signature() {
    let mut fixture = law_fixture(LawCase::default());
    let cost = fixture.language.theory.cost.as_ref().unwrap();
    let product = cost.product.clone();
    let sort = cost.signature_sort.clone();
    fixture
        .language
        .theory
        .constructors
        .push(TheoryConstructorV1 {
            name: "DifferentProduct".into(),
            domain: vec![sort.clone(), sort.clone()],
            codomain: sort,
        });
    for term in &mut fixture.language.theory.equations[fixture.equations[0]]
        .arena
        .terms
    {
        if let TheoryTermFormV1::Constructor { constructor, .. } = &mut term.form {
            if *constructor == product {
                *constructor = "DifferentProduct".into();
            }
        }
    }
    with_verified(&fixture.language, |verified| {
        assert!(verified.check_source_signature_acu().is_none())
    });
}

#[test]
fn signature_acu_rejects_another_unit_with_the_same_signature() {
    let mut fixture = law_fixture(LawCase::default());
    let cost = fixture.language.theory.cost.as_ref().unwrap();
    let unit = cost.unit.clone();
    let sort = cost.signature_sort.clone();
    fixture
        .language
        .theory
        .constructors
        .push(TheoryConstructorV1 {
            name: "DifferentUnit".into(),
            domain: Vec::new(),
            codomain: sort,
        });
    for term in &mut fixture.language.theory.equations[fixture.equations[2]]
        .arena
        .terms
    {
        if let TheoryTermFormV1::Constructor { constructor, .. } = &mut term.form {
            if *constructor == unit {
                *constructor = "DifferentUnit".into();
            }
        }
    }
    with_verified(&fixture.language, |verified| {
        assert!(verified.check_source_signature_acu().is_none())
    });
}

#[test]
fn signature_acu_skips_earlier_near_misses_and_retains_first_checked_witnesses() {
    let case = LawCase::default();
    let mut fixture = law_fixture(case);
    let [x, y, z] = fixture.variables;
    let mut repeated = fixture.language.theory.equations[fixture.equations[0]].clone();
    repeated.name = "earlier-repeated-variable-association".into();
    for term in &mut repeated.arena.terms {
        if let TheoryTermFormV1::Variable(variable) = &mut term.form {
            if *variable == z {
                *variable = x;
            }
        }
    }
    let mut near_commutation = fixture.language.theory.equations[fixture.equations[1]].clone();
    near_commutation.name = "earlier-product-xy-equals-yy".into();
    let TheoryTermFormV1::Constructor { arguments, .. } =
        &near_commutation.arena.terms[near_commutation.right.0 as usize].form
    else {
        panic!("commutativity fixture has a product on the right");
    };
    let right_leaf = arguments[1];
    near_commutation.arena.terms[right_leaf.0 as usize].form = TheoryTermFormV1::Variable(y);
    fixture
        .language
        .theory
        .equations
        .splice(0..0, [repeated, near_commutation]);
    fixture.equations = fixture.equations.map(|index| index + 2);
    for index in fixture.equations {
        let mut later = fixture.language.theory.equations[index].clone();
        later.name.push_str("-later-duplicate");
        fixture.language.theory.equations.push(later);
    }
    assert_laws(&fixture, case);
}

#[test]
fn reflexive_product_equation_is_rejected_before_signature_certification() {
    let mut fixture = law_fixture(LawCase::default());
    let equation = &mut fixture.language.theory.equations[fixture.equations[1]];
    let name = equation.name.clone();
    let TheoryTermFormV1::Constructor { arguments, .. } =
        &equation.arena.terms[equation.right.0 as usize].form
    else {
        panic!("commutativity fixture has a product on the right");
    };
    let [first, second] = arguments.as_slice() else {
        panic!("commutativity fixture product is binary");
    };
    let (first, second) = (*first, *second);
    equation.arena.terms[first.0 as usize].form = TheoryTermFormV1::Variable(fixture.variables[0]);
    equation.arena.terms[second.0 as usize].form = TheoryTermFormV1::Variable(fixture.variables[1]);
    // Both sides are x*y with distinct term nodes and distinct variable IDs.
    // The source is typed, but no verified image can cross the existing
    // non-progressing-equation gate to reach the sufficient ACU checker.
    fixture
        .language
        .validate()
        .expect("reflexive product is well-typed source");
    assert!(matches!(
        compile_theory_semantic_image(&fixture.language, TheoryImageAdmissionLimits::default()),
        Err(TheoryImageCompileError::NonProgressing { rule }) if rule == name
    ));
}

#[test]
fn signature_acu_rejects_conditional_laws_and_non_input_unit_variables() {
    for law in 0..3 {
        let mut fixture = law_fixture(LawCase::default());
        let arena = &mut fixture.language.theory.equations[fixture.equations[law]].arena;
        arena.premises.push(TheoryPremiseNodeV1 {
            form: TheoryPremiseFormV1::Guard(CanonicalValue::String("condition".into())),
        });
        arena.premise_roots.push(TheoryPremiseId(0));
        with_verified(&fixture.language, |verified| {
            assert!(verified.check_source_signature_acu().is_none())
        });
    }
    let mut fixture = law_fixture(LawCase::default());
    fixture.language.theory.equations[fixture.equations[2]]
        .arena
        .variables[0]
        .role = TheoryVariableRoleV1::Binder;
    with_verified(&fixture.language, |verified| {
        assert!(verified.check_source_signature_acu().is_none())
    });
}

#[test]
fn malformed_signature_law_source_is_rejected_before_recognition() {
    for malformed in 0..4 {
        let mut fixture = law_fixture(LawCase::default());
        let equation = &mut fixture.language.theory.equations[fixture.equations[0]];
        match malformed {
            0 => {
                for term in &mut equation.arena.terms {
                    if let TheoryTermFormV1::Constructor { constructor, .. } = &mut term.form {
                        *constructor = "UndeclaredProduct".into();
                    }
                }
            },
            1 => equation.arena.terms[0].sort = "Expr".into(),
            2 => equation.arena.premise_roots.push(TheoryPremiseId(0)),
            _ => equation.arena.premises.push(TheoryPremiseNodeV1 {
                form: TheoryPremiseFormV1::Guard(CanonicalValue::String("unreachable".into())),
            }),
        }
        assert!(fixture.language.validate().is_err(), "malformed source case {malformed}");
    }
}

#[test]
fn signature_acu_certificate_retains_its_exact_source_bound_cost_image() {
    let fingerprint = |salt| {
        let fixture = law_fixture(LawCase { salt, ..LawCase::default() });
        with_verified(&fixture.language, |verified| {
            let certificate = verified
                .check_source_signature_acu()
                .expect("source ACU laws");
            assert_eq!(certificate.cost_image().fingerprint(), verified.fingerprint());
            certificate.cost_image().fingerprint()
        })
    };
    assert_ne!(fingerprint(1), fingerprint(2));
}
