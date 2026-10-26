//! Admission of the exact authored equation roster, not a second normalizer.
//! Unsupported valid presentations return no certificate; malformed source or
//! a mismatched image must fail the earlier source/image admission boundary.

mod carrier_domain;
mod runtime;

use super::*;
use mettail_grammar_core::{SourceEquationSectionLawV1 as Law, SourceEquationSectionRolesV1};

const LAWS: [Law; 10] = [
    Law::AltZeroLeft,
    Law::AltZeroRight,
    Law::AltIdempotent,
    Law::ProductZeroLeft,
    Law::ProductZeroRight,
    Law::ProductUnitLeft,
    Law::ProductUnitRight,
    Law::ClosureZero,
    Law::ClosureUnit,
    Law::ClosureNested,
];

#[derive(Clone, Debug, Default)]
struct SectionCase {
    salt: u16,
    declaration_rotation: usize,
    reverse_declarations: bool,
    equation_order: [u8; 10],
    reversed: [bool; 10],
    variable: u32,
    shared: bool,
    duplicate: Option<usize>,
}

#[derive(Clone, Copy)]
struct ExpectedWitness {
    law: Law,
    direction: TheoryRuleDirectionV1,
    variable: Option<TheoryVariableId>,
}

struct SectionFixture {
    language: LanguageCoreV1,
    roles: SourceEquationSectionRolesV1,
    sort: String,
    names: [String; 5],
    expected: Vec<ExpectedWitness>,
}

struct SectionArena<'a> {
    sort: &'a str,
    names: &'a [String; 5],
    shared: bool,
    variables: [Option<TheoryTermId>; 3],
    terms: Vec<TheoryTermNodeV1>,
}

impl<'a> SectionArena<'a> {
    fn new(sort: &'a str, names: &'a [String; 5], shared: bool) -> Self {
        Self {
            sort,
            names,
            shared,
            variables: [None; 3],
            terms: Vec::new(),
        }
    }

    fn push(&mut self, form: TheoryTermFormV1) -> TheoryTermId {
        let id = TheoryTermId(u32::try_from(self.terms.len()).expect("bounded section arena"));
        self.terms
            .push(TheoryTermNodeV1 { sort: self.sort.into(), form });
        id
    }

    fn variable(&mut self, id: u32) -> TheoryTermId {
        if self.shared {
            if let Some(term) = self.variables[id as usize] {
                return term;
            }
        }
        let term = self.push(TheoryTermFormV1::Variable(TheoryVariableId(id)));
        self.variables[id as usize] = Some(term);
        term
    }

    fn app(&mut self, role: usize, arguments: Vec<TheoryTermId>) -> TheoryTermId {
        self.push(TheoryTermFormV1::Constructor {
            constructor: self.names[role].clone(),
            arguments,
        })
    }

    fn finish(self, salt: u16) -> TheoryRuleArenaV1 {
        TheoryRuleArenaV1 {
            // Dense IDs stay valid while the ID actually used by a law varies.
            // Unused declarations are not evidence of a schema variable.
            variables: (0..3)
                .map(|id| TheoryVariableV1 {
                    id: TheoryVariableId(id),
                    name: format!("parameter_{salt}_{id}"),
                    sort: self.sort.into(),
                    role: TheoryVariableRoleV1::Input,
                })
                .collect(),
            terms: self.terms,
            premises: Vec::new(),
            premise_roots: Vec::new(),
        }
    }
}

fn source_equation(
    law: usize,
    case: &SectionCase,
    sort: &str,
    names: &[String; 5],
) -> (TheoryEquationV1, ExpectedWitness) {
    let mut arena = SectionArena::new(sort, names, case.shared);
    let (mut left, mut right) = match law {
        0..=6 => {
            let x = arena.variable(case.variable);
            let other = match law {
                2 => arena.variable(case.variable),
                5 | 6 => arena.app(1, Vec::new()),
                _ => arena.app(0, Vec::new()),
            };
            let arguments = if matches!(law, 0 | 3 | 5) {
                vec![other, x]
            } else {
                vec![x, other]
            };
            let left = arena.app(if law <= 2 { 2 } else { 3 }, arguments);
            let right = if matches!(law, 3 | 4) {
                arena.app(0, Vec::new())
            } else {
                arena.variable(case.variable)
            };
            (left, right)
        },
        7 | 8 => {
            let constant = arena.app(if law == 7 { 0 } else { 1 }, Vec::new());
            let left = arena.app(4, vec![constant]);
            (left, arena.app(1, Vec::new()))
        },
        9 => {
            let x = arena.variable(case.variable);
            let inner = arena.app(4, vec![x]);
            let left = arena.app(4, vec![inner]);
            let right = if case.shared {
                inner
            } else {
                let x = arena.variable(case.variable);
                arena.app(4, vec![x])
            };
            (left, right)
        },
        _ => panic!("the fixture contains exactly ten schema kinds"),
    };
    // The existing source validator requires RHS variables to occur on the
    // authored LHS. Reversing an erasing product law violates that boundary;
    // those cases are tested separately as invalid source, not admitted laws.
    let reverse = case.reversed[law] && !matches!(law, 3 | 4);
    if reverse {
        std::mem::swap(&mut left, &mut right);
    }
    (
        TheoryEquationV1 {
            name: format!("equation_{}_{law}", case.salt),
            arena: arena.finish(case.salt),
            left,
            right,
        },
        ExpectedWitness {
            law: LAWS[law],
            direction: if reverse {
                TheoryRuleDirectionV1::Reverse
            } else {
                TheoryRuleDirectionV1::Forward
            },
            variable: (!matches!(law, 7 | 8)).then_some(TheoryVariableId(case.variable)),
        },
    )
}

fn constructor_id(language: &LanguageCoreV1, name: &str) -> TheoryConstructorId {
    TheoryConstructorId(
        u32::try_from(
            language
                .theory
                .constructors
                .iter()
                .position(|constructor| constructor.name == name)
                .expect("fixture constructor is declared"),
        )
        .expect("bounded constructor roster"),
    )
}

fn section_fixture(case: &SectionCase) -> SectionFixture {
    let mut language = fixture();
    language.theory.equations.clear();
    // Keep the unrelated Expr rewrite/action: neither belongs to the equation
    // roster, and a section certificate must not accidentally include them.
    let sort = format!("Section_{}", case.salt);
    let other_sort = format!("Other_{}", case.salt);
    for name in [&sort, &other_sort] {
        language.theory.sorts.push(TheorySortV1 {
            name: name.clone(),
            kind: TheorySortKindV1::Opaque { abi: format!("test/section/{name}") },
        });
    }
    let names = ["Zero", "Unit", "Alternative", "Product", "Closure"]
        .map(|name| format!("section_{}_{name}", case.salt));
    for (name, arity) in names.iter().zip([0, 0, 2, 2, 1]) {
        language.theory.constructors.push(TheoryConstructorV1 {
            name: name.clone(),
            domain: vec![sort.clone(); arity],
            codomain: sort.clone(),
        });
    }
    // Same-signature decoys ensure admission uses exact identities, not arity.
    for (name, arity) in [
        ("OtherConstant", 0),
        ("OtherBinary", 2),
        ("Plus", 1),
        ("Optional", 1),
        ("Repeat", 1),
    ] {
        language.theory.constructors.push(TheoryConstructorV1 {
            name: format!("section_{}_{name}", case.salt),
            domain: vec![sort.clone(); arity],
            codomain: sort.clone(),
        });
    }
    language.theory.constructors.push(TheoryConstructorV1 {
        name: format!("section_{}_WrongSort", case.salt),
        domain: vec![other_sort.clone(); 2],
        codomain: other_sort,
    });
    let count = language.theory.constructors.len();
    language
        .theory
        .constructors
        .rotate_left(case.declaration_rotation % count);
    language
        .theory
        .sorts
        .rotate_left(case.declaration_rotation % 3);
    if case.reverse_declarations {
        language.theory.constructors.reverse();
        language.theory.sorts.reverse();
    }
    let roles = SourceEquationSectionRolesV1 {
        sort: TheorySortId(
            u32::try_from(
                language
                    .theory
                    .sorts
                    .iter()
                    .position(|item| item.name == sort)
                    .expect("section sort is declared"),
            )
            .expect("bounded sort roster"),
        ),
        zero: constructor_id(&language, &names[0]),
        unit: constructor_id(&language, &names[1]),
        alternative: constructor_id(&language, &names[2]),
        product: constructor_id(&language, &names[3]),
        closure: constructor_id(&language, &names[4]),
    };
    let mut order: Vec<_> = (0..10).collect();
    order.sort_by_key(|&law| (case.equation_order[law], law));
    let mut expected = Vec::new();
    for law in order {
        let (equation, witness) = source_equation(law, case, &sort, &names);
        language.theory.equations.push(equation);
        expected.push(witness);
    }
    if let Some(law) = case.duplicate {
        let (mut equation, witness) = source_equation(law, case, &sort, &names);
        equation.name.push_str("_duplicate");
        language.theory.equations.push(equation);
        expected.push(witness);
    }
    SectionFixture { language, roles, sort, names, expected }
}

fn compiled_section(language: &LanguageCoreV1) -> TheorySemanticImageV1 {
    language
        .validate()
        .expect("section fixture is valid source before recognition");
    let limits = TheoryImageAdmissionLimits::default();
    let semantic = compile_theory_semantic_image(language, limits)
        .expect("valid section fixture compiles through the existing compiler");
    semantic
        .validate(language, limits)
        .expect("the image is source-exact before recognition");
    semantic
}

fn assert_admitted(fixture: &SectionFixture) {
    let semantic = compiled_section(&fixture.language);
    let certificate = semantic
        .check_source_equation_section(
            &fixture.language,
            fixture.roles,
            TheoryImageAdmissionLimits::default(),
        )
        .expect("valid source/image admission")
        .expect("the complete exact equation roster is supported");
    assert!(std::ptr::eq(certificate.language(), &fixture.language));
    assert!(std::ptr::eq(certificate.semantic_image(), &semantic));
    assert_eq!(certificate.roles(), fixture.roles);
    assert_eq!(certificate.witnesses().len(), fixture.language.theory.equations.len());
    for (index, (actual, expected)) in certificate
        .witnesses()
        .iter()
        .zip(&fixture.expected)
        .enumerate()
    {
        assert_eq!(actual.equation as usize, index, "every row retains its source position");
        assert_eq!(actual.law, expected.law);
        assert_eq!(actual.direction, expected.direction);
        assert_eq!(actual.variable, expected.variable);
    }
}

fn assert_unsupported(fixture: &SectionFixture) {
    let semantic = compiled_section(&fixture.language);
    assert!(semantic
        .check_source_equation_section(
            &fixture.language,
            fixture.roles,
            TheoryImageAdmissionLimits::default()
        )
        .expect("unsupported schema is still a valid source/image pair")
        .is_none());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn equation_section_preserves_renamed_reordered_oriented_source_witnesses(
        salt in any::<u16>(),
        declaration_rotation in 0usize..42,
        reverse_declarations in any::<bool>(),
        equation_order in any::<[u8; 10]>(),
        reversed in any::<[bool; 10]>(),
        variable in 0u32..3,
        shared in any::<bool>(),
        duplicate in proptest::option::of(0usize..10),
    ) {
        assert_admitted(&section_fixture(&SectionCase {
            salt, declaration_rotation, reverse_declarations, equation_order,
            reversed, variable, shared, duplicate,
        }));
    }

    #[test]
    fn equation_section_rejects_distinct_variable_near_misses(
        variable in 0u32..3,
        return_second in any::<bool>(),
        compound_rhs in any::<bool>(),
    ) {
        let case = SectionCase { variable, shared: false, ..SectionCase::default() };
        let mut fixture = section_fixture(&case);
        let equation = &mut fixture.language.theory.equations[2];
        let TheoryTermFormV1::Constructor { arguments, .. } = &equation.arena.terms[equation.left.0 as usize].form else {
            panic!("idempotence fixture has a binary constructor on the left");
        };
        let second = arguments[1];
        let other = TheoryVariableId((variable + 1) % 3);
        equation.arena.terms[second.0 as usize].form = TheoryTermFormV1::Variable(other);
        if return_second {
            equation.arena.terms[equation.right.0 as usize].form = TheoryTermFormV1::Variable(other);
        }
        if compound_rhs {
            // Both variables remain available on the authored LHS, while the
            // RHS repeats only one variable ID.
            let rhs_variable = equation.right;
            equation.right = TheoryTermId(u32::try_from(equation.arena.terms.len()).expect("small near-miss arena"));
            equation.arena.terms.push(TheoryTermNodeV1 {
                sort: fixture.sort.clone(),
                form: TheoryTermFormV1::Constructor {
                    constructor: fixture.names[2].clone(),
                    arguments: vec![rhs_variable, rhs_variable],
                },
            });
            assert_ne!(equation.left, equation.right);
        }
        assert_unsupported(&fixture);
    }
}

#[test]
fn equation_section_requires_each_law_and_accepts_redundant_schema_rows() {
    for missing in 0..10 {
        let mut fixture = section_fixture(&SectionCase::default());
        fixture.language.theory.equations.remove(missing);
        assert_unsupported(&fixture);
        let mut substitute = fixture.language.theory.equations[0].clone();
        substitute.name.push_str("_not_the_missing_law");
        fixture.language.theory.equations.push(substitute);
        assert_unsupported(&fixture);
        assert_admitted(&section_fixture(&SectionCase {
            duplicate: Some(missing),
            ..SectionCase::default()
        }));
    }
    let mut fixture = section_fixture(&SectionCase::default());
    fixture.language.theory.equations.clear();
    assert_unsupported(&fixture);
}

#[test]
fn equation_section_accepts_every_source_valid_orientation_and_sharing_shape() {
    for reverse in [false, true] {
        for shared in [false, true] {
            assert_admitted(&section_fixture(&SectionCase {
                reversed: [reverse; 10],
                shared,
                variable: 2,
                ..SectionCase::default()
            }));
        }
    }
}

#[test]
fn equation_section_rejects_extra_plus_optional_and_repeat_expansion_equations() {
    for kind in ["Plus", "Optional", "Repeat"] {
        let mut fixture = section_fixture(&SectionCase::default());
        let mut arena = SectionArena::new(&fixture.sort, &fixture.names, true);
        let x = arena.variable(0);
        let left = arena.push(TheoryTermFormV1::Constructor {
            constructor: format!("section_0_{kind}"),
            arguments: vec![x],
        });
        let right = match kind {
            "Plus" => {
                let closure = arena.app(4, vec![x]);
                arena.app(3, vec![x, closure])
            },
            "Optional" => {
                let unit = arena.app(1, Vec::new());
                arena.app(2, vec![unit, x])
            },
            _ => arena.app(3, vec![x, x]),
        };
        fixture.language.theory.equations.push(TheoryEquationV1 {
            name: format!("unsupported-{kind}-expansion"),
            arena: arena.finish(0),
            left,
            right,
        });
        assert_unsupported(&fixture);
    }
}

#[test]
fn equation_section_rejects_conditional_and_non_input_source_laws() {
    for law in 0..10 {
        let mut fixture = section_fixture(&SectionCase::default());
        let arena = &mut fixture.language.theory.equations[law].arena;
        arena.premises.push(TheoryPremiseNodeV1 {
            form: TheoryPremiseFormV1::Guard(CanonicalValue::String("condition".into())),
        });
        arena.premise_roots.push(TheoryPremiseId(0));
        assert_unsupported(&fixture);
    }
    let mut fixture = section_fixture(&SectionCase::default());
    fixture.language.theory.equations[0].arena.variables[0].role = TheoryVariableRoleV1::Binder;
    assert_unsupported(&fixture);
}

#[test]
fn equation_section_rejects_wrong_role_identity_signature_sort_and_aliases() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    let ids = [
        fixture.roles.zero,
        fixture.roles.unit,
        fixture.roles.alternative,
        fixture.roles.product,
        fixture.roles.closure,
    ];
    let assign = |mut roles: SourceEquationSectionRolesV1, position: usize, id| {
        match position {
            0 => roles.zero = id,
            1 => roles.unit = id,
            2 => roles.alternative = id,
            3 => roles.product = id,
            _ => roles.closure = id,
        }
        roles
    };
    let rejects = |roles| {
        assert!(semantic
            .check_source_equation_section(
                &fixture.language,
                roles,
                TheoryImageAdmissionLimits::default()
            )
            .expect("the image remains valid when only candidate roles change")
            .is_none())
    };
    for (position, replacement) in
        ["OtherConstant", "OtherConstant", "OtherBinary", "OtherBinary", "Plus"]
            .iter()
            .enumerate()
    {
        rejects(assign(
            fixture.roles,
            position,
            constructor_id(&fixture.language, &format!("section_0_{replacement}")),
        ));
    }
    for first in 0..5 {
        for second in (first + 1)..5 {
            rejects(assign(fixture.roles, first, ids[second]));
        }
    }
    rejects(assign(fixture.roles, 0, constructor_id(&fixture.language, "section_0_Plus")));
    rejects(assign(
        fixture.roles,
        3,
        constructor_id(&fixture.language, "section_0_WrongSort"),
    ));
    rejects(assign(fixture.roles, 4, TheoryConstructorId(u32::MAX)));
    let mut roles = fixture.roles;
    roles.sort = TheorySortId(
        u32::try_from(
            fixture
                .language
                .theory
                .sorts
                .iter()
                .position(|sort| sort.name == "Other_0")
                .expect("other sort exists"),
        )
        .expect("small sort roster"),
    );
    rejects(roles);
    roles.sort = TheorySortId(u32::MAX);
    rejects(roles);
}

#[test]
fn equation_section_rejects_malformed_source_and_stale_image_before_recognition() {
    let fixture = section_fixture(&SectionCase::default());
    let semantic = compiled_section(&fixture.language);
    for malformed in 0..6 {
        let mut language = fixture.language.clone();
        match malformed {
            0 | 1 => {
                let equation = &mut language.theory.equations[3 + malformed];
                std::mem::swap(&mut equation.left, &mut equation.right);
            },
            2 => {
                let equation = &mut language.theory.equations[0];
                equation.arena.terms[equation.right.0 as usize].form =
                    TheoryTermFormV1::Variable(TheoryVariableId(1));
            },
            3 => language.theory.equations[0].arena.terms[0].sort = "Expr".into(),
            4 => language.theory.equations[0]
                .arena
                .premises
                .push(TheoryPremiseNodeV1 {
                    form: TheoryPremiseFormV1::Guard(CanonicalValue::String("unreachable".into())),
                }),
            _ => language.theory.equations[0]
                .arena
                .premise_roots
                .push(TheoryPremiseId(0)),
        }
        let errors = language
            .validate()
            .expect_err("malformed control must fail source validation");
        if malformed <= 2 {
            assert!(errors.iter().any(|error| matches!(error,
                LanguageCoreValidationError::Theory(TheoryValidationError::UnboundVariable { .. })
            )), "reversed erasing laws and a changed RHS variable are unbound, not merely stale-image failures");
        }
        assert!(semantic
            .check_source_equation_section(
                &language,
                fixture.roles,
                TheoryImageAdmissionLimits::default()
            )
            .is_err());
    }
    let mut renamed_owner = fixture.language.clone();
    renamed_owner.theory.equations[0]
        .name
        .push_str("_different_owner");
    renamed_owner
        .validate()
        .expect("the different owner is independently source-valid");
    assert!(semantic
        .check_source_equation_section(
            &renamed_owner,
            fixture.roles,
            TheoryImageAdmissionLimits::default()
        )
        .is_err());
    let mut forged = semantic.clone();
    forged.rules[0].right = forged.rules[0].left;
    assert!(forged
        .check_source_equation_section(
            &fixture.language,
            fixture.roles,
            TheoryImageAdmissionLimits::default()
        )
        .is_err());
}
