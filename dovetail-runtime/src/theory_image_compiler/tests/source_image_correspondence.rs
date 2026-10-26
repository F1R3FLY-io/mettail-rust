//! Rich source/image field correspondence through real source admission.
//!
//! Every generated arena is reachable and source-valid before compilation.
//! Concrete fixture expectations and single-field mutations check projection;
//! they do not evaluate source terms or implement another image compiler.
//! Unit has a separate lowerer-only control: no grammar carrier currently admits
//! it as a source literal, unlike the eight generated literal variants.

use super::*;
use mettail_grammar_core::{is_canonical_signed_big_endian, PathMapModeV1};

struct CollectionCase {
    term: TheoryTermId,
    sort: &'static str,
    element: &'static str,
    kind: CollectionKind,
    arguments: Vec<TheoryTermId>,
    remainder: Option<TheoryVariableId>,
    mode: Option<PathMapModeV1>,
}

struct RichCase {
    language: LanguageCoreV1,
    terms: BTreeMap<&'static str, TheoryTermId>,
    variables: BTreeMap<&'static str, TheoryVariableId>,
    sorts: BTreeMap<&'static str, String>,
    literals: Vec<(TheoryTermId, TheoryLiteralV1)>,
    collections: Vec<CollectionCase>,
    constructor: String,
    root_arguments: Vec<TheoryTermId>,
}

fn node(
    arena: &mut TheoryRuleArenaV1,
    names: &mut BTreeMap<&'static str, TheoryTermId>,
    name: &'static str,
    sort: &str,
    form: TheoryTermFormV1,
) -> TheoryTermId {
    let id = TheoryTermId(arena.terms.len() as u32);
    arena
        .terms
        .push(TheoryTermNodeV1 { sort: sort.into(), form });
    assert!(names.insert(name, id).is_none());
    id
}

fn rich_case(
    salt: u16,
    literals: Vec<TheoryLiteralV1>,
    variable_rotation: usize,
    table_rotation: usize,
) -> RichCase {
    let mut language = fixture();
    language.theory.equations.clear();
    language.theory.rewrites.clear();
    language.theory.actions.clear();
    let mut sorts = BTreeMap::from([("Expr", "Expr".to_string())]);
    for name in [
        "String", "Bytes", "Integer", "Float", "Boolean", "Rational", "Fixed", "FnA", "FnB",
        "Pair", "PairExpr", "List", "Pairs", "Bag", "Set", "Map", "PathMap",
    ] {
        sorts.insert(name, format!("rich_{salt}_{name}"));
    }
    let s = |name: &str| sorts[name].clone();
    for (name, carrier, builtin) in [
        ("String", TheoryLiteralCarrierV1::String, BuiltinCarrier::String),
        ("Bytes", TheoryLiteralCarrierV1::Bytes, BuiltinCarrier::Bytes),
        ("Integer", TheoryLiteralCarrierV1::Integer, BuiltinCarrier::Integer),
        ("Float", TheoryLiteralCarrierV1::Float, BuiltinCarrier::Float),
        ("Boolean", TheoryLiteralCarrierV1::Boolean, BuiltinCarrier::Boolean),
        ("Rational", TheoryLiteralCarrierV1::Rational, BuiltinCarrier::Rational),
        ("Fixed", TheoryLiteralCarrierV1::FixedPoint, BuiltinCarrier::FixedPoint),
    ] {
        // OSLF Syntax sorts are coupled to grammar categories even when these
        // semantic literal values have no parser production in this fixture.
        language.grammar.categories.push(Category {
            id: CategoryId(language.grammar.categories.len() as u32),
            name: s(name),
            carrier: Carrier::Builtin(builtin),
            primary: false,
            admits_variables: false,
        });
        language.theory.sorts.push(TheorySortV1 {
            name: s(name),
            kind: TheorySortKindV1::Syntax { literal: Some(carrier) },
        });
    }
    for (name, domain, multiple) in [("FnA", "Expr", false), ("FnB", "Integer", true)] {
        language.theory.sorts.push(TheorySortV1 {
            name: s(name),
            kind: TheorySortKindV1::Function {
                domain: s(domain),
                codomain: s("Expr"),
                multiple,
            },
        });
    }
    for (name, right) in [("Pair", "Integer"), ("PairExpr", "Expr")] {
        language.theory.sorts.push(TheorySortV1 {
            name: s(name),
            kind: TheorySortKindV1::Product { factors: vec![s("Expr"), s(right)] },
        });
    }
    for (name, kind, element, keyed) in [
        ("List", CollectionKind::List, "Expr", false),
        ("Pairs", CollectionKind::List, "PairExpr", false),
        ("Bag", CollectionKind::Bag, "Expr", false),
        ("Set", CollectionKind::Set, "Expr", false),
        ("Map", CollectionKind::Map, "Pair", true),
        ("PathMap", CollectionKind::PathMap, "Pair", true),
    ] {
        language.theory.sorts.push(TheorySortV1 {
            name: s(name),
            kind: TheorySortKindV1::Collection {
                kind,
                key: keyed.then(|| s("Expr")),
                element: s(element),
            },
        });
    }
    use TheoryVariableRoleV1::{Binder, Input, Remainder};
    let declarations = [
        ("x", "Expr", Input),
        ("fa", "FnA", Input),
        ("fb", "FnB", Input),
        ("a", "Expr", Binder),
        ("b", "Integer", Binder),
        ("rest", "List", Remainder),
        ("path_rest", "PathMap", Remainder),
        ("p", "Expr", Binder),
        ("q", "Expr", Binder),
    ];
    let mut variables = BTreeMap::new();
    let mut arena = TheoryRuleArenaV1 {
        variables: Vec::new(),
        terms: Vec::new(),
        premises: Vec::new(),
        premise_roots: Vec::new(),
    };
    for (index, &(name, sort, role)) in declarations.iter().enumerate() {
        let id = TheoryVariableId(((index + variable_rotation) % declarations.len()) as u32);
        variables.insert(name, id);
        arena.variables.push(TheoryVariableV1 {
            id,
            name: format!("v_{salt}_{name}"),
            sort: s(sort),
            role,
        });
    }
    arena.variables.sort_by_key(|variable| variable.id);
    let mut terms = BTreeMap::new();
    let x = node(
        &mut arena,
        &mut terms,
        "x",
        &s("Expr"),
        TheoryTermFormV1::Variable(variables["x"]),
    );
    let fa = node(
        &mut arena,
        &mut terms,
        "fa",
        &s("FnA"),
        TheoryTermFormV1::Variable(variables["fa"]),
    );
    let fb = node(
        &mut arena,
        &mut terms,
        "fb",
        &s("FnB"),
        TheoryTermFormV1::Variable(variables["fb"]),
    );
    let zero = node(
        &mut arena,
        &mut terms,
        "zero",
        &s("Expr"),
        TheoryTermFormV1::Constructor {
            constructor: "Zero".into(),
            arguments: Vec::new(),
        },
    );
    let wrap = node(
        &mut arena,
        &mut terms,
        "wrap",
        &s("Expr"),
        TheoryTermFormV1::Constructor {
            constructor: "Wrap".into(),
            arguments: vec![x],
        },
    );
    let mut literal_cases = Vec::new();
    let literal_names =
        ["String", "Bytes", "Integer", "Float", "Boolean", "Integer", "Rational", "Fixed"];
    assert_eq!(literals.len(), literal_names.len());
    for (index, (literal, sort)) in literals.into_iter().zip(literal_names).enumerate() {
        let id = TheoryTermId(arena.terms.len() as u32);
        arena.terms.push(TheoryTermNodeV1 {
            sort: s(sort),
            form: TheoryTermFormV1::Literal(literal.clone()),
        });
        literal_cases.push((id, literal));
        if index == 2 {
            terms.insert("integer", id);
        }
    }
    let integer = terms["integer"];
    let abs_a = node(
        &mut arena,
        &mut terms,
        "abs_a",
        &s("FnA"),
        TheoryTermFormV1::Abstraction { binder: variables["a"], body: wrap },
    );
    let abs_b = node(
        &mut arena,
        &mut terms,
        "abs_b",
        &s("FnB"),
        TheoryTermFormV1::Abstraction { binder: variables["b"], body: wrap },
    );
    let sub_a = node(
        &mut arena,
        &mut terms,
        "sub_a",
        &s("Expr"),
        TheoryTermFormV1::Substitution { abstraction: fa, argument: x },
    );
    let sub_b = node(
        &mut arena,
        &mut terms,
        "sub_b",
        &s("Expr"),
        TheoryTermFormV1::Substitution { abstraction: fb, argument: integer },
    );
    let pair = node(
        &mut arena,
        &mut terms,
        "pair",
        &s("Pair"),
        TheoryTermFormV1::Product { factors: vec![x, integer] },
    );
    let mut collections = Vec::new();
    for (name, sort, element, kind, arguments, remainder, mode) in [
        (
            "list",
            "List",
            "Expr",
            CollectionKind::List,
            vec![x, zero],
            Some(variables["rest"]),
            None,
        ),
        ("bag", "Bag", "Expr", CollectionKind::Bag, vec![wrap, zero], None, None),
        ("set", "Set", "Expr", CollectionKind::Set, vec![x, zero], None, None),
        ("map", "Map", "Pair", CollectionKind::Map, vec![pair], None, None),
        (
            "path_empty",
            "PathMap",
            "Pair",
            CollectionKind::PathMap,
            vec![],
            None,
            Some(PathMapModeV1::NeutralEmpty),
        ),
        (
            "path_set",
            "PathMap",
            "Pair",
            CollectionKind::PathMap,
            vec![x, zero],
            None,
            Some(PathMapModeV1::Set),
        ),
        (
            "path_map",
            "PathMap",
            "Pair",
            CollectionKind::PathMap,
            vec![pair],
            None,
            Some(PathMapModeV1::Map),
        ),
        (
            "path_remainder",
            "PathMap",
            "Pair",
            CollectionKind::PathMap,
            vec![],
            Some(variables["path_rest"]),
            None,
        ),
        ("source_a", "List", "Expr", CollectionKind::List, vec![x, zero], None, None),
        ("source_b", "List", "Expr", CollectionKind::List, vec![wrap, zero], None, None),
    ] {
        let term = node(
            &mut arena,
            &mut terms,
            name,
            &s(sort),
            TheoryTermFormV1::Collection {
                elements: arguments.clone(),
                remainder,
                pathmap_mode: mode,
            },
        );
        collections.push(CollectionCase {
            term,
            sort,
            element,
            kind,
            arguments,
            remainder,
            mode,
        });
    }
    let p = node(
        &mut arena,
        &mut terms,
        "p",
        &s("Expr"),
        TheoryTermFormV1::Variable(variables["p"]),
    );
    let q = node(
        &mut arena,
        &mut terms,
        "q",
        &s("Expr"),
        TheoryTermFormV1::Variable(variables["q"]),
    );
    let body = node(
        &mut arena,
        &mut terms,
        "body",
        &s("PairExpr"),
        TheoryTermFormV1::Product { factors: vec![p, q] },
    );
    let sources = vec![terms["source_a"], terms["source_b"]];
    let mapped = node(
        &mut arena,
        &mut terms,
        "mapped",
        &s("Pairs"),
        TheoryTermFormV1::Map {
            sources,
            parameters: vec![variables["p"], variables["q"]],
            body,
        },
    );
    let enclosing = node(
        &mut arena,
        &mut terms,
        "enclosing",
        &s("Pairs"),
        TheoryTermFormV1::Collection {
            elements: vec![mapped],
            remainder: None,
            pathmap_mode: None,
        },
    );
    collections.push(CollectionCase {
        term: enclosing,
        sort: "Pairs",
        element: "PairExpr",
        kind: CollectionKind::List,
        arguments: vec![mapped],
        remainder: None,
        mode: None,
    });
    let mut root_arguments = vec![abs_a, abs_b, sub_a, sub_b, pair];
    root_arguments.extend(literal_cases.iter().map(|(id, _)| *id));
    // Sources and body are reached only through their owning map. In particular
    // p/q never acquire an outside-body path, and each remainder occurs once.
    root_arguments.extend(
        collections
            .iter()
            .filter(|case| ![terms["source_a"], terms["source_b"]].contains(&case.term))
            .map(|case| case.term),
    );
    let constructor = format!("Rich_{salt}");
    language.theory.constructors.push(TheoryConstructorV1 {
        name: constructor.clone(),
        domain: root_arguments
            .iter()
            .map(|id| arena.terms[id.0 as usize].sort.clone())
            .collect(),
        codomain: s("Expr"),
    });
    let left = node(
        &mut arena,
        &mut terms,
        "root",
        &s("Expr"),
        TheoryTermFormV1::Constructor {
            constructor: constructor.clone(),
            arguments: root_arguments.clone(),
        },
    );
    language.theory.rewrites.push(TheoryRewriteV1 {
        name: format!("rich_rule_{salt}"),
        arena,
        left,
        right: zero,
    });
    // The same reachable arena exercises the second production term/variable
    // validator without creating a second family of source fixtures.
    let arena = &language.theory.rewrites[0].arena;
    let judgment = format!("RichJudgment_{salt}");
    language.theory.judgments.push(JudgmentDeclV1 {
        name: judgment.clone(),
        arguments: vec![s("Expr")],
        decision: JudgmentDecisionV1::Bounded,
        rules: vec![JudgmentRuleV1 {
            name: format!("rich_judgment_rule_{salt}"),
            variables: arena.variables.clone(),
            terms: arena.terms.clone(),
            premises: Vec::new(),
            conclusion: JudgmentAtomV1 { judgment, terms: vec![left] },
        }],
    });
    let sort_count = language.theory.sorts.len();
    language
        .theory
        .sorts
        .rotate_left(table_rotation % sort_count);
    let constructor_count = language.theory.constructors.len();
    language
        .theory
        .constructors
        .rotate_left(table_rotation % constructor_count);
    RichCase {
        language,
        terms,
        variables,
        sorts,
        literals: literal_cases,
        collections,
        constructor,
        root_arguments,
    }
}

fn sort_id(case: &RichCase, name: &str) -> TheorySortId {
    TheorySortId(
        case.language
            .theory
            .sorts
            .iter()
            .position(|sort| sort.name == name)
            .expect("fixture sort name must have a declared source position") as u32,
    )
}

fn constructor_id(case: &RichCase, name: &str) -> TheoryConstructorId {
    TheoryConstructorId(
        case.language
            .theory
            .constructors
            .iter()
            .position(|constructor| constructor.name == name)
            .expect("fixture constructor name must have a declared source position") as u32,
    )
}

fn assert_apply(
    image: &TheorySemanticImageV1,
    term: TheoryTermId,
    operator: TheoryImageOperatorV1,
    arguments: Vec<TheoryTermId>,
    slots: Vec<TheoryVariableId>,
    remainder: Option<TheoryVariableId>,
    pathmap_mode: Option<PathMapModeV1>,
) {
    assert_eq!(
        image.rules[0].terms[term.0 as usize].form,
        TheoryImageTermFormV1::Apply {
            operator,
            arguments,
            slots,
            remainder,
            pathmap_mode,
        },
        "exact lowered fields at source term {}",
        term.0
    );
}

fn reject_mutation(
    case: &RichCase,
    image: &TheorySemanticImageV1,
    mutate: impl FnOnce(&mut TheorySemanticImageV1),
) {
    let mut changed = image.clone();
    mutate(&mut changed);
    assert_ne!(&changed, image, "the negative control must actually alter the image");
    assert_eq!(changed.language_fingerprint, image.language_fingerprint);
    assert_eq!(changed.grammar_fingerprint, image.grammar_fingerprint);
    assert_eq!(changed.theory_fingerprint, image.theory_fingerprint);
    assert_eq!(changed.patterns, image.patterns);
    assert_eq!(changed.judgment_patterns, image.judgment_patterns);
    assert_eq!(
        changed
            .validate(&case.language, TheoryImageAdmissionLimits::default())
            .expect_err("changed image must not validate against its unchanged authored source"),
        mutation_error(&image.rules[0], &changed.rules[0], false),
        "the intended source-field check, not fingerprints or automata, must reject the mutation"
    );

    if changed.rules[0].terms != image.rules[0].terms
        || changed.rules[0].variables != image.rules[0].variables
    {
        let mut changed_judgment = image.clone();
        changed_judgment.judgment_rules[0].terms = changed.rules[0].terms.clone();
        changed_judgment.judgment_rules[0].variables = changed.rules[0].variables.clone();
        assert_ne!(&changed_judgment, image, "the judgment control must also change its arena");
        assert_eq!(
            changed_judgment
                .validate(&case.language, TheoryImageAdmissionLimits::default())
                .expect_err("the judgment validator must reject the same changed arena"),
            mutation_error(&image.rules[0], &changed.rules[0], true),
            "the judgment source-field check must reject before automaton validation"
        );
    }
}

// Classify the single field group altered by a test case, so a rejection at
// another admission boundary cannot stand in for source-exact validation.
fn mutation_error(
    original: &TheoryRuleProgramV1,
    changed: &TheoryRuleProgramV1,
    judgment: bool,
) -> TheoryImageError {
    let kind = if original.left != changed.left || original.right != changed.right {
        assert!(!judgment, "rewrite roots are not judgment-arena fields");
        "rule header"
    } else if original.terms.len() != changed.terms.len()
        || original.variables.len() != changed.variables.len()
    {
        if judgment {
            "judgment rule"
        } else {
            "rule arena"
        }
    } else if original.variables != changed.variables {
        for (index, (before, after)) in original
            .variables
            .iter()
            .zip(&changed.variables)
            .enumerate()
        {
            if before.id != after.id {
                return TheoryImageError::NonDenseId {
                    kind: if judgment {
                        "judgment rule variable"
                    } else {
                        "rule variable"
                    },
                    expected: index as u32,
                    actual: after.id.0,
                };
            }
        }
        if judgment {
            "judgment rule variable"
        } else {
            "rule variable"
        }
    } else {
        assert_ne!(original.terms, changed.terms, "expected one changed term field group");
        if judgment {
            "judgment rule term"
        } else {
            "rule term"
        }
    };
    TheoryImageError::SourceMismatch { kind, index: 0 }
}

fn assert_rich_fields(case: &RichCase, image: &TheorySemanticImageV1) {
    let source = &case.language.theory.rewrites[0];
    assert_eq!(image.rules.len(), 1);
    let program = &image.rules[0];
    assert_eq!(image.judgment_rules.len(), 1);
    assert_eq!(image.judgment_rules[0].terms, program.terms);
    assert_eq!(image.judgment_rules[0].variables, program.variables);
    assert_eq!(image.judgment_rules[0].conclusion.terms, vec![source.left]);
    assert_eq!(program.origin, TheoryRuleOriginV1::Rewrite { source: 0 });
    assert_eq!(program.left, source.left);
    assert_eq!(program.right, source.right);
    assert_eq!(program.terms.len(), source.arena.terms.len());
    for (index, node) in source.arena.terms.iter().enumerate() {
        assert_eq!(program.terms[index].sort, sort_id(case, &node.sort), "source index {index}");
    }
    assert_eq!(program.variables.len(), source.arena.variables.len());
    for (actual, expected) in program.variables.iter().zip(&source.arena.variables) {
        assert_eq!(actual.id, expected.id);
        assert_eq!(actual.sort, sort_id(case, &expected.sort));
        assert_eq!(actual.role, expected.role);
    }
    for name in ["x", "fa", "fb", "p", "q"] {
        assert_eq!(
            program.terms[case.terms[name].0 as usize].form,
            TheoryImageTermFormV1::Slot(case.variables[name])
        );
    }
    for (name, constructor, arguments) in [
        ("zero", "Zero", vec![]),
        ("wrap", "Wrap", vec![case.terms["x"]]),
        ("root", case.constructor.as_str(), case.root_arguments.clone()),
    ] {
        assert_apply(
            image,
            case.terms[name],
            TheoryImageOperatorV1::Constructor(constructor_id(case, constructor)),
            arguments,
            vec![],
            None,
            None,
        );
    }
    for (name, sort, binder) in [("abs_a", "FnA", "a"), ("abs_b", "FnB", "b")] {
        assert_apply(
            image,
            case.terms[name],
            TheoryImageOperatorV1::Abstraction { sort: sort_id(case, &case.sorts[sort]) },
            vec![case.terms["wrap"]],
            vec![case.variables[binder]],
            None,
            None,
        );
    }
    // Equal codomains do not identify function sorts. The reference's own
    // source sort, including its distinct domain/multiplicity, supplies the ID.
    for (name, function, abstraction, argument) in
        [("sub_a", "FnA", "fa", "x"), ("sub_b", "FnB", "fb", "integer")]
    {
        assert_apply(
            image,
            case.terms[name],
            TheoryImageOperatorV1::Substitution {
                sort: sort_id(case, &case.sorts["Expr"]),
                function: sort_id(case, &case.sorts[function]),
            },
            vec![case.terms[abstraction], case.terms[argument]],
            vec![],
            None,
            None,
        );
    }
    for (name, sort, left, right) in
        [("pair", "Pair", "x", "integer"), ("body", "PairExpr", "p", "q")]
    {
        assert_apply(
            image,
            case.terms[name],
            TheoryImageOperatorV1::Product { sort: sort_id(case, &case.sorts[sort]) },
            vec![case.terms[left], case.terms[right]],
            vec![],
            None,
            None,
        );
    }
    for collection in &case.collections {
        assert_apply(
            image,
            collection.term,
            TheoryImageOperatorV1::Collection {
                sort: sort_id(case, &case.sorts[collection.sort]),
                // Set-mode PathMap still stores the declared pair element here;
                // the mode-sensitive key carrier is a separate runtime readback.
                element: sort_id(case, &case.sorts[collection.element]),
                kind: collection.kind,
            },
            collection.arguments.clone(),
            vec![],
            collection.remainder,
            collection.mode,
        );
    }
    for (term, value) in &case.literals {
        let sort = sort_id(case, &source.arena.terms[term.0 as usize].sort);
        assert_apply(
            image,
            *term,
            TheoryImageOperatorV1::Literal { sort, value: value.clone() },
            vec![],
            vec![],
            None,
            None,
        );
    }
    assert_eq!(
        program.terms[case.terms["mapped"].0 as usize].form,
        TheoryImageTermFormV1::Map {
            sources: vec![case.terms["source_a"], case.terms["source_b"]],
            parameters: vec![case.variables["p"], case.variables["q"]],
            body: case.terms["body"],
        }
    );
}

pub(super) fn changed_literal(value: &TheoryLiteralV1) -> TheoryLiteralV1 {
    match value {
        TheoryLiteralV1::String(value) => TheoryLiteralV1::String(format!("{value}\0")),
        TheoryLiteralV1::Bytes(value) => {
            let mut value = value.clone();
            value.push(0);
            TheoryLiteralV1::Bytes(value)
        },
        TheoryLiteralV1::Integer(value) => TheoryLiteralV1::Integer(value ^ 1),
        TheoryLiteralV1::FloatBits(value) => TheoryLiteralV1::FloatBits(value ^ 1),
        TheoryLiteralV1::Boolean(value) => TheoryLiteralV1::Boolean(!value),
        TheoryLiteralV1::Unit => TheoryLiteralV1::Boolean(false),
        TheoryLiteralV1::BigInt(value) => {
            let mut value = value.clone();
            *value
                .last_mut()
                .expect("canonical BigInt payload is nonempty") ^= 1;
            TheoryLiteralV1::BigInt(value)
        },
        TheoryLiteralV1::BigRat { numerator, denominator } => TheoryLiteralV1::BigRat {
            numerator: vec![if numerator == &[1] { 0xff } else { 1 }],
            denominator: denominator.clone(),
        },
        TheoryLiteralV1::FixedPoint { unscaled, scale } => TheoryLiteralV1::FixedPoint {
            unscaled: unscaled.clone(),
            scale: scale ^ 1,
        },
    }
}

fn check_field_mutations(case: &RichCase, image: &TheorySemanticImageV1) {
    let next_sort = |sort: TheorySortId| TheorySortId((sort.0 + 1) % image.sorts.len() as u32);
    for (index, term) in image.rules[0].terms.iter().enumerate() {
        reject_mutation(case, image, |changed| {
            changed.rules[0].terms[index].sort = next_sort(term.sort)
        });
        let mut forms = Vec::new();
        match &term.form {
            TheoryImageTermFormV1::Slot(variable) => {
                forms.push(TheoryImageTermFormV1::Slot(TheoryVariableId(
                    (variable.0 + 1) % image.rules[0].variables.len() as u32,
                )));
                forms.push(TheoryImageTermFormV1::Slot(TheoryVariableId(u32::MAX)));
            },
            TheoryImageTermFormV1::Apply {
                operator,
                arguments,
                slots,
                remainder,
                pathmap_mode,
            } => {
                let mut operators = Vec::new();
                match operator {
                    TheoryImageOperatorV1::Constructor(id) => {
                        operators.push(TheoryImageOperatorV1::Constructor(TheoryConstructorId(
                            (id.0 + 1) % image.constructors.len() as u32,
                        )))
                    },
                    TheoryImageOperatorV1::Abstraction { sort } => operators
                        .push(TheoryImageOperatorV1::Abstraction { sort: next_sort(*sort) }),
                    TheoryImageOperatorV1::Substitution { sort, function } => {
                        operators.push(TheoryImageOperatorV1::Substitution {
                            sort: next_sort(*sort),
                            function: *function,
                        });
                        let first = sort_id(case, &case.sorts["FnA"]);
                        let second = sort_id(case, &case.sorts["FnB"]);
                        operators.push(TheoryImageOperatorV1::Substitution {
                            sort: *sort,
                            function: if *function == first { second } else { first },
                        });
                    },
                    TheoryImageOperatorV1::Collection { sort, element, kind } => {
                        operators.push(TheoryImageOperatorV1::Collection {
                            sort: next_sort(*sort),
                            element: *element,
                            kind: *kind,
                        });
                        operators.push(TheoryImageOperatorV1::Collection {
                            sort: *sort,
                            element: next_sort(*element),
                            kind: *kind,
                        });
                        operators.push(TheoryImageOperatorV1::Collection {
                            sort: *sort,
                            element: *element,
                            kind: if *kind == CollectionKind::List {
                                CollectionKind::Bag
                            } else {
                                CollectionKind::List
                            },
                        });
                    },
                    TheoryImageOperatorV1::Product { sort } => {
                        operators.push(TheoryImageOperatorV1::Product { sort: next_sort(*sort) })
                    },
                    TheoryImageOperatorV1::Literal { sort, value } => {
                        operators.push(TheoryImageOperatorV1::Literal {
                            sort: next_sort(*sort),
                            value: value.clone(),
                        });
                        operators.push(TheoryImageOperatorV1::Literal {
                            sort: *sort,
                            value: changed_literal(value),
                        });
                        match value {
                            TheoryLiteralV1::BigRat { numerator, denominator } => {
                                operators.push(TheoryImageOperatorV1::Literal {
                                    sort: *sort,
                                    value: TheoryLiteralV1::BigRat {
                                        numerator: numerator.clone(),
                                        denominator: vec![if denominator == &[1] { 2 } else { 1 }],
                                    },
                                })
                            },
                            TheoryLiteralV1::FixedPoint { unscaled, scale } => {
                                let mut unscaled = unscaled.clone();
                                *unscaled
                                    .last_mut()
                                    .expect("canonical fixed-point payload is nonempty") ^= 1;
                                operators.push(TheoryImageOperatorV1::Literal {
                                    sort: *sort,
                                    value: TheoryLiteralV1::FixedPoint { unscaled, scale: *scale },
                                });
                            },
                            _ => {},
                        }
                    },
                    _ => panic!("fixture contains only authored term operators"),
                }
                let with_operator = |operator| TheoryImageTermFormV1::Apply {
                    operator,
                    arguments: arguments.clone(),
                    slots: slots.clone(),
                    remainder: *remainder,
                    pathmap_mode: *pathmap_mode,
                };
                forms.extend(operators.into_iter().map(with_operator));
                let mut bad_arguments = vec![vec![TheoryTermId(u32::MAX)]];
                let mut different_width = arguments.clone();
                if different_width.is_empty() {
                    different_width.push(TheoryTermId(0));
                } else {
                    different_width.pop();
                }
                bad_arguments.push(different_width);
                if !arguments.is_empty() {
                    let mut changed = arguments.clone();
                    changed[0] = if changed[0] == case.terms["zero"] {
                        case.terms["x"]
                    } else {
                        case.terms["zero"]
                    };
                    bad_arguments.push(changed);
                }
                if arguments.len() > 1 {
                    let mut reversed = arguments.clone();
                    reversed.reverse();
                    if reversed != *arguments {
                        bad_arguments.push(reversed);
                    }
                }
                for arguments in bad_arguments {
                    forms.push(TheoryImageTermFormV1::Apply {
                        operator: operator.clone(),
                        arguments,
                        slots: slots.clone(),
                        remainder: *remainder,
                        pathmap_mode: *pathmap_mode,
                    });
                }
                let mut changed_slots = slots.clone();
                if changed_slots.is_empty() {
                    changed_slots.push(TheoryVariableId(0));
                } else {
                    changed_slots[0] = TheoryVariableId(u32::MAX);
                }
                forms.push(TheoryImageTermFormV1::Apply {
                    operator: operator.clone(),
                    arguments: arguments.clone(),
                    slots: changed_slots,
                    remainder: *remainder,
                    pathmap_mode: *pathmap_mode,
                });
                if !slots.is_empty() {
                    let mut changed_slots = slots.clone();
                    changed_slots[0] = case.variables["p"];
                    forms.push(TheoryImageTermFormV1::Apply {
                        operator: operator.clone(),
                        arguments: arguments.clone(),
                        slots: changed_slots,
                        remainder: *remainder,
                        pathmap_mode: *pathmap_mode,
                    });
                }
                forms.push(TheoryImageTermFormV1::Apply {
                    operator: operator.clone(),
                    arguments: arguments.clone(),
                    slots: slots.clone(),
                    remainder: if remainder.is_some() {
                        None
                    } else {
                        Some(TheoryVariableId(0))
                    },
                    pathmap_mode: *pathmap_mode,
                });
                forms.push(TheoryImageTermFormV1::Apply {
                    operator: operator.clone(),
                    arguments: arguments.clone(),
                    slots: slots.clone(),
                    remainder: *remainder,
                    pathmap_mode: if pathmap_mode.is_some() {
                        None
                    } else {
                        Some(PathMapModeV1::Set)
                    },
                });
                if let Some(mode) = pathmap_mode {
                    forms.push(TheoryImageTermFormV1::Apply {
                        operator: operator.clone(),
                        arguments: arguments.clone(),
                        slots: slots.clone(),
                        remainder: *remainder,
                        pathmap_mode: Some(if *mode == PathMapModeV1::Map {
                            PathMapModeV1::Set
                        } else {
                            PathMapModeV1::Map
                        }),
                    });
                }
            },
            TheoryImageTermFormV1::Map { sources, parameters, body } => {
                let mut reversed_sources = sources.clone();
                reversed_sources.reverse();
                let mut short_sources = sources.clone();
                short_sources.pop();
                for sources in
                    [reversed_sources, short_sources, vec![], vec![TheoryTermId(u32::MAX)]]
                {
                    forms.push(TheoryImageTermFormV1::Map {
                        sources,
                        parameters: parameters.clone(),
                        body: *body,
                    });
                }
                let mut reversed_parameters = parameters.clone();
                reversed_parameters.reverse();
                let mut short_parameters = parameters.clone();
                short_parameters.pop();
                for parameters in [
                    reversed_parameters,
                    short_parameters,
                    vec![],
                    vec![TheoryVariableId(u32::MAX)],
                ] {
                    forms.push(TheoryImageTermFormV1::Map {
                        sources: sources.clone(),
                        parameters,
                        body: *body,
                    });
                }
                for body in [case.terms["pair"], TheoryTermId(u32::MAX)] {
                    forms.push(TheoryImageTermFormV1::Map {
                        sources: sources.clone(),
                        parameters: parameters.clone(),
                        body,
                    });
                }
            },
        }
        for form in forms {
            reject_mutation(case, image, |changed| changed.rules[0].terms[index].form = form);
        }
    }
    reject_mutation(case, image, |changed| {
        changed.rules[0].terms.pop();
    });
    reject_mutation(case, image, |changed| {
        let extra = changed.rules[0].terms[0].clone();
        changed.rules[0].terms.push(extra);
    });
    reject_mutation(case, image, |changed| {
        changed.rules[0]
            .terms
            .swap(case.terms["abs_a"].0 as usize, case.terms["abs_b"].0 as usize)
    });
    reject_mutation(case, image, |changed| {
        changed.rules[0]
            .terms
            .swap(case.terms["p"].0 as usize, case.terms["q"].0 as usize)
    });
    reject_mutation(case, image, |changed| {
        changed.rules[0].variables.pop();
    });
    reject_mutation(case, image, |changed| {
        let mut extra = changed.rules[0].variables[0].clone();
        extra.id = TheoryVariableId(changed.rules[0].variables.len() as u32);
        changed.rules[0].variables.push(extra);
    });
    reject_mutation(case, image, |changed| changed.rules[0].left = TheoryTermId(u32::MAX));
    reject_mutation(case, image, |changed| changed.rules[0].right = case.terms["wrap"]);
    for index in 0..image.rules[0].variables.len() {
        reject_mutation(case, image, |changed| {
            changed.rules[0].variables[index].id = TheoryVariableId(u32::MAX)
        });
        reject_mutation(case, image, |changed| {
            changed.rules[0].variables[index].sort = next_sort(image.rules[0].variables[index].sort)
        });
        reject_mutation(case, image, |changed| {
            changed.rules[0].variables[index].role = TheoryVariableRoleV1::Derived
        });
    }
}

fn signed_bytes() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 1..6)
        .prop_filter("canonical signed big-endian bytes", |bytes| {
            is_canonical_signed_big_endian(bytes)
        })
}

pub(super) fn rich_literals() -> impl Strategy<Value = Vec<TheoryLiteralV1>> {
    (
        prop::collection::vec(any::<char>(), 0..8),
        prop::collection::vec(any::<u8>(), 0..8),
        any::<i128>(),
        any::<u64>(),
        any::<bool>(),
        signed_bytes(),
        1u8..128,
        signed_bytes(),
        any::<u32>(),
    )
        .prop_map(
            |(text, bytes, integer, bits, boolean, big, denominator, unscaled, scale)| {
                vec![
                    TheoryLiteralV1::String(text.into_iter().collect()),
                    TheoryLiteralV1::Bytes(bytes),
                    TheoryLiteralV1::Integer(integer),
                    TheoryLiteralV1::FloatBits(bits),
                    TheoryLiteralV1::Boolean(boolean),
                    TheoryLiteralV1::BigInt(big),
                    TheoryLiteralV1::BigRat {
                        numerator: vec![if boolean { 1 } else { 0xff }],
                        denominator: vec![denominator],
                    },
                    TheoryLiteralV1::FixedPoint { unscaled, scale },
                ]
            },
        )
}

#[test]
fn unit_literal_projection_is_exact_but_source_admission_refuses_missing_carrier() {
    let mut language = fixture();
    language
        .validate()
        .expect("the unmodified fixture is source-valid");
    let unit = TheoryTermNodeV1 {
        sort: "Expr".into(),
        form: TheoryTermFormV1::Literal(TheoryLiteralV1::Unit),
    };
    let context = CompileContext::new(&language).expect("the fixture names resolve uniquely");
    // This intentionally calls only the existing lowerer. Exact projection of
    // Unit does not establish whole-source admission or a supported Unit carrier.
    let terms = compile_term_nodes(std::slice::from_ref(&unit), &[], &context)
        .expect("the raw lowerer preserves the Unit payload and declared sort");
    assert_eq!(
        terms,
        vec![TheoryImageTermNodeV1 {
            sort: TheorySortId(0),
            form: TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Literal {
                    sort: TheorySortId(0),
                    value: TheoryLiteralV1::Unit,
                },
                arguments: Vec::new(),
                slots: Vec::new(),
                remainder: None,
                pathmap_mode: None,
            },
        }]
    );

    // All term sorts/references remain consistent with this declared literal
    // sort, but the Dynamic grammar carrier cannot realize Syntax(Some(Unit)).
    language.theory.sorts[0].kind = TheorySortKindV1::Syntax {
        literal: Some(TheoryLiteralCarrierV1::Unit),
    };
    language.theory.rewrites[0].arena.terms[1] = unit;
    language
        .grammar
        .validate()
        .expect("the refusal is not caused by an invalid grammar");
    assert_eq!(
        language
            .validate()
            .expect_err("no existing grammar carrier admits the Unit literal sort"),
        vec![LanguageCoreValidationError::Theory(TheoryValidationError::SortMismatch {
            owner: "sort `Expr` literal carrier".into(),
            expected: "None".into(),
            actual: "Some(Unit)".into(),
        })]
    );
    assert!(matches!(
        compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default()),
        Err(TheoryImageCompileError::Image(TheoryImageError::InvalidLanguage(_)))
    ));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn generated_rich_source_image_preserves_exact_fields_and_rejects_mutations(
        salt in any::<u16>(), literals in rich_literals(), variable_rotation in 0usize..9, table_rotation in 0usize..40,
    ) {
        let case = rich_case(salt, literals, variable_rotation, table_rotation);
        case.language.validate().expect("all rich terms are source-valid and reachable before image compilation");
        let limits = TheoryImageAdmissionLimits::default();
        let image = compile_theory_semantic_image(&case.language, limits).expect("compile the admitted rich source");
        image.validate(&case.language, limits).expect("independently validate the source-bound image");
        assert_rich_fields(&case, &image);
        check_field_mutations(&case, &image);
    }

    #[test]
    fn generated_rich_source_admission_refuses_unknown_and_duplicate_names(
        salt in any::<u16>(), literals in rich_literals(), variable_rotation in 0usize..9, table_rotation in 0usize..40,
    ) {
        let case = rich_case(salt, literals, variable_rotation, table_rotation);
        case.language.validate().expect("negative controls start from an admitted source");
        for fault in 0..6 {
            let mut source = case.language.clone();
            match fault {
                0 => source.theory.rewrites[0].arena.terms[case.terms["x"].0 as usize].sort = format!("missing_sort_{salt}"),
                1 => source.theory.rewrites[0].arena.terms[case.terms["zero"].0 as usize].form = TheoryTermFormV1::Constructor { constructor: format!("missing_constructor_{salt}"), arguments: Vec::new() },
                2 => { let duplicate = source.theory.sorts[0].clone(); source.theory.sorts.push(duplicate); },
                3 => { let duplicate = source.theory.constructors[0].clone(); source.theory.constructors.push(duplicate); },
                4 => source.theory.rewrites[0].arena.variables[1].name = source.theory.rewrites[0].arena.variables[0].name.clone(),
                5 => source.theory.rewrites[0].arena.variables[0].sort = format!("missing_variable_sort_{salt}"),
                _ => unreachable!(),
            }
            prop_assert!(source.validate().is_err(), "invalid source must be rejected before projection");
            prop_assert!(matches!(
                compile_theory_semantic_image(&source, TheoryImageAdmissionLimits::default()),
                Err(TheoryImageCompileError::Image(TheoryImageError::InvalidLanguage(_)))
            ), "compiler must reject at source admission before resolving unknown or duplicate names");
        }
    }
}
