use dovetail::egraph::{EClassId, EGraph, ENode};
use dovetail::key::FramedSemanticOperator;
use mettail_dovetail_runtime::{
    compile_theory_semantic_image, theory_operator_to_machine, ProvenSemanticRewriteSteps,
    SemanticInputDecision, SemanticInputLimits, SemanticPremiseReceipt,
    SemanticRelationExecutionRequest, SemanticTransitionDecision, SemanticTransitionInput,
    SemanticTransitionLimits, SemanticTransitionMatcher,
};
use mettail_elab::canonical::{value_to_language_core, RhoValue};
use mettail_grammar_core::{
    LanguageCoreV1, LanguageRight, LanguageRights, PathMapModeV1, TheoryConstructorId,
    TheoryImageAdmissionLimits, TheoryImageOperatorV1, TheoryRuleProgramId, TheorySemanticImageV1,
    TheorySortId, TheorySortKindImageV1,
};
use proptest::prelude::*;

fn text(value: impl Into<String>) -> RhoValue {
    RhoValue::String(value.into())
}
fn list(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(values.into_iter().collect())
}
fn node(tag: &str, values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    list(std::iter::once(text(tag)).chain(values))
}
fn map(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
    RhoValue::Map(
        values
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect(),
    )
}
fn typed(name: &str, ty: RhoValue) -> RhoValue {
    node("typed", [text(name), ty])
}
fn term(name: &str, category: &str, domains: Vec<RhoValue>) -> RhoValue {
    map([
        ("label", text(name)),
        ("category", text(category)),
        (
            "context",
            list(
                domains
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| node("param", [text(format!("arg{index}")), ty.clone()])),
            ),
        ),
        (
            "syntax",
            list(
                std::iter::once(node("lit", [text(name.to_lowercase())]))
                    .chain((0..domains.len()).map(|index| text(format!("arg{index}")))),
            ),
        ),
    ])
}
fn rule(
    name: &str,
    context: Vec<RhoValue>,
    left: RhoValue,
    right: RhoValue,
    premises: Vec<RhoValue>,
) -> RhoValue {
    map([
        ("name", text(name)),
        ("context", list(context)),
        ("left", left),
        ("right", right),
        ("premises", list(premises)),
    ])
}

#[derive(Clone, Copy, Debug)]
enum Context {
    Binders(usize),
    Collection(usize),
    Pair,
}

impl Context {
    fn depth(self) -> usize {
        if let Self::Binders(depth) = self {
            depth
        } else {
            0
        }
    }
    fn keyed(self) -> bool {
        matches!(self, Self::Collection(3 | 5))
    }
    fn ty(self) -> RhoValue {
        match self {
            Self::Binders(depth) => {
                (0..depth).fold(text("P"), |body, _| node("arrow", [text("N"), body]))
            },
            Self::Collection(0) => node("vec", [text("P")]),
            Self::Collection(1) => node("bag", [text("P")]),
            Self::Collection(2) => node("set", [text("P")]),
            Self::Collection(3) => node("map", [text("N"), text("P")]),
            Self::Collection(4) => node("pathmap", [text("P"), text("N")]),
            Self::Collection(5) => node("pathmap", [text("N"), text("P")]),
            Self::Collection(_) => unreachable!(),
            Self::Pair => text("P"),
        }
    }
    fn names(self) -> Vec<String> {
        (0..self.depth()).map(|index| format!("x{index}")).collect()
    }
    fn wrap(self, first: RhoValue, second: Option<RhoValue>) -> RhoValue {
        let child = match self {
            Self::Binders(_) => self
                .names()
                .iter()
                .rev()
                .fold(first, |body, name| node("^", [text(name), body])),
            Self::Collection(kind) => {
                let first = if self.keyed() {
                    node("product", [text("key"), first])
                } else {
                    first
                };
                let mut fields = vec![list([first]), RhoValue::Nil];
                if kind == 4 {
                    fields.push(text("set"));
                }
                if kind == 5 {
                    fields.push(text("map"));
                }
                node("coll", fields)
            },
            Self::Pair => return node("Outer", [first, second.unwrap()]),
        };
        node("Outer", [child])
    }
}

fn language(context: Context, explicit: bool, salt: u16) -> LanguageCoreV1 {
    let arguments = (0..context.depth().max(1))
        .map(|index| format!("n{index}"))
        .collect::<Vec<_>>();
    let names = context.names();
    let f = format!("family{salt}");
    let g = format!("other{salt}");
    let family_type = || {
        names
            .iter()
            .rev()
            .fold(node("rewrite", [text("P")]), |body, _| node("arrow", [text("N"), body]))
    };
    let projection = |side: &str, family: &str| node(side, [node(family, names.iter().map(text))]);
    let mut bindings = if context.keyed() {
        vec![typed("key", text("N"))]
    } else {
        vec![]
    };
    let pair = matches!(context, Context::Pair);
    let (left, right, premises) = if explicit {
        if pair {
            bindings.push(typed(&g, family_type()));
        }
        bindings.push(typed(&f, family_type()));
        (
            context.wrap(projection("s", &f), pair.then(|| projection("s", &g))),
            context.wrap(projection("t", &f), pair.then(|| projection("t", &g))),
            vec![],
        )
    } else {
        if pair {
            bindings.push(typed("second_source", text("P")));
        }
        bindings.push(typed("first_source", text("P")));
        let mut premises = Vec::new();
        if pair {
            premises.push(node("~>", [text("second_source"), text("second_target")]));
        }
        premises.push(node("~>", [text("first_source"), text("first_target")]));
        (
            context.wrap(text("first_source"), pair.then(|| text("second_source"))),
            context.wrap(text("first_target"), pair.then(|| text("second_target"))),
            premises,
        )
    };
    let child_context = arguments
        .iter()
        .map(|name| typed(name, text("N")))
        .collect::<Vec<_>>();
    let mut rewrites = vec![
        rule(
            "FirstStep",
            child_context.clone(),
            node("Tick", arguments.iter().map(text)),
            node("Done", arguments.iter().map(text)),
            vec![],
        ),
        rule("Under", bindings, left, right, premises),
    ];
    let mut terms = (0..context.depth().max(2))
        .map(|index| term(&format!("Name{index}"), "N", vec![]))
        .collect::<Vec<_>>();
    let domains = vec![text("N"); arguments.len()];
    terms.extend([
        term("Tick", "P", domains.clone()),
        term("Done", "P", domains.clone()),
        term(
            "Outer",
            "P",
            if pair {
                vec![text("P"), text("P")]
            } else {
                vec![context.ty()]
            },
        ),
    ]);
    if pair {
        terms.extend([term("OtherTick", "P", domains.clone()), term("OtherDone", "P", domains)]);
        rewrites.push(rule(
            "SecondStep",
            child_context,
            node("OtherTick", arguments.iter().map(text)),
            node("OtherDone", arguments.iter().map(text)),
            vec![],
        ));
    }
    value_to_language_core(&map([
        ("mettail", text("language/3")),
        ("name", text("FamilyExecution")),
        ("types", list([text("P"), text("N")])),
        ("terms", list(terms)),
        ("rewrites", list(rewrites)),
        ("oslf", map([])),
    ]))
    .expect("canonical family fixture lowers through the public adapter")
}

fn input_limits() -> SemanticInputLimits {
    SemanticInputLimits {
        work: 100_000,
        nodes: 512,
        bytes: 256 * 1024,
    }
}
fn limits() -> SemanticTransitionLimits {
    SemanticTransitionLimits {
        work: 1_000_000,
        normalization_steps: 64,
        outputs: 64,
        frontier: 256,
        proofs: 256,
        proof_nodes: 256,
        term_nodes: 512,
        term_bytes: 256 * 1024,
        output_nodes: 512,
        output_bytes: 256 * 1024,
    }
}
fn constructor_id(language: &LanguageCoreV1, name: &str) -> TheoryConstructorId {
    TheoryConstructorId(
        language
            .theory
            .constructors
            .iter()
            .position(|item| item.name == name)
            .unwrap() as u32,
    )
}
fn add(
    graph: &mut EGraph<FramedSemanticOperator>,
    operator: TheoryImageOperatorV1,
    children: Vec<EClassId>,
) -> EClassId {
    graph.add(ENode::new(theory_operator_to_machine(&operator), children))
}
fn ground(
    language: &LanguageCoreV1,
    image: &TheorySemanticImageV1,
    context: Context,
    reduced: bool,
) -> SemanticTransitionInput {
    let mut graph = EGraph::new();
    let names = (0..context.depth().max(2))
        .map(|index| {
            add(
                &mut graph,
                TheoryImageOperatorV1::Constructor(constructor_id(
                    language,
                    &format!("Name{index}"),
                )),
                vec![],
            )
        })
        .collect::<Vec<_>>();
    let arguments = names[..context.depth().max(1)].to_vec();
    let mut body = add(
        &mut graph,
        TheoryImageOperatorV1::Constructor(constructor_id(
            language,
            if reduced { "Done" } else { "Tick" },
        )),
        arguments,
    );
    let outer = constructor_id(language, "Outer");
    let mut sort = image.constructors[outer.0 as usize].domain[0];
    let children = match context {
        Context::Binders(depth) => {
            let mut functions = Vec::new();
            for _ in 0..depth {
                functions.push(sort);
                let TheorySortKindImageV1::Function { codomain, .. } =
                    image.sorts[sort.0 as usize].kind
                else {
                    panic!("registered function")
                };
                sort = codomain;
            }
            for (function, name) in functions.into_iter().zip(&names).rev() {
                body = add(
                    &mut graph,
                    TheoryImageOperatorV1::Abstraction { sort: function },
                    vec![*name, body],
                );
            }
            vec![body]
        },
        Context::Collection(which) => {
            let TheorySortKindImageV1::Collection { kind, element, .. } =
                image.sorts[sort.0 as usize].kind
            else {
                panic!("registered collection")
            };
            if context.keyed() {
                body = add(
                    &mut graph,
                    TheoryImageOperatorV1::Product { sort: element },
                    vec![names[1], body],
                );
            }
            let mut children = Vec::new();
            if which == 4 || which == 5 {
                children.push(add(
                    &mut graph,
                    TheoryImageOperatorV1::PathMapMode {
                        sort,
                        mode: if which == 4 {
                            PathMapModeV1::Set
                        } else {
                            PathMapModeV1::Map
                        },
                    },
                    vec![],
                ));
            }
            children.push(body);
            vec![add(
                &mut graph,
                TheoryImageOperatorV1::Collection { sort, element, kind },
                children,
            )]
        },
        Context::Pair => {
            let second = add(
                &mut graph,
                TheoryImageOperatorV1::Constructor(constructor_id(
                    language,
                    if reduced { "OtherDone" } else { "OtherTick" },
                )),
                vec![names[1]],
            );
            vec![body, second]
        },
    };
    let root = add(&mut graph, TheoryImageOperatorV1::Constructor(outer), children);
    match SemanticTransitionInput::admit(graph, root, input_limits(), || false) {
        SemanticInputDecision::Proven(input) => input,
        _ => panic!("finite ground family input admits"),
    }
}

fn steps(
    image: &TheorySemanticImageV1,
    relation_sort: TheorySortId,
    input: SemanticTransitionInput,
) -> ProvenSemanticRewriteSteps {
    let matcher =
        SemanticTransitionMatcher::restore(image).expect("restore checked semantic image");
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let (decision, work) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image,
            relation_sort,
            granted_rights: &rights,
            input,
            limits: limits(),
        },
        || false,
    );
    match decision {
        SemanticTransitionDecision::ProvenSteps(roster) => {
            assert_eq!(roster.work, work);
            roster
        },
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            panic!("finite family execution was undetermined: {reason:?}")
        },
        SemanticTransitionDecision::Refuted(reason) => {
            panic!("family execution was refused: {reason:?}")
        },
        _ => panic!("relation step must return a complete roster"),
    }
}
fn rule_name(image: &TheorySemanticImageV1, id: TheoryRuleProgramId) -> &str {
    &image.rules.iter().find(|rule| rule.id == id).unwrap().name
}

fn check(context: Context, salt: u16) {
    let mut observations = Vec::new();
    for explicit in [true, false] {
        let language = language(context, explicit, salt);
        let image = compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
            .expect("compile actual lowered family");
        let sort = image.constructors[constructor_id(&language, "Outer").0 as usize].codomain;
        let expected = ground(&language, &image, context, true);
        let before = ground(&language, &image, context, false);
        let before_key = before.exact_key().as_bytes().to_vec();
        let roster = steps(&image, sort, before);
        assert_eq!(roster.occurrences.len(), 1);
        let occurrence = &roster.occurrences[0];
        assert_eq!(occurrence.receipt.before, before_key);
        assert_eq!(occurrence.receipt.after.as_slice(), expected.exact_key().as_bytes());
        assert_eq!(rule_name(&image, occurrence.receipt.rule), "Under");
        let premises = occurrence
            .receipt
            .premises
            .iter()
            .map(|premise| match premise {
                SemanticPremiseReceipt::Transition { rule, premise, child_rule } => {
                    assert_eq!(rule_name(&image, *rule), "Under");
                    (*premise, rule_name(&image, *child_rule).to_owned())
                },
                other => panic!("unexpected family premise receipt: {other:?}"),
            })
            .collect::<Vec<_>>();
        let expected_premises = if matches!(context, Context::Pair) {
            vec![(0, "SecondStep".into()), (1, "FirstStep".into())]
        } else {
            vec![(0, "FirstStep".into())]
        };
        assert_eq!(premises, expected_premises);
        observations.push((occurrence.receipt.after.clone(), premises));
        assert!(steps(&image, sort, expected).occurrences.is_empty());
    }
    assert_eq!(observations[0], observations[1]);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]
    #[test]
    fn families_under_nested_binders_execute_as_ordinary_transition_rules(depth in 1usize..5, salt in any::<u16>()) {
        check(Context::Binders(depth), salt);
    }
    #[test]
    fn families_in_registered_collections_preserve_typed_context_and_exact_keys(which in 0usize..6, salt in any::<u16>()) {
        check(Context::Collection(which), salt);
    }
    #[test]
    fn independent_families_execute_in_declaration_order(salt in any::<u16>()) {
        check(Context::Pair, salt);
    }
}

#[test]
fn ordinary_transition_rule_under_one_binder_preserves_its_binding() {
    let context = Context::Binders(1);
    let language = language(context, false, 0);
    let image =
        compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default()).unwrap();
    let sort = image.constructors[constructor_id(&language, "Outer").0 as usize].codomain;
    let roster = steps(&image, sort, ground(&language, &image, context, false));
    assert_eq!(roster.occurrences.len(), 1);
    let expected = ground(&language, &image, context, true);
    assert_eq!(roster.occurrences[0].receipt.after.as_slice(), expected.exact_key().as_bytes());
}
