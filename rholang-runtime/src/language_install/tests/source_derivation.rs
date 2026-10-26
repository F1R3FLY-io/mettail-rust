//! Source-coordinate correspondence through the full installed Regex theory.
//! These tests inspect retained receipts, not an independent replay of the
//! recursive derivation: transition receipts intentionally remain flat.

use super::*;
use crate::installed_flt::InstalledFltAdapter;
use crate::semantic_service::InstalledSemanticBundle;
use mettail_dovetail_runtime::{
    EquationSectionLimits, ProvenSemanticRewriteSteps, SemanticInputLimits,
    SemanticIntrinsicOpcodeV1, SemanticPremiseReceipt, SemanticResourceReceipt,
    SemanticTransitionDecision, SourceEquationSection,
};
use mettail_grammar_core::{
    InstalledLanguage, SourceEquationSectionLawV1, SourceEquationSectionRolesV1,
    TheoryConstructorId, TheoryRuleDirectionV1, TheoryRuleOriginV1, TheoryRuleProgramId,
    TheorySortId, TheoryVariableRoleV1,
};
use mettail_rholang_codegen::ReflectedCodecBudget;
use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

struct InstalledRegex {
    runtime: RholangLanguageRuntime,
    token: Par,
    installed: Arc<InstalledLanguage>,
}

impl InstalledRegex {
    fn new(source: &str) -> Self {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let batch = runtime
            .install_all(rholang_ddl_candidate(source))
            .expect("full Regex source installs");
        let token = batch.exports[0].handle.clone();
        let handle = runtime.resolve(&token, LanguageRight::Reduce).unwrap();
        let installed = runtime
            .service()
            .table()
            .authorize(&handle, LanguageRight::Reduce)
            .unwrap();
        Self { runtime, token, installed }
    }

    fn construct(&self, fragments: &[&str], values: &[(&str, DynamicValue)]) -> Par {
        assert_eq!(fragments.len(), values.len() + 1);
        let owner = grammar_fingerprint_label(self.installed.commitment().language_fingerprint);
        let mut pieces = Vec::new();
        let mut holes = Vec::new();
        let mut fills = BTreeMap::new();
        for (index, fragment) in fragments.iter().enumerate() {
            pieces.push(RuntimeTemplatePiece::Text((*fragment).into()));
            if let Some((category, value)) = values.get(index) {
                let id = u32::try_from(index).unwrap();
                let name = format!("value{index}");
                let ground =
                    dynamic_syntax_to_ground_term(value, self.installed.core(), &BTreeMap::new())
                        .expect("existing native reflection");
                fills.insert(
                    name.clone(),
                    mettail_rholang_codegen::reflect_ground_term_par(&ground, &owner),
                );
                holes.push(NamedRuntimeTemplateHole {
                    id,
                    name,
                    category: Some((*category).into()),
                });
                pieces.push(RuntimeTemplatePiece::Hole(id));
            }
        }
        self.runtime
            .construct_template(&self.token, &pieces, &holes, Some("Computation"), &fills)
            .expect("full Regex grammar constructs the generated term")
    }

    fn term(&self, text: &str) -> Par {
        self.construct(&[text], &[])
    }

    fn text_key(&self, text: &str) -> Vec<u8> {
        let owner = grammar_fingerprint_label(self.installed.commitment().language_fingerprint);
        let ground = dynamic_syntax_to_ground_term(
            &DynamicValue::Text(text.into()),
            self.installed.core(),
            &BTreeMap::new(),
        )
        .unwrap();
        let value = mettail_rholang_codegen::reflect_ground_term_par(&ground, &owner);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, 10_000_000, 64 * 1024 * 1024, &mut cancelled);
        let adapter = InstalledFltAdapter::new(&self.installed, &mut budget).unwrap();
        let (category, _) = adapter.select_category("Text", &mut budget).unwrap();
        adapter
            .to_kernel(
                &value,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000,
                },
                &mut budget,
            )
            .unwrap()
            .exact_key()
            .as_bytes()
            .to_vec()
    }

    fn source_rule(&self, name: &str) -> TheoryRuleProgramId {
        let source = self
            .installed
            .language_core()
            .theory
            .rewrites
            .iter()
            .position(|rule| rule.name == name)
            .expect("authored Regex rewrite");
        let image = self.installed.base_semantic_image().unwrap();
        let program = image
            .rules
            .iter()
            .find(|rule| rule.origin == TheoryRuleOriginV1::Rewrite { source: source as u32 })
            .expect("compiled source rewrite");
        assert_eq!(program.name, name);
        program.id
    }

    fn roster(&self, input: &Par) -> (ProvenSemanticRewriteSteps, Vec<Par>) {
        let handle = self
            .runtime
            .resolve(&self.token, LanguageRight::Reduce)
            .unwrap();
        let policy = self.runtime.service().policy().semantic_service;
        let limits = policy.effective(self.installed.language_core().theory.limits, policy);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(
            &mut work,
            10_000_000,
            limits.boundary_payload_bytes,
            &mut cancelled,
        );
        let adapter = InstalledFltAdapter::new(&self.installed, &mut budget).unwrap();
        let (category, sort) = adapter.select_category("Computation", &mut budget).unwrap();
        let admitted = adapter
            .to_kernel(
                input,
                category,
                SemanticInputLimits {
                    work: limits.execution.work,
                    nodes: limits.execution.term_nodes,
                    bytes: limits.execution.term_bytes,
                },
                &mut budget,
            )
            .expect("installed input admission");
        let input_key = admitted.exact_key().as_bytes().to_vec();
        let prepared = InstalledSemanticBundle::prepare_rewrite_roster(
            self.runtime.service().table(),
            &handle,
            &[LanguageRight::Reduce],
            &mut budget,
        )
        .expect("owner-bound matcher preparation");
        let cost = prepared
            .prepare_costed_roster_image(
                self.runtime.service().policy().semantic_image,
                &mut budget,
            )
            .unwrap();
        assert!(cost.is_none(), "the full Regex fixture is uncosted");
        let (decision, charged) = prepared
            .execute_step_roster_accounted(sort, admitted, cost, limits.execution, || false)
            .unwrap();
        let proven = match decision {
            SemanticTransitionDecision::ProvenSteps(proven) => proven,
            SemanticTransitionDecision::Undetermined { reason, work, .. } => {
                panic!("full Regex roster undetermined: {reason:?}, work={work}")
            },
            SemanticTransitionDecision::Refuted(reason) => {
                panic!("full Regex roster refuted: {reason:?}")
            },
            _ => panic!("expected an exhaustive one-step roster"),
        };
        // This fixture is uncosted and has projections: the existing bundle
        // executes its projection-extended image, not the costed base route.
        // Retain both identities rather than treating their digests as equal.
        let image = self
            .installed
            .semantic_image()
            .expect("installed execution image");
        let projected = self
            .installed
            .projected_image()
            .expect("Regex has typed projections");
        let base_image = self
            .installed
            .base_semantic_image()
            .expect("source-exact base image");
        let commitment = self.installed.commitment();
        assert_eq!(proven.work, charged);
        assert_eq!(proven.input, input_key);
        assert_eq!(proven.language_fingerprint, commitment.language_fingerprint);
        assert_eq!(proven.theory_fingerprint, commitment.theory_fingerprint);
        assert_eq!(proven.image_fingerprint, image.fingerprint().unwrap());
        assert_eq!(Some(proven.image_fingerprint), commitment.semantic_image_fingerprint);
        assert_eq!(projected.base_image_fingerprint, base_image.fingerprint().unwrap());
        assert_eq!(proven.relation_sort, sort);
        for (ordinal, occurrence) in proven.occurrences.iter().enumerate() {
            assert_eq!(occurrence.ordinal, ordinal);
            assert_eq!(occurrence.output_sort, sort);
            assert_eq!(occurrence.receipt.before, proven.input);
            assert_eq!(occurrence.resource, SemanticResourceReceipt::NoSemanticGrade);
            let program = &image.rules[occurrence.receipt.rule.0 as usize];
            assert_eq!(program.id, occurrence.receipt.rule);
            let TheoryRuleOriginV1::Rewrite { source } = program.origin else {
                panic!("a directed roster cannot execute an equation")
            };
            assert_eq!(
                program.name,
                self.installed.language_core().theory.rewrites[source as usize].name,
            );
        }
        let reflected = adapter
            .reflect_rewrite_steps(&proven, sort, &mut budget)
            .unwrap();
        assert_eq!(reflected.len(), proven.occurrences.len());
        self.runtime
            .service()
            .table()
            .authorize(&handle, LanguageRight::Reduce)
            .expect("the same handle remains authorized before publication");
        (proven, reflected)
    }

    fn assert_foreign_input_refused(&self, input: &Par) {
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, 10_000_000, 64 * 1024 * 1024, &mut cancelled);
        let adapter = InstalledFltAdapter::new(&self.installed, &mut budget).unwrap();
        let (category, _) = adapter.select_category("Computation", &mut budget).unwrap();
        assert!(adapter
            .to_kernel(
                input,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000
                },
                &mut budget,
            )
            .is_err());
    }
}

#[test]
fn full_installed_regex_admits_its_exact_source_equation_section() {
    use SourceEquationSectionLawV1::*;

    let fixture = InstalledRegex::new(SOURCE);
    let source = fixture.installed.language_core();
    assert!(source.theory.cost.is_none(), "the actual Regex fixture remains uncosted");
    let sort = TheorySortId(
        u32::try_from(
            source
                .theory
                .sorts
                .iter()
                .position(|sort| sort.name == "Pattern")
                .expect("installed Regex declares Pattern"),
        )
        .expect("installed sort index is representable"),
    );
    let constructor = |name: &str| {
        TheoryConstructorId(
            u32::try_from(
                source
                    .theory
                    .constructors
                    .iter()
                    .position(|constructor| constructor.name == name)
                    .expect("installed Regex declares the requested role constructor"),
            )
            .expect("installed constructor index is representable"),
        )
    };
    let roles = SourceEquationSectionRolesV1 {
        sort,
        zero: constructor("PFail"),
        unit: constructor("PEpsilon"),
        alternative: constructor("PAlt"),
        product: constructor("PConcat"),
        closure: constructor("PStar"),
    };
    // Regex has typed projections. Admission binds the original source-exact
    // base image, not its projection-extended execution image.
    let semantic = fixture
        .installed
        .base_semantic_image()
        .expect("installed Regex retains its base semantic image");
    let certificate = semantic
        .check_source_equation_section(
            source,
            roles,
            fixture.runtime.service().policy().semantic_image,
        )
        .expect("the installed source and base image pass admission")
        .expect("the real Regex equation roster is the supported section");
    assert!(std::ptr::eq(certificate.language(), source));
    assert!(std::ptr::eq(certificate.semantic_image(), semantic));
    assert_eq!(certificate.roles(), roles);
    let source_fingerprint = certificate
        .language()
        .fingerprint()
        .expect("installed source fingerprints");
    let projected = fixture
        .installed
        .projected_image()
        .expect("the unchanged Regex fixture has projections");
    let commitment = fixture.installed.commitment();
    assert_eq!(
        source_fingerprint,
        certificate.semantic_image().language_fingerprint,
        "source admission retains the unextended language identity",
    );
    assert_eq!(
        certificate
            .semantic_image()
            .fingerprint()
            .expect("base semantic image fingerprints"),
        projected.base_image_fingerprint,
    );
    assert_eq!(projected.projected_language_fingerprint, commitment.language_fingerprint);
    assert_eq!(
        commitment.projected_language_fingerprint,
        Some(projected.projected_language_fingerprint),
    );
    assert_ne!(
        source_fingerprint, projected.projected_language_fingerprint,
        "the fixture's projection-augmented identity is distinct from its base source identity",
    );
    let expected = [
        AltZeroLeft,
        AltZeroRight,
        AltIdempotent,
        ProductZeroLeft,
        ProductZeroRight,
        ProductUnitLeft,
        ProductUnitRight,
        ClosureZero,
        ClosureUnit,
        ClosureNested,
    ];
    assert_eq!(source.theory.equations.len(), expected.len());
    assert_eq!(certificate.witnesses().len(), expected.len());
    for (index, (witness, law)) in certificate.witnesses().iter().zip(expected).enumerate() {
        assert_eq!(witness.equation as usize, index);
        assert_eq!(witness.law, law, "all ten distinct laws retain authored source order");
        assert_eq!(witness.direction, TheoryRuleDirectionV1::Forward);
        let equation = &source.theory.equations[index];
        assert!(equation.arena.premises.is_empty());
        assert!(equation.arena.premise_roots.is_empty());
        if matches!(law, ClosureZero | ClosureUnit) {
            assert_eq!(witness.variable, None);
        } else {
            let variable = witness
                .variable
                .expect("this source schema has an input variable");
            let declaration = &equation.arena.variables[variable.0 as usize];
            assert_eq!(declaration.id, variable);
            assert_eq!(declaration.role, TheoryVariableRoleV1::Input);
            assert_eq!(declaration.sort, "Pattern");
        }
    }

    let section = SourceEquationSection::restore(&certificate).expect("source section restores");
    let limits = EquationSectionLimits {
        term: SemanticInputLimits {
            work: 1_000_000,
            nodes: 10_000,
            bytes: 1_000_000,
        },
        egraph_nodes: 10_000,
        saturation_iterations: 128,
        unfolded_occurrences: 100_000,
    };
    let mut work = 0;
    let mut cancelled = || false;
    let mut budget =
        ReflectedCodecBudget::new(&mut work, 10_000_000, 64 * 1024 * 1024, &mut cancelled);
    let adapter = InstalledFltAdapter::new(&fixture.installed, &mut budget).unwrap();
    let (category, interacting_sort) = adapter.select_category("Computation", &mut budget).unwrap();
    assert_ne!(interacting_sort, roles.sort);
    for root in [roles.sort, interacting_sort] {
        let domain = section
            .check_carrier_domain(root, limits.term, || false)
            .expect("the installed source supports bounded carrier admission")
            .certificate
            .expect("both Pattern and Computation have equation-stable key domains");
        assert_eq!(domain.root_sort(), root);
        assert!(std::ptr::eq(domain.source_section(), &certificate));
    }
    for (before, after) in
        [("donePattern(a|(?!))", "donePattern(a)"), ("nullable(a|(?!))", "nullable(a)")]
    {
        let input = adapter
            .to_kernel(&fixture.term(before), category, limits.term, &mut budget)
            .expect("the installed grammar admits a computation with a reducible pattern");
        let expected = adapter
            .to_kernel(&fixture.term(after), category, limits.term, &mut budget)
            .expect("the installed grammar admits the expected computation");
        let report = section
            .normalize_in_sort(input, interacting_sort, limits, || false)
            .expect("equations normalize below the distinct interacting carrier");
        assert_eq!(report.normal_form.exact_key(), expected.exact_key());
        let repeated = section
            .normalize_in_sort(report.normal_form, interacting_sort, limits, || false)
            .expect("the accepted computation remains normal");
        assert_eq!(repeated.normal_form.exact_key(), expected.exact_key());
    }
}

fn wrapped(wrapper: &str, depth: usize, inner: &str) -> String {
    format!("{}{inner}{}", format!("{wrapper}(").repeat(depth), ")".repeat(depth))
}

#[test]
fn generated_full_regex_recursive_source_lifting_retains_repeated_activations() {
    let fixture = InstalledRegex::new(SOURCE);
    let mut runner = TestRunner::new(Config::with_cases(24));
    runner
        .run(
            &(0usize..3, 2usize..=5, prop::sample::select(vec!['a', 'z', 'λ', '中', '🦀'])),
            |(kind, depth, scalar)| {
                let (wrapper, rule_name) = [
                    ("nullableCore", "NullableCoreStep"),
                    ("derivativeCore", "DerivativeCoreStep"),
                    ("fullNullable", "FullNullableStep"),
                ][kind];
                let parent = fixture.source_rule(rule_name);
                let leaf = fixture.source_rule("StartNullable");
                let input = fixture.term(&wrapped(wrapper, depth, &format!("nullable({scalar})")));
                let expected = fixture.term(&wrapped(
                    wrapper,
                    depth,
                    &format!("nullableSurface(eEval({scalar},eNil))"),
                ));
                let (roster, outputs) = fixture.roster(&input);
                prop_assert_eq!(outputs.len(), 1);
                prop_assert_eq!(outputs[0].cmp(&expected), std::cmp::Ordering::Equal);
                let receipt = &roster.occurrences[0].receipt;
                prop_assert_eq!(receipt.rule, parent);
                let program =
                    &fixture.installed.base_semantic_image().unwrap().rules[parent.0 as usize];
                prop_assert_eq!(program.premise_roots.len(), 1);
                // Receipts are child-completion ordered. Equal repeated coordinates
                // are retained; this is not an assertion of independent tree replay.
                let expected_premises = (0..depth)
                    .map(|index| SemanticPremiseReceipt::Transition {
                        rule: parent,
                        premise: program.premise_roots[0],
                        child_rule: if index == 0 { leaf } else { parent },
                    })
                    .collect::<Vec<_>>();
                prop_assert_eq!(&receipt.premises, &expected_premises);
                Ok(())
            },
        )
        .unwrap();
}

fn unicode_text() -> impl Strategy<Value = String> {
    prop::collection::vec(prop::sample::select(vec!['a', 'é', 'λ', '中', '🦀', '\n', '\0']), 0..4)
        .prop_map(|scalars| scalars.into_iter().collect())
}

#[test]
fn generated_full_regex_intrinsic_receipts_preserve_ordered_unicode_data_flow() {
    let fixture = InstalledRegex::new(SOURCE);
    let rule = fixture.source_rule("ReplaceAllAdvanceEmpty");
    let roots =
        &fixture.installed.base_semantic_image().unwrap().rules[rule.0 as usize].premise_roots;
    assert_eq!(roots.len(), 2);
    let mut runner = TestRunner::new(Config::with_cases(24));
    runner
        .run(
            &(
                unicode_text(),
                prop::sample::select(vec!['é', 'λ', '中', '🦀']),
                unicode_text(),
                unicode_text(),
            ),
            |(prefix, scalar, suffix, inserted)| {
                let text = format!("{prefix}{scalar}{suffix}");
                let copied = scalar.to_string();
                let input_at = |cursor, end| {
                    fixture.construct(
                        &["replaceEmptyEnd(", ",a,empty,", &format!(",{cursor},{end},"), ",", ")"],
                        &[
                            ("Flag", DynamicValue::Boolean(false)),
                            ("Text", DynamicValue::Text(text.clone())),
                            ("Text", DynamicValue::Text(prefix.clone())),
                            ("Text", DynamicValue::Text(inserted.clone())),
                        ],
                    )
                };
                let expected = fixture.construct(
                    &["replaceJoinEmpty(", ",", ",", ",replaceCompute(a,empty,", ",yes))"],
                    &[
                        ("Text", DynamicValue::Text(prefix.clone())),
                        ("Text", DynamicValue::Text(inserted.clone())),
                        ("Text", DynamicValue::Text(copied.clone())),
                        ("Text", DynamicValue::Text(suffix.clone())),
                    ],
                );
                let (roster, outputs) = fixture.roster(&input_at(prefix.len(), text.len()));
                prop_assert_eq!(outputs.len(), 1);
                prop_assert_eq!(outputs[0].cmp(&expected), std::cmp::Ordering::Equal);
                let receipt = &roster.occurrences[0].receipt;
                prop_assert_eq!(receipt.rule, rule);
                let [SemanticPremiseReceipt::Intrinsic {
                    rule: first_rule,
                    premise: first,
                    receipt: scalar_receipt,
                }, SemanticPremiseReceipt::Intrinsic {
                    rule: second_rule,
                    premise: second,
                    receipt: slice_receipt,
                }] = receipt.premises.as_slice()
                else {
                    return Err(TestCaseError::fail("two ordered intrinsic receipts required"));
                };
                prop_assert_eq!((*first_rule, *second_rule), (rule, rule));
                prop_assert_eq!((*first, *second), (roots[0], roots[1]));
                prop_assert_eq!(scalar_receipt.opcode, SemanticIntrinsicOpcodeV1::Utf8ScalarAt);
                prop_assert_eq!(slice_receipt.opcode, SemanticIntrinsicOpcodeV1::Utf8Slice);
                prop_assert_eq!(
                    (scalar_receipt.inputs.len(), scalar_receipt.outputs.len()),
                    (2, 2)
                );
                prop_assert_eq!((slice_receipt.inputs.len(), slice_receipt.outputs.len()), (3, 1));
                prop_assert_eq!(&scalar_receipt.inputs[0], &slice_receipt.inputs[0]);
                prop_assert_eq!(&scalar_receipt.outputs[1], &slice_receipt.inputs[1]);
                prop_assert_eq!(&scalar_receipt.inputs[0], &fixture.text_key(&text));
                prop_assert_eq!(&scalar_receipt.outputs[0], &fixture.text_key(&copied));
                prop_assert_eq!(&slice_receipt.outputs[0], &fixture.text_key(&suffix));
                prop_assert!(scalar_receipt.work > 0 && slice_receipt.work > 0);
                // Every selected scalar is multibyte; the next byte is not a
                // boundary. The last case lets the first premise succeed but
                // refutes the slice; none may publish a successful prefix.
                for (cursor, end) in [
                    (prefix.len() + 1, text.len()),
                    (text.len(), text.len()),
                    (prefix.len(), prefix.len() + 1),
                ] {
                    let (refuted, outputs) = fixture.roster(&input_at(cursor, end));
                    prop_assert!(refuted.occurrences.is_empty());
                    prop_assert!(outputs.is_empty());
                }
                Ok(())
            },
        )
        .unwrap();
}

#[test]
fn generated_full_regex_rosters_keep_source_proof_multiplicity_and_exact_owner() {
    let original = InstalledRegex::new(SOURCE);
    assert_eq!(SOURCE.matches("TwinYesFirst :").count(), 1);
    let renamed = InstalledRegex::new(&SOURCE.replace("TwinYesFirst :", "TwinYesFirstRenamed :"));
    assert_ne!(
        original.installed.commitment().language_fingerprint,
        renamed.installed.commitment().language_fingerprint
    );
    assert_ne!(
        original.installed.commitment().theory_fingerprint,
        renamed.installed.commitment().theory_fingerprint
    );
    let mut runner = TestRunner::new(Config::with_cases(16));
    runner
        .run(&(any::<bool>(), 0usize..=3), |(twin, depth)| {
            for (fixture, foreign, first_twin) in [
                (&original, &renamed, "TwinYesFirst"),
                (&renamed, &original, "TwinYesFirstRenamed"),
            ] {
                let input = fixture.term(&wrapped(
                    "fullNullable",
                    depth,
                    if twin { "twinYes" } else { "forkYes" },
                ));
                foreign.assert_foreign_input_refused(&input);
                let expected_rules = if twin {
                    [fixture.source_rule(first_twin), fixture.source_rule("TwinYesSecond")]
                } else {
                    [
                        fixture.source_rule("ForkYesDirect"),
                        fixture.source_rule("ForkYesThroughNullable"),
                    ]
                };
                let (roster, outputs) = fixture.roster(&input);
                prop_assert_eq!(roster.occurrences.len(), 2);
                prop_assert_eq!(outputs.len(), 2);
                let parent = fixture.source_rule("FullNullableStep");
                let root = fixture.installed.base_semantic_image().unwrap().rules
                    [parent.0 as usize]
                    .premise_roots[0];
                let mut seen = BTreeSet::new();
                for (occurrence, output) in roster.occurrences.iter().zip(&outputs) {
                    let leaf = if depth == 0 {
                        prop_assert!(occurrence.receipt.premises.is_empty());
                        occurrence.receipt.rule
                    } else {
                        prop_assert_eq!(occurrence.receipt.rule, parent);
                        prop_assert_eq!(occurrence.receipt.premises.len(), depth);
                        let SemanticPremiseReceipt::Transition { child_rule, .. } =
                            &occurrence.receipt.premises[0]
                        else {
                            return Err(TestCaseError::fail("recursive leaf receipt required"));
                        };
                        let expected = (0..depth)
                            .map(|index| SemanticPremiseReceipt::Transition {
                                rule: parent,
                                premise: root,
                                child_rule: if index == 0 { *child_rule } else { parent },
                            })
                            .collect::<Vec<_>>();
                        prop_assert_eq!(&occurrence.receipt.premises, &expected);
                        *child_rule
                    };
                    prop_assert!(expected_rules.contains(&leaf));
                    prop_assert!(seen.insert(leaf));
                    let expected = fixture.term(&wrapped(
                        "fullNullable",
                        depth,
                        if twin || leaf == expected_rules[0] {
                            "doneBool(yes)"
                        } else {
                            "nullable(a?)"
                        },
                    ));
                    prop_assert_eq!(output.cmp(&expected), std::cmp::Ordering::Equal);
                }
                prop_assert_eq!(seen, BTreeSet::from(expected_rules));
                // TwinYes has equal immediate outputs; ForkYes has distinct
                // immediate successors. Neither roster may merge its proofs.
                prop_assert_eq!(
                    roster.occurrences[0].receipt.after == roster.occurrences[1].receipt.after,
                    twin
                );
            }
            Ok(())
        })
        .unwrap();
}
