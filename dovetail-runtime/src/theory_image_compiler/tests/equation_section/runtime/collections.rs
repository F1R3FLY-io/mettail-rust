//! Collection composition through the real source compiler and term builder.
//! Seed rewrites construct canonical inputs/expectations using the existing
//! collection canonicalizer; no test-local collection normalizer is used.

use super::*;
use mettail_grammar_core::PathMapModeV1;

const KINDS: [CollectionKind; 4] = [
    CollectionKind::Bag,
    CollectionKind::Set,
    CollectionKind::Map,
    CollectionKind::PathMap,
];

struct CollectionSection {
    fixture: SectionFixture,
    pair: String,
    sorts: [String; 4],
    wrappers: [String; 4],
}

fn kind_index(kind: CollectionKind) -> usize {
    KINDS
        .iter()
        .position(|candidate| *candidate == kind)
        .expect("test collection kind")
}

fn collection_section(salt: u16) -> CollectionSection {
    let mut fixture = section_fixture(&SectionCase {
        salt,
        declaration_rotation: usize::from(salt),
        reversed: [true; 10],
        ..SectionCase::default()
    });
    let pair = format!("collection_{salt}_Pair");
    fixture.language.theory.sorts.push(TheorySortV1 {
        name: pair.clone(),
        kind: TheorySortKindV1::Product { factors: vec![fixture.sort.clone(); 2] },
    });
    let sorts = ["Bag", "Set", "Map", "PathMap"].map(|name| format!("collection_{salt}_{name}"));
    let wrappers = sorts.each_ref().map(|name| format!("{name}Envelope"));
    for ((name, wrapper), kind) in sorts.iter().zip(&wrappers).zip(KINDS) {
        let keyed = matches!(kind, CollectionKind::Map | CollectionKind::PathMap);
        fixture.language.theory.sorts.push(TheorySortV1 {
            name: name.clone(),
            kind: TheorySortKindV1::Collection {
                kind,
                key: keyed.then(|| fixture.sort.clone()),
                element: if keyed {
                    pair.clone()
                } else {
                    fixture.sort.clone()
                },
            },
        });
        // Internal semantic constructors need no new parser syntax.
        fixture
            .language
            .theory
            .constructors
            .push(TheoryConstructorV1 {
                name: wrapper.clone(),
                domain: vec![name.clone()],
                codomain: fixture.sort.clone(),
            });
    }
    CollectionSection { fixture, pair, sorts, wrappers }
}

struct CollectionArena<'a> {
    source: &'a CollectionSection,
    terms: Vec<TheoryTermNodeV1>,
}

impl CollectionArena<'_> {
    fn push(&mut self, sort: String, form: TheoryTermFormV1) -> TheoryTermId {
        let id = TheoryTermId(u32::try_from(self.terms.len()).expect("bounded source arena"));
        self.terms.push(TheoryTermNodeV1 { sort, form });
        id
    }

    fn app(&mut self, op: Op, arguments: Vec<TheoryTermId>) -> TheoryTermId {
        let id = operator_id(&self.source.fixture, op);
        self.push(
            self.source.fixture.sort.clone(),
            TheoryTermFormV1::Constructor {
                constructor: self.source.fixture.language.theory.constructors[id.0 as usize]
                    .name
                    .clone(),
                arguments,
            },
        )
    }

    fn tree(&mut self, tree: &Tree) -> TheoryTermId {
        let arguments = tree.1.iter().map(|child| self.tree(child)).collect();
        self.app(tree.0, arguments)
    }

    fn pair(&mut self, key: TheoryTermId, value: TheoryTermId) -> TheoryTermId {
        self.push(
            self.source.pair.clone(),
            TheoryTermFormV1::Product { factors: vec![key, value] },
        )
    }

    fn wrapped(
        &mut self,
        kind: CollectionKind,
        mode: Option<PathMapModeV1>,
        elements: Vec<TheoryTermId>,
    ) -> TheoryTermId {
        let index = kind_index(kind);
        let collection = self.push(
            self.source.sorts[index].clone(),
            TheoryTermFormV1::Collection {
                elements,
                remainder: None,
                pathmap_mode: mode,
            },
        );
        self.push(
            self.source.fixture.sort.clone(),
            TheoryTermFormV1::Constructor {
                constructor: self.source.wrappers[index].clone(),
                arguments: vec![collection],
            },
        )
    }
}

fn add_builder(
    source: &mut CollectionSection,
    build: impl FnOnce(&mut CollectionArena<'_>) -> TheoryTermId,
) -> TheoryConstructorId {
    let seed = format!("collection_seed_{}", source.fixture.language.theory.rewrites.len());
    source
        .fixture
        .language
        .theory
        .constructors
        .push(TheoryConstructorV1 {
            name: seed.clone(),
            domain: Vec::new(),
            codomain: source.fixture.sort.clone(),
        });
    let seed_id = constructor_id(&source.fixture.language, &seed);
    let mut arena = CollectionArena { source, terms: Vec::new() };
    let right = build(&mut arena);
    let left = arena.push(
        source.fixture.sort.clone(),
        TheoryTermFormV1::Constructor {
            constructor: seed.clone(),
            arguments: Vec::new(),
        },
    );
    let terms = arena.terms;
    source
        .fixture
        .language
        .theory
        .rewrites
        .push(TheoryRewriteV1 {
            name: seed,
            arena: TheoryRuleArenaV1 {
                variables: Vec::new(),
                terms,
                premises: Vec::new(),
                premise_roots: Vec::new(),
            },
            left,
            right,
        });
    seed_id
}

fn constructed(
    source: &CollectionSection,
    semantic: &TheorySemanticImageV1,
    seed: TheoryConstructorId,
) -> SemanticTransitionInput {
    let mut graph = EGraph::new();
    let root = graph.add(ENode::leaf(theory_operator_to_machine(
        &TheoryImageOperatorV1::Constructor(seed),
    )));
    let matcher = SemanticTransitionMatcher::restore(semantic).expect("source builder matcher");
    let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
    let (decision, used) = matcher.execute_rewrite_step_roster_accounted(
        SemanticRelationExecutionRequest {
            image: semantic,
            relation_sort: source.fixture.roles.sort,
            granted_rights: &rights,
            input: admit(graph, root),
            limits: normalization_limits(),
        },
        || false,
    );
    let steps = match decision {
        SemanticTransitionDecision::ProvenSteps(steps) => steps,
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            panic!("source collection construction: {reason:?}")
        },
        SemanticTransitionDecision::Refuted(reason) => {
            panic!("source collection construction: {reason:?}")
        },
        _ => panic!("the one-step source builder must return its proof roster"),
    };
    assert_eq!(steps.work, used);
    assert_eq!(
        steps.occurrences.len(),
        1,
        "only the designated seed rewrite fires; no section equation executes here"
    );
    let (graph, occurrences) = steps.into_parts();
    admit(graph, occurrences[0].output)
}

fn descendant(input: &SemanticTransitionInput, path: &[usize]) -> SemanticTransitionInput {
    let mut current = input.root_subroot();
    for &index in path {
        current = current
            .child(index)
            .expect("exact expected collection path");
    }
    match current.admit(limits().term, || false).0 {
        SemanticInputDecision::Proven(input) => input,
        _ => panic!("retained exact descendant must re-admit"),
    }
}

fn collection_len(input: &SemanticTransitionInput) -> usize {
    input
        .root_subroot()
        .child(0)
        .expect("collection envelope")
        .child_count()
        .expect("exact collection")
}

// Choose a removable extreme constant under the actual exact-key order. The
// two redexes then sort B-before-A, while their normal forms sort A-before-B.
// This guarantees a real permutation, rather than merely testing a lucky
// constructor-ID order. All three constants have the same framing width.
fn reordering_terms(fixture: &SectionFixture) -> (Tree, Tree, Tree, Tree) {
    let mut values = [Op::Zero, Op::Unit, Op::Atom]
        .map(|op| (input(fixture, &leaf(op)).exact_key().clone(), op));
    values.sort_by(|left, right| left.0.cmp(&right.0));
    let pivot_index = if values[0].1 == Op::Atom { 2 } else { 0 };
    let pivot = values[pivot_index].1;
    let other: Vec<_> = values
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != pivot_index)
        .map(|(_, (_, op))| leaf(*op))
        .collect();
    let (a, b) = (other[0].clone(), other[1].clone());
    let op = if pivot == Op::Zero {
        Op::Alt
    } else {
        Op::Product
    };
    let (redex_a, redex_b) = if pivot_index == 0 {
        (binary(op, a.clone(), leaf(pivot)), binary(op, leaf(pivot), b.clone()))
    } else {
        (binary(op, leaf(pivot), a.clone()), binary(op, b.clone(), leaf(pivot)))
    };
    assert!(input(fixture, &redex_b).exact_key() < input(fixture, &redex_a).exact_key());
    (a, b, redex_a, redex_b)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(12))]

    #[test]
    fn section_runtime_bag_reorders_after_collapse_without_losing_multiplicity(
        salt in any::<u16>(), repeats in 2usize..=5,
    ) {
        let mut source = collection_section(salt);
        let (a, b, redex_a, redex_b) = reordering_terms(&source.fixture);
        let before = add_builder(&mut source, |arena| {
            let a = arena.tree(&redex_a);
            let b = arena.tree(&redex_b);
            let mut entries = vec![a; repeats];
            entries.push(b);
            arena.wrapped(CollectionKind::Bag, None, entries)
        });
        let after = add_builder(&mut source, |arena| {
            let a = arena.tree(&a);
            let b = arena.tree(&b);
            let mut entries = vec![a; repeats];
            entries.push(b);
            arena.wrapped(CollectionKind::Bag, None, entries)
        });
        let semantic = compiled_section(&source.fixture.language);
        let original = constructed(&source, &semantic, before);
        prop_assert_eq!(descendant(&original, &[0, 0]).exact_key().clone(), input(&source.fixture, &redex_b).exact_key().clone());
        let report = success(normalize(&source.fixture, &semantic, original, limits(), || false));
        assert_report(&report, &constructed(&source, &semantic, after));
        prop_assert_eq!(collection_len(&report.normal_form), repeats + 1);
        for index in 0..repeats {
            prop_assert_eq!(descendant(&report.normal_form, &[0, index]).exact_key().clone(), input(&source.fixture, &a).exact_key().clone());
        }
        prop_assert_eq!(descendant(&report.normal_form, &[0, repeats]).exact_key().clone(), input(&source.fixture, &b).exact_key().clone());
    }

    #[test]
    fn section_runtime_set_dedup_exposes_an_enclosing_alt_redex(
        salt in any::<u16>(), depth in 0usize..=4,
    ) {
        let mut source = collection_section(salt);
        let mut value = leaf(Op::Atom);
        for _ in 0..depth { value = unary(Op::Plus, value); }
        let before = add_builder(&mut source, |arena| {
            let normal = arena.tree(&value);
            let first = arena.tree(&binary(Op::Alt, leaf(Op::Zero), value.clone()));
            let second = arena.tree(&binary(Op::Product, value.clone(), leaf(Op::Unit)));
            let nontrivial = arena.wrapped(CollectionKind::Set, None, vec![normal, first, second]);
            let singleton = arena.wrapped(CollectionKind::Set, None, vec![normal]);
            arena.app(Op::Alt, vec![nontrivial, singleton])
        });
        let after = add_builder(&mut source, |arena| {
            let normal = arena.tree(&value);
            arena.wrapped(CollectionKind::Set, None, vec![normal])
        });
        let semantic = compiled_section(&source.fixture.language);
        let original = constructed(&source, &semantic, before);
        prop_assert_ne!(descendant(&original, &[0]).exact_key().clone(), descendant(&original, &[1]).exact_key().clone());
        let report = success(normalize(&source.fixture, &semantic, original, limits(), || false));
        assert_report(&report, &constructed(&source, &semantic, after));
        prop_assert_eq!(collection_len(&report.normal_form), 1);
        prop_assert!(report.phases.len() >= 2, "Set dedup needs a subsequent equation phase");
        let total_iterations: usize = report.phases.iter().map(|phase| {
            phase.saturation.stats.iterations + phase.raw_irreducibility.stats.iterations
                + phase.collection_irreducibility.as_ref().map_or(0, |probe| probe.stats.iterations)
        }).sum();
        let mut exact = limits();
        exact.saturation_iterations = total_iterations;
        let exact_report = success(normalize(&source.fixture, &semantic,
            constructed(&source, &semantic, before), exact, || false));
        assert_report(&exact_report, &constructed(&source, &semantic, after));
        let exact_total: usize = exact_report.phases.iter().map(|phase| {
            phase.saturation.stats.iterations + phase.raw_irreducibility.stats.iterations
                + phase.collection_irreducibility.as_ref().map_or(0, |probe| probe.stats.iterations)
        }).sum();
        prop_assert_eq!(exact_total, total_iterations);
        exact.saturation_iterations -= 1;
        let refused = failure(normalize(&source.fixture, &semantic,
            constructed(&source, &semantic, before), exact, || false));
        prop_assert_eq!(refused.reason, EquationSectionFailureKind::Saturation(SaturationOutcome::IterationLimit));
        prop_assert!(refused.boundary_work > 0 && refused.boundary_work <= exact.term.work);
        // The first saturation alone cannot see equality of a three-child Set
        // and a singleton Set; canonical reconstruction must expose the Alt.
        let again = success(normalize(&source.fixture, &semantic, report.normal_form, limits(), || false));
        assert_report(&again, &constructed(&source, &semantic, after));
    }

    #[test]
    fn section_runtime_noncolliding_map_keys_reorder_with_their_values(
        salt in any::<u16>(), swapped_values in any::<bool>(),
    ) {
        for (kind, mode) in [(CollectionKind::Map, None), (CollectionKind::PathMap, Some(PathMapModeV1::Map))] {
            let mut source = collection_section(salt);
            let (a, b, redex_a, redex_b) = reordering_terms(&source.fixture);
            let mut values = [unary(Op::Plus, leaf(Op::Atom)), unary(Op::Optional, leaf(Op::Atom))];
            if swapped_values { values.swap(0, 1); }
            let mut build = |keys: [&Tree; 2]| add_builder(&mut source, |arena| {
                let entries = keys.into_iter().zip(&values).map(|(key, value)| {
                    let key = arena.tree(key);
                    let value = arena.tree(value);
                    arena.pair(key, value)
                }).collect();
                arena.wrapped(kind, mode, entries)
            });
            let before = build([&redex_a, &redex_b]);
            let after = build([&a, &b]);
            let semantic = compiled_section(&source.fixture.language);
            let report = success(normalize(&source.fixture, &semantic, constructed(&source, &semantic, before), limits(), || false));
            assert_report(&report, &constructed(&source, &semantic, after));
            let offset = usize::from(mode.is_some());
            prop_assert_eq!(collection_len(&report.normal_form), 2 + offset);
            for (index, key) in [&a, &b].into_iter().enumerate() {
                prop_assert_eq!(descendant(&report.normal_form, &[0, index + offset, 0]).exact_key().clone(), input(&source.fixture, key).exact_key().clone());
                prop_assert_eq!(descendant(&report.normal_form, &[0, index + offset, 1]).exact_key().clone(), input(&source.fixture, &values[index]).exact_key().clone());
            }
        }
    }

    #[test]
    fn section_runtime_collection_key_collisions_refuse_unless_annihilation_erases_the_branch(
        salt in any::<u16>(), same_values in any::<bool>(),
    ) {
        for (kind, mode) in [
            (CollectionKind::Map, None),
            (CollectionKind::PathMap, Some(PathMapModeV1::Map)),
            (CollectionKind::PathMap, Some(PathMapModeV1::Set)),
        ] {
            let mut source = collection_section(salt);
            let mut build = |erasing: Option<bool>| add_builder(&mut source, |arena| {
                let key = arena.tree(&leaf(Op::Atom));
                let other_key = arena.tree(&binary(Op::Alt, leaf(Op::Zero), leaf(Op::Atom)));
                let entries = if mode == Some(PathMapModeV1::Set) {
                    vec![key, other_key]
                } else {
                    let value = arena.tree(&unary(Op::Plus, leaf(Op::Atom)));
                    let other_value = if same_values { value } else { arena.tree(&unary(Op::Optional, leaf(Op::Atom))) };
                    vec![arena.pair(key, value), arena.pair(other_key, other_value)]
                };
                let wrapped = arena.wrapped(kind, mode, entries);
                match erasing {
                    None => wrapped,
                    Some(zero_first) => {
                        let zero = arena.app(Op::Zero, Vec::new());
                        arena.app(Op::Product, if zero_first { vec![zero, wrapped] } else { vec![wrapped, zero] })
                    },
                }
            });
            let retained = build(None);
            let erased_left = build(Some(true));
            let erased_right = build(Some(false));
            let semantic = compiled_section(&source.fixture.language);
            let original = constructed(&source, &semantic, retained);
            prop_assert_eq!(collection_len(&original), 2 + usize::from(mode.is_some()));
            let prefix = original.admission_work();
            let refused = failure(normalize(&source.fixture, &semantic, original, limits(), || false));
            prop_assert_eq!(refused.reason, EquationSectionFailureKind::Boundary(SemanticMatchUndetermined::InvalidImageEvidence));
            prop_assert!(refused.boundary_work > prefix);
            prop_assert!(refused.boundary_work <= limits().term.work);
            for seed in [erased_left, erased_right] {
                let report = success(normalize(&source.fixture, &semantic, constructed(&source, &semantic, seed), limits(), || false));
                assert_report(&report, &input(&source.fixture, &leaf(Op::Zero)));
                prop_assert_eq!(report.normal_form.egraph().node_count(), 1, "discarded colliding collections do not survive publication");
            }
        }
    }
}

#[test]
fn section_runtime_preserves_three_distinct_empty_pathmap_modes() {
    let mut source = collection_section(731);
    let modes = [PathMapModeV1::NeutralEmpty, PathMapModeV1::Set, PathMapModeV1::Map];
    let seeds = modes.map(|mode| {
        let before = add_builder(&mut source, |arena| {
            let empty = arena.wrapped(CollectionKind::PathMap, Some(mode), Vec::new());
            let unit = arena.app(Op::Unit, Vec::new());
            arena.app(Op::Product, vec![unit, empty])
        });
        let after = add_builder(&mut source, |arena| {
            arena.wrapped(CollectionKind::PathMap, Some(mode), Vec::new())
        });
        (before, after)
    });
    let semantic = compiled_section(&source.fixture.language);
    let sort = TheorySortId(
        u32::try_from(
            source
                .fixture
                .language
                .theory
                .sorts
                .iter()
                .position(|sort| sort.name == source.sorts[3])
                .expect("PathMap source sort"),
        )
        .expect("bounded sort roster"),
    );
    let mut keys = Vec::new();
    for (mode, (before, after)) in modes.into_iter().zip(seeds) {
        let report = success(normalize(
            &source.fixture,
            &semantic,
            constructed(&source, &semantic, before),
            limits(),
            || false,
        ));
        assert_report(&report, &constructed(&source, &semantic, after));
        assert_eq!(collection_len(&report.normal_form), 1, "only the explicit mode marker remains");
        let marker = descendant(&report.normal_form, &[0, 0]);
        assert_eq!(
            marker.root_subroot().operator(),
            Some(&theory_operator_to_machine(&TheoryImageOperatorV1::PathMapMode { sort, mode }))
        );
        assert_eq!(marker.root_subroot().child_count(), Some(0));
        keys.push(report.normal_form.exact_key().clone());
    }
    assert_ne!(keys[0], keys[1]);
    assert_ne!(keys[0], keys[2]);
    assert_ne!(keys[1], keys[2]);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EquationPlacement {
    Bare,
    AroundEntry,
    InsideEntry,
    AroundEnvelope,
}

// All placements denote the same opaque Pair(stem, marker(stem)): only authored
// Alt-zero/Product-unit equations and congruence are inserted. Sharing changes
// source arena references, not syntax, values, or collection multiplicities.
fn equivalent_entry(
    arena: &mut CollectionArena<'_>,
    stem: &Tree,
    shared_stem: &mut Option<TheoryTermId>,
    share: bool,
    marker: Op,
    placement: EquationPlacement,
) -> TheoryTermId {
    let mut part = |arena: &mut CollectionArena<'_>| {
        if share {
            *shared_stem.get_or_insert_with(|| arena.tree(stem))
        } else {
            arena.tree(stem)
        }
    };
    let mut left = part(arena);
    let mut right = part(arena);
    if placement == EquationPlacement::InsideEntry {
        let unit = arena.app(Op::Unit, Vec::new());
        left = arena.app(Op::Product, vec![unit, left]);
        let zero = arena.app(Op::Zero, Vec::new());
        right = arena.app(Op::Alt, vec![right, zero]);
    }
    let marked = arena.app(marker, vec![right]);
    let entry = arena.app(Op::Pair, vec![left, marked]);
    if placement == EquationPlacement::AroundEntry {
        let zero = arena.app(Op::Zero, Vec::new());
        arena.app(Op::Alt, vec![zero, entry])
    } else {
        entry
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    #[test]
    fn section_runtime_equivalent_collection_enumerations_sharing_and_equation_placements_agree(
        salt in any::<u16>(), depth in 0usize..=3, repeats in 2usize..=4,
        rotation in 0usize..5, swapped_values in any::<bool>(),
    ) {
        for (kind, mode) in [
            (CollectionKind::Bag, None),
            (CollectionKind::Set, None),
            (CollectionKind::Map, None),
            (CollectionKind::PathMap, Some(PathMapModeV1::Map)),
            (CollectionKind::PathMap, Some(PathMapModeV1::Set)),
        ] {
            let mut source = collection_section(salt);
            let mut stem = leaf(Op::Atom);
            for _ in 0..depth { stem = unary(Op::Plus, stem); }
            let pair_entries = kind == CollectionKind::Map || mode == Some(PathMapModeV1::Map);
            let keyed = kind == CollectionKind::Map || kind == CollectionKind::PathMap;
            // Only Bag/Set enumerate duplicate entries. Every Map/PathMap
            // retains two distinct normal keys, so these are successful
            // equivalence controls, not the collision-refusal cases above.
            let mut rows = if keyed { vec![0] } else { vec![0; repeats] };
            rows.push(1);
            let mut reversed = rows.clone();
            reversed.reverse();
            prop_assert_ne!(&rows, &reversed, "the source enumeration really changes");
            let mut rotated = rows.clone();
            let row_count = rotated.len();
            rotated.rotate_left(rotation % row_count);
            let mut build = |order: &[usize], placement, share| {
                let seed = add_builder(&mut source, |arena| {
                    let mut shared_stem = None;
                    let mut entries = Vec::new();
                    for &row in order {
                        // Distinct opaque markers prove the two normalized
                        // keys stay different without a test-local evaluator.
                        let markers = [Op::Optional, Op::Repeat];
                        let key = equivalent_entry(arena, &stem, &mut shared_stem,
                            share, markers[row], placement);
                        let entry = if pair_entries {
                            let value_row = if swapped_values { 1 - row } else { row };
                            let value = equivalent_entry(arena, &stem, &mut shared_stem,
                                share, markers[value_row], placement);
                            arena.pair(key, value)
                        } else { key };
                        entries.push(entry);
                    }
                    let wrapped = arena.wrapped(kind, mode, entries);
                    if placement == EquationPlacement::AroundEnvelope {
                        let unit = arena.app(Op::Unit, Vec::new());
                        arena.app(Op::Product, vec![wrapped, unit])
                    } else { wrapped }
                });
                let terms = source.fixture.language.theory.rewrites.last()
                    .expect("the source builder was appended").arena.terms.len();
                (seed, terms)
            };
            let (plain, _) = build(&rows, EquationPlacement::Bare, false);
            let (duplicated, duplicate_terms) = build(&rows, EquationPlacement::AroundEntry, false);
            let (shared, shared_terms) = build(&reversed, EquationPlacement::AroundEntry, true);
            let (inside, _) = build(&rotated, EquationPlacement::InsideEntry, true);
            let (outside, _) = build(&reversed, EquationPlacement::AroundEnvelope, false);
            prop_assert!(shared_terms < duplicate_terms,
                "the source arenas differ in sharing, even though egraph admission hash-conses both");
            let semantic = compiled_section(&source.fixture.language);
            let expected = constructed(&source, &semantic, plain);
            let duplicated_input = constructed(&source, &semantic, duplicated);
            let shared_input = constructed(&source, &semantic, shared);
            prop_assert_eq!(duplicated_input.exact_key(), shared_input.exact_key(),
                "the existing canonicalizer makes enumeration and arena sharing immaterial");
            let inside_input = constructed(&source, &semantic, inside);
            prop_assert_ne!(duplicated_input.exact_key(), inside_input.exact_key(),
                "alternate equation placement produces genuinely different pre-section terms");
            let outside_input = constructed(&source, &semantic, outside);
            let offset = usize::from(mode.is_some());
            if keyed {
                let key_path = |index| if pair_entries { vec![0, offset + index, 0] } else { vec![0, offset + index] };
                let normal_keys: Vec<_> = (0..2).map(|index|
                    descendant(&expected, &key_path(index)).exact_key().clone()).collect();
                prop_assert_ne!(&normal_keys[0], &normal_keys[1]);
                for original in [&duplicated_input, &shared_input, &inside_input] {
                    for index in 0..2 {
                        let changed = descendant(original, &key_path(index));
                        prop_assert!(normal_keys.iter().all(|key| key != changed.exact_key()),
                            "each source Map/PathMap key actually changes under the equations");
                    }
                }
            }
            for original in [duplicated_input, shared_input, inside_input, outside_input] {
                prop_assert_ne!(original.exact_key(), expected.exact_key());
                let report = success(normalize(&source.fixture, &semantic, original, limits(), || false));
                assert_report(&report, &expected);
                prop_assert!(report.phases[0].saturation.stats.total_merges > 0);
                prop_assert_eq!(collection_len(&report.normal_form),
                    if kind == CollectionKind::Bag { repeats + 1 } else { 2 + offset });
            }
        }
    }
}
