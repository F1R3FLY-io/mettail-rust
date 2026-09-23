//! Neutral adapter witnesses for the lifted original legacy normalizer.
//! Expected outputs and constructor traces are authored explicitly; the tests
//! do not implement a second conversion algorithm or construct a source AST.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::legacy_rule_normalization::{
    normalize_legacy_rule_with, try_normalize_legacy_rule_with, LegacyItemView,
    LegacyNormalizationError, LegacyNormalizationEvent, LegacyRuleNormalizationAdapter,
};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
struct OriginalName {
    spelling: &'static str,
    identity: usize,
}

fn original(identity: usize) -> OriginalName {
    // Equal spelling must not discard the identity of the borrowed source.
    OriginalName { spelling: "Same", identity }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GeneratedName {
    Fresh(usize),
    Elems,
}

#[derive(Debug, PartialEq, Eq)]
enum Item {
    Terminal(String),
    NonTerminal(OriginalName, NonTerminalKind),
    Binder(OriginalName),
    Collection(u8, OriginalName, String, Option<(String, String)>),
}

fn category(identity: usize) -> Item {
    Item::NonTerminal(original(identity), NonTerminalKind::Category)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Param {
    Simple(GeneratedName, OriginalName),
    Abstraction(GeneratedName, GeneratedName, OriginalName, OriginalName),
    Collection(GeneratedName, u8, OriginalName),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Syntax {
    Literal(String),
    Param(GeneratedName),
    Sep(GeneratedName, String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    HasTermContext,
    HasSyntaxPattern,
    ItemsLen,
    Item(usize),
    Fresh(usize),
    Elems,
    ConstructParam(Param),
    ConstructSyntax(Syntax),
}

struct Adapter<'input> {
    items: &'input [Item],
    context_present: bool,
    syntax_present: bool,
    events: Rc<RefCell<Vec<Event>>>,
}

impl<'input> Adapter<'input> {
    fn new(items: &'input [Item]) -> Self {
        Self {
            items,
            context_present: false,
            syntax_present: false,
            events: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn param(&self, param: Param) -> Param {
        self.events
            .borrow_mut()
            .push(Event::ConstructParam(param.clone()));
        param
    }

    fn syntax(&self, syntax: Syntax) -> Syntax {
        self.events
            .borrow_mut()
            .push(Event::ConstructSyntax(syntax.clone()));
        syntax
    }
}

impl<'input> LegacyRuleNormalizationAdapter<'input> for Adapter<'input> {
    type OriginalName = OriginalName;
    type GeneratedName = GeneratedName;
    type CollectionKind = u8;
    type Param = Param;
    type Syntax = Syntax;

    fn has_term_context(&self) -> bool {
        self.events.borrow_mut().push(Event::HasTermContext);
        self.context_present
    }

    fn has_syntax_pattern(&self) -> bool {
        self.events.borrow_mut().push(Event::HasSyntaxPattern);
        self.syntax_present
    }

    fn items_len(&self) -> usize {
        self.events.borrow_mut().push(Event::ItemsLen);
        self.items.len()
    }

    fn item(&self, index: usize) -> LegacyItemView<'input, OriginalName, u8> {
        self.events.borrow_mut().push(Event::Item(index));
        match &self.items[index] {
            Item::Terminal(text) => LegacyItemView::Terminal(text),
            Item::NonTerminal(ident, kind) => LegacyItemView::NonTerminal { ident, kind: *kind },
            Item::Binder(category) => LegacyItemView::Binder { category },
            Item::Collection(kind, element, separator, delimiters) => LegacyItemView::Collection {
                kind,
                element,
                separator,
                delimiters: delimiters.as_ref().map(|(open, close)| (open, close)),
            },
        }
    }

    fn fresh_name(&mut self, index: usize) -> GeneratedName {
        self.events.borrow_mut().push(Event::Fresh(index));
        GeneratedName::Fresh(index)
    }

    fn elems_name(&mut self) -> GeneratedName {
        self.events.borrow_mut().push(Event::Elems);
        GeneratedName::Elems
    }

    fn make_simple(&mut self, name: GeneratedName, category: OriginalName) -> Param {
        self.param(Param::Simple(name, category))
    }

    fn make_abstraction(
        &mut self,
        binder: GeneratedName,
        body: GeneratedName,
        domain: OriginalName,
        codomain: OriginalName,
    ) -> Param {
        self.param(Param::Abstraction(binder, body, domain, codomain))
    }

    fn make_collection(&mut self, name: GeneratedName, kind: u8, element: OriginalName) -> Param {
        self.param(Param::Collection(name, kind, element))
    }

    fn make_literal(&mut self, text: String) -> Syntax {
        self.syntax(Syntax::Literal(text))
    }

    fn make_param(&mut self, name: GeneratedName) -> Syntax {
        self.syntax(Syntax::Param(name))
    }

    fn make_sep(&mut self, name: GeneratedName, separator: String) -> Syntax {
        self.syntax(Syntax::Sep(name, separator))
    }
}

fn assert_events(adapter: &Adapter<'_>, expected: &[Event]) {
    assert_eq!(adapter.events.borrow().as_slice(), expected);
}

fn rich_items() -> [Item; 8] {
    [
        category(10),
        Item::Binder(original(20)),
        Item::Binder(original(21)),
        Item::Terminal("between".into()),
        Item::Collection(7, original(30), "|".into(), Some(("[".into(), "]".into()))),
        category(40),
        Item::Collection(9, original(50), "::".into(), Some(("map(".into(), "END".into()))),
        category(60),
    ]
}

#[test]
fn presence_gates_short_circuit_before_any_item_or_constructor_observation() {
    let items = [category(17)];
    for syntax_present in [false, true] {
        let mut adapter = Adapter::new(&items);
        adapter.context_present = true;
        adapter.syntax_present = syntax_present;
        assert!(normalize_legacy_rule_with(&mut adapter).is_none());
        assert_events(&adapter, &[Event::HasTermContext]);
    }
    let mut adapter = Adapter::new(&items);
    adapter.syntax_present = true;
    assert!(normalize_legacy_rule_with(&mut adapter).is_none());
    assert_events(&adapter, &[Event::HasTermContext, Event::HasSyntaxPattern]);
}

#[test]
fn preflight_stops_at_noncategory_without_building_the_convertible_prefix() {
    for kind in [
        NonTerminalKind::Var,
        NonTerminalKind::Integer,
        NonTerminalKind::Boolean,
        NonTerminalKind::StringLiteral,
        NonTerminalKind::FloatLiteral,
        NonTerminalKind::Ident,
    ] {
        let items = [category(1), Item::NonTerminal(original(2), kind), category(3)];
        let mut adapter = Adapter::new(&items);
        assert!(normalize_legacy_rule_with(&mut adapter).is_none());
        assert_events(
            &adapter,
            &[
                Event::HasTermContext,
                Event::HasSyntaxPattern,
                Event::ItemsLen,
                Event::Item(0),
                Event::Item(1),
            ],
        );
    }
}

#[test]
fn missing_delimiters_keeps_the_original_constructed_prefix_trace_but_returns_none() {
    use GeneratedName::Fresh;
    let items = [
        Item::Terminal("prefix".into()),
        category(11),
        Item::Collection(5, original(22), ",".into(), None),
        category(33),
    ];
    let mut adapter = Adapter::new(&items);
    assert!(normalize_legacy_rule_with(&mut adapter).is_none());
    assert_events(
        &adapter,
        &[
            Event::HasTermContext,
            Event::HasSyntaxPattern,
            Event::ItemsLen,
            Event::Item(0),
            Event::Item(1),
            Event::Item(2),
            Event::Item(3),
            Event::ItemsLen,
            Event::Item(0),
            Event::ConstructSyntax(Syntax::Literal("prefix".into())),
            Event::Item(1),
            Event::Fresh(0),
            Event::ConstructParam(Param::Simple(Fresh(0), original(11))),
            Event::ConstructSyntax(Syntax::Param(Fresh(0))),
            Event::Item(2),
        ],
    );
    assert!(!adapter.context_present && !adapter.syntax_present);
}

#[test]
fn names_stay_distinct_while_pending_binder_and_duplicate_elems_preserve_order() {
    use GeneratedName::{Elems, Fresh};
    let items = rich_items();
    let mut adapter = Adapter::new(&items);
    let result = normalize_legacy_rule_with(&mut adapter).expect("neutral rule normalizes");
    let expected_params = vec![
        Param::Simple(Fresh(0), original(10)),
        Param::Collection(Elems, 7, original(30)),
        Param::Abstraction(Fresh(1), Fresh(2), original(21), original(40)),
        Param::Collection(Elems, 9, original(50)),
        Param::Simple(Fresh(3), original(60)),
    ];
    let expected_syntax = vec![
        Syntax::Param(Fresh(0)),
        Syntax::Literal("between".into()),
        Syntax::Literal("[".into()),
        Syntax::Sep(Elems, "|".into()),
        Syntax::Literal("]".into()),
        Syntax::Param(Fresh(1)),
        Syntax::Param(Fresh(2)),
        Syntax::Literal("map(".into()),
        Syntax::Sep(Elems, "::".into()),
        Syntax::Literal("END".into()),
        Syntax::Param(Fresh(3)),
    ];
    assert_eq!(result, (expected_params.clone(), expected_syntax.clone()));
    let mut expected_events = vec![Event::HasTermContext, Event::HasSyntaxPattern, Event::ItemsLen];
    expected_events.extend((0..8).map(Event::Item));
    expected_events.extend([
        Event::ItemsLen,
        Event::Item(0),
        Event::Fresh(0),
        Event::ConstructParam(expected_params[0].clone()),
        Event::ConstructSyntax(expected_syntax[0].clone()),
        Event::Item(1),
        Event::Item(2),
        Event::Item(3),
        Event::ConstructSyntax(expected_syntax[1].clone()),
        Event::Item(4),
        Event::Elems,
        Event::ConstructParam(expected_params[1].clone()),
        Event::ConstructSyntax(expected_syntax[2].clone()),
        Event::ConstructSyntax(expected_syntax[3].clone()),
        Event::ConstructSyntax(expected_syntax[4].clone()),
        Event::Item(5),
        Event::Fresh(1),
        Event::Fresh(2),
        Event::ConstructParam(expected_params[2].clone()),
        Event::ConstructSyntax(expected_syntax[5].clone()),
        Event::ConstructSyntax(expected_syntax[6].clone()),
        Event::Item(6),
        Event::Elems,
        Event::ConstructParam(expected_params[3].clone()),
        Event::ConstructSyntax(expected_syntax[7].clone()),
        Event::ConstructSyntax(expected_syntax[8].clone()),
        Event::ConstructSyntax(expected_syntax[9].clone()),
        Event::Item(7),
        Event::Fresh(3),
        Event::ConstructParam(expected_params[4].clone()),
        Event::ConstructSyntax(expected_syntax[10].clone()),
    ]);
    assert_events(&adapter, &expected_events);
    assert!(std::ptr::eq(adapter.items, items.as_slice()));
    assert!(!adapter.context_present && !adapter.syntax_present);
}

#[test]
fn trailing_binder_discards_built_outputs_without_constructing_a_binder_parameter() {
    let items = [category(1), Item::Binder(original(2)), Item::Terminal("last".into())];
    let mut adapter = Adapter::new(&items);
    assert!(normalize_legacy_rule_with(&mut adapter).is_none());
    assert_events(
        &adapter,
        &[
            Event::HasTermContext,
            Event::HasSyntaxPattern,
            Event::ItemsLen,
            Event::Item(0),
            Event::Item(1),
            Event::Item(2),
            Event::ItemsLen,
            Event::Item(0),
            Event::Fresh(0),
            Event::ConstructParam(Param::Simple(GeneratedName::Fresh(0), original(1))),
            Event::ConstructSyntax(Syntax::Param(GeneratedName::Fresh(0))),
            Event::Item(1),
            Event::Item(2),
            Event::ConstructSyntax(Syntax::Literal("last".into())),
        ],
    );
}

#[test]
fn pure_literals_are_constructed_then_refused_and_empty_input_has_no_constructors() {
    let items = [Item::Terminal("(".into()), Item::Terminal(")".into())];
    let mut adapter = Adapter::new(&items);
    assert!(normalize_legacy_rule_with(&mut adapter).is_none());
    assert_events(
        &adapter,
        &[
            Event::HasTermContext,
            Event::HasSyntaxPattern,
            Event::ItemsLen,
            Event::Item(0),
            Event::Item(1),
            Event::ItemsLen,
            Event::Item(0),
            Event::ConstructSyntax(Syntax::Literal("(".into())),
            Event::Item(1),
            Event::ConstructSyntax(Syntax::Literal(")".into())),
        ],
    );
    let mut empty = Adapter::new(&[]);
    assert!(normalize_legacy_rule_with(&mut empty).is_none());
    assert_events(
        &empty,
        &[Event::HasTermContext, Event::HasSyntaxPattern, Event::ItemsLen, Event::ItemsLen],
    );
}

/// Owned test observations of the borrowed admission API, not another converter.
#[derive(Clone, Debug, PartialEq, Eq)]
enum AdmissionSnapshot {
    PreflightItem(usize),
    BuildItem(usize),
    FreshName(usize),
    ElemsName,
    PendingBinder(OriginalName),
    Simple {
        name: GeneratedName,
        category: OriginalName,
    },
    Abstraction {
        binder: GeneratedName,
        body: GeneratedName,
        domain: OriginalName,
        codomain: OriginalName,
    },
    Collection {
        name: GeneratedName,
        kind: u8,
        element: OriginalName,
    },
    Literal(String),
    Param(GeneratedName),
    Sep {
        name: GeneratedName,
        separator: String,
    },
}

fn admission_snapshot(
    event: LegacyNormalizationEvent<'_, OriginalName, GeneratedName, u8>,
) -> AdmissionSnapshot {
    use LegacyNormalizationEvent as Input;
    match event {
        Input::PreflightItem(index) => AdmissionSnapshot::PreflightItem(index),
        Input::BuildItem(index) => AdmissionSnapshot::BuildItem(index),
        Input::FreshName(index) => AdmissionSnapshot::FreshName(index),
        Input::ElemsName => AdmissionSnapshot::ElemsName,
        Input::PendingBinder(category) => AdmissionSnapshot::PendingBinder(category.clone()),
        Input::Simple { name, category } => AdmissionSnapshot::Simple {
            name: name.clone(),
            category: category.clone(),
        },
        Input::Abstraction { binder, body, domain, codomain } => AdmissionSnapshot::Abstraction {
            binder: binder.clone(),
            body: body.clone(),
            domain: domain.clone(),
            codomain: codomain.clone(),
        },
        Input::Collection { name, kind, element } => AdmissionSnapshot::Collection {
            name: name.clone(),
            kind: *kind,
            element: element.clone(),
        },
        Input::Literal(text) => AdmissionSnapshot::Literal(text.to_owned()),
        Input::Param(name) => AdmissionSnapshot::Param(name.clone()),
        Input::Sep { name, separator } => AdmissionSnapshot::Sep {
            name: name.clone(),
            separator: separator.to_owned(),
        },
    }
}

fn rich_expected_admissions() -> Vec<AdmissionSnapshot> {
    use AdmissionSnapshot as A;
    use GeneratedName::{Elems, Fresh};
    let mut events: Vec<_> = (0..8).map(A::PreflightItem).collect();
    events.extend([
        A::BuildItem(0),
        A::FreshName(0),
        A::Simple { name: Fresh(0), category: original(10) },
        A::Param(Fresh(0)),
        A::BuildItem(1),
        A::PendingBinder(original(20)),
        A::BuildItem(2),
        A::PendingBinder(original(21)),
        A::BuildItem(3),
        A::Literal("between".into()),
        A::BuildItem(4),
        A::ElemsName,
        A::Collection {
            name: Elems,
            kind: 7,
            element: original(30),
        },
        A::Literal("[".into()),
        A::Sep { name: Elems, separator: "|".into() },
        A::Literal("]".into()),
        A::BuildItem(5),
        A::FreshName(1),
        A::FreshName(2),
        A::Abstraction {
            binder: Fresh(1),
            body: Fresh(2),
            domain: original(21),
            codomain: original(40),
        },
        A::Param(Fresh(1)),
        A::Param(Fresh(2)),
        A::BuildItem(6),
        A::ElemsName,
        A::Collection {
            name: Elems,
            kind: 9,
            element: original(50),
        },
        A::Literal("map(".into()),
        A::Sep { name: Elems, separator: "::".into() },
        A::Literal("END".into()),
        A::BuildItem(7),
        A::FreshName(3),
        A::Simple { name: Fresh(3), category: original(60) },
        A::Param(Fresh(3)),
    ]);
    events
}

#[test]
fn admission_acceptance_preserves_rich_original_output_and_exact_site_payloads() {
    let items = rich_items();
    let mut original_adapter = Adapter::new(&items);
    let original_output = normalize_legacy_rule_with(&mut original_adapter)
        .expect("the original rich fixture normalizes");
    let mut adapter = Adapter::new(&items);
    let callbacks = Rc::clone(&adapter.events);
    let mut admissions = Vec::new();
    let mut before_site = Vec::new();
    let output = try_normalize_legacy_rule_with(&mut adapter, |event| {
        admissions.push(admission_snapshot(event));
        before_site.push(callbacks.borrow().clone());
        Ok::<_, usize>(())
    })
    .expect("all rich-fixture sites are admitted")
    .expect("the admitted rich fixture normalizes");
    assert_eq!(output, original_output);
    assert_events(&adapter, &original_adapter.events.borrow());
    assert_eq!(admissions, rich_expected_admissions());
    assert_eq!(admissions.len(), 40, "all original admission variants are exercised");
    assert_eq!(before_site.len(), 40);
    assert_eq!(
        before_site[0],
        [Event::HasTermContext, Event::HasSyntaxPattern, Event::ItemsLen],
        "the first item read follows its admission",
    );
    assert!(std::ptr::eq(adapter.items, items.as_slice()));
    assert!(!adapter.context_present && !adapter.syntax_present);
}

#[test]
fn admission_denial_at_every_rich_site_stops_before_its_callback_and_all_suffixes() {
    let items = rich_items();
    let mut accepted = Adapter::new(&items);
    let accepted_callbacks = Rc::clone(&accepted.events);
    let mut before_site = Vec::new();
    let mut accepted_sites = Vec::new();
    let accepted_output = try_normalize_legacy_rule_with(&mut accepted, |event| {
        accepted_sites.push(admission_snapshot(event));
        before_site.push(accepted_callbacks.borrow().clone());
        Ok::<_, usize>(())
    })
    .expect("reference rich-fixture admissions all succeed");
    assert!(accepted_output.is_some());
    assert_eq!(accepted_sites, rich_expected_admissions());
    assert_eq!(before_site.len(), 40);

    for denied in 0..before_site.len() {
        let mut adapter = Adapter::new(&items);
        let mut observed = Vec::new();
        let result = try_normalize_legacy_rule_with(&mut adapter, |event| {
            let index = observed.len();
            observed.push(admission_snapshot(event));
            if index == denied {
                Err(index)
            } else {
                Ok(())
            }
        });
        assert!(
            matches!(result, Err(LegacyNormalizationError::Admission(index)) if index == denied),
            "denied site {denied} must return its admission error, never a partial pair or None",
        );
        assert_eq!(observed, accepted_sites[..=denied], "admission suffix at site {denied}");
        assert_events(&adapter, &before_site[denied]);
        assert!(std::ptr::eq(adapter.items, items.as_slice()));
        assert!(!adapter.context_present && !adapter.syntax_present);
    }
}

#[test]
fn admission_presence_gates_never_call_even_an_always_denying_policy() {
    let items = rich_items();
    for (context, syntax, expected) in [
        (true, false, vec![Event::HasTermContext]),
        (true, true, vec![Event::HasTermContext]),
        (false, true, vec![Event::HasTermContext, Event::HasSyntaxPattern]),
    ] {
        let mut adapter = Adapter::new(&items);
        adapter.context_present = context;
        adapter.syntax_present = syntax;
        let mut calls = 0;
        let result = try_normalize_legacy_rule_with(&mut adapter, |_| {
            calls += 1;
            Err::<(), _>("presence gate must avoid admission")
        })
        .expect("presence refusal does not invoke admission");
        assert!(result.is_none());
        assert_eq!(calls, 0);
        assert_events(&adapter, &expected);
        assert_eq!((adapter.context_present, adapter.syntax_present), (context, syntax));
    }
}

#[test]
fn admission_preflight_retains_noncategory_refusal_before_all_build_sites() {
    let items = [category(1), Item::NonTerminal(original(2), NonTerminalKind::Var), category(3)];
    let mut adapter = Adapter::new(&items);
    let mut sites = Vec::new();
    let output = try_normalize_legacy_rule_with(&mut adapter, |event| {
        sites.push(admission_snapshot(event));
        Ok::<_, usize>(())
    })
    .expect("the original noncategory refusal is not an admission error");
    assert!(output.is_none());
    assert_eq!(
        sites,
        [AdmissionSnapshot::PreflightItem(0), AdmissionSnapshot::PreflightItem(1)]
    );
    assert_events(
        &adapter,
        &[
            Event::HasTermContext,
            Event::HasSyntaxPattern,
            Event::ItemsLen,
            Event::Item(0),
            Event::Item(1),
        ],
    );

    let mut denied = Adapter::new(&items);
    let result = try_normalize_legacy_rule_with(&mut denied, |event| {
        if matches!(event, LegacyNormalizationEvent::PreflightItem(1)) {
            Err(1)
        } else {
            Ok(())
        }
    });
    assert!(matches!(result, Err(LegacyNormalizationError::Admission(1))));
    assert_events(
        &denied,
        &[Event::HasTermContext, Event::HasSyntaxPattern, Event::ItemsLen, Event::Item(0)],
    );
}

#[test]
fn admission_keeps_original_semantic_none_separate_from_errors_after_private_prefixes() {
    let cases = [
        vec![category(1), Item::Collection(5, original(2), ",".into(), None), category(3)],
        vec![category(1), Item::Binder(original(2)), Item::Terminal("last".into())],
        vec![Item::Terminal("(".into()), Item::Terminal(")".into())],
        vec![],
    ];
    for items in &cases {
        let mut original_adapter = Adapter::new(items);
        assert!(normalize_legacy_rule_with(&mut original_adapter).is_none());
        let mut adapter = Adapter::new(items);
        let callbacks = Rc::clone(&adapter.events);
        let mut observations = Vec::new();
        let output = try_normalize_legacy_rule_with(&mut adapter, |event| {
            observations.push((admission_snapshot(event), callbacks.borrow().clone()));
            Ok::<_, usize>(())
        })
        .expect("accepted sites preserve semantic refusal rather than fabricate an error");
        assert!(output.is_none());
        assert_events(&adapter, &original_adapter.events.borrow());
        assert!(!adapter.context_present && !adapter.syntax_present);
        for denied_index in 0..observations.len() {
            let mut denied = Adapter::new(items);
            let mut calls = 0;
            let result = try_normalize_legacy_rule_with(&mut denied, |_| {
                let index = calls;
                calls += 1;
                if index == denied_index {
                    Err(index)
                } else {
                    Ok(())
                }
            });
            assert!(
                matches!(result, Err(LegacyNormalizationError::Admission(index)) if index == denied_index)
            );
            assert_eq!(calls, denied_index + 1);
            assert_events(&denied, &observations[denied_index].1);
        }
        if items.is_empty() {
            assert!(observations.is_empty(), "empty input has no admission sites");
        }
    }
}
