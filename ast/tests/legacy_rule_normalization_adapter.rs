//! Neutral adapter witnesses for the lifted original legacy normalizer.
//! Expected outputs and constructor traces are authored explicitly; the tests
//! do not implement a second conversion algorithm or construct a source AST.

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::legacy_rule_normalization::{
    normalize_legacy_rule_with, LegacyItemView, LegacyRuleNormalizationAdapter,
};
use std::cell::RefCell;

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
    events: RefCell<Vec<Event>>,
}

impl<'input> Adapter<'input> {
    fn new(items: &'input [Item]) -> Self {
        Self {
            items,
            context_present: false,
            syntax_present: false,
            events: RefCell::new(Vec::new()),
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
    let items = [
        category(10),
        Item::Binder(original(20)),
        Item::Binder(original(21)),
        Item::Terminal("between".into()),
        Item::Collection(7, original(30), "|".into(), Some(("[".into(), "]".into()))),
        category(40),
        Item::Collection(9, original(50), "::".into(), Some(("map(".into(), "END".into()))),
        category(60),
    ];
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
