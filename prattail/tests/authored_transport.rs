use mettail_grammar_core as core;
use mettail_prattail::{
    binding_power::Associativity, compose::compose_languages, CategorySpec, LanguageSpec,
    RuleSpecInput, SyntaxItemSpec,
};
use std::sync::Arc;

fn store() -> (Arc<core::AuthoredRuleStore>, [core::AuthoredRuleId; 2]) {
    let mut store = core::AuthoredRuleStore::new();
    let category = core::AuthoredNameId(
        store
            .try_push(core::AuthoredNode::Name(core::AuthoredName {
                spelling: "Term".into(),
                equality_class: 0,
            }))
            .expect("authored fixture node is retained"),
    );
    let mut rules = Vec::new();
    for (index, spelling) in ["Zero", "One"].into_iter().enumerate() {
        let label = core::AuthoredNameId(
            store
                .try_push(core::AuthoredNode::Name(core::AuthoredName {
                    spelling: spelling.into(),
                    equality_class: index as u32 + 1,
                }))
                .expect("authored fixture node is retained"),
        );
        rules.push(core::AuthoredRuleId(
            store
                .try_push(core::AuthoredNode::Rule(core::AuthoredRule {
                    label,
                    category,
                    term_context: None,
                    syntax_pattern: None,
                    items: vec![core::AuthoredLegacyItem::Terminal(spelling.into())],
                }))
                .expect("authored fixture node is retained"),
        ));
    }
    (
        Arc::new(store),
        rules
            .try_into()
            .expect("fixture contains exactly two rules"),
    )
}

fn input(label: &str, authored: Option<core::AuthoredRuleRef>) -> RuleSpecInput {
    RuleSpecInput {
        authored,
        label: label.into(),
        category: "Term".into(),
        syntax: vec![SyntaxItemSpec::Terminal(label.into())],
        associativity: Associativity::Left,
        shares_level_with_previous: false,
        prefix_precedence: None,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
        source_location: None,
        is_auto_injected: false,
    }
}

fn language(inputs: Vec<RuleSpecInput>) -> LanguageSpec {
    LanguageSpec::new(
        "Transport".into(),
        vec![CategorySpec {
            name: "Term".into(),
            native_type: None,
            is_primary: true,
            has_var: false,
        }],
        inputs,
    )
}

#[test]
fn authored_transport_forwards_exact_owner_and_rule_through_composition() {
    let (store, rules) = store();
    let left = language(vec![input(
        "Zero",
        Some(core::AuthoredRuleRef {
            store: Arc::clone(&store),
            rule: rules[0],
        }),
    )]);
    let right = language(vec![input(
        "One",
        Some(core::AuthoredRuleRef {
            store: Arc::clone(&store),
            rule: rules[1],
        }),
    )]);
    assert!(Arc::ptr_eq(
        &left.rules[0]
            .authored
            .as_ref()
            .expect("authored rule was forwarded")
            .store,
        &store
    ));
    let combined = compose_languages(&left, &right).expect("compatible source grammars compose");
    for (rule, expected) in combined.rules.iter().zip(rules) {
        let authored = rule.authored.as_ref().expect("authored rule was forwarded");
        assert!(Arc::ptr_eq(&authored.store, &store));
        assert_eq!(authored.rule, expected);
    }
    let grammar = combined
        .to_grammar_core()
        .expect("compatible authored references lower to one store");
    assert_eq!(grammar.authored.as_ref(), Some(store.as_ref()));
    assert_eq!(
        grammar
            .productions
            .iter()
            .map(|rule| rule.authored)
            .collect::<Vec<_>>(),
        rules.into_iter().map(Some).collect::<Vec<_>>()
    );
}

#[test]
fn authored_transport_rejects_equal_payload_in_distinct_allocations() {
    let (store, rules) = store();
    let second = Arc::new(store.as_ref().clone());
    assert_eq!(store, second);
    assert!(!Arc::ptr_eq(&store, &second));
    let language = language(vec![
        input("Zero", Some(core::AuthoredRuleRef { store, rule: rules[0] })),
        input("One", Some(core::AuthoredRuleRef { store: second, rule: rules[1] })),
    ]);
    assert!(language
        .to_grammar_core()
        .expect_err("invalid authored transport must be refused")
        .contains("different authored store"));
}

#[test]
fn authored_transport_absence_does_not_erase_another_rule_owner() {
    let (store, rules) = store();
    for present_first in [false, true] {
        let present = input(
            "Zero",
            Some(core::AuthoredRuleRef {
                store: Arc::clone(&store),
                rule: rules[0],
            }),
        );
        let absent = input("One", None);
        let inputs = if present_first {
            vec![present, absent]
        } else {
            vec![absent, present]
        };
        let grammar = language(inputs)
            .to_grammar_core()
            .expect("compatible authored references lower to one store");
        assert_eq!(grammar.authored.as_ref(), Some(store.as_ref()));
        assert_eq!(grammar.productions[usize::from(!present_first)].authored, Some(rules[0]));
        assert_eq!(grammar.productions[usize::from(present_first)].authored, None);
    }
    let grammar = language(vec![input("Zero", None)])
        .to_grammar_core()
        .expect("compatible authored references lower to one store");
    assert_eq!(grammar.authored, None);
    assert_eq!(grammar.productions[0].authored, None);
}

#[test]
fn authored_transport_bridge_rejects_mismatched_rule_association() {
    let (store, rules) = store();
    let language =
        language(vec![input("Zero", Some(core::AuthoredRuleRef { store, rule: rules[1] }))]);
    assert!(language
        .to_grammar_core()
        .expect_err("invalid authored transport must be refused")
        .contains("InvalidAuthoredRule"));
}
