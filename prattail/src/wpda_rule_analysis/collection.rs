//! Original collection-literal classifier over exact shallow observations.
//!
//! Collection kinds remain caller-owned values, not a new native-type taxonomy.
//! The source adapter must retain every authored position and project a Sep with
//! a source expression to Other: unlike infix classification, this classifier
//! admits only source-free Sep operations. Pair-separator lookup remains a lazy
//! caller-owned operation at its original successful-classification site.

use super::InfixSyntaxShape;

/// Classification of a collection-literal rule, with the original fields.
#[derive(Debug, Clone)]
pub struct CollectionShape<K> {
    /// First-token slice of the open delimiter — what the lexer emits as a
    /// single `Fixed` token. When `has_synth_paren` is true, the full logical
    /// open delimiter is this token followed by a separate `"("` token.
    pub open_token: String,
    /// True when the synthetic-rule emitter (`synthetic.rs`) split a default
    /// open delimiter like `"list("` into the 4-element pattern
    /// `[Literal("list"), Literal("("), Op(Sep), Literal(close)]`. The
    /// engine consumes two tokens in sequence (open keyword, then `(`) before
    /// pushing the CollectionMarker.
    pub has_synth_paren: bool,
    /// Close delimiter.
    pub close: String,
    /// Separator between elements (e.g., `"|"` for HashBag, `","` for Map between pairs).
    pub separator: String,
    /// Pair separator for Map (`":"` between key and value). `None` for List/Bag/Set.
    pub pair_separator: Option<String>,
    /// Category name of each element (e.g., `"Proc"`).
    pub element_cat: String,
    /// Existing backend container kind, retained without reclassification.
    pub coll_kind: K,
    /// Constructor label (e.g., `"PPar"`).
    pub label: String,
}

/// Only observations consumed by the original collection classifier.
///
/// The kind is borrowed so projection does not clone it before the original
/// singleton-parameter and immediate-base-element checks succeed.
pub struct CollectionRuleShape<'a, K> {
    pub label: String,
    pub term_context: Option<Vec<CollectionParamShape<'a, K>>>,
    pub syntax_pattern: Option<Vec<InfixSyntaxShape>>,
}

/// Unsupported parameters keep their positions; they are never filtered.
pub enum CollectionParamShape<'a, K> {
    SimpleCollection {
        name: String,
        kind: &'a K,
        element_base: Option<String>,
    },
    Other,
}

/// Apply the original collection classifier in its original branch order.
///
/// Source-free Sep projection is part of the caller's observation contract.
/// The resolver returns the original declared-result-category pair separator;
/// None is a successful descriptor field, not classification failure.
pub fn classify_collection<K: Clone>(
    rule: &CollectionRuleShape<'_, K>,
    pair_separator: impl FnOnce() -> Option<String>,
) -> Option<CollectionShape<K>> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    // Expect exactly 1 Simple param of Collection type.
    if tc.len() != 1 {
        return None;
    }
    let (param_name, coll_type, element_ident) = match &tc[0] {
        CollectionParamShape::SimpleCollection { name, kind, element_base } => match element_base {
            Some(elem) => (name, K::clone(*kind), elem.to_string()),
            None => return None,
        },
        _ => return None,
    };
    // Accept 3-element [Literal, Sep, Literal] or 4-element
    // [Literal, Literal("("), Sep, Literal] form.
    let (open_token, has_synth_paren, sep_idx, close_idx) = match sp.len() {
        3 => {
            let open_kw = match &sp[0] {
                InfixSyntaxShape::Literal(s) => s.clone(),
                _ => return None,
            };
            (open_kw, false, 1usize, 2usize)
        },
        4 => {
            let open_kw = match &sp[0] {
                InfixSyntaxShape::Literal(s) => s.clone(),
                _ => return None,
            };
            // Second element must be the literal '(' split by synthesis.
            match &sp[1] {
                InfixSyntaxShape::Literal(s) if s == "(" => {},
                _ => return None,
            }
            (open_kw, true, 2usize, 3usize)
        },
        _ => return None,
    };
    let close = match &sp[close_idx] {
        InfixSyntaxShape::Literal(s) => s.clone(),
        _ => return None,
    };
    let separator = match &sp[sep_idx] {
        InfixSyntaxShape::Sep { collection, separator } if collection == param_name => {
            separator.clone()
        },
        _ => return None,
    };
    let pair_separator = pair_separator();
    Some(CollectionShape {
        open_token,
        has_synth_paren,
        close,
        separator,
        pair_separator,
        element_cat: element_ident,
        coll_kind: coll_type,
        label: rule.label.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    struct CountingKind {
        value: u8,
        events: Rc<RefCell<Vec<&'static str>>>,
    }

    impl Clone for CountingKind {
        fn clone(&self) -> Self {
            self.events.borrow_mut().push("clone");
            Self {
                value: self.value,
                events: Rc::clone(&self.events),
            }
        }
    }

    fn rule(kind: &CountingKind) -> CollectionRuleShape<'_, CountingKind> {
        CollectionRuleShape {
            label: "PPar".into(),
            term_context: Some(vec![CollectionParamShape::SimpleCollection {
                name: "ps".into(),
                kind,
                element_base: Some("Proc".into()),
            }]),
            syntax_pattern: Some(vec![
                InfixSyntaxShape::Literal("{".into()),
                InfixSyntaxShape::Sep {
                    collection: "ps".into(),
                    separator: "|".into(),
                },
                InfixSyntaxShape::Literal("}".into()),
            ]),
        }
    }

    #[test]
    fn collection_clone_waits_for_both_lists_singleton_and_base_element() {
        for case in 0..6 {
            let events = Rc::new(RefCell::new(Vec::new()));
            let kind = CountingKind { value: 7, events: Rc::clone(&events) };
            let mut view = rule(&kind);
            match case {
                0 => view.term_context = None,
                1 => view.syntax_pattern = None,
                2 => view.term_context = Some(vec![]),
                3 => view
                    .term_context
                    .as_mut()
                    .expect("fixture context")
                    .push(CollectionParamShape::Other),
                4 => view.term_context = Some(vec![CollectionParamShape::Other]),
                5 => {
                    view.term_context = Some(vec![CollectionParamShape::SimpleCollection {
                        name: "ps".into(),
                        kind: &kind,
                        element_base: None,
                    }])
                },
                _ => unreachable!(),
            }
            let result =
                classify_collection(&view, || panic!("early refusal cannot resolve pairs"));
            assert!(result.is_none(), "case {case}");
            assert!(events.borrow().is_empty(), "case {case} cloned before the original gate");
        }
    }

    #[test]
    fn collection_clone_precedes_syntax_refusal_but_pair_resolver_stays_lazy() {
        for syntax in [
            vec![],
            vec![InfixSyntaxShape::Literal("{".into())],
            vec![
                InfixSyntaxShape::Other,
                InfixSyntaxShape::Sep {
                    collection: "ps".into(),
                    separator: "|".into(),
                },
                InfixSyntaxShape::Literal("}".into()),
            ],
            vec![
                InfixSyntaxShape::Literal("list".into()),
                InfixSyntaxShape::Literal("[".into()),
                InfixSyntaxShape::Sep {
                    collection: "ps".into(),
                    separator: "|".into(),
                },
                InfixSyntaxShape::Literal("}".into()),
            ],
            vec![
                InfixSyntaxShape::Literal("{".into()),
                InfixSyntaxShape::Sep {
                    collection: "ps".into(),
                    separator: "|".into(),
                },
                InfixSyntaxShape::Other,
            ],
            vec![
                InfixSyntaxShape::Literal("{".into()),
                // This is also the required projection of source-bearing Sep.
                InfixSyntaxShape::Other,
                InfixSyntaxShape::Literal("}".into()),
            ],
            vec![
                InfixSyntaxShape::Literal("{".into()),
                InfixSyntaxShape::Sep {
                    collection: "different".into(),
                    separator: "|".into(),
                },
                InfixSyntaxShape::Literal("}".into()),
            ],
        ] {
            let events = Rc::new(RefCell::new(Vec::new()));
            let kind = CountingKind { value: 7, events: Rc::clone(&events) };
            let mut view = rule(&kind);
            view.syntax_pattern = Some(syntax);
            let result =
                classify_collection(&view, || panic!("syntax refusal cannot resolve pairs"));
            assert!(result.is_none());
            assert_eq!(*events.borrow(), ["clone"]);
        }
    }

    #[test]
    fn collection_pair_resolver_runs_once_after_clone_and_none_is_success() {
        for split_open in [false, true] {
            let events = Rc::new(RefCell::new(Vec::new()));
            let kind = CountingKind { value: 7, events: Rc::clone(&events) };
            let mut view = rule(&kind);
            if split_open {
                view.syntax_pattern = Some(vec![
                    InfixSyntaxShape::Literal("list".into()),
                    InfixSyntaxShape::Literal("(".into()),
                    InfixSyntaxShape::Sep {
                        collection: "ps".into(),
                        separator: "|".into(),
                    },
                    InfixSyntaxShape::Literal("}".into()),
                ]);
            }
            let payload = if split_open {
                Some(String::from("=>"))
            } else {
                None
            };
            let expected_pair = payload.clone();
            let shape = classify_collection(&view, || {
                events.borrow_mut().push("resolve");
                payload
            })
            .expect("both original collection shapes classify");
            assert_eq!(*events.borrow(), ["clone", "resolve"]);
            assert_eq!(shape.open_token, if split_open { "list" } else { "{" });
            assert_eq!(shape.has_synth_paren, split_open);
            assert_eq!(shape.close, "}");
            assert_eq!(shape.separator, "|");
            assert_eq!(shape.pair_separator, expected_pair);
            assert_eq!(shape.element_cat, "Proc");
            assert_eq!(shape.coll_kind.value, 7);
            assert_eq!(shape.label, "PPar");
        }
    }
}
