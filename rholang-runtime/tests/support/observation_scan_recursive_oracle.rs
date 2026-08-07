use mettail_runtime::RuntimeObservationValue;

pub(crate) fn binder_apply_redex_present(
    apply_label: &str,
    value: &RuntimeObservationValue,
) -> bool {
    match value {
        RuntimeObservationValue::Term { constructor, children } => {
            (constructor == apply_label
                && matches!(
                    children.first(),
                    Some(RuntimeObservationValue::Term { constructor, .. })
                        if constructor == "^lambda"
                ))
                || children
                    .iter()
                    .any(|child| binder_apply_redex_present(apply_label, child))
        },
        RuntimeObservationValue::List(items)
        | RuntimeObservationValue::Tuple(items)
        | RuntimeObservationValue::Set(items) => items
            .iter()
            .any(|item| binder_apply_redex_present(apply_label, item)),
        RuntimeObservationValue::Bag(entries) => entries
            .iter()
            .any(|(value, _)| binder_apply_redex_present(apply_label, value)),
        RuntimeObservationValue::Map(entries) => entries.iter().any(|(key, value)| {
            binder_apply_redex_present(apply_label, key)
                || binder_apply_redex_present(apply_label, value)
        }),
        _ => false,
    }
}

pub(crate) fn flatten(value: &RuntimeObservationValue) -> RuntimeObservationValue {
    match value {
        RuntimeObservationValue::Bag(entries) => {
            let mut flat = Vec::with_capacity(entries.len());
            for (element, count) in entries {
                let element = flatten(element);
                for _ in 0..*count {
                    match &element {
                        RuntimeObservationValue::Bag(inner) => {
                            for (inner_element, inner_count) in inner {
                                for _ in 0..*inner_count {
                                    flat.push((inner_element.clone(), 1));
                                }
                            }
                        },
                        other => flat.push((other.clone(), 1)),
                    }
                }
            }
            RuntimeObservationValue::Bag(flat)
        },
        RuntimeObservationValue::Term { constructor, children } => RuntimeObservationValue::Term {
            constructor: constructor.clone(),
            children: children.iter().map(flatten).collect(),
        },
        other => other.clone(),
    }
}

fn bag_elements(value: &RuntimeObservationValue) -> Option<Vec<&RuntimeObservationValue>> {
    match value {
        RuntimeObservationValue::Bag(entries) => {
            let mut elements = Vec::with_capacity(entries.len());
            for (element, count) in entries {
                for _ in 0..*count {
                    elements.push(element);
                }
            }
            Some(elements)
        },
        _ => None,
    }
}

pub(crate) fn guarded_ac_trio_redex_present(
    amb_label: &str,
    in_label: &str,
    out_label: &str,
    open_label: &str,
    value: &RuntimeObservationValue,
) -> bool {
    let recurse = |child: &RuntimeObservationValue| {
        guarded_ac_trio_redex_present(amb_label, in_label, out_label, open_label, child)
    };
    if let RuntimeObservationValue::Term { constructor, children } = value {
        if constructor == amb_label && children.len() == 2 {
            let outer_name = &children[0];
            if let Some(body) = bag_elements(&children[1]) {
                for element in &body {
                    let RuntimeObservationValue::Term { constructor, children } = element else {
                        continue;
                    };
                    if constructor != amb_label || children.len() != 2 {
                        continue;
                    }
                    let Some(inner) = bag_elements(&children[1]) else {
                        continue;
                    };
                    if inner.iter().any(|inner_element| {
                        matches!(
                            inner_element,
                            RuntimeObservationValue::Term { constructor, children }
                                if constructor == out_label
                                    && children.first() == Some(outer_name)
                        )
                    }) {
                        return true;
                    }
                }
            }
        }
    }
    if let Some(elements) = bag_elements(value) {
        for (index, element) in elements.iter().enumerate() {
            let RuntimeObservationValue::Term { constructor, children } = element else {
                continue;
            };
            let sibling_amb_named = |name: &RuntimeObservationValue| {
                elements.iter().enumerate().any(|(sibling_index, sibling)| {
                    sibling_index != index
                        && matches!(
                            sibling,
                            RuntimeObservationValue::Term { constructor, children }
                                if constructor == amb_label && children.first() == Some(name)
                        )
                })
            };
            if constructor == open_label && children.len() == 2 && sibling_amb_named(&children[0]) {
                return true;
            }
            if constructor == amb_label && children.len() == 2 {
                if let Some(body) = bag_elements(&children[1]) {
                    if body.iter().any(|body_element| {
                        matches!(
                            body_element,
                            RuntimeObservationValue::Term { constructor, children }
                                if constructor == in_label
                                    && children.len() == 2
                                    && sibling_amb_named(&children[0])
                        )
                    }) {
                        return true;
                    }
                }
            }
        }
    }
    match value {
        RuntimeObservationValue::Term { children, .. } => children.iter().any(recurse),
        RuntimeObservationValue::List(items)
        | RuntimeObservationValue::Tuple(items)
        | RuntimeObservationValue::Set(items) => items.iter().any(recurse),
        RuntimeObservationValue::Bag(entries) => {
            entries.iter().any(|(element, _)| recurse(element))
        },
        RuntimeObservationValue::Map(entries) => entries
            .iter()
            .any(|(key, value)| recurse(key) || recurse(value)),
        _ => false,
    }
}
