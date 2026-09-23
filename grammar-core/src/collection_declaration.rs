//! Original collection declaration defaults and ordered element selection.
//!
//! Frontends supply borrowed observations; this worker preserves the original
//! first-declaration and first-rule behavior. A declared collection's failed
//! native observation returns immediately instead of searching constructor rules.

use crate::CollectionKind;

/// Declared collection delimiters, including the optional key/value separator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectionDelimiters {
    pub open: String,
    pub close: String,
    pub sep: String,
    /// The original optional separator; absence is not a request for a default.
    pub key_val_sep: Option<String>,
}

/// Default delimiters for List: `list(`, `)`, `,`.
pub fn list_defaults() -> CollectionDelimiters {
    CollectionDelimiters {
        open: "list(".to_string(),
        close: ")".to_string(),
        sep: ",".to_string(),
        key_val_sep: None,
    }
}

/// Default delimiters for Bag: `bag(`, `)`, `,`.
pub fn bag_defaults() -> CollectionDelimiters {
    CollectionDelimiters {
        open: "bag(".to_string(),
        close: ")".to_string(),
        sep: ",".to_string(),
        key_val_sep: None,
    }
}

/// Default delimiters for Map: `map(`, `)`, `,`, `:`.
pub fn map_defaults() -> CollectionDelimiters {
    CollectionDelimiters {
        open: "map(".to_string(),
        close: ")".to_string(),
        sep: ",".to_string(),
        key_val_sep: Some(":".to_string()),
    }
}

/// Default delimiters for Set: `Set(`, `)`, `,`.
pub fn set_defaults() -> CollectionDelimiters {
    CollectionDelimiters {
        open: "Set(".to_string(),
        close: ")".to_string(),
        sep: ",".to_string(),
        key_val_sep: None,
    }
}

/// Default delimiters for Pathmap: `pathmap(`, `)`, `,`, `:`.
pub fn pathmap_defaults() -> CollectionDelimiters {
    CollectionDelimiters {
        open: "pathmap(".to_string(),
        close: ")".to_string(),
        sep: ",".to_string(),
        key_val_sep: Some(":".to_string()),
    }
}

/// Original declared-collection constructor labels, distinct from native labels.
pub fn declared_collection_literal_label(kind: CollectionKind) -> &'static str {
    match kind {
        CollectionKind::List => "ListLit",
        CollectionKind::Bag => "BagLit",
        CollectionKind::Map => "MapLit",
        CollectionKind::Set => "SetLit",
        CollectionKind::PathMap => "PathmapLit",
    }
}

/// Borrowed source observations at the original collection-selection sites.
/// Implementations retain source equality and clone only the selected element.
pub trait CollectionElementReader<'input> {
    type Declaration: 'input;
    type Rule: 'input;
    type Item: 'input;
    type Element;

    fn type_matches(&self, declaration: &'input Self::Declaration) -> bool;
    fn has_collection(&self, declaration: &'input Self::Declaration) -> bool;
    /// Preserve the original optional-native chain and its shallow element probe.
    fn native_element(&self, declaration: &'input Self::Declaration) -> Option<Self::Element>;
    fn rule_matches(&self, rule: &'input Self::Rule) -> bool;
    fn items(&self, rule: &'input Self::Rule) -> &'input [Self::Item];
    fn item_element(&self, item: &'input Self::Item) -> Option<Self::Element>;
}

/// Select exactly the original first declared native or first constructor element.
pub fn collection_element_for_category<'input, R: CollectionElementReader<'input>>(
    reader: &R,
    declarations: &'input [R::Declaration],
    rules: &'input [R::Rule],
) -> Option<R::Element> {
    if let Some(lang_type) = declarations.iter().find(|t| reader.type_matches(t)) {
        if reader.has_collection(lang_type) {
            return reader.native_element(lang_type);
        }
    }
    // Term-based: only the first matching constructor's items are searched.
    rules
        .iter()
        .find(|r| reader.rule_matches(r))
        .and_then(|r| reader.items(r).iter().find_map(|i| reader.item_element(i)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    struct Declaration {
        id: usize,
        matches: bool,
        collection: bool,
        native: Option<usize>,
    }

    struct Rule {
        id: usize,
        matches: bool,
        items: Vec<Option<usize>>,
    }

    #[derive(Default)]
    struct Reader {
        trace: RefCell<Vec<(&'static str, usize)>>,
    }

    impl<'input> CollectionElementReader<'input> for Reader {
        type Declaration = Declaration;
        type Rule = Rule;
        type Item = Option<usize>;
        type Element = usize;

        fn type_matches(&self, declaration: &'input Declaration) -> bool {
            self.trace.borrow_mut().push(("type", declaration.id));
            declaration.matches
        }

        fn has_collection(&self, declaration: &'input Declaration) -> bool {
            self.trace.borrow_mut().push(("collection", declaration.id));
            declaration.collection
        }

        fn native_element(&self, declaration: &'input Declaration) -> Option<usize> {
            self.trace.borrow_mut().push(("native", declaration.id));
            declaration.native
        }

        fn rule_matches(&self, rule: &'input Rule) -> bool {
            self.trace.borrow_mut().push(("rule", rule.id));
            rule.matches
        }

        fn items(&self, rule: &'input Rule) -> &'input [Option<usize>] {
            self.trace.borrow_mut().push(("items", rule.id));
            &rule.items
        }

        fn item_element(&self, item: &'input Option<usize>) -> Option<usize> {
            self.trace.borrow_mut().push(("item", item.unwrap_or(0)));
            *item
        }
    }

    #[test]
    fn shared_collection_native_result_stops_all_later_observations() {
        for native in [None, Some(7)] {
            let reader = Reader::default();
            let declarations = [
                Declaration {
                    id: 1,
                    matches: false,
                    collection: true,
                    native: Some(1),
                },
                Declaration {
                    id: 2,
                    matches: true,
                    collection: true,
                    native,
                },
                Declaration {
                    id: 3,
                    matches: true,
                    collection: true,
                    native: Some(3),
                },
            ];
            let rules = [Rule {
                id: 4,
                matches: true,
                items: vec![Some(4)],
            }];
            assert_eq!(collection_element_for_category(&reader, &declarations, &rules), native);
            assert_eq!(
                *reader.trace.borrow(),
                [("type", 1), ("type", 2), ("collection", 2), ("native", 2),]
            );
        }
    }

    #[test]
    fn shared_collection_first_noncollection_and_empty_rule_suppress_later_matches() {
        let reader = Reader::default();
        let declarations = [
            Declaration {
                id: 1,
                matches: true,
                collection: false,
                native: Some(1),
            },
            Declaration {
                id: 2,
                matches: true,
                collection: true,
                native: Some(2),
            },
        ];
        let rules = [
            Rule { id: 3, matches: true, items: vec![] },
            Rule {
                id: 4,
                matches: true,
                items: vec![Some(4)],
            },
        ];
        assert_eq!(collection_element_for_category(&reader, &declarations, &rules), None);
        assert_eq!(
            *reader.trace.borrow(),
            [("type", 1), ("collection", 1), ("rule", 3), ("items", 3),]
        );
    }

    #[test]
    fn shared_collection_term_scan_keeps_rule_and_item_order() {
        let reader = Reader::default();
        let declarations = [Declaration {
            id: 1,
            matches: false,
            collection: true,
            native: Some(1),
        }];
        let rules = [
            Rule {
                id: 2,
                matches: false,
                items: vec![Some(2)],
            },
            Rule {
                id: 3,
                matches: true,
                items: vec![None, Some(4), Some(5)],
            },
            Rule {
                id: 6,
                matches: true,
                items: vec![Some(6)],
            },
        ];
        assert_eq!(collection_element_for_category(&reader, &declarations, &rules), Some(4));
        assert_eq!(
            *reader.trace.borrow(),
            [("type", 1), ("rule", 2), ("rule", 3), ("items", 3), ("item", 0), ("item", 4),]
        );
    }

    #[test]
    fn shared_collection_defaults_and_declared_labels_keep_all_five_original_records() {
        for (kind, actual, opening, key_separator, label) in [
            (CollectionKind::List, list_defaults(), "list(", None, "ListLit"),
            (CollectionKind::Bag, bag_defaults(), "bag(", None, "BagLit"),
            (CollectionKind::Map, map_defaults(), "map(", Some(":"), "MapLit"),
            (CollectionKind::Set, set_defaults(), "Set(", None, "SetLit"),
            (CollectionKind::PathMap, pathmap_defaults(), "pathmap(", Some(":"), "PathmapLit"),
        ] {
            assert_eq!(
                actual,
                CollectionDelimiters {
                    open: opening.to_string(),
                    close: ")".to_string(),
                    sep: ",".to_string(),
                    key_val_sep: key_separator.map(str::to_string),
                }
            );
            assert_eq!(declared_collection_literal_label(kind), label);
        }
    }
}
