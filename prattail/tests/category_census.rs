//! Shared-reader tests paired with the pre-relocation macro AST baselines.

use mettail_prattail::wpda_rule_analysis::census::{
    build_label_index_with, collect_category_names_with_literals, CategoryCensusReader,
};

// Intentionally not Clone: callbacks must observe the original occurrences.
struct Rule {
    id: usize,
    category: &'static str,
}

struct Category {
    id: usize,
    name: &'static str,
    collection: bool,
    native: bool,
}

struct Token {
    id: usize,
    from_literals: bool,
    category: Option<&'static str>,
}

struct Reader<'a> {
    rules: &'a [Rule],
    types: &'a [Category],
    tokens: &'a [Token],
    events: Vec<String>,
}

impl CategoryCensusReader for Reader<'_> {
    type Rule = Rule;
    type Type = Category;
    type Token = Token;

    fn rule_category(&mut self, rule: &Rule) -> String {
        assert!(std::ptr::eq(rule, &self.rules[rule.id]));
        self.events.push(format!("r{}", rule.id));
        rule.category.into()
    }

    fn type_name(&mut self, category: &Category) -> String {
        assert!(std::ptr::eq(category, &self.types[category.id]));
        self.events.push(format!("t{}", category.id));
        category.name.into()
    }

    fn has_collection(&mut self, category: &Category) -> bool {
        assert!(std::ptr::eq(category, &self.types[category.id]));
        self.events.push(format!("c{}", category.id));
        category.collection
    }

    fn has_native(&mut self, category: &Category) -> bool {
        assert!(std::ptr::eq(category, &self.types[category.id]));
        self.events.push(format!("n{}", category.id));
        category.native
    }

    fn from_literals(&mut self, token: &Token) -> bool {
        assert!(std::ptr::eq(token, &self.tokens[token.id]));
        self.events.push(format!("f{}", token.id));
        token.from_literals
    }

    fn token_category(&mut self, token: &Token) -> Option<String> {
        assert!(std::ptr::eq(token, &self.tokens[token.id]));
        self.events.push(format!("k{}", token.id));
        token.category.map(str::to_owned)
    }
}

#[test]
fn census_retains_original_borrows_and_lazy_five_pass_observations() {
    let rules = [
        Rule { id: 0, category: "RuleZ" },
        Rule { id: 1, category: "RuleA" },
        Rule { id: 2, category: "RuleZ" },
    ];
    let types = [
        Category {
            id: 0,
            name: "Reference",
            collection: false,
            native: false,
        },
        Category {
            id: 1,
            name: "Native",
            collection: false,
            native: true,
        },
        Category {
            id: 2,
            name: "Collection",
            collection: true,
            native: true,
        },
        Category {
            id: 3,
            name: "Literal",
            collection: true,
            native: true,
        },
        Category {
            id: 4,
            name: "RuleZ",
            collection: true,
            native: true,
        },
        Category {
            id: 5,
            name: "Literal",
            collection: false,
            native: false,
        },
    ];
    let tokens = [
        Token {
            id: 0,
            from_literals: false,
            category: Some("Reference"),
        },
        Token {
            id: 1,
            from_literals: true,
            category: None,
        },
        Token {
            id: 2,
            from_literals: true,
            category: Some("Literal"),
        },
        Token {
            id: 3,
            from_literals: true,
            category: Some("Undeclared"),
        },
    ];
    let mut reader = Reader {
        rules: &rules,
        types: &types,
        tokens: &tokens,
        events: vec![],
    };
    assert_eq!(
        collect_category_names_with_literals(&rules, &types, &tokens, &mut reader),
        ["RuleZ", "RuleA", "Literal", "Collection", "Native", "Reference"]
    );
    // Exact trace, not a second implementation of the discovery algorithm.
    // f0 never has k0; Literal stops before f3; seen categories still read
    // their names but not their eligibility or token observations.
    let expected = "r0 r1 r2
        t0 f0 f1 k1 f2 k2 f3 k3
        t1 f0 f1 k1 f2 k2 f3 k3
        t2 f0 f1 k1 f2 k2 f3 k3
        t3 f0 f1 k1 f2 k2
        t4 t5
        t0 c0 t1 c1 t2 c2 t3 t4 t5
        t0 n0 t1 n1 t2 t3 t4 t5
        t0 t1 t2 t3 t4 t5";
    assert_eq!(reader.events, expected.split_whitespace().collect::<Vec<_>>());
}

#[test]
fn empty_census_performs_no_observations() {
    let mut reader = Reader {
        rules: &[],
        types: &[],
        tokens: &[],
        events: vec![],
    };
    assert!(collect_category_names_with_literals(&[], &[], &[], &mut reader).is_empty());
    assert!(reader.events.is_empty());
}

#[test]
fn label_index_retains_borrow_order_owner_and_last_duplicate() {
    let categories = ["Z".into(), "Empty".into(), "Z".into(), "A".into()];
    let per_cat = vec![
        vec![Rule { id: 0, category: "NotOwner" }],
        vec![],
        vec![Rule { id: 1, category: "NotOwner" }, Rule { id: 2, category: "NotOwner" }],
        vec![Rule { id: 3, category: "NotOwner" }],
    ];
    let sources: Vec<_> = per_cat.iter().flatten().collect();
    let mut seen = Vec::with_capacity(sources.len());
    let index = build_label_index_with(&categories, &per_cat, |rule| {
        assert!(std::ptr::eq(rule, sources[rule.id]));
        seen.push(rule.id);
        "Same".into()
    });
    assert_eq!(seen, [0, 1, 2, 3]);
    assert_eq!(index.len(), 2);
    assert_eq!(index.get(&("Z".into(), "Same".into())), Some(&(2, 1)));
    assert_eq!(index.get(&("A".into(), "Same".into())), Some(&(3, 0)));
}

#[test]
fn original_narrowing_casts_are_not_replaced_by_a_new_admission_policy() {
    let row = (0..=65536).collect::<Vec<_>>();
    let mut count = 0;
    let index = build_label_index_with(&["Z".into()], &[row], |rule| {
        assert_eq!(*rule, count);
        count += 1;
        "Same".into()
    });
    assert_eq!(count, 65537);
    assert_eq!(index.get(&("Z".into(), "Same".into())), Some(&(0, 0)));

    let categories = vec!["Z".into(); 65537];
    let mut rows: Vec<Vec<usize>> = (0..categories.len()).map(|_| vec![]).collect();
    rows[0].push(0);
    rows[65536].push(65536);
    let mut seen = Vec::with_capacity(2);
    let index = build_label_index_with(&categories, &rows, |rule| {
        seen.push(*rule);
        "Same".into()
    });
    assert_eq!(seen, [0, 65536]);
    assert_eq!(index.get(&("Z".into(), "Same".into())), Some(&(0, 0)));
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn missing_category_is_checked_even_for_empty_rows() {
    let _ = build_label_index_with::<Rule>(&[], &[vec![]], |_| {
        panic!("empty row must never call its label reader")
    });
}
