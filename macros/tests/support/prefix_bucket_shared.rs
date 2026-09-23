// Shared-driver adapter checks, separate from the frozen original snapshots.
use super::*;
use mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor;
use mettail_prattail::wpda_rule_analysis::atomic_prefix::UnifiedDescriptor;
use mettail_prattail::wpda_rule_analysis::prefix::{
    FirstLegacyItem, FirstPredicate, FirstSetContext, IdentSummaryContext,
};
use mettail_prattail::wpda_rule_analysis::prefix_bucket::{
    derive_prefix_buckets, PrefixBucketContext,
};
use std::cell::RefCell;

type Reader = super::super::super::binder::MacroBinderSyntaxReader;

struct Observed<'source> {
    original: MacroFirstSetContext<'source>,
    calls: RefCell<Vec<String>>,
}

impl<'source> Observed<'source> {
    fn new(language: &'source LanguageDef) -> Self {
        Self {
            original: MacroFirstSetContext { language },
            calls: RefCell::new(Vec::new()),
        }
    }

    fn call(&self, event: String) {
        self.calls.borrow_mut().push(event);
    }
}

impl<'source> FirstSetContext<'source, Reader> for Observed<'source> {
    type Category = &'source LangType;
    type Literal = AtomicShape;
    // No TokenStream payload is required by the shared driver itself.
    type Pattern = String;

    fn rules_len(&self) -> usize {
        self.original.rules_len()
    }
    fn rule_at(&self, index: usize) -> &'source GrammarRule {
        self.original.rule_at(index)
    }
    fn find_category(&mut self, name: &str) -> Option<Self::Category> {
        self.call(format!("find:{name}"));
        self.original.find_category(name)
    }
    fn is_data(&self, category: Self::Category) -> bool {
        self.original.is_data(category)
    }
    fn collection_open(&self, category: Self::Category) -> Option<&'source str> {
        self.original.collection_open(category)
    }
    fn legacy_first(
        &self,
        rule: &'source GrammarRule,
    ) -> Option<FirstLegacyItem<'source, &'source Ident>> {
        self.original.legacy_first(rule)
    }
    fn native_first(
        &mut self,
        category: Self::Category,
        name: &str,
    ) -> Vec<(String, Option<String>)> {
        self.original
            .native_first(category, name)
            .into_iter()
            .map(|(pattern, guard)| (pattern.to_string(), guard.map(|value| value.to_string())))
            .collect()
    }
    fn atomic(&mut self, rule: &'source GrammarRule) -> AtomicDescriptor<AtomicShape> {
        self.call(format!("atomic:{}", rule.label));
        self.original.atomic(rule)
    }
    fn patterned_first(&mut self, literal: AtomicShape) -> Vec<(String, Option<String>)> {
        self.original
            .patterned_first(literal)
            .into_iter()
            .map(|(pattern, guard)| (pattern.to_string(), guard.map(|value| value.to_string())))
            .collect()
    }
    fn binder_leading(&mut self, rule: &'source GrammarRule) -> Option<String> {
        self.original.binder_leading(rule)
    }
    fn predicate_parts(&mut self, predicate: FirstPredicate<'_>) -> (String, Option<String>) {
        let (pattern, guard) = self.original.predicate_parts(predicate);
        (pattern.to_string(), guard.map(|value| value.to_string()))
    }
}

impl<'source> IdentSummaryContext<'source, Reader> for Observed<'source> {
    fn categories_len(&self) -> usize {
        self.call("ident-summary".into());
        self.original.categories_len()
    }
    fn category_at(&self, index: usize) -> Self::Category {
        self.original.category_at(index)
    }
    fn category_spelling(&self, category: Self::Category) -> String {
        self.original.category_spelling(category)
    }
    fn legacy_len(&self, rule: &'source GrammarRule) -> usize {
        self.original.legacy_len(rule)
    }
    fn legacy_at(
        &self,
        rule: &'source GrammarRule,
        index: usize,
    ) -> Option<FirstLegacyItem<'source, &'source Ident>> {
        self.original.legacy_at(rule, index)
    }
}

impl<'source> PrefixBucketContext<'source, Reader> for Observed<'source> {
    fn infix(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Option<mettail_prattail::binding_power::InfixRuleInfo> {
        self.call(format!("infix:{}", rule.label));
        self.original.infix(rule)
    }
    fn category_names(&mut self) -> Vec<String> {
        self.call("census".into());
        self.original.category_names()
    }
    fn binding_power_table(&mut self) -> mettail_prattail::binding_power::BindingPowerTable {
        self.call("bp".into());
        self.original.binding_power_table()
    }
    fn explicit_prefix_bp(&self, rule: &'source GrammarRule) -> Option<u8> {
        self.original.explicit_prefix_bp(rule)
    }
    fn binder_shape(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Option<super::super::super::binder::BinderShape> {
        self.call(format!("binder:{}", rule.label));
        self.original.binder_shape(rule)
    }
    fn atomic_rows(
        &mut self,
        category: u16,
        rule: u16,
        shape: &AtomicDescriptor<AtomicShape>,
    ) -> Vec<mettail_prattail::wpda_rule_analysis::atomic_prefix::PrefixArmDescriptor<String>> {
        self.call(format!("rows:{rule}"));
        self.original
            .atomic_rows(category, rule, shape)
            .into_iter()
            .map(|row| mettail_prattail::wpda_rule_analysis::atomic_prefix::PrefixArmDescriptor {
                pattern: row.pattern.to_string(),
                extra_guard: row.extra_guard.map(|guard| guard.to_string()),
                rule_idx: row.rule_idx,
                category_src_idx: row.category_src_idx,
            })
            .collect()
    }
    fn nested_guest_openers(&mut self, open: &str) -> Vec<String> {
        self.original.nested_guest_openers(open)
    }
}

#[test]
fn prefix_bucket_shared_two_classification_passes_and_plain_payload() {
    let lang = empty_lang();
    let first = terminal_rule("First", "Expr", "z");
    let second = terminal_rule("Second", "Expr", "a");
    let mut context = Observed::new(&lang);
    let (buckets, order) = derive_prefix_buckets(
        &super::super::super::binder::MacroBinderSyntaxReader,
        &mut context,
        9,
        "Expr",
        &[(4, &first), (7, &second)],
        false,
    );
    assert_eq!(
        *context.calls.borrow(),
        [
            "census",
            "bp",
            "atomic:First",
            "rows:4",
            "binder:First",
            "atomic:Second",
            "rows:7",
            "binder:Second",
            "atomic:First",
            "atomic:Second",
        ]
    );
    assert_eq!(order.len(), 2);
    for (key, rule) in order.iter().zip([4, 7]) {
        let bucket = buckets
            .get(key)
            .expect("insertion roster retains the bucket");
        let [UnifiedDescriptor::Atomic(row)] = bucket.descs.as_slice() else {
            panic!("expected one original atomic descriptor");
        };
        assert_eq!((row.category_src_idx, row.rule_idx), (9, rule));
    }
    assert!(order[0].1.contains("\"z\""));
    assert!(order[1].1.contains("\"a\""));
}

#[test]
fn prefix_bucket_shared_compatibility_queries_remain_lazy() {
    let mut lang = empty_lang();
    for category in ["Expr", "Source"] {
        lang.types.push(LangType {
            name: Ident::new(category, Span::call_site()),
            role: CategoryRole::Object,
            native_type: None,
            collection_kind: None,
        });
    }
    let projection = judgement_rule(
        "Project",
        "Expr",
        &[("value", "Source")],
        vec![SyntaxExpr::Param(Ident::new("value", Span::call_site()))],
    );
    for enabled in [false, true] {
        let mut context = Observed::new(&lang);
        let (buckets, _) = derive_prefix_buckets(
            &super::super::super::binder::MacroBinderSyntaxReader,
            &mut context,
            0,
            "Expr",
            &[(4, &projection)],
            enabled,
        );
        assert_eq!(buckets.is_empty(), enabled);
        let calls = context.calls.borrow();
        assert_eq!(
            calls.iter().filter(|call| *call == "ident-summary").count(),
            usize::from(enabled)
        );
        assert_eq!(calls.iter().filter(|call| *call == "find:Expr").count(), usize::from(enabled));
        assert_eq!(
            calls
                .iter()
                .filter(|call| *call == "atomic:Project")
                .count(),
            2
        );
    }

    // An authored Ident-led structure makes the source non-exclusive. Its
    // original summary must stop before the result's home-variable lookup.
    lang.terms.push(judgement_rule(
        "NamedSource",
        "Source",
        &[("name", "Ident")],
        vec![
            SyntaxExpr::Param(Ident::new("name", Span::call_site())),
            SyntaxExpr::Literal(":".into()),
        ],
    ));
    let mut context = Observed::new(&lang);
    let (buckets, _) = derive_prefix_buckets(
        &super::super::super::binder::MacroBinderSyntaxReader,
        &mut context,
        0,
        "Expr",
        &[(4, &projection)],
        true,
    );
    assert!(!buckets.is_empty());
    let calls = context.calls.borrow();
    assert!(calls.iter().any(|call| call == "ident-summary"));
    assert!(!calls.iter().any(|call| call == "find:Expr"));
}
