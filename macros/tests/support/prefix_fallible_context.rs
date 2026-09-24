use super::*;
use mettail_prattail::wpda_rule_analysis::atomic_prefix::PrefixArmDescriptor;
use mettail_prattail::wpda_rule_analysis::prefix::{
    self as first, TryFirstSetContext, TryIdentSummaryContext,
};
use mettail_prattail::wpda_rule_analysis::prefix_bucket::{
    try_derive_prefix_buckets, PrefixBuckets, TryPrefixBucketContext,
};
use std::collections::BTreeSet;

type Event = (&'static str, String);
type Checked<T> = Result<T, usize>;

struct Failing<'source> {
    original: Observed<'source>,
    fail_at: Option<usize>,
    attempts: RefCell<Vec<Event>>,
    completed: RefCell<Vec<usize>>,
}

impl<'source> Failing<'source> {
    fn new(language: &'source LanguageDef, fail_at: Option<usize>) -> Self {
        Self {
            original: Observed::new(language),
            fail_at,
            attempts: RefCell::new(Vec::new()),
            completed: RefCell::new(Vec::new()),
        }
    }

    fn begin(&self, method: &'static str, detail: String) -> Checked<usize> {
        let mut attempts = self.attempts.borrow_mut();
        let ordinal = attempts.len();
        attempts.push((method, detail));
        if self.fail_at == Some(ordinal) {
            Err(ordinal)
        } else {
            Ok(ordinal)
        }
    }
}

macro_rules! forward {
    ($context:ident, $method:literal, $detail:expr, $call:expr) => {{
        let ordinal = $context.begin($method, $detail)?;
        let result = $call;
        $context.completed.borrow_mut().push(ordinal);
        Ok(result)
    }};
}

// Implement only the additive fallible interfaces, never the old traits.
impl<'source> TryFirstSetContext<'source, Reader> for Failing<'source> {
    type Error = usize;
    type Category = &'source LangType;
    type Literal = AtomicShape;
    type Pattern = String;

    fn try_rules_len(&self) -> Checked<usize> {
        forward!(self, "rules_len", String::new(), self.original.rules_len())
    }
    fn try_rule_at(&self, index: usize) -> Checked<&'source GrammarRule> {
        forward!(self, "rule_at", index.to_string(), self.original.rule_at(index))
    }
    fn try_find_category(&mut self, name: &str) -> Checked<Option<Self::Category>> {
        forward!(self, "find_category", name.into(), self.original.find_category(name))
    }
    fn try_is_data(&self, category: Self::Category) -> Checked<bool> {
        forward!(self, "is_data", category.name.to_string(), self.original.is_data(category))
    }
    fn try_collection_open(&self, category: Self::Category) -> Checked<Option<&'source str>> {
        forward!(
            self,
            "collection_open",
            category.name.to_string(),
            self.original.collection_open(category)
        )
    }
    fn try_legacy_first(
        &self,
        rule: &'source GrammarRule,
    ) -> Checked<Option<FirstLegacyItem<'source, &'source Ident>>> {
        forward!(self, "legacy_first", rule.label.to_string(), self.original.legacy_first(rule))
    }
    fn try_native_first(
        &mut self,
        category: Self::Category,
        name: &str,
    ) -> Checked<Vec<(String, Option<String>)>> {
        forward!(
            self,
            "native_first",
            format!("{}:{name}", category.name),
            self.original.native_first(category, name)
        )
    }
    fn try_atomic(&mut self, rule: &'source GrammarRule) -> Checked<AtomicDescriptor<AtomicShape>> {
        forward!(self, "atomic", rule.label.to_string(), self.original.atomic(rule))
    }
    fn try_patterned_first(
        &mut self,
        literal: AtomicShape,
    ) -> Checked<Vec<(String, Option<String>)>> {
        forward!(
            self,
            "patterned_first",
            format!("{literal:?}"),
            self.original.patterned_first(literal)
        )
    }
    fn try_binder_leading(&mut self, rule: &'source GrammarRule) -> Checked<Option<String>> {
        forward!(
            self,
            "binder_leading",
            rule.label.to_string(),
            self.original.binder_leading(rule)
        )
    }
    fn try_predicate_parts(
        &mut self,
        predicate: FirstPredicate<'_>,
    ) -> Checked<(String, Option<String>)> {
        let detail = match &predicate {
            FirstPredicate::Fixed(text) => format!("fixed:{text}"),
            FirstPredicate::Ident => "ident".into(),
            FirstPredicate::Integer => "integer".into(),
            FirstPredicate::Boolean => "boolean".into(),
            FirstPredicate::String => "string".into(),
            FirstPredicate::Float => "float".into(),
            FirstPredicate::CaptureName(text) => format!("capture:{text}"),
            FirstPredicate::GuestOpen(text) => format!("guest:{text}"),
        };
        forward!(self, "predicate_parts", detail, self.original.predicate_parts(predicate))
    }
}

impl<'source> TryIdentSummaryContext<'source, Reader> for Failing<'source> {
    fn try_categories_len(&self) -> Checked<usize> {
        forward!(self, "categories_len", String::new(), self.original.categories_len())
    }
    fn try_category_at(&self, index: usize) -> Checked<Self::Category> {
        forward!(self, "category_at", index.to_string(), self.original.category_at(index))
    }
    fn try_category_spelling(&self, category: Self::Category) -> Checked<String> {
        forward!(
            self,
            "category_spelling",
            category.name.to_string(),
            self.original.category_spelling(category)
        )
    }
    fn try_legacy_len(&self, rule: &'source GrammarRule) -> Checked<usize> {
        forward!(self, "legacy_len", rule.label.to_string(), self.original.legacy_len(rule))
    }
    fn try_legacy_at(
        &self,
        rule: &'source GrammarRule,
        index: usize,
    ) -> Checked<Option<FirstLegacyItem<'source, &'source Ident>>> {
        forward!(
            self,
            "legacy_at",
            format!("{}:{index}", rule.label),
            self.original.legacy_at(rule, index)
        )
    }
}

impl<'source> TryPrefixBucketContext<'source, Reader> for Failing<'source> {
    fn try_infix(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Checked<Option<mettail_prattail::binding_power::InfixRuleInfo>> {
        forward!(self, "infix", rule.label.to_string(), self.original.infix(rule))
    }
    fn try_category_names(&mut self) -> Checked<Vec<String>> {
        forward!(self, "category_names", String::new(), self.original.category_names())
    }
    fn try_binding_power_table(
        &mut self,
    ) -> Checked<mettail_prattail::binding_power::BindingPowerTable> {
        forward!(self, "binding_power_table", String::new(), self.original.binding_power_table())
    }
    fn try_explicit_prefix_bp(&self, rule: &'source GrammarRule) -> Checked<Option<u8>> {
        forward!(
            self,
            "explicit_prefix_bp",
            rule.label.to_string(),
            self.original.explicit_prefix_bp(rule)
        )
    }
    fn try_binder_shape(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Checked<Option<super::super::super::super::binder::BinderShape>> {
        forward!(self, "binder_shape", rule.label.to_string(), self.original.binder_shape(rule))
    }
    fn try_atomic_rows(
        &mut self,
        category: u16,
        rule: u16,
        shape: &AtomicDescriptor<AtomicShape>,
    ) -> Checked<Vec<PrefixArmDescriptor<String>>> {
        forward!(
            self,
            "atomic_rows",
            format!("{category}:{rule}:{shape:?}"),
            self.original.atomic_rows(category, rule, shape)
        )
    }
    fn try_nested_guest_openers(&mut self, open: &str) -> Checked<Vec<String>> {
        forward!(
            self,
            "nested_guest_openers",
            open.into(),
            self.original.nested_guest_openers(open)
        )
    }
}

fn sweep<'source, T>(
    language: &'source LanguageDef,
    coverage: &mut BTreeSet<&'static str>,
    run: impl Fn(&mut Failing<'source>) -> Checked<T>,
) -> T {
    let mut successful = Failing::new(language, None);
    let result = run(&mut successful).expect("all callbacks succeed");
    let trace = successful.attempts.into_inner();
    assert_eq!(successful.completed.into_inner(), (0..trace.len()).collect::<Vec<_>>());
    coverage.extend(trace.iter().map(|event| event.0));
    let original_trace = successful.original.calls.into_inner();
    for ordinal in 0..trace.len() {
        let mut failing = Failing::new(language, Some(ordinal));
        match run(&mut failing) {
            Err(actual) => assert_eq!(actual, ordinal),
            Ok(_) => panic!("callback {ordinal} returned a partial/successful output"),
        }
        assert_eq!(*failing.attempts.borrow(), trace[..=ordinal]);
        assert_eq!(*failing.completed.borrow(), (0..ordinal).collect::<Vec<_>>());
        assert!(original_trace.starts_with(&failing.original.calls.borrow()));
    }
    result
}

fn first_rows(
    rows: Vec<first::FirstToken<String>>,
) -> Vec<(String, Option<String>, Option<String>, bool)> {
    rows.into_iter()
        .map(|row| (row.pattern, row.extra_guard, row.leading_literal, row.is_var_contribution))
        .collect()
}

fn check_first_and_ident(
    language: &LanguageDef,
    category: &str,
    coverage: &mut BTreeSet<&'static str>,
) {
    let reader = super::super::super::super::binder::MacroBinderSyntaxReader;
    let mut original = Observed::new(language);
    let expected = first_rows(first::first_set_of_category(category, &reader, &mut original));
    let actual = sweep(language, coverage, |context| {
        first::try_first_set_of_category(category, &reader, context).map(first_rows)
    });
    assert_eq!(actual, expected);
    let expected = first::category_leading_literals(category, &reader, &original);
    let actual = sweep(language, coverage, |context| {
        first::try_category_leading_literals(category, &reader, context)
    });
    assert_eq!(actual, expected);
    let expected = first::result_has_home_var_reading(category, &reader, &mut original);
    let actual = sweep(language, coverage, |context| {
        first::try_result_has_home_var_reading(category, &reader, context)
    });
    assert_eq!(actual, expected);
    let expected = first::ident_first_categories(&reader, &mut original);
    let actual = sweep(language, coverage, |context| {
        first::try_ident_first_categories(&reader, context)
    });
    assert_eq!(actual, expected);
    let expected = first::source_ident_first_is_var_only(category, &reader, &mut original);
    let actual = sweep(language, coverage, |context| {
        first::try_source_ident_first_is_var_only(category, &reader, context)
    });
    assert_eq!(actual, expected);
}

// Exhaustive test-only representation retains every descriptor field.
fn descriptor_fields(descriptor: &UnifiedDescriptor<String>) -> String {
    match descriptor {
        UnifiedDescriptor::CrossCatLhs { source_src_idx, sigil_leads_result_rule } => {
            format!("CrossCatLhs:{:?}", (source_src_idx, sigil_leads_result_rule))
        },
        UnifiedDescriptor::Atomic(row) => format!(
            "Atomic:{:?}",
            (&row.pattern, &row.extra_guard, row.rule_idx, row.category_src_idx)
        ),
        UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
            format!("BinderPrefix:{:?}", (rule_idx, body_src_idx))
        },
        UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
            format!("LeadingCategory:{:?}", (rule_idx, source_src_idx))
        },
        UnifiedDescriptor::LeadingTokenKindCapture { rule_idx, body_src_idx, kind_name } => {
            format!("LeadingTokenKindCapture:{:?}", (rule_idx, body_src_idx, kind_name))
        },
        UnifiedDescriptor::LeadingGuestBody {
            rule_idx,
            body_src_idx,
            open_kind,
            nested_open_kinds,
            close_kind,
        } => format!(
            "LeadingGuestBody:{:?}",
            (rule_idx, body_src_idx, open_kind, nested_open_kinds, close_kind)
        ),
        UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp } => {
            format!("CrossCatPrefixUnary:{:?}", (rule_idx, source_src_idx, operand_bp))
        },
        UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx } => {
            format!("CrossCatProjection:{:?}", (rule_idx, source_src_idx))
        },
        UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
            format!("NullaryLiteralRun:{rule_idx}")
        },
    }
}

type Key = (String, String);
type BucketFields = (Vec<(Key, String, Option<String>, Vec<String>)>, Vec<Key>);

fn bucket_fields((buckets, order): PrefixBuckets<String>) -> BucketFields {
    (
        buckets
            .into_iter()
            .map(|(key, bucket)| {
                (
                    key,
                    bucket.pat,
                    bucket.extra_guard,
                    bucket.descs.iter().map(descriptor_fields).collect(),
                )
            })
            .collect(),
        order,
    )
}

fn check_buckets<'source>(
    language: &'source LanguageDef,
    indexed: &[(u16, &'source GrammarRule)],
    gate: bool,
    coverage: &mut BTreeSet<&'static str>,
) {
    let reader = super::super::super::super::binder::MacroBinderSyntaxReader;
    let expected = bucket_fields(derive_prefix_buckets(
        &reader,
        &mut Observed::new(language),
        9,
        "Expr",
        indexed,
        gate,
    ));
    let actual = sweep(language, coverage, |context| {
        try_derive_prefix_buckets(&reader, context, 9, "Expr", indexed, gate).map(bucket_fields)
    });
    assert_eq!(actual, expected);
}

#[test]
fn fallible_workers_preserve_outputs_and_stop_at_every_reached_callback() {
    let mut coverage = BTreeSet::new();
    // Existing separate global/indexed roster and duplicate occurrence fixtures.
    let empty = empty_lang();
    let first = terminal_rule("First", "Expr", "z");
    let second = terminal_rule("Second", "Expr", "a");
    check_buckets(&empty, &[(4, &first), (7, &second), (4, &first)], false, &mut coverage);
    check_first_and_ident(&empty, "Missing", &mut coverage);

    // Reuse the native/patterned fixture and existing projection/binder/guest shapes.
    let mut language = lang_with_int_literal();
    for (name, role) in [("Expr", CategoryRole::Data), ("Source", CategoryRole::Object)] {
        language.types.push(LangType {
            name: Ident::new(name, Span::call_site()),
            role,
            native_type: None,
            collection_kind: None,
        });
    }
    let p = |name| SyntaxExpr::Param(Ident::new(name, Span::call_site()));
    let lit = |text: &str| SyntaxExpr::Literal(text.into());
    let mut legacy_projection = category_rule("LegacyProjection", "Expr", "Source");
    legacy_projection.syntax_pattern = Some(vec![p("value")]);
    language.terms = vec![
        category_rule("Literal", "Int", "Int"),
        terminal_rule("SourceAtom", "Source", "x"),
        legacy_projection,
        judgement_rule("Wrapped", "Expr", &[("body", "Expr")], vec![lit("x"), p("body"), lit(")")]),
        terminal_rule("HomeAtom", "Expr", "x"),
        judgement_rule(
            "CrossInfix",
            "Expr",
            &[("left", "Source"), ("right", "Source")],
            vec![p("left"), lit("+"), p("right")],
        ),
        judgement_rule(
            "CrossPrefix",
            "Expr",
            &[("value", "Source")],
            vec![lit("cast"), p("value")],
        ),
        judgement_rule(
            "Guest",
            "Expr",
            &[],
            vec![SyntaxExpr::GuestBody {
                open: Ident::new("Open", Span::call_site()),
                close: Ident::new("Close", Span::call_site()),
                bind: Ident::new("guest", Span::call_site()),
                kind: DelimitedRegionKind::Flt,
            }],
        ),
    ];
    for category in ["Int", "Expr", "Source"] {
        check_first_and_ident(&language, category, &mut coverage);
    }
    let indexed: Vec<_> = language
        .terms
        .iter()
        .enumerate()
        .filter(|(_, rule)| rule.category == "Expr")
        .map(|(index, rule)| (u16::try_from(index).expect("tiny fixture"), rule))
        .collect();
    for gate in [false, true] {
        check_buckets(&language, &indexed, gate, &mut coverage);
    }

    // This is actual reached coverage, not merely a count of implemented methods.
    let expected: BTreeSet<_> = [
        "rules_len",
        "rule_at",
        "find_category",
        "is_data",
        "collection_open",
        "legacy_first",
        "native_first",
        "atomic",
        "patterned_first",
        "binder_leading",
        "predicate_parts",
        "categories_len",
        "category_at",
        "category_spelling",
        "legacy_len",
        "legacy_at",
        "infix",
        "category_names",
        "binding_power_table",
        "explicit_prefix_bp",
        "binder_shape",
        "atomic_rows",
        "nested_guest_openers",
    ]
    .into_iter()
    .collect();
    assert_eq!(coverage, expected, "fixture union must actually reach all 23 callbacks");
}
