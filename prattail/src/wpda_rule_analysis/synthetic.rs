//! Original synthetic-rule scheduling over neutral generated shapes.
//!
//! User rules remain opaque owned payloads. The adapter clones only retained
//! users, normalizes them in grouped order, and resolves source-specific
//! metadata lazily at the original synthesis sites. This module does not
//! normalize grammar syntax or classify native carriers.
//!
//! The phase order, current-list variable scan, delimiter split, and binder
//! loops are relocated from the original macro synthetic-rule builder.
//! Synthetic recipes are materialized at each original insertion site, so a
//! constructor failure cannot be deferred into category-bucket output order.

use super::atomic::{LegacyAtomicItem, LegacyAtomicKind};
use super::InfixSyntaxShape;

/// A source rule with its original category observation.
pub struct UserInput<'a, U> {
    pub category: String,
    pub source: &'a U,
}

/// Direct observations of a declared category, in declaration order.
///
/// Labels, collection elements and binder eligibility are deliberately absent:
/// their original helpers are invoked lazily through the adapter.
pub struct TypeInput<'a, T> {
    pub name: String,
    pub is_data: bool,
    pub has_native: bool,
    pub has_collection: bool,
    pub source: &'a T,
}

/// Existing collection metadata resolved by the source adapter.
pub struct CollectionRecipe<K> {
    pub kind: K,
    pub label: String,
    pub element_category: String,
    pub open: String,
    pub close: String,
    pub separator: String,
}

/// Structural fields of an original synthetic rule.
///
/// The remaining metadata has the original fixed synthetic defaults. Static
/// materialization supplies those defaults without inspecting user syntax.
pub struct SyntheticRule<K> {
    pub label: String,
    pub category: String,
    pub items: Vec<LegacyAtomicItem>,
    pub term_context: Option<Vec<SyntheticParam<K>>>,
    pub syntax_pattern: Option<Vec<InfixSyntaxShape>>,
}

/// Exactly the parameter forms constructed by the original synthesis passes.
pub enum SyntheticParam<K> {
    Simple {
        name: String,
        ty: SyntheticType<K>,
    },
    Abstraction {
        binder: String,
        body: String,
        domain: String,
        codomain: String,
    },
}

/// Exactly the simple-parameter types constructed by synthesis.
pub enum SyntheticType<K> {
    Base(String),
    Collection { kind: K, element: String },
}

/// Source-specific operations retained at their original decision sites.
///
/// Native labels, collection metadata and binder detection reuse existing
/// source helpers. The shared builder neither implements nor guesses them.
pub trait SynthesisAdapter {
    type SourceUser;
    type SourceType;
    type RulePayload;
    type CollectionKind: Clone;

    fn clone_user(&mut self, source: &Self::SourceUser) -> Self::RulePayload;
    fn normalize_user(&mut self, rule: &mut Self::RulePayload);
    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> bool;
    fn materialize_synthetic(
        &mut self,
        rule: SyntheticRule<Self::CollectionKind>,
    ) -> Self::RulePayload;
    fn has_literal_block(&mut self, source: &Self::SourceType) -> bool;
    fn literal_label(&mut self, source: &Self::SourceType) -> String;
    fn collection(&mut self, source: &Self::SourceType) -> CollectionRecipe<Self::CollectionKind>;
    fn var_label(&mut self, source: &Self::SourceType) -> String;
    fn declares_binder(&mut self) -> bool;
}

/// Build the original per-category user-plus-synthetic rule sequence.
///
/// Category lookup retains the original last-duplicate behavior. User payloads
/// need not implement Clone: the adapter owns the original single clone, and
/// callers receive original and synthetic rules in the same backend payload.
/// Materialization is eager at each original push; no final row-wise conversion
/// can reorder constructor validation or execute after its first failure.
pub fn build_per_category_rules<A: SynthesisAdapter>(
    categories: &[String],
    users: &[UserInput<'_, A::SourceUser>],
    types: &[TypeInput<'_, A::SourceType>],
    vector_kind: A::CollectionKind,
    adapter: &mut A,
) -> Vec<Vec<A::RulePayload>> {
    let cat_idx: std::collections::HashMap<&str, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();

    let mut per_cat: Vec<Vec<A::RulePayload>> = (0..categories.len()).map(|_| Vec::new()).collect();

    // 1. User rules in source order; clone only after category admission.
    for rule in users {
        if let Some(&i) = cat_idx.get(rule.category.as_str()) {
            per_cat[i].push(adapter.clone_user(rule.source));
        }
    }

    // 1b. Preserve the original grouped normalization phase and opaque payload.
    for cat_rules in per_cat.iter_mut() {
        for rule in cat_rules.iter_mut() {
            adapter.normalize_user(rule);
        }
    }

    // 2. Synthetic literal-patterned rules, in declared-type order.
    for type_def in types {
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        if type_def.has_collection {
            continue;
        }
        // Preserve the original probe, which is not a synthesis gate.
        let _has_literal_block = adapter.has_literal_block(type_def.source);
        if !type_def.has_native {
            continue;
        }
        let label = adapter.literal_label(type_def.source);
        let synthetic = SyntheticRule {
            label,
            category: cat_name.clone(),
            items: vec![LegacyAtomicItem::NonTerminal {
                ident: cat_name.clone(),
                kind: LegacyAtomicKind::Category,
            }],
            term_context: None,
            syntax_pattern: None,
        };
        per_cat[i].push(adapter.materialize_synthetic(synthetic));
    }

    // Stage 1.3. Synthetic collection literals, after all native literals.
    for type_def in types {
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        if !type_def.has_collection {
            continue;
        }
        let collection = adapter.collection(type_def.source);
        let (kind, label_str) = (collection.kind, collection.label);
        let (open, close, sep) = (collection.open, collection.close, collection.separator);
        let element_cat_str = collection.element_category;
        // Original trim semantics: remove all trailing '(' and split once.
        let trimmed_open = open.trim_end_matches('(').to_string();
        let needs_synth_paren = open != trimmed_open;
        let mut sp = Vec::new();
        sp.push(InfixSyntaxShape::Literal(trimmed_open));
        if needs_synth_paren {
            sp.push(InfixSyntaxShape::Literal("(".to_string()));
        }
        sp.push(InfixSyntaxShape::Sep {
            collection: "elems".to_string(),
            separator: sep,
        });
        sp.push(InfixSyntaxShape::Literal(close));
        let synthetic = SyntheticRule {
            label: label_str,
            category: cat_name.clone(),
            items: Vec::new(),
            term_context: Some(vec![SyntheticParam::Simple {
                name: "elems".to_string(),
                ty: SyntheticType::Collection { kind, element: element_cat_str },
            }]),
            syntax_pattern: Some(sp),
        };
        per_cat[i].push(adapter.materialize_synthetic(synthetic));
    }

    // 3. Missing Var rules, including native and collection categories.
    for type_def in types {
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        // Scan the CURRENT list, including a Var inserted for an earlier
        // duplicate declared type. Preserve the original short-circuit order.
        let has_user_var_rule = per_cat[i]
            .iter()
            .any(|rule| adapter.first_item_is_var(rule));
        if has_user_var_rule {
            continue;
        }
        let label = adapter.var_label(type_def.source);
        let synthetic = SyntheticRule {
            label,
            category: cat_name.clone(),
            items: vec![LegacyAtomicItem::NonTerminal {
                ident: cat_name.clone(),
                kind: LegacyAtomicKind::Var,
            }],
            term_context: None,
            syntax_pattern: None,
        };
        per_cat[i].push(adapter.materialize_synthetic(synthetic));
    }

    // 4. Original binder gate, after all literal/collection/variable passes.
    let has_binders = adapter.declares_binder();
    if has_binders {
        let category_names: Vec<String> = types
            .iter()
            .filter(|category| !category.is_data)
            .map(|category| category.name.clone())
            .collect();
        // Original (home, dom) iteration: Apply followed by MApply per pair.
        for home in &category_names {
            let Some(&home_i) = cat_idx.get(home.as_str()) else {
                continue;
            };
            for dom in &category_names {
                let dom_lower = dom.to_lowercase();
                let dollar_token = format!("${}", dom_lower);
                let ddollar_token = format!("$${}(", dom_lower);
                let apply_label = format!("Apply{}", dom);
                let mapply_label = format!("MApply{}", dom);

                let apply_rule = SyntheticRule {
                    label: apply_label,
                    category: home.clone(),
                    items: Vec::new(),
                    term_context: Some(vec![
                        SyntheticParam::Simple {
                            name: "f".to_string(),
                            ty: SyntheticType::Base(home.clone()),
                        },
                        SyntheticParam::Simple {
                            name: "x".to_string(),
                            ty: SyntheticType::Base(dom.clone()),
                        },
                    ]),
                    syntax_pattern: Some(vec![
                        InfixSyntaxShape::Literal(dollar_token),
                        InfixSyntaxShape::Literal("(".to_string()),
                        InfixSyntaxShape::Param("f".to_string()),
                        InfixSyntaxShape::Literal(",".to_string()),
                        InfixSyntaxShape::Param("x".to_string()),
                        InfixSyntaxShape::Literal(")".to_string()),
                    ]),
                };
                per_cat[home_i].push(adapter.materialize_synthetic(apply_rule));

                let mapply_rule = SyntheticRule {
                    label: mapply_label,
                    category: home.clone(),
                    items: Vec::new(),
                    term_context: Some(vec![
                        SyntheticParam::Simple {
                            name: "f".to_string(),
                            ty: SyntheticType::Base(home.clone()),
                        },
                        SyntheticParam::Simple {
                            name: "xs".to_string(),
                            ty: SyntheticType::Collection {
                                kind: vector_kind.clone(),
                                element: dom.clone(),
                            },
                        },
                    ]),
                    syntax_pattern: Some(vec![
                        InfixSyntaxShape::Literal(ddollar_token),
                        InfixSyntaxShape::Param("f".to_string()),
                        InfixSyntaxShape::Literal(",".to_string()),
                        InfixSyntaxShape::Sep {
                            collection: "xs".to_string(),
                            separator: ",".to_string(),
                        },
                        InfixSyntaxShape::Literal(")".to_string()),
                    ]),
                };
                per_cat[home_i].push(adapter.materialize_synthetic(mapply_rule));
            }
        }

        // 4b. Separate original lambda pass: one Lam<Home> per declared home
        // entry, not one lambda for each (home, domain) pair.
        for home in &category_names {
            let Some(&home_i) = cat_idx.get(home.as_str()) else {
                continue;
            };
            for binder_cat in std::iter::once(home) {
                let lam_label = format!("Lam{}", binder_cat);
                let lam_rule = SyntheticRule {
                    label: lam_label,
                    category: home.clone(),
                    items: Vec::new(),
                    term_context: Some(vec![SyntheticParam::Abstraction {
                        binder: "x".to_string(),
                        body: "p".to_string(),
                        domain: binder_cat.clone(),
                        codomain: home.clone(),
                    }]),
                    syntax_pattern: Some(vec![
                        InfixSyntaxShape::Literal("^".to_string()),
                        InfixSyntaxShape::Param("x".to_string()),
                        InfixSyntaxShape::Literal(".".to_string()),
                        InfixSyntaxShape::Literal("{".to_string()),
                        InfixSyntaxShape::Param("p".to_string()),
                        InfixSyntaxShape::Literal("}".to_string()),
                    ]),
                };
                per_cat[home_i].push(adapter.materialize_synthetic(lam_rule));
            }
        }
    }

    per_cat
}

#[cfg(test)]
mod tests {
    use super::*;

    struct UserSource {
        label: &'static str,
        is_var: bool,
    }

    struct TypeSource {
        name: &'static str,
    }

    // Deliberately not Clone: original payloads must not be cloned by grouping,
    // normalization or by any post-synthesis output conversion.
    struct Payload {
        label: String,
        is_var: bool,
        normalized: bool,
    }

    #[derive(Default)]
    struct TraceAdapter {
        events: Vec<String>,
        fail_at: Option<&'static str>,
        print_events: bool,
    }

    impl TraceAdapter {
        fn record(&mut self, event: String) {
            if self.print_events {
                eprintln!("SYNTHESIS_TRACE:{event}");
            }
            self.events.push(event);
        }
    }

    impl SynthesisAdapter for TraceAdapter {
        type SourceUser = UserSource;
        type SourceType = TypeSource;
        type RulePayload = Payload;
        type CollectionKind = ();

        fn clone_user(&mut self, source: &UserSource) -> Payload {
            self.record(format!("clone:{}", source.label));
            Payload {
                label: source.label.into(),
                is_var: source.is_var,
                normalized: false,
            }
        }

        fn normalize_user(&mut self, rule: &mut Payload) {
            self.record(format!("normalize:{}", rule.label));
            rule.normalized = true;
        }

        fn first_item_is_var(&mut self, rule: &Payload) -> bool {
            self.record(format!("scan:{}", rule.label));
            rule.is_var
        }

        fn materialize_synthetic(&mut self, rule: SyntheticRule<()>) -> Payload {
            self.record(format!("emit:{}:{}", rule.category, rule.label));
            if self.fail_at == Some(rule.label.as_str()) {
                panic!("fixture materialization failure: {}", rule.label);
            }
            Payload {
                label: rule.label,
                is_var: matches!(
                    rule.items.first(),
                    Some(LegacyAtomicItem::NonTerminal { kind: LegacyAtomicKind::Var, .. })
                ),
                normalized: false,
            }
        }

        fn has_literal_block(&mut self, source: &TypeSource) -> bool {
            self.record(format!("probe:{}", source.name));
            false
        }

        fn literal_label(&mut self, source: &TypeSource) -> String {
            self.record(format!("literal-label:{}", source.name));
            format!("{}Lit", source.name)
        }

        fn collection(&mut self, _: &TypeSource) -> CollectionRecipe<()> {
            panic!("these fixtures have no collection category");
        }

        fn var_label(&mut self, source: &TypeSource) -> String {
            self.record(format!("var-label:{}", source.name));
            format!("{}Var", source.name)
        }

        fn declares_binder(&mut self) -> bool {
            self.record("binders".into());
            false
        }
    }

    fn type_input(source: &TypeSource, native: bool) -> TypeInput<'_, TypeSource> {
        TypeInput {
            name: source.name.into(),
            is_data: false,
            has_native: native,
            has_collection: false,
            source,
        }
    }

    fn labels(payloads: &[Payload]) -> Vec<&str> {
        payloads
            .iter()
            .map(|payload| payload.label.as_str())
            .collect()
    }

    #[test]
    fn synthetic_adapter_non_clone_payloads_preserve_grouped_normalization() {
        let source = [
            UserSource { label: "A1", is_var: false },
            UserSource { label: "B1", is_var: false },
            UserSource { label: "A2", is_var: true },
            UserSource { label: "Skipped", is_var: false },
        ];
        let users = [
            UserInput { category: "A".into(), source: &source[0] },
            UserInput { category: "B".into(), source: &source[1] },
            UserInput { category: "A".into(), source: &source[2] },
            UserInput {
                category: "Missing".into(),
                source: &source[3],
            },
        ];
        let mut adapter = TraceAdapter::default();
        let rows =
            build_per_category_rules(&["B".into(), "A".into()], &users, &[], (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["B1"]);
        assert_eq!(labels(&rows[1]), ["A1", "A2"]);
        assert!(rows.iter().flatten().all(|payload| payload.normalized));
        assert!(rows[1][1].is_var);
        assert_eq!(
            adapter.events,
            [
                "clone:A1",
                "clone:B1",
                "clone:A2",
                "normalize:B1",
                "normalize:A1",
                "normalize:A2",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_duplicate_types_scan_current_materialized_vars() {
        let category = TypeSource { name: "A" };
        let types = [type_input(&category, true), type_input(&category, true)];
        let mut adapter = TraceAdapter::default();
        let rows = build_per_category_rules(&["A".into()], &[], &types, (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["ALit", "ALit", "AVar"]);
        assert!(!rows[0][0].is_var);
        assert!(!rows[0][1].is_var);
        assert!(rows[0][2].is_var);
        assert!(rows[0].iter().all(|payload| !payload.normalized));
        assert_eq!(
            adapter.events,
            [
                "probe:A",
                "literal-label:A",
                "emit:A:ALit",
                "probe:A",
                "literal-label:A",
                "emit:A:ALit",
                "scan:ALit",
                "scan:ALit",
                "var-label:A",
                "emit:A:AVar",
                "scan:ALit",
                "scan:ALit",
                "scan:AVar",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_emits_in_declaration_not_bucket_order() {
        let sources = [TypeSource { name: "A" }, TypeSource { name: "B" }];
        let types = [type_input(&sources[0], false), type_input(&sources[1], false)];
        let mut adapter = TraceAdapter::default();
        let rows =
            build_per_category_rules(&["B".into(), "A".into()], &[], &types, (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["BVar"]);
        assert_eq!(labels(&rows[1]), ["AVar"]);
        assert_eq!(
            adapter.events,
            [
                "probe:A",
                "probe:B",
                "var-label:A",
                "emit:A:AVar",
                "var-label:B",
                "emit:B:BVar",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_first_materializer_failure_stops_suffix() {
        const CHILD: &str = "METTAIL_TEST_SYNTHESIS_FIRST_FAILURE_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let sources = [TypeSource { name: "A" }, TypeSource { name: "B" }];
            let types = [type_input(&sources[0], true), type_input(&sources[1], true)];
            let mut adapter = TraceAdapter {
                fail_at: Some("ALit"),
                print_events: true,
                ..TraceAdapter::default()
            };
            let _ =
                build_per_category_rules(&["B".into(), "A".into()], &[], &types, (), &mut adapter);
            panic!("the first materializer must fail");
        }

        // Use a subprocess rather than assuming this compiler profile supports
        // catch_unwind. The expected panic may abort or unwind in the child.
        let output = std::process::Command::new(
            std::env::current_exe().expect("unit-test executable is available"),
        )
        .args([
            "--exact",
            "wpda_rule_analysis::synthetic::tests::synthetic_adapter_first_materializer_failure_stops_suffix",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .output()
        .expect("materialization failure child starts");
        assert!(!output.status.success(), "the child must fail at its first materializer");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("SYNTHESIS_TRACE:probe:A"), "{stderr}");
        assert!(stderr.contains("SYNTHESIS_TRACE:literal-label:A"), "{stderr}");
        assert!(stderr.contains("SYNTHESIS_TRACE:emit:A:ALit"), "{stderr}");
        assert!(stderr.contains("fixture materialization failure: ALit"), "{stderr}");
        for suppressed in ["probe:B", "emit:B:", "var-label:", "binders"] {
            assert!(!stderr.contains(&format!("SYNTHESIS_TRACE:{suppressed}")), "{stderr}");
        }
    }
}
