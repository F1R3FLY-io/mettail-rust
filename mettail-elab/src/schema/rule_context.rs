use super::{decode_type_expr, expect_list, require_len, tagged_head};
use crate::canonical::{RhoValue, ValueDecodeError};

#[derive(Debug)]
pub(crate) enum DecodedRuleContext<'a> {
    Ordinary(&'a RhoValue),
    RewriteFamily {
        domains: Vec<&'a RhoValue>,
        result: &'a RhoValue,
    },
}

pub(crate) fn decode_rule_context_type<'a>(
    value: &'a RhoValue,
    path: &str,
    allow_family: bool,
) -> Result<DecodedRuleContext<'a>, ValueDecodeError> {
    let ordinary_error = match decode_type_expr(value, path) {
        Ok(_) => return Ok(DecodedRuleContext::Ordinary(value)),
        Err(error) => error,
    };
    if !allow_family {
        return Err(ordinary_error);
    }
    let mut current = value;
    let mut current_path = path.to_string();
    let mut domains = Vec::new();
    loop {
        let values = expect_list(current, &current_path)?;
        match tagged_head(values, &current_path)? {
            "arrow" => {
                require_len(values, 3, &current_path)?;
                decode_type_expr(&values[1], &format!("{current_path}[1]"))?;
                domains.try_reserve(1).map_err(|_| {
                    ValueDecodeError::new(&current_path, "rewrite-family domain allocation failed")
                })?;
                domains.push(&values[1]);
                current = &values[2];
                current_path.push_str("[2]");
            },
            "rewrite" => {
                require_len(values, 2, &current_path)?;
                decode_type_expr(&values[1], &format!("{current_path}[1]"))?;
                return Ok(DecodedRuleContext::RewriteFamily { domains, result: &values[1] });
            },
            _ => return Err(ordinary_error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::BTreeMap;

    fn text(value: impl Into<String>) -> RhoValue {
        RhoValue::String(value.into())
    }

    fn tagged(tag: &str, values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
        RhoValue::List(std::iter::once(text(tag)).chain(values).collect())
    }

    fn ordinary_type() -> impl Strategy<Value = RhoValue> {
        (0u16..256)
            .prop_map(|index| text(format!("Sort{index}")))
            .prop_recursive(5, 96, 3, |inner| {
                prop_oneof![
                    (prop::sample::select(vec!["multi", "bag", "set", "vec"]), inner.clone())
                        .prop_map(|(tag, value)| tagged(tag, [value])),
                    (prop::sample::select(vec!["arrow", "map", "pathmap"]), inner.clone(), inner,)
                        .prop_map(|(tag, first, second)| tagged(tag, [first, second])),
                ]
            })
    }

    fn assemble(domains: &[RhoValue], result: &RhoValue) -> RhoValue {
        domains
            .iter()
            .rev()
            .fold(tagged("rewrite", [result.clone()]), |tail, domain| {
                tagged("arrow", [domain.clone(), tail])
            })
    }

    proptest! {
        #[test]
        fn ordinary_values_retain_exact_payload(value in ordinary_type(), allow_family in any::<bool>()) {
            let DecodedRuleContext::Ordinary(decoded) =
                decode_rule_context_type(&value, "$.type", allow_family).unwrap()
            else { return Err(TestCaseError::fail("ordinary type became a rewrite family")); };
            prop_assert!(std::ptr::eq(decoded, &value));
            prop_assert_eq!(decoded, &value);
        }

        #[test]
        fn families_preserve_complete_ordered_types(
            domains in prop::collection::vec(ordinary_type(), 0..8),
            result in ordinary_type(),
        ) {
            let value = assemble(&domains, &result);
            let DecodedRuleContext::RewriteFamily { domains: actual, result: ending } =
                decode_rule_context_type(&value, "$.type", true).unwrap()
            else { return Err(TestCaseError::fail("family became an ordinary type")); };
            prop_assert_eq!(actual, domains.iter().collect::<Vec<_>>());
            prop_assert_eq!(ending, &result);
            prop_assert!(decode_rule_context_type(&value, "$.type", false).is_err());
            prop_assert!(decode_type_expr(&value, "$.type").is_err());
        }

        #[test]
        fn families_cannot_appear_inside_ordinary_domains_or_results(
            domain in ordinary_type(),
            result in ordinary_type(),
        ) {
            let invalid_domain = tagged("arrow", [tagged("rewrite", [domain]), tagged("rewrite", [result.clone()])]);
            let invalid_result = tagged("rewrite", [tagged("bag", [tagged("rewrite", [result])])]);
            prop_assert!(decode_rule_context_type(&invalid_domain, "$.type", true).is_err());
            prop_assert!(decode_rule_context_type(&invalid_result, "$.type", true).is_err());
        }
    }

    #[test]
    fn ordinary_names_and_invalid_tag_shapes_keep_existing_admission() {
        for name in ["Rewrite", "R", "rewrite"] {
            let value = text(name);
            assert!(matches!(
                decode_rule_context_type(&value, "$.type", true).unwrap(),
                DecodedRuleContext::Ordinary(_)
            ));
        }
        for value in [
            tagged("rewrite", []),
            tagged("rewrite", [text("P"), text("Q")]),
            tagged("unknown", [text("P")]),
            tagged("arrow", [text("P")]),
            tagged("rewrite", [text("not a category")]),
            tagged("bag", [tagged("rewrite", [text("P")])]),
            RhoValue::Nil,
        ] {
            assert!(decode_rule_context_type(&value, "$.type", true).is_err());
        }
    }

    #[test]
    fn semantic_rules_admit_families_only_in_rewrite_contexts() {
        let family = assemble(&[text("P")], &text("P"));
        let rule = RhoValue::Map(BTreeMap::from([
            ("name".into(), text("Under")),
            (
                "context".into(),
                RhoValue::List(vec![tagged("typed", [text("family"), family.clone()])]),
            ),
            ("left".into(), text("a")),
            ("right".into(), text("b")),
        ]));
        assert!(super::super::validate_rewrite(&rule, "$.rule").is_ok());
        assert!(super::super::validate_equation(&rule, "$.rule").is_err());
        let premise = tagged(
            "intrinsic",
            [RhoValue::Map(BTreeMap::from([
                ("op".into(), text("utf8_slice")),
                ("inputs".into(), RhoValue::List(vec![text("input"), text("start"), text("end")])),
                (
                    "outputs".into(),
                    RhoValue::List(vec![tagged("typed", [text("output"), family])]),
                ),
            ]))],
        );
        assert!(super::super::validate_premise(&premise, "$.premise", true).is_err());
    }

    #[test]
    fn codomain_scan_and_cleanup_use_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let domains = vec![text("P"); 2048];
                let value = assemble(&domains, &text("P"));
                let DecodedRuleContext::RewriteFamily { domains: actual, .. } =
                    decode_rule_context_type(&value, "$.type", true).unwrap()
                else {
                    panic!("family became an ordinary type");
                };
                assert_eq!(actual.len(), domains.len());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
