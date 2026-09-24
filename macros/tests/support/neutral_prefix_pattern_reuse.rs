//! Constructor correspondence against the original macro quotation callbacks.
//! Only equality partitions and Ident observations are compared; neutral key
//! ordering is not asserted to reproduce Rust-token lexical ordering.

use super::*;
use mettail_prattail::wpda_rule_analysis::native_first::{
    NativeFirstConstructors, NativePatternSite,
};
use mettail_prattail::wpda_rule_analysis::prefix::FirstPredicate;
use mettail_prattail::wpda_rule_analysis::prefix_pattern::{
    neutral_predicate_parts, NeutralNativeFirstConstructors, NeutralPattern, NeutralPatternKey,
    PrefixPatternObservation,
};

struct Row {
    site: String,
    original: (TokenStream, Option<TokenStream>),
    neutral: (NeutralPattern, Option<NeutralPattern>),
}

fn predicate_row<'text>(
    site: impl Into<String>,
    predicate: impl Fn() -> FirstPredicate<'text>,
) -> Row {
    Row {
        site: site.into(),
        original: first_predicate_parts(predicate()),
        neutral: neutral_predicate_parts(predicate()),
    }
}

fn original_key(row: &Row) -> (String, String) {
    (
        row.original.0.to_string(),
        row.original
            .1
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_default(),
    )
}

fn neutral_key(row: &Row) -> (NeutralPatternKey, NeutralPatternKey) {
    (
        row.neutral.0.key(),
        row.neutral
            .1
            .as_ref()
            .map(PrefixPatternObservation::key)
            .unwrap_or_default(),
    )
}

fn rows() -> Vec<Row> {
    let mut rows = vec![
        predicate_row("predicate Ident", || FirstPredicate::Ident),
        predicate_row("predicate Integer", || FirstPredicate::Integer),
        predicate_row("predicate Boolean", || FirstPredicate::Boolean),
        predicate_row("predicate String", || FirstPredicate::String),
        predicate_row("predicate Float", || FirstPredicate::Float),
    ];
    // Include characters that Rust quotation must escape, Unicode and texts
    // that distinguish the original literal substring test from token meaning.
    let texts = [
        "",
        "x",
        "Ident",
        "prefixIdentSuffix",
        "ident",
        "Id\0ent",
        "\"Ident\"",
        "\\Ident",
        "\\u{49}dent",
        "line\nIdent\r\t",
        "λ日本語🙂",
        "r#Ident",
        "|",
        "\\\"\0",
        "\u{2028}Ident\u{2029}",
    ];
    for text in texts {
        rows.push(predicate_row(format!("fixed {text:?}"), || FirstPredicate::Fixed(text)));
        rows.push(predicate_row(format!("capture {text:?}"), || FirstPredicate::CaptureName(text)));
        rows.push(predicate_row(format!("guest {text:?}"), || FirstPredicate::GuestOpen(text)));
    }
    let sites = [
        NativePatternSite::IntegerTyped,
        NativePatternSite::CustomTyped,
        NativePatternSite::RationalTyped,
        NativePatternSite::FixedPointTyped,
        NativePatternSite::FloatBare,
        NativePatternSite::BooleanAlternative,
        NativePatternSite::StringBare,
        NativePatternSite::IntegerBare,
    ];
    for site in sites {
        rows.push(Row {
            site: format!("native {site:?} without guard"),
            original: (MacroNativeFirstConstructors.pattern(site), None),
            neutral: (NeutralNativeFirstConstructors.pattern(site), None),
        });
        for text in texts {
            rows.push(Row {
                site: format!("native {site:?} category {text:?}"),
                original: (
                    MacroNativeFirstConstructors.pattern(site),
                    Some(MacroNativeFirstConstructors.category_guard(text)),
                ),
                neutral: (
                    NeutralNativeFirstConstructors.pattern(site),
                    Some(NeutralNativeFirstConstructors.category_guard(text)),
                ),
            });
        }
    }
    rows.push(Row {
        site: "Ident with present empty guard".into(),
        original: (first_predicate_parts(FirstPredicate::Ident).0, Some(TokenStream::new())),
        neutral: (
            neutral_predicate_parts(FirstPredicate::Ident).0,
            Some(NeutralPattern::default()),
        ),
    });
    rows
}

#[test]
fn neutral_constructor_keys_preserve_complete_original_equality_partition() {
    let rows = rows();
    let original: Vec<_> = rows.iter().map(original_key).collect();
    let neutral: Vec<_> = rows.iter().map(neutral_key).collect();
    for (left, left_row) in rows.iter().enumerate() {
        for (right, right_row) in rows.iter().enumerate() {
            assert_eq!(
                original[left] == original[right],
                neutral[left] == neutral[right],
                "pair-key equality changed between {} and {}",
                left_row.site,
                right_row.site,
            );
        }
    }
}

#[test]
fn neutral_individual_observations_match_original_quotation() {
    let rows = rows();
    let mut observations = Vec::new();
    for row in &rows {
        observations.push((row.site.as_str(), row.original.0.to_string(), &row.neutral.0));
        match (&row.original.1, &row.neutral.1) {
            (Some(original), Some(neutral)) => {
                observations.push((row.site.as_str(), original.to_string(), neutral));
            },
            (None, None) => {},
            _ => panic!("constructor changed guard presence at {}", row.site),
        }
    }
    for (site, original, neutral) in &observations {
        assert_eq!(
            neutral.mentions_ident(),
            original.contains("Ident"),
            "Ident observation at {site}"
        );
        for (other_site, other_original, other_neutral) in &observations {
            assert_eq!(
                original == other_original,
                neutral.key() == other_neutral.key(),
                "individual key equality changed between {site} and {other_site}",
            );
        }
    }
}

#[test]
fn equivalent_native_sites_share_keys_but_guest_binding_shape_stays_distinct() {
    for (predicate, native) in [
        (FirstPredicate::Integer, NativePatternSite::IntegerBare),
        (FirstPredicate::Boolean, NativePatternSite::BooleanAlternative),
        (FirstPredicate::String, NativePatternSite::StringBare),
        (FirstPredicate::Float, NativePatternSite::FloatBare),
    ] {
        assert_eq!(
            neutral_predicate_parts(predicate).0.key(),
            NeutralNativeFirstConstructors.pattern(native).key()
        );
    }
    let guest = predicate_row("guest", || FirstPredicate::GuestOpen("Same"));
    let native = Row {
        site: "typed Custom".into(),
        original: (
            MacroNativeFirstConstructors.pattern(NativePatternSite::CustomTyped),
            Some(MacroNativeFirstConstructors.category_guard("Same")),
        ),
        neutral: (
            NeutralNativeFirstConstructors.pattern(NativePatternSite::CustomTyped),
            Some(NeutralNativeFirstConstructors.category_guard("Same")),
        ),
    };
    assert_ne!(original_key(&guest), original_key(&native));
    assert_ne!(neutral_key(&guest), neutral_key(&native));
}

#[test]
fn empty_guard_key_collision_preserves_guard_sensitive_ident_observation() {
    let absent = predicate_row("absent guard", || FirstPredicate::Ident);
    let present = Row {
        site: "empty guard".into(),
        original: (absent.original.0.clone(), Some(TokenStream::new())),
        neutral: (absent.neutral.0.clone(), Some(NeutralPattern::default())),
    };
    assert_eq!(original_key(&absent), original_key(&present));
    assert_eq!(neutral_key(&absent), neutral_key(&present));
    // The original summary tests guard absence BEFORE examining the pattern.
    assert!(absent.original.1.is_none() && absent.original.0.to_string().contains("Ident"));
    assert!(absent.neutral.1.is_none() && absent.neutral.0.mentions_ident());
    assert!(!(present.original.1.is_none() && present.original.0.to_string().contains("Ident")));
    assert!(!(present.neutral.1.is_none() && present.neutral.0.mentions_ident()));
}
