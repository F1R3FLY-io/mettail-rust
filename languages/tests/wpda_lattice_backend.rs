use mettail_languages::rhocalc;

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative() {
    let parsed = rhocalc::Name::parse_via_wpda("merge")
        .expect("Name parser should accept identifier text that is a Proc keyword");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_structured_parse() {
    let parsed = rhocalc::Name::parse_structured("merge")
        .expect("structured Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_string_parse() {
    let parsed = rhocalc::Name::parse("merge")
        .expect("string Name parser should share the WPDA lattice backend");
    assert!(matches!(parsed, rhocalc::Name::NVar(_)), "got {:?}", parsed);
}

#[test]
fn rhocalc_name_keyword_text_uses_identifier_alternative_in_all_parse() {
    let parsed = rhocalc::Name::parse_via_wpda_all("merge")
        .expect("all-results Name parser should share the WPDA lattice backend");
    assert!(
        parsed.iter().any(|term| matches!(term, rhocalc::Name::NVar(_))),
        "got {:?}",
        parsed
    );
}
