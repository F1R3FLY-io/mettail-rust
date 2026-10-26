use proptest::prelude::*;

mettail_macros::language! {
    name: ModalFragmentEntry,
    options { emit_tests: false, emit_simulator: false, emit_blockly: false },
    types { noadmit Document data Piece data ClassPiece data Word },
    tokens {
        LineComment = r"//[^\n]*" -> COMMENTS;
        RegionOpen = r"@\{" push(body);
        WordsOpen = "@<" push(words);
        mode words {
            WordsClose = ">" pop;
            WordToken = "[a-z]+";
        }
        raw mode body {
            RegionClose = r"\}" pop;
            ClassOpen = r"\[" push(class_body);
            BodyText = r"[^\[\]}]+";
        }
        raw mode class_body {
            ClassClose = r"\]" pop;
            ClassText = r"[^\]]+";
        }
    },
    terms {
        DocumentBody . pieces:Vec(Piece)
            |- open@RegionOpen pieces.*sep("") close@RegionClose : Document;
        Text . |- text@BodyText : Piece;
        Class . pieces:Vec(ClassPiece)
            |- open@ClassOpen pieces.*sep("") close@ClassClose : Piece;
        Characters . |- text@ClassText : ClassPiece;
        Words . items:Vec(Word)
            |- open@WordsOpen items.*sep("") close@WordsClose : Document;
        WordText . |- text@WordToken : Word;
    },
    equations {},
    rewrites {},
}

#[test]
fn entry_mode_does_not_change_default_token_admission() {
    assert!(Piece::parse("\0").is_err());
    assert!(ClassPiece::parse("\0").is_err());
    assert!(Piece::parse_via_wpda_in_lexer_mode("\0", Some("missing")).is_err());
    for source in ["}", "[", "[a", "a}"] {
        assert!(Piece::parse_via_wpda_in_lexer_mode(source, Some("body")).is_err());
        assert!(Piece::parse_via_wpda_all_with_weights_in_lexer_mode(source, Some("body")).is_err());
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn ordinary_mode_keeps_collection_boundaries_and_declared_layout(
        words in proptest::collection::vec("[a-z]{1,6}", 2..8),
    ) {
        let source = format!("@< {} >", words.join("  "));
        let parsed = Document::parse(&source).expect("ordinary collection");
        prop_assert_eq!(&parsed.to_string(), &source);
        let Document::Words(_, items, _) = &parsed else {
            return Err(TestCaseError::fail("ordinary collection lost its constructor"));
        };
        let values: Vec<_> = items.iter().map(|Word::WordText(text)| text).collect();
        prop_assert_eq!(values, words.iter().collect::<Vec<_>>());
        let (readings, weights) = Document::parse_via_wpda_all_with_weights_in_lexer_mode(&source, None)
            .expect("ordinary collection forest");
        prop_assert!(readings.contains(&parsed));
        prop_assert_eq!(readings.len(), weights.len());
    }

    #[test]
    fn fragment_entry_preserves_raw_text_and_nested_mode_boundaries(
        parts in proptest::collection::vec(
            proptest::sample::select(vec!["a", "z", " ", "\t", "\n", "\0", "λ", "中"]), 1..16,
        ),
    ) {
        let text = parts.concat();
        let expected = Piece::Text(text.clone());
        prop_assert_eq!(Piece::parse_via_wpda_in_lexer_mode(&text, Some("body")).expect("body"), expected.clone());
        let (values, weights) = Piece::parse_via_wpda_all_with_weights_in_lexer_mode(&text, Some("body"))
            .expect("all body readings");
        prop_assert_eq!(values, vec![expected]);
        prop_assert_eq!(weights.len(), 1);
        prop_assert_eq!(ClassPiece::parse_via_wpda_in_lexer_mode(&text, Some("class_body")).expect("class"), ClassPiece::Characters(text.clone()));
        let nested = format!("[{text}]");
        let value = Piece::parse_via_wpda_in_lexer_mode(&nested, Some("body")).expect("nested mode");
        prop_assert_eq!(value.to_string(), nested);
        let whole = format!("@{{{text}[{text}]{text}}}");
        for tokens in [lex(&whole).expect("linear tokens"), lex_with_streams(&whole).expect("retained streams").tokens] {
            let raw_texts: Vec<_> = tokens.iter()
                .filter(|(token, _)| matches!(token_to_kind(token), mettail_prattail::automata::TokenKind::Custom(name) if name == "BodyText"))
                .map(|(_, range)| &whole[range.start.byte_offset..range.end.byte_offset])
                .collect();
            prop_assert_eq!(raw_texts, vec![text.as_str(), text.as_str()]);
        }
        let value = Document::parse(&whole).expect("whole source");
        prop_assert_eq!(&value.to_string(), &whole);
        let value = Document::parse_via_wpda_in_lexer_mode(&whole, None).expect("default context");
        prop_assert_eq!(&value.to_string(), &whole);
    }
}
