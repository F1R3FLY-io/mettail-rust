use super::*;

fn encode_recursive(out: &mut Vec<u8>, pattern: &DvPattern<String>) {
    match pattern {
        DvPattern::Var(name) => {
            out.push(0x00);
            push_segment(out, name);
        },
        DvPattern::App { op, args } => {
            out.push(0x01);
            push_segment(out, op);
            push_u32(out, args.len());
            for arg in args {
                encode_recursive(out, arg);
            }
        },
        DvPattern::AcApp { op, fixed, rest } => {
            out.push(0x02);
            push_segment(out, op);
            push_u32(out, fixed.len());
            for arg in fixed {
                encode_recursive(out, arg);
            }
            match rest {
                None => out.push(0x00),
                Some(rest) => {
                    out.push(0x01);
                    push_segment(out, rest);
                },
            }
        },
    }
}

#[test]
fn pattern_encoder_matches_recursive_bytes() {
    let corpus = [
        DvPattern::Var("x".to_owned()),
        DvPattern::App {
            op: "f".to_owned(),
            args: vec![
                DvPattern::Var("x".to_owned()),
                DvPattern::App { op: "g".to_owned(), args: Vec::new() },
            ],
        },
        DvPattern::AcApp {
            op: "PPar".to_owned(),
            fixed: vec![
                DvPattern::Var("head".to_owned()),
                DvPattern::AcApp {
                    op: "Inner".to_owned(),
                    fixed: vec![DvPattern::Var("item".to_owned())],
                    rest: None,
                },
            ],
            rest: Some("tail".to_owned()),
        },
    ];
    for pattern in &corpus {
        let mut actual = Vec::new();
        let mut expected = Vec::new();
        encode_pattern(&mut actual, pattern);
        encode_recursive(&mut expected, pattern);
        assert_eq!(actual, expected);
    }
}

#[test]
fn pattern_encoder_is_stack_safe_at_twenty_thousand_levels() {
    std::thread::Builder::new()
        .name("fragment-pattern-encoder-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = DvPattern::Var("x".to_owned());
            for _ in 0..20_000 {
                pattern = DvPattern::App { op: "f".to_owned(), args: vec![pattern] };
            }
            let mut bytes = Vec::new();
            encode_pattern(&mut bytes, &pattern);
            assert!(!bytes.is_empty());
        })
        .expect("spawn fragment pattern stack-gate thread")
        .join()
        .expect("fragment pattern encoder overflowed or panicked");
}
