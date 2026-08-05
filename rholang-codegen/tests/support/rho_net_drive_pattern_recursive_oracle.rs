use super::*;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
}

fn fixture_def() -> LanguageDef {
    syn::parse_str(
        r#"
            name: DrivePatternOracle,
            types { Term },
            terms {
                Leaf . |- "leaf" : Term ;
                N . child:Term |- "n(" child ")" : Term ;
                Pair . left:Term, right:Term |- "pair(" left "," right ")" : Term ;
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
            },
            equations {},
            rewrites {},
        "#,
    )
    .expect("driver pattern oracle definition parses")
}

fn recursive_transcribe(
    pattern: &Pattern,
    def: &LanguageDef,
    fingerprint: &str,
    order: &mut Vec<String>,
) -> Result<Par, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            let name = name.to_string();
            if order.contains(&name) {
                return Err(format!(
                    "repeated LHS variable {name:?} (a non-linear POSITIONAL redex arm is \
                     not driver-supported; MatchCase.guard equalities ride the AC carrier \
                     arms only)"
                ));
            }
            if collides_with_drive_frame(&name) {
                return Err(format!(
                    "LHS variable {name:?} collides with a driver frame name \
                     ({DRIVE_FRAME_NAMES:?} / c#, r#, s#)"
                ));
            }
            let level = order.len();
            order.push(name);
            Ok(pat_free(level))
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let term = def
                .terms
                .iter()
                .find(|term| term.label == label)
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm LHS"))?;
            let tag = if is_binder_term(term) {
                if is_multi_binder_term(term) {
                    return Err(format!(
                        "multi-binder constructor {label:?} has no driver arm this stage"
                    ));
                }
                if args.len() != 1 {
                    return Err(format!(
                        "binder constructor {label:?} applied to {} argument(s) in a redex-arm \
                         LHS (the reflected binder node has exactly one child, its body)",
                        args.len()
                    ));
                }
                LAMBDA_REFLECT_LABEL
            } else {
                label.as_str()
            };
            let children = args
                .iter()
                .map(|arg| recursive_transcribe(arg, def, fingerprint, order))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(pat_tagged(fingerprint, tag, children))
        },
        _ => Err("redex-arm oracle fixture reached unsupported metasyntax".to_string()),
    }
}

fn recursive_rebuild(
    pattern: &Pattern,
    def: &LanguageDef,
    fingerprint: &str,
    env: &Env,
) -> Result<Node, String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => Ok(env.var(&name.to_string())),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let term = def
                .terms
                .iter()
                .find(|term| term.label == label)
                .ok_or_else(|| format!("unknown constructor {label:?} in a redex-arm rebuild"))?;
            let tag = if is_binder_term(term) {
                LAMBDA_REFLECT_LABEL
            } else {
                label.as_str()
            };
            let children = args
                .iter()
                .map(|arg| recursive_rebuild(arg, def, fingerprint, env))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(tagged(fingerprint, tag, children))
        },
        _ => {
            Err("redex-arm rebuild reached a shape the transcription admitted incorrectly"
                .to_string())
        },
    }
}

#[test]
fn iterative_transcription_and_rebuild_match_recursive_oracles() {
    let def = fixture_def();
    let pattern = apply("Pair", vec![apply("Lam", vec![variable("body")]), variable("arg")]);
    let mut actual_order = Vec::new();
    let mut expected_order = Vec::new();
    let actual = transcribe_lhs_pattern(&pattern, &def, "oracle-fp", &mut actual_order);
    let expected = recursive_transcribe(&pattern, &def, "oracle-fp", &mut expected_order);
    assert_eq!(actual_order, expected_order);
    assert_eq!(actual, expected);

    let env = Env::root(&["body", "arg"]);
    let actual = rebuild_from_pattern(&pattern, &def, "oracle-fp", &env)
        .expect("iterative rebuild succeeds");
    let expected =
        recursive_rebuild(&pattern, &def, "oracle-fp", &env).expect("recursive rebuild succeeds");
    assert_eq!(actual.par, expected.par);
    assert_eq!(actual.free, expected.free);

    let repeated = apply("Pair", vec![variable("x"), variable("x")]);
    let mut actual_order = Vec::new();
    let mut expected_order = Vec::new();
    assert_eq!(
        transcribe_lhs_pattern(&repeated, &def, "oracle-fp", &mut actual_order),
        recursive_transcribe(&repeated, &def, "oracle-fp", &mut expected_order)
    );
}

#[test]
fn transcription_and_rebuild_handle_depth_2k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("rho-drive-pattern-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 2_000;
            let def = fixture_def();
            let mut pattern = variable("x");
            for _ in 0..DEPTH {
                pattern = apply("N", vec![pattern]);
            }
            let mut order = Vec::new();
            let transcribed = transcribe_lhs_pattern(&pattern, &def, "deep-fp", &mut order)
                .expect("deep transcription succeeds");
            assert_eq!(order, ["x"]);
            drop(transcribed);

            let env = Env::root(&["x"]);
            let rebuilt = rebuild_from_pattern(&pattern, &def, "deep-fp", &env)
                .expect("deep rebuild succeeds");
            assert_eq!(rebuilt.free, [0]);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("driver pattern PDAs do not overflow a 256 KiB stack");
}
