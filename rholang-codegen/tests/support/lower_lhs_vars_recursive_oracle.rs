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

fn recursive_collect(
    pattern: &Pattern,
    vars: &mut Vec<Ident>,
    seen: &mut HashSet<String>,
    bound: &mut Vec<String>,
) -> Result<(), UnsupportedFamily> {
    match pattern {
        Pattern::Term(PatternTerm::Var(ident)) => {
            if bound.contains(&ident.to_string()) {
                return Ok(());
            }
            if seen.insert(ident.to_string()) {
                vars.push(ident.clone());
            }
            Ok(())
        },
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            for arg in args {
                recursive_collect(arg, vars, seen, bound)?;
            }
            Ok(())
        },
        Pattern::Term(PatternTerm::Lambda { binder, body }) => {
            bound.push(binder.to_string());
            let result = recursive_collect(body, vars, seen, bound);
            bound.pop();
            result
        },
        Pattern::Term(PatternTerm::MultiLambda { binders, body }) => {
            bound.extend(binders.iter().map(ToString::to_string));
            let result = recursive_collect(body, vars, seen, bound);
            bound.truncate(bound.len() - binders.len());
            result
        },
        Pattern::Term(PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. }) => {
            Err(UnsupportedFamily::Substitution)
        },
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
        Pattern::IndexedVec { .. } => Err(UnsupportedFamily::IndexedVecOrdered),
    }
}

fn recursive_lower_lhs_vars(pattern: &Pattern) -> Result<Vec<Ident>, UnsupportedFamily> {
    let mut vars = Vec::new();
    recursive_collect(pattern, &mut vars, &mut HashSet::new(), &mut Vec::new())?;
    Ok(vars)
}

#[test]
fn iterative_lhs_variable_collection_matches_recursive_oracle() {
    let fixture = apply(
        "Root",
        vec![
            variable("a"),
            Pattern::Term(PatternTerm::Lambda {
                binder: ident("x"),
                body: Box::new(apply(
                    "Body",
                    vec![
                        variable("x"),
                        variable("b"),
                        Pattern::Term(PatternTerm::Lambda {
                            binder: ident("x"),
                            body: Box::new(apply("Nested", vec![variable("x"), variable("c")])),
                        }),
                    ],
                )),
            }),
            variable("x"),
            variable("a"),
        ],
    );
    let actual = lower_lhs_vars(&fixture).map(|vars| {
        vars.into_iter()
            .map(|var| var.to_string())
            .collect::<Vec<_>>()
    });
    let expected = recursive_lower_lhs_vars(&fixture).map(|vars| {
        vars.into_iter()
            .map(|var| var.to_string())
            .collect::<Vec<_>>()
    });
    assert_eq!(actual, expected);

    let rejected = Pattern::Collection {
        coll_type: Some(CollectionType::HashBag),
        elements: vec![variable("x")],
        rest: None,
    };
    assert_eq!(lower_lhs_vars(&rejected), recursive_lower_lhs_vars(&rejected));
}

#[test]
fn lhs_variable_collection_handles_20k_binders_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("rho-lhs-vars-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut nested = variable("x");
            for _ in 0..DEPTH {
                nested = Pattern::Term(PatternTerm::Lambda {
                    binder: ident("x"),
                    body: Box::new(nested),
                });
            }
            let fixture = apply("Root", vec![nested, variable("free")]);
            let vars = lower_lhs_vars(&fixture)
                .expect("deep binder pattern is supported")
                .into_iter()
                .map(|var| var.to_string())
                .collect::<Vec<_>>();
            assert_eq!(vars, ["free"]);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("LHS-variable PDA does not overflow a 256 KiB stack");
}
