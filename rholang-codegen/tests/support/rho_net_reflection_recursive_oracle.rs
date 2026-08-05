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
            name: ReflectionOracle,
            types { Proc },
            terms {
                Leaf . |- "leaf" : Proc ;
                Wrap . child:Proc |- "wrap(" child ")" : Proc ;
                Pair . left:Proc, right:Proc |- "pair(" left "," right ")" : Proc ;
                PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
            },
            equations {},
            rewrites {},
        "#,
    )
    .expect("reflection oracle definition parses")
}

fn recursive_ground(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Term(PatternTerm::Apply { args, .. }) => args.iter().all(recursive_ground),
        Pattern::Term(PatternTerm::Lambda { body, .. })
        | Pattern::Term(PatternTerm::MultiLambda { body, .. }) => recursive_ground(body),
        _ => false,
    }
}

fn recursive_reflect_binder(
    label: &str,
    binders: &[Ident],
    body: &Pattern,
    vars: &[Ident],
    k: usize,
    fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(fingerprint, label));
    let mut elements = Vec::with_capacity(binders.len() + 3);
    let mut locally_free = tag.locally_free.clone();
    elements.push(tag);
    elements.push(ground_marker_tag_par(fingerprint, recursive_ground(body)));
    for binder in binders {
        let leaf = reflect_bound_var_leaf(binder, fingerprint);
        locally_free = union(locally_free, leaf.locally_free.clone());
        elements.push(leaf);
    }
    binder_env.extend(binders.iter().map(ToString::to_string));
    let body_result = recursive_reflect(body, vars, k, fingerprint, binder_env, def);
    binder_env.truncate(binder_env.len() - binders.len());
    let body = body_result?;
    locally_free = union(locally_free, body.locally_free.clone());
    elements.push(body);
    Ok(new_elist_par(elements, locally_free.clone(), false, None, locally_free, false))
}

#[allow(clippy::too_many_arguments)]
fn recursive_hashbag(
    op: &Ident,
    elements: &[Pattern],
    rest: Option<&Ident>,
    vars: &[Ident],
    k: usize,
    fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: &LanguageDef,
) -> Result<Par, UnsupportedFamily> {
    let channel = ac_soup_channel(fingerprint, &op.to_string());
    let mut soup = Par::default();
    for element in elements {
        let reflected = recursive_reflect(element, vars, k, fingerprint, binder_env, Some(def))?;
        let free = reflected.locally_free.clone();
        soup = soup.append(new_send_par(
            new_gstring_par(channel.clone(), Vec::new(), false),
            vec![reflected],
            false,
            free.clone(),
            false,
            free,
            false,
        ));
    }
    if let Some(rest) = rest {
        let rest = Pattern::Term(PatternTerm::Var(rest.clone()));
        soup = soup.append(recursive_reflect(&rest, vars, k, fingerprint, binder_env, Some(def))?);
    }
    Ok(soup)
}

fn recursive_reflect(
    pattern: &Pattern,
    vars: &[Ident],
    k: usize,
    fingerprint: &str,
    binder_env: &mut Vec<String>,
    def: Option<&LanguageDef>,
) -> Result<Par, UnsupportedFamily> {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => {
            if binder_env.contains(&name.to_string()) {
                return Ok(reflect_bound_var_leaf(name, fingerprint));
            }
            vars.iter()
                .position(|var| var == name)
                .map(|index| new_boundvar_par(rhs_var_index(k, index), Vec::new(), false))
                .ok_or(UnsupportedFamily::DanglingRhsVariable)
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let (Some(def), [Pattern::Collection { coll_type, elements, rest }]) =
                (def, args.as_slice())
            {
                if resolve_collection_kind(def, constructor, coll_type.as_ref())
                    == Some(CollectionType::HashBag)
                {
                    return recursive_hashbag(
                        constructor,
                        elements,
                        rest.as_ref(),
                        vars,
                        k,
                        fingerprint,
                        binder_env,
                        def,
                    );
                }
            }
            let label = constructor.to_string();
            let tag = GPrivateBuilder::new_par_from_string(reflect_tag(fingerprint, &label));
            let mut elements = Vec::with_capacity(args.len() + 2);
            let mut locally_free = tag.locally_free.clone();
            elements.push(tag);
            if is_marked_object_label(&label) {
                elements
                    .push(ground_marker_tag_par(fingerprint, args.iter().all(recursive_ground)));
            }
            for arg in args {
                let child = recursive_reflect(arg, vars, k, fingerprint, binder_env, def)?;
                locally_free = union(locally_free, child.locally_free.clone());
                elements.push(child);
            }
            Ok(new_elist_par(elements, locally_free.clone(), false, None, locally_free, false))
        },
        Pattern::Term(PatternTerm::Lambda { binder, body }) => recursive_reflect_binder(
            LAMBDA_REFLECT_LABEL,
            std::slice::from_ref(binder),
            body,
            vars,
            k,
            fingerprint,
            binder_env,
            def,
        ),
        Pattern::Term(PatternTerm::MultiLambda { binders, body }) => recursive_reflect_binder(
            MULTILAMBDA_REFLECT_LABEL,
            binders,
            body,
            vars,
            k,
            fingerprint,
            binder_env,
            def,
        ),
        Pattern::Term(PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. }) => {
            Err(UnsupportedFamily::Substitution)
        },
        Pattern::Collection { .. } => Err(UnsupportedFamily::CollectionAc),
        Pattern::Map { .. } => Err(UnsupportedFamily::MapAc),
        Pattern::Zip { .. } => Err(UnsupportedFamily::ZipAc),
        Pattern::IndexedVec { .. } => Err(UnsupportedFamily::IndexedVecOrdered),
    }
}

#[test]
fn iterative_reflection_matches_recursive_oracle() {
    let def = fixture_def();
    let vars = vec![ident("x"), ident("rest")];
    let pattern = apply(
        "Pair",
        vec![
            Pattern::Term(PatternTerm::Lambda {
                binder: ident("bound"),
                body: Box::new(apply("Pair", vec![variable("bound"), variable("x")])),
            }),
            apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: None,
                    elements: vec![
                        apply("Wrap", vec![variable("x")]),
                        Pattern::Term(PatternTerm::Lambda {
                            binder: ident("inner"),
                            body: Box::new(variable("inner")),
                        }),
                    ],
                    rest: Some(ident("rest")),
                }],
            ),
        ],
    );
    let actual = reflect_term_par(&pattern, &vars, vars.len(), "oracle-fp", Some(&def));
    let expected =
        recursive_reflect(&pattern, &vars, vars.len(), "oracle-fp", &mut Vec::new(), Some(&def));
    assert_eq!(actual, expected);

    let dangling = variable("missing");
    assert_eq!(
        reflect_term_par(&dangling, &vars, vars.len(), "oracle-fp", Some(&def)),
        recursive_reflect(&dangling, &vars, vars.len(), "oracle-fp", &mut Vec::new(), Some(&def),)
    );
}

#[test]
fn reflection_pda_handles_deep_and_wide_inputs_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("rho-reflection-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 2_000;
            let def = fixture_def();
            let mut nested = variable("x");
            for _ in 0..DEPTH {
                nested = Pattern::Term(PatternTerm::Lambda {
                    binder: ident("x"),
                    body: Box::new(nested),
                });
            }
            let reflected = reflect_term_par(&nested, &[], 0, "deep-fp", Some(&def))
                .expect("deep binder reflection succeeds");
            assert!(!reflected.exprs.is_empty());
            drop(reflected);

            const WIDTH: usize = 5_000;
            let elements = (0..WIDTH).map(|_| apply("Leaf", Vec::new())).collect();
            let bag = apply(
                "PPar",
                vec![Pattern::Collection {
                    coll_type: Some(CollectionType::HashBag),
                    elements,
                    rest: None,
                }],
            );
            let reflected = reflect_term_par(&bag, &[], 0, "wide-fp", Some(&def))
                .expect("wide HashBag reflection succeeds");
            assert_eq!(reflected.sends.len(), WIDTH);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("reflection PDA does not overflow a 256 KiB stack");
}
