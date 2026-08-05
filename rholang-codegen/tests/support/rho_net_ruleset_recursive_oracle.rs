use super::*;

fn ident(name: &str) -> syn::Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
}

fn recursive_convert(
    pattern: &Pattern,
    mode: PatternConversionMode<'_>,
) -> Result<DvPattern<String>, PatternConvertReject> {
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) => Ok(DvPattern::var(id.to_string())),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let label = constructor.to_string();
            let op = match mode {
                PatternConversionMode::Base => label,
                PatternConversionMode::BinderAware(tags) => tags
                    .get(label.as_str())
                    .map(|tag| (*tag).to_string())
                    .unwrap_or(label),
            };
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let fixed = elements
                    .iter()
                    .map(|element| recursive_convert(element, mode))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::ac(op, fixed, rest.as_ref().map(ToString::to_string)))
            } else {
                let children = args
                    .iter()
                    .map(|arg| recursive_convert(arg, mode))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::app(op, children))
            }
        },
        Pattern::Term(PatternTerm::Lambda { body, .. }) => match mode {
            PatternConversionMode::Base => Err(PatternConvertReject::Binder),
            PatternConversionMode::BinderAware(_) => Ok(DvPattern::app(
                LAMBDA_REFLECT_LABEL.to_string(),
                vec![recursive_convert(body, mode)?],
            )),
        },
        Pattern::Term(PatternTerm::MultiLambda { body, .. }) => match mode {
            PatternConversionMode::Base => Err(PatternConvertReject::Binder),
            PatternConversionMode::BinderAware(_) => Ok(DvPattern::app(
                MULTILAMBDA_REFLECT_LABEL.to_string(),
                vec![recursive_convert(body, mode)?],
            )),
        },
        Pattern::Term(PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. }) => {
            Err(PatternConvertReject::Subst)
        },
        Pattern::Collection { .. }
        | Pattern::Map { .. }
        | Pattern::Zip { .. }
        | Pattern::IndexedVec { .. } => Err(PatternConvertReject::CollectionSearch),
    }
}

fn recursive_instantiate(
    pattern: &Pattern,
    sigma: &HashMap<&str, &GroundTerm>,
    rule: &str,
    image: StructuralGroundImage,
) -> Result<GroundTerm, String> {
    let (context, side, noun) = match image {
        StructuralGroundImage::Lhs => ("in-Rho match subject", "LHS", "redex"),
        StructuralGroundImage::Rhs => ("contextual contractum", "RHS", "contractum"),
    };
    match pattern {
        Pattern::Term(PatternTerm::Var(id)) => {
            let name = id.to_string();
            sigma
                .get(name.as_str())
                .map(|ground| (*ground).clone())
                .ok_or_else(|| format!("{context} for {rule}: σ missing {side} variable {name}"))
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { .. }] = args.as_slice() {
                return Err(format!(
                    "{context} for {rule}: AC constructor {constructor} has no positional {noun} image"
                ));
            }
            let children = args
                .iter()
                .map(|arg| recursive_instantiate(arg, sigma, rule, image))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(GroundTerm::new(constructor.to_string(), children))
        },
        _ => Err(format!(
            "{context} for {rule}: non-structural {side} has no ground {noun} image"
        )),
    }
}

fn recursive_collect_sites(
    node: &GroundTerm,
    location: &str,
    roots: &BTreeSet<String>,
    sites: &mut Vec<String>,
) {
    if roots.contains(&node.constructor) {
        sites.push(location.to_string());
    }
    for (index, child) in node.children.iter().enumerate() {
        recursive_collect_sites(
            child,
            &spread_child_location(location, &node.constructor, index),
            roots,
            sites,
        );
    }
}

fn fixture() -> Pattern {
    apply(
        "Bag",
        vec![Pattern::Collection {
            coll_type: None,
            elements: vec![
                apply("Pair", vec![variable("x"), variable("y")]),
                apply("Wrap", vec![variable("z")]),
            ],
            rest: Some(ident("rest")),
        }],
    )
}

#[test]
fn iterative_ruleset_walkers_match_recursive_oracles() {
    let base_fixture = fixture();
    assert_eq!(
        convert_pattern_with_mode(&base_fixture, PatternConversionMode::Base),
        recursive_convert(&base_fixture, PatternConversionMode::Base)
    );

    let binder_fixture = Pattern::Term(PatternTerm::Lambda {
        binder: ident("x"),
        body: Box::new(apply("Lam", vec![apply("Use", vec![variable("x")])])),
    });
    let tags = HashMap::from([("Lam".to_string(), LAMBDA_REFLECT_LABEL)]);
    assert_eq!(
        convert_pattern_with_mode(&binder_fixture, PatternConversionMode::BinderAware(&tags),),
        recursive_convert(&binder_fixture, PatternConversionMode::BinderAware(&tags),)
    );

    let positional = apply("Root", vec![apply("Left", vec![variable("x")]), variable("y")]);
    let x = GroundTerm::new("X", vec![GroundTerm::nullary("Leaf")]);
    let y = GroundTerm::nullary("Y");
    let sigma = HashMap::from([("x", &x), ("y", &y)]);
    for image in [StructuralGroundImage::Lhs, StructuralGroundImage::Rhs] {
        assert_eq!(
            instantiate_structural_ground_pattern(&positional, &sigma, "Rule", image),
            recursive_instantiate(&positional, &sigma, "Rule", image)
        );
    }

    let subject = GroundTerm::new(
        "Root",
        vec![
            GroundTerm::new("Hit", vec![GroundTerm::nullary("Hit")]),
            GroundTerm::nullary("Miss"),
        ],
    );
    let roots = BTreeSet::from(["Hit".to_string()]);
    let mut actual = Vec::new();
    let mut expected = Vec::new();
    collect_redex_sites(&subject, "site0", &roots, &mut actual);
    recursive_collect_sites(&subject, "site0", &roots, &mut expected);
    assert_eq!(actual, expected);
}

#[test]
fn ground_reconstruction_and_location_walk_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("rho-ruleset-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut pattern = variable("x");
            for _ in 0..DEPTH {
                pattern = apply("N", vec![pattern]);
            }
            let leaf = GroundTerm::nullary("Leaf");
            let sigma = HashMap::from([("x", &leaf)]);
            let ground = instantiate_structural_ground_pattern(
                &pattern,
                &sigma,
                "Deep",
                StructuralGroundImage::Rhs,
            )
            .expect("the iterative instantiator handles a deeply nested pattern");

            let roots = BTreeSet::from(["Leaf".to_string()]);
            let mut sites = Vec::new();
            collect_redex_sites(&ground, "site0", &roots, &mut sites);
            assert_eq!(sites.len(), 1);
            assert!(sites[0].ends_with("/N.0"));
        })
        .expect("small-stack thread starts")
        .join()
        .expect("iterative walkers do not overflow a 256 KiB stack");
}
