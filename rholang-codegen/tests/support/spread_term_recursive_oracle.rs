use super::*;

fn recursive_ground_term_is_hereditarily_ground(term: &GroundTerm) -> bool {
    if term.coll_type.is_some() || term.constructor == BOUND_VAR_REFLECT_LABEL {
        return false;
    }
    term.constructor == FREE_VAR_REFLECT_LABEL
        || term
            .children
            .iter()
            .all(recursive_ground_term_is_hereditarily_ground)
}

fn recursive_spread_term_par_at(
    locations: &SubjectLocationIndex<'_>,
    position: SubjectPosition,
    language_fingerprint: &str,
    root_location: &str,
) -> Par {
    let term = locations.term(position);
    let location = locations.channel("loc", language_fingerprint, root_location, position);
    let chain_location = locations.channel("col", language_fingerprint, root_location, position);
    let capture_location = locations.channel("cap", language_fingerprint, root_location, position);
    if matches!(
        term.coll_type,
        Some(CollectionType::HashBag | CollectionType::HashSet | CollectionType::HashMap)
    ) {
        let carrier = reflect_ac_collection_par(term, language_fingerprint);
        let free = carrier.locally_free.clone();
        let chain = new_send_par(
            new_gstring_par(chain_location.clone(), Vec::new(), false),
            vec![carrier.clone()],
            false,
            free.clone(),
            false,
            free.clone(),
            false,
        );
        let capture = new_send_par(
            new_gstring_par(capture_location.clone(), Vec::new(), false),
            vec![carrier],
            false,
            free.clone(),
            false,
            free,
            false,
        );
        return chain.append(capture);
    }

    let head_tag =
        GPrivateBuilder::new_par_from_string(reflect_tag(language_fingerprint, &term.constructor));
    let mut par = new_send_par(
        new_gstring_par(location, Vec::new(), false),
        vec![head_tag.clone()],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    let mut child_chain_channels = Vec::with_capacity(term.children.len());
    for (index, _child) in term.children.iter().enumerate() {
        let child_position = locations
            .child(position, index)
            .expect("indexed child exists");
        let child_chain =
            locations.channel("col", language_fingerprint, root_location, child_position);
        child_chain_channels.push(child_chain.clone());
        par = par.append(recursive_spread_term_par_at(
            locations,
            child_position,
            language_fingerprint,
            root_location,
        ));
    }
    let marker = is_marked_object_label(&term.constructor).then(|| {
        ground_marker_tag_par(
            language_fingerprint,
            recursive_ground_term_is_hereditarily_ground(term),
        )
    });
    par.append(collapse_publish(
        &chain_location,
        &capture_location,
        head_tag,
        marker,
        &child_chain_channels,
    ))
}

#[test]
fn iterative_spread_is_byte_identical_to_recursive_oracle() {
    let subject = GroundTerm::new(
        "Root",
        vec![
            GroundTerm::new(
                FREE_VAR_REFLECT_LABEL,
                vec![GroundTerm::nullary(BOUND_VAR_REFLECT_LABEL)],
            ),
            GroundTerm::collection(
                CollectionType::HashSet,
                "Set",
                vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
            ),
            GroundTerm::new("Pair", vec![GroundTerm::nullary("C"), GroundTerm::nullary("D")]),
        ],
    );
    let locations = SubjectLocationIndex::new(&subject);
    let actual = spread_term_par(&subject, "fixture-fp", "site0");
    let expected =
        recursive_spread_term_par_at(&locations, SubjectPosition::ROOT, "fixture-fp", "site0");
    assert_eq!(actual, expected);
}

#[test]
fn iterative_spread_handles_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("rho-spread-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut subject = GroundTerm::nullary("Leaf");
            for _ in 0..DEPTH {
                subject = GroundTerm::new("N", vec![subject]);
            }
            let spread = spread_term_par(&subject, "deep-fp", "site0");
            assert_eq!(spread.sends.len(), DEPTH + 3);
            assert_eq!(spread.receives.len(), DEPTH);
        })
        .expect("small-stack thread starts")
        .join()
        .expect("spread PDA does not overflow a 256 KiB stack");
}
