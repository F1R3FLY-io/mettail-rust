use super::*;
const NODE_DESCRIPTOR_DOMAIN_V1: &[u8; 8] = b"MTSNODE1";

struct CanonicalCandidate {
    original: u32,
    digest: [u8; 32],
    exact: Vec<u8>,
    node: SemanticNodeV1,
}

/// Canonicalize an image that has already passed the complete structural,
/// category, scope, reachability, authority, and resource admission checks.
///
/// Nodes are processed by structural height. Every child therefore has a
/// canonical identifier before its parent descriptor is formed. Within one
/// height bucket, the complete exact descriptor defines the total order. A
/// BLAKE3 digest is only a fast inequality check before exact interning, in the
/// same style as Dovetail's exact content-key contract.
pub(super) fn canonicalize_well_formed(
    image: &SemanticTermImageV1,
    limits: SemanticTermAdmissionLimits,
) -> Result<SemanticTermImageV1, SemanticTermImageError> {
    let heights = node_heights(image)?;
    let mut order = empty_vec(image.nodes.len())?;
    for index in 0..image.nodes.len() {
        order.push(checked_u32(index)?);
    }
    order.sort_unstable_by_key(|index| heights[*index as usize]);

    let mut remap = empty_vec(image.nodes.len())?;
    remap.resize(image.nodes.len(), None);
    let mut canonical_nodes = empty_vec(image.nodes.len())?;

    let mut cursor = 0usize;
    while cursor < order.len() {
        let height = heights[order[cursor] as usize];
        let mut end = cursor + 1;
        while end < order.len() && heights[order[end] as usize] == height {
            end += 1;
        }

        let mut candidates = empty_vec(end - cursor)?;
        for original in &order[cursor..end] {
            let node = canonicalize_node(&image.nodes[*original as usize], &remap, *original)?;
            let exact = exact_node_descriptor(&node)?;
            let digest = *blake3::hash(&exact).as_bytes();
            candidates.push(CanonicalCandidate { original: *original, digest, exact, node });
        }
        candidates.sort_unstable_by(|left, right| left.exact.cmp(&right.exact));

        let mut previous_key: Option<([u8; 32], Vec<u8>)> = None;
        let mut previous_id = None;
        for candidate in candidates {
            let canonical_id = if previous_key.as_ref().is_some_and(|(digest, exact)| {
                accelerated_exact_equal(digest, exact, &candidate.digest, &candidate.exact)
            }) {
                let id = previous_id.expect("an exact predecessor has a canonical ID");
                debug_assert_eq!(canonical_nodes[id as usize], candidate.node);
                id
            } else {
                let id = checked_u32(canonical_nodes.len())?;
                canonical_nodes.push(candidate.node);
                previous_key = Some((candidate.digest, candidate.exact));
                previous_id = Some(id);
                id
            };
            remap[candidate.original as usize] = Some(canonical_id);
        }
        cursor = end;
    }

    let mut roots = empty_vec(image.roots.len())?;
    for root in &image.roots {
        roots.push(mapped_reference(&remap, *root, *root, 0)?);
    }
    let canonical = SemanticTermImageV1 {
        abi: image.abi,
        signature_fingerprint: image.signature_fingerprint,
        nodes: canonical_nodes,
        roots,
    };
    enforce_limit(encoded_image_len(&canonical)?, limits.max_encoded_bytes, "encoded bytes")?;
    Ok(canonical)
}

fn node_heights(image: &SemanticTermImageV1) -> Result<Vec<u32>, SemanticTermImageError> {
    let mut heights = empty_vec(image.nodes.len())?;
    for (node_index, node) in image.nodes.iter().enumerate() {
        let node_index = checked_u32(node_index)?;
        let mut maximum = None;
        for field in &node.fields {
            for_each_reference(field, &mut |target| {
                let child_height = heights.get(target as usize).copied().ok_or(
                    SemanticTermImageError::Reference { node: node_index, field: 0, target },
                )?;
                maximum =
                    Some(maximum.map_or(child_height, |height: u32| height.max(child_height)));
                Ok(())
            })?;
        }
        heights.push(match maximum {
            None => 0,
            Some(height) => height
                .checked_add(1)
                .ok_or(SemanticTermImageError::LengthOverflow)?,
        });
    }
    Ok(heights)
}

fn for_each_reference(
    field: &SemanticFieldV1,
    visit: &mut impl FnMut(u32) -> Result<(), SemanticTermImageError>,
) -> Result<(), SemanticTermImageError> {
    match field {
        SemanticFieldV1::Child(target) => visit(*target)?,
        SemanticFieldV1::Sequence(targets) => {
            for target in targets {
                visit(*target)?;
            }
        },
        SemanticFieldV1::Collection { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticCollectionEntryV1::Value(target) => visit(*target)?,
                    SemanticCollectionEntryV1::KeyValue { key, value } => {
                        visit(*key)?;
                        visit(*value)?;
                    },
                }
            }
        },
        SemanticFieldV1::PathMap { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticPathMapEntryV1::Key(target) => visit(*target)?,
                    SemanticPathMapEntryV1::KeyValue { key, value } => {
                        visit(*key)?;
                        visit(*value)?;
                    },
                }
            }
        },
        SemanticFieldV1::Optional(Some(target)) => visit(*target)?,
        SemanticFieldV1::OptionalSequence(Some(targets)) => {
            for target in targets {
                visit(*target)?;
            }
        },
        SemanticFieldV1::Scope { body, .. } => visit(*body)?,
        SemanticFieldV1::Optional(None)
        | SemanticFieldV1::OptionalSequence(None)
        | SemanticFieldV1::OptionalTokenText(_)
        | SemanticFieldV1::Variable(_)
        | SemanticFieldV1::Atom(_)
        | SemanticFieldV1::TokenText(_)
        | SemanticFieldV1::Bytes(_)
        | SemanticFieldV1::Opaque(_)
        | SemanticFieldV1::Unit => {},
    }
    Ok(())
}

fn canonicalize_node(
    node: &SemanticNodeV1,
    remap: &[Option<u32>],
    node_index: u32,
) -> Result<SemanticNodeV1, SemanticTermImageError> {
    let mut fields = empty_vec(node.fields.len())?;
    for (field_index, field) in node.fields.iter().enumerate() {
        fields.push(canonicalize_field(field, remap, node_index, checked_u32(field_index)?)?);
    }
    Ok(SemanticNodeV1 {
        operator: node.operator,
        payload: node.payload.clone(),
        fields,
    })
}

fn canonicalize_field(
    field: &SemanticFieldV1,
    remap: &[Option<u32>],
    node: u32,
    field_index: u32,
) -> Result<SemanticFieldV1, SemanticTermImageError> {
    Ok(match field {
        SemanticFieldV1::Child(target) => {
            SemanticFieldV1::Child(mapped_reference(remap, *target, node, field_index)?)
        },
        SemanticFieldV1::Sequence(targets) => {
            let mut mapped = empty_vec(targets.len())?;
            for target in targets {
                mapped.push(mapped_reference(remap, *target, node, field_index)?);
            }
            SemanticFieldV1::Sequence(mapped)
        },
        SemanticFieldV1::Collection { kind, entries } => SemanticFieldV1::Collection {
            kind: *kind,
            entries: canonicalize_collection(*kind, entries, remap, node, field_index)?,
        },
        SemanticFieldV1::PathMap { mode, entries } => SemanticFieldV1::PathMap {
            mode: *mode,
            entries: canonicalize_pathmap(*mode, entries, remap, node, field_index)?,
        },
        SemanticFieldV1::Optional(target) => SemanticFieldV1::Optional(
            target
                .map(|target| mapped_reference(remap, target, node, field_index))
                .transpose()?,
        ),
        SemanticFieldV1::OptionalSequence(targets) => {
            let targets = match targets {
                None => None,
                Some(targets) => {
                    let mut mapped = empty_vec(targets.len())?;
                    for target in targets {
                        mapped.push(mapped_reference(remap, *target, node, field_index)?);
                    }
                    Some(mapped)
                },
            };
            SemanticFieldV1::OptionalSequence(targets)
        },
        SemanticFieldV1::Scope { domain, arity, body } => SemanticFieldV1::Scope {
            domain: *domain,
            arity: *arity,
            body: mapped_reference(remap, *body, node, field_index)?,
        },
        SemanticFieldV1::Variable(variable) => SemanticFieldV1::Variable(variable.clone()),
        SemanticFieldV1::Atom(atom) => SemanticFieldV1::Atom(atom.clone()),
        SemanticFieldV1::TokenText(text) => SemanticFieldV1::TokenText(text.clone()),
        SemanticFieldV1::Bytes(bytes) => SemanticFieldV1::Bytes(bytes.clone()),
        SemanticFieldV1::OptionalTokenText(text) => {
            SemanticFieldV1::OptionalTokenText(text.clone())
        },
        SemanticFieldV1::Opaque(atom) => SemanticFieldV1::Opaque(atom.clone()),
        SemanticFieldV1::Unit => SemanticFieldV1::Unit,
    })
}

fn canonicalize_pathmap(
    mode: PathMapModeV1,
    entries: &[SemanticPathMapEntryV1],
    remap: &[Option<u32>],
    node: u32,
    field: u32,
) -> Result<Vec<SemanticPathMapEntryV1>, SemanticTermImageError> {
    match mode {
        PathMapModeV1::NeutralEmpty => {
            if !entries.is_empty() {
                return Err(SemanticTermImageError::PathMapMode { node, field });
            }
            Ok(Vec::new())
        },
        PathMapModeV1::Set => {
            let mut keys = empty_vec(entries.len())?;
            for entry in entries {
                let SemanticPathMapEntryV1::Key(key) = entry else {
                    return Err(SemanticTermImageError::PathMapMode { node, field });
                };
                keys.push(mapped_reference(remap, *key, node, field)?);
            }
            keys.sort_unstable();
            reject_duplicate_pathmap_keys(&keys, node, field)?;
            let mut output = empty_vec(keys.len())?;
            for key in keys {
                output.push(SemanticPathMapEntryV1::Key(key));
            }
            Ok(output)
        },
        PathMapModeV1::Map => {
            let mut pairs = empty_vec(entries.len())?;
            for entry in entries {
                let SemanticPathMapEntryV1::KeyValue { key, value } = entry else {
                    return Err(SemanticTermImageError::PathMapMode { node, field });
                };
                pairs.push((
                    mapped_reference(remap, *key, node, field)?,
                    mapped_reference(remap, *value, node, field)?,
                ));
            }
            pairs.sort_unstable_by_key(|(key, _)| *key);
            if let Some(pair) = pairs.windows(2).find(|pair| pair[0].0 == pair[1].0) {
                return Err(SemanticTermImageError::DuplicateCollectionKey {
                    node,
                    field,
                    key: pair[0].0,
                });
            }
            let mut output = empty_vec(pairs.len())?;
            for (key, value) in pairs {
                output.push(SemanticPathMapEntryV1::KeyValue { key, value });
            }
            Ok(output)
        },
    }
}

fn reject_duplicate_pathmap_keys(
    keys: &[u32],
    node: u32,
    field: u32,
) -> Result<(), SemanticTermImageError> {
    if let Some(pair) = keys.windows(2).find(|pair| pair[0] == pair[1]) {
        return Err(SemanticTermImageError::DuplicateCollectionKey { node, field, key: pair[0] });
    }
    Ok(())
}

fn canonicalize_collection(
    kind: CollectionKind,
    entries: &[SemanticCollectionEntryV1],
    remap: &[Option<u32>],
    node: u32,
    field: u32,
) -> Result<Vec<SemanticCollectionEntryV1>, SemanticTermImageError> {
    match kind {
        CollectionKind::List => {
            let mut output = empty_vec(entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::Value(target) = entry else {
                    return Err(SemanticTermImageError::CollectionKind { node, field });
                };
                output.push(SemanticCollectionEntryV1::Value(mapped_reference(
                    remap, *target, node, field,
                )?));
            }
            Ok(output)
        },
        CollectionKind::Bag | CollectionKind::Set => {
            let mut values = empty_vec(entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::Value(target) = entry else {
                    return Err(SemanticTermImageError::CollectionKind { node, field });
                };
                values.push(mapped_reference(remap, *target, node, field)?);
            }
            values.sort_unstable();
            if kind == CollectionKind::Set {
                values.dedup();
            }
            let mut output = empty_vec(values.len())?;
            for value in values {
                output.push(SemanticCollectionEntryV1::Value(value));
            }
            Ok(output)
        },
        CollectionKind::Map | CollectionKind::PathMap => {
            let mut pairs = empty_vec(entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::KeyValue { key, value } = entry else {
                    return Err(SemanticTermImageError::CollectionKind { node, field });
                };
                pairs.push((
                    mapped_reference(remap, *key, node, field)?,
                    mapped_reference(remap, *value, node, field)?,
                ));
            }
            pairs.sort_unstable_by_key(|(key, _)| *key);
            if let Some(pair) = pairs.windows(2).find(|pair| pair[0].0 == pair[1].0) {
                return Err(SemanticTermImageError::DuplicateCollectionKey {
                    node,
                    field,
                    key: pair[0].0,
                });
            }
            let mut output = empty_vec(pairs.len())?;
            for (key, value) in pairs {
                output.push(SemanticCollectionEntryV1::KeyValue { key, value });
            }
            Ok(output)
        },
    }
}

fn mapped_reference(
    remap: &[Option<u32>],
    target: u32,
    node: u32,
    field: u32,
) -> Result<u32, SemanticTermImageError> {
    remap
        .get(target as usize)
        .and_then(|mapped| *mapped)
        .ok_or(SemanticTermImageError::Reference { node, field, target })
}

fn exact_node_descriptor(node: &SemanticNodeV1) -> Result<Vec<u8>, SemanticTermImageError> {
    let mut length = NODE_DESCRIPTOR_DOMAIN_V1.len() + 4 + 1 + 4;
    if let Some(payload) = &node.payload {
        checked_add(&mut length, encoded_atom_len(payload)?)?;
    }
    for field in &node.fields {
        checked_add(&mut length, encoded_field_len(field)?)?;
    }
    let mut output = empty_vec(length)?;
    output.extend_from_slice(NODE_DESCRIPTOR_DOMAIN_V1);
    write_u32(&mut output, node.operator.0);
    match &node.payload {
        None => output.push(0),
        Some(payload) => {
            output.push(1);
            encode_atom(payload, &mut output)?;
        },
    }
    write_u32(&mut output, checked_u32(node.fields.len())?);
    for field in &node.fields {
        encode_field(field, &mut output)?;
    }
    debug_assert_eq!(output.len(), length);
    Ok(output)
}

fn accelerated_exact_equal(
    left_digest: &[u8; 32],
    left_exact: &[u8],
    right_digest: &[u8; 32],
    right_exact: &[u8],
) -> bool {
    left_digest == right_digest && left_exact == right_exact
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_collision_falls_back_to_the_complete_exact_descriptor() {
        let collision = [7; 32];
        assert!(!accelerated_exact_equal(&collision, b"left", &collision, b"right"));
        assert!(accelerated_exact_equal(&collision, b"same", &collision, b"same"));
    }
}
