//! Equijoin: combine two relations on matching column values.

use super::Row;

/// Equijoin: rows from left and right where left[left_indices[i]] == right[right_indices[i]].
/// Output row layout: [join_keys, non-key_left_cols, non-key_right_cols].
pub fn equijoin(
    left: Vec<Row>,
    right: Vec<Row>,
    left_indices: Vec<usize>,
    right_indices: Vec<usize>,
) -> Vec<Row> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    debug_assert_eq!(left_indices.len(), right_indices.len());

    let mut result = Vec::new();
    for left_row in &left {
        let key: Vec<String> = left_indices.iter().map(|&i| left_row[i].clone()).collect();
        for right_row in &right {
            let matches = right_indices
                .iter()
                .zip(key.iter())
                .all(|(&ri, k)| right_row[ri] == *k);
            if !matches {
                continue;
            }
            let mut out = Vec::with_capacity(
                key.len()
                    + (left_row.len() - left_indices.len())
                    + (right_row.len() - right_indices.len()),
            );
            out.extend(key.clone());
            for (i, v) in left_row.iter().enumerate() {
                if !left_indices.contains(&i) {
                    out.push(v.clone());
                }
            }
            for (i, v) in right_row.iter().enumerate() {
                if !right_indices.contains(&i) {
                    out.push(v.clone());
                }
            }
            result.push(out);
        }
    }
    result
}
