//! Set difference: rows in left that are not in right on the join columns.

use super::Row;

/// Rows from left whose key (left_cols) is not in right's key (right_cols).
/// join_indices: (left_col_idx, right_col_idx) for each key column.
pub fn difference(
    left: Vec<Row>,
    right: Vec<Row>,
    join_indices: Vec<(usize, usize)>,
) -> Vec<Row> {
    if left.is_empty() {
        return Vec::new();
    }
    if right.is_empty() {
        return left;
    }

    let right_keys: std::collections::HashSet<Vec<String>> = right
        .into_iter()
        .map(|row| {
            join_indices
                .iter()
                .map(|(_, ri)| row[*ri].clone())
                .collect()
        })
        .collect();

    left.into_iter()
        .filter(|row| {
            let key: Vec<String> = join_indices
                .iter()
                .map(|(li, _)| row[*li].clone())
                .collect();
            !right_keys.contains(&key)
        })
        .collect()
}
