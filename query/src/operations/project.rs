//! Project: select columns from each row.

use super::Row;

/// Select specified columns from each row, in order.
pub fn project(input: Vec<Row>, columns: Vec<usize>) -> Vec<Row> {
    input
        .into_iter()
        .map(|row| columns.iter().map(|&idx| row[idx].clone()).collect())
        .collect()
}
