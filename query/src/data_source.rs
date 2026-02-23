//! Data source that reads relations from Ascent results.

use mettail_runtime::AscentResults;

/// Data source backed by `AscentResults.custom_relations`.
/// All relations (generated + custom) are in one map after unified extraction.
#[derive(Debug)]
pub struct AscentResultsDataSource<'a> {
    pub results: &'a AscentResults,
}

impl<'a> AscentResultsDataSource<'a> {
    pub fn new(results: &'a AscentResults) -> Self {
        AscentResultsDataSource { results }
    }

    /// Return all rows for a relation as `Vec<Vec<String>>`. Returns empty vec if relation missing.
    pub fn get_relation(&self, name: &str) -> Vec<Vec<String>> {
        self.results
            .custom_relations
            .get(name)
            .map(|data| data.tuples.clone())
            .unwrap_or_default()
    }
}
