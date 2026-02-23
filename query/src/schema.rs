//! Query schema: relation name → parameter types.
//!
//! Used for type inference when parsing a single rule and for validating body relations.

use std::collections::HashMap;

/// Schema for queryable relations: each relation name maps to its parameter type names.
#[derive(Debug, Clone, Default)]
pub struct QuerySchema {
    /// relation name → param_types (e.g. "path" → ["Proc", "Proc"])
    pub relations: HashMap<String, Vec<String>>,
}

impl QuerySchema {
    pub fn new() -> Self {
        QuerySchema { relations: HashMap::new() }
    }

    pub fn from_custom_relations(
        custom_relations: &HashMap<String, mettail_runtime::RelationData>,
    ) -> Self {
        let relations = custom_relations
            .iter()
            .map(|(name, data)| (name.clone(), data.param_types.clone()))
            .collect();
        QuerySchema { relations }
    }

    pub fn get(&self, relation: &str) -> Option<&[String]> {
        self.relations.get(relation).map(|v| v.as_slice())
    }

    pub fn contains_relation(&self, name: &str) -> bool {
        self.relations.contains_key(name)
    }
}
