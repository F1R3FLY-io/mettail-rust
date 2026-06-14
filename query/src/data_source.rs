//! Data sources that read queryable relations from runtime outputs.

use crate::schema::QuerySchema;
use mettail_runtime::{
    AscentResults, RuntimeBackendOutput, RuntimeBackendReport, RuntimeObservationValue,
};

pub trait QueryDataSource {
    /// Return all rows for a relation as `Vec<Vec<String>>`.
    fn get_relation(&self, name: &str) -> Vec<Vec<String>>;
}

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

    pub fn schema(&self) -> QuerySchema {
        QuerySchema::from_custom_relations(&self.results.custom_relations)
    }
}

impl QueryDataSource for AscentResultsDataSource<'_> {
    fn get_relation(&self, name: &str) -> Vec<Vec<String>> {
        self.results
            .custom_relations
            .get(name)
            .map(|data| data.tuples.clone())
            .unwrap_or_default()
    }
}

#[derive(Debug)]
pub struct RuntimeReportDataSource<'a> {
    pub report: &'a RuntimeBackendReport,
}

impl<'a> RuntimeReportDataSource<'a> {
    pub fn new(report: &'a RuntimeBackendReport) -> Self {
        RuntimeReportDataSource { report }
    }

    pub fn schema(&self) -> QuerySchema {
        let mut relations = vec![(
            "runtime_backend".to_string(),
            vec!["RuntimeBackend".to_string(), "RuntimeBackendArtifact".to_string()],
        )];

        match self.report.output() {
            RuntimeBackendOutput::Ascent(results) => {
                relations.extend(
                    results
                        .custom_relations
                        .iter()
                        .map(|(name, data)| (name.clone(), data.param_types.clone())),
                );
            },
            RuntimeBackendOutput::Dovetail(_) => {
                relations.extend([
                    (
                        "dovetail_report".to_string(),
                        vec![
                            "Completeness".to_string(),
                            "RootCount".to_string(),
                            "TermCount".to_string(),
                            "EdgeCount".to_string(),
                        ],
                    ),
                    (
                        "dovetail_root".to_string(),
                        vec![
                            "Ordinal".to_string(),
                            "KeyHex".to_string(),
                            "OpDisplay".to_string(),
                            "WeightDisplay".to_string(),
                        ],
                    ),
                    (
                        "dovetail_term".to_string(),
                        vec![
                            "Ordinal".to_string(),
                            "ClassId".to_string(),
                            "KeyHex".to_string(),
                            "OpDisplay".to_string(),
                            "WeightDisplay".to_string(),
                            "IsRoot".to_string(),
                        ],
                    ),
                    (
                        "dovetail_edge".to_string(),
                        vec![
                            "ParentKeyHex".to_string(),
                            "ChildKeyHex".to_string(),
                            "ChildIndex".to_string(),
                        ],
                    ),
                ]);
            },
            RuntimeBackendOutput::Observations(_) => {
                relations.extend([
                    (
                        "runtime_observation_channel".to_string(),
                        vec!["Channel".to_string(), "Count".to_string()],
                    ),
                    (
                        "runtime_observation".to_string(),
                        vec!["Channel".to_string(), "Value".to_string()],
                    ),
                    (
                        "runtime_observation_value".to_string(),
                        vec!["Channel".to_string(), "Index".to_string(), "Value".to_string()],
                    ),
                ]);
            },
            _ => {},
        }

        QuerySchema::from_relation_types(relations)
    }

    fn metadata_relation(&self, name: &str) -> Option<Vec<Vec<String>>> {
        match name {
            "runtime_backend" => Some(vec![vec![
                self.report.backend().to_string(),
                self.report.artifact().to_string(),
            ]]),
            _ => None,
        }
    }
}

impl QueryDataSource for RuntimeReportDataSource<'_> {
    fn get_relation(&self, name: &str) -> Vec<Vec<String>> {
        if let Some(rows) = self.metadata_relation(name) {
            return rows;
        }

        match self.report.output() {
            RuntimeBackendOutput::Ascent(results) => {
                AscentResultsDataSource::new(results).get_relation(name)
            },
            RuntimeBackendOutput::Dovetail(report) => match name {
                "dovetail_report" => vec![vec![
                    report.completeness.to_string(),
                    report.roots.len().to_string(),
                    report.terms.len().to_string(),
                    report.derivation_edges.len().to_string(),
                ]],
                "dovetail_root" => report
                    .root_ordinals
                    .iter()
                    .filter_map(|ordinal| report.terms.get(*ordinal as usize))
                    .map(|term| {
                        vec![
                            term.ordinal.to_string(),
                            hex_bytes(&term.key),
                            term.op_display.clone(),
                            term.weight_display.clone(),
                        ]
                    })
                    .collect(),
                "dovetail_term" => report
                    .terms
                    .iter()
                    .map(|term| {
                        vec![
                            term.ordinal.to_string(),
                            term.class_id.to_string(),
                            hex_bytes(&term.key),
                            term.op_display.clone(),
                            term.weight_display.clone(),
                            term.is_root.to_string(),
                        ]
                    })
                    .collect(),
                "dovetail_edge" => report
                    .derivation_edges
                    .iter()
                    .map(|edge| {
                        vec![
                            hex_bytes(&edge.parent_key),
                            hex_bytes(&edge.child_key),
                            edge.child_index.to_string(),
                        ]
                    })
                    .collect(),
                _ => Vec::new(),
            },
            RuntimeBackendOutput::Observations(observations) => match name {
                "runtime_observation_channel" => observations
                    .iter()
                    .map(|observation| {
                        vec![observation.channel.clone(), observation.observed_count().to_string()]
                    })
                    .collect(),
                "runtime_observation" => observations
                    .iter()
                    .flat_map(|observation| {
                        observation.values.iter().map(|value| {
                            vec![observation.channel.clone(), observation_value_text(value)]
                        })
                    })
                    .collect(),
                "runtime_observation_value" => observations
                    .iter()
                    .flat_map(|observation| {
                        observation.values.iter().enumerate().map(|(index, value)| {
                            vec![
                                observation.channel.clone(),
                                index.to_string(),
                                observation_value_text(value),
                            ]
                        })
                    })
                    .collect(),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }
}

fn observation_value_text(value: &RuntimeObservationValue) -> String {
    match value {
        RuntimeObservationValue::Text(value) | RuntimeObservationValue::TermDisplay(value) => {
            value.clone()
        },
        _ => format!("{}", value),
    }
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}
