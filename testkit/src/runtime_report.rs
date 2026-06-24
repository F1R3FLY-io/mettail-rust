use mettail_runtime::{
    AscentResults, Language, RuntimeBackendOutput, RuntimeBackendReport, RuntimeChannelObservation,
    RuntimeDovetailRunReport, RuntimeObservationValue, Term,
};

pub fn run_default_backend_report(
    language: &dyn Language,
    term: &dyn Term,
    context: &str,
) -> Result<RuntimeBackendReport, String> {
    mettail_runtime::clear_var_cache();
    let backend = language
        .selected_default_runtime_backend()
        .map(|backend| backend.to_string())
        .unwrap_or_else(|| "no selected default runtime backend".to_string());
    language
        .run_default_backend_report(term)
        .map_err(|error| format!("{} failed on {} backend: {}", context, backend, error))
}

/// Run the legacy Ascent engine as an explicit reference oracle.
///
/// This helper is for generated regression tests and differential-oracle
/// checks. It deliberately does not consult `Language::default_runtime_backend`
/// and must not be used as production runtime dispatch.
pub fn run_ascent_oracle_report(
    language: &dyn Language,
    term: &dyn Term,
    context: &str,
) -> Result<RuntimeBackendReport, String> {
    mettail_runtime::clear_var_cache();
    language
        .run_ascent(term)
        .map(RuntimeBackendReport::ascent)
        .map_err(|error| format!("{} failed on explicit Ascent oracle: {}", context, error))
}

pub fn expect_ascent_graph(
    report: RuntimeBackendReport,
    context: &str,
) -> Result<AscentResults, String> {
    let backend = report.backend();
    match report.into_output() {
        RuntimeBackendOutput::Ascent(results) => Ok(results),
        RuntimeBackendOutput::Observations(_) => Err(format!(
            "{} requires an Ascent-shaped rewrite graph; {} returned runtime observations",
            context, backend
        )),
        other => Err(format!(
            "{} requires an Ascent-shaped rewrite graph; {} returned {}",
            context,
            backend,
            other.kind_name()
        )),
    }
}

pub fn report_contains_expected(report: &RuntimeBackendReport, expected: &str) -> bool {
    match report.output() {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .any(|normal_form| normal_form.display == expected),
        RuntimeBackendOutput::Dovetail(report) => {
            dovetail_report_summary(report) == expected
                || report
                    .terms
                    .iter()
                    .any(|term| term.op_display == expected || term.key == expected.as_bytes())
        },
        RuntimeBackendOutput::Observations(observations) => {
            observation_summary(observations) == expected
                || observations.iter().any(|observation| {
                    observation
                        .values
                        .iter()
                        .any(|value| observation_value_matches(value, expected))
                })
        },
        _ => false,
    }
}

pub fn report_observed_outputs(report: &RuntimeBackendReport) -> Vec<String> {
    match report.output() {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .map(|normal_form| normal_form.display.clone())
            .collect(),
        RuntimeBackendOutput::Dovetail(report) => {
            let mut outputs = Vec::new();
            outputs.push(dovetail_report_summary(report));
            outputs.extend(
                report
                    .terms
                    .iter()
                    .filter(|term| term.is_root)
                    .map(|term| term.op_display.clone()),
            );
            outputs
        },
        RuntimeBackendOutput::Observations(observations) => {
            let mut outputs = Vec::new();
            let summary = observation_summary(observations);
            if !summary.is_empty() {
                outputs.push(summary);
            }
            for observation in observations {
                for value in &observation.values {
                    push_observation_value_outputs(value, &mut outputs);
                }
            }
            outputs
        },
        _ => Vec::new(),
    }
}

pub fn report_semantic_outputs(report: &RuntimeBackendReport) -> Vec<String> {
    match report.output() {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .map(|normal_form| normal_form.display.clone())
            .collect(),
        RuntimeBackendOutput::Dovetail(report) => report
            .terms
            .iter()
            .filter(|term| term.is_root)
            .map(|term| term.op_display.clone())
            .collect(),
        RuntimeBackendOutput::Observations(observations) => {
            let mut outputs = Vec::new();
            for observation in observations {
                for value in &observation.values {
                    push_observation_value_outputs(value, &mut outputs);
                }
            }
            outputs
        },
        _ => Vec::new(),
    }
}

pub fn report_signature(report: &RuntimeBackendReport) -> Vec<String> {
    let mut signature = vec![
        format!("backend={}", report.backend()),
        format!("artifact={}", report.artifact()),
        format!("output={}", report.output().kind_name()),
    ];

    match report.output() {
        RuntimeBackendOutput::Ascent(results) => {
            let mut normal_forms: Vec<String> = results
                .normal_forms()
                .iter()
                .map(|normal_form| normal_form.display.clone())
                .collect();
            normal_forms.sort();
            signature.push(format!("normal_forms={}", normal_forms.join("|")));
            signature.push(format!("terms={}", results.all_terms.len()));
            signature.push(format!("rewrites={}", results.rewrites.len()));
        },
        RuntimeBackendOutput::Dovetail(report) => {
            signature.push(format!("completeness={}", report.completeness));
            signature.push(format!("roots={}", report.roots.len()));
            signature.push(format!("terms={}", report.terms.len()));
            signature.push(format!("edges={}", report.derivation_edges.len()));
            signature.push(format!("summary={}", dovetail_report_summary(report)));
        },
        RuntimeBackendOutput::Observations(observations) => {
            signature.push(format!("observations={}", observation_summary(observations)));
        },
        _ => {
            signature.push("unsupported_output".to_string());
        },
    }

    signature
}

fn dovetail_report_summary(report: &RuntimeDovetailRunReport) -> String {
    let roots = report
        .root_ordinals
        .iter()
        .filter_map(|ordinal| report.terms.get(*ordinal))
        .map(|term| format!("{}#{}", term.op_display, hex_bytes(&term.key)))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "DovetailRunReport(completeness={}, roots=[{}], terms={}, edges={})",
        report.completeness,
        roots,
        report.terms.len(),
        report.derivation_edges.len()
    )
}

fn observation_summary(observations: &[RuntimeChannelObservation]) -> String {
    observations
        .iter()
        .map(|observation| {
            let values = observation
                .values
                .iter()
                .map(|value| format!("{}", value))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}=[{}]", observation.channel, values)
        })
        .collect::<Vec<_>>()
        .join("; ")
}

fn observation_value_matches(value: &RuntimeObservationValue, expected: &str) -> bool {
    format!("{}", value) == expected || raw_observation_text(value) == Some(expected)
}

fn push_observation_value_outputs(value: &RuntimeObservationValue, outputs: &mut Vec<String>) {
    let formatted = format!("{}", value);
    outputs.push(formatted.clone());
    if let Some(raw) = raw_observation_text(value) {
        if raw != formatted {
            outputs.push(raw.to_string());
        }
    }
}

fn raw_observation_text(value: &RuntimeObservationValue) -> Option<&str> {
    match value {
        RuntimeObservationValue::Text(value) | RuntimeObservationValue::TermDisplay(value) => {
            Some(value.as_str())
        },
        _ => None,
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

#[cfg(test)]
mod tests {
    use mettail_runtime::{
        RuntimeBackendReport, RuntimeDovetailCompleteness, RuntimeDovetailGraphKind,
        RuntimeDovetailRunReport, RuntimeDovetailTermRecord,
    };

    use super::*;

    fn sample_dovetail_report() -> RuntimeBackendReport {
        RuntimeBackendReport::try_dovetail(RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![RuntimeDovetailTermRecord {
                ordinal: 0,
                class_id: 0,
                key: b"root".to_vec(),
                op_display: "normal-form".to_string(),
                weight_display: "1".to_string(),
                is_root: true,
                source_display: None,
            }],
            derivation_edges: Vec::new(),
            rule_firings: Vec::new(),
            completeness: RuntimeDovetailCompleteness::Complete,
            graph_kind: RuntimeDovetailGraphKind::Derivation,
        })
        .expect("sample Dovetail report is shape-valid")
    }

    #[test]
    fn dovetail_reports_have_stable_testkit_outputs() {
        let report = sample_dovetail_report();

        assert!(report_contains_expected(&report, "normal-form"));
        assert!(report_contains_expected(
            &report,
            "DovetailRunReport(completeness=Complete, roots=[normal-form#726f6f74], terms=1, edges=0)"
        ));
        assert_eq!(report_semantic_outputs(&report), vec!["normal-form".to_string()]);
        assert_eq!(
            report_observed_outputs(&report),
            vec![
                "DovetailRunReport(completeness=Complete, roots=[normal-form#726f6f74], terms=1, edges=0)"
                    .to_string(),
                "normal-form".to_string(),
            ]
        );
        assert_eq!(
            report_signature(&report),
            vec![
                "backend=Dovetail".to_string(),
                "artifact=DovetailRunReport".to_string(),
                "output=DovetailRunReport".to_string(),
                "completeness=Complete".to_string(),
                "roots=1".to_string(),
                "terms=1".to_string(),
                "edges=0".to_string(),
                "summary=DovetailRunReport(completeness=Complete, roots=[normal-form#726f6f74], terms=1, edges=0)"
                    .to_string(),
            ]
        );
    }
}
