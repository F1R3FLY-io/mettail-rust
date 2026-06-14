use mettail_runtime::{
    AscentResults, Language, RuntimeBackendOutput, RuntimeBackendReport, RuntimeChannelObservation,
    RuntimeObservationValue, Term,
};

pub fn run_default_backend_report(
    language: &dyn Language,
    term: &dyn Term,
    context: &str,
) -> Result<RuntimeBackendReport, String> {
    mettail_runtime::clear_var_cache();
    language.run_default_backend_report(term).map_err(|error| {
        format!(
            "{} failed on {} backend: {}",
            context,
            language.default_runtime_backend(),
            error
        )
    })
}

pub fn expect_ascent_graph(
    report: RuntimeBackendReport,
    context: &str,
) -> Result<AscentResults, String> {
    match report.output {
        RuntimeBackendOutput::Ascent(results) => Ok(results),
        RuntimeBackendOutput::Observations(_) => Err(format!(
            "{} requires an Ascent-shaped rewrite graph; {} returned runtime observations",
            context, report.backend
        )),
        other => Err(format!(
            "{} requires an Ascent-shaped rewrite graph; {} returned {}",
            context,
            report.backend,
            other.kind_name()
        )),
    }
}

pub fn report_contains_expected(report: &RuntimeBackendReport, expected: &str) -> bool {
    match &report.output {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .any(|normal_form| normal_form.display == expected),
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
    match &report.output {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .map(|normal_form| normal_form.display.clone())
            .collect(),
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
    match &report.output {
        RuntimeBackendOutput::Ascent(results) => results
            .normal_forms()
            .iter()
            .map(|normal_form| normal_form.display.clone())
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
        format!("backend={}", report.backend),
        format!("artifact={}", report.artifact),
        format!("output={}", report.output.kind_name()),
    ];

    match &report.output {
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
        RuntimeBackendOutput::Observations(observations) => {
            signature.push(format!("observations={}", observation_summary(observations)));
        },
        _ => {
            signature.push("unsupported_output".to_string());
        },
    }

    signature
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
