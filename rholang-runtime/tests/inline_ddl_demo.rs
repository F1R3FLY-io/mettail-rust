#![cfg(feature = "rholang-runtime")]

use mettail_grammar_core::{
    STRUCTURAL_ADMISSION_WORK_UNITS, STRUCTURAL_THEOREM_CHECKER_ABI_V1,
    STRUCTURAL_THEOREM_LIMIT_PROFILE_V1,
};
use mettail_languages::rholang::Proc;
use mettail_rholang_runtime::{
    lower_rholang_proc, run_normalized_par_with_language_runtime_and_read_par_channels,
    EmptyRegistrySnapshot, LanguageInstallPolicy, LanguageInstallService, RholangLanguageRuntime,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{KeyValuePair, Par};
use std::collections::BTreeMap;
use std::sync::Arc;

const APPLICATION: &str = include_str!("../../demos/mettail-inline-ddl/inline-ddl.rho");

fn exact_expr(value: &Par) -> Option<&ExprInstance> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.matches.is_empty()
        || !value.unforgeables.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
    {
        return None;
    }
    let [expr] = value.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

fn exact_list(value: &Par) -> Option<&[Par]> {
    let ExprInstance::EListBody(list) = exact_expr(value)? else {
        return None;
    };
    list.remainder.is_none().then_some(list.ps.as_slice())
}

fn exact_map(value: &Par) -> Option<&[KeyValuePair]> {
    let ExprInstance::EMapBody(map) = exact_expr(value)? else {
        return None;
    };
    map.remainder.is_none().then_some(map.kvs.as_slice())
}

fn exact_string(value: &Par) -> Option<&str> {
    let ExprInstance::GString(value) = exact_expr(value)? else {
        return None;
    };
    Some(value)
}

fn exact_bytes(value: &Par) -> Option<&[u8]> {
    let ExprInstance::GByteArray(value) = exact_expr(value)? else {
        return None;
    };
    Some(value)
}

fn exact_int(value: &Par) -> Option<i64> {
    let ExprInstance::GInt(value) = exact_expr(value)? else {
        return None;
    };
    Some(*value)
}

fn map_entry<'a>(value: &'a Par, key: &str) -> Option<&'a Par> {
    exact_map(value)?.iter().find_map(|pair| {
        (pair.key.as_ref().and_then(exact_string) == Some(key))
            .then(|| pair.value.as_ref())
            .flatten()
    })
}

fn parse_status(response: &Par) -> Option<&str> {
    let result = map_entry(response, "ok")?;
    map_entry(result, "status").and_then(exact_string)
}

fn error_code(response: &Par) -> Option<&str> {
    let error = map_entry(response, "error")?;
    map_entry(error, "code").and_then(exact_string)
}

#[derive(Debug, PartialEq, Eq)]
struct ProofIdentity {
    language: Vec<u8>,
    category: u32,
    term: Vec<u8>,
    theorem: Vec<u8>,
    evidence_hash: Vec<u8>,
}

fn framed_hash_field(hasher: &mut blake3::Hasher, value: &[u8]) {
    hasher.update(&(value.len() as u64).to_be_bytes());
    hasher.update(value);
}

fn assert_bounded_structural_proof(proof: &Par) -> ProofIdentity {
    let language = exact_bytes(map_entry(proof, "language").expect("proof language field"))
        .expect("proof language is bytes");
    let category = exact_int(map_entry(proof, "category").expect("proof category field"))
        .and_then(|value| u32::try_from(value).ok())
        .expect("proof category is a nonnegative u32");
    let term = exact_bytes(map_entry(proof, "term").expect("proof term field"))
        .expect("proof term is bytes");
    let theorem = exact_bytes(map_entry(proof, "theorem").expect("proof theorem field"))
        .expect("proof theorem is bytes");
    let checker = exact_string(map_entry(proof, "checker").expect("proof checker field"))
        .expect("proof checker is a string");
    let limits = exact_string(map_entry(proof, "limits").expect("proof limits field"))
        .expect("proof limits are a string");
    let evidence = exact_bytes(map_entry(proof, "evidence").expect("proof evidence field"))
        .expect("proof evidence is bytes");
    let evidence_hash =
        exact_bytes(map_entry(proof, "evidence-hash").expect("proof evidence-hash field"))
            .expect("proof evidence hash is bytes");
    let work = exact_int(map_entry(proof, "work").expect("proof work field"))
        .expect("proof work is an integer");
    let evidence_bytes =
        exact_int(map_entry(proof, "evidence-bytes").expect("proof evidence-bytes field"))
            .expect("proof evidence byte count is an integer");

    assert_eq!(language.len(), 32, "language identity is a complete fingerprint");
    assert_eq!(term.len(), 32, "term identity is a complete structural hash");
    assert_eq!(theorem.len(), 32, "theorem identity is a complete hash");
    assert_eq!(checker, STRUCTURAL_THEOREM_CHECKER_ABI_V1);
    assert_eq!(limits, STRUCTURAL_THEOREM_LIMIT_PROFILE_V1);
    assert_eq!(work, STRUCTURAL_ADMISSION_WORK_UNITS as i64);
    assert_eq!(evidence_bytes, evidence.len() as i64);
    assert!(work <= 1, "the application granted one logical work unit");
    assert!(evidence_bytes <= 4096, "the application granted 4096 evidence bytes");

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"mettail-admission-certificate/1\0");
    hasher.update(language);
    hasher.update(&category.to_be_bytes());
    hasher.update(term);
    hasher.update(theorem);
    framed_hash_field(&mut hasher, checker.as_bytes());
    framed_hash_field(&mut hasher, limits.as_bytes());
    framed_hash_field(&mut hasher, evidence);
    assert_eq!(
        evidence_hash,
        hasher.finalize().as_bytes(),
        "the serialized evidence hash must bind the complete certificate envelope",
    );

    ProofIdentity {
        language: language.to_vec(),
        category,
        term: term.to_vec(),
        theorem: theorem.to_vec(),
        evidence_hash: evidence_hash.to_vec(),
    }
}

async fn run_application(program: &Par) -> (Arc<LanguageInstallService>, BTreeMap<String, Par>) {
    let service = Arc::new(LanguageInstallService::new(
        Arc::new(EmptyRegistrySnapshot),
        LanguageInstallPolicy::default(),
    ));
    let runtime = Arc::new(RholangLanguageRuntime::new(service.clone()));
    let mut outputs =
        run_normalized_par_with_language_runtime_and_read_par_channels(program, runtime, &["OUT"])
            .await
            .expect("the committed application runs on the real Rholang evaluator");

    let mut labelled = BTreeMap::new();
    for output in outputs.remove("OUT").expect("OUT was requested") {
        let [label, response] = exact_list(&output).expect("OUT datum is [label, response]") else {
            panic!("OUT datum must have arity two")
        };
        let label = exact_string(label)
            .expect("OUT label is a string")
            .to_string();
        assert!(
            labelled.insert(label.clone(), response.clone()).is_none(),
            "duplicate OUT label `{label}`"
        );
    }
    (service, labelled)
}

#[tokio::test]
async fn committed_application_runs_the_inline_ddl_installation_contract_end_to_end() {
    mettail_runtime::clear_var_cache();
    let parsed = Proc::parse_via_wpda(APPLICATION)
        .expect("the committed application parses through nouveau Rholang");
    let program = lower_rholang_proc(&parsed)
        .expect("the committed application lowers without source reconstruction");
    let (service, labelled) = run_application(&program).await;
    let (_replay_service, replay) = run_application(&program).await;

    assert_eq!(labelled, replay, "fresh executions must produce the same semantic transcript");

    println!("labels: {:?}", labelled.keys().collect::<Vec<_>>());
    assert_eq!(labelled.len(), 13, "every application branch must reply exactly once");
    for label in ["left-positive", "right-positive"] {
        assert_eq!(parse_status(&labelled[label]), Some("accepted"), "{label}");
    }
    for label in ["left-negative", "right-negative", "left-crossfire", "right-crossfire"] {
        assert_eq!(parse_status(&labelled[label]), Some("rejected"), "{label}");
    }
    assert_eq!(
        error_code(&labelled["atomic-failure"]),
        Some("InvalidSurfaceDdl"),
        "the invalid suffix must reject the complete installation batch",
    );

    let committed = map_entry(&labelled["theorem-positive"], "ok")
        .expect("positive theorem response has an ok arm");
    assert_eq!(map_entry(committed, "status").and_then(exact_string), Some("committed"),);
    let captures = exact_list(map_entry(committed, "captures").expect("typed capture telescope"))
        .expect("captures form a proper list");
    assert_eq!(captures.len(), 1, "the whole-term hole extracts exactly one capture");
    assert!(
        exact_list(&captures[0]).is_some_and(|term| !term.is_empty()),
        "the capture is the reflected foreign term, not rendered guest text",
    );
    assert_eq!(
        exact_bytes(map_entry(committed, "pattern").expect("pattern identity")).map(<[u8]>::len),
        Some(32),
        "the committed match names its compiled structural pattern",
    );
    let message_identity = assert_bounded_structural_proof(
        map_entry(committed, "message-proof").expect("message admission proof"),
    );
    let capture_proofs =
        exact_list(map_entry(committed, "capture-proofs").expect("capture proof telescope"))
            .expect("capture proofs form a proper list");
    assert_eq!(capture_proofs.len(), 1);
    let capture_identity = assert_bounded_structural_proof(&capture_proofs[0]);
    assert_eq!(
        message_identity, capture_identity,
        "a whole-term typed hole returns the exact theorem-admitted message",
    );

    for (label, expected) in [
        ("theorem-invalid", "TheoremRefuted"),
        ("wrong-language", "WrongLanguageOrCategory"),
        ("stale-authority", "StaleAuthority"),
        ("ambiguous-pattern", "AmbiguousPattern"),
        ("theorem-exhausted", "AdmissionExhausted"),
    ] {
        assert_eq!(error_code(&labelled[label]), Some(expected), "{label}");
    }
    assert_eq!(
        service
            .installed_count()
            .expect("installed table is readable"),
        3,
        "only the three valid exports are visible; ValidPrefix from the failed batch was never published",
    );

    for (label, response) in &labelled {
        let result = parse_status(response).or_else(|| error_code(response));
        println!("{label}: {}", result.expect("every labelled response has a result"));
    }
    println!("installed-languages: 3");
}
