use super::*;

const SOURCE: &str = include_str!("../../../tests/fixtures/regex_gslt.rho");

#[test]
fn practical_regex_gslt_executes_declared_rules_through_the_generated_rholang_entrypoint() {
    let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
        Arc::new(MemoryRegistry::default()),
        LanguageInstallPolicy::default(),
    )));
    let batch = runtime
        .install_all(rholang_ddl_candidate(SOURCE))
        .expect("practical regex declaration installs through the actual inline DDL path");
    assert_eq!(batch.exports.len(), 1);
    assert_eq!(batch.exports[0].name, "Regex");
    let token = &batch.exports[0].handle;
    for (source, action, expected) in [
        ("nullable((?!))", "nullable", "doneBool(false)"),
        ("nullable(())", "nullable", "doneBool(true)"),
        ("nullable(a)", "nullable", "doneBool(false)"),
        ("nullable(.)", "nullable", "doneBool(false)"),
        ("nullable((a))", "nullable", "doneBool(false)"),
        ("nullable(a|())", "nullable", "doneBool(true)"),
        ("nullable(a())", "nullable", "doneBool(false)"),
        ("nullable(a*)", "nullable", "doneBool(true)"),
        ("nullable(a+)", "nullable", "doneBool(false)"),
        ("nullable(a?)", "nullable", "doneBool(true)"),
        ("derivative(a,a+)", "derivative", "donePattern(a*)"),
        ("nullable(a{2,3})", "nullable", "doneBool(false)"),
        ("nullable(a{0,0})", "nullable", "doneBool(true)"),
        ("nullable(a{3,2})", "nullable", "doneBool(false)"),
        ("nullable(λ?)", "nullable", "doneBool(true)"),
        ("derivative(a,(?!))", "derivative", "donePattern((?!))"),
        ("derivative(a,())", "derivative", "donePattern((?!))"),
        ("derivative(a,a)", "derivative", "donePattern(())"),
        ("derivative(a,b)", "derivative", "donePattern((?!))"),
        ("derivative(λ,.)", "derivative", "donePattern(())"),
        ("derivative(λ,λ)", "derivative", "donePattern(())"),
        ("derivative(a,a|b)", "derivative", "donePattern(())"),
        ("derivative(a,ab)", "derivative", "donePattern(b)"),
        ("derivative(b,ab)", "derivative", "donePattern((?!))"),
        ("derivative(b,a?b)", "derivative", "donePattern(())"),
        ("derivative(a,a*)", "derivative", "donePattern(a*)"),
    ] {
        let input = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Text(source.into())],
                &[],
                Some("Computation"),
                &BTreeMap::new(),
            )
            .unwrap_or_else(|error| panic!("declared request {source} must parse: {error:?}"));
        let expected = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Text(expected.into())],
                &[],
                Some("Computation"),
                &BTreeMap::new(),
            )
            .expect("declared result syntax");
        let report = runtime.execute_semantic(
            SemanticServiceRequest {
                handle: token,
                operation: SemanticOperation::Reduce(action),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            || false,
        );
        let outputs = report.outcome.unwrap_or_else(|error| {
            panic!(
                "{source}: {error:?}; total work={}, kernel work={:?}",
                report.work, report.kernel_work
            )
        });
        assert_eq!(outputs.len(), 1, "{source}: deterministic declared result");
        assert_eq!(outputs[0].term, expected, "{source}: complete structural result");
        eprintln!("{source}: exact result verified; work={}", report.work);
    }
}
