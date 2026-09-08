use super::*;

fn premise(op: &str, inputs: &[&str], outputs: &[(&str, &str)]) -> RhoValue {
    list([
        string("intrinsic"),
        map([
            ("op", string(op)),
            ("inputs", list(inputs.iter().map(|name| string(name)))),
            (
                "outputs",
                list(
                    outputs
                        .iter()
                        .map(|(name, sort)| list([string("typed"), string(name), string(sort)])),
                ),
            ),
        ]),
    ])
}

fn rewrite(premises: Vec<RhoValue>, rhs: &str) -> RhoValue {
    map([
        ("name", string("IntrinsicRule")),
        (
            "context",
            list(["a", "b", "c"].map(|name| list([string("typed"), string(name), string("Int")]))),
        ),
        ("left", string("a")),
        ("right", string(rhs)),
        ("premises", list(premises)),
    ])
}

fn presentation_accepts(rule: &RhoValue) -> bool {
    crate::schema::validate_fragment(&map([("rewrites", list([rule.clone()]))])).is_ok()
}

#[test]
fn shared_intrinsic_shape_admits_all_six_without_reordering_operands() {
    // Contextual compilation below tests binding order only. Carrier-valid
    // execution is checked separately through the actual installed theory.
    for (op, inputs, outputs, expected) in [
        (
            "exact_term_eq",
            vec!["b", "a"],
            vec![("out", "Int")],
            IntrinsicOpcode::ExactTermEq,
        ),
        ("utf8_at_end", vec!["a", "b"], vec![("out", "Int")], IntrinsicOpcode::Utf8AtEnd),
        (
            "utf8_scalar_at",
            vec!["a", "b"],
            vec![("out", "Int"), ("next", "Int")],
            IntrinsicOpcode::Utf8ScalarAt,
        ),
        (
            "utf8_slice",
            vec!["a", "c", "b"],
            vec![("out", "Int")],
            IntrinsicOpcode::Utf8Slice,
        ),
        (
            "checked_nat_add",
            vec!["a", "a"],
            vec![("out", "Int")],
            IntrinsicOpcode::CheckedNatAdd,
        ),
        (
            "utf8_concat_many",
            vec!["a"],
            vec![("out", "Int")],
            IntrinsicOpcode::Utf8ConcatMany,
        ),
    ] {
        let raw = premise(op, &inputs, &outputs);
        let shape = decode_intrinsic_shape(&raw, "test").expect("closed shape");
        assert_eq!(shape.opcode, expected);
        assert_eq!(shape.inputs, inputs);
        assert_eq!(
            shape.outputs,
            outputs
                .iter()
                .map(|(name, sort)| (*name, sort.to_string()))
                .collect::<Vec<_>>()
        );
        let rule = rewrite(vec![raw], "out");
        assert!(presentation_accepts(&rule), "presentation must admit {op}");
        let mut compiled = theory();
        compile_surface_rules(&[], &[rule], &mut compiled).expect("contextual binding");
        let arena = &compiled.rewrites[0].arena;
        let core::TheoryPremiseFormV1::Intrinsic(intrinsic) = &arena.premises[0].form else {
            panic!("same intrinsic must reach the core");
        };
        let mut actual_inputs = Vec::new();
        let mut actual_outputs = Vec::new();
        intrinsic
            .for_each_input(|id| actual_inputs.push(arena.variables[id.0 as usize].name.as_str()));
        intrinsic.for_each_output(|id| {
            let variable = &arena.variables[id.0 as usize];
            assert_eq!(variable.role, core::TheoryVariableRoleV1::Derived);
            actual_outputs.push(variable.name.as_str());
        });
        assert_eq!(actual_inputs, inputs);
        assert_eq!(actual_outputs, outputs.iter().map(|(name, _)| *name).collect::<Vec<_>>());
    }
}

#[test]
fn shared_intrinsic_shape_rejects_malformed_closed_payloads() {
    let valid = premise("checked_nat_add", &["a", "b"], &[("out", "Int")]);
    let mut cases = vec![
        premise("host_callback", &["a", "b"], &[("out", "Int")]),
        premise("checked_nat_add", &["a"], &[("out", "Int")]),
        premise("checked_nat_add", &["a", "b", "c"], &[("out", "Int")]),
        premise("checked_nat_add", &["a", "b"], &[]),
        premise("checked_nat_add", &["a", "b"], &[("out", "Int"), ("extra", "Int")]),
        premise("checked_nat_add", &["", "b"], &[("out", "Int")]),
        premise("checked_nat_add", &["a", "b"], &[("", "Int")]),
    ];
    for key in ["op", "inputs", "outputs"] {
        let mut raw = valid.clone();
        let RhoValue::List(tagged) = &mut raw else {
            unreachable!()
        };
        let RhoValue::Map(spec) = &mut tagged[1] else {
            unreachable!()
        };
        spec.remove(key);
        cases.push(raw);
    }
    let mut extra = valid.clone();
    let RhoValue::List(tagged) = &mut extra else {
        unreachable!()
    };
    let RhoValue::Map(spec) = &mut tagged[1] else {
        unreachable!()
    };
    spec.insert("callback".into(), string("not allowed"));
    cases.push(extra);
    let mut malformed_output = valid;
    let RhoValue::List(tagged) = &mut malformed_output else {
        unreachable!()
    };
    let RhoValue::Map(spec) = &mut tagged[1] else {
        unreachable!()
    };
    spec.insert(
        "outputs".into(),
        list([list([string("untyped"), string("out"), string("Int")])]),
    );
    cases.push(malformed_output);
    for raw in cases {
        assert!(decode_intrinsic_shape(&raw, "test").is_err());
        assert!(!presentation_accepts(&rewrite(vec![raw], "out")));
    }
}

#[test]
fn shared_intrinsic_shape_never_substitutes_for_contextual_checks() {
    for (raw, expected) in [
        (
            premise("checked_nat_add", &["missing", "b"], &[("out", "Int")]),
            "not available",
        ),
        (premise("checked_nat_add", &["a", "b"], &[("a", "Int")]), "not fresh"),
        (
            premise("utf8_scalar_at", &["a", "b"], &[("out", "Int"), ("out", "Int")]),
            "not fresh",
        ),
        (
            premise("checked_nat_add", &["a", "b"], &[("out", "Unknown")]),
            "unknown theory sort",
        ),
    ] {
        let rule = rewrite(vec![raw], "out");
        assert!(presentation_accepts(&rule), "shape check is not contextual compilation");
        let error =
            compile_surface_rules(&[], &[rule], &mut theory()).expect_err("contextual refusal");
        assert!(error.message.contains(expected), "{error:?}");
    }
}

#[test]
fn shared_intrinsic_shape_preserves_sequential_derived_variable_scope() {
    let rule = rewrite(
        vec![
            premise("checked_nat_add", &["a", "b"], &[("sum", "Int")]),
            premise("checked_nat_add", &["sum", "c"], &[("out", "Int")]),
        ],
        "out",
    );
    assert!(presentation_accepts(&rule));
    let mut compiled = theory();
    compile_surface_rules(&[], &[rule], &mut compiled)
        .expect("derived output is available to the next premise");
    let arena = &compiled.rewrites[0].arena;
    let core::TheoryPremiseFormV1::Intrinsic(core::TheoryIntrinsicV1::CheckedNatAdd {
        left, ..
    }) = arena.premises[1].form
    else {
        panic!("second addition retained");
    };
    assert_eq!(arena.variables[left.0 as usize].name, "sum");
    assert_eq!(arena.variables[left.0 as usize].role, core::TheoryVariableRoleV1::Derived);
}

#[test]
fn shared_intrinsic_shape_keeps_quantified_outputs_local() {
    let context =
        list([list([string("typed"), string("xs"), list([string("vec"), string("Expr")])])]);
    let scoped = list([
        string("forall"),
        string("xs"),
        string("x"),
        premise("exact_term_eq", &["x", "x"], &[("same", "Int")]),
    ]);
    let rule = |premises: Vec<RhoValue>, rhs: &str| {
        map([
            ("name", string("QuantifiedIntrinsic")),
            ("context", context.clone()),
            ("left", string("xs")),
            ("right", string(rhs)),
            ("premises", list(premises)),
        ])
    };
    let local = rule(vec![scoped.clone()], "xs");
    assert!(presentation_accepts(&local));
    let mut compiled = theory();
    compile_surface_rules(&[], &[local], &mut compiled).expect("local binding compiles");
    let arena = &compiled.rewrites[0].arena;
    assert_eq!(arena.variables[1].role, core::TheoryVariableRoleV1::Quantified);
    assert_eq!(arena.variables[2].role, core::TheoryVariableRoleV1::Derived);
    assert!(matches!(arena.premises[1].form, core::TheoryPremiseFormV1::ForAll { .. }));
    for (escaping, expected) in [
        (rule(vec![scoped.clone()], "same"), "unbound right-side variable `same`"),
        (
            rule(
                vec![scoped, premise("exact_term_eq", &["same", "same"], &[("out", "Int")])],
                "xs",
            ),
            "intrinsic input `same` is not available",
        ),
    ] {
        assert!(presentation_accepts(&escaping));
        let error = compile_surface_rules(&[], &[escaping], &mut theory())
            .expect_err("quantified intrinsic output cannot escape");
        assert!(error.message.contains(expected), "{error:?}");
    }
}
