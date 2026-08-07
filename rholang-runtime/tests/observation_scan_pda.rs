#[path = "support/observation_scan_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_rholang_runtime::{binder_apply_redex_present, flatten_observation_value, DriveNfScan};
use mettail_runtime::RuntimeObservationValue;

fn term(
    constructor: impl Into<String>,
    children: Vec<RuntimeObservationValue>,
) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.into(),
        children,
    }
}

fn bag(entries: Vec<(RuntimeObservationValue, usize)>) -> RuntimeObservationValue {
    RuntimeObservationValue::Bag(entries)
}

fn guarded_scan(value: &RuntimeObservationValue) -> bool {
    DriveNfScan::GuardedAcMobilityTrio {
        amb_label: "PAmb".to_owned(),
        in_label: "PIn".to_owned(),
        out_label: "POut".to_owned(),
        open_label: "POpen".to_owned(),
    }
    .redex_present(value)
}

fn guarded_oracle(value: &RuntimeObservationValue) -> bool {
    let value = recursive_oracle::flatten(value);
    recursive_oracle::guarded_ac_trio_redex_present("PAmb", "PIn", "POut", "POpen", &value)
}

fn shallow_corpus() -> Vec<RuntimeObservationValue> {
    let name_n = RuntimeObservationValue::PrivateName(vec![1]);
    let name_m = RuntimeObservationValue::PrivateName(vec![2]);
    let nil = term("PNil", Vec::new());
    let lambda = term("^lambda", vec![RuntimeObservationValue::Int(0)]);
    let beta = term("App", vec![lambda, RuntimeObservationValue::Int(7)]);
    let open = term("POpen", vec![name_n.clone(), nil.clone()]);
    let amb_n = term("PAmb", vec![name_n.clone(), bag(vec![(nil.clone(), 1)])]);
    let enter = term("PIn", vec![name_m.clone(), nil.clone()]);
    let amb_enter = term("PAmb", vec![name_n.clone(), bag(vec![(enter, 1)])]);
    let amb_m = term("PAmb", vec![name_m.clone(), bag(vec![(nil.clone(), 1)])]);
    let exit = term("POut", vec![name_m.clone(), nil.clone()]);
    let inner_amb = term("PAmb", vec![name_n, bag(vec![(exit, 1)])]);
    let outer_amb = term("PAmb", vec![name_m, bag(vec![(inner_amb, 1)])]);

    vec![
        RuntimeObservationValue::Int(1),
        beta.clone(),
        RuntimeObservationValue::List(vec![RuntimeObservationValue::Bool(false), beta.clone()]),
        RuntimeObservationValue::Tuple(vec![beta.clone()]),
        RuntimeObservationValue::Set(vec![beta.clone()]),
        RuntimeObservationValue::Map(vec![(RuntimeObservationValue::Text("key".to_owned()), beta)]),
        bag(vec![(open, 1), (amb_n, 1)]),
        bag(vec![(amb_enter, 1), (amb_m, 1)]),
        outer_amb,
        term("Wrapper", vec![bag(vec![(bag(vec![(term("Leaf", Vec::new()), 2)]), 3)])]),
        // Zero multiplicity is deliberately absent from the logical bag view.
        bag(vec![(term("POpen", vec![RuntimeObservationValue::Int(0), nil]), 0)]),
    ]
}

#[test]
fn pda_scans_and_flatten_match_recursive_oracles() {
    for value in shallow_corpus() {
        assert_eq!(
            binder_apply_redex_present("App", &value),
            recursive_oracle::binder_apply_redex_present("App", &value),
            "binder scan diverged for {value:?}"
        );
        assert_eq!(
            flatten_observation_value(&value),
            recursive_oracle::flatten(&value),
            "flatten diverged for {value:?}"
        );
        assert_eq!(
            guarded_scan(&value),
            guarded_oracle(&value),
            "guarded scan diverged for {value:?}"
        );
    }
}

#[test]
fn scans_and_flatten_are_stack_safe_at_twenty_thousand_levels() {
    std::thread::Builder::new()
        .name("observation-scan-pda-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut value = RuntimeObservationValue::Int(0);
            for _ in 0..20_000 {
                value = term("Wrapper", vec![value]);
            }

            assert!(!binder_apply_redex_present("App", &value));
            let flattened = flatten_observation_value(&value);
            assert_eq!(flattened, value);
            assert!(!guarded_scan(&value));
        })
        .expect("spawn observation scan stack-gate thread")
        .join()
        .expect("observation scan PDA overflowed or panicked");
}
