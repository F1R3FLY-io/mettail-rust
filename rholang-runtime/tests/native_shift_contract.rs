#![cfg(feature = "runtime-report")]

use mettail_rholang_codegen::{
    bound_var_par, native_shift_amount_par, native_shift_channel, NativeShiftSpec,
};
use mettail_rholang_runtime::run::run_installed_program_with_call_definitions_and_read_runtime_values;
use mettail_rholang_runtime::{native_shift_definitions_for, par_as_runtime_observation_value};
use models::rhoapi::Par;
use models::rust::utils::{new_gstring_par, new_send_par};

const FP: &str = "mettail-langdef-v1:native-shift-runtime";

#[tokio::test]
async fn one_contract_call_shifts_and_produces_directly_on_the_dynamic_out_channel() {
    let out = "native-shift-out";
    let value = bound_var_par(3, FP);
    let call = new_send_par(
        native_shift_channel(FP),
        vec![
            native_shift_amount_par(20_000),
            value,
            new_gstring_par(out.to_owned(), Vec::new(), false),
        ],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    assert_eq!(call.sends.len(), 1, "the generated ABI is one dispatch send");
    assert!(call.news.is_empty() && call.receives.is_empty());

    let definitions = native_shift_definitions_for(&[NativeShiftSpec::new(FP, [], [])])
        .expect("one fingerprint has one collision-free shift Definition");
    let observed = run_installed_program_with_call_definitions_and_read_runtime_values(
        &Par::default(),
        &call,
        definitions,
        out,
    )
    .await
    .expect("native shift contract executes");
    let expected_par = bound_var_par(20_003, FP);
    let expected = par_as_runtime_observation_value(&expected_par)
        .expect("shifted reflected bound is an observation value");
    assert_eq!(observed, vec![expected]);
}
