//! Structured dynamic-send payloads cross the runtime boundary as AST.
//!
//! This exercises the generic `RhoAstSend` builder directly: the test does not
//! parse Rholang text and does not assemble raw `rhoapi::Par` by hand.

use mettail_rholang_codegen::{RhoAstLiteral, RhoAstSend};
use mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_runtime_values;
use mettail_runtime::RuntimeObservationValue;

#[tokio::test]
async fn structured_ast_send_payloads_roundtrip_through_rspace_observation() {
    let send = RhoAstSend::new(
        "OUT",
        vec![
            RhoAstLiteral::List(vec![
                RhoAstLiteral::Int(1),
                RhoAstLiteral::String("two".to_string()),
            ]),
            RhoAstLiteral::Map(vec![(
                RhoAstLiteral::String("key".to_string()),
                RhoAstLiteral::Bool(true),
            )]),
            RhoAstLiteral::Bag(vec![
                (RhoAstLiteral::String("alpha".to_string()), 2),
                (RhoAstLiteral::String("beta".to_string()), 1),
            ]),
            RhoAstLiteral::Uri("rho:example".to_string()),
            RhoAstLiteral::Bytes(vec![0xde, 0xad, 0xbe, 0xef]),
            RhoAstLiteral::DoubleBits(0x3ff0_0000_0000_0000),
            RhoAstLiteral::BigIntBytes(vec![0x01, 0x02, 0x03]),
            RhoAstLiteral::BigRationalBytes {
                numerator: vec![0x02],
                denominator: vec![0x03],
            },
            RhoAstLiteral::FixedPointBytes { unscaled: vec![0x04, 0x05], scale: 2 },
            RhoAstLiteral::PrivateName(b"private-name".to_vec()),
            RhoAstLiteral::DeployId(b"deploy-id".to_vec()),
            RhoAstLiteral::DeployerId(b"deployer-id".to_vec()),
            RhoAstLiteral::SysAuthToken,
            RhoAstLiteral::Tuple(vec![
                RhoAstLiteral::String("tuple".to_string()),
                RhoAstLiteral::Int(3),
            ]),
            RhoAstLiteral::Set(vec![RhoAstLiteral::Int(5), RhoAstLiteral::Int(4)]),
        ],
    )
    .expect("structured AST send should build");

    let values = run_normalized_par_for_oracle_and_read_runtime_values(send.par(), "OUT")
        .await
        .expect("structured AST send should execute on RhoRuntime");

    assert_eq!(
        values,
        vec![
            RuntimeObservationValue::List(vec![
                RuntimeObservationValue::Int(1),
                RuntimeObservationValue::Text("two".to_string()),
            ]),
            RuntimeObservationValue::Map(vec![(
                RuntimeObservationValue::Text("key".to_string()),
                RuntimeObservationValue::Bool(true),
            )]),
            RuntimeObservationValue::Bag(vec![
                (RuntimeObservationValue::Text("alpha".to_string()), 2),
                (RuntimeObservationValue::Text("beta".to_string()), 1),
            ]),
            RuntimeObservationValue::Uri("rho:example".to_string()),
            RuntimeObservationValue::Bytes(vec![0xde, 0xad, 0xbe, 0xef]),
            RuntimeObservationValue::DoubleBits(0x3ff0_0000_0000_0000),
            RuntimeObservationValue::BigIntBytes(vec![0x01, 0x02, 0x03]),
            RuntimeObservationValue::BigRationalBytes {
                numerator: vec![0x02],
                denominator: vec![0x03],
            },
            RuntimeObservationValue::FixedPointBytes { unscaled: vec![0x04, 0x05], scale: 2 },
            RuntimeObservationValue::PrivateName(b"private-name".to_vec()),
            RuntimeObservationValue::DeployId(b"deploy-id".to_vec()),
            RuntimeObservationValue::DeployerId(b"deployer-id".to_vec()),
            RuntimeObservationValue::SysAuthToken,
            RuntimeObservationValue::Tuple(vec![
                RuntimeObservationValue::Text("tuple".to_string()),
                RuntimeObservationValue::Int(3),
            ]),
            RuntimeObservationValue::Set(vec![
                RuntimeObservationValue::Int(4),
                RuntimeObservationValue::Int(5),
            ]),
        ]
    );
}
