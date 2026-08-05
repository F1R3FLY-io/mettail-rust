//! Normalized Rholang AST builders for generated dynamic sends.
//!
//! The static backend program is produced by `lower_language_def`. Runtime
//! calls and witness facts are dynamic inputs, but they must still cross the
//! same boundary: normalized `rhoapi::Par`, with Rholang-looking text only as a
//! reader annotation.

use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::{
    Expr, GBigRational, GDeployId, GDeployerId, GFixedPoint, GPrivate, GSysAuthToken, GUnforgeable,
    Par,
};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_elist_par, new_emap_par, new_eset_par, new_etuple_par, new_gbool_par, new_gbytearray_par,
    new_gint_par, new_gstring_par, new_guri_par, new_key_value_pair, new_send_par,
};

/// Ground value used by generated Rho call and witness sends.
pub enum RhoAstLiteral {
    Int(i64),
    Bool(bool),
    String(String),
    Uri(String),
    Bytes(Vec<u8>),
    DoubleBits(u64),
    BigIntBytes(Vec<u8>),
    BigRationalBytes { numerator: Vec<u8>, denominator: Vec<u8> },
    FixedPointBytes { unscaled: Vec<u8>, scale: u32 },
    PrivateName(Vec<u8>),
    DeployId(Vec<u8>),
    DeployerId(Vec<u8>),
    SysAuthToken,
    List(Vec<RhoAstLiteral>),
    Tuple(Vec<RhoAstLiteral>),
    Set(Vec<RhoAstLiteral>),
    Map(Vec<(RhoAstLiteral, RhoAstLiteral)>),
    Bag(Vec<(RhoAstLiteral, usize)>),
    QuotedChannel(String),
}

mod lifecycle;

enum AnnotationTask<'literal> {
    Visit(&'literal RhoAstLiteral),
    Text(&'static str),
    Count(usize),
}

impl RhoAstLiteral {
    pub fn try_to_par(&self) -> Result<Par, RhoAstBuildError> {
        enum Task<'literal> {
            Visit(&'literal RhoAstLiteral),
            Sequence { kind: u8, base: usize },
            Map { base: usize, len: usize },
            Bag { base: usize, counts: Vec<i64> },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(literal) => match literal {
                    Self::Int(value) => values.push(new_gint_par(*value, Vec::new(), false)),
                    Self::Bool(value) => values.push(new_gbool_par(*value, Vec::new(), false)),
                    Self::String(value) | Self::QuotedChannel(value) => {
                        values.push(new_gstring_par(value.clone(), Vec::new(), false));
                    },
                    Self::Uri(value) => {
                        values.push(new_guri_par(value.clone(), Vec::new(), false));
                    },
                    Self::Bytes(value) => {
                        values.push(new_gbytearray_par(value.clone(), Vec::new(), false));
                    },
                    Self::DoubleBits(value) => {
                        values.push(expr_par(ExprInstance::GDouble(*value)));
                    },
                    Self::BigIntBytes(value) => {
                        values.push(expr_par(ExprInstance::GBigInt(value.clone())));
                    },
                    Self::BigRationalBytes { numerator, denominator } => {
                        values.push(expr_par(ExprInstance::GBigRat(GBigRational {
                            numerator: numerator.clone(),
                            denominator: denominator.clone(),
                        })))
                    },
                    Self::FixedPointBytes { unscaled, scale } => {
                        values.push(expr_par(ExprInstance::GFixedPoint(GFixedPoint {
                            unscaled: unscaled.clone(),
                            scale: *scale,
                        })))
                    },
                    Self::PrivateName(value) => {
                        values.push(unforgeable_par(UnfInstance::GPrivateBody(GPrivate {
                            id: value.clone(),
                        })))
                    },
                    Self::DeployId(value) => {
                        values.push(unforgeable_par(UnfInstance::GDeployIdBody(GDeployId {
                            sig: value.clone(),
                        })))
                    },
                    Self::DeployerId(value) => {
                        values.push(unforgeable_par(UnfInstance::GDeployerIdBody(GDeployerId {
                            public_key: value.clone(),
                        })))
                    },
                    Self::SysAuthToken => values
                        .push(unforgeable_par(UnfInstance::GSysAuthTokenBody(GSysAuthToken {}))),
                    Self::List(children) | Self::Tuple(children) | Self::Set(children) => {
                        let kind = match literal {
                            Self::List(_) => 0,
                            Self::Tuple(_) => 1,
                            Self::Set(_) => 2,
                            _ => unreachable!(),
                        };
                        tasks.push(Task::Sequence { kind, base: values.len() });
                        for child in children.iter().rev() {
                            tasks.push(Task::Visit(child));
                        }
                    },
                    Self::Map(entries) => {
                        tasks.push(Task::Map { base: values.len(), len: entries.len() });
                        for (key, value) in entries.iter().rev() {
                            tasks.push(Task::Visit(value));
                            tasks.push(Task::Visit(key));
                        }
                    },
                    Self::Bag(entries) => {
                        let counts = entries
                            .iter()
                            .map(|(_, count)| {
                                i64::try_from(*count)
                                    .map_err(|_| RhoAstBuildError::BagMultiplicityTooLarge)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        tasks.push(Task::Bag { base: values.len(), counts });
                        for (value, _) in entries.iter().rev() {
                            tasks.push(Task::Visit(value));
                        }
                    },
                },
                Task::Sequence { kind, base } => {
                    let children = values.split_off(base);
                    values.push(match kind {
                        0 => new_elist_par(children, Vec::new(), false, None, Vec::new(), false),
                        1 => new_etuple_par(children),
                        2 => new_eset_par(children, Vec::new(), false, None, Vec::new(), false),
                        _ => unreachable!("unknown literal sequence kind"),
                    });
                },
                Task::Map { base, len } => {
                    let children = values.split_off(base);
                    debug_assert_eq!(children.len(), len * 2);
                    let mut children = children.into_iter();
                    let entries = (0..len)
                        .map(|_| {
                            new_key_value_pair(
                                children.next().expect("literal PDA lost a map key"),
                                children.next().expect("literal PDA lost a map value"),
                            )
                        })
                        .collect();
                    values.push(new_emap_par(entries, Vec::new(), false, None, Vec::new(), false));
                },
                Task::Bag { base, counts } => {
                    let children = values.split_off(base);
                    debug_assert_eq!(children.len(), counts.len());
                    let encoded_entries = children
                        .into_iter()
                        .zip(counts)
                        .map(|(value, count)| {
                            new_elist_par(
                                vec![value, new_gint_par(count, Vec::new(), false)],
                                Vec::new(),
                                false,
                                None,
                                Vec::new(),
                                false,
                            )
                        })
                        .collect();
                    let entries =
                        new_elist_par(encoded_entries, Vec::new(), false, None, Vec::new(), false);
                    let tag = GPrivateBuilder::new_par_from_string(
                        crate::RHOLANG_BAG_ABI_TAG.to_string(),
                    );
                    values.push(new_elist_par(
                        vec![tag, entries],
                        Vec::new(),
                        false,
                        None,
                        Vec::new(),
                        false,
                    ));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        Ok(values.pop().expect("literal-to-Par PDA produced no value"))
    }

    pub fn annotation(&self) -> String {
        let mut out = String::new();
        let mut tasks = vec![AnnotationTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                AnnotationTask::Text(text) => out.push_str(text),
                AnnotationTask::Count(count) => out.push_str(&count.to_string()),
                AnnotationTask::Visit(literal) => match literal {
                    Self::Int(value) => out.push_str(&value.to_string()),
                    Self::Bool(value) => out.push_str(&value.to_string()),
                    Self::String(value) => out.push_str(&format!("{value:?}")),
                    Self::Uri(value) => out.push_str(&format!("Uri({value:?})")),
                    Self::Bytes(value) => out.push_str(&format!("0x{}", hex_bytes(value))),
                    Self::DoubleBits(value) => {
                        out.push_str(&format!("DoubleBits(0x{value:016x})"));
                    },
                    Self::BigIntBytes(value) => {
                        out.push_str(&format!("BigInt(0x{})", hex_bytes(value)));
                    },
                    Self::BigRationalBytes { numerator, denominator } => out.push_str(&format!(
                        "BigRat(0x{}/0x{})",
                        hex_bytes(numerator),
                        hex_bytes(denominator)
                    )),
                    Self::FixedPointBytes { unscaled, scale } => out
                        .push_str(&format!("FixedPoint(0x{} scale {scale})", hex_bytes(unscaled))),
                    Self::PrivateName(value) => {
                        out.push_str(&format!("Private(0x{})", hex_bytes(value)));
                    },
                    Self::DeployId(value) => {
                        out.push_str(&format!("DeployId(0x{})", hex_bytes(value)));
                    },
                    Self::DeployerId(value) => {
                        out.push_str(&format!("DeployerId(0x{})", hex_bytes(value)));
                    },
                    Self::SysAuthToken => out.push_str("SysAuthToken"),
                    Self::List(children) => {
                        out.push('[');
                        push_annotation_sequence(&mut tasks, children, "]");
                    },
                    Self::Tuple(children) => {
                        out.push('(');
                        push_annotation_sequence(&mut tasks, children, ")");
                    },
                    Self::Set(children) => {
                        out.push_str("Set{");
                        push_annotation_sequence(&mut tasks, children, "}");
                    },
                    Self::Map(entries) => {
                        out.push('{');
                        tasks.push(AnnotationTask::Text("}"));
                        for (index, (key, value)) in entries.iter().enumerate().rev() {
                            tasks.push(AnnotationTask::Visit(value));
                            tasks.push(AnnotationTask::Text(": "));
                            tasks.push(AnnotationTask::Visit(key));
                            if index != 0 {
                                tasks.push(AnnotationTask::Text(", "));
                            }
                        }
                    },
                    Self::Bag(entries) => {
                        out.push_str("Bag{");
                        tasks.push(AnnotationTask::Text("}"));
                        for (index, (value, count)) in entries.iter().enumerate().rev() {
                            tasks.push(AnnotationTask::Count(*count));
                            tasks.push(AnnotationTask::Text(" * "));
                            tasks.push(AnnotationTask::Visit(value));
                            if index != 0 {
                                tasks.push(AnnotationTask::Text(", "));
                            }
                        }
                    },
                    Self::QuotedChannel(value) => out.push_str(&format!("@{value:?}")),
                },
            }
        }
        out
    }
}

fn push_annotation_sequence<'literal>(
    tasks: &mut Vec<AnnotationTask<'literal>>,
    children: &'literal [RhoAstLiteral],
    close: &'static str,
) {
    tasks.push(AnnotationTask::Text(close));
    for (index, child) in children.iter().enumerate().rev() {
        tasks.push(AnnotationTask::Visit(child));
        if index != 0 {
            tasks.push(AnnotationTask::Text(", "));
        }
    }
}

fn expr_par(expr_instance: ExprInstance) -> Par {
    Par::default().with_exprs(vec![Expr { expr_instance: Some(expr_instance) }])
}

fn unforgeable_par(unf_instance: UnfInstance) -> Par {
    Par::default().with_unforgeables(vec![GUnforgeable { unf_instance: Some(unf_instance) }])
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

/// Construction error for generated Rho AST sends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoAstBuildError {
    EmptyChannel,
    EmptyReturnChannel,
    EmptyWitnessKey,
    BagMultiplicityTooLarge,
}

/// A generated dynamic send represented as normalized `rhoapi::Par`.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoAstSend {
    channel: String,
    data: Vec<RhoAstLiteral>,
    par: Par,
    text_annotation: String,
}

impl RhoAstSend {
    /// Construct `@"channel"!(data...)` directly as normalized AST.
    pub fn new(
        channel: impl Into<String>,
        data: Vec<RhoAstLiteral>,
    ) -> Result<Self, RhoAstBuildError> {
        let channel = channel.into();
        if channel.is_empty() {
            return Err(RhoAstBuildError::EmptyChannel);
        }

        let par = new_send_par(
            new_gstring_par(channel.clone(), Vec::new(), false),
            data.iter()
                .map(RhoAstLiteral::try_to_par)
                .collect::<Result<Vec<_>, _>>()?,
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let data_annotation = data
            .iter()
            .map(RhoAstLiteral::annotation)
            .collect::<Vec<_>>()
            .join(", ");
        let text_annotation = format!("@{channel:?}!({data_annotation})");

        Ok(Self { channel, data, par, text_annotation })
    }

    /// Construct the scalar-contract ABI call:
    /// `@"operation"!(arg..., @"return_channel")`.
    pub fn contract_call(
        operation: impl Into<String>,
        mut arguments: Vec<RhoAstLiteral>,
        return_channel: impl Into<String>,
    ) -> Result<Self, RhoAstBuildError> {
        let return_channel = return_channel.into();
        if return_channel.is_empty() {
            return Err(RhoAstBuildError::EmptyReturnChannel);
        }
        arguments.push(RhoAstLiteral::QuotedChannel(return_channel));
        Self::new(operation, arguments)
    }

    /// Convenience constructor for calculator-style binary integer calls.
    pub fn binary_int_call(
        operation: impl Into<String>,
        left: i64,
        right: i64,
        return_channel: impl Into<String>,
    ) -> Result<Self, RhoAstBuildError> {
        Self::contract_call(
            operation,
            vec![RhoAstLiteral::Int(left), RhoAstLiteral::Int(right)],
            return_channel,
        )
    }

    /// Convenience constructor for calculator-style unary integer calls.
    pub fn unary_int_call(
        operation: impl Into<String>,
        value: i64,
        return_channel: impl Into<String>,
    ) -> Result<Self, RhoAstBuildError> {
        Self::contract_call(operation, vec![RhoAstLiteral::Int(value)], return_channel)
    }

    /// Construct an enabled ambiguity witness fact:
    /// `@"witness_channel"!("key", "payload")`.
    ///
    /// Disabled/refuted alternatives are represented by the absence of this
    /// send; exact-key conflict handling belongs to `mettail-rho-adapter`.
    pub fn ambiguity_witness(
        witness_channel: impl Into<String>,
        key: impl Into<String>,
        payload: impl Into<String>,
    ) -> Result<Self, RhoAstBuildError> {
        let key = key.into();
        if key.is_empty() {
            return Err(RhoAstBuildError::EmptyWitnessKey);
        }
        Self::new(
            witness_channel,
            vec![RhoAstLiteral::String(key), RhoAstLiteral::String(payload.into())],
        )
    }

    pub fn channel(&self) -> &str {
        &self.channel
    }

    pub fn data(&self) -> &[RhoAstLiteral] {
        &self.data
    }

    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::expr::ExprInstance;

    fn only_expr(par: &Par) -> &ExprInstance {
        let [expr] = par.exprs.as_slice() else {
            panic!("expected exactly one expression");
        };
        expr.expr_instance.as_ref().expect("expression instance")
    }

    fn gstring(par: &Par) -> Option<&str> {
        let [expr] = par.exprs.as_slice() else {
            return None;
        };
        match expr.expr_instance.as_ref()? {
            ExprInstance::GString(value) => Some(value.as_str()),
            _ => None,
        }
    }

    #[test]
    fn contract_call_builds_normalized_ast_not_source_text() {
        let call = RhoAstSend::binary_int_call("AddInt", 2, 3, "OUT").expect("valid binary call");

        assert_eq!(call.channel(), "AddInt");
        assert_eq!(call.text_annotation(), "@\"AddInt\"!(2, 3, @\"OUT\")");
        assert!(call.par().receives.is_empty());
        assert_eq!(call.par().sends.len(), 1);
        assert!(!call.par().connective_used);
        assert!(call.par().locally_free.is_empty());

        let send = &call.par().sends[0];
        assert!(!send.persistent);
        assert_eq!(send.data.len(), 3);
        assert_eq!(gstring(send.chan.as_ref().expect("channel")), Some("AddInt"));
        assert_eq!(gstring(&send.data[2]), Some("OUT"));
        assert!(send.locally_free.is_empty());
        assert!(!send.connective_used);
    }

    #[test]
    fn ambiguity_witness_is_a_two_field_ast_fact() {
        let witness =
            RhoAstSend::ambiguity_witness("AMB", "branch-a", "payload-a").expect("valid witness");

        assert_eq!(witness.channel(), "AMB");
        assert_eq!(witness.text_annotation(), "@\"AMB\"!(\"branch-a\", \"payload-a\")");
        let send = &witness.par().sends[0];
        assert_eq!(gstring(send.chan.as_ref().expect("channel")), Some("AMB"));
        assert_eq!(send.data.len(), 2);
        assert_eq!(gstring(&send.data[0]), Some("branch-a"));
        assert_eq!(gstring(&send.data[1]), Some("payload-a"));
    }

    #[test]
    fn structured_literals_build_normalized_ast_payloads() {
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
                RhoAstLiteral::Bag(vec![(RhoAstLiteral::String("alpha".to_string()), 2)]),
            ],
        )
        .expect("structured literals should build");

        assert_eq!(
            send.text_annotation(),
            "@\"OUT\"!([1, \"two\"], {\"key\": true}, Bag{\"alpha\" * 2})"
        );
        let data = &send.par().sends[0].data;
        assert!(matches!(only_expr(&data[0]), ExprInstance::EListBody(list) if list.ps.len() == 2));
        assert!(matches!(only_expr(&data[1]), ExprInstance::EMapBody(map) if map.kvs.len() == 1));
        let ExprInstance::EListBody(bag) = only_expr(&data[2]) else {
            panic!("bag should use tagged EList ABI");
        };
        assert_eq!(bag.ps.len(), 2);
        assert_eq!(
            bag.ps[0],
            GPrivateBuilder::new_par_from_string(crate::RHOLANG_BAG_ABI_TAG.to_string())
        );
    }

    #[test]
    fn rejects_empty_channels_and_empty_witness_keys() {
        assert_eq!(
            RhoAstSend::new("", Vec::new()).expect_err("empty send channel"),
            RhoAstBuildError::EmptyChannel
        );
        assert_eq!(
            RhoAstSend::contract_call("AddInt", Vec::new(), "").expect_err("empty return channel"),
            RhoAstBuildError::EmptyReturnChannel
        );
        assert_eq!(
            RhoAstSend::ambiguity_witness("AMB", "", "payload").expect_err("empty witness key"),
            RhoAstBuildError::EmptyWitnessKey
        );
        assert_eq!(
            RhoAstSend::new(
                "OUT",
                vec![RhoAstLiteral::Bag(vec![(
                    RhoAstLiteral::String("x".to_string()),
                    usize::MAX
                )])],
            )
            .expect_err("oversized bag multiplicity"),
            RhoAstBuildError::BagMultiplicityTooLarge
        );
    }
}
