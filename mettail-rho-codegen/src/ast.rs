//! Normalized Rholang AST builders for generated dynamic sends.
//!
//! The static backend program is produced by `lower_language_def`. Runtime
//! calls and witness facts are dynamic inputs, but they must still cross the
//! same boundary: normalized `rhoapi::Par`, with Rholang-looking text only as a
//! reader annotation.

use models::rhoapi::Par;
use models::rust::utils::{new_gbool_par, new_gint_par, new_gstring_par, new_send_par};

/// Ground value used by generated Rho call and witness sends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoAstLiteral {
    Int(i64),
    Bool(bool),
    String(String),
    QuotedChannel(String),
}

impl RhoAstLiteral {
    fn to_par(&self) -> Par {
        match self {
            Self::Int(value) => new_gint_par(*value, Vec::new(), false),
            Self::Bool(value) => new_gbool_par(*value, Vec::new(), false),
            Self::String(value) | Self::QuotedChannel(value) => {
                new_gstring_par(value.clone(), Vec::new(), false)
            },
        }
    }

    fn annotation(&self) -> String {
        match self {
            Self::Int(value) => value.to_string(),
            Self::Bool(value) => value.to_string(),
            Self::String(value) => format!("{value:?}"),
            Self::QuotedChannel(value) => format!("@{value:?}"),
        }
    }
}

/// Construction error for generated Rho AST sends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoAstBuildError {
    EmptyChannel,
    EmptyReturnChannel,
    EmptyWitnessKey,
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
            data.iter().map(RhoAstLiteral::to_par).collect(),
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
    }
}
