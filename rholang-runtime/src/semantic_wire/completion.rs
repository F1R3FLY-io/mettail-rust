//! Fixed-depth reply metadata, using the receipt codec's scalar/list schedule.
//! SemanticReplyCompletion.v checks the exact schema and prepaid shell bound.

use super::receipt::{Decoder, Encoder};
use super::SemanticWireError;
use crate::semantic_service::SemanticServiceLimits;
use mettail_dovetail_runtime::SemanticTransitionLimits;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use models::rhoapi::Par;

type Result<T> = std::result::Result<T, SemanticWireError>;

/// Logical cumulative usage. These fields neither confer authority nor settle
/// funding. The kernel subtotal is data and is never charged during encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticWireUsage {
    pub work: u64,
    pub kernel_work: Option<u64>,
    pub effective_limits: Option<SemanticServiceLimits>,
    pub remaining_boundary_payload_bytes: usize,
}

fn host_word(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| SemanticWireError::IntegerRange)
}

impl<C: FnMut() -> bool> Encoder<'_, '_, C> {
    fn limits(&mut self, limits: SemanticServiceLimits) -> Result<Par> {
        let x = limits.execution;
        self.tuple(|e| {
            Ok([
                e.uint(x.work)?,
                e.uint(host_word(x.normalization_steps)?)?,
                e.uint(host_word(x.outputs)?)?,
                e.uint(host_word(x.frontier)?)?,
                e.uint(host_word(x.proofs)?)?,
                e.uint(host_word(x.proof_nodes)?)?,
                e.uint(host_word(x.term_nodes)?)?,
                e.uint(host_word(x.term_bytes)?)?,
                e.uint(host_word(x.output_nodes)?)?,
                e.uint(host_word(x.output_bytes)?)?,
                e.uint(host_word(limits.boundary_payload_bytes)?)?,
            ])
        })
    }

    fn option<T>(
        &mut self,
        value: Option<T>,
        encode: impl FnOnce(&mut Self, T) -> Result<Par>,
    ) -> Result<Par> {
        match value {
            None => self.tuple(|e| Ok([e.uint(0u8)?])),
            Some(value) => self.tuple(|e| Ok([e.uint(1u8)?, encode(e, value)?])),
        }
    }

    fn usage(&mut self, usage: SemanticWireUsage) -> Result<Par> {
        self.tuple(|e| {
            Ok([
                e.uint(usage.work)?,
                e.option(usage.kernel_work, |e, n| e.uint(n))?,
                e.option(usage.effective_limits, Self::limits)?,
                e.uint(host_word(usage.remaining_boundary_payload_bytes)?)?,
            ])
        })
    }
}

impl<C: FnMut() -> bool> Decoder<'_, '_, C> {
    fn host_word(&mut self, value: &Par) -> Result<usize> {
        usize::try_from(self.uint(value)?).map_err(|_| SemanticWireError::IntegerRange)
    }

    fn limits(&mut self, value: &Par) -> Result<SemanticServiceLimits> {
        let [w, n, o, f, p, pn, tn, tb, on, ob, boundary] = self.tuple(value)?;
        Ok(SemanticServiceLimits {
            execution: SemanticTransitionLimits {
                work: self.uint(w)?,
                normalization_steps: self.host_word(n)?,
                outputs: self.host_word(o)?,
                frontier: self.host_word(f)?,
                proofs: self.host_word(p)?,
                proof_nodes: self.host_word(pn)?,
                term_nodes: self.host_word(tn)?,
                term_bytes: self.host_word(tb)?,
                output_nodes: self.host_word(on)?,
                output_bytes: self.host_word(ob)?,
            },
            boundary_payload_bytes: self.host_word(boundary)?,
        })
    }

    fn option<T>(
        &mut self,
        value: &Par,
        decode: impl FnOnce(&mut Self, &Par) -> Result<T>,
    ) -> Result<Option<T>> {
        match self.list(value)? {
            [tag] if self.uint(tag)? == 0 => Ok(None),
            [tag, value] if self.uint(tag)? == 1 => decode(self, value).map(Some),
            _ => Err(SemanticWireError::Shape("semantic option arity or tag")),
        }
    }

    fn usage(&mut self, value: &Par) -> Result<SemanticWireUsage> {
        let [work, kernel, limits, remaining] = self.tuple(value)?;
        Ok(SemanticWireUsage {
            work: self.uint(work)?,
            kernel_work: self.option(kernel, Self::uint)?,
            effective_limits: self.option(limits, Self::limits)?,
            remaining_boundary_payload_bytes: self.host_word(remaining)?,
        })
    }
}

/// Encode exactly the eleven limits, without the policy's schedule markers.
pub fn encode_limits_v1<C: FnMut() -> bool>(
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Par> {
    Encoder { budget }.limits(limits)
}

/// Borrow canonical closed metadata; no payload allocation or source parsing.
pub fn decode_limits_v1<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SemanticServiceLimits> {
    Decoder { budget }.limits(value)
}

/// Decode the exact four-field usage schema, preserving both optional values.
pub fn decode_usage_v1<C: FnMut() -> bool>(
    value: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SemanticWireUsage> {
    Decoder { budget }.usage(value)
}

const COMPLETION_WORK: usize = 152;
const COMPLETION_BYTES: usize = 742;

/// A host-generated diagnostic has a fixed-size code, never untrusted text.
#[derive(Clone, Copy)]
pub(super) enum DiagnosticDomain {
    Wire,
    Access,
    Service,
    Kernel,
    Boundary,
    Restore,
}

impl DiagnosticDomain {
    fn tag(self) -> u8 {
        match self {
            Self::Wire => 0,
            Self::Access => 1,
            Self::Service => 2,
            Self::Kernel => 3,
            Self::Boundary => 4,
            Self::Restore => 5,
        }
    }
}

pub(super) enum ReplyBody {
    Proven(Par),
    Refuted(DiagnosticDomain, u16),
    Undetermined(DiagnosticDomain, u16),
    Error(DiagnosticDomain, u16),
}

impl ReplyBody {
    fn status(&self) -> u8 {
        match self {
            Self::Proven(_) => 0,
            Self::Refuted(..) => 1,
            Self::Undetermined(..) => 2,
            Self::Error(..) => 3,
        }
    }

    fn encode<C: FnMut() -> bool>(self, encoder: &mut Encoder<'_, '_, C>) -> Result<Par> {
        match self {
            Self::Proven(value) => {
                if !value.locally_free.is_empty() || value.connective_used {
                    return Err(SemanticWireError::Shape("semantic result body is not closed"));
                }
                Ok(value)
            },
            Self::Refuted(domain, code)
            | Self::Undetermined(domain, code)
            | Self::Error(domain, code) => {
                encoder.tuple(|e| Ok([e.uint(domain.tag())?, e.uint(code)?]))
            },
        }
    }
}

/// Wrap the operation's one cancellation source before any accounted stage.
pub(super) struct StickyCancellation<C> {
    check: C,
    observed: bool,
}

impl<C: FnMut() -> bool> StickyCancellation<C> {
    pub(super) fn new(check: C) -> Self {
        Self { check, observed: false }
    }

    pub(super) fn poll(&mut self) -> bool {
        self.observed |= (self.check)();
        self.observed
    }
}

/// Private, non-Clone credit. Ownership is consumed even if encoding fails.
pub(super) struct CompletionPermit {
    initial_limits: SemanticServiceLimits,
    minimum_work: u64,
    minimum_payload: usize,
}

impl CompletionPermit {
    pub(super) fn reserve<C: FnMut() -> bool>(
        limits: SemanticServiceLimits,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self> {
        let spent = limits
            .boundary_payload_bytes
            .checked_sub(budget.remaining_bytes())
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        budget
            .work_used()
            .checked_add(COMPLETION_WORK as u64)
            .filter(|n| *n <= limits.execution.work)
            .ok_or(DynamicReflectionError::WorkLimit)?;
        budget.charge(COMPLETION_WORK, COMPLETION_BYTES)?;
        Ok(Self {
            initial_limits: limits,
            minimum_work: budget.work_used(),
            minimum_payload: spent + COMPLETION_BYTES,
        })
    }

    pub(super) fn finish<C: FnMut() -> bool>(
        self,
        body: ReplyBody,
        usage: SemanticWireUsage,
        cancellation: &mut StickyCancellation<C>,
    ) -> Result<Par> {
        let limits = usage.effective_limits.unwrap_or(self.initial_limits);
        if limits
            .commitment_words()
            .into_iter()
            .zip(self.initial_limits.commitment_words())
            .any(|(current, initial)| current > initial)
        {
            return Err(SemanticWireError::Shape("semantic completion amplified limits"));
        }
        if usage.work < self.minimum_work || usage.work > limits.execution.work {
            return Err(DynamicReflectionError::WorkLimit.into());
        }
        if usage.kernel_work.is_some_and(|n| n > usage.work) {
            return Err(SemanticWireError::Shape("kernel work exceeds cumulative work"));
        }
        limits
            .boundary_payload_bytes
            .checked_sub(usage.remaining_boundary_payload_bytes)
            .filter(|n| *n >= self.minimum_payload)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let status = body.status();
        let proven = status == 0;
        let mut local_work = 0;
        let mut check = || {
            let cancelled = cancellation.poll();
            proven && cancelled
        };
        let mut local = ReflectedCodecBudget::new(
            &mut local_work,
            COMPLETION_WORK as u64,
            COMPLETION_BYTES,
            &mut check,
        );
        let result = Encoder { budget: &mut local }
            .tuple(|e| Ok([e.uint(1u8)?, e.uint(status)?, body.encode(e)?, e.usage(usage)?]))?;
        local.charge(0, 0)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests;
