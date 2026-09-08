//! Owned six-field request extraction. This composes the existing scalar and
//! limits codecs with the exact-list view; it is not a source parser. The
//! request retains structural input and reply values without cloning them.

use super::receipt::Decoder;
use super::{decode_limits_v1, SemanticWireError};
use crate::language_install::exact_string;
use crate::semantic_service::SemanticServiceLimits;
use mettail_rholang_codegen::ReflectedCodecBudget;
use models::rhoapi::{expr::ExprInstance, Par};

pub(crate) struct OwnedSemanticRequest {
    fields: [Par; 6],
    pub(crate) limits: SemanticServiceLimits,
}

impl OwnedSemanticRequest {
    pub(crate) fn decode<C: FnMut() -> bool>(
        mut payload: Vec<Par>,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, SemanticWireError> {
        budget.charge(1, 0)?;
        if payload.len() != 1 {
            return Err(SemanticWireError::Shape("semantic call requires one datum"));
        }
        let mut datum = payload.pop().expect("singleton checked");
        let mut decoder = Decoder { budget };
        let [version, _handle, name, _input, limits, _reply] = decoder.tuple(&datum)?;
        if decoder.uint(version)? != 1 {
            return Err(SemanticWireError::Shape("semantic request version"));
        }
        decoder.budget.charge(1, 0)?;
        if !name.locally_free.is_empty() || name.connective_used {
            return Err(SemanticWireError::Shape(
                "semantic declaration name has nonliteral metadata",
            ));
        }
        let name = exact_string(name)
            .ok_or(SemanticWireError::Shape("semantic declaration name must be a string"))?;
        decoder.budget.charge(name.len(), 0)?;
        let limits = decode_limits_v1(limits, decoder.budget)?;
        decoder.budget.charge(6, 0)?;
        let Some(ExprInstance::EListBody(list)) = datum.exprs[0].expr_instance.as_mut() else {
            unreachable!("exact tuple view established the unique list expression")
        };
        let fields = std::mem::take(&mut list.ps)
            .try_into()
            .map_err(|_| SemanticWireError::Shape("semantic request arity"))?;
        Ok(Self { fields, limits })
    }

    pub(crate) fn handle(&self) -> &Par {
        &self.fields[1]
    }

    pub(crate) fn name(&self) -> &str {
        exact_string(&self.fields[2]).expect("validated immutable declaration name")
    }

    pub(crate) fn input(&self) -> &Par {
        &self.fields[3]
    }

    pub(crate) fn into_reply(self) -> Par {
        let [_, _, _, _, _, reply] = self.fields;
        reply
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language_install::{exact_list, wire_list};
    use crate::semantic_wire::encode_limits_v1;
    use mettail_rholang_codegen::DynamicReflectionError;
    use models::rust::utils::{new_gint_par, new_gstring_par};

    fn datum(input: Par, reply: Par) -> Par {
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 1000, &mut cancel);
        let limits = encode_limits_v1(SemanticServiceLimits::default(), &mut budget).unwrap();
        wire_list(vec![
            new_gint_par(1, Vec::new(), false),
            Par::default(),
            new_gstring_par("expand-plus".into(), Vec::new(), false),
            input,
            limits,
            reply,
        ])
    }

    #[test]
    fn semantic_wire_request_preserves_fields_and_exact_prefix_without_payload_allocation() {
        let value =
            datum(wire_list(vec![Par::default()]), wire_list(vec![Par::default(), Par::default()]));
        let before = exact_list(&value).unwrap();
        let input = exact_list(&before[3]).unwrap().as_ptr();
        let reply = exact_list(&before[5]).unwrap().as_ptr();
        let mut work = 7;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
        let request = OwnedSemanticRequest::decode(vec![value], &mut budget).expect("request");
        assert_eq!(request.handle(), &Par::default());
        assert_eq!(request.name(), "expand-plus");
        assert_eq!(request.limits, SemanticServiceLimits::default());
        assert_eq!(exact_list(request.input()).unwrap().as_ptr(), input);
        assert_eq!(exact_list(&request.into_reply()).unwrap().as_ptr(), reply);
        assert_eq!(budget.remaining_bytes(), 0);
        assert_eq!(budget.work_used(), 7 + 1 + 1 + 1 + 1 + 11 + 1 + 11 + 6);
    }

    #[test]
    fn semantic_wire_request_rejects_wrong_arity_version_and_name_without_inspecting_guest() {
        let mut cases = vec![vec![], vec![Par::default(), Par::default()], vec![Par::default()]];
        for index in 0..6 {
            let mut value = datum(Par::default(), Par::default());
            let Some(ExprInstance::EListBody(list)) = value.exprs[0].expr_instance.as_mut() else {
                unreachable!()
            };
            match index {
                0 => {
                    list.ps.pop();
                },
                1 => list.ps.push(Par::default()),
                2 => list.ps[0] = new_gint_par(2, Vec::new(), false),
                3 => list.ps[2] = new_gint_par(1, Vec::new(), false),
                4 => list.ps[2].locally_free.push(1),
                _ => list.ps[2].sends.push(Default::default()),
            }
            cases.push(vec![value]);
        }
        for payload in cases {
            let mut work = 7;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
            assert!(OwnedSemanticRequest::decode(payload, &mut budget).is_err());
            assert!(budget.work_used() >= 7);
            assert_eq!(budget.remaining_bytes(), 0);
        }
    }

    #[test]
    fn semantic_wire_request_exact_work_and_every_cancellation_boundary() {
        let mut work = 7;
        let mut calls = 0;
        let mut cancel = || {
            calls += 1;
            false
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
        OwnedSemanticRequest::decode(vec![datum(Par::default(), Par::default())], &mut budget)
            .unwrap();
        budget.finish();
        for (allowance, accepted) in [(work, true), (work - 1, false)] {
            let mut prefix = 7;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut prefix, allowance, 0, &mut cancel);
            assert_eq!(
                OwnedSemanticRequest::decode(
                    vec![datum(Par::default(), Par::default())],
                    &mut budget
                )
                .is_ok(),
                accepted
            );
            assert!(budget.work_used() <= allowance);
        }
        for stop in 1..=calls {
            let mut prefix = 7;
            let mut count = 0;
            let mut cancel = || {
                count += 1;
                count == stop
            };
            let mut budget = ReflectedCodecBudget::new(&mut prefix, work, 0, &mut cancel);
            assert!(matches!(
                OwnedSemanticRequest::decode(
                    vec![datum(Par::default(), Par::default())],
                    &mut budget
                ),
                Err(SemanticWireError::Resource(DynamicReflectionError::Cancelled))
            ));
            assert!(budget.work_used() <= work);
        }
    }

    #[test]
    fn semantic_wire_request_moves_deep_input_and_reply_on_small_stack() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut input = Par::default();
                let mut reply = Par::default();
                for _ in 0..20_000 {
                    input = wire_list(vec![input]);
                    reply = wire_list(vec![reply]);
                }
                let mut work = 0;
                let mut cancel = || false;
                let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancel);
                let request =
                    OwnedSemanticRequest::decode(vec![datum(input, reply)], &mut budget).unwrap();
                drop(request.into_reply());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
