//! Compiler-internal qualified FLT guard descriptor and its explicit capture map.
//! The existing structural template codec is reused as data, never sent to a
//! construction service or substituted through an arbitrary list expression.
use crate::language_install::{
    decode_flt_construct_call, encode_flt_construct_call, exact_expr, exact_list, exact_string,
    wire_list, NamedRuntimeTemplateHole, RholangLanguageRuntime,
};
use crate::semantic_service::{predicate::PredicateEvidence, SemanticServiceLimits};
use mettail_grammar_core::RuntimeTemplatePiece;
use mettail_rholang_codegen::ReflectedCodecBudget;
use models::rhoapi::{expr::ExprInstance, var::VarInstance, Par};
use models::rust::utils::new_gstring_par;
use std::collections::BTreeMap;

const DESCRIPTOR: &str = "mettail-qualified-flt-where/1";

pub(crate) fn encode_flt_predicate_descriptor(
    selector: Par,
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: &str,
    captures: &BTreeMap<String, Par>,
) -> Par {
    wire_list(vec![
        new_gstring_par(DESCRIPTOR.into(), Vec::new(), false),
        encode_flt_construct_call(selector, pieces, holes, category, captures, Par::default()),
    ])
}

pub(crate) fn is_descriptor(value: &Par) -> bool {
    exact_list(value)
        .and_then(|fields| fields.first())
        .and_then(exact_string)
        == Some(DESCRIPTOR)
}

/// Resolve only one declared selector/capture slot. A substituted payload is
/// never traversed, preserving its own nested binders and opaque collections.
fn capture<'a>(value: &'a Par, bindings: &'a [Par]) -> Result<&'a Par, &'static str> {
    match exact_expr(value) {
        Some(ExprInstance::EVarBody(var)) => {
            match var.v.as_ref().and_then(|v| v.var_instance.as_ref()) {
                Some(VarInstance::BoundVar(index)) => usize::try_from(*index)
                    .ok()
                    .and_then(|index| bindings.len().checked_sub(index.checked_add(1)?))
                    .and_then(|index| bindings.get(index))
                    .ok_or("predicate capture is outside receive scope"),
                _ => Err("predicate capture is not a bound reference"),
            }
        },
        _ => Ok(value),
    }
}

/// One candidate uses one cumulative semantic/codec allowance. Template
/// recognition continues through the installed parser's existing host policy;
/// captured bytes never become parser source text.
pub(crate) fn prepare<C: FnMut() -> bool>(
    runtime: &RholangLanguageRuntime,
    descriptor: &Par,
    bindings: &[Par],
    work: &mut u64,
    remaining_bytes: &mut usize,
    limits: SemanticServiceLimits,
    cancel: &mut C,
) -> Result<PredicateEvidence, String> {
    let [tag, template] = exact_list(descriptor).ok_or("predicate descriptor is not a list")?
    else {
        return Err("predicate descriptor arity".into());
    };
    if exact_string(tag) != Some(DESCRIPTOR) {
        return Err("predicate descriptor version".into());
    }
    let call = decode_flt_construct_call(template).map_err(|e| e.to_string())?;
    let handle = capture(&call.handle, bindings)?;
    let mut budget =
        ReflectedCodecBudget::new(work, limits.execution.work, *remaining_bytes, cancel);
    let input = (|| -> Result<Par, String> {
        let mut fills = BTreeMap::new();
        for (name, value) in &call.fills {
            budget
                .charge(name.len().checked_add(1).ok_or("capture size overflow")?, name.len())
                .map_err(|e| format!("{e:?}"))?;
            let value = capture(value, bindings)?;
            fills.insert(name.clone(), value.clone());
        }
        runtime
            .construct_template_with_budget(
                handle,
                &call.pieces,
                &call.holes,
                Some(&call.category),
                &fills,
                &mut budget,
            )
            .map_err(|e| format!("{e:?}"))
    })();
    *remaining_bytes = budget.finish();
    let input = input?;
    let evidence = runtime.prepare_where_predicate(
        handle,
        &input,
        *work,
        limits
            .boundary_payload_bytes
            .checked_sub(*remaining_bytes)
            .ok_or("predicate payload accounting")?,
        limits,
        cancel,
    );
    *work = evidence.work();
    *remaining_bytes = evidence.remaining_bytes();
    Ok(evidence)
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rust::utils::{new_boundvar_par, new_gint_par};
    #[test]
    fn captures_keep_join_order_repetition_and_payload_scope() {
        let values = vec![new_gint_par(10, vec![], false), new_gint_par(20, vec![], false)];
        let first = new_boundvar_par(1, vec![], false);
        let second = new_boundvar_par(0, vec![], false);
        assert!(std::ptr::eq(capture(&first, &values).unwrap(), &values[0]));
        assert!(std::ptr::eq(capture(&second, &values).unwrap(), &values[1]));
        assert!(std::ptr::eq(
            capture(&first, &values).unwrap(),
            capture(&first, &values).unwrap()
        ));
        assert!(capture(&new_boundvar_par(2, vec![], false), &values).is_err());
        let opaque = wire_list(vec![first]);
        assert!(std::ptr::eq(capture(&opaque, &values).unwrap(), &opaque));
    }
}
