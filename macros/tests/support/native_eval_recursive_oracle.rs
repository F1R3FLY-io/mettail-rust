use super::*;

pub(super) fn collect_native_dependencies(
    params: &[TermParam],
    native_index: &HashMap<String, usize>,
    out: &mut Vec<usize>,
) {
    for param in params {
        match param {
            TermParam::Simple { ty: TypeExpr::Base(target), .. } => {
                if let Some(&index) = native_index.get(&target.to_string()) {
                    out.push(index);
                }
            },
            TermParam::Optional { params } => {
                collect_native_dependencies(params, native_index, out);
            },
            _ => {},
        }
    }
}

pub(super) fn classify_term_params_for_pda(params: &[TermParam]) -> Option<Vec<PdaParam<'_>>> {
    fn collect<'a>(
        params: &'a [TermParam],
        in_opt: bool,
        out: &mut Vec<PdaParam<'a>>,
    ) -> Option<()> {
        for param in params {
            match param {
                TermParam::Simple { name, ty } => {
                    let TypeExpr::Base(base) = ty else {
                        return None;
                    };
                    out.push(PdaParam::Term {
                        name: name.clone(),
                        ty: base,
                        is_optional: in_opt,
                    });
                },
                TermParam::GuardBody { name } => {
                    out.push(PdaParam::Guard { name: name.clone() });
                },
                TermParam::Optional { params } => collect(params, true, out)?,
                TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => return None,
            }
        }
        Some(())
    }

    let mut out = Vec::with_capacity(params.len());
    collect(params, false, &mut out)?;
    Some(out)
}
