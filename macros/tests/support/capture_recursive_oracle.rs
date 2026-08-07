use super::*;

pub(super) fn push_declaration_order<'a>(
    term_context: &'a [TermParam],
    optional: bool,
    out: &mut Vec<FieldSlot<'a>>,
) {
    for param in term_context {
        match param {
            TermParam::Simple { name, .. } => out.push(FieldSlot {
                name: name.to_string(),
                source: FieldSlotSource::Param(param),
                optional,
            }),
            TermParam::GuardBody { name } => out.push(FieldSlot {
                name: name.to_string(),
                source: FieldSlotSource::Param(param),
                optional,
            }),
            TermParam::Abstraction { body, .. } | TermParam::MultiAbstraction { body, .. } => {
                out.push(FieldSlot {
                    name: body.to_string(),
                    source: FieldSlotSource::Param(param),
                    optional,
                });
            },
            TermParam::Optional { params } => push_declaration_order(params, true, out),
        }
    }
}

pub(super) fn find_param<'a>(
    term_context: &'a [TermParam],
    name: &str,
) -> Option<(&'a TermParam, bool)> {
    fn go<'a>(
        params: &'a [TermParam],
        name: &str,
        optional: bool,
    ) -> Option<(&'a TermParam, bool)> {
        for param in params {
            match param {
                TermParam::Simple { name: candidate, .. }
                | TermParam::GuardBody { name: candidate }
                    if candidate == name =>
                {
                    return Some((param, optional));
                },
                TermParam::Optional { params } => {
                    if let Some(found) = go(params, name, true) {
                        return Some(found);
                    }
                },
                _ => {},
            }
        }
        None
    }

    go(term_context, name, false)
}

pub(super) fn walk_pattern<'a>(
    exprs: &'a [SyntaxExpr],
    term_context: &'a [TermParam],
    abstraction_names: &HashSet<String>,
    optional: bool,
    out: &mut Vec<FieldSlot<'a>>,
) {
    for expr in exprs {
        match expr {
            SyntaxExpr::Literal(_) => {},
            SyntaxExpr::TokenKind { name, bind } => {
                let field_name = bind
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| format!("__tok_{name}"));
                out.push(FieldSlot {
                    name: field_name,
                    source: FieldSlotSource::TokenText,
                    optional,
                });
            },
            SyntaxExpr::Param(id) => {
                push_named_param(id.to_string(), term_context, abstraction_names, out);
            },
            SyntaxExpr::GuestBody { open, close, bind } => out.push(FieldSlot {
                name: bind.to_string(),
                source: FieldSlotSource::GuestBody { open, close },
                optional,
            }),
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                walk_pattern(inner, term_context, abstraction_names, true, out);
            },
            SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                push_named_param(collection.to_string(), term_context, abstraction_names, out);
            },
            SyntaxExpr::Op(PatternOp::Sep { source: Some(source), .. }) => {
                if let PatternOp::Map { source: zip, .. } = source.as_ref() {
                    if let PatternOp::Zip { left, .. } = zip.as_ref() {
                        push_named_param(left.to_string(), term_context, abstraction_names, out);
                    }
                }
            },
            SyntaxExpr::Op(PatternOp::Zip { .. } | PatternOp::Map { .. } | PatternOp::Var(_)) => {},
        }
    }
}
