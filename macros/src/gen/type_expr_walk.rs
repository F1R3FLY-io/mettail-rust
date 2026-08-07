use mettail_ast::types::TypeExpr;

/// Return the terminal base category reached through the payload-bearing arm
/// of a type expression without consuming native stack in type nesting depth.
pub(crate) fn terminal_base(ty: &TypeExpr) -> &syn::Ident {
    let mut current = ty;
    loop {
        current = match current {
            TypeExpr::Base(ident) => return ident,
            TypeExpr::Collection { element, .. } => element,
            TypeExpr::Arrow { codomain, .. } => codomain,
            TypeExpr::MultiBinder(inner) => inner,
            TypeExpr::Refined { base, .. } => base,
            TypeExpr::Map { value, .. } => value,
        };
    }
}

#[cfg(test)]
#[path = "../../tests/support/type_expr_walk_recursive_oracle.rs"]
mod recursive_oracle;
