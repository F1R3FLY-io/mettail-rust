use mettail_ast::types::TypeExpr;

/// Borrowed declaration-order traversal over every base category in a type
/// expression. Binary arms visit their left payload before their right payload,
/// matching the recursive source equation without consuming native stack in
/// type nesting depth.
pub(crate) struct TypeExprBaseIdents<'a> {
    work: Vec<&'a TypeExpr>,
}

impl<'a> TypeExprBaseIdents<'a> {
    pub(crate) fn new(ty: &'a TypeExpr) -> Self {
        Self { work: vec![ty] }
    }
}

impl<'a> Iterator for TypeExprBaseIdents<'a> {
    type Item = &'a syn::Ident;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(ty) = self.work.pop() {
            match ty {
                TypeExpr::Base(ident) => return Some(ident),
                TypeExpr::Arrow { domain, codomain } => {
                    self.work.push(codomain);
                    self.work.push(domain);
                },
                TypeExpr::MultiBinder(inner) => self.work.push(inner),
                TypeExpr::Collection { element, .. } => self.work.push(element),
                TypeExpr::Refined { base, .. } => self.work.push(base),
                TypeExpr::Map { key, value } => {
                    self.work.push(value);
                    self.work.push(key);
                },
            }
        }
        None
    }
}

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
