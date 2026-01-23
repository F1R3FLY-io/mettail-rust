use syn::Ident;

use super::types::{TypeExpr, TypeContext, TypeError};

/// Type alias for backward compatibility
// pub type Expr = Term;

/// Term expression in the meta-language
/// 
/// Represents both object-level syntax and meta-level operations.
/// Used in equations and rewrites for pattern matching and construction.
#[derive(Clone, Debug)]
pub enum Term {
    Var(Ident),
    Apply {
        constructor: Ident,
        args: Vec<Term>,
    },
    /// Substitution: subst(term, var, replacement)
    /// Represents term[replacement/var] - substitute replacement for var in term
    Subst {
        term: Box<Term>,
        var: Ident,
        replacement: Box<Term>,
    },
    /// Multi-substitution: multisubst(scope, r0, r1, ...)
    /// Applies a multi-binder scope to replacement terms
    /// scope: Term that evaluates to Scope<Vec<Binder>, Box<Body>>
    /// replacements: Individual replacement terms (same count as binders)
    /// Result: body with all binders simultaneously substituted
    MultiSubst {
        /// The scope term (multi-lambda or variable bound to one)
        scope: Box<Term>,
        /// Individual replacement terms
        replacements: Vec<Term>,
    },
    // NOTE: CollectionConstruct has been removed.
    // Collection syntax like {P, Q, ...rest} is now Pattern::Collection,
    // which is rule specification, not object-language.
    // Runtime collections use HashBag<T> directly.
    
    /// Lambda abstraction: \x.body
    /// Meta-level function for use in definitions and term contexts
    /// Type annotation is external: \x.body:[A -> B]
    Lambda {
        /// Bound variable name
        binder: Ident,
        /// Lambda body
        body: Box<Term>,
    },
    /// Multi-binder lambda: ^[x0, x1, ...].body
    /// Binds a list of variables simultaneously
    MultiLambda {
        /// Bound variable names
        binders: Vec<Ident>,
        /// Lambda body
        body: Box<Term>,
    },
}

impl Term {
    /// Collect free variables in this expression
    pub fn free_vars(&self) -> std::collections::HashSet<String> {
        use std::collections::HashSet;
        
        match self {
            Term::Var(v) => {
                let mut set = HashSet::new();
                set.insert(v.to_string());
                set
            }
            Term::Apply { args, .. } => {
                let mut vars = HashSet::new();
                for arg in args {
                    vars.extend(arg.free_vars());
                }
                vars
            }
            Term::Subst { term, var, replacement } => {
                let mut vars = term.free_vars();
                vars.insert(var.to_string()); // The substitution variable is referenced
                vars.extend(replacement.free_vars());
                vars
            }
            Term::Lambda { binder, body } => {
                let mut vars = body.free_vars();
                vars.remove(&binder.to_string()); // binder is bound, not free
                vars
            }
            Term::MultiLambda { binders, body } => {
                let mut vars = body.free_vars();
                // Remove all bound variables
                for binder in binders {
                    vars.remove(&binder.to_string());
                }
                vars
            }
            Term::MultiSubst { scope, replacements } => {
                let mut vars = scope.free_vars();
                // Collect free vars from each replacement term
                for repl in replacements {
                    vars.extend(repl.free_vars());
                }
                vars
            }
        }
    }

    /// Capture-avoiding substitution: replace `var` with `replacement` in `self`
    /// 
    /// This handles:
    /// - Direct variable replacement
    /// - Shadowing (don't substitute in lambda body if binder matches var)
    /// - Capture detection (panic if replacement contains free var that would be captured)
    pub fn substitute(&self, var: &Ident, replacement: &Term) -> Term {
        let var_str = var.to_string();
        
        match self {
            Term::Var(v) => {
                if v.to_string() == var_str {
                    replacement.clone()
                } else {
                    Term::Var(v.clone())
                }
            }
            
            Term::Apply { constructor, args } => Term::Apply {
                constructor: constructor.clone(),
                args: args.iter().map(|a| a.substitute(var, replacement)).collect(),
            },
            
            Term::Subst { term, var: v, replacement: r } => Term::Subst {
                term: Box::new(term.substitute(var, replacement)),
                var: v.clone(),
                replacement: Box::new(r.substitute(var, replacement)),
            },
            
            Term::Lambda { binder, body } => {
                let binder_str = binder.to_string();
                
                if binder_str == var_str {
                    // Shadowed - binder hides var, don't substitute in body
                    self.clone()
                } else if replacement.free_vars().contains(&binder_str) {
                    // Would capture: replacement contains a free variable with same name as binder
                    // TODO: Implement alpha-renaming to handle this case
                    panic!(
                        "Capture-avoiding substitution: variable '{}' in replacement would be captured by binder '{}'",
                        binder_str, binder_str
                    )
                } else {
                    // Safe to substitute in body
                    Term::Lambda {
                        binder: binder.clone(),
                        body: Box::new(body.substitute(var, replacement)),
                    }
                }
            }
            
            Term::MultiLambda { binders, body } => {
                // Check if var is shadowed by any binder
                let binder_strs: Vec<String> = binders.iter().map(|b| b.to_string()).collect();
                
                if binder_strs.contains(&var_str) {
                    // Shadowed by one of the binders
                    self.clone()
                } else {
                    // Check for capture
                    let repl_free = replacement.free_vars();
                    for binder_str in &binder_strs {
                        if repl_free.contains(binder_str) {
                            panic!(
                                "Capture-avoiding substitution: variable '{}' in replacement would be captured by multi-binder '{}'",
                                binder_str, binder_str
                            );
                        }
                    }
                    Term::MultiLambda {
                        binders: binders.clone(),
                        body: Box::new(body.substitute(var, replacement)),
                    }
                }
            }
            
            Term::MultiSubst { scope, replacements } => {
                // Substitute in both scope and replacements
                Term::MultiSubst {
                    scope: Box::new(scope.substitute(var, replacement)),
                    replacements: replacements.iter()
                        .map(|r| r.substitute(var, replacement))
                        .collect(),
                }
            }
        }
    }
    
    /// Apply a lambda to an argument (beta reduction)
    /// Returns Err if self is not a lambda
    pub fn apply(&self, arg: &Term) -> Result<Term, String> {
        match self {
            Term::Lambda { binder, body } => {
                Ok(body.substitute(binder, arg))
            }
            Term::MultiLambda { binders, body } => {
                // Multi-lambda application requires multiple arguments
                // For now, only support single collective substitution
                if binders.len() == 1 {
                    Ok(body.substitute(&binders[0], arg))
                } else {
                    Err(format!(
                        "Cannot apply multi-lambda with {} binders to single argument",
                        binders.len()
                    ))
                }
            }
            _ => Err(format!("Cannot apply non-lambda expression: {:?}", self)),
        }
    }
}

impl Term {
    /// Infer the type of an expression given a type context
    /// 
    /// For lambdas, requires an expected type annotation since we don't store
    /// types in the Lambda itself.
    pub fn infer_type(&self, ctx: &TypeContext) -> Result<TypeExpr, TypeError> {
        match self {
            Term::Var(v) => {
                ctx.lookup(&v.to_string())
                    .cloned()
                    .ok_or_else(|| TypeError::UnboundVariable(v.to_string()))
            }
            
            Term::Apply { constructor, args } => {
                // Look up constructor signature
                if let Some(sig) = ctx.lookup_constructor(&constructor.to_string()) {
                    // Verify argument count matches
                    if args.len() != sig.arg_types.len() {
                        return Err(TypeError::CannotInfer(format!(
                            "Constructor {} expects {} arguments, got {}",
                            constructor, sig.arg_types.len(), args.len()
                        )));
                    }
                    // Type check each argument against expected type
                    for (arg, expected_type) in args.iter().zip(sig.arg_types.iter()) {
                        arg.check_type(expected_type, ctx)?;
                    }
                    // Return the result type
                    Ok(sig.result_type.clone())
                } else {
                    Err(TypeError::CannotInfer(format!(
                        "Constructor {} not found in context", 
                        constructor
                    )))
                }
            }
            
            Term::Lambda { .. } | Term::MultiLambda { .. } => {
                // Lambda types must be provided externally via annotation
                Err(TypeError::CannotInfer(
                    "Lambda types must be annotated: ^x.body:[A->B]".to_string()
                ))
            }
            
            Term::Subst { term, .. } => {
                // Substitution preserves the term's type
                term.infer_type(ctx)
            }
            
            Term::MultiSubst { .. } => {
                // MultiSubst produces the body type of the scope
                // Type cannot be inferred without knowing the scope's type
                Err(TypeError::CannotInfer(
                    "MultiSubst type depends on scope body type".to_string()
                ))
            }
        }
    }

    /// Check that this expression has a given type
    pub fn check_type(&self, expected: &TypeExpr, ctx: &TypeContext) -> Result<(), TypeError> {
        match (self, expected) {
            // Lambda checking: ^x.body : [A -> B] means body : B in context x:A
            (Term::Lambda { binder, body }, TypeExpr::Arrow { domain, codomain }) => {
                let extended_ctx = ctx.with_var(&binder.to_string(), (**domain).clone());
                body.check_type(codomain, &extended_ctx)
            }
            
            // MultiLambda checking: ^[x0,x1,...].body : [A* -> B]
            (Term::MultiLambda { binders, body }, TypeExpr::Arrow { domain, codomain }) => {
                match domain.as_ref() {
                    TypeExpr::MultiBinder(elem_type) => {
                        // Each binder has the element type
                        let mut extended_ctx = ctx.clone();
                        for binder in binders {
                            extended_ctx = extended_ctx.with_var(&binder.to_string(), (**elem_type).clone());
                        }
                        body.check_type(codomain, &extended_ctx)
                    }
                    _ => Err(TypeError::CannotInfer(format!(
                        "MultiLambda ^[...]._ requires a multi-binder domain type (T*), got {}",
                        domain
                    )))
                }
            }
            
            // For other cases, try to infer and compare
            _ => {
                let inferred = self.infer_type(ctx)?;
                if &inferred == expected {
                    Ok(())
                } else {
                    Err(TypeError::TypeMismatch {
                        expected: expected.clone(),
                        found: inferred,
                        context: format!("{:?}", self),
                    })
                }
            }
        }
    }

    /// Apply a typed lambda to an argument, checking types
    pub fn apply_typed(&self, arg: &Term, ctx: &TypeContext, func_type: &TypeExpr) -> Result<Term, TypeError> {
        match (self, func_type) {
            (Term::Lambda { binder, body }, TypeExpr::Arrow { domain, codomain: _ }) => {
                // Check arg has the domain type
                arg.check_type(domain, ctx)?;
                // Substitute arg for binder in body
                Ok(body.substitute(binder, arg))
            }
            (Term::Lambda { .. }, _) => {
                Err(TypeError::NotAFunction(func_type.clone()))
            }
            _ => {
                Err(TypeError::NotAFunction(func_type.clone()))
            }
        }
    }
}
