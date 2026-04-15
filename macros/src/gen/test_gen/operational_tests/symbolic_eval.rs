//! Symbolic evaluator for `syn::Expr` at macro expansion time.
//!
//! Interprets the Rust code from `![...]` blocks to compute expected values
//! for operational semantics tests. Uses an iterative work-stack to avoid
//! call-stack recursion.
//!
//! Returns `None` when the expression is too complex to evaluate at macro time,
//! falling back to smoke tests in the test generator.

use std::collections::HashMap;

/// Symbolic values produced by the evaluator.
#[derive(Debug, Clone, PartialEq)]
pub enum SymValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    /// Value that cannot be determined at macro time.
    #[allow(dead_code)]
    Unknown,
}

impl SymValue {
    /// Convert to a display string appropriate for a given native type.
    /// For example, `SymValue::Int(3)` with native type "i32" produces "3".
    pub fn to_display_string(&self, native_type: &str) -> Option<String> {
        match (self, native_type) {
            (SymValue::Int(v), "i32" | "i64" | "u32" | "u64" | "isize" | "usize") => {
                Some(format!("{}", v))
            },
            (SymValue::Float(v), "f32" | "f64") => {
                // Format float to match Rust's default Display behavior
                let s = format!("{}", v);
                // Ensure there's a decimal point for float display
                if s.contains('.') || s.contains('E') || s.contains('e') || s == "NaN" || s == "inf" || s == "-inf" {
                    Some(s)
                } else {
                    Some(format!("{}.0", s))
                }
            },
            (SymValue::Bool(v), "bool") => Some(format!("{}", v)),
            (SymValue::Str(v), "str" | "String") => Some(format!("\"{}\"", v)),
            (SymValue::Unknown, _) => None,
            _ => None,
        }
    }
}

/// Evaluate a `syn::Expr` with the given environment.
///
/// Uses an iterative work-stack (trampoline) to avoid call-stack recursion.
/// Returns `None` when the expression cannot be evaluated at macro time.
pub fn symbolic_eval(
    expr: &syn::Expr,
    env: &HashMap<String, SymValue>,
) -> Option<SymValue> {
    // We use a continuation-passing trampoline.
    // Each work item is either:
    //   Eval(expr_index) — evaluate the expression at this index
    //   Apply(op) — apply an operation to values on the value stack
    //
    // Expressions are stored in a flat arena to avoid recursive references.

    // For simplicity and correctness, we use a two-stack approach:
    // - work_stack: operations to perform
    // - value_stack: intermediate results

    enum WorkItem<'a> {
        Eval(&'a syn::Expr),
        ApplyBinary(syn::BinOp),
        ApplyUnary(syn::UnOp),
        ApplyMethodCall(String, usize), // method name, arg count (excluding receiver)
        ApplyCast(String),              // target type string
        #[allow(dead_code)]
        ApplyIf,                        // condition evaluated, then need to eval branch
        #[allow(dead_code)]
        EvalIfBranch(&'a syn::Expr, Option<&'a syn::Expr>), // then_branch, else_branch
        #[allow(dead_code)]
        ApplyBlock,                     // block result
    }

    let mut work_stack: Vec<WorkItem> = Vec::with_capacity(16);
    let mut value_stack: Vec<Option<SymValue>> = Vec::with_capacity(16);

    work_stack.push(WorkItem::Eval(expr));

    while let Some(item) = work_stack.pop() {
        match item {
            WorkItem::Eval(e) => {
                match e {
                    syn::Expr::Lit(lit) => {
                        let val = eval_lit(&lit.lit);
                        value_stack.push(val);
                    },
                    syn::Expr::Path(path) => {
                        // Variable lookup
                        if let Some(ident) = path.path.get_ident() {
                            let name = ident.to_string();
                            if let Some(val) = env.get(&name) {
                                value_stack.push(Some(val.clone()));
                            } else {
                                // Could be a bool literal: true/false
                                match name.as_str() {
                                    "true" => value_stack.push(Some(SymValue::Bool(true))),
                                    "false" => value_stack.push(Some(SymValue::Bool(false))),
                                    _ => value_stack.push(None),
                                }
                            }
                        } else {
                            value_stack.push(None);
                        }
                    },
                    syn::Expr::Binary(bin) => {
                        // Push: first eval right, then eval left, then apply op
                        // (stack is LIFO so push in reverse order)
                        work_stack.push(WorkItem::ApplyBinary(bin.op.clone()));
                        work_stack.push(WorkItem::Eval(&bin.left));
                        work_stack.push(WorkItem::Eval(&bin.right));
                    },
                    syn::Expr::Unary(un) => {
                        work_stack.push(WorkItem::ApplyUnary(un.op.clone()));
                        work_stack.push(WorkItem::Eval(&un.expr));
                    },
                    syn::Expr::Paren(paren) => {
                        work_stack.push(WorkItem::Eval(&paren.expr));
                    },
                    syn::Expr::Group(group) => {
                        work_stack.push(WorkItem::Eval(&group.expr));
                    },
                    syn::Expr::MethodCall(mc) => {
                        let method_name = mc.method.to_string();
                        let arg_count = mc.args.len();

                        // Work stack is LIFO. We want:
                        //   1. Args evaluated first → their values at bottom of value_stack
                        //   2. Receiver evaluated last → its value on top of value_stack
                        //   3. ApplyMethodCall pops receiver (top), then pops args
                        //
                        // Push to work_stack in reverse execution order:
                        //   - ApplyMethodCall first (deepest, runs last)
                        //   - Receiver second (runs second-to-last)
                        //   - Args last (on top, run first)
                        work_stack.push(WorkItem::ApplyMethodCall(method_name, arg_count));
                        work_stack.push(WorkItem::Eval(&mc.receiver));
                        // Push args in forward order so they're evaluated in reverse,
                        // then reversed when popped from value_stack
                        for arg in mc.args.iter().rev() {
                            work_stack.push(WorkItem::Eval(arg));
                        }
                    },
                    syn::Expr::Block(block) => {
                        // Evaluate the last expression in the block
                        if let Some(last_stmt) = block.block.stmts.last() {
                            match last_stmt {
                                syn::Stmt::Expr(expr, _) => {
                                    work_stack.push(WorkItem::Eval(expr));
                                },
                                _ => {
                                    // Block with non-expression last statement — can't eval
                                    value_stack.push(None);
                                },
                            }
                        } else {
                            value_stack.push(None);
                        }
                    },
                    syn::Expr::If(if_expr) => {
                        // First evaluate the condition
                        let then_branch_expr = if_expr.then_branch.stmts.last().and_then(|s| {
                            match s {
                                syn::Stmt::Expr(e, _) => Some(e),
                                _ => None,
                            }
                        });
                        let else_branch_expr = if_expr.else_branch.as_ref().and_then(|(_, e)| {
                            Some(e.as_ref())
                        });

                        work_stack.push(WorkItem::EvalIfBranch(
                            // We need to pass the original if_expr branches
                            // This is tricky with lifetime-safe iteration.
                            // Use a simpler approach: evaluate condition, then decide.
                            &if_expr.cond,
                            None,
                        ));

                        // Actually, let's just try to evaluate the condition synchronously
                        // using a nested call through the trampoline. Since if-expressions
                        // can be complex, we handle this specially:
                        // We push EvalIfBranch which will evaluate condition result
                        // and then push the appropriate branch.
                        // But we need the condition to be evaluated first.

                        // Simplified approach: push condition eval, then ApplyIf
                        // which will pop the condition value and decide what to push next.
                        // But ApplyIf needs the branch bodies... we store them as part of
                        // the work item.

                        // Clear the work items we just pushed and use a different approach
                        work_stack.pop(); // remove the EvalIfBranch we just pushed

                        // Evaluate condition inline (since we can't store borrows easily)
                        let cond_val = symbolic_eval(&if_expr.cond, env);
                        match cond_val {
                            Some(SymValue::Bool(true)) => {
                                if let Some(then_expr) = then_branch_expr {
                                    work_stack.push(WorkItem::Eval(then_expr));
                                } else {
                                    value_stack.push(None);
                                }
                            },
                            Some(SymValue::Bool(false)) => {
                                if let Some(else_expr) = else_branch_expr {
                                    work_stack.push(WorkItem::Eval(else_expr));
                                } else {
                                    value_stack.push(None);
                                }
                            },
                            Some(SymValue::Int(v)) => {
                                // C-style: nonzero is truthy
                                if v != 0 {
                                    if let Some(then_expr) = then_branch_expr {
                                        work_stack.push(WorkItem::Eval(then_expr));
                                    } else {
                                        value_stack.push(None);
                                    }
                                } else if let Some(else_expr) = else_branch_expr {
                                    work_stack.push(WorkItem::Eval(else_expr));
                                } else {
                                    value_stack.push(None);
                                }
                            },
                            _ => {
                                value_stack.push(None);
                            },
                        }
                    },
                    syn::Expr::Cast(cast) => {
                        // Extract the target type
                        let target_type = type_to_string(&cast.ty);
                        work_stack.push(WorkItem::ApplyCast(target_type));
                        work_stack.push(WorkItem::Eval(&cast.expr));
                    },
                    syn::Expr::Match(_) => {
                        // Match expressions in rust_code are too complex to evaluate
                        // symbolically at macro time. Fall back to smoke test.
                        value_stack.push(None);
                    },
                    syn::Expr::Closure(_) => {
                        value_stack.push(None);
                    },
                    syn::Expr::Call(_) => {
                        // Handle simple cases like String::from(...) or things like product::<i32>()
                        value_stack.push(None);
                    },
                    syn::Expr::Index(_) | syn::Expr::Field(_) | syn::Expr::Tuple(_) => {
                        value_stack.push(None);
                    },
                    syn::Expr::Reference(ref_expr) => {
                        // &expr — just evaluate the inner expression
                        work_stack.push(WorkItem::Eval(&ref_expr.expr));
                    },
                    syn::Expr::Array(_) => {
                        // Array literal — can't evaluate meaningfully for our purposes
                        value_stack.push(None);
                    },
                    _ => {
                        // Anything else — can't evaluate at macro time
                        value_stack.push(None);
                    },
                }
            },

            WorkItem::ApplyBinary(op) => {
                // Pop right then left (they were pushed: right first, then left)
                // After eval: left is on top, right is below
                let left = value_stack.pop().unwrap_or(None);
                let right = value_stack.pop().unwrap_or(None);
                let result = apply_binary_op(&op, left, right);
                value_stack.push(result);
            },

            WorkItem::ApplyUnary(op) => {
                let operand = value_stack.pop().unwrap_or(None);
                let result = apply_unary_op(&op, operand);
                value_stack.push(result);
            },

            WorkItem::ApplyMethodCall(method_name, arg_count) => {
                // Value stack layout (top to bottom): receiver, arg[n-1], ..., arg[0]
                // Receiver was evaluated last → on top
                let receiver = value_stack.pop().unwrap_or(None);
                // Args were evaluated first → below receiver
                // They were pushed in reverse eval order, so popping gives them
                // in forward order (arg[0] first)
                let mut args = Vec::with_capacity(arg_count);
                for _ in 0..arg_count {
                    args.push(value_stack.pop().unwrap_or(None));
                }
                // args are now in reverse order (last arg first), so reverse them
                args.reverse();
                let result = apply_method_call(&method_name, receiver, &args);
                value_stack.push(result);
            },

            WorkItem::ApplyCast(target_type) => {
                let val = value_stack.pop().unwrap_or(None);
                let result = apply_cast(val, &target_type);
                value_stack.push(result);
            },

            WorkItem::ApplyIf | WorkItem::EvalIfBranch(_, _) | WorkItem::ApplyBlock => {
                // These are handled inline above; shouldn't reach here normally
                value_stack.push(None);
            },
        }
    }

    // The final result should be on top of the value stack
    value_stack.pop().unwrap_or(None)
}

/// Evaluate a literal value.
fn eval_lit(lit: &syn::Lit) -> Option<SymValue> {
    match lit {
        syn::Lit::Int(i) => {
            i.base10_parse::<i64>().ok().map(SymValue::Int)
        },
        syn::Lit::Float(f) => {
            f.base10_parse::<f64>().ok().map(SymValue::Float)
        },
        syn::Lit::Bool(b) => {
            Some(SymValue::Bool(b.value))
        },
        syn::Lit::Str(s) => {
            Some(SymValue::Str(s.value()))
        },
        _ => None,
    }
}

/// Apply a binary operator to two symbolic values.
fn apply_binary_op(
    op: &syn::BinOp,
    left: Option<SymValue>,
    right: Option<SymValue>,
) -> Option<SymValue> {
    let l = left?;
    let r = right?;

    match op {
        syn::BinOp::Add(_) | syn::BinOp::AddAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a.wrapping_add(*b))),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Float(a + b)),
            (SymValue::Str(a), SymValue::Str(b)) => {
                let mut s = a.clone();
                s.push_str(b);
                Some(SymValue::Str(s))
            },
            _ => None,
        },
        syn::BinOp::Sub(_) | syn::BinOp::SubAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a.wrapping_sub(*b))),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Float(a - b)),
            _ => None,
        },
        syn::BinOp::Mul(_) | syn::BinOp::MulAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a.wrapping_mul(*b))),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Float(a * b)),
            _ => None,
        },
        syn::BinOp::Div(_) | syn::BinOp::DivAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => {
                if *b == 0 { None } else { Some(SymValue::Int(a / b)) }
            },
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Float(a / b)),
            _ => None,
        },
        syn::BinOp::Rem(_) | syn::BinOp::RemAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => {
                if *b == 0 { None } else { Some(SymValue::Int(a % b)) }
            },
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Float(a % b)),
            _ => None,
        },
        syn::BinOp::And(_) => match (&l, &r) {
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(*a && *b)),
            _ => None,
        },
        syn::BinOp::Or(_) => match (&l, &r) {
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(*a || *b)),
            _ => None,
        },
        syn::BinOp::BitAnd(_) | syn::BinOp::BitAndAssign(_) => match (&l, &r) {
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(*a & *b)),
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a & b)),
            _ => None,
        },
        syn::BinOp::BitOr(_) | syn::BinOp::BitOrAssign(_) => match (&l, &r) {
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(*a | *b)),
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a | b)),
            _ => None,
        },
        syn::BinOp::BitXor(_) | syn::BinOp::BitXorAssign(_) => match (&l, &r) {
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(*a ^ *b)),
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Int(a ^ b)),
            _ => None,
        },
        syn::BinOp::Eq(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a == b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a == b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a == b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a == b)),
            _ => None,
        },
        syn::BinOp::Ne(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a != b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a != b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a != b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a != b)),
            _ => None,
        },
        syn::BinOp::Lt(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a < b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a < b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a < b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a < b)),
            _ => None,
        },
        syn::BinOp::Gt(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a > b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a > b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a > b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a > b)),
            _ => None,
        },
        syn::BinOp::Le(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a <= b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a <= b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a <= b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a <= b)),
            _ => None,
        },
        syn::BinOp::Ge(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => Some(SymValue::Bool(a >= b)),
            (SymValue::Float(a), SymValue::Float(b)) => Some(SymValue::Bool(a >= b)),
            (SymValue::Bool(a), SymValue::Bool(b)) => Some(SymValue::Bool(a >= b)),
            (SymValue::Str(a), SymValue::Str(b)) => Some(SymValue::Bool(a >= b)),
            _ => None,
        },
        syn::BinOp::Shl(_) | syn::BinOp::ShlAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => {
                if *b >= 0 && *b < 64 {
                    Some(SymValue::Int(a.wrapping_shl(*b as u32)))
                } else {
                    None
                }
            },
            _ => None,
        },
        syn::BinOp::Shr(_) | syn::BinOp::ShrAssign(_) => match (&l, &r) {
            (SymValue::Int(a), SymValue::Int(b)) => {
                if *b >= 0 && *b < 64 {
                    Some(SymValue::Int(a.wrapping_shr(*b as u32)))
                } else {
                    None
                }
            },
            _ => None,
        },
        _ => None,
    }
}

/// Apply a unary operator to a symbolic value.
fn apply_unary_op(
    op: &syn::UnOp,
    operand: Option<SymValue>,
) -> Option<SymValue> {
    let v = operand?;
    match op {
        syn::UnOp::Neg(_) => match &v {
            SymValue::Int(i) => Some(SymValue::Int(-i)),
            SymValue::Float(f) => Some(SymValue::Float(-f)),
            _ => None,
        },
        syn::UnOp::Not(_) => match &v {
            SymValue::Bool(b) => Some(SymValue::Bool(!b)),
            SymValue::Int(i) => Some(SymValue::Int(!i)),
            _ => None,
        },
        syn::UnOp::Deref(_) => {
            // Dereferencing — pass through
            Some(v)
        },
        _ => None,
    }
}

/// Apply a method call to a symbolic receiver.
fn apply_method_call(
    method_name: &str,
    receiver: Option<SymValue>,
    args: &[Option<SymValue>],
) -> Option<SymValue> {
    let recv = receiver?;

    match (method_name, &recv) {
        ("pow", SymValue::Int(base)) => {
            if let Some(Some(SymValue::Int(exp))) = args.first() {
                if *exp >= 0 && *exp <= 32 {
                    Some(SymValue::Int((*base as i64).wrapping_pow(*exp as u32)))
                } else {
                    None
                }
            } else {
                None
            }
        },
        ("powf", SymValue::Float(base)) => {
            if let Some(Some(SymValue::Float(exp))) = args.first() {
                Some(SymValue::Float(base.powf(*exp)))
            } else {
                None
            }
        },
        ("sin", SymValue::Float(v)) => Some(SymValue::Float(v.sin())),
        ("cos", SymValue::Float(v)) => Some(SymValue::Float(v.cos())),
        ("exp", SymValue::Float(v)) => Some(SymValue::Float(v.exp())),
        ("ln", SymValue::Float(v)) => Some(SymValue::Float(v.ln())),
        ("sqrt", SymValue::Float(v)) => Some(SymValue::Float(v.sqrt())),
        ("abs", SymValue::Int(v)) => Some(SymValue::Int(v.abs())),
        ("abs", SymValue::Float(v)) => Some(SymValue::Float(v.abs())),
        ("len", SymValue::Str(s)) => Some(SymValue::Int(s.len() as i64)),
        ("to_string", v) => match v {
            SymValue::Int(i) => Some(SymValue::Str(format!("{}", i))),
            SymValue::Float(f) => Some(SymValue::Str(format!("{}", f))),
            SymValue::Bool(b) => Some(SymValue::Str(format!("{}", b))),
            SymValue::Str(s) => Some(SymValue::Str(s.clone())),
            SymValue::Unknown => None,
        },
        ("parse", SymValue::Str(s)) => {
            // Try to parse as various types — this is best-effort
            if let Ok(v) = s.parse::<i64>() {
                Some(SymValue::Int(v))
            } else if let Ok(v) = s.parse::<f64>() {
                Some(SymValue::Float(v))
            } else if let Ok(v) = s.parse::<bool>() {
                Some(SymValue::Bool(v))
            } else {
                None
            }
        },
        ("unwrap_or", _) => {
            // For parse().unwrap_or(default) chains — too complex, bail
            None
        },
        ("max", SymValue::Int(a)) => {
            if let Some(Some(SymValue::Int(b))) = args.first() {
                Some(SymValue::Int((*a).max(*b)))
            } else {
                None
            }
        },
        ("min", SymValue::Int(a)) => {
            if let Some(Some(SymValue::Int(b))) = args.first() {
                Some(SymValue::Int((*a).min(*b)))
            } else {
                None
            }
        },
        ("max", SymValue::Float(a)) => {
            if let Some(Some(SymValue::Float(b))) = args.first() {
                Some(SymValue::Float(a.max(*b)))
            } else {
                None
            }
        },
        ("min", SymValue::Float(a)) => {
            if let Some(Some(SymValue::Float(b))) = args.first() {
                Some(SymValue::Float(a.min(*b)))
            } else {
                None
            }
        },
        ("clone", v) => Some(v.clone()),
        ("get", SymValue::Float(v)) => {
            // CanonicalFloat64::get() returns the inner f64
            Some(SymValue::Float(*v))
        },
        ("push_str", SymValue::Str(_)) => {
            // Mutation — can't handle symbolically
            None
        },
        ("concat", _) => {
            // Array/slice method — too complex
            None
        },
        ("product", _) => {
            // Iterator method — too complex
            None
        },
        _ => None,
    }
}

/// Apply a type cast to a symbolic value.
fn apply_cast(val: Option<SymValue>, target_type: &str) -> Option<SymValue> {
    let v = val?;
    match (target_type, &v) {
        ("i32", SymValue::Int(i)) => Some(SymValue::Int(*i as i32 as i64)),
        ("i64", SymValue::Int(i)) => Some(SymValue::Int(*i)),
        ("u32", SymValue::Int(i)) => Some(SymValue::Int(*i as u32 as i64)),
        ("u64", SymValue::Int(i)) => Some(SymValue::Int(*i as u64 as i64)),
        ("f32", SymValue::Int(i)) => Some(SymValue::Float(*i as f32 as f64)),
        ("f64", SymValue::Int(i)) => Some(SymValue::Float(*i as f64)),
        ("f32", SymValue::Float(f)) => Some(SymValue::Float(*f as f32 as f64)),
        ("f64", SymValue::Float(f)) => Some(SymValue::Float(*f)),
        ("i32", SymValue::Float(f)) => Some(SymValue::Int(*f as i32 as i64)),
        ("i64", SymValue::Float(f)) => Some(SymValue::Int(*f as i64)),
        ("u32", SymValue::Float(f)) => Some(SymValue::Int(*f as u32 as i64)),
        ("u64", SymValue::Float(f)) => Some(SymValue::Int(*f as u64 as i64)),
        ("i32", SymValue::Bool(b)) => Some(SymValue::Int(if *b { 1 } else { 0 })),
        ("i64", SymValue::Bool(b)) => Some(SymValue::Int(if *b { 1 } else { 0 })),
        _ => None,
    }
}

/// Convert a syn::Type to a simple type string for cast handling.
fn type_to_string(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Path(p) => {
            if let Some(seg) = p.path.segments.last() {
                seg.ident.to_string()
            } else {
                String::new()
            }
        },
        _ => String::new(),
    }
}
