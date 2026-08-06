//! Bounded recursive references for the grammar-shape expression walkers.
//!
//! Production uses loops or an explicit worklist. These superseded equations run only on a shallow
//! corpus; the production implementations alone exercise the 20,000-level small-stack gate.

use super::*;
use quote::ToTokens;

fn bare_param_wrap_name_recursive(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Call(call) if is_smart_ptr_new(&call.func) && call.args.len() == 1 => {
            bare_param_wrap_name_recursive(&call.args[0])
        },
        syn::Expr::MethodCall(call) if call.method == "clone" && call.args.is_empty() => {
            bare_param_wrap_name_recursive(&call.receiver)
        },
        syn::Expr::Reference(reference) => bare_param_wrap_name_recursive(&reference.expr),
        syn::Expr::Paren(paren) => bare_param_wrap_name_recursive(&paren.expr),
        syn::Expr::Group(group) => bare_param_wrap_name_recursive(&group.expr),
        syn::Expr::Path(path) if path.path.segments.len() == 1 && path.qself.is_none() => {
            Some(path.path.segments[0].ident.to_string())
        },
        _ => None,
    }
}

fn unwrap_single_expr_recursive(expr: &syn::Expr) -> Option<&syn::Expr> {
    match expr {
        syn::Expr::Block(block) if block.block.stmts.len() == 1 => match &block.block.stmts[0] {
            syn::Stmt::Expr(inner, None) => unwrap_single_expr_recursive(inner),
            _ => None,
        },
        syn::Expr::Paren(paren) => unwrap_single_expr_recursive(&paren.expr),
        syn::Expr::Group(group) => unwrap_single_expr_recursive(&group.expr),
        other => Some(other),
    }
}

fn is_param_ref_recursive(expr: &syn::Expr, params: &HashSet<String>) -> bool {
    match expr {
        syn::Expr::Path(path) => is_single_ident_in(&path.path, params),
        syn::Expr::Paren(paren) => is_param_ref_recursive(&paren.expr, params),
        syn::Expr::Group(group) => is_param_ref_recursive(&group.expr, params),
        _ => false,
    }
}

fn is_fold_alias_node_recursive(expr: &syn::Expr, params: &HashSet<String>) -> bool {
    match expr {
        syn::Expr::Call(call) => {
            if is_smart_ptr_new(&call.func) {
                return call.args.len() == 1 && is_fold_alias_node_recursive(&call.args[0], params);
            }
            if constructor_path(&call.func).is_some() {
                return call
                    .args
                    .iter()
                    .all(|arg| is_fold_alias_node_recursive(arg, params));
            }
            false
        },
        syn::Expr::MethodCall(call) => {
            call.method == "clone"
                && call.args.is_empty()
                && is_param_ref_recursive(&call.receiver, params)
        },
        syn::Expr::Path(path) => {
            is_nullary_variant_path(&path.path) || is_single_ident_in(&path.path, params)
        },
        syn::Expr::Paren(paren) => is_fold_alias_node_recursive(&paren.expr, params),
        syn::Expr::Group(group) => is_fold_alias_node_recursive(&group.expr, params),
        _ => false,
    }
}

fn block_tail_expr_recursive(expr: &syn::Expr) -> Option<&syn::Expr> {
    match expr {
        syn::Expr::Block(block) => match block.block.stmts.last()? {
            syn::Stmt::Expr(inner, None) => block_tail_expr_recursive(inner),
            _ => None,
        },
        syn::Expr::Paren(paren) => block_tail_expr_recursive(&paren.expr),
        syn::Expr::Group(group) => block_tail_expr_recursive(&group.expr),
        other => Some(other),
    }
}

fn channel_wrap_leaf_param_recursive(expr: &syn::Expr, params: &HashSet<String>) -> Option<String> {
    match expr {
        syn::Expr::Call(call) => {
            if is_smart_ptr_new(&call.func) || constructor_path(&call.func).is_some() {
                if call.args.len() == 1 {
                    return channel_wrap_leaf_param_recursive(&call.args[0], params);
                }
                return None;
            }
            None
        },
        syn::Expr::MethodCall(call) => {
            if call.method == "clone"
                && call.args.is_empty()
                && is_param_ref_recursive(&call.receiver, params)
            {
                if let syn::Expr::Path(path) = &*call.receiver {
                    return path.path.get_ident().map(ToString::to_string);
                }
            }
            None
        },
        syn::Expr::Path(path) => path
            .path
            .get_ident()
            .map(ToString::to_string)
            .filter(|name| params.contains(name)),
        syn::Expr::Paren(paren) => channel_wrap_leaf_param_recursive(&paren.expr, params),
        syn::Expr::Group(group) => channel_wrap_leaf_param_recursive(&group.expr, params),
        _ => None,
    }
}

fn channel_wrap_has_constructor_recursive(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Call(call) => {
            if is_smart_ptr_new(&call.func) {
                return call.args.len() == 1
                    && channel_wrap_has_constructor_recursive(&call.args[0]);
            }
            constructor_path(&call.func).is_some()
        },
        syn::Expr::Paren(paren) => channel_wrap_has_constructor_recursive(&paren.expr),
        syn::Expr::Group(group) => channel_wrap_has_constructor_recursive(&group.expr),
        _ => false,
    }
}

fn rendered(expr: Option<&syn::Expr>) -> Option<String> {
    expr.map(|expr| expr.to_token_stream().to_string())
}

#[test]
fn grammar_shape_walkers_match_the_bounded_recursive_equations() {
    let params = HashSet::from(["p".to_string(), "q".to_string()]);
    let corpus: Vec<syn::Expr> = vec![
        syn::parse_quote!(p),
        syn::parse_quote!((p.clone())),
        syn::parse_quote!(&std::sync::Arc::new(p.clone())),
        syn::parse_quote!(Proc::Pair(std::sync::Arc::new(p.clone()), Proc::PZero)),
        syn::parse_quote!(some_free_function(p)),
        syn::parse_quote!({ Proc::Wrap(p.clone()) }),
        syn::parse_quote!({
            let x = p;
            Proc::Wrap(x)
        }),
        syn::parse_quote!(std::sync::Arc::new(Name::NQuote(std::sync::Arc::new(p.clone())))),
    ];

    for (index, expr) in corpus.iter().enumerate() {
        assert_eq!(
            bare_param_wrap_name(expr),
            bare_param_wrap_name_recursive(expr),
            "bare wrapper item {index}",
        );
        assert_eq!(
            rendered(unwrap_single_expr(expr)),
            rendered(unwrap_single_expr_recursive(expr)),
            "single-expression item {index}",
        );
        assert_eq!(
            is_param_ref(expr, &params),
            is_param_ref_recursive(expr, &params),
            "parameter reference item {index}",
        );
        assert_eq!(
            is_fold_alias_node(expr, &params),
            is_fold_alias_node_recursive(expr, &params),
            "fold alias item {index}",
        );
        assert_eq!(
            rendered(block_tail_expr(expr)),
            rendered(block_tail_expr_recursive(expr)),
            "block tail item {index}",
        );
        assert_eq!(
            channel_wrap_leaf_param(expr, &params),
            channel_wrap_leaf_param_recursive(expr, &params),
            "channel leaf item {index}",
        );
        assert_eq!(
            channel_wrap_has_constructor(expr),
            channel_wrap_has_constructor_recursive(expr),
            "channel constructor item {index}",
        );
    }
}

#[test]
fn grammar_shape_walkers_are_stack_safe_at_depth_20k() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("grammar-shape-walkers-256k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut expr: syn::Expr = syn::parse_quote!(p);
            for _ in 0..DEPTH {
                expr = syn::Expr::Paren(syn::ExprParen {
                    attrs: Vec::new(),
                    paren_token: syn::token::Paren::default(),
                    expr: Box::new(expr),
                });
            }
            let params = HashSet::from(["p".to_string()]);
            assert_eq!(bare_param_wrap_name(&expr).as_deref(), Some("p"));
            assert!(matches!(unwrap_single_expr(&expr), Some(syn::Expr::Path(_))));
            assert!(is_param_ref(&expr, &params));
            assert!(is_fold_alias_node(&expr, &params));
            assert!(matches!(block_tail_expr(&expr), Some(syn::Expr::Path(_))));
            assert_eq!(channel_wrap_leaf_param(&expr, &params).as_deref(), Some("p"));
            assert!(!channel_wrap_has_constructor(&expr));

            // `syn::Expr` itself has recursive ownership; the campaign's generated lifecycle
            // work does not control this third-party test fixture's destructor.
            std::mem::forget(expr);
        })
        .expect("spawn grammar-shape depth gate")
        .join()
        .expect("grammar-shape walkers must not overflow or panic");
}
