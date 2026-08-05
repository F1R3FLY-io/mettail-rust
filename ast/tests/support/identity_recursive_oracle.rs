use super::*;
use proc_macro2::{Delimiter, Ident, Span, TokenStream, TokenTree};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

fn recursive_type(ty: &TypeExpr, out: &mut String) {
    match ty {
        TypeExpr::Base(id) => {
            out.push_str("base(");
            push_ident(out, id);
            out.push(')');
        },
        TypeExpr::Arrow { domain, codomain } => {
            out.push_str("arrow(");
            recursive_type(domain, out);
            out.push(',');
            recursive_type(codomain, out);
            out.push(')');
        },
        TypeExpr::MultiBinder(inner) => {
            out.push_str("multi(");
            recursive_type(inner, out);
            out.push(')');
        },
        TypeExpr::Collection { coll_type, element } => {
            out.push_str("collection(");
            write_collection_type(coll_type, out);
            out.push(',');
            recursive_type(element, out);
            out.push(')');
        },
        TypeExpr::Refined { var, base, predicate_repr } => {
            out.push_str("refined(");
            push_ident(out, var);
            out.push(',');
            recursive_type(base, out);
            out.push(',');
            out.push_str(predicate_repr);
            out.push(')');
        },
        TypeExpr::Map { key, value } => {
            out.push_str("maptype(");
            recursive_type(key, out);
            out.push(',');
            recursive_type(value, out);
            out.push(')');
        },
    }
}

fn recursive_pattern(pattern: &Pattern, out: &mut String) {
    match pattern {
        Pattern::Term(term) => recursive_pattern_term(term, out),
        Pattern::Collection { coll_type, elements, rest } => {
            out.push_str("collection(");
            if let Some(coll_type) = coll_type {
                write_collection_type(coll_type, out);
            }
            out.push(':');
            for element in elements {
                recursive_pattern(element, out);
                out.push(',');
            }
            out.push(':');
            if let Some(rest) = rest {
                push_ident(out, rest);
            }
            out.push(')');
        },
        Pattern::Map { collection, params, body } => {
            out.push_str("pmap(");
            recursive_pattern(collection, out);
            out.push(',');
            push_ids(out, params);
            out.push(',');
            recursive_pattern(body, out);
            out.push(')');
        },
        Pattern::Zip { first, second } => {
            out.push_str("pzip(");
            recursive_pattern(first, out);
            out.push(',');
            recursive_pattern(second, out);
            out.push(')');
        },
        Pattern::IndexedVec { collection, index, element } => {
            out.push_str("pidx(");
            push_ident(out, collection);
            out.push(',');
            push_ident(out, index);
            out.push(',');
            recursive_pattern(element, out);
            out.push(')');
        },
    }
}

fn recursive_pattern_term(term: &PatternTerm, out: &mut String) {
    match term {
        PatternTerm::Var(id) => {
            out.push_str("pvar(");
            push_ident(out, id);
            out.push(')');
        },
        PatternTerm::Apply { constructor, args } => {
            out.push_str("apply(");
            push_ident(out, constructor);
            out.push(':');
            for arg in args {
                recursive_pattern(arg, out);
                out.push(',');
            }
            out.push(')');
        },
        PatternTerm::Lambda { binder, body } => {
            out.push_str("lambda(");
            push_ident(out, binder);
            out.push(',');
            recursive_pattern(body, out);
            out.push(')');
        },
        PatternTerm::MultiLambda { binders, body } => {
            out.push_str("multilambda(");
            push_ids(out, binders);
            out.push(',');
            recursive_pattern(body, out);
            out.push(')');
        },
        PatternTerm::Subst { term, var, replacement } => {
            out.push_str("subst(");
            recursive_pattern(term, out);
            out.push(',');
            push_ident(out, var);
            out.push(',');
            recursive_pattern(replacement, out);
            out.push(')');
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            out.push_str("multisubst(");
            recursive_pattern(scope, out);
            out.push(':');
            for replacement in replacements {
                recursive_pattern(replacement, out);
                out.push(',');
            }
            out.push(')');
        },
    }
}

fn recursive_behavioral(pred: &BehavioralPred, out: &mut String) {
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            out.push_str("brel(");
            push_ident(out, relation_name);
            out.push(',');
            out.push_str(if *negated { "not" } else { "pos" });
            out.push(',');
            for arg in args {
                write_pred_arg(arg, out);
                out.push(',');
            }
            out.push(')');
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            out.push_str("bquant(");
            write_quantifier(quantifier, out);
            out.push(',');
            push_ident(out, var);
            out.push(',');
            if let Some(domain) = domain {
                push_ident(out, domain);
            }
            out.push(',');
            if let Some(bound) = bound {
                out.push_str(&bound.to_string());
            }
            out.push(',');
            recursive_behavioral(body, out);
            out.push(')');
        },
        BehavioralPred::And(left, right) => recursive_binary_behavioral("and", left, right, out),
        BehavioralPred::Or(left, right) => recursive_binary_behavioral("or", left, right, out),
        BehavioralPred::Not(inner) => {
            out.push_str("bnot(");
            recursive_behavioral(inner, out);
            out.push(')');
        },
        BehavioralPred::Implies(left, right) => {
            recursive_binary_behavioral("implies", left, right, out);
        },
        BehavioralPred::AcMatch { bag, elements, rest } => {
            out.push_str("ac(");
            push_ident(out, bag);
            out.push(',');
            push_ids(out, elements);
            out.push(',');
            if let Some(rest) = rest {
                push_ident(out, rest);
            }
            out.push(')');
        },
        BehavioralPred::Top => out.push_str("top"),
    }
}

fn recursive_binary_behavioral(
    name: &str,
    left: &BehavioralPred,
    right: &BehavioralPred,
    out: &mut String,
) {
    out.push_str(name);
    out.push('(');
    recursive_behavioral(left, out);
    out.push(',');
    recursive_behavioral(right, out);
    out.push(')');
}

fn recursive_premise(premise: &Premise, out: &mut String) {
    match premise {
        Premise::Freshness(freshness) => {
            out.push_str("fresh(");
            push_ident(out, &freshness.var);
            out.push(',');
            write_freshness_target(&freshness.term, out);
            out.push(')');
        },
        Premise::Congruence { source, target } => {
            out.push_str("cong(");
            push_ident(out, source);
            out.push(',');
            push_ident(out, target);
            out.push(')');
        },
        Premise::CongruenceWithheld { source, target } => {
            out.push_str("ncong(");
            push_ident(out, source);
            out.push(',');
            push_ident(out, target);
            out.push(')');
        },
        Premise::RelationQuery { relation, args } => {
            out.push_str("rel(");
            push_ident(out, relation);
            out.push(',');
            push_ids(out, args);
            out.push(')');
        },
        Premise::ForAll { collection, param, body } => {
            out.push_str("forall(");
            push_ident(out, collection);
            out.push(',');
            push_ident(out, param);
            out.push(',');
            recursive_premise(body, out);
            out.push(')');
        },
        Premise::BehavioralGuard(pred) => recursive_behavioral(pred, out),
        Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => {
            out.push_str("synthetic-inj(");
            push_ident(out, inner_var);
            out.push(',');
            push_ident(out, source_category);
            out.push(',');
            push_ids(out, excluded_variants);
            out.push(')');
        },
    }
}

fn recursive_tree(expr: &TreeConstraintExpr, out: &mut String) {
    match expr {
        TreeConstraintExpr::ForallChildren { symbol, body } => {
            out.push_str("forall-children(");
            out.push_str(symbol);
            out.push(',');
            recursive_tree(body, out);
            out.push(')');
        },
        TreeConstraintExpr::ExistsChild => out.push_str("exists-child"),
        TreeConstraintExpr::Not(inner) => {
            out.push_str("not(");
            recursive_tree(inner, out);
            out.push(')');
        },
        TreeConstraintExpr::Match(symbols) => {
            out.push_str("match(");
            for symbol in symbols {
                out.push_str(symbol);
                out.push('|');
            }
            out.push(')');
        },
        TreeConstraintExpr::Atom(symbol) => {
            out.push_str("atom(");
            out.push_str(symbol);
            out.push(')');
        },
        TreeConstraintExpr::And(left, right) | TreeConstraintExpr::Or(left, right) => {
            out.push_str(if matches!(expr, TreeConstraintExpr::And(_, _)) {
                "and("
            } else {
                "or("
            });
            recursive_tree(left, out);
            out.push(',');
            recursive_tree(right, out);
            out.push(')');
        },
    }
}

fn recursive_syntax_exprs(exprs: &[SyntaxExpr], out: &mut String) {
    out.push('[');
    for expr in exprs {
        match expr {
            SyntaxExpr::Literal(value) => {
                out.push_str("lit(");
                out.push_str(value);
                out.push(')');
            },
            SyntaxExpr::Param(id) => {
                out.push_str("param(");
                push_ident(out, id);
                out.push(')');
            },
            SyntaxExpr::Op(op) => recursive_pattern_op(op, out),
            SyntaxExpr::TokenKind { name, bind } => {
                out.push_str("tokenkind(");
                push_ident(out, name);
                if let Some(bind) = bind {
                    out.push('@');
                    push_ident(out, bind);
                }
                out.push(')');
            },
            SyntaxExpr::GuestBody { open, close, bind } => {
                out.push_str("guestbody(");
                push_ident(out, bind);
                out.push(',');
                push_ident(out, open);
                out.push(',');
                push_ident(out, close);
                out.push(')');
            },
        }
        out.push(';');
    }
    out.push(']');
}

fn recursive_pattern_op(op: &PatternOp, out: &mut String) {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            out.push_str("sep(");
            push_ident(out, collection);
            out.push(',');
            out.push_str(separator);
            out.push(',');
            if let Some(source) = source {
                recursive_pattern_op(source, out);
            }
            out.push(')');
        },
        PatternOp::Zip { left, right } => {
            out.push_str("zip(");
            push_ident(out, left);
            out.push(',');
            push_ident(out, right);
            out.push(')');
        },
        PatternOp::Map { source, params, body } => {
            out.push_str("map(");
            recursive_pattern_op(source, out);
            out.push(',');
            push_ids(out, params);
            out.push(',');
            recursive_syntax_exprs(body, out);
            out.push(')');
        },
        PatternOp::Opt { inner } => {
            out.push_str("opt(");
            recursive_syntax_exprs(inner, out);
            out.push(')');
        },
        PatternOp::Var(id) => {
            out.push_str("var(");
            push_ident(out, id);
            out.push(')');
        },
    }
}

fn recursive_term_params(params: &[TermParam], out: &mut String) {
    out.push('[');
    for param in params {
        match param {
            TermParam::Simple { name, ty } => {
                out.push_str("simple(");
                push_ident(out, name);
                out.push(',');
                recursive_type(ty, out);
                out.push(')');
            },
            TermParam::Abstraction { binder, body, ty } => {
                out.push_str("abs(");
                push_ident(out, binder);
                out.push(',');
                push_ident(out, body);
                out.push(',');
                recursive_type(ty, out);
                out.push(')');
            },
            TermParam::MultiAbstraction { binder, body, ty } => {
                out.push_str("multiabs(");
                push_ident(out, binder);
                out.push(',');
                push_ident(out, body);
                out.push(',');
                recursive_type(ty, out);
                out.push(')');
            },
            TermParam::GuardBody { name } => {
                out.push_str("guard(");
                push_ident(out, name);
                out.push(')');
            },
            TermParam::Optional { params } => {
                out.push_str("optional(");
                recursive_term_params(params, out);
                out.push(')');
            },
        }
        out.push(';');
    }
    out.push(']');
}

fn recursive_refinement(pred: &RefinementPredicate, out: &mut String) {
    match pred {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            for (index, (var, coefficient)) in terms.iter().enumerate() {
                if index != 0 {
                    out.push_str(" + ");
                }
                if *coefficient == 1 {
                    push_ident(out, var);
                } else {
                    out.push_str(&coefficient.to_string());
                    out.push('*');
                    push_ident(out, var);
                }
            }
            out.push(' ');
            out.push_str(&relation.to_string());
            out.push(' ');
            out.push_str(&rhs.to_string());
        },
        RefinementPredicate::Relation { name, args, negated } => {
            if *negated {
                out.push('~');
            }
            push_ident(out, name);
            out.push('(');
            for (index, arg) in args.iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                match arg {
                    PredArg::Var(id) | PredArg::Constant(id) => push_ident(out, id),
                }
            }
            out.push(')');
        },
        RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
            write_quantifier(quantifier, out);
            if let Some(bound) = bound {
                out.push_str("_{k=");
                out.push_str(&bound.to_string());
                out.push('}');
            }
            out.push(' ');
            push_ident(out, var);
            if let Some(domain) = domain {
                out.push_str(" in ");
                push_ident(out, domain);
            }
            out.push_str(". (");
            recursive_refinement(body, out);
            out.push(')');
        },
        RefinementPredicate::And(left, right)
        | RefinementPredicate::Or(left, right)
        | RefinementPredicate::Implies(left, right) => {
            out.push('(');
            recursive_refinement(left, out);
            out.push_str(match pred {
                RefinementPredicate::And(_, _) => " && ",
                RefinementPredicate::Or(_, _) => " || ",
                _ => " => ",
            });
            recursive_refinement(right, out);
            out.push(')');
        },
        RefinementPredicate::Not(inner) => {
            out.push('~');
            recursive_refinement(inner, out);
        },
        RefinementPredicate::TermEq(left, right) | RefinementPredicate::TermNeq(left, right) => {
            match left {
                PredArg::Var(id) | PredArg::Constant(id) => push_ident(out, id),
            }
            out.push_str(if matches!(pred, RefinementPredicate::TermEq(_, _)) {
                " == "
            } else {
                " != "
            });
            match right {
                PredArg::Var(id) | PredArg::Constant(id) => push_ident(out, id),
            }
        },
    }
}

fn recursive_tokens(out: &mut String, stream: &TokenStream) {
    for (index, tree) in stream.clone().into_iter().enumerate() {
        if index != 0 {
            out.push(' ');
        }
        match tree {
            TokenTree::Group(group) => {
                let (open, close) = match group.delimiter() {
                    Delimiter::Parenthesis => ("(", ")"),
                    Delimiter::Brace => ("{", "}"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::None => ("", ""),
                };
                out.push_str(open);
                recursive_tokens(out, &group.stream());
                out.push_str(close);
            },
            TokenTree::Ident(id) => push_ident(out, &id),
            TokenTree::Punct(punct) => out.push(punct.as_char()),
            TokenTree::Literal(literal) => out.push_str(&literal.to_string()),
        }
    }
}

fn mixed_pattern(seed: usize, depth: usize) -> Pattern {
    if depth == 0 {
        return Pattern::Term(PatternTerm::Var(ident(if seed & 1 == 0 { "x" } else { "y" })));
    }
    match seed % 10 {
        0 => Pattern::Term(PatternTerm::Apply {
            constructor: ident("Node"),
            args: vec![mixed_pattern(seed + 1, depth - 1), mixed_pattern(seed + 3, depth - 1)],
        }),
        1 => Pattern::Collection {
            coll_type: Some(CollectionType::PathMap),
            elements: vec![mixed_pattern(seed + 1, depth - 1)],
            rest: Some(ident("rest")),
        },
        2 => Pattern::Map {
            collection: Box::new(mixed_pattern(seed + 1, depth - 1)),
            params: vec![ident("entry")],
            body: Box::new(mixed_pattern(seed + 2, depth - 1)),
        },
        3 => Pattern::Zip {
            first: Box::new(mixed_pattern(seed + 1, depth - 1)),
            second: Box::new(mixed_pattern(seed + 2, depth - 1)),
        },
        4 => Pattern::IndexedVec {
            collection: ident("items"),
            index: ident("i"),
            element: Box::new(mixed_pattern(seed + 1, depth - 1)),
        },
        5 => Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(mixed_pattern(seed + 1, depth - 1)),
        }),
        6 => Pattern::Term(PatternTerm::MultiLambda {
            binders: vec![ident("x"), ident("y")],
            body: Box::new(mixed_pattern(seed + 1, depth - 1)),
        }),
        7 => Pattern::Term(PatternTerm::Subst {
            term: Box::new(mixed_pattern(seed + 1, depth - 1)),
            var: ident("x"),
            replacement: Box::new(mixed_pattern(seed + 2, depth - 1)),
        }),
        8 => Pattern::Term(PatternTerm::MultiSubst {
            scope: Box::new(mixed_pattern(seed + 1, depth - 1)),
            replacements: vec![mixed_pattern(seed + 2, depth - 1)],
        }),
        _ => Pattern::Term(PatternTerm::Var(ident("leaf"))),
    }
}

fn mixed_type(seed: usize, depth: usize) -> TypeExpr {
    if depth == 0 {
        return TypeExpr::Base(ident("T"));
    }
    match seed % 5 {
        0 => TypeExpr::Arrow {
            domain: Box::new(mixed_type(seed + 1, depth - 1)),
            codomain: Box::new(mixed_type(seed + 2, depth - 1)),
        },
        1 => TypeExpr::MultiBinder(Box::new(mixed_type(seed + 1, depth - 1))),
        2 => TypeExpr::Collection {
            coll_type: CollectionType::PathMap,
            element: Box::new(mixed_type(seed + 1, depth - 1)),
        },
        3 => TypeExpr::Refined {
            var: ident("v"),
            base: Box::new(mixed_type(seed + 1, depth - 1)),
            predicate_repr: "v > 0".into(),
        },
        _ => TypeExpr::Map {
            key: Box::new(mixed_type(seed + 1, depth - 1)),
            value: Box::new(mixed_type(seed + 2, depth - 1)),
        },
    }
}

fn behavioral(depth: usize) -> BehavioralPred {
    if depth == 0 {
        return BehavioralPred::RelationQuery {
            relation_name: ident("reachable"),
            args: vec![PredArg::Var(ident("x")), PredArg::Constant(ident("Root"))],
            negated: true,
        };
    }
    match depth % 5 {
        0 => BehavioralPred::Quantified {
            quantifier: Quantifier::ForAll,
            var: ident("x"),
            domain: Some(ident("nodes")),
            bound: Some(depth),
            body: Box::new(behavioral(depth - 1)),
        },
        1 => BehavioralPred::And(Box::new(behavioral(depth - 1)), Box::new(BehavioralPred::Top)),
        2 => BehavioralPred::Or(Box::new(behavioral(depth - 1)), Box::new(BehavioralPred::Top)),
        3 => BehavioralPred::Not(Box::new(behavioral(depth - 1))),
        _ => BehavioralPred::Implies(
            Box::new(behavioral(depth - 1)),
            Box::new(BehavioralPred::AcMatch {
                bag: ident("bag"),
                elements: vec![ident("a"), ident("b")],
                rest: Some(ident("tail")),
            }),
        ),
    }
}

fn refinement(depth: usize) -> RefinementPredicate {
    if depth == 0 {
        return RefinementPredicate::Linear {
            terms: vec![(ident("x"), 1), (ident("y"), -2)],
            relation: crate::language::LinearRelation::Le,
            rhs: 17,
        };
    }
    match depth % 5 {
        0 => RefinementPredicate::Quantified {
            quantifier: Quantifier::Exists,
            var: ident("x"),
            domain: Some(ident("nodes")),
            bound: Some(depth),
            body: Box::new(refinement(depth - 1)),
        },
        1 => RefinementPredicate::And(
            Box::new(refinement(depth - 1)),
            Box::new(RefinementPredicate::TermEq(
                PredArg::Var(ident("x")),
                PredArg::Constant(ident("Z")),
            )),
        ),
        2 => RefinementPredicate::Or(
            Box::new(refinement(depth - 1)),
            Box::new(RefinementPredicate::TermNeq(
                PredArg::Var(ident("x")),
                PredArg::Constant(ident("Z")),
            )),
        ),
        3 => RefinementPredicate::Not(Box::new(refinement(depth - 1))),
        _ => RefinementPredicate::Implies(
            Box::new(refinement(depth - 1)),
            Box::new(RefinementPredicate::Relation {
                name: ident("safe"),
                args: vec![PredArg::Var(ident("x"))],
                negated: false,
            }),
        ),
    }
}

#[test]
fn iterative_identity_matches_recursive_oracles() {
    for seed in 0..256 {
        let pattern = mixed_pattern(seed, 5);
        let mut expected = String::new();
        recursive_pattern(&pattern, &mut expected);
        assert_eq!(pattern_identity(&pattern), expected, "pattern seed {seed}");

        let ty = mixed_type(seed, 5);
        let mut actual = String::new();
        let mut expected = String::new();
        write_type_expr(&ty, &mut actual);
        recursive_type(&ty, &mut expected);
        assert_eq!(actual, expected, "type seed {seed}");
    }

    let pred = behavioral(12);
    let mut expected = String::new();
    recursive_behavioral(&pred, &mut expected);
    assert_eq!(behavioral_predicate_identity(&pred), expected);

    let mut premise = Premise::BehavioralGuard(BehavioralPred::Top);
    for depth in 0..12 {
        premise = Premise::ForAll {
            collection: ident("items"),
            param: ident(if depth & 1 == 0 { "x" } else { "y" }),
            body: Box::new(premise),
        };
    }
    let mut actual = String::new();
    let mut expected = String::new();
    write_premise(&premise, &mut actual);
    recursive_premise(&premise, &mut expected);
    assert_eq!(actual, expected);

    let tree = TreeConstraintExpr::And(
        Box::new(TreeConstraintExpr::ForallChildren {
            symbol: "Node".into(),
            body: Box::new(TreeConstraintExpr::Not(Box::new(TreeConstraintExpr::Atom(
                "Bad".into(),
            )))),
        }),
        Box::new(TreeConstraintExpr::Or(
            Box::new(TreeConstraintExpr::ExistsChild),
            Box::new(TreeConstraintExpr::Match(vec!["Leaf".into(), "Nil".into()])),
        )),
    );
    let mut actual = String::new();
    let mut expected = String::new();
    write_tree_constraint_expr(&tree, &mut actual);
    recursive_tree(&tree, &mut expected);
    assert_eq!(actual, expected);

    let op = PatternOp::Sep {
        collection: ident("ignored"),
        separator: ",".into(),
        source: Some(Box::new(PatternOp::Map {
            source: Box::new(PatternOp::Zip {
                left: ident("keys"),
                right: ident("values"),
            }),
            params: vec![ident("k"), ident("v")],
            body: vec![
                SyntaxExpr::Literal(":".into()),
                SyntaxExpr::Param(ident("v")),
                SyntaxExpr::TokenKind {
                    name: ident("Comma"),
                    bind: Some(ident("comma")),
                },
                SyntaxExpr::GuestBody {
                    open: ident("Open"),
                    close: ident("Close"),
                    bind: ident("guest"),
                },
                SyntaxExpr::Op(PatternOp::Opt {
                    inner: vec![SyntaxExpr::Param(ident("k"))],
                }),
            ],
        })),
    };
    let mut actual = String::new();
    let mut expected = String::new();
    run_identity_tasks(&mut actual, vec![IdentityTask::PatternOp(&op)]);
    recursive_pattern_op(&op, &mut expected);
    assert_eq!(actual, expected);

    let params = vec![TermParam::Optional {
        params: vec![
            TermParam::Simple { name: ident("x"), ty: mixed_type(1, 3) },
            TermParam::Abstraction {
                binder: ident("b"),
                body: ident("p"),
                ty: mixed_type(2, 3),
            },
            TermParam::MultiAbstraction {
                binder: ident("bs"),
                body: ident("ps"),
                ty: mixed_type(3, 3),
            },
            TermParam::GuardBody { name: ident("guard") },
            TermParam::Optional { params: Vec::new() },
        ],
    }];
    let mut actual = String::new();
    let mut expected = String::new();
    write_term_params(&params, &mut actual);
    recursive_term_params(&params, &mut expected);
    assert_eq!(actual, expected);

    let refinement = refinement(12);
    let mut actual = String::new();
    let mut expected = String::new();
    write_refinement_predicate(&refinement, &mut actual);
    recursive_refinement(&refinement, &mut expected);
    assert_eq!(actual, expected);

    let tokens: TokenStream = "outer(alpha, [beta { gamma }])"
        .parse()
        .expect("token fixture");
    let mut actual = String::new();
    let mut expected = String::new();
    push_token_stream_canonical(&mut actual, &tokens);
    recursive_tokens(&mut expected, &tokens);
    assert_eq!(actual, expected);
}

#[test]
fn deep_pattern_and_type_identity_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("identity-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = Pattern::Term(PatternTerm::Var(ident("leaf")));
            for _ in 0..DEPTH {
                pattern = Pattern::Term(PatternTerm::Apply {
                    constructor: ident("Node"),
                    args: vec![pattern],
                });
            }
            let identity = pattern_identity(&pattern);
            assert!(identity.starts_with("apply(Node:apply(Node:"));
            assert!(identity.ends_with(",)"));
            assert_eq!(identity.matches("apply(Node:").count(), DEPTH);
            drop(pattern);

            let mut ty = TypeExpr::Base(ident("T"));
            for _ in 0..DEPTH {
                ty = TypeExpr::MultiBinder(Box::new(ty));
            }
            let mut identity = String::new();
            write_type_expr(&ty, &mut identity);
            assert!(identity.starts_with("multi(multi("));
            assert!(identity.ends_with(')'));
            assert_eq!(identity.matches("multi(").count(), DEPTH);
            drop(ty);
        })
        .expect("small-stack identity thread must spawn");
    handle
        .join()
        .expect("identity PDAs must not overflow the native stack");
}
