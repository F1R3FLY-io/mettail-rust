//! Stack-safe lifecycle and lowering machines for recursive language-model trees.

use super::{
    BehavioralPred, Condition, ConstraintDomain, FreshnessCondition, FreshnessTarget,
    LinearRelation, PredArg, Premise, Quantifier, RefinementPredicate, TreeConstraintExpr,
};
use proc_macro2::TokenStream;
use quote::quote;

fn write_model_debug_indent(
    formatter: &mut std::fmt::Formatter<'_>,
    indent: usize,
) -> std::fmt::Result {
    for _ in 0..indent {
        formatter.write_str("    ")?;
    }
    Ok(())
}

fn fmt_model_ident(
    ident: &syn::Ident,
    indent: usize,
    pretty: bool,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    if pretty {
        formatter.write_str("Ident {\n")?;
        write_model_debug_indent(formatter, indent + 1)?;
        write!(formatter, "sym: {ident},\n")?;
        write_model_debug_indent(formatter, indent)?;
        formatter.write_str("}")
    } else {
        write!(formatter, "Ident {{ sym: {ident} }}")
    }
}

enum BehavioralDebugTask<'pred> {
    Visit(&'pred BehavioralPred, usize),
    PredArg(&'pred PredArg, usize),
    PredArgList(&'pred [PredArg], usize),
    Ident(&'pred syn::Ident, usize),
    IdentList(&'pred [syn::Ident], usize),
    OptionIdent(&'pred Option<syn::Ident>, usize),
    OptionUsize(Option<usize>, usize),
    Quantifier(&'pred Quantifier),
    Bool(bool),
    Usize(usize),
    FieldPred(&'static str, &'pred BehavioralPred, usize),
    FieldPredArgs(&'static str, &'pred [PredArg], usize),
    FieldIdent(&'static str, &'pred syn::Ident, usize),
    FieldIdentList(&'static str, &'pred [syn::Ident], usize),
    FieldOptionIdent(&'static str, &'pred Option<syn::Ident>, usize),
    FieldOptionUsize(&'static str, Option<usize>, usize),
    FieldQuantifier(&'static str, &'pred Quantifier, usize),
    FieldBool(&'static str, bool, usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
    CloseList(usize),
}

fn push_compact_behavioral_list<'pred, T>(
    tasks: &mut Vec<BehavioralDebugTask<'pred>>,
    values: &'pred [T],
    wrap: impl Fn(&'pred T) -> BehavioralDebugTask<'pred>,
) {
    tasks.push(BehavioralDebugTask::Text("]"));
    for (index, value) in values.iter().enumerate().rev() {
        tasks.push(wrap(value));
        if index != 0 {
            tasks.push(BehavioralDebugTask::Text(", "));
        }
    }
}

fn fmt_behavioral_predicate_at(
    root: &BehavioralPred,
    root_indent: usize,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let pretty = formatter.alternate();
    let mut tasks = vec![BehavioralDebugTask::Visit(root, root_indent)];
    while let Some(task) = tasks.pop() {
        match task {
            BehavioralDebugTask::Text(text) => formatter.write_str(text)?,
            BehavioralDebugTask::Indent(indent) => write_model_debug_indent(formatter, indent)?,
            BehavioralDebugTask::CloseTuple(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str(")")?;
            },
            BehavioralDebugTask::CloseStruct(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("}")?;
            },
            BehavioralDebugTask::CloseList(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("]")?;
            },
            BehavioralDebugTask::Ident(ident, indent) => {
                fmt_model_ident(ident, indent, pretty, formatter)?;
            },
            BehavioralDebugTask::Bool(value) => write!(formatter, "{value}")?,
            BehavioralDebugTask::Usize(value) => write!(formatter, "{value}")?,
            BehavioralDebugTask::Quantifier(quantifier) => write!(formatter, "{quantifier:?}")?,
            BehavioralDebugTask::OptionUsize(None, _) => formatter.write_str("None")?,
            BehavioralDebugTask::OptionUsize(Some(value), _) if !pretty => {
                write!(formatter, "Some({value})")?;
            },
            BehavioralDebugTask::OptionUsize(Some(value), indent) => {
                formatter.write_str("Some(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Usize(value));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::OptionIdent(None, _) => formatter.write_str("None")?,
            BehavioralDebugTask::OptionIdent(Some(ident), _) if !pretty => {
                formatter.write_str("Some(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Ident(ident, 0));
            },
            BehavioralDebugTask::OptionIdent(Some(ident), indent) => {
                formatter.write_str("Some(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Ident(ident, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::PredArg(PredArg::Var(ident), _) if !pretty => {
                formatter.write_str("Var(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Ident(ident, 0));
            },
            BehavioralDebugTask::PredArg(PredArg::Constant(ident), _) if !pretty => {
                formatter.write_str("Constant(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Ident(ident, 0));
            },
            BehavioralDebugTask::PredArg(arg, indent) => {
                formatter.write_str(match arg {
                    PredArg::Var(_) => "Var(\n",
                    PredArg::Constant(_) => "Constant(\n",
                })?;
                let ident = match arg {
                    PredArg::Var(ident) | PredArg::Constant(ident) => ident,
                };
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Ident(ident, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::PredArgList(args, _) if !pretty => {
                formatter.write_str("[")?;
                push_compact_behavioral_list(&mut tasks, args, |arg| {
                    BehavioralDebugTask::PredArg(arg, 0)
                });
            },
            BehavioralDebugTask::PredArgList([], _) => formatter.write_str("[]")?,
            BehavioralDebugTask::PredArgList(args, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(BehavioralDebugTask::CloseList(indent));
                for arg in args.iter().rev() {
                    tasks.push(BehavioralDebugTask::Text(",\n"));
                    tasks.push(BehavioralDebugTask::PredArg(arg, indent + 1));
                    tasks.push(BehavioralDebugTask::Indent(indent + 1));
                }
            },
            BehavioralDebugTask::IdentList(idents, _) if !pretty => {
                formatter.write_str("[")?;
                push_compact_behavioral_list(&mut tasks, idents, |ident| {
                    BehavioralDebugTask::Ident(ident, 0)
                });
            },
            BehavioralDebugTask::IdentList([], _) => formatter.write_str("[]")?,
            BehavioralDebugTask::IdentList(idents, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(BehavioralDebugTask::CloseList(indent));
                for ident in idents.iter().rev() {
                    tasks.push(BehavioralDebugTask::Text(",\n"));
                    tasks.push(BehavioralDebugTask::Ident(ident, indent + 1));
                    tasks.push(BehavioralDebugTask::Indent(indent + 1));
                }
            },
            BehavioralDebugTask::FieldPred(name, pred, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(pred, indent));
            },
            BehavioralDebugTask::FieldPredArgs(name, args, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::PredArgList(args, indent));
            },
            BehavioralDebugTask::FieldIdent(name, ident, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Ident(ident, indent));
            },
            BehavioralDebugTask::FieldIdentList(name, idents, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::IdentList(idents, indent));
            },
            BehavioralDebugTask::FieldOptionIdent(name, ident, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::OptionIdent(ident, indent));
            },
            BehavioralDebugTask::FieldOptionUsize(name, value, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: ")?;
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::OptionUsize(value, indent));
            },
            BehavioralDebugTask::FieldQuantifier(name, quantifier, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: {quantifier:?},\n")?;
            },
            BehavioralDebugTask::FieldBool(name, value, indent) => {
                write_model_debug_indent(formatter, indent)?;
                write!(formatter, "{name}: {value},\n")?;
            },
            BehavioralDebugTask::Visit(
                BehavioralPred::RelationQuery { relation_name, args, negated },
                indent,
            ) if pretty => {
                formatter.write_str("RelationQuery {\n")?;
                tasks.push(BehavioralDebugTask::CloseStruct(indent));
                tasks.push(BehavioralDebugTask::FieldBool("negated", *negated, indent + 1));
                tasks.push(BehavioralDebugTask::FieldPredArgs("args", args, indent + 1));
                tasks.push(BehavioralDebugTask::FieldIdent(
                    "relation_name",
                    relation_name,
                    indent + 1,
                ));
            },
            BehavioralDebugTask::Visit(
                BehavioralPred::Quantified { quantifier, var, domain, bound, body },
                indent,
            ) if pretty => {
                formatter.write_str("Quantified {\n")?;
                tasks.push(BehavioralDebugTask::CloseStruct(indent));
                tasks.push(BehavioralDebugTask::FieldPred("body", body, indent + 1));
                tasks.push(BehavioralDebugTask::FieldOptionUsize("bound", *bound, indent + 1));
                tasks.push(BehavioralDebugTask::FieldOptionIdent("domain", domain, indent + 1));
                tasks.push(BehavioralDebugTask::FieldIdent("var", var, indent + 1));
                tasks.push(BehavioralDebugTask::FieldQuantifier(
                    "quantifier",
                    quantifier,
                    indent + 1,
                ));
            },
            BehavioralDebugTask::Visit(BehavioralPred::And(left, right), indent) if pretty => {
                formatter.write_str("And(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(right, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(left, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Or(left, right), indent) if pretty => {
                formatter.write_str("Or(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(right, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(left, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Not(inner), indent) if pretty => {
                formatter.write_str("Not(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(inner, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Implies(left, right), indent) if pretty => {
                formatter.write_str("Implies(\n")?;
                tasks.push(BehavioralDebugTask::CloseTuple(indent));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(right, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
                tasks.push(BehavioralDebugTask::Text(",\n"));
                tasks.push(BehavioralDebugTask::Visit(left, indent + 1));
                tasks.push(BehavioralDebugTask::Indent(indent + 1));
            },
            BehavioralDebugTask::Visit(BehavioralPred::AcMatch { bag, elements, rest }, indent)
                if pretty =>
            {
                formatter.write_str("AcMatch {\n")?;
                tasks.push(BehavioralDebugTask::CloseStruct(indent));
                tasks.push(BehavioralDebugTask::FieldOptionIdent("rest", rest, indent + 1));
                tasks.push(BehavioralDebugTask::FieldIdentList("elements", elements, indent + 1));
                tasks.push(BehavioralDebugTask::FieldIdent("bag", bag, indent + 1));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Top, _) => formatter.write_str("Top")?,
            BehavioralDebugTask::Visit(
                BehavioralPred::RelationQuery { relation_name, args, negated },
                _,
            ) => {
                formatter.write_str("RelationQuery { relation_name: ")?;
                tasks.push(BehavioralDebugTask::Text(" }"));
                tasks.push(BehavioralDebugTask::Bool(*negated));
                tasks.push(BehavioralDebugTask::Text(", negated: "));
                tasks.push(BehavioralDebugTask::PredArgList(args, 0));
                tasks.push(BehavioralDebugTask::Text(", args: "));
                tasks.push(BehavioralDebugTask::Ident(relation_name, 0));
            },
            BehavioralDebugTask::Visit(
                BehavioralPred::Quantified { quantifier, var, domain, bound, body },
                _,
            ) => {
                formatter.write_str("Quantified { quantifier: ")?;
                tasks.push(BehavioralDebugTask::Text(" }"));
                tasks.push(BehavioralDebugTask::Visit(body, 0));
                tasks.push(BehavioralDebugTask::Text(", body: "));
                tasks.push(BehavioralDebugTask::OptionUsize(*bound, 0));
                tasks.push(BehavioralDebugTask::Text(", bound: "));
                tasks.push(BehavioralDebugTask::OptionIdent(domain, 0));
                tasks.push(BehavioralDebugTask::Text(", domain: "));
                tasks.push(BehavioralDebugTask::Ident(var, 0));
                tasks.push(BehavioralDebugTask::Text(", var: "));
                tasks.push(BehavioralDebugTask::Quantifier(quantifier));
            },
            BehavioralDebugTask::Visit(BehavioralPred::And(left, right), _) => {
                formatter.write_str("And(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Visit(right, 0));
                tasks.push(BehavioralDebugTask::Text(", "));
                tasks.push(BehavioralDebugTask::Visit(left, 0));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Or(left, right), _) => {
                formatter.write_str("Or(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Visit(right, 0));
                tasks.push(BehavioralDebugTask::Text(", "));
                tasks.push(BehavioralDebugTask::Visit(left, 0));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Not(inner), _) => {
                formatter.write_str("Not(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Visit(inner, 0));
            },
            BehavioralDebugTask::Visit(BehavioralPred::Implies(left, right), _) => {
                formatter.write_str("Implies(")?;
                tasks.push(BehavioralDebugTask::Text(")"));
                tasks.push(BehavioralDebugTask::Visit(right, 0));
                tasks.push(BehavioralDebugTask::Text(", "));
                tasks.push(BehavioralDebugTask::Visit(left, 0));
            },
            BehavioralDebugTask::Visit(BehavioralPred::AcMatch { bag, elements, rest }, _) => {
                formatter.write_str("AcMatch { bag: ")?;
                tasks.push(BehavioralDebugTask::Text(" }"));
                tasks.push(BehavioralDebugTask::OptionIdent(rest, 0));
                tasks.push(BehavioralDebugTask::Text(", rest: "));
                tasks.push(BehavioralDebugTask::IdentList(elements, 0));
                tasks.push(BehavioralDebugTask::Text(", elements: "));
                tasks.push(BehavioralDebugTask::Ident(bag, 0));
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for BehavioralPred {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_behavioral_predicate_at(self, 0, formatter)
    }
}

enum ContextDebugTask<'model> {
    Premise(&'model Premise, usize),
    Condition(&'model Condition, usize),
    Behavioral(&'model BehavioralPred, usize),
    Freshness(&'model FreshnessCondition, usize),
    FreshnessTarget(&'model FreshnessTarget, usize),
    Ident(&'model syn::Ident, usize),
    IdentList(&'model [syn::Ident], usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
    CloseList(usize),
}

fn push_context_ident_field<'model>(
    tasks: &mut Vec<ContextDebugTask<'model>>,
    name: &'static str,
    ident: &'model syn::Ident,
    indent: usize,
) {
    tasks.push(ContextDebugTask::Text(",\n"));
    tasks.push(ContextDebugTask::Ident(ident, indent));
    tasks.push(ContextDebugTask::Text(name));
    tasks.push(ContextDebugTask::Indent(indent));
}

fn push_context_ident_list_field<'model>(
    tasks: &mut Vec<ContextDebugTask<'model>>,
    name: &'static str,
    idents: &'model [syn::Ident],
    indent: usize,
) {
    tasks.push(ContextDebugTask::Text(",\n"));
    tasks.push(ContextDebugTask::IdentList(idents, indent));
    tasks.push(ContextDebugTask::Text(name));
    tasks.push(ContextDebugTask::Indent(indent));
}

fn push_pretty_context_tuple<'model>(
    tasks: &mut Vec<ContextDebugTask<'model>>,
    value: ContextDebugTask<'model>,
    indent: usize,
) {
    tasks.push(ContextDebugTask::CloseTuple(indent));
    tasks.push(ContextDebugTask::Text(",\n"));
    tasks.push(value);
    tasks.push(ContextDebugTask::Indent(indent + 1));
}

fn fmt_context_at(
    root: ContextDebugTask<'_>,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let pretty = formatter.alternate();
    let mut tasks = vec![root];
    while let Some(task) = tasks.pop() {
        match task {
            ContextDebugTask::Text(text) => formatter.write_str(text)?,
            ContextDebugTask::Indent(indent) => write_model_debug_indent(formatter, indent)?,
            ContextDebugTask::CloseTuple(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str(")")?;
            },
            ContextDebugTask::CloseStruct(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("}")?;
            },
            ContextDebugTask::CloseList(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("]")?;
            },
            ContextDebugTask::Ident(ident, indent) => {
                fmt_model_ident(ident, indent, pretty, formatter)?;
            },
            ContextDebugTask::IdentList([], _) => formatter.write_str("[]")?,
            ContextDebugTask::IdentList(idents, _) if !pretty => {
                formatter.write_str("[")?;
                tasks.push(ContextDebugTask::Text("]"));
                for (index, ident) in idents.iter().enumerate().rev() {
                    tasks.push(ContextDebugTask::Ident(ident, 0));
                    if index != 0 {
                        tasks.push(ContextDebugTask::Text(", "));
                    }
                }
            },
            ContextDebugTask::IdentList(idents, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(ContextDebugTask::CloseList(indent));
                for ident in idents.iter().rev() {
                    tasks.push(ContextDebugTask::Text(",\n"));
                    tasks.push(ContextDebugTask::Ident(ident, indent + 1));
                    tasks.push(ContextDebugTask::Indent(indent + 1));
                }
            },
            ContextDebugTask::Behavioral(predicate, indent) => {
                fmt_behavioral_predicate_at(predicate, indent, formatter)?;
            },
            ContextDebugTask::FreshnessTarget(FreshnessTarget::Var(ident), indent)
            | ContextDebugTask::FreshnessTarget(FreshnessTarget::CollectionRest(ident), indent)
                if pretty =>
            {
                formatter.write_str(match task {
                    ContextDebugTask::FreshnessTarget(FreshnessTarget::Var(_), _) => "Var(\n",
                    _ => "CollectionRest(\n",
                })?;
                push_pretty_context_tuple(
                    &mut tasks,
                    ContextDebugTask::Ident(ident, indent + 1),
                    indent,
                );
            },
            ContextDebugTask::FreshnessTarget(FreshnessTarget::Var(ident), _) => {
                formatter.write_str("Var(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Ident(ident, 0));
            },
            ContextDebugTask::FreshnessTarget(FreshnessTarget::CollectionRest(ident), _) => {
                formatter.write_str("CollectionRest(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Ident(ident, 0));
            },
            ContextDebugTask::Freshness(condition, indent) if pretty => {
                formatter.write_str("FreshnessCondition {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                tasks.push(ContextDebugTask::Text(",\n"));
                tasks.push(ContextDebugTask::FreshnessTarget(&condition.term, indent + 1));
                tasks.push(ContextDebugTask::Text("term: "));
                tasks.push(ContextDebugTask::Indent(indent + 1));
                push_context_ident_field(&mut tasks, "var: ", &condition.var, indent + 1);
            },
            ContextDebugTask::Freshness(condition, _) => {
                formatter.write_str("FreshnessCondition { var: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::FreshnessTarget(&condition.term, 0));
                tasks.push(ContextDebugTask::Text(", term: "));
                tasks.push(ContextDebugTask::Ident(&condition.var, 0));
            },
            ContextDebugTask::Premise(Premise::Freshness(condition), indent) if pretty => {
                formatter.write_str("Freshness(\n")?;
                push_pretty_context_tuple(
                    &mut tasks,
                    ContextDebugTask::Freshness(condition, indent + 1),
                    indent,
                );
            },
            ContextDebugTask::Premise(Premise::Freshness(condition), _) => {
                formatter.write_str("Freshness(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Freshness(condition, 0));
            },
            ContextDebugTask::Premise(Premise::Congruence { source, target }, indent)
            | ContextDebugTask::Premise(Premise::CongruenceWithheld { source, target }, indent)
                if pretty =>
            {
                formatter.write_str(match task {
                    ContextDebugTask::Premise(Premise::Congruence { .. }, _) => "Congruence {\n",
                    _ => "CongruenceWithheld {\n",
                })?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                push_context_ident_field(&mut tasks, "target: ", target, indent + 1);
                push_context_ident_field(&mut tasks, "source: ", source, indent + 1);
            },
            ContextDebugTask::Premise(Premise::Congruence { source, target }, _) => {
                formatter.write_str("Congruence { source: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::Ident(target, 0));
                tasks.push(ContextDebugTask::Text(", target: "));
                tasks.push(ContextDebugTask::Ident(source, 0));
            },
            ContextDebugTask::Premise(Premise::CongruenceWithheld { source, target }, _) => {
                formatter.write_str("CongruenceWithheld { source: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::Ident(target, 0));
                tasks.push(ContextDebugTask::Text(", target: "));
                tasks.push(ContextDebugTask::Ident(source, 0));
            },
            ContextDebugTask::Premise(Premise::RelationQuery { relation, args }, indent)
                if pretty =>
            {
                formatter.write_str("RelationQuery {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                push_context_ident_list_field(&mut tasks, "args: ", args, indent + 1);
                push_context_ident_field(&mut tasks, "relation: ", relation, indent + 1);
            },
            ContextDebugTask::Premise(Premise::RelationQuery { relation, args }, _) => {
                formatter.write_str("RelationQuery { relation: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::IdentList(args, 0));
                tasks.push(ContextDebugTask::Text(", args: "));
                tasks.push(ContextDebugTask::Ident(relation, 0));
            },
            ContextDebugTask::Premise(Premise::ForAll { collection, param, body }, indent)
                if pretty =>
            {
                formatter.write_str("ForAll {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                tasks.push(ContextDebugTask::Text(",\n"));
                tasks.push(ContextDebugTask::Premise(body, indent + 1));
                tasks.push(ContextDebugTask::Text("body: "));
                tasks.push(ContextDebugTask::Indent(indent + 1));
                push_context_ident_field(&mut tasks, "param: ", param, indent + 1);
                push_context_ident_field(&mut tasks, "collection: ", collection, indent + 1);
            },
            ContextDebugTask::Premise(Premise::ForAll { collection, param, body }, _) => {
                formatter.write_str("ForAll { collection: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::Premise(body, 0));
                tasks.push(ContextDebugTask::Text(", body: "));
                tasks.push(ContextDebugTask::Ident(param, 0));
                tasks.push(ContextDebugTask::Text(", param: "));
                tasks.push(ContextDebugTask::Ident(collection, 0));
            },
            ContextDebugTask::Premise(Premise::BehavioralGuard(predicate), indent) if pretty => {
                formatter.write_str("BehavioralGuard(\n")?;
                push_pretty_context_tuple(
                    &mut tasks,
                    ContextDebugTask::Behavioral(predicate, indent + 1),
                    indent,
                );
            },
            ContextDebugTask::Premise(Premise::BehavioralGuard(predicate), _) => {
                formatter.write_str("BehavioralGuard(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Behavioral(predicate, 0));
            },
            ContextDebugTask::Premise(
                Premise::SyntheticInjGuard {
                    inner_var,
                    source_category,
                    excluded_variants,
                },
                indent,
            ) if pretty => {
                formatter.write_str("SyntheticInjGuard {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                push_context_ident_list_field(
                    &mut tasks,
                    "excluded_variants: ",
                    excluded_variants,
                    indent + 1,
                );
                push_context_ident_field(
                    &mut tasks,
                    "source_category: ",
                    source_category,
                    indent + 1,
                );
                push_context_ident_field(&mut tasks, "inner_var: ", inner_var, indent + 1);
            },
            ContextDebugTask::Premise(
                Premise::SyntheticInjGuard {
                    inner_var,
                    source_category,
                    excluded_variants,
                },
                _,
            ) => {
                formatter.write_str("SyntheticInjGuard { inner_var: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::IdentList(excluded_variants, 0));
                tasks.push(ContextDebugTask::Text(", excluded_variants: "));
                tasks.push(ContextDebugTask::Ident(source_category, 0));
                tasks.push(ContextDebugTask::Text(", source_category: "));
                tasks.push(ContextDebugTask::Ident(inner_var, 0));
            },
            ContextDebugTask::Condition(Condition::Freshness(condition), indent) if pretty => {
                formatter.write_str("Freshness(\n")?;
                push_pretty_context_tuple(
                    &mut tasks,
                    ContextDebugTask::Freshness(condition, indent + 1),
                    indent,
                );
            },
            ContextDebugTask::Condition(Condition::Freshness(condition), _) => {
                formatter.write_str("Freshness(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Freshness(condition, 0));
            },
            ContextDebugTask::Condition(Condition::EnvQuery { relation, args }, indent)
                if pretty =>
            {
                formatter.write_str("EnvQuery {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                push_context_ident_list_field(&mut tasks, "args: ", args, indent + 1);
                push_context_ident_field(&mut tasks, "relation: ", relation, indent + 1);
            },
            ContextDebugTask::Condition(Condition::EnvQuery { relation, args }, _) => {
                formatter.write_str("EnvQuery { relation: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::IdentList(args, 0));
                tasks.push(ContextDebugTask::Text(", args: "));
                tasks.push(ContextDebugTask::Ident(relation, 0));
            },
            ContextDebugTask::Condition(Condition::ForAll { collection, param, body }, indent)
                if pretty =>
            {
                formatter.write_str("ForAll {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                tasks.push(ContextDebugTask::Text(",\n"));
                tasks.push(ContextDebugTask::Condition(body, indent + 1));
                tasks.push(ContextDebugTask::Text("body: "));
                tasks.push(ContextDebugTask::Indent(indent + 1));
                push_context_ident_field(&mut tasks, "param: ", param, indent + 1);
                push_context_ident_field(&mut tasks, "collection: ", collection, indent + 1);
            },
            ContextDebugTask::Condition(Condition::ForAll { collection, param, body }, _) => {
                formatter.write_str("ForAll { collection: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::Condition(body, 0));
                tasks.push(ContextDebugTask::Text(", body: "));
                tasks.push(ContextDebugTask::Ident(param, 0));
                tasks.push(ContextDebugTask::Text(", param: "));
                tasks.push(ContextDebugTask::Ident(collection, 0));
            },
            ContextDebugTask::Condition(Condition::BehavioralGuard(predicate), indent)
                if pretty =>
            {
                formatter.write_str("BehavioralGuard(\n")?;
                push_pretty_context_tuple(
                    &mut tasks,
                    ContextDebugTask::Behavioral(predicate, indent + 1),
                    indent,
                );
            },
            ContextDebugTask::Condition(Condition::BehavioralGuard(predicate), _) => {
                formatter.write_str("BehavioralGuard(")?;
                tasks.push(ContextDebugTask::Text(")"));
                tasks.push(ContextDebugTask::Behavioral(predicate, 0));
            },
            ContextDebugTask::Condition(
                Condition::SyntheticInjGuard {
                    inner_var,
                    source_category,
                    excluded_variants,
                },
                indent,
            ) if pretty => {
                formatter.write_str("SyntheticInjGuard {\n")?;
                tasks.push(ContextDebugTask::CloseStruct(indent));
                push_context_ident_list_field(
                    &mut tasks,
                    "excluded_variants: ",
                    excluded_variants,
                    indent + 1,
                );
                push_context_ident_field(
                    &mut tasks,
                    "source_category: ",
                    source_category,
                    indent + 1,
                );
                push_context_ident_field(&mut tasks, "inner_var: ", inner_var, indent + 1);
            },
            ContextDebugTask::Condition(
                Condition::SyntheticInjGuard {
                    inner_var,
                    source_category,
                    excluded_variants,
                },
                _,
            ) => {
                formatter.write_str("SyntheticInjGuard { inner_var: ")?;
                tasks.push(ContextDebugTask::Text(" }"));
                tasks.push(ContextDebugTask::IdentList(excluded_variants, 0));
                tasks.push(ContextDebugTask::Text(", excluded_variants: "));
                tasks.push(ContextDebugTask::Ident(source_category, 0));
                tasks.push(ContextDebugTask::Text(", source_category: "));
                tasks.push(ContextDebugTask::Ident(inner_var, 0));
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for Premise {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_context_at(ContextDebugTask::Premise(self, 0), formatter)
    }
}

impl std::fmt::Debug for Condition {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_context_at(ContextDebugTask::Condition(self, 0), formatter)
    }
}

enum BehavioralCloneTask<'pred> {
    Visit(&'pred BehavioralPred),
    Quantified(&'pred BehavioralPred, usize),
    And(usize),
    Or(usize),
    Not(usize),
    Implies(usize),
}

fn clone_behavioral_predicate(root: &BehavioralPred) -> BehavioralPred {
    let mut tasks = vec![BehavioralCloneTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            BehavioralCloneTask::Visit(BehavioralPred::RelationQuery {
                relation_name,
                args,
                negated,
            }) => values.push(BehavioralPred::RelationQuery {
                relation_name: relation_name.clone(),
                args: args.clone(),
                negated: *negated,
            }),
            BehavioralCloneTask::Visit(pred @ BehavioralPred::Quantified { body, .. }) => {
                tasks.push(BehavioralCloneTask::Quantified(pred, values.len()));
                tasks.push(BehavioralCloneTask::Visit(body));
            },
            BehavioralCloneTask::Visit(BehavioralPred::And(left, right)) => {
                tasks.push(BehavioralCloneTask::And(values.len()));
                tasks.push(BehavioralCloneTask::Visit(right));
                tasks.push(BehavioralCloneTask::Visit(left));
            },
            BehavioralCloneTask::Visit(BehavioralPred::Or(left, right)) => {
                tasks.push(BehavioralCloneTask::Or(values.len()));
                tasks.push(BehavioralCloneTask::Visit(right));
                tasks.push(BehavioralCloneTask::Visit(left));
            },
            BehavioralCloneTask::Visit(BehavioralPred::Not(inner)) => {
                tasks.push(BehavioralCloneTask::Not(values.len()));
                tasks.push(BehavioralCloneTask::Visit(inner));
            },
            BehavioralCloneTask::Visit(BehavioralPred::Implies(left, right)) => {
                tasks.push(BehavioralCloneTask::Implies(values.len()));
                tasks.push(BehavioralCloneTask::Visit(right));
                tasks.push(BehavioralCloneTask::Visit(left));
            },
            BehavioralCloneTask::Visit(BehavioralPred::AcMatch { bag, elements, rest }) => values
                .push(BehavioralPred::AcMatch {
                    bag: bag.clone(),
                    elements: elements.clone(),
                    rest: rest.clone(),
                }),
            BehavioralCloneTask::Visit(BehavioralPred::Top) => values.push(BehavioralPred::Top),
            BehavioralCloneTask::Quantified(source, value_base) => {
                let BehavioralPred::Quantified { quantifier, var, domain, bound, .. } = source
                else {
                    unreachable!("quantified clone task carries a quantified predicate")
                };
                let body = values
                    .pop()
                    .expect("behavioral clone PDA lost a quantified body");
                values.truncate(value_base);
                values.push(BehavioralPred::Quantified {
                    quantifier: quantifier.clone(),
                    var: var.clone(),
                    domain: domain.clone(),
                    bound: *bound,
                    body: Box::new(body),
                });
            },
            BehavioralCloneTask::And(value_base) => {
                let right = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary right operand");
                let left = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary left operand");
                values.truncate(value_base);
                values.push(BehavioralPred::And(Box::new(left), Box::new(right)));
            },
            BehavioralCloneTask::Or(value_base) => {
                let right = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary right operand");
                let left = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary left operand");
                values.truncate(value_base);
                values.push(BehavioralPred::Or(Box::new(left), Box::new(right)));
            },
            BehavioralCloneTask::Implies(value_base) => {
                let right = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary right operand");
                let left = values
                    .pop()
                    .expect("behavioral clone PDA lost a binary left operand");
                values.truncate(value_base);
                values.push(BehavioralPred::Implies(Box::new(left), Box::new(right)));
            },
            BehavioralCloneTask::Not(value_base) => {
                let inner = values
                    .pop()
                    .expect("behavioral clone PDA lost a negated operand");
                values.truncate(value_base);
                values.push(BehavioralPred::Not(Box::new(inner)));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("behavioral clone PDA produced no result")
}

impl Clone for BehavioralPred {
    fn clone(&self) -> Self {
        clone_behavioral_predicate(self)
    }
}

fn take_behavioral_children(pred: &mut BehavioralPred, work: &mut Vec<BehavioralPred>) {
    let take =
        |child: &mut Box<BehavioralPred>| *std::mem::replace(child, Box::new(BehavioralPred::Top));
    match pred {
        BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
            work.push(take(body));
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        BehavioralPred::RelationQuery { .. }
        | BehavioralPred::AcMatch { .. }
        | BehavioralPred::Top => {},
    }
}

impl Drop for BehavioralPred {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_behavioral_children(self, &mut work);
        while let Some(mut pred) = work.pop() {
            take_behavioral_children(&mut pred, &mut work);
        }
    }
}

impl Clone for Premise {
    fn clone(&self) -> Self {
        let mut wrappers = Vec::new();
        let mut current = self;
        while let Premise::ForAll { collection, param, body } = current {
            wrappers.push((collection.clone(), param.clone()));
            current = body;
        }
        let mut cloned = match current {
            Premise::Freshness(condition) => Premise::Freshness(condition.clone()),
            Premise::Congruence { source, target } => Premise::Congruence {
                source: source.clone(),
                target: target.clone(),
            },
            Premise::CongruenceWithheld { source, target } => Premise::CongruenceWithheld {
                source: source.clone(),
                target: target.clone(),
            },
            Premise::RelationQuery { relation, args } => Premise::RelationQuery {
                relation: relation.clone(),
                args: args.clone(),
            },
            Premise::BehavioralGuard(predicate) => Premise::BehavioralGuard(predicate.clone()),
            Premise::SyntheticInjGuard {
                inner_var,
                source_category,
                excluded_variants,
            } => Premise::SyntheticInjGuard {
                inner_var: inner_var.clone(),
                source_category: source_category.clone(),
                excluded_variants: excluded_variants.clone(),
            },
            Premise::ForAll { .. } => unreachable!("ForAll spine was consumed above"),
        };
        for (collection, param) in wrappers.into_iter().rev() {
            cloned = Premise::ForAll {
                collection,
                param,
                body: Box::new(cloned),
            };
        }
        cloned
    }
}

impl Clone for Condition {
    fn clone(&self) -> Self {
        let mut wrappers = Vec::new();
        let mut current = self;
        while let Condition::ForAll { collection, param, body } = current {
            wrappers.push((collection.clone(), param.clone()));
            current = body;
        }
        let mut cloned = match current {
            Condition::Freshness(condition) => Condition::Freshness(condition.clone()),
            Condition::EnvQuery { relation, args } => Condition::EnvQuery {
                relation: relation.clone(),
                args: args.clone(),
            },
            Condition::BehavioralGuard(predicate) => Condition::BehavioralGuard(predicate.clone()),
            Condition::SyntheticInjGuard {
                inner_var,
                source_category,
                excluded_variants,
            } => Condition::SyntheticInjGuard {
                inner_var: inner_var.clone(),
                source_category: source_category.clone(),
                excluded_variants: excluded_variants.clone(),
            },
            Condition::ForAll { .. } => unreachable!("ForAll spine was consumed above"),
        };
        for (collection, param) in wrappers.into_iter().rev() {
            cloned = Condition::ForAll {
                collection,
                param,
                body: Box::new(cloned),
            };
        }
        cloned
    }
}

fn condition_placeholder() -> Condition {
    Condition::EnvQuery {
        relation: syn::Ident::new("_", proc_macro2::Span::call_site()),
        args: Vec::new(),
    }
}

fn take_condition_children(condition: &mut Condition, work: &mut Vec<Condition>) {
    if let Condition::ForAll { body, .. } = condition {
        work.push(*std::mem::replace(body, Box::new(condition_placeholder())));
    }
}

impl Drop for Condition {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_condition_children(self, &mut work);
        while let Some(mut condition) = work.pop() {
            take_condition_children(&mut condition, &mut work);
        }
    }
}

enum FormulaTask<'pred> {
    Visit(&'pred BehavioralPred),
    Quantified {
        quantifier: &'pred Quantifier,
        var: &'pred syn::Ident,
        domain: &'pred Option<syn::Ident>,
        bound: Option<usize>,
    },
    AfterLeft {
        kind: BinaryFormula,
        right: &'pred BehavioralPred,
    },
    Binary {
        kind: BinaryFormula,
        left: TokenStream,
    },
    Not,
}

#[derive(Clone, Copy)]
enum BinaryFormula {
    And,
    Or,
    Implies,
}

pub(super) fn behavioral_pred_to_quantified_formula(
    root: &BehavioralPred,
) -> Result<TokenStream, String> {
    let mut tasks = vec![FormulaTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            FormulaTask::Visit(BehavioralPred::RelationQuery { relation_name, args, negated }) => {
                let relation = relation_name.to_string();
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| match arg {
                        PredArg::Var(var) => {
                            let var = var.to_string();
                            quote! { prattail::logict::QuantifiedArg::Var(#var.to_string()) }
                        },
                        PredArg::Constant(constant) => {
                            let constant = constant.to_string();
                            quote! { prattail::logict::QuantifiedArg::Constant(#constant.to_string()) }
                        },
                    })
                    .collect();
                let atom = quote! {
                    prattail::logict::QuantifiedFormula::atom(
                        #relation,
                        vec![#(#args),*],
                    )
                };
                values.push(if *negated {
                    quote! { prattail::logict::QuantifiedFormula::not(#atom) }
                } else {
                    atom
                });
            },
            FormulaTask::Visit(BehavioralPred::Quantified {
                quantifier,
                var,
                domain,
                bound,
                body,
            }) => {
                tasks.push(FormulaTask::Quantified { quantifier, var, domain, bound: *bound });
                tasks.push(FormulaTask::Visit(body));
            },
            FormulaTask::Visit(BehavioralPred::And(left, right)) => {
                tasks.push(FormulaTask::AfterLeft { kind: BinaryFormula::And, right });
                tasks.push(FormulaTask::Visit(left));
            },
            FormulaTask::Visit(BehavioralPred::Or(left, right)) => {
                tasks.push(FormulaTask::AfterLeft { kind: BinaryFormula::Or, right });
                tasks.push(FormulaTask::Visit(left));
            },
            FormulaTask::Visit(BehavioralPred::Not(inner)) => {
                tasks.push(FormulaTask::Not);
                tasks.push(FormulaTask::Visit(inner));
            },
            FormulaTask::Visit(BehavioralPred::Implies(left, right)) => {
                tasks.push(FormulaTask::AfterLeft { kind: BinaryFormula::Implies, right });
                tasks.push(FormulaTask::Visit(left));
            },
            FormulaTask::Visit(BehavioralPred::AcMatch { .. }) => {
                return Err("ac_match behavioral predicates require specialized Ascent partition lowering and cannot be embedded in QuantifiedFormula".to_string());
            },
            FormulaTask::Visit(BehavioralPred::Top) => values.push(quote! {
                prattail::logict::QuantifiedFormula::atom(
                    "__top__",
                    vec![],
                )
            }),
            FormulaTask::Quantified { quantifier, var, domain, bound } => {
                let body = values
                    .pop()
                    .expect("behavioral formula PDA lost a quantified body");
                let var = var.to_string();
                let domain = if let Some(domain) = domain {
                    let relation = domain.to_string();
                    if let Some(limit) = bound {
                        quote! {
                            prattail::logict::QuantifiedDomain::Bounded {
                                relation: #relation.to_string(),
                                limit: #limit,
                            }
                        }
                    } else {
                        quote! {
                            prattail::logict::QuantifiedDomain::Relation(#relation.to_string())
                        }
                    }
                } else {
                    quote! {
                        prattail::logict::QuantifiedDomain::Relation(#var.to_string())
                    }
                };
                values.push(match quantifier {
                    Quantifier::ForAll => quote! {
                        prattail::logict::QuantifiedFormula::forall(#var, #domain, #body)
                    },
                    Quantifier::Exists => quote! {
                        prattail::logict::QuantifiedFormula::exists(#var, #domain, #body)
                    },
                });
            },
            FormulaTask::AfterLeft { kind, right } => {
                let left = values
                    .pop()
                    .expect("behavioral formula PDA lost a binary left operand");
                tasks.push(FormulaTask::Binary { kind, left });
                tasks.push(FormulaTask::Visit(right));
            },
            FormulaTask::Binary { kind, left } => {
                let right = values
                    .pop()
                    .expect("behavioral formula PDA lost a binary right operand");
                values.push(match kind {
                    BinaryFormula::And => quote! {
                        prattail::logict::QuantifiedFormula::and(#left, #right)
                    },
                    BinaryFormula::Or => quote! {
                        prattail::logict::QuantifiedFormula::or(#left, #right)
                    },
                    BinaryFormula::Implies => quote! {
                        prattail::logict::QuantifiedFormula::implies(#left, #right)
                    },
                });
            },
            FormulaTask::Not => {
                let inner = values
                    .pop()
                    .expect("behavioral formula PDA lost a negated operand");
                values.push(quote! {
                    prattail::logict::QuantifiedFormula::not(#inner)
                });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("behavioral formula PDA produced no result"))
}

#[derive(Clone, Copy)]
enum RefinementBinary {
    And,
    Or,
    Implies,
}

enum RefinementCloneTask<'pred> {
    Visit(&'pred RefinementPredicate),
    Quantified(&'pred RefinementPredicate, usize),
    Binary(RefinementBinary, usize),
    Not(usize),
}

impl Clone for RefinementPredicate {
    fn clone(&self) -> Self {
        let mut tasks = vec![RefinementCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                RefinementCloneTask::Visit(RefinementPredicate::Linear {
                    terms,
                    relation,
                    rhs,
                }) => values.push(RefinementPredicate::Linear {
                    terms: terms.clone(),
                    relation: relation.clone(),
                    rhs: *rhs,
                }),
                RefinementCloneTask::Visit(RefinementPredicate::Relation {
                    name,
                    args,
                    negated,
                }) => values.push(RefinementPredicate::Relation {
                    name: name.clone(),
                    args: args.clone(),
                    negated: *negated,
                }),
                RefinementCloneTask::Visit(
                    source @ RefinementPredicate::Quantified { body, .. },
                ) => {
                    tasks.push(RefinementCloneTask::Quantified(source, values.len()));
                    tasks.push(RefinementCloneTask::Visit(body));
                },
                RefinementCloneTask::Visit(RefinementPredicate::And(left, right)) => {
                    tasks.push(RefinementCloneTask::Binary(RefinementBinary::And, values.len()));
                    tasks.push(RefinementCloneTask::Visit(right));
                    tasks.push(RefinementCloneTask::Visit(left));
                },
                RefinementCloneTask::Visit(RefinementPredicate::Or(left, right)) => {
                    tasks.push(RefinementCloneTask::Binary(RefinementBinary::Or, values.len()));
                    tasks.push(RefinementCloneTask::Visit(right));
                    tasks.push(RefinementCloneTask::Visit(left));
                },
                RefinementCloneTask::Visit(RefinementPredicate::Not(inner)) => {
                    tasks.push(RefinementCloneTask::Not(values.len()));
                    tasks.push(RefinementCloneTask::Visit(inner));
                },
                RefinementCloneTask::Visit(RefinementPredicate::Implies(left, right)) => {
                    tasks
                        .push(RefinementCloneTask::Binary(RefinementBinary::Implies, values.len()));
                    tasks.push(RefinementCloneTask::Visit(right));
                    tasks.push(RefinementCloneTask::Visit(left));
                },
                RefinementCloneTask::Visit(RefinementPredicate::TermEq(left, right)) => {
                    values.push(RefinementPredicate::TermEq(left.clone(), right.clone()));
                },
                RefinementCloneTask::Visit(RefinementPredicate::TermNeq(left, right)) => {
                    values.push(RefinementPredicate::TermNeq(left.clone(), right.clone()));
                },
                RefinementCloneTask::Quantified(source, value_base) => {
                    let RefinementPredicate::Quantified { quantifier, var, domain, bound, .. } =
                        source
                    else {
                        unreachable!("quantified clone task carries a quantified predicate")
                    };
                    let body = values
                        .pop()
                        .expect("refinement clone PDA lost a quantified body");
                    values.truncate(value_base);
                    values.push(RefinementPredicate::Quantified {
                        quantifier: quantifier.clone(),
                        var: var.clone(),
                        domain: domain.clone(),
                        bound: *bound,
                        body: Box::new(body),
                    });
                },
                RefinementCloneTask::Binary(kind, value_base) => {
                    let right = values
                        .pop()
                        .expect("refinement clone PDA lost a binary right operand");
                    let left = values
                        .pop()
                        .expect("refinement clone PDA lost a binary left operand");
                    values.truncate(value_base);
                    values.push(match kind {
                        RefinementBinary::And => {
                            RefinementPredicate::And(Box::new(left), Box::new(right))
                        },
                        RefinementBinary::Or => {
                            RefinementPredicate::Or(Box::new(left), Box::new(right))
                        },
                        RefinementBinary::Implies => {
                            RefinementPredicate::Implies(Box::new(left), Box::new(right))
                        },
                    });
                },
                RefinementCloneTask::Not(value_base) => {
                    let inner = values
                        .pop()
                        .expect("refinement clone PDA lost a negated operand");
                    values.truncate(value_base);
                    values.push(RefinementPredicate::Not(Box::new(inner)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("refinement clone PDA produced no result")
    }
}

fn refinement_placeholder() -> RefinementPredicate {
    RefinementPredicate::Linear {
        terms: Vec::new(),
        relation: LinearRelation::Eq,
        rhs: 0,
    }
}

fn take_refinement_children(
    predicate: &mut RefinementPredicate,
    work: &mut Vec<RefinementPredicate>,
) {
    let take = |child: &mut Box<RefinementPredicate>| {
        *std::mem::replace(child, Box::new(refinement_placeholder()))
    };
    match predicate {
        RefinementPredicate::Quantified { body, .. } | RefinementPredicate::Not(body) => {
            work.push(take(body));
        },
        RefinementPredicate::And(left, right)
        | RefinementPredicate::Or(left, right)
        | RefinementPredicate::Implies(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        RefinementPredicate::Linear { .. }
        | RefinementPredicate::Relation { .. }
        | RefinementPredicate::TermEq(..)
        | RefinementPredicate::TermNeq(..) => {},
    }
}

impl Drop for RefinementPredicate {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_refinement_children(self, &mut work);
        while let Some(mut predicate) = work.pop() {
            take_refinement_children(&mut predicate, &mut work);
        }
    }
}

enum RefinementDebugTask<'pred> {
    Visit(&'pred RefinementPredicate, usize),
    PredArg(&'pred PredArg, usize),
    PredArgs(&'pred [PredArg], usize),
    Ident(&'pred syn::Ident, usize),
    OptionIdent(&'pred Option<syn::Ident>, usize),
    OptionUsize(Option<usize>, usize),
    Terms(&'pred [(syn::Ident, i64)], usize),
    Term(&'pred (syn::Ident, i64), usize),
    Quantifier(&'pred Quantifier),
    Relation(&'pred LinearRelation),
    Bool(bool),
    I64(i64),
    Usize(usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
    CloseList(usize),
}

fn push_refinement_debug_field<'pred>(
    tasks: &mut Vec<RefinementDebugTask<'pred>>,
    name: &'static str,
    value: RefinementDebugTask<'pred>,
    indent: usize,
) {
    tasks.push(RefinementDebugTask::Text(",\n"));
    tasks.push(value);
    tasks.push(RefinementDebugTask::Text(name));
    tasks.push(RefinementDebugTask::Indent(indent));
}

fn push_refinement_debug_tuple<'pred>(
    tasks: &mut Vec<RefinementDebugTask<'pred>>,
    value: RefinementDebugTask<'pred>,
    indent: usize,
) {
    tasks.push(RefinementDebugTask::CloseTuple(indent));
    tasks.push(RefinementDebugTask::Text(",\n"));
    tasks.push(value);
    tasks.push(RefinementDebugTask::Indent(indent + 1));
}

fn fmt_refinement_debug_at(
    root: &RefinementPredicate,
    root_indent: usize,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let pretty = formatter.alternate();
    let mut tasks = vec![RefinementDebugTask::Visit(root, root_indent)];
    while let Some(task) = tasks.pop() {
        match task {
            RefinementDebugTask::Text(text) => formatter.write_str(text)?,
            RefinementDebugTask::Indent(indent) => write_model_debug_indent(formatter, indent)?,
            RefinementDebugTask::CloseTuple(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str(")")?;
            },
            RefinementDebugTask::CloseStruct(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("}")?;
            },
            RefinementDebugTask::CloseList(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("]")?;
            },
            RefinementDebugTask::Ident(ident, indent) => {
                fmt_model_ident(ident, indent, pretty, formatter)?;
            },
            RefinementDebugTask::Quantifier(quantifier) => write!(formatter, "{quantifier:?}")?,
            RefinementDebugTask::Relation(relation) => write!(formatter, "{relation:?}")?,
            RefinementDebugTask::Bool(value) => write!(formatter, "{value}")?,
            RefinementDebugTask::I64(value) => write!(formatter, "{value}")?,
            RefinementDebugTask::Usize(value) => write!(formatter, "{value}")?,
            RefinementDebugTask::OptionIdent(None, _) => formatter.write_str("None")?,
            RefinementDebugTask::OptionIdent(Some(ident), _) if !pretty => {
                formatter.write_str("Some(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Ident(ident, 0));
            },
            RefinementDebugTask::OptionIdent(Some(ident), indent) => {
                formatter.write_str("Some(\n")?;
                push_refinement_debug_tuple(
                    &mut tasks,
                    RefinementDebugTask::Ident(ident, indent + 1),
                    indent,
                );
            },
            RefinementDebugTask::OptionUsize(None, _) => formatter.write_str("None")?,
            RefinementDebugTask::OptionUsize(Some(value), _) if !pretty => {
                write!(formatter, "Some({value})")?;
            },
            RefinementDebugTask::OptionUsize(Some(value), indent) => {
                formatter.write_str("Some(\n")?;
                push_refinement_debug_tuple(&mut tasks, RefinementDebugTask::Usize(value), indent);
            },
            RefinementDebugTask::PredArg(PredArg::Var(ident), _) if !pretty => {
                formatter.write_str("Var(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Ident(ident, 0));
            },
            RefinementDebugTask::PredArg(PredArg::Constant(ident), _) if !pretty => {
                formatter.write_str("Constant(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Ident(ident, 0));
            },
            RefinementDebugTask::PredArg(argument, indent) => {
                formatter.write_str(match argument {
                    PredArg::Var(_) => "Var(\n",
                    PredArg::Constant(_) => "Constant(\n",
                })?;
                let ident = match argument {
                    PredArg::Var(ident) | PredArg::Constant(ident) => ident,
                };
                push_refinement_debug_tuple(
                    &mut tasks,
                    RefinementDebugTask::Ident(ident, indent + 1),
                    indent,
                );
            },
            RefinementDebugTask::PredArgs([], _) => formatter.write_str("[]")?,
            RefinementDebugTask::PredArgs(arguments, _) if !pretty => {
                formatter.write_str("[")?;
                tasks.push(RefinementDebugTask::Text("]"));
                for (index, argument) in arguments.iter().enumerate().rev() {
                    tasks.push(RefinementDebugTask::PredArg(argument, 0));
                    if index != 0 {
                        tasks.push(RefinementDebugTask::Text(", "));
                    }
                }
            },
            RefinementDebugTask::PredArgs(arguments, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(RefinementDebugTask::CloseList(indent));
                for argument in arguments.iter().rev() {
                    tasks.push(RefinementDebugTask::Text(",\n"));
                    tasks.push(RefinementDebugTask::PredArg(argument, indent + 1));
                    tasks.push(RefinementDebugTask::Indent(indent + 1));
                }
            },
            RefinementDebugTask::Term((ident, coefficient), _) if !pretty => {
                formatter.write_str("(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::I64(*coefficient));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::Ident(ident, 0));
            },
            RefinementDebugTask::Term((ident, coefficient), indent) => {
                formatter.write_str("(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::I64(*coefficient));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Ident(ident, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Terms([], _) => formatter.write_str("[]")?,
            RefinementDebugTask::Terms(terms, _) if !pretty => {
                formatter.write_str("[")?;
                tasks.push(RefinementDebugTask::Text("]"));
                for (index, term) in terms.iter().enumerate().rev() {
                    tasks.push(RefinementDebugTask::Term(term, 0));
                    if index != 0 {
                        tasks.push(RefinementDebugTask::Text(", "));
                    }
                }
            },
            RefinementDebugTask::Terms(terms, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(RefinementDebugTask::CloseList(indent));
                for term in terms.iter().rev() {
                    tasks.push(RefinementDebugTask::Text(",\n"));
                    tasks.push(RefinementDebugTask::Term(term, indent + 1));
                    tasks.push(RefinementDebugTask::Indent(indent + 1));
                }
            },
            RefinementDebugTask::Visit(
                RefinementPredicate::Linear { terms, relation, rhs },
                indent,
            ) if pretty => {
                formatter.write_str("Linear {\n")?;
                tasks.push(RefinementDebugTask::CloseStruct(indent));
                push_refinement_debug_field(
                    &mut tasks,
                    "rhs: ",
                    RefinementDebugTask::I64(*rhs),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "relation: ",
                    RefinementDebugTask::Relation(relation),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "terms: ",
                    RefinementDebugTask::Terms(terms, indent + 1),
                    indent + 1,
                );
            },
            RefinementDebugTask::Visit(
                RefinementPredicate::Relation { name, args, negated },
                indent,
            ) if pretty => {
                formatter.write_str("Relation {\n")?;
                tasks.push(RefinementDebugTask::CloseStruct(indent));
                push_refinement_debug_field(
                    &mut tasks,
                    "negated: ",
                    RefinementDebugTask::Bool(*negated),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "args: ",
                    RefinementDebugTask::PredArgs(args, indent + 1),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "name: ",
                    RefinementDebugTask::Ident(name, indent + 1),
                    indent + 1,
                );
            },
            RefinementDebugTask::Visit(
                RefinementPredicate::Quantified { quantifier, var, domain, bound, body },
                indent,
            ) if pretty => {
                formatter.write_str("Quantified {\n")?;
                tasks.push(RefinementDebugTask::CloseStruct(indent));
                push_refinement_debug_field(
                    &mut tasks,
                    "body: ",
                    RefinementDebugTask::Visit(body, indent + 1),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "bound: ",
                    RefinementDebugTask::OptionUsize(*bound, indent + 1),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "domain: ",
                    RefinementDebugTask::OptionIdent(domain, indent + 1),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "var: ",
                    RefinementDebugTask::Ident(var, indent + 1),
                    indent + 1,
                );
                push_refinement_debug_field(
                    &mut tasks,
                    "quantifier: ",
                    RefinementDebugTask::Quantifier(quantifier),
                    indent + 1,
                );
            },
            RefinementDebugTask::Visit(RefinementPredicate::And(left, right), indent) if pretty => {
                formatter.write_str("And(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(right, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(left, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Or(left, right), indent) if pretty => {
                formatter.write_str("Or(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(right, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(left, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Not(inner), indent) if pretty => {
                formatter.write_str("Not(\n")?;
                push_refinement_debug_tuple(
                    &mut tasks,
                    RefinementDebugTask::Visit(inner, indent + 1),
                    indent,
                );
            },
            RefinementDebugTask::Visit(RefinementPredicate::Implies(left, right), indent)
                if pretty =>
            {
                formatter.write_str("Implies(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(right, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::Visit(left, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Visit(RefinementPredicate::TermEq(left, right), indent)
                if pretty =>
            {
                formatter.write_str("TermEq(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::PredArg(right, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::PredArg(left, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Visit(RefinementPredicate::TermNeq(left, right), indent)
                if pretty =>
            {
                formatter.write_str("TermNeq(\n")?;
                tasks.push(RefinementDebugTask::CloseTuple(indent));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::PredArg(right, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
                tasks.push(RefinementDebugTask::Text(",\n"));
                tasks.push(RefinementDebugTask::PredArg(left, indent + 1));
                tasks.push(RefinementDebugTask::Indent(indent + 1));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Linear { terms, relation, rhs }, _) => {
                formatter.write_str("Linear { terms: ")?;
                tasks.push(RefinementDebugTask::Text(" }"));
                tasks.push(RefinementDebugTask::I64(*rhs));
                tasks.push(RefinementDebugTask::Text(", rhs: "));
                tasks.push(RefinementDebugTask::Relation(relation));
                tasks.push(RefinementDebugTask::Text(", relation: "));
                tasks.push(RefinementDebugTask::Terms(terms, 0));
            },
            RefinementDebugTask::Visit(
                RefinementPredicate::Relation { name, args, negated },
                _,
            ) => {
                formatter.write_str("Relation { name: ")?;
                tasks.push(RefinementDebugTask::Text(" }"));
                tasks.push(RefinementDebugTask::Bool(*negated));
                tasks.push(RefinementDebugTask::Text(", negated: "));
                tasks.push(RefinementDebugTask::PredArgs(args, 0));
                tasks.push(RefinementDebugTask::Text(", args: "));
                tasks.push(RefinementDebugTask::Ident(name, 0));
            },
            RefinementDebugTask::Visit(
                RefinementPredicate::Quantified { quantifier, var, domain, bound, body },
                _,
            ) => {
                formatter.write_str("Quantified { quantifier: ")?;
                tasks.push(RefinementDebugTask::Text(" }"));
                tasks.push(RefinementDebugTask::Visit(body, 0));
                tasks.push(RefinementDebugTask::Text(", body: "));
                tasks.push(RefinementDebugTask::OptionUsize(*bound, 0));
                tasks.push(RefinementDebugTask::Text(", bound: "));
                tasks.push(RefinementDebugTask::OptionIdent(domain, 0));
                tasks.push(RefinementDebugTask::Text(", domain: "));
                tasks.push(RefinementDebugTask::Ident(var, 0));
                tasks.push(RefinementDebugTask::Text(", var: "));
                tasks.push(RefinementDebugTask::Quantifier(quantifier));
            },
            RefinementDebugTask::Visit(RefinementPredicate::And(left, right), _) => {
                formatter.write_str("And(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Visit(right, 0));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::Visit(left, 0));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Or(left, right), _) => {
                formatter.write_str("Or(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Visit(right, 0));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::Visit(left, 0));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Not(inner), _) => {
                formatter.write_str("Not(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Visit(inner, 0));
            },
            RefinementDebugTask::Visit(RefinementPredicate::Implies(left, right), _) => {
                formatter.write_str("Implies(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::Visit(right, 0));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::Visit(left, 0));
            },
            RefinementDebugTask::Visit(RefinementPredicate::TermEq(left, right), _) => {
                formatter.write_str("TermEq(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::PredArg(right, 0));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::PredArg(left, 0));
            },
            RefinementDebugTask::Visit(RefinementPredicate::TermNeq(left, right), _) => {
                formatter.write_str("TermNeq(")?;
                tasks.push(RefinementDebugTask::Text(")"));
                tasks.push(RefinementDebugTask::PredArg(right, 0));
                tasks.push(RefinementDebugTask::Text(", "));
                tasks.push(RefinementDebugTask::PredArg(left, 0));
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for RefinementPredicate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_refinement_debug_at(self, 0, formatter)
    }
}

enum RefinementDisplayTask<'pred> {
    Visit(&'pred RefinementPredicate),
    Text(&'static str),
}

pub(super) fn fmt_refinement_predicate(
    root: &RefinementPredicate,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let mut tasks = vec![RefinementDisplayTask::Visit(root)];
    while let Some(task) = tasks.pop() {
        match task {
            RefinementDisplayTask::Text(text) => formatter.write_str(text)?,
            RefinementDisplayTask::Visit(RefinementPredicate::Linear { terms, relation, rhs }) => {
                for (index, (variable, coefficient)) in terms.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(" + ")?;
                    }
                    if *coefficient == 1 {
                        write!(formatter, "{variable}")?;
                    } else {
                        write!(formatter, "{coefficient}*{variable}")?;
                    }
                }
                write!(formatter, " {relation} {rhs}")?;
            },
            RefinementDisplayTask::Visit(RefinementPredicate::Relation { name, args, negated }) => {
                if *negated {
                    formatter.write_str("~")?;
                }
                write!(formatter, "{name}(")?;
                for (index, arg) in args.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(", ")?;
                    }
                    match arg {
                        PredArg::Var(variable) | PredArg::Constant(variable) => {
                            write!(formatter, "{variable}")?;
                        },
                    }
                }
                formatter.write_str(")")?;
            },
            RefinementDisplayTask::Visit(RefinementPredicate::Quantified {
                quantifier,
                var,
                domain,
                bound,
                body,
            }) => {
                formatter.write_str(match quantifier {
                    Quantifier::ForAll => "forall",
                    Quantifier::Exists => "exists",
                })?;
                if let Some(bound) = bound {
                    write!(formatter, "_{{k={bound}}}")?;
                }
                write!(formatter, " {var}")?;
                if let Some(domain) = domain {
                    write!(formatter, " in {domain}")?;
                }
                formatter.write_str(". (")?;
                tasks.push(RefinementDisplayTask::Text(")"));
                tasks.push(RefinementDisplayTask::Visit(body));
            },
            RefinementDisplayTask::Visit(RefinementPredicate::And(left, right)) => {
                formatter.write_str("(")?;
                tasks.push(RefinementDisplayTask::Text(")"));
                tasks.push(RefinementDisplayTask::Visit(right));
                tasks.push(RefinementDisplayTask::Text(" && "));
                tasks.push(RefinementDisplayTask::Visit(left));
            },
            RefinementDisplayTask::Visit(RefinementPredicate::Or(left, right)) => {
                formatter.write_str("(")?;
                tasks.push(RefinementDisplayTask::Text(")"));
                tasks.push(RefinementDisplayTask::Visit(right));
                tasks.push(RefinementDisplayTask::Text(" || "));
                tasks.push(RefinementDisplayTask::Visit(left));
            },
            RefinementDisplayTask::Visit(RefinementPredicate::Not(inner)) => {
                formatter.write_str("~")?;
                tasks.push(RefinementDisplayTask::Visit(inner));
            },
            RefinementDisplayTask::Visit(RefinementPredicate::Implies(left, right)) => {
                formatter.write_str("(")?;
                tasks.push(RefinementDisplayTask::Text(")"));
                tasks.push(RefinementDisplayTask::Visit(right));
                tasks.push(RefinementDisplayTask::Text(" => "));
                tasks.push(RefinementDisplayTask::Visit(left));
            },
            RefinementDisplayTask::Visit(RefinementPredicate::TermEq(left, right)) => {
                fmt_pred_arg_display(left, formatter)?;
                formatter.write_str(" == ")?;
                fmt_pred_arg_display(right, formatter)?;
            },
            RefinementDisplayTask::Visit(RefinementPredicate::TermNeq(left, right)) => {
                fmt_pred_arg_display(left, formatter)?;
                formatter.write_str(" != ")?;
                fmt_pred_arg_display(right, formatter)?;
            },
        }
    }
    Ok(())
}

fn fmt_pred_arg_display(
    argument: &PredArg,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match argument {
        PredArg::Var(value) | PredArg::Constant(value) => write!(formatter, "{value}"),
    }
}

pub(super) fn classify_refinement_predicate(root: &RefinementPredicate) -> ConstraintDomain {
    let mut tasks = vec![root];
    let mut domains = Vec::with_capacity(4);
    let mut seen = [false; 4];
    while let Some(predicate) = tasks.pop() {
        let domain = match predicate {
            RefinementPredicate::Linear { .. } => Some((0, ConstraintDomain::Presburger)),
            RefinementPredicate::Relation { .. } | RefinementPredicate::Quantified { .. } => {
                Some((2, ConstraintDomain::Behavioral))
            },
            RefinementPredicate::TermEq(..) | RefinementPredicate::TermNeq(..) => {
                Some((3, ConstraintDomain::Unification))
            },
            RefinementPredicate::Not(inner) => {
                tasks.push(inner);
                None
            },
            RefinementPredicate::And(left, right)
            | RefinementPredicate::Or(left, right)
            | RefinementPredicate::Implies(left, right) => {
                tasks.push(right);
                tasks.push(left);
                None
            },
        };
        if let Some((index, domain)) = domain {
            if !seen[index] {
                seen[index] = true;
                domains.push(domain);
            }
        }
    }
    if domains.len() == 1 {
        domains
            .pop()
            .expect("a refinement predicate always has one leaf domain")
    } else {
        ConstraintDomain::Product(domains)
    }
}

enum DomainCloneTask<'domain> {
    Visit(&'domain ConstraintDomain),
    Product { value_base: usize, child_count: usize },
}

impl Clone for ConstraintDomain {
    fn clone(&self) -> Self {
        let mut tasks = vec![DomainCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                DomainCloneTask::Visit(ConstraintDomain::Presburger) => {
                    values.push(ConstraintDomain::Presburger);
                },
                DomainCloneTask::Visit(ConstraintDomain::Lattice) => {
                    values.push(ConstraintDomain::Lattice);
                },
                DomainCloneTask::Visit(ConstraintDomain::Behavioral) => {
                    values.push(ConstraintDomain::Behavioral);
                },
                DomainCloneTask::Visit(ConstraintDomain::Unification) => {
                    values.push(ConstraintDomain::Unification);
                },
                DomainCloneTask::Visit(ConstraintDomain::Product(children)) => {
                    tasks.push(DomainCloneTask::Product {
                        value_base: values.len(),
                        child_count: children.len(),
                    });
                    for child in children.iter().rev() {
                        tasks.push(DomainCloneTask::Visit(child));
                    }
                },
                DomainCloneTask::Product { value_base, child_count } => {
                    debug_assert_eq!(values.len(), value_base + child_count);
                    let children = values.split_off(value_base);
                    values.push(ConstraintDomain::Product(children));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("domain clone PDA produced no result")
    }
}

impl Drop for ConstraintDomain {
    fn drop(&mut self) {
        let mut work = match self {
            ConstraintDomain::Product(children) => std::mem::take(children),
            ConstraintDomain::Presburger
            | ConstraintDomain::Lattice
            | ConstraintDomain::Behavioral
            | ConstraintDomain::Unification => return,
        };
        while let Some(mut domain) = work.pop() {
            if let ConstraintDomain::Product(children) = &mut domain {
                work.append(children);
            }
        }
    }
}

impl PartialEq for ConstraintDomain {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (ConstraintDomain::Presburger, ConstraintDomain::Presburger)
                | (ConstraintDomain::Lattice, ConstraintDomain::Lattice)
                | (ConstraintDomain::Behavioral, ConstraintDomain::Behavioral)
                | (ConstraintDomain::Unification, ConstraintDomain::Unification) => {},
                (ConstraintDomain::Product(left), ConstraintDomain::Product(right))
                    if left.len() == right.len() =>
                {
                    work.extend(left.iter().zip(right).rev());
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for ConstraintDomain {}

enum DomainDebugTask<'domain> {
    Visit(&'domain ConstraintDomain, usize),
    List(&'domain [ConstraintDomain], usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseList(usize),
}

fn fmt_constraint_domain_debug(
    root: &ConstraintDomain,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let pretty = formatter.alternate();
    let mut tasks = vec![DomainDebugTask::Visit(root, 0)];
    while let Some(task) = tasks.pop() {
        match task {
            DomainDebugTask::Text(text) => formatter.write_str(text)?,
            DomainDebugTask::Indent(indent) => write_model_debug_indent(formatter, indent)?,
            DomainDebugTask::CloseTuple(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str(")")?;
            },
            DomainDebugTask::CloseList(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("]")?;
            },
            DomainDebugTask::Visit(ConstraintDomain::Presburger, _) => {
                formatter.write_str("Presburger")?;
            },
            DomainDebugTask::Visit(ConstraintDomain::Lattice, _) => {
                formatter.write_str("Lattice")?;
            },
            DomainDebugTask::Visit(ConstraintDomain::Behavioral, _) => {
                formatter.write_str("Behavioral")?;
            },
            DomainDebugTask::Visit(ConstraintDomain::Unification, _) => {
                formatter.write_str("Unification")?;
            },
            DomainDebugTask::Visit(ConstraintDomain::Product(children), indent) if pretty => {
                formatter.write_str("Product(\n")?;
                tasks.push(DomainDebugTask::CloseTuple(indent));
                tasks.push(DomainDebugTask::Text(",\n"));
                tasks.push(DomainDebugTask::List(children, indent + 1));
                tasks.push(DomainDebugTask::Indent(indent + 1));
            },
            DomainDebugTask::Visit(ConstraintDomain::Product(children), _) => {
                formatter.write_str("Product(")?;
                tasks.push(DomainDebugTask::Text(")"));
                tasks.push(DomainDebugTask::List(children, 0));
            },
            DomainDebugTask::List([], _) => formatter.write_str("[]")?,
            DomainDebugTask::List(children, _) if !pretty => {
                formatter.write_str("[")?;
                tasks.push(DomainDebugTask::Text("]"));
                for (index, child) in children.iter().enumerate().rev() {
                    tasks.push(DomainDebugTask::Visit(child, 0));
                    if index != 0 {
                        tasks.push(DomainDebugTask::Text(", "));
                    }
                }
            },
            DomainDebugTask::List(children, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(DomainDebugTask::CloseList(indent));
                for child in children.iter().rev() {
                    tasks.push(DomainDebugTask::Text(",\n"));
                    tasks.push(DomainDebugTask::Visit(child, indent + 1));
                    tasks.push(DomainDebugTask::Indent(indent + 1));
                }
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for ConstraintDomain {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_constraint_domain_debug(self, formatter)
    }
}

enum DomainDisplayTask<'domain> {
    Visit(&'domain ConstraintDomain),
    Text(&'static str),
}

pub(super) fn fmt_constraint_domain(
    root: &ConstraintDomain,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let mut tasks = vec![DomainDisplayTask::Visit(root)];
    while let Some(task) = tasks.pop() {
        match task {
            DomainDisplayTask::Text(text) => formatter.write_str(text)?,
            DomainDisplayTask::Visit(ConstraintDomain::Presburger) => {
                formatter.write_str("Presburger")?;
            },
            DomainDisplayTask::Visit(ConstraintDomain::Lattice) => {
                formatter.write_str("Lattice")?;
            },
            DomainDisplayTask::Visit(ConstraintDomain::Behavioral) => {
                formatter.write_str("Behavioral")?;
            },
            DomainDisplayTask::Visit(ConstraintDomain::Unification) => {
                formatter.write_str("Unification")?;
            },
            DomainDisplayTask::Visit(ConstraintDomain::Product(children)) => {
                formatter.write_str("Product(")?;
                tasks.push(DomainDisplayTask::Text(")"));
                for (index, child) in children.iter().enumerate().rev() {
                    tasks.push(DomainDisplayTask::Visit(child));
                    if index != 0 {
                        tasks.push(DomainDisplayTask::Text(", "));
                    }
                }
            },
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum TreeConstraintBinary {
    And,
    Or,
}

enum TreeConstraintCloneTask<'expr> {
    Visit(&'expr TreeConstraintExpr),
    ForallChildren(&'expr str, usize),
    Not(usize),
    Binary(TreeConstraintBinary, usize),
}

impl Clone for TreeConstraintExpr {
    fn clone(&self) -> Self {
        let mut tasks = vec![TreeConstraintCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::ForallChildren {
                    symbol,
                    body,
                }) => {
                    tasks.push(TreeConstraintCloneTask::ForallChildren(symbol, values.len()));
                    tasks.push(TreeConstraintCloneTask::Visit(body));
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::ExistsChild) => {
                    values.push(TreeConstraintExpr::ExistsChild);
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::Not(inner)) => {
                    tasks.push(TreeConstraintCloneTask::Not(values.len()));
                    tasks.push(TreeConstraintCloneTask::Visit(inner));
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::Match(symbols)) => {
                    values.push(TreeConstraintExpr::Match(symbols.clone()));
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::Atom(symbol)) => {
                    values.push(TreeConstraintExpr::Atom(symbol.clone()));
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::And(left, right)) => {
                    tasks.push(TreeConstraintCloneTask::Binary(
                        TreeConstraintBinary::And,
                        values.len(),
                    ));
                    tasks.push(TreeConstraintCloneTask::Visit(right));
                    tasks.push(TreeConstraintCloneTask::Visit(left));
                },
                TreeConstraintCloneTask::Visit(TreeConstraintExpr::Or(left, right)) => {
                    tasks.push(TreeConstraintCloneTask::Binary(
                        TreeConstraintBinary::Or,
                        values.len(),
                    ));
                    tasks.push(TreeConstraintCloneTask::Visit(right));
                    tasks.push(TreeConstraintCloneTask::Visit(left));
                },
                TreeConstraintCloneTask::ForallChildren(symbol, value_base) => {
                    let body = values
                        .pop()
                        .expect("tree-constraint clone PDA lost a forall body");
                    values.truncate(value_base);
                    values.push(TreeConstraintExpr::ForallChildren {
                        symbol: symbol.to_owned(),
                        body: Box::new(body),
                    });
                },
                TreeConstraintCloneTask::Not(value_base) => {
                    let inner = values
                        .pop()
                        .expect("tree-constraint clone PDA lost a negated operand");
                    values.truncate(value_base);
                    values.push(TreeConstraintExpr::Not(Box::new(inner)));
                },
                TreeConstraintCloneTask::Binary(kind, value_base) => {
                    let right = values
                        .pop()
                        .expect("tree-constraint clone PDA lost a binary right operand");
                    let left = values
                        .pop()
                        .expect("tree-constraint clone PDA lost a binary left operand");
                    values.truncate(value_base);
                    values.push(match kind {
                        TreeConstraintBinary::And => {
                            TreeConstraintExpr::And(Box::new(left), Box::new(right))
                        },
                        TreeConstraintBinary::Or => {
                            TreeConstraintExpr::Or(Box::new(left), Box::new(right))
                        },
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("tree-constraint clone PDA produced no result")
    }
}

fn take_tree_constraint_children(
    expression: &mut TreeConstraintExpr,
    work: &mut Vec<TreeConstraintExpr>,
) {
    let take = |child: &mut Box<TreeConstraintExpr>| {
        *std::mem::replace(child, Box::new(TreeConstraintExpr::ExistsChild))
    };
    match expression {
        TreeConstraintExpr::ForallChildren { body, .. } | TreeConstraintExpr::Not(body) => {
            work.push(take(body));
        },
        TreeConstraintExpr::And(left, right) | TreeConstraintExpr::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        TreeConstraintExpr::ExistsChild
        | TreeConstraintExpr::Match(_)
        | TreeConstraintExpr::Atom(_) => {},
    }
}

impl Drop for TreeConstraintExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_tree_constraint_children(self, &mut work);
        while let Some(mut expression) = work.pop() {
            take_tree_constraint_children(&mut expression, &mut work);
        }
    }
}

enum TreeConstraintDebugTask<'expr> {
    Visit(&'expr TreeConstraintExpr, usize),
    String(&'expr str),
    Strings(&'expr [String], usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
    CloseList(usize),
}

fn fmt_tree_constraint_debug(
    root: &TreeConstraintExpr,
    formatter: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let pretty = formatter.alternate();
    let mut tasks = vec![TreeConstraintDebugTask::Visit(root, 0)];
    while let Some(task) = tasks.pop() {
        match task {
            TreeConstraintDebugTask::Text(text) => formatter.write_str(text)?,
            TreeConstraintDebugTask::Indent(indent) => {
                write_model_debug_indent(formatter, indent)?;
            },
            TreeConstraintDebugTask::CloseTuple(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str(")")?;
            },
            TreeConstraintDebugTask::CloseStruct(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("}")?;
            },
            TreeConstraintDebugTask::CloseList(indent) => {
                write_model_debug_indent(formatter, indent)?;
                formatter.write_str("]")?;
            },
            TreeConstraintDebugTask::String(value) => write!(formatter, "{value:?}")?,
            TreeConstraintDebugTask::Strings([], _) => formatter.write_str("[]")?,
            TreeConstraintDebugTask::Strings(strings, _) if !pretty => {
                formatter.write_str("[")?;
                tasks.push(TreeConstraintDebugTask::Text("]"));
                for (index, value) in strings.iter().enumerate().rev() {
                    tasks.push(TreeConstraintDebugTask::String(value));
                    if index != 0 {
                        tasks.push(TreeConstraintDebugTask::Text(", "));
                    }
                }
            },
            TreeConstraintDebugTask::Strings(strings, indent) => {
                formatter.write_str("[\n")?;
                tasks.push(TreeConstraintDebugTask::CloseList(indent));
                for value in strings.iter().rev() {
                    tasks.push(TreeConstraintDebugTask::Text(",\n"));
                    tasks.push(TreeConstraintDebugTask::String(value));
                    tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
                }
            },
            TreeConstraintDebugTask::Visit(
                TreeConstraintExpr::ForallChildren { symbol, body },
                indent,
            ) if pretty => {
                formatter.write_str("ForallChildren {\n")?;
                tasks.push(TreeConstraintDebugTask::CloseStruct(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(body, indent + 1));
                tasks.push(TreeConstraintDebugTask::Text("body: "));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::String(symbol));
                tasks.push(TreeConstraintDebugTask::Text("symbol: "));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::ExistsChild, _) => {
                formatter.write_str("ExistsChild")?;
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Not(inner), indent) if pretty => {
                formatter.write_str("Not(\n")?;
                tasks.push(TreeConstraintDebugTask::CloseTuple(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(inner, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Match(symbols), indent)
                if pretty =>
            {
                formatter.write_str("Match(\n")?;
                tasks.push(TreeConstraintDebugTask::CloseTuple(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Strings(symbols, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Atom(symbol), indent) if pretty => {
                formatter.write_str("Atom(\n")?;
                tasks.push(TreeConstraintDebugTask::CloseTuple(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::String(symbol));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::And(left, right), indent)
                if pretty =>
            {
                formatter.write_str("And(\n")?;
                tasks.push(TreeConstraintDebugTask::CloseTuple(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(right, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(left, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Or(left, right), indent)
                if pretty =>
            {
                formatter.write_str("Or(\n")?;
                tasks.push(TreeConstraintDebugTask::CloseTuple(indent));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(right, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
                tasks.push(TreeConstraintDebugTask::Text(",\n"));
                tasks.push(TreeConstraintDebugTask::Visit(left, indent + 1));
                tasks.push(TreeConstraintDebugTask::Indent(indent + 1));
            },
            TreeConstraintDebugTask::Visit(
                TreeConstraintExpr::ForallChildren { symbol, body },
                _,
            ) => {
                formatter.write_str("ForallChildren { symbol: ")?;
                tasks.push(TreeConstraintDebugTask::Text(" }"));
                tasks.push(TreeConstraintDebugTask::Visit(body, 0));
                tasks.push(TreeConstraintDebugTask::Text(", body: "));
                tasks.push(TreeConstraintDebugTask::String(symbol));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Not(inner), _) => {
                formatter.write_str("Not(")?;
                tasks.push(TreeConstraintDebugTask::Text(")"));
                tasks.push(TreeConstraintDebugTask::Visit(inner, 0));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Match(symbols), _) => {
                formatter.write_str("Match(")?;
                tasks.push(TreeConstraintDebugTask::Text(")"));
                tasks.push(TreeConstraintDebugTask::Strings(symbols, 0));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Atom(symbol), _) => {
                formatter.write_str("Atom(")?;
                tasks.push(TreeConstraintDebugTask::Text(")"));
                tasks.push(TreeConstraintDebugTask::String(symbol));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::And(left, right), _) => {
                formatter.write_str("And(")?;
                tasks.push(TreeConstraintDebugTask::Text(")"));
                tasks.push(TreeConstraintDebugTask::Visit(right, 0));
                tasks.push(TreeConstraintDebugTask::Text(", "));
                tasks.push(TreeConstraintDebugTask::Visit(left, 0));
            },
            TreeConstraintDebugTask::Visit(TreeConstraintExpr::Or(left, right), _) => {
                formatter.write_str("Or(")?;
                tasks.push(TreeConstraintDebugTask::Text(")"));
                tasks.push(TreeConstraintDebugTask::Visit(right, 0));
                tasks.push(TreeConstraintDebugTask::Text(", "));
                tasks.push(TreeConstraintDebugTask::Visit(left, 0));
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for TreeConstraintExpr {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_tree_constraint_debug(self, formatter)
    }
}
