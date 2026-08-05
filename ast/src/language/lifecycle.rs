//! Stack-safe lifecycle and lowering machines for recursive language-model trees.

use super::{
    BehavioralPred, Condition, FreshnessCondition, FreshnessTarget, PredArg, Premise, Quantifier,
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
