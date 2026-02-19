//! Full rule parse via ascent_syntax_export: type inference, program build, validate, then build Query from pre-parsed structure.

use crate::ast::{BodyAtom, Query, Term, Variable};
use crate::parse::pre_parse::{PreParseError, PreParsedBodyAtom, PreParsedRule, pre_parse_rule};
use crate::schema::QuerySchema;
use ascent_syntax_export::{parse_ascent_program_text, BodyItemNode};

#[derive(Debug)]
pub enum ParseError {
    PreParse(PreParseError),
    Ascent(syn::Error),
    SingleRule,
    IncludeSourceInBody,
    Unsafe(String),
    NonStratified(String),
    UnknownRelation { relation: String },
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::PreParse(e) => write!(f, "{}", e),
            ParseError::Ascent(e) => write!(f, "Parse error: {}", e),
            ParseError::SingleRule => write!(f, "Expected exactly one rule; got multiple or none"),
            ParseError::IncludeSourceInBody => write!(f, "include_source! is not allowed in query body"),
            ParseError::Unsafe(msg) => write!(f, "{}", msg),
            ParseError::NonStratified(msg) => write!(f, "{}", msg),
            ParseError::UnknownRelation { relation } => {
                write!(f, "Unknown relation '{}' (not in schema)", relation)
            }
        }
    }
}

impl std::error::Error for ParseError {}

/// Infer head parameter types from body and schema.
/// For each head variable, use the type from the first positive body atom where it appears.
fn infer_head_types(pre: &PreParsedRule, schema: &QuerySchema) -> Result<Vec<String>, ParseError> {
    let mut types = Vec::with_capacity(pre.head_args.len());
    for arg in &pre.head_args {
        if arg == "_" {
            return Err(ParseError::Unsafe(
                "Wildcard in head is not allowed (head variables must be bound)".into(),
            ));
        }
        let ty = type_of_variable_in_positive_body(arg, pre, schema)?;
        types.push(ty);
    }
    Ok(types)
}

fn type_of_variable_in_positive_body(
    var: &str,
    pre: &PreParsedRule,
    schema: &QuerySchema,
) -> Result<String, ParseError> {
    for atom in &pre.body_atoms {
        if atom.negated {
            continue;
        }
        let param_types = schema
            .get(&atom.relation)
            .ok_or_else(|| ParseError::UnknownRelation {
                relation: atom.relation.clone(),
            })?;
        for (j, arg) in atom.args.iter().enumerate() {
            if arg == var {
                let ty = param_types
                    .get(j)
                    .cloned()
                    .unwrap_or_else(|| "Proc".to_string());
                return Ok(ty);
            }
        }
    }
    Err(ParseError::Unsafe(format!(
        "Variable '{}' in head but not in any positive body atom",
        var
    )))
}

/// Build the full Ascent program string: relation declaration + rule.
fn build_program_string(pre: &PreParsedRule, head_types: &[String]) -> String {
    let decl = format!(
        "relation {}({});",
        pre.head_rel,
        head_types.join(", ")
    );
    format!("{}\n{}", decl, rule_only(pre))
}

/// Reconstruct just the rule part (head <-- body;) from pre-parsed. Ascent uses semicolon.
fn rule_only(pre: &PreParsedRule) -> String {
    let head_args = pre.head_args.join(", ");
    let head = format!("{}({})", pre.head_rel, head_args);
    let body: Vec<String> = pre
        .body_atoms
        .iter()
        .map(|a| {
            let prefix = if a.negated { "!" } else { "" };
            let args = a.args.join(", ");
            format!("{}{}({})", prefix, a.relation, args)
        })
        .collect();
    format!("{} <-- {} ;", head, body.join(", "))
}

/// Validate that every body relation is in the schema.
fn validate_body_relations(pre: &PreParsedRule, schema: &QuerySchema) -> Result<(), ParseError> {
    for atom in &pre.body_atoms {
        if !schema.contains_relation(&atom.relation) {
            return Err(ParseError::UnknownRelation {
                relation: atom.relation.clone(),
            });
        }
    }
    Ok(())
}

/// Convert a pre-parsed arg string to our Term.
fn arg_to_term(s: &str) -> Term {
    if s == "_" {
        Term::Wildcard
    } else if Variable::is_valid_name(s) {
        Term::Variable(Variable::new(s))
    } else {
        Term::Constant(s.to_string())
    }
}

/// Build our Query AST from the pre-parsed rule (after ascent validation).
fn query_from_pre_parsed(pre: PreParsedRule) -> Query {
    let head_terms: Vec<Term> = pre
        .head_args
        .into_iter()
        .map(|a| arg_to_term(&a))
        .collect();
    let head = crate::ast::Atom {
        relation: pre.head_rel,
        terms: head_terms,
    };
    let body: Vec<BodyAtom> = pre
        .body_atoms
        .into_iter()
        .map(|a| body_atom_from_pre(a))
        .collect();
    Query { head, body }
}

fn body_atom_from_pre(a: PreParsedBodyAtom) -> BodyAtom {
    let terms: Vec<Term> = a.args.iter().map(|s| arg_to_term(s)).collect();
    let inner = BodyAtom::Relation {
        name: a.relation,
        terms,
    };
    if a.negated {
        BodyAtom::Negation(Box::new(inner))
    } else {
        inner
    }
}

/// Parse a single rule string into a Query using the given schema.
/// Validates with ascent_syntax_export and enforces safety/stratification.
pub fn parse_query(rule_str: &str, schema: &QuerySchema) -> Result<Query, ParseError> {
    let pre = pre_parse_rule(rule_str).map_err(ParseError::PreParse)?;
    validate_body_relations(&pre, schema)?;
    let head_types = infer_head_types(&pre, schema)?;
    let program_str = build_program_string(&pre, &head_types);
    let program = parse_ascent_program_text(&program_str).map_err(ParseError::Ascent)?;
    if program.rules.len() != 1 {
        return Err(ParseError::SingleRule);
    }
    // Reject any macro invocation in body (e.g. include_source!)
    if program.rules[0]
        .body_items
        .iter()
        .any(|bi| matches!(bi, BodyItemNode::MacroInvocation(_)))
    {
        return Err(ParseError::IncludeSourceInBody);
    }
    let query = query_from_pre_parsed(pre);
    query.is_safe().map_err(ParseError::Unsafe)?;
    query.check_stratification().map_err(ParseError::NonStratified)?;
    Ok(query)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schema::QuerySchema;
    use std::collections::HashMap;

    fn rhocalc_like_schema() -> QuerySchema {
        let mut relations = HashMap::new();
        relations.insert("path".into(), vec!["Proc".into(), "Proc".into()]);
        relations.insert("rw_proc".into(), vec!["Proc".into(), "Proc".into()]);
        relations.insert("proc".into(), vec!["Proc".into()]);
        relations.insert("step_term".into(), vec!["Proc".into()]);
        QuerySchema { relations }
    }

    #[test]
    fn test_parse_query_simple() {
        let schema = rhocalc_like_schema();
        let q = parse_query(
            "query(result) <-- path(term, result), !rw_proc(result, _).",
            &schema,
        )
        .unwrap();
        assert_eq!(q.head.relation, "query");
        assert_eq!(q.head.terms.len(), 1);
        assert!(matches!(&q.head.terms[0], Term::Variable(v) if v.name == "result"));
        assert_eq!(q.body.len(), 2);
        assert!(matches!(&q.body[0], BodyAtom::Relation { name, .. } if name == "path"));
        assert!(matches!(&q.body[1], BodyAtom::Negation(..)));
    }

    #[test]
    fn test_parse_unknown_relation() {
        let schema = rhocalc_like_schema();
        let err = parse_query("q(x) <-- path(x, y), bad_rel(y).", &schema).unwrap_err();
        assert!(matches!(err, ParseError::UnknownRelation { relation } if relation == "bad_rel"));
    }
}
