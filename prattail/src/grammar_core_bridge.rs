//! Staged bridge from the proc-macro-era specification to `GrammarCore`.

use crate::binding_power::Associativity;
use crate::grammar::ir::CollectionKind;
use crate::{LanguageSpec, SyntaxItemSpec};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet};

impl LanguageSpec {
    /// Project this compile-time specification into the same semantic IR used
    /// by runtime-authored grammars. Rust action bodies are represented by
    /// named host capabilities and are never copied into the IR.
    pub fn to_grammar_core(&self) -> Result<core::GrammarCoreV1, String> {
        let mut output = core::GrammarCoreV1::new(self.name.clone());
        output.provenance.frontend = "language!-compile-time".into();
        output.categories = self
            .types
            .iter()
            .enumerate()
            .map(|(index, category)| core::Category {
                id: core::CategoryId(index as u32),
                name: category.name.clone(),
                carrier: category
                    .native_type
                    .as_ref()
                    .map(|name| core::Carrier::HostOpaque { stable_name: name.clone() })
                    .unwrap_or(core::Carrier::Dynamic),
                primary: category.is_primary,
                admits_variables: category.has_var,
            })
            .collect();
        let categories: BTreeMap<&str, core::CategoryId> = output
            .categories
            .iter()
            .map(|category| (category.name.as_str(), category.id))
            .collect();

        let mut literal_terminals = BTreeSet::new();
        for rule in &self.rules {
            collect_terminals(&rule.syntax, &mut literal_terminals);
        }
        output
            .capabilities
            .insert(core::Capability::TokenDecoder("builtin/float".into()));
        output.tokens = builtin_tokens(self);
        let mut token_ids: BTreeMap<String, core::TokenId> = output
            .tokens
            .iter()
            .map(|token| (token.name.clone(), token.id))
            .collect();
        let mut literal_ids = BTreeMap::new();
        for terminal in literal_terminals {
            let id = core::TokenId(output.tokens.len() as u32);
            literal_ids.insert(terminal.clone(), id);
            output.tokens.push(core::TokenDefinition {
                id,
                name: format!("literal/{terminal}"),
                pattern: core::TokenPattern::Literal(terminal),
                priority: 1,
                mode: core::ModeId(0),
                channel: "main".into(),
                transition: core::ModeTransition::default(),
                decoder: core::TokenDecoder::Unit,
                reservation: core::Reservation::Contextual,
            });
        }
        for token in &self.custom_tokens {
            let id = core::TokenId(output.tokens.len() as u32);
            token_ids.insert(token.name.clone(), id);
            let decoder = if token.constructor_code.is_some() {
                let capability = format!("macro-token/{}", token.name);
                output
                    .capabilities
                    .insert(core::Capability::TokenDecoder(capability.clone()));
                core::TokenDecoder::Capability(capability)
            } else {
                core::TokenDecoder::Text
            };
            output.tokens.push(core::TokenDefinition {
                id,
                name: token.name.clone(),
                pattern: core::TokenPattern::Regex(token.pattern.clone()),
                priority: i16::from(token.priority),
                mode: core::ModeId(0),
                channel: token.stream.clone().unwrap_or_else(|| "main".into()),
                transition: core::ModeTransition { push: None, pop: token.is_pop },
                decoder,
                reservation: core::Reservation::None,
            });
        }
        output.modes[0].token_ids = output.tokens.iter().map(|token| token.id).collect();

        for (index, rule) in self.rules.iter().enumerate() {
            let result = categories
                .get(rule.category.as_str())
                .copied()
                .ok_or_else(|| {
                    format!("rule `{}` has unknown category `{}`", rule.label, rule.category)
                })?;
            let syntax = lower_items(&rule.syntax, &categories, &literal_ids, &token_ids)?;
            let constructor = core::ConstructorId(index as u32);
            let slots = collect_slots(&syntax);
            output.reductions.push(core::ReductionPlan {
                output_category: result,
                constructor,
                input_arity: slots.len() as u16,
                fields: (0..slots.len() as u16)
                    .map(core::FieldSource::Input)
                    .collect(),
            });
            if rule.rust_code.is_some() {
                output
                    .capabilities
                    .insert(core::Capability::SemanticPredicate(format!(
                        "macro-action/{}",
                        rule.label
                    )));
            }
            output.productions.push(core::Production {
                id: core::ProductionId(index as u32),
                constructor,
                label: rule.label.clone(),
                result,
                syntax,
                precedence: core::Precedence {
                    binding_power: rule.prefix_precedence.map(u16::from),
                    associativity: match rule.associativity {
                        Associativity::Left => core::Associativity::Left,
                        Associativity::Right => core::Associativity::Right,
                    },
                    shares_previous_level: rule.shares_level_with_previous,
                },
                classification: core::ProductionClass {
                    infix: rule.is_infix,
                    postfix: rule.is_postfix,
                    prefix: rule.is_unary_prefix,
                    variable: rule.is_var,
                    literal: rule.is_literal,
                    binder: rule.has_binder || rule.has_multi_binder,
                    collection: rule.is_collection,
                    cross_category: rule.is_cross_category,
                    cast: rule.is_cast,
                    generated: rule.is_auto_injected,
                },
                reduction: index as u32,
                provenance: rule.source_location.map(|location| core::SourceProvenance {
                    uri: None,
                    line: location.line,
                    column: location.column,
                }),
            });
        }

        let constructors: BTreeMap<&str, core::ConstructorId> = output
            .productions
            .iter()
            .map(|production| (production.label.as_str(), production.constructor))
            .collect();
        output.semantic_dependencies = self
            .semantic_dependency_groups
            .iter()
            .map(|group| {
                let mut dependencies: Vec<_> = group
                    .iter()
                    .filter_map(|label| constructors.get(label.as_str()).copied())
                    .collect();
                dependencies.sort_unstable();
                dependencies.dedup();
                dependencies
            })
            .collect();
        output
            .validate()
            .map_err(|errors| format!("GrammarCore validation failed: {errors:?}"))?;
        Ok(output)
    }
}

fn builtin_tokens(spec: &LanguageSpec) -> Vec<core::TokenDefinition> {
    let definitions = [
        (
            "Identifier",
            core::TokenPattern::Regex(spec.literal_patterns.ident.clone()),
            core::TokenDecoder::Text,
        ),
        (
            "Integer",
            core::TokenPattern::Regex(spec.literal_patterns.integer.clone()),
            core::TokenDecoder::Integer { radix: None },
        ),
        (
            "Float",
            core::TokenPattern::Regex(spec.literal_patterns.float.clone()),
            core::TokenDecoder::Capability("builtin/float".into()),
        ),
        (
            "String",
            core::TokenPattern::Regex(spec.literal_patterns.string.clone()),
            core::TokenDecoder::Text,
        ),
    ];
    definitions
        .into_iter()
        .enumerate()
        .map(|(index, (name, pattern, decoder))| core::TokenDefinition {
            id: core::TokenId(index as u32),
            name: name.into(),
            pattern,
            priority: 0,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder,
            reservation: core::Reservation::None,
        })
        .collect()
}

fn collect_terminals(items: &[SyntaxItemSpec], output: &mut BTreeSet<String>) {
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(text) => {
                output.insert(text.clone());
            },
            SyntaxItemSpec::Sep { body, .. } | SyntaxItemSpec::Zip { body, .. } => {
                collect_terminals(std::slice::from_ref(body), output);
            },
            SyntaxItemSpec::Map { body_items } | SyntaxItemSpec::Optional { inner: body_items } => {
                collect_terminals(body_items, output);
            },
            _ => {},
        }
    }
}

fn lower_items(
    items: &[SyntaxItemSpec],
    categories: &BTreeMap<&str, core::CategoryId>,
    literals: &BTreeMap<String, core::TokenId>,
    tokens: &BTreeMap<String, core::TokenId>,
) -> Result<Vec<core::SyntaxItem>, String> {
    items
        .iter()
        .map(|item| lower_item(item, categories, literals, tokens))
        .collect()
}

fn lower_item(
    item: &SyntaxItemSpec,
    categories: &BTreeMap<&str, core::CategoryId>,
    literals: &BTreeMap<String, core::TokenId>,
    tokens: &BTreeMap<String, core::TokenId>,
) -> Result<core::SyntaxItem, String> {
    let category = |name: &str| {
        categories
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown syntax category `{name}`"))
    };
    Ok(match item {
        SyntaxItemSpec::Terminal(text) => core::SyntaxItem::Token(literals[text]),
        SyntaxItemSpec::NonTerminal { category: name, param_name } => core::SyntaxItem::Category {
            category: category(name)?,
            slot: param_name.clone(),
        },
        SyntaxItemSpec::IdentCapture { param_name } => {
            core::SyntaxItem::CaptureIdent { slot: param_name.clone() }
        },
        SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
            core::SyntaxItem::CaptureToken {
                token: tokens
                    .get(kind_name)
                    .copied()
                    .ok_or_else(|| format!("unknown token kind `{kind_name}`"))?,
                slot: param_name.clone(),
            }
        },
        SyntaxItemSpec::Binder { param_name, category: name, is_multi } => {
            core::SyntaxItem::Binder {
                slot: param_name.clone(),
                category: category(name)?,
                multiple: *is_multi,
            }
        },
        SyntaxItemSpec::Collection {
            param_name,
            element_category,
            separator,
            kind,
            key_val_separator,
        } => core::SyntaxItem::Collection {
            slot: param_name.clone(),
            element: category(element_category)?,
            separator: separator.clone(),
            kind: lower_collection(*kind),
            key_value_separator: key_val_separator.clone(),
        },
        SyntaxItemSpec::Sep { body, separator, kind } => core::SyntaxItem::Repeat {
            body: vec![lower_item(body, categories, literals, tokens)?],
            separator: separator.clone(),
            kind: lower_collection(*kind),
        },
        SyntaxItemSpec::Map { body_items } => {
            core::SyntaxItem::Sequence(lower_items(body_items, categories, literals, tokens)?)
        },
        SyntaxItemSpec::Zip { left_name, right_name, body, .. } => core::SyntaxItem::Zip {
            left_slot: left_name.clone(),
            right_slot: right_name.clone(),
            body: vec![lower_item(body, categories, literals, tokens)?],
        },
        SyntaxItemSpec::BinderCollection { param_name, separator } => core::SyntaxItem::Repeat {
            body: vec![core::SyntaxItem::CaptureIdent { slot: param_name.clone() }],
            separator: separator.clone(),
            kind: core::CollectionKind::List,
        },
        SyntaxItemSpec::Optional { inner } => {
            core::SyntaxItem::Optional(lower_items(inner, categories, literals, tokens)?)
        },
        SyntaxItemSpec::GuardExpression { param_name } => {
            core::SyntaxItem::Guard { slot: param_name.clone() }
        },
    })
}

fn lower_collection(kind: CollectionKind) -> core::CollectionKind {
    match kind {
        CollectionKind::HashBag => core::CollectionKind::Bag,
        CollectionKind::HashSet => core::CollectionKind::Set,
        CollectionKind::Vec => core::CollectionKind::List,
        CollectionKind::HashMap => core::CollectionKind::Map,
        CollectionKind::PathMap => core::CollectionKind::PathMap,
    }
}

fn collect_slots(items: &[core::SyntaxItem]) -> Vec<&str> {
    let mut output = Vec::new();
    for item in items {
        match item {
            core::SyntaxItem::Category { slot, .. }
            | core::SyntaxItem::CaptureIdent { slot }
            | core::SyntaxItem::CaptureToken { slot, .. }
            | core::SyntaxItem::Binder { slot, .. }
            | core::SyntaxItem::Collection { slot, .. }
            | core::SyntaxItem::Guard { slot } => output.push(slot.as_str()),
            core::SyntaxItem::Repeat { body, .. }
            | core::SyntaxItem::Sequence(body)
            | core::SyntaxItem::Optional(body)
            | core::SyntaxItem::Zip { body, .. } => output.extend(collect_slots(body)),
            core::SyntaxItem::Token(_) => {},
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CategorySpec, RuleSpecInput};

    #[test]
    fn compile_time_frontend_reaches_grammar_core_without_source_actions() {
        let spec = LanguageSpec::new(
            "Tiny".into(),
            vec![CategorySpec {
                name: "Expr".into(),
                native_type: None,
                is_primary: true,
                has_var: true,
            }],
            vec![RuleSpecInput {
                label: "Zero".into(),
                category: "Expr".into(),
                syntax: vec![SyntaxItemSpec::Terminal("0".into())],
                associativity: Associativity::Left,
                shares_level_with_previous: false,
                prefix_precedence: None,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
                is_auto_injected: false,
            }],
        );
        let core = spec.to_grammar_core().expect("valid core");
        assert_eq!(core.productions[0].label, "Zero");
        assert!(core.validate().is_ok());
    }
}
