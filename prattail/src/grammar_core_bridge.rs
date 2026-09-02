//! Staged bridge from the proc-macro-era specification to `GrammarCore`.

use crate::binding_power::Associativity;
use crate::grammar::ir::CollectionKind;
use crate::{
    BeamWidthConfig, CustomTokenSpec, LanguageSpec, RefinementPredKind, ReservationMode,
    SyntaxItemSpec,
};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet};

impl LanguageSpec {
    /// Project this compile-time specification into the same semantic IR used
    /// by runtime-authored grammars. Rust action bodies are represented by
    /// named host capabilities and are never copied into the IR.
    pub fn to_grammar_core(&self) -> Result<core::GrammarCoreV1, String> {
        // This bridge also runs inside the proc-macro crate, whose feature set
        // is independent of the generated language crate's diagnostic feature.
        // The environment switch is therefore the authoritative gate here.
        let trace = std::env::var_os("PRATTAIL_MACRO_TRACE").is_some();
        macro_rules! stage {
            ($name:literal) => {
                if trace {
                    eprintln!("[macro-trace] {} grammar_core:{}", self.name, $name);
                }
            };
        }

        stage!("initialize.start");
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
                    .as_deref()
                    .map(lower_carrier)
                    .unwrap_or(core::Carrier::Dynamic),
                primary: category.is_primary,
                admits_variables: category.has_var,
            })
            .collect();
        let categories: BTreeMap<String, core::CategoryId> = output
            .categories
            .iter()
            .map(|category| (category.name.clone(), category.id))
            .collect();
        stage!("initialize.done");

        stage!("collect_terminals.start");
        let mut literal_terminals = BTreeSet::new();
        for rule in &self.rules {
            collect_terminals(&rule.syntax, &mut literal_terminals);
        }
        stage!("collect_terminals.done");
        output.parser_configuration = lower_parser_configuration(self)?;
        output.synchronization = lower_synchronization(self);
        output.tree_invariants = self
            .tree_invariants
            .iter()
            .map(|invariant| core::TreeInvariant {
                name: invariant.name.clone(),
                formula: core::CanonicalValue::String(invariant.formula.clone()),
            })
            .collect();
        output.refinement_types = self
            .refinement_types
            .iter()
            .map(|refinement| core::RefinementType {
                name: refinement.name.clone(),
                base_category: refinement.base_category.clone(),
                variable_name: refinement.variable_name.clone(),
                predicate_kind: match refinement.predicate_kind {
                    RefinementPredKind::Presburger => core::RefinementPredicateKind::Presburger,
                    RefinementPredKind::Behavioral => core::RefinementPredicateKind::Behavioral,
                    RefinementPredKind::Structural => core::RefinementPredicateKind::Structural,
                    RefinementPredKind::Mixed => core::RefinementPredicateKind::Mixed,
                },
                predicate: core::CanonicalValue::String(refinement.predicate_repr.clone()),
            })
            .collect();
        output.guard_configuration = lower_guard_configuration(self, &mut output.capabilities);

        stage!("tokens.start");
        let mode_names = lower_modes(self, &mut output)?;
        let mut token_ids = BTreeMap::new();
        add_builtin_tokens(self, &mut output, &mut token_ids);
        for token in &self.custom_tokens {
            if !token.is_builtin_override {
                add_custom_token(token, core::ModeId(0), &mode_names, &mut output, &mut token_ids)?;
            }
        }
        for (mode_index, mode) in self.modes.iter().enumerate() {
            let mode_id = core::ModeId(mode_index as u32 + 1);
            for token in &mode.token_specs {
                add_custom_token(token, mode_id, &mode_names, &mut output, &mut token_ids)?;
            }
        }
        let mut literal_ids = BTreeMap::new();
        for terminal in literal_terminals {
            let id = core::TokenId(output.tokens.len() as u32);
            literal_ids.insert(terminal.clone(), id);
            let reservation = lower_terminal_reservation(self, &terminal);
            output.tokens.push(core::TokenDefinition {
                id,
                name: format!("literal/{terminal}"),
                pattern: core::TokenPattern::Literal(terminal),
                category: None,
                evaluation: None,
                priority: 1,
                mode: core::ModeId(0),
                channel: "main".into(),
                transition: core::ModeTransition::default(),
                decoder: core::TokenDecoder::Unit,
                reservation,
            });
            output.modes[0].token_ids.push(id);
        }
        stage!("tokens.done");

        stage!("productions.start");
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
                evaluation: rule
                    .rust_code
                    .as_ref()
                    .map(|code| core::NativeEvaluation::Source {
                        semantics: vec!["Rust".into()],
                        text: code.to_string(),
                    }),
                evaluation_mode: match rule.eval_mode.as_deref() {
                    Some("fold") => Some(core::EvaluationMode::Fold),
                    Some("step") => Some(core::EvaluationMode::Step),
                    _ => None,
                },
                tier: None,
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
        stage!("productions.done");

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
        stage!("validate.start");
        output
            .validate()
            .map_err(|errors| format!("GrammarCore validation failed: {errors:?}"))?;
        stage!("validate.done");
        Ok(output)
    }
}

fn lower_carrier(name: &str) -> core::Carrier {
    let compact: String = name
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect();
    let open = compact.find('<');
    let head_end = open.unwrap_or(compact.len());
    let head = compact[..head_end]
        .rsplit("::")
        .next()
        .unwrap_or(&compact[..head_end]);
    let normalized = match open {
        Some(index) => format!("{head}{}", &compact[index..]),
        None => head.to_string(),
    };
    let last = normalized.as_str();
    let builtin = match last {
        "bool" => Some(core::BuiltinCarrier::Boolean),
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" | "BigInt" | "CanonicalBigInt" => Some(core::BuiltinCarrier::Integer),
        "BigRat" | "CanonicalBigRat" => Some(core::BuiltinCarrier::Rational),
        "Fixed" | "CanonicalFixedPoint" => Some(core::BuiltinCarrier::FixedPoint),
        "f32" | "f64" | "CanonicalFloat64" => Some(core::BuiltinCarrier::Float),
        "str" | "String" => Some(core::BuiltinCarrier::String),
        _ => None,
    };
    if let Some(builtin) = builtin {
        return core::Carrier::Builtin(builtin);
    }
    for (prefix, kind, arity) in [
        ("Vec<", core::CollectionKind::List, 1usize),
        ("HashBag<", core::CollectionKind::Bag, 1),
        ("HashSet<", core::CollectionKind::Set, 1),
        ("HashMap<", core::CollectionKind::Map, 2),
        ("PathMap<", core::CollectionKind::PathMap, 2),
    ] {
        if let Some(arguments) = normalized
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix('>'))
        {
            let parts = split_generic_arguments(arguments);
            if parts.len() == arity {
                return core::Carrier::Collection(core::CollectionCarrier {
                    kind,
                    key: parts[0].to_string(),
                    value: parts.get(1).map(|part| (*part).to_string()),
                });
            }
        }
    }
    core::Carrier::HostOpaque { stable_name: name.to_string() }
}

fn split_generic_arguments(arguments: &str) -> Vec<&str> {
    let mut depth = 0u32;
    let mut start = 0usize;
    let mut output = Vec::new();
    for (index, character) in arguments.char_indices() {
        match character {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                output.push(&arguments[start..index]);
                start = index + 1;
            },
            _ => {},
        }
    }
    output.push(&arguments[start..]);
    output
}

fn lower_modes(
    spec: &LanguageSpec,
    output: &mut core::GrammarCoreV1,
) -> Result<BTreeMap<String, core::ModeId>, String> {
    let mut names = BTreeMap::from([("default".to_string(), core::ModeId(0))]);
    for (index, mode) in spec.modes.iter().enumerate() {
        let id = core::ModeId(index as u32 + 1);
        if names.insert(mode.name.clone(), id).is_some() {
            return Err(format!("duplicate lexer mode `{}`", mode.name));
        }
        output.modes.push(core::LexerMode {
            id,
            name: mode.name.clone(),
            token_ids: Vec::new(),
            raw: mode.raw,
        });
    }
    Ok(names)
}

fn add_builtin_tokens(
    spec: &LanguageSpec,
    output: &mut core::GrammarCoreV1,
    token_ids: &mut BTreeMap<String, core::TokenId>,
) {
    let definitions = [
        ("Identifier", spec.literal_patterns.ident.clone(), core::TokenDecoder::Text),
        (
            "Integer",
            spec.literal_patterns.integer.clone(),
            core::TokenDecoder::Integer { radix: None },
        ),
        (
            "Float",
            spec.literal_patterns.float.clone(),
            core::TokenDecoder::Capability("builtin/float".into()),
        ),
        ("String", spec.literal_patterns.string.clone(), core::TokenDecoder::Text),
        (
            "Boolean",
            spec.literal_patterns
                .boolean
                .clone()
                .unwrap_or_else(|| "true|false".into()),
            core::TokenDecoder::Capability("builtin/boolean".into()),
        ),
    ];
    output
        .capabilities
        .insert(core::Capability::TokenDecoder("builtin/float".into()));
    output
        .capabilities
        .insert(core::Capability::TokenDecoder("builtin/boolean".into()));
    for (name, pattern, decoder) in definitions {
        let id = core::TokenId(output.tokens.len() as u32);
        output.tokens.push(core::TokenDefinition {
            id,
            name: name.into(),
            pattern: core::TokenPattern::Regex(pattern),
            category: None,
            evaluation: None,
            priority: 0,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder,
            reservation: core::Reservation::None,
        });
        output.modes[0].token_ids.push(id);
        token_ids.insert(name.into(), id);
    }
    // Frontend metasyntax and GrammarCore use a few different names for the
    // same built-in token families. Keep one token definition per family and
    // expose aliases only in this lookup map, so explicit captures never
    // require duplicate coextensive regexes (which would fork every matching
    // token in the language).
    if let Some(identifier) = token_ids.get("Identifier").copied() {
        token_ids.insert("Ident".into(), identifier);
    }
    if let Some(string) = token_ids.get("String").copied() {
        token_ids.insert("StringLit".into(), string);
        token_ids.insert("StringLiteral".into(), string);
    }
    if let Some(float) = token_ids.get("Float").copied() {
        token_ids.insert("FloatLiteral".into(), float);
    }
    for (family, patterns, decoder_prefix) in [
        ("Integer", &spec.literal_patterns.integer_by_category, "builtin/integer"),
        ("Rational", &spec.literal_patterns.rational_by_category, "builtin/rational"),
        ("FixedPoint", &spec.literal_patterns.fixed_by_category, "builtin/fixed"),
    ] {
        let mut patterns: Vec<_> = patterns.iter().collect();
        patterns.sort_by(|left, right| left.0.cmp(right.0));
        for (category, pattern) in patterns {
            let name = format!("{family}/{category}");
            let capability = format!("{decoder_prefix}/{category}");
            let id = core::TokenId(output.tokens.len() as u32);
            output
                .capabilities
                .insert(core::Capability::TokenDecoder(capability.clone()));
            output.tokens.push(core::TokenDefinition {
                id,
                name: name.clone(),
                pattern: core::TokenPattern::Regex(pattern.clone()),
                category: None,
                evaluation: None,
                priority: 0,
                mode: core::ModeId(0),
                channel: "main".into(),
                transition: core::ModeTransition::default(),
                decoder: core::TokenDecoder::Capability(capability),
                reservation: core::Reservation::None,
            });
            output.modes[0].token_ids.push(id);
            token_ids.insert(name, id);
        }
    }
}

fn add_custom_token(
    token: &CustomTokenSpec,
    mode: core::ModeId,
    mode_names: &BTreeMap<String, core::ModeId>,
    output: &mut core::GrammarCoreV1,
    token_ids: &mut BTreeMap<String, core::TokenId>,
) -> Result<(), String> {
    let id = core::TokenId(output.tokens.len() as u32);
    let qualified_name = if mode == core::ModeId(0) {
        token.name.clone()
    } else {
        format!("{}/{}", output.modes[mode.0 as usize].name, token.name)
    };
    if token_ids.contains_key(&qualified_name) {
        return Err(format!("duplicate token kind `{qualified_name}`"));
    }
    let decoder = if token.constructor_code.is_some() {
        let capability = format!("macro-token/{qualified_name}");
        output
            .capabilities
            .insert(core::Capability::TokenDecoder(capability.clone()));
        core::TokenDecoder::Capability(capability)
    } else if token.category.is_some() || token.payload_type.is_some() {
        core::TokenDecoder::Text
    } else {
        core::TokenDecoder::Unit
    };
    let push = token
        .push_mode
        .as_ref()
        .map(|name| {
            mode_names
                .get(name)
                .copied()
                .ok_or_else(|| format!("token `{qualified_name}` pushes unknown mode `{name}`"))
        })
        .transpose()?;
    output.tokens.push(core::TokenDefinition {
        id,
        name: qualified_name.clone(),
        pattern: core::TokenPattern::Regex(token.pattern.clone()),
        category: None,
        evaluation: None,
        priority: i16::from(token.priority),
        mode,
        channel: token.stream.clone().unwrap_or_else(|| "main".into()),
        transition: core::ModeTransition { push, pop: token.is_pop },
        decoder,
        reservation: core::Reservation::None,
    });
    output.modes[mode.0 as usize].token_ids.push(id);
    token_ids.insert(qualified_name, id);
    if mode == core::ModeId(0) {
        token_ids.insert(token.name.clone(), id);
    }
    Ok(())
}

fn lower_terminal_reservation(spec: &LanguageSpec, terminal: &str) -> core::Reservation {
    match spec.reservation_policy.mode {
        ReservationMode::None => core::Reservation::None,
        ReservationMode::Auto if spec.reservation_policy.contextual.contains(terminal) => {
            core::Reservation::Contextual
        },
        ReservationMode::Auto if is_identifier_terminal(terminal) => core::Reservation::Reserved,
        ReservationMode::Auto => core::Reservation::None,
    }
}

fn is_identifier_terminal(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_alphabetic())
        && characters.all(|character| character == '_' || character.is_alphanumeric())
}

fn lower_synchronization(spec: &LanguageSpec) -> Vec<core::SyncConstraint> {
    spec.sync
        .iter()
        .flat_map(|sync| sync.constraints.iter())
        .map(|constraint| match constraint {
            crate::SyncConstraintSpec::Align { stream_a, stream_b, boundary_pattern } => {
                core::SyncConstraint::Align {
                    stream_a: stream_a.clone(),
                    stream_b: stream_b.clone(),
                    boundary_pattern: boundary_pattern.clone(),
                }
            },
            crate::SyncConstraintSpec::Track { auxiliary, primary } => {
                core::SyncConstraint::Track {
                    auxiliary: auxiliary.clone(),
                    primary: primary.clone(),
                }
            },
        })
        .collect()
}

fn lower_guard_configuration(
    spec: &LanguageSpec,
    capabilities: &mut BTreeSet<core::Capability>,
) -> Option<core::GuardConfiguration> {
    spec.guard_config.as_ref().map(|guards| {
        let theories = guards
            .theories
            .iter()
            .map(|theory| {
                capabilities.insert(core::Capability::GuardTheory(theory.theory_type.clone()));
                core::GuardTheory {
                    name: theory.name.clone(),
                    implementation: theory.theory_type.clone(),
                    handled_categories: theory.handled_types.clone(),
                }
            })
            .collect();
        core::GuardConfiguration {
            theories,
            channel_categories: guards.channel_categories.clone(),
            join_patterns: guards
                .join_patterns
                .iter()
                .map(|join| core::JoinPattern {
                    label: join.label.clone(),
                    channel_categories: join.channel_categories.clone(),
                })
                .collect(),
            selectivity_overrides: guards
                .selectivity_overrides
                .iter()
                .map(|(name, value)| (name.clone(), *value))
                .collect(),
            cost_overrides: guards
                .cost_overrides
                .iter()
                .map(|(name, value)| (name.clone(), *value))
                .collect(),
            has_explicit_connectives: guards.has_explicit_connectives,
            has_explicit_predicates: guards.has_explicit_predicates,
        }
    })
}

fn lower_parser_configuration(spec: &LanguageSpec) -> Result<core::ParserConfiguration, String> {
    let recovery = &spec.recovery_config;
    let to_u32 = |name: &str, value: usize| {
        u32::try_from(value).map_err(|_| format!("{name} exceeds the GrammarCore u32 range"))
    };
    Ok(core::ParserConfiguration {
        beam_width: match spec.beam_width {
            BeamWidthConfig::Disabled => core::BeamWidth::Disabled,
            BeamWidthConfig::Explicit(value) => core::BeamWidth::Explicit(value),
            BeamWidthConfig::Auto => core::BeamWidth::Auto,
        },
        log_semiring_model_path: spec.log_semiring_model_path.clone(),
        recovery: core::RecoveryConfiguration {
            skip_per_token: recovery.skip_per_token,
            delete_cost: recovery.delete_cost,
            substitute_cost: recovery.substitute_cost,
            insert_cost: recovery.insert_cost,
            swap_cost: recovery.swap_cost,
            max_skip_lookahead: to_u32("max_skip_lookahead", recovery.max_skip_lookahead)?,
            deep_nesting_threshold: to_u32(
                "deep_nesting_threshold",
                recovery.deep_nesting_threshold,
            )?,
            deep_nesting_skip_mult: recovery.deep_nesting_skip_mult,
            shallow_depth_threshold: to_u32(
                "shallow_depth_threshold",
                recovery.shallow_depth_threshold,
            )?,
            shallow_depth_skip_mult: recovery.shallow_depth_skip_mult,
            low_bp_threshold: recovery.low_bp_threshold,
            low_bp_skip_mult: recovery.low_bp_skip_mult,
            collection_insert_mult: recovery.collection_insert_mult,
            group_insert_mult: recovery.group_insert_mult,
            bracket_insert_mult: recovery.bracket_insert_mult,
            mixfix_substitute_mult: recovery.mixfix_substitute_mult,
            simulation_valid_mult: recovery.simulation_valid_mult,
            simulation_fail_penalty: recovery.simulation_fail_penalty,
            beam_width: recovery.beam_width,
            cascade_window: to_u32("cascade_window", recovery.cascade_window)?,
            vpa_nesting_ceiling: recovery
                .vpa_nesting_ceiling
                .map(|value| to_u32("vpa_nesting_ceiling", value))
                .transpose()?,
            adaptive_weight_threshold: recovery.adaptive_weight_threshold,
            deterministic_skip_discount: recovery.deterministic_skip_discount,
            ambiguous_insert_discount: recovery.ambiguous_insert_discount,
            max_recovery_depth: recovery.max_recovery_depth,
        },
        reservation: match spec.reservation_policy.mode {
            ReservationMode::None => core::KeywordReservation::None,
            ReservationMode::Auto => core::KeywordReservation::Auto {
                contextual: spec.reservation_policy.contextual.iter().cloned().collect(),
            },
        },
    })
}

fn collect_terminals(items: &[SyntaxItemSpec], output: &mut BTreeSet<String>) {
    let mut work: Vec<_> = items.iter().rev().collect();
    while let Some(item) = work.pop() {
        match item {
            SyntaxItemSpec::Terminal(text) => {
                output.insert(text.clone());
            },
            SyntaxItemSpec::Sep { body, .. } | SyntaxItemSpec::Zip { body, .. } => {
                work.push(body);
            },
            SyntaxItemSpec::Map { body_items } | SyntaxItemSpec::Optional { inner: body_items } => {
                work.extend(body_items.iter().rev());
            },
            _ => {},
        }
    }
}

fn lower_items(
    items: &[SyntaxItemSpec],
    categories: &BTreeMap<String, core::CategoryId>,
    literals: &BTreeMap<String, core::TokenId>,
    tokens: &BTreeMap<String, core::TokenId>,
) -> Result<Vec<core::SyntaxItem>, String> {
    enum Job<'a> {
        Items(&'a [SyntaxItemSpec]),
        Item(&'a SyntaxItemSpec),
        FinishItems(usize),
        FinishRepeat { separator: &'a str, kind: CollectionKind },
        FinishSequence,
        FinishOptional,
    }

    let category = |name: &str| {
        categories
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown syntax category `{name}`"))
    };
    let mut jobs = vec![Job::Items(items)];
    let mut values: Vec<Vec<core::SyntaxItem>> = Vec::new();
    while let Some(job) = jobs.pop() {
        match job {
            Job::Items(items) => {
                jobs.push(Job::FinishItems(items.len()));
                for item in items.iter().rev() {
                    jobs.push(Job::Item(item));
                }
            },
            Job::FinishItems(count) => {
                let start = values
                    .len()
                    .checked_sub(count)
                    .expect("every syntax item result is scheduled");
                let chunks = values.split_off(start);
                let capacity = chunks.iter().map(Vec::len).sum();
                let mut output = Vec::with_capacity(capacity);
                for mut chunk in chunks {
                    output.append(&mut chunk);
                }
                values.push(output);
            },
            Job::Item(item) => {
                let lowered = match item {
                    SyntaxItemSpec::Terminal(text) => core::SyntaxItem::Token(literals[text]),
                    SyntaxItemSpec::NonTerminal { category: name, param_name } => {
                        core::SyntaxItem::Category {
                            category: category(name)?,
                            slot: param_name.clone(),
                        }
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
                    } => {
                        let kind = lower_collection(*kind);
                        let element = category(element_category)?;
                        core::SyntaxItem::Collection {
                            slot: param_name.clone(),
                            key: matches!(
                                kind,
                                core::CollectionKind::Map | core::CollectionKind::PathMap
                            )
                            .then_some(element),
                            element,
                            separator: separator.clone(),
                            kind,
                            key_value_separator: key_val_separator.clone(),
                        }
                    },
                    SyntaxItemSpec::Sep { body, separator, kind } => {
                        jobs.push(Job::FinishRepeat { separator, kind: *kind });
                        jobs.push(Job::Item(body));
                        continue;
                    },
                    SyntaxItemSpec::Map { body_items } => {
                        jobs.push(Job::FinishSequence);
                        jobs.push(Job::Items(body_items));
                        continue;
                    },
                    SyntaxItemSpec::Zip { body, .. } => {
                        jobs.push(Job::FinishSequence);
                        jobs.push(Job::Item(body));
                        continue;
                    },
                    SyntaxItemSpec::BinderCollection { param_name, separator } => {
                        core::SyntaxItem::Repeat {
                            body: vec![core::SyntaxItem::CaptureIdent { slot: param_name.clone() }],
                            separator: separator.clone(),
                            kind: core::CollectionKind::List,
                        }
                    },
                    SyntaxItemSpec::Optional { inner } => {
                        jobs.push(Job::FinishOptional);
                        jobs.push(Job::Items(inner));
                        continue;
                    },
                    SyntaxItemSpec::GuardExpression { param_name } => {
                        core::SyntaxItem::Guard { slot: param_name.clone() }
                    },
                };
                values.push(vec![lowered]);
            },
            Job::FinishRepeat { separator, kind } => {
                let body = values.pop().expect("a repeated syntax result is scheduled");
                if body.len() != 1 {
                    return Err("a separated syntax body must lower to exactly one item".into());
                }
                values.push(vec![core::SyntaxItem::Repeat {
                    body,
                    separator: separator.into(),
                    kind: lower_collection(kind),
                }]);
            },
            Job::FinishSequence => {
                let body = values.pop().expect("a sequence syntax result is scheduled");
                values.push(vec![core::SyntaxItem::Sequence(body)]);
            },
            Job::FinishOptional => {
                let body = values
                    .pop()
                    .expect("an optional syntax result is scheduled");
                values.push(vec![core::SyntaxItem::Optional(body)]);
            },
        }
    }
    if values.len() != 1 {
        return Err("syntax lowering produced an invalid value stack".into());
    }
    Ok(values.pop().expect("checked one syntax result"))
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
    let mut work: Vec<_> = items.iter().rev().collect();
    while let Some(item) = work.pop() {
        match item {
            core::SyntaxItem::Category { slot, .. }
            | core::SyntaxItem::CaptureIdent { slot }
            | core::SyntaxItem::CaptureToken { slot, .. }
            | core::SyntaxItem::Binder { slot, .. }
            | core::SyntaxItem::Collection { slot, .. }
            | core::SyntaxItem::ForeignLanguage { slot, .. }
            | core::SyntaxItem::Guard { slot } => output.push(slot.as_str()),
            core::SyntaxItem::Repeat { body, .. }
            | core::SyntaxItem::Sequence(body)
            | core::SyntaxItem::Optional(body) => work.extend(body.iter().rev()),
            core::SyntaxItem::Zip { left_slot, right_slot, .. } => {
                output.push(left_slot);
                output.push(right_slot);
            },
            core::SyntaxItem::Separated { source, .. } => {
                work.push(source);
            },
            core::SyntaxItem::Mapped { source, .. } => {
                work.push(source);
            },
            core::SyntaxItem::Token(_) => {},
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CategorySpec, GuardConfigSpec, JoinPatternSpec, LexerModeSpec, RefinementTypeSpec,
        RuleSpecInput, SyncConstraintSpec, SyncSpec, TheoryRegistrationSpec, TreeInvariantSpec,
    };

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

    #[test]
    fn explicit_builtin_ident_capture_reuses_the_identifier_token() {
        let spec = LanguageSpec::new(
            "CapturedIdent".into(),
            vec![CategorySpec {
                name: "Expr".into(),
                native_type: None,
                is_primary: true,
                has_var: false,
            }],
            vec![RuleSpecInput {
                label: "Name".into(),
                category: "Expr".into(),
                syntax: vec![SyntaxItemSpec::TokenKindCapture {
                    param_name: "name".into(),
                    kind_name: "Ident".into(),
                }],
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

        let core = spec
            .to_grammar_core()
            .expect("builtin Ident capture must lower");
        let identifier = core
            .tokens
            .iter()
            .find(|token| token.name == "Identifier")
            .expect("GrammarCore identifier token");
        assert_eq!(
            core.productions[0].syntax,
            vec![core::SyntaxItem::CaptureToken {
                token: identifier.id,
                slot: "name".into(),
            }]
        );
        assert!(core.validate().is_ok());
    }

    #[test]
    fn projection_preserves_every_language_spec_configuration_channel() {
        let mut spec = LanguageSpec::new(
            "Configured".into(),
            vec![CategorySpec {
                name: "Expr".into(),
                native_type: Some("mettail_runtime::HashBag<Expr>".into()),
                is_primary: true,
                has_var: true,
            }],
            vec![RuleSpecInput {
                label: "Join".into(),
                category: "Expr".into(),
                syntax: vec![SyntaxItemSpec::Terminal("join".into())],
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
        spec.beam_width = BeamWidthConfig::Explicit(7.5);
        spec.log_semiring_model_path = Some("registry:model/one".into());
        spec.recovery_config.skip_per_token = 0.75;
        spec.reservation_policy = crate::ReservationPolicy::auto();
        spec.custom_tokens.push(CustomTokenSpec {
            name: "Quote".into(),
            pattern: "\\\"".into(),
            category: None,
            payload_type: None,
            constructor_code: None,
            is_builtin_override: false,
            priority: 4,
            push_mode: Some("string".into()),
            is_pop: false,
            stream: None,
        });
        spec.modes.push(LexerModeSpec {
            name: "string".into(),
            token_specs: vec![CustomTokenSpec {
                name: "Chunk".into(),
                pattern: "[^\\\"]+".into(),
                category: Some("Expr".into()),
                payload_type: Some("str".into()),
                constructor_code: None,
                is_builtin_override: false,
                priority: 2,
                push_mode: None,
                is_pop: true,
                stream: Some("text".into()),
            }],
            raw: true,
        });
        spec.sync = Some(SyncSpec {
            constraints: vec![SyncConstraintSpec::Track {
                auxiliary: "text".into(),
                primary: "main".into(),
            }],
        });
        spec.tree_invariants.push(TreeInvariantSpec {
            name: "rooted".into(),
            formula: "forall n in subtree(root): holds(node, n)".into(),
        });
        spec.refinement_types.push(RefinementTypeSpec {
            name: "NonEmpty".into(),
            base_category: "Expr".into(),
            variable_name: "x".into(),
            predicate_kind: RefinementPredKind::Structural,
            predicate_repr: "non_empty(x)".into(),
        });
        spec.guard_config = Some(GuardConfigSpec {
            theories: vec![TheoryRegistrationSpec {
                name: "structural".into(),
                theory_type: "registry:theory/structural/v1".into(),
                handled_types: Some(vec!["Expr".into()]),
            }],
            channel_categories: Some(vec!["Expr".into()]),
            join_patterns: vec![JoinPatternSpec {
                label: "Join".into(),
                channel_categories: vec!["Expr".into(), "Expr".into()],
            }],
            selectivity_overrides: [("halts".into(), 0.25)].into(),
            cost_overrides: [("halts".into(), 3)].into(),
            has_explicit_connectives: true,
            has_explicit_predicates: true,
        });

        let core = spec.to_grammar_core().expect("fully configured core");
        assert!(matches!(
            core.categories[0].carrier,
            core::Carrier::Collection(core::CollectionCarrier {
                kind: core::CollectionKind::Bag,
                ..
            })
        ));
        assert_eq!(core.modes.len(), 2);
        assert!(core.modes[1].raw);
        assert_eq!(core.synchronization.len(), 1);
        assert_eq!(core.tree_invariants.len(), 1);
        assert_eq!(core.refinement_types.len(), 1);
        assert!(core.guard_configuration.is_some());
        assert!(matches!(core.parser_configuration.beam_width, core::BeamWidth::Explicit(7.5)));
        assert!(core.tokens.iter().any(|token| {
            token.name == "Quote"
                && token.transition.push == Some(core::ModeId(1))
                && token.mode == core::ModeId(0)
        }));
        assert!(core.tokens.iter().any(|token| {
            token.name == "string/Chunk"
                && token.transition.pop
                && token.mode == core::ModeId(1)
                && token.channel == "text"
        }));
        assert!(core.tokens.iter().any(|token| {
            token.name == "literal/join" && token.reservation == core::Reservation::Reserved
        }));
        assert!(core.validate().is_ok());

        let fingerprint = core.fingerprint().expect("fingerprint");
        spec.recovery_config.skip_per_token = 0.76;
        assert_ne!(
            fingerprint,
            spec.to_grammar_core()
                .expect("changed core")
                .fingerprint()
                .expect("changed fingerprint")
        );
    }
}
