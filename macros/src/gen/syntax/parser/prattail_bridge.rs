//! Bridge between MeTTaIL's `LanguageDef` AST and PraTTaIL's `LanguageSpec`.
//!
//! Converts the rich `LanguageDef` type (with both old BNFC-style and new
//! judgement-style syntax) into the simplified `LanguageSpec` that PraTTaIL
//! uses for parser generation.
//!
//! This bridge performs **structural mapping only** — converting `GrammarRule`
//! syntax items to `SyntaxItemSpec`. All semantic classification (is_infix,
//! is_postfix, is_cast, etc.) is performed by PraTTaIL's `classify` module
//! via `LanguageSpec::new()`.

use std::collections::HashSet;

use crate::gen::native::native_type_to_full_string;
use crate::gen::runtime::wpda_codegen::collection::kv_sep_for;
use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, NonTerminalKind, PatternOp, SyntaxExpr, TermParam},
    language::{AttributeValue, LanguageDef},
    types::{CollectionType, TypeExpr},
};
use mettail_prattail::{
    binding_power::Associativity, grammar::ir::CollectionKind, BeamWidthConfig, CategorySpec,
    CustomTokenSpec, LanguageSpec, LexerModeSpec, LiteralPatterns, RefinementPredKind,
    RefinementTypeSpec, ReservationPolicy, RuleSpecInput, SyncConstraintSpec, SyncSpec,
    SyntaxItemSpec, TreeInvariantSpec,
};

/// Convert a `LanguageDef` to a PraTTaIL `LanguageSpec`.
///
/// Performs structural mapping of syntax items, then delegates all
/// flag classification to `LanguageSpec::new()`.
///
/// # Errors
///
/// `Err(diagnostic)` iff an `options { }` value has a shape this bridge cannot
/// decode — see [`unexpected_option_shape`], which is where the reason for
/// refusing rather than asserting is written down. Every such value is supposed
/// to have been rejected at parse time, so an `Err` here is a MACRO BUG and its
/// message says so.
pub fn language_def_to_spec(language: &LanguageDef) -> Result<LanguageSpec, String> {
    let categories: Vec<CategorySpec> = language
        .types
        .iter()
        .enumerate()
        .map(|(idx, t)| CategorySpec {
            name: t.name.to_string(),
            // Use full path so downstream codegen can emit unambiguously qualified
            // type references (e.g. `mettail_runtime::CanonicalBigRat`), not just
            // the last segment. `native_type_to_string` gave just the last segment,
            // which broke `literals {}` Token-variant payloads referencing types
            // outside the caller's `use` scope.
            native_type: t.native_type.as_ref().map(native_type_to_full_string),
            is_primary: idx == 0,
            has_var: true, // For now, all categories are assumed to have a Var variant.
                           // Future: derive from grammar analysis (categories with no Var rule
                           // should get `has_var: false`, e.g. List/Bag synthetic collection types).
        })
        .collect();

    let cat_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

    let mut inputs: Vec<RuleSpecInput> = language
        .terms
        .iter()
        .map(|rule| convert_rule(rule, &cat_names))
        .collect();

    // PIECE 3 (keyword reservation): collect the *ident-shaped* collection-open
    // delimiters (e.g. `Set` from a `Set( … )` literal, as opposed to bracket
    // openers like `[`, `{`, `#{`). Such an opener is a grammar keyword AND the
    // constructor token of a collection literal; the collection-literal parser
    // needs it to remain lexable as an identifier, so reserving it would break
    // `Set( … )`. These are escalated to the reservation policy's `contextual`
    // opt-out set — grammar-derived, general, no per-language hardcode.
    let mut contextual_collection_openers: HashSet<String> = HashSet::new();

    // Synthesize collection-literal rules (`ListLit`, `BagLit`, `MapLit`)
    // for every `![Vec<T>] as Cat` / `![HashBag<T>] as Cat` /
    // `![HashMap<K,V>] as Cat` declaration. The merge plan B.1 specifies
    // that `collection_kind` carries the defaults (`list(`, `)`, `,`;
    // `bag(…)`, `map(k:v, …)`) — without these synthetic rules there is
    // no surface syntax for constructing collection literals, and any
    // Display → parse roundtrip of `ListLit(v)` / `BagLit(v)` / `MapLit(v)`
    // fails. Each synthesized rule parses `open ... close` using PraTTaIL's
    // existing `Collection` SyntaxItemSpec (same machinery as user-written
    // `xs.*sep(",")` rules).
    for lt in &language.types {
        let Some(ref ck) = lt.collection_kind else {
            continue;
        };
        // Stage 2 (2026-06-27): read the delimiters through the single
        // delimiters() accessor; only the irreducible variant → (kind, label)
        // mapping stays a per-variant match.
        let d = ck.delimiters();
        let (kind, label) = match ck {
            mettail_ast::language::CollectionCategory::List(_) => (CollectionKind::Vec, "ListLit"),
            mettail_ast::language::CollectionCategory::Bag(_) => {
                (CollectionKind::HashBag, "BagLit")
            },
            mettail_ast::language::CollectionCategory::Map(_) => {
                (CollectionKind::HashMap, "MapLit")
            },
            mettail_ast::language::CollectionCategory::Set(_) => {
                (CollectionKind::HashSet, "SetLit")
            },
            mettail_ast::language::CollectionCategory::Pathmap(_) => {
                (CollectionKind::PathMap, "PathmapLit")
            },
        };
        let (open, close, sep, kv) =
            (d.open.clone(), d.close.clone(), d.sep.clone(), d.key_val_sep.clone());
        // Resolve element category from the collection's payload type.
        // For Vec<Proc>/HashBag<Proc>, that's Proc; for HashMap<K, V>
        // the element is the key category — the map's `key_val_separator`
        // expresses the `:` between key and value in `SyntaxItemSpec::Collection`.
        let elem_cat = language
            .collection_element_type_for_category(&lt.name)
            .map(|i| i.to_string())
            .unwrap_or_else(|| lt.name.to_string());
        // Split `open` into its prefix and its terminal paren (if any):
        //   - Default form `list(` → prefix `list`, synthesized paren `(`.
        //   - User delimiter `[` → prefix `[`, no synthesized paren.
        // Without this split, user-declared delimiters (e.g. `List ["[", "]", ","]`)
        // produced parser rules like `[ ( elems )` instead of `[ elems ]`,
        // making empty `[]` and non-default delimiters unparseable.
        let trimmed_open = open.trim_end_matches('(').to_string();
        let needs_synth_paren = open != trimmed_open;
        // If the opener is lexically an identifier (e.g. `Set`), it collides
        // with the identifier pattern and would be reserved under `auto`;
        // record it as a contextual opt-out so the collection literal keeps
        // parsing (grammar-derived; bracket openers like `[`/`{` are skipped).
        if !trimmed_open.is_empty()
            && trimmed_open
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_')
        {
            contextual_collection_openers.insert(trimmed_open.clone());
        }
        let mut syntax = Vec::with_capacity(4);
        syntax.push(SyntaxItemSpec::Terminal(trimmed_open));
        if needs_synth_paren {
            syntax.push(SyntaxItemSpec::Terminal("(".to_string()));
        }
        syntax.push(SyntaxItemSpec::Collection {
            param_name: "elems".to_string(),
            element_category: elem_cat,
            separator: sep,
            kind,
            key_val_separator: kv,
        });
        syntax.push(SyntaxItemSpec::Terminal(close));
        inputs.push(RuleSpecInput {
            label: label.to_string(),
            category: lt.name.to_string(),
            syntax,
            associativity: Associativity::Left,
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            is_auto_injected: false,
        });
    }

    // Extract beam_width from options (defaults to Disabled if not specified)
    let beam_width = match language.options.get("beam_width") {
        Some(AttributeValue::Float(f)) => BeamWidthConfig::Explicit(*f),
        Some(AttributeValue::Keyword(kw)) => match kw.as_str() {
            "none" | "disabled" => BeamWidthConfig::Disabled,
            "auto" => BeamWidthConfig::Auto,
            other => {
                return Err(unexpected_option_shape(
                    "beam_width",
                    &format!("the keyword `{other}`"),
                    "a float, or one of the keywords `none`, `disabled`, `auto`",
                ))
            },
        },
        None => BeamWidthConfig::Disabled,
        Some(other) => {
            return Err(unexpected_option_shape(
                "beam_width",
                &describe_option_value(other),
                "a float, or one of the keywords `none`, `disabled`, `auto`",
            ))
        },
    };

    let log_semiring_model_path = match language.options.get("log_semiring_model_path") {
        Some(AttributeValue::Str(s)) => Some(s.clone()),
        None => None,
        Some(other) => {
            return Err(unexpected_option_shape(
                "log_semiring_model_path",
                &describe_option_value(other),
                "a string path",
            ))
        },
    };

    // PIECE 3: keyword-reservation policy. `auto` reserves identifier-shaped
    // keyword terminals (default-reserve modeling); `none` (the default when
    // the option is absent) retains full ambiguity for Fortran-style
    // languages. Validated at parse time (ast/language/parse.rs).
    //
    // Under `auto`, ident-shaped collection-open delimiters (e.g. `Set`) are
    // escalated to the `contextual` opt-out so `Set( … )` literals keep
    // parsing — the grammar-derived global-vs-contextual decision (see the
    // S0-kw-no-break measurement: reserving `Set` broke `Set(1,2,3).size()`
    // et al. while every bracket-delimited collection was unaffected).
    let reservation_policy = match language.options.get("reserved_keywords") {
        Some(AttributeValue::Keyword(kw)) => match kw.as_str() {
            "auto" => ReservationPolicy {
                mode: mettail_prattail::ReservationMode::Auto,
                contextual: contextual_collection_openers,
            },
            "none" => ReservationPolicy::none(),
            other => {
                return Err(unexpected_option_shape(
                    "reserved_keywords",
                    &format!("the keyword `{other}`"),
                    "the keyword `auto` or `none`",
                ))
            },
        },
        None => ReservationPolicy::none(),
        Some(other) => {
            return Err(unexpected_option_shape(
                "reserved_keywords",
                &describe_option_value(other),
                "the keyword `auto` or `none`",
            ))
        },
    };

    let semantic_dependency_groups = collect_semantic_dependency_groups(language);

    // Convert token definitions to CustomTokenSpec
    let mut literal_patterns = LiteralPatterns::default();
    let mut integer_alternatives: Vec<String> = Vec::new();
    let custom_tokens: Vec<CustomTokenSpec> = language
        .token_defs
        .iter()
        .map(|td| {
            let name = td.name.to_string();

            // Resolve the NativeKind for this token's category so all
            // dispatch below is typed — no string comparisons on variant
            // family names.
            let native_kind = td.category.as_ref().and_then(|cat| {
                language
                    .types
                    .iter()
                    .find(|t| t.name == *cat)
                    .and_then(|t| t.native_type.as_ref())
                    .map(mettail_ast::language::NativeKind::from_syn_type)
            });

            // A "builtin" token is one whose NativeKind maps to a
            // standard Token variant family (Integer, Float, Boolean,
            // StringLit). Every non-None return from standard_token_variant()
            // IS a builtin family — no string comparison needed.
            let is_builtin = native_kind
                .and_then(|k| k.standard_token_variant())
                .is_some();

            // Update LiteralPatterns from the resolved NativeKind.
            // Multiple literals can share a built-in token family (e.g.
            // Int/UInt32/BigInt all map to Integer). We build a UNION
            // regex so the single `Token::Integer(i64)` matches any.
            if let Some(kind) = native_kind {
                if is_builtin {
                    if kind.is_integer() {
                        integer_alternatives.push(td.pattern.clone());
                    } else {
                        match kind {
                            mettail_ast::language::NativeKind::Float32
                            | mettail_ast::language::NativeKind::Float64 => {
                                literal_patterns.float = td.pattern.clone();
                            },
                            mettail_ast::language::NativeKind::Bool => {
                                literal_patterns.boolean = Some(td.pattern.clone());
                            },
                            mettail_ast::language::NativeKind::Str => {
                                literal_patterns.string = td.pattern.clone();
                            },
                            _ => {},
                        }
                    }
                } else if td.from_literals {
                    // Non-builtin literal families: Rational, FixedPoint.
                    // Populate the by_category maps for the NFA builder.
                    // Key = mapped variant name (not original category).
                    match kind {
                        mettail_ast::language::NativeKind::CanonicalBigRat => {
                            literal_patterns
                                .rational_by_category
                                .insert(name.clone(), td.pattern.clone());
                        },
                        mettail_ast::language::NativeKind::CanonicalFixedPoint => {
                            literal_patterns
                                .fixed_by_category
                                .insert(name.clone(), td.pattern.clone());
                        },
                        _ => {},
                    }
                }
            }

            // For built-in overrides, also update LiteralPatterns for
            // the Ident pattern (no NativeKind — Ident is structural).
            if !is_builtin && td.from_literals && name == "Ident" {
                literal_patterns.ident = td.pattern.clone();
            }

            // Payload type: built-in literals keep the built-in payload
            // (i64, bool, f64, …); non-builtin literal-block tokens carry
            // raw `&'a str`; tokens{} entries inherit their category's
            // native type.
            let payload_type = if td.from_literals {
                if is_builtin {
                    td.category.as_ref().and_then(|cat| {
                        categories
                            .iter()
                            .find(|c| c.name == cat.to_string())
                            .and_then(|c| c.native_type.clone())
                    })
                } else {
                    Some("str".to_string())
                }
            } else {
                td.category.as_ref().and_then(|cat| {
                    categories
                        .iter()
                        .find(|c| c.name == cat.to_string())
                        .and_then(|c| c.native_type.clone())
                })
            };

            CustomTokenSpec {
                name,
                pattern: td.pattern.clone(),
                category: td.category.as_ref().map(|c| c.to_string()),
                payload_type,
                constructor_code: td.rust_code.as_ref().map(|code| code.to_string()),
                is_builtin_override: is_builtin,
                priority: td.priority.unwrap_or(2),
                push_mode: td.push_mode.as_ref().map(|m| m.to_string()),
                is_pop: td.is_pop,
                stream: td.stream.as_ref().map(|s| s.to_string()),
            }
        })
        .collect();

    // Build the union integer pattern from all Integer-mapped literals.
    // Multiple categories (Int/UInt32/BigInt) each contribute a regex
    // alternative; the DFA matches the union as a single `Token::Integer`.
    if !integer_alternatives.is_empty() {
        let union = integer_alternatives
            .iter()
            .map(|p| format!("({})", p))
            .collect::<Vec<_>>()
            .join("|");
        literal_patterns.integer = union;
    }

    // Convert mode definitions
    let modes: Vec<LexerModeSpec> = language
        .mode_defs
        .iter()
        .map(|md| LexerModeSpec {
            name: md.name.to_string(),
            token_specs: md
                .token_defs
                .iter()
                .map(|td| {
                    let payload_type = if td.from_literals {
                        Some("str".to_string())
                    } else {
                        td.category.as_ref().and_then(|cat| {
                            categories
                                .iter()
                                .find(|c| c.name == cat.to_string())
                                .and_then(|c| c.native_type.clone())
                        })
                    };
                    CustomTokenSpec {
                        name: td.name.to_string(),
                        pattern: td.pattern.clone(),
                        category: td.category.as_ref().map(|c| c.to_string()),
                        payload_type,
                        constructor_code: td.rust_code.as_ref().map(|code| code.to_string()),
                        is_builtin_override: false, // modes can't override built-ins
                        priority: td.priority.unwrap_or(2),
                        push_mode: td.push_mode.as_ref().map(|m| m.to_string()),
                        is_pop: td.is_pop,
                        stream: td.stream.as_ref().map(|s| s.to_string()),
                    }
                })
                .collect(),
            raw: md.raw,
        })
        .collect();

    // Convert sync constraints
    let sync = if language.sync_constraints.is_empty() {
        None
    } else {
        Some(SyncSpec {
            constraints: language
                .sync_constraints
                .iter()
                .map(|sc| match sc {
                    mettail_ast::language::SyncConstraint::Align {
                        stream_a,
                        stream_b,
                        boundary_pattern,
                    } => SyncConstraintSpec::Align {
                        stream_a: stream_a.to_string(),
                        stream_b: stream_b.to_string(),
                        boundary_pattern: boundary_pattern.clone(),
                    },
                    mettail_ast::language::SyncConstraint::Track { auxiliary, primary } => {
                        SyncConstraintSpec::Track {
                            auxiliary: auxiliary.to_string(),
                            primary: primary.to_string(),
                        }
                    },
                })
                .collect(),
        })
    };

    // Convert tree invariants to spec (formula as string for now)
    let tree_invariants: Vec<TreeInvariantSpec> = language
        .tree_invariants
        .iter()
        .map(|ti| TreeInvariantSpec {
            name: ti.name.to_string(),
            formula: format!("{:?}", ti.constraint),
        })
        .collect();

    let mut spec = LanguageSpec::with_options(
        language.name.to_string(),
        categories,
        inputs,
        beam_width,
        log_semiring_model_path,
        literal_patterns,
    );
    spec.semantic_dependency_groups = semantic_dependency_groups;
    spec.custom_tokens = custom_tokens;
    spec.modes = modes;
    spec.sync = sync;
    spec.tree_invariants = tree_invariants;
    spec.reservation_policy = reservation_policy;

    // Convert refinement type definitions from the macros AST to the pipeline spec.
    spec.refinement_types = language
        .refinement_types
        .iter()
        .map(|rt| {
            let kind = match rt.predicate.to_pred_kind_str() {
                "Presburger" => RefinementPredKind::Presburger,
                "Behavioral" => RefinementPredKind::Behavioral,
                "Structural" => RefinementPredKind::Structural,
                "Mixed" => RefinementPredKind::Mixed,
                _ => RefinementPredKind::Mixed,
            };
            RefinementTypeSpec {
                name: rt.name.to_string(),
                base_category: rt.base_type.to_string(),
                variable_name: rt.var.to_string(),
                predicate_kind: kind,
                predicate_repr: format!("{}", rt.predicate),
            }
        })
        .collect();

    // Lower the guard configuration (design doc §2A) from the macro AST
    // to the pipeline-side `GuardConfigSpec`. `None` is preserved as `None`.
    spec.guard_config = language.guard_config.as_ref().map(lower_guard_config);

    Ok(spec)
}

/// ★ #141 group G7 — the message that replaced five `unreachable!("… validated at
/// parse time")`.
///
/// # Why these were converted even though the claim is TRUE
///
/// The claim really does hold: `ast/src/language/parse.rs` rejects every
/// out-of-domain `beam_width`, `log_semiring_model_path` and `reserved_keywords`
/// value while parsing the `options { }` block, with a `syn::Error` carrying the
/// same domain this bridge expects. Classified `PreValidated` in the repair
/// design, and that classification is retained here rather than in a table
/// somewhere else.
///
/// What `unreachable!` bought was a *comment* asserting the two domains agree.
/// What it cost, in this workspace specifically, is that if they ever DISAGREED
/// the reader would be told nothing whatsoever: `[profile.dev]` compiles this
/// proc macro under cranelift, where a panic does not unwind across the
/// `proc_macro` bridge — `rustc` aborts with `fatal runtime error: Rust cannot
/// catch foreign exceptions` and no message at all. The five sites were therefore
/// "a comment, plus a silent build kill if the comment is wrong".
///
/// The conversion costs one `Err` per site and buys an assertable claim: the
/// bridge's accepted domain is now testable from a unit test that hands it an
/// out-of-domain value directly (see
/// `an_out_of_domain_option_value_refuses_instead_of_asserting`), which is
/// exactly the agreement `unreachable!` could only assume.
fn unexpected_option_shape(option: &str, found: &str, expected: &str) -> String {
    format!(
        "mettail internal error: the `options {{ }}` value for `{option}` reached the \
         PraTTaIL bridge as {found}, but this bridge accepts only {expected}. \
         `ast/src/language/parse.rs` is supposed to have rejected it while parsing the \
         `options` block, so the parser's accepted domain and the bridge's have drifted \
         apart. This is a macro bug, not a grammar bug — please report it."
    )
}

/// Name an option value's SHAPE for [`unexpected_option_shape`].
///
/// The value itself is not interpolated for the non-keyword arms: what went wrong
/// is the variant, and printing e.g. a float where a keyword was required reads
/// as though the number were at fault.
fn describe_option_value(value: &AttributeValue) -> String {
    match value {
        AttributeValue::Float(_) => "a float".to_string(),
        AttributeValue::Int(_) => "an integer".to_string(),
        AttributeValue::Bool(_) => "a boolean".to_string(),
        AttributeValue::Str(_) => "a string".to_string(),
        AttributeValue::Keyword(kw) => format!("the keyword `{kw}`"),
    }
}

/// Lower a `GuardConfig` (macros-side, syn-based) to a `GuardConfigSpec`
/// (prattail-side, syn-free). All identifiers are converted to strings;
/// `syn::Type` becomes its quoted token-stream representation.
///
/// This is the central data flow point that detaches the pipeline from
/// the `syn` crate while preserving the user's guard configuration.
fn lower_guard_config(
    gc: &mettail_ast::language::GuardConfig,
) -> mettail_prattail::GuardConfigSpec {
    use mettail_prattail::{GuardConfigSpec, JoinPatternSpec, TheoryRegistrationSpec};
    use std::collections::HashMap;

    // Theories: identifier → string, syn::Type → quoted string
    let theories: Vec<TheoryRegistrationSpec> = gc
        .theories
        .iter()
        .map(|t| {
            // Convert the syn::Type to its quoted token-stream form so the
            // pipeline (which has no syn dependency) can compare against
            // known theory type names like "PresburgerAlgebra".
            let ty = &t.theory_type;
            let theory_type = quote::quote!(#ty).to_string();
            TheoryRegistrationSpec {
                name: t.name.to_string(),
                theory_type,
                handled_types: t
                    .handled_types
                    .as_ref()
                    .map(|cats| cats.iter().map(|c| c.to_string()).collect()),
            }
        })
        .collect();

    // Channel categories and join patterns (when present)
    let (channel_categories, join_patterns): (Option<Vec<String>>, Vec<JoinPatternSpec>) =
        match &gc.channels {
            Some(cfg) => {
                let cats: Vec<String> = cfg
                    .channel_categories
                    .iter()
                    .map(|d| d.category.to_string())
                    .collect();
                let joins: Vec<JoinPatternSpec> = cfg
                    .join_patterns
                    .iter()
                    .map(|jp| JoinPatternSpec {
                        label: jp.label.to_string(),
                        channel_categories: jp
                            .channel_params
                            .iter()
                            .map(|p| p.category.to_string())
                            .collect(),
                    })
                    .collect();
                (Some(cats), joins)
            },
            None => (None, Vec::new()),
        };

    // Per-predicate annotation overrides
    let mut selectivity_overrides: HashMap<String, f64> = HashMap::new();
    let mut cost_overrides: HashMap<String, u32> = HashMap::new();
    if let Some(preds) = gc.builtin_predicates.as_ref() {
        for p in preds {
            let name = p.name.to_string();
            if let Some(s) = p.annotations.selectivity {
                selectivity_overrides.insert(name.clone(), s);
            }
            if let Some(c) = p.annotations.cost {
                cost_overrides.insert(name, c);
            }
        }
    }

    GuardConfigSpec {
        theories,
        channel_categories,
        join_patterns,
        selectivity_overrides,
        cost_overrides,
        has_explicit_connectives: gc.connectives.is_some(),
        has_explicit_predicates: gc.builtin_predicates.is_some(),
    }
}

/// Convert a single grammar rule to a PraTTaIL `RuleSpecInput`.
///
/// Only performs structural mapping — no flag classification.
fn convert_rule(rule: &GrammarRule, cat_names: &[String]) -> RuleSpecInput {
    // Convert syntax items
    let syntax = if let Some(ref pattern) = rule.syntax_pattern {
        convert_syntax_pattern(pattern, rule.term_context.as_deref().unwrap_or(&[]), cat_names)
    } else {
        convert_grammar_items(&rule.items, cat_names)
    };

    // Extract source location from the proc-macro span of the rule label
    let source_location = {
        let span = rule.label.span();
        let start = span.start();
        Some(mettail_prattail::SourceLocation {
            line: start.line as u32,
            column: start.column as u32,
        })
    };

    RuleSpecInput {
        label: rule.label.to_string(),
        category: rule.category.to_string(),
        syntax,
        associativity: if rule.is_right_assoc {
            Associativity::Right
        } else {
            Associativity::Left
        },
        shares_level_with_previous: rule.shares_level_with_previous,
        prefix_precedence: rule.prefix_bp,
        has_rust_code: rule.rust_code.is_some(),
        rust_code: rule.rust_code.as_ref().map(|rc| {
            let expr = &rc.code;
            quote::quote! { #expr }
        }),
        eval_mode: rule.eval_mode.as_ref().map(|e| format!("{:?}", e)),
        source_location,
        // Stage 3.13b (2026-05-01): propagate provenance flag from the AST.
        is_auto_injected: rule.is_auto_injected,
    }
}

/// Opt-Group: find a TermParam by name, recursing into Optional groups
/// so inner-param references inside `#opt(...)` resolve. Returns the
/// INNERMOST matching TermParam (e.g., the `Simple { name: e, ty: Int }`
/// inside an `Optional { params: [Simple{e,Int}] }`).
fn find_param_by_name<'a>(context: &'a [TermParam], name_str: &str) -> Option<&'a TermParam> {
    for p in context {
        match p {
            TermParam::Simple { name: n, .. } => {
                if n.to_string() == name_str {
                    return Some(p);
                }
            },
            TermParam::Abstraction { binder, body, .. } => {
                if binder.to_string() == name_str || body.to_string() == name_str {
                    return Some(p);
                }
            },
            TermParam::MultiAbstraction { binder, body, .. } => {
                if binder.to_string() == name_str || body.to_string() == name_str {
                    return Some(p);
                }
            },
            TermParam::GuardBody { name } => {
                if name.to_string() == name_str {
                    return Some(p);
                }
            },
            TermParam::Optional { params: inner } => {
                if let Some(found) = find_param_by_name(inner, name_str) {
                    return Some(found);
                }
            },
        }
    }
    None
}

/// Convert new-style syntax pattern to SyntaxItemSpec list.
fn convert_syntax_pattern(
    pattern: &[SyntaxExpr],
    context: &[TermParam],
    cat_names: &[String],
) -> Vec<SyntaxItemSpec> {
    let mut items = Vec::new();

    for expr in pattern {
        match expr {
            SyntaxExpr::Literal(text) => {
                items.push(SyntaxItemSpec::Terminal(text.clone()));
            },
            SyntaxExpr::Param(name) => {
                let name_str = name.to_string();
                // Look up the parameter type from context (recursing into
                // any Optional groups so inner-param references resolve).
                if let Some(param) = find_param_by_name(context, &name_str) {
                    match param {
                        TermParam::Simple { ty, .. } => {
                            let base_cat = extract_base_category(ty);
                            if cat_names.contains(&base_cat) {
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            } else {
                                items.push(SyntaxItemSpec::IdentCapture { param_name: name_str });
                            }
                        },
                        TermParam::Abstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_binder_category(ty),
                                    is_multi: false,
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        },
                        TermParam::MultiAbstraction { binder, body: _, ty, .. } => {
                            if binder.to_string() == name_str {
                                items.push(SyntaxItemSpec::Binder {
                                    param_name: name_str,
                                    category: extract_binder_category(ty),
                                    is_multi: true,
                                });
                            } else {
                                let base_cat = extract_base_category(ty);
                                items.push(SyntaxItemSpec::NonTerminal {
                                    category: base_cat,
                                    param_name: name_str,
                                });
                            }
                        },
                        TermParam::GuardBody { name } => {
                            // Phase 2F: emit a GuardExpression item so the
                            // generated parser switches into the
                            // predicate sublanguage parser at this point.
                            items.push(SyntaxItemSpec::GuardExpression {
                                param_name: name.to_string(),
                            });
                        },
                        TermParam::Optional { .. } => {
                            // Opt-Group: an Optional itself is never directly
                            // referenced by name in syntax_pattern — only its
                            // INNER params are. find_param_by_name unwraps
                            // through Optional, so reaching this arm means the
                            // lookup found the wrapper itself, which indicates
                            // a malformed lookup. Fall through to ident capture.
                            items.push(SyntaxItemSpec::IdentCapture { param_name: name_str });
                        },
                    }
                } else {
                    // Unknown parameter — treat as ident capture
                    items.push(SyntaxItemSpec::IdentCapture { param_name: name_str });
                }
            },
            SyntaxExpr::Op(op) => {
                // Pattern operations are handled as collections or special items
                convert_pattern_op(op, context, cat_names, &mut items);
            },
            SyntaxExpr::TokenKind { name, bind } => {
                // L9-3: consume ONE token of the declared custom KIND, binding
                // its text. An @-less capture gets a synthesized `__tok_<name>`
                // slot so the arg still reaches the semantic action (D-5).
                let kind_name = name.to_string();
                let param_name = bind
                    .as_ref()
                    .map(|b| b.to_string())
                    .unwrap_or_else(|| format!("__tok_{}", kind_name));
                items.push(SyntaxItemSpec::TokenKindCapture { kind_name, param_name });
            },
            SyntaxExpr::GuestBody { open, bind, .. } => {
                // L9-4: for the prattail ANALYSIS (binding powers / Parikh /
                // spine mergeability) a guest body behaves like a leading
                // token-kind capture — the opener kind triggers, and the whole
                // region is consumed atomically (non-mergeable). The actual
                // FltNode assembly is emitted by `binder.rs`'s
                // `GuestBodyCapture` position, not from this spec.
                items.push(SyntaxItemSpec::TokenKindCapture {
                    kind_name: open.to_string(),
                    param_name: bind.to_string(),
                });
            },
        }
    }

    items
}

/// Classify a parameter name from the term context into the correct SyntaxItemSpec.
///
/// Checks whether the parameter is a binder, a nonterminal, or an ident capture
/// based on its definition in the term context.
fn classify_param_from_context(
    name_str: &str,
    context: &[TermParam],
    cat_names: &[String],
) -> SyntaxItemSpec {
    if let Some(param) = find_param_by_name(context, name_str) {
        match param {
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_binder_category(ty),
                    is_multi: false,
                }
            },
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name_str => {
                SyntaxItemSpec::Binder {
                    param_name: name_str.to_string(),
                    category: extract_binder_category(ty),
                    is_multi: true,
                }
            },
            TermParam::Simple { ty, .. } => {
                let base_cat = extract_base_category(ty);
                if cat_names.contains(&base_cat) {
                    SyntaxItemSpec::NonTerminal {
                        category: base_cat,
                        param_name: name_str.to_string(),
                    }
                } else {
                    SyntaxItemSpec::IdentCapture { param_name: name_str.to_string() }
                }
            },
            // body of an abstraction — treat as nonterminal
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
                let base_cat = extract_base_category(ty);
                SyntaxItemSpec::NonTerminal {
                    category: base_cat,
                    param_name: name_str.to_string(),
                }
            },
            TermParam::GuardBody { name } => {
                // Phase 2F: emit GuardExpression; the parser switches
                // to the predicate sublanguage parser here.
                SyntaxItemSpec::GuardExpression { param_name: name.to_string() }
            },
            TermParam::Optional { .. } => {
                // Opt-Group: find_param_by_name unwraps Optional, so an
                // outer Optional should never be returned. Conservative
                // fallback: ident capture.
                SyntaxItemSpec::IdentCapture { param_name: name_str.to_string() }
            },
        }
    } else {
        SyntaxItemSpec::IdentCapture { param_name: name_str.to_string() }
    }
}

/// Convert a pattern operation to syntax items.
fn convert_pattern_op(
    op: &PatternOp,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(source_op) = source {
                // Chained pattern: e.g., *zip(ns,xs).*map(|n,x| n "?" x).*sep(",")
                convert_chained_sep(source_op, separator, context, cat_names, items);
            } else {
                let coll_name = collection.to_string();

                // Check if this is a multi-binder collection (e.g., xs.*sep(",")
                // where xs comes from ^[xs].p:[Name* -> Proc])
                let is_multi_binder = context.iter().any(|p| {
                    matches!(p, TermParam::MultiAbstraction { binder, .. }
                        if binder.to_string() == coll_name)
                });

                if is_multi_binder {
                    items.push(SyntaxItemSpec::BinderCollection {
                        param_name: coll_name,
                        separator: separator.clone(),
                    });
                } else {
                    // Phase 4 #5b (2026-05-12): propagate the per-slot
                    // kv_separator from the param's type. HashMap binder
                    // slots emit `Some(":")` (or user-overridden), Vec/
                    // HashBag/HashSet emit `None`. This populates the
                    // lexer's terminal set via `collect_terminals_recursive`
                    // in `pipeline.rs:4263-4296` so the `:` token is
                    // recognized by the lexer.
                    let (elem_cat, kind, kv) = find_collection_info(&coll_name, context);
                    items.push(SyntaxItemSpec::Collection {
                        param_name: coll_name,
                        element_category: elem_cat,
                        separator: separator.clone(),
                        key_val_separator: kv,
                        kind,
                    });
                }
            }
        },
        PatternOp::Zip { left, right } => {
            // Zip is usually followed by Map and Sep — handle at the Map level.
            // Classify each parameter correctly (binder vs nonterminal vs ident).
            items.push(classify_param_from_context(&left.to_string(), context, cat_names));
            items.push(classify_param_from_context(&right.to_string(), context, cat_names));
        },
        PatternOp::Map { source: _, params: _, body } => {
            // Map transforms — convert the body items.
            // Parameters inside the map body are local closure params (e.g., |n,x|)
            // and reference the same types as the original term context params.
            for expr in body {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        items.push(SyntaxItemSpec::Terminal(text.clone()));
                    },
                    SyntaxExpr::Param(name) => {
                        // Map closure params reference original context params.
                        // Classify them correctly.
                        items.push(classify_param_from_context(
                            &name.to_string(),
                            context,
                            cat_names,
                        ));
                    },
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, items);
                    },
                    SyntaxExpr::TokenKind { name, bind } => {
                        let kind_name = name.to_string();
                        let param_name = bind
                            .as_ref()
                            .map(|b| b.to_string())
                            .unwrap_or_else(|| format!("__tok_{}", kind_name));
                        items.push(SyntaxItemSpec::TokenKindCapture { kind_name, param_name });
                    },
                    SyntaxExpr::GuestBody { open, bind, .. } => {
                        items.push(SyntaxItemSpec::TokenKindCapture {
                            kind_name: open.to_string(),
                            param_name: bind.to_string(),
                        });
                    },
                }
            }
        },
        PatternOp::Opt { inner } => {
            // Optional groups: collect inner items and wrap in SyntaxItemSpec::Optional
            let mut opt_items = Vec::new();
            for expr in inner {
                match expr {
                    SyntaxExpr::Literal(text) => {
                        opt_items.push(SyntaxItemSpec::Terminal(text.clone()));
                    },
                    SyntaxExpr::Param(name) => {
                        let item =
                            classify_param_from_context(&name.to_string(), context, cat_names);
                        opt_items.push(item);
                    },
                    SyntaxExpr::Op(inner_op) => {
                        convert_pattern_op(inner_op, context, cat_names, &mut opt_items);
                    },
                    SyntaxExpr::TokenKind { name, bind } => {
                        let kind_name = name.to_string();
                        let param_name = bind
                            .as_ref()
                            .map(|b| b.to_string())
                            .unwrap_or_else(|| format!("__tok_{}", kind_name));
                        opt_items.push(SyntaxItemSpec::TokenKindCapture { kind_name, param_name });
                    },
                    SyntaxExpr::GuestBody { open, bind, .. } => {
                        opt_items.push(SyntaxItemSpec::TokenKindCapture {
                            kind_name: open.to_string(),
                            param_name: bind.to_string(),
                        });
                    },
                }
            }
            items.push(SyntaxItemSpec::Optional { inner: opt_items });
        },
        PatternOp::Var(name) => {
            items.push(SyntaxItemSpec::IdentCapture { param_name: name.to_string() });
        },
    }
}

/// Convert a chained Sep(Map(Zip(...))) pattern into composed Sep/Zip/Map items.
///
/// This handles patterns like `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")`,
/// converting them into composed `Sep { body: Zip { body: Map { .. } } }`
/// items that the RD generator can handle as a separated list of structured patterns.
fn convert_chained_sep(
    source_op: &PatternOp,
    separator: &str,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match source_op {
        PatternOp::Map { source, params, body } => {
            match source.as_ref() {
                PatternOp::Zip { left, right } => {
                    let left_name = left.to_string();
                    let right_name = right.to_string();

                    // Determine categories for left and right from the term context
                    let left_cat = find_param_category(&left_name, context);
                    let right_cat = find_param_category(&right_name, context);

                    // Build a mapping from closure params to zip params
                    // e.g., |n,x| means n→ns (left), x→xs (right)
                    let mut param_mapping: std::collections::HashMap<String, String> =
                        std::collections::HashMap::new();
                    if !params.is_empty() {
                        param_mapping.insert(params[0].to_string(), left_name.clone());
                    }
                    if params.len() >= 2 {
                        param_mapping.insert(params[1].to_string(), right_name.clone());
                    }

                    // Convert body items, resolving closure params to their original context
                    let body_items: Vec<SyntaxItemSpec> = body
                        .iter()
                        .map(|expr| match expr {
                            SyntaxExpr::Literal(text) => SyntaxItemSpec::Terminal(text.clone()),
                            SyntaxExpr::Param(name) => {
                                let name_str = name.to_string();
                                // Check if this is a closure param and map it back
                                if let Some(original) = param_mapping.get(&name_str) {
                                    classify_param_from_context(original, context, cat_names)
                                } else {
                                    classify_param_from_context(&name_str, context, cat_names)
                                }
                            },
                            SyntaxExpr::Op(_) => {
                                // Nested ops in map body — fallback to ident capture
                                SyntaxItemSpec::IdentCapture {
                                    param_name: "__nested_op__".to_string(),
                                }
                            },
                            SyntaxExpr::TokenKind { name, bind } => {
                                let kind_name = name.to_string();
                                let param_name = bind
                                    .as_ref()
                                    .map(|b| b.to_string())
                                    .unwrap_or_else(|| format!("__tok_{}", kind_name));
                                SyntaxItemSpec::TokenKindCapture { kind_name, param_name }
                            },
                            SyntaxExpr::GuestBody { open, bind, .. } => {
                                SyntaxItemSpec::TokenKindCapture {
                                    kind_name: open.to_string(),
                                    param_name: bind.to_string(),
                                }
                            },
                        })
                        .collect();

                    items.push(SyntaxItemSpec::Sep {
                        body: Box::new(SyntaxItemSpec::Zip {
                            left_name,
                            right_name,
                            left_category: left_cat,
                            right_category: right_cat,
                            body: Box::new(SyntaxItemSpec::Map { body_items }),
                        }),
                        separator: separator.to_string(),
                        kind: CollectionKind::Vec,
                    });
                },
                _ => {
                    // Unsupported map source — fall back to simple collection
                    items.push(SyntaxItemSpec::Collection {
                        param_name: "__chain__".to_string(),
                        element_category: "Unknown".to_string(),
                        separator: separator.to_string(),
                        key_val_separator: None,
                        kind: CollectionKind::Vec,
                    });
                },
            }
        },
        _ => {
            // Unsupported sep source — fall back to simple collection
            items.push(SyntaxItemSpec::Collection {
                param_name: "__chain__".to_string(),
                element_category: "Unknown".to_string(),
                separator: separator.to_string(),
                key_val_separator: None,
                kind: CollectionKind::Vec,
            });
        },
    }
}

/// Find the category of a parameter from the term context.
fn find_param_category(name: &str, context: &[TermParam]) -> String {
    for param in context {
        match param {
            TermParam::Simple { name: n, ty, .. } if n.to_string() == name => {
                return extract_base_category(ty);
            },
            TermParam::Abstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_binder_category(ty);
            },
            TermParam::Abstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            },
            TermParam::MultiAbstraction { binder, ty, .. } if binder.to_string() == name => {
                return extract_binder_category(ty);
            },
            TermParam::MultiAbstraction { body, ty, .. } if body.to_string() == name => {
                return extract_base_category(ty);
            },
            _ => {},
        }
    }
    "Unknown".to_string()
}

/// Convert old-style grammar items to SyntaxItemSpec list.
fn convert_grammar_items(
    grammar_items: &[GrammarItem],
    cat_names: &[String],
) -> Vec<SyntaxItemSpec> {
    let mut items = Vec::new();

    for gi in grammar_items {
        match gi {
            GrammarItem::Terminal(text) => {
                items.push(SyntaxItemSpec::Terminal(text.clone()));
            },
            GrammarItem::NonTerminal { ident: nt, kind } => {
                let nt_str = nt.to_string();
                // `Ident` now classifies as its own builtin kind (it used to reach this
                // arm only through the `nt_str == "Ident"` string test), so match the
                // kind. The string test is retained: it is what an UNDECLARED `Ident`
                // reference resolved through before the kind existed, and both routes
                // must keep producing the same `IdentCapture`.
                if matches!(kind, NonTerminalKind::Var | NonTerminalKind::Ident)
                    || nt_str == "Ident"
                {
                    items.push(SyntaxItemSpec::IdentCapture { param_name: nt_str.to_lowercase() });
                } else if cat_names.contains(&nt_str) {
                    items.push(SyntaxItemSpec::NonTerminal {
                        category: nt_str.clone(),
                        param_name: nt_str.to_lowercase(),
                    });
                } else {
                    items.push(SyntaxItemSpec::IdentCapture { param_name: nt_str.to_lowercase() });
                }
            },
            GrammarItem::Binder { category } => {
                items.push(SyntaxItemSpec::Binder {
                    param_name: format!("binder_{}", category.to_string().to_lowercase()),
                    category: category.to_string(),
                    is_multi: false,
                });
            },
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => {
                let kind = match coll_type {
                    CollectionType::HashBag | CollectionType::HashMap | CollectionType::PathMap => {
                        CollectionKind::HashBag
                    },
                    CollectionType::HashSet => CollectionKind::HashSet,
                    CollectionType::Vec => CollectionKind::Vec,
                };
                // Add open delimiter if present
                if let Some((ref open, _)) = delimiters {
                    items.push(SyntaxItemSpec::Terminal(open.clone()));
                }
                items.push(SyntaxItemSpec::Collection {
                    param_name: element_type.to_string().to_lowercase(),
                    element_category: element_type.to_string(),
                    separator: separator.clone(),
                    key_val_separator: None,
                    kind,
                });
                // Add close delimiter if present
                if let Some((_, ref close)) = delimiters {
                    items.push(SyntaxItemSpec::Terminal(close.clone()));
                }
            },
        }
    }

    items
}

/// Extract the base category name from a TypeExpr.
/// For Arrow types, follows the codomain (appropriate for body variables).
fn extract_base_category(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Base(ident) => ident.to_string(),
        TypeExpr::Collection { element, .. } => extract_base_category(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category(inner),
        TypeExpr::Refined { base, .. } => extract_base_category(base),
        TypeExpr::Map { value, .. } => extract_base_category(value),
    }
}

/// Extract the binder's category from an abstraction type.
/// For Arrow types `[A -> B]` or `[A* -> B]`, returns the domain category `A`.
fn extract_binder_category(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Arrow { domain, .. } => extract_base_category(domain),
        _ => extract_base_category(ty),
    }
}

/// Find collection info (element category, kind, and optional kv_separator)
/// from term context.
///
/// Phase 4 #5b (2026-05-12): also returns the optional key/value separator
/// for HashMap collection slots. For Vec/HashBag/HashSet, the kv_separator
/// is `None`. For HashMap (whether parsed as `TypeExpr::Collection {
/// coll_type: HashMap, ... }` or `TypeExpr::Map { ... }`), the kv_separator
/// defaults to `":"` (the language! `map_defaults`).
fn find_collection_info(
    name: &str,
    context: &[TermParam],
) -> (String, CollectionKind, Option<String>) {
    for param in context {
        if let TermParam::Simple { name: n, ty, .. } = param {
            if n.to_string() == name {
                if let TypeExpr::Collection { coll_type, element, .. } = ty {
                    let elem_cat = extract_base_category(element);
                    let kind = match coll_type {
                        CollectionType::HashBag
                        | CollectionType::HashMap
                        | CollectionType::PathMap => CollectionKind::HashBag,
                        CollectionType::HashSet => CollectionKind::HashSet,
                        CollectionType::Vec => CollectionKind::Vec,
                    };
                    // Stage 3 (2026-06-27): lexer-terminal kv-source routed
                    // through the single `kv_sep_for` resolver. An inline term-
                    // context collection type carries no declared delimiters, so
                    // `declared = None` ⇒ per-type default (`HashMap`/`PathMap`
                    // ⇒ `":"`, else `None`) — byte-identical to the former match.
                    let kv = kv_sep_for(coll_type, None);
                    return (elem_cat, kind, kv);
                }
                if let TypeExpr::Map { value, .. } = ty {
                    // Phase 4 #5b (2026-05-12): `HashMap(K, V)` Map type.
                    // Stage 3 (2026-06-27): kv via `kv_sep_for(HashMap, None)` ⇒
                    // `Some(":")`, byte-identical to the former literal.
                    let elem_cat = extract_base_category(value);
                    return (
                        elem_cat,
                        CollectionKind::HashBag,
                        kv_sep_for(&CollectionType::HashMap, None),
                    );
                }
            }
        }
    }

    // Fallback: unknown element type
    ("Unknown".to_string(), CollectionKind::Vec, None)
}

// ══════════════════════════════════════════════════════════════════════════════
// Semantic dependency groups for transitive liveness analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Collect semantic dependency groups from equations, rewrites, and the logic block.
///
/// Each group is the set of constructor labels co-referenced by a single equation,
/// rewrite rule, or the entire logic block. The pipeline uses these groups for
/// transitive liveness analysis: if any label in a group is parsing-live, all labels
/// in the group are semantically live (the user's specification references them).
///
/// **Extraction strategies:**
/// - **equations/rewrites**: Structured `Pattern` traversal via `collect_constructor_labels()`
/// - **logic**: `TokenStream` scanning — intersect `Ident` tokens with known rule labels
///
/// The logic block is conservatively treated as a single dependency group because it
/// stores raw Ascent syntax (`TokenStream`), not structured `Pattern` types.
pub fn collect_semantic_dependency_groups(language: &LanguageDef) -> Vec<HashSet<String>> {
    // Collect all known constructor labels from terms for logic block matching.
    let known_labels: HashSet<String> = language
        .terms
        .iter()
        .map(|rule| rule.label.to_string())
        .collect();

    let mut groups = Vec::new();

    // Equations: structured Pattern traversal.
    for eq in &language.equations {
        let mut labels = HashSet::new();
        eq.left.collect_constructor_labels(&mut labels);
        eq.right.collect_constructor_labels(&mut labels);
        if !labels.is_empty() {
            groups.push(labels);
        }
    }

    // Rewrites: structured Pattern traversal.
    for rw in &language.rewrites {
        let mut labels = HashSet::new();
        rw.left.collect_constructor_labels(&mut labels);
        rw.right.collect_constructor_labels(&mut labels);
        if !labels.is_empty() {
            groups.push(labels);
        }
    }

    // Logic block: scan TokenStream for Ident tokens matching known constructor labels.
    // The logic block stores raw Ascent syntax (TokenStream), not structured Patterns.
    // Conservative: treats the entire block as one dependency group.
    if let Some(logic) = &language.logic {
        let mut labels = HashSet::new();
        collect_constructor_idents_from_token_stream(&logic.content, &known_labels, &mut labels);
        if !labels.is_empty() {
            groups.push(labels);
        }
    }

    groups
}

/// Recursively scan a `TokenStream` for `Ident` tokens that match known constructor labels.
///
/// Handles nested `Group` token trees (delimited by `(...)`, `{...}`, `[...]`).
/// Constructor labels are typically CamelCase (`PIn`, `PNew`) while Ascent variables
/// are lowercase (`p0`, `x`), so false positives are negligible.
fn collect_constructor_idents_from_token_stream(
    tokens: &proc_macro2::TokenStream,
    known_labels: &HashSet<String>,
    labels: &mut HashSet<String>,
) {
    for tt in tokens.clone() {
        match tt {
            proc_macro2::TokenTree::Ident(ident) => {
                let s = ident.to_string();
                if known_labels.contains(&s) {
                    labels.insert(s);
                }
            },
            proc_macro2::TokenTree::Group(group) => {
                collect_constructor_idents_from_token_stream(&group.stream(), known_labels, labels);
            },
            _ => {}, // Punct, Literal — skip
        }
    }
}

/// Generate the PraTTaIL parser along with pipeline analysis data.
///
/// Returns `(TokenStream, PipelineAnalysis)` where the analysis captures
/// WFST-derived data (dead rules, constructor weights, category weights)
/// for downstream optimization by the Ascent codegen.
///
/// # Errors
///
/// `Err(diagnostic)` from either of the two fallible stages this function joins:
/// the `LanguageDef → LanguageSpec` bridge (an undecodable `options` value, G7)
/// and the PraTTaIL pipeline itself (a lexer soundness gate rejecting the
/// grammar, change 7). Both messages are user-facing and reach `language!`, which
/// renders them as `compile_error!`.
pub fn generate_prattail_parser_with_analysis(
    language: &LanguageDef,
) -> Result<(proc_macro2::TokenStream, mettail_prattail::PipelineAnalysis), String> {
    let spec = language_def_to_spec(language)?;
    mettail_prattail::generate_parser_with_analysis(&spec)
}

/// ★ THE TWO REFUSALS THIS BRIDGE CAN RAISE, asserted on the text they carry.
#[cfg(test)]
mod refusal_tests {
    use super::*;
    use quote::quote;

    fn parse_language(source: proc_macro2::TokenStream) -> LanguageDef {
        syn::parse2(source).expect("the fixture grammar must parse")
    }

    /// The fixture body, parameterised by the token block, so the mutation and
    /// its control differ in exactly one token declaration.
    fn modal_grammar(name: &str, extra_default_token: proc_macro2::TokenStream) -> LanguageDef {
        let name = syn::Ident::new(name, proc_macro2::Span::call_site());
        parse_language(quote! {
            name: #name,
            options { emit_tests: false, emit_simulator: false, emit_blockly: false },
            types { Term },
            tokens {
                PushBang = "!" push(inner) ;
                #extra_default_token
                raw mode inner {
                    CloseInner = "!" pop ;
                    GuestChunk = "[^!]+" ;
                }
            },
            terms {
                Plus . a:Term, b:Term |- a "+" b : Term;
            },
        })
    }

    /// ★ #141 change 7 — a lexer soundness rejection REACHES the macro boundary
    /// as a value.
    ///
    /// MUTATION: `PlainBang`, whose pattern `"!"` is the same as the mode-pushing
    /// `PushBang`'s. The two collapse into one DFA accepting state with different
    /// mode effects, so the active mode becomes path-dependent — the Delimiter
    /// Unambiguity Invariant — and `prattail` refuses to emit a lexer.
    ///
    /// Before this change the refusal travelled through
    /// `generate_lexer_as_string_hybrid`, a wrapper whose whole body was
    /// `Err(rejection) => panic!("{rejection}")`, inside a cranelift-compiled
    /// proc macro: `rustc` died with `fatal runtime error: Rust cannot catch
    /// foreign exceptions` and printed nothing. The fallible entry point it wraps
    /// had existed, unused outside `lexer.rs`'s own tests, since `87292ef4`.
    ///
    /// CONTROL that must NOT discriminate: the same grammar with `PlainBang`
    /// removed — one token declaration, nothing else — must generate. Without it
    /// this cell would also be satisfied by a bridge that rejected every modal
    /// grammar, or that failed for an unrelated reason and happened to mention
    /// the phrase.
    #[test]
    fn a_lexer_soundness_rejection_returns_a_message_naming_both_tokens() {
        let rejected = modal_grammar("RedDuiBad", quote! { PlainBang = "!" ; });

        // MUTATION APPLIED: the conflicting declaration really is present, and
        // the control really lacks it.
        assert!(
            rejected.token_defs.iter().any(|t| t.name == "PlainBang"),
            "the mutation must declare `PlainBang`",
        );

        let rejection = generate_prattail_parser_with_analysis(&rejected)
            .expect_err("the `!` push/plain conflict must be refused, not emitted");
        assert!(
            rejection.contains("DUI violation"),
            "the grammar was refused, but not as a DUI violation: {rejection}",
        );
        assert!(
            rejection.contains("PushBang") && rejection.contains("PlainBang"),
            "the diagnostic must name BOTH conflicting tokens or it cannot be \
             acted on: {rejection}",
        );

        // ★ THE CONTROL — drop the one conflicting token and the same shape emits.
        let accepted = modal_grammar("RedDuiOk", quote! {});
        assert!(
            !accepted.token_defs.iter().any(|t| t.name == "PlainBang"),
            "the control must differ in exactly that declaration",
        );
        let (code, _analysis) = generate_prattail_parser_with_analysis(&accepted)
            .expect("removing the conflicting token must make the same grammar generable");
        assert!(!code.is_empty(), "the control must really emit a parser, not an empty stream");
    }

    /// ★ #141 group G7 — an out-of-domain `options { }` value REFUSES instead of
    /// asserting `unreachable!`.
    ///
    /// MUTATION: the option map is written directly, which is the only way to
    /// reach these arms — `ast/src/language/parse.rs` rejects the same values
    /// while parsing the `options` block, which is exactly the claim
    /// `unreachable!("… validated at parse time")` was making. That claim is not
    /// disputed here; what is asserted is that the two domains' AGREEMENT is now
    /// checkable, and that a disagreement produces a message instead of a
    /// `SIGABRT` with no output.
    ///
    /// CONTROL that must NOT discriminate: the in-domain value on the same
    /// option, on the same fixture, must still convert.
    #[test]
    fn an_out_of_domain_option_value_refuses_instead_of_asserting() {
        let cases: [(&str, AttributeValue, AttributeValue, &str); 3] = [
            (
                "beam_width",
                AttributeValue::Keyword("aggressive".to_string()),
                AttributeValue::Keyword("auto".to_string()),
                "the keyword `aggressive`",
            ),
            (
                "reserved_keywords",
                AttributeValue::Bool(true),
                AttributeValue::Keyword("none".to_string()),
                "a boolean",
            ),
            (
                "log_semiring_model_path",
                AttributeValue::Int(7),
                AttributeValue::Str("model.json".to_string()),
                "an integer",
            ),
        ];

        for (option, out_of_domain, in_domain, shape) in cases {
            let mut language = crate::gen::empty_language_for_tests();
            language.options.insert(option.to_string(), out_of_domain);

            let rejection = language_def_to_spec(&language)
                .err()
                .unwrap_or_else(|| panic!("`{option}` must refuse an out-of-domain value"));
            assert!(
                rejection.contains(option),
                "the diagnostic must name the option it refused: {rejection}",
            );
            assert!(
                rejection.contains(shape),
                "the diagnostic must name the SHAPE it found ({shape}): {rejection}",
            );
            assert!(
                rejection.contains("ast/src/language/parse.rs"),
                "★ the `PreValidated` claim must travel with the refusal — the \
                 message names the validator whose domain has drifted: {rejection}",
            );

            // ★ THE CONTROL — the same option, in domain, on the same fixture.
            let mut language = crate::gen::empty_language_for_tests();
            language.options.insert(option.to_string(), in_domain);
            assert!(
                language_def_to_spec(&language).is_ok(),
                "an in-domain `{option}` must still convert — otherwise the \
                 refusal above proves only that the bridge rejects everything",
            );
        }
    }
}
