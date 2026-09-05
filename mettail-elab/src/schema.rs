use crate::canonical::{RhoValue, ValueDecodeError};
use mettail_grammar_core as core;
use std::collections::{BTreeMap, BTreeSet};

const TOP_LEVEL_KEYS: &[&str] = &[
    "mettail",
    "name",
    "options",
    "rights",
    "semantics",
    "types",
    "literals",
    "tokens",
    "modes",
    "sync",
    "tree_invariants",
    "guards",
    "terms",
    "equations",
    "rewrites",
    "relations",
    "oslf",
    "extends",
    "includes",
    "mixins",
    "exports",
    "replacements",
    "context",
    "doc",
];

#[derive(Clone, Debug)]
pub(crate) struct LanguageSchema {
    notation: String,
    pub name: String,
    options: Options,
    requested_rights: core::LanguageRights,
    semantics: Vec<String>,
    types: Vec<TypeDecl>,
    literals: Vec<LiteralDecl>,
    tokens: Vec<TokenDecl>,
    modes: Vec<ModeDecl>,
    synchronization: Vec<core::SyncConstraint>,
    tree_invariants: Vec<NamedValue>,
    guards: Option<GuardSchema>,
    terms: Vec<TermDecl>,
    equations: Vec<RhoValue>,
    rewrites: Vec<RhoValue>,
    relations: Vec<RhoValue>,
    exports: Vec<(String, String)>,
    context: Option<String>,
    documentation: Option<String>,
    theory: core::TheoryCoreV1,
}

#[derive(Clone, Debug, Default)]
struct Options {
    beam_width: Option<core::BeamWidth>,
    log_semiring_model_path: Option<String>,
    reserved_keywords: Option<core::KeywordReservation>,
    recovery: Option<core::RecoveryConfiguration>,
}

#[derive(Clone, Debug)]
struct TypeDecl {
    name: String,
    carrier: core::Carrier,
    collection: Option<CollectionDecl>,
    refinement: Option<RefinementDecl>,
    admits_variables: bool,
}

#[derive(Clone, Debug)]
struct CollectionDecl {
    kind: core::CollectionKind,
    open: Option<String>,
    close: Option<String>,
    separator: Option<String>,
    key_value_separator: Option<String>,
}

#[derive(Clone, Debug)]
struct RefinementDecl {
    variable: String,
    base: String,
    predicate: RhoValue,
}

#[derive(Clone, Debug)]
struct LiteralDecl {
    category: String,
    pattern: String,
    evaluation: core::NativeEvaluation,
}

#[derive(Clone, Debug)]
struct TokenDecl {
    name: String,
    pattern: String,
    category: Option<String>,
    evaluation: Option<core::NativeEvaluation>,
    priority: i16,
    push: Option<String>,
    pop: bool,
    stream: Option<String>,
}

#[derive(Clone, Debug)]
struct ModeDecl {
    name: String,
    raw: bool,
    tokens: Vec<TokenDecl>,
}

#[derive(Clone, Debug)]
struct NamedValue {
    name: String,
    value: RhoValue,
}

#[derive(Clone, Debug)]
struct GuardSchema {
    value: RhoValue,
    theories: Vec<core::GuardTheory>,
    channel_categories: Option<Vec<String>>,
    join_patterns: Vec<core::JoinPattern>,
    selectivity: BTreeMap<String, f64>,
    costs: BTreeMap<String, u32>,
    has_connectives: bool,
    has_predicates: bool,
}

#[derive(Clone, Debug)]
struct TermDecl {
    label: String,
    category: String,
    context: Vec<Param>,
    body: TermBody,
    evaluation: Option<core::NativeEvaluation>,
    mode: Option<core::EvaluationMode>,
    associativity: core::Associativity,
    prefix_binding_power: Option<u16>,
    shares_previous_level: bool,
    tier: Option<core::TierDirective>,
}

#[derive(Clone, Debug)]
enum TermBody {
    Judgement(Vec<SyntaxNode>),
    Bnf(Vec<BnfNode>),
}

#[derive(Clone, Debug)]
enum Param {
    Plain {
        name: String,
        ty: TypeExpr,
    },
    Binder {
        binder: String,
        body: String,
        ty: TypeExpr,
        multiple: bool,
    },
    Guard(String),
    Optional(Vec<Param>),
}

impl Drop for Param {
    fn drop(&mut self) {
        let mut work = Vec::<Box<Param>>::new();
        detach_param_children(self, &mut work);
        while let Some(mut param) = work.pop() {
            detach_param_children(&mut param, &mut work);
        }
    }
}

fn detach_param_children(param: &mut Param, work: &mut Vec<Box<Param>>) {
    if let Param::Optional(params) = param {
        work.extend(std::mem::take(params).into_iter().map(Box::new));
    }
}

#[derive(Clone, Debug)]
enum TypeExpr {
    Base(String),
    Arrow(Box<TypeExpr>, Box<TypeExpr>),
    Multi(Box<TypeExpr>),
    Collection(core::CollectionKind, Box<TypeExpr>, Option<Box<TypeExpr>>),
}

impl Drop for TypeExpr {
    fn drop(&mut self) {
        let mut work = Vec::<Box<TypeExpr>>::new();
        detach_type_expr_children(self, &mut work);
        while let Some(mut value) = work.pop() {
            detach_type_expr_children(&mut value, &mut work);
        }
    }
}

fn detach_type_expr_children(value: &mut TypeExpr, work: &mut Vec<Box<TypeExpr>>) {
    let leaf = || Box::new(TypeExpr::Base(String::new()));
    match value {
        TypeExpr::Arrow(left, right) => {
            work.push(std::mem::replace(left, leaf()));
            work.push(std::mem::replace(right, leaf()));
        },
        TypeExpr::Multi(value) => work.push(std::mem::replace(value, leaf())),
        TypeExpr::Collection(_, key, value) => {
            work.push(std::mem::replace(key, leaf()));
            if let Some(value) = value {
                work.push(std::mem::replace(value, leaf()));
            }
        },
        TypeExpr::Base(_) => {},
    }
}

#[derive(Clone, Debug)]
enum SyntaxNode {
    Reference(String),
    Literal(String),
    Separated(Box<SyntaxNode>, String),
    Zip(String, String),
    Map {
        source: Box<SyntaxNode>,
        bindings: Vec<String>,
        body: Vec<SyntaxNode>,
    },
    Optional(Vec<SyntaxNode>),
    Token {
        name: String,
        binding: Option<String>,
    },
    ForeignLanguage {
        binding: String,
        open: String,
        close: String,
    },
}

impl Drop for SyntaxNode {
    fn drop(&mut self) {
        let mut work = Vec::<Box<SyntaxNode>>::new();
        detach_syntax_node_children(self, &mut work);
        while let Some(mut node) = work.pop() {
            detach_syntax_node_children(&mut node, &mut work);
        }
    }
}

fn detach_syntax_node_children(node: &mut SyntaxNode, work: &mut Vec<Box<SyntaxNode>>) {
    let leaf = || Box::new(SyntaxNode::Reference(String::new()));
    match node {
        SyntaxNode::Separated(source, _) => {
            work.push(std::mem::replace(source, leaf()));
        },
        SyntaxNode::Map { source, body, .. } => {
            work.push(std::mem::replace(source, leaf()));
            work.extend(std::mem::take(body).into_iter().map(Box::new));
        },
        SyntaxNode::Optional(body) => {
            work.extend(std::mem::take(body).into_iter().map(Box::new));
        },
        SyntaxNode::Reference(_)
        | SyntaxNode::Literal(_)
        | SyntaxNode::Zip(_, _)
        | SyntaxNode::Token { .. }
        | SyntaxNode::ForeignLanguage { .. } => {},
    }
}

#[derive(Clone, Debug)]
enum BnfNode {
    Literal(String),
    Nonterminal(String),
    Binding(String),
    Collection {
        kind: core::CollectionKind,
        element: String,
        separator: String,
        open: Option<String>,
        close: Option<String>,
    },
}

pub(crate) fn decode(value: &RhoValue) -> Result<LanguageSchema, ValueDecodeError> {
    let spec = expect_map(value, "$")?;
    reject_unknown_keys(spec, TOP_LEVEL_KEYS, "$")?;
    let notation = expect_string(required(spec, "mettail", "$")?, "$.mettail")?;
    if notation != "language/2" && notation != "language/3" {
        return error("$.mettail", format!("unsupported schema `{notation}`"));
    }
    if notation == "language/2" && spec.contains_key("oslf") {
        return error("$.oslf", "`oslf` requires the `language/3` schema");
    }
    let name = identifier(expect_string(required(spec, "name", "$")?, "$.name")?, "$.name")?;
    let options = spec
        .get("options")
        .map(|value| decode_options(value, "$.options"))
        .transpose()?
        .unwrap_or_default();
    let requested_rights = decode_requested_rights(spec.get("rights"), "$.rights")?;
    let semantics = spec
        .get("semantics")
        .map(|value| decode_semantics(value, "$.semantics"))
        .transpose()?
        .unwrap_or_else(|| vec!["Rust".into()]);
    let types = decode_sequence(spec.get("types"), "$.types", decode_type)?;
    let literals = decode_sequence(spec.get("literals"), "$.literals", decode_literal)?;
    let tokens = decode_sequence(spec.get("tokens"), "$.tokens", decode_token)?;
    let modes = decode_sequence(spec.get("modes"), "$.modes", decode_mode)?;
    let synchronization = decode_sequence(spec.get("sync"), "$.sync", decode_synchronization)?;
    let tree_invariants =
        decode_sequence(spec.get("tree_invariants"), "$.tree_invariants", decode_tree_invariant)?;
    let guards = spec
        .get("guards")
        .map(|value| decode_guards(value, "$.guards"))
        .transpose()?;
    let terms = decode_sequence(spec.get("terms"), "$.terms", decode_term)?;
    let equations =
        validate_value_sequence(spec.get("equations"), "$.equations", validate_equation)?;
    let rewrites = validate_value_sequence(spec.get("rewrites"), "$.rewrites", validate_rewrite)?;
    let relations =
        validate_value_sequence(spec.get("relations"), "$.relations", validate_relation)?;
    if notation == "language/3" && !relations.is_empty() {
        return error(
            "$.relations",
            "language/3 relations require typed `oslf.judgments`; legacy relation declarations do not identify argument sorts or a decision policy",
        );
    }
    let theory = if notation == "language/3" {
        decode_oslf(spec.get("oslf"), "$.oslf")?
    } else {
        core::TheoryCoreV1::structural()
    };
    for key in ["extends", "includes", "mixins"] {
        validate_name_list(spec.get(key), &format!("$.{key}"))?;
    }
    let exports = decode_exports(spec.get("exports"), "$.exports")?;
    validate_replacements(spec.get("replacements"), "$.replacements")?;
    let context = optional_string(spec, "context", "$")?;
    let documentation = optional_string(spec, "doc", "$")?;
    validate_unique_names(types.iter().map(|value| &value.name), "$.types")?;
    validate_unique_names(tokens.iter().map(|value| &value.name), "$.tokens")?;
    validate_unique_names(modes.iter().map(|value| &value.name), "$.modes")?;
    validate_unique_names(terms.iter().map(|value| &value.label), "$.terms")?;
    validate_unique_names(tree_invariants.iter().map(|value| &value.name), "$.tree_invariants")?;
    Ok(LanguageSchema {
        notation: notation.to_string(),
        name,
        options,
        requested_rights,
        semantics,
        types,
        literals,
        tokens,
        modes,
        synchronization,
        tree_invariants,
        guards,
        terms,
        equations,
        rewrites,
        relations,
        exports,
        context,
        documentation,
        theory,
    })
}

pub(crate) fn decode_composed(
    value: &RhoValue,
    resolver: Option<&dyn crate::canonical::LanguageValueResolver>,
) -> Result<LanguageSchema, ValueDecodeError> {
    let composed = compose_value(value, resolver)?;
    let mut schema = decode(&composed)?;
    schema.apply_exports()?;
    Ok(schema)
}

#[derive(Clone, Copy)]
enum DuplicatePolicy {
    Error,
    Override,
}

#[derive(Clone)]
struct ReplacementDecision {
    label: String,
    keep_left: bool,
    rename: Option<String>,
}

const MAX_COMPOSED_LANGUAGES: usize = 256;

#[derive(Clone, Copy)]
enum CompositionKind {
    Extends,
    Includes,
    Mixin,
}

struct CompositionDependency {
    kind: CompositionKind,
    name: String,
}

struct CompositionFrame {
    name: String,
    local: RhoValue,
    replacements: Vec<ReplacementDecision>,
    dependencies: Vec<CompositionDependency>,
    next_dependency: usize,
    mixed: Option<RhoValue>,
}

fn compose_value(
    value: &RhoValue,
    resolver: Option<&dyn crate::canonical::LanguageValueResolver>,
) -> Result<RhoValue, ValueDecodeError> {
    let mut pending = Some(value.clone());
    let mut completed = None;
    let mut frames = Vec::<CompositionFrame>::new();
    let mut active = Vec::<String>::new();
    let mut admitted_languages = 0usize;

    loop {
        if let Some(value) = pending.take() {
            admitted_languages = admitted_languages.checked_add(1).ok_or_else(|| {
                ValueDecodeError::new("$", "language composition count overflowed")
            })?;
            if admitted_languages > MAX_COMPOSED_LANGUAGES {
                return error(
                    "$",
                    format!(
                        "language composition exceeds {MAX_COMPOSED_LANGUAGES} resolved languages"
                    ),
                );
            }
            crate::canonical::admit_canonical_value(&value)?;
            let schema = decode(&value)?;
            let values = expect_map(&value, "$")?;
            let extends = values
                .get("extends")
                .map(|value| decode_ident_list(value, "$.extends"))
                .transpose()?
                .unwrap_or_default();
            let includes = values
                .get("includes")
                .map(|value| decode_ident_list(value, "$.includes"))
                .transpose()?
                .unwrap_or_default();
            let mixins = values
                .get("mixins")
                .map(|value| decode_ident_list(value, "$.mixins"))
                .transpose()?
                .unwrap_or_default();
            if extends.is_empty() && includes.is_empty() && mixins.is_empty() {
                completed = Some(value);
                continue;
            }
            let resolver = resolver.ok_or_else(|| {
                ValueDecodeError::new(
                    "$",
                    "extends/includes/mixins require a registry language resolver",
                )
            })?;
            if active.contains(&schema.name) {
                active.push(schema.name);
                return error("$", format!("language composition cycle: {}", active.join(" -> ")));
            }
            active.push(schema.name.clone());
            let replacements =
                decode_replacement_decisions(values.get("replacements"), "$.replacements")?;
            let local = without_composition_keys(values);
            let dependencies = extends
                .into_iter()
                .map(|name| CompositionDependency { kind: CompositionKind::Extends, name })
                .chain(
                    includes.into_iter().map(|name| CompositionDependency {
                        kind: CompositionKind::Includes,
                        name,
                    }),
                )
                .chain(
                    mixins
                        .into_iter()
                        .map(|name| CompositionDependency { kind: CompositionKind::Mixin, name }),
                )
                .collect::<Vec<_>>();
            let first_name = dependencies[0].name.clone();
            frames.push(CompositionFrame {
                name: schema.name,
                local,
                replacements,
                dependencies,
                next_dependency: 0,
                mixed: None,
            });
            pending = Some(resolve_language_value(&first_name, resolver)?);
            continue;
        }

        let child = completed
            .take()
            .expect("composition machine has a child result");
        let Some(frame) = frames.last_mut() else {
            return Ok(child);
        };
        let dependency = &frame.dependencies[frame.next_dependency];
        match dependency.kind {
            CompositionKind::Extends => {
                frame.local = merge_language_values(
                    child,
                    std::mem::replace(&mut frame.local, RhoValue::Nil),
                    DuplicatePolicy::Error,
                    &frame.replacements,
                    &format!("$.extends[{}]", dependency.name),
                )?;
            },
            CompositionKind::Includes => {
                let mut included = child;
                retain_fields(
                    &mut included,
                    &[
                        "options",
                        "rights",
                        "semantics",
                        "types",
                        "literals",
                        "tokens",
                        "modes",
                        "sync",
                        "tree_invariants",
                        "guards",
                        "terms",
                        "exports",
                        "context",
                        "doc",
                    ],
                );
                frame.local = merge_language_values(
                    included,
                    std::mem::replace(&mut frame.local, RhoValue::Nil),
                    DuplicatePolicy::Override,
                    &frame.replacements,
                    &format!("$.includes[{}]", dependency.name),
                )?;
            },
            CompositionKind::Mixin => {
                let mut fragment = child;
                // Compile-time `language_fragment!` contributes exactly the
                // open grammar surface: categories, literal/custom tokens,
                // lexer modes, and productions.  Requested rights and every
                // semantic field are intentionally absent from this
                // projection; a reusable grammar fragment is data, not an
                // authority or an evaluator.  See MixinProjection.v.
                retain_fields(&mut fragment, &["types", "literals", "tokens", "modes", "terms"]);
                frame.mixed = Some(match frame.mixed.take() {
                    None => fragment,
                    Some(accumulated) => merge_language_values(
                        accumulated,
                        fragment,
                        DuplicatePolicy::Override,
                        &[],
                        &format!("$.mixins[{}]", dependency.name),
                    )?,
                });
            },
        }
        frame.next_dependency += 1;
        if frame.next_dependency < frame.dependencies.len() {
            let name = frame.dependencies[frame.next_dependency].name.clone();
            let resolver = resolver.expect("a frame is created only with a resolver");
            pending = Some(resolve_language_value(&name, resolver)?);
            continue;
        }

        let mut frame = frames.pop().expect("checked a composition frame");
        active.pop();
        if let Some(mixed) = frame.mixed.take() {
            frame.local = merge_language_values(
                mixed,
                frame.local,
                DuplicatePolicy::Override,
                &frame.replacements,
                "$.mixins",
            )?;
        }
        let RhoValue::Map(local_values) = &mut frame.local else {
            unreachable!()
        };
        let mut local = std::mem::take(local_values);
        let notation = local
            .get("mettail")
            .cloned()
            .unwrap_or_else(|| RhoValue::String("language/2".into()));
        local.insert("mettail".into(), notation);
        local.insert("name".into(), RhoValue::String(frame.name));
        local.remove("replacements");
        completed = Some(RhoValue::Map(local));
    }
}

fn resolve_language_value(
    name: &str,
    resolver: &dyn crate::canonical::LanguageValueResolver,
) -> Result<RhoValue, ValueDecodeError> {
    resolver
        .resolve_language(name)
        .map_err(|message| ValueDecodeError::new(format!("registry:{name}"), message))?
        .ok_or_else(|| ValueDecodeError::new(format!("registry:{name}"), "language not found"))
}

fn without_composition_keys(values: &BTreeMap<String, RhoValue>) -> RhoValue {
    let mut values = values.clone();
    values.remove("extends");
    values.remove("includes");
    values.remove("mixins");
    RhoValue::Map(values)
}

fn retain_fields(value: &mut RhoValue, fields: &[&str]) {
    let RhoValue::Map(values) = value else { return };
    values.retain(|key, _| fields.contains(&key.as_str()));
}

fn decode_replacement_decisions(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<Vec<ReplacementDecision>, ValueDecodeError> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    expect_list(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let item_path = format!("{path}[{index}]");
            let values = expect_map(value, &item_path)?;
            Ok(ReplacementDecision {
                label: expect_string(
                    required(values, "label", &item_path)?,
                    &format!("{item_path}.label"),
                )?
                .to_string(),
                keep_left: expect_string(
                    required(values, "keep", &item_path)?,
                    &format!("{item_path}.keep"),
                )? == "left",
                rename: optional_string(values, "rename", &item_path)?,
            })
        })
        .collect()
}

fn merge_language_values(
    mut base: RhoValue,
    mut extension: RhoValue,
    policy: DuplicatePolicy,
    replacements: &[ReplacementDecision],
    path: &str,
) -> Result<RhoValue, ValueDecodeError> {
    apply_replacement_decisions(&mut base, &mut extension, replacements, path)?;
    let RhoValue::Map(base_values) = &mut base else {
        return error(path, "base language is not a map");
    };
    let mut base = std::mem::take(base_values);
    let RhoValue::Map(extension_values) = &mut extension else {
        return error(path, "extension language is not a map");
    };
    let mut extension = std::mem::take(extension_values);
    let language3 = [&base, &extension]
        .iter()
        .any(|values| values.get("mettail") == Some(&RhoValue::String("language/3".into())));
    for key in ["mettail", "name", "extends", "includes", "mixins", "replacements"] {
        base.remove(key);
        extension.remove(key);
    }
    let mut output = BTreeMap::new();
    merge_option_maps(&mut output, &base, &extension, "options", path)?;
    merge_named_field(
        &mut output,
        &base,
        &extension,
        "types",
        type_name,
        DuplicatePolicy::Error,
        path,
    )?;
    merge_named_field(&mut output, &base, &extension, "literals", literal_name, policy, path)?;
    merge_named_field(&mut output, &base, &extension, "tokens", record_name, policy, path)?;
    merge_modes(&mut output, &base, &extension, policy, path)?;
    replace_if_extension_nonempty(&mut output, &base, &extension, "sync");
    replace_if_extension_nonempty(&mut output, &base, &extension, "tree_invariants");
    merge_guards(&mut output, &base, &extension, path)?;
    merge_named_field(&mut output, &base, &extension, "terms", term_label, policy, path)?;
    merge_named_field(&mut output, &base, &extension, "equations", record_name, policy, path)?;
    merge_named_field(&mut output, &base, &extension, "rewrites", record_name, policy, path)?;
    merge_relations(&mut output, &base, &extension, path)?;
    merge_oslf(&mut output, &base, &extension, path)?;
    append_unique_field(&mut output, &base, &extension, "exports", path)?;
    merge_requested_rights(&mut output, &base, &extension, path)?;
    for key in ["semantics", "context", "doc"] {
        if let Some(value) = extension.get(key).or_else(|| base.get(key)) {
            output.insert(key.into(), value.clone());
        }
    }
    output.insert(
        "mettail".into(),
        RhoValue::String(
            if language3 {
                "language/3"
            } else {
                "language/2"
            }
            .into(),
        ),
    );
    Ok(RhoValue::Map(output))
}

fn apply_replacement_decisions(
    base: &mut RhoValue,
    extension: &mut RhoValue,
    replacements: &[ReplacementDecision],
    path: &str,
) -> Result<(), ValueDecodeError> {
    for decision in replacements {
        let base_has = contains_named(base, "terms", &decision.label, term_label)?;
        let extension_has = contains_named(extension, "terms", &decision.label, term_label)?;
        if !(base_has && extension_has) {
            continue;
        }
        match (&decision.rename, decision.keep_left) {
            (None, true) => remove_named(extension, "terms", &decision.label, term_label)?,
            (None, false) => remove_named(base, "terms", &decision.label, term_label)?,
            (Some(rename), true) => rename_label_in_spec(extension, &decision.label, rename)?,
            (Some(rename), false) => rename_label_in_spec(base, &decision.label, rename)?,
        }
    }
    let _ = path;
    Ok(())
}

type NameFn = fn(&RhoValue, &str) -> Result<String, ValueDecodeError>;

fn contains_named(
    value: &RhoValue,
    key: &str,
    name: &str,
    name_of: NameFn,
) -> Result<bool, ValueDecodeError> {
    let RhoValue::Map(values) = value else {
        return Ok(false);
    };
    let Some(RhoValue::List(items)) = values.get(key) else {
        return Ok(false);
    };
    for (index, item) in items.iter().enumerate() {
        if name_of(item, &format!("$.{key}[{index}]"))? == name {
            return Ok(true);
        }
    }
    Ok(false)
}

fn remove_named(
    value: &mut RhoValue,
    key: &str,
    name: &str,
    name_of: NameFn,
) -> Result<(), ValueDecodeError> {
    let RhoValue::Map(values) = value else {
        return Ok(());
    };
    let Some(RhoValue::List(items)) = values.get_mut(key) else {
        return Ok(());
    };
    let mut retained = Vec::with_capacity(items.len());
    for (index, item) in std::mem::take(items).into_iter().enumerate() {
        if name_of(&item, &format!("$.{key}[{index}]"))? != name {
            retained.push(item);
        }
    }
    *items = retained;
    Ok(())
}

fn rename_label_in_spec(
    value: &mut RhoValue,
    from: &str,
    to: &str,
) -> Result<(), ValueDecodeError> {
    identifier(to, "$.replacements.rename")?;
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            RhoValue::Map(values) => {
                if values.get("label") == Some(&RhoValue::String(from.into())) {
                    values.insert("label".into(), RhoValue::String(to.into()));
                }
                work.extend(values.values_mut());
            },
            RhoValue::List(values) => {
                if values.first() == Some(&RhoValue::String(from.into())) {
                    values[0] = RhoValue::String(to.into());
                }
                work.extend(values.iter_mut());
            },
            _ => {},
        }
    }
    Ok(())
}

fn merge_option_maps(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = match base.get(key) {
        Some(value) => expect_map(value, &format!("{path}.{key}"))?.clone(),
        None => BTreeMap::new(),
    };
    if let Some(value) = extension.get(key) {
        merged.extend(expect_map(value, &format!("{path}.{key}"))?.clone());
    }
    if !merged.is_empty() {
        output.insert(key.into(), RhoValue::Map(merged));
    }
    Ok(())
}

fn merge_named_field(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    key: &str,
    name_of: NameFn,
    policy: DuplicatePolicy,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let base_items = optional_list_field(base, key, path)?;
    let extension_items = optional_list_field(extension, key, path)?;
    let mut merged = base_items.to_vec();
    for (index, item) in extension_items.iter().enumerate() {
        let name = name_of(item, &format!("{path}.{key}[{index}]"))?;
        let existing = merged
            .iter()
            .enumerate()
            .find_map(|(existing_index, existing)| {
                name_of(existing, &format!("{path}.{key}[{existing_index}]"))
                    .ok()
                    .filter(|existing_name| existing_name == &name)
                    .map(|_| existing_index)
            });
        match (existing, policy) {
            (None, _) => merged.push(item.clone()),
            (Some(existing), DuplicatePolicy::Override) => {
                merged.remove(existing);
                merged.push(item.clone());
            },
            (Some(existing), DuplicatePolicy::Error) if merged[existing] == *item => {},
            (Some(_), DuplicatePolicy::Error) if matches!(key, "tokens" | "literals") => {},
            (Some(_), DuplicatePolicy::Error) => {
                return error(
                    format!("{path}.{key}"),
                    format!("duplicate {key} name `{name}` in additive composition"),
                )
            },
        }
    }
    if !merged.is_empty() {
        output.insert(key.into(), RhoValue::List(merged));
    }
    Ok(())
}

fn merge_modes(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    policy: DuplicatePolicy,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = optional_list_field(base, "modes", path)?.to_vec();
    for (index, mode) in optional_list_field(extension, "modes", path)?
        .iter()
        .enumerate()
    {
        let name = record_name(mode, &format!("{path}.modes[{index}]"))?;
        if let Some(existing_index) = merged.iter().position(|existing| {
            record_name(existing, &format!("{path}.modes"))
                .ok()
                .as_deref()
                == Some(name.as_str())
        }) {
            let existing = expect_map(&merged[existing_index], &format!("{path}.modes"))?;
            let incoming = expect_map(mode, &format!("{path}.modes[{index}]"))?;
            let mut combined = existing.clone();
            let raw = existing
                .get("raw")
                .map(|value| expect_bool(value, &format!("{path}.modes.raw")))
                .transpose()?
                .unwrap_or(false)
                || incoming
                    .get("raw")
                    .map(|value| expect_bool(value, &format!("{path}.modes.raw")))
                    .transpose()?
                    .unwrap_or(false);
            let mut token_holder = BTreeMap::new();
            merge_named_field(
                &mut token_holder,
                existing,
                incoming,
                "tokens",
                record_name,
                policy,
                &format!("{path}.modes[{name}]"),
            )?;
            combined.extend(incoming.clone());
            if let Some(tokens) = token_holder.remove("tokens") {
                combined.insert("tokens".into(), tokens);
            }
            if raw {
                combined.insert("raw".into(), RhoValue::Boolean(true));
            } else {
                combined.remove("raw");
            }
            merged[existing_index] = RhoValue::Map(combined);
        } else {
            merged.push(mode.clone());
        }
    }
    if !merged.is_empty() {
        output.insert("modes".into(), RhoValue::List(merged));
    }
    Ok(())
}

fn replace_if_extension_nonempty(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    key: &str,
) {
    let value = match extension.get(key) {
        Some(RhoValue::List(values)) if !values.is_empty() => extension.get(key),
        _ => base.get(key),
    };
    if let Some(value) = value {
        output.insert(key.into(), value.clone());
    }
}

fn merge_guards(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let (Some(base), Some(extension)) = (base.get("guards"), extension.get("guards")) else {
        if let Some(value) = extension.get("guards").or_else(|| base.get("guards")) {
            output.insert("guards".into(), value.clone());
        }
        return Ok(());
    };
    let base = expect_map(base, &format!("{path}.guards"))?;
    let extension = expect_map(extension, &format!("{path}.guards"))?;
    let mut merged = BTreeMap::new();
    merge_guard_predicates(&mut merged, base, extension, path)?;
    merge_guard_theories(&mut merged, base, extension, path)?;
    for key in ["connectives", "channels"] {
        if let Some(value) = extension.get(key).or_else(|| base.get(key)) {
            merged.insert(key.into(), value.clone());
        }
    }
    output.insert("guards".into(), RhoValue::Map(merged));
    Ok(())
}

fn merge_oslf(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let (base_oslf, extension_oslf) = (base.get("oslf"), extension.get("oslf"));
    let Some(base_or_extension) = extension_oslf.or(base_oslf) else {
        return Ok(());
    };
    let Some(base_oslf) = base_oslf else {
        output.insert("oslf".into(), base_or_extension.clone());
        return Ok(());
    };
    let Some(extension_oslf) = extension_oslf else {
        output.insert("oslf".into(), base_or_extension.clone());
        return Ok(());
    };
    let base_oslf = expect_map(base_oslf, &format!("{path}.oslf"))?;
    let extension_oslf = expect_map(extension_oslf, &format!("{path}.oslf"))?;
    let mut merged = BTreeMap::new();
    merge_named_field(
        &mut merged,
        base_oslf,
        extension_oslf,
        "actions",
        record_id,
        DuplicatePolicy::Error,
        &format!("{path}.oslf"),
    )?;
    for key in ["judgments", "observations", "morphisms", "effects"] {
        merge_named_field(
            &mut merged,
            base_oslf,
            extension_oslf,
            key,
            record_name,
            DuplicatePolicy::Error,
            &format!("{path}.oslf"),
        )?;
    }
    merge_named_field(
        &mut merged,
        base_oslf,
        extension_oslf,
        "checkers",
        checker_abi,
        DuplicatePolicy::Error,
        &format!("{path}.oslf"),
    )?;
    for key in ["interactive", "continued", "cost", "resource_projection"] {
        merge_equal_oslf_singleton(&mut merged, base_oslf, extension_oslf, key, path)?;
    }
    merge_theory_limits(&mut merged, base_oslf, extension_oslf, path)?;
    output.insert("oslf".into(), RhoValue::Map(merged));
    Ok(())
}

fn merge_equal_oslf_singleton(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<(), ValueDecodeError> {
    match (base.get(key), extension.get(key)) {
        (Some(left), Some(right)) if left != right => error(
            format!("{path}.oslf.{key}"),
            format!(
                "conflicting `{key}` witnesses require an explicit checked theory morphism or forgetting operation"
            ),
        ),
        (Some(value), _) | (_, Some(value)) => {
            output.insert(key.into(), value.clone());
            Ok(())
        },
        (None, None) => Ok(()),
    }
}

fn merge_theory_limits(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    if base.get("limits").is_none() && extension.get("limits").is_none() {
        return Ok(());
    }
    let defaults = core::TheoryLimitsV1::default();
    let left = base
        .get("limits")
        .map(|value| decode_theory_limits(value, &format!("{path}.oslf.limits")))
        .transpose()?
        .unwrap_or(defaults);
    let right = extension
        .get("limits")
        .map(|value| decode_theory_limits(value, &format!("{path}.oslf.limits")))
        .transpose()?
        .unwrap_or(defaults);
    output.insert(
        "limits".into(),
        RhoValue::Map(BTreeMap::from([
            (
                "max_term_nodes".into(),
                RhoValue::Integer(left.max_term_nodes.min(right.max_term_nodes).into()),
            ),
            (
                "max_proof_nodes".into(),
                RhoValue::Integer(left.max_proof_nodes.min(right.max_proof_nodes).into()),
            ),
            (
                "max_frontier".into(),
                RhoValue::Integer(left.max_frontier.min(right.max_frontier).into()),
            ),
            (
                "max_steps".into(),
                RhoValue::Integer(left.max_steps.min(right.max_steps).into()),
            ),
            (
                "max_grade_bits".into(),
                RhoValue::Integer(left.max_grade_bits.min(right.max_grade_bits).into()),
            ),
        ])),
    );
    Ok(())
}

fn record_id(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    required_nonempty_string(values, "id", path)
}

fn checker_abi(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    required_nonempty_string(values, "abi", path)
}

fn merge_guard_predicates(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = optional_list_field(base, "predicates", path)?.to_vec();
    for predicate in optional_list_field(extension, "predicates", path)? {
        let name = record_name(predicate, &format!("{path}.guards.predicates"))?;
        if let Some(index) = merged.iter().position(|value| {
            record_name(value, &format!("{path}.guards.predicates"))
                .ok()
                .as_deref()
                == Some(name.as_str())
        }) {
            let base_predicate = expect_map(&merged[index], &format!("{path}.guards.predicates"))?;
            let extension_predicate = expect_map(predicate, &format!("{path}.guards.predicates"))?;
            let base_arity = expect_list(required(base_predicate, "params", path)?, path)?.len();
            let extension_arity =
                expect_list(required(extension_predicate, "params", path)?, path)?.len();
            if base_arity != extension_arity {
                return error(
                    format!("{path}.guards.predicates"),
                    format!("predicate `{name}` has conflicting arities"),
                );
            }
            let mut combined = base_predicate.clone();
            combined.extend(extension_predicate.clone());
            let mut annotations = base_predicate
                .get("annotations")
                .map(|value| expect_map(value, path).cloned())
                .transpose()?
                .unwrap_or_default();
            if let Some(value) = extension_predicate.get("annotations") {
                annotations.extend(expect_map(value, path)?.clone());
            }
            if !annotations.is_empty() {
                combined.insert("annotations".into(), RhoValue::Map(annotations));
            }
            merged[index] = RhoValue::Map(combined);
        } else {
            merged.push(predicate.clone());
        }
    }
    if !merged.is_empty() {
        output.insert("predicates".into(), RhoValue::List(merged));
    }
    Ok(())
}

fn merge_guard_theories(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = optional_list_field(base, "theories", path)?.to_vec();
    for theory in optional_list_field(extension, "theories", path)? {
        let name = record_name(theory, &format!("{path}.guards.theories"))?;
        if let Some(existing) = merged.iter().find(|value| {
            record_name(value, &format!("{path}.guards.theories"))
                .ok()
                .as_deref()
                == Some(name.as_str())
        }) {
            let left = expect_map(existing, path)?;
            let right = expect_map(theory, path)?;
            if left.get("theory") != right.get("theory") {
                return error(
                    format!("{path}.guards.theories"),
                    format!("guard theory `{name}` has conflicting implementations"),
                );
            }
        } else {
            merged.push(theory.clone());
        }
    }
    if !merged.is_empty() {
        output.insert("theories".into(), RhoValue::List(merged));
    }
    Ok(())
}

fn merge_relations(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = optional_list_field(base, "relations", path)?.to_vec();
    for relation in optional_list_field(extension, "relations", path)? {
        let name = relation_name(relation, &format!("{path}.relations"))?;
        if let Some(index) = merged.iter().position(|value| {
            relation_name(value, &format!("{path}.relations"))
                .ok()
                .as_deref()
                == Some(name.as_str())
        }) {
            let left = expect_map(&merged[index], path)?;
            let right = expect_map(relation, path)?;
            if left.get("params") != right.get("params") {
                return error(
                    format!("{path}.relations"),
                    format!("relation `{name}` has conflicting parameters"),
                );
            }
            let mut combined = left.clone();
            let mut rules = left
                .get("rules")
                .map(|value| expect_list(value, path).map(<[_]>::to_vec))
                .transpose()?
                .unwrap_or_default();
            if let Some(value) = right.get("rules") {
                rules.extend_from_slice(expect_list(value, path)?);
            }
            combined.extend(right.clone());
            if !rules.is_empty() {
                combined.insert("rules".into(), RhoValue::List(rules));
            }
            merged[index] = RhoValue::Map(combined);
        } else {
            merged.push(relation.clone());
        }
    }
    if !merged.is_empty() {
        output.insert("relations".into(), RhoValue::List(merged));
    }
    Ok(())
}

fn append_unique_field(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut merged = optional_list_field(base, key, path)?.to_vec();
    for item in optional_list_field(extension, key, path)? {
        if !merged.contains(item) {
            merged.push(item.clone());
        }
    }
    if !merged.is_empty() {
        output.insert(key.into(), RhoValue::List(merged));
    }
    Ok(())
}

fn merge_requested_rights(
    output: &mut BTreeMap<String, RhoValue>,
    base: &BTreeMap<String, RhoValue>,
    extension: &BTreeMap<String, RhoValue>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut rights = decode_requested_rights(base.get("rights"), &format!("{path}.rights"))?;
    let extension_rights =
        decode_requested_rights(extension.get("rights"), &format!("{path}.rights"))?;
    rights = core::LanguageRights::from_rights(rights.iter().chain(extension_rights.iter()));
    output.insert(
        "rights".into(),
        RhoValue::List(
            rights
                .iter()
                .map(|right| RhoValue::String(right.name().into()))
                .collect(),
        ),
    );
    Ok(())
}

fn optional_list_field<'a>(
    values: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<&'a [RhoValue], ValueDecodeError> {
    values
        .get(key)
        .map(|value| expect_list(value, &format!("{path}.{key}")))
        .transpose()
        .map(Option::unwrap_or_default)
}

fn type_name(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    match value {
        RhoValue::String(name) => Ok(name.clone()),
        RhoValue::Map(values) => Ok(expect_string(
            required(values, "name", path)?,
            &format!("{path}.name"),
        )?
        .to_string()),
        _ => error(path, "expected type declaration"),
    }
}

fn record_name(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    Ok(expect_string(required(values, "name", path)?, &format!("{path}.name"))?.to_string())
}

fn term_label(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    Ok(expect_string(required(values, "label", path)?, &format!("{path}.label"))?.to_string())
}

fn relation_name(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    Ok(
        expect_string(required(values, "relation", path)?, &format!("{path}.relation"))?
            .to_string(),
    )
}

fn literal_name(value: &RhoValue, path: &str) -> Result<String, ValueDecodeError> {
    let values = expect_map(value, path)?;
    Ok(format!(
        "{}\u{0}{}",
        expect_string(required(values, "category", path)?, &format!("{path}.category"))?,
        expect_string(required(values, "pattern", path)?, &format!("{path}.pattern"))?
    ))
}

fn decode_options(value: &RhoValue, path: &str) -> Result<Options, ValueDecodeError> {
    const KEYS: &[&str] = &[
        "beam_width",
        "log_semiring_model_path",
        "dispatch",
        "emit_tests",
        "emit_blockly",
        "emit_simulator",
        "parse_only",
        "case_insensitive",
        "unicode_normalization",
        "reserved_keywords",
        "contextual_keywords",
        "recovery",
    ];
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, KEYS, path)?;
    let beam_width = values
        .get("beam_width")
        .map(|value| match value {
            RhoValue::FloatBits(bits) if f64::from_bits(*bits).is_finite() => {
                Ok(core::BeamWidth::Explicit(f64::from_bits(*bits)))
            },
            RhoValue::String(value) if value == "none" || value == "disabled" => {
                Ok(core::BeamWidth::Disabled)
            },
            RhoValue::String(value) if value == "auto" => Ok(core::BeamWidth::Auto),
            _ => error(
                format!("{path}.beam_width"),
                "expected a finite float or `none`, `disabled`, or `auto`",
            ),
        })
        .transpose()?;
    let log_semiring_model_path = values
        .get("log_semiring_model_path")
        .map(|value| expect_string(value, &format!("{path}.log_semiring_model_path")))
        .transpose()?
        .map(str::to_string);
    if let Some(value) = values.get("dispatch") {
        expect_enum_string(value, &["static", "weighted", "auto"], &format!("{path}.dispatch"))?;
    }
    for key in ["emit_tests", "emit_blockly", "emit_simulator", "parse_only", "case_insensitive"] {
        if let Some(value) = values.get(key) {
            expect_bool(value, &format!("{path}.{key}"))?;
        }
    }
    if let Some(value) = values.get("unicode_normalization") {
        expect_enum_string(
            value,
            &["NFC", "NFD", "NFKC", "NFKD", "none"],
            &format!("{path}.unicode_normalization"),
        )?;
    }
    let contextual = values
        .get("contextual_keywords")
        .map(|value| decode_string_set(value, &format!("{path}.contextual_keywords")))
        .transpose()?
        .unwrap_or_default();
    let reserved_keywords = values
        .get("reserved_keywords")
        .map(|value| {
            Ok(
                match expect_enum_string(
                    value,
                    &["auto", "none"],
                    &format!("{path}.reserved_keywords"),
                )? {
                    "auto" => core::KeywordReservation::Auto { contextual: contextual.clone() },
                    _ if contextual.is_empty() => core::KeywordReservation::None,
                    _ => {
                        return error(
                            format!("{path}.contextual_keywords"),
                            "contextual keyword exceptions require `reserved_keywords: auto`",
                        );
                    },
                },
            )
        })
        .transpose()?;
    if reserved_keywords.is_none() && !contextual.is_empty() {
        return error(
            format!("{path}.contextual_keywords"),
            "contextual keyword exceptions require `reserved_keywords: auto`",
        );
    }
    let recovery = values
        .get("recovery")
        .map(|value| decode_recovery(value, &format!("{path}.recovery")))
        .transpose()?;
    Ok(Options {
        beam_width,
        log_semiring_model_path,
        reserved_keywords,
        recovery,
    })
}

fn decode_string_set(value: &RhoValue, path: &str) -> Result<BTreeSet<String>, ValueDecodeError> {
    let mut output = BTreeSet::new();
    for (index, value) in expect_list(value, path)?.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let value = expect_nonempty_string(value, &item_path)?.to_string();
        if !output.insert(value.clone()) {
            return error(item_path, format!("duplicate string `{value}`"));
        }
    }
    Ok(output)
}

fn decode_recovery(
    value: &RhoValue,
    path: &str,
) -> Result<core::RecoveryConfiguration, ValueDecodeError> {
    const KEYS: &[&str] = &[
        "skip_per_token",
        "delete_cost",
        "substitute_cost",
        "insert_cost",
        "swap_cost",
        "max_skip_lookahead",
        "deep_nesting_threshold",
        "deep_nesting_skip_mult",
        "shallow_depth_threshold",
        "shallow_depth_skip_mult",
        "low_bp_threshold",
        "low_bp_skip_mult",
        "collection_insert_mult",
        "group_insert_mult",
        "bracket_insert_mult",
        "mixfix_substitute_mult",
        "simulation_valid_mult",
        "simulation_fail_penalty",
        "beam_width",
        "cascade_window",
        "vpa_nesting_ceiling",
        "adaptive_weight_threshold",
        "deterministic_skip_discount",
        "ambiguous_insert_discount",
        "max_recovery_depth",
    ];
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, KEYS, path)?;
    let mut output = core::RecoveryConfiguration::default();
    macro_rules! nonnegative_float {
        ($field:ident) => {
            if let Some(value) = values.get(stringify!($field)) {
                output.$field =
                    expect_nonnegative_f64(value, &format!("{path}.{}", stringify!($field)))?;
            }
        };
    }
    macro_rules! unsigned32 {
        ($field:ident) => {
            if let Some(value) = values.get(stringify!($field)) {
                output.$field = expect_u32(value, &format!("{path}.{}", stringify!($field)))?;
            }
        };
    }
    nonnegative_float!(skip_per_token);
    nonnegative_float!(delete_cost);
    nonnegative_float!(substitute_cost);
    nonnegative_float!(insert_cost);
    nonnegative_float!(swap_cost);
    unsigned32!(max_skip_lookahead);
    unsigned32!(deep_nesting_threshold);
    nonnegative_float!(deep_nesting_skip_mult);
    unsigned32!(shallow_depth_threshold);
    nonnegative_float!(shallow_depth_skip_mult);
    if let Some(value) = values.get("low_bp_threshold") {
        output.low_bp_threshold = expect_u8(value, &format!("{path}.low_bp_threshold"))?;
    }
    nonnegative_float!(low_bp_skip_mult);
    nonnegative_float!(collection_insert_mult);
    nonnegative_float!(group_insert_mult);
    nonnegative_float!(bracket_insert_mult);
    nonnegative_float!(mixfix_substitute_mult);
    nonnegative_float!(simulation_valid_mult);
    nonnegative_float!(simulation_fail_penalty);
    if let Some(value) = values.get("beam_width") {
        output.beam_width = match value {
            RhoValue::String(value) if value == "none" || value == "disabled" => None,
            _ => Some(expect_nonnegative_f64(value, &format!("{path}.beam_width"))?),
        };
    }
    unsigned32!(cascade_window);
    if let Some(value) = values.get("vpa_nesting_ceiling") {
        output.vpa_nesting_ceiling = match value {
            RhoValue::String(value) if value == "none" || value == "disabled" => None,
            _ => Some(expect_u32(value, &format!("{path}.vpa_nesting_ceiling"))?),
        };
    }
    nonnegative_float!(adaptive_weight_threshold);
    nonnegative_float!(deterministic_skip_discount);
    nonnegative_float!(ambiguous_insert_discount);
    if let Some(value) = values.get("max_recovery_depth") {
        output.max_recovery_depth = expect_u8(value, &format!("{path}.max_recovery_depth"))?;
    }
    Ok(output)
}

fn decode_requested_rights(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<core::LanguageRights, ValueDecodeError> {
    let Some(value) = value else {
        return Ok(core::LanguageRights::native_flt_default());
    };
    let mut rights = BTreeSet::new();
    for (index, value) in expect_list(value, path)?.iter().enumerate() {
        let item_path = format!("{path}[{index}]");
        let name = expect_string(value, &item_path)?;
        let right = core::LanguageRight::from_name(name).ok_or_else(|| {
            ValueDecodeError::new(
                &item_path,
                format!(
                    "unknown language right `{name}`; expected Parse, Construct, Match, Observe, ReflectAst, Reduce, Bridge, Publish, Introspect, Check, SearchProof, or Spend"
                ),
            )
        })?;
        if !rights.insert(right) {
            return error(item_path, format!("duplicate language right `{name}`"));
        }
    }
    Ok(core::LanguageRights::from_rights(rights))
}

fn decode_oslf(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<core::TheoryCoreV1, ValueDecodeError> {
    let mut theory = core::TheoryCoreV1::structural();
    theory.profile = core::TheoryProfileV1::Oslf;
    let Some(value) = value else {
        return Ok(theory);
    };
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "actions",
            "judgments",
            "observations",
            "morphisms",
            "effects",
            "interactive",
            "continued",
            "cost",
            "resource_projection",
            "checkers",
            "limits",
        ],
        path,
    )?;
    theory.effects =
        decode_sequence(values.get("effects"), &format!("{path}.effects"), decode_effect)?;
    theory.actions =
        decode_sequence(values.get("actions"), &format!("{path}.actions"), decode_action)?;
    for (index, value) in values
        .get("judgments")
        .map(|value| expect_list(value, &format!("{path}.judgments")))
        .transpose()?
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        theory
            .judgments
            .push(decode_judgment(value, &format!("{path}.judgments[{index}]"))?);
    }
    theory.observations = decode_sequence(
        values.get("observations"),
        &format!("{path}.observations"),
        decode_observation,
    )?;
    theory.morphisms =
        decode_sequence(values.get("morphisms"), &format!("{path}.morphisms"), decode_morphism)?;
    theory.interactive = values
        .get("interactive")
        .map(|value| decode_interactive(value, &format!("{path}.interactive")))
        .transpose()?;
    theory.continued = values
        .get("continued")
        .map(|value| decode_continued(value, &format!("{path}.continued")))
        .transpose()?;
    theory.cost = values
        .get("cost")
        .map(|value| decode_cost(value, &format!("{path}.cost")))
        .transpose()?;
    theory.resource_projection = values
        .get("resource_projection")
        .map(|value| decode_resource_projection(value, &format!("{path}.resource_projection")))
        .transpose()?;
    theory.checker_requirements = decode_sequence(
        values.get("checkers"),
        &format!("{path}.checkers"),
        decode_checker_requirement,
    )?;
    if let Some(value) = values.get("limits") {
        theory.limits = decode_theory_limits(value, &format!("{path}.limits"))?;
    }
    Ok(theory)
}

fn decode_effect(value: &RhoValue, path: &str) -> Result<core::EffectDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "class", "requires", "emits"], path)?;
    Ok(core::EffectDeclV1 {
        name: required_nonempty_string(values, "name", path)?,
        class: values
            .get("class")
            .map(|value| decode_effect_class(value, &format!("{path}.class")))
            .transpose()?
            .unwrap_or(core::SemanticEffectClassV1::Pure),
        requires: decode_nonempty_string_list(values.get("requires"), &format!("{path}.requires"))?,
        emits: decode_nonempty_string_list(values.get("emits"), &format!("{path}.emits"))?,
    })
}

fn decode_action(value: &RhoValue, path: &str) -> Result<core::SemanticActionV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "id",
            "domain",
            "codomain",
            "transition",
            "effect",
            "effect_class",
            "required_rights",
            "grade",
            "execution",
        ],
        path,
    )?;
    Ok(core::SemanticActionV1 {
        id: required_nonempty_string(values, "id", path)?,
        domain: decode_required_string_list(values, "domain", path)?,
        codomain: required_nonempty_string(values, "codomain", path)?,
        transition: decode_theory_rule_reference(
            required(values, "transition", path)?,
            &format!("{path}.transition"),
        )?,
        effect: required_nonempty_string(values, "effect", path)?,
        effect_class: values
            .get("effect_class")
            .map(|value| decode_effect_class(value, &format!("{path}.effect_class")))
            .transpose()?
            .unwrap_or(core::SemanticEffectClassV1::Pure),
        required_rights: decode_action_rights(
            values.get("required_rights"),
            &format!("{path}.required_rights"),
        )?,
        grade: required_nonempty_string(values, "grade", path)?,
        execution: decode_action_execution(
            required(values, "execution", path)?,
            &format!("{path}.execution"),
        )?,
    })
}

fn decode_action_execution(
    value: &RhoValue,
    path: &str,
) -> Result<core::SemanticActionExecutionV1, ValueDecodeError> {
    if let RhoValue::String(tag) = value {
        return match tag.as_str() {
            "one_step" => Ok(core::SemanticActionExecutionV1::OneStep),
            _ => error(path, format!("unknown action execution policy `{tag}`")),
        };
    }
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &["kind", "relation_sort", "terminal_constructors", "branching"],
        path,
    )?;
    let kind = expect_enum_string(
        required(values, "kind", path)?,
        &["normalize"],
        &format!("{path}.kind"),
    )?;
    debug_assert_eq!(kind, "normalize");
    let branching = match expect_enum_string(
        required(values, "branching", path)?,
        &["deterministic", "fair_all_normal_forms"],
        &format!("{path}.branching"),
    )? {
        "deterministic" => core::SemanticNormalizationBranchingV1::Deterministic,
        _ => core::SemanticNormalizationBranchingV1::FairAllNormalForms,
    };
    Ok(core::SemanticActionExecutionV1::Normalize {
        relation_sort: required_nonempty_string(values, "relation_sort", path)?,
        terminal_constructors: decode_required_string_list(values, "terminal_constructors", path)?,
        branching,
    })
}

fn decode_effect_class(
    value: &RhoValue,
    path: &str,
) -> Result<core::SemanticEffectClassV1, ValueDecodeError> {
    Ok(
        match expect_enum_string(
            value,
            &["pure", "structural", "behavioral", "resource", "external"],
            path,
        )? {
            "pure" => core::SemanticEffectClassV1::Pure,
            "structural" => core::SemanticEffectClassV1::Structural,
            "behavioral" => core::SemanticEffectClassV1::Behavioral,
            "resource" => core::SemanticEffectClassV1::Resource,
            _ => core::SemanticEffectClassV1::External,
        },
    )
}

fn decode_action_rights(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<core::LanguageRights, ValueDecodeError> {
    let mut rights = Vec::new();
    let mut seen = BTreeSet::new();
    for (index, value) in value
        .map(|value| expect_list(value, path))
        .transpose()?
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        let name = expect_nonempty_string(value, &format!("{path}[{index}]"))?;
        let right = core::LanguageRight::from_name(name).ok_or_else(|| {
            ValueDecodeError::new(format!("{path}[{index}]"), format!("unknown right `{name}`"))
        })?;
        if !seen.insert(right) {
            return error(format!("{path}[{index}]"), format!("duplicate right `{name}`"));
        }
        rights.push(right);
    }
    Ok(core::LanguageRights::from_rights(rights))
}

fn decode_theory_rule_reference(
    value: &RhoValue,
    path: &str,
) -> Result<core::TheoryRuleReferenceV1, ValueDecodeError> {
    let values = expect_list(value, path)?;
    require_len(values, 2, path)?;
    let name = expect_nonempty_string(&values[1], &format!("{path}[1]"))?.to_string();
    match expect_string(&values[0], &format!("{path}[0]"))? {
        "rewrite" => Ok(core::TheoryRuleReferenceV1::Rewrite(name)),
        "equation" => Ok(core::TheoryRuleReferenceV1::Equation(name)),
        "handler" => Ok(core::TheoryRuleReferenceV1::Handler(name)),
        tag => error(format!("{path}[0]"), format!("unknown rule reference `{tag}`")),
    }
}

fn decode_judgment(value: &RhoValue, path: &str) -> Result<core::JudgmentDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "arguments", "decision", "rules"], path)?;
    let decision = match expect_enum_string(
        required(values, "decision", path)?,
        &["exact", "bounded"],
        &format!("{path}.decision"),
    )? {
        "exact" => core::JudgmentDecisionV1::Exact,
        _ => core::JudgmentDecisionV1::Bounded,
    };
    let mut rules = Vec::new();
    for (index, value) in expect_list(required(values, "rules", path)?, &format!("{path}.rules"))?
        .iter()
        .enumerate()
    {
        rules.push(decode_judgment_rule(value, &format!("{path}.rules[{index}]"))?);
    }
    Ok(core::JudgmentDeclV1 {
        name: required_nonempty_string(values, "name", path)?,
        arguments: decode_required_string_list(values, "arguments", path)?,
        decision,
        rules,
    })
}

fn decode_judgment_rule(
    value: &RhoValue,
    path: &str,
) -> Result<core::JudgmentRuleV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "premises", "conclusion"], path)?;
    let mut variables = Vec::new();
    let mut variable_ids = BTreeMap::new();
    let mut terms = Vec::new();
    let mut premises = Vec::new();
    for (index, value) in
        expect_list(required(values, "premises", path)?, &format!("{path}.premises"))?
            .iter()
            .enumerate()
    {
        premises.push(decode_judgment_atom(
            value,
            &format!("{path}.premises[{index}]"),
            &mut variables,
            &mut variable_ids,
            &mut terms,
        )?);
    }
    let conclusion = decode_judgment_atom(
        required(values, "conclusion", path)?,
        &format!("{path}.conclusion"),
        &mut variables,
        &mut variable_ids,
        &mut terms,
    )?;
    Ok(core::JudgmentRuleV1 {
        name: required_nonempty_string(values, "name", path)?,
        variables,
        terms,
        premises,
        conclusion,
    })
}

fn decode_judgment_atom(
    value: &RhoValue,
    path: &str,
    variables: &mut Vec<core::TheoryVariableV1>,
    variable_ids: &mut BTreeMap<String, core::TheoryVariableId>,
    terms: &mut Vec<core::TheoryTermNodeV1>,
) -> Result<core::JudgmentAtomV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["judgment", "terms"], path)?;
    let mut roots = Vec::new();
    for (index, value) in expect_list(required(values, "terms", path)?, &format!("{path}.terms"))?
        .iter()
        .enumerate()
    {
        roots.push(decode_theory_term(
            value,
            &format!("{path}.terms[{index}]"),
            variables,
            variable_ids,
            terms,
        )?);
    }
    Ok(core::JudgmentAtomV1 {
        judgment: required_nonempty_string(values, "judgment", path)?,
        terms: roots,
    })
}

fn decode_theory_term(
    value: &RhoValue,
    path: &str,
    variables: &mut Vec<core::TheoryVariableV1>,
    variable_ids: &mut BTreeMap<String, core::TheoryVariableId>,
    arena: &mut Vec<core::TheoryTermNodeV1>,
) -> Result<core::TheoryTermId, ValueDecodeError> {
    enum Task<'a> {
        Visit(&'a RhoValue, String),
        FinishConstructor { name: String, arity: usize },
    }
    let mut tasks = vec![Task::Visit(value, path.to_string())];
    let mut values = Vec::<core::TheoryTermId>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(value, path) => {
                let tagged = expect_list(value, &path)?;
                let tag = tagged_head(tagged, &path)?;
                match tag {
                    "var" => {
                        require_len(tagged, 2, &path)?;
                        let name =
                            expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?.to_string();
                        let variable = if let Some(variable) = variable_ids.get(&name) {
                            *variable
                        } else {
                            let variable = core::TheoryVariableId(variables.len() as u32);
                            variable_ids.insert(name.clone(), variable);
                            variables.push(core::TheoryVariableV1 {
                                id: variable,
                                name,
                                sort: String::new(),
                                role: core::TheoryVariableRoleV1::Input,
                            });
                            variable
                        };
                        let id = core::TheoryTermId(arena.len() as u32);
                        arena.push(core::TheoryTermNodeV1 {
                            sort: String::new(),
                            form: core::TheoryTermFormV1::Variable(variable),
                        });
                        values.push(id);
                    },
                    "literal" => {
                        require_len(tagged, 2, &path)?;
                        let literal = match &tagged[1] {
                            RhoValue::String(value) => core::TheoryLiteralV1::String(value.clone()),
                            RhoValue::Bytes(value) => core::TheoryLiteralV1::Bytes(value.clone()),
                            RhoValue::Integer(value) => core::TheoryLiteralV1::Integer(*value),
                            RhoValue::FloatBits(value) => core::TheoryLiteralV1::FloatBits(*value),
                            RhoValue::Boolean(value) => core::TheoryLiteralV1::Boolean(*value),
                            RhoValue::Nil => core::TheoryLiteralV1::Unit,
                            _ => {
                                return error(format!("{path}[1]"), "theory literal must be scalar")
                            },
                        };
                        let id = core::TheoryTermId(arena.len() as u32);
                        arena.push(core::TheoryTermNodeV1 {
                            sort: String::new(),
                            form: core::TheoryTermFormV1::Literal(literal),
                        });
                        values.push(id);
                    },
                    "ctor" => {
                        require_len(tagged, 3, &path)?;
                        let name =
                            expect_nonempty_string(&tagged[1], &format!("{path}[1]"))?.to_string();
                        let children = expect_list(&tagged[2], &format!("{path}[2]"))?;
                        tasks.push(Task::FinishConstructor { name, arity: children.len() });
                        for (index, child) in children.iter().enumerate().rev() {
                            tasks.push(Task::Visit(child, format!("{path}[2][{index}]")));
                        }
                    },
                    _ => return error(&path, format!("unknown theory term tag `{tag}`")),
                }
            },
            Task::FinishConstructor { name, arity } => {
                let start = values
                    .len()
                    .checked_sub(arity)
                    .expect("constructor children are scheduled before their parent");
                let arguments = values.drain(start..).collect();
                let id = core::TheoryTermId(arena.len() as u32);
                arena.push(core::TheoryTermNodeV1 {
                    sort: String::new(),
                    form: core::TheoryTermFormV1::Constructor { constructor: name, arguments },
                });
                values.push(id);
            },
        }
    }
    if values.len() != 1 {
        return error(path, "theory term decoder did not produce exactly one root");
    }
    Ok(values[0])
}

fn decode_observation(
    value: &RhoValue,
    path: &str,
) -> Result<core::ObservationDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "action", "result"], path)?;
    Ok(core::ObservationDeclV1 {
        name: required_nonempty_string(values, "name", path)?,
        action: required_nonempty_string(values, "action", path)?,
        result: required_nonempty_string(values, "result", path)?,
    })
}

fn decode_morphism(
    value: &RhoValue,
    path: &str,
) -> Result<core::TheoryMorphismV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &["name", "source", "target", "categories", "constructors", "actions", "grades"],
        path,
    )?;
    Ok(core::TheoryMorphismV1 {
        name: required_nonempty_string(values, "name", path)?,
        source: required_nonempty_string(values, "source", path)?,
        target: required_nonempty_string(values, "target", path)?,
        categories: decode_string_pairs(values.get("categories"), &format!("{path}.categories"))?,
        constructors: decode_string_pairs(
            values.get("constructors"),
            &format!("{path}.constructors"),
        )?,
        actions: decode_string_pairs(values.get("actions"), &format!("{path}.actions"))?,
        grades: decode_string_pairs(values.get("grades"), &format!("{path}.grades"))?,
    })
}

fn decode_interactive(
    value: &RhoValue,
    path: &str,
) -> Result<core::InteractiveDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["cut", "channel_sort", "datum_sort", "continuation_sort"], path)?;
    Ok(core::InteractiveDeclV1 {
        cut: required_nonempty_string(values, "cut", path)?,
        channel_sort: required_nonempty_string(values, "channel_sort", path)?,
        datum_sort: required_nonempty_string(values, "datum_sort", path)?,
        continuation_sort: required_nonempty_string(values, "continuation_sort", path)?,
    })
}

fn decode_continued(
    value: &RhoValue,
    path: &str,
) -> Result<core::ContinuedDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "k",
            "kp",
            "ke",
            "k_prime",
            "near",
            "compute",
            "section",
            "wrappability",
            "quote_faithfulness",
        ],
        path,
    )?;
    Ok(core::ContinuedDeclV1 {
        k: required_nonempty_string(values, "k", path)?,
        kp: required_nonempty_string(values, "kp", path)?,
        ke: required_nonempty_string(values, "ke", path)?,
        k_prime: required_nonempty_string(values, "k_prime", path)?,
        near: required_nonempty_string(values, "near", path)?,
        compute: required_nonempty_string(values, "compute", path)?,
        section: required_nonempty_string(values, "section", path)?,
        wrappability: required_nonempty_string(values, "wrappability", path)?,
        quote_faithfulness: required_nonempty_string(values, "quote_faithfulness", path)?,
    })
}

fn decode_cost(value: &RhoValue, path: &str) -> Result<core::CostDeclV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "base",
            "signature_sort",
            "stack_sort",
            "wrapped_sort",
            "located_sort",
            "product",
            "unit",
            "rules",
            "eta",
            "mu",
            "map",
            "laws",
        ],
        path,
    )?;
    Ok(core::CostDeclV1 {
        base: required_nonempty_string(values, "base", path)?,
        signature_sort: required_nonempty_string(values, "signature_sort", path)?,
        stack_sort: required_nonempty_string(values, "stack_sort", path)?,
        wrapped_sort: required_nonempty_string(values, "wrapped_sort", path)?,
        located_sort: required_nonempty_string(values, "located_sort", path)?,
        product: required_nonempty_string(values, "product", path)?,
        unit: required_nonempty_string(values, "unit", path)?,
        rules: decode_required_string_list(values, "rules", path)?,
        eta: required_nonempty_string(values, "eta", path)?,
        mu: required_nonempty_string(values, "mu", path)?,
        map: required_nonempty_string(values, "map", path)?,
        laws: decode_required_string_list(values, "laws", path)?,
    })
}

fn decode_resource_projection(
    value: &RhoValue,
    path: &str,
) -> Result<core::ResourceProjectionV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["abi", "grade_sort", "demand_sort", "project", "proof"], path)?;
    Ok(core::ResourceProjectionV1 {
        abi: required_nonempty_string(values, "abi", path)?,
        grade_sort: required_nonempty_string(values, "grade_sort", path)?,
        demand_sort: required_nonempty_string(values, "demand_sort", path)?,
        project: required_nonempty_string(values, "project", path)?,
        proof: required_nonempty_string(values, "proof", path)?,
    })
}

fn decode_checker_requirement(
    value: &RhoValue,
    path: &str,
) -> Result<core::CheckerRequirementV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["abi", "limit_profile"], path)?;
    Ok(core::CheckerRequirementV1 {
        abi: required_nonempty_string(values, "abi", path)?,
        limit_profile: required_nonempty_string(values, "limit_profile", path)?,
    })
}

fn decode_theory_limits(
    value: &RhoValue,
    path: &str,
) -> Result<core::TheoryLimitsV1, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "max_rule_variables",
            "max_term_nodes",
            "max_premise_nodes",
            "max_proof_nodes",
            "max_frontier",
            "max_steps",
            "max_grade_bits",
            "max_output_nodes",
            "max_output_bytes",
        ],
        path,
    )?;
    let defaults = core::TheoryLimitsV1::default();
    Ok(core::TheoryLimitsV1 {
        max_rule_variables: optional_u32(values, "max_rule_variables", path)?
            .unwrap_or(defaults.max_rule_variables),
        max_term_nodes: optional_u32(values, "max_term_nodes", path)?
            .unwrap_or(defaults.max_term_nodes),
        max_premise_nodes: optional_u32(values, "max_premise_nodes", path)?
            .unwrap_or(defaults.max_premise_nodes),
        max_proof_nodes: optional_u32(values, "max_proof_nodes", path)?
            .unwrap_or(defaults.max_proof_nodes),
        max_frontier: optional_u32(values, "max_frontier", path)?.unwrap_or(defaults.max_frontier),
        max_steps: optional_u32(values, "max_steps", path)?.unwrap_or(defaults.max_steps),
        max_grade_bits: optional_u32(values, "max_grade_bits", path)?
            .unwrap_or(defaults.max_grade_bits),
        max_output_nodes: optional_u32(values, "max_output_nodes", path)?
            .unwrap_or(defaults.max_output_nodes),
        max_output_bytes: optional_u32(values, "max_output_bytes", path)?
            .unwrap_or(defaults.max_output_bytes),
    })
}

fn required_nonempty_string(
    values: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<String, ValueDecodeError> {
    Ok(expect_nonempty_string(required(values, key, path)?, &format!("{path}.{key}"))?.to_string())
}

fn decode_required_string_list(
    values: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<Vec<String>, ValueDecodeError> {
    decode_nonempty_string_list(Some(required(values, key, path)?), &format!("{path}.{key}"))
}

fn decode_nonempty_string_list(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<Vec<String>, ValueDecodeError> {
    let mut output = Vec::new();
    for (index, value) in value
        .map(|value| expect_list(value, path))
        .transpose()?
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        output.push(expect_nonempty_string(value, &format!("{path}[{index}]"))?.to_string());
    }
    Ok(output)
}

fn decode_string_pairs(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<Vec<(String, String)>, ValueDecodeError> {
    let mut output = Vec::new();
    for (index, value) in value
        .map(|value| expect_list(value, path))
        .transpose()?
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        let item_path = format!("{path}[{index}]");
        let pair = expect_list(value, &item_path)?;
        require_len(pair, 2, &item_path)?;
        output.push((
            expect_nonempty_string(&pair[0], &format!("{item_path}[0]"))?.to_string(),
            expect_nonempty_string(&pair[1], &format!("{item_path}[1]"))?.to_string(),
        ));
    }
    Ok(output)
}

fn optional_u32(
    values: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<Option<u32>, ValueDecodeError> {
    values
        .get(key)
        .map(|value| expect_u32(value, &format!("{path}.{key}")))
        .transpose()
}

fn decode_semantics(value: &RhoValue, path: &str) -> Result<Vec<String>, ValueDecodeError> {
    let target = match value {
        RhoValue::String(value) => vec![value.clone()],
        RhoValue::List(values) => {
            require_tagged_len(values, "path", 2, path)?;
            expect_list(&values[1], &format!("{path}[1]"))?
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    identifier(
                        expect_string(value, &format!("{path}[1][{index}]"))?,
                        &format!("{path}[1][{index}]"),
                    )
                })
                .collect::<Result<Vec<_>, _>>()?
        },
        _ => return error(path, "expected a semantics name or [\"path\", [...]]"),
    };
    if target.is_empty() {
        return error(path, "semantics path must not be empty");
    }
    Ok(target)
}

fn decode_type(value: &RhoValue, path: &str) -> Result<TypeDecl, ValueDecodeError> {
    if let RhoValue::String(name) = value {
        return Ok(TypeDecl {
            name: identifier(name, path)?,
            carrier: core::Carrier::Dynamic,
            collection: None,
            refinement: None,
            admits_variables: true,
        });
    }
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &["name", "carrier", "collection", "refine", "admits_variables"],
        path,
    )?;
    let name = identifier(
        expect_string(required(values, "name", path)?, &format!("{path}.name"))?,
        &format!("{path}.name"),
    )?;
    let carrier = values
        .get("carrier")
        .map(|value| decode_carrier(value, &format!("{path}.carrier")))
        .transpose()?
        .unwrap_or(core::Carrier::Dynamic);
    let collection = values
        .get("collection")
        .map(|value| decode_collection(value, &format!("{path}.collection")))
        .transpose()?;
    if matches!(carrier, core::Carrier::Collection(_)) != collection.is_some() {
        return error(path, "collection carriers and `collection` metadata must occur together");
    }
    let refinement = values
        .get("refine")
        .map(|value| decode_refinement(value, &format!("{path}.refine")))
        .transpose()?;
    let admits_variables = values
        .get("admits_variables")
        .map(|value| expect_bool(value, &format!("{path}.admits_variables")))
        .transpose()?
        .unwrap_or(true);
    Ok(TypeDecl {
        name,
        carrier,
        collection,
        refinement,
        admits_variables,
    })
}

pub(crate) fn decode_carrier(
    value: &RhoValue,
    path: &str,
) -> Result<core::Carrier, ValueDecodeError> {
    if let RhoValue::String(name) = value {
        return Ok(match name.as_str() {
            "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64"
            | "u128" | "usize" | "BigInt" => core::Carrier::Builtin(core::BuiltinCarrier::Integer),
            "BigRat" => core::Carrier::Builtin(core::BuiltinCarrier::Rational),
            "Fixed" => core::Carrier::Builtin(core::BuiltinCarrier::FixedPoint),
            "f32" | "f64" => core::Carrier::Builtin(core::BuiltinCarrier::Float),
            "bool" => core::Carrier::Builtin(core::BuiltinCarrier::Boolean),
            "str" | "String" => core::Carrier::Builtin(core::BuiltinCarrier::String),
            _ => return error(path, format!("unknown carrier `{name}`")),
        });
    }
    let values = expect_list(value, path)?;
    let tag = tagged_head(values, path)?;
    match tag {
        "vec" | "bag" | "set" => {
            require_len(values, 2, path)?;
            Ok(core::Carrier::Collection(core::CollectionCarrier {
                kind: collection_kind(tag, &format!("{path}[0]"))?,
                key: identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?,
                value: None,
            }))
        },
        "map" | "pathmap" => {
            require_len(values, 3, path)?;
            Ok(core::Carrier::Collection(core::CollectionCarrier {
                kind: collection_kind(tag, &format!("{path}[0]"))?,
                key: identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?,
                value: Some(identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?),
            }))
        },
        "extern" => {
            require_len(values, 2, path)?;
            Ok(core::Carrier::Extern {
                urn: expect_nonempty_string(&values[1], &format!("{path}[1]"))?.to_string(),
            })
        },
        _ => error(path, format!("unknown carrier tag `{tag}`")),
    }
}

fn decode_collection(value: &RhoValue, path: &str) -> Result<CollectionDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["kind", "open", "close", "sep", "key_val_sep"], path)?;
    let kind = collection_kind(
        expect_string(required(values, "kind", path)?, &format!("{path}.kind"))?,
        &format!("{path}.kind"),
    )?;
    Ok(CollectionDecl {
        kind,
        open: optional_string(values, "open", path)?,
        close: optional_string(values, "close", path)?,
        separator: optional_string(values, "sep", path)?,
        key_value_separator: optional_string(values, "key_val_sep", path)?,
    })
}

fn decode_refinement(value: &RhoValue, path: &str) -> Result<RefinementDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["var", "base", "pred"], path)?;
    let variable = identifier(
        expect_string(required(values, "var", path)?, &format!("{path}.var"))?,
        &format!("{path}.var"),
    )?;
    let base = identifier(
        expect_string(required(values, "base", path)?, &format!("{path}.base"))?,
        &format!("{path}.base"),
    )?;
    let predicate = required(values, "pred", path)?.clone();
    validate_refinement_predicate(&predicate, &format!("{path}.pred"))?;
    Ok(RefinementDecl { variable, base, predicate })
}

fn decode_literal(value: &RhoValue, path: &str) -> Result<LiteralDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["category", "pattern", "eval"], path)?;
    let category = identifier(
        expect_string(required(values, "category", path)?, &format!("{path}.category"))?,
        &format!("{path}.category"),
    )?;
    Ok(LiteralDecl {
        category,
        pattern: expect_nonempty_string(
            required(values, "pattern", path)?,
            &format!("{path}.pattern"),
        )?
        .to_string(),
        evaluation: decode_native_evaluation(
            required(values, "eval", path)?,
            &format!("{path}.eval"),
        )?,
    })
}

pub(crate) fn validate_fragment(value: &RhoValue) -> Result<LanguageSchema, ValueDecodeError> {
    let fragment = expect_map(value, "Data")?;
    if let Some(key) = fragment
        .keys()
        .find(|key| matches!(key.as_str(), "mettail" | "name"))
    {
        return error(
            format!("Data.{key}"),
            "whole-language identity keys are not permitted in Data(v)",
        );
    }
    let mut complete = fragment.clone();
    complete.insert(
        "mettail".into(),
        RhoValue::String(
            if fragment.contains_key("oslf") {
                "language/3"
            } else {
                "language/2"
            }
            .into(),
        ),
    );
    complete.insert("name".into(), RhoValue::String("DataFragment".into()));
    decode(&RhoValue::Map(complete))
}

impl LanguageSchema {
    pub(crate) fn category_names(&self) -> impl Iterator<Item = &str> {
        self.types
            .iter()
            .map(|declaration| declaration.name.as_str())
    }

    pub(crate) fn term_labels(&self) -> impl Iterator<Item = &str> {
        self.terms
            .iter()
            .map(|declaration| declaration.label.as_str())
    }
}

fn decode_token(value: &RhoValue, path: &str) -> Result<TokenDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &["name", "pattern", "category", "eval", "priority", "push", "pop", "stream"],
        path,
    )?;
    let priority = values
        .get("priority")
        .map(|value| expect_i16(value, &format!("{path}.priority")))
        .transpose()?
        .unwrap_or(0);
    Ok(TokenDecl {
        name: identifier(
            expect_string(required(values, "name", path)?, &format!("{path}.name"))?,
            &format!("{path}.name"),
        )?,
        pattern: expect_nonempty_string(
            required(values, "pattern", path)?,
            &format!("{path}.pattern"),
        )?
        .to_string(),
        category: optional_identifier(values, "category", path)?,
        evaluation: values
            .get("eval")
            .map(|value| decode_native_evaluation(value, &format!("{path}.eval")))
            .transpose()?,
        priority,
        push: optional_identifier(values, "push", path)?,
        pop: values
            .get("pop")
            .map(|value| expect_bool(value, &format!("{path}.pop")))
            .transpose()?
            .unwrap_or(false),
        stream: optional_identifier(values, "stream", path)?,
    })
}

fn decode_mode(value: &RhoValue, path: &str) -> Result<ModeDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "raw", "tokens"], path)?;
    Ok(ModeDecl {
        name: identifier(
            expect_string(required(values, "name", path)?, &format!("{path}.name"))?,
            &format!("{path}.name"),
        )?,
        raw: values
            .get("raw")
            .map(|value| expect_bool(value, &format!("{path}.raw")))
            .transpose()?
            .unwrap_or(false),
        tokens: decode_sequence(
            Some(required(values, "tokens", path)?),
            &format!("{path}.tokens"),
            decode_token,
        )?,
    })
}

fn decode_native_evaluation(
    value: &RhoValue,
    path: &str,
) -> Result<core::NativeEvaluation, ValueDecodeError> {
    let values = expect_list(value, path)?;
    let tag = tagged_head(values, path)?;
    match tag {
        "op" => {
            require_len(values, 2, path)?;
            let name = expect_string(&values[1], &format!("{path}[1]"))?;
            const NAMES: &[&str] = &[
                "add", "sub", "mul", "div", "mod", "neg", "eq", "ne", "lt", "gt", "le", "ge",
                "and", "or", "xor", "not", "concat", "len",
            ];
            if !NAMES.contains(&name) {
                return error(format!("{path}[1]"), format!("unknown operator `{name}`"));
            }
            Ok(core::NativeEvaluation::Operator(name.to_string()))
        },
        "carrier" => {
            require_len(values, 3, path)?;
            let kind = expect_enum_string(
                &values[1],
                &["int", "rat", "fixed", "float", "bool", "str"],
                &format!("{path}[1]"),
            )?;
            let parameters = expect_map(&values[2], &format!("{path}[2]"))?;
            reject_unknown_keys(
                parameters,
                &["suffix", "require_suffix", "exclude_suffix", "allow_overflow_of"],
                &format!("{path}[2]"),
            )?;
            for (key, value) in parameters {
                expect_string(value, &format!("{path}[2].{key}"))?;
            }
            Ok(core::NativeEvaluation::Carrier {
                kind: kind.to_string(),
                parameters: parameters
                    .iter()
                    .map(|(key, value)| (key.clone(), to_core_value(value)))
                    .collect(),
            })
        },
        "handler" => {
            require_len(values, 2, path)?;
            Ok(core::NativeEvaluation::Handler(
                expect_nonempty_string(&values[1], &format!("{path}[1]"))?.to_string(),
            ))
        },
        "src" => {
            require_len(values, 3, path)?;
            let semantics = decode_semantics(&values[1], &format!("{path}[1]"))?;
            let text = expect_nonempty_string(&values[2], &format!("{path}[2]"))?.to_string();
            Ok(core::NativeEvaluation::Source { semantics, text })
        },
        _ => error(path, format!("unknown NativeEval tag `{tag}`")),
    }
}

fn decode_synchronization(
    value: &RhoValue,
    path: &str,
) -> Result<core::SyncConstraint, ValueDecodeError> {
    let values = expect_list(value, path)?;
    match tagged_head(values, path)? {
        "align" => {
            require_len(values, 4, path)?;
            Ok(core::SyncConstraint::Align {
                stream_a: identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?,
                stream_b: identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?,
                boundary_pattern: expect_nonempty_string(&values[3], &format!("{path}[3]"))?
                    .to_string(),
            })
        },
        "track" => {
            require_len(values, 3, path)?;
            Ok(core::SyncConstraint::Track {
                auxiliary: identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?,
                primary: identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?,
            })
        },
        tag => error(path, format!("unknown synchronization tag `{tag}`")),
    }
}

fn decode_tree_invariant(value: &RhoValue, path: &str) -> Result<NamedValue, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "constraint", "doc"], path)?;
    if let Some(doc) = values.get("doc") {
        expect_string(doc, &format!("{path}.doc"))?;
    }
    let constraint = required(values, "constraint", path)?.clone();
    validate_tree_constraint(&constraint, &format!("{path}.constraint"))?;
    Ok(NamedValue {
        name: identifier(
            expect_string(required(values, "name", path)?, &format!("{path}.name"))?,
            &format!("{path}.name"),
        )?,
        value: constraint,
    })
}

fn decode_guards(value: &RhoValue, path: &str) -> Result<GuardSchema, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["predicates", "connectives", "theories", "channels"], path)?;
    let mut selectivity = BTreeMap::new();
    let mut costs = BTreeMap::new();
    if let Some(predicates) = values.get("predicates") {
        for (index, predicate) in expect_list(predicates, &format!("{path}.predicates"))?
            .iter()
            .enumerate()
        {
            let predicate_path = format!("{path}.predicates[{index}]");
            let predicate = expect_map(predicate, &predicate_path)?;
            reject_unknown_keys(
                predicate,
                &["name", "params", "forms", "annotations", "doc"],
                &predicate_path,
            )?;
            let name = identifier(
                expect_string(
                    required(predicate, "name", &predicate_path)?,
                    &format!("{predicate_path}.name"),
                )?,
                &format!("{predicate_path}.name"),
            )?;
            for (param_index, param) in expect_list(
                required(predicate, "params", &predicate_path)?,
                &format!("{predicate_path}.params"),
            )?
            .iter()
            .enumerate()
            {
                let decoded =
                    decode_param(param, &format!("{predicate_path}.params[{param_index}]"))?;
                if !matches!(decoded, Param::Plain { .. }) {
                    return error(
                        format!("{predicate_path}.params[{param_index}]"),
                        "built-in predicate params must use the `param` tag",
                    );
                }
            }
            for (form_index, form) in expect_list(
                required(predicate, "forms", &predicate_path)?,
                &format!("{predicate_path}.forms"),
            )?
            .iter()
            .enumerate()
            {
                for (item_index, item) in
                    expect_list(form, &format!("{predicate_path}.forms[{form_index}]"))?
                        .iter()
                        .enumerate()
                {
                    decode_syntax_node(
                        item,
                        &format!("{predicate_path}.forms[{form_index}][{item_index}]"),
                    )?;
                }
            }
            if let Some(annotations) = predicate.get("annotations") {
                let annotations =
                    expect_map(annotations, &format!("{predicate_path}.annotations"))?;
                for (key, value) in annotations {
                    validate_scalar(value, &format!("{predicate_path}.annotations.{key}"))?;
                    match (key.as_str(), value) {
                        ("selectivity", RhoValue::FloatBits(bits)) => {
                            let value = f64::from_bits(*bits);
                            if !value.is_finite() || !(0.0..=1.0).contains(&value) {
                                return error(
                                    format!("{predicate_path}.annotations.selectivity"),
                                    "selectivity must be a finite float in [0,1]",
                                );
                            }
                            selectivity.insert(name.clone(), value);
                        },
                        ("cost", RhoValue::Integer(value)) => {
                            let value = u32::try_from(*value).map_err(|_| {
                                ValueDecodeError::new(
                                    format!("{predicate_path}.annotations.cost"),
                                    "cost must be a nonnegative u32",
                                )
                            })?;
                            costs.insert(name.clone(), value);
                        },
                        ("selectivity", _) => {
                            return error(
                                format!("{predicate_path}.annotations.selectivity"),
                                "selectivity requires a float",
                            )
                        },
                        ("cost", _) => {
                            return error(
                                format!("{predicate_path}.annotations.cost"),
                                "cost requires an integer",
                            )
                        },
                        _ => {},
                    }
                }
            }
            if let Some(doc) = predicate.get("doc") {
                expect_string(doc, &format!("{predicate_path}.doc"))?;
            }
        }
    }
    if let Some(connectives) = values.get("connectives") {
        for (index, connective) in expect_list(connectives, &format!("{path}.connectives"))?
            .iter()
            .enumerate()
        {
            let connective_path = format!("{path}.connectives[{index}]");
            let connective = expect_map(connective, &connective_path)?;
            reject_unknown_keys(connective, &["role", "keywords"], &connective_path)?;
            expect_nonempty_string(
                required(connective, "role", &connective_path)?,
                &format!("{connective_path}.role"),
            )?;
            for (keyword_index, keyword) in expect_list(
                required(connective, "keywords", &connective_path)?,
                &format!("{connective_path}.keywords"),
            )?
            .iter()
            .enumerate()
            {
                expect_nonempty_string(
                    keyword,
                    &format!("{connective_path}.keywords[{keyword_index}]"),
                )?;
            }
        }
    }
    let theories = values
        .get("theories")
        .map(|theories| {
            expect_list(theories, &format!("{path}.theories"))?
                .iter()
                .enumerate()
                .map(|(index, theory)| {
                    let theory_path = format!("{path}.theories[{index}]");
                    let theory = expect_map(theory, &theory_path)?;
                    reject_unknown_keys(theory, &["name", "theory", "for"], &theory_path)?;
                    Ok(core::GuardTheory {
                        name: identifier(
                            expect_string(
                                required(theory, "name", &theory_path)?,
                                &format!("{theory_path}.name"),
                            )?,
                            &format!("{theory_path}.name"),
                        )?,
                        implementation: expect_nonempty_string(
                            required(theory, "theory", &theory_path)?,
                            &format!("{theory_path}.theory"),
                        )?
                        .to_string(),
                        handled_categories: theory
                            .get("for")
                            .map(|value| decode_ident_list(value, &format!("{theory_path}.for")))
                            .transpose()?,
                    })
                })
                .collect()
        })
        .transpose()?
        .unwrap_or_default();
    let mut channel_categories = None;
    let mut join_patterns = Vec::new();
    if let Some(channels) = values.get("channels") {
        let channels_path = format!("{path}.channels");
        let channels = expect_map(channels, &channels_path)?;
        reject_unknown_keys(channels, &["channel", "join"], &channels_path)?;
        channel_categories = channels
            .get("channel")
            .map(|value| decode_ident_list(value, &format!("{channels_path}.channel")))
            .transpose()?;
        if let Some(joins) = channels.get("join") {
            for (index, join) in expect_list(joins, &format!("{channels_path}.join"))?
                .iter()
                .enumerate()
            {
                let join_path = format!("{channels_path}.join[{index}]");
                let join = expect_map(join, &join_path)?;
                reject_unknown_keys(join, &["label", "params"], &join_path)?;
                let mut categories = Vec::new();
                for (param_index, parameter) in expect_list(
                    required(join, "params", &join_path)?,
                    &format!("{join_path}.params"),
                )?
                .iter()
                .enumerate()
                {
                    let parameter_path = format!("{join_path}.params[{param_index}]");
                    let pair = expect_list(parameter, &parameter_path)?;
                    require_len(pair, 2, &parameter_path)?;
                    identifier(
                        expect_string(&pair[0], &format!("{parameter_path}[0]"))?,
                        &format!("{parameter_path}[0]"),
                    )?;
                    categories.push(identifier(
                        expect_string(&pair[1], &format!("{parameter_path}[1]"))?,
                        &format!("{parameter_path}[1]"),
                    )?);
                }
                join_patterns.push(core::JoinPattern {
                    label: identifier(
                        expect_string(
                            required(join, "label", &join_path)?,
                            &format!("{join_path}.label"),
                        )?,
                        &format!("{join_path}.label"),
                    )?,
                    channel_categories: categories,
                });
            }
        }
    }
    Ok(GuardSchema {
        value: value.clone(),
        theories,
        channel_categories,
        join_patterns,
        selectivity,
        costs,
        has_connectives: values.contains_key("connectives"),
        has_predicates: values.contains_key("predicates"),
    })
}

fn decode_term(value: &RhoValue, path: &str) -> Result<TermDecl, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(
        values,
        &[
            "label",
            "category",
            "context",
            "syntax",
            "items",
            "eval",
            "mode",
            "assoc",
            "prefix_bp",
            "shares_previous_level",
            "tier",
            "doc",
        ],
        path,
    )?;
    let has_syntax = values.contains_key("syntax");
    let has_items = values.contains_key("items");
    if has_syntax == has_items {
        return error(path, "exactly one of `syntax` and `items` is required");
    }
    if let Some(doc) = values.get("doc") {
        expect_string(doc, &format!("{path}.doc"))?;
    }
    let context = values
        .get("context")
        .map(|value| {
            expect_list(value, &format!("{path}.context"))?
                .iter()
                .enumerate()
                .map(|(index, value)| decode_param(value, &format!("{path}.context[{index}]")))
                .collect()
        })
        .transpose()?
        .unwrap_or_default();
    let body = if let Some(syntax) = values.get("syntax") {
        TermBody::Judgement(
            expect_list(syntax, &format!("{path}.syntax"))?
                .iter()
                .enumerate()
                .map(|(index, value)| decode_syntax_node(value, &format!("{path}.syntax[{index}]")))
                .collect::<Result<Vec<_>, _>>()?,
        )
    } else {
        let items = required(values, "items", path)?;
        TermBody::Bnf(
            expect_list(items, &format!("{path}.items"))?
                .iter()
                .enumerate()
                .map(|(index, value)| decode_bnf_node(value, &format!("{path}.items[{index}]")))
                .collect::<Result<Vec<_>, _>>()?,
        )
    };
    let evaluation = values
        .get("eval")
        .map(|value| decode_native_evaluation(value, &format!("{path}.eval")))
        .transpose()?;
    let mode = values
        .get("mode")
        .map(|value| {
            Ok(match expect_enum_string(value, &["fold", "step"], &format!("{path}.mode"))? {
                "fold" => core::EvaluationMode::Fold,
                _ => core::EvaluationMode::Step,
            })
        })
        .transpose()?;
    if evaluation.is_none() && mode.is_some() {
        return error(format!("{path}.mode"), "evaluation mode requires an `eval` action");
    }
    let associativity = values
        .get("assoc")
        .map(|value| {
            Ok(match expect_enum_string(value, &["left", "right"], &format!("{path}.assoc"))? {
                "right" => core::Associativity::Right,
                _ => core::Associativity::Left,
            })
        })
        .transpose()?
        .unwrap_or(core::Associativity::Left);
    let prefix_binding_power = values
        .get("prefix_bp")
        .map(|value| expect_u16(value, &format!("{path}.prefix_bp")))
        .transpose()?;
    let shares_previous_level = values
        .get("shares_previous_level")
        .map(|value| expect_bool(value, &format!("{path}.shares_previous_level")))
        .transpose()?
        .unwrap_or(false);
    let tier = values
        .get("tier")
        .map(|value| decode_tier(value, &format!("{path}.tier")))
        .transpose()?;
    Ok(TermDecl {
        label: identifier(
            expect_string(required(values, "label", path)?, &format!("{path}.label"))?,
            &format!("{path}.label"),
        )?,
        category: identifier(
            expect_string(required(values, "category", path)?, &format!("{path}.category"))?,
            &format!("{path}.category"),
        )?,
        context,
        body,
        evaluation,
        mode,
        associativity,
        prefix_binding_power,
        shares_previous_level,
        tier,
    })
}

fn decode_tier(value: &RhoValue, path: &str) -> Result<core::TierDirective, ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["tier", "bound", "force"], path)?;
    let tier = match expect_enum_string(
        required(values, "tier", path)?,
        &["t1", "t2", "t3", "t4"],
        &format!("{path}.tier"),
    )? {
        "t1" => core::EvaluationTier::T1,
        "t2" => core::EvaluationTier::T2,
        "t3" => core::EvaluationTier::T3,
        _ => core::EvaluationTier::T4,
    };
    Ok(core::TierDirective {
        tier,
        bound: values
            .get("bound")
            .map(|value| expect_u32(value, &format!("{path}.bound")))
            .transpose()?,
        force: values
            .get("force")
            .map(|value| expect_bool(value, &format!("{path}.force")))
            .transpose()?
            .unwrap_or(false),
    })
}

fn decode_param(value: &RhoValue, path: &str) -> Result<Param, ValueDecodeError> {
    enum Task<'a> {
        Visit { value: &'a RhoValue, path: String },
        FinishOptional(usize),
    }

    let mut tasks = vec![Task::Visit { value, path: path.into() }];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { value, path } => {
                let values = expect_list(value, &path)?;
                match tagged_head(values, &path)? {
                    "param" => {
                        if !matches!(values.len(), 3 | 4) {
                            return error(
                                &path,
                                format!("param expects 3 or 4 items, found {}", values.len()),
                            );
                        }
                        if values.len() == 4 {
                            expect_enum_string(
                                &values[3],
                                &["forall", "exists"],
                                &format!("{path}[3]"),
                            )?;
                        }
                        output.push(Param::Plain {
                            name: identifier(
                                expect_string(&values[1], &format!("{path}[1]"))?,
                                &format!("{path}[1]"),
                            )?,
                            ty: decode_type_expr(&values[2], &format!("{path}[2]"))?,
                        });
                    },
                    tag @ ("binder" | "binders") => {
                        require_len(values, 4, &path)?;
                        output.push(Param::Binder {
                            binder: identifier(
                                expect_string(&values[1], &format!("{path}[1]"))?,
                                &format!("{path}[1]"),
                            )?,
                            body: identifier(
                                expect_string(&values[2], &format!("{path}[2]"))?,
                                &format!("{path}[2]"),
                            )?,
                            ty: decode_type_expr(&values[3], &format!("{path}[3]"))?,
                            multiple: tag == "binders",
                        });
                    },
                    "guard" => {
                        require_len(values, 2, &path)?;
                        output.push(Param::Guard(identifier(
                            expect_string(&values[1], &format!("{path}[1]"))?,
                            &format!("{path}[1]"),
                        )?));
                    },
                    "optional" => {
                        require_len(values, 2, &path)?;
                        let params = expect_list(&values[1], &format!("{path}[1]"))?;
                        tasks.push(Task::FinishOptional(params.len()));
                        for (index, param) in params.iter().enumerate().rev() {
                            tasks.push(Task::Visit {
                                value: param,
                                path: format!("{path}[1][{index}]"),
                            });
                        }
                    },
                    tag => return error(&path, format!("unknown parameter tag `{tag}`")),
                }
            },
            Task::FinishOptional(count) => {
                let start = output.len() - count;
                let params = output.drain(start..).collect();
                output.push(Param::Optional(params));
            },
        }
    }
    Ok(output.pop().expect("parameter decoder produces one value"))
}

fn decode_type_expr(value: &RhoValue, path: &str) -> Result<TypeExpr, ValueDecodeError> {
    enum Task<'a> {
        Visit { value: &'a RhoValue, path: String },
        FinishArrow,
        FinishMulti,
        FinishCollection { kind: core::CollectionKind, keyed: bool },
    }

    let mut tasks = vec![Task::Visit { value, path: path.into() }];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { value: RhoValue::String(name), path } => {
                output.push(TypeExpr::Base(identifier(name, &path)?));
            },
            Task::Visit { value, path } => {
                let values = expect_list(value, &path)?;
                let tag = tagged_head(values, &path)?;
                match tag {
                    "arrow" => {
                        require_len(values, 3, &path)?;
                        tasks.push(Task::FinishArrow);
                        tasks.push(Task::Visit {
                            value: &values[2],
                            path: format!("{path}[2]"),
                        });
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "multi" => {
                        require_len(values, 2, &path)?;
                        tasks.push(Task::FinishMulti);
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "vec" | "bag" | "set" => {
                        require_len(values, 2, &path)?;
                        tasks.push(Task::FinishCollection {
                            kind: collection_kind(tag, &format!("{path}[0]"))?,
                            keyed: false,
                        });
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "map" | "pathmap" => {
                        require_len(values, 3, &path)?;
                        tasks.push(Task::FinishCollection {
                            kind: collection_kind(tag, &format!("{path}[0]"))?,
                            keyed: true,
                        });
                        tasks.push(Task::Visit {
                            value: &values[2],
                            path: format!("{path}[2]"),
                        });
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    _ => return error(&path, format!("unknown type-expression tag `{tag}`")),
                }
            },
            Task::FinishArrow => {
                let right = output.pop().expect("arrow codomain is scheduled");
                let left = output.pop().expect("arrow domain is scheduled");
                output.push(TypeExpr::Arrow(Box::new(left), Box::new(right)));
            },
            Task::FinishMulti => {
                let element = output.pop().expect("multi element is scheduled");
                output.push(TypeExpr::Multi(Box::new(element)));
            },
            Task::FinishCollection { kind, keyed } => {
                let value = keyed.then(|| Box::new(output.pop().expect("map value is scheduled")));
                let key = output.pop().expect("collection element/key is scheduled");
                output.push(TypeExpr::Collection(kind, Box::new(key), value));
            },
        }
    }
    Ok(output
        .pop()
        .expect("type-expression decoder produces one value"))
}

fn decode_syntax_node(value: &RhoValue, path: &str) -> Result<SyntaxNode, ValueDecodeError> {
    enum Task<'a> {
        Visit { value: &'a RhoValue, path: String },
        FinishSeparated(String),
        FinishMap { bindings: Vec<String>, body_count: usize },
        FinishOptional(usize),
    }

    let mut tasks = vec![Task::Visit { value, path: path.into() }];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { value: RhoValue::String(name), path } => {
                output.push(SyntaxNode::Reference(identifier(name, &path)?));
            },
            Task::Visit { value, path } => {
                let values = expect_list(value, &path)?;
                match tagged_head(values, &path)? {
                    "lit" => {
                        require_len(values, 2, &path)?;
                        output.push(SyntaxNode::Literal(
                            expect_string(&values[1], &format!("{path}[1]"))?.to_string(),
                        ));
                    },
                    "sep" => {
                        require_len(values, 3, &path)?;
                        let separator =
                            expect_string(&values[2], &format!("{path}[2]"))?.to_string();
                        tasks.push(Task::FinishSeparated(separator));
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "zip" => {
                        require_len(values, 3, &path)?;
                        output.push(SyntaxNode::Zip(
                            identifier(
                                expect_string(&values[1], &format!("{path}[1]"))?,
                                &format!("{path}[1]"),
                            )?,
                            identifier(
                                expect_string(&values[2], &format!("{path}[2]"))?,
                                &format!("{path}[2]"),
                            )?,
                        ));
                    },
                    "map" => {
                        require_len(values, 4, &path)?;
                        let bindings = decode_ident_list(&values[2], &format!("{path}[2]"))?;
                        let body = expect_list(&values[3], &format!("{path}[3]"))?;
                        tasks.push(Task::FinishMap { bindings, body_count: body.len() });
                        for (index, node) in body.iter().enumerate().rev() {
                            tasks.push(Task::Visit {
                                value: node,
                                path: format!("{path}[3][{index}]"),
                            });
                        }
                        tasks.push(Task::Visit {
                            value: &values[1],
                            path: format!("{path}[1]"),
                        });
                    },
                    "opt" => {
                        require_len(values, 2, &path)?;
                        let body = expect_list(&values[1], &format!("{path}[1]"))?;
                        tasks.push(Task::FinishOptional(body.len()));
                        for (index, node) in body.iter().enumerate().rev() {
                            tasks.push(Task::Visit {
                                value: node,
                                path: format!("{path}[1][{index}]"),
                            });
                        }
                    },
                    "tok" => {
                        require_len(values, 3, &path)?;
                        output.push(SyntaxNode::Token {
                            name: identifier(
                                expect_string(&values[1], &format!("{path}[1]"))?,
                                &format!("{path}[1]"),
                            )?,
                            binding: match &values[2] {
                                RhoValue::Nil => None,
                                RhoValue::String(name) => {
                                    Some(identifier(name, &format!("{path}[2]"))?)
                                },
                                _ => {
                                    return error(
                                        format!("{path}[2]"),
                                        "expected a binding name or Nil",
                                    )
                                },
                            },
                        });
                    },
                    "flt" => {
                        require_len(values, 4, &path)?;
                        output.push(SyntaxNode::ForeignLanguage {
                            binding: identifier(
                                expect_string(&values[1], &format!("{path}[1]"))?,
                                &format!("{path}[1]"),
                            )?,
                            open: expect_string(&values[2], &format!("{path}[2]"))?.to_string(),
                            close: expect_string(&values[3], &format!("{path}[3]"))?.to_string(),
                        });
                    },
                    tag => return error(&path, format!("unknown syntax-item tag `{tag}`")),
                }
            },
            Task::FinishSeparated(separator) => {
                let source = output.pop().expect("separated source is scheduled");
                output.push(SyntaxNode::Separated(Box::new(source), separator));
            },
            Task::FinishMap { bindings, body_count } => {
                let body_start = output.len() - body_count;
                let body = output.drain(body_start..).collect();
                let source = output.pop().expect("mapped source is scheduled");
                output.push(SyntaxNode::Map { source: Box::new(source), bindings, body });
            },
            Task::FinishOptional(count) => {
                let start = output.len() - count;
                let body = output.drain(start..).collect();
                output.push(SyntaxNode::Optional(body));
            },
        }
    }
    Ok(output
        .pop()
        .expect("syntax-node decoder produces one value"))
}

fn decode_bnf_node(value: &RhoValue, path: &str) -> Result<BnfNode, ValueDecodeError> {
    let values = expect_list(value, path)?;
    match tagged_head(values, path)? {
        "lit" => {
            require_len(values, 2, path)?;
            Ok(BnfNode::Literal(expect_string(&values[1], &format!("{path}[1]"))?.to_string()))
        },
        "nt" => {
            require_len(values, 2, path)?;
            Ok(BnfNode::Nonterminal(identifier(
                expect_string(&values[1], &format!("{path}[1]"))?,
                &format!("{path}[1]"),
            )?))
        },
        "bind" => {
            require_len(values, 2, path)?;
            Ok(BnfNode::Binding(identifier(
                expect_string(&values[1], &format!("{path}[1]"))?,
                &format!("{path}[1]"),
            )?))
        },
        "coll" => {
            require_len(values, 6, path)?;
            Ok(BnfNode::Collection {
                kind: collection_kind(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?,
                element: identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?,
                separator: expect_string(&values[3], &format!("{path}[3]"))?.to_string(),
                open: expect_nil_or_string(&values[4], &format!("{path}[4]"))?,
                close: expect_nil_or_string(&values[5], &format!("{path}[5]"))?,
            })
        },
        tag => error(path, format!("unknown BNF-item tag `{tag}`")),
    }
}

fn validate_equation(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    validate_semantic_rule(value, path, false)
}

fn validate_rewrite(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    validate_semantic_rule(value, path, true)
}

fn validate_semantic_rule(
    value: &RhoValue,
    path: &str,
    rewrite: bool,
) -> Result<(), ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["name", "premises", "context", "left", "right"], path)?;
    identifier(
        expect_string(required(values, "name", path)?, &format!("{path}.name"))?,
        &format!("{path}.name"),
    )?;
    if let Some(context) = values.get("context") {
        for (index, entry) in expect_list(context, &format!("{path}.context"))?
            .iter()
            .enumerate()
        {
            let entry_path = format!("{path}.context[{index}]");
            let entry = expect_list(entry, &entry_path)?;
            require_tagged_len(entry, "typed", 3, &entry_path)?;
            identifier(
                expect_string(&entry[1], &format!("{entry_path}[1]"))?,
                &format!("{entry_path}[1]"),
            )?;
            decode_type_expr(&entry[2], &format!("{entry_path}[2]"))?;
        }
    }
    if let Some(premises) = values.get("premises") {
        for (index, premise) in expect_list(premises, &format!("{path}.premises"))?
            .iter()
            .enumerate()
        {
            validate_premise(premise, &format!("{path}.premises[{index}]"), rewrite)?;
        }
    }
    validate_pattern(required(values, "left", path)?, &format!("{path}.left"))?;
    validate_pattern(required(values, "right", path)?, &format!("{path}.right"))?;
    Ok(())
}

fn validate_pattern(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        if let RhoValue::String(name) = value {
            identifier(name, &path)?;
            continue;
        }
        let values = expect_list(value, &path)?;
        let tag = tagged_head(values, &path)?;
        match tag {
            "eval" => {
                if !matches!(values.len(), 3 | 4) {
                    return error(
                        &path,
                        format!("eval expects 3 or 4 items, found {}", values.len()),
                    );
                }
                if values.len() == 4 {
                    identifier(
                        expect_string(&values[2], &format!("{path}[2]"))?,
                        &format!("{path}[2]"),
                    )?;
                    work.push((&values[3], format!("{path}[3]")));
                } else {
                    work.push((&values[2], format!("{path}[2]")));
                }
                work.push((&values[1], format!("{path}[1]")));
            },
            "^" => {
                require_len(values, 3, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                work.push((&values[2], format!("{path}[2]")));
            },
            "^*" => {
                require_len(values, 3, &path)?;
                decode_ident_list(&values[1], &format!("{path}[1]"))?;
                work.push((&values[2], format!("{path}[2]")));
            },
            "coll" => {
                if !matches!(values.len(), 3 | 4) {
                    return error(
                        &path,
                        "coll expects elements, remainder, and an optional PathMap mode",
                    );
                }
                expect_nil_or_identifier(&values[2], &format!("{path}[2]"))?;
                if values.len() == 4 {
                    validate_pathmap_mode(&values[3], &format!("{path}[3]"))?;
                }
                let children = expect_list(&values[1], &format!("{path}[1]"))?;
                for (index, child) in children.iter().enumerate().rev() {
                    work.push((child, format!("{path}[1][{index}]")));
                }
            },
            "coll_typed" => {
                if !matches!(values.len(), 4 | 5) {
                    return error(
                        &path,
                        "coll_typed expects an element sort, elements, remainder, and an optional PathMap mode",
                    );
                }
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                expect_nil_or_identifier(&values[3], &format!("{path}[3]"))?;
                if values.len() == 5 {
                    validate_pathmap_mode(&values[4], &format!("{path}[4]"))?;
                }
                let children = expect_list(&values[2], &format!("{path}[2]"))?;
                for (index, child) in children.iter().enumerate().rev() {
                    work.push((child, format!("{path}[2][{index}]")));
                }
            },
            "pmap" => {
                require_len(values, 4, &path)?;
                decode_ident_list(&values[2], &format!("{path}[2]"))?;
                work.push((&values[3], format!("{path}[3]")));
                work.push((&values[1], format!("{path}[1]")));
            },
            "pzip" => {
                require_len(values, 3, &path)?;
                work.push((&values[2], format!("{path}[2]")));
                work.push((&values[1], format!("{path}[1]")));
            },
            "lit" => {
                require_len(values, 3, &path)?;
                decode_carrier(&values[1], &format!("{path}[1]"))?;
                validate_scalar(&values[2], &format!("{path}[2]"))?;
            },
            constructor => {
                identifier(constructor, &format!("{path}[0]"))?;
                for (index, argument) in values[1..].iter().enumerate().rev() {
                    work.push((argument, format!("{path}[{}]", index + 1)));
                }
            },
        }
    }
    Ok(())
}

fn validate_premise(value: &RhoValue, path: &str, rewrite: bool) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        let values = expect_list(value, &path)?;
        match tagged_head(values, &path)? {
            "fresh" | "fresh_rest" => {
                require_len(values, 3, &path)?;
                for index in 1..3 {
                    identifier(
                        expect_string(&values[index], &format!("{path}[{index}]"))?,
                        &format!("{path}[{index}]"),
                    )?;
                }
            },
            "~>" => {
                if !rewrite {
                    return error(&path, "rewrite premises are not admissible in equations");
                }
                require_len(values, 3, &path)?;
                for index in 1..3 {
                    identifier(
                        expect_string(&values[index], &format!("{path}[{index}]"))?,
                        &format!("{path}[{index}]"),
                    )?;
                }
            },
            "rel" => {
                require_len(values, 3, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                decode_ident_list(&values[2], &format!("{path}[2]"))?;
            },
            "forall" => {
                require_len(values, 4, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?;
                work.push((&values[3], format!("{path}[3]")));
            },
            "guard" => {
                require_len(values, 2, &path)?;
                validate_behavioral_predicate(&values[1], &format!("{path}[1]"))?;
            },
            tag => return error(&path, format!("unknown premise tag `{tag}`")),
        }
    }
    Ok(())
}

fn validate_refinement_predicate(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        let values = expect_list(value, &path)?;
        match tagged_head(values, &path)? {
            "linear" => {
                require_len(values, 4, &path)?;
                for (index, term) in expect_list(&values[1], &format!("{path}[1]"))?
                    .iter()
                    .enumerate()
                {
                    let term_path = format!("{path}[1][{index}]");
                    let pair = expect_list(term, &term_path)?;
                    require_len(pair, 2, &term_path)?;
                    identifier(
                        expect_string(&pair[0], &format!("{term_path}[0]"))?,
                        &format!("{term_path}[0]"),
                    )?;
                    expect_integer(&pair[1], &format!("{term_path}[1]"))?;
                }
                expect_relation(&values[2], &format!("{path}[2]"))?;
                expect_integer(&values[3], &format!("{path}[3]"))?;
            },
            "call" | "ncall" => {
                require_len(values, 3, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                validate_predicate_args(&values[2], &format!("{path}[2]"))?;
            },
            "quant" => {
                require_len(values, 6, &path)?;
                expect_enum_string(&values[1], &["forall", "exists"], &format!("{path}[1]"))?;
                identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?;
                expect_nil_or_identifier(&values[3], &format!("{path}[3]"))?;
                expect_nil_or_integer(&values[4], &format!("{path}[4]"))?;
                work.push((&values[5], format!("{path}[5]")));
            },
            "and" | "or" => {
                require_len(values, 2, &path)?;
                for (index, predicate) in expect_list(&values[1], &format!("{path}[1]"))?
                    .iter()
                    .enumerate()
                    .rev()
                {
                    work.push((predicate, format!("{path}[1][{index}]")));
                }
            },
            "not" => {
                require_len(values, 2, &path)?;
                work.push((&values[1], format!("{path}[1]")));
            },
            "implies" => {
                require_len(values, 3, &path)?;
                work.push((&values[2], format!("{path}[2]")));
                work.push((&values[1], format!("{path}[1]")));
            },
            "term_eq" | "term_neq" => {
                require_len(values, 3, &path)?;
                validate_predicate_arg(&values[1], &format!("{path}[1]"))?;
                validate_predicate_arg(&values[2], &format!("{path}[2]"))?;
            },
            "cmp" => {
                require_len(values, 4, &path)?;
                expect_relation(&values[1], &format!("{path}[1]"))?;
                validate_arithmetic_term(&values[2], &format!("{path}[2]"))?;
                validate_arithmetic_term(&values[3], &format!("{path}[3]"))?;
            },
            "in" => {
                require_len(values, 3, &path)?;
                validate_arithmetic_term(&values[1], &format!("{path}[1]"))?;
                validate_domain(&values[2], &format!("{path}[2]"))?;
            },
            "true" | "false" => require_len(values, 1, &path)?,
            "modal" => return error(&path, "modal predicates are not defined by language/2"),
            tag => return error(&path, format!("unknown refinement predicate tag `{tag}`")),
        }
    }
    Ok(())
}

fn validate_behavioral_predicate(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        let values = expect_list(value, &path)?;
        match tagged_head(values, &path)? {
            "call" | "ncall" => {
                require_len(values, 3, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                validate_predicate_args(&values[2], &format!("{path}[2]"))?;
            },
            "quant" => {
                require_len(values, 6, &path)?;
                expect_enum_string(&values[1], &["forall", "exists"], &format!("{path}[1]"))?;
                identifier(
                    expect_string(&values[2], &format!("{path}[2]"))?,
                    &format!("{path}[2]"),
                )?;
                expect_nil_or_identifier(&values[3], &format!("{path}[3]"))?;
                expect_nil_or_integer(&values[4], &format!("{path}[4]"))?;
                work.push((&values[5], format!("{path}[5]")));
            },
            "and" | "or" => {
                require_len(values, 2, &path)?;
                for (index, predicate) in expect_list(&values[1], &format!("{path}[1]"))?
                    .iter()
                    .enumerate()
                    .rev()
                {
                    work.push((predicate, format!("{path}[1][{index}]")));
                }
            },
            "not" => {
                require_len(values, 2, &path)?;
                work.push((&values[1], format!("{path}[1]")));
            },
            "implies" => {
                require_len(values, 3, &path)?;
                work.push((&values[2], format!("{path}[2]")));
                work.push((&values[1], format!("{path}[1]")));
            },
            "ac_match" => {
                require_len(values, 4, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                decode_ident_list(&values[2], &format!("{path}[2]"))?;
                expect_nil_or_identifier(&values[3], &format!("{path}[3]"))?;
            },
            "true" => require_len(values, 1, &path)?,
            "modal" => return error(&path, "modal predicates are not defined by language/2"),
            tag => return error(&path, format!("unknown behavioral predicate tag `{tag}`")),
        }
    }
    Ok(())
}

fn validate_predicate_args(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    for (index, value) in expect_list(value, path)?.iter().enumerate() {
        validate_predicate_arg(value, &format!("{path}[{index}]"))?;
    }
    Ok(())
}

fn validate_predicate_arg(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_list(value, path)?;
    match tagged_head(values, path)? {
        "var" | "const" => {
            require_len(values, 2, path)?;
            identifier(expect_string(&values[1], &format!("{path}[1]"))?, &format!("{path}[1]"))?;
            Ok(())
        },
        tag => error(path, format!("unknown predicate-argument tag `{tag}`")),
    }
}

fn validate_arithmetic_term(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        match value {
            RhoValue::String(name) => {
                identifier(name, &path)?;
            },
            RhoValue::Integer(_) => {},
            RhoValue::List(values) => match tagged_head(values, &path)? {
                "add" | "sub" | "mul" => {
                    require_len(values, 3, &path)?;
                    work.push((&values[2], format!("{path}[2]")));
                    work.push((&values[1], format!("{path}[1]")));
                },
                "neg" => {
                    require_len(values, 2, &path)?;
                    work.push((&values[1], format!("{path}[1]")));
                },
                tag => return error(&path, format!("unknown arithmetic-term tag `{tag}`")),
            },
            _ => return error(&path, "expected an arithmetic term"),
        }
    }
    Ok(())
}

fn validate_domain(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_list(value, path)?;
    match tagged_head(values, path)? {
        "range" => {
            require_len(values, 3, path)?;
            expect_integer(&values[1], &format!("{path}[1]"))?;
            expect_integer(&values[2], &format!("{path}[2]"))?;
        },
        "finite" => {
            require_len(values, 2, path)?;
            for (index, value) in expect_list(&values[1], &format!("{path}[1]"))?
                .iter()
                .enumerate()
            {
                expect_integer(value, &format!("{path}[1][{index}]"))?;
            }
        },
        tag => return error(path, format!("unknown domain tag `{tag}`")),
    }
    Ok(())
}

fn validate_tree_constraint(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        let values = expect_list(value, &path)?;
        match tagged_head(values, &path)? {
            "forall" | "exists" => {
                require_len(values, 4, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                validate_tree_domain(&values[2], &format!("{path}[2]"))?;
                work.push((&values[3], format!("{path}[3]")));
            },
            "and" | "or" => {
                require_len(values, 2, &path)?;
                for (index, value) in expect_list(&values[1], &format!("{path}[1]"))?
                    .iter()
                    .enumerate()
                    .rev()
                {
                    work.push((value, format!("{path}[1][{index}]")));
                }
            },
            "not" => {
                require_len(values, 2, &path)?;
                work.push((&values[1], format!("{path}[1]")));
            },
            "holds" => {
                require_len(values, 3, &path)?;
                identifier(
                    expect_string(&values[1], &format!("{path}[1]"))?,
                    &format!("{path}[1]"),
                )?;
                for (index, value) in expect_list(&values[2], &format!("{path}[2]"))?
                    .iter()
                    .enumerate()
                {
                    validate_tree_node_ref(value, &format!("{path}[2][{index}]"))?;
                }
            },
            "descends" => {
                require_len(values, 3, &path)?;
                validate_tree_node_ref(&values[1], &format!("{path}[1]"))?;
                validate_tree_node_ref(&values[2], &format!("{path}[2]"))?;
            },
            tag => return error(&path, format!("unknown tree-constraint tag `{tag}`")),
        }
    }
    Ok(())
}

fn validate_tree_domain(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_list(value, path)?;
    match tagged_head(values, path)? {
        "children" | "subtree" => {
            require_len(values, 2, path)?;
            validate_tree_node_ref(&values[1], &format!("{path}[1]"))
        },
        "category" | "label" => {
            require_len(values, 2, path)?;
            identifier(expect_string(&values[1], &format!("{path}[1]"))?, &format!("{path}[1]"))?;
            Ok(())
        },
        tag => error(path, format!("unknown tree-domain tag `{tag}`")),
    }
}

fn validate_tree_node_ref(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut current = value;
    let mut current_path = path.to_owned();
    loop {
        if let RhoValue::String(name) = current {
            return identifier(name, &current_path).map(|_| ());
        }
        let values = expect_list(current, &current_path)?;
        match tagged_head(values, &current_path)? {
            "root" => return require_len(values, 1, &current_path),
            "parent" => {
                require_len(values, 2, &current_path)?;
                current = &values[1];
                current_path.push_str("[1]");
            },
            tag => return error(&current_path, format!("unknown tree-node reference tag `{tag}`")),
        }
    }
}

fn validate_relation(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["relation", "params", "doc", "rules"], path)?;
    identifier(
        expect_string(required(values, "relation", path)?, &format!("{path}.relation"))?,
        &format!("{path}.relation"),
    )?;
    decode_ident_list(required(values, "params", path)?, &format!("{path}.params"))?;
    if let Some(doc) = values.get("doc") {
        expect_string(doc, &format!("{path}.doc"))?;
    }
    if let Some(rules) = values.get("rules") {
        for (index, rule) in expect_list(rules, &format!("{path}.rules"))?
            .iter()
            .enumerate()
        {
            validate_logic_rule(rule, &format!("{path}.rules[{index}]"))?;
        }
    }
    Ok(())
}

fn validate_logic_rule(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_map(value, path)?;
    reject_unknown_keys(values, &["head", "body"], path)?;
    validate_relation_atom(required(values, "head", path)?, &format!("{path}.head"))?;
    for (index, atom) in expect_list(required(values, "body", path)?, &format!("{path}.body"))?
        .iter()
        .enumerate()
    {
        let atom_path = format!("{path}.body[{index}]");
        let values = expect_list(atom, &atom_path)?;
        match tagged_head(values, &atom_path)? {
            "rel" => validate_relation_atom(atom, &atom_path)?,
            "not" => {
                require_len(values, 2, &atom_path)?;
                validate_relation_atom(&values[1], &format!("{atom_path}[1]"))?;
            },
            "guard" => {
                require_len(values, 2, &atom_path)?;
                validate_refinement_predicate(&values[1], &format!("{atom_path}[1]"))?;
            },
            tag => return error(&atom_path, format!("unknown rule-atom tag `{tag}`")),
        }
    }
    Ok(())
}

fn validate_relation_atom(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let values = expect_list(value, path)?;
    require_tagged_len(values, "rel", 3, path)?;
    identifier(expect_string(&values[1], &format!("{path}[1]"))?, &format!("{path}[1]"))?;
    for (index, term) in expect_list(&values[2], &format!("{path}[2]"))?
        .iter()
        .enumerate()
    {
        validate_rule_term(term, &format!("{path}[2][{index}]"))?;
    }
    Ok(())
}

fn validate_rule_term(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, path.to_owned())];
    while let Some((value, path)) = work.pop() {
        match value {
            RhoValue::String(_)
            | RhoValue::Bytes(_)
            | RhoValue::Integer(_)
            | RhoValue::FloatBits(_)
            | RhoValue::Boolean(_)
            | RhoValue::Nil => {},
            RhoValue::List(values) => {
                require_len(values, 2, &path)?;
                identifier(
                    expect_string(&values[0], &format!("{path}[0]"))?,
                    &format!("{path}[0]"),
                )?;
                let arguments = expect_list(&values[1], &format!("{path}[1]"))?;
                for (index, argument) in arguments.iter().enumerate().rev() {
                    work.push((argument, format!("{path}[1][{index}]")));
                }
            },
            RhoValue::Map(_) => return error(&path, "maps are not rule terms"),
        }
    }
    Ok(())
}

fn validate_name_list(value: Option<&RhoValue>, path: &str) -> Result<(), ValueDecodeError> {
    if let Some(value) = value {
        decode_ident_list(value, path)?;
    }
    Ok(())
}

fn decode_exports(
    value: Option<&RhoValue>,
    path: &str,
) -> Result<Vec<(String, String)>, ValueDecodeError> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    let mut output = Vec::new();
    for (index, pair) in expect_list(value, path)?.iter().enumerate() {
        let pair_path = format!("{path}[{index}]");
        let pair = expect_list(pair, &pair_path)?;
        require_len(pair, 2, &pair_path)?;
        output.push((
            identifier(
                expect_string(&pair[0], &format!("{pair_path}[0]"))?,
                &format!("{pair_path}[0]"),
            )?,
            identifier(
                expect_string(&pair[1], &format!("{pair_path}[1]"))?,
                &format!("{pair_path}[1]"),
            )?,
        ));
    }
    Ok(output)
}

fn validate_replacements(value: Option<&RhoValue>, path: &str) -> Result<(), ValueDecodeError> {
    let Some(value) = value else { return Ok(()) };
    for (index, replacement) in expect_list(value, path)?.iter().enumerate() {
        let replacement_path = format!("{path}[{index}]");
        let replacement = expect_map(replacement, &replacement_path)?;
        reject_unknown_keys(replacement, &["label", "keep", "rename"], &replacement_path)?;
        identifier(
            expect_string(
                required(replacement, "label", &replacement_path)?,
                &format!("{replacement_path}.label"),
            )?,
            &format!("{replacement_path}.label"),
        )?;
        expect_enum_string(
            required(replacement, "keep", &replacement_path)?,
            &["left", "right"],
            &format!("{replacement_path}.keep"),
        )?;
        optional_identifier(replacement, "rename", &replacement_path)?;
    }
    Ok(())
}

fn required<'a>(
    values: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<&'a RhoValue, ValueDecodeError> {
    values
        .get(key)
        .ok_or_else(|| ValueDecodeError::new(format!("{path}.{key}"), "missing required field"))
}

fn optional_string(
    values: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<Option<String>, ValueDecodeError> {
    values
        .get(key)
        .map(|value| expect_string(value, &format!("{path}.{key}")).map(str::to_string))
        .transpose()
}

fn optional_identifier(
    values: &BTreeMap<String, RhoValue>,
    key: &str,
    path: &str,
) -> Result<Option<String>, ValueDecodeError> {
    values
        .get(key)
        .map(|value| {
            identifier(expect_string(value, &format!("{path}.{key}"))?, &format!("{path}.{key}"))
        })
        .transpose()
}

fn expect_map<'a>(
    value: &'a RhoValue,
    path: &str,
) -> Result<&'a BTreeMap<String, RhoValue>, ValueDecodeError> {
    match value {
        RhoValue::Map(values) => Ok(values),
        _ => error(path, "expected map"),
    }
}

fn expect_list<'a>(value: &'a RhoValue, path: &str) -> Result<&'a [RhoValue], ValueDecodeError> {
    match value {
        RhoValue::List(values) => Ok(values),
        _ => error(path, "expected list"),
    }
}

fn expect_string<'a>(value: &'a RhoValue, path: &str) -> Result<&'a str, ValueDecodeError> {
    match value {
        RhoValue::String(value) => Ok(value),
        _ => error(path, "expected string"),
    }
}

fn expect_nonempty_string<'a>(
    value: &'a RhoValue,
    path: &str,
) -> Result<&'a str, ValueDecodeError> {
    let value = expect_string(value, path)?;
    if value.is_empty() {
        error(path, "string must not be empty")
    } else {
        Ok(value)
    }
}

fn expect_bool(value: &RhoValue, path: &str) -> Result<bool, ValueDecodeError> {
    match value {
        RhoValue::Boolean(value) => Ok(*value),
        _ => error(path, "expected boolean"),
    }
}

fn expect_integer(value: &RhoValue, path: &str) -> Result<i128, ValueDecodeError> {
    match value {
        RhoValue::Integer(value) => Ok(*value),
        _ => error(path, "expected integer"),
    }
}

fn expect_i16(value: &RhoValue, path: &str) -> Result<i16, ValueDecodeError> {
    i16::try_from(expect_integer(value, path)?)
        .map_err(|_| ValueDecodeError::new(path, "integer is outside the i16 range"))
}

fn expect_u8(value: &RhoValue, path: &str) -> Result<u8, ValueDecodeError> {
    u8::try_from(expect_integer(value, path)?)
        .map_err(|_| ValueDecodeError::new(path, "integer is outside the u8 range"))
}

fn expect_u16(value: &RhoValue, path: &str) -> Result<u16, ValueDecodeError> {
    u16::try_from(expect_integer(value, path)?)
        .map_err(|_| ValueDecodeError::new(path, "integer is outside the u16 range"))
}

fn expect_u32(value: &RhoValue, path: &str) -> Result<u32, ValueDecodeError> {
    u32::try_from(expect_integer(value, path)?)
        .map_err(|_| ValueDecodeError::new(path, "integer is outside the u32 range"))
}

fn expect_nonnegative_f64(value: &RhoValue, path: &str) -> Result<f64, ValueDecodeError> {
    let RhoValue::FloatBits(bits) = value else {
        return error(path, "expected a finite nonnegative float");
    };
    let value = f64::from_bits(*bits);
    if value.is_finite() && value >= 0.0 {
        Ok(value)
    } else {
        error(path, "expected a finite nonnegative float")
    }
}

fn expect_enum_string<'a>(
    value: &'a RhoValue,
    accepted: &[&str],
    path: &str,
) -> Result<&'a str, ValueDecodeError> {
    let value = expect_string(value, path)?;
    if accepted.contains(&value) {
        Ok(value)
    } else {
        error(path, format!("expected one of {}, found `{value}`", accepted.join(", ")))
    }
}

fn expect_nil_or_string(value: &RhoValue, path: &str) -> Result<Option<String>, ValueDecodeError> {
    match value {
        RhoValue::Nil => Ok(None),
        RhoValue::String(value) => Ok(Some(value.clone())),
        _ => error(path, "expected string or Nil"),
    }
}

fn validate_pathmap_mode(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    match value {
        RhoValue::Nil => Ok(()),
        RhoValue::String(value) if matches!(value.as_str(), "neutral-empty" | "set" | "map") => {
            Ok(())
        },
        _ => error(path, "expected neutral-empty, set, map, or Nil"),
    }
}

fn expect_nil_or_identifier(
    value: &RhoValue,
    path: &str,
) -> Result<Option<String>, ValueDecodeError> {
    match value {
        RhoValue::Nil => Ok(None),
        RhoValue::String(value) => identifier(value, path).map(Some),
        _ => error(path, "expected identifier or Nil"),
    }
}

fn expect_nil_or_integer(value: &RhoValue, path: &str) -> Result<Option<i128>, ValueDecodeError> {
    match value {
        RhoValue::Nil => Ok(None),
        RhoValue::Integer(value) => Ok(Some(*value)),
        _ => error(path, "expected integer or Nil"),
    }
}

fn tagged_head<'a>(values: &'a [RhoValue], path: &str) -> Result<&'a str, ValueDecodeError> {
    values
        .first()
        .ok_or_else(|| ValueDecodeError::new(path, "tagged list must not be empty"))
        .and_then(|value| expect_string(value, &format!("{path}[0]")))
}

fn require_len(values: &[RhoValue], expected: usize, path: &str) -> Result<(), ValueDecodeError> {
    if values.len() == expected {
        Ok(())
    } else {
        error(path, format!("expected {expected} items, found {}", values.len()))
    }
}

fn require_tagged_len(
    values: &[RhoValue],
    tag: &str,
    expected: usize,
    path: &str,
) -> Result<(), ValueDecodeError> {
    require_len(values, expected, path)?;
    let actual = tagged_head(values, path)?;
    if actual == tag {
        Ok(())
    } else {
        error(format!("{path}[0]"), format!("expected tag `{tag}`, found `{actual}`"))
    }
}

fn reject_unknown_keys(
    values: &BTreeMap<String, RhoValue>,
    accepted: &[&str],
    path: &str,
) -> Result<(), ValueDecodeError> {
    if let Some(key) = values.keys().find(|key| !accepted.contains(&key.as_str())) {
        error(format!("{path}.{key}"), "unknown key")
    } else {
        Ok(())
    }
}

fn decode_sequence<T>(
    value: Option<&RhoValue>,
    path: &str,
    mut decode: impl FnMut(&RhoValue, &str) -> Result<T, ValueDecodeError>,
) -> Result<Vec<T>, ValueDecodeError> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    expect_list(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| decode(value, &format!("{path}[{index}]")))
        .collect()
}

fn validate_value_sequence(
    value: Option<&RhoValue>,
    path: &str,
    mut validate: impl FnMut(&RhoValue, &str) -> Result<(), ValueDecodeError>,
) -> Result<Vec<RhoValue>, ValueDecodeError> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    let values = expect_list(value, path)?;
    for (index, value) in values.iter().enumerate() {
        validate(value, &format!("{path}[{index}]"))?;
    }
    Ok(values.to_vec())
}

fn decode_ident_list(value: &RhoValue, path: &str) -> Result<Vec<String>, ValueDecodeError> {
    expect_list(value, path)?
        .iter()
        .enumerate()
        .map(|(index, value)| {
            identifier(
                expect_string(value, &format!("{path}[{index}]"))?,
                &format!("{path}[{index}]"),
            )
        })
        .collect()
}

fn validate_unique_names<'a>(
    values: impl IntoIterator<Item = &'a String>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut names = BTreeSet::new();
    for name in values {
        if !names.insert(name) {
            return error(path, format!("duplicate name `{name}`"));
        }
    }
    Ok(())
}

fn validate_scalar(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    match value {
        RhoValue::String(_)
        | RhoValue::Integer(_)
        | RhoValue::FloatBits(_)
        | RhoValue::Boolean(_)
        | RhoValue::Nil => Ok(()),
        _ => error(path, "expected scalar"),
    }
}

fn expect_relation(value: &RhoValue, path: &str) -> Result<(), ValueDecodeError> {
    expect_enum_string(value, &["lt", "le", "gt", "ge", "eq", "ne"], path).map(|_| ())
}

fn collection_kind(value: &str, path: &str) -> Result<core::CollectionKind, ValueDecodeError> {
    match value {
        "list" | "vec" => Ok(core::CollectionKind::List),
        "bag" => Ok(core::CollectionKind::Bag),
        "set" => Ok(core::CollectionKind::Set),
        "map" => Ok(core::CollectionKind::Map),
        "pathmap" => Ok(core::CollectionKind::PathMap),
        _ => error(path, format!("unknown collection kind `{value}`")),
    }
}

fn identifier(value: &str, path: &str) -> Result<String, ValueDecodeError> {
    let mut chars = value.chars();
    if !chars
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
        || !chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return error(path, format!("`{value}` is not an ASCII identifier"));
    }
    const RUST_KEYWORDS: &[&str] = &[
        "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn",
        "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
        "return", "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe",
        "use", "where", "while", "async", "await", "dyn", "abstract", "become", "box", "do",
        "final", "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
    ];
    if RUST_KEYWORDS.contains(&value) {
        return error(path, format!("`{value}` is a reserved Rust keyword"));
    }
    if value.starts_with('^') {
        return error(path, "labels beginning with `^` are reserved for reflected runtime markers");
    }
    Ok(value.to_string())
}

pub(crate) fn to_core_value(value: &RhoValue) -> core::CanonicalValue {
    enum Task<'a> {
        Visit(&'a RhoValue),
        FinishList(usize),
        FinishMap(Vec<&'a str>),
    }

    let mut tasks = vec![Task::Visit(value)];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(RhoValue::Map(values)) => {
                tasks.push(Task::FinishMap(values.keys().map(String::as_str).collect()));
                tasks.extend(values.values().rev().map(Task::Visit));
            },
            Task::Visit(RhoValue::List(values)) => {
                tasks.push(Task::FinishList(values.len()));
                tasks.extend(values.iter().rev().map(Task::Visit));
            },
            Task::Visit(RhoValue::String(value)) => {
                output.push(core::CanonicalValue::String(value.clone()));
            },
            Task::Visit(RhoValue::Bytes(value)) => {
                output.push(core::CanonicalValue::Bytes(value.clone()));
            },
            Task::Visit(RhoValue::Integer(value)) => {
                output.push(core::CanonicalValue::Integer(*value));
            },
            Task::Visit(RhoValue::FloatBits(bits)) => {
                output.push(core::CanonicalValue::FloatBits(*bits));
            },
            Task::Visit(RhoValue::Boolean(value)) => {
                output.push(core::CanonicalValue::Boolean(*value));
            },
            Task::Visit(RhoValue::Nil) => output.push(core::CanonicalValue::Nil),
            Task::FinishList(count) => {
                let start = output.len() - count;
                let values = output.drain(start..).collect();
                output.push(core::CanonicalValue::List(values));
            },
            Task::FinishMap(keys) => {
                let start = output.len() - keys.len();
                let values: Vec<_> = output.drain(start..).collect();
                output.push(core::CanonicalValue::Map(
                    keys.into_iter().map(str::to_string).zip(values).collect(),
                ));
            },
        }
    }
    output
        .pop()
        .expect("canonical value conversion produces one value")
}

impl LanguageSchema {
    fn apply_exports(&mut self) -> Result<(), ValueDecodeError> {
        for (index, (from, to)) in self.exports.clone().into_iter().enumerate() {
            if from == to {
                continue;
            }
            if !self
                .types
                .iter()
                .any(|declaration| declaration.name == from)
            {
                return error(
                    format!("$.exports[{index}][0]"),
                    format!("unknown exported category `{from}`"),
                );
            }
            if self.types.iter().any(|declaration| declaration.name == to) {
                return error(
                    format!("$.exports[{index}][1]"),
                    format!("export rename collides with category `{to}`"),
                );
            }
            self.rename_category(&from, &to);
        }
        Ok(())
    }

    fn rename_category(&mut self, from: &str, to: &str) {
        for declaration in &mut self.types {
            rename_string(&mut declaration.name, from, to);
            match &mut declaration.carrier {
                core::Carrier::Collection(collection) => {
                    rename_string(&mut collection.key, from, to);
                    if let Some(value) = &mut collection.value {
                        rename_string(value, from, to);
                    }
                },
                _ => {},
            }
            if let Some(refinement) = &mut declaration.refinement {
                rename_string(&mut refinement.base, from, to);
            }
        }
        for literal in &mut self.literals {
            rename_string(&mut literal.category, from, to);
        }
        for token in self.tokens.iter_mut().chain(
            self.modes
                .iter_mut()
                .flat_map(|mode| mode.tokens.iter_mut()),
        ) {
            if let Some(category) = &mut token.category {
                rename_string(category, from, to);
            }
        }
        for term in &mut self.terms {
            rename_string(&mut term.category, from, to);
            for param in &mut term.context {
                rename_param_category(param, from, to);
            }
            if let TermBody::Bnf(items) = &mut term.body {
                for item in items {
                    match item {
                        BnfNode::Nonterminal(category)
                        | BnfNode::Collection { element: category, .. } => {
                            rename_string(category, from, to)
                        },
                        _ => {},
                    }
                }
            }
        }
        for invariant in &mut self.tree_invariants {
            rename_tagged_string(&mut invariant.value, "category", 1, from, to);
        }
        if let Some(guards) = &mut self.guards {
            for theory in &mut guards.theories {
                if let Some(categories) = &mut theory.handled_categories {
                    for category in categories {
                        rename_string(category, from, to);
                    }
                }
            }
            if let Some(categories) = &mut guards.channel_categories {
                for category in categories {
                    rename_string(category, from, to);
                }
            }
            for join in &mut guards.join_patterns {
                for category in &mut join.channel_categories {
                    rename_string(category, from, to);
                }
            }
        }
        for value in self.equations.iter_mut().chain(self.rewrites.iter_mut()) {
            rename_tagged_string(value, "coll_typed", 1, from, to);
        }
    }

    pub(crate) fn lower(&self) -> Result<core::GrammarCoreV1, ValueDecodeError> {
        let mut output = core::GrammarCoreV1::new(&self.name);
        output.provenance.frontend = format!("rholang-{}", self.notation);
        output.backend_context = self.context.clone();
        output.documentation = self.documentation.clone();
        if self.notation == "language/2" {
            output.semantic_program.target = self.semantics.clone();
            output.semantic_program.equations = self.equations.iter().map(to_core_value).collect();
            output.semantic_program.rewrites = self.rewrites.iter().map(to_core_value).collect();
            output.semantic_program.relations = self.relations.iter().map(to_core_value).collect();
            output.semantic_program.guards = self
                .guards
                .as_ref()
                .map(|guards| to_core_value(&guards.value));
        }
        if let Some(beam_width) = self.options.beam_width {
            output.parser_configuration.beam_width = beam_width;
        }
        if let Some(path) = &self.options.log_semiring_model_path {
            output.parser_configuration.log_semiring_model_path = Some(path.clone());
        }
        if let Some(reservation) = &self.options.reserved_keywords {
            output.parser_configuration.reservation = reservation.clone();
        }
        if let Some(recovery) = &self.options.recovery {
            output.parser_configuration.recovery = recovery.clone();
        }
        output.synchronization = self.synchronization.clone();
        output.categories = self
            .types
            .iter()
            .enumerate()
            .map(|(index, declaration)| core::Category {
                id: core::CategoryId(index as u32),
                name: declaration.name.clone(),
                carrier: declaration.carrier.clone(),
                primary: index == 0,
                admits_variables: declaration.admits_variables,
            })
            .collect();
        let categories: BTreeMap<_, _> = output
            .categories
            .iter()
            .map(|category| (category.name.clone(), category.id))
            .collect();
        for declaration in &self.types {
            if let core::Carrier::Extern { urn } = &declaration.carrier {
                output
                    .capabilities
                    .insert(core::Capability::ExternCarrier(urn.clone()));
            }
            if let Some(collection) = &declaration.collection {
                let _ = (
                    collection.kind,
                    &collection.open,
                    &collection.close,
                    &collection.separator,
                    &collection.key_value_separator,
                );
            }
            if let Some(refinement) = &declaration.refinement {
                output.refinement_types.push(core::RefinementType {
                    name: declaration.name.clone(),
                    base_category: refinement.base.clone(),
                    variable_name: refinement.variable.clone(),
                    predicate_kind: core::RefinementPredicateKind::Presburger,
                    predicate: to_core_value(&refinement.predicate),
                });
            }
        }
        output.tree_invariants = self
            .tree_invariants
            .iter()
            .map(|invariant| core::TreeInvariant {
                name: invariant.name.clone(),
                formula: to_core_value(&invariant.value),
            })
            .collect();
        if let Some(guards) = &self.guards {
            for theory in &guards.theories {
                output
                    .capabilities
                    .insert(core::Capability::GuardTheory(theory.implementation.clone()));
            }
            output.guard_configuration = Some(core::GuardConfiguration {
                theories: guards.theories.clone(),
                channel_categories: guards.channel_categories.clone(),
                join_patterns: guards.join_patterns.clone(),
                selectivity_overrides: guards.selectivity.clone(),
                cost_overrides: guards.costs.clone(),
                has_explicit_connectives: guards.has_connectives,
                has_explicit_predicates: guards.has_predicates,
            });
        }

        output.modes = std::iter::once(core::LexerMode {
            id: core::ModeId(0),
            name: "default".into(),
            token_ids: Vec::new(),
            raw: false,
        })
        .chain(
            self.modes
                .iter()
                .enumerate()
                .map(|(index, mode)| core::LexerMode {
                    id: core::ModeId(index as u32 + 1),
                    name: mode.name.clone(),
                    token_ids: Vec::new(),
                    raw: mode.raw,
                }),
        )
        .collect();
        let mode_ids: BTreeMap<_, _> = output
            .modes
            .iter()
            .map(|mode| (mode.name.clone(), mode.id))
            .collect();
        if self.modes.iter().any(|mode| mode.name == "default") {
            return error("$.modes", "`default` is the reserved implicit lexer mode name");
        }

        let identifier_id = core::TokenId(0);
        output.tokens.push(core::TokenDefinition {
            id: identifier_id,
            name: "Identifier".into(),
            pattern: core::TokenPattern::Builtin(core::BuiltinToken::Identifier),
            category: None,
            evaluation: None,
            priority: 0,
            mode: core::ModeId(0),
            channel: "main".into(),
            transition: core::ModeTransition::default(),
            decoder: core::TokenDecoder::Text,
            reservation: core::Reservation::None,
        });
        output.modes[0].token_ids.push(identifier_id);
        let mut token_ids = BTreeMap::from([("Identifier".to_string(), identifier_id)]);
        for (index, literal) in self.literals.iter().enumerate() {
            let name = format!("literal/{}/{}", literal.category, index);
            let token = TokenDecl {
                name,
                pattern: literal.pattern.clone(),
                category: Some(literal.category.clone()),
                evaluation: Some(literal.evaluation.clone()),
                priority: 0,
                push: None,
                pop: false,
                stream: None,
            };
            add_token(
                &token,
                core::ModeId(0),
                &mode_ids,
                &categories,
                &mut output,
                &mut token_ids,
                "$.literals",
            )?;
        }
        for (index, token) in self.tokens.iter().enumerate() {
            add_token(
                token,
                core::ModeId(0),
                &mode_ids,
                &categories,
                &mut output,
                &mut token_ids,
                &format!("$.tokens[{index}]"),
            )?;
        }
        for (mode_index, mode) in self.modes.iter().enumerate() {
            for (token_index, token) in mode.tokens.iter().enumerate() {
                add_token(
                    token,
                    core::ModeId(mode_index as u32 + 1),
                    &mode_ids,
                    &categories,
                    &mut output,
                    &mut token_ids,
                    &format!("$.modes[{mode_index}].tokens[{token_index}]"),
                )?;
            }
        }
        let mut literal_ids = BTreeMap::new();
        let mut literal_text = BTreeSet::new();
        for term in &self.terms {
            collect_term_literals(&term.body, &mut literal_text);
        }
        for terminal in literal_text {
            let id = core::TokenId(output.tokens.len() as u32);
            literal_ids.insert(terminal.clone(), id);
            output.tokens.push(core::TokenDefinition {
                id,
                name: format!("terminal/{terminal}"),
                pattern: core::TokenPattern::Literal(terminal),
                category: None,
                evaluation: None,
                priority: 1,
                mode: core::ModeId(0),
                channel: "main".into(),
                transition: core::ModeTransition::default(),
                decoder: core::TokenDecoder::Unit,
                reservation: core::Reservation::Contextual,
            });
            output.modes[0].token_ids.push(id);
        }

        for (index, term) in self.terms.iter().enumerate() {
            let path = format!("$.terms[{index}]");
            let result = category_id(&categories, &term.category, &format!("{path}.category"))?;
            let descriptors =
                parameter_descriptors(&term.context, &categories, &format!("{path}.context"))?;
            let syntax = lower_term_body(
                &term.body,
                &descriptors,
                &categories,
                &token_ids,
                &literal_ids,
                identifier_id,
                &path,
            )?;
            let slots = collect_core_slots(&syntax);
            let constructor = core::ConstructorId(index as u32);
            if let Some(evaluation) = &term.evaluation {
                register_evaluation_capability(evaluation, &mut output.capabilities);
            }
            output.reductions.push(core::ReductionPlan {
                output_category: result,
                constructor,
                input_arity: u16::try_from(slots.len()).map_err(|_| {
                    ValueDecodeError::new(&path, "term has more than u16::MAX semantic inputs")
                })?,
                fields: (0..slots.len() as u16)
                    .map(core::FieldSource::Input)
                    .collect(),
                evaluation: term.evaluation.clone(),
                evaluation_mode: term
                    .evaluation
                    .as_ref()
                    .map(|_| term.mode.unwrap_or(core::EvaluationMode::Fold)),
                tier: term.tier.clone(),
            });
            let classification = classify_production(&syntax, &term.context);
            output.productions.push(core::Production {
                id: core::ProductionId(index as u32),
                constructor,
                label: term.label.clone(),
                result,
                syntax,
                precedence: core::Precedence {
                    binding_power: term.prefix_binding_power,
                    associativity: term.associativity,
                    shares_previous_level: term.shares_previous_level,
                },
                classification,
                reduction: index as u32,
                provenance: None,
            });
        }
        let constructors: BTreeMap<_, _> = output
            .productions
            .iter()
            .map(|production| (production.label.clone(), production.constructor))
            .collect();
        if self.notation == "language/2" {
            output.semantic_dependencies = self
                .equations
                .iter()
                .chain(self.rewrites.iter())
                .map(|value| {
                    let mut dependencies = BTreeSet::new();
                    collect_constructor_references(value, &constructors, &mut dependencies);
                    dependencies.into_iter().collect()
                })
                .collect();
        }
        output.validate().map_err(|errors| {
            ValueDecodeError::new("$", format!("invalid GrammarCore: {errors:?}"))
        })?;
        Ok(output)
    }

    pub(crate) fn lower_language(&self) -> Result<core::LanguageCoreV1, ValueDecodeError> {
        let grammar = self.lower()?;
        let mut theory = self.theory.clone();
        if theory.profile == core::TheoryProfileV1::Oslf {
            self.complete_theory_signature(&mut theory)?;
            crate::theory_compile::compile_surface_rules(
                &self.equations,
                &self.rewrites,
                &mut theory,
            )?;
            crate::theory_compile::infer_judgment_types(&mut theory)?;
        }
        let language = core::LanguageCoreV1 {
            abi: core::LANGUAGE_CORE_ABI_CURRENT,
            grammar,
            theory,
        };
        language.validate().map_err(|errors| {
            ValueDecodeError::new("$.oslf", format!("invalid LanguageCore: {errors:?}"))
        })?;
        Ok(language)
    }

    pub(crate) fn requested_rights(&self) -> core::LanguageRights {
        self.requested_rights.clone()
    }

    fn complete_theory_signature(
        &self,
        theory: &mut core::TheoryCoreV1,
    ) -> Result<(), ValueDecodeError> {
        if !theory.sorts.is_empty()
            || !theory.constructors.is_empty()
            || !theory.binders.is_empty()
            || !theory.equations.is_empty()
            || !theory.rewrites.is_empty()
        {
            return error(
                "$.oslf",
                "presentation lowering cannot be mixed with an embedded executable signature",
            );
        }
        let mut sort_indices = BTreeMap::<String, usize>::new();
        for declaration in &self.types {
            let literal = theory_literal_carrier(&declaration.carrier);
            let index = theory.sorts.len();
            if sort_indices
                .insert(declaration.name.clone(), index)
                .is_some()
            {
                return error("$.types", format!("duplicate theory sort `{}`", declaration.name));
            }
            theory.sorts.push(core::TheorySortV1 {
                name: declaration.name.clone(),
                kind: core::TheorySortKindV1::Syntax { literal },
            });
        }
        let guard_sort = "mettail:sort:guard/1".to_string();
        for term in &self.terms {
            let mut domain = Vec::new();
            let mut argument = 0usize;
            let mut work: Vec<_> = term.context.iter().rev().collect();
            while let Some(parameter) = work.pop() {
                match parameter {
                    Param::Plain { ty, .. } => {
                        domain.push(ensure_theory_sort(ty, theory, &mut sort_indices)?);
                        argument += 1;
                    },
                    Param::Binder { binder, body, ty, multiple } => {
                        let TypeExpr::Arrow(from, to) = ty else {
                            return error("$.terms", "binder parameter requires an arrow sort");
                        };
                        let bound_sort = ensure_theory_sort(from, theory, &mut sort_indices)?;
                        let body_sort = ensure_theory_sort(to, theory, &mut sort_indices)?;
                        let result_sort = if *multiple {
                            let name = format!("[*{bound_sort} -> {body_sort}]");
                            insert_theory_sort(
                                name.clone(),
                                core::TheorySortKindV1::Function {
                                    domain: bound_sort.clone(),
                                    codomain: body_sort.clone(),
                                    multiple: true,
                                },
                                theory,
                                &mut sort_indices,
                            )?;
                            name
                        } else {
                            ensure_theory_sort(ty, theory, &mut sort_indices)?
                        };
                        theory.binders.push(core::TheoryBinderV1 {
                            name: format!("{}::{binder}.{body}", term.label),
                            constructor: term.label.clone(),
                            argument: u16::try_from(argument).map_err(|_| {
                                ValueDecodeError::new(
                                    "$.terms",
                                    "constructor has more than u16::MAX semantic arguments",
                                )
                            })?,
                            bound_sort,
                            body_sort,
                            result_sort: result_sort.clone(),
                            multiple: *multiple,
                        });
                        domain.push(result_sort);
                        argument += 1;
                    },
                    Param::Guard(_) => {
                        if !sort_indices.contains_key(&guard_sort) {
                            let index = theory.sorts.len();
                            sort_indices.insert(guard_sort.clone(), index);
                            theory.sorts.push(core::TheorySortV1 {
                                name: guard_sort.clone(),
                                kind: core::TheorySortKindV1::Opaque {
                                    abi: "mettail:guard-value/1".into(),
                                },
                            });
                        }
                        domain.push(guard_sort.clone());
                        argument += 1;
                    },
                    Param::Optional(parameters) => work.extend(parameters.iter().rev()),
                }
            }
            theory.constructors.push(core::TheoryConstructorV1 {
                name: term.label.clone(),
                domain,
                codomain: term.category.clone(),
            });
        }
        Ok(())
    }
}

fn ensure_theory_sort(
    root: &TypeExpr,
    theory: &mut core::TheoryCoreV1,
    indices: &mut BTreeMap<String, usize>,
) -> Result<String, ValueDecodeError> {
    enum Task<'a> {
        Visit(&'a TypeExpr),
        FinishList,
        FinishCollection(core::CollectionKind, bool),
        FinishArrow,
    }
    let mut tasks = vec![Task::Visit(root)];
    let mut values = Vec::<String>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(TypeExpr::Base(name)) => {
                if !indices.contains_key(name) {
                    return error("$.types", format!("unknown theory sort `{name}`"));
                }
                values.push(name.clone());
            },
            Task::Visit(TypeExpr::Multi(element)) => {
                tasks.push(Task::FinishList);
                tasks.push(Task::Visit(element));
            },
            Task::Visit(TypeExpr::Collection(kind, key, value)) => {
                tasks.push(Task::FinishCollection(*kind, value.is_some()));
                if let Some(value) = value {
                    tasks.push(Task::Visit(value));
                }
                tasks.push(Task::Visit(key));
            },
            Task::Visit(TypeExpr::Arrow(domain, codomain)) => {
                tasks.push(Task::FinishArrow);
                tasks.push(Task::Visit(codomain));
                tasks.push(Task::Visit(domain));
            },
            Task::FinishList => {
                let element = values.pop().expect("list element sort is scheduled");
                let name = format!("List({element})");
                insert_theory_sort(
                    name.clone(),
                    core::TheorySortKindV1::Collection {
                        kind: core::CollectionKind::List,
                        key: None,
                        element,
                    },
                    theory,
                    indices,
                )?;
                values.push(name);
            },
            Task::FinishCollection(kind, has_value) => {
                let value =
                    has_value.then(|| values.pop().expect("collection value sort is scheduled"));
                let key = values.pop().expect("collection key sort is scheduled");
                match (kind, value.is_some()) {
                    (core::CollectionKind::Map | core::CollectionKind::PathMap, true)
                    | (
                        core::CollectionKind::List
                        | core::CollectionKind::Bag
                        | core::CollectionKind::Set,
                        false,
                    ) => {},
                    (core::CollectionKind::Map | core::CollectionKind::PathMap, false) => {
                        return error(
                            "$.types",
                            "map and PathMap type expressions require key and value sorts",
                        );
                    },
                    _ => {
                        return error(
                            "$.types",
                            "list, bag, and set type expressions accept exactly one element sort",
                        );
                    },
                }
                let name = match &value {
                    Some(value) => format!("{}({key},{value})", collection_sort_name(kind)),
                    None => format!("{}({key})", collection_sort_name(kind)),
                };
                let (declared_key, element) = match value {
                    Some(value) => {
                        let product = derived_product_sort_name(&key, &value);
                        insert_theory_sort(
                            product.clone(),
                            core::TheorySortKindV1::Product { factors: vec![key.clone(), value] },
                            theory,
                            indices,
                        )?;
                        (Some(key), product)
                    },
                    None => (None, key),
                };
                insert_theory_sort(
                    name.clone(),
                    core::TheorySortKindV1::Collection { kind, key: declared_key, element },
                    theory,
                    indices,
                )?;
                values.push(name);
            },
            Task::FinishArrow => {
                let codomain = values.pop().expect("arrow codomain sort is scheduled");
                let domain = values.pop().expect("arrow domain sort is scheduled");
                let name = format!("[{domain} -> {codomain}]");
                insert_theory_sort(
                    name.clone(),
                    core::TheorySortKindV1::Function { domain, codomain, multiple: false },
                    theory,
                    indices,
                )?;
                values.push(name);
            },
        }
    }
    if values.len() != 1 {
        return error("$.types", "theory sort compiler produced an invalid value stack");
    }
    Ok(values.pop().expect("checked one theory sort"))
}

fn derived_product_sort_name(key: &str, value: &str) -> String {
    format!("@product:{}:{key}:{}:{value}", key.len(), value.len(),)
}

fn insert_theory_sort(
    name: String,
    kind: core::TheorySortKindV1,
    theory: &mut core::TheoryCoreV1,
    indices: &mut BTreeMap<String, usize>,
) -> Result<(), ValueDecodeError> {
    if let Some(index) = indices.get(&name) {
        if theory.sorts[*index].kind != kind {
            return error("$.types", format!("inconsistent definitions of theory sort `{name}`"));
        }
        return Ok(());
    }
    indices.insert(name.clone(), theory.sorts.len());
    theory.sorts.push(core::TheorySortV1 { name, kind });
    Ok(())
}

fn collection_sort_name(kind: core::CollectionKind) -> &'static str {
    match kind {
        core::CollectionKind::Bag => "HashBag",
        core::CollectionKind::Set => "Set",
        core::CollectionKind::List => "List",
        core::CollectionKind::Map => "Map",
        core::CollectionKind::PathMap => "PathMap",
    }
}

fn theory_literal_carrier(carrier: &core::Carrier) -> Option<core::TheoryLiteralCarrierV1> {
    Some(match carrier {
        core::Carrier::Dynamic | core::Carrier::Collection(_) => return None,
        core::Carrier::Builtin(core::BuiltinCarrier::Boolean) => {
            core::TheoryLiteralCarrierV1::Boolean
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Integer) => {
            core::TheoryLiteralCarrierV1::Integer
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Rational) => {
            core::TheoryLiteralCarrierV1::Rational
        },
        core::Carrier::Builtin(core::BuiltinCarrier::FixedPoint) => {
            core::TheoryLiteralCarrierV1::FixedPoint
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Float) => core::TheoryLiteralCarrierV1::Float,
        core::Carrier::Builtin(core::BuiltinCarrier::String) => {
            core::TheoryLiteralCarrierV1::String
        },
        core::Carrier::Builtin(core::BuiltinCarrier::Bytes) => core::TheoryLiteralCarrierV1::Bytes,
        core::Carrier::Extern { urn } => core::TheoryLiteralCarrierV1::External(urn.clone()),
        core::Carrier::HostOpaque { stable_name } => {
            core::TheoryLiteralCarrierV1::HostOpaque(stable_name.clone())
        },
    })
}

fn rename_param_category(param: &mut Param, from: &str, to: &str) {
    let mut work = vec![param];
    while let Some(param) = work.pop() {
        match param {
            Param::Plain { ty, .. } | Param::Binder { ty, .. } => {
                rename_type_expr_category(ty, from, to);
            },
            Param::Optional(params) => work.extend(params.iter_mut()),
            Param::Guard(_) => {},
        }
    }
}

fn rename_type_expr_category(value: &mut TypeExpr, from: &str, to: &str) {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            TypeExpr::Base(category) => rename_string(category, from, to),
            TypeExpr::Arrow(left, right) => {
                work.push(right);
                work.push(left);
            },
            TypeExpr::Multi(value) => work.push(value),
            TypeExpr::Collection(_, key, value) => {
                if let Some(value) = value {
                    work.push(value);
                }
                work.push(key);
            },
        }
    }
}

fn rename_tagged_string(value: &mut RhoValue, tag: &str, index: usize, from: &str, to: &str) {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            RhoValue::Map(values) => work.extend(values.values_mut()),
            RhoValue::List(values) => {
                if values.first() == Some(&RhoValue::String(tag.into())) {
                    if let Some(RhoValue::String(value)) = values.get_mut(index) {
                        rename_string(value, from, to);
                    }
                }
                work.extend(values.iter_mut());
            },
            _ => {},
        }
    }
}

fn rename_string(value: &mut String, from: &str, to: &str) {
    if value == from {
        *value = to.to_string();
    }
}

#[derive(Clone, Debug)]
enum ParameterDescriptor {
    Category(core::CategoryId),
    Identifier,
    Binder {
        category: core::CategoryId,
        multiple: bool,
    },
    Collection {
        key: Option<core::CategoryId>,
        element: core::CategoryId,
        kind: core::CollectionKind,
    },
    Guard,
}

fn add_token(
    declaration: &TokenDecl,
    mode: core::ModeId,
    mode_ids: &BTreeMap<String, core::ModeId>,
    categories: &BTreeMap<String, core::CategoryId>,
    output: &mut core::GrammarCoreV1,
    token_ids: &mut BTreeMap<String, core::TokenId>,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let qualified = if mode == core::ModeId(0) {
        declaration.name.clone()
    } else {
        format!("{}/{}", output.modes[mode.0 as usize].name, declaration.name)
    };
    if token_ids.contains_key(&qualified) {
        return error(path, format!("duplicate token name `{qualified}`"));
    }
    let category = declaration
        .category
        .as_ref()
        .map(|name| category_id(categories, name, &format!("{path}.category")))
        .transpose()?;
    let push = declaration
        .push
        .as_ref()
        .map(|name| {
            mode_ids.get(name).copied().ok_or_else(|| {
                ValueDecodeError::new(
                    format!("{path}.push"),
                    format!("unknown lexer mode `{name}`"),
                )
            })
        })
        .transpose()?;
    if let Some(evaluation) = &declaration.evaluation {
        register_evaluation_capability(evaluation, &mut output.capabilities);
    }
    let id = core::TokenId(output.tokens.len() as u32);
    output.tokens.push(core::TokenDefinition {
        id,
        name: qualified.clone(),
        pattern: core::TokenPattern::Regex(declaration.pattern.clone()),
        category,
        evaluation: declaration.evaluation.clone(),
        priority: declaration.priority,
        mode,
        channel: declaration.stream.clone().unwrap_or_else(|| "main".into()),
        transition: core::ModeTransition { push, pop: declaration.pop },
        decoder: if category.is_some() || declaration.evaluation.is_some() {
            core::TokenDecoder::Text
        } else {
            core::TokenDecoder::Unit
        },
        reservation: core::Reservation::None,
    });
    output.modes[mode.0 as usize].token_ids.push(id);
    token_ids.insert(qualified, id);
    if mode == core::ModeId(0) || !token_ids.contains_key(&declaration.name) {
        token_ids.insert(declaration.name.clone(), id);
    }
    Ok(())
}

fn register_evaluation_capability(
    evaluation: &core::NativeEvaluation,
    capabilities: &mut BTreeSet<core::Capability>,
) {
    if let core::NativeEvaluation::Handler(urn) = evaluation {
        capabilities.insert(core::Capability::NativeEvaluator(urn.clone()));
    }
}

fn category_id(
    categories: &BTreeMap<String, core::CategoryId>,
    name: &str,
    path: &str,
) -> Result<core::CategoryId, ValueDecodeError> {
    categories
        .get(name)
        .copied()
        .ok_or_else(|| ValueDecodeError::new(path, format!("unknown category `{name}`")))
}

fn collect_term_literals(body: &TermBody, output: &mut BTreeSet<String>) {
    match body {
        TermBody::Judgement(values) => {
            let mut work: Vec<_> = values.iter().rev().collect();
            while let Some(node) = work.pop() {
                match node {
                    SyntaxNode::Literal(value) => {
                        output.insert(value.clone());
                    },
                    SyntaxNode::Separated(source, _) => work.push(source),
                    SyntaxNode::Map { source, body, .. } => {
                        work.extend(body.iter().rev());
                        work.push(source);
                    },
                    SyntaxNode::Optional(values) => work.extend(values.iter().rev()),
                    SyntaxNode::Reference(_)
                    | SyntaxNode::Zip(_, _)
                    | SyntaxNode::Token { .. }
                    | SyntaxNode::ForeignLanguage { .. } => {},
                }
            }
        },
        TermBody::Bnf(values) => {
            for value in values {
                if let BnfNode::Literal(value) = value {
                    output.insert(value.clone());
                }
            }
        },
    }
}

fn parameter_descriptors(
    params: &[Param],
    categories: &BTreeMap<String, core::CategoryId>,
    path: &str,
) -> Result<BTreeMap<String, ParameterDescriptor>, ValueDecodeError> {
    let mut output = BTreeMap::new();
    let mut work: Vec<_> = params.iter().rev().collect();
    while let Some(param) = work.pop() {
        let mut insert = |name: &str, descriptor| {
            if output.insert(name.to_string(), descriptor).is_some() {
                error(path, format!("duplicate parameter `{name}`"))
            } else {
                Ok(())
            }
        };
        match param {
            Param::Plain { name, ty } => insert(name, descriptor_for_type(ty, categories, path)?),
            Param::Binder { binder, body, ty, multiple } => {
                let (from, to) = arrow_categories(ty, categories, path)?;
                insert(
                    binder,
                    ParameterDescriptor::Binder { category: from, multiple: *multiple },
                )?;
                insert(body, ParameterDescriptor::Category(to))
            },
            Param::Guard(name) => insert(name, ParameterDescriptor::Guard),
            Param::Optional(params) => {
                work.extend(params.iter().rev());
                Ok(())
            },
        }?;
    }
    Ok(output)
}

fn descriptor_for_type(
    ty: &TypeExpr,
    categories: &BTreeMap<String, core::CategoryId>,
    path: &str,
) -> Result<ParameterDescriptor, ValueDecodeError> {
    match ty {
        TypeExpr::Base(name) => {
            Ok(ParameterDescriptor::Category(category_id(categories, name, path)?))
        },
        TypeExpr::Multi(element) => Ok(ParameterDescriptor::Collection {
            key: None,
            element: type_base_category(element, categories, path)?,
            kind: core::CollectionKind::List,
        }),
        TypeExpr::Collection(kind, key, value) => Ok(ParameterDescriptor::Collection {
            key: value
                .as_ref()
                .map(|_| type_base_category(key, categories, path))
                .transpose()?,
            element: type_base_category(value.as_deref().unwrap_or(key), categories, path)?,
            kind: *kind,
        }),
        TypeExpr::Arrow(_, _) => Ok(ParameterDescriptor::Identifier),
    }
}

fn arrow_categories(
    ty: &TypeExpr,
    categories: &BTreeMap<String, core::CategoryId>,
    path: &str,
) -> Result<(core::CategoryId, core::CategoryId), ValueDecodeError> {
    let TypeExpr::Arrow(from, to) = ty else {
        return error(path, "binder parameter requires an arrow type");
    };
    Ok((
        type_base_category(from, categories, path)?,
        type_base_category(to, categories, path)?,
    ))
}

fn type_base_category(
    ty: &TypeExpr,
    categories: &BTreeMap<String, core::CategoryId>,
    path: &str,
) -> Result<core::CategoryId, ValueDecodeError> {
    let mut current = ty;
    loop {
        current = match current {
            TypeExpr::Base(name) => return category_id(categories, name, path),
            TypeExpr::Multi(value) | TypeExpr::Collection(_, value, None) => value,
            TypeExpr::Collection(_, _, Some(value)) | TypeExpr::Arrow(_, value) => value,
        };
    }
}

fn lower_term_body(
    body: &TermBody,
    descriptors: &BTreeMap<String, ParameterDescriptor>,
    categories: &BTreeMap<String, core::CategoryId>,
    tokens: &BTreeMap<String, core::TokenId>,
    literals: &BTreeMap<String, core::TokenId>,
    identifier_token: core::TokenId,
    path: &str,
) -> Result<Vec<core::SyntaxItem>, ValueDecodeError> {
    match body {
        TermBody::Judgement(values) => values
            .iter()
            .enumerate()
            .map(|(index, value)| {
                lower_syntax_node(
                    value,
                    descriptors,
                    tokens,
                    literals,
                    identifier_token,
                    &format!("{path}.syntax[{index}]"),
                )
            })
            .collect(),
        TermBody::Bnf(values) => values
            .iter()
            .enumerate()
            .map(|(index, value)| {
                let item_path = format!("{path}.items[{index}]");
                Ok(match value {
                    BnfNode::Literal(value) => {
                        core::SyntaxItem::Token(*literals.get(value).ok_or_else(|| {
                            ValueDecodeError::new(
                                &item_path,
                                format!("missing terminal token `{value}`"),
                            )
                        })?)
                    },
                    BnfNode::Nonterminal(name) => core::SyntaxItem::Category {
                        category: category_id(categories, name, &item_path)?,
                        slot: format!("nt{index}"),
                    },
                    BnfNode::Binding(name) => core::SyntaxItem::CaptureToken {
                        token: identifier_token,
                        slot: name.clone(),
                    },
                    BnfNode::Collection { kind, element, separator, open, close } => {
                        let body = core::SyntaxItem::Collection {
                            slot: format!("collection{index}"),
                            key: matches!(
                                kind,
                                core::CollectionKind::Map | core::CollectionKind::PathMap
                            )
                            .then(|| category_id(categories, element, &item_path))
                            .transpose()?,
                            element: category_id(categories, element, &item_path)?,
                            separator: separator.clone(),
                            kind: *kind,
                            key_value_separator: matches!(
                                kind,
                                core::CollectionKind::Map | core::CollectionKind::PathMap
                            )
                            .then(|| ":".to_string()),
                        };
                        let mut sequence = Vec::new();
                        if let Some(open) = open {
                            sequence.push(core::SyntaxItem::Token(
                                *literals.get(open).ok_or_else(|| {
                                    ValueDecodeError::new(
                                        &item_path,
                                        format!("missing terminal token `{open}`"),
                                    )
                                })?,
                            ));
                        }
                        sequence.push(body);
                        if let Some(close) = close {
                            sequence.push(core::SyntaxItem::Token(
                                *literals.get(close).ok_or_else(|| {
                                    ValueDecodeError::new(
                                        &item_path,
                                        format!("missing terminal token `{close}`"),
                                    )
                                })?,
                            ));
                        }
                        core::SyntaxItem::Sequence(sequence)
                    },
                })
            })
            .collect(),
    }
}

fn lower_syntax_node(
    node: &SyntaxNode,
    descriptors: &BTreeMap<String, ParameterDescriptor>,
    tokens: &BTreeMap<String, core::TokenId>,
    literals: &BTreeMap<String, core::TokenId>,
    identifier_token: core::TokenId,
    path: &str,
) -> Result<core::SyntaxItem, ValueDecodeError> {
    enum Task<'a> {
        Visit {
            node: &'a SyntaxNode,
            descriptors: std::sync::Arc<BTreeMap<String, ParameterDescriptor>>,
        },
        FinishSeparated(String),
        FinishMapped {
            bindings: Vec<String>,
            body_count: usize,
        },
        FinishOptional(usize),
    }

    let descriptors = std::sync::Arc::new(descriptors.clone());
    let mut tasks = vec![Task::Visit { node, descriptors }];
    let mut output = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit {
                node: SyntaxNode::Reference(name),
                descriptors,
            } => {
                output.push(match descriptors.get(name) {
                    Some(ParameterDescriptor::Category(category)) => {
                        core::SyntaxItem::Category { category: *category, slot: name.clone() }
                    },
                    Some(ParameterDescriptor::Identifier) => core::SyntaxItem::CaptureToken {
                        token: identifier_token,
                        slot: name.clone(),
                    },
                    Some(ParameterDescriptor::Binder { category, multiple }) => {
                        core::SyntaxItem::Binder {
                            slot: name.clone(),
                            category: *category,
                            multiple: *multiple,
                        }
                    },
                    Some(ParameterDescriptor::Collection { key, element, kind }) => {
                        core::SyntaxItem::Collection {
                            slot: name.clone(),
                            key: *key,
                            element: *element,
                            separator: String::new(),
                            kind: *kind,
                            key_value_separator: key.map(|_| ":".to_string()),
                        }
                    },
                    Some(ParameterDescriptor::Guard) => {
                        core::SyntaxItem::Guard { slot: name.clone() }
                    },
                    None => return error(path, format!("unknown parameter `{name}`")),
                });
            },
            Task::Visit { node: SyntaxNode::Literal(value), .. } => {
                output.push(core::SyntaxItem::Token(*literals.get(value).ok_or_else(|| {
                    ValueDecodeError::new(path, format!("missing terminal token `{value}`"))
                })?));
            },
            Task::Visit {
                node: SyntaxNode::Separated(source, separator),
                descriptors,
            } => {
                tasks.push(Task::FinishSeparated(separator.clone()));
                tasks.push(Task::Visit { node: source, descriptors });
            },
            Task::Visit {
                node: SyntaxNode::Zip(left, right),
                descriptors,
            } => {
                output.push(core::SyntaxItem::Zip {
                    left_slot: left.clone(),
                    right_slot: right.clone(),
                    left_kind: source_collection_kind(left, &descriptors, path)?,
                    right_kind: source_collection_kind(right, &descriptors, path)?,
                    body: Vec::new(),
                });
            },
            Task::Visit {
                node: SyntaxNode::Map { source, bindings, body },
                descriptors,
            } => {
                let source_descriptors = mapped_source_descriptors(source, &descriptors, path)?;
                if source_descriptors.len() != bindings.len() {
                    return error(
                        path,
                        format!(
                            "mapped source has {} stream(s), but {} binding(s) were declared",
                            source_descriptors.len(),
                            bindings.len()
                        ),
                    );
                }
                let mut local = (*descriptors).clone();
                for (binding, descriptor) in bindings.iter().zip(source_descriptors) {
                    if local.insert(binding.clone(), descriptor).is_some() {
                        return error(
                            path,
                            format!("mapped binding `{binding}` shadows a parameter"),
                        );
                    }
                }
                let local = std::sync::Arc::new(local);
                tasks.push(Task::FinishMapped {
                    bindings: bindings.clone(),
                    body_count: body.len(),
                });
                for node in body.iter().rev() {
                    tasks.push(Task::Visit { node, descriptors: local.clone() });
                }
                tasks.push(Task::Visit { node: source, descriptors });
            },
            Task::Visit {
                node: SyntaxNode::Optional(body),
                descriptors,
            } => {
                tasks.push(Task::FinishOptional(body.len()));
                for node in body.iter().rev() {
                    tasks.push(Task::Visit { node, descriptors: descriptors.clone() });
                }
            },
            Task::Visit {
                node: SyntaxNode::Token { name, binding },
                ..
            } => {
                let token = *tokens.get(name).ok_or_else(|| {
                    ValueDecodeError::new(path, format!("unknown token kind `{name}`"))
                })?;
                output.push(match binding {
                    Some(slot) => core::SyntaxItem::CaptureToken { token, slot: slot.clone() },
                    None => core::SyntaxItem::Token(token),
                });
            },
            Task::Visit {
                node: SyntaxNode::ForeignLanguage { binding, open, close },
                ..
            } => output.push(core::SyntaxItem::ForeignLanguage {
                slot: binding.clone(),
                open: open.clone(),
                close: close.clone(),
            }),
            Task::FinishSeparated(separator) => {
                let source = output.pop().expect("separated source is scheduled");
                output.push(core::SyntaxItem::Separated { source: Box::new(source), separator });
            },
            Task::FinishMapped { bindings, body_count } => {
                let body_start = output.len() - body_count;
                let body = output.drain(body_start..).collect();
                let source = output.pop().expect("mapped source is scheduled");
                output.push(core::SyntaxItem::Mapped { source: Box::new(source), bindings, body });
            },
            Task::FinishOptional(count) => {
                let start = output.len() - count;
                let body = output.drain(start..).collect();
                output.push(core::SyntaxItem::Optional(body));
            },
        }
    }
    Ok(output.pop().expect("syntax lowering produces one item"))
}

fn mapped_source_descriptors(
    source: &SyntaxNode,
    descriptors: &BTreeMap<String, ParameterDescriptor>,
    path: &str,
) -> Result<Vec<ParameterDescriptor>, ValueDecodeError> {
    fn element_descriptor(
        name: &str,
        descriptors: &BTreeMap<String, ParameterDescriptor>,
        path: &str,
    ) -> Result<ParameterDescriptor, ValueDecodeError> {
        match descriptors.get(name) {
            Some(ParameterDescriptor::Collection { element, .. }) => {
                Ok(ParameterDescriptor::Category(*element))
            },
            Some(ParameterDescriptor::Binder { category, multiple: true }) => {
                Ok(ParameterDescriptor::Binder { category: *category, multiple: false })
            },
            Some(_) => error(path, format!("mapped source `{name}` is not a collection")),
            None => error(path, format!("unknown mapped source `{name}`")),
        }
    }

    match source {
        SyntaxNode::Reference(name) => Ok(vec![element_descriptor(name, descriptors, path)?]),
        SyntaxNode::Zip(left, right) => Ok(vec![
            element_descriptor(left, descriptors, path)?,
            element_descriptor(right, descriptors, path)?,
        ]),
        _ => error(path, "map source must be a collection reference or zip"),
    }
}

fn source_collection_kind(
    name: &str,
    descriptors: &BTreeMap<String, ParameterDescriptor>,
    path: &str,
) -> Result<core::CollectionKind, ValueDecodeError> {
    match descriptors.get(name) {
        Some(ParameterDescriptor::Collection { kind, .. }) => Ok(*kind),
        Some(ParameterDescriptor::Binder { multiple: true, .. }) => Ok(core::CollectionKind::List),
        Some(_) => error(path, format!("mapped source `{name}` is not a collection")),
        None => error(path, format!("unknown mapped source `{name}`")),
    }
}

fn collect_core_slots(items: &[core::SyntaxItem]) -> Vec<&str> {
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

fn classify_production(items: &[core::SyntaxItem], params: &[Param]) -> core::ProductionClass {
    let is_category = |item: &core::SyntaxItem| {
        matches!(
            item,
            core::SyntaxItem::Category { .. }
                | core::SyntaxItem::Collection { .. }
                | core::SyntaxItem::Binder { .. }
        )
    };
    let is_token = |item: &core::SyntaxItem| matches!(item, core::SyntaxItem::Token(_));
    core::ProductionClass {
        infix: items.len() >= 3
            && items.first().is_some_and(is_category)
            && items.last().is_some_and(is_category)
            && items[1..items.len() - 1].iter().any(is_token),
        postfix: items.len() >= 2
            && items.first().is_some_and(is_category)
            && items.last().is_some_and(is_token),
        prefix: items.len() >= 2
            && items.first().is_some_and(is_token)
            && items.last().is_some_and(is_category),
        variable: items.len() == 1
            && matches!(
                items[0],
                core::SyntaxItem::CaptureIdent { .. } | core::SyntaxItem::CaptureToken { .. }
            ),
        literal: items.iter().all(is_token) && params.is_empty(),
        binder: params
            .iter()
            .any(|param| matches!(param, Param::Binder { .. })),
        collection: items
            .iter()
            .any(|item| matches!(item, core::SyntaxItem::Collection { .. })),
        ..core::ProductionClass::default()
    }
}

fn collect_constructor_references(
    value: &RhoValue,
    constructors: &BTreeMap<String, core::ConstructorId>,
    output: &mut BTreeSet<core::ConstructorId>,
) {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            RhoValue::Map(values) => work.extend(values.values()),
            RhoValue::List(values) => {
                if let Some(RhoValue::String(head)) = values.first() {
                    if let Some(constructor) = constructors.get(head) {
                        output.insert(*constructor);
                    }
                }
                work.extend(values.iter());
            },
            _ => {},
        }
    }
}

fn error<T>(path: impl Into<String>, message: impl Into<String>) -> Result<T, ValueDecodeError> {
    Err(ValueDecodeError::new(path, message))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical::{
        value_to_core, value_to_core_with_resolver, value_to_installable_language_core,
        value_to_installable_language_core_with_resolver, value_to_language_core,
        value_to_language_core_with_resolver, LanguageValueResolver,
    };

    fn s(value: &str) -> RhoValue {
        RhoValue::String(value.into())
    }

    fn l(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
        RhoValue::List(values.into_iter().collect())
    }

    fn m(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
        RhoValue::Map(
            values
                .into_iter()
                .map(|(key, value)| (key.into(), value))
                .collect(),
        )
    }

    fn term(label: &str, category: &str, terminal: &str) -> RhoValue {
        m([
            ("label", s(label)),
            ("category", s(category)),
            ("syntax", l([l([s("lit"), s(terminal)])])),
        ])
    }

    fn language(
        name: &str,
        fields: impl IntoIterator<Item = (&'static str, RhoValue)>,
    ) -> RhoValue {
        let mut values =
            BTreeMap::from([("mettail".into(), s("language/2")), ("name".into(), s(name))]);
        values.extend(fields.into_iter().map(|(key, value)| (key.into(), value)));
        RhoValue::Map(values)
    }

    fn language3(
        name: &str,
        fields: impl IntoIterator<Item = (&'static str, RhoValue)>,
    ) -> RhoValue {
        let mut value = language(name, fields);
        let RhoValue::Map(values) = &mut value else {
            unreachable!()
        };
        values.insert("mettail".into(), s("language/3"));
        value
    }

    #[test]
    fn exhaustive_language_value_lowers_every_top_level_channel() {
        let value = language(
            "Complete",
            [
                (
                    "options",
                    m([
                        ("beam_width", RhoValue::FloatBits(1.5f64.to_bits())),
                        ("log_semiring_model_path", s("model.json")),
                        ("dispatch", s("weighted")),
                        ("emit_tests", RhoValue::Boolean(false)),
                        ("emit_blockly", RhoValue::Boolean(false)),
                        ("emit_simulator", RhoValue::Boolean(false)),
                        ("parse_only", RhoValue::Boolean(false)),
                        ("case_insensitive", RhoValue::Boolean(false)),
                        ("unicode_normalization", s("NFC")),
                        ("reserved_keywords", s("auto")),
                    ]),
                ),
                ("semantics", s("Rust")),
                (
                    "types",
                    l([
                        s("Expr"),
                        m([("name", s("Int")), ("carrier", s("i64"))]),
                        m([
                            ("name", s("ExprList")),
                            ("carrier", l([s("vec"), s("Expr")])),
                            (
                                "collection",
                                m([
                                    ("kind", s("list")),
                                    ("open", s("[")),
                                    ("close", s("]")),
                                    ("sep", s(",")),
                                ]),
                            ),
                        ]),
                        m([
                            ("name", s("Positive")),
                            (
                                "refine",
                                m([
                                    ("var", s("x")),
                                    ("base", s("Int")),
                                    ("pred", l([s("cmp"), s("gt"), s("x"), RhoValue::Integer(0)])),
                                ]),
                            ),
                        ]),
                    ]),
                ),
                (
                    "literals",
                    l([m([
                        ("category", s("Int")),
                        ("pattern", s("[0-9]+")),
                        ("eval", l([s("carrier"), s("int"), m([])])),
                    ])]),
                ),
                (
                    "tokens",
                    l([m([
                        ("name", s("Named")),
                        ("pattern", s("[A-Za-z]+")),
                        ("category", s("Expr")),
                        ("eval", l([s("handler"), s("mtl:native:named")])),
                        ("priority", RhoValue::Integer(2)),
                        ("push", s("Quoted")),
                        ("stream", s("main")),
                    ])]),
                ),
                (
                    "modes",
                    l([m([
                        ("name", s("Quoted")),
                        ("raw", RhoValue::Boolean(true)),
                        (
                            "tokens",
                            l([m([
                                ("name", s("QuoteEnd")),
                                ("pattern", s("\\\"")),
                                ("pop", RhoValue::Boolean(true)),
                            ])]),
                        ),
                    ])]),
                ),
                ("sync", l([l([s("track"), s("aux"), s("main")])])),
                (
                    "tree_invariants",
                    l([m([
                        ("name", s("RootHolds")),
                        ("constraint", l([s("holds"), s("NodePred"), l([l([s("root")])])])),
                        ("doc", s("tree rule")),
                    ])]),
                ),
                (
                    "guards",
                    m([
                        (
                            "predicates",
                            l([m([
                                ("name", s("Ready")),
                                ("params", l([l([s("param"), s("x"), s("Expr")])])),
                                ("forms", l([l([l([s("lit"), s("ready")]), s("x")])])),
                                (
                                    "annotations",
                                    m([
                                        ("selectivity", RhoValue::FloatBits(0.25f64.to_bits())),
                                        ("cost", RhoValue::Integer(2)),
                                    ]),
                                ),
                            ])]),
                        ),
                        (
                            "connectives",
                            l([m([("role", s("conjunction")), ("keywords", l([s("and")]))])]),
                        ),
                        (
                            "theories",
                            l([m([
                                ("name", s("GuardTheory")),
                                ("theory", s("mtl:guard:default")),
                                ("for", l([s("Expr")])),
                            ])]),
                        ),
                        ("channels", m([("channel", l([s("Expr")]))])),
                    ]),
                ),
                (
                    "terms",
                    l([
                        term("Zero", "Expr", "0"),
                        m([
                            ("label", s("Plus")),
                            ("category", s("Expr")),
                            (
                                "context",
                                l([
                                    l([s("param"), s("left"), s("Expr")]),
                                    l([s("param"), s("right"), s("Expr")]),
                                ]),
                            ),
                            ("syntax", l([s("left"), l([s("lit"), s("+")]), s("right")])),
                            ("eval", l([s("op"), s("add")])),
                            ("mode", s("fold")),
                            ("assoc", s("left")),
                            ("tier", m([("tier", s("t1")), ("bound", RhoValue::Integer(8))])),
                        ]),
                    ]),
                ),
                (
                    "equations",
                    l([m([
                        ("name", s("ZeroRight")),
                        ("left", l([s("Plus"), s("x"), l([s("Zero")])])),
                        ("right", s("x")),
                    ])]),
                ),
                (
                    "rewrites",
                    l([m([
                        ("name", s("StepPlus")),
                        ("premises", l([l([s("~>"), s("x"), s("y")])])),
                        ("left", l([s("Plus"), s("x"), s("z")])),
                        ("right", l([s("Plus"), s("y"), s("z")])),
                    ])]),
                ),
                (
                    "relations",
                    l([m([
                        ("relation", s("Reachable")),
                        ("params", l([s("Expr"), s("Expr")])),
                        (
                            "rules",
                            l([m([
                                ("head", l([s("rel"), s("Reachable"), l([s("x"), s("x")])])),
                                ("body", l([l([s("guard"), l([s("true")])])])),
                            ])]),
                        ),
                    ])]),
                ),
                ("extends", l([])),
                ("includes", l([])),
                ("mixins", l([])),
                ("exports", l([l([s("Expr"), s("Term")])])),
                ("replacements", l([])),
                ("context", s("backend preamble")),
                ("doc", s("complete fixture")),
            ],
        );
        let core = value_to_core(&value).expect("exhaustive language lowers");
        assert!(core
            .categories
            .iter()
            .any(|category| category.name == "Term"));
        assert_eq!(core.semantic_program.relations.len(), 1);
        assert_eq!(core.tree_invariants.len(), 1);
        assert!(core.guard_configuration.is_some());
        assert_eq!(core.backend_context.as_deref(), Some("backend preamble"));
    }

    #[test]
    fn canonical_value_preserves_every_lossless_parser_profile_field() {
        let recovery = m([
            ("skip_per_token", RhoValue::FloatBits(0.1f64.to_bits())),
            ("delete_cost", RhoValue::FloatBits(0.2f64.to_bits())),
            ("substitute_cost", RhoValue::FloatBits(0.3f64.to_bits())),
            ("insert_cost", RhoValue::FloatBits(0.4f64.to_bits())),
            ("swap_cost", RhoValue::FloatBits(0.5f64.to_bits())),
            ("max_skip_lookahead", RhoValue::Integer(6)),
            ("deep_nesting_threshold", RhoValue::Integer(7)),
            ("deep_nesting_skip_mult", RhoValue::FloatBits(0.8f64.to_bits())),
            ("shallow_depth_threshold", RhoValue::Integer(9)),
            ("shallow_depth_skip_mult", RhoValue::FloatBits(1.0f64.to_bits())),
            ("low_bp_threshold", RhoValue::Integer(11)),
            ("low_bp_skip_mult", RhoValue::FloatBits(1.2f64.to_bits())),
            ("collection_insert_mult", RhoValue::FloatBits(1.3f64.to_bits())),
            ("group_insert_mult", RhoValue::FloatBits(1.4f64.to_bits())),
            ("bracket_insert_mult", RhoValue::FloatBits(1.5f64.to_bits())),
            ("mixfix_substitute_mult", RhoValue::FloatBits(1.6f64.to_bits())),
            ("simulation_valid_mult", RhoValue::FloatBits(1.7f64.to_bits())),
            ("simulation_fail_penalty", RhoValue::FloatBits(1.8f64.to_bits())),
            ("beam_width", RhoValue::FloatBits(1.9f64.to_bits())),
            ("cascade_window", RhoValue::Integer(20)),
            ("vpa_nesting_ceiling", RhoValue::Integer(21)),
            ("adaptive_weight_threshold", RhoValue::FloatBits(2.2f64.to_bits())),
            ("deterministic_skip_discount", RhoValue::FloatBits(2.3f64.to_bits())),
            ("ambiguous_insert_discount", RhoValue::FloatBits(2.4f64.to_bits())),
            ("max_recovery_depth", RhoValue::Integer(25)),
        ]);
        let value = language(
            "Lossless",
            [
                (
                    "options",
                    m([
                        ("reserved_keywords", s("auto")),
                        ("contextual_keywords", l([s("for"), s("in")])),
                        ("recovery", recovery),
                    ]),
                ),
                (
                    "types",
                    l([
                        m([("name", s("Closed")), ("admits_variables", RhoValue::Boolean(false))]),
                        m([("name", s("Open")), ("admits_variables", RhoValue::Boolean(true))]),
                    ]),
                ),
                (
                    "terms",
                    l([
                        term("First", "Closed", "a"),
                        m([
                            ("label", s("Second")),
                            ("category", s("Closed")),
                            ("syntax", l([l([s("lit"), s("b")])])),
                            ("shares_previous_level", RhoValue::Boolean(true)),
                        ]),
                    ]),
                ),
            ],
        );
        let core = value_to_core(&value).expect("lossless parser profile lowers");
        assert!(!core.categories[0].admits_variables);
        assert!(core.categories[1].admits_variables);
        assert!(!core.productions[0].precedence.shares_previous_level);
        assert!(core.productions[1].precedence.shares_previous_level);
        assert_eq!(
            core.parser_configuration.reservation,
            core::KeywordReservation::Auto {
                contextual: BTreeSet::from(["for".into(), "in".into()]),
            },
        );
        assert_eq!(
            core.parser_configuration.recovery,
            core::RecoveryConfiguration {
                skip_per_token: 0.1,
                delete_cost: 0.2,
                substitute_cost: 0.3,
                insert_cost: 0.4,
                swap_cost: 0.5,
                max_skip_lookahead: 6,
                deep_nesting_threshold: 7,
                deep_nesting_skip_mult: 0.8,
                shallow_depth_threshold: 9,
                shallow_depth_skip_mult: 1.0,
                low_bp_threshold: 11,
                low_bp_skip_mult: 1.2,
                collection_insert_mult: 1.3,
                group_insert_mult: 1.4,
                bracket_insert_mult: 1.5,
                mixfix_substitute_mult: 1.6,
                simulation_valid_mult: 1.7,
                simulation_fail_penalty: 1.8,
                beam_width: Some(1.9),
                cascade_window: 20,
                vpa_nesting_ceiling: Some(21),
                adaptive_weight_threshold: 2.2,
                deterministic_skip_discount: 2.3,
                ambiguous_insert_discount: 2.4,
                max_recovery_depth: 25,
            },
        );
    }

    #[test]
    fn parser_profile_rejects_unscoped_contextual_keywords_and_negative_costs() {
        let contextual = language(
            "BadContextual",
            [(
                "options",
                m([("reserved_keywords", s("none")), ("contextual_keywords", l([s("for")]))]),
            )],
        );
        let error = value_to_core(&contextual).expect_err("contextual exception must be scoped");
        assert!(format!("{error:?}").contains("require `reserved_keywords: auto`"));

        let negative = language(
            "BadRecovery",
            [(
                "options",
                m([("recovery", m([("delete_cost", RhoValue::FloatBits((-1.0f64).to_bits()))]))]),
            )],
        );
        let error = value_to_core(&negative).expect_err("negative recovery cost must fail");
        assert!(format!("{error:?}").contains("finite nonnegative float"));
    }

    #[test]
    fn language3_lowers_complete_oslf_structure_to_a_flat_language_core() {
        let oslf = m([
            ("effects", l([m([("name", s("Pure")), ("requires", l([])), ("emits", l([]))])])),
            (
                "actions",
                l([m([
                    ("id", s("step")),
                    ("domain", l([s("Datum")])),
                    ("codomain", s("Datum")),
                    ("transition", l([s("handler"), s("mtl:handler:step/1")])),
                    ("effect", s("Pure")),
                    ("grade", s("Sig")),
                    ("execution", s("one_step")),
                ])]),
            ),
            (
                "judgments",
                l([m([
                    ("name", s("Admits")),
                    ("arguments", l([s("Datum")])),
                    ("decision", s("bounded")),
                    (
                        "rules",
                        l([m([
                            ("name", s("AdmitsCtor")),
                            ("premises", l([])),
                            (
                                "conclusion",
                                m([
                                    ("judgment", s("Admits")),
                                    (
                                        "terms",
                                        l([l([s("ctor"), s("Wrap"), l([l([s("var"), s("x")])])])]),
                                    ),
                                ]),
                            ),
                        ])]),
                    ),
                ])]),
            ),
            (
                "observations",
                l([m([("name", s("StepResult")), ("action", s("step")), ("result", s("Datum"))])]),
            ),
            (
                "morphisms",
                l([m([
                    ("name", s("Identity")),
                    ("source", s("G")),
                    ("target", s("G")),
                    ("categories", l([l([s("Datum"), s("Datum")])])),
                    ("constructors", l([])),
                    ("actions", l([l([s("step"), s("step")])])),
                    ("grades", l([l([s("Sig"), s("Sig")])])),
                ])]),
            ),
            (
                "interactive",
                m([
                    ("cut", s("cut")),
                    ("channel_sort", s("Channel")),
                    ("datum_sort", s("Datum")),
                    ("continuation_sort", s("Kont")),
                ]),
            ),
            (
                "continued",
                m([
                    ("k", s("K")),
                    ("kp", s("Kp")),
                    ("ke", s("Ke")),
                    ("k_prime", s("KPrime")),
                    ("near", s("near")),
                    ("compute", s("compute")),
                    ("section", s("section")),
                    ("wrappability", s("mtl:proof:wrappable/1")),
                    ("quote_faithfulness", s("mtl:proof:quote-faithful/1")),
                ]),
            ),
            (
                "cost",
                m([
                    ("base", s("G")),
                    ("signature_sort", s("Sig")),
                    ("stack_sort", s("Stack")),
                    ("wrapped_sort", s("Wrapped")),
                    ("located_sort", s("Located")),
                    ("product", s("product")),
                    ("unit", s("unit")),
                    ("rules", l([s("R1"), s("R2"), s("R3")])),
                    ("eta", s("eta")),
                    ("mu", s("mu")),
                    ("map", s("map")),
                    ("laws", l([s("left-unit"), s("right-unit"), s("associative")])),
                ]),
            ),
            (
                "resource_projection",
                m([
                    ("abi", s("mtl:projection/1")),
                    ("grade_sort", s("Sig")),
                    ("demand_sort", s("Demand")),
                    ("project", s("mtl:project:grade-demand/1")),
                    ("proof", s("mtl:proof:conservative/1")),
                ]),
            ),
            (
                "checkers",
                l([m([
                    ("abi", s("mtl:checker:oslf/1")),
                    ("limit_profile", s("mtl:limits:oslf/1")),
                ])]),
            ),
            (
                "limits",
                m([
                    ("max_term_nodes", RhoValue::Integer(128)),
                    ("max_proof_nodes", RhoValue::Integer(256)),
                    ("max_frontier", RhoValue::Integer(32)),
                    ("max_steps", RhoValue::Integer(1024)),
                    ("max_grade_bits", RhoValue::Integer(64)),
                ]),
            ),
        ]);
        let value = language3(
            "OslfGuest",
            [
                (
                    "types",
                    l([
                        s("Channel"),
                        s("Datum"),
                        s("Kont"),
                        s("Demand"),
                        s("Sig"),
                        s("Stack"),
                        s("Wrapped"),
                        s("Located"),
                    ]),
                ),
                (
                    "terms",
                    l([m([
                        ("label", s("Wrap")),
                        ("category", s("Datum")),
                        ("context", l([l([s("param"), s("x"), s("Datum")])])),
                        ("syntax", l([s("x")])),
                    ])]),
                ),
                ("oslf", oslf),
            ],
        );
        let language = value_to_language_core(&value).expect("complete language/3 lowers");
        assert_eq!(language.theory.profile, core::TheoryProfileV1::Oslf);
        assert_eq!(language.theory.actions.len(), 1);
        assert_eq!(language.theory.judgments.len(), 1);
        let rule = &language.theory.judgments[0].rules[0];
        assert_eq!(rule.terms.len(), 2);
        assert!(matches!(
            rule.terms[1].form,
            core::TheoryTermFormV1::Constructor { ref arguments, .. }
                if arguments == &[core::TheoryTermId(0)]
        ));
        assert!(language.theory.interactive.is_some());
        assert!(language.theory.continued.is_some());
        assert!(language.theory.cost.is_some());
        assert!(language.theory.resource_projection.is_some());
        assert_ne!(language.grammar_fingerprint().unwrap(), language.theory_fingerprint().unwrap());
    }

    #[test]
    fn language_schema_versions_and_oslf_presence_fail_closed() {
        let language2_with_oslf = language("BadV2", [("oslf", m([]))]);
        let error = value_to_language_core(&language2_with_oslf)
            .expect_err("language/2 must reject OSLF data");
        assert!(format!("{error:?}").contains("requires the `language/3` schema"));

        let cost_without_continuation = language3(
            "BadCost",
            [(
                "oslf",
                m([(
                    "cost",
                    m([
                        ("base", s("G")),
                        ("signature_sort", s("Sig")),
                        ("stack_sort", s("Stack")),
                        ("wrapped_sort", s("Wrapped")),
                        ("located_sort", s("Located")),
                        ("product", s("product")),
                        ("unit", s("unit")),
                        ("rules", l([])),
                        ("eta", s("eta")),
                        ("mu", s("mu")),
                        ("map", s("map")),
                        ("laws", l([])),
                    ]),
                )]),
            )],
        );
        let error = value_to_language_core(&cost_without_continuation)
            .expect_err("Cost(G) without continued structure must fail");
        assert!(format!("{error:?}").contains("CostRequiresContinued"));

        let untyped_relation = language3(
            "UntypedRelation",
            [(
                "relations",
                l([m([
                    ("relation", s("Reachable")),
                    ("params", l([s("left"), s("right")])),
                    ("rules", l([])),
                ])]),
            )],
        );
        let error = value_to_language_core(&untyped_relation).expect_err(
            "language/3 must not guess sorts or a decision policy for legacy relations",
        );
        assert!(format!("{error:?}").contains("typed `oslf.judgments`"));
    }

    #[test]
    fn beam_width_does_not_widen_an_integer_to_float() {
        let value = language(
            "NumericKinds",
            [
                ("options", m([("beam_width", RhoValue::Integer(2))])),
                ("types", l([s("Expr")])),
            ],
        );
        let error = value_to_core(&value).expect_err("integer beam width must fail");
        assert!(format!("{error:?}").contains("expected a finite float"));
    }

    #[test]
    fn requested_rights_are_canonical_security_requests() {
        let omitted = language("Rights", [("types", l([s("Expr")]))]);
        let explicit_default = language(
            "Rights",
            [
                (
                    "rights",
                    l([
                        s("Reduce"),
                        s("Parse"),
                        s("ReflectAst"),
                        s("Construct"),
                        s("Observe"),
                        s("Match"),
                    ]),
                ),
                ("types", l([s("Expr")])),
            ],
        );
        let omitted_install =
            value_to_installable_language_core(&omitted).expect("default rights lower");
        let explicit_install =
            value_to_installable_language_core(&explicit_default).expect("explicit rights lower");
        assert_eq!(omitted_install.requested_rights, core::LanguageRights::native_flt_default());
        assert_eq!(omitted_install.requested_rights, explicit_install.requested_rights);
        assert_eq!(omitted_install.language, explicit_install.language);
        assert_eq!(
            omitted_install.language.grammar_fingerprint().unwrap(),
            explicit_install.language.grammar_fingerprint().unwrap()
        );

        let no_rights = value_to_installable_language_core(&language(
            "Rights",
            [("rights", l([])), ("types", l([s("Expr")]))],
        ))
        .expect("an explicit empty request is valid");
        assert_eq!(no_rights.requested_rights, core::LanguageRights::none());
        assert_eq!(no_rights.language, omitted_install.language);
    }

    #[test]
    fn requested_rights_reject_unknown_and_duplicate_names() {
        for rights in [l([s("Execute")]), l([s("Parse"), s("Parse")])] {
            let error = value_to_core(&language("BadRights", [("rights", rights)]))
                .expect_err("invalid right declaration must fail closed");
            assert!(format!("{error:?}").contains("language right"));
        }
    }

    #[test]
    fn nested_model_defaults_do_not_split_language_identity() {
        let omitted = language(
            "Defaults",
            [("types", l([s("Expr")])), ("terms", l([term("Zero", "Expr", "0")]))],
        );
        let explicit = language(
            "Defaults",
            [
                ("types", l([s("Expr")])),
                (
                    "terms",
                    l([m([
                        ("label", s("Zero")),
                        ("category", s("Expr")),
                        ("context", l([])),
                        ("syntax", l([l([s("lit"), s("0")])])),
                        ("assoc", s("left")),
                    ])]),
                ),
            ],
        );
        let omitted = value_to_core(&omitted).expect("omitted defaults lower");
        let explicit = value_to_core(&explicit).expect("explicit defaults lower");
        assert_eq!(omitted, explicit);
        assert_eq!(omitted.fingerprint().unwrap(), explicit.fingerprint().unwrap());
    }

    #[derive(Default)]
    struct Values(BTreeMap<String, RhoValue>);

    impl LanguageValueResolver for Values {
        fn resolve_language(&self, name: &str) -> Result<Option<RhoValue>, String> {
            Ok(self.0.get(name).cloned())
        }
    }

    #[test]
    fn registry_composition_is_ordered_and_local_includes_override() {
        let base = language(
            "Base",
            [
                ("types", l([s("Expr")])),
                ("terms", l([term("Value", "Expr", "base"), term("Inherited", "Expr", "i")])),
            ],
        );
        let local = language(
            "Local",
            [
                ("includes", l([s("Base")])),
                ("types", l([s("Expr")])),
                ("terms", l([term("Value", "Expr", "local"), term("Own", "Expr", "o")])),
            ],
        );
        let resolver = Values(BTreeMap::from([("Base".into(), base)]));
        let core = value_to_core_with_resolver(&local, &resolver).expect("composition lowers");
        let labels: Vec<_> = core
            .productions
            .iter()
            .map(|production| production.label.as_str())
            .collect();
        assert_eq!(labels, ["Inherited", "Value", "Own"]);
        let value_rule = core
            .productions
            .iter()
            .find(|production| production.label == "Value")
            .unwrap();
        let core::SyntaxItem::Token(token) = value_rule.syntax[0] else {
            panic!("literal token")
        };
        assert!(
            matches!(&core.tokens[token.0 as usize].pattern, core::TokenPattern::Literal(text) if text == "local")
        );
    }

    #[test]
    fn registry_composition_unions_default_and_explicit_right_requests() {
        let base = language("Base", [("types", l([s("Expr")]))]);
        let local = language(
            "Local",
            [
                ("includes", l([s("Base")])),
                ("rights", l([s("Bridge")])),
                ("types", l([s("Expr")])),
            ],
        );
        let resolver = Values(BTreeMap::from([("Base".into(), base)]));
        let install = value_to_installable_language_core_with_resolver(&local, &resolver)
            .expect("composition lowers");
        assert!(install
            .requested_rights
            .contains(core::LanguageRight::Parse));
        assert!(install
            .requested_rights
            .contains(core::LanguageRight::Bridge));
        assert!(!install
            .requested_rights
            .contains(core::LanguageRight::Publish));
    }

    #[test]
    fn registry_mixins_preserve_the_complete_lexer_fragment_without_authority_or_semantics() {
        let fragment = language(
            "LexicalFragment",
            [
                ("rights", l([s("Publish")])),
                ("types", l([s("Expr")])),
                (
                    "literals",
                    l([m([
                        ("category", s("Expr")),
                        ("pattern", s("[0-9]+")),
                        ("eval", l([s("handler"), s("mtl:test:literal/1")])),
                    ])]),
                ),
                (
                    "tokens",
                    l([m([
                        ("name", s("Word")),
                        ("pattern", s("[a-z]+")),
                        ("category", s("Expr")),
                    ])]),
                ),
                (
                    "modes",
                    l([m([
                        ("name", s("Quoted")),
                        ("raw", RhoValue::Boolean(true)),
                        ("tokens", l([m([("name", s("QuoteEnd")), ("pattern", s("x"))])])),
                    ])]),
                ),
                ("terms", l([term("Zero", "Expr", "0")])),
                (
                    "equations",
                    l([m([
                        ("name", s("IdEquation")),
                        ("left", l([s("Zero")])),
                        ("right", l([s("Zero")])),
                    ])]),
                ),
                (
                    "rewrites",
                    l([m([
                        ("name", s("IdRewrite")),
                        ("left", l([s("Zero")])),
                        ("right", l([s("Zero")])),
                    ])]),
                ),
            ],
        );
        let local = language("Local", [("mixins", l([s("LexicalFragment")]))]);
        let resolver = Values(BTreeMap::from([("LexicalFragment".into(), fragment)]));

        let install = value_to_installable_language_core_with_resolver(&local, &resolver)
            .expect("the complete grammar fragment must survive runtime mixin projection");
        let core = &install.language.grammar;
        assert!(core
            .categories
            .iter()
            .any(|category| category.name == "Expr"));
        assert!(core
            .productions
            .iter()
            .any(|production| production.label == "Zero"));
        assert!(core
            .modes
            .iter()
            .any(|mode| mode.name == "Quoted" && mode.raw));
        for token in ["Word", "Quoted/QuoteEnd", "literal/Expr/0"] {
            assert!(
                core.tokens
                    .iter()
                    .any(|definition| definition.name == token),
                "mixin token `{token}` was discarded",
            );
        }
        assert_eq!(core.semantic_program.equations, Vec::new());
        assert_eq!(core.semantic_program.rewrites, Vec::new());
        assert!(install
            .requested_rights
            .contains(core::LanguageRight::Parse));
        assert!(!install
            .requested_rights
            .contains(core::LanguageRight::Publish));
    }

    #[test]
    fn registry_extends_composes_oslf_while_includes_remains_grammar_only() {
        let base = language3(
            "SemanticBase",
            [
                ("types", l([s("Datum"), s("Grade")])),
                (
                    "oslf",
                    m([
                        (
                            "effects",
                            l([m([("name", s("Pure")), ("requires", l([])), ("emits", l([]))])]),
                        ),
                        (
                            "actions",
                            l([m([
                                ("id", s("step")),
                                ("domain", l([s("Datum")])),
                                ("codomain", s("Datum")),
                                ("transition", l([s("handler"), s("mtl:step/1")])),
                                ("effect", s("Pure")),
                                ("grade", s("Grade")),
                                ("execution", s("one_step")),
                            ])]),
                        ),
                        ("limits", m([("max_steps", RhoValue::Integer(100))])),
                    ]),
                ),
            ],
        );
        let derived = language3(
            "Derived",
            [
                ("extends", l([s("SemanticBase")])),
                (
                    "oslf",
                    m([
                        (
                            "observations",
                            l([m([
                                ("name", s("Result")),
                                ("action", s("step")),
                                ("result", s("Datum")),
                            ])]),
                        ),
                        ("limits", m([("max_steps", RhoValue::Integer(50))])),
                    ]),
                ),
            ],
        );
        let resolver = Values(BTreeMap::from([("SemanticBase".into(), base.clone())]));
        let derived_core = value_to_language_core_with_resolver(&derived, &resolver)
            .expect("extends composes syntax and OSLF structure");
        assert_eq!(derived_core.theory.profile, core::TheoryProfileV1::Oslf);
        assert_eq!(derived_core.theory.actions.len(), 1);
        assert_eq!(derived_core.theory.observations.len(), 1);
        assert_eq!(derived_core.theory.limits.max_steps, 50);

        let grammar_only = language("GrammarOnly", [("includes", l([s("SemanticBase")]))]);
        let language = value_to_language_core_with_resolver(&grammar_only, &resolver)
            .expect("includes imports grammar without semantic authority");
        assert_eq!(language.theory, core::TheoryCoreV1::structural());
        assert!(language
            .grammar
            .categories
            .iter()
            .any(|category| category.name == "Datum"));
    }

    #[test]
    fn registry_composition_cycles_are_rejected() {
        let a = language("A", [("extends", l([s("B")]))]);
        let b = language("B", [("extends", l([s("A")]))]);
        let resolver = Values(BTreeMap::from([("A".into(), a.clone()), ("B".into(), b)]));
        let error = value_to_core_with_resolver(&a, &resolver).expect_err("cycle must fail");
        assert!(format!("{error:?}").contains("A -> B -> A"));
    }

    struct ChainResolver {
        length: usize,
    }

    impl LanguageValueResolver for ChainResolver {
        fn resolve_language(&self, name: &str) -> Result<Option<RhoValue>, String> {
            let Some(index) = name
                .strip_prefix('L')
                .and_then(|value| value.parse::<usize>().ok())
            else {
                return Ok(None);
            };
            if index >= self.length {
                return Ok(None);
            }
            Ok(Some(if index + 1 == self.length {
                language(name, [("types", l([s("Expr")]))])
            } else {
                language(name, [("extends", l([s(&format!("L{}", index + 1))]))])
            }))
        }
    }

    fn compose_chain_on_small_stack(
        length: usize,
    ) -> Result<core::GrammarCoreV1, crate::canonical::ValueToCoreError> {
        std::thread::Builder::new()
            .name("mettail-composition-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(move || {
                let resolver = ChainResolver { length };
                let root = resolver
                    .resolve_language("L0")
                    .expect("resolver succeeds")
                    .expect("root exists");
                value_to_core_with_resolver(&root, &resolver)
            })
            .expect("spawn composition worker")
            .join()
            .expect("composition worker must not overflow or panic")
    }

    #[test]
    fn registry_composition_machine_is_bounded_and_stack_independent() {
        let core = compose_chain_on_small_stack(MAX_COMPOSED_LANGUAGES)
            .expect("chain at the admission bound lowers");
        assert!(core
            .categories
            .iter()
            .any(|category| category.name == "Expr"));

        let error = compose_chain_on_small_stack(20_000)
            .expect_err("overlong acyclic composition must fail closed");
        assert!(format!("{error:?}").contains("composition exceeds"));
    }

    #[test]
    fn deeply_nested_admitted_schema_lowers_on_a_small_stack() {
        std::thread::Builder::new()
            .name("mettail-schema-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut syntax = l([s("lit"), s("x")]);
                for _ in 0..100 {
                    syntax = l([s("opt"), l([syntax])]);
                }
                let syntax_language = language(
                    "NestedSyntax",
                    [
                        ("types", l([s("Expr")])),
                        (
                            "terms",
                            l([m([
                                ("label", s("Nested")),
                                ("category", s("Expr")),
                                ("context", l([])),
                                ("syntax", l([syntax])),
                            ])]),
                        ),
                    ],
                );
                let syntax_core = value_to_core(&syntax_language).expect("nested syntax lowers");
                drop(syntax_core);

                let mut ty = s("Expr");
                for _ in 0..200 {
                    ty = l([s("multi"), ty]);
                }
                let type_language = language(
                    "NestedType",
                    [
                        ("types", l([s("Expr")])),
                        (
                            "terms",
                            l([m([
                                ("label", s("Nested")),
                                ("category", s("Expr")),
                                ("context", l([l([s("param"), s("x"), ty])])),
                                ("syntax", l([s("x")])),
                            ])]),
                        ),
                    ],
                );
                let type_core = value_to_core(&type_language).expect("nested type lowers");
                drop(type_core);
            })
            .expect("spawn schema worker")
            .join()
            .expect("schema lowering must not overflow or panic");
    }
}
