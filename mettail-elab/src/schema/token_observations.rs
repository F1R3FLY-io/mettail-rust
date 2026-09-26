//! DDL append receipts for the original token-kind writer, not another lexer.
//!
//! The supported source domain is deliberately finite: scalar/object category
//! declarations, flat nonbinding rule syntax, direct nonbinding List(Base) Sep,
//! and explicit/literal/mode tokens. Binder, collection declarations, keyed or
//! nested collections, mapped/chained/optional, and foreign-language source
//! projections still need their original lexer-input observations connected.
//! For those forms lowering succeeds unchanged with no observation table;
//! OwnedTokenSource then explicitly refuses MissingTable. Incomplete rosters
//! must never be published as complete metadata.

use super::*;
use mettail_prattail::token_declarations::{
    prepare_literal_patterns, project_global_tokens, project_mode_token, TokenDeclarationFields,
    TokenDeclarationReader,
};
use mettail_prattail::wpda_owned::token_bindings::TokenObservationProducer;
use mettail_prattail::wpda_rule_analysis::authored::AuthoredRuleReader;

pub(super) struct Prepared {
    pub producer: TokenObservationProducer,
    pub source_variants: Vec<String>,
    /// Same original collected terminals feed the observation roster AND the
    /// existing Core fixed-token append sites (including arbitrary separators).
    pub terminals: BTreeSet<String>,
}

#[derive(Clone, Copy)]
enum SourceToken<'a> {
    Explicit(&'a TokenDecl),
    Literal(&'a LiteralDecl),
}

impl SourceToken<'_> {
    fn category(&self) -> Option<&str> {
        match self {
            Self::Explicit(token) => token.category.as_deref(),
            Self::Literal(token) => Some(&token.category),
        }
    }
}

struct Reader<'a> {
    schema: &'a LanguageSchema,
    names: Vec<&'a str>,
    tokens: Vec<SourceToken<'a>>,
}

impl TokenDeclarationReader for Reader<'_> {
    type Token = usize;
    type Output = TokenDeclarationFields;
    fn name(&self, source: usize) -> String {
        self.names[source].to_owned()
    }
    fn native_kind(&self, source: usize) -> Option<core::NativeKind> {
        self.tokens[source].category().and_then(|name| {
            self.schema
                .types
                .iter()
                .find(|ty| ty.name == name)
                .and_then(|ty| ty.native)
        })
    }
    fn pattern(&self, source: usize) -> String {
        match self.tokens[source] {
            SourceToken::Explicit(token) => token.pattern.clone(),
            SourceToken::Literal(token) => token.pattern.clone(),
        }
    }
    fn from_literals(&self, source: usize) -> bool {
        matches!(self.tokens[source], SourceToken::Literal(_))
    }
    fn category_native_type(&self, source: usize) -> Option<String> {
        self.tokens[source].category().and_then(|name| {
            self.schema
                .types
                .iter()
                .find(|ty| ty.name == name)
                .and_then(|ty| ty.native_type_spelling.clone())
        })
    }
    fn finish(&self, _: usize, fields: TokenDeclarationFields) -> Self::Output {
        fields
    }
}

fn simple_list_parameter(param: &Param) -> bool {
    matches!(param, Param::Plain { ty: TypeExpr::Collection(core::CollectionKind::List, element, None), .. }
        if matches!(element.as_ref(), TypeExpr::Base(_)))
}

/// Only a domain guard, not a replacement syntax classifier or traversal.
/// A direct Sep of List(Base) follows the original nonbinder Vec branch in
/// convert_pattern_op/find_collection_info: Collection(separator, None).
fn supported_source_domain(schema: &LanguageSchema) -> bool {
    schema
        .types
        .iter()
        .all(|ty| ty.collection.is_none() && !matches!(ty.carrier, core::Carrier::Extern { .. }))
        && schema.terms.iter().all(|term| {
            term.context.iter().all(|param| {
                matches!(param, Param::Plain { ty: TypeExpr::Base(_), .. } | Param::Guard(_))
                    || simple_list_parameter(param)
            }) && match &term.body {
                TermBody::Bnf(items) => items.iter().all(|item| {
                    matches!(
                        item,
                        BnfNode::Literal(_) | BnfNode::Nonterminal(_) | BnfNode::Binding(_)
                    )
                }),
                TermBody::Judgement(items) => items.iter().all(|item| match item {
                    SyntaxNode::Reference(_)
                    | SyntaxNode::Literal(_)
                    | SyntaxNode::Token { .. } => true,
                    SyntaxNode::Separated(source, _) => {
                        let SyntaxNode::Reference(name) = source.as_ref() else {
                            return false;
                        };
                        term.context
                            .iter()
                            .find(|param| match param {
                                Param::Plain { name: candidate, .. } | Param::Guard(candidate) => {
                                    candidate == name
                                },
                                _ => false,
                            })
                            .is_some_and(simple_list_parameter)
                    },
                    _ => false,
                }),
            }
        })
}

/// Called only after supported_source_domain and the original binder traversal.
/// The simple-list guard establishes the original Collection observation; this
/// function supplies fields to the shared worker rather than emitting tokens.
fn term_terminals(term: &TermDecl) -> Vec<String> {
    use mettail_prattail::lexer::{collect_terminal_observations, TerminalObservation as O};
    match &term.body {
        TermBody::Bnf(items) => {
            collect_terminal_observations(items.iter().map(|item| match item {
                BnfNode::Literal(text) => O::Terminal(text),
                _ => O::Other,
            }))
        },
        TermBody::Judgement(items) => {
            collect_terminal_observations(items.iter().map(|item| match item {
                SyntaxNode::Literal(text) => O::Terminal(text),
                SyntaxNode::Separated(_, separator) => {
                    O::Collection { separator, key_val_separator: None }
                },
                _ => O::Other,
            }))
        },
    }
}

pub(super) fn prepare(
    schema: &LanguageSchema,
    store: &core::AuthoredRuleStore,
    roots: &[u32],
) -> Result<Option<Prepared>, ValueDecodeError> {
    if !supported_source_domain(schema) {
        return Ok(None);
    }
    // Observe actual retained rules with the existing source binder traversal.
    // Even a flat BNF Binding is not silently treated as binder absence.
    let rule_reader = AuthoredRuleReader::new(store).map_err(|error| {
        ValueDecodeError::new("$", format!("token observation source: {error}"))
    })?;
    if core::term_param_walk::declares_binder(
        &rule_reader,
        roots.iter().copied().map(core::AuthoredRuleId),
    ) {
        return Ok(None);
    }
    let header = store.declarations().ok_or_else(|| {
        ValueDecodeError::new("$", "token observation source omitted declarations")
    })?;
    let names = header
        .tokens
        .iter()
        .map(|token| match store.get(token.name.0) {
            Some(core::AuthoredNode::Name(name)) => Ok(name.spelling.as_str()),
            _ => Err(ValueDecodeError::new("$", "token observation source name is not retained")),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let tokens = schema
        .tokens
        .iter()
        .map(SourceToken::Explicit)
        .chain(schema.literals.iter().map(SourceToken::Literal))
        .chain(
            schema
                .modes
                .iter()
                .flat_map(|mode| mode.tokens.iter().map(SourceToken::Explicit)),
        )
        .collect::<Vec<_>>();
    if names.len() != tokens.len() {
        return Err(ValueDecodeError::new(
            "$",
            "token observation source roster differs from declarations",
        ));
    }
    let reader = Reader { schema, names, tokens };
    let globals = schema.tokens.len() + schema.literals.len();
    let (patterns, origins, global) = project_global_tokens(&reader, 0..globals);
    let mut next = globals;
    let modes = schema
        .modes
        .iter()
        .map(|mode| {
            let rows = (next..next + mode.tokens.len())
                .map(|source| project_mode_token(&reader, source))
                .collect::<Vec<_>>();
            next += mode.tokens.len();
            rows
        })
        .collect::<Vec<_>>();
    let source_variants = global
        .iter()
        .zip(&origins.builtin_overrides)
        .map(|(token, family)| {
            family
                .map(str::to_owned)
                .unwrap_or_else(|| token.name.clone())
        })
        .chain(modes.iter().flatten().map(|token| token.name.clone()))
        .collect();
    let types = schema
        .types
        .iter()
        .map(|ty| mettail_prattail::lexer::TypeInfo {
            name: ty.name.clone(),
            language_name: schema.name.clone(),
            native_type_name: ty.native_type_spelling.clone(),
        })
        .collect::<Vec<_>>();
    let terminals: BTreeSet<String> = schema.terms.iter().flat_map(term_terminals).collect();
    let category_names = schema
        .types
        .iter()
        .filter(|ty| ty.admits_variables)
        .map(|ty| ty.name.clone())
        .collect::<Vec<_>>();
    // False is justified by the successful original source traversal above;
    // positive/unsupported forms never reach this extraction.
    let mut input = mettail_prattail::lexer::extract_terminals_from_source(
        &terminals,
        &types,
        false,
        &category_names,
    );
    prepare_literal_patterns(&mut input, &patterns);
    let producer =
        TokenObservationProducer::for_metadata(&input, &global, modes.iter().map(Vec::as_slice));
    Ok(Some(Prepared { producer, source_variants, terminals }))
}
