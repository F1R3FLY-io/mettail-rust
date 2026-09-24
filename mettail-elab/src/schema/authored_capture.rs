//! Borrow the decoded, renamed schema before its lossy parser projection.
//!
//! The core capture worker owns traversal and identity/equality assignment.
//! This adapter only supplies the existing eight shallow observations. Sourced
//! separators use the original parser's `__chain__` convention: correspondence
//! is with classifier observations, not arbitrary programmatic AST identity.
//!
//! Admission follows AuthoredRuntimeCaptureAdmission: N first observations,
//! E typed reference fields, Q vector elements, R ordered roots, B string bytes.
//! I=R+E+Q uses the existing canonical item cap. This conservative retained
//! domain is not claimed identical to canonical input admission. Copies are
//! prepaid; Finish moves strings/remaps IDs without charging content again.
//! Judgement compatibility items use the original shared context converter.
//! Its aggregate W charges visits/frames/items once and bindings twice, so
//! I=R+E+Q+W also bounds this finite occurrence work (not instruction count).
//! Bounds describe logical lengths, not allocator capacities or physical RSS.
//! Declaration capture additionally prepays header/remap and binding-builder
//! contents in Q, plus header-row and literal-selector work in W. Rich schema
//! carriers stay in the schema/Core; native observations are captured before
//! lowering. This does not establish native decoder or value parity.
//! Three additional shallow observations per category are prepaid in W.
//! Collection element roots borrow the current renamed carrier key; their
//! Name payload copies are paid by the existing capture source, not the header.

use super::{
    BnfNode, LanguageSchema, LiteralDecl, Param, SyntaxNode, TermBody, TermDecl, TypeExpr,
};
use crate::canonical::{
    account_canonical_string, ValueDecodeError, MAX_CANONICAL_COLLECTION_ITEMS,
    MAX_CANONICAL_VALUE_NODES,
};
use mettail_grammar_core::context_items::{
    try_convert_term_context_to_items_with, ContextItemsError, ContextItemsEvent,
    ContextItemsReader,
};
use mettail_grammar_core::*;
use std::cell::RefCell;

#[derive(Clone, Copy)]
enum Handle<'a> {
    Name(&'a String),
    LiteralName {
        owner: &'a LiteralDecl,
        spelling: &'a str,
    },
    ChainName(&'a SyntaxNode),
    Names(&'a Vec<String>),
    Type(&'a TypeExpr),
    Param(&'a Param),
    Params(&'a Vec<Param>),
    Syntax(&'a Vec<SyntaxNode>),
    Operation(&'a SyntaxNode),
    Rule(&'a TermDecl),
}

fn failure(message: &str) -> ValueDecodeError {
    ValueDecodeError::new("$.terms", message)
}

fn add(left: usize, right: usize) -> Result<usize, ValueDecodeError> {
    left.checked_add(right)
        .ok_or_else(|| failure("authored capture logical size overflowed"))
}

#[derive(Default)]
struct Budget {
    roots: usize,
    nodes: usize,
    edges: usize,
    slots: usize,
    strings: usize,
    context_work: usize,
}

impl Budget {
    fn roots(roots: usize) -> Result<Self, ValueDecodeError> {
        if roots > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(failure("authored capture root roster exceeds canonical item limit"));
        }
        Ok(Self { roots, ..Self::default() })
    }

    fn observe(&mut self, edges: usize, slots: usize) -> Result<(), ValueDecodeError> {
        let nodes = add(self.nodes, 1)?;
        let edges = add(self.edges, edges)?;
        let slots = add(self.slots, slots)?;
        let items = add(add(add(self.roots, edges)?, slots)?, self.context_work)?;
        if nodes > MAX_CANONICAL_VALUE_NODES || items > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(failure("authored capture exceeds canonical node/item limits"));
        }
        self.nodes = nodes;
        self.edges = edges;
        self.slots = slots;
        Ok(())
    }

    fn string(&mut self, value: &str) -> Result<(), ValueDecodeError> {
        account_canonical_string(value, &mut self.strings)
    }

    /// Prepaid header content is separate from observed arena nodes/edges.
    /// W is capture-wide: subsequent context events add to these source costs.
    fn header_content(
        &mut self,
        roots: usize,
        slots: usize,
        work: usize,
    ) -> Result<(), ValueDecodeError> {
        let roots = add(self.roots, roots)?;
        let slots = add(self.slots, slots)?;
        let work = add(self.context_work, work)?;
        let items = add(add(add(roots, self.edges)?, slots)?, work)?;
        if self.nodes > MAX_CANONICAL_VALUE_NODES || items > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(failure("authored declaration content exceeds canonical item limit"));
        }
        self.roots = roots;
        self.slots = slots;
        self.context_work = work;
        Ok(())
    }

    /// Same-loop admission; generated item edges/slots are not another node.
    fn context_event(
        &mut self,
        event: ContextItemsEvent<&String, CollectionKind>,
    ) -> Result<(), ValueDecodeError> {
        let (work, item, separator) = match event {
            ContextItemsEvent::VisitParameter | ContextItemsEvent::EnterOptional => (1, 0, None),
            ContextItemsEvent::Nonterminal(_) | ContextItemsEvent::Binder(_) => (1, 1, None),
            ContextItemsEvent::Collection { separator, .. } => (1, 1, Some(separator)),
            ContextItemsEvent::Binding => (2, 0, None),
        };
        let work = add(self.context_work, work)?;
        let edges = add(self.edges, item)?;
        let slots = add(self.slots, item)?;
        let items = add(add(add(self.roots, edges)?, slots)?, work)?;
        if self.nodes > MAX_CANONICAL_VALUE_NODES || items > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(failure("authored context conversion exceeds canonical node/item limits"));
        }
        if let Some(separator) = separator {
            self.string(separator)?;
        }
        self.context_work = work;
        self.edges = edges;
        self.slots = slots;
        Ok(())
    }

    fn phase<H, K>(
        &self,
        phase: AuthoredCaptureAdmission,
        node: &AuthoredNode<H, K>,
    ) -> Result<(), ValueDecodeError> {
        let entering = usize::from(phase.phase == AuthoredCapturePhase::Enter);
        let finishing = usize::from(phase.phase == AuthoredCapturePhase::Finish);
        let new_class = usize::from(finishing == 1 && matches!(node, AuthoredNode::Name(_)));
        let frames = add(add(self.roots, self.nodes)?, self.edges)?;
        if add(phase.memoized_nodes, entering)? > self.nodes
            || add(phase.stored_nodes, finishing)? > self.nodes
            || add(phase.name_classes, new_class)? > self.nodes
            || phase.scheduled_frames > frames
        {
            return Err(failure("authored capture occupancy exceeds admitted logical content"));
        }
        Ok(())
    }
}

/// Counts only source rosters, never grammar syntax. All arithmetic is checked.
/// Q prepays each actual vector construction: initial header H, remapped
/// category/token/mode rows J, pending builder P, finalized P and token zip T.
struct HeaderCounts {
    categories: usize,
    tokens: usize,
    globals: usize,
    modes: usize,
}

impl HeaderCounts {
    fn admit(schema: &LanguageSchema, budget: &mut Budget) -> Result<Self, ValueDecodeError> {
        // Pay the finite mode roster before inspecting nested vector lengths.
        budget.header_content(0, 0, schema.modes.len())?;
        let mut mode_tokens = 0;
        for mode in &schema.modes {
            mode_tokens = add(mode_tokens, mode.tokens.len())?;
        }
        let categories = schema.types.len();
        let observation_work = categories
            .checked_mul(3)
            .ok_or_else(|| failure("authored native observation work overflowed"))?;
        budget.header_content(0, 0, observation_work)?;
        let globals = add(schema.tokens.len(), schema.literals.len())?;
        let tokens = add(globals, mode_tokens)?;
        let modes = schema.modes.len();
        for count in [categories, tokens, modes] {
            u32::try_from(count).map_err(|_| failure("authored declaration roster exceeds u32"))?;
        }
        let initial = add(add(add(add(categories, tokens)?, globals)?, modes)?, mode_tokens)?;
        let remapped = add(add(categories, tokens)?, modes)?;
        let pending = add(add(add(categories, tokens)?, tokens)?, modes)?;
        let finalized = add(pending, tokens)?;
        let slots = add(add(add(initial, remapped)?, pending)?, finalized)?;
        let comparisons = categories
            .checked_mul(schema.literals.len())
            .ok_or_else(|| failure("authored literal selector work overflowed"))?;
        // Mode-row work was already paid above. This charges the upper bound
        // for each literal's one original first-match selector call, not a
        // second lookup and not individual string-comparison instructions.
        budget.header_content(0, slots, add(add(categories, tokens)?, comparisons)?)?;
        let mut roots = add(categories, modes)?;
        for category in &schema.types {
            if matches!(&category.carrier, Carrier::Collection(_)) {
                roots = add(roots, 1)?;
            }
        }
        roots = add(roots, add(schema.literals.len(), schema.literals.len())?)?;
        for token in schema
            .tokens
            .iter()
            .chain(schema.modes.iter().flat_map(|mode| &mode.tokens))
        {
            roots = add(
                roots,
                1 + usize::from(token.category.is_some()) + usize::from(token.push.is_some()),
            )?;
        }
        budget.header_content(roots, 0, 0)?;
        Ok(Self { categories, tokens, globals, modes })
    }
}

fn reserved<T>(count: usize) -> Result<Vec<T>, ValueDecodeError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| failure("authored declaration allocation failed"))?;
    Ok(values)
}

fn declaration_header<'a>(
    schema: &'a LanguageSchema,
    counts: &HeaderCounts,
    budget: &mut Budget,
) -> Result<AuthoredDeclarations<Handle<'a>>, ValueDecodeError> {
    let mut categories = reserved(counts.categories)?;
    let mut tokens = reserved(counts.tokens)?;
    let mut global_tokens = reserved(counts.globals)?;
    let mut modes = reserved(counts.modes)?;
    for category in &schema.types {
        let (byte_observation, literal_observation, element_observation) = match &category.carrier {
            Carrier::Collection(collection) => (
                SourceObservation::Unavailable,
                SourceObservation::Unavailable,
                SourceObservation::Known(Some(name(&collection.key))),
            ),
            Carrier::Extern { .. } => (
                SourceObservation::Known(false),
                SourceObservation::Known(Some(LiteralNativeObservation::CanonicalOpaque)),
                SourceObservation::Known(None),
            ),
            _ => {
                // Actual scalar decoding yields closed variants. Preserve
                // the original string gate for any retained Other payload
                // in a directly supplied schema fixture as well.
                if let Some(NativeType::Other(spelling)) = &category.scalar_native {
                    budget.string(spelling)?;
                }
                (
                    SourceObservation::Known(false),
                    SourceObservation::Known(
                        category
                            .scalar_native
                            .clone()
                            .map(LiteralNativeObservation::ExactNativeType),
                    ),
                    SourceObservation::Known(None),
                )
            },
        };
        let collection = if let Some(collection) = &category.collection {
            for text in [
                &collection.open,
                &collection.close,
                &collection.separator,
                &collection.key_value_separator,
            ]
            .into_iter()
            .flatten()
            {
                budget.string(text)?;
            }
            Some(AuthoredCollectionDeclaration {
                kind: collection.kind,
                open: collection.open.clone(),
                close: collection.close.clone(),
                separator: collection.separator.clone(),
                key_value_separator: collection.key_value_separator.clone(),
            })
        } else {
            None
        };
        categories.push(AuthoredCategoryDeclaration {
            name: name(&category.name),
            native: category.native,
            byte_observation,
            literal_observation,
            element_observation,
            collection,
        });
    }
    let explicit = |token: &'a super::TokenDecl| AuthoredTokenDeclaration {
        name: name(&token.name),
        category: token.category.as_ref().map(name),
        from_literals: false,
        has_evaluation: token.evaluation.is_some(),
        push: token.push.as_ref().map(name),
    };
    // Source order matches the authored macro declaration view. The execution
    // lowering remains literal-first and binds actual append receipts there.
    for token in &schema.tokens {
        global_tokens.push(source_token_index(tokens.len())?);
        tokens.push(explicit(token));
    }
    for literal in &schema.literals {
        let spelling = normalize_literal_name(
            literal.category.as_str(),
            &schema.types,
            |category| category.name.as_str(),
            |category| category.native.as_ref(),
            |kind| *kind,
            |variant, _| variant,
            |_| literal.category.as_str(),
        );
        global_tokens.push(source_token_index(tokens.len())?);
        tokens.push(AuthoredTokenDeclaration {
            name: AuthoredNameId(Handle::LiteralName { owner: literal, spelling }),
            category: Some(name(&literal.category)),
            from_literals: true,
            has_evaluation: true,
            push: None,
        });
    }
    for mode in &schema.modes {
        let mut source_tokens = reserved(mode.tokens.len())?;
        for token in &mode.tokens {
            source_tokens.push(source_token_index(tokens.len())?);
            tokens.push(explicit(token));
        }
        modes.push(AuthoredModeDeclaration {
            name: name(&mode.name),
            tokens: source_tokens,
        });
    }
    Ok(AuthoredDeclarations { categories, tokens, global_tokens, modes })
}

fn source_token_index(index: usize) -> Result<u32, ValueDecodeError> {
    u32::try_from(index).map_err(|_| failure("authored source token index exceeds u32"))
}

struct Source<'a, 'b> {
    _rules: &'a [TermDecl],
    budget: &'b RefCell<Budget>,
}

fn name(value: &String) -> AuthoredNameId<Handle<'_>> {
    AuthoredNameId(Handle::Name(value))
}

/// FIPS decode_terms already defaults the runtime key to []. Judgement
/// syntax has Some(context), like the original judgement parser. Ordinary
/// empty BNF has None; runtime-only nonempty BNF parameters remain retained.
/// This does not rewrite the macro adapter's actual AST Option.
fn context(rule: &TermDecl) -> Option<&Vec<Param>> {
    match &rule.body {
        TermBody::Judgement(_) => Some(&rule.context),
        TermBody::Bnf(_) if rule.context.is_empty() => None,
        TermBody::Bnf(_) => Some(&rule.context),
    }
}

/// Shallow observations of decoded schema values for the ORIGINAL converter.
/// Name equality is schema string equality; no identifier reconstruction.
struct SchemaContextItemsReader;

impl<'a> TermParamReader<'a> for SchemaContextItemsReader {
    type Parameters = &'a [Param];
    type Param = &'a Param;
    type Name = &'a String;
    type Type = &'a TypeExpr;

    fn params_len(&self, params: Self::Parameters) -> usize {
        params.len()
    }

    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        params.get(index)
    }

    fn param(
        &self,
        param: Self::Param,
    ) -> TermParamObservation<Self::Name, Self::Parameters, Self::Type> {
        match param {
            Param::Plain { name, ty } => TermParamObservation::Simple { name, ty },
            Param::Guard(name) => TermParamObservation::GuardBody { name },
            Param::Optional(params) => TermParamObservation::Optional { params },
            Param::Binder { binder, body, ty, multiple: false } => {
                TermParamObservation::Abstraction { binder, body, ty }
            },
            Param::Binder { binder, body, ty, multiple: true } => {
                TermParamObservation::MultiAbstraction { binder, body, ty }
            },
        }
    }
}

impl<'a> ContextItemsReader<'a> for SchemaContextItemsReader {
    type CollectionKind = CollectionKind;
    type Item = AuthoredLegacyItem<Handle<'a>>;

    fn base_name(&self, ty: Self::Type) -> Option<Self::Name> {
        match ty {
            TypeExpr::Base(name) => Some(name),
            _ => None,
        }
    }

    fn collection(&self, ty: Self::Type) -> Option<(Self::CollectionKind, Self::Type)> {
        match ty {
            TypeExpr::Collection(kind, element, None) => Some((*kind, element)),
            _ => None,
        }
    }

    fn map(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)> {
        match ty {
            TypeExpr::Collection(CollectionKind::Map, key, Some(value)) => Some((key, value)),
            _ => None,
        }
    }

    fn arrow(&self, ty: Self::Type) -> Option<(Self::Type, Self::Type)> {
        match ty {
            TypeExpr::Arrow(domain, codomain) => Some((domain, codomain)),
            _ => None,
        }
    }

    fn multi_binder(&self, ty: Self::Type) -> Option<Self::Type> {
        match ty {
            TypeExpr::Multi(inner) => Some(inner),
            _ => None,
        }
    }

    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool {
        left == right
    }
    fn hash_map_kind(&self) -> Self::CollectionKind {
        CollectionKind::Map
    }
    fn make_nonterminal(&self, value: Self::Name) -> Self::Item {
        AuthoredLegacyItem::NonTerminal {
            ident: name(value),
            kind: NonTerminalKind::classify(value),
        }
    }
    fn make_binder(&self, value: Self::Name) -> Self::Item {
        AuthoredLegacyItem::Binder { category: name(value) }
    }
    fn make_collection(
        &self,
        kind: Self::CollectionKind,
        element: Self::Name,
        separator: &'static str,
    ) -> Self::Item {
        AuthoredLegacyItem::Collection {
            kind,
            element: name(element),
            separator: separator.to_owned(),
            open: None,
            close: None,
        }
    }
}

impl Source<'_, '_> {
    fn context_items<'a>(
        &self,
        params: &'a [Param],
    ) -> Result<Vec<AuthoredLegacyItem<Handle<'a>>>, ValueDecodeError> {
        let (items, _bindings) =
            try_convert_term_context_to_items_with(&SchemaContextItemsReader, params, |event| {
                self.budget.borrow_mut().context_event(event)
            })
            .map_err(|error| match error {
                ContextItemsError::Admission(error) => error,
                ContextItemsError::Allocation => {
                    failure("authored context conversion allocation failed")
                },
            })?;
        // Bindings are constructed and paid at the original callback sites.
        // This capture projection retains only items, not GrammarRule.bindings.
        Ok(items)
    }

    /// No temporary edge roster or owned payload is constructed in this pass.
    fn precharge(&self, handle: Handle<'_>) -> Result<(), ValueDecodeError> {
        let mut budget = self.budget.borrow_mut();
        let (edges, slots) = match handle {
            Handle::Name(text) => {
                budget.string(text)?;
                (0, 0)
            },
            Handle::LiteralName { spelling, .. } => {
                budget.string(spelling)?;
                (0, 0)
            },
            Handle::ChainName(_) => {
                budget.string(AUTHORED_CHAIN_COLLECTION_NAME)?;
                (0, 0)
            },
            Handle::Names(values) => (values.len(), values.len()),
            Handle::Params(values) => (values.len(), values.len()),
            Handle::Type(ty) => (
                match ty {
                    TypeExpr::Base(_) | TypeExpr::Multi(_) => 1,
                    TypeExpr::Arrow(_, _) => 2,
                    TypeExpr::Collection(_, _, value) => 1 + usize::from(value.is_some()),
                },
                0,
            ),
            Handle::Param(param) => (
                match param {
                    Param::Plain { .. } => 2,
                    Param::Binder { .. } => 3,
                    Param::Guard(_) | Param::Optional(_) => 1,
                },
                0,
            ),
            Handle::Syntax(values) => {
                let mut edges = 0;
                for value in values {
                    let count = match value {
                        SyntaxNode::Literal(text) => {
                            budget.string(text)?;
                            0
                        },
                        SyntaxNode::Token { binding, .. } => 1 + usize::from(binding.is_some()),
                        SyntaxNode::ForeignLanguage { .. } => 3,
                        _ => 1,
                    };
                    edges = add(edges, count)?;
                }
                (edges, values.len())
            },
            Handle::Operation(value) => (
                match value {
                    SyntaxNode::Separated(source, separator) => {
                        budget.string(separator)?;
                        if matches!(source.as_ref(), SyntaxNode::Reference(_)) {
                            1
                        } else {
                            2
                        }
                    },
                    SyntaxNode::Map { .. } => 3,
                    SyntaxNode::Zip(_, _) => 2,
                    SyntaxNode::Optional(_) => 1,
                    _ => 0,
                },
                0,
            ),
            Handle::Rule(rule) => {
                let mut edges = 2 + usize::from(context(rule).is_some());
                let slots = match &rule.body {
                    TermBody::Judgement(_) => {
                        edges = add(edges, 1)?;
                        0
                    },
                    TermBody::Bnf(items) => {
                        for item in items {
                            match item {
                                BnfNode::Literal(text) => budget.string(text)?,
                                BnfNode::Nonterminal(_) | BnfNode::Binding(_) => {
                                    edges = add(edges, 1)?
                                },
                                BnfNode::Collection { separator, open, close, .. } => {
                                    edges = add(edges, 1)?;
                                    budget.string(separator)?;
                                    if let Some(open) = open {
                                        budget.string(open)?;
                                    }
                                    if let Some(close) = close {
                                        budget.string(close)?;
                                    }
                                },
                            }
                        }
                        items.len()
                    },
                };
                (edges, slots)
            },
        };
        budget.observe(edges, slots)
    }
}

impl<'a> AuthoredCaptureSource for Source<'a, '_> {
    type Handle = Handle<'a>;
    type Identity = (u8, usize);
    type NameKey = &'a str;
    type Error = ValueDecodeError;

    fn identity(&self, handle: Self::Handle) -> Self::Identity {
        // Vec object addresses preserve distinct empty source occurrences too.
        // ChainName is an occurrence of its owning Sep, not one global name ID.
        match handle {
            Handle::Name(value) => (0, std::ptr::from_ref(value) as usize),
            Handle::ChainName(value) => (1, std::ptr::from_ref(value) as usize),
            Handle::Names(value) => (2, std::ptr::from_ref(value) as usize),
            Handle::Type(value) => (3, std::ptr::from_ref(value) as usize),
            Handle::Param(value) => (4, std::ptr::from_ref(value) as usize),
            Handle::Params(value) => (5, std::ptr::from_ref(value) as usize),
            Handle::Syntax(value) => (6, std::ptr::from_ref(value) as usize),
            Handle::Operation(value) => (7, std::ptr::from_ref(value) as usize),
            Handle::Rule(value) => (8, std::ptr::from_ref(value) as usize),
            Handle::LiteralName { owner, .. } => (9, std::ptr::from_ref(owner) as usize),
        }
    }

    fn shallow(
        &mut self,
        handle: Self::Handle,
    ) -> Result<AuthoredNode<Self::Handle, Self::NameKey>, Self::Error> {
        self.precharge(handle)?;
        Ok(match handle {
            Handle::Name(value) => AuthoredNode::Name(AuthoredName {
                spelling: value.clone(),
                equality_class: value.as_str(),
            }),
            Handle::LiteralName { spelling, .. } => AuthoredNode::Name(AuthoredName {
                spelling: spelling.to_owned(),
                equality_class: spelling,
            }),
            Handle::ChainName(_) => AuthoredNode::Name(AuthoredName {
                spelling: AUTHORED_CHAIN_COLLECTION_NAME.into(),
                equality_class: AUTHORED_CHAIN_COLLECTION_NAME,
            }),
            Handle::Names(values) => AuthoredNode::Names(values.iter().map(name).collect()),
            Handle::Params(values) => AuthoredNode::Params(
                values
                    .iter()
                    .map(|value| AuthoredParamId(Handle::Param(value)))
                    .collect(),
            ),
            Handle::Type(ty) => AuthoredNode::Type(match ty {
                TypeExpr::Base(value) => AuthoredType::Base(name(value)),
                TypeExpr::Arrow(domain, codomain) => AuthoredType::Arrow {
                    domain: AuthoredTypeId(Handle::Type(domain)),
                    codomain: AuthoredTypeId(Handle::Type(codomain)),
                },
                TypeExpr::Multi(inner) => AuthoredType::MultiBinder {
                    inner: AuthoredTypeId(Handle::Type(inner)),
                },
                TypeExpr::Collection(kind, key, value) => match (kind, value) {
                    (CollectionKind::Map, Some(value)) => AuthoredType::Map {
                        key: AuthoredTypeId(Handle::Type(key)),
                        value: AuthoredTypeId(Handle::Type(value)),
                    },
                    (CollectionKind::PathMap, Some(value)) => AuthoredType::KeyedPathMap {
                        key: AuthoredTypeId(Handle::Type(key)),
                        value: AuthoredTypeId(Handle::Type(value)),
                    },
                    (_, None) => AuthoredType::Collection {
                        kind: *kind,
                        element: AuthoredTypeId(Handle::Type(key)),
                    },
                    (_, Some(_)) => {
                        return Err(failure("unexpected keyed collection in decoded schema"))
                    },
                },
            }),
            Handle::Param(param) => AuthoredNode::Param(match param {
                Param::Plain { name: value, ty } => AuthoredParam::Simple {
                    name: name(value),
                    ty: AuthoredTypeId(Handle::Type(ty)),
                },
                Param::Guard(value) => AuthoredParam::GuardBody { name: name(value) },
                Param::Optional(values) => AuthoredParam::Optional {
                    params: AuthoredParamsId(Handle::Params(values)),
                },
                Param::Binder { binder, body, ty, multiple: false } => AuthoredParam::Abstraction {
                    binder: name(binder),
                    body: name(body),
                    ty: AuthoredTypeId(Handle::Type(ty)),
                },
                Param::Binder { binder, body, ty, multiple: true } => {
                    AuthoredParam::MultiAbstraction {
                        binder: name(binder),
                        body: name(body),
                        ty: AuthoredTypeId(Handle::Type(ty)),
                    }
                },
            }),
            Handle::Syntax(values) => AuthoredNode::Syntax(
                values
                    .iter()
                    .map(|value| match value {
                        SyntaxNode::Reference(value) => AuthoredSyntax::Param(name(value)),
                        SyntaxNode::Literal(value) => AuthoredSyntax::Literal(value.clone()),
                        SyntaxNode::Token { name: value, binding } => AuthoredSyntax::TokenKind {
                            name: name(value),
                            bind: binding.as_ref().map(name),
                        },
                        SyntaxNode::ForeignLanguage { binding, open, close } => {
                            AuthoredSyntax::GuestBody {
                                open: name(open),
                                close: name(close),
                                bind: name(binding),
                                kind: AuthoredDelimitedRegionKind::Flt,
                            }
                        },
                        _ => AuthoredSyntax::Op(AuthoredOperationId(Handle::Operation(value))),
                    })
                    .collect(),
            ),
            Handle::Operation(value) => AuthoredNode::Operation(match value {
                SyntaxNode::Separated(source, separator) => match source.as_ref() {
                    SyntaxNode::Reference(collection) => AuthoredOperation::Sep {
                        collection: name(collection),
                        separator: separator.clone(),
                        source: None,
                    },
                    _ => AuthoredOperation::Sep {
                        collection: AuthoredNameId(Handle::ChainName(value)),
                        separator: separator.clone(),
                        source: Some(AuthoredOperationId(Handle::Operation(source))),
                    },
                },
                SyntaxNode::Map { source, bindings, body } => AuthoredOperation::Map {
                    source: AuthoredOperationId(Handle::Operation(source)),
                    params: AuthoredNamesId(Handle::Names(bindings)),
                    body: AuthoredSyntaxId(Handle::Syntax(body)),
                },
                SyntaxNode::Zip(left, right) => {
                    AuthoredOperation::Zip { left: name(left), right: name(right) }
                },
                SyntaxNode::Optional(inner) => AuthoredOperation::Opt {
                    inner: AuthoredSyntaxId(Handle::Syntax(inner)),
                },
                _ => AuthoredOperation::Unsupported { tag: 0 },
            }),
            Handle::Rule(rule) => AuthoredNode::Rule(AuthoredRule {
                label: name(&rule.label),
                category: name(&rule.category),
                source_body_present: SourceObservation::Known(rule.evaluation.is_some()),
                explicit_fold: SourceObservation::Known(
                    rule.mode == Some(mettail_grammar_core::EvaluationMode::Fold),
                ),
                term_context: context(rule).map(|params| AuthoredParamsId(Handle::Params(params))),
                syntax_pattern: match &rule.body {
                    TermBody::Judgement(values) => Some(AuthoredSyntaxId(Handle::Syntax(values))),
                    TermBody::Bnf(_) => None,
                },
                items: match &rule.body {
                    TermBody::Judgement(_) => self.context_items(&rule.context)?,
                    TermBody::Bnf(items) => items
                        .iter()
                        .map(|item| match item {
                            BnfNode::Literal(value) => AuthoredLegacyItem::Terminal(value.clone()),
                            BnfNode::Nonterminal(value) => AuthoredLegacyItem::NonTerminal {
                                ident: name(value),
                                kind: NonTerminalKind::classify(value),
                            },
                            BnfNode::Binding(value) => {
                                AuthoredLegacyItem::Binder { category: name(value) }
                            },
                            BnfNode::Collection { kind, element, separator, open, close } => {
                                AuthoredLegacyItem::Collection {
                                    kind: *kind,
                                    element: name(element),
                                    separator: separator.clone(),
                                    open: open.clone(),
                                    close: close.clone(),
                                }
                            },
                        })
                        .collect(),
                },
            }),
        })
    }
}

pub(super) fn capture_language(
    schema: &LanguageSchema,
) -> Result<CapturedAuthoredNodes, ValueDecodeError> {
    let mut budget = Budget::roots(schema.terms.len())?;
    let counts = HeaderCounts::admit(schema, &mut budget)?;
    let header = declaration_header(schema, &counts, &mut budget)?;
    let budget = RefCell::new(budget);
    let mut roots = reserved(schema.terms.len())?;
    roots.extend(
        schema
            .terms
            .iter()
            .map(|rule| (AuthoredNodeTag::Rule, Handle::Rule(rule))),
    );
    let mut source = Source { _rules: &schema.terms, budget: &budget };
    capture_authored_declarations(&mut source, &roots, header, |phase, node| {
        budget.borrow().phase(phase, node)
    })
    .map_err(capture_error)
}

fn capture_error(error: AuthoredCaptureError<ValueDecodeError>) -> ValueDecodeError {
    match error {
        AuthoredCaptureError::Source(error) | AuthoredCaptureError::Admission(error) => error,
        error => ValueDecodeError::new("$.terms", format!("authored capture failed: {error:?}")),
    }
}

#[cfg(test)]
pub(super) fn capture(rules: &[TermDecl]) -> Result<CapturedAuthoredNodes, ValueDecodeError> {
    let budget = RefCell::new(Budget::roots(rules.len())?);
    let mut roots = Vec::new();
    roots
        .try_reserve(rules.len())
        .map_err(|_| failure("authored capture root allocation failed"))?;
    roots.extend(
        rules
            .iter()
            .map(|rule| (AuthoredNodeTag::Rule, Handle::Rule(rule))),
    );
    let mut source = Source { _rules: rules, budget: &budget };
    capture_authored_nodes(&mut source, &roots, |phase, node| budget.borrow().phase(phase, node))
        .map_err(capture_error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical::{RhoValue, MAX_CANONICAL_STRING_BYTES};
    use std::collections::BTreeMap;

    fn header_fixture() -> LanguageSchema {
        let mut schema = super::super::decode(&RhoValue::Map(BTreeMap::from([
            ("mettail".into(), RhoValue::String("language/2".into())),
            ("name".into(), RhoValue::String("Header".into())),
        ])))
        .expect("minimal schema decodes without rule reconstruction");
        schema.types = vec![
            super::super::TypeDecl {
                name: "Expr".into(),
                carrier: Carrier::Dynamic,
                native: None,
                scalar_native: None,
                collection: None,
                refinement: None,
                admits_variables: true,
            },
            super::super::TypeDecl {
                name: "Number".into(),
                carrier: Carrier::Builtin(BuiltinCarrier::Integer),
                native: Some(NativeKind::Int32),
                scalar_native: Some(NativeType::Int32),
                collection: None,
                refinement: None,
                admits_variables: true,
            },
            super::super::TypeDecl {
                name: "List".into(),
                carrier: Carrier::Collection(CollectionCarrier {
                    kind: CollectionKind::List,
                    key: "Expr".into(),
                    value: None,
                }),
                native: Some(NativeKind::Other),
                scalar_native: None,
                collection: Some(super::super::CollectionDecl {
                    kind: CollectionKind::List,
                    open: Some("[".into()),
                    close: None,
                    separator: Some(",".into()),
                    key_value_separator: Some("=>".into()),
                }),
                refinement: None,
                admits_variables: false,
            },
        ];
        let token =
            |name: &str, category: Option<&str>, push: Option<&str>| super::super::TokenDecl {
                name: name.into(),
                pattern: "x".into(),
                category: category.map(str::to_owned),
                evaluation: None,
                priority: 0,
                push: push.map(str::to_owned),
                pop: false,
                stream: None,
            };
        schema.tokens = vec![token("Integer", Some("Number"), Some("Body"))];
        schema.literals = ["Number", "Expr"]
            .into_iter()
            .map(|category| LiteralDecl {
                category: category.into(),
                pattern: "x".into(),
                evaluation: NativeEvaluation::Carrier {
                    kind: "int".into(),
                    parameters: BTreeMap::new(),
                },
            })
            .collect();
        schema.modes = vec![super::super::ModeDecl {
            name: "Body".into(),
            raw: true,
            tokens: vec![token("Close", None, None), token("Item", Some("Expr"), None)],
        }];
        schema
    }

    fn observation_fixture() -> LanguageSchema {
        let mut schema = header_fixture();
        schema.types.clear();
        schema.tokens.clear();
        schema.literals.clear();
        schema.modes.clear();
        schema
    }

    fn observed_type(
        name: &str,
        carrier: RhoValue,
        collection: Option<&str>,
    ) -> super::super::TypeDecl {
        let mut fields = BTreeMap::from([
            ("name".to_owned(), RhoValue::String(name.to_owned())),
            ("carrier".to_owned(), carrier),
        ]);
        if let Some(kind) = collection {
            fields.insert(
                "collection".to_owned(),
                RhoValue::Map(BTreeMap::from([(
                    "kind".to_owned(),
                    RhoValue::String(kind.to_owned()),
                )])),
            );
        }
        super::super::decode_type(&RhoValue::Map(fields), "$.types")
            .expect("source observation fixture uses an accepted carrier")
    }

    #[test]
    fn schema_native_observations_keep_every_scalar_width_and_original_alias() {
        let cases = [
            ("i8", NativeType::Int8),
            ("i16", NativeType::Int16),
            ("i32", NativeType::Int32),
            ("i64", NativeType::Int64),
            ("i128", NativeType::Int128),
            ("isize", NativeType::Isize),
            ("u8", NativeType::UInt8),
            ("u16", NativeType::UInt16),
            ("u32", NativeType::UInt32),
            ("u64", NativeType::UInt64),
            ("u128", NativeType::UInt128),
            ("usize", NativeType::Usize),
            ("f32", NativeType::Float32),
            ("f64", NativeType::Float64),
            ("bool", NativeType::Bool),
            ("str", NativeType::Str),
            ("String", NativeType::Str),
            ("BigInt", NativeType::CanonicalBigInt),
            ("BigRat", NativeType::CanonicalBigRat),
            ("Fixed", NativeType::CanonicalFixedPoint),
        ];
        let mut schema = observation_fixture();
        for (index, (symbol, expected)) in cases.iter().enumerate() {
            let declaration = observed_type(
                &format!("Scalar{index}"),
                RhoValue::String((*symbol).to_owned()),
                None,
            );
            assert_eq!(declaration.scalar_native.as_ref(), Some(expected));
            schema.types.push(declaration);
        }
        let captured = capture_language(&schema).expect("all scalar source facts capture");
        let header = captured
            .store
            .declarations()
            .expect("scalar header retained");
        for (row, (_, expected)) in header.categories.iter().zip(&cases) {
            assert_eq!(row.byte_observation, SourceObservation::Known(false));
            assert_eq!(row.element_observation, SourceObservation::Known(None));
            assert_eq!(
                row.literal_observation,
                SourceObservation::Known(Some(LiteralNativeObservation::ExactNativeType(
                    expected.clone()
                )))
            );
        }
        assert_eq!(NativeType::from_type_str("BigRat"), NativeType::Other("BigRat".into()));
        assert_eq!(NativeType::from_type_str("Fixed"), NativeType::Other("Fixed".into()));
    }

    #[test]
    fn schema_native_observations_keep_absence_and_urn_independent_positive_opacity() {
        let mut schema = observation_fixture();
        schema.types.push(
            super::super::decode_type(&RhoValue::String("Structural".into()), "$.types")
                .expect("structural category has no native observation"),
        );
        for (index, urn) in ["mtl:carrier:opaque", "HashSetLit", "PathMapLit", "UserBigInt"]
            .into_iter()
            .enumerate()
        {
            let declaration = observed_type(
                &format!("Opaque{index}"),
                RhoValue::List(vec![
                    RhoValue::String("extern".into()),
                    RhoValue::String(urn.into()),
                ]),
                None,
            );
            assert_eq!(declaration.carrier, Carrier::Extern { urn: urn.into() });
            assert_eq!(declaration.scalar_native, None);
            schema.types.push(declaration);
        }
        let captured = capture_language(&schema).expect("canonical opaque observations capture");
        let header = captured
            .store
            .declarations()
            .expect("opaque header retained");
        assert_eq!(header.categories[0].literal_observation, SourceObservation::Known(None));
        assert_ne!(header.categories[0].literal_observation, SourceObservation::Unavailable);
        for row in &header.categories[1..] {
            assert_eq!(row.byte_observation, SourceObservation::Known(false));
            assert_eq!(row.element_observation, SourceObservation::Known(None));
            assert_eq!(
                row.literal_observation,
                SourceObservation::Known(Some(LiteralNativeObservation::CanonicalOpaque))
            );
            let SourceObservation::Known(Some(observation)) = &row.literal_observation else {
                panic!("extern must retain positive canonical opacity");
            };
            assert_eq!(
                constructor_labels::generate_literal_label_observed(
                    || false,
                    || observation.clone(),
                    str::to_owned,
                ),
                "Lit",
                "registry names never select a Rust wrapper or integer label"
            );
        }
    }

    #[test]
    fn schema_native_observations_borrow_renamed_first_keys_in_header_root_order() {
        let mut schema = observation_fixture();
        for name in ["Key", "Value"] {
            schema.types.push(
                super::super::decode_type(&RhoValue::String(name.into()), "$.types")
                    .expect("collection categories are valid source names"),
            );
        }
        for (index, (tag, kind, keyed)) in [
            ("vec", "list", false),
            ("bag", "bag", false),
            ("set", "set", false),
            ("map", "map", true),
            ("pathmap", "pathmap", true),
        ]
        .into_iter()
        .enumerate()
        {
            let mut carrier = vec![RhoValue::String(tag.into()), RhoValue::String("Key".into())];
            if keyed {
                carrier.push(RhoValue::String("Value".into()));
            }
            schema.types.push(observed_type(
                &format!("Collection{index}"),
                RhoValue::List(carrier),
                Some(kind),
            ));
        }
        schema.rename_category("Key", "RenamedKey");
        let captured = capture_language(&schema).expect("renamed collection source captures");
        let header = captured
            .store
            .declarations()
            .expect("collection header retained");
        let mut ordered = Vec::new();
        header
            .try_for_each_name(|id| {
                ordered.push(named(&captured.store, id).spelling.as_str());
                Ok::<_, ()>(())
            })
            .expect("all retained declaration references are valid");
        assert_eq!(
            ordered,
            [
                "RenamedKey",
                "Value",
                "Collection0",
                "RenamedKey",
                "Collection1",
                "RenamedKey",
                "Collection2",
                "RenamedKey",
                "Collection3",
                "RenamedKey",
                "Collection4",
                "RenamedKey",
            ]
        );
        for (index, row) in header.categories[2..].iter().enumerate() {
            assert_eq!(row.byte_observation, SourceObservation::Unavailable);
            assert_eq!(row.literal_observation, SourceObservation::Unavailable);
            let SourceObservation::Known(Some(element)) = &row.element_observation else {
                panic!("canonical collection must retain its first key name");
            };
            assert_eq!(named(&captured.store, *element).spelling, "RenamedKey");
            assert_eq!(
                named(&captured.store, *element).equality_class,
                named(&captured.store, header.categories[0].name).equality_class,
                "existing capture table preserves source String equality"
            );
            let Carrier::Collection(carrier) = &schema.types[index + 2].carrier else {
                panic!("fixture collection carrier is retained");
            };
            if index >= 3 {
                assert_eq!(carrier.value.as_deref(), Some("Value"));
            }
        }
    }

    #[test]
    fn schema_native_observations_pay_before_probes_and_other_spelling_copies() {
        let mut schema = header_fixture();
        let mut unpaid = Budget {
            context_work: MAX_CANONICAL_COLLECTION_ITEMS - 8,
            ..Budget::default()
        };
        assert!(HeaderCounts::admit(&schema, &mut unpaid).is_err());
        assert_eq!(
            (unpaid.roots, unpaid.nodes, unpaid.edges, unpaid.slots, unpaid.strings),
            (0, 0, 0, 0, 0)
        );

        // A direct fixture reaches the generic string-carrying observation;
        // accepted scalar schema symbols themselves use closed NativeType arms.
        schema = observation_fixture();
        let mut category = observed_type("OpaqueSource", RhoValue::String("i32".into()), None);
        category.scalar_native = Some(NativeType::Other("OpaqueSource".into()));
        schema.types.push(category);
        let mut budget = Budget::default();
        let counts =
            HeaderCounts::admit(&schema, &mut budget).expect("observation logical work fits");
        assert_eq!((budget.roots, budget.context_work, budget.strings), (1, 4, 0));
        let header = declaration_header(&schema, &counts, &mut budget)
            .expect("Other spelling is copied after the original string gate");
        assert_eq!(budget.strings, "OpaqueSource".len());
        assert_eq!(budget.nodes, 0, "header has not copied any Name payload");
        assert_eq!(header.categories.len(), 1);
        let mut full = Budget {
            strings: crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES,
            ..Budget::default()
        };
        let counts =
            HeaderCounts::admit(&schema, &mut full).expect("logical work fits independently");
        assert!(declaration_header(&schema, &counts, &mut full).is_err());
        assert_eq!(full.nodes, 0);
        assert_eq!(
            full.strings,
            crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES + "OpaqueSource".len()
        );
    }

    #[test]
    fn schema_header_keeps_order_presence_literal_identity_and_partial_delimiters() {
        let schema = header_fixture();
        let captured = capture_language(&schema).expect("declarations capture without rules");
        assert!(captured.roots.is_empty(), "declarations are not fabricated rule roots");
        let header = captured
            .store
            .declarations()
            .expect("header survives empty rule roster");
        assert_eq!(header.global_tokens, [0, 1, 2]);
        assert_eq!(header.modes[0].tokens, [3, 4]);
        assert_eq!(named(&captured.store, header.modes[0].name).spelling, "Body");
        assert_eq!(
            header
                .categories
                .iter()
                .map(|category| category.native)
                .collect::<Vec<_>>(),
            [None, Some(NativeKind::Int32), Some(NativeKind::Other)]
        );
        let collection = header.categories[2]
            .collection
            .as_ref()
            .expect("declared collection remains present");
        assert_eq!(collection.kind, CollectionKind::List);
        assert_eq!(collection.open.as_deref(), Some("["));
        assert_eq!(collection.close, None);
        assert_eq!(collection.separator.as_deref(), Some(","));
        assert_eq!(collection.key_value_separator.as_deref(), Some("=>"));
        assert_eq!(
            header
                .tokens
                .iter()
                .map(|token| named(&captured.store, token.name).spelling.as_str())
                .collect::<Vec<_>>(),
            ["Integer", "Integer", "Expr", "Close", "Item"]
        );
        assert_eq!(
            header
                .tokens
                .iter()
                .map(|token| (token.from_literals, token.has_evaluation))
                .collect::<Vec<_>>(),
            [(false, false), (true, true), (true, true), (false, false), (false, false)]
        );
        assert_eq!(
            named(
                &captured.store,
                header.tokens[1]
                    .category
                    .expect("literal source category remains present")
            )
            .spelling,
            "Number"
        );
        assert_eq!(
            named(&captured.store, header.tokens[0].push.expect("source push remains present"))
                .spelling,
            "Body"
        );
        assert!(header.tokens[1].push.is_none() && header.tokens[3].category.is_none());
        assert_ne!(
            header.tokens[0].name, header.tokens[1].name,
            "equal names retain distinct original occurrences"
        );
        assert_eq!(
            named(&captured.store, header.tokens[0].name).equality_class,
            named(&captured.store, header.tokens[1].name).equality_class
        );
    }

    #[test]
    fn schema_header_pays_exact_vector_phases_roots_work_and_only_copied_bytes() {
        let schema = header_fixture();
        let mut budget = Budget::default();
        let counts = HeaderCounts::admit(&schema, &mut budget).expect("header counts fit");
        // C=3,G=1,L=2,U=2,M=1,T=5. H=14,J=9,P=14,F=19.
        assert_eq!((counts.categories, counts.tokens, counts.globals, counts.modes), (3, 5, 3, 1));
        assert_eq!(
            (
                budget.roots,
                budget.nodes,
                budget.edges,
                budget.slots,
                budget.context_work,
                budget.strings
            ),
            (15, 0, 0, 56, 24, 0)
        );
        let header =
            declaration_header(&schema, &counts, &mut budget).expect("paid header constructs");
        assert_eq!(
            budget.strings, 4,
            "only declared collection strings copied before Name capture"
        );
        let mut roots = 0;
        header
            .try_for_each_name(|_| {
                roots += 1;
                Ok::<_, ()>(())
            })
            .expect("count header names");
        assert_eq!(roots, budget.roots);
        let number = "Number".to_owned();
        budget
            .context_event(ContextItemsEvent::Nonterminal(&number))
            .expect("context work adds to prepaid header work");
        assert_eq!((budget.nodes, budget.edges, budget.slots, budget.context_work), (0, 1, 57, 25));
    }

    #[test]
    fn schema_header_budget_exact_boundary_and_refusal_precede_payload_copy() {
        let schema = header_fixture();
        let total = 15 + 56 + 24;
        let mut exact = Budget {
            context_work: MAX_CANONICAL_COLLECTION_ITEMS - total,
            ..Budget::default()
        };
        HeaderCounts::admit(&schema, &mut exact)
            .expect("all header phases exactly fit the item limit");
        assert_eq!(
            exact.roots + exact.edges + exact.slots + exact.context_work,
            MAX_CANONICAL_COLLECTION_ITEMS
        );
        let mut short = Budget {
            context_work: MAX_CANONICAL_COLLECTION_ITEMS - total + 1,
            ..Budget::default()
        };
        assert!(HeaderCounts::admit(&schema, &mut short).is_err());
        assert_eq!(
            (short.nodes, short.edges, short.strings),
            (0, 0, 0),
            "refused header admission copied no payload or source node"
        );
        let mut string_full = Budget {
            strings: crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES,
            ..Budget::default()
        };
        let counts = HeaderCounts::admit(&schema, &mut string_full)
            .expect("logical header slots fit independently");
        assert!(
            declaration_header(&schema, &counts, &mut string_full).is_err(),
            "original string gate refuses before collection copies"
        );
        assert_eq!(string_full.nodes, 0);
        assert_eq!(string_full.strings, crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES + 1);
    }

    #[test]
    fn schema_header_shared_selector_stops_at_first_equal_and_rule_roots_stay_first() {
        let mut schema = header_fixture();
        // Direct source observation fixture: original first-match semantics,
        // not a claim that duplicate declarations pass final Core validation.
        schema.types[0].name = "Number".into();
        schema.literals[1].category = "Missing".into();
        schema.terms =
            vec![term(None, TermBody::Judgement(vec![])), term(None, TermBody::Bnf(vec![]))];
        let captured = capture_language(&schema).expect("shallow source observations capture");
        assert_eq!(captured.roots.len(), 2);
        assert!(rule(&captured.store, captured.roots[0])
            .syntax_pattern
            .is_some());
        assert!(rule(&captured.store, captured.roots[1])
            .syntax_pattern
            .is_none());
        let header = captured
            .store
            .declarations()
            .expect("source header retained");
        assert_eq!(
            named(&captured.store, header.tokens[1].name).spelling,
            "Number",
            "first equal declaration without native prevents later standard variant"
        );
        assert_eq!(
            named(&captured.store, header.tokens[2].name).spelling,
            "Missing",
            "missing declaration clones original spelling"
        );
    }

    fn term(context: Option<Vec<Param>>, body: TermBody) -> TermDecl {
        TermDecl {
            label: "Rule".into(),
            category: "Expr".into(),
            context: context.unwrap_or_default(),
            body,
            evaluation: None,
            mode: None,
            associativity: Associativity::Left,
            prefix_binding_power: None,
            shares_previous_level: false,
            tier: None,
        }
    }

    fn node(store: &AuthoredRuleStore, id: u32) -> &AuthoredNode {
        store
            .get(id)
            .expect("authored capture fixture must be valid")
    }
    fn rule(store: &AuthoredRuleStore, id: u32) -> &AuthoredRule {
        let AuthoredNode::Rule(rule) = node(store, id) else {
            panic!("rule")
        };
        rule
    }
    fn named(store: &AuthoredRuleStore, id: AuthoredNameId) -> &AuthoredName {
        let AuthoredNode::Name(name) = node(store, id.0) else {
            panic!("name")
        };
        name
    }

    fn base(value: &str) -> TypeExpr {
        TypeExpr::Base(value.to_owned())
    }

    fn plain(ty: TypeExpr) -> Param {
        Param::Plain { name: "value".into(), ty }
    }

    fn binder(domain: TypeExpr, body_type: TypeExpr, multiple: bool) -> Param {
        Param::Binder {
            binder: "binder".into(),
            body: "body".into(),
            ty: TypeExpr::Arrow(Box::new(domain), Box::new(body_type)),
            multiple,
        }
    }

    fn borrowed_name<'a>(id: &AuthoredNameId<Handle<'a>>) -> &'a str {
        let Handle::Name(value) = id.0 else {
            panic!("context items retain their original borrowed name")
        };
        value
    }

    #[test]
    fn context_items_use_original_top_level_optional_map_and_binding_rules() {
        let params = vec![
            plain(base("Var")),
            plain(TypeExpr::Collection(CollectionKind::Bag, Box::new(base("Elem")), None)),
            plain(TypeExpr::Collection(
                CollectionKind::Map,
                Box::new(base("Elem")),
                Some(Box::new(base("Elem"))),
            )),
            plain(TypeExpr::Collection(
                CollectionKind::Map,
                Box::new(base("Elem")),
                Some(Box::new(base("Other"))),
            )),
            binder(base("Domain"), base("Result"), false),
            binder(TypeExpr::Multi(Box::new(base("Many"))), base("MultiResult"), true),
            binder(
                TypeExpr::Multi(Box::new(base("NotBase"))),
                TypeExpr::Multi(Box::new(base("NotBody"))),
                false,
            ),
            Param::Optional(vec![
                binder(base("IgnoredDomain"), base("OptionalResult"), false),
                binder(base("NotMulti"), base("OptionalMultiResult"), true),
                Param::Optional(vec![Param::Guard("guard".into()), plain(base("Ident"))]),
            ]),
        ];
        let budget = RefCell::new(Budget::default());
        let mut events = Vec::new();
        let (items, bindings) =
            try_convert_term_context_to_items_with(&SchemaContextItemsReader, &params, |event| {
                events.push(match event {
                    ContextItemsEvent::VisitParameter => "visit",
                    ContextItemsEvent::EnterOptional => "optional",
                    ContextItemsEvent::Binding => "binding",
                    _ => "item",
                });
                budget.borrow_mut().context_event(event)
            })
            .expect("original context conversion accepts supported shallow schema observations");
        let observations: Vec<_> = items
            .iter()
            .map(|item| match item {
                AuthoredLegacyItem::NonTerminal { ident, .. } => ("nt", borrowed_name(ident)),
                AuthoredLegacyItem::Binder { category } => ("binder", borrowed_name(category)),
                AuthoredLegacyItem::Collection { element, .. } => {
                    ("collection", borrowed_name(element))
                },
                AuthoredLegacyItem::Terminal(_) => {
                    panic!("context converter never invents terminals")
                },
            })
            .collect();
        assert_eq!(
            observations,
            [
                ("nt", "Var"),
                ("collection", "Elem"),
                ("collection", "Elem"),
                ("binder", "Domain"),
                ("nt", "Result"),
                ("binder", "Many"),
                ("nt", "MultiResult"),
                ("nt", "OptionalResult"),
                ("nt", "OptionalMultiResult"),
                ("nt", "Ident"),
            ]
        );
        assert!(matches!(
            items[0],
            AuthoredLegacyItem::NonTerminal { kind: NonTerminalKind::Var, .. }
        ));
        assert!(matches!(
            items[9],
            AuthoredLegacyItem::NonTerminal { kind: NonTerminalKind::Ident, .. }
        ));
        for (index, kind, expected) in
            [(1, CollectionKind::Bag, "|"), (2, CollectionKind::Map, ",")]
        {
            assert!(matches!(&items[index],
                AuthoredLegacyItem::Collection { kind: actual, separator, open: None, close: None, .. }
                    if *actual == kind && separator == expected));
        }
        assert_eq!(bindings, [(3, vec![4]), (5, vec![6]), (7, vec![7])]);
        assert_eq!(events.iter().filter(|&&event| event == "binding").count(), 3);
        assert_eq!(events.iter().filter(|&&event| event == "optional").count(), 2);
        let budget = budget.borrow();
        assert_eq!((budget.nodes, budget.edges, budget.slots, budget.strings), (0, 10, 10, 2));
        assert_eq!(
            budget.context_work,
            events.len() + 3,
            "each binding costs two, all other callbacks one"
        );
    }

    #[test]
    fn context_items_admission_counts_exact_content_and_aggregate_occurrences() {
        let original = "Original".to_owned();
        let mut budget = Budget {
            nodes: 9,
            context_work: MAX_CANONICAL_COLLECTION_ITEMS - 3,
            ..Budget::default()
        };
        budget
            .context_event(ContextItemsEvent::Nonterminal(&original))
            .expect("one item edge, slot and event exactly fit");
        assert_eq!((budget.nodes, budget.edges, budget.slots, budget.strings), (9, 1, 1, 0));
        assert!(budget
            .context_event(ContextItemsEvent::VisitParameter)
            .is_err());
        assert_eq!(budget.context_work, MAX_CANONICAL_COLLECTION_ITEMS - 2);

        let budget = RefCell::new(Budget {
            context_work: MAX_CANONICAL_COLLECTION_ITEMS - 2,
            ..Budget::default()
        });
        let source = Source { _rules: &[], budget: &budget };
        let params = [Param::Guard("g".into())];
        assert!(source
            .context_items(&params)
            .expect("first rule visit fits")
            .is_empty());
        assert!(source
            .context_items(&params)
            .expect("second rule visit fits")
            .is_empty());
        assert!(
            source.context_items(&params).is_err(),
            "third rule does not reset aggregate work"
        );
        assert_eq!(budget.borrow().context_work, MAX_CANONICAL_COLLECTION_ITEMS);
    }

    #[test]
    fn context_items_separator_refusal_stops_before_item_and_suffix() {
        let params = [
            plain(TypeExpr::Collection(CollectionKind::List, Box::new(base("Elem")), None)),
            plain(base("NeverVisited")),
        ];
        let budget = RefCell::new(Budget {
            strings: crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES,
            ..Budget::default()
        });
        let mut callbacks = 0;
        let result =
            try_convert_term_context_to_items_with(&SchemaContextItemsReader, &params, |event| {
                callbacks += 1;
                budget.borrow_mut().context_event(event)
            });
        assert!(matches!(result, Err(ContextItemsError::Admission(_))));
        assert_eq!(callbacks, 2, "visit then collection refusal, no later parameter");
        let budget = budget.borrow();
        assert_eq!((budget.nodes, budget.edges, budget.slots, budget.context_work), (0, 0, 0, 1));
        assert_eq!(
            budget.strings,
            crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES + 1,
            "original string helper retains its private aggregate assignment on refusal"
        );
    }

    #[test]
    fn judgement_items_derive_once_but_bnf_items_and_presence_are_unchanged() {
        let rules = [
            term(Some(vec![plain(base("Ident"))]), TermBody::Judgement(vec![])),
            term(
                Some(vec![plain(base("IgnoredContextItem"))]),
                TermBody::Bnf(vec![BnfNode::Literal("bnf".into())]),
            ),
            term(None, TermBody::Judgement(vec![])),
            term(None, TermBody::Bnf(vec![])),
        ];
        let captured =
            capture(&rules).expect("original body-form context observations remain capturable");
        let first = rule(&captured.store, captured.roots[0]);
        assert_eq!(first.items.len(), 1);
        let AuthoredLegacyItem::NonTerminal { ident, kind } = &first.items[0] else {
            panic!("judgement context emits the original nonterminal item")
        };
        assert_eq!(
            (*kind, named(&captured.store, *ident).spelling.as_str()),
            (NonTerminalKind::Ident, "Ident")
        );
        let bnf = rule(&captured.store, captured.roots[1]);
        assert!(bnf.term_context.is_some());
        assert!(matches!(&bnf.items[..], [AuthoredLegacyItem::Terminal(text)] if text == "bnf"));
        assert!(rule(&captured.store, captured.roots[2])
            .term_context
            .is_some());
        assert!(rule(&captured.store, captured.roots[2]).items.is_empty());
        assert!(rule(&captured.store, captured.roots[3])
            .term_context
            .is_none());
    }

    #[test]
    fn context_items_deep_optional_conversion_and_capture_use_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut nested = plain(base("Leaf"));
                for _ in 0..10_000 {
                    nested = Param::Optional(vec![nested]);
                }
                let rules = [term(Some(vec![nested]), TermBody::Judgement(vec![]))];
                let captured = capture(&rules)
                    .expect("original optional frame loop and capture remain stack safe");
                assert_eq!(rule(&captured.store, captured.roots[0]).items.len(), 1);
                drop(captured);
                drop(rules);
            })
            .expect("spawn small-stack schema context test")
            .join()
            .expect("context conversion and source/capture cleanup remain stack safe");
    }
    fn syntax(store: &AuthoredRuleStore, rule_id: u32) -> &[AuthoredSyntax] {
        let id = rule(store, rule_id)
            .syntax_pattern
            .expect("authored capture fixture must be valid");
        let AuthoredNode::Syntax(syntax) = node(store, id.0) else {
            panic!("syntax")
        };
        syntax
    }

    #[test]
    fn retains_normalized_contexts_and_ordered_roots() {
        let rules = [
            term(None, TermBody::Judgement(vec![])),
            term(Some(vec![]), TermBody::Judgement(vec![])),
            term(None, TermBody::Bnf(vec![])),
        ];
        let captured = capture(&rules).expect("authored capture fixture must be valid");
        let rs: Vec<_> = captured
            .roots
            .iter()
            .map(|id| rule(&captured.store, *id))
            .collect();
        assert!(rs[0].term_context.is_some());
        assert!(rs[1].term_context.is_some());
        assert!(rs[0].syntax_pattern.is_some() && rs[1].syntax_pattern.is_some());
        assert!(rs[2].syntax_pattern.is_none());
        assert!(captured.roots.windows(2).all(|ids| ids[0] < ids[1]));
        assert_ne!(rs[0].label, rs[1].label);
        assert_eq!(
            named(&captured.store, rs[0].label).equality_class,
            named(&captured.store, rs[1].label).equality_class
        );
    }

    #[test]
    fn preserves_ordered_duplicate_params_full_types_and_keyed_pathmap() {
        let rules = [term(
            Some(vec![
                Param::Plain {
                    name: "dup".into(),
                    ty: TypeExpr::Base("Expr".into()),
                },
                Param::Plain {
                    name: "dup".into(),
                    ty: TypeExpr::Collection(
                        CollectionKind::PathMap,
                        Box::new(TypeExpr::Base("Key".into())),
                        Some(Box::new(TypeExpr::Base("Value".into()))),
                    ),
                },
                Param::Binder {
                    binder: "b".into(),
                    body: "body".into(),
                    multiple: true,
                    ty: TypeExpr::Arrow(
                        Box::new(TypeExpr::Base("Domain".into())),
                        Box::new(TypeExpr::Base("Result".into())),
                    ),
                },
                Param::Optional(vec![
                    Param::Guard("guard".into()),
                    Param::Plain {
                        name: "multi".into(),
                        ty: TypeExpr::Multi(Box::new(TypeExpr::Base("Hidden".into()))),
                    },
                ]),
            ]),
            TermBody::Judgement(vec![]),
        )];
        let c = capture(&rules).expect("authored capture fixture must be valid");
        let context = rule(&c.store, c.roots[0])
            .term_context
            .expect("authored capture fixture must be valid");
        let AuthoredNode::Params(params) = node(&c.store, context.0) else {
            panic!("unexpected retained observation variant in source fixture")
        };
        assert_eq!(params.len(), 4);
        let AuthoredNode::Param(AuthoredParam::Simple { name: left, .. }) =
            node(&c.store, params[0].0)
        else {
            panic!("unexpected retained observation variant in source fixture")
        };
        let AuthoredNode::Param(AuthoredParam::Simple { name: right, ty }) =
            node(&c.store, params[1].0)
        else {
            panic!("unexpected retained observation variant in source fixture")
        };
        assert_ne!(left, right);
        assert_eq!(named(&c.store, *left).equality_class, named(&c.store, *right).equality_class);
        let AuthoredNode::Type(AuthoredType::KeyedPathMap { key, value }) = node(&c.store, ty.0)
        else {
            panic!("unexpected retained observation variant in source fixture")
        };
        assert_ne!(key, value);
        for (id, expected) in [(*key, "Key"), (*value, "Value")] {
            let AuthoredNode::Type(AuthoredType::Base(name)) = node(&c.store, id.0) else {
                panic!("unexpected retained observation variant in source fixture")
            };
            assert_eq!(named(&c.store, *name).spelling, expected);
        }
        let AuthoredNode::Param(AuthoredParam::MultiAbstraction { binder, body, ty }) =
            node(&c.store, params[2].0)
        else {
            panic!("unexpected retained observation variant in source fixture")
        };
        assert_eq!(named(&c.store, *binder).spelling, "b");
        assert_eq!(named(&c.store, *body).spelling, "body");
        let AuthoredNode::Type(AuthoredType::Arrow { domain, codomain }) = node(&c.store, ty.0)
        else {
            panic!("the original arrow retains both children")
        };
        for (id, expected) in [(*domain, "Domain"), (*codomain, "Result")] {
            let AuthoredNode::Type(AuthoredType::Base(name)) = node(&c.store, id.0) else {
                panic!("arrow child retains its original base observation")
            };
            assert_eq!(named(&c.store, *name).spelling, expected);
        }
        assert!((0..c.store.len() as u32).any(|id| matches!(
            node(&c.store, id),
            AuthoredNode::Type(AuthoredType::MultiBinder { inner })
                if matches!(node(&c.store, inner.0), AuthoredNode::Type(AuthoredType::Base(name))
                    if named(&c.store, *name).spelling == "Hidden")
        )));
    }

    #[test]
    fn sourced_separators_keep_distinct_occurrences_and_original_convention() {
        let make_chain = || {
            SyntaxNode::Separated(
                Box::new(SyntaxNode::Map {
                    source: Box::new(SyntaxNode::Zip("left".into(), "right".into())),
                    bindings: vec!["x".into(), "x".into()],
                    body: vec![SyntaxNode::Reference("x".into())],
                }),
                ",".into(),
            )
        };
        let rules = [term(
            None,
            TermBody::Judgement(vec![
                make_chain(),
                make_chain(),
                SyntaxNode::Separated(Box::new(SyntaxNode::Reference("plain".into())), ";".into()),
                SyntaxNode::Separated(
                    Box::new(SyntaxNode::Literal("runtime-only".into())),
                    "!".into(),
                ),
            ]),
        )];
        let c = capture(&rules).expect("authored capture fixture must be valid");
        let mut chains = Vec::new();
        for (index, expr) in syntax(&c.store, c.roots[0]).iter().enumerate() {
            let AuthoredSyntax::Op(id) = expr else {
                panic!("unexpected retained observation variant in source fixture")
            };
            let AuthoredNode::Operation(AuthoredOperation::Sep { collection, separator, source }) =
                node(&c.store, id.0)
            else {
                panic!("unexpected retained observation variant in source fixture")
            };
            if index == 2 {
                assert!(source.is_none());
                assert_eq!(separator, ";");
                assert_eq!(named(&c.store, *collection).spelling, "plain");
            } else {
                assert_eq!(named(&c.store, *collection).spelling, AUTHORED_CHAIN_COLLECTION_NAME);
                if index < 2 {
                    chains.push((
                        *collection,
                        source.expect("authored capture fixture must be valid"),
                    ));
                    let AuthoredNode::Operation(AuthoredOperation::Map { source, params, body }) =
                        node(&c.store, source.expect("authored capture fixture must be valid").0)
                    else {
                        panic!("unexpected retained observation variant in source fixture")
                    };
                    assert!(matches!(
                        node(&c.store, source.0),
                        AuthoredNode::Operation(AuthoredOperation::Zip { .. })
                    ));
                    let AuthoredNode::Names(names) = node(&c.store, params.0) else {
                        panic!("unexpected retained observation variant in source fixture")
                    };
                    assert_eq!(names.len(), 2);
                    assert_ne!(names[0], names[1]);
                    assert_eq!(
                        named(&c.store, names[0]).equality_class,
                        named(&c.store, names[1]).equality_class
                    );
                    assert!(
                        matches!(node(&c.store, body.0), AuthoredNode::Syntax(values) if values.len() == 1)
                    );
                } else {
                    assert!(matches!(
                        node(&c.store, source.expect("authored capture fixture must be valid").0),
                        AuthoredNode::Operation(AuthoredOperation::Unsupported { tag: 0 })
                    ));
                }
            }
        }
        assert_ne!(chains[0].0, chains[1].0);
        assert_ne!(chains[0].1, chains[1].1);
        assert_eq!(
            named(&c.store, chains[0].0).equality_class,
            named(&c.store, chains[1].0).equality_class
        );
    }

    #[test]
    fn legacy_observations_preserve_original_classifier_and_half_delimiters() {
        let rules = [term(
            None,
            TermBody::Bnf(vec![
                BnfNode::Literal("(".into()),
                BnfNode::Nonterminal("Ident".into()),
                BnfNode::Binding("Expr".into()),
                BnfNode::Collection {
                    kind: CollectionKind::List,
                    element: "Expr".into(),
                    separator: ",".into(),
                    open: Some("[".into()),
                    close: None,
                },
            ]),
        )];
        let c = capture(&rules).expect("authored capture fixture must be valid");
        let items = &rule(&c.store, c.roots[0]).items;
        assert!(matches!(&items[0], AuthoredLegacyItem::Terminal(text) if text == "("));
        assert!(
            matches!(&items[1], AuthoredLegacyItem::NonTerminal { kind, .. } if *kind == NonTerminalKind::classify("Ident"))
        );
        assert!(matches!(&items[2], AuthoredLegacyItem::Binder { .. }));
        assert!(
            matches!(&items[3], AuthoredLegacyItem::Collection { open: Some(open), close: None, separator, .. } if open == "[" && separator == ",")
        );
    }

    #[test]
    fn prepaid_counts_equal_owned_observations_without_finish_recharge() {
        let rules = [term(
            Some(vec![Param::Optional(vec![
                Param::Guard("g".into()),
                Param::Plain {
                    name: "function".into(),
                    ty: TypeExpr::Arrow(
                        Box::new(TypeExpr::Multi(Box::new(TypeExpr::Base("Domain".into())))),
                        Box::new(TypeExpr::Base("Result".into())),
                    ),
                },
            ])]),
            TermBody::Judgement(vec![
                SyntaxNode::Literal("lit".into()),
                SyntaxNode::Token {
                    name: "token".into(),
                    binding: Some("bind".into()),
                },
                SyntaxNode::ForeignLanguage {
                    binding: "flt".into(),
                    open: "open".into(),
                    close: "close".into(),
                },
                SyntaxNode::Optional(vec![]),
            ]),
        )];
        let budget =
            RefCell::new(Budget::roots(1).expect("authored capture fixture must be valid"));
        let mut source = Source { _rules: &rules, budget: &budget };
        let roots = [(AuthoredNodeTag::Rule, Handle::Rule(&rules[0]))];
        let c = capture_authored_nodes(&mut source, &roots, |phase, node| {
            budget.borrow().phase(phase, node)
        })
        .expect("authored capture fixture must be valid");
        let (mut edges, mut slots, mut strings) = (0, 0, 0);
        for id in 0..c.store.len() as u32 {
            let value = node(&c.store, id);
            value
                .try_for_each_reference(|_, _| {
                    edges += 1;
                    Ok::<_, ()>(())
                })
                .expect("authored capture fixture must be valid");
            match value {
                AuthoredNode::Name(name) => strings += name.spelling.len(),
                AuthoredNode::Names(values) => slots += values.len(),
                AuthoredNode::Params(values) => slots += values.len(),
                AuthoredNode::Syntax(values) => {
                    slots += values.len();
                    for value in values {
                        if let AuthoredSyntax::Literal(value) = value {
                            strings += value.len();
                        }
                    }
                },
                AuthoredNode::Rule(rule) => {
                    slots += rule.items.len();
                    for item in &rule.items {
                        if let AuthoredLegacyItem::Collection { separator, open, close, .. } = item
                        {
                            strings += separator.len();
                            strings += open.as_ref().map_or(0, String::len);
                            strings += close.as_ref().map_or(0, String::len);
                        }
                    }
                },
                _ => {},
            }
        }
        let budget = budget.borrow();
        assert_eq!(
            (budget.nodes, budget.edges, budget.slots, budget.strings),
            (c.store.len(), edges, slots, strings)
        );
    }

    #[test]
    fn source_copy_and_root_admission_refuse_before_producing_owned_recipes() {
        assert!(Budget::roots(MAX_CANONICAL_COLLECTION_ITEMS + 1).is_err());
        let value = "x".repeat(MAX_CANONICAL_STRING_BYTES + 1);
        let budget = RefCell::new(Budget::default());
        let mut source = Source { _rules: &[], budget: &budget };
        assert!(source.shallow(Handle::Name(&value)).is_err());
        assert_eq!(budget.borrow().nodes, 0);
        budget.borrow_mut().nodes = MAX_CANONICAL_VALUE_NODES;
        assert!(source
            .shallow(Handle::ChainName(&SyntaxNode::Literal(String::new())))
            .is_err());
        assert_eq!(budget.borrow().nodes, MAX_CANONICAL_VALUE_NODES);
    }

    #[test]
    fn retained_caps_are_exact_logical_sizes_not_finish_allocation_counts() {
        let mut budget = Budget {
            nodes: MAX_CANONICAL_VALUE_NODES - 1,
            ..Budget::default()
        };
        budget
            .observe(0, 0)
            .expect("exact retained node limit fits");
        assert!(budget.observe(0, 0).is_err());
        let mut budget = Budget {
            roots: 1,
            edges: MAX_CANONICAL_COLLECTION_ITEMS - 2,
            ..Budget::default()
        };
        budget
            .observe(0, 1)
            .expect("root plus edges plus payload slots exactly fits");
        assert!(budget.observe(0, 1).is_err());
        let mut budget = Budget {
            strings: crate::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES,
            ..Budget::default()
        };
        budget
            .string("")
            .expect("zero bytes do not consume more content");
        assert!(budget.string("x").is_err());
    }

    #[test]
    fn phase_refuses_unadmitted_map_store_class_or_frame_growth() {
        let budget = Budget {
            roots: 1,
            nodes: 2,
            edges: 3,
            ..Budget::default()
        };
        let name: AuthoredNode =
            AuthoredNode::Name(AuthoredName { spelling: "n".into(), equality_class: 0 });
        let allowed = AuthoredCaptureAdmission {
            phase: AuthoredCapturePhase::Enter,
            memoized_nodes: 1,
            stored_nodes: 1,
            name_classes: 1,
            scheduled_frames: 6,
        };
        budget
            .phase(allowed, &name)
            .expect("derived frame ceiling and node occupancies fit");
        assert!(budget
            .phase(AuthoredCaptureAdmission { memoized_nodes: 2, ..allowed }, &name)
            .is_err());
        assert!(budget
            .phase(
                AuthoredCaptureAdmission {
                    phase: AuthoredCapturePhase::Finish,
                    stored_nodes: 2,
                    ..allowed
                },
                &name
            )
            .is_err());
        assert!(budget
            .phase(
                AuthoredCaptureAdmission {
                    phase: AuthoredCapturePhase::Finish,
                    name_classes: 2,
                    ..allowed
                },
                &name
            )
            .is_err());
        assert!(budget
            .phase(AuthoredCaptureAdmission { scheduled_frames: 7, ..allowed }, &name)
            .is_err());
    }

    #[test]
    fn deep_source_capture_and_flat_store_lifecycle_use_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut param = Param::Guard("leaf".into());
                for _ in 0..4000 {
                    param = Param::Optional(vec![param]);
                }
                let rules = [term(Some(vec![param]), TermBody::Judgement(vec![]))];
                let c = capture(&rules).expect("deep source capture must use the core worklist");
                assert!(c.store.len() > 8000);
                c.store
                    .validate()
                    .expect("deep captured store validates iteratively");
                drop(c.store.clone());
                drop(c);
                drop(rules);
            })
            .expect("small stack test thread starts")
            .join()
            .expect("flat lifecycle stays on heap worklists");
    }

    #[test]
    fn runtime_bnf_defaults_agree_and_nonempty_context_is_retained_and_validated() {
        let s = |text: &str| RhoValue::String(text.into());
        let make = |context: Option<RhoValue>| {
            let mut fields = BTreeMap::from([
                ("label".into(), s("Bnf")),
                ("category".into(), s("Expr")),
                ("items".into(), RhoValue::List(vec![RhoValue::List(vec![s("lit"), s("b")])])),
            ]);
            if let Some(context) = context {
                fields.insert("context".into(), context);
            }
            RhoValue::Map(BTreeMap::from([
                ("mettail".into(), s("language/2")),
                ("name".into(), s("BnfContexts")),
                ("types".into(), RhoValue::List(vec![s("Expr")])),
                ("terms".into(), RhoValue::List(vec![RhoValue::Map(fields)])),
            ]))
        };
        let absent =
            crate::canonical::value_to_core(&make(None)).expect("absent BNF context lowers");
        let empty = crate::canonical::value_to_core(&make(Some(RhoValue::List(vec![]))))
            .expect("empty BNF context lowers");
        assert_eq!(absent, empty);
        assert_eq!(
            absent.fingerprint().expect("absent BNF fingerprint"),
            empty.fingerprint().expect("empty BNF fingerprint")
        );
        let nonempty = make(Some(RhoValue::List(vec![RhoValue::List(vec![
            s("param"),
            s("unused"),
            s("Expr"),
        ])])));
        let retained = crate::canonical::value_to_core(&nonempty)
            .expect("unused valid BNF parameter remains accepted");
        let store = retained.authored.as_ref().expect("BNF source is retained");
        let source = rule(store, retained.productions[0].authored.expect("BNF source root").0);
        assert!(source.syntax_pattern.is_none());
        let params = source
            .term_context
            .expect("nonempty BNF context is not discarded");
        assert!(matches!(node(store, params.0), AuthoredNode::Params(params) if params.len() == 1));
        let invalid = make(Some(RhoValue::List(vec![RhoValue::List(vec![
            s("param"),
            s("unused"),
            s("Missing"),
        ])])));
        assert!(
            crate::canonical::value_to_core(&invalid).is_err(),
            "original parameter validation still runs for BNF"
        );
    }

    #[test]
    fn actual_value_lowering_attaches_one_store_and_normalizes_judgement_context() {
        let s = |value: &str| RhoValue::String(value.into());
        let make = |label: &str, context: bool| {
            let mut fields = BTreeMap::from([
                ("label".into(), s(label)),
                ("category".into(), s("Expr")),
                ("syntax".into(), RhoValue::List(vec![RhoValue::List(vec![s("lit"), s(label)])])),
            ]);
            if context {
                fields.insert("context".into(), RhoValue::List(vec![]));
            }
            RhoValue::Map(fields)
        };
        let value = RhoValue::Map(BTreeMap::from([
            ("mettail".into(), s("language/2")),
            ("name".into(), s("Retained")),
            ("types".into(), RhoValue::List(vec![s("Expr")])),
            ("terms".into(), RhoValue::List(vec![make("Absent", false), make("Empty", true)])),
        ]));
        let core = crate::canonical::value_to_core(&value)
            .expect("authored capture fixture must be valid");
        let store = core
            .authored
            .as_ref()
            .expect("authored capture fixture must be valid");
        assert_eq!(core.productions.len(), 2);
        for production in &core.productions {
            let rule = rule(
                store,
                production
                    .authored
                    .expect("authored capture fixture must be valid")
                    .0,
            );
            assert_eq!(named(store, rule.label).spelling, production.label);
            assert!(rule.term_context.is_some());
        }
    }
}
