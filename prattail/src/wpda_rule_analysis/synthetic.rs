//! Original synthetic-rule scheduling over neutral generated shapes.
//!
//! User rules remain opaque owned payloads. The adapter clones only retained
//! users, normalizes them in grouped order, and resolves source-specific
//! metadata lazily at the original synthesis sites. This module does not
//! normalize grammar syntax or classify native carriers.
//!
//! The phase order, current-list variable scan, delimiter split, and binder
//! loops are relocated from the original macro synthetic-rule builder.
//! Synthetic recipes are materialized at each original insertion site, so a
//! constructor failure cannot be deferred into category-bucket output order.

use super::atomic::{LegacyAtomicItem, LegacyAtomicKind};
use super::InfixSyntaxShape;

/// A source rule with its original category observation.
pub struct UserInput<'a, U> {
    pub category: String,
    pub source: &'a U,
}

/// Direct observations of a declared category, in declaration order.
///
/// Labels, collection elements and binder eligibility are deliberately absent:
/// their original helpers are invoked lazily through the adapter.
pub struct TypeInput<'a, T> {
    pub name: String,
    pub is_data: bool,
    pub has_native: bool,
    pub has_collection: bool,
    pub source: &'a T,
}

/// Existing collection metadata resolved by the source adapter.
pub struct CollectionRecipe<K> {
    pub kind: K,
    pub label: String,
    pub element_category: String,
    pub open: String,
    pub close: String,
    pub separator: String,
}

/// Structural fields of an original synthetic rule.
///
/// The remaining metadata has the original fixed synthetic defaults. Static
/// materialization supplies those defaults without inspecting user syntax.
pub struct SyntheticRule<K> {
    pub label: String,
    pub category: String,
    pub items: Vec<LegacyAtomicItem>,
    pub term_context: Option<Vec<SyntheticParam<K>>>,
    pub syntax_pattern: Option<Vec<InfixSyntaxShape>>,
}

/// Exactly the parameter forms constructed by the original synthesis passes.
pub enum SyntheticParam<K> {
    Simple {
        name: String,
        ty: SyntheticType<K>,
    },
    Abstraction {
        binder: String,
        body: String,
        domain: String,
        codomain: String,
    },
}

/// Exactly the simple-parameter types constructed by synthesis.
pub enum SyntheticType<K> {
    Base(String),
    Collection { kind: K, element: String },
}

/// Source-specific operations retained at their original decision sites.
///
/// Native labels, collection metadata and binder detection reuse existing
/// source helpers. The shared builder neither implements nor guesses them.
pub trait SynthesisAdapter {
    type SourceUser;
    type SourceType;
    type RulePayload;
    type CollectionKind: Clone;

    fn clone_user(&mut self, source: &Self::SourceUser) -> Self::RulePayload;
    fn normalize_user(&mut self, rule: &mut Self::RulePayload);
    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> bool;
    fn materialize_synthetic(
        &mut self,
        rule: SyntheticRule<Self::CollectionKind>,
    ) -> Self::RulePayload;
    fn has_literal_block(&mut self, source: &Self::SourceType) -> bool;
    fn literal_label(&mut self, source: &Self::SourceType) -> String;
    fn collection(&mut self, source: &Self::SourceType) -> CollectionRecipe<Self::CollectionKind>;
    fn var_label(&mut self, source: &Self::SourceType) -> String;
    fn declares_binder(&mut self) -> bool;
}

/// Original loop sites, including the separate grouped-normalization phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SynthesisPhase {
    Users,
    Normalize,
    Native,
    Collections,
    Variables,
    BinderNames,
    Pairs,
    Lambdas,
}

/// Borrowed callback inputs at their original invocation sites.
pub enum SynthesisCallback<'a, U, T, P, K> {
    CloneUser(&'a U),
    NormalizeUser(&'a P),
    FirstItemIsVar(&'a P),
    Materialize(&'a SyntheticRule<K>),
    HasLiteralBlock(&'a T),
    LiteralLabel(&'a T),
    Collection(&'a T),
    VarLabel(&'a T),
    DeclaresBinder,
}

/// Inline admission, not an allocated execution plan.
///
/// Policies charge finite logical work and shallow storage before its site.
/// Original Unicode lowercase/format operations and adapter callbacks remain
/// their original implementations: this is not a physical-RSS or universal
/// allocator-failure guarantee. Adapters must admit their own retained output
/// before copying/appending it; moves do not constitute another logical copy.
pub enum SynthesisEvent<'a, U, T, P, K> {
    CategoryIndexSlots(usize),
    CategoryIndexEntry {
        index: usize,
        name: &'a str,
    },
    BucketSlots(usize),
    Visit(SynthesisPhase),
    CategoryLookup(&'a str),
    RowSlot(usize),
    StringCopy(&'a str),
    TrimOpen(&'a str),
    Lowercase(&'a str),
    Format {
        prefix: &'a str,
        body: &'a str,
        suffix: &'a str,
    },
    RecipeSlots {
        items: usize,
        params: usize,
        syntax: usize,
    },
    BinderNameSlots(usize),
    VectorKindClone(&'a K),
    Callback(SynthesisCallback<'a, U, T, P, K>),
}

pub type SynthesisEventFor<'a, A> = SynthesisEvent<
    'a,
    <A as TrySynthesisAdapter>::SourceUser,
    <A as TrySynthesisAdapter>::SourceType,
    <A as TrySynthesisAdapter>::RulePayload,
    <A as TrySynthesisAdapter>::CollectionKind,
>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SynthesisError<E> {
    Admission(E),
    Callback(E),
    Allocation,
}

/// Fallible callbacks over one private owner. On error, the owner and partial
/// rows are dropped; callers receive neither. No payload Clone is required.
pub trait TrySynthesisAdapter: Sized {
    type SourceUser;
    type SourceType;
    type RulePayload;
    type CollectionKind: Clone;
    type Error;

    fn admit(&mut self, event: SynthesisEventFor<'_, Self>) -> Result<(), Self::Error>;
    fn clone_user(&mut self, source: &Self::SourceUser) -> Result<Self::RulePayload, Self::Error>;
    fn normalize_user(self, rule: &mut Self::RulePayload) -> Result<Self, Self::Error>;
    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> Result<bool, Self::Error>;
    fn materialize_synthetic(
        self,
        rule: SyntheticRule<Self::CollectionKind>,
    ) -> Result<(Self, Self::RulePayload), Self::Error>;
    fn has_literal_block(&mut self, source: &Self::SourceType) -> Result<bool, Self::Error>;
    fn literal_label(&mut self, source: &Self::SourceType) -> Result<String, Self::Error>;
    fn collection(
        &mut self,
        source: &Self::SourceType,
    ) -> Result<CollectionRecipe<Self::CollectionKind>, Self::Error>;
    fn var_label(&mut self, source: &Self::SourceType) -> Result<String, Self::Error>;
    fn declares_binder(&mut self) -> Result<bool, Self::Error>;
}

fn admit<A: TrySynthesisAdapter>(
    adapter: &mut A,
    event: SynthesisEventFor<'_, A>,
) -> Result<(), SynthesisError<A::Error>> {
    adapter.admit(event).map_err(SynthesisError::Admission)
}

fn reserve<T, E>(values: &mut Vec<T>, additional: usize) -> Result<(), SynthesisError<E>> {
    values
        .try_reserve_exact(additional)
        .map_err(|_| SynthesisError::Allocation)
}

// Category rows grow at original insertion sites; unlike fixed recipe rosters,
// their final lengths are not known without an extra synthesis traversal.
fn reserve_row<T, E>(values: &mut Vec<T>) -> Result<(), SynthesisError<E>> {
    values
        .try_reserve(1)
        .map_err(|_| SynthesisError::Allocation)
}

fn copy_admitted<E>(text: &str) -> Result<String, SynthesisError<E>> {
    let mut output = String::new();
    output
        .try_reserve_exact(text.len())
        .map_err(|_| SynthesisError::Allocation)?;
    output.push_str(text);
    Ok(output)
}

fn copy<A: TrySynthesisAdapter>(
    adapter: &mut A,
    text: &str,
) -> Result<String, SynthesisError<A::Error>> {
    admit(adapter, SynthesisEvent::StringCopy(text))?;
    copy_admitted(text)
}

type RecipeVectors<K> = (Vec<LegacyAtomicItem>, Vec<SyntheticParam<K>>, Vec<InfixSyntaxShape>);

fn recipe_vectors<A: TrySynthesisAdapter>(
    adapter: &mut A,
    items: usize,
    params: usize,
    syntax: usize,
) -> Result<RecipeVectors<A::CollectionKind>, SynthesisError<A::Error>> {
    admit(adapter, SynthesisEvent::RecipeSlots { items, params, syntax })?;
    let (mut i, mut p, mut s) = (Vec::new(), Vec::new(), Vec::new());
    reserve(&mut i, items)?;
    reserve(&mut p, params)?;
    reserve(&mut s, syntax)?;
    Ok((i, p, s))
}

fn emit<A: TrySynthesisAdapter>(
    mut adapter: A,
    rows: &mut [Vec<A::RulePayload>],
    index: usize,
    rule: SyntheticRule<A::CollectionKind>,
) -> Result<A, SynthesisError<A::Error>> {
    admit(&mut adapter, SynthesisEvent::RowSlot(index))?;
    reserve_row(&mut rows[index])?;
    admit(&mut adapter, SynthesisEvent::Callback(SynthesisCallback::Materialize(&rule)))?;
    let (adapter, payload) = adapter
        .materialize_synthetic(rule)
        .map_err(SynthesisError::Callback)?;
    rows[index].push(payload);
    Ok(adapter)
}

struct InfallibleAdapter<'a, A>(&'a mut A);

impl<A: SynthesisAdapter> TrySynthesisAdapter for InfallibleAdapter<'_, A> {
    type SourceUser = A::SourceUser;
    type SourceType = A::SourceType;
    type RulePayload = A::RulePayload;
    type CollectionKind = A::CollectionKind;
    type Error = std::convert::Infallible;

    fn admit(&mut self, _: SynthesisEventFor<'_, Self>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn clone_user(&mut self, source: &Self::SourceUser) -> Result<Self::RulePayload, Self::Error> {
        Ok(self.0.clone_user(source))
    }
    fn normalize_user(self, rule: &mut Self::RulePayload) -> Result<Self, Self::Error> {
        self.0.normalize_user(rule);
        Ok(self)
    }
    fn first_item_is_var(&mut self, rule: &Self::RulePayload) -> Result<bool, Self::Error> {
        Ok(self.0.first_item_is_var(rule))
    }
    fn materialize_synthetic(
        self,
        rule: SyntheticRule<Self::CollectionKind>,
    ) -> Result<(Self, Self::RulePayload), Self::Error> {
        let payload = self.0.materialize_synthetic(rule);
        Ok((self, payload))
    }
    fn has_literal_block(&mut self, source: &Self::SourceType) -> Result<bool, Self::Error> {
        Ok(self.0.has_literal_block(source))
    }
    fn literal_label(&mut self, source: &Self::SourceType) -> Result<String, Self::Error> {
        Ok(self.0.literal_label(source))
    }
    fn collection(
        &mut self,
        source: &Self::SourceType,
    ) -> Result<CollectionRecipe<Self::CollectionKind>, Self::Error> {
        Ok(self.0.collection(source))
    }
    fn var_label(&mut self, source: &Self::SourceType) -> Result<String, Self::Error> {
        Ok(self.0.var_label(source))
    }
    fn declares_binder(&mut self) -> Result<bool, Self::Error> {
        Ok(self.0.declares_binder())
    }
}

/// Build the original per-category user-plus-synthetic rule sequence.
///
/// Category lookup retains the original last-duplicate behavior. User payloads
/// need not implement Clone: the adapter owns the original single clone, and
/// callers receive original and synthetic rules in the same backend payload.
/// Materialization is eager at each original push; no final row-wise conversion
/// can reorder constructor validation or execute after its first failure.
pub fn build_per_category_rules<A: SynthesisAdapter>(
    categories: &[String],
    users: &[UserInput<'_, A::SourceUser>],
    types: &[TypeInput<'_, A::SourceType>],
    vector_kind: A::CollectionKind,
    adapter: &mut A,
) -> Vec<Vec<A::RulePayload>> {
    match try_build_per_category_rules(
        categories,
        users,
        types,
        vector_kind,
        InfallibleAdapter(adapter),
    ) {
        Ok((_, rows)) => rows,
        Err(SynthesisError::Admission(never) | SynthesisError::Callback(never)) => match never {},
        Err(SynthesisError::Allocation) => panic!("synthetic rule output allocation failed"),
    }
}

/// The original worker, with inline admission and fallible callback boundaries.
/// Only complete success returns the consumed adapter and homogeneous rows.
pub fn try_build_per_category_rules<A: TrySynthesisAdapter>(
    categories: &[String],
    users: &[UserInput<'_, A::SourceUser>],
    types: &[TypeInput<'_, A::SourceType>],
    vector_kind: A::CollectionKind,
    mut adapter: A,
) -> Result<(A, Vec<Vec<A::RulePayload>>), SynthesisError<A::Error>> {
    admit(&mut adapter, SynthesisEvent::CategoryIndexSlots(categories.len()))?;
    let mut cat_idx = std::collections::HashMap::new();
    cat_idx
        .try_reserve(categories.len())
        .map_err(|_| SynthesisError::Allocation)?;
    for (i, name) in categories.iter().enumerate() {
        admit(&mut adapter, SynthesisEvent::CategoryIndexEntry { index: i, name })?;
        cat_idx.insert(name.as_str(), i);
    }
    admit(&mut adapter, SynthesisEvent::BucketSlots(categories.len()))?;
    let mut per_cat: Vec<Vec<A::RulePayload>> = Vec::new();
    reserve(&mut per_cat, categories.len())?;
    per_cat.resize_with(categories.len(), Vec::new);

    // 1. User rules in source order; clone only after category admission.
    for rule in users {
        admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Users))?;
        admit(&mut adapter, SynthesisEvent::CategoryLookup(&rule.category))?;
        if let Some(&i) = cat_idx.get(rule.category.as_str()) {
            admit(&mut adapter, SynthesisEvent::RowSlot(i))?;
            reserve_row(&mut per_cat[i])?;
            admit(
                &mut adapter,
                SynthesisEvent::Callback(SynthesisCallback::CloneUser(rule.source)),
            )?;
            per_cat[i].push(
                adapter
                    .clone_user(rule.source)
                    .map_err(SynthesisError::Callback)?,
            );
        }
    }

    // 1b. Preserve the original grouped normalization phase and opaque payload.
    for cat_rules in per_cat.iter_mut() {
        admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Normalize))?;
        for rule in cat_rules.iter_mut() {
            admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Normalize))?;
            admit(&mut adapter, SynthesisEvent::Callback(SynthesisCallback::NormalizeUser(rule)))?;
            adapter = adapter
                .normalize_user(rule)
                .map_err(SynthesisError::Callback)?;
        }
    }

    // 2. Synthetic literal-patterned rules, in declared-type order.
    for type_def in types {
        admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Native))?;
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        admit(&mut adapter, SynthesisEvent::CategoryLookup(cat_name))?;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        if type_def.has_collection {
            continue;
        }
        // Preserve the original probe, which is not a synthesis gate.
        admit(
            &mut adapter,
            SynthesisEvent::Callback(SynthesisCallback::HasLiteralBlock(type_def.source)),
        )?;
        let _has_literal_block = adapter
            .has_literal_block(type_def.source)
            .map_err(SynthesisError::Callback)?;
        if !type_def.has_native {
            continue;
        }
        admit(
            &mut adapter,
            SynthesisEvent::Callback(SynthesisCallback::LiteralLabel(type_def.source)),
        )?;
        let label = adapter
            .literal_label(type_def.source)
            .map_err(SynthesisError::Callback)?;
        let (mut items, _, _) = recipe_vectors(&mut adapter, 1, 0, 0)?;
        let category = copy(&mut adapter, cat_name)?;
        items.push(LegacyAtomicItem::NonTerminal {
            ident: copy(&mut adapter, cat_name)?,
            kind: LegacyAtomicKind::Category,
        });
        let synthetic = SyntheticRule {
            label,
            category,
            items,
            term_context: None,
            syntax_pattern: None,
        };
        adapter = emit(adapter, &mut per_cat, i, synthetic)?;
    }

    // Stage 1.3. Synthetic collection literals, after all native literals.
    for type_def in types {
        admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Collections))?;
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        admit(&mut adapter, SynthesisEvent::CategoryLookup(cat_name))?;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        if !type_def.has_collection {
            continue;
        }
        admit(
            &mut adapter,
            SynthesisEvent::Callback(SynthesisCallback::Collection(type_def.source)),
        )?;
        let collection = adapter
            .collection(type_def.source)
            .map_err(SynthesisError::Callback)?;
        let (kind, label_str) = (collection.kind, collection.label);
        let (open, close, sep) = (collection.open, collection.close, collection.separator);
        let element_cat_str = collection.element_category;
        // Original trim semantics: remove all trailing '(' and split once.
        admit(&mut adapter, SynthesisEvent::TrimOpen(&open))?;
        let trimmed_open = copy_admitted(open.trim_end_matches('('))?;
        let needs_synth_paren = open != trimmed_open;
        let (items, mut params, mut sp) =
            recipe_vectors(&mut adapter, 0, 1, if needs_synth_paren { 4 } else { 3 })?;
        sp.push(InfixSyntaxShape::Literal(trimmed_open));
        if needs_synth_paren {
            sp.push(InfixSyntaxShape::Literal(copy(&mut adapter, "(")?));
        }
        sp.push(InfixSyntaxShape::Sep {
            collection: copy(&mut adapter, "elems")?,
            separator: sep,
        });
        sp.push(InfixSyntaxShape::Literal(close));
        let category = copy(&mut adapter, cat_name)?;
        params.push(SyntheticParam::Simple {
            name: copy(&mut adapter, "elems")?,
            ty: SyntheticType::Collection { kind, element: element_cat_str },
        });
        let synthetic = SyntheticRule {
            label: label_str,
            category,
            items,
            term_context: Some(params),
            syntax_pattern: Some(sp),
        };
        adapter = emit(adapter, &mut per_cat, i, synthetic)?;
    }

    // 3. Missing Var rules, including native and collection categories.
    for type_def in types {
        admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Variables))?;
        if type_def.is_data {
            continue;
        }
        let cat_name = &type_def.name;
        admit(&mut adapter, SynthesisEvent::CategoryLookup(cat_name))?;
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        // Scan the CURRENT list, including a Var inserted for an earlier
        // duplicate declared type. Preserve the original short-circuit order.
        let mut has_user_var_rule = false;
        for rule in &per_cat[i] {
            admit(&mut adapter, SynthesisEvent::Callback(SynthesisCallback::FirstItemIsVar(rule)))?;
            if adapter
                .first_item_is_var(rule)
                .map_err(SynthesisError::Callback)?
            {
                has_user_var_rule = true;
                break;
            }
        }
        if has_user_var_rule {
            continue;
        }
        admit(
            &mut adapter,
            SynthesisEvent::Callback(SynthesisCallback::VarLabel(type_def.source)),
        )?;
        let label = adapter
            .var_label(type_def.source)
            .map_err(SynthesisError::Callback)?;
        let (mut items, _, _) = recipe_vectors(&mut adapter, 1, 0, 0)?;
        let category = copy(&mut adapter, cat_name)?;
        items.push(LegacyAtomicItem::NonTerminal {
            ident: copy(&mut adapter, cat_name)?,
            kind: LegacyAtomicKind::Var,
        });
        let synthetic = SyntheticRule {
            label,
            category,
            items,
            term_context: None,
            syntax_pattern: None,
        };
        adapter = emit(adapter, &mut per_cat, i, synthetic)?;
    }

    // 4. Original binder gate, after all literal/collection/variable passes.
    admit(&mut adapter, SynthesisEvent::Callback(SynthesisCallback::DeclaresBinder))?;
    let has_binders = adapter
        .declares_binder()
        .map_err(SynthesisError::Callback)?;
    if has_binders {
        admit(&mut adapter, SynthesisEvent::BinderNameSlots(types.len()))?;
        let mut category_names = Vec::new();
        reserve(&mut category_names, types.len())?;
        for category in types {
            admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::BinderNames))?;
            if !category.is_data {
                category_names.push(copy(&mut adapter, &category.name)?);
            }
        }
        // Original (home, dom) iteration: Apply followed by MApply per pair.
        for home in &category_names {
            admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Pairs))?;
            admit(&mut adapter, SynthesisEvent::CategoryLookup(home))?;
            let Some(&home_i) = cat_idx.get(home.as_str()) else {
                continue;
            };
            for dom in &category_names {
                admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Pairs))?;
                admit(&mut adapter, SynthesisEvent::Lowercase(dom))?;
                let dom_lower = dom.to_lowercase();
                admit(
                    &mut adapter,
                    SynthesisEvent::Format {
                        prefix: "$",
                        body: &dom_lower,
                        suffix: "",
                    },
                )?;
                let dollar_token = format!("${}", dom_lower);
                admit(
                    &mut adapter,
                    SynthesisEvent::Format {
                        prefix: "$$",
                        body: &dom_lower,
                        suffix: "(",
                    },
                )?;
                let ddollar_token = format!("$${}(", dom_lower);
                admit(
                    &mut adapter,
                    SynthesisEvent::Format { prefix: "Apply", body: dom, suffix: "" },
                )?;
                let apply_label = format!("Apply{}", dom);
                admit(
                    &mut adapter,
                    SynthesisEvent::Format { prefix: "MApply", body: dom, suffix: "" },
                )?;
                let mapply_label = format!("MApply{}", dom);

                let (items, mut params, mut syntax) = recipe_vectors(&mut adapter, 0, 2, 6)?;
                let category = copy(&mut adapter, home)?;
                params.push(SyntheticParam::Simple {
                    name: copy(&mut adapter, "f")?,
                    ty: SyntheticType::Base(copy(&mut adapter, home)?),
                });
                params.push(SyntheticParam::Simple {
                    name: copy(&mut adapter, "x")?,
                    ty: SyntheticType::Base(copy(&mut adapter, dom)?),
                });
                syntax.push(InfixSyntaxShape::Literal(dollar_token));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, "(")?));
                syntax.push(InfixSyntaxShape::Param(copy(&mut adapter, "f")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, ",")?));
                syntax.push(InfixSyntaxShape::Param(copy(&mut adapter, "x")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, ")")?));
                let apply_rule = SyntheticRule {
                    label: apply_label,
                    category,
                    items,
                    term_context: Some(params),
                    syntax_pattern: Some(syntax),
                };
                adapter = emit(adapter, &mut per_cat, home_i, apply_rule)?;

                let (items, mut params, mut syntax) = recipe_vectors(&mut adapter, 0, 2, 5)?;
                let category = copy(&mut adapter, home)?;
                params.push(SyntheticParam::Simple {
                    name: copy(&mut adapter, "f")?,
                    ty: SyntheticType::Base(copy(&mut adapter, home)?),
                });
                let name = copy(&mut adapter, "xs")?;
                admit(&mut adapter, SynthesisEvent::VectorKindClone(&vector_kind))?;
                let kind = vector_kind.clone();
                params.push(SyntheticParam::Simple {
                    name,
                    ty: SyntheticType::Collection { kind, element: copy(&mut adapter, dom)? },
                });
                syntax.push(InfixSyntaxShape::Literal(ddollar_token));
                syntax.push(InfixSyntaxShape::Param(copy(&mut adapter, "f")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, ",")?));
                syntax.push(InfixSyntaxShape::Sep {
                    collection: copy(&mut adapter, "xs")?,
                    separator: copy(&mut adapter, ",")?,
                });
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, ")")?));
                let mapply_rule = SyntheticRule {
                    label: mapply_label,
                    category,
                    items,
                    term_context: Some(params),
                    syntax_pattern: Some(syntax),
                };
                adapter = emit(adapter, &mut per_cat, home_i, mapply_rule)?;
            }
        }

        // 4b. Separate original lambda pass: one Lam<Home> per declared home
        // entry, not one lambda for each (home, domain) pair.
        for home in &category_names {
            admit(&mut adapter, SynthesisEvent::Visit(SynthesisPhase::Lambdas))?;
            admit(&mut adapter, SynthesisEvent::CategoryLookup(home))?;
            let Some(&home_i) = cat_idx.get(home.as_str()) else {
                continue;
            };
            for binder_cat in std::iter::once(home) {
                admit(
                    &mut adapter,
                    SynthesisEvent::Format {
                        prefix: "Lam",
                        body: binder_cat,
                        suffix: "",
                    },
                )?;
                let lam_label = format!("Lam{}", binder_cat);
                let (items, mut params, mut syntax) = recipe_vectors(&mut adapter, 0, 1, 6)?;
                let category = copy(&mut adapter, home)?;
                params.push(SyntheticParam::Abstraction {
                    binder: copy(&mut adapter, "x")?,
                    body: copy(&mut adapter, "p")?,
                    domain: copy(&mut adapter, binder_cat)?,
                    codomain: copy(&mut adapter, home)?,
                });
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, "^")?));
                syntax.push(InfixSyntaxShape::Param(copy(&mut adapter, "x")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, ".")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, "{")?));
                syntax.push(InfixSyntaxShape::Param(copy(&mut adapter, "p")?));
                syntax.push(InfixSyntaxShape::Literal(copy(&mut adapter, "}")?));
                let lam_rule = SyntheticRule {
                    label: lam_label,
                    category,
                    items,
                    term_context: Some(params),
                    syntax_pattern: Some(syntax),
                };
                adapter = emit(adapter, &mut per_cat, home_i, lam_rule)?;
            }
        }
    }

    Ok((adapter, per_cat))
}

#[cfg(test)]
mod baseline_tests;

#[cfg(test)]
mod fallible_tests;

#[cfg(test)]
mod tests {
    use super::*;

    struct UserSource {
        label: &'static str,
        is_var: bool,
    }

    struct TypeSource {
        name: &'static str,
    }

    // Deliberately not Clone: original payloads must not be cloned by grouping,
    // normalization or by any post-synthesis output conversion.
    struct Payload {
        label: String,
        is_var: bool,
        normalized: bool,
    }

    #[derive(Default)]
    struct TraceAdapter {
        events: Vec<String>,
        fail_at: Option<&'static str>,
        print_events: bool,
    }

    impl TraceAdapter {
        fn record(&mut self, event: String) {
            if self.print_events {
                eprintln!("SYNTHESIS_TRACE:{event}");
            }
            self.events.push(event);
        }
    }

    impl SynthesisAdapter for TraceAdapter {
        type SourceUser = UserSource;
        type SourceType = TypeSource;
        type RulePayload = Payload;
        type CollectionKind = ();

        fn clone_user(&mut self, source: &UserSource) -> Payload {
            self.record(format!("clone:{}", source.label));
            Payload {
                label: source.label.into(),
                is_var: source.is_var,
                normalized: false,
            }
        }

        fn normalize_user(&mut self, rule: &mut Payload) {
            self.record(format!("normalize:{}", rule.label));
            rule.normalized = true;
        }

        fn first_item_is_var(&mut self, rule: &Payload) -> bool {
            self.record(format!("scan:{}", rule.label));
            rule.is_var
        }

        fn materialize_synthetic(&mut self, rule: SyntheticRule<()>) -> Payload {
            self.record(format!("emit:{}:{}", rule.category, rule.label));
            if self.fail_at == Some(rule.label.as_str()) {
                panic!("fixture materialization failure: {}", rule.label);
            }
            Payload {
                label: rule.label,
                is_var: matches!(
                    rule.items.first(),
                    Some(LegacyAtomicItem::NonTerminal { kind: LegacyAtomicKind::Var, .. })
                ),
                normalized: false,
            }
        }

        fn has_literal_block(&mut self, source: &TypeSource) -> bool {
            self.record(format!("probe:{}", source.name));
            false
        }

        fn literal_label(&mut self, source: &TypeSource) -> String {
            self.record(format!("literal-label:{}", source.name));
            format!("{}Lit", source.name)
        }

        fn collection(&mut self, _: &TypeSource) -> CollectionRecipe<()> {
            panic!("these fixtures have no collection category");
        }

        fn var_label(&mut self, source: &TypeSource) -> String {
            self.record(format!("var-label:{}", source.name));
            format!("{}Var", source.name)
        }

        fn declares_binder(&mut self) -> bool {
            self.record("binders".into());
            false
        }
    }

    fn type_input(source: &TypeSource, native: bool) -> TypeInput<'_, TypeSource> {
        TypeInput {
            name: source.name.into(),
            is_data: false,
            has_native: native,
            has_collection: false,
            source,
        }
    }

    fn labels(payloads: &[Payload]) -> Vec<&str> {
        payloads
            .iter()
            .map(|payload| payload.label.as_str())
            .collect()
    }

    #[test]
    fn synthetic_adapter_non_clone_payloads_preserve_grouped_normalization() {
        let source = [
            UserSource { label: "A1", is_var: false },
            UserSource { label: "B1", is_var: false },
            UserSource { label: "A2", is_var: true },
            UserSource { label: "Skipped", is_var: false },
        ];
        let users = [
            UserInput { category: "A".into(), source: &source[0] },
            UserInput { category: "B".into(), source: &source[1] },
            UserInput { category: "A".into(), source: &source[2] },
            UserInput {
                category: "Missing".into(),
                source: &source[3],
            },
        ];
        let mut adapter = TraceAdapter::default();
        let rows =
            build_per_category_rules(&["B".into(), "A".into()], &users, &[], (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["B1"]);
        assert_eq!(labels(&rows[1]), ["A1", "A2"]);
        assert!(rows.iter().flatten().all(|payload| payload.normalized));
        assert!(rows[1][1].is_var);
        assert_eq!(
            adapter.events,
            [
                "clone:A1",
                "clone:B1",
                "clone:A2",
                "normalize:B1",
                "normalize:A1",
                "normalize:A2",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_duplicate_types_scan_current_materialized_vars() {
        let category = TypeSource { name: "A" };
        let types = [type_input(&category, true), type_input(&category, true)];
        let mut adapter = TraceAdapter::default();
        let rows = build_per_category_rules(&["A".into()], &[], &types, (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["ALit", "ALit", "AVar"]);
        assert!(!rows[0][0].is_var);
        assert!(!rows[0][1].is_var);
        assert!(rows[0][2].is_var);
        assert!(rows[0].iter().all(|payload| !payload.normalized));
        assert_eq!(
            adapter.events,
            [
                "probe:A",
                "literal-label:A",
                "emit:A:ALit",
                "probe:A",
                "literal-label:A",
                "emit:A:ALit",
                "scan:ALit",
                "scan:ALit",
                "var-label:A",
                "emit:A:AVar",
                "scan:ALit",
                "scan:ALit",
                "scan:AVar",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_emits_in_declaration_not_bucket_order() {
        let sources = [TypeSource { name: "A" }, TypeSource { name: "B" }];
        let types = [type_input(&sources[0], false), type_input(&sources[1], false)];
        let mut adapter = TraceAdapter::default();
        let rows =
            build_per_category_rules(&["B".into(), "A".into()], &[], &types, (), &mut adapter);
        assert_eq!(labels(&rows[0]), ["BVar"]);
        assert_eq!(labels(&rows[1]), ["AVar"]);
        assert_eq!(
            adapter.events,
            [
                "probe:A",
                "probe:B",
                "var-label:A",
                "emit:A:AVar",
                "var-label:B",
                "emit:B:BVar",
                "binders",
            ]
        );
    }

    #[test]
    fn synthetic_adapter_first_materializer_failure_stops_suffix() {
        const CHILD: &str = "METTAIL_TEST_SYNTHESIS_FIRST_FAILURE_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let sources = [TypeSource { name: "A" }, TypeSource { name: "B" }];
            let types = [type_input(&sources[0], true), type_input(&sources[1], true)];
            let mut adapter = TraceAdapter {
                fail_at: Some("ALit"),
                print_events: true,
                ..TraceAdapter::default()
            };
            let _ =
                build_per_category_rules(&["B".into(), "A".into()], &[], &types, (), &mut adapter);
            panic!("the first materializer must fail");
        }

        // Use a subprocess rather than assuming this compiler profile supports
        // catch_unwind. The expected panic may abort or unwind in the child.
        let output = std::process::Command::new(
            std::env::current_exe().expect("unit-test executable is available"),
        )
        .args([
            "--exact",
            "wpda_rule_analysis::synthetic::tests::synthetic_adapter_first_materializer_failure_stops_suffix",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .output()
        .expect("materialization failure child starts");
        assert!(!output.status.success(), "the child must fail at its first materializer");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("SYNTHESIS_TRACE:probe:A"), "{stderr}");
        assert!(stderr.contains("SYNTHESIS_TRACE:literal-label:A"), "{stderr}");
        assert!(stderr.contains("SYNTHESIS_TRACE:emit:A:ALit"), "{stderr}");
        assert!(stderr.contains("fixture materialization failure: ALit"), "{stderr}");
        for suppressed in ["probe:B", "emit:B:", "var-label:", "binders"] {
            assert!(!stderr.contains(&format!("SYNTHESIS_TRACE:{suppressed}")), "{stderr}");
        }
    }
}
