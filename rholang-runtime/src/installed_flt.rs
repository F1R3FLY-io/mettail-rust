//! Structural conversion support for one immutable installed language/image pair.
//!
//! The binding index is operation-scoped and borrows admitted declarations. It
//! does not select a language, grant authority, or evaluate semantic rules.

use dovetail::egraph::{EClassId, EGraph, EGraphConfig, ENode};
use dovetail::key::FramedSemanticOperator;
use mettail_ast::validation::is_reserved_reflect_label;
use mettail_dovetail_runtime::{
    theory_positional_native_view, ProvenSemanticTransitions, RuntimeLiteralRef,
    SemanticInputDecision, SemanticInputLimits, SemanticMatchRefutation, SemanticMatchUndetermined,
    SemanticTransitionInput, TheoryPositionalNativeEncoding, TheoryPositionalNativeView,
};
use mettail_grammar_core::{
    Category, CategoryId, ConstructorId, DynamicValue, InstalledLanguage, Production,
    TheoryConstructorId, TheoryConstructorImageV1, TheoryImageOperatorV1, TheoryLiteralCarrierV1,
    TheoryLiteralV1, TheorySemanticImageV1, TheorySortId, TheorySortKindImageV1,
};
use mettail_rholang_codegen::{
    decode_dynamic_native_label, encode_dynamic_native_label, DynamicNativeRef,
    DynamicReflectionError, ReflectedCodecBudget, ReflectedPositionalContext,
};
use models::rhoapi::Par;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;

/// Logical payload schedule over 32-bit declaration coordinates, independent
/// of host pointer size. This is not a wire encoding or physical allocation
/// bound; hash-table control storage and allocator overhead are excluded.
#[derive(Clone, Copy)]
enum IndexSlotKind {
    OptionalCoordinate,
    CoordinatePair,
    ForwardBinding,
}

impl IndexSlotKind {
    fn bytes(self) -> usize {
        match self {
            Self::OptionalCoordinate => 5,
            Self::CoordinatePair => 8,
            Self::ForwardBinding => 12,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum InstalledFltBindingError {
    MissingSemanticImage,
    InconsistentBinding(&'static str),
    ConflictingGrammarLabel(ConstructorId),
    ReservedConstructorLabel(TheoryConstructorId),
    Resource(DynamicReflectionError),
}

impl From<DynamicReflectionError> for InstalledFltBindingError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Resource(error)
    }
}

/// Both directions retain this exact image signature, including its grammar
/// pair and ordered domain. Labels borrow the canonical source declaration.
#[derive(Clone, Copy, Debug)]
pub(crate) struct InstalledFltConstructor<'a> {
    pub signature: &'a TheoryConstructorImageV1,
    pub label: &'a str,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum InstalledFltSort<'a> {
    Syntax {
        category: &'a Category,
        literal: Option<&'a TheoryLiteralCarrierV1>,
    },
    /// The sort exists, but is outside the positional/native boundary. This is
    /// distinct from a syntax sort with no literal carrier or an invalid ID.
    Unsupported(&'a TheorySortKindImageV1),
}

pub(crate) struct InstalledFltBindings<'a> {
    image: &'a TheorySemanticImageV1,
    category_to_sort: Vec<Option<TheorySortId>>,
    sort_to_category: Vec<Option<&'a Category>>,
    constructors: Vec<InstalledFltConstructor<'a>>,
    forward: HashMap<(TheorySortId, &'a str), TheoryConstructorId>,
}

impl<'a> InstalledFltBindings<'a> {
    pub(crate) fn new<C: FnMut() -> bool>(
        installed: &'a InstalledLanguage,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, InstalledFltBindingError> {
        budget.charge(1, 0)?;
        let image = installed
            .semantic_image()
            .ok_or(InstalledFltBindingError::MissingSemanticImage)?;
        let language = installed.language_core();
        let grammar = &language.grammar;
        // Installation already validated this exact immutable pair. These
        // inexpensive shape guards protect indexed assembly, not a second
        // whole-image validation or a reconstructed semantic signature.
        if image.sorts.len() != language.theory.sorts.len()
            || image.constructors.len() != language.theory.constructors.len()
        {
            return Err(InstalledFltBindingError::InconsistentBinding("source roster length"));
        }
        let mut category_to_sort =
            reserve_vector(grammar.categories.len(), IndexSlotKind::OptionalCoordinate, budget)?;
        category_to_sort.resize(grammar.categories.len(), None);
        let mut sort_to_category =
            reserve_vector(image.sorts.len(), IndexSlotKind::OptionalCoordinate, budget)?;
        sort_to_category.resize(image.sorts.len(), None);
        let mut names: HashMap<&str, &Category> =
            reserve_map(grammar.categories.len(), IndexSlotKind::CoordinatePair, budget)?;
        for category in &grammar.categories {
            budget.charge(category.name.len(), 0)?;
            match names.entry(category.name.as_str()) {
                Entry::Vacant(slot) => {
                    slot.insert(category);
                },
                Entry::Occupied(_) => {
                    return Err(InstalledFltBindingError::InconsistentBinding("category name"));
                },
            }
        }
        for (index, (sort, source)) in image.sorts.iter().zip(&language.theory.sorts).enumerate() {
            budget.charge(1, 0)?;
            if sort.id.0 as usize != index {
                return Err(InstalledFltBindingError::InconsistentBinding("sort coordinate"));
            }
            if let TheorySortKindImageV1::Syntax { .. } = &sort.kind {
                budget.charge(source.name.len(), 0)?;
                let category = names
                    .get(source.name.as_str())
                    .copied()
                    .ok_or(InstalledFltBindingError::InconsistentBinding("named syntax sort"))?;
                let slot = category_to_sort
                    .get_mut(category.id.0 as usize)
                    .ok_or(InstalledFltBindingError::InconsistentBinding("category coordinate"))?;
                if slot.is_some() {
                    return Err(InstalledFltBindingError::InconsistentBinding("category sort"));
                }
                *slot = Some(sort.id);
                sort_to_category[index] = Some(category);
            }
        }
        // Mirror the existing reflector's global ConstructorId -> label rule.
        // Production alternatives may repeat an identical binding. Do not size
        // an array from the maximum grammar constructor ID; the reservation is
        // made directly from the admitted production roster cardinality.
        let mut grammar_labels: HashMap<ConstructorId, &Production> =
            reserve_map(grammar.productions.len(), IndexSlotKind::CoordinatePair, budget)?;
        for production in &grammar.productions {
            budget.charge(1, 0)?;
            budget.charge(production.label.len(), 0)?;
            match grammar_labels.entry(production.constructor) {
                Entry::Vacant(slot) => {
                    slot.insert(production);
                },
                Entry::Occupied(slot) if slot.get().label != production.label => {
                    return Err(InstalledFltBindingError::ConflictingGrammarLabel(
                        production.constructor,
                    ));
                },
                Entry::Occupied(_) => {},
            }
        }
        let mut constructors =
            reserve_vector(image.constructors.len(), IndexSlotKind::CoordinatePair, budget)?;
        let mut forward =
            reserve_map(image.constructors.len(), IndexSlotKind::ForwardBinding, budget)?;
        // Exactly one entry per semantic constructor, never per production.
        // Source order supplies dense reverse coordinates; map iteration is
        // never used to assign IDs or to order any output.
        for (index, (signature, source)) in image
            .constructors
            .iter()
            .zip(&language.theory.constructors)
            .enumerate()
        {
            budget.charge(1, 0)?;
            budget.charge(source.name.len(), 0)?;
            if signature.id.0 as usize != index {
                return Err(InstalledFltBindingError::InconsistentBinding(
                    "constructor coordinate",
                ));
            }
            if is_reserved_reflect_label(&source.name) {
                return Err(InstalledFltBindingError::ReservedConstructorLabel(signature.id));
            }
            let binding = signature
                .grammar
                .ok_or(InstalledFltBindingError::InconsistentBinding("grammar binding"))?;
            let production = grammar_labels
                .get(&binding.constructor)
                .ok_or(InstalledFltBindingError::InconsistentBinding("grammar constructor"))?;
            if production.label != source.name || production.result != binding.category {
                return Err(InstalledFltBindingError::InconsistentBinding(
                    "grammar label or category",
                ));
            }
            if category_to_sort.get(binding.category.0 as usize) != Some(&Some(signature.codomain))
            {
                return Err(InstalledFltBindingError::InconsistentBinding(
                    "constructor result sort",
                ));
            }
            match forward.entry((signature.codomain, source.name.as_str())) {
                Entry::Vacant(slot) => {
                    slot.insert(signature.id);
                },
                Entry::Occupied(_) => {
                    return Err(InstalledFltBindingError::InconsistentBinding(
                        "reflected constructor key",
                    ));
                },
            }
            constructors.push(InstalledFltConstructor { signature, label: &source.name });
        }
        Ok(Self {
            image,
            category_to_sort,
            sort_to_category,
            constructors,
            forward,
        })
    }

    pub(crate) fn image(&self) -> &'a TheorySemanticImageV1 {
        self.image
    }

    pub(crate) fn sort_for_category<C: FnMut() -> bool>(
        &self,
        category: CategoryId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<TheorySortId>, InstalledFltBindingError> {
        budget.charge(1, 0)?;
        Ok(self
            .category_to_sort
            .get(category.0 as usize)
            .copied()
            .flatten())
    }

    pub(crate) fn sort<C: FnMut() -> bool>(
        &self,
        expected: TheorySortId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<InstalledFltSort<'a>>, InstalledFltBindingError> {
        budget.charge(1, 0)?;
        let Some(sort) = self
            .image
            .sorts
            .get(expected.0 as usize)
            .filter(|sort| sort.id == expected)
        else {
            return Ok(None);
        };
        Ok(Some(match &sort.kind {
            TheorySortKindImageV1::Syntax { literal } => {
                let category = self
                    .sort_to_category
                    .get(expected.0 as usize)
                    .copied()
                    .flatten()
                    .ok_or(InstalledFltBindingError::InconsistentBinding("syntax category"))?;
                InstalledFltSort::Syntax { category, literal: literal.as_ref() }
            },
            shape => InstalledFltSort::Unsupported(shape),
        }))
    }

    pub(crate) fn constructor<C: FnMut() -> bool>(
        &self,
        expected: TheorySortId,
        label: &str,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<InstalledFltConstructor<'a>>, InstalledFltBindingError> {
        budget.charge(1, 0)?;
        budget.charge(label.len(), 0)?;
        let Some(id) = self.forward.get(&(expected, label)) else {
            return Ok(None);
        };
        self.constructor_by_id(*id, budget)
    }

    pub(crate) fn constructor_by_id<C: FnMut() -> bool>(
        &self,
        id: TheoryConstructorId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<InstalledFltConstructor<'a>>, InstalledFltBindingError> {
        budget.charge(1, 0)?;
        Ok(self
            .constructors
            .get(id.0 as usize)
            .filter(|entry| entry.signature.id == id)
            .copied())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum InstalledFltError {
    Binding(InstalledFltBindingError),
    Resource(DynamicReflectionError),
    Kernel(SemanticMatchUndetermined),
    Refuted(SemanticMatchRefutation),
    UnsupportedOrMalformed(&'static str),
}

impl From<InstalledFltBindingError> for InstalledFltError {
    fn from(error: InstalledFltBindingError) -> Self {
        Self::Binding(error)
    }
}

impl From<DynamicReflectionError> for InstalledFltError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Resource(error)
    }
}

impl From<SemanticMatchUndetermined> for InstalledFltError {
    fn from(error: SemanticMatchUndetermined) -> Self {
        Self::Kernel(error)
    }
}

/// One operation-scoped adapter for the exact immutable installed pair. This
/// object grants no rights: the service must authorize the installed handle
/// before constructing it, and validate transition receipts before publication.
pub(crate) struct InstalledFltAdapter<'a> {
    bindings: InstalledFltBindings<'a>,
    fingerprint: String,
}

/// The two borrowed traversals instantiate the same occurrence machine. A
/// child cursor schedules one occurrence at a time, without collecting an
/// intermediate instruction program or cloning any reflected subtree.
enum OccurrenceTask<'a, R> {
    Visit(&'a R, TheorySortId),
    Children(&'a [R], &'a [TheorySortId]),
    Assemble(InstalledFltConstructor<'a>, usize),
}

// Fixed logical payload, not Rust layout: a tag plus two 64-bit spans covers
// the task variants. A reflected value is an eight-byte occurrence reference
// and a ground bit. Kernel references retain their existing four-byte IDs.
const TASK_SLOT_BYTES: usize = 33;
const REFLECTED_VALUE_SLOT_BYTES: usize = 9;
const CLASS_SLOT_BYTES: usize = 4;

impl<'a> InstalledFltAdapter<'a> {
    pub(crate) fn new<C: FnMut() -> bool>(
        installed: &'a InstalledLanguage,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, InstalledFltError> {
        let bindings = InstalledFltBindings::new(installed, budget)?;
        let owner_bytes = "mettail-grammar-core-v1:".len() + 64;
        budget.charge(owner_bytes, owner_bytes)?;
        let fingerprint = crate::language_install::grammar_fingerprint_label(
            installed.commitment().language_fingerprint,
        );
        Ok(Self { bindings, fingerprint })
    }

    /// Resolve the action's expected theory sort through the already checked
    /// named binding. Equal numeric sort/category coordinates are not assumed.
    pub(crate) fn input_category<C: FnMut() -> bool>(
        &self,
        sort: TheorySortId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<CategoryId, InstalledFltError> {
        match self.bindings.sort(sort, budget)? {
            Some(InstalledFltSort::Syntax { category, .. }) => Ok(category.id),
            _ => Err(InstalledFltError::UnsupportedOrMalformed(
                "action input is not a bound syntax sort",
            )),
        }
    }

    pub(crate) fn to_kernel<C: FnMut() -> bool>(
        &self,
        par: &Par,
        category: CategoryId,
        limits: SemanticInputLimits,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<SemanticTransitionInput, InstalledFltError> {
        let sort = self
            .bindings
            .sort_for_category(category, budget)?
            .ok_or(InstalledFltError::UnsupportedOrMalformed("unbound input category"))?;
        let context = ReflectedPositionalContext::new(&self.fingerprint, budget)?;
        // Fresh add-only coordinates must not overflow UnionFind's u32 IDs.
        let mut graph = EGraph::with_config(EGraphConfig {
            max_nodes: limits.nodes.min(u32::MAX as usize),
        });
        let mut tasks = OccurrenceBuffer::new();
        let mut values = OccurrenceBuffer::new();
        push_occurrence(&mut tasks, OccurrenceTask::Visit(par, sort), TASK_SLOT_BYTES, budget)?;
        while let Some(task) = tasks.pop() {
            budget.charge(1, 0)?;
            match task {
                OccurrenceTask::Visit(par, sort) => {
                    let literal = self.syntax_literal(sort, budget)?;
                    let head = context.view(par, budget)?.ok_or(
                        InstalledFltError::UnsupportedOrMalformed("noncanonical closed FLT head"),
                    )?;
                    match self.bindings.constructor(sort, head.label(), budget)? {
                        Some(binding) => {
                            if binding.signature.domain.len() != head.children().len() {
                                return Err(InstalledFltError::UnsupportedOrMalformed(
                                    "constructor arity",
                                ));
                            }
                            push_occurrence(
                                &mut tasks,
                                OccurrenceTask::Assemble(binding, values.len()),
                                TASK_SLOT_BYTES,
                                budget,
                            )?;
                            push_occurrence(
                                &mut tasks,
                                OccurrenceTask::Children(
                                    head.children(),
                                    &binding.signature.domain,
                                ),
                                TASK_SLOT_BYTES,
                                budget,
                            )?;
                        },
                        None => {
                            if !head.children().is_empty() {
                                return Err(InstalledFltError::UnsupportedOrMalformed(
                                    "native arity",
                                ));
                            }
                            let mut decoded = decode_dynamic_native_label(head.label(), budget)?;
                            let value = match (literal, decoded.as_mut()) {
                                (
                                    Some(TheoryLiteralCarrierV1::String),
                                    Some(DynamicValue::Text(text)),
                                ) => TheoryLiteralV1::String(std::mem::take(text)),
                                (
                                    Some(TheoryLiteralCarrierV1::Integer),
                                    Some(DynamicValue::Integer(value)),
                                ) => TheoryLiteralV1::Integer(*value),
                                (
                                    Some(TheoryLiteralCarrierV1::Boolean),
                                    Some(DynamicValue::Boolean(value)),
                                ) => TheoryLiteralV1::Boolean(*value),
                                _ => {
                                    return Err(InstalledFltError::UnsupportedOrMalformed(
                                        "native literal carrier",
                                    ))
                                },
                            };
                            let root = insert_kernel_node(
                                &mut graph,
                                &TheoryImageOperatorV1::Literal { sort, value },
                                &mut values,
                                0,
                                budget,
                            )?;
                            push_occurrence(&mut values, root, CLASS_SLOT_BYTES, budget)?;
                        },
                    }
                },
                OccurrenceTask::Children(children, sorts) => {
                    match (children.split_first(), sorts.split_first()) {
                        (None, None) => {},
                        (Some((child, rest)), Some((sort, later))) => {
                            push_occurrence(
                                &mut tasks,
                                OccurrenceTask::Children(rest, later),
                                TASK_SLOT_BYTES,
                                budget,
                            )?;
                            push_occurrence(
                                &mut tasks,
                                OccurrenceTask::Visit(child, *sort),
                                TASK_SLOT_BYTES,
                                budget,
                            )?;
                        },
                        _ => {
                            return Err(InstalledFltError::UnsupportedOrMalformed(
                                "child sort roster",
                            ))
                        },
                    }
                },
                OccurrenceTask::Assemble(binding, base) => {
                    let arity = binding.signature.domain.len();
                    if values.len().checked_sub(base) != Some(arity) {
                        return Err(InstalledFltError::UnsupportedOrMalformed(
                            "input assembly frame",
                        ));
                    }
                    let root = insert_kernel_node(
                        &mut graph,
                        &TheoryImageOperatorV1::Constructor(binding.signature.id),
                        &mut values,
                        arity,
                        budget,
                    )?;
                    push_occurrence(&mut values, root, CLASS_SLOT_BYTES, budget)?;
                },
            }
        }
        let [root] = values.as_slice() else {
            return Err(InstalledFltError::UnsupportedOrMalformed("input root cardinality"));
        };
        let decision = budget.run_accounted_stage(|remaining, cancel| {
            SemanticTransitionInput::admit_accounted(
                graph,
                *root,
                SemanticInputLimits {
                    work: limits.work.min(remaining),
                    ..limits
                },
                cancel,
            )
        })?;
        match decision {
            SemanticInputDecision::Proven(input) => Ok(input),
            SemanticInputDecision::Refuted(reason) => Err(InstalledFltError::Refuted(reason)),
            SemanticInputDecision::Undetermined { reason, .. } => Err(reason.into()),
        }
    }

    /// Reconstruct all original kernel results under one allowance. No sorting,
    /// filtering, deduplication, or new admission pass occurs here. The private
    /// bundle graph supplies the admitted acyclic projection; each output sort
    /// and each repeated child occurrence is still checked explicitly.
    pub(crate) fn reflect_transitions<C: FnMut() -> bool>(
        &self,
        bundle: &ProvenSemanticTransitions,
        expected_sort: TheorySortId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Vec<Par>, InstalledFltError> {
        let context = ReflectedPositionalContext::new(&self.fingerprint, budget)?;
        let mut outputs = reserve_occurrences(bundle.transitions.len(), 8, budget)?;
        for transition in &bundle.transitions {
            budget.charge(1, 0)?;
            if transition.output_sort != expected_sort {
                return Err(InstalledFltError::UnsupportedOrMalformed("transition output sort"));
            }
            let mut tasks = OccurrenceBuffer::new();
            let mut values = OccurrenceBuffer::new();
            push_occurrence(
                &mut tasks,
                OccurrenceTask::Visit(&transition.output, expected_sort),
                TASK_SLOT_BYTES,
                budget,
            )?;
            while let Some(task) = tasks.pop() {
                budget.charge(1, 0)?;
                match task {
                    OccurrenceTask::Visit(class, sort) => {
                        self.syntax_literal(sort, budget)?;
                        let view = budget
                            .run_accounted_stage(|remaining, cancel| {
                                let mut used = 0;
                                let result = theory_positional_native_view(
                                    self.bindings.image(),
                                    bundle.egraph(),
                                    *class,
                                    sort,
                                    &mut used,
                                    remaining,
                                    cancel,
                                );
                                (result, used)
                            })??
                            .ok_or(InstalledFltError::UnsupportedOrMalformed(
                                "kernel node shape",
                            ))?;
                        match view {
                            TheoryPositionalNativeView::Constructor { signature, children } => {
                                let binding = self
                                    .bindings
                                    .constructor_by_id(signature.id, budget)?
                                    .ok_or(InstalledFltError::UnsupportedOrMalformed(
                                        "kernel constructor binding",
                                    ))?;
                                push_occurrence(
                                    &mut tasks,
                                    OccurrenceTask::Assemble(binding, values.len()),
                                    TASK_SLOT_BYTES,
                                    budget,
                                )?;
                                push_occurrence(
                                    &mut tasks,
                                    OccurrenceTask::Children(children, &signature.domain),
                                    TASK_SLOT_BYTES,
                                    budget,
                                )?;
                            },
                            TheoryPositionalNativeView::Literal { value, .. } => {
                                let native = match value {
                                    RuntimeLiteralRef::String(text) => DynamicNativeRef::Text(text),
                                    RuntimeLiteralRef::Integer(value) => {
                                        DynamicNativeRef::Integer(value)
                                    },
                                    RuntimeLiteralRef::Boolean(value) => {
                                        DynamicNativeRef::Boolean(value)
                                    },
                                };
                                let label = encode_dynamic_native_label(native, budget)?;
                                let value = context.assemble(&label, Vec::new(), budget)?;
                                push_occurrence(
                                    &mut values,
                                    value,
                                    REFLECTED_VALUE_SLOT_BYTES,
                                    budget,
                                )?;
                            },
                        }
                    },
                    OccurrenceTask::Children(children, sorts) => {
                        match (children.split_first(), sorts.split_first()) {
                            (None, None) => {},
                            (Some((child, rest)), Some((sort, later))) => {
                                push_occurrence(
                                    &mut tasks,
                                    OccurrenceTask::Children(rest, later),
                                    TASK_SLOT_BYTES,
                                    budget,
                                )?;
                                push_occurrence(
                                    &mut tasks,
                                    OccurrenceTask::Visit(child, *sort),
                                    TASK_SLOT_BYTES,
                                    budget,
                                )?;
                            },
                            _ => {
                                return Err(InstalledFltError::UnsupportedOrMalformed(
                                    "kernel child sort roster",
                                ))
                            },
                        }
                    },
                    OccurrenceTask::Assemble(binding, base) => {
                        let arity = binding.signature.domain.len();
                        if values.len().checked_sub(base) != Some(arity) {
                            return Err(InstalledFltError::UnsupportedOrMalformed(
                                "output assembly frame",
                            ));
                        }
                        let mut children =
                            reserve_occurrences(arity, REFLECTED_VALUE_SLOT_BYTES, budget)?;
                        children.extend(values.drain(base..));
                        let value = context.assemble(binding.label, children, budget)?;
                        push_occurrence(&mut values, value, REFLECTED_VALUE_SLOT_BYTES, budget)?;
                    },
                }
            }
            if values.len() != 1 {
                return Err(InstalledFltError::UnsupportedOrMalformed("output root cardinality"));
            }
            let (par, _) = values.pop().expect("checked unique root");
            outputs.push(par);
        }
        Ok(outputs)
    }

    fn syntax_literal<C: FnMut() -> bool>(
        &self,
        sort: TheorySortId,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<&'a TheoryLiteralCarrierV1>, InstalledFltError> {
        match self.bindings.sort(sort, budget)? {
            Some(InstalledFltSort::Syntax { literal, .. }) => Ok(literal),
            _ => Err(InstalledFltError::UnsupportedOrMalformed("non-syntax or unknown sort")),
        }
    }
}

fn reserve_occurrences<T, C: FnMut() -> bool>(
    count: usize,
    slot_bytes: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<T>, InstalledFltError> {
    let bytes = count
        .checked_mul(slot_bytes)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(count, bytes)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    Ok(values)
}

/// Logical reservation must not depend on allocator-specific spare capacity.
/// The Vec owns stack-safe values; this wrapper changes neither their order nor
/// their destructor, and has no recursively owned frame chain.
struct OccurrenceBuffer<T> {
    values: Vec<T>,
    logical_capacity: usize,
}

impl<T> OccurrenceBuffer<T> {
    fn new() -> Self {
        Self { values: Vec::new(), logical_capacity: 0 }
    }

    fn len(&self) -> usize {
        self.values.len()
    }

    fn as_slice(&self) -> &[T] {
        &self.values
    }

    fn pop(&mut self) -> Option<T> {
        self.values.pop()
    }

    fn drain(&mut self, range: std::ops::RangeFrom<usize>) -> std::vec::Drain<'_, T> {
        self.values.drain(range)
    }
}

fn push_occurrence<T, C: FnMut() -> bool>(
    values: &mut OccurrenceBuffer<T>,
    value: T,
    slot_bytes: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), InstalledFltError> {
    budget.charge(1, 0)?;
    if values.len() == values.logical_capacity {
        let extra = values.logical_capacity.max(1);
        let next = values
            .logical_capacity
            .checked_add(extra)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let bytes = extra
            .checked_mul(slot_bytes)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        budget.charge(extra, bytes)?;
        values
            .values
            .try_reserve_exact(extra)
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        values.logical_capacity = next;
    }
    values.values.push(value);
    Ok(())
}

fn insert_kernel_node<C: FnMut() -> bool>(
    graph: &mut EGraph<FramedSemanticOperator>,
    operator: &TheoryImageOperatorV1,
    values: &mut OccurrenceBuffer<EClassId>,
    arity: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<EClassId, InstalledFltError> {
    let base = values
        .len()
        .checked_sub(arity)
        .ok_or(InstalledFltError::UnsupportedOrMalformed("kernel assembly arity"))?;
    let encoding = TheoryPositionalNativeEncoding::new(operator)?
        .ok_or(InstalledFltError::UnsupportedOrMalformed("kernel operator encoding"))?;
    let bytes = encoding.fresh_node_payload_bytes(arity)?;
    budget.charge(bytes, bytes)?;
    let mut children = reserve_occurrences(arity, CLASS_SLOT_BYTES, budget)?;
    for child in &values.as_slice()[base..] {
        budget.charge(1, 0)?;
        if graph.try_find(*child) != Some(*child) {
            return Err(InstalledFltError::UnsupportedOrMalformed("fresh child coordinate"));
        }
    }
    children.extend(values.drain(base..));
    graph
        .try_add_with_budget(ENode::new(encoding.encode()?, children))
        .ok_or_else(|| SemanticMatchUndetermined::InputLimitExceeded.into())
}

fn reserve_slots<C: FnMut() -> bool>(
    count: usize,
    kind: IndexSlotKind,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), InstalledFltBindingError> {
    let bytes = count
        .checked_mul(kind.bytes())
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    // Logical slot payload, not allocator capacity, table control bytes or RSS.
    budget.charge(count, bytes)?;
    Ok(())
}

fn reserve_vector<T, C: FnMut() -> bool>(
    count: usize,
    kind: IndexSlotKind,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<T>, InstalledFltBindingError> {
    reserve_slots(count, kind, budget)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    Ok(values)
}

fn reserve_map<K: Eq + Hash, V, C: FnMut() -> bool>(
    count: usize,
    kind: IndexSlotKind,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<HashMap<K, V>, InstalledFltBindingError> {
    reserve_slots(count, kind, budget)?;
    let mut values = HashMap::new();
    values
        .try_reserve(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn installed_flt_occurrence_reservations_ignore_physical_spare_capacity() {
        for physical in [0, 1, 100] {
            let mut values = OccurrenceBuffer {
                values: Vec::with_capacity(physical),
                logical_capacity: 0,
            };
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100, 100, &mut cancel);
            for value in 0..5 {
                push_occurrence(&mut values, value, CLASS_SLOT_BYTES, &mut budget)
                    .expect("logical growth");
            }
            assert_eq!(values.as_slice(), &[0, 1, 2, 3, 4]);
            assert_eq!(values.logical_capacity, 8);
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (13, 68));
            for expected in (0..5).rev() {
                assert_eq!(values.pop(), Some(expected));
            }
            push_occurrence(&mut values, 9, CLASS_SLOT_BYTES, &mut budget)
                .expect("reuse reservation");
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (14, 68));
        }
    }

    #[test]
    fn installed_flt_bindings_slot_overflow_is_refused_before_allocation_or_charge() {
        let mut work = 7;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, u64::MAX, usize::MAX, &mut cancelled);
        for kind in [
            IndexSlotKind::OptionalCoordinate,
            IndexSlotKind::CoordinatePair,
            IndexSlotKind::ForwardBinding,
        ] {
            assert!(matches!(
                reserve_vector::<u8, _>(usize::MAX, kind, &mut budget),
                Err(InstalledFltBindingError::Resource(DynamicReflectionError::PayloadByteLimit))
            ));
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (7, usize::MAX));
        }
    }
}
