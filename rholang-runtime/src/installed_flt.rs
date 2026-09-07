//! Structural conversion support for one immutable installed language/image pair.
//!
//! The binding index is operation-scoped and borrows admitted declarations. It
//! does not select a language, grant authority, or evaluate semantic rules.

use mettail_ast::validation::is_reserved_reflect_label;
use mettail_grammar_core::{
    Category, CategoryId, ConstructorId, InstalledLanguage, Production, TheoryConstructorId,
    TheoryConstructorImageV1, TheoryLiteralCarrierV1, TheorySemanticImageV1, TheorySortId,
    TheorySortKindImageV1,
};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
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
