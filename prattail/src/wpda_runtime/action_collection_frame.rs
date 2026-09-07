use super::{ActionArg, ActionArgMismatch, ActionEntry, SemanticBuilder};
use std::sync::Arc;

/// One closed, ordered collection selection. This is not a native collection
/// value or a parser accumulator ID. Its private, immutable item slice accepts
/// only terms and the explicit absent-value marker, so it cannot recursively
/// contain another selected collection or an unbound accumulator reference.
#[derive(Clone, Debug)]
pub struct SelectedCollection {
    items: Arc<[ActionArg]>,
}

impl SelectedCollection {
    pub fn new(items: Vec<ActionArg>) -> Result<Self, ActionArgMismatch> {
        for item in &items {
            if !matches!(item, ActionArg::Term { .. } | ActionArg::UnsetCollectionValue) {
                return Err(ActionArgMismatch {
                    requested: "selected collection term or absent value",
                    found: item.variant_name(),
                });
            }
        }
        Ok(Self { items: items.into() })
    }

    pub fn items(&self) -> &[ActionArg] {
        &self.items
    }
}

/// Failure of one reconstructed semantic-action invocation.
///
/// Collection protocol failures describe an invalid reconstruction, not an
/// exhausted parse family. Callers must keep them distinct from evidence that
/// a grammar's semantic action is undefined on a particular combination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActionInvocationError {
    Arity { expected: usize, actual: usize },
    CollectionLimit { limit: usize, actual: usize },
    UnboundCollectionReference { id: u8 },
    MissingCollection { id: u8 },
    RepeatedCollectionDrain { id: u8 },
    UndrainedCollection { id: u8 },
    OpenParserState,
    ResultCount { actual: usize },
    NonTermResult { found: &'static str },
}

impl std::fmt::Display for ActionInvocationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arity { expected, actual } => {
                write!(formatter, "action requires {expected} arguments, but received {actual}")
            },
            Self::CollectionLimit { limit, actual } => {
                write!(formatter, "action collection limit {limit} exceeded (requested {actual})")
            },
            Self::UnboundCollectionReference { id } => {
                write!(formatter, "parser collection reference {id} has no selected payload")
            },
            Self::MissingCollection { id } => {
                write!(formatter, "action collection slot {id} does not exist")
            },
            Self::RepeatedCollectionDrain { id } => {
                write!(formatter, "action collection slot {id} was drained more than once")
            },
            Self::UndrainedCollection { id } => {
                write!(formatter, "action collection slot {id} was not drained")
            },
            Self::OpenParserState => {
                formatter.write_str("action left open parser scopes or accumulators")
            },
            Self::ResultCount { actual } => {
                write!(formatter, "action requires one result, but produced {actual}")
            },
            Self::NonTermResult { found } => {
                write!(formatter, "action requires a term result, but produced {found}")
            },
        }
    }
}

impl std::error::Error for ActionInvocationError {}

/// Indexed, invocation-local collection storage. A consumed slot stays in
/// place, so draining in source order cannot shift a later occurrence's ID.
/// Parser-time nested collection accumulators remain a separate stack.
///
/// `get_mut(...).take()` refines `indexed_take` in
/// `OccurrenceCollectionAssembly.v`. The sticky failure and final scan refine
/// `checked_drain` and `action_frame_complete` in the same model.
#[derive(Clone)]
pub(super) struct ActionCollectionFrame {
    slots: Vec<Option<Vec<ActionArg>>>,
    failure: Option<ActionInvocationError>,
}

impl ActionCollectionFrame {
    fn new(collections: Vec<Vec<ActionArg>>) -> Result<Self, ActionInvocationError> {
        let limit = usize::from(u8::MAX) + 1;
        if collections.len() > limit {
            return Err(ActionInvocationError::CollectionLimit {
                limit,
                actual: collections.len(),
            });
        }
        Ok(Self {
            slots: collections.into_iter().map(Some).collect(),
            failure: None,
        })
    }

    pub(super) fn drain(&mut self, id: u8) -> Vec<ActionArg> {
        let result = match self.slots.get_mut(usize::from(id)) {
            Some(slot) => slot
                .take()
                .ok_or(ActionInvocationError::RepeatedCollectionDrain { id }),
            None => Err(ActionInvocationError::MissingCollection { id }),
        };
        match result {
            Ok(items) => items,
            Err(error) => {
                // The generated callback ABI returns unit. It may continue
                // executing, but invoke_action cannot publish its output.
                self.failure.get_or_insert(error);
                Vec::new()
            },
        }
    }

    fn finish(self, has_result: bool) -> Result<(), ActionInvocationError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        // A partial generated action may reject before consuming arguments.
        // Undrained slots invalidate a constructed value, not that rejection.
        if !has_result {
            return Ok(());
        }
        if let Some(index) = self.slots.iter().position(Option::is_some) {
            // The constructor checks the complete index range before any
            // callback runs; no truncating index cast is permitted here.
            let id = u8::try_from(index).expect("checked action collection index");
            return Err(ActionInvocationError::UndrainedCollection { id });
        }
        Ok(())
    }
}

impl SemanticBuilder {
    /// Assign fresh invocation-local IDs to closed collection occurrences,
    /// preserving optional-group structure with an explicit work stack.
    /// Even two occurrences sharing the same immutable payload get distinct
    /// slots. Allocation is checked before narrowing an index to the action
    /// ABI's u8 carrier; no parser ID is accepted as a selected payload.
    pub fn invoke_selected_action(
        entry: ActionEntry,
        args: Vec<ActionArg>,
    ) -> Result<Option<ActionArg>, ActionInvocationError> {
        let expected = usize::from(entry.arity);
        if args.len() != expected {
            return Err(ActionInvocationError::Arity { expected, actual: args.len() });
        }
        enum Task {
            Visit(ActionArg),
            FinishOptional(usize),
        }
        let mut tasks: Vec<_> = args.into_iter().rev().map(Task::Visit).collect();
        let mut values = Vec::with_capacity(expected);
        let mut collections = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(arg) => match &arg {
                    ActionArg::SelectedCollection(selected) => {
                        let id = u8::try_from(collections.len()).map_err(|_| {
                            ActionInvocationError::CollectionLimit {
                                limit: usize::from(u8::MAX) + 1,
                                actual: collections.len() + 1,
                            }
                        })?;
                        collections.push(selected.items().to_vec());
                        values.push(ActionArg::CollectionId(id));
                    },
                    ActionArg::CollectionId(id) => {
                        return Err(ActionInvocationError::UnboundCollectionReference { id: *id });
                    },
                    ActionArg::Optional(Some(_)) => {
                        let inner = arg.into_optional().flatten().expect("present optional");
                        tasks.push(Task::FinishOptional(inner.len()));
                        tasks.extend(inner.into_iter().rev().map(Task::Visit));
                    },
                    _ => values.push(arg),
                },
                Task::FinishOptional(count) => {
                    let first = values
                        .len()
                        .checked_sub(count)
                        .expect("selected argument plan preserves optional arity");
                    let inner = values.split_off(first);
                    values.push(ActionArg::Optional(Some(inner)));
                },
            }
        }
        Self::invoke_action(entry, values, collections)
    }

    /// Invoke a generated action on one fully selected argument combination.
    ///
    /// `collections[i]` supplies exactly the occurrence referred to by
    /// `CollectionId(i)` in `args`, including inside optional groups. IDs are
    /// local to this invocation, not SPPF node IDs or parser-stack positions.
    /// The occurrence assembler is responsible for this structural mapping.
    /// There is no alternative selection, ranking, or family truncation here.
    ///
    /// `Ok(Some(term))` constructs one term and consumes every slot exactly
    /// once, in any order. `Ok(None)` is rejection by the trusted partial
    /// generated action; unused arguments need not be drained on that path.
    /// `Err` is a protocol/resource failure, never semantic rejection, and
    /// dominates even if the callback later returns without a value. Open
    /// parser state and nonterm/multiple results are failures. Callbacks are
    /// trusted generated builders, not language-supplied effectful code.
    pub fn invoke_action(
        entry: ActionEntry,
        args: Vec<ActionArg>,
        collections: Vec<Vec<ActionArg>>,
    ) -> Result<Option<ActionArg>, ActionInvocationError> {
        let expected = usize::from(entry.arity);
        if args.len() != expected {
            return Err(ActionInvocationError::Arity { expected, actual: args.len() });
        }
        let frame = ActionCollectionFrame::new(collections)?;
        let mut builder = Self::new();
        builder.action_collections = Some(Box::new(frame));
        (entry.action_fn)(&mut builder, args);
        builder
            .action_collections
            .take()
            .expect("invocation-local collection frame remains installed")
            .finish(!builder.stack.is_empty())?;
        if !builder.binder_scopes.is_empty()
            || !builder.collection_stack.is_empty()
            || !builder.optional_stack.is_empty()
        {
            return Err(ActionInvocationError::OpenParserState);
        }
        if builder.stack.is_empty() {
            return Ok(None);
        }
        if builder.stack.len() != 1 {
            return Err(ActionInvocationError::ResultCount { actual: builder.stack.len() });
        }
        let result = builder.stack.pop_back().expect("checked single result");
        if matches!(result, ActionArg::Term { .. }) {
            Ok(Some(result))
        } else {
            Err(ActionInvocationError::NonTermResult { found: result.variant_name() })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wpda_runtime::ANY_CAT;
    use std::sync::Arc;

    fn item(value: i32) -> ActionArg {
        ActionArg::Term {
            value: Arc::new(value),
            type_name: std::any::type_name::<i32>(),
        }
    }

    fn selected(values: &[i32]) -> ActionArg {
        ActionArg::SelectedCollection(
            SelectedCollection::new(values.iter().copied().map(item).collect()).unwrap(),
        )
    }

    #[test]
    fn indexed_action_frame_assigns_independent_ids_to_shared_payloads() {
        let shared = selected(&[7, 3]);
        let output = SemanticBuilder::invoke_selected_action(
            entry(2, drain_requested),
            vec![shared.clone(), shared],
        )
        .unwrap()
        .expect("the collection action constructs a value")
        .try_into_term::<Vec<Vec<i32>>>()
        .unwrap();
        assert_eq!(output, vec![vec![7, 3], vec![7, 3]]);
    }

    #[test]
    fn indexed_action_frame_keeps_all_four_ordered_item_selections() {
        let family = [item(1), item(2)];
        let mut outputs = Vec::new();
        for left in &family {
            for right in &family {
                let collection =
                    SelectedCollection::new(vec![left.clone(), right.clone()]).unwrap();
                let result = SemanticBuilder::invoke_selected_action(
                    entry(1, drain_requested),
                    vec![ActionArg::SelectedCollection(collection)],
                )
                .unwrap()
                .expect("the collection action constructs a value")
                .try_into_term::<Vec<Vec<i32>>>()
                .unwrap();
                outputs.push(result);
            }
        }
        assert_eq!(
            outputs,
            vec![vec![vec![1, 1]], vec![vec![1, 2]], vec![vec![2, 1]], vec![vec![2, 2]]]
        );
    }

    #[test]
    fn indexed_action_frame_preserves_optional_shape_and_checks_nested_capacity() {
        fn check_shape(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
            let mut args = args.into_iter();
            let first = args.next().unwrap().into_optional().unwrap().unwrap();
            assert_eq!(first.len(), 2);
            assert!(matches!(&first[0], ActionArg::Optional(None)));
            assert!(matches!(&first[1], ActionArg::CollectionId(0)));
            assert!(matches!(args.next().unwrap(), ActionArg::Optional(None)));
            assert!(matches!(args.next().unwrap(), ActionArg::CollectionId(1)));
            let second = ActionArg::try_into_terms::<i32>(builder.drain_collection(1)).unwrap();
            let first = ActionArg::try_into_terms::<i32>(builder.drain_collection(0)).unwrap();
            builder.push_term(vec![first, second]);
        }
        let output = SemanticBuilder::invoke_selected_action(
            entry(3, check_shape),
            vec![
                ActionArg::Optional(Some(vec![ActionArg::Optional(None), selected(&[1])])),
                ActionArg::Optional(None),
                selected(&[2]),
            ],
        )
        .unwrap()
        .expect("the collection action constructs a value")
        .try_into_term::<Vec<Vec<i32>>>()
        .unwrap();
        assert_eq!(output, vec![vec![1], vec![2]]);
        fn must_not_run(_: &mut SemanticBuilder, _: Vec<ActionArg>) {
            panic!("oversized nested frame reached the callback");
        }
        let result = SemanticBuilder::invoke_selected_action(
            entry(1, must_not_run),
            vec![ActionArg::Optional(Some(vec![selected(&[]); 257]))],
        );
        assert_eq!(
            result.unwrap_err(),
            ActionInvocationError::CollectionLimit { limit: 256, actual: 257 }
        );
    }

    #[test]
    fn indexed_action_frame_selected_payload_is_closed_and_exact() {
        let values =
            SelectedCollection::new(vec![item(1), ActionArg::UnsetCollectionValue]).unwrap();
        assert_eq!(values.items().len(), 2);
        assert!(values.items()[1].is_unset_collection_value());
        for invalid in [ActionArg::CollectionId(0), ActionArg::Optional(None), selected(&[1])] {
            assert!(SelectedCollection::new(vec![item(1), invalid, item(2)]).is_err());
        }
        let result = SemanticBuilder::invoke_selected_action(
            entry(1, drain_requested),
            vec![ActionArg::CollectionId(0)],
        );
        assert_eq!(
            result.unwrap_err(),
            ActionInvocationError::UnboundCollectionReference { id: 0 }
        );
    }

    fn entry(arity: u8, action_fn: super::super::SemanticActionFn) -> ActionEntry {
        ActionEntry {
            action_fn,
            arity,
            expected_input_cats: &[],
            output_cat: ANY_CAT,
        }
    }

    fn drain_requested(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
        let mut output = Vec::new();
        for arg in args {
            let id = arg.as_collection_id().expect("test collection argument");
            output.push(ActionArg::try_into_terms::<i32>(builder.drain_collection(id)).unwrap());
        }
        builder.push_term(output);
    }

    #[test]
    fn indexed_action_frame_drains_in_either_order_without_aliasing() {
        for ids in [[0, 1], [1, 0]] {
            let output = SemanticBuilder::invoke_action(
                entry(2, drain_requested),
                ids.map(ActionArg::CollectionId).into(),
                vec![vec![item(7), item(7)], vec![item(3)]],
            )
            .unwrap()
            .expect("the collection action constructs a value")
            .try_into_term::<Vec<Vec<i32>>>()
            .unwrap();
            let families = [vec![7, 7], vec![3]];
            assert_eq!(output, ids.map(|id| families[usize::from(id)].clone()));
        }
    }

    #[test]
    fn indexed_action_frame_empty_is_not_missing_or_repeated() {
        let valid = SemanticBuilder::invoke_action(
            entry(1, drain_requested),
            vec![ActionArg::CollectionId(0)],
            vec![vec![]],
        );
        assert_eq!(
            valid
                .unwrap()
                .unwrap()
                .try_into_term::<Vec<Vec<i32>>>()
                .unwrap(),
            vec![vec![]]
        );
        let missing = SemanticBuilder::invoke_action(
            entry(1, drain_requested),
            vec![ActionArg::CollectionId(0)],
            vec![],
        );
        assert_eq!(missing.unwrap_err(), ActionInvocationError::MissingCollection { id: 0 });
        let repeated = SemanticBuilder::invoke_action(
            entry(2, drain_requested),
            vec![ActionArg::CollectionId(0), ActionArg::CollectionId(0)],
            vec![vec![]],
        );
        assert_eq!(repeated.unwrap_err(), ActionInvocationError::RepeatedCollectionDrain { id: 0 });
    }

    #[test]
    fn indexed_action_frame_failure_survives_later_valid_drains_and_output() {
        let result = SemanticBuilder::invoke_action(
            entry(3, drain_requested),
            vec![
                ActionArg::CollectionId(2),
                ActionArg::CollectionId(0),
                ActionArg::CollectionId(1),
            ],
            vec![vec![item(1)], vec![item(2)]],
        );
        assert_eq!(result.unwrap_err(), ActionInvocationError::MissingCollection { id: 2 });
        let undrained = SemanticBuilder::invoke_action(
            entry(1, drain_requested),
            vec![ActionArg::CollectionId(0)],
            vec![vec![item(1)], vec![]],
        );
        assert_eq!(undrained.unwrap_err(), ActionInvocationError::UndrainedCollection { id: 1 });
    }

    #[test]
    fn indexed_action_frame_checks_capacity_before_invoking_callback() {
        fn must_not_run(_: &mut SemanticBuilder, _: Vec<ActionArg>) {
            panic!("invalid invocation reached callback");
        }
        let result =
            SemanticBuilder::invoke_action(entry(0, must_not_run), vec![], vec![vec![]; 257]);
        assert_eq!(
            result.unwrap_err(),
            ActionInvocationError::CollectionLimit { limit: 256, actual: 257 }
        );
        let arity = SemanticBuilder::invoke_action(entry(1, must_not_run), vec![], vec![]);
        assert_eq!(arity.unwrap_err(), ActionInvocationError::Arity { expected: 1, actual: 0 });
        let mut frame = ActionCollectionFrame::new(vec![vec![]; 256]).unwrap();
        for id in 0..=u8::MAX {
            assert!(frame.drain(id).is_empty());
        }
        assert_eq!(frame.finish(true), Ok(()));
    }

    #[test]
    fn indexed_action_frame_requires_one_term_and_closed_scopes() {
        let cases: [(super::super::SemanticActionFn, ActionInvocationError); 3] = [
            (
                |b, _| {
                    b.push_term(1_i32);
                    b.push_term(2_i32);
                },
                ActionInvocationError::ResultCount { actual: 2 },
            ),
            (
                |b, _| b.push_collection_id(0),
                ActionInvocationError::NonTermResult { found: "ActionArg::CollectionId" },
            ),
            (
                |b, _| {
                    b.start_collection();
                    b.push_term(1_i32);
                },
                ActionInvocationError::OpenParserState,
            ),
        ];
        for (callback, error) in cases {
            assert_eq!(
                SemanticBuilder::invoke_action(entry(0, callback), vec![], vec![]).unwrap_err(),
                error
            );
        }
    }

    #[test]
    fn indexed_action_frame_preserves_optional_collection_references() {
        fn action(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
            let mut work: Vec<_> = args.into_iter().rev().collect();
            let mut output = Vec::new();
            while let Some(arg) = work.pop() {
                if let Some(id) = arg.as_collection_id() {
                    output.extend(
                        ActionArg::try_into_terms::<i32>(builder.drain_collection(id)).unwrap(),
                    );
                } else if let Some(Some(inner)) = arg.into_optional() {
                    work.extend(inner.into_iter().rev());
                }
            }
            builder.push_term(output);
        }
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut nested = ActionArg::CollectionId(0);
                for _ in 0..20_000 {
                    nested = ActionArg::Optional(Some(vec![nested]));
                }
                let output = SemanticBuilder::invoke_action(
                    entry(2, action),
                    vec![nested, ActionArg::CollectionId(1)],
                    vec![vec![item(3), item(4)], vec![item(5)]],
                )
                .unwrap()
                .unwrap();
                assert_eq!(output.try_into_term::<Vec<i32>>().unwrap(), vec![3, 4, 5]);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn indexed_action_frame_normalizes_deep_selected_optional_occurrences() {
        fn action(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
            let mut pending: Vec<_> = args.into_iter().rev().collect();
            let mut output = Vec::new();
            while let Some(arg) = pending.pop() {
                if let Some(id) = arg.as_collection_id() {
                    output.extend(
                        ActionArg::try_into_terms::<i32>(builder.drain_collection(id)).unwrap(),
                    );
                } else if let Some(Some(inner)) = arg.into_optional() {
                    pending.extend(inner.into_iter().rev());
                }
            }
            builder.push_term(output);
        }
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut nested = selected(&[3, 4]);
                for _ in 0..20_000 {
                    nested = ActionArg::Optional(Some(vec![nested]));
                }
                let output = SemanticBuilder::invoke_selected_action(
                    entry(2, action),
                    vec![nested, selected(&[5])],
                )
                .unwrap()
                .expect("the collection action constructs a value")
                .try_into_term::<Vec<i32>>()
                .unwrap();
                assert_eq!(output, vec![3, 4, 5]);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn indexed_action_frame_distinguishes_partial_rejection_from_protocol_failure() {
        fn reject_before_draining(_: &mut SemanticBuilder, _: Vec<ActionArg>) {}
        let rejected = SemanticBuilder::invoke_selected_action(
            entry(1, reject_before_draining),
            vec![selected(&[1, 2])],
        );
        assert!(
            matches!(rejected, Ok(None)),
            "a rejected combination need not drain unused items"
        );

        fn invalid_drain_then_no_result(builder: &mut SemanticBuilder, _: Vec<ActionArg>) {
            builder.drain_collection(1);
        }
        let failed = SemanticBuilder::invoke_selected_action(
            entry(1, invalid_drain_then_no_result),
            vec![selected(&[1, 2])],
        );
        assert_eq!(failed.unwrap_err(), ActionInvocationError::MissingCollection { id: 1 });
    }
}
