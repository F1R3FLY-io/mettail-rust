//! Stack-safe retention of shallow authored observations.
//!
//! The `AuthoredRuleCaptureProjection` model supplies the Enter/Finish laws:
//! observe once, schedule children in field order, resolve completed references,
//! assign source-name equality classes, then append a checked owned node.
//! This is structural capture, not grammar classification or parsing.
//!
//! Source adapters must preserve their original identity/equality observations
//! and charge source-owned payload copies before making them. Callers admit the
//! initial root roster. The admission callback below gates subsequent worklist
//! growth and each finishing operation; it does not invent a budget policy.

use crate::authored::*;
use std::collections::HashMap;
use std::hash::Hash;

/// A shallow borrowed view of an existing frontend. Equal identities must
/// denote the same stable observation for the duration of capture. Identity
/// is ephemeral; it is never written to the resulting store.
pub trait AuthoredCaptureSource {
    type Handle: Copy;
    type Identity: Copy + Eq + Hash;
    /// Use the original name's Eq/Hash, not its spelling or occurrence address.
    type NameKey: Eq + Hash;
    type Error;

    fn identity(&self, handle: Self::Handle) -> Self::Identity;
    fn shallow(
        &mut self,
        handle: Self::Handle,
    ) -> Result<AuthoredNode<Self::Handle, Self::NameKey>, Self::Error>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthoredCapturePhase {
    Enter,
    Finish,
}

/// Sizes before the phase mutates its private state. `scheduled_frames` is
/// the exact worklist length after this phase, excluding the popped frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthoredCaptureAdmission {
    pub phase: AuthoredCapturePhase,
    pub stored_nodes: usize,
    pub memoized_nodes: usize,
    pub name_classes: usize,
    pub scheduled_frames: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthoredCaptureError<E> {
    Source(E),
    Admission(E),
    WrongSourceTag {
        expected: AuthoredNodeTag,
        actual: AuthoredNodeTag,
    },
    Cycle,
    OwnerNotPending,
    ChildNotReady,
    RootNotReady,
    IndexOverflow,
    Allocation,
    Store(AuthoredStoreError),
}

/// Returned only after every root is Ready and the complete store validates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedAuthoredNodes {
    pub store: AuthoredRuleStore,
    pub roots: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mark {
    Pending,
    Ready(u32),
}

enum Frame<H, K, I> {
    Enter(AuthoredNodeTag, H),
    Finish((AuthoredNodeTag, I), AuthoredNode<H, K>),
}

/// Append declaration name roots to the caller-admitted rule roster and run
/// the original capture controller once. Names share its identity memo and
/// source-equality classes, including in languages with no rules. The returned
/// root roster still contains only the original rule roots in their positions.
/// Callers must admit header payloads and the combined root count beforehand.
pub fn capture_authored_declarations<S: AuthoredCaptureSource>(
    source: &mut S,
    rules: &[(AuthoredNodeTag, S::Handle)],
    declarations: AuthoredDeclarations<S::Handle>,
    admit: impl FnMut(
        AuthoredCaptureAdmission,
        &AuthoredNode<S::Handle, S::NameKey>,
    ) -> Result<(), S::Error>,
) -> Result<CapturedAuthoredNodes, AuthoredCaptureError<S::Error>> {
    use AuthoredCaptureError as Error;
    let mut count = rules.len();
    declarations.try_for_each_name(|_| {
        count = count.checked_add(1).ok_or(Error::IndexOverflow)?;
        Ok(())
    })?;
    let mut roots = Vec::new();
    roots.try_reserve(count).map_err(|_| Error::Allocation)?;
    roots.extend_from_slice(rules);
    declarations.try_for_each_name(|name| {
        roots.push((AuthoredNodeTag::Name, name.0));
        Ok::<_, Error<S::Error>>(())
    })?;
    let mut captured = capture_authored_nodes(source, &roots, admit)?;
    let mut names = captured.roots[rules.len()..].iter().copied();
    let declarations = declarations
        .try_map_names(|_| names.next().map(AuthoredNameId).ok_or(Error::RootNotReady))?;
    if names.next().is_some() {
        return Err(Error::RootNotReady);
    }
    captured.store = captured
        .store
        .with_declarations(declarations)
        .map_err(Error::Store)?;
    captured.roots.truncate(rules.len());
    Ok(captured)
}

/// Capture an ordered root roster with an explicit heap worklist. Completed
/// shared nodes are reused, but duplicate roots retain their positions.
/// No store escapes on any error, including admission refusal or a cycle.
pub fn capture_authored_nodes<S: AuthoredCaptureSource>(
    source: &mut S,
    roots: &[(AuthoredNodeTag, S::Handle)],
    mut admit: impl FnMut(
        AuthoredCaptureAdmission,
        &AuthoredNode<S::Handle, S::NameKey>,
    ) -> Result<(), S::Error>,
) -> Result<CapturedAuthoredNodes, AuthoredCaptureError<S::Error>> {
    use AuthoredCaptureError as Error;
    let mut work = Vec::new();
    work.try_reserve(roots.len())
        .map_err(|_| Error::Allocation)?;
    work.extend(
        roots
            .iter()
            .rev()
            .map(|&(tag, handle)| Frame::Enter(tag, handle)),
    );
    let mut memo = HashMap::new();
    let mut classes = HashMap::new();
    let mut store = AuthoredRuleStore::new();

    while let Some(frame) = work.pop() {
        match frame {
            Frame::Enter(tag, handle) => {
                let key = (tag, source.identity(handle));
                match memo.get(&key) {
                    Some(Mark::Ready(_)) => continue,
                    Some(Mark::Pending) => return Err(Error::Cycle),
                    None => {},
                }
                let recipe = source.shallow(handle).map_err(Error::Source)?;
                if recipe.tag() != tag {
                    return Err(Error::WrongSourceTag { expected: tag, actual: recipe.tag() });
                }
                let mut children = 0usize;
                recipe.try_for_each_reference(|_, _| {
                    children = children.checked_add(1).ok_or(Error::IndexOverflow)?;
                    Ok(())
                })?;
                let extra = children.checked_add(1).ok_or(Error::IndexOverflow)?;
                let scheduled_frames = work.len().checked_add(extra).ok_or(Error::IndexOverflow)?;
                admit(
                    AuthoredCaptureAdmission {
                        phase: AuthoredCapturePhase::Enter,
                        stored_nodes: store.len(),
                        memoized_nodes: memo.len(),
                        name_classes: classes.len(),
                        scheduled_frames,
                    },
                    &recipe,
                )
                .map_err(Error::Admission)?;
                work.try_reserve(extra).map_err(|_| Error::Allocation)?;
                memo.try_reserve(1).map_err(|_| Error::Allocation)?;
                memo.insert(key, Mark::Pending);

                // Push children in authored order then reverse just that suffix
                // for the LIFO worklist. Move the same recipe into its Finish
                // frame; no second source read or recursive clone is needed.
                let start = work.len();
                recipe.try_for_each_reference(|child_tag, child| {
                    work.push(Frame::Enter(child_tag, child));
                    Ok::<_, Error<S::Error>>(())
                })?;
                work[start..].reverse();
                work.insert(start, Frame::Finish(key, recipe));
            },
            Frame::Finish(key, recipe) => {
                if memo.get(&key) != Some(&Mark::Pending) {
                    return Err(Error::OwnerNotPending);
                }
                admit(
                    AuthoredCaptureAdmission {
                        phase: AuthoredCapturePhase::Finish,
                        stored_nodes: store.len(),
                        memoized_nodes: memo.len(),
                        name_classes: classes.len(),
                        scheduled_frames: work.len(),
                    },
                    &recipe,
                )
                .map_err(Error::Admission)?;
                let owned = recipe.try_map_observations(
                    |tag, handle| match memo.get(&(tag, source.identity(handle))) {
                        Some(Mark::Ready(index)) => Ok(*index),
                        _ => Err(Error::ChildNotReady),
                    },
                    |name| {
                        let class = match classes.get(&name) {
                            Some(class) => *class,
                            None => {
                                let class = u32::try_from(classes.len())
                                    .map_err(|_| Error::IndexOverflow)?;
                                classes.try_reserve(1).map_err(|_| Error::Allocation)?;
                                classes.insert(name, class);
                                class
                            },
                        };
                        Ok(class)
                    },
                )?;
                let index = store.try_push(owned).map_err(Error::Store)?;
                memo.insert(key, Mark::Ready(index));
            },
        }
    }

    let mut captured_roots = Vec::new();
    captured_roots
        .try_reserve(roots.len())
        .map_err(|_| Error::Allocation)?;
    for &(tag, handle) in roots {
        match memo.get(&(tag, source.identity(handle))) {
            Some(Mark::Ready(index)) => captured_roots.push(*index),
            _ => return Err(Error::RootNotReady),
        }
    }
    store.validate().map_err(Error::Store)?;
    Ok(CapturedAuthoredNodes { store, roots: captured_roots })
}

impl<I, K> AuthoredNode<I, K> {
    /// Substitute only immediate references and the source name equality key.
    /// Field order is identical to `try_for_each_reference`; strings, tags,
    /// separators, optional presence and list multiplicity are unchanged.
    pub fn try_map_observations<J, L, E>(
        self,
        mut resolve: impl FnMut(AuthoredNodeTag, I) -> Result<J, E>,
        mut name_class: impl FnMut(K) -> Result<L, E>,
    ) -> Result<AuthoredNode<J, L>, E> {
        use AuthoredNode as Node;
        use AuthoredNodeTag as Tag;
        macro_rules! reference {
            ($kind:ident, $id:ident, $value:expr) => {
                $id(resolve(Tag::$kind, $value.0)?)
            };
        }
        Ok(match self {
            Node::Name(name) => Node::Name(AuthoredName {
                spelling: name.spelling,
                equality_class: name_class(name.equality_class)?,
            }),
            Node::Names(names) => Node::Names(
                names
                    .into_iter()
                    .map(|name| Ok(reference!(Name, AuthoredNameId, name)))
                    .collect::<Result<_, E>>()?,
            ),
            Node::Type(ty) => Node::Type(match ty {
                AuthoredType::Base(name) => {
                    AuthoredType::Base(reference!(Name, AuthoredNameId, name))
                },
                AuthoredType::Collection { kind, element } => AuthoredType::Collection {
                    kind,
                    element: reference!(Type, AuthoredTypeId, element),
                },
                AuthoredType::Map { key, value } => AuthoredType::Map {
                    key: reference!(Type, AuthoredTypeId, key),
                    value: reference!(Type, AuthoredTypeId, value),
                },
                AuthoredType::Arrow { domain, codomain } => AuthoredType::Arrow {
                    domain: reference!(Type, AuthoredTypeId, domain),
                    codomain: reference!(Type, AuthoredTypeId, codomain),
                },
                AuthoredType::MultiBinder { inner } => AuthoredType::MultiBinder {
                    inner: reference!(Type, AuthoredTypeId, inner),
                },
                AuthoredType::Unsupported { tag } => AuthoredType::Unsupported { tag },
                AuthoredType::KeyedPathMap { key, value } => AuthoredType::KeyedPathMap {
                    key: reference!(Type, AuthoredTypeId, key),
                    value: reference!(Type, AuthoredTypeId, value),
                },
            }),
            Node::Param(param) => Node::Param(match param {
                AuthoredParam::Simple { name, ty } => AuthoredParam::Simple {
                    name: reference!(Name, AuthoredNameId, name),
                    ty: reference!(Type, AuthoredTypeId, ty),
                },
                AuthoredParam::GuardBody { name } => AuthoredParam::GuardBody {
                    name: reference!(Name, AuthoredNameId, name),
                },
                AuthoredParam::Abstraction { binder, body, ty } => AuthoredParam::Abstraction {
                    binder: reference!(Name, AuthoredNameId, binder),
                    body: reference!(Name, AuthoredNameId, body),
                    ty: reference!(Type, AuthoredTypeId, ty),
                },
                AuthoredParam::MultiAbstraction { binder, body, ty } => {
                    AuthoredParam::MultiAbstraction {
                        binder: reference!(Name, AuthoredNameId, binder),
                        body: reference!(Name, AuthoredNameId, body),
                        ty: reference!(Type, AuthoredTypeId, ty),
                    }
                },
                AuthoredParam::Optional { params } => AuthoredParam::Optional {
                    params: reference!(Params, AuthoredParamsId, params),
                },
            }),
            Node::Params(params) => Node::Params(
                params
                    .into_iter()
                    .map(|param| Ok(reference!(Param, AuthoredParamId, param)))
                    .collect::<Result<_, E>>()?,
            ),
            Node::Syntax(items) => Node::Syntax(
                items
                    .into_iter()
                    .map(|item| {
                        Ok(match item {
                            AuthoredSyntax::Literal(text) => AuthoredSyntax::Literal(text),
                            AuthoredSyntax::Param(name) => {
                                AuthoredSyntax::Param(reference!(Name, AuthoredNameId, name))
                            },
                            AuthoredSyntax::TokenKind { name, bind } => AuthoredSyntax::TokenKind {
                                name: reference!(Name, AuthoredNameId, name),
                                bind: bind
                                    .map(|name| Ok(reference!(Name, AuthoredNameId, name)))
                                    .transpose()?,
                            },
                            AuthoredSyntax::GuestBody { open, close, bind, kind } => {
                                AuthoredSyntax::GuestBody {
                                    open: reference!(Name, AuthoredNameId, open),
                                    close: reference!(Name, AuthoredNameId, close),
                                    bind: reference!(Name, AuthoredNameId, bind),
                                    kind,
                                }
                            },
                            AuthoredSyntax::Op(operation) => AuthoredSyntax::Op(reference!(
                                Operation,
                                AuthoredOperationId,
                                operation
                            )),
                        })
                    })
                    .collect::<Result<_, E>>()?,
            ),
            Node::Operation(operation) => Node::Operation(match operation {
                AuthoredOperation::Opt { inner } => AuthoredOperation::Opt {
                    inner: reference!(Syntax, AuthoredSyntaxId, inner),
                },
                AuthoredOperation::Sep { collection, separator, source } => {
                    AuthoredOperation::Sep {
                        collection: reference!(Name, AuthoredNameId, collection),
                        separator,
                        source: source
                            .map(|source| Ok(reference!(Operation, AuthoredOperationId, source)))
                            .transpose()?,
                    }
                },
                AuthoredOperation::Map { source, params, body } => AuthoredOperation::Map {
                    source: reference!(Operation, AuthoredOperationId, source),
                    params: reference!(Names, AuthoredNamesId, params),
                    body: reference!(Syntax, AuthoredSyntaxId, body),
                },
                AuthoredOperation::Zip { left, right } => AuthoredOperation::Zip {
                    left: reference!(Name, AuthoredNameId, left),
                    right: reference!(Name, AuthoredNameId, right),
                },
                AuthoredOperation::Unsupported { tag } => AuthoredOperation::Unsupported { tag },
            }),
            Node::Rule(rule) => Node::Rule(AuthoredRule {
                label: reference!(Name, AuthoredNameId, rule.label),
                category: reference!(Name, AuthoredNameId, rule.category),
                source_body_present: rule.source_body_present,
                explicit_fold: rule.explicit_fold,
                term_context: rule
                    .term_context
                    .map(|params| Ok(reference!(Params, AuthoredParamsId, params)))
                    .transpose()?,
                syntax_pattern: rule
                    .syntax_pattern
                    .map(|syntax| Ok(reference!(Syntax, AuthoredSyntaxId, syntax)))
                    .transpose()?,
                items: rule
                    .items
                    .into_iter()
                    .map(|item| {
                        Ok(match item {
                            AuthoredLegacyItem::Terminal(text) => {
                                AuthoredLegacyItem::Terminal(text)
                            },
                            AuthoredLegacyItem::NonTerminal { ident, kind } => {
                                AuthoredLegacyItem::NonTerminal {
                                    ident: reference!(Name, AuthoredNameId, ident),
                                    kind,
                                }
                            },
                            AuthoredLegacyItem::Binder { category } => AuthoredLegacyItem::Binder {
                                category: reference!(Name, AuthoredNameId, category),
                            },
                            AuthoredLegacyItem::Collection {
                                kind,
                                element,
                                separator,
                                open,
                                close,
                            } => AuthoredLegacyItem::Collection {
                                kind,
                                element: reference!(Name, AuthoredNameId, element),
                                separator,
                                open,
                                close,
                            },
                        })
                    })
                    .collect::<Result<_, E>>()?,
            }),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CollectionKind;
    use std::convert::Infallible;

    struct Graph {
        nodes: Vec<AuthoredNode<usize, u64>>,
        reads: Vec<usize>,
    }

    impl AuthoredCaptureSource for Graph {
        type Handle = usize;
        type Identity = usize;
        type NameKey = u64;
        type Error = &'static str;

        fn identity(&self, handle: usize) -> usize {
            handle
        }
        fn shallow(&mut self, handle: usize) -> Result<AuthoredNode<usize, u64>, Self::Error> {
            self.reads.push(handle);
            self.nodes.get(handle).cloned().ok_or("missing source")
        }
    }

    fn name(spelling: &str, equality_class: u64) -> AuthoredNode<usize, u64> {
        AuthoredNode::Name(AuthoredName {
            spelling: spelling.into(),
            equality_class,
        })
    }

    fn graph() -> Graph {
        use AuthoredNode as N;
        Graph {
            nodes: vec![
                N::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(1),
                    category: AuthoredNameId(2),
                    term_context: Some(AuthoredParamsId(3)),
                    syntax_pattern: Some(AuthoredSyntaxId(4)),
                    items: vec![AuthoredLegacyItem::NonTerminal {
                        ident: AuthoredNameId(2),
                        kind: AuthoredNonTerminalKind::Category,
                    }],
                }),
                name("same", 7),
                name("same", 8),
                N::Params(vec![AuthoredParamId(5), AuthoredParamId(5)]),
                N::Syntax(vec![
                    AuthoredSyntax::Op(AuthoredOperationId(6)),
                    AuthoredSyntax::Op(AuthoredOperationId(6)),
                    AuthoredSyntax::Param(AuthoredNameId(7)),
                    AuthoredSyntax::Literal("raw".into()),
                ]),
                N::Param(AuthoredParam::Simple {
                    name: AuthoredNameId(1),
                    ty: AuthoredTypeId(8),
                }),
                N::Operation(AuthoredOperation::Map {
                    source: AuthoredOperationId(9),
                    params: AuthoredNamesId(10),
                    body: AuthoredSyntaxId(11),
                }),
                name("different", 7),
                N::Type(AuthoredType::Base(AuthoredNameId(2))),
                N::Operation(AuthoredOperation::Unsupported { tag: 42 }),
                N::Names(vec![AuthoredNameId(1), AuthoredNameId(7), AuthoredNameId(1)]),
                N::Syntax(vec![]),
            ],
            reads: vec![],
        }
    }

    #[test]
    fn declarations_use_one_capture_memo_and_keep_original_rule_roots() {
        let declarations = || AuthoredDeclarations {
            categories: vec![AuthoredCategoryDeclaration {
                name: AuthoredNameId(2),
                native: None,
                collection: None,
                byte_observation: crate::SourceObservation::Unavailable,
                literal_observation: crate::SourceObservation::Unavailable,
                element_observation: crate::SourceObservation::Unavailable,
            }],
            tokens: vec![AuthoredTokenDeclaration {
                name: AuthoredNameId(1),
                category: Some(AuthoredNameId(2)),
                from_literals: false,
                has_evaluation: true,
                push: Some(AuthoredNameId(7)),
            }],
            global_tokens: vec![0],
            modes: vec![AuthoredModeDeclaration { name: AuthoredNameId(7), tokens: vec![] }],
        };
        let mut source = graph();
        let mut old_source = graph();
        let roots = [(AuthoredNodeTag::Rule, 0), (AuthoredNodeTag::Rule, 0)];
        let baseline = capture_authored_nodes(&mut old_source, &roots, |_, _| Ok(()))
            .expect("original rule capture");
        let captured =
            capture_authored_declarations(&mut source, &roots, declarations(), |_, _| Ok(()))
                .expect("same controller with header");
        assert_eq!(captured.roots, baseline.roots);
        assert_eq!(source.reads, old_source.reads, "all declaration names were already memoized");
        assert_eq!(captured.store.len(), baseline.store.len());
        let header = captured.store.declarations().expect("retained header");
        assert_eq!(header.categories[0].name, header.tokens[0].category.expect("source category"));
        assert_eq!(header.modes[0].name, header.tokens[0].push.expect("source push"));
        let mut source = graph();
        let captured =
            capture_authored_declarations(&mut source, &[], declarations(), |_, _| Ok(()))
                .expect("zero-rule language capture");
        assert!(captured.roots.is_empty());
        assert_eq!(source.reads, [2, 1, 7], "declaration field order with shared identities");
        assert_eq!(captured.store.len(), 3);
        let header = captured.store.declarations().expect("zero-rule header");
        let name = |id: AuthoredNameId| match captured.store.get(id.0).expect("retained name") {
            AuthoredNode::Name(name) => name,
            _ => panic!("header name changed tag"),
        };
        assert_eq!(
            name(header.tokens[0].name).equality_class,
            name(header.modes[0].name).equality_class
        );
        assert_ne!(
            name(header.categories[0].name).equality_class,
            name(header.tokens[0].name).equality_class
        );
        let mut extended = declarations();
        extended.categories[0].element_observation =
            crate::SourceObservation::Known(Some(AuthoredNameId(7)));
        let mut extended_source = graph();
        let extended =
            capture_authored_declarations(&mut extended_source, &[], extended, |_, _| Ok(()))
                .expect("element uses the same capture table");
        assert_eq!(extended_source.reads, [2, 7, 1]);
        let extended_header = extended.store.declarations().expect("extended header");
        assert_eq!(
            extended_header.categories[0].element_observation,
            crate::SourceObservation::Known(Some(extended_header.modes[0].name))
        );
        let mut source = graph();
        assert!(matches!(
            capture_authored_declarations(&mut source, &[], declarations(), |_, _| Err("refused")),
            Err(AuthoredCaptureError::Admission("refused"))
        ));
    }

    #[test]
    fn capture_preserves_aliases_source_equality_and_ordered_roots() {
        let mut graph = graph();
        let mut phases = Vec::new();
        let captured = capture_authored_nodes(
            &mut graph,
            &[
                (AuthoredNodeTag::Rule, 0),
                (AuthoredNodeTag::Rule, 0),
                (AuthoredNodeTag::Name, 7),
            ],
            |step, node| {
                phases.push((step, node.tag()));
                Ok(())
            },
        )
        .expect("capture complete graph");
        assert_eq!(graph.reads, [0, 1, 2, 3, 5, 8, 4, 6, 9, 10, 7, 11]);
        assert_eq!(captured.roots, [11, 11, 6]);
        assert_eq!(captured.store.len(), 12);
        assert_eq!(phases.len(), 24, "Ready reuse has no admission callback");
        assert_eq!(
            phases[0].0,
            AuthoredCaptureAdmission {
                phase: AuthoredCapturePhase::Enter,
                stored_nodes: 0,
                memoized_nodes: 0,
                name_classes: 0,
                scheduled_frames: 8,
            }
        );
        for (index, expected_spelling, expected_class) in
            [(0, "same", 0), (1, "same", 1), (6, "different", 0)]
        {
            assert_eq!(
                captured.store.get(index),
                Some(&AuthoredNode::Name(AuthoredName {
                    spelling: expected_spelling.into(),
                    equality_class: expected_class,
                }))
            );
        }
        assert_eq!(
            captured.store.get(4),
            Some(&AuthoredNode::Params(vec![AuthoredParamId(3), AuthoredParamId(3)]))
        );
        assert_eq!(
            captured.store.get(7),
            Some(&AuthoredNode::Names(vec![
                AuthoredNameId(0),
                AuthoredNameId(6),
                AuthoredNameId(0)
            ]))
        );
        assert_eq!(
            captured.store.get(10),
            Some(&AuthoredNode::Syntax(vec![
                AuthoredSyntax::Op(AuthoredOperationId(9)),
                AuthoredSyntax::Op(AuthoredOperationId(9)),
                AuthoredSyntax::Param(AuthoredNameId(6)),
                AuthoredSyntax::Literal("raw".into()),
            ]))
        );
        captured.store.validate().expect("captured store valid");
    }

    #[test]
    fn capture_refuses_cycles_wrong_tags_missing_source_and_admission() {
        let mut cycle = Graph {
            nodes: vec![AuthoredNode::Type(AuthoredType::Arrow {
                domain: AuthoredTypeId(0),
                codomain: AuthoredTypeId(0),
            })],
            reads: vec![],
        };
        assert_eq!(
            capture_authored_nodes(&mut cycle, &[(AuthoredNodeTag::Type, 0)], |_, _| Ok(())),
            Err(AuthoredCaptureError::Cycle)
        );
        assert_eq!(cycle.reads, [0]);
        let mut wrong = graph();
        assert_eq!(
            capture_authored_nodes(&mut wrong, &[(AuthoredNodeTag::Type, 1)], |_, _| panic!(
                "wrong tag must precede admission"
            )),
            Err(AuthoredCaptureError::WrongSourceTag {
                expected: AuthoredNodeTag::Type,
                actual: AuthoredNodeTag::Name
            })
        );
        assert_eq!(
            capture_authored_nodes(
                &mut wrong,
                &[(AuthoredNodeTag::Name, usize::MAX)],
                |_, _| panic!("missing source must precede admission")
            ),
            Err(AuthoredCaptureError::Source("missing source"))
        );
        for phase in [AuthoredCapturePhase::Enter, AuthoredCapturePhase::Finish] {
            let mut input = graph();
            let mut calls = Vec::new();
            let result =
                capture_authored_nodes(&mut input, &[(AuthoredNodeTag::Rule, 0)], |step, _| {
                    calls.push(step);
                    if step.phase == phase {
                        Err("budget")
                    } else {
                        Ok(())
                    }
                });
            assert_eq!(result, Err(AuthoredCaptureError::Admission("budget")));
            assert_eq!(calls.last().expect("admission called").stored_nodes, 0);
            assert_eq!(calls.last().expect("admission called").name_classes, 0);
            assert_eq!(
                input.reads,
                if phase == AuthoredCapturePhase::Enter {
                    vec![0]
                } else {
                    vec![0, 1]
                }
            );
        }
    }

    #[test]
    fn capture_preserves_absent_versus_present_empty_sequences() {
        let mut graph = Graph {
            nodes: vec![
                AuthoredNode::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(2),
                    category: AuthoredNameId(2),
                    term_context: None,
                    syntax_pattern: None,
                    items: vec![],
                }),
                AuthoredNode::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(2),
                    category: AuthoredNameId(2),
                    term_context: Some(AuthoredParamsId(3)),
                    syntax_pattern: Some(AuthoredSyntaxId(4)),
                    items: vec![],
                }),
                name("R", 99),
                AuthoredNode::Params(vec![]),
                AuthoredNode::Syntax(vec![]),
                AuthoredNode::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(2),
                    category: AuthoredNameId(2),
                    term_context: Some(AuthoredParamsId(3)),
                    syntax_pattern: None,
                    items: vec![],
                }),
                AuthoredNode::Rule(AuthoredRule {
                    source_body_present: crate::SourceObservation::Unavailable,
                    explicit_fold: crate::SourceObservation::Unavailable,
                    label: AuthoredNameId(2),
                    category: AuthoredNameId(2),
                    term_context: None,
                    syntax_pattern: Some(AuthoredSyntaxId(4)),
                    items: vec![],
                }),
            ],
            reads: vec![],
        };
        let captured = capture_authored_nodes(
            &mut graph,
            &[
                (AuthoredNodeTag::Rule, 0),
                (AuthoredNodeTag::Rule, 1),
                (AuthoredNodeTag::Rule, 5),
                (AuthoredNodeTag::Rule, 6),
            ],
            |_, _| Ok(()),
        )
        .expect("capture optional presence");
        for (root, expected) in
            captured
                .roots
                .iter()
                .zip([(false, false), (true, true), (true, false), (false, true)])
        {
            let Some(AuthoredNode::Rule(rule)) = captured.store.get(*root) else {
                panic!("rule")
            };
            assert_eq!((rule.term_context.is_some(), rule.syntax_pattern.is_some()), expected);
        }
        let Some(AuthoredNode::Rule(absent)) = captured.store.get(captured.roots[0]) else {
            panic!("rule")
        };
        let Some(AuthoredNode::Rule(present)) = captured.store.get(captured.roots[1]) else {
            panic!("rule")
        };
        assert_eq!((absent.term_context, absent.syntax_pattern), (None, None));
        assert_eq!(
            captured
                .store
                .get(present.term_context.expect("present params").0),
            Some(&AuthoredNode::Params(vec![]))
        );
        assert_eq!(
            captured
                .store
                .get(present.syntax_pattern.expect("present syntax").0),
            Some(&AuthoredNode::Syntax(vec![]))
        );
    }

    #[test]
    fn remap_visits_every_immediate_field_in_exact_visitor_order() {
        use AuthoredNode as N;
        let mut nodes: Vec<AuthoredNode<u32, u32>> = vec![
            N::Name(AuthoredName {
                spelling: "raw".into(),
                equality_class: 17,
            }),
            N::Names(vec![AuthoredNameId(1), AuthoredNameId(1), AuthoredNameId(3)]),
            N::Type(AuthoredType::Base(AuthoredNameId(1))),
            N::Type(AuthoredType::Collection {
                kind: CollectionKind::List,
                element: AuthoredTypeId(2),
            }),
            N::Type(AuthoredType::Map {
                key: AuthoredTypeId(1),
                value: AuthoredTypeId(2),
            }),
            N::Type(AuthoredType::KeyedPathMap {
                key: AuthoredTypeId(1),
                value: AuthoredTypeId(2),
            }),
            N::Type(AuthoredType::Arrow {
                domain: AuthoredTypeId(1),
                codomain: AuthoredTypeId(2),
            }),
            N::Type(AuthoredType::MultiBinder { inner: AuthoredTypeId(2) }),
            N::Type(AuthoredType::Unsupported { tag: 99 }),
            N::Param(AuthoredParam::Simple {
                name: AuthoredNameId(1),
                ty: AuthoredTypeId(2),
            }),
            N::Param(AuthoredParam::GuardBody { name: AuthoredNameId(1) }),
            N::Param(AuthoredParam::Abstraction {
                binder: AuthoredNameId(1),
                body: AuthoredNameId(2),
                ty: AuthoredTypeId(3),
            }),
            N::Param(AuthoredParam::MultiAbstraction {
                binder: AuthoredNameId(1),
                body: AuthoredNameId(2),
                ty: AuthoredTypeId(3),
            }),
            N::Param(AuthoredParam::Optional { params: AuthoredParamsId(1) }),
            N::Params(vec![AuthoredParamId(1), AuthoredParamId(1)]),
            N::Operation(AuthoredOperation::Opt { inner: AuthoredSyntaxId(1) }),
            N::Operation(AuthoredOperation::Map {
                source: AuthoredOperationId(1),
                params: AuthoredNamesId(2),
                body: AuthoredSyntaxId(3),
            }),
            N::Operation(AuthoredOperation::Zip {
                left: AuthoredNameId(1),
                right: AuthoredNameId(2),
            }),
            N::Operation(AuthoredOperation::Unsupported { tag: 55 }),
        ];
        for presence in [false, true] {
            nodes.push(N::Operation(AuthoredOperation::Sep {
                collection: AuthoredNameId(1),
                separator: ";|".into(),
                source: presence.then_some(AuthoredOperationId(2)),
            }));
            nodes.push(N::Syntax(vec![
                AuthoredSyntax::Literal("unparsed".into()),
                AuthoredSyntax::Param(AuthoredNameId(1)),
                AuthoredSyntax::TokenKind {
                    name: AuthoredNameId(2),
                    bind: presence.then_some(AuthoredNameId(3)),
                },
                AuthoredSyntax::GuestBody {
                    open: AuthoredNameId(4),
                    close: AuthoredNameId(5),
                    bind: AuthoredNameId(6),
                    kind: AuthoredDelimitedRegionKind::Flt,
                },
                AuthoredSyntax::Op(AuthoredOperationId(7)),
            ]));
            nodes.push(N::Rule(AuthoredRule {
                source_body_present: crate::SourceObservation::Unavailable,
                explicit_fold: crate::SourceObservation::Unavailable,
                label: AuthoredNameId(1),
                category: AuthoredNameId(2),
                term_context: presence.then_some(AuthoredParamsId(3)),
                syntax_pattern: presence.then_some(AuthoredSyntaxId(4)),
                items: vec![
                    AuthoredLegacyItem::Terminal("opaque".into()),
                    AuthoredLegacyItem::NonTerminal {
                        ident: AuthoredNameId(5),
                        kind: AuthoredNonTerminalKind::Integer,
                    },
                    AuthoredLegacyItem::Binder { category: AuthoredNameId(6) },
                    AuthoredLegacyItem::Collection {
                        kind: CollectionKind::Map,
                        element: AuthoredNameId(7),
                        separator: ",".into(),
                        open: Some("[".into()),
                        close: None,
                    },
                ],
            }));
        }
        for node in nodes {
            let mut expected = Vec::new();
            node.try_for_each_reference(|tag, id| {
                expected.push((tag, id));
                Ok::<_, Infallible>(())
            })
            .expect("infallible visitor");
            let mut actual = Vec::new();
            let mut names = 0;
            let mapped = node
                .clone()
                .try_map_observations(
                    |tag, id| {
                        actual.push((tag, id));
                        Ok::<_, Infallible>(id + 100)
                    },
                    |key| {
                        names += 1;
                        Ok(key + 100)
                    },
                )
                .expect("infallible remap");
            assert_eq!(actual, expected);
            assert_eq!(names, usize::from(node.tag() == AuthoredNodeTag::Name));
            let mut mapped_edges = Vec::new();
            mapped
                .try_for_each_reference(|tag, id| {
                    mapped_edges.push((tag, id));
                    Ok::<_, Infallible>(())
                })
                .expect("infallible visitor");
            assert_eq!(
                mapped_edges,
                expected
                    .iter()
                    .map(|&(tag, id)| (tag, id + 100))
                    .collect::<Vec<_>>()
            );
            let recovered = mapped
                .try_map_observations(|_, id| Ok::<_, Infallible>(id - 100), |key| Ok(key - 100))
                .expect("invert renaming");
            assert_eq!(recovered, node, "all nonreference payloads preserved");
            for stop in 0..expected.len() {
                let mut visited = 0;
                let result = node.clone().try_map_observations(
                    |_, id| {
                        let position = visited;
                        visited += 1;
                        if position == stop {
                            Err("stop")
                        } else {
                            Ok(id)
                        }
                    },
                    Ok,
                );
                assert_eq!(result, Err("stop"));
                assert_eq!(visited, stop + 1, "no observation after failure");
            }
        }
    }

    #[test]
    fn capture_and_drop_deep_source_use_a_small_native_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut nodes = vec![
                    name("leaf", 100),
                    AuthoredNode::Type(AuthoredType::Base(AuthoredNameId(0))),
                ];
                for child in 1..20_001 {
                    let ty = match child % 2 {
                        0 => AuthoredType::MultiBinder { inner: AuthoredTypeId(child) },
                        _ => AuthoredType::Arrow {
                            domain: AuthoredTypeId(1),
                            codomain: AuthoredTypeId(child),
                        },
                    };
                    nodes.push(AuthoredNode::Type(ty));
                }
                let root = nodes.len() - 1;
                let mut graph = Graph { nodes, reads: vec![] };
                let result =
                    capture_authored_nodes(&mut graph, &[(AuthoredNodeTag::Type, root)], |_, _| {
                        Ok(())
                    })
                    .expect("deep worklist capture");
                assert_eq!(result.store.len(), root + 1);
                assert_eq!(result.roots, [root as u32]);
                drop(result);
                drop(graph);
            })
            .expect("spawn small-stack capture")
            .join()
            .expect("capture and cleanup stack-safe");
    }
}
