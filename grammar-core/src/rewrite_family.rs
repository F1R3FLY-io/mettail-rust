use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewritePatternKind<N> {
    Variable(N),
    Application(N),
    Abstraction { binders: usize },
    Context,
    Computation,
}

pub trait RewriteFamilyReader {
    type Node: Copy;
    type Name: Copy;
    type Sort: Copy;
    type Error;

    fn kind(&self, node: Self::Node) -> Result<RewritePatternKind<Self::Name>, Self::Error>;
    fn child_count(&self, node: Self::Node) -> usize;
    fn child_at(&self, node: Self::Node, index: usize) -> Option<Self::Node>;
    fn binder_at(&self, node: Self::Node, index: usize) -> Option<Self::Name>;
    fn variable_count(&self, node: Self::Node) -> usize;
    fn variable_at(&self, node: Self::Node, index: usize) -> Option<Self::Name>;
    fn same_header(&self, left: Self::Node, right: Self::Node) -> Result<bool, Self::Error>;
    fn same_name(&self, left: Self::Name, right: Self::Name) -> bool;
    fn name_is(&self, name: Self::Name, spelling: &str) -> bool;
    fn same_sort(&self, left: Self::Sort, right: Self::Sort) -> bool;
    fn valid_sort(&self, sort: Self::Sort) -> Result<bool, Self::Error>;
    fn node_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
    ) -> Result<Option<Self::Sort>, Self::Error>;
    fn child_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
        index: usize,
    ) -> Result<Option<Self::Sort>, Self::Error>;
    fn abstraction_sorts(
        &self,
        expected: Self::Sort,
        binder_count: usize,
    ) -> Result<(Self::Sort, Self::Sort), Self::Error>;
}

pub struct RewriteFamilyDeclaration<N, S> {
    pub context_index: usize,
    pub name: N,
    pub domains: Vec<S>,
    pub result: S,
}

pub struct RewriteFamilyInput<N, S> {
    pub context_index: usize,
    pub name: N,
    pub sort: S,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewriteSide {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RewriteFamilyLocation {
    Pattern {
        side: RewriteSide,
        occurrence: usize,
        path: Vec<usize>,
    },
    Context(usize),
    External(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewriteFamilyProblem {
    DuplicateDeclaration,
    UnknownSort,
    ContextMismatch,
    ProjectionMismatch,
    ProjectionOutsideTypedContext,
    FamilyAsValue,
    FamilyAsBinder,
    ArgumentArity,
    ArgumentNotVariable,
    EscapedArgument,
    ArgumentSort,
    RepeatedArgument,
    MissingDependency,
    RepeatedFamily,
    MissingFamily,
    EndpointSort,
    UnknownBinderSort,
    AmbiguousBinderReference { binder_index: usize },
}

#[derive(Debug, PartialEq, Eq)]
pub enum RewriteFamilyError<E> {
    Reader(E),
    Allocation,
    CounterOverflow,
    InvalidReader,
    Invalid {
        problem: RewriteFamilyProblem,
        family: Option<usize>,
        location: RewriteFamilyLocation,
        related: Option<RewriteFamilyLocation>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct ProjectionReplacement {
    pub side: RewriteSide,
    pub occurrence: usize,
    pub subtree_end: usize,
    pub family: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct BinderRename {
    pub left_occurrence: usize,
    pub right_occurrence: usize,
    pub binder_index: usize,
    pub name: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NormalizedFamily {
    pub context_index: usize,
    pub source: String,
    pub target: String,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct RewriteFamilyPlan {
    pub replacements: Vec<ProjectionReplacement>,
    pub binder_renames: Vec<BinderRename>,
    pub families: Vec<NormalizedFamily>,
}

#[derive(Clone, Copy)]
enum Site {
    Pattern {
        side: RewriteSide,
        occurrence: usize,
        path: usize,
    },
    Context(usize),
    External(usize),
}

struct Path {
    parent: Option<usize>,
    child: usize,
}

struct Binding<N, S> {
    name: N,
    sort: S,
    site: Site,
    right_occurrence: usize,
    binder_index: usize,
}

struct Projection<N> {
    family: usize,
    side: RewriteSide,
    arguments: Vec<N>,
    nodes: usize,
}

enum Frame<N, S> {
    Visit {
        left: N,
        right: N,
        expected: Option<S>,
        path: usize,
        enabled: bool,
    },
    Children {
        left: N,
        right: N,
        expected: Option<S>,
        path: usize,
        enabled: bool,
        next: usize,
        count: usize,
    },
    Leave(usize),
}

fn push<T, E>(items: &mut Vec<T>, item: T) -> Result<(), RewriteFamilyError<E>> {
    items
        .try_reserve(1)
        .map_err(|_| RewriteFamilyError::Allocation)?;
    items.push(item);
    Ok(())
}

fn increment<E>(value: usize, amount: usize) -> Result<usize, RewriteFamilyError<E>> {
    value
        .checked_add(amount)
        .ok_or(RewriteFamilyError::CounterOverflow)
}

fn location<E>(site: Site, paths: &[Path]) -> Result<RewriteFamilyLocation, RewriteFamilyError<E>> {
    match site {
        Site::Context(index) => Ok(RewriteFamilyLocation::Context(index)),
        Site::External(index) => Ok(RewriteFamilyLocation::External(index)),
        Site::Pattern { side, occurrence, mut path } => {
            let mut indices = Vec::new();
            while let Some(parent) = paths[path].parent {
                push(&mut indices, paths[path].child)?;
                path = parent;
            }
            indices.reverse();
            Ok(RewriteFamilyLocation::Pattern { side, occurrence, path: indices })
        },
    }
}

fn invalid<E>(
    problem: RewriteFamilyProblem,
    family: Option<usize>,
    site: Site,
    related: Option<Site>,
    paths: &[Path],
) -> RewriteFamilyError<E> {
    let primary = match location(site, paths) {
        Ok(value) => value,
        Err(error) => return error,
    };
    let related = match related.map(|site| location(site, paths)).transpose() {
        Ok(value) => value,
        Err(error) => return error,
    };
    RewriteFamilyError::Invalid {
        problem,
        family,
        location: primary,
        related,
    }
}

fn family_index<R: RewriteFamilyReader>(
    reader: &R,
    declarations: &[RewriteFamilyDeclaration<R::Name, R::Sort>],
    name: R::Name,
) -> Option<usize> {
    declarations
        .iter()
        .position(|family| reader.same_name(family.name, name))
}

fn projection<R: RewriteFamilyReader>(
    reader: &R,
    node: R::Node,
    declarations: &[RewriteFamilyDeclaration<R::Name, R::Sort>],
    site: Site,
    paths: &[Path],
) -> Result<Option<Projection<R::Name>>, RewriteFamilyError<R::Error>> {
    let RewritePatternKind::Application(selector) =
        reader.kind(node).map_err(RewriteFamilyError::Reader)?
    else {
        return Ok(None);
    };
    let side = if reader.name_is(selector, "s") {
        RewriteSide::Left
    } else if reader.name_is(selector, "t") {
        RewriteSide::Right
    } else {
        return Ok(None);
    };
    if reader.child_count(node) != 1 {
        return Ok(None);
    }
    let call = reader
        .child_at(node, 0)
        .ok_or(RewriteFamilyError::InvalidReader)?;
    let (name, count) = match reader.kind(call).map_err(RewriteFamilyError::Reader)? {
        RewritePatternKind::Variable(name) => {
            if reader.child_count(call) != 0 || reader.variable_count(call) != 0 {
                return Err(RewriteFamilyError::InvalidReader);
            }
            (name, 0)
        },
        RewritePatternKind::Application(name) => (name, reader.child_count(call)),
        _ => return Ok(None),
    };
    let Some(family) = family_index(reader, declarations, name) else {
        return Ok(None);
    };
    if count != declarations[family].domains.len() {
        return Err(invalid(RewriteFamilyProblem::ArgumentArity, Some(family), site, None, paths));
    }
    let mut arguments = Vec::new();
    for index in 0..count {
        let arg = reader
            .child_at(call, index)
            .ok_or(RewriteFamilyError::InvalidReader)?;
        let RewritePatternKind::Variable(name) =
            reader.kind(arg).map_err(RewriteFamilyError::Reader)?
        else {
            return Err(invalid(
                RewriteFamilyProblem::ArgumentNotVariable,
                Some(family),
                site,
                None,
                paths,
            ));
        };
        if reader.child_count(arg) != 0 || reader.variable_count(arg) != 0 {
            return Err(RewriteFamilyError::InvalidReader);
        }
        push(&mut arguments, name)?;
    }
    Ok(Some(Projection {
        family,
        side,
        arguments,
        nodes: increment(count, 2)?,
    }))
}

fn fresh_name<E>(
    mut is_reserved: impl FnMut(&str) -> bool,
    next: &mut usize,
) -> Result<String, RewriteFamilyError<E>> {
    loop {
        let mut name = String::new();
        name.try_reserve(64)
            .map_err(|_| RewriteFamilyError::Allocation)?;
        write!(&mut name, "__mettail_rewrite_{}", *next)
            .map_err(|_| RewriteFamilyError::InvalidReader)?;
        *next = increment(*next, 1)?;
        if !is_reserved(&name) {
            return Ok(name);
        }
    }
}

pub fn plan_rewrite_families<R: RewriteFamilyReader>(
    reader: &R,
    left: R::Node,
    right: R::Node,
    declarations: &[RewriteFamilyDeclaration<R::Name, R::Sort>],
    ambient: &[RewriteFamilyInput<R::Name, R::Sort>],
    external_names: &[R::Name],
    reserved_names: &[R::Name],
) -> Result<RewriteFamilyPlan, RewriteFamilyError<R::Error>> {
    if declarations.is_empty() {
        return Ok(RewriteFamilyPlan::default());
    }
    let mut paths = Vec::new();
    push(&mut paths, Path { parent: None, child: 0 })?;
    let mut reserved = Vec::new();
    let mut external = Vec::new();
    let mut bindings = Vec::new();
    let mut scope = Vec::new();
    for &name in reserved_names {
        push(&mut reserved, name)?;
    }
    for (index, &name) in external_names.iter().enumerate() {
        if let Some(family) = family_index(reader, declarations, name) {
            return Err(invalid(
                RewriteFamilyProblem::FamilyAsValue,
                Some(family),
                Site::External(index),
                None,
                &paths,
            ));
        }
        push(&mut reserved, name)?;
        push(&mut external, (name, Site::External(index)))?;
    }
    for (index, input) in ambient.iter().enumerate() {
        let site = Site::Context(input.context_index);
        if family_index(reader, declarations, input.name).is_some()
            || ambient[..index]
                .iter()
                .any(|other| reader.same_name(other.name, input.name))
        {
            return Err(invalid(
                RewriteFamilyProblem::DuplicateDeclaration,
                None,
                site,
                None,
                &paths,
            ));
        }
        push(&mut reserved, input.name)?;
        push(&mut external, (input.name, site))?;
        push(
            &mut bindings,
            Binding {
                name: input.name,
                sort: input.sort,
                site,
                right_occurrence: 0,
                binder_index: 0,
            },
        )?;
        push(&mut scope, index)?;
    }
    let mut seen = Vec::new();
    for (index, family) in declarations.iter().enumerate() {
        let site = Site::Context(family.context_index);
        if declarations[..index]
            .iter()
            .any(|other| reader.same_name(other.name, family.name))
        {
            return Err(invalid(
                RewriteFamilyProblem::DuplicateDeclaration,
                Some(index),
                site,
                None,
                &paths,
            ));
        }
        for &sort in family.domains.iter().chain(std::iter::once(&family.result)) {
            if !reader
                .valid_sort(sort)
                .map_err(RewriteFamilyError::Reader)?
            {
                return Err(invalid(
                    RewriteFamilyProblem::UnknownSort,
                    Some(index),
                    site,
                    None,
                    &paths,
                ));
            }
        }
        push(&mut reserved, family.name)?;
        push(&mut seen, None)?;
    }
    let mut plan = RewriteFamilyPlan::default();
    let mut frames = Vec::new();
    push(
        &mut frames,
        Frame::Visit {
            left,
            right,
            expected: None,
            path: 0,
            enabled: true,
        },
    )?;
    let mut left_next = 0;
    let mut right_next = 0;
    while let Some(frame) = frames.pop() {
        let (left, right, expected, path, enabled) = match frame {
            Frame::Leave(length) => {
                scope.truncate(length);
                continue;
            },
            Frame::Children {
                left,
                right,
                expected,
                path,
                enabled,
                next,
                count,
            } => {
                if next == count {
                    continue;
                }
                let left_child = reader
                    .child_at(left, next)
                    .ok_or(RewriteFamilyError::InvalidReader)?;
                let right_child = reader
                    .child_at(right, next)
                    .ok_or(RewriteFamilyError::InvalidReader)?;
                let child_path = paths.len();
                push(&mut paths, Path { parent: Some(path), child: next })?;
                let child_expected = if enabled {
                    let sort = |node| match reader.kind(node).map_err(RewriteFamilyError::Reader)? {
                        RewritePatternKind::Abstraction { binders } => {
                            let expected = expected.ok_or(RewriteFamilyError::InvalidReader)?;
                            Ok(Some(
                                reader
                                    .abstraction_sorts(expected, binders)
                                    .map_err(RewriteFamilyError::Reader)?
                                    .1,
                            ))
                        },
                        _ => reader
                            .child_sort(node, expected, next)
                            .map_err(RewriteFamilyError::Reader),
                    };
                    let l = sort(left)?;
                    let r = sort(right)?;
                    match (l, r) {
                        (Some(l), Some(r)) if reader.same_sort(l, r) => Some(l),
                        (None, None) => None,
                        _ => {
                            return Err(invalid(
                                RewriteFamilyProblem::ContextMismatch,
                                None,
                                Site::Pattern {
                                    side: RewriteSide::Left,
                                    occurrence: left_next,
                                    path: child_path,
                                },
                                None,
                                &paths,
                            ))
                        },
                    }
                } else {
                    None
                };
                push(
                    &mut frames,
                    Frame::Children {
                        left,
                        right,
                        expected,
                        path,
                        enabled,
                        next: increment(next, 1)?,
                        count,
                    },
                )?;
                push(
                    &mut frames,
                    Frame::Visit {
                        left: left_child,
                        right: right_child,
                        expected: child_expected,
                        path: child_path,
                        enabled: enabled && child_expected.is_some(),
                    },
                )?;
                continue;
            },
            Frame::Visit { left, right, expected, path, enabled } => {
                (left, right, expected, path, enabled)
            },
        };
        let left_occurrence = left_next;
        let right_occurrence = right_next;
        left_next = increment(left_next, 1)?;
        right_next = increment(right_next, 1)?;
        let left_site = Site::Pattern {
            side: RewriteSide::Left,
            occurrence: left_occurrence,
            path,
        };
        let right_site = Site::Pattern {
            side: RewriteSide::Right,
            occurrence: right_occurrence,
            path,
        };
        let left_projection = projection(reader, left, declarations, left_site, &paths)?;
        let right_projection = projection(reader, right, declarations, right_site, &paths)?;
        if left_projection.is_some() || right_projection.is_some() {
            if !enabled {
                return Err(invalid(
                    RewriteFamilyProblem::ProjectionOutsideTypedContext,
                    None,
                    left_site,
                    Some(right_site),
                    &paths,
                ));
            }
            let (Some(l), Some(r)) = (left_projection, right_projection) else {
                return Err(invalid(
                    RewriteFamilyProblem::ProjectionMismatch,
                    None,
                    left_site,
                    Some(right_site),
                    &paths,
                ));
            };
            let family = l.family;
            if l.side != RewriteSide::Left || r.side != RewriteSide::Right || family != r.family {
                return Err(invalid(
                    RewriteFamilyProblem::ProjectionMismatch,
                    Some(family),
                    left_site,
                    Some(right_site),
                    &paths,
                ));
            }
            if let Some(previous) = seen[family] {
                return Err(invalid(
                    RewriteFamilyProblem::RepeatedFamily,
                    Some(family),
                    left_site,
                    Some(previous),
                    &paths,
                ));
            }
            if expected.is_some_and(|sort| !reader.same_sort(sort, declarations[family].result)) {
                return Err(invalid(
                    RewriteFamilyProblem::EndpointSort,
                    Some(family),
                    left_site,
                    None,
                    &paths,
                ));
            }
            let mut arguments = Vec::new();
            for (index, (&l_name, &r_name)) in l.arguments.iter().zip(&r.arguments).enumerate() {
                let l_id = scope
                    .iter()
                    .rev()
                    .find(|&&id| reader.same_name(bindings[id].name, l_name));
                let r_id = scope
                    .iter()
                    .rev()
                    .find(|&&id| reader.same_name(bindings[id].name, r_name));
                let (Some(&l_id), Some(&r_id)) = (l_id, r_id) else {
                    return Err(invalid(
                        RewriteFamilyProblem::EscapedArgument,
                        Some(family),
                        left_site,
                        Some(right_site),
                        &paths,
                    ));
                };
                if l_id != r_id {
                    return Err(invalid(
                        RewriteFamilyProblem::ProjectionMismatch,
                        Some(family),
                        left_site,
                        Some(right_site),
                        &paths,
                    ));
                }
                if !reader.same_sort(bindings[l_id].sort, declarations[family].domains[index]) {
                    return Err(invalid(
                        RewriteFamilyProblem::ArgumentSort,
                        Some(family),
                        left_site,
                        None,
                        &paths,
                    ));
                }
                if arguments.contains(&l_id) {
                    return Err(invalid(
                        RewriteFamilyProblem::RepeatedArgument,
                        Some(family),
                        left_site,
                        None,
                        &paths,
                    ));
                }
                push(&mut arguments, l_id)?;
                push(&mut reserved, l_name)?;
                push(&mut reserved, r_name)?;
            }
            if scope
                .iter()
                .any(|id| *id >= ambient.len() && !arguments.contains(id))
            {
                return Err(invalid(
                    RewriteFamilyProblem::MissingDependency,
                    Some(family),
                    left_site,
                    None,
                    &paths,
                ));
            }
            left_next = increment(left_occurrence, l.nodes)?;
            right_next = increment(right_occurrence, r.nodes)?;
            push(
                &mut plan.replacements,
                ProjectionReplacement {
                    side: RewriteSide::Left,
                    occurrence: left_occurrence,
                    subtree_end: left_next,
                    family,
                },
            )?;
            push(
                &mut plan.replacements,
                ProjectionReplacement {
                    side: RewriteSide::Right,
                    occurrence: right_occurrence,
                    subtree_end: right_next,
                    family,
                },
            )?;
            seen[family] = Some(left_site);
            continue;
        }
        if !reader
            .same_header(left, right)
            .map_err(RewriteFamilyError::Reader)?
            || reader.child_count(left) != reader.child_count(right)
            || reader.variable_count(left) != reader.variable_count(right)
        {
            return Err(invalid(
                RewriteFamilyProblem::ContextMismatch,
                None,
                left_site,
                Some(right_site),
                &paths,
            ));
        }
        let left_kind = reader.kind(left).map_err(RewriteFamilyError::Reader)?;
        let right_kind = reader.kind(right).map_err(RewriteFamilyError::Reader)?;
        if let RewritePatternKind::Variable(name) | RewritePatternKind::Application(name) =
            left_kind
        {
            if let Some(family) = family_index(reader, declarations, name) {
                return Err(invalid(
                    RewriteFamilyProblem::FamilyAsValue,
                    Some(family),
                    left_site,
                    None,
                    &paths,
                ));
            }
        }
        let enabled = enabled && !matches!(left_kind, RewritePatternKind::Computation);
        let expected = if enabled {
            let l = reader
                .node_sort(left, expected)
                .map_err(RewriteFamilyError::Reader)?;
            let r = reader
                .node_sort(right, expected)
                .map_err(RewriteFamilyError::Reader)?;
            if expected.is_some_and(|expected| {
                l.is_none_or(|actual| !reader.same_sort(expected, actual))
                    || r.is_none_or(|actual| !reader.same_sort(expected, actual))
            }) {
                return Err(invalid(
                    RewriteFamilyProblem::ContextMismatch,
                    None,
                    left_site,
                    Some(right_site),
                    &paths,
                ));
            }
            match (l, r) {
                (Some(l), Some(r)) if reader.same_sort(l, r) => Some(l),
                (None, None) => None,
                _ => {
                    return Err(invalid(
                        RewriteFamilyProblem::ContextMismatch,
                        None,
                        left_site,
                        Some(right_site),
                        &paths,
                    ))
                },
            }
        } else {
            None
        };
        match (left_kind, right_kind) {
            (RewritePatternKind::Variable(l), RewritePatternKind::Variable(r))
            | (RewritePatternKind::Application(l), RewritePatternKind::Application(r)) => {
                if !reader.same_name(l, r) {
                    return Err(invalid(
                        RewriteFamilyProblem::ContextMismatch,
                        None,
                        left_site,
                        Some(right_site),
                        &paths,
                    ));
                }
                if let Some(family) = family_index(reader, declarations, l) {
                    return Err(invalid(
                        RewriteFamilyProblem::FamilyAsValue,
                        Some(family),
                        left_site,
                        None,
                        &paths,
                    ));
                }
                push(&mut reserved, l)?;
                push(&mut reserved, r)?;
                if matches!(left_kind, RewritePatternKind::Variable(_)) {
                    push(&mut external, (l, left_site))?;
                    push(&mut external, (r, right_site))?;
                }
            },
            (
                RewritePatternKind::Abstraction { binders: count },
                RewritePatternKind::Abstraction { binders: other },
            ) if count == other => {
                if reader.child_count(left) != 1 {
                    return Err(RewriteFamilyError::InvalidReader);
                }
                let binder_sort = if enabled {
                    let sort = expected.ok_or_else(|| {
                        invalid(
                            RewriteFamilyProblem::UnknownBinderSort,
                            None,
                            left_site,
                            None,
                            &paths,
                        )
                    })?;
                    Some(
                        reader
                            .abstraction_sorts(sort, count)
                            .map_err(RewriteFamilyError::Reader)?
                            .0,
                    )
                } else {
                    None
                };
                let old_scope = scope.len();
                for index in 0..count {
                    let l = reader
                        .binder_at(left, index)
                        .ok_or(RewriteFamilyError::InvalidReader)?;
                    let r = reader
                        .binder_at(right, index)
                        .ok_or(RewriteFamilyError::InvalidReader)?;
                    if !reader.same_name(l, r) {
                        return Err(invalid(
                            RewriteFamilyProblem::ContextMismatch,
                            None,
                            left_site,
                            Some(right_site),
                            &paths,
                        ));
                    }
                    if let Some(family) = family_index(reader, declarations, l) {
                        return Err(invalid(
                            RewriteFamilyProblem::FamilyAsBinder,
                            Some(family),
                            left_site,
                            None,
                            &paths,
                        ));
                    }
                    push(&mut reserved, l)?;
                    push(&mut reserved, r)?;
                    if let Some(sort) = binder_sort {
                        let id = bindings.len();
                        push(
                            &mut bindings,
                            Binding {
                                name: l,
                                sort,
                                site: left_site,
                                right_occurrence,
                                binder_index: index,
                            },
                        )?;
                        push(&mut scope, id)?;
                    } else {
                        push(&mut external, (l, left_site))?;
                        push(&mut external, (r, right_site))?;
                    }
                }
                push(&mut frames, Frame::Leave(old_scope))?;
            },
            (RewritePatternKind::Context, RewritePatternKind::Context)
            | (RewritePatternKind::Computation, RewritePatternKind::Computation) => {},
            _ => {
                return Err(invalid(
                    RewriteFamilyProblem::ContextMismatch,
                    None,
                    left_site,
                    Some(right_site),
                    &paths,
                ))
            },
        }
        for index in 0..reader.variable_count(left) {
            let l = reader
                .variable_at(left, index)
                .ok_or(RewriteFamilyError::InvalidReader)?;
            let r = reader
                .variable_at(right, index)
                .ok_or(RewriteFamilyError::InvalidReader)?;
            if !reader.same_name(l, r) {
                return Err(invalid(
                    RewriteFamilyProblem::ContextMismatch,
                    None,
                    left_site,
                    Some(right_site),
                    &paths,
                ));
            }
            if let Some(family) = family_index(reader, declarations, l) {
                return Err(invalid(
                    RewriteFamilyProblem::FamilyAsValue,
                    Some(family),
                    left_site,
                    None,
                    &paths,
                ));
            }
            push(&mut reserved, l)?;
            push(&mut reserved, r)?;
            push(&mut external, (l, left_site))?;
            push(&mut external, (r, right_site))?;
        }
        push(
            &mut frames,
            Frame::Children {
                left,
                right,
                expected,
                path,
                enabled,
                next: 0,
                count: reader.child_count(left),
            },
        )?;
    }
    for (index, site) in seen.iter().enumerate() {
        if site.is_none() {
            return Err(invalid(
                RewriteFamilyProblem::MissingFamily,
                Some(index),
                Site::Context(declarations[index].context_index),
                None,
                &paths,
            ));
        }
    }
    let mut next_name = 0;
    for (index, binding) in bindings.iter().enumerate().skip(ambient.len()) {
        let repeated = bindings
            .iter()
            .enumerate()
            .skip(ambient.len())
            .any(|(other, item)| other != index && reader.same_name(item.name, binding.name));
        if !repeated {
            continue;
        }
        if let Some((_, site)) = external
            .iter()
            .find(|(name, _)| reader.same_name(*name, binding.name))
        {
            return Err(invalid(
                RewriteFamilyProblem::AmbiguousBinderReference {
                    binder_index: binding.binder_index,
                },
                None,
                binding.site,
                Some(*site),
                &paths,
            ));
        }
        let Site::Pattern { occurrence, .. } = binding.site else {
            return Err(RewriteFamilyError::InvalidReader);
        };
        push(
            &mut plan.binder_renames,
            BinderRename {
                left_occurrence: occurrence,
                right_occurrence: binding.right_occurrence,
                binder_index: binding.binder_index,
                name: fresh_name(
                    |candidate| reserved.iter().any(|name| reader.name_is(*name, candidate)),
                    &mut next_name,
                )?,
            },
        )?;
    }
    for family in declarations {
        let source = fresh_name(
            |candidate| reserved.iter().any(|name| reader.name_is(*name, candidate)),
            &mut next_name,
        )?;
        let target = fresh_name(
            |candidate| reserved.iter().any(|name| reader.name_is(*name, candidate)),
            &mut next_name,
        )?;
        push(
            &mut plan.families,
            NormalizedFamily {
                context_index: family.context_index,
                source,
                target,
            },
        )?;
    }
    Ok(plan)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn checked_name_allocator_matches_finite_candidate_oracle(
            start in 0usize..100,
            reserved in prop::collection::btree_set(0usize..140, 0..100),
            count in 1usize..30,
        ) {
            let expected: Vec<_> = (start..).filter(|index| !reserved.contains(index)).take(count).collect();
            let reserved: std::collections::BTreeSet<_> = reserved.iter().map(|index| format!("__mettail_rewrite_{index}")).collect();
            let mut next = start;
            for index in expected {
                let actual = fresh_name::<()>(|name| reserved.contains(name), &mut next).unwrap();
                prop_assert_eq!(actual, format!("__mettail_rewrite_{index}"));
                prop_assert_eq!(next, index + 1);
            }
        }
    }

    #[test]
    fn checked_name_allocator_refuses_counter_overflow() {
        let mut next = usize::MAX - 1;
        let name = fresh_name::<()>(|_| false, &mut next).unwrap();
        assert_eq!(name, format!("__mettail_rewrite_{}", usize::MAX - 1));
        assert_eq!(next, usize::MAX);
        assert_eq!(
            fresh_name::<()>(|_| false, &mut next),
            Err(RewriteFamilyError::CounterOverflow)
        );
        assert_eq!(next, usize::MAX);
        let mut next = usize::MAX - 2;
        assert_eq!(fresh_name::<()>(|_| true, &mut next), Err(RewriteFamilyError::CounterOverflow));
        assert_eq!(next, usize::MAX);
    }
}
