use super::*;
use crate::schema::rule_context::{decode_rule_context_type, DecodedRuleContext};
use mettail_grammar_core::rewrite_family::{
    plan_rewrite_families, RewriteFamilyDeclaration, RewriteFamilyError, RewriteFamilyInput,
    RewriteFamilyLocation, RewriteFamilyPlan, RewriteFamilyProblem, RewriteFamilyReader,
    RewritePatternKind, RewriteSide,
};

enum Children<'a> {
    Slice(&'a [RhoValue]),
    Fields(&'a [RhoValue], &'static [usize]),
}

impl<'a> Children<'a> {
    fn len(&self) -> usize {
        match self {
            Self::Slice(values) => values.len(),
            Self::Fields(_, indices) => indices.len(),
        }
    }

    fn get(&self, index: usize) -> Option<&'a RhoValue> {
        match self {
            Self::Slice(values) => values.get(index),
            Self::Fields(values, indices) => values.get(*indices.get(index)?),
        }
    }
}

struct View<'a> {
    kind: RewritePatternKind<&'a str>,
    children: Children<'a>,
    binders: &'a [RhoValue],
    variables: &'a [RhoValue],
}

fn view<'a>(value: &'a RhoValue, path: &str) -> Result<View<'a>, ValueDecodeError> {
    let mut result = View {
        kind: RewritePatternKind::Context,
        children: Children::Slice(&[]),
        binders: &[],
        variables: &[],
    };
    if let RhoValue::String(name) = value {
        result.kind = RewritePatternKind::Variable(name);
        return Ok(result);
    }
    let values = expect_list(value, path)?;
    let tag = values
        .first()
        .ok_or_else(|| ValueDecodeError::new(path, "empty pattern"))?;
    let tag = expect_nonempty_string(tag, path)?;
    match tag {
        "^" | "^*" => {
            require_len(values, 3, path)?;
            result.binders = if tag == "^" {
                &values[1..2]
            } else {
                expect_list(&values[1], path)?
            };
            result.kind = RewritePatternKind::Abstraction { binders: result.binders.len() };
            result.children = Children::Fields(values, &[2]);
        },
        "coll" | "coll_typed" => {
            let offset = usize::from(tag == "coll_typed");
            if values.len() != 3 + offset && values.len() != 4 + offset {
                return error(path, "invalid collection pattern shape");
            }
            result.children = Children::Slice(expect_list(&values[1 + offset], path)?);
            match &values[2 + offset] {
                RhoValue::Nil => {},
                RhoValue::String(_) => result.variables = &values[2 + offset..3 + offset],
                _ => return error(path, "collection remainder must be a variable or Nil"),
            }
        },
        "lit" => require_len(values, 3, path)?,
        "product" => result.children = Children::Slice(&values[1..]),
        "eval" => {
            result.kind = RewritePatternKind::Computation;
            match values.len() {
                3 => result.children = Children::Slice(&values[1..]),
                4 => {
                    result.children = Children::Fields(values, &[1, 3]);
                    result.variables = &values[2..3];
                },
                _ => return error(path, "invalid substitution pattern shape"),
            }
        },
        "pmap" => {
            require_len(values, 4, path)?;
            result.kind = RewritePatternKind::Computation;
            result.children = Children::Fields(values, &[1, 3]);
            result.variables = expect_list(&values[2], path)?;
        },
        "pzip" => {
            require_len(values, 3, path)?;
            result.kind = RewritePatternKind::Computation;
            result.children = Children::Slice(&values[1..]);
        },
        _ => {
            result.kind = RewritePatternKind::Application(tag);
            result.children = Children::Slice(&values[1..]);
        },
    }
    Ok(result)
}

struct Reader<'a> {
    signature: &'a Signature,
    path: &'a str,
    limits: core::TheoryLimitsV1,
}

impl<'a> Reader<'a> {
    fn registered(&self, name: &str) -> Result<&'a core::TheorySortV1, ValueDecodeError> {
        self.signature.sort(name).ok_or_else(|| {
            ValueDecodeError::new(self.path, format!("unknown theory sort `{name}`"))
        })
    }

    fn collection_element(
        &self,
        values: &[RhoValue],
        sort: &str,
    ) -> Result<&'a str, ValueDecodeError> {
        let offset = usize::from(pattern_tag_is_list(values, "coll_typed"));
        let mode = values
            .get(3 + offset)
            .map(|value| decode_pathmap_mode(value, self.path))
            .transpose()?
            .flatten();
        let core::TheorySortKindV1::Collection { kind, key, element } =
            &self.registered(sort)?.kind
        else {
            return error(self.path, format!("`{sort}` is not a collection sort"));
        };
        if *kind != core::CollectionKind::PathMap && mode.is_some() {
            return error(self.path, "only a PathMap collection may carry PathMap mode evidence");
        }
        let element = match (kind, mode) {
            (core::CollectionKind::PathMap, Some(core::PathMapModeV1::Set)) => {
                key.as_deref().ok_or_else(|| {
                    ValueDecodeError::new(
                        self.path,
                        "set-mode PathMap sort has no declared key sort",
                    )
                })?
            },
            _ => element.as_str(),
        };
        if offset == 1 && expect_nonempty_string(&values[1], self.path)? != element {
            return error(self.path, format!("collection element sort is `{element}`"));
        }
        Ok(element)
    }
}

fn pattern_tag_is_list(values: &[RhoValue], tag: &str) -> bool {
    matches!(values.first(), Some(RhoValue::String(name)) if name == tag)
}

impl<'a> RewriteFamilyReader for Reader<'a> {
    type Node = &'a RhoValue;
    type Name = &'a str;
    type Sort = &'a str;
    type Error = ValueDecodeError;

    fn kind(&self, node: Self::Node) -> Result<RewritePatternKind<Self::Name>, Self::Error> {
        Ok(view(node, self.path)?.kind)
    }

    fn child_count(&self, node: Self::Node) -> usize {
        view(node, self.path).map_or(0, |view| view.children.len())
    }

    fn child_at(&self, node: Self::Node, index: usize) -> Option<Self::Node> {
        view(node, self.path).ok()?.children.get(index)
    }

    fn binder_at(&self, node: Self::Node, index: usize) -> Option<Self::Name> {
        let RhoValue::String(name) = view(node, self.path).ok()?.binders.get(index)? else {
            return None;
        };
        Some(name)
    }

    fn variable_count(&self, node: Self::Node) -> usize {
        view(node, self.path).map_or(0, |view| view.variables.len())
    }

    fn variable_at(&self, node: Self::Node, index: usize) -> Option<Self::Name> {
        let RhoValue::String(name) = view(node, self.path).ok()?.variables.get(index)? else {
            return None;
        };
        Some(name)
    }

    fn same_header(&self, left: Self::Node, right: Self::Node) -> Result<bool, Self::Error> {
        match (left, right) {
            (RhoValue::String(left), RhoValue::String(right)) => Ok(left == right),
            (RhoValue::List(left), RhoValue::List(right)) => {
                if left.len() != right.len() || left.first() != right.first() {
                    return Ok(false);
                }
                let tag = expect_nonempty_string(&left[0], self.path)?;
                Ok(match tag {
                    "lit" => left == right,
                    "coll" => left[2..] == right[2..],
                    "coll_typed" => left[1] == right[1] && left[3..] == right[3..],
                    _ => true,
                })
            },
            _ => Ok(false),
        }
    }

    fn same_name(&self, left: Self::Name, right: Self::Name) -> bool {
        left == right
    }
    fn name_is(&self, name: Self::Name, spelling: &str) -> bool {
        name == spelling
    }
    fn same_sort(&self, left: Self::Sort, right: Self::Sort) -> bool {
        left == right
    }
    fn valid_sort(&self, sort: Self::Sort) -> Result<bool, Self::Error> {
        Ok(self.signature.sort(sort).is_some())
    }

    fn node_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
    ) -> Result<Option<Self::Sort>, Self::Error> {
        let shape = view(node, self.path)?;
        if let RewritePatternKind::Application(name) = shape.kind {
            let constructor = self.signature.constructors.get(name).ok_or_else(|| {
                ValueDecodeError::new(self.path, format!("unknown constructor `{name}`"))
            })?;
            if constructor.domain.len() != shape.children.len()
                || expected.is_some_and(|sort| sort != constructor.codomain)
            {
                return error(
                    self.path,
                    format!("constructor `{name}` has incompatible arity or result sort"),
                );
            }
            return Ok(Some(&constructor.codomain));
        }
        let RhoValue::List(values) = node else {
            return Ok(expected);
        };
        let tag = expect_nonempty_string(&values[0], self.path)?;
        match tag {
            "^*" => error(
                self.path,
                "multi-abstraction is not supported by the executable theory compiler",
            ),
            "^" => {
                if let Some(sort) = expected {
                    self.abstraction_sorts(sort, shape.binders.len())?;
                }
                Ok(expected)
            },
            "coll" | "coll_typed" => {
                let sort = match expected {
                    Some(sort) => sort,
                    None => {
                        let explicit = if tag == "coll_typed" {
                            Some(expect_nonempty_string(&values[1], self.path)?)
                        } else {
                            None
                        };
                        let name = RuleCompiler::new(self.signature, self.limits, self.path)
                            .unique_collection_sort(explicit, self.path)?;
                        &self.registered(&name)?.name
                    },
                };
                self.collection_element(values, sort)?;
                Ok(Some(sort))
            },
            "product" => {
                if let Some(sort) = expected {
                    let core::TheorySortKindV1::Product { factors } = &self.registered(sort)?.kind
                    else {
                        return error(self.path, format!("`{sort}` is not a product sort"));
                    };
                    if factors.len() != shape.children.len() {
                        return error(
                            self.path,
                            "product arity differs from its registered factors",
                        );
                    }
                }
                Ok(expected)
            },
            _ => Ok(expected),
        }
    }

    fn child_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
        index: usize,
    ) -> Result<Option<Self::Sort>, Self::Error> {
        let shape = view(node, self.path)?;
        if shape.children.get(index).is_none() {
            return error(self.path, "pattern child index is out of range");
        }
        if let RewritePatternKind::Application(name) = shape.kind {
            let constructor = self.signature.constructors.get(name).ok_or_else(|| {
                ValueDecodeError::new(self.path, format!("unknown constructor `{name}`"))
            })?;
            return constructor
                .domain
                .get(index)
                .map(|sort| Some(sort.as_str()))
                .ok_or_else(|| {
                    ValueDecodeError::new(self.path, "constructor domain index is out of range")
                });
        }
        let Some(sort) = expected else {
            return Ok(None);
        };
        let RhoValue::List(values) = node else {
            return Ok(None);
        };
        match expect_nonempty_string(&values[0], self.path)? {
            "coll" | "coll_typed" => {
                let element = self.collection_element(values, sort)?;
                Ok(Some(
                    if shape
                        .children
                        .get(index)
                        .is_some_and(|child| pattern_tag_is(child, "pmap"))
                    {
                        sort
                    } else {
                        element
                    },
                ))
            },
            "product" => {
                let core::TheorySortKindV1::Product { factors } = &self.registered(sort)?.kind
                else {
                    return error(self.path, format!("`{sort}` is not a product sort"));
                };
                factors
                    .get(index)
                    .map(|sort| Some(sort.as_str()))
                    .ok_or_else(|| {
                        ValueDecodeError::new(self.path, "product factor index is out of range")
                    })
            },
            _ => Ok(None),
        }
    }

    fn abstraction_sorts(
        &self,
        expected: Self::Sort,
        binder_count: usize,
    ) -> Result<(Self::Sort, Self::Sort), Self::Error> {
        match &self.registered(expected)?.kind {
            core::TheorySortKindV1::Function { domain, codomain, multiple: false }
                if binder_count == 1 =>
            {
                Ok((domain, codomain))
            },
            _ => error(self.path, format!("`{expected}` is not a unary function sort")),
        }
    }
}

fn premise_names<'a>(
    premises: Option<&'a RhoValue>,
    path: &str,
) -> Result<Vec<&'a str>, ValueDecodeError> {
    let mut names = Vec::new();
    let Some(premises) = premises else {
        return Ok(names);
    };
    let mut work = expect_list(premises, path)?
        .iter()
        .rev()
        .map(|value| (value, false))
        .collect::<Vec<_>>();
    while let Some((value, predicate)) = work.pop() {
        let values = expect_list(value, path)?;
        let tag = values
            .first()
            .ok_or_else(|| ValueDecodeError::new(path, "empty premise or predicate"))?;
        let tag = expect_nonempty_string(tag, path)?;
        if predicate {
            match tag {
                "call" | "ncall" => {
                    require_len(values, 3, path)?;
                    for arg in expect_list(&values[2], path)? {
                        let arg = expect_list(arg, path)?;
                        require_len(arg, 2, path)?;
                        match expect_nonempty_string(&arg[0], path)? {
                            "var" => names.push(expect_nonempty_string(&arg[1], path)?),
                            "const" => {},
                            _ => return error(path, "unknown predicate argument"),
                        }
                    }
                },
                "quant" => {
                    require_len(values, 6, path)?;
                    names.push(expect_nonempty_string(&values[2], path)?);
                    work.push((&values[5], true));
                },
                "and" | "or" => {
                    require_len(values, 2, path)?;
                    work.extend(
                        expect_list(&values[1], path)?
                            .iter()
                            .rev()
                            .map(|value| (value, true)),
                    );
                },
                "not" => {
                    require_len(values, 2, path)?;
                    work.push((&values[1], true));
                },
                "implies" => {
                    require_len(values, 3, path)?;
                    work.push((&values[2], true));
                    work.push((&values[1], true));
                },
                "ac_match" => {
                    require_len(values, 4, path)?;
                    names.push(expect_nonempty_string(&values[1], path)?);
                    for name in expect_list(&values[2], path)? {
                        names.push(expect_nonempty_string(name, path)?);
                    }
                    if !matches!(values[3], RhoValue::Nil) {
                        names.push(expect_nonempty_string(&values[3], path)?);
                    }
                },
                "true" => require_len(values, 1, path)?,
                _ => return error(path, "unknown behavioral predicate"),
            }
        } else {
            match tag {
                "fresh" | "fresh_rest" | "~>" => {
                    require_len(values, 3, path)?;
                    names.push(expect_nonempty_string(&values[1], path)?);
                    names.push(expect_nonempty_string(&values[2], path)?);
                },
                "rel" => {
                    require_len(values, 3, path)?;
                    for name in expect_list(&values[2], path)? {
                        names.push(expect_nonempty_string(name, path)?);
                    }
                },
                "forall" => {
                    require_len(values, 4, path)?;
                    names.push(expect_nonempty_string(&values[1], path)?);
                    names.push(expect_nonempty_string(&values[2], path)?);
                    work.push((&values[3], false));
                },
                "guard" => {
                    require_len(values, 2, path)?;
                    work.push((&values[1], true));
                },
                "intrinsic" => {
                    let shape = decode_intrinsic_shape(value, path)?;
                    names.extend(shape.inputs);
                    names.extend(shape.outputs.into_iter().map(|(name, _)| name));
                },
                _ => return error(path, "unknown rewrite premise"),
            }
        }
    }
    Ok(names)
}

fn apply_pattern_plan(
    value: &mut RhoValue,
    side: RewriteSide,
    plan: &RewriteFamilyPlan,
    path: &str,
) -> Result<(), ValueDecodeError> {
    let mut replacements = plan
        .replacements
        .iter()
        .filter(|edit| edit.side == side)
        .peekable();
    let mut renames = plan.binder_renames.iter().peekable();
    let mut work = vec![value];
    let mut next = 0usize;
    while let Some(value) = work.pop() {
        let occurrence = next;
        next = next.checked_add(1).ok_or_else(|| {
            ValueDecodeError::new(path, "rewrite-family occurrence counter overflow")
        })?;
        if replacements
            .peek()
            .is_some_and(|edit| edit.occurrence == occurrence)
        {
            let edit = replacements
                .next()
                .ok_or_else(|| ValueDecodeError::new(path, "missing projection edit"))?;
            let family = plan
                .families
                .get(edit.family)
                .ok_or_else(|| ValueDecodeError::new(path, "missing family edit"))?;
            *value = RhoValue::String(
                match side {
                    RewriteSide::Left => &family.source,
                    RewriteSide::Right => &family.target,
                }
                .clone(),
            );
            next = edit.subtree_end;
            continue;
        }
        while renames.peek().is_some_and(|edit| match side { RewriteSide::Left => edit.left_occurrence, RewriteSide::Right => edit.right_occurrence } == occurrence) {
            let edit = renames.next().ok_or_else(|| ValueDecodeError::new(path, "missing binder edit"))?;
            let RhoValue::List(values) = value else { return error(path, "binder edit is not an abstraction"); };
            let multiple = pattern_tag_is_list(values, "^*");
            if !multiple && !pattern_tag_is_list(values, "^") { return error(path, "binder edit is not an abstraction"); }
            let binder = values.get_mut(1).ok_or_else(|| ValueDecodeError::new(path, "missing abstraction binder"))?;
            let binder = if multiple {
                let RhoValue::List(binders) = binder else { return error(path, "invalid abstraction binders"); };
                binders.get_mut(edit.binder_index).ok_or_else(|| ValueDecodeError::new(path, "binder edit index is out of range"))?
            } else {
                if edit.binder_index != 0 { return error(path, "binder edit index is out of range"); }
                binder
            };
            *binder = RhoValue::String(edit.name.clone());
        }
        let RhoValue::List(values) = value else {
            continue;
        };
        let tag = expect_nonempty_string(&values[0], path)?;
        let (slice_start, selected, collection) = match tag {
            "^" | "^*" => (0, Some(&[2][..]), None),
            "coll" => (0, None, Some(1)),
            "coll_typed" => (0, None, Some(2)),
            "lit" => continue,
            "eval" if values.len() == 4 => (0, Some(&[1, 3][..]), None),
            "pmap" => (0, Some(&[1, 3][..]), None),
            _ => (1, None, None),
        };
        if let Some(index) = collection {
            let RhoValue::List(children) = &mut values[index] else {
                return error(path, "invalid collection elements");
            };
            work.extend(children.iter_mut().rev());
        } else {
            for (index, child) in values.iter_mut().enumerate().rev() {
                if selected.map_or(index >= slice_start, |indices| indices.contains(&index)) {
                    work.push(child);
                }
            }
        }
    }
    if replacements.next().is_some() || renames.next().is_some() {
        return error(path, "rewrite-family edits do not match the original pattern");
    }
    Ok(())
}

pub(super) fn normalize(
    value: &RhoValue,
    path: &str,
    signature: &Signature,
    limits: core::TheoryLimitsV1,
) -> Result<Option<RhoValue>, ValueDecodeError> {
    let values = expect_map(value, path)?;
    let Some(context) = values.get("context") else {
        return Ok(None);
    };
    let context = expect_list(context, path)?;
    let mut decoded = Vec::new();
    for entry in context {
        let fields = expect_list(entry, path)?;
        require_len(fields, 3, path)?;
        if expect_nonempty_string(&fields[0], path)? != "typed" {
            return error(path, "expected typed context binding");
        }
        decoded.push((
            expect_nonempty_string(&fields[1], path)?,
            decode_rule_context_type(&fields[2], path, true)?,
        ));
    }
    if !decoded
        .iter()
        .any(|(_, ty)| matches!(ty, DecodedRuleContext::RewriteFamily { .. }))
    {
        return Ok(None);
    }
    let mut sorts = Vec::new();
    for (_, ty) in &decoded {
        let (domains, result) = match ty {
            DecodedRuleContext::Ordinary(value) => (Vec::new(), decode_context_sort(value, path)?),
            DecodedRuleContext::RewriteFamily { domains, result } => (
                domains
                    .iter()
                    .map(|value| decode_context_sort(value, path))
                    .collect::<Result<Vec<_>, _>>()?,
                decode_context_sort(result, path)?,
            ),
        };
        sorts.push((domains, result));
    }
    let mut declarations = Vec::new();
    let mut ambient = Vec::new();
    for (context_index, ((name, ty), (domains, result))) in decoded.iter().zip(&sorts).enumerate() {
        match ty {
            DecodedRuleContext::Ordinary(_) => ambient.push(RewriteFamilyInput {
                context_index,
                name: *name,
                sort: result.as_str(),
            }),
            DecodedRuleContext::RewriteFamily { .. } => {
                declarations.push(RewriteFamilyDeclaration {
                    context_index,
                    name: *name,
                    domains: domains.iter().map(String::as_str).collect(),
                    result: result.as_str(),
                })
            },
        }
    }
    let external = premise_names(values.get("premises"), path)?;
    let reserved = signature
        .constructors
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let reader = Reader { signature, path, limits };
    let plan = plan_rewrite_families(
        &reader,
        required(values, "left", path)?,
        required(values, "right", path)?,
        &declarations,
        &ambient,
        &external,
        &reserved,
    )
    .map_err(|error| match error {
        RewriteFamilyError::Reader(error) => error,
        RewriteFamilyError::Invalid {
            problem: RewriteFamilyProblem::AmbiguousBinderReference { binder_index },
            location: RewriteFamilyLocation::Pattern { side, occurrence, path: children },
            related,
            ..
        } => {
            let key = match side { RewriteSide::Left => "left", RewriteSide::Right => "right" };
            let mut node = match required(values, key, path) { Ok(node) => node, Err(error) => return error };
            for &child in &children {
                let Some(next) = reader.child_at(node, child) else {
                    return ValueDecodeError::new(path, "invalid diagnostic pattern path");
                };
                node = next;
            }
            let Some(binder) = reader.binder_at(node, binder_index) else {
                return ValueDecodeError::new(path, "invalid diagnostic binder index");
            };
            ValueDecodeError::new(path, format!("AmbiguousBinderReference: binder `{binder}` at {side:?} occurrence {occurrence}, path {children:?}, index {binder_index}. Conflicting reference at {related:?}"))
        },
        failure => ValueDecodeError::new(path, format!("rewrite family: {failure:?}")),
    })?;
    let mut normalized = value.clone();
    let RhoValue::Map(output) = &mut normalized else {
        return error(path, "expected rewrite map");
    };
    for (key, side) in [("left", RewriteSide::Left), ("right", RewriteSide::Right)] {
        let pattern = output
            .get_mut(key)
            .ok_or_else(|| ValueDecodeError::new(path, "missing rewrite pattern"))?;
        apply_pattern_plan(pattern, side, &plan, path)?;
    }
    let mut ordinary = context
        .iter()
        .zip(&decoded)
        .filter(|(_, (_, ty))| matches!(ty, DecodedRuleContext::Ordinary(_)))
        .map(|(entry, _)| entry.clone())
        .collect::<Vec<_>>();
    let premises = output
        .entry("premises".into())
        .or_insert_with(|| RhoValue::List(Vec::new()));
    let RhoValue::List(premises) = premises else {
        return error(path, "expected rewrite premises list");
    };
    ordinary
        .try_reserve(plan.families.len())
        .map_err(|_| ValueDecodeError::new(path, "rewrite-family context allocation failed"))?;
    premises
        .try_reserve(plan.families.len())
        .map_err(|_| ValueDecodeError::new(path, "rewrite-family premise allocation failed"))?;
    for family in &plan.families {
        let DecodedRuleContext::RewriteFamily { result, .. } = &decoded[family.context_index].1
        else {
            return error(path, "family edit identifies an ordinary context binding");
        };
        ordinary.push(RhoValue::List(vec![
            RhoValue::String("typed".into()),
            RhoValue::String(family.source.clone()),
            (*result).clone(),
        ]));
        premises.push(RhoValue::List(vec![
            RhoValue::String("~>".into()),
            RhoValue::String(family.source.clone()),
            RhoValue::String(family.target.clone()),
        ]));
    }
    output.insert("context".into(), RhoValue::List(ordinary));
    Ok(Some(normalized))
}

#[cfg(test)]
mod tests;
