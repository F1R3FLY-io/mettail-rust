//! Bounded structural paths to maximal installed reflected terms in a subject.
//!
//! A path indexes the flattened *direct `Par` children* of each `Par`, starting
//! at zero. The field order is sends (channel, data), receives (each bind's
//! patterns, source; body, condition), news (body, injections sorted by key),
//! exprs (operand order, map entries key then value), matches (target, each
//! case's pattern, source, guard), bundles (body), connectives (operands), and
//! conditionals (condition, true, false). Missing optional fields consume no
//! index. The path is structural; it grants no installed-language authority.

use std::fmt;

use mettail_rholang_codegen::{parse_reflected_tag, DynamicReflectionError, ReflectedCodecBudget};
use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::{Expr, Par};
use prost::Message;

const INSTALLED_FINGERPRINT_PREFIX: &str = "mettail-grammar-core-v1:";
// Logical retained slots, independent of host pointer width or allocator.
const CHILD_SLOT_BYTES: usize = 8;
const MAP_KEY_SLOT_BYTES: usize = 8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ScanError {
    Budget(DynamicReflectionError),
    AllocationFailed,
    PathOverflow,
    /// Nonempty entry tries carry encoded key `Par`s that cannot be borrowed;
    /// their iterative decoder has no budgeted materialization bound. Zipper
    /// cursors likewise contain encoded segments. Refuse rather than miss one.
    OpaquePathMap,
    /// An installed reflected list is mixed with sibling process/expressions,
    /// so there is no borrowed `Par` node that a binding path can designate.
    CompositeReflectedRoot,
    ReificationDepthExceeded,
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Budget(error) => write!(f, "subject occurrence scan: {error}"),
            Self::AllocationFailed => f.write_str("subject occurrence scan: allocation failed"),
            Self::PathOverflow => f.write_str("subject occurrence scan: child path overflow"),
            Self::OpaquePathMap => {
                f.write_str("subject occurrence scan: PathMap or zipper has opaque entries")
            },
            Self::CompositeReflectedRoot => {
                f.write_str("subject occurrence scan: reflected FLT is embedded in a composite Par")
            },
            Self::ReificationDepthExceeded => {
                f.write_str("host configuration exceeds checked reification depth")
            },
        }
    }
}

impl From<DynamicReflectionError> for ScanError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Budget(error)
    }
}

/// An outermost syntactic installed reflected root. `fingerprint` only
/// identifies a candidate; the selected owner's adapter validates the term.
pub(crate) struct SubjectOccurrence<'a> {
    pub(crate) path: Vec<u32>,
    pub(crate) term: &'a Par,
    pub(crate) fingerprint: String,
}

/// A reflected guest occupying one exact expression slot of the submitted
/// top-level `Par`. Unlike a v2 child path, this locator names the `Expr`
/// itself, including when ordinary host processes are parallel siblings.
pub(crate) struct TopLevelExprOccurrence<'a> {
    pub(crate) index: usize,
    pub(crate) expr: &'a Expr,
    pub(crate) fingerprint: String,
}

/// Discover the complete top-level product subset. Reflected top-level
/// expressions are retained as guest candidates; every other child is walked
/// with the ordinary fail-closed scanner, so a nested or transported FLT is
/// never silently omitted from the owner roster.
pub(crate) fn scan_top_level_reflected_exprs<'a, C: FnMut() -> bool>(
    subject: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<TopLevelExprOccurrence<'a>>, ScanError> {
    budget.charge(1, 0)?;
    charge_clone_footprint(subject, budget)?;
    let mut found = Vec::new();
    for (index, expr) in subject.exprs.iter().enumerate() {
        budget.charge(1, CHILD_SLOT_BYTES)?;
        if let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() {
            if let Some(fingerprint) = reflected_list_fingerprint(&list.ps, budget)? {
                found
                    .try_reserve(1)
                    .map_err(|_| ScanError::AllocationFailed)?;
                found.push(TopLevelExprOccurrence { index, expr, fingerprint });
            }
        }
    }
    let mut pending = direct_children_except_top_level_reflected(subject, budget)?;
    while let Some(term) = pending.pop() {
        budget.charge(1, 0)?;
        charge_clone_footprint(term, budget)?;
        if installed_root_fingerprint(term, budget)?.is_some() {
            return Err(ScanError::CompositeReflectedRoot);
        }
        let children = direct_children(term, budget)?;
        pending
            .try_reserve(children.len())
            .map_err(|_| ScanError::AllocationFailed)?;
        pending.extend(children);
    }
    // The eventual iterative clone copies the reflected syntax too. Walk it
    // separately for resource preflight, without treating nested constructor
    // tags as independent owner claims inside the maximal guest root.
    for occurrence in &found {
        let Some(ExprInstance::EListBody(list)) = occurrence.expr.expr_instance.as_ref() else {
            unreachable!("top-level occurrence was discovered as an exact list");
        };
        let mut guest_nodes = Vec::new();
        guest_nodes
            .try_reserve(list.ps.len())
            .map_err(|_| ScanError::AllocationFailed)?;
        guest_nodes.extend(list.ps.iter());
        while let Some(term) = guest_nodes.pop() {
            charge_clone_footprint(term, budget)?;
            let children = direct_children(term, budget)?;
            guest_nodes
                .try_reserve(children.len())
                .map_err(|_| ScanError::AllocationFailed)?;
            guest_nodes.extend(children);
        }
    }
    Ok(found)
}

fn charge_clone_footprint<C: FnMut() -> bool>(
    term: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), ScanError> {
    // The composite scanner is a preflight for one iterative `Par` clone.
    // Charge fixed storage and flat scalar bytes before that allocation.
    budget.charge(1, std::mem::size_of::<Par>())?;
    for expr in &term.exprs {
        let bytes = match expr.expr_instance.as_ref() {
            Some(ExprInstance::GString(value) | ExprInstance::GUri(value)) => value.len(),
            Some(ExprInstance::GByteArray(value) | ExprInstance::GBigInt(value)) => value.len(),
            Some(ExprInstance::GBigRat(value)) => value
                .numerator
                .len()
                .saturating_add(value.denominator.len()),
            Some(ExprInstance::GFixedPoint(value)) => value.unscaled.len(),
            _ => 0,
        };
        budget.charge(1, std::mem::size_of::<Expr>().saturating_add(bytes))?;
    }
    for unforgeable in &term.unforgeables {
        let bytes = match unforgeable.unf_instance.as_ref() {
            Some(UnfInstance::GPrivateBody(value)) => value.id.len(),
            Some(UnfInstance::GDeployIdBody(value)) => value.sig.len(),
            Some(UnfInstance::GDeployerIdBody(value)) => value.public_key.len(),
            _ => 0,
        };
        budget.charge(1, std::mem::size_of_val(unforgeable).saturating_add(bytes))?;
    }
    Ok(())
}

/// Resource-check one borrowed host value before canonical reification. The
/// current host reifier uses protobuf encoding for channel sort keys, so its
/// recursion is bounded here before it can see a hostile deep channel. An
/// installed FLT in the host side is never silently assigned to the retained
/// guest slot.
pub(crate) fn validate_reifiable_host_par<C: FnMut() -> bool>(
    root: &Par,
    max_depth: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), ScanError> {
    let mut pending = vec![(0usize, root)];
    while let Some((depth, term)) = pending.pop() {
        if depth > max_depth {
            return Err(ScanError::ReificationDepthExceeded);
        }
        charge_clone_footprint(term, budget)?;
        if installed_root_fingerprint(term, budget)?.is_some() {
            return Err(ScanError::CompositeReflectedRoot);
        }
        let children = direct_children(term, budget)?;
        pending
            .try_reserve(children.len())
            .map_err(|_| ScanError::AllocationFailed)?;
        let next_depth = depth.checked_add(1).ok_or(ScanError::PathOverflow)?;
        pending.extend(children.into_iter().map(|child| (next_depth, child)));
    }
    Ok(())
}

/// Enumerate installed reflected roots in strictly increasing path order.
/// Descendants of a recognized root are its guest syntax, not separate owner
/// claims. Native literal roots have no reflected tag and require an explicit
/// v2 binding plus adapter validation at the caller.
pub(crate) fn scan_installed_occurrences<'a, C: FnMut() -> bool>(
    subject: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<SubjectOccurrence<'a>>, ScanError> {
    let mut pending = vec![(Vec::<u32>::new(), subject)];
    let mut found = Vec::new();
    while let Some((path, term)) = pending.pop() {
        budget.charge(1, 0)?;
        if let Some(fingerprint) = installed_root_fingerprint(term, budget)? {
            budget.charge(1, path.len().checked_mul(4).ok_or(ScanError::PathOverflow)?)?;
            found
                .try_reserve(1)
                .map_err(|_| ScanError::AllocationFailed)?;
            found.push(SubjectOccurrence { path, term, fingerprint });
            continue;
        }
        let children = direct_children(term, budget)?;
        pending
            .try_reserve(children.len())
            .map_err(|_| ScanError::AllocationFailed)?;
        for (index, child) in children.into_iter().enumerate().rev() {
            let index = u32::try_from(index).map_err(|_| ScanError::PathOverflow)?;
            let bytes = path
                .len()
                .checked_add(1)
                .and_then(|len| len.checked_mul(4))
                .ok_or(ScanError::PathOverflow)?;
            budget.charge(1, bytes)?;
            let mut child_path = Vec::new();
            child_path
                .try_reserve_exact(path.len() + 1)
                .map_err(|_| ScanError::AllocationFailed)?;
            child_path.extend_from_slice(&path);
            child_path.push(index);
            pending.push((child_path, child));
        }
    }
    debug_assert!(found.windows(2).all(|pair| pair[0].path < pair[1].path));
    Ok(found)
}

/// Resolve an explicit binding path using the same canonical child order.
/// This also permits a bound native literal, which has no reflected tag for
/// [`scan_installed_occurrences`] to discover on its own.
pub(crate) fn term_at_path<'a, C: FnMut() -> bool>(
    subject: &'a Par,
    path: &[u32],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<&'a Par>, ScanError> {
    let mut term = subject;
    budget.charge(1, 0)?;
    for &index in path {
        let children = direct_children(term, budget)?;
        let index = usize::try_from(index).map_err(|_| ScanError::PathOverflow)?;
        let Some(child) = children.get(index) else {
            return Ok(None);
        };
        term = child;
        budget.charge(1, 0)?;
    }
    Ok(Some(term))
}

fn installed_root_fingerprint<C: FnMut() -> bool>(
    term: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<String>, ScanError> {
    let Some(items) = crate::language_install::exact_list(term) else {
        return Ok(None);
    };
    reflected_list_fingerprint(items, budget)
}

fn reflected_list_fingerprint<C: FnMut() -> bool>(
    items: &[Par],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<String>, ScanError> {
    let Some(head) = items.first() else {
        return Ok(None);
    };
    if !head.sends.is_empty()
        || !head.receives.is_empty()
        || !head.news.is_empty()
        || !head.exprs.is_empty()
        || !head.matches.is_empty()
        || !head.bundles.is_empty()
        || !head.connectives.is_empty()
        || !head.conditionals.is_empty()
    {
        return Ok(None);
    }
    let [unforgeable] = head.unforgeables.as_slice() else {
        return Ok(None);
    };
    let Some(UnfInstance::GPrivateBody(private)) = unforgeable.unf_instance.as_ref() else {
        return Ok(None);
    };
    budget.charge(private.id.len(), private.id.len())?;
    let Ok(tag) = String::decode(private.id.as_slice()) else {
        return Ok(None);
    };
    let Some((fingerprint, _label)) = parse_reflected_tag(&tag) else {
        return Ok(None);
    };
    let Some(hex) = fingerprint.strip_prefix(INSTALLED_FINGERPRINT_PREFIX) else {
        return Ok(None);
    };
    if hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Ok(None);
    }
    budget.charge(fingerprint.len(), fingerprint.len())?;
    Ok(Some(fingerprint.to_owned()))
}

fn push_child<'a, C: FnMut() -> bool>(
    children: &mut Vec<&'a Par>,
    child: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), ScanError> {
    budget.charge(1, CHILD_SLOT_BYTES)?;
    children
        .try_reserve(1)
        .map_err(|_| ScanError::AllocationFailed)?;
    children.push(child);
    Ok(())
}

fn direct_children<'a, C: FnMut() -> bool>(
    term: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<&'a Par>, ScanError> {
    direct_children_mode(term, budget, false)
}

fn direct_children_except_top_level_reflected<'a, C: FnMut() -> bool>(
    term: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<&'a Par>, ScanError> {
    direct_children_mode(term, budget, true)
}

fn direct_children_mode<'a, C: FnMut() -> bool>(
    term: &'a Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
    skip_reflected_exprs: bool,
) -> Result<Vec<&'a Par>, ScanError> {
    // A `Par` may contain a reflected EList expression alongside other sends
    // or expressions. `exact_list(term)` then cannot identify the FLT, and the
    // list head is only a GPrivate child: ordinary child traversal would miss
    // this installed occurrence entirely. No borrowed `Par` names the list
    // expression alone, so both scanning and explicit path lookup refuse it.
    if crate::language_install::exact_list(term).is_none() {
        for expr in &term.exprs {
            if let Some(ExprInstance::EListBody(list)) = expr.expr_instance.as_ref() {
                if !skip_reflected_exprs && reflected_list_fingerprint(&list.ps, budget)?.is_some()
                {
                    return Err(ScanError::CompositeReflectedRoot);
                }
            }
        }
    }
    let mut children = Vec::new();
    macro_rules! child {
        ($value:expr) => {
            if let Some(value) = ($value).as_ref() {
                push_child(&mut children, value, budget)?;
            }
        };
    }
    for send in &term.sends {
        child!(send.chan);
        for item in &send.data {
            push_child(&mut children, item, budget)?;
        }
    }
    for receive in &term.receives {
        for bind in &receive.binds {
            for pattern in &bind.patterns {
                push_child(&mut children, pattern, budget)?;
            }
            child!(bind.source);
        }
        child!(receive.body);
        child!(receive.condition);
    }
    for new in &term.news {
        child!(new.p);
        let key_bytes = new
            .injections
            .len()
            .checked_mul(MAP_KEY_SLOT_BYTES)
            .ok_or(ScanError::PathOverflow)?;
        budget.charge(new.injections.len(), key_bytes)?;
        let mut keys = Vec::new();
        keys.try_reserve(new.injections.len())
            .map_err(|_| ScanError::AllocationFailed)?;
        keys.extend(new.injections.keys());
        keys.sort_unstable();
        for key in keys {
            push_child(&mut children, &new.injections[key], budget)?;
        }
    }
    for expr in &term.exprs {
        use ExprInstance::*;
        match expr.expr_instance.as_ref() {
            Some(ENotBody(op)) => child!(op.p),
            Some(ENegBody(op)) => child!(op.p),
            Some(EMultBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EDivBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EPlusBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EMinusBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(ELtBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(ELteBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EGtBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EGteBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EEqBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(ENeqBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EAndBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EOrBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EModBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EPercentPercentBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EPlusPlusBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EMinusMinusBody(op)) => {
                child!(op.p1);
                child!(op.p2);
            },
            Some(EMatchesBody(op)) => {
                child!(op.target);
                child!(op.pattern);
            },
            Some(EListBody(list)) => {
                if skip_reflected_exprs && reflected_list_fingerprint(&list.ps, budget)?.is_some() {
                    continue;
                }
                for item in &list.ps {
                    push_child(&mut children, item, budget)?;
                }
            },
            Some(ETupleBody(tuple)) => {
                for item in &tuple.ps {
                    push_child(&mut children, item, budget)?;
                }
            },
            Some(ESetBody(set)) => {
                for item in &set.ps {
                    push_child(&mut children, item, budget)?;
                }
            },
            Some(EMapBody(map)) => {
                for pair in &map.kvs {
                    child!(pair.key);
                    child!(pair.value);
                }
            },
            Some(EMethodBody(method)) => {
                child!(method.target);
                for argument in &method.arguments {
                    push_child(&mut children, argument, budget)?;
                }
            },
            Some(EPathmapBody(pathmap)) if pathmap.is_empty() => {},
            Some(EPathmapBody(_) | EZipperBody(_)) => return Err(ScanError::OpaquePathMap),
            Some(
                GInt(_) | GBool(_) | GString(_) | GUri(_) | GByteArray(_) | GDouble(_) | GBigInt(_)
                | GBigRat(_) | GFixedPoint(_) | EVarBody(_),
            )
            | None => {},
        }
    }
    for matched in &term.matches {
        child!(matched.target);
        for case in &matched.cases {
            child!(case.pattern);
            child!(case.source);
            child!(case.guard);
        }
    }
    for bundle in &term.bundles {
        child!(bundle.body);
    }
    for connective in &term.connectives {
        match connective.connective_instance.as_ref() {
            Some(ConnectiveInstance::ConnAndBody(body) | ConnectiveInstance::ConnOrBody(body)) => {
                for item in &body.ps {
                    push_child(&mut children, item, budget)?;
                }
            },
            Some(ConnectiveInstance::ConnNotBody(body)) => push_child(&mut children, body, budget)?,
            Some(
                ConnectiveInstance::VarRefBody(_)
                | ConnectiveInstance::ConnBool(_)
                | ConnectiveInstance::ConnInt(_)
                | ConnectiveInstance::ConnString(_)
                | ConnectiveInstance::ConnUri(_)
                | ConnectiveInstance::ConnByteArray(_),
            )
            | None => {},
        }
    }
    for conditional in &term.conditionals {
        child!(conditional.condition);
        child!(conditional.if_true);
        child!(conditional.if_false);
    }
    Ok(children)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_rholang_codegen::reflected_tag_string;
    use models::rhoapi::{EPathMap, Expr, New, Send};
    use models::rust::rholang::implicits::GPrivateBuilder;
    use models::rust::utils::new_gint_par;

    fn fingerprint() -> String {
        format!("{INSTALLED_FINGERPRINT_PREFIX}{}", "a".repeat(64))
    }

    fn reflected(label: &str, children: Vec<Par>) -> Par {
        let tag = GPrivateBuilder::new_par_from_string(reflected_tag_string(&fingerprint(), label));
        let mut parts = vec![tag];
        parts.extend(children);
        crate::language_install::wire_list(parts)
    }

    fn scan(subject: &Par) -> Result<Vec<SubjectOccurrence<'_>>, ScanError> {
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 8_000_000, &mut cancelled);
        scan_installed_occurrences(subject, &mut budget)
    }

    #[test]
    fn finds_maximal_roots_in_lexicographic_path_order() {
        let nested = crate::language_install::wire_list(vec![reflected("B", vec![])]);
        let subject = crate::language_install::wire_list(vec![
            reflected("A", vec![]),
            nested,
            reflected("C", vec![]),
        ]);
        let found = scan(&subject).expect("bounded scan");
        let paths: Vec<_> = found.iter().map(|item| item.path.as_slice()).collect();
        assert_eq!(paths, [&[0][..], &[1, 0][..], &[2][..]]);
        assert!(found.iter().all(|item| item.fingerprint == fingerprint()));

        let outer = reflected("Outer", vec![reflected("Inner", vec![])]);
        let found = scan(&outer).expect("outer root");
        assert_eq!(found.len(), 1);
        assert!(found[0].path.is_empty());
        assert!(std::ptr::eq(found[0].term, &outer));
    }

    #[test]
    fn new_injection_paths_sort_keys_before_indexing() {
        let mut new = New::default();
        new.p = Some(Par::default());
        new.injections.insert("z".into(), reflected("Z", vec![]));
        new.injections.insert("a".into(), reflected("A", vec![]));
        let mut subject = Par::default();
        subject.news = vec![new];
        let found = scan(&subject).expect("bounded scan");
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].path, [1]);
        assert_eq!(found[1].path, [2]);
    }

    #[test]
    fn explicit_path_can_select_native_literal_child() {
        let subject = crate::language_install::wire_list(vec![
            new_gint_par(7, Vec::new(), false),
            reflected("Tagged", vec![]),
        ]);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 10_000, &mut cancelled);
        assert_eq!(
            term_at_path(&subject, &[0], &mut budget).expect("bounded lookup"),
            Some(&new_gint_par(7, Vec::new(), false)),
        );
        assert_eq!(term_at_path(&subject, &[2], &mut budget).expect("bounded lookup"), None,);
    }

    #[test]
    fn scans_deep_lists_without_recursive_calls() {
        let mut subject = reflected("Leaf", vec![]);
        for _ in 0..512 {
            subject = crate::language_install::wire_list(vec![subject]);
        }
        let found = scan(&subject).expect("iterative scan");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].path.len(), 512);
        assert!(found[0].path.iter().all(|index| *index == 0));
    }

    #[test]
    fn empty_pathmap_has_no_hidden_occurrences() {
        let mut subject = Par::default();
        subject.exprs = vec![Expr {
            expr_instance: Some(ExprInstance::EPathmapBody(EPathMap::default())),
        }];
        assert!(scan(&subject)
            .expect("empty trie has no encoded keys")
            .is_empty());
    }

    #[test]
    fn nonempty_pathmap_refuses_instead_of_hiding_an_occurrence() {
        let mut pathmap = EPathMap::default();
        pathmap.insert_entry(reflected("Hidden", vec![]));
        let mut subject = Par::default();
        subject.exprs = vec![Expr {
            expr_instance: Some(ExprInstance::EPathmapBody(pathmap)),
        }];
        assert!(matches!(scan(&subject), Err(ScanError::OpaquePathMap)));
    }

    #[test]
    fn composite_reflected_expression_refuses_v1_scan_and_v2_path_lookup() {
        let mut subject = reflected("Embedded", vec![]);
        subject
            .exprs
            .push(new_gint_par(7, Vec::new(), false).exprs[0].clone());
        assert!(matches!(scan(&subject), Err(ScanError::CompositeReflectedRoot)));

        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 10_000, &mut cancelled);
        assert!(matches!(
            term_at_path(&subject, &[0], &mut budget),
            Err(ScanError::CompositeReflectedRoot)
        ));
    }

    #[test]
    fn typed_top_level_scan_names_exact_expression_and_rejects_nested_guest() {
        let mut subject = reflected("Embedded", vec![]);
        subject.sends.push(Send::default());
        subject
            .exprs
            .insert(0, new_gint_par(7, Vec::new(), false).exprs.remove(0));
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancelled);
        let found = scan_top_level_reflected_exprs(&subject, &mut budget)
            .expect("bounded top-level product scan");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].index, 1);
        assert!(std::ptr::eq(found[0].expr, &subject.exprs[1]));
        assert_eq!(found[0].fingerprint, fingerprint());

        let mut nested = Par::default();
        nested.news.push(New {
            p: Some(reflected("Hidden", vec![])),
            ..New::default()
        });
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 1_000_000, &mut cancelled);
        assert!(matches!(
            scan_top_level_reflected_exprs(&nested, &mut budget),
            Err(ScanError::CompositeReflectedRoot)
        ));
    }

    #[test]
    fn exhausted_work_budget_refuses_before_visiting_root() {
        let subject = new_gint_par(1, Vec::new(), false);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 0, 100, &mut cancelled);
        assert!(matches!(
            scan_installed_occurrences(&subject, &mut budget),
            Err(ScanError::Budget(DynamicReflectionError::WorkLimit))
        ));
    }

    #[test]
    fn child_and_path_slots_use_a_fixed_budget_schedule() {
        let subject = crate::language_install::wire_list(vec![new_gint_par(1, Vec::new(), false)]);
        for (limit, bytes, expected) in [
            (4, 12, Ok(0)),
            (3, 12, Err(DynamicReflectionError::WorkLimit)),
            (4, 11, Err(DynamicReflectionError::PayloadByteLimit)),
        ] {
            let mut work = 0;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, limit, bytes, &mut cancelled);
            let outcome = scan_installed_occurrences(&subject, &mut budget)
                .map(|found| found.len())
                .map_err(|error| match error {
                    ScanError::Budget(error) => error,
                    other => panic!("unexpected scan error: {other}"),
                });
            assert_eq!(outcome, expected);
        }
    }
}
