//! Local precharges around the unchanged structural DDL projection.
//!
//! `RholangPreparationReservation` supplies paid action, ordered-roster and
//! suffix laws; `RequiredVecBindingReservation` supplies flat partial cleanup.
//! This is a local helper-shape census, not a second full source walk or DDL parser.
//! Four linked rosters need paid length inspection because their existing
//! producers have no constant-time length. The original producers remain the
//! sole constructors. Embedded process values retain their producer's own
//! cleanup credits. Units are logical records and owned text bytes, not RSS.

use super::*;

pub(super) fn parts(
    work: usize,
    records: usize,
    bytes: usize,
    reserve: &mut Reservation<'_>,
) -> Result<(), RholangAstLowerError> {
    mettail_runtime::reserve_binding_parts(work, records, bytes, &mut |w, u| reserve(w, u)).map_err(
        |error| match error {
            mettail_runtime::BindingFailure::Reservation(error) => error,
            mettail_runtime::BindingFailure::SizeOverflow => {
                RholangAstLowerError::PreparationSizeOverflow
            },
            _ => {
                unreachable!("reserve_binding_parts returns only reservation or arithmetic failure")
            },
        },
    )
}

fn add(left: usize, right: usize) -> Result<usize, RholangAstLowerError> {
    left.checked_add(right)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)
}
fn mul(left: usize, right: usize) -> Result<usize, RholangAstLowerError> {
    left.checked_mul(right)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)
}

/// Each temporary roster pays setup/terminal/release and each inserted borrowed
/// occurrence pays construction, transfer and flat disposal. No source term is
/// cloned by these rosters; their nesting inside a local helper is bounded.
pub(super) fn rosters(
    count: usize,
    slots: usize,
    reserve: &mut Reservation<'_>,
) -> Result<(), RholangAstLowerError> {
    parts(add(mul(count, 3)?, mul(slots, 3)?)?, add(count, slots)?, 0, reserve)
}

fn linked_len<'a, T>(
    mut cursor: &'a T,
    mut next: impl FnMut(&'a T) -> Option<&'a T>,
    reserve: &mut Reservation<'_>,
) -> Result<usize, RholangAstLowerError> {
    let mut count = 0;
    loop {
        parts(2, 0, 0, reserve)?;
        count = add(count, 1)?;
        match next(cursor) {
            Some(tail) => cursor = tail,
            None => return Ok(count),
        }
    }
}

pub(super) fn expansion(
    task: &Task<'_>,
    reserve: &mut Reservation<'_>,
) -> Result<(), RholangAstLowerError> {
    // Pay the borrowed discriminant/length selection before inspection.
    parts(1, 0, 0, reserve)?;
    let (count, slots) = match task {
        Task::Text(_) | Task::QuotedText(_) | Task::FinishNode { .. } => {
            return parts(3, 1, 0, reserve);
        },
        Task::Process(_) => return parts(6, 2, 0, reserve),
        Task::Node { children, .. } => {
            // Finish task, reverse consuming iteration and pending occurrences.
            return rosters(1, add(children.len(), 1)?, reserve);
        },
        Task::Module { imports, items, .. } => {
            let imports = match imports {
                Some(DdlImports::DdlImportsNonEmpty(_, tail)) => add(tail.len(), 1)?,
                None => 0,
            };
            (
                add(3, add(items.len(), imports)?)?,
                add(3, add(mul(items.len(), 2)?, mul(imports, 3)?)?)?,
            )
        },
        Task::Theory { parameters, .. } => (2, add(parameters.len(), 3)?),
        Task::Param(_) | Task::Replacement(_) | Task::Freshness(_) | Task::Premise(_) => (1, 2),
        Task::Path(path) => (
            1,
            match path {
                DdlPath::DdlPathQualified(..) => 2,
                _ => 1,
            },
        ),
        Task::CatDecl(_) | Task::Sort(_) => (1, 1),
        Task::Export(export) => (
            2,
            match export {
                DdlExport::DdlExportDirect(_) => 2,
                _ => 3,
            },
        ),
        Task::TermRule(DdlTermRule::DdlTerm(_, bindings, syntax, _)) => {
            (3, add(add(bindings.len(), syntax.len())?, 4)?)
        },
        Task::Binding(binding) => (
            1,
            match binding {
                DdlBinding::DdlBindingPlain(..) => 2,
                _ => 4,
            },
        ),
        Task::SyntaxItem(item) => (
            1,
            match item {
                DdlSyntaxItem::DdlSyntaxProjection(..) => 2,
                _ => 1,
            },
        ),
        Task::Equation(equation) => {
            let len = match equation {
                DdlEquation::DdlEquationDirect(..) => 0,
                DdlEquation::DdlEquationConditional(freshness, ..) => linked_len(
                    freshness.as_ref(),
                    |value| match value {
                        DdlFreshnesses::DdlFreshnessMore(_, tail) => Some(tail.as_ref()),
                        _ => None,
                    },
                    reserve,
                )?,
            };
            (2, add(len, 3)?)
        },
        Task::Rewrite(rewrite) => {
            let len = match rewrite {
                DdlRewrite::DdlRewriteDirect(..) => 0,
                DdlRewrite::DdlRewriteConditional(_, premises, ..) => linked_len(
                    premises.as_ref(),
                    |value| match value {
                        DdlPremises::DdlPremiseMore(_, tail) => Some(tail.as_ref()),
                        _ => None,
                    },
                    reserve,
                )?,
            };
            (2, add(len, 4)?)
        },
        Task::TheoryExpr(expression) => theory(expression)?,
        Task::RuleAst(ast) => match ast {
            DdlRuleAst::DdlRuleAstSubst(..) | DdlRuleAst::DdlRuleAstAbs(..) => (1, 2),
            DdlRuleAst::DdlRuleAstSExp(_, arguments) => (2, add(arguments.len(), 2)?),
            DdlRuleAst::DdlRuleAstCollectionEmpty => (2, 1),
            DdlRuleAst::DdlRuleAstCollection(items) => {
                let len = linked_len(
                    items.as_ref(),
                    |value| match value {
                        DdlRuleAstItems::DdlRuleAstItemMore(_, tail) => Some(tail.as_ref()),
                        _ => None,
                    },
                    reserve,
                )?;
                (2, add(len, 1)?)
            },
            DdlRuleAst::DdlRuleAstCollectionRemainder(_, tail) => {
                let len = linked_len(
                    tail.as_ref(),
                    |value| match value {
                        DdlRuleAstRemainderTail::DdlRuleAstTailMore(_, rest) => Some(rest.as_ref()),
                        _ => None,
                    },
                    reserve,
                )? - 1;
                // Original rest roster, combined first/rest/remainder roster,
                // remainder's one child, and collection's sequence child.
                (4, add(mul(len, 2)?, 4)?)
            },
            DdlRuleAst::DdlRuleAstRemainderOnly(_) | DdlRuleAst::DdlRuleAstVar(_) => (1, 1),
        },
    };
    rosters(count, slots, reserve)?;
    // The structural expansion publishes one pending task after its helpers.
    parts(3, 1, 0, reserve)
}

fn theory(expression: &DdlTheoryExpr) -> Result<(usize, usize), RholangAstLowerError> {
    use DdlTheoryExpr::*;
    Ok(match expression {
        DdlTheoryDiff(..) | DdlTheoryJoin(..) | DdlTheoryMeet(..) => (1, 2),
        DdlTheoryTypes(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryExports(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryReplacements(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryTerms(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryEquations(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryRewrites(_, entries) => (3, add(entries.len(), 3)?),
        DdlTheoryData(..) => (2, 3),
        DdlTheoryEmpty => (1, 0),
        DdlTheoryFree(_) => (1, 1),
        DdlTheoryLet(..) => (1, 3),
        DdlTheoryBraceGroup(_) | DdlTheoryParenGroup(_) => (0, 0),
        DdlTheoryApply(_, arguments) => (2, add(arguments.len(), 2)?),
        DdlTheoryRef(_) => (2, 2),
        DdlTheoryTypesImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryExportsImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryReplacementsImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryTermsImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryEquationsImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryRewritesImplicit(entries) => (4, add(entries.len(), 3)?),
        DdlTheoryDataImplicit(_) => (3, 3),
    })
}

pub(super) fn text(
    bytes: usize,
    quoted: bool,
    reserve: &mut Reservation<'_>,
) -> Result<(), RholangAstLowerError> {
    // Decoder uses one forward scalar scan, at most two pushes per escape,
    // and never expands beyond captured UTF-8 bytes. Its finite diagnostic
    // allocation is included even on malformed framing/escape paths.
    let work = add(12, mul(bytes, if quoted { 4 } else { 1 })?)?;
    parts(work, 4, add(bytes, if quoted { 64 } else { 0 })?, reserve)
}

pub(super) fn node(
    children: usize,
    tag_bytes: usize,
    reserve: &mut Reservation<'_>,
) -> Result<(), RholangAstLowerError> {
    let width = add(children, 1)?;
    std::alloc::Layout::array::<Par>(width)
        .map_err(|_| RholangAstLowerError::PreparationSizeOverflow)?;
    // split_off copies the ordered suffix; insert may move it to grow and
    // shifts it once for the tag. Flat list construction/drop is local;
    // children retain their previously established independent root credits.
    rosters(2, add(children, width)?, reserve)?;
    parts(add(12, mul(children, 3)?)?, 4, 0, reserve)?;
    text(tag_bytes, false, reserve)
}
