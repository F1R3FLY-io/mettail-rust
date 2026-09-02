//! Structural foreign-language templates captured by the host parser.
//!
//! An FLT is not a string interpolation. The capture records an ordered sequence
//! of guest-text spans and typed hole terminals. Guest lexers consume each text
//! span independently and receive holes as synthetic identifier terminals, so a
//! hole cannot join tokens, close a delimiter, or inject guest source.

use crate::{get_or_create_var, OrdVar, Var};
use moniker::BoundTerm;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Stable telescope index assigned at the first occurrence of a hole name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltHoleId(pub u32);

/// Half-open byte range relative to the start of the captured guest body.
///
/// Ranges are provenance only. Runtime guest parsing projects them away and
/// consumes the structural [`FltTemplatePiece`] payloads.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltSourceRange {
    pub start: usize,
    pub end: usize,
}

impl FltSourceRange {
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn len(self) -> Option<usize> {
        self.end.checked_sub(self.start)
    }

    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// One declared FLT hole. Repeated occurrences share the same [`FltHoleId`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltHole {
    pub id: FltHoleId,
    pub name: String,
    pub category: Option<String>,
    /// Range of the first occurrence. Later occurrences carry their own range
    /// on [`FltTemplatePiece::Hole`].
    pub first_occurrence: FltSourceRange,
}

/// One element of the structural template, in source order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FltTemplatePiece {
    /// Exact guest source between holes. It is lexed in isolation, ensuring no
    /// token can span a hole boundary.
    Text { text: String, range: FltSourceRange },
    /// A typed lattice terminal referring to the template telescope.
    Hole { id: FltHoleId, range: FltSourceRange },
}

impl FltTemplatePiece {
    pub const fn range(&self) -> FltSourceRange {
        match self {
            Self::Text { range, .. } | Self::Hole { range, .. } => *range,
        }
    }
}

/// Exact finite extent of one captured template. The values are recomputed by
/// validation and compared with trusted runtime limits before guest parsing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltTemplateBounds {
    pub source_bytes: usize,
    pub body_bytes: usize,
    pub piece_count: usize,
    pub hole_declarations: usize,
    pub hole_occurrences: usize,
}

/// The variance selected by the Rholang use site. Guest text cannot choose it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FltPolarity {
    PositiveConstruction,
    NegativePattern,
}

/// Immutable, context-indexed view staged for the installed-language port.
#[derive(Clone, Copy, Debug)]
pub struct ScopedFltTemplate<'a> {
    pub selector: &'a OrdVar,
    pub selector_name: &'a str,
    pub category: &'a str,
    pub polarity: FltPolarity,
    pub telescope: &'a [FltHole],
    pub pieces: &'a [FltTemplatePiece],
    pub bounds: FltTemplateBounds,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FltTemplateError {
    EmptySelector,
    InvalidSelector(String),
    EmptyRootCategory,
    InvalidRootCategory(String),
    EmptyHoleName(FltHoleId),
    InvalidHoleName(String),
    InvalidHoleCategory(String),
    UnknownHole(FltHoleId),
    UnusedHole(FltHoleId),
    DuplicateHoleId(FltHoleId),
    ConflictingHoleDeclaration(String),
    NonCanonicalHoleOrder {
        expected: FltHoleId,
        found: FltHoleId,
    },
    WrongFirstOccurrenceRange {
        id: FltHoleId,
        expected: FltSourceRange,
        found: FltSourceRange,
    },
    InvalidPieceRange(FltSourceRange),
    EmptyTextPiece(FltSourceRange),
    NonContiguousPieceRange {
        expected: usize,
        found: usize,
    },
    PieceWidthMismatch {
        range: FltSourceRange,
        bytes: usize,
    },
    WrongBounds {
        expected: FltTemplateBounds,
        found: FltTemplateBounds,
    },
    ExtentOverflow,
    SourceMismatch,
}

impl fmt::Display for FltTemplateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySelector => formatter.write_str("FLT selector is empty"),
            Self::InvalidSelector(selector) => {
                write!(formatter, "FLT selector `{selector}` is not a Rholang identifier")
            },
            Self::EmptyRootCategory => formatter.write_str("FLT result category is empty"),
            Self::InvalidRootCategory(category) => write!(
                formatter,
                "FLT result category `{category}` is not a qualified identifier",
            ),
            Self::EmptyHoleName(id) => write!(formatter, "FLT hole {id:?} has an empty name"),
            Self::InvalidHoleName(name) => {
                write!(formatter, "FLT hole name `{name}` is not an identifier")
            },
            Self::InvalidHoleCategory(category) => write!(
                formatter,
                "FLT hole category `{category}` is not a qualified identifier",
            ),
            Self::UnknownHole(id) => write!(formatter, "FLT template refers to unknown hole {id:?}"),
            Self::UnusedHole(id) => write!(formatter, "FLT hole {id:?} has no occurrence"),
            Self::DuplicateHoleId(id) => write!(formatter, "FLT hole id {id:?} is duplicated"),
            Self::ConflictingHoleDeclaration(name) => {
                write!(formatter, "FLT hole `{name}` has conflicting declarations")
            },
            Self::NonCanonicalHoleOrder { expected, found } => write!(
                formatter,
                "FLT hole ids are not first-occurrence ordered: expected {expected:?}, found {found:?}",
            ),
            Self::WrongFirstOccurrenceRange { id, expected, found } => write!(
                formatter,
                "FLT hole {id:?} has first range {found:?}, expected {expected:?}",
            ),
            Self::InvalidPieceRange(range) => {
                write!(formatter, "FLT piece has invalid source range {range:?}")
            },
            Self::EmptyTextPiece(range) => {
                write!(formatter, "FLT text piece at {range:?} is empty")
            },
            Self::NonContiguousPieceRange { expected, found } => write!(
                formatter,
                "FLT piece range starts at {found}, expected contiguous byte {expected}",
            ),
            Self::PieceWidthMismatch { range, bytes } => write!(
                formatter,
                "FLT piece range {range:?} does not have payload width {bytes}",
            ),
            Self::WrongBounds { expected, found } => write!(
                formatter,
                "FLT extent {found:?} does not match structural extent {expected:?}",
            ),
            Self::ExtentOverflow => formatter.write_str("FLT structural extent overflowed usize"),
            Self::SourceMismatch => formatter.write_str(
                "FLT structural pieces do not reconstruct the captured guest source",
            ),
        }
    }
}

impl std::error::Error for FltTemplateError {}

/// Native capture of a delimited FLT guest body.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltNode {
    /// The lexical Rholang selector. This is closed/opened with the surrounding
    /// receive/new scope, so the surface tag denotes the installed handle bound
    /// at run time rather than an ambient global registry name.
    pub selector: OrdVar,
    /// Original lexical selector spelling. This is diagnostic syntax, never a
    /// registry-global name or an authority token.
    pub selector_name: String,
    /// Explicit result category selected before the guest body delimiter.
    pub category: String,
    pub open_src: String,
    /// Retained only for exact diagnostics and display. Parsing uses `pieces`.
    pub body_src: String,
    pub holes: Vec<FltHole>,
    pub pieces: Vec<FltTemplatePiece>,
    pub close_src: String,
    /// Exact finite structural extent, checked again by [`Self::validate`].
    pub bounds: FltTemplateBounds,
    /// Best available opener position retained for integration diagnostics.
    /// Piece ranges remain exact because they are body-relative.
    pub position: usize,
}

impl FltNode {
    /// Checked constructor for programmatically created, usually hole-free
    /// nodes. Parsed FLTs use [`Self::from_structural_parts`].
    pub fn new(
        selector_name: String,
        category: String,
        body_src: String,
        holes: Vec<FltHole>,
        position: usize,
    ) -> Result<Self, FltTemplateError> {
        let mut pieces = Vec::new();
        let mut cursor = 0usize;
        for hole in &holes {
            if hole.first_occurrence.start > cursor && hole.first_occurrence.start <= body_src.len()
            {
                pieces.push(FltTemplatePiece::Text {
                    text: body_src[cursor..hole.first_occurrence.start].to_string(),
                    range: FltSourceRange::new(cursor, hole.first_occurrence.start),
                });
            }
            pieces.push(FltTemplatePiece::Hole {
                id: hole.id,
                range: hole.first_occurrence,
            });
            cursor = hole.first_occurrence.end.min(body_src.len());
        }
        if cursor < body_src.len() {
            pieces.push(FltTemplatePiece::Text {
                text: body_src[cursor..].to_string(),
                range: FltSourceRange::new(cursor, body_src.len()),
            });
        }
        Self::from_structural_parts(
            selector_name,
            category,
            String::new(),
            body_src,
            holes,
            pieces,
            String::new(),
            position,
        )
    }

    pub fn from_structural_parts(
        selector_name: String,
        category: String,
        open_src: String,
        body_src: String,
        holes: Vec<FltHole>,
        pieces: Vec<FltTemplatePiece>,
        close_src: String,
        position: usize,
    ) -> Result<Self, FltTemplateError> {
        let selector = OrdVar(Var::Free(get_or_create_var(&selector_name)));
        let bounds = structural_bounds(&open_src, &body_src, &holes, &pieces, &close_src)?;
        let node = Self {
            selector,
            selector_name,
            category,
            open_src,
            body_src,
            holes,
            pieces,
            close_src,
            bounds,
            position,
        };
        node.validate()?;
        Ok(node)
    }

    /// Validate telescope identity, occurrence references, and exact-source
    /// reconstruction. The traversal is iterative and bounded by the node size.
    pub fn validate(&self) -> Result<(), FltTemplateError> {
        if self.selector_name.is_empty() {
            return Err(FltTemplateError::EmptySelector);
        }
        if !valid_identifier(&self.selector_name, false) {
            return Err(FltTemplateError::InvalidSelector(self.selector_name.clone()));
        }
        if self.category.is_empty() {
            return Err(FltTemplateError::EmptyRootCategory);
        }
        if !valid_identifier(&self.category, true) {
            return Err(FltTemplateError::InvalidRootCategory(self.category.clone()));
        }
        let mut by_id = BTreeMap::new();
        let mut by_name: BTreeMap<&str, (FltHoleId, &Option<String>)> = BTreeMap::new();
        for (index, hole) in self.holes.iter().enumerate() {
            let expected = FltHoleId(u32::try_from(index).unwrap_or(u32::MAX));
            if hole.id != expected {
                return Err(FltTemplateError::NonCanonicalHoleOrder { expected, found: hole.id });
            }
            if hole.name.is_empty() {
                return Err(FltTemplateError::EmptyHoleName(hole.id));
            }
            if !valid_identifier(&hole.name, false) {
                return Err(FltTemplateError::InvalidHoleName(hole.name.clone()));
            }
            if let Some(category) = &hole.category {
                if !valid_identifier(category, true) {
                    return Err(FltTemplateError::InvalidHoleCategory(category.clone()));
                }
            }
            if by_id.insert(hole.id, hole).is_some() {
                return Err(FltTemplateError::DuplicateHoleId(hole.id));
            }
            if let Some((prior_id, prior_category)) = by_name.get(hole.name.as_str()) {
                if *prior_id != hole.id || *prior_category != &hole.category {
                    return Err(FltTemplateError::ConflictingHoleDeclaration(hole.name.clone()));
                }
            } else {
                by_name.insert(hole.name.as_str(), (hole.id, &hole.category));
            }
        }

        let mut occurred = BTreeSet::new();
        let mut cursor = 0usize;
        for piece in &self.pieces {
            let range = piece.range();
            if range.end < range.start || range.end > self.body_src.len() {
                return Err(FltTemplateError::InvalidPieceRange(range));
            }
            if range.start != cursor {
                return Err(FltTemplateError::NonContiguousPieceRange {
                    expected: cursor,
                    found: range.start,
                });
            }
            match piece {
                FltTemplatePiece::Text { text, range } => {
                    if text.is_empty() {
                        return Err(FltTemplateError::EmptyTextPiece(*range));
                    }
                    if range.len() != Some(text.len()) {
                        return Err(FltTemplateError::PieceWidthMismatch {
                            range: *range,
                            bytes: text.len(),
                        });
                    }
                    if self.body_src.get(range.start..range.end) != Some(text.as_str()) {
                        return Err(FltTemplateError::SourceMismatch);
                    }
                },
                FltTemplatePiece::Hole { id, range } => {
                    let hole = by_id.get(id).ok_or(FltTemplateError::UnknownHole(*id))?;
                    if occurred.insert(*id) {
                        let expected =
                            FltHoleId(u32::try_from(occurred.len() - 1).unwrap_or(u32::MAX));
                        if *id != expected {
                            return Err(FltTemplateError::NonCanonicalHoleOrder {
                                expected,
                                found: *id,
                            });
                        }
                        if hole.first_occurrence != *range {
                            return Err(FltTemplateError::WrongFirstOccurrenceRange {
                                id: *id,
                                expected: *range,
                                found: hole.first_occurrence,
                            });
                        }
                    }
                    let mut syntax = String::with_capacity(
                        3 + hole.name.len()
                            + hole
                                .category
                                .as_ref()
                                .map_or(0, |category| 1 + category.len()),
                    );
                    syntax.push_str("${");
                    syntax.push_str(&hole.name);
                    if let Some(category) = &hole.category {
                        syntax.push(':');
                        syntax.push_str(category);
                    }
                    syntax.push('}');
                    if range.len() != Some(syntax.len()) {
                        return Err(FltTemplateError::PieceWidthMismatch {
                            range: *range,
                            bytes: syntax.len(),
                        });
                    }
                    if self.body_src.get(range.start..range.end) != Some(syntax.as_str()) {
                        return Err(FltTemplateError::SourceMismatch);
                    }
                },
            }
            cursor = range.end;
        }
        if cursor != self.body_src.len() {
            return Err(FltTemplateError::SourceMismatch);
        }
        if occurred.len() != self.holes.len() {
            let unused = self
                .holes
                .iter()
                .find(|hole| !occurred.contains(&hole.id))
                .expect("different cardinalities imply an unused declaration");
            return Err(FltTemplateError::UnusedHole(unused.id));
        }
        let expected = structural_bounds(
            &self.open_src,
            &self.body_src,
            &self.holes,
            &self.pieces,
            &self.close_src,
        )?;
        if self.bounds != expected {
            return Err(FltTemplateError::WrongBounds { expected, found: self.bounds });
        }
        Ok(())
    }

    pub fn hole(&self, id: FltHoleId) -> Option<&FltHole> {
        self.holes.get(id.0 as usize).filter(|hole| hole.id == id)
    }

    /// Attach host-selected variance without copying or mutating the parsed
    /// structural capture.
    pub fn stage(&self, polarity: FltPolarity) -> ScopedFltTemplate<'_> {
        ScopedFltTemplate {
            selector: &self.selector,
            selector_name: &self.selector_name,
            category: &self.category,
            polarity,
            telescope: &self.holes,
            pieces: &self.pieces,
            bounds: self.bounds,
        }
    }
}

fn structural_bounds(
    open_src: &str,
    body_src: &str,
    holes: &[FltHole],
    pieces: &[FltTemplatePiece],
    close_src: &str,
) -> Result<FltTemplateBounds, FltTemplateError> {
    let source_bytes = open_src
        .len()
        .checked_add(body_src.len())
        .and_then(|bytes| bytes.checked_add(close_src.len()))
        .ok_or(FltTemplateError::ExtentOverflow)?;
    let hole_occurrences = pieces
        .iter()
        .filter(|piece| matches!(piece, FltTemplatePiece::Hole { .. }))
        .count();
    Ok(FltTemplateBounds {
        source_bytes,
        body_bytes: body_src.len(),
        piece_count: pieces.len(),
        hole_declarations: holes.len(),
        hole_occurrences,
    })
}

fn valid_identifier(value: &str, allow_dot: bool) -> bool {
    let mut parts = value.split('.');
    let valid_part = |part: &str| {
        let mut chars = part.chars();
        matches!(chars.next(), Some('a'..='z' | 'A'..='Z' | '_'))
            && chars.all(|character| matches!(character, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
    };
    valid_part(parts.next().unwrap_or(""))
        && (allow_dot || parts.clone().next().is_none())
        && parts.all(valid_part)
}

impl BoundTerm<String> for FltNode {
    fn term_eq(&self, other: &Self) -> bool {
        self == other
    }

    fn close_term(&mut self, state: moniker::ScopeState, on_free: &impl moniker::OnFreeFn<String>) {
        self.selector.close_term(state, on_free);
    }

    fn open_term(
        &mut self,
        state: moniker::ScopeState,
        on_bound: &impl moniker::OnBoundFn<String>,
    ) {
        self.selector.open_term(state, on_bound);
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&moniker::Var<String>)) {
        self.selector.visit_vars(on_var);
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut moniker::Var<String>)) {
        self.selector.visit_mut_vars(on_var);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Binder, Scope};

    #[test]
    fn selector_closes_and_reopens_with_its_rholang_binder() {
        let selector = get_or_create_var("lambda");
        let node = FltNode::new("lambda".into(), "Term".into(), "x".into(), Vec::new(), 0)
            .expect("valid node");
        assert_eq!(node.selector.0, Var::Free(selector.clone()));

        let scope = Scope::new::<String>(Binder(selector), node);
        assert!(matches!(scope.unsafe_body().selector.0, Var::Bound(_)));

        let (Binder(reopened_binder), reopened_node) = scope.unbind::<String>();
        assert_eq!(reopened_node.selector.0, Var::Free(reopened_binder));
    }

    #[test]
    fn structural_template_validates_and_preserves_repeated_hole_identity() {
        let node = FltNode::from_structural_parts(
            "lam".into(),
            "Term".into(),
            "lam:Term`".into(),
            "App(${f}, ${f})".into(),
            vec![FltHole {
                id: FltHoleId(0),
                name: "f".into(),
                category: None,
                first_occurrence: FltSourceRange::new(4, 8),
            }],
            vec![
                FltTemplatePiece::Text {
                    text: "App(".into(),
                    range: FltSourceRange::new(0, 4),
                },
                FltTemplatePiece::Hole {
                    id: FltHoleId(0),
                    range: FltSourceRange::new(4, 8),
                },
                FltTemplatePiece::Text {
                    text: ", ".into(),
                    range: FltSourceRange::new(8, 10),
                },
                FltTemplatePiece::Hole {
                    id: FltHoleId(0),
                    range: FltSourceRange::new(10, 14),
                },
                FltTemplatePiece::Text {
                    text: ")".into(),
                    range: FltSourceRange::new(14, 15),
                },
            ],
            "`".into(),
            0,
        )
        .expect("valid structural FLT");
        assert_eq!(node.holes.len(), 1);
        assert_eq!(
            node.pieces
                .iter()
                .filter(|piece| matches!(piece, FltTemplatePiece::Hole { .. }))
                .count(),
            2,
        );
        assert_eq!(
            node.bounds,
            FltTemplateBounds {
                source_bytes: 25,
                body_bytes: 15,
                piece_count: 5,
                hole_declarations: 1,
                hole_occurrences: 2,
            },
        );
        assert_eq!(node.holes[0].first_occurrence, FltSourceRange::new(4, 8));

        let construction = node.stage(FltPolarity::PositiveConstruction);
        let pattern = node.stage(FltPolarity::NegativePattern);
        assert_eq!(construction.selector_name, "lam");
        assert_eq!(construction.category, "Term");
        assert_eq!(construction.telescope, pattern.telescope);
        assert_eq!(construction.pieces, pattern.pieces);
        assert_eq!(construction.bounds, pattern.bounds);
        assert_ne!(construction.polarity, pattern.polarity);
    }

    #[test]
    fn text_cannot_impersonate_a_hole_piece() {
        let node = FltNode::from_structural_parts(
            "lam".into(),
            "Term".into(),
            "lam`".into(),
            "${x}".into(),
            Vec::new(),
            vec![FltTemplatePiece::Text {
                text: "${x}".into(),
                range: FltSourceRange::new(0, 4),
            }],
            "`".into(),
            0,
        )
        .expect("text is inert guest text, not a structural hole");
        assert!(node.holes.is_empty());
        assert!(matches!(node.pieces.as_slice(), [FltTemplatePiece::Text { .. }]));
    }

    #[test]
    fn malformed_hole_name_cannot_inject_guest_tokens() {
        let error = FltNode::from_structural_parts(
            "lam".into(),
            "Term".into(),
            "lam`".into(),
            "${x) K}".into(),
            vec![FltHole {
                id: FltHoleId(0),
                name: "x) K".into(),
                category: None,
                first_occurrence: FltSourceRange::new(0, 7),
            }],
            vec![FltTemplatePiece::Hole {
                id: FltHoleId(0),
                range: FltSourceRange::new(0, 7),
            }],
            "`".into(),
            0,
        )
        .expect_err("hole names are terminals, never guest source fragments");
        assert!(matches!(error, FltTemplateError::InvalidHoleName(_)));
    }

    #[test]
    fn telescope_order_and_first_offsets_are_canonical() {
        let error = FltNode::from_structural_parts(
            "lam".into(),
            "Term".into(),
            "lam`".into(),
            "${y}${x}".into(),
            vec![
                FltHole {
                    id: FltHoleId(0),
                    name: "x".into(),
                    category: None,
                    first_occurrence: FltSourceRange::new(4, 8),
                },
                FltHole {
                    id: FltHoleId(1),
                    name: "y".into(),
                    category: None,
                    first_occurrence: FltSourceRange::new(0, 4),
                },
            ],
            vec![
                FltTemplatePiece::Hole {
                    id: FltHoleId(1),
                    range: FltSourceRange::new(0, 4),
                },
                FltTemplatePiece::Hole {
                    id: FltHoleId(0),
                    range: FltSourceRange::new(4, 8),
                },
            ],
            "`".into(),
            0,
        )
        .expect_err("ids follow first occurrence, not declaration order alone");
        assert!(matches!(error, FltTemplateError::NonCanonicalHoleOrder { .. }));
    }
}
