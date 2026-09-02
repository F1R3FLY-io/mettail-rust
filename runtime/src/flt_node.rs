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

/// One declared FLT hole. Repeated occurrences share the same [`FltHoleId`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltHole {
    pub id: FltHoleId,
    pub name: String,
    pub category: Option<String>,
    /// Byte offset of the first occurrence, retained for diagnostics.
    pub offset: usize,
}

/// One element of the structural template, in source order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FltTemplatePiece {
    /// Exact guest source between holes. It is lexed in isolation, ensuring no
    /// token can span a hole boundary.
    Text(String),
    /// A typed lattice terminal referring to the template telescope.
    Hole(FltHoleId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FltTemplateError {
    EmptyTag,
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
    WrongHoleOffset {
        id: FltHoleId,
        expected: usize,
        found: usize,
    },
    SourceMismatch,
}

impl fmt::Display for FltTemplateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTag => formatter.write_str("FLT tag is empty"),
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
            Self::WrongHoleOffset { id, expected, found } => write!(
                formatter,
                "FLT hole {id:?} has first offset {found}, expected {expected}",
            ),
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
    /// Original selector spelling, retained for exact display and diagnostics.
    pub tag: String,
    pub open_src: String,
    /// Retained only for exact diagnostics and display. Parsing uses `pieces`.
    pub body_src: String,
    pub holes: Vec<FltHole>,
    pub pieces: Vec<FltTemplatePiece>,
    pub close_src: String,
    pub position: usize,
}

impl FltNode {
    /// Compatibility constructor for programmatically created, usually
    /// hole-free nodes. Parsed FLTs use [`Self::from_structural_parts`].
    pub fn new(tag: String, body_src: String, holes: Vec<FltHole>, position: usize) -> Self {
        let selector = OrdVar(Var::Free(get_or_create_var(&tag)));
        let mut pieces = Vec::new();
        let mut cursor = 0usize;
        for hole in &holes {
            if hole.offset > cursor && hole.offset <= body_src.len() {
                pieces.push(FltTemplatePiece::Text(body_src[cursor..hole.offset].to_string()));
            }
            pieces.push(FltTemplatePiece::Hole(hole.id));
            let literal_len = 3
                + hole.name.len()
                + hole
                    .category
                    .as_ref()
                    .map_or(0, |category| 1 + category.len());
            cursor = hole.offset.saturating_add(literal_len).min(body_src.len());
        }
        if cursor < body_src.len() || pieces.is_empty() {
            pieces.push(FltTemplatePiece::Text(body_src[cursor..].to_string()));
        }
        Self {
            selector,
            open_src: tag.clone(),
            tag,
            body_src,
            holes,
            pieces,
            close_src: String::new(),
            position,
        }
    }

    pub fn from_structural_parts(
        tag: String,
        open_src: String,
        body_src: String,
        holes: Vec<FltHole>,
        pieces: Vec<FltTemplatePiece>,
        close_src: String,
        position: usize,
    ) -> Result<Self, FltTemplateError> {
        let selector = OrdVar(Var::Free(get_or_create_var(&tag)));
        let node = Self {
            selector,
            tag,
            open_src,
            body_src,
            holes,
            pieces,
            close_src,
            position,
        };
        node.validate()?;
        Ok(node)
    }

    /// Validate telescope identity, occurrence references, and exact-source
    /// reconstruction. The traversal is iterative and bounded by the node size.
    pub fn validate(&self) -> Result<(), FltTemplateError> {
        if self.tag.is_empty() {
            return Err(FltTemplateError::EmptyTag);
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

        let mut rebuilt = String::with_capacity(self.body_src.len());
        let mut occurred = BTreeSet::new();
        for piece in &self.pieces {
            match piece {
                FltTemplatePiece::Text(text) => rebuilt.push_str(text),
                FltTemplatePiece::Hole(id) => {
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
                        if hole.offset != rebuilt.len() {
                            return Err(FltTemplateError::WrongHoleOffset {
                                id: *id,
                                expected: rebuilt.len(),
                                found: hole.offset,
                            });
                        }
                    }
                    rebuilt.push_str("${");
                    rebuilt.push_str(&hole.name);
                    if let Some(category) = &hole.category {
                        rebuilt.push(':');
                        rebuilt.push_str(category);
                    }
                    rebuilt.push('}');
                },
            }
        }
        if rebuilt != self.body_src {
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
        Ok(())
    }

    pub fn hole(&self, id: FltHoleId) -> Option<&FltHole> {
        self.holes.get(id.0 as usize).filter(|hole| hole.id == id)
    }
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
        let node = FltNode::new("lambda".into(), "x".into(), Vec::new(), 0);
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
            "lam`".into(),
            "App(${f}, ${f})".into(),
            vec![FltHole {
                id: FltHoleId(0),
                name: "f".into(),
                category: None,
                offset: 4,
            }],
            vec![
                FltTemplatePiece::Text("App(".into()),
                FltTemplatePiece::Hole(FltHoleId(0)),
                FltTemplatePiece::Text(", ".into()),
                FltTemplatePiece::Hole(FltHoleId(0)),
                FltTemplatePiece::Text(")".into()),
            ],
            "`".into(),
            0,
        )
        .expect("valid structural FLT");
        assert_eq!(node.holes.len(), 1);
        assert_eq!(
            node.pieces
                .iter()
                .filter(|piece| matches!(piece, FltTemplatePiece::Hole(_)))
                .count(),
            2,
        );
    }

    #[test]
    fn text_cannot_impersonate_a_hole_piece() {
        let node = FltNode::from_structural_parts(
            "lam".into(),
            "lam`".into(),
            "${x}".into(),
            Vec::new(),
            vec![FltTemplatePiece::Text("${x}".into())],
            "`".into(),
            0,
        )
        .expect("text is inert guest text, not a structural hole");
        assert!(node.holes.is_empty());
        assert!(matches!(node.pieces.as_slice(), [FltTemplatePiece::Text(_)]));
    }

    #[test]
    fn malformed_hole_name_cannot_inject_guest_tokens() {
        let error = FltNode::from_structural_parts(
            "lam".into(),
            "lam`".into(),
            "${x) K}".into(),
            vec![FltHole {
                id: FltHoleId(0),
                name: "x) K".into(),
                category: None,
                offset: 0,
            }],
            vec![FltTemplatePiece::Hole(FltHoleId(0))],
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
            "lam`".into(),
            "${y}${x}".into(),
            vec![
                FltHole {
                    id: FltHoleId(0),
                    name: "x".into(),
                    category: None,
                    offset: 4,
                },
                FltHole {
                    id: FltHoleId(1),
                    name: "y".into(),
                    category: None,
                    offset: 0,
                },
            ],
            vec![FltTemplatePiece::Hole(FltHoleId(1)), FltTemplatePiece::Hole(FltHoleId(0))],
            "`".into(),
            0,
        )
        .expect_err("ids follow first occurrence, not declaration order alone");
        assert!(matches!(error, FltTemplateError::NonCanonicalHoleOrder { .. }));
    }
}
