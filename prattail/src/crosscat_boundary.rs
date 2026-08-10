//! ★ THE CROSS-CATEGORY PROJECTION-BOUNDARY WALK — the per-hop decision, factored out so its
//! VERIFIED MODEL can be executed against it.
//!
//! # Why this module exists
//!
//! `wpda_walker.rs::cgll_pure_crosscat_boundaries` walks the caller chain from an operand frame
//! looking for an enclosing projection whose floor should take the pending operator instead. It
//! has a verified model —
//! `formal/rocq/prattail_wpda_runtime/theories/CollectionElementProjectionBoundary.v` — which
//! states the walk as five edge kinds and eight lines:
//!
//! ```text
//!   walk []                = None_
//!   walk (Proj t   :: _)   = Found t          (* the hop's OWN evidence terminates the walk *)
//!   walk (CollElem :: _)   = None_
//!   walk (Grouping :: _)   = None_            (* `grouping_stops_walk`                      *)
//!   walk (RuleSlot :: _)   = None_
//!   walk (Pass :: rest)    = walk rest
//! ```
//!
//! The theorems are proved. **The bridge was missing**: nothing executable connected the Rust
//! loop to those lines, so the loop drifted from them TWICE, and each drift was found only as a
//! production parse failure weeks later:
//!
//! | # | drift | measured symptom |
//! |---|---|---|
//! | 1 | `GroupingMarker` was absent from the stop-kind list, so `walk (… :: Grouping :: _)` did NOT return `None_` | `@(@@Nil!().subtract(a!(Nil)))!(Nil)` FAILED while the `{}`-delimited twin parsed — the only difference being `()` versus `{}` |
//! | 2 | the whole stop test was gated on `slot.xcat == 0`, exempting every hop whose push carried a cross-category edge | the `(`-open fan stamps its grouping frames with `xcat = 3`, so a group did not shield its interior from an outer `@`-projection floor |
//!
//! Both are divergences from the model, and both are decidable from the hop's own facts. This
//! module holds that decision as ONE pure function, [`classify_hop`], which the walker calls and
//! which `prattail/tests/crosscat_boundary_oracle.rs` property-tests against an independent
//! transcription of the model above. There is no second implementation: the walker's behaviour
//! IS what the oracle checks.
//!
//! [`BoundaryTargetSummary`] is the incremental, token-independent projection of the same walk.
//! It forms a monotone lattice over reachable target categories and lets the walker reject a
//! lookahead without revisiting ancestry when no reachable category recognizes that token. It
//! never decides a positive result: positives still execute the exact cycle-safe DFS, preserving
//! first-target and ANY-yield/ALL-suppress behavior. Its independent property oracle is
//! `prattail/tests/crosscat_boundary_summary_oracle.rs`; its admission-free equivalence proof is
//! `formal/rocq/prattail_wpda_runtime/theories/CrossCatBoundarySummary.v`.
//!
//! # The correspondence, stated once
//!
//! A hop is one caller-chain edge, carrying: the pushed frame's cross-category stamp `xcat`, its
//! boundary floor `xcat_bp`, its wrap category `xcat_wrap`, the category it pushed `pushed_cat`,
//! and the CALLER frame's kind and category.
//!
//! ```text
//!   model edge        ⟸  hop facts
//!   ────────────────      ─────────────────────────────────────────────────────────────────
//!   Grouping          ⟸  caller kind is GroupingMarker      ⎫ a frame that RE-SCOPES its
//!   CollElem          ⟸  caller kind is CollectionMarker    ⎬ content behind a SELF-DELIMITING
//!   RuleSlot          ⟸  caller kind is MixfixMarker/RuleAt(k>0) ⎭ close cannot hand its
//!                                                             interior operators outward
//!   Proj t            ⟸  the hop resolves a boundary target with floor t
//!   Pass              ⟸  anything else
//! ```
//!
//! and the one refinement the model's own derivation forces: `walk (Proj t :: Grouping :: rest)
//! = Found t`. A hop that carries EXPLICIT, INTRINSIC evidence of its own target reports that
//! target even when its caller is a re-scoping frame — and then the walk STOPS, because there is
//! no derivation in the model in which a chain reads a target from BEYOND a stop edge.
//! "Explicit and intrinsic" is `xcat == 4` (the `CrossCatProjection` stamp, whose target is the
//! hop's own `pushed_cat`) or `xcat == 3` with a recorded wrap; the INFERRED rows `xcat ∈ {1,2}`
//! read their target OFF THE CALLER and so are not intrinsic, and a bare `xcat == 3` has no
//! wrap to read.

use crate::wpda_runtime::SymbolKind;

/// Is `kind` a frame that RE-SCOPES its content behind a self-delimiting close?
///
/// This is the Rust side of the model's `{ Grouping, CollElem, RuleSlot }` stop set. The
/// criterion — stated in `CollectionElementProjectionBoundary.v` and not inferable from the enum
/// — is that such a frame cannot hand its interior operators to anything outside it.
///
/// ⚠ `GroupingMarker`'s absence from this list was drift #1 (see the module header): a `(`-group
/// did not shield its interior from an outer `@`-projection floor, and a reading was destroyed
/// before the forest ever saw it.
#[inline]
pub fn kind_is_rescoping(kind: SymbolKind) -> bool {
    matches!(
        kind,
        SymbolKind::MixfixMarker | SymbolKind::CollectionMarker | SymbolKind::GroupingMarker
    ) || matches!(kind, SymbolKind::RuleAt(k) if k > 0)
}

/// Does this hop carry EXPLICIT, INTRINSIC evidence of its own boundary target?
///
/// `xcat == 4` is the `CrossCatProjection` stamp: the target is the hop's own `pushed_cat` — the
/// projection's own result category — read from neither the caller nor anything outside a
/// surrounding group, so consuming it hands nothing across a re-scoping boundary. `xcat == 3`
/// with a recorded wrap is the same in kind (the wrap is stored on the hop); a bare `xcat == 3`
/// has `xcat_wrap == u16::MAX` and is NOT explicit, which is what keeps the `(`-open fan's
/// per-category grouping frames stopping at a grouping.
///
/// ⚠ Widening this to `xcat != 0` was drift #2 (see the module header).
#[inline]
pub fn hop_has_explicit_target(xcat: u8, xcat_wrap: u16) -> bool {
    xcat == 4 || (xcat == 3 && xcat_wrap != u16::MAX)
}

/// The facts one caller-chain hop contributes to the walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HopFacts {
    /// Cross-category scope stamp of the PUSH that created this frame.
    pub xcat: u8,
    /// The hop's boundary floor (`u16::MAX` = none).
    pub xcat_bp: u16,
    /// The hop's boundary wrap category (`u16::MAX` = none).
    pub xcat_wrap: u16,
    /// The category this hop pushed — the `xcat == 4` target.
    pub pushed_cat: u16,
    /// The caller frame's kind, when this frame has a caller (a seed frame has none).
    pub caller_kind: Option<SymbolKind>,
    /// The caller frame's category — the `xcat ∈ {1,2}` target.
    pub caller_cat: u16,
}

/// What the walk does at one hop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HopVerdict {
    /// The chain DIES at this hop WITHOUT running its boundary mapping: its caller re-scopes and
    /// it carries no intrinsic evidence of its own. Model: a stop edge ahead of this hop's edge.
    pub dies_before_mapping: bool,
    /// The boundary target `(category, floor)` this hop resolves, if any. Only meaningful when
    /// `!dies_before_mapping`.
    pub target: Option<(u16, u16)>,
    /// After this hop's mapping has run, the walk must not ascend: the frame above re-scopes.
    /// Model: `walk (… :: Grouping :: _) = None_`.
    pub stops_after_mapping: bool,
}

/// ★ THE PER-HOP DECISION, in one place.
///
/// The walker calls this; the oracle checks it against the model. Any future change to the stop
/// set, to the evidence predicate, or to the target resolution happens HERE and is therefore
/// checked, which is precisely the property the two historical drifts lacked.
#[inline]
pub fn classify_hop(hop: &HopFacts) -> HopVerdict {
    let caller_is_stop = hop.caller_kind.map(kind_is_rescoping).unwrap_or(false);
    let explicit = hop_has_explicit_target(hop.xcat, hop.xcat_wrap);
    if caller_is_stop && !explicit {
        return HopVerdict {
            dies_before_mapping: true,
            target: None,
            stops_after_mapping: true,
        };
    }
    // Boundary mapping for THIS hop.
    let target: Option<(u16, u16)> = match hop.xcat {
        4 => Some((hop.pushed_cat, hop.xcat_bp)),
        1 | 2 => hop.caller_kind.map(|_| (hop.caller_cat, hop.xcat_bp)),
        3 if hop.xcat_wrap != u16::MAX => Some((hop.xcat_wrap, hop.xcat_bp)),
        _ => None,
    };
    HopVerdict {
        dies_before_mapping: false,
        target,
        stops_after_mapping: caller_is_stop,
    }
}

/// ARM G v3: EXPLICIT wrap evidence admits SAME-CATEGORY boundaries; the INFERRED rows
/// (`xcat ∈ {1,2}`) keep the `target != source` filter, because their caller-category
/// reconstruction is pure-side inference rather than a stored payload.
#[inline]
pub fn boundary_admits_same_category(xcat: u8, xcat_wrap: u16) -> bool {
    hop_has_explicit_target(xcat, xcat_wrap)
}

/// Sparse-overflow category bitset used by [`BoundaryTargetSummary`]. The first 256 source
/// indices are allocation-free; the sorted overflow preserves full `u16` generality without
/// attaching an 8 KiB dense set to every GSS node.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct BoundaryCategorySet {
    low: [u64; 4],
    high: Vec<u16>,
}

impl BoundaryCategorySet {
    fn is_empty(&self) -> bool {
        self.low.iter().all(|&word| word == 0) && self.high.is_empty()
    }

    fn insert(&mut self, cat: u16) -> bool {
        let word = usize::from(cat) / u64::BITS as usize;
        if word < self.low.len() {
            let mask = 1_u64 << (usize::from(cat) % u64::BITS as usize);
            let changed = self.low[word] & mask == 0;
            self.low[word] |= mask;
            return changed;
        }
        match self.high.binary_search(&cat) {
            Ok(_) => false,
            Err(at) => {
                self.high.insert(at, cat);
                true
            },
        }
    }

    fn union_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (dst, src) in self.low.iter_mut().zip(other.low) {
            let merged = *dst | src;
            changed |= merged != *dst;
            *dst = merged;
        }
        for &cat in &other.high {
            changed |= self.insert(cat);
        }
        changed
    }

    fn any(&self, mut predicate: impl FnMut(u16) -> bool) -> bool {
        for (word_idx, &word) in self.low.iter().enumerate() {
            let mut remaining = word;
            while remaining != 0 {
                let bit = remaining.trailing_zeros() as usize;
                let cat = (word_idx * u64::BITS as usize + bit) as u16;
                if predicate(cat) {
                    return true;
                }
                remaining &= remaining - 1;
            }
        }
        self.high.iter().copied().any(predicate)
    }
}

/// Monotone lattice summary of every boundary target reachable from one GSS node before a
/// scope-resetting/dead hop.
///
/// Explicit wrap evidence admits the source category itself. Inferred targets occupy a separate
/// component because they require `target != source`. The summary deliberately forgets target
/// order: it is used only to prove that the exact walk's result is empty. A positive result still
/// runs the exhaustive walk, preserving first-target and ANY-yield/ALL-suppress semantics.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BoundaryTargetSummary {
    same_category_admissible: BoundaryCategorySet,
    cross_category_only: BoundaryCategorySet,
    inherits_callers: bool,
}

impl BoundaryTargetSummary {
    /// Token-independent transfer for one caller-chain hop.
    pub fn from_hop(hop: &HopFacts) -> Self {
        let verdict = classify_hop(hop);
        if verdict.dies_before_mapping {
            return Self::default();
        }
        let mut summary = Self {
            inherits_callers: !verdict.stops_after_mapping,
            ..Self::default()
        };
        if let Some((target_cat, _)) = verdict.target {
            if boundary_admits_same_category(hop.xcat, hop.xcat_wrap) {
                summary.same_category_admissible.insert(target_cat);
            } else {
                summary.cross_category_only.insert(target_cat);
            }
        }
        summary
    }

    /// Whether a lookahead rejected by this hop may continue to caller nodes.
    pub fn inherits_callers(&self) -> bool {
        self.inherits_callers
    }

    /// Whether either lattice component contains a reachable target.
    pub fn has_targets(&self) -> bool {
        !self.same_category_admissible.is_empty() || !self.cross_category_only.is_empty()
    }

    /// Join reachable targets from a caller summary. Returns whether this
    /// summary grew; repeated joins reach an idempotent fixed point.
    pub fn union_targets_from(&mut self, other: &Self) -> bool {
        self.same_category_admissible
            .union_from(&other.same_category_admissible)
            | self
                .cross_category_only
                .union_from(&other.cross_category_only)
    }

    /// Does any summarized target recognize the lookahead while satisfying the
    /// explicit/inferred same-category rule?
    pub fn may_recognize(&self, source_cat: u16, mut recognizes: impl FnMut(u16) -> bool) -> bool {
        self.same_category_admissible.any(&mut recognizes)
            || self
                .cross_category_only
                .any(|cat| cat != source_cat && recognizes(cat))
    }
}
