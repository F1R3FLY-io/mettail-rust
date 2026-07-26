//! **THE** reserved-band allocator for every MeTTaIL system-process contract (#36 S4 + S5).
//!
//! MeTTaIL installs two families of f1r3node *system processes* — machine-side contracts the
//! emitted Rholang calls through a fixed unforgeable channel:
//!
//! | band | what it serves | built by |
//! |---|---|---|
//! | **held-fold** (Tier-3 trampoline) | one contract per width/precision fold SITE | `rholang-runtime/src/fold_contract.rs` |
//! | **native-handler** (A-S3) | one contract per registrable native RULE | `rholang-runtime/src/native_contract.rs` |
//!
//! Each contract needs two identifiers, and f1r3node treats them very differently:
//!
//! * a **`fixed_channel`** — the unforgeable `GPrivate` the emitted `Par` sends to. This is
//!   **CONSENSUS-VISIBLE**: it is embedded in the emitted `Par` as a send target, so it is part
//!   of the term every validator normalizes and stores.
//! * a **`body_ref`** — the `i64` key under which f1r3node's `dispatch_table_creator` registers
//!   the handler. This is **NOT visible via the state root** (`installed_continuations` is
//!   excluded from `hot_store::changes()`), but it IS **replay-relevant**: a node that
//!   reconstructs a different `body_ref → handler` map than the one that produced a block
//!   dispatches differently and diverges.
//!
//! # The defect this module exists to remove
//!
//! Both bands used to key on a bare index alone — `GPrivate{id: [0xF1, rule_index]}` with
//! `body_ref = 0xF100 + rule_index`, and `GPrivate{id: [0xF0, site_index]}` with
//! `body_ref = 0xF000 + site_index`. The language fingerprint appeared only in the `Definition`
//! URN, which f1r3node does not key on.
//!
//! Two co-installed native-bearing languages therefore both allocate rule index `0`, producing
//! an **identical `fixed_channel` AND an identical `body_ref`**. f1r3node's
//! `dispatch_table_creator` builds a `HashMap`, so the later insert silently wins — and which
//! one is "later" depends on install order. Two nodes that install in different orders reduce
//! the same term differently. That is a consensus fault reachable without an attacker: it is the
//! default outcome of co-installing two languages that each declare one native rule.
//!
//! # The fix, and why it is shaped this way
//!
//! **Channels are made collision-free BY CONSTRUCTION.** The fingerprint bytes are appended
//! verbatim to the id: `[tag, index] ++ fingerprint.as_bytes()`. Two ids are equal iff their
//! `(tag, index, fingerprint)` triples are equal, with no digest and therefore no collision
//! probability at all. This is computable at macro time — the fingerprint is a compile-time
//! property of the language definition — so nothing is deferred to install time.
//!
//! **`body_ref`s cannot be collision-free, so they are made deterministic and CHECKED.** A
//! `body_ref` is one `i64`; the `(fingerprint, index)` domain is unbounded; the pigeonhole
//! principle settles it. Two responses are possible and only one is safe:
//!
//! * an **allocation counter** ("hand out 0xF100, 0xF101, … as contracts register") is
//!   collision-free but **order-dependent**, which reintroduces exactly the divergence the fix
//!   is for, in a form that is harder to see. Rejected.
//! * a **deterministic function of `(fingerprint, index)`** is order-independent and replay-
//!   stable, at the price of a residual digest-collision probability. Chosen — and the residual
//!   is converted from *silent wrong dispatch* into a *loud refusal* by
//!   [`check_body_refs_pairwise_distinct`], which every `Definition`-materializing entry point
//!   calls before handing the set to f1r3node.
//!
//! # `body_ref` layout
//!
//! ```text
//!  bit 63    62 … 56       55 … 48        47 … 0
//! ┌───────┬────────────┬─────────────┬──────────────────────────┐
//! │   0   │  band id   │    index    │  48-bit fingerprint hash │
//! └───────┴────────────┴─────────────┴──────────────────────────┘
//!  always   1=held-fold  site_index /   FNV-1a over the whole
//!  clear    2=native      rule_index    fingerprint string
//! ```
//!
//! * bit 63 is always clear, so every `body_ref` is a positive `i64` (f1r3node compares them as
//!   signed);
//! * the band id occupies bits 62..56, so the two bands occupy the strictly disjoint ranges
//!   `0x0100_0000_0000_0000..=0x01FF_…` and `0x0200_0000_0000_0000..=0x02FF_…`, and both sit
//!   astronomically above f1r3node's own std (`0..=36`) and test-framework (`101..=108`)
//!   `body_ref`s and outside `non_deterministic_ops()`;
//! * the index occupies bits 55..48, so within ONE language two different sites/rules can never
//!   collide *at all* — the residual collision risk is strictly cross-fingerprint, at the
//!   birthday bound of a 48-bit digest (~2²⁴ ≈ 16.7 M co-installed languages for even odds),
//!   and it is checked rather than assumed.
//!
//! # Why the digest is FNV-1a and not [`std::hash::DefaultHasher`]
//!
//! `DefaultHasher`'s output is explicitly **not** guaranteed stable across Rust releases. A
//! `body_ref` derived from it would silently change under a toolchain upgrade, so two nodes on
//! different toolchains would build different dispatch tables from the *same* language — a
//! replay divergence introduced by a compiler bump. FNV-1a is specified here in full, in code,
//! and can never drift.
//!
//! Reference: Fowler, Noll & Vo, *FNV Hash* — the 64-bit variant, offset basis
//! `0xcbf29ce484222325`, prime `0x100000001b3`. IETF draft:
//! <https://datatracker.ietf.org/doc/html/draft-eastlake-fnv-21>

use models::rhoapi::g_unforgeable::UnfInstance::GPrivateBody;
use models::rhoapi::{GPrivate, GUnforgeable, Par};

/// FNV-1a 64-bit offset basis.
const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
/// FNV-1a 64-bit prime.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Bit position of the band id inside a `body_ref`.
const BAND_ID_SHIFT: u32 = 56;
/// Bit position of the site/rule index inside a `body_ref`.
const INDEX_SHIFT: u32 = 48;
/// The low bits a `body_ref` reserves for the fingerprint digest.
const DIGEST_BITS: u32 = 48;
/// Mask selecting [`DIGEST_BITS`] low bits.
const DIGEST_MASK: u64 = (1u64 << DIGEST_BITS) - 1;

/// The stable 48-bit digest of a language fingerprint — FNV-1a 64 over the fingerprint's UTF-8
/// bytes, truncated to the low [`DIGEST_BITS`] bits.
///
/// Specified in code (not delegated to a hasher whose output may change) precisely because a
/// `body_ref` derived from it is replay-relevant: see this module's header.
pub fn fingerprint_digest(language_fingerprint: &str) -> u64 {
    let mut hash = FNV_OFFSET_BASIS;
    for byte in language_fingerprint.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash & DIGEST_MASK
}

/// One reserved system-process band: a channel tag byte plus a `body_ref` band id.
///
/// Construct nothing at runtime — the two bands are the `const`s [`HELD_FOLD_BAND`] and
/// [`NATIVE_HANDLER_BAND`]. Making this a type rather than two parallel sets of free functions
/// is the point of #36 S5: the held-fold and native-handler bands had the identical defect and
/// were being fixed separately, which is how they drifted apart in the first place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SystemProcessBand {
    /// Human-readable band name, for error messages.
    pub name: &'static str,
    /// The `body_ref` band id, occupying bits 62..56. MUST be in `1..=126` (bit 63 stays clear).
    pub band_id: u8,
    /// The leading byte of every channel id in this band.
    pub channel_tag: u8,
}

/// The Tier-3 held-fold trampoline band (one contract per fold SITE).
pub const HELD_FOLD_BAND: SystemProcessBand = SystemProcessBand {
    name: "held-fold",
    band_id: 1,
    channel_tag: MTL_FOLD_CHANNEL_TAG,
};

/// The A-S3 native-handler band (one contract per registrable native RULE).
pub const NATIVE_HANDLER_BAND: SystemProcessBand = SystemProcessBand {
    name: "native-handler",
    band_id: 2,
    channel_tag: MTL_NATIVE_CHANNEL_TAG,
};

/// Leading byte of every held-fold contract channel id.
pub const MTL_FOLD_CHANNEL_TAG: u8 = 0xF0;
/// Leading byte of every native-handler contract channel id.
pub const MTL_NATIVE_CHANNEL_TAG: u8 = 0xF1;

impl SystemProcessBand {
    /// The unforgeable contract channel for `(index, fingerprint)` in this band:
    /// `GPrivate{id: [channel_tag, index] ++ fingerprint.as_bytes()}`.
    ///
    /// **Collision-free by construction, not by digest**: the fingerprint rides verbatim, so two
    /// channels are equal iff their `(band, index, fingerprint)` triples are. The id is at least
    /// three bytes, so it also cannot equal any of f1r3node's own single-byte system-process
    /// channel ids (std `0..=36`, test framework `101..=108`).
    ///
    /// ★ CONSENSUS-VISIBLE: this channel is embedded in the emitted `Par` as a send target.
    pub fn channel(&self, index: u8, language_fingerprint: &str) -> Par {
        let fingerprint_bytes = language_fingerprint.as_bytes();
        let mut id = Vec::with_capacity(2 + fingerprint_bytes.len());
        id.push(self.channel_tag);
        id.push(index);
        id.extend_from_slice(fingerprint_bytes);
        Par::default().with_unforgeables(vec![GUnforgeable {
            unf_instance: Some(GPrivateBody(GPrivate { id })),
        }])
    }

    /// The `body_ref` for `(index, fingerprint)` in this band — a DETERMINISTIC function of its
    /// inputs and nothing else (never an allocation counter; see this module's header for why
    /// that distinction is the whole point).
    ///
    /// ★ Not state-root visible, but replay-relevant.
    pub fn body_ref(&self, index: u8, language_fingerprint: &str) -> i64 {
        debug_assert!(
            self.band_id >= 1 && self.band_id <= 126,
            "a band id must leave the i64 sign bit clear"
        );
        let bits = (u64::from(self.band_id) << BAND_ID_SHIFT)
            | (u64::from(index) << INDEX_SHIFT)
            | fingerprint_digest(language_fingerprint);
        // The sign bit is clear by construction (band_id ≤ 126 ⇒ bit 63 = 0), so this cast is
        // value-preserving into the positive i64 range.
        bits as i64
    }

    /// The inclusive `body_ref` range this band occupies.
    pub fn body_ref_range(&self) -> std::ops::RangeInclusive<i64> {
        let base = (u64::from(self.band_id) << BAND_ID_SHIFT) as i64;
        base..=(base | ((1i64 << BAND_ID_SHIFT) - 1))
    }
}

/// A band allocation that cannot be handed to f1r3node.
///
/// The only variant is a `body_ref` collision, which is unreachable within one language (the
/// index occupies its own bit field) and is the residual 48-bit digest birthday risk across
/// co-installed languages. Surfacing it as a typed error is what converts a digest collision
/// from *silent wrong dispatch* — f1r3node's `dispatch_table_creator` `HashMap` would simply let
/// the later insert win — into a loud refusal at install time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BandAllocationError {
    /// Two distinct specs in the same band derived the same `body_ref`.
    BodyRefCollision {
        /// The band whose allocation collided.
        band: &'static str,
        /// The `body_ref` both specs derived.
        body_ref: i64,
        /// The first spec's identity (its `Definition` URN).
        first: String,
        /// The colliding spec's identity (its `Definition` URN).
        second: String,
    },
}

impl std::fmt::Display for BandAllocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BandAllocationError::BodyRefCollision { band, body_ref, first, second } => write!(
                f,
                "{band} band: {first:?} and {second:?} both derive body_ref {body_ref:#x} — \
                 f1r3node's dispatch table is keyed by body_ref, so installing both would let \
                 one silently shadow the other and make reduction depend on install order. \
                 This is a 48-bit fingerprint-digest collision; refusing rather than dispatching \
                 wrongly."
            ),
        }
    }
}

impl std::error::Error for BandAllocationError {}

/// Verify that a set of `(identity, body_ref)` allocations in one band is pairwise distinct.
///
/// Every entry point that materializes `Definition`s calls this BEFORE handing them to
/// f1r3node, so a digest collision is refused loudly instead of resolving into whichever
/// handler the `HashMap` happened to keep.
pub fn check_body_refs_pairwise_distinct<'a, I>(
    band: &SystemProcessBand,
    allocations: I,
) -> Result<(), BandAllocationError>
where
    I: IntoIterator<Item = (&'a str, i64)>,
{
    let iter = allocations.into_iter();
    let (lower, _) = iter.size_hint();
    let mut seen: std::collections::HashMap<i64, &'a str> = std::collections::HashMap::with_capacity(lower);
    for (identity, body_ref) in iter {
        if let Some(first) = seen.insert(body_ref, identity) {
            return Err(BandAllocationError::BodyRefCollision {
                band: band.name,
                body_ref,
                first: first.to_string(),
                second: identity.to_string(),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const FP_A: &str = "mettail-langdef-v1:6ef0c40636bb0bca";
    const FP_B: &str = "mettail-langdef-v1:0123456789abcdef";

    /// ★ THE DEFECT THIS MODULE REMOVES: two co-installed languages each allocating index 0 no
    /// longer produce the same channel or the same `body_ref` in either band.
    #[test]
    fn index_zero_in_two_languages_no_longer_collides() {
        for band in [HELD_FOLD_BAND, NATIVE_HANDLER_BAND] {
            assert_ne!(
                band.channel(0, FP_A),
                band.channel(0, FP_B),
                "{}: two languages' index-0 channels must differ — this equality is the \
                 consensus fault (identical fixed_channel ⇒ f1r3node's dispatch table lets the \
                 later install win, so reduction depends on install order)",
                band.name
            );
            assert_ne!(
                band.body_ref(0, FP_A),
                band.body_ref(0, FP_B),
                "{}: two languages' index-0 body_refs must differ",
                band.name
            );
        }
    }

    /// The channel carries the fingerprint VERBATIM, so collision-freedom is by construction
    /// rather than by digest — there is no probability to bound.
    #[test]
    fn the_channel_id_is_tag_index_then_the_fingerprint_bytes() {
        let par = NATIVE_HANDLER_BAND.channel(7, FP_A);
        let [unforgeable] = par.unforgeables.as_slice() else {
            panic!("a band channel is exactly one unforgeable");
        };
        let Some(GPrivateBody(private)) = unforgeable.unf_instance.as_ref() else {
            panic!("a band channel is a GPrivate");
        };
        let mut expected = vec![MTL_NATIVE_CHANNEL_TAG, 7];
        expected.extend_from_slice(FP_A.as_bytes());
        assert_eq!(private.id, expected);
        assert!(
            private.id.len() > 2,
            "a fingerprint-scoped id is longer than the old two-byte form, so it cannot equal \
             any f1r3node single-byte system-process id either"
        );
    }

    /// The two bands are disjoint from each other and from f1r3node's own `body_ref`s, and every
    /// allocation is a positive `i64` (the sign bit is structurally clear).
    #[test]
    fn the_bands_are_disjoint_and_positive() {
        let fold = HELD_FOLD_BAND.body_ref_range();
        let native = NATIVE_HANDLER_BAND.body_ref_range();
        assert!(fold.end() < native.start(), "the two bands must not overlap");
        assert!(
            *fold.start() > 108,
            "both bands sit above f1r3node's std (0-36) and test-framework (101-108) body_refs"
        );
        for fingerprint in [FP_A, FP_B, "", "not-a-fingerprint"] {
            for index in [0u8, 1, 42, u8::MAX] {
                for (band, range) in
                    [(HELD_FOLD_BAND, &fold), (NATIVE_HANDLER_BAND, &native)]
                {
                    let body_ref = band.body_ref(index, fingerprint);
                    assert!(body_ref > 0, "{}: body_ref must be positive", band.name);
                    assert!(
                        range.contains(&body_ref),
                        "{}: body_ref {body_ref:#x} must stay inside its band",
                        band.name
                    );
                }
            }
        }
    }

    /// Within ONE language two indices can never collide — the index has its own bit field, so
    /// this is structural, not probabilistic.
    #[test]
    fn distinct_indices_in_one_language_never_collide() {
        let refs: std::collections::BTreeSet<i64> =
            (0..=u8::MAX).map(|i| NATIVE_HANDLER_BAND.body_ref(i, FP_A)).collect();
        assert_eq!(refs.len(), 256, "all 256 indices must be pairwise distinct");
    }

    /// The digest is order-independent and stable: the SAME `(fingerprint, index)` always maps
    /// to the same `body_ref`, no matter when or in what order it is asked for. That is the
    /// property an allocation counter would destroy.
    #[test]
    fn allocation_is_deterministic_not_order_dependent() {
        let first: Vec<i64> = [(0u8, FP_A), (1, FP_B), (2, FP_A)]
            .iter()
            .map(|(i, fp)| NATIVE_HANDLER_BAND.body_ref(*i, fp))
            .collect();
        // Ask again in the OPPOSITE order; a counter would hand out different values.
        let mut reversed: Vec<i64> = [(2u8, FP_A), (1, FP_B), (0, FP_A)]
            .iter()
            .map(|(i, fp)| NATIVE_HANDLER_BAND.body_ref(*i, fp))
            .collect();
        reversed.reverse();
        assert_eq!(first, reversed, "allocation must not depend on request order");
    }

    /// FNV-1a is pinned against its published test vectors, so a future edit cannot quietly
    /// change every `body_ref` in the tree.
    #[test]
    fn fnv1a_matches_the_published_vectors() {
        // The published FNV-1a 64 values, truncated to the 48 bits this module uses.
        for (input, full) in [
            ("", 0xcbf29ce484222325u64),
            ("a", 0xaf63dc4c8601ec8cu64),
            ("foobar", 0x85944171f73967e8u64),
        ] {
            assert_eq!(
                fingerprint_digest(input),
                full & DIGEST_MASK,
                "FNV-1a 64 of {input:?} must match the published vector"
            );
        }
    }

    /// A collision is REFUSED, not resolved — the check reports both colliding identities.
    #[test]
    fn a_body_ref_collision_is_a_typed_refusal() {
        assert_eq!(
            check_body_refs_pairwise_distinct(
                &NATIVE_HANDLER_BAND,
                [("mtl:native:a:R", 5i64), ("mtl:native:b:R", 5)]
            ),
            Err(BandAllocationError::BodyRefCollision {
                band: "native-handler",
                body_ref: 5,
                first: "mtl:native:a:R".to_string(),
                second: "mtl:native:b:R".to_string(),
            })
        );
        assert!(check_body_refs_pairwise_distinct(
            &NATIVE_HANDLER_BAND,
            [("mtl:native:a:R", 5i64), ("mtl:native:b:R", 6)]
        )
        .is_ok());
    }
}
