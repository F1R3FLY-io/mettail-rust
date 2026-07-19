//! A-S3 (native dispatch boundary tightening): the registered NATIVE-HANDLER contract seam —
//! the generalization of the Tier-3 held-fold trampoline (`rholang-runtime/src/fold_contract.rs`)
//! to EVERY registrable `fold` native rule (`NativeSystemProcessRewrite` / `NativeFold`).
//!
//! Before A-S3, an admitted rho-net match for a native rule forwarded a HOST-COMPUTED value: the
//! D-stage (Dovetail) evaluated the rule's `![…] fold` body and the value bridge
//! ([`native_locate_bridge_par`](crate::native_locate_bridge_par)) carried that pre-computed
//! contractum into the call `Par` — the machine only ferried it. A-S3 makes the native contractum
//! DIRECTED COMPUTE ON THE MACHINE: the generated report-free match body records one
//! [`NativeHandlerSpec`] per located native rule (via the thread-local pending registry below),
//! the runtime converts each spec into a system-process `Definition`
//! (`rholang-runtime/src/native_contract.rs`) injected through the SAME `extra_system_processes`
//! seam the held-fold trampoline uses, and the co-installed contract-call bridge
//! ([`native_locate_contract_bridge_par`](crate::native_locate_contract_bridge_par)) forwards the
//! automaton's located σ operands to that `Definition`'s channel — so the trusted evaluator runs
//! when the MACHINE's COMM dispatches it, and the rule's σ-receiver consumes the RETURNED value.
//! The f1r3node registry precedent holds: the handler is data injected one-way, no back-edge
//! (`BridgeInertness.v`).
//!
//! # Reserved MeTTaIL system-process bands (the SINGLE enumeration point)
//!
//! Every MeTTaIL-injected `Definition` lives on a reserved two-byte unforgeable channel
//! `GPrivate{id: [tag, index]}` and a reserved `body_ref` band. f1r3node's own bands are
//! single-byte channel ids (std 0–36, test-framework 101–108) and body_refs 0–36, so a two-byte
//! id can never collide with them; the two MeTTaIL bands are kept disjoint FROM EACH OTHER by
//! their leading tag byte (channels) and by non-overlapping `u8`-offset ranges (body_refs),
//! asserted by [`tests::mettail_system_process_bands_do_not_collide`]:
//!
//! | band                       | channel id            | body_ref range      |
//! |----------------------------|-----------------------|---------------------|
//! | held-fold trampoline       | `[0xF0, site_index]`  | `0xF000 + site`     |
//! | native-handler contract    | `[0xF1, rule_index]`  | `0xF100 + rule`     |
//!
//! `rholang-runtime/src/fold_contract.rs` and `rholang-runtime/src/native_contract.rs` both
//! import these constants — neither redeclares a band.
//!
//! FV: `formal/rocq/rho_bridge/theories/NativeSystemProcessBoundary.v` (section 4 — the A-S3
//! dispatch COMM: the emitted value is the REGISTERED HANDLER's output on the machine-captured
//! σ at COMM time) reusing the trampoline structure of `HeldFoldContractSound.v`.

use std::cell::RefCell;
use std::sync::Arc;

use models::rhoapi::g_unforgeable::UnfInstance::GPrivateBody;
use models::rhoapi::{GPrivate, GUnforgeable, Par};

use crate::rho_net_lower::GroundTerm;

/// First byte of every held-fold contract's unforgeable channel id `[0xF0, site_index]` — the
/// Tier-3 held-fold trampoline band (`rholang-runtime/src/fold_contract.rs` builds its channels
/// from this).
pub const MTL_FOLD_CHANNEL_TAG: u8 = 0xF0;

/// Reserved `body_ref` band base for held-fold contracts: `0xF000 + site_index` (site is `u8`,
/// so the band is `0xF000..=0xF0FF` — well clear of f1r3node's std 0–36 / test 101–108, and NOT
/// in `non_deterministic_ops()`: the folds are pure, dispatch is a `DeterministicCall`).
pub const MTL_FOLD_BODY_REF_BASE: i64 = 0xF000;

/// First byte of every A-S3 native-handler contract's unforgeable channel id
/// `[0xF1, rule_index]` — disjoint from the held-fold band by the leading tag byte.
pub const MTL_NATIVE_CHANNEL_TAG: u8 = 0xF1;

/// Reserved `body_ref` band base for A-S3 native-handler contracts: `0xF100 + rule_index`
/// (rule index is `u8`, so the band is `0xF100..=0xF1FF` — disjoint from the held-fold band
/// `0xF000..=0xF0FF`, from f1r3node's std/test refs, and NOT in `non_deterministic_ops()`:
/// a registrable native evaluator is a pure function of its σ operands, so dispatch is a
/// `DeterministicCall` and replay reproduces bit-identically).
pub const MTL_NATIVE_BODY_REF_BASE: i64 = 0xF100;

/// The unforgeable native-handler contract channel for a native rule index (two-byte private
/// name `[0xF1, rule_index]`). The co-installed contract-call bridge
/// ([`native_locate_contract_bridge_par`](crate::native_locate_contract_bridge_par)) sends the
/// located σ operands here, and the runtime installs the rule's handler `Definition` on it.
pub fn native_contract_channel(rule_index: u8) -> Par {
    Par::default().with_unforgeables(vec![GUnforgeable {
        unf_instance: Some(GPrivateBody(GPrivate {
            id: vec![MTL_NATIVE_CHANNEL_TAG, rule_index],
        })),
    }])
}

/// The reserved `body_ref` for a native rule index's handler `Definition`.
pub fn native_contract_body_ref(rule_index: u8) -> i64 {
    MTL_NATIVE_BODY_REF_BASE + rule_index as i64
}

/// The URN of a registered native-handler `Definition`: `mtl:native:{fingerprint}:{label}` —
/// the native band mirroring the held-fold URNs (`mtl:fold:{kind}:{width}#{site}`). `label` is
/// the Dovetail firing label (`"{Category}_{Label}"`, category-qualified so it is unique per
/// rule within the definition), and the fingerprint scopes the URN to one language definition.
pub fn native_handler_urn(language_fingerprint: &str, fired_rule_label: &str) -> String {
    format!("mtl:native:{language_fingerprint}:{fired_rule_label}")
}

/// The trusted machine-side native evaluator: the EXACT `![…] fold` body of the rule, compiled
/// by the `language!` macro into a pure function over the located σ operands (each a decoded
/// reflected [`GroundTerm`]). Returns the reduced value as a literal-leaf `GroundTerm`
/// (`"NumLit(8)"`), or `None` when the fold DEFERS — the same fold-gate semantics as the
/// D-stage dispatcher (`__class_is_fold_value` / `try_eval()?`): a non-value operand (a free
/// variable, an unevaluable subterm) or a safe-arithmetic decline (overflow, ÷0) leaves the
/// redex unreduced rather than fabricating a value.
pub type NativeHandlerEvaluator = Arc<dyn Fn(&[GroundTerm]) -> Option<GroundTerm> + Send + Sync>;

/// The static spec of ONE registrable native rule's machine-side handler contract — everything
/// the runtime needs to build the system-process `Definition` the dispatch COMM invokes
/// (`rholang-runtime/src/native_contract.rs::native_definition`). Recorded by the generated
/// report-free match body (`rho_net_match_invocation_to`) through the pending registry below,
/// drained by the runtime's invocation-compiler bracket, and injected via
/// `extra_system_processes` — exactly the held-fold trampoline's path.
#[derive(Clone)]
pub struct NativeHandlerSpec {
    /// The `Definition` URN (`mtl:native:{fingerprint}:{label}`, [`native_handler_urn`]).
    pub urn: String,
    /// The Dovetail firing label (`"{Category}_{Label}"`) — the rule identity.
    pub fired_rule_label: String,
    /// The BARE head label (`"PowInt"`) the automaton locates sites by.
    pub bare_label: String,
    /// The native rule's arity `k` — the located σ operand count. The `Definition` arity is
    /// `k + 1` (`[σ₀, …, σ_{k-1}, out]`).
    pub arity: usize,
    /// The language fingerprint the located σ operands arrive reflected under (the spread's
    /// collapse ABI) and the handler's result is reflected back under.
    pub fingerprint: String,
    /// The rule's index in the ruleset's `native_dispatch` order — keys the reserved channel
    /// `[0xF1, rule_index]` and `body_ref` deterministically, so replay installs the identical
    /// contract on the identical channel.
    pub rule_index: u8,
    /// The installed dispatch receiver's SOURCE channel name — the handler `produce`s
    /// `[value, out]` here, and the rule's σ-receiver (`for (result, out <- c) { out!(result) }`)
    /// consumes the RETURNED value.
    pub dispatch_channel: String,
    /// The trusted machine-side evaluator (the rule's own `fold` body).
    pub evaluator: NativeHandlerEvaluator,
}

impl std::fmt::Debug for NativeHandlerSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeHandlerSpec")
            .field("urn", &self.urn)
            .field("fired_rule_label", &self.fired_rule_label)
            .field("bare_label", &self.bare_label)
            .field("arity", &self.arity)
            .field("fingerprint", &self.fingerprint)
            .field("rule_index", &self.rule_index)
            .field("dispatch_channel", &self.dispatch_channel)
            .field("evaluator", &"<trusted native fold body>")
            .finish()
    }
}

thread_local! {
    // A-S3: the native-handler specs recorded by the CURRENT report-free invocation compile on
    // THIS thread. The runtime brackets every invocation-compiler run
    // (`backend.rs::clear_pending_fold_sites` / `drain_pending_fold_definitions`, the SAME
    // bracket the held-fold trampoline rides): cleared before the compile, drained right after
    // on the same thread, so nothing leaks across runs — and specs recorded by a compile that
    // ultimately DEFERS are drained-and-dropped harmlessly.
    static PENDING_NATIVE_HANDLER_SPECS: RefCell<Vec<NativeHandlerSpec>> =
        const { RefCell::new(Vec::new()) };
}

/// Record the native-handler specs of the current report-free invocation compile (called by the
/// generated `rho_net_match_invocation_to` once its admission is decided — never on a deferral
/// return path, though the runtime bracket would discard a stray record anyway).
pub fn record_pending_native_handler_specs(specs: Vec<NativeHandlerSpec>) {
    PENDING_NATIVE_HANDLER_SPECS.with(|cell| cell.borrow_mut().extend(specs));
}

/// Take (and clear) the pending native-handler specs recorded on this thread.
pub fn take_pending_native_handler_specs() -> Vec<NativeHandlerSpec> {
    PENDING_NATIVE_HANDLER_SPECS.with(|cell| std::mem::take(&mut *cell.borrow_mut()))
}

/// Clear the pending native-handler specs (the runtime bracket's opening half).
pub fn clear_pending_native_handler_specs() {
    PENDING_NATIVE_HANDLER_SPECS.with(|cell| cell.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reserved-band collision test the band table above promises: the held-fold and
    /// native-handler bands are disjoint from each other (channels by leading tag byte,
    /// body_refs by non-overlapping `u8`-offset ranges) and from f1r3node's own bands
    /// (single-byte channel ids std 0–36 / test 101–108; body_refs 0–36).
    #[test]
    fn mettail_system_process_bands_do_not_collide() {
        // Channel bands: both MeTTaIL bands are TWO-byte ids, so no single-byte f1r3node id
        // (std or test framework) can ever equal one; the two MeTTaIL bands differ in their
        // leading tag byte, so `[0xF0, a] != [0xF1, b]` for every `a`, `b`.
        assert_ne!(
            MTL_FOLD_CHANNEL_TAG, MTL_NATIVE_CHANNEL_TAG,
            "the held-fold and native-handler channel bands must differ in their leading tag byte"
        );
        for index in [0u8, 1, 42, u8::MAX] {
            let native = native_contract_channel(index);
            let [unforgeable] = native.unforgeables.as_slice() else {
                panic!("native contract channel is a single unforgeable");
            };
            let Some(GPrivateBody(private)) = unforgeable.unf_instance.as_ref() else {
                panic!("native contract channel is a GPrivate");
            };
            assert_eq!(
                private.id,
                vec![MTL_NATIVE_CHANNEL_TAG, index],
                "the native channel id is the two-byte [0xF1, rule_index]"
            );
            assert_eq!(private.id.len(), 2, "two-byte id: disjoint from every single-byte band");
        }

        // body_ref bands: the held-fold band is 0xF000..=0xF0FF (u8 site offset), the native
        // band 0xF100..=0xF1FF (u8 rule offset) — disjoint ranges, both far above f1r3node's
        // std body_refs 0–36.
        let fold_band = MTL_FOLD_BODY_REF_BASE..=MTL_FOLD_BODY_REF_BASE + u8::MAX as i64;
        let native_band = MTL_NATIVE_BODY_REF_BASE..=MTL_NATIVE_BODY_REF_BASE + u8::MAX as i64;
        assert!(
            fold_band.end() < native_band.start(),
            "the held-fold body_ref band must end before the native band starts \
             ({:#x} < {:#x})",
            fold_band.end(),
            native_band.start()
        );
        assert!(
            *fold_band.start() > 108,
            "both MeTTaIL body_ref bands sit above f1r3node's std (0-36) and test (101-108) refs"
        );
        assert_eq!(native_contract_body_ref(0), MTL_NATIVE_BODY_REF_BASE);
        assert_eq!(native_contract_body_ref(u8::MAX), MTL_NATIVE_BODY_REF_BASE + 255);
    }

    /// The pending registry is a clear/record/take bracket: record accumulates, take drains and
    /// clears, clear discards — the runtime's invocation-compiler bracket semantics.
    #[test]
    fn pending_native_handler_spec_registry_brackets() {
        clear_pending_native_handler_specs();
        let spec = NativeHandlerSpec {
            urn: native_handler_urn("mettail-langdef-v1:00", "Int_PowInt"),
            fired_rule_label: "Int_PowInt".to_string(),
            bare_label: "PowInt".to_string(),
            arity: 2,
            fingerprint: "mettail-langdef-v1:00".to_string(),
            rule_index: 0,
            dispatch_channel: "sa:scalar/PowInt".to_string(),
            evaluator: Arc::new(|_args| None),
        };
        record_pending_native_handler_specs(vec![spec.clone()]);
        record_pending_native_handler_specs(vec![spec]);
        let drained = take_pending_native_handler_specs();
        assert_eq!(drained.len(), 2, "record accumulates");
        assert!(take_pending_native_handler_specs().is_empty(), "take clears");

        record_pending_native_handler_specs(vec![NativeHandlerSpec {
            urn: "mtl:native:fp:X".to_string(),
            fired_rule_label: "X".to_string(),
            bare_label: "X".to_string(),
            arity: 0,
            fingerprint: "fp".to_string(),
            rule_index: 1,
            dispatch_channel: "c".to_string(),
            evaluator: Arc::new(|_args| None),
        }]);
        clear_pending_native_handler_specs();
        assert!(take_pending_native_handler_specs().is_empty(), "clear discards");
    }

    #[test]
    fn native_handler_urn_carries_the_mandated_band() {
        assert_eq!(
            native_handler_urn("mettail-langdef-v1:ab12", "Int_PowInt"),
            "mtl:native:mettail-langdef-v1:ab12:Int_PowInt",
            "URN band is mtl:native:{{fingerprint}}:{{label}}"
        );
    }
}
