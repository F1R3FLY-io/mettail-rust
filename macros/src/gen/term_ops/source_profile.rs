//! Source-profile correspondence against the actual generated enums.
//!
//! This census consumes the host-owned source-profile macro rows: exact
//! categories and constructors, complete original Rust field sequences, and
//! explicit role transitions or opaque slots. It does not itself run the gate.
//! The existing classifier determines carriers.
//! T = term, N = name, P = receive pattern, PN = name-shaped receive pattern,
//! G = guard, D = declaration, I = inherit, Q = quote (PN -> P, otherwise T),
//! B = Boolean operand (G -> G, otherwise T).
//!
//! The observer emitted by checked_source.rs uses RholangSourceImports'
//! hereditary worklist laws with original borrowed occurrences plus these
//! roles. Concrete source association for its paid scheduling, policy dispatch,
//! projections and collection scans is a separate obligation: this census
//! establishes constructor/field correspondence only, not runtime verification.
//!
//! Scheduling/charging recipe emitted by checked_source.rs:
//! - A single Vec retains typed borrowed jobs (original reference and role).
//!   Prepay reserve_binding_parts(3, 2, 0) before Vec/ordinal initialization
//!   and eventual flat Vec disposal. Schedule the root through the same push
//!   rule as every child; aliases are separate occurrences, without cloning.
//! - Before every pop, including the terminal None, prepay (1, 0, 0).
//!   Before matching a popped category/constructor and checking/incrementing
//!   its occurrence ordinal, prepay (3, 1, 0). Use checked_add; overflow fails
//!   closed, retains previous charges, and yields no successful witness.
//! - Separately prepay (2, 1, 0) before policy dispatch and field-slice retention.
//!   Refuse an unlisted constructor before helper selection, payload match or
//!   child projection. Prepay (3, 1, 0) for helper selection and pointer
//!   retention, its call, and its single payload match. No inline constructor
//!   bodies accumulate in the category frame: one common call selects a
//!   noinline per-constructor helper, which only appends borrowed jobs and
//!   never recursively visits children. The earlier tag-only match does not
//!   also pay for this dispatch. Selection preserves the helpers' higher-ranked
//!   source lifetime and instantiates it at the call, without lifetime erasure.
//! - For a supported carrier recipe, prepay (1, 0, 0) for the field-count
//!   check, then (1, 0, 0) per original slot to check its child/opaque mask.
//!   Reject an invalid policy before child traversal. Prepay (2, 1, 0) before
//!   selecting and applying each child field's role transition. Collection
//!   elements share that original slot's role; Map keys and values both use it.
//!   The policy contract requires constant-time, side-effect-free dispatch and
//!   transitions, as supplied by the host table; these charges do not bound
//!   arbitrary user-provided callback computation.
//! - Before retaining the current batch-start index, prepay (1, 1, 0).
//!   Before each original child/collection/scope-body projection prepay
//!   (1, 0, 0). Scope::unsafe_body is a safe Rust borrowed accessor here;
//!   binder patterns are metadata, never opened, cloned, or freshened.
//! - Before constructing/pushing each borrowed job prepay (3, 1, 0): one
//!   construction, one push, and one eventual flat disposal. Opaque String,
//!   native scalar and FltNode payloads have no host-child jobs or inspection.
//! - Vec fields: prepay (1, 1, 0) for iterator setup, then (1, 0, 0) before
//!   every next, including None. Map/Bag fields instead call the existing
//!   try_for_each_entry with the same callback; their paid setup/next/native
//!   scan is not charged a second time. The visitor pays the child projection
//!   and push groups above. Append Map key then value; append each Bag key
//!   once even at count zero, in unchanged native representation order.
//! - Append fields and elements in original declaration/representation order,
//!   then reverse ONLY the newly appended batch using the existing paid
//!   reversal template: (3, 2, 0) setup; (1, 0, 0) each guard including the
//!   terminal guard; (6, 1, 0) each endpoint swap. Keep checked_sub/checked_add
//!   exactly as reverse_binding_task_batch. This choice reuses the existing
//!   paid callback scans without a new lifetime-erased iterator mechanism.
//! - A normal refusal discards only flat borrowed jobs using their prepaid
//!   disposal work, with no further fallible reservation or AST Drop. All
//!   numbers denote logical source groups/records, not allocator byte bounds.
//!   reserve_binding_parts checks work+owned_bytes and 4*records+owned_bytes;
//!   its callback is the caller's existing ReflectedCodecBudget::charge.
//!
//! Law association: RholangInitialGraphResources::precharged_action and its
//! cancellation/refusal/no-refund/exact-success laws apply at every group;
//! SourceMapEntryVisit preserves the original pair prefix and paid advances;
//! NativeHashBagEntryVisit preserves original keys/counts and paid sparse
//! scans. PaidTaskBatchReversal::completed_exterior_is_unchanged and
//! lifo_visits_original_batch give the exact children ++ pending pop order
//! required by RholangSourceImports::accepted_step_preserves_every_ordered_child_occurrence.
//! These existing laws provide the abstract proof basis; their presence does
//! not by itself verify checked_source.rs or the host insertion. Concrete
//! generated-source association, first-refusal diagnostics, reservation cuts,
//! and runtime integration require their own checks. This census must not be
//! reported as proof that the public preparation path has passed those checks.

#[path = "../../../../languages/src/rholang/source_profile_policy.rs"]
mod policy;

#[path = "source_profile_tests.rs"]
mod tests;
