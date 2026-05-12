//! Phase 4 #5b (2026-05-12): Class-2 SimpleCollection HashMap smoke grammar.
//!
//! Exercises a HashMap collection slot in a Class-2 binder rule. The
//! walker's 3-phase `kv_phase` dispatch parses `(k0 : v0 , k1 : v1 , ...)`
//! sequences: phase 0 (outer dispatch — close / `,` / first-key element),
//! phase 1 (Consume `:`), phase 2 (Push CategoryEntry for value parse).
//! The walker's `set_cursor_inner_state` patches `kv_phase` based on
//! `cursor.collection_stack[acc_id].len()` parity AND the per-slot
//! `kv_separator_for_collection` engine query.
//!
//! Grammar:
//!   ChooseMap . a:Proc, ms:HashMap(Proc, Proc)
//!       |- "chooseMap" a "(" ms.*sep(",") ")" : Proc;
//!
//! Note: `HashMap(Proc, Proc)` is the parseable form — the parser
//! requires explicit key + value types per `ast/src/types.rs::128-144`.
//! `classify_binder` (extended Phase 4 #5b) lowers same-K-V `TypeExpr::Map`
//! to `SimpleCollection { coll_kind: HashMap, elem_cat }` mirroring
//! Class-5's invariant.
//!
//! Expected behavior:
//! - PRED-1 empty `chooseMap 0 ( )` → `ChooseMap(Box<PZero>, HashMapLit::default())`.
//! - PRED-2 singleton `chooseMap 0 ( 0 : 0 )` → `ChooseMap(Box<PZero>, {PZero: PZero})`.
//! - PRED-3 two pairs `chooseMap 0 ( 0 : 0 , 0 : 0 )` →
//!     `ChooseMap(Box<PZero>, {PZero: PZero})` (HashMap dedups identical keys
//!     so len after second insert remains 1).

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2HashMapSmoke,

    types {
        Proc
    },

    terms {
        PZero . |- "0" : Proc;

        ChooseMap . a:Proc, ms:HashMap(Proc, Proc)
            |- "chooseMap" a "(" ms.*sep(",") ")" : Proc;
    },

    equations {},

    rewrites {},
}
