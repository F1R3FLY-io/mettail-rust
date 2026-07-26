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

// Task #11 (extended 2026-07-26): as a library module this definition inherited
// `languages/src/lib.rs`'s crate-level `#![allow(unused_imports, ...)]`. A `#[path]`-included
// module inherits nothing, and each consumer exercises a different slice of the generated
// surface (the parser, the codegen helpers, or neither), so `dead_code` / `unused_imports`
// are expected here rather than a signal. They are allowed at the definition -- the one place
// every consumer shares -- instead of being re-allowed at each `#[path]` site.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Class2HashMapSmoke,

    options {
        // Task #11 (extended 2026-07-26): this is a NON-PRODUCTION language definition
        // (`languages/src/` is production-only), so it lives in
        // `languages/tests/definitions/`. The key tells the macro to emit the generated
        // suite INLINE (the opt-in `class2hashmapsmoke_generated_tests!` wrapper) instead of writing
        // `languages/tests/gen_class2hashmapsmoke_*.rs`, whose `use mettail_languages::class2hashmapsmoke::*;`
        // header cannot resolve once the definition has left the library; it also gives the
        // simulation CLI a `#[path]` prologue instead of that same library import.
        hosted_in: "tests/definitions/class2hashmapsmoke.rs",
    },

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
