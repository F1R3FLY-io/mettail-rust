//! Minimal typed-Dovetail fixture for whole collection-literal categories.
//!
//! `ForceTyped` is deliberately a non-native-output fold. Its presence selects
//! the generated typed Dovetail backend. The independent `Control` rewrite
//! makes the production normal-form entry point available and demonstrates
//! that the fixture exercises a live structural-rewrite backend. The
//! collection values tested by the companion integration suite remain
//! redex-free, and their zero-iteration structural round trip therefore
//! isolates collection lowering and reconstruction from saturation.
//!
//! `A` and `B` intentionally share the same displayed surface, `x`. They are
//! distinct constructors and therefore distinct semantic terms. This makes
//! display-only collection identity collide while exact structural child keys
//! remain different.

#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: StructuralCollectionDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        ![Vec<Proc>] as List {
            open_parts: ["["],
            close_parts: ["]"],
            sep: ",",
        }
        ![mettail_runtime::HashBag<Proc>] as Bag {
            open_parts: ["#{"],
            close_parts: ["}#"],
            sep: "|",
        }
        ![mettail_runtime::HashSetLit<Proc>] as Set {
            open_parts: ["Set("],
            close_parts: [")"],
            sep: ",",
        }
        ![mettail_runtime::HashMapLit<Proc, Proc>] as Map {
            open_parts: ["{"],
            close_parts: ["}"],
            sep: ",",
            key_val_sep: ":",
        }
        ![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap {
            open_parts: ["pathmap("],
            close_parts: [")"],
            sep: ",",
            key_val_sep: ":",
        }
    },

    terms {
        A . |- "x" : Proc;
        B . |- "x" : Proc;
        C . p:Proc |- "c" "(" p ")" : Proc;
        D . |- "d" : Proc;

        // Selects the typed backend without changing any collection term used
        // by the structural tests.
        ForceTyped . p:Proc |- "force" "(" p ")" : Proc ![{
            match p {
                Proc::A => Proc::B,
                _ => Proc::A,
            }
        }] fold;
    },

    equations {},
    rewrites {
        Control . |- (C p) ~> D;
    },
}
