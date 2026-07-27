//! The canary for `language!` DISCOVERY — a definition in a top-level
//! `languages/tests/*.rs`, which is exactly where a definition used to escape the
//! formal requirements audit.
//!
//! ## What this file is for
//!
//! `dovetail/tests/language_inventory.rs` and `ast/tests/dovetail_language_inventory.rs`
//! assert that the set of `language!` definitions they discover EQUALS the inventory in
//! `dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v`. Those scans used
//! to enumerate two directories — `languages/src` and `languages/tests/definitions` — so
//! a definition written anywhere else was in neither, and its equations, rewrites,
//! folds and premises carried no formal requirements entry while every test stayed
//! green.
//!
//! That was not a hypothetical. `Pi` and `Turing` (equations, rewrites, a freshness
//! premise, a substituting COMM; a native fold and two transition rewrites) sat outside
//! formal coverage in `languages/tests/omnibus_*.rs` until `e1bfcd38` relocated them,
//! and `L9FltToy`/`L9ModalToy` — each with a `step` rewrite and native `![…]` actions —
//! sat outside it in `languages/tests/l9_*_toy.rs` until the scan was widened to the
//! whole package.
//!
//! `DiscoveryCanary` is the standing witness that the widening holds. It is inventoried
//! like any other reduction language, so if the roots ever narrow again — or if a
//! `bin`/`generated`-style skip is reintroduced over this directory — the inventory
//! equality fails immediately and names it, instead of a real language silently losing
//! its formal coverage some months later.
//!
//! It is deliberately the smallest language that carries a requirement: one native
//! carrier and one `step` rule whose `![…]` action makes it a native fold. Being tiny
//! keeps its macro expansion cheap, and being REAL (it parses and evaluates below)
//! keeps it from rotting into an unexercised fixture.

#![allow(unused_imports, dead_code)]

use mettail_macros::language;
use mettail_runtime::Language;

language! {
    name: DiscoveryCanary,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i64] as Num
    },

    terms {
        AddNum . a:Num, b:Num |- a "+" b : Num ![a + b] step;
    },
}

#[test]
fn canary_language_is_registered() {
    assert_eq!(DiscoveryCanaryLanguage.name(), "DiscoveryCanary");
}

#[test]
fn canary_language_parses_and_evaluates() {
    mettail_runtime::clear_var_cache();
    let term = Num::parse("1 + 2").expect("the canary grammar parses its one rule");
    assert_eq!(format!("{term}"), "1 + 2");
}
