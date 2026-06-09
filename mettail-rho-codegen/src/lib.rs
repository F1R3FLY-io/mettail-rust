//! # mettail-rho-codegen — COMPILE-TIME GSLT → Rholang VM lowering
//!
//! MeTTaIL is the COMPILER; f1r3node-rust's Rho machine is the parallel RUNTIME.
//! This crate lowers a MeTTaIL `LanguageDef` into a **parallel-optimized Rholang
//! VM** — three artifacts:
//!  1. reduction rules as `Par` contracts (the COMM family),
//!  2. native `Vec<Definition>` system processes (HOL `fold`/`step`),
//!  3. the `OslfResourceLogic` adapter wiring (see `mettail-rho-adapter`).
//!
//! Rule classification drives the lowering: COMM/interaction → RSpace
//! produce/consume; structural/congruence → par-context (`eval_par` — the AMBIENT
//! structural rule, emit `Par`, never fork); HOL `fold`/`step` → native
//! `Definition` handler; equations → compile-time e-graph; injection/cast → `Par`
//! wrapper. The e-graph / WTA / decision-tree remain **compile-time analyses**
//! that GENERATE indexing + ordering + recognition plugging into f1r3node's
//! existing matcher/join/lock/`check_commit` — speed + parallelism without
//! forking the runtime.
//!
//! ## Dependency direction (STRICTLY one-way)
//! Depends ONE-WAY on f1r3node-rust; never the reverse (proven in
//! `formal/rocq/rho_bridge/theories/BridgeInertness.v`; enforced by the host
//! guard test `mettail_rust_is_not_a_cargo_dependency`).
//!
//! ## Status
//! Skeleton — fully integrated, NOT feature-gated (no f1r3node deps yet; they land
//! with the code that uses them). M-RHO.0.3 adds the pure `LanguageDef → Rholang`
//! translator (`lower_term_to_rholang` / `lower_rule_to_rholang`) consumed by a new
//! `macros::gen::runtime::rho_vm::generate_rho_vm` sibling of `generate_ascent_source`,
//! plus the `rholang` dep for a parse round-trip (`Compiler::source_to_adt → Par == Ok`),
//! and the totality-or-explicit-rejection proof `RhoLoweringTotalOrRejects.v`
//! (out-of-subset constructors are REFUSED, never silently dropped — "miss
//! nothing" at the codegen layer).

#![forbid(unsafe_code)]

pub mod lower;
pub use lower::{lower_language_def, RhoLowering};

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::LanguageDef;
    use rholang::rust::interpreter::compiler::compiler::Compiler;

    // The calculator's scalar-operator fragment, by its real rule names. Body-less
    // (the lowering keys on the concrete-syntax operator + operand types, not the
    // `![…]` eval body), so this parses by `syn::parse_str` without validation.
    // First block = Rholang-native scalar ops (lower to contracts); last four =
    // out-of-subset (`^`/`bitand` have no Rholang op; `!` is postfix; `AddBigInt`
    // has non-native BigInt operands) and MUST be rejected, never silently dropped.
    const CALC_SCALAR_FRAGMENT: &str = r#"
        name: CalcScalarFrag,
        types { Proc }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            SubInt . a:Int, b:Int |- a "-" b : Int ;
            MulInt . a:Int, b:Int |- a "*" b : Int ;
            DivInt . a:Int, b:Int |- a "/" b : Int ;
            ModInt . a:Int, b:Int |- a "%" b : Int ;
            Neg . a:Int |- "-" a : Int ;
            EqInt . a:Int, b:Int |- a "==" b : Bool ;
            NeInt . a:Int, b:Int |- a "!=" b : Bool ;
            LtInt . a:Int, b:Int |- a "<" b : Bool ;
            And . a:Bool, b:Bool |- a "and" b : Bool ;
            Not . a:Bool |- "not" a : Bool ;
            PowInt . a:Int, b:Int |- a "^" b : Int ;
            BitAndInt . a:Int, b:Int |- a "bitand" b : Int ;
            Fact . a:Int |- a "!" : Int ;
            AddBigInt . a:BigInt, b:BigInt |- a "+" b : BigInt ;
        }
    "#;

    fn parse_fragment() -> LanguageDef {
        syn::parse_str::<LanguageDef>(CALC_SCALAR_FRAGMENT)
            .expect("calculator scalar fragment must parse as a LanguageDef")
    }

    #[test]
    fn lowers_supported_scalar_ops_and_rejects_the_rest() {
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert_eq!(
            out.lowered,
            vec![
                "AddInt", "SubInt", "MulInt", "DivInt", "ModInt", "Neg", "EqInt", "NeInt",
                "LtInt", "And", "Not",
            ],
            "Rholang-native scalar ops must lower to contracts"
        );
        assert_eq!(
            out.rejected,
            vec!["PowInt", "BitAndInt", "Fact", "AddBigInt"],
            "out-of-subset rules must be rejected (surfaced), never silently dropped"
        );
    }

    #[test]
    fn lowering_is_total_and_disjoint() {
        // Miss nothing: every term rule is accounted for in exactly one of
        // lowered / rejected (the operational image of RhoLoweringTotalOrRejects.v).
        let def = parse_fragment();
        let out = lower_language_def(&def);
        assert_eq!(
            out.lowered.len() + out.rejected.len(),
            def.terms.len(),
            "every rule must be classified exactly once (total)"
        );
        for name in &out.lowered {
            assert!(!out.rejected.contains(name), "lowered/rejected must be disjoint: {name}");
        }
    }

    #[test]
    fn emitted_rholang_parses_via_host_compiler() {
        // The parse round-trip gate: the lowered Rholang is well-formed (normalizes
        // to a Par) under f1r3node-rust's own compiler.
        let def = parse_fragment();
        let out = lower_language_def(&def);
        let result = Compiler::source_to_adt(&out.source);
        assert!(
            result.is_ok(),
            "lowered Rholang must parse via Compiler::source_to_adt; source:\n{}\nerr: {:?}",
            out.source,
            result.err()
        );
    }
}
