//! Compile and execute the actual Rholang DDL depth-zero strategy constructors.
//!
//! Closed categories need a finite constructor tree, not necessarily a nullary
//! constructor. These checks exercise generated Rust and the generated parser;
//! macro-level source-syntax checks alone cannot establish either correspondence.
//! Positive-depth constructor coverage is a separate obligation.

#![cfg(all(feature = "rholang", feature = "strategies"))]

use mettail_languages::rholang::{strategies::*, *};

macro_rules! check_bases {
    ($($category:ident => $builder:ident),+ $(,)?) => {
        #[test]
        fn every_ddl_category_has_a_typed_roundtripping_depth_zero_base() {
            for tape in [&[][..], &[0; 32][..], &[255; 32][..]] {
                $(
                    let term: $category = $builder(&mut TapeReader::new(tape), 0);
                    let source = term.to_string();
                    let parsed = $category::parse(&source).unwrap_or_else(|error| {
                        panic!("{} base {source:?} failed to parse: {error:?}", stringify!($category))
                    });
                    assert_eq!(term, parsed, "{} base {source:?}", stringify!($category));
                )+
            }
        }
    };
}

check_bases! {
    DdlImports => build_ddlimports_from_tape,
    DdlImport => build_ddlimport_from_tape,
    DdlModuleItem => build_ddlmoduleitem_from_tape,
    DdlParam => build_ddlparam_from_tape,
    DdlPath => build_ddlpath_from_tape,
    DdlTheoryExpr => build_ddltheoryexpr_from_tape,
    DdlCatDecl => build_ddlcatdecl_from_tape,
    DdlExport => build_ddlexport_from_tape,
    DdlReplacement => build_ddlreplacement_from_tape,
    DdlTermRule => build_ddltermrule_from_tape,
    DdlBinding => build_ddlbinding_from_tape,
    DdlSort => build_ddlsort_from_tape,
    DdlSyntaxItem => build_ddlsyntaxitem_from_tape,
    DdlEquation => build_ddlequation_from_tape,
    DdlFreshnesses => build_ddlfreshnesses_from_tape,
    DdlFreshness => build_ddlfreshness_from_tape,
    DdlRewrite => build_ddlrewrite_from_tape,
    DdlPremises => build_ddlpremises_from_tape,
    DdlPremise => build_ddlpremise_from_tape,
    DdlRuleAstItems => build_ddlruleastitems_from_tape,
    DdlRuleAstRemainderTail => build_ddlruleastremaindertail_from_tape,
    DdlRuleAst => build_ddlruleast_from_tape,
}
