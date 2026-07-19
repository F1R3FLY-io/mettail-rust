use mettail_ast::language::LanguageDef;
use quote::quote;
use syn::parse2;

#[test]
fn minirho_for_doc_example_parses_as_language_def() {
    let language = parse2::<LanguageDef>(quote! {
        name: MiniRhoFor,

        options {
            emit_simulator: false,
            emit_blockly: false,
        },

        types {
            Proc
            Name
        },

        terms {
            PZero . |- "0" : Proc ;

            PPar . ps:HashBag(Proc)
                |- "{" ps.*sep("|") "}" : Proc ;

            POutput . n:Name, q:Name
                |- n "!" "(" q ")" : Proc ;

            PFor . n:Name, ^x.p:[Name -> Proc]
                |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
        },

        equations {},

        rewrites {
            Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
                ~> (PPar {(eval cont Q), ...rest});

            ParCong . | S ~> T
                |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
        }
    })
    .expect("MiniRhoFor doc example must parse as a LanguageDef");

    mettail_ast::validation::validate_language(&language)
        .expect("MiniRhoFor doc example must satisfy language validation");

    assert_eq!(language.name.to_string(), "MiniRhoFor");

    let types = language
        .types
        .iter()
        .map(|ty| ty.name.to_string())
        .collect::<Vec<_>>();
    assert_eq!(types, ["Proc", "Name"]);

    assert!(language
        .terms
        .iter()
        .any(|term| term.label.to_string() == "PFor"));
    assert!(language
        .terms
        .iter()
        .any(|term| term.label.to_string() == "POutput"));
    assert!(language
        .rewrites
        .iter()
        .any(|rewrite| rewrite.name.to_string() == "Comm"));
}

/// TriDemo is doc 28 §6's worked multi-rule language: three base rewrites whose
/// second and third left-hand sides share the whole `Pair(x, y)` sub-pattern, so
/// the one compiled set automaton interns 8 states from 11 raw pattern nodes
/// (three interner hits — the shared state). The interning trace, dispatch map,
/// and serializer routing are documented in
/// `docs/architecture/rho-native-integration/28-translation-rule-system.md`;
/// the state count and both admission gates are pinned by
/// `rholang-codegen/tests/doc28_golden_listing.rs`.
#[test]
fn tri_demo_doc_example_parses_as_language_def() {
    let language = parse2::<LanguageDef>(quote! {
        name: TriDemo,

        options {
            emit_simulator: false,
            emit_blockly: false,
        },

        types {
            Term
        },

        terms {
            Pair . a:Term, b:Term |- "pair" "(" a "," b ")" : Term ;
            Swap . a:Term, b:Term |- "swap" "(" a "," b ")" : Term ;
            Wrap . t:Term |- "wrap" "(" t ")" : Term ;
            Flip . t:Term |- "flip" "(" t ")" : Term ;
        },

        equations {},

        rewrites {
            SwapRule . |- (Swap a b) ~> (Pair b a) ;
            WrapRule . |- (Wrap (Pair x y)) ~> (Pair x y) ;
            FlipRule . |- (Flip (Pair x y)) ~> (Pair y x) ;
        }
    })
    .expect("TriDemo doc example must parse as a LanguageDef");

    mettail_ast::validation::validate_language(&language)
        .expect("TriDemo doc example must satisfy language validation");

    assert_eq!(language.name.to_string(), "TriDemo");
    assert_eq!(
        language
            .rewrites
            .iter()
            .map(|rewrite| rewrite.name.to_string())
            .collect::<Vec<_>>(),
        ["SwapRule", "WrapRule", "FlipRule"],
        "doc 28 §6.2's interning trace assumes this rewrite (= compile) order",
    );
}
