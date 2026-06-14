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
