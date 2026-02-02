#[cfg(test)]
mod tests {
    use crate::ast::grammar::{GrammarItem, TermParam};
    use crate::ast::grammar::{PatternOp, SyntaxExpr};
    use crate::ast::language::LanguageDef;
    use crate::ast::types::{CollectionType, TypeExpr};
    use quote::quote;
    use syn::{parse2, Ident};

    #[test]
    fn parse_hashbag_simple() {
        let input = quote! {
            name: TestBag,
            types { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "|" ;
                EZero . Elem ::= "0" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse HashBag: {:?}", result.err());

        let language = result.unwrap();
        assert_eq!(language.name.to_string(), "TestBag");
        assert_eq!(language.terms.len(), 2);

        // Check EBag has a Collection item
        let ebag = &language.terms[0];
        assert_eq!(ebag.label.to_string(), "EBag");
        assert_eq!(ebag.items.len(), 1);

        match &ebag.items[0] {
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => {
                assert_eq!(*coll_type, CollectionType::HashBag);
                assert_eq!(element_type.to_string(), "Elem");
                assert_eq!(separator, "|");
                assert!(delimiters.is_none());
            },
            _ => panic!("Expected Collection item"),
        }
    }

    #[test]
    fn parse_collection_with_delimiters() {
        let input = quote! {
            name: TestList,
            types { Elem }
            terms {
                EList . Elem ::= Vec(Elem) sep "," delim "[" "]" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse Vec with delimiters: {:?}", result.err());

        let language = result.unwrap();
        let elist = &language.terms[0];

        match &elist.items[0] {
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                assert_eq!(*coll_type, CollectionType::Vec);
                assert_eq!(separator, ",");
                assert_eq!(delimiters.as_ref().unwrap(), &("[".to_string(), "]".to_string()));
            },
            _ => panic!("Expected Collection item with delimiters"),
        }
    }

    #[test]
    fn parse_hashset_collection() {
        let input = quote! {
            name: TestSet,
            types { Elem }
            terms {
                ESet . Elem ::= HashSet(Elem) sep "," delim "{" "}" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse HashSet: {:?}", result.err());

        let language = result.unwrap();
        let eset = &language.terms[0];

        match &eset.items[0] {
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                assert_eq!(*coll_type, CollectionType::HashSet);
                assert_eq!(separator, ",");
                assert_eq!(delimiters.as_ref().unwrap(), &("{".to_string(), "}".to_string()));
            },
            _ => panic!("Expected HashSet collection"),
        }
    }

    #[test]
    fn parse_collection_error_empty_separator() {
        let input = quote! {
            name: TestBad,
            types { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_err(), "Should reject empty separator");
        let err = result.err().unwrap();
        assert!(err.to_string().contains("separator cannot be empty"));
    }

    #[test]
    fn parse_collection_error_missing_sep() {
        let input = quote! {
            name: TestBad,
            types { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) "|" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_err(), "Should require 'sep' keyword");
        // The error will be about unexpected token, not specifically about 'sep'
        // Just verify it fails to parse
    }

    // =========================================================================
    // TypeExpr Tests
    // =========================================================================

    #[test]
    fn parse_type_expr_base() {
        let input = quote! { Name };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse base type: {:?}", result.err());

        let ty = result.unwrap();
        assert!(matches!(ty, TypeExpr::Base(ident) if ident == "Name"));
    }

    #[test]
    fn parse_type_expr_arrow() {
        let input = quote! { [Name -> Proc] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse arrow type: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                assert!(matches!(*domain, TypeExpr::Base(ref id) if id == "Name"));
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "Proc"));
            },
            _ => panic!("Expected Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_nested_arrow() {
        // Higher-order: [[A -> B] -> C]
        let input = quote! { [[A -> B] -> C] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse nested arrow: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "C"));
                match *domain {
                    TypeExpr::Arrow {
                        domain: inner_domain,
                        codomain: inner_codomain,
                    } => {
                        assert!(matches!(*inner_domain, TypeExpr::Base(ref id) if id == "A"));
                        assert!(matches!(*inner_codomain, TypeExpr::Base(ref id) if id == "B"));
                    },
                    _ => panic!("Expected inner Arrow type"),
                }
            },
            _ => panic!("Expected outer Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_multi_binder() {
        // [Name* -> Proc] is an arrow with MultiBinder domain
        let input = quote! { [Name* -> Proc] };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse multi-binder: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Arrow { domain, codomain } => {
                match *domain {
                    TypeExpr::MultiBinder(inner) => {
                        assert!(matches!(*inner, TypeExpr::Base(ref id) if id == "Name"));
                    },
                    _ => panic!("Expected MultiBinder domain, got {:?}", domain),
                }
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "Proc"));
            },
            _ => panic!("Expected Arrow type"),
        }
    }

    #[test]
    fn parse_type_expr_standalone_multi_binder() {
        // Name* without arrow context
        let input = quote! { Name* };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse standalone multi-binder: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::MultiBinder(inner) => {
                assert!(matches!(*inner, TypeExpr::Base(ref id) if id == "Name"));
            },
            _ => panic!("Expected MultiBinder type, got {:?}", ty),
        }
    }

    #[test]
    fn parse_type_expr_collection_vec() {
        let input = quote! { Vec(Name) };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse Vec: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Collection { coll_type, element } => {
                assert_eq!(coll_type, CollectionType::Vec);
                assert!(matches!(*element, TypeExpr::Base(ref id) if id == "Name"));
            },
            _ => panic!("Expected Collection type"),
        }
    }

    #[test]
    fn parse_type_expr_collection_hashbag() {
        let input = quote! { HashBag(Proc) };
        let result = parse2::<TypeExpr>(input);
        assert!(result.is_ok(), "Failed to parse HashBag: {:?}", result.err());

        let ty = result.unwrap();
        match ty {
            TypeExpr::Collection { coll_type, element } => {
                assert_eq!(coll_type, CollectionType::HashBag);
                assert!(matches!(*element, TypeExpr::Base(ref id) if id == "Proc"));
            },
            _ => panic!("Expected Collection type"),
        }
    }

    // =========================================================================
    // TypeContext and Type Checking Tests
    // =========================================================================

    fn make_base_type(name: &str) -> TypeExpr {
        TypeExpr::Base(Ident::new(name, proc_macro2::Span::call_site()))
    }

    fn make_arrow_type(domain: TypeExpr, codomain: TypeExpr) -> TypeExpr {
        TypeExpr::Arrow {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    // =========================================================================
    // Constructor Signature and Apply Type Inference Tests
    // =========================================================================

    fn make_collection_type(coll_type: CollectionType, element: TypeExpr) -> TypeExpr {
        TypeExpr::Collection { coll_type, element: Box::new(element) }
    }

    // =========================================================================
    // New Constructor Syntax Tests (Judgement-style)
    // =========================================================================

    #[test]
    fn parse_new_syntax_simple() {
        // Simple parameter: n:Name |- n : Name ;
        let input = quote! {
            name: TestSimple,
            types { Name }
            terms {
                NVar . n:Name |- n : Name ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse new syntax: {:?}", result.err());

        let language = result.unwrap();
        assert_eq!(language.terms.len(), 1);

        let rule = &language.terms[0];
        assert_eq!(rule.label.to_string(), "NVar");
        assert_eq!(rule.category.to_string(), "Name");
        assert!(rule.term_context.is_some());
        assert!(rule.syntax_pattern.is_some());

        let ctx = rule.term_context.as_ref().unwrap();
        assert_eq!(ctx.len(), 1);
        match &ctx[0] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "n");
                assert!(matches!(ty, TypeExpr::Base(id) if id == "Name"));
            },
            _ => panic!("Expected Simple param"),
        }
    }

    #[test]
    fn parse_new_syntax_abstraction() {
        // Abstraction: n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
        // All syntax literals must be quoted strings; only parameter references are unquoted
        let input = quote! {
            name: TestAbs,
            types { Proc Name }
            terms {
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse abstraction syntax: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];

        assert_eq!(rule.label.to_string(), "PInput");
        assert_eq!(rule.category.to_string(), "Proc");

        let ctx = rule.term_context.as_ref().unwrap();
        assert_eq!(ctx.len(), 2);

        // First param: n:Name
        match &ctx[0] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "n");
                assert!(matches!(ty, TypeExpr::Base(id) if id == "Name"));
            },
            _ => panic!("Expected Simple param for n"),
        }

        // Second param: ^x.p:[Name -> Proc]
        match &ctx[1] {
            TermParam::Abstraction { binder, body, ty } => {
                assert_eq!(binder.to_string(), "x");
                assert_eq!(body.to_string(), "p");
                match ty {
                    TypeExpr::Arrow { domain, codomain } => {
                        assert!(matches!(domain.as_ref(), TypeExpr::Base(id) if id == "Name"));
                        assert!(matches!(codomain.as_ref(), TypeExpr::Base(id) if id == "Proc"));
                    },
                    _ => panic!("Expected Arrow type"),
                }
            },
            _ => panic!("Expected Abstraction param for ^x.p"),
        }

        // Check syntax pattern
        let pattern = rule.syntax_pattern.as_ref().unwrap();
        // Should have: Literal("for"), Literal("("), Param(x), Literal("<-"), Param(n), Literal(")"), Literal("{"), Param(p), Literal("}")
        assert_eq!(pattern.len(), 9, "Pattern should have 9 tokens");
        assert!(matches!(&pattern[0], SyntaxExpr::Literal(s) if s == "for"));
        assert!(matches!(&pattern[1], SyntaxExpr::Literal(s) if s == "("));
        assert!(matches!(&pattern[2], SyntaxExpr::Param(id) if id == "x"));
        assert!(matches!(&pattern[3], SyntaxExpr::Literal(s) if s == "<-"));
        assert!(matches!(&pattern[4], SyntaxExpr::Param(id) if id == "n"));
        assert!(matches!(&pattern[5], SyntaxExpr::Literal(s) if s == ")"));
        assert!(matches!(&pattern[6], SyntaxExpr::Literal(s) if s == "{"));
        assert!(matches!(&pattern[7], SyntaxExpr::Param(id) if id == "p"));
        assert!(matches!(&pattern[8], SyntaxExpr::Literal(s) if s == "}"));
    }

    #[test]
    fn parse_new_syntax_multi_abstraction() {
        // Multi-binder: ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- ...
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestMulti,
            types { Proc Name }
            terms {
                PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- "inputs" "(" xs "," ns ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse multi-abstraction: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];

        let ctx = rule.term_context.as_ref().unwrap();
        assert_eq!(ctx.len(), 2);

        // First param: ns:Vec(Name)
        match &ctx[0] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "ns");
                match ty {
                    TypeExpr::Collection { coll_type, element } => {
                        assert_eq!(*coll_type, CollectionType::Vec);
                        assert!(matches!(element.as_ref(), TypeExpr::Base(id) if id == "Name"));
                    },
                    _ => panic!("Expected Collection type"),
                }
            },
            _ => panic!("Expected Simple param for ns"),
        }

        // Second param: ^[xs].p:[Name* -> Proc]
        match &ctx[1] {
            TermParam::MultiAbstraction { binder, body, ty } => {
                assert_eq!(binder.to_string(), "xs");
                assert_eq!(body.to_string(), "p");
                match ty {
                    TypeExpr::Arrow { domain, codomain } => {
                        assert!(matches!(domain.as_ref(), TypeExpr::MultiBinder(_)));
                        assert!(matches!(codomain.as_ref(), TypeExpr::Base(id) if id == "Proc"));
                    },
                    _ => panic!("Expected Arrow type"),
                }
            },
            _ => panic!("Expected MultiAbstraction param"),
        }
    }

    #[test]
    fn parse_old_syntax_still_works() {
        // Old syntax should still work
        let input = quote! {
            name: TestOld,
            types { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Old syntax should still work: {:?}", result.err());

        let language = result.unwrap();
        assert_eq!(language.terms.len(), 2);

        // Old syntax should have term_context = None
        assert!(language.terms[0].term_context.is_none());
        assert!(language.terms[1].term_context.is_none());
    }

    #[test]
    fn parse_mixed_syntax() {
        // Mix of old and new syntax
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestMixed,
            types { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Mixed syntax should work: {:?}", result.err());

        let language = result.unwrap();

        // First rule: old syntax
        assert!(language.terms[0].term_context.is_none());

        // Second rule: new syntax
        assert!(language.terms[1].term_context.is_some());
    }

    // =========================================================================
    // Syntax Pattern Token Tests
    // =========================================================================

    #[test]
    fn test_syntax_pattern_content() {
        // Verify the syntax pattern is captured correctly
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestPattern,
            types { Proc Name }
            terms {
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok());

        let language = result.unwrap();
        let rule = &language.terms[0];

        let pattern = rule.syntax_pattern.as_ref().unwrap();

        // Pattern should be: Literal("for"), Literal("("), Param(x), Literal("<-"), Param(n), ...
        // Find parameter references (unquoted identifiers) in the pattern
        let param_refs: Vec<_> = pattern
            .iter()
            .filter_map(|t| match t {
                SyntaxExpr::Param(id) => Some(id.to_string()),
                _ => None,
            })
            .collect();

        // Only parameter references should be Param tokens (not "for" which is Literal)
        assert!(param_refs.contains(&"x".to_string()), "Should contain param 'x'");
        assert!(param_refs.contains(&"n".to_string()), "Should contain param 'n'");
        assert!(param_refs.contains(&"p".to_string()), "Should contain param 'p'");
        assert!(!param_refs.contains(&"for".to_string()), "'for' should be Literal, not Param");

        // Find literals in the pattern
        let literals: Vec<_> = pattern
            .iter()
            .filter_map(|t| match t {
                SyntaxExpr::Literal(s) => Some(s.clone()),
                _ => None,
            })
            .collect();

        assert!(literals.contains(&"for".to_string()), "Should contain literal 'for'");
        assert!(literals.contains(&"<-".to_string()), "Should contain literal '<-'");
    }

    // =========================================================================
    // Grammar Generation Tests
    // =========================================================================

    #[test]
    fn test_lalrpop_generation_with_new_syntax() {
        use crate::gen::syntax::parser::generate_lalrpop_grammar;

        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestGrammar,
            types { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let language = result.unwrap();
        let grammar = generate_lalrpop_grammar(&language);

        println!("Generated Grammar:\n{}", grammar);

        // Verify the grammar contains the expected elements
        assert!(grammar.contains("\"for\""), "Grammar should contain 'for' literal");
        assert!(grammar.contains("\"<-\""), "Grammar should contain '<-' literal");
        assert!(
            grammar.contains("<n:Name>") || grammar.contains("<n: Name>"),
            "Grammar should capture 'n' as Name"
        );
        assert!(
            grammar.contains("<x:Ident>") || grammar.contains("<x: Ident>"),
            "Grammar should capture binder 'x' as Ident"
        );
        assert!(
            grammar.contains("<p:Proc>") || grammar.contains("<p: Proc>"),
            "Grammar should capture body 'p' as Proc"
        );
        assert!(grammar.contains("Scope"), "Grammar should create Scope for binding");
    }

    // =========================================================================
    // Pattern Operation Tests (#sep, #zip, #map, #opt)
    // =========================================================================

    #[test]
    fn parse_sep_function_syntax() {
        // #sep(ps, "|") function call syntax
        // Note: Can't use quote! because # has special meaning there
        let input = r#"
            name: TestSep,
            types { Proc }
            terms {
                PPar . ps:HashBag(Proc) |- "{" *sep(ps, "|") "}" : Proc ;
            }
        "#;

        let result = syn::parse_str::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse *sep: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];

        let pattern = rule.syntax_pattern.as_ref().unwrap();

        // Should have: Literal("{"), Op(Sep{...}), Literal("}")
        assert_eq!(pattern.len(), 3, "Pattern should have 3 elements, got {:?}", pattern);
        assert!(matches!(&pattern[0], SyntaxExpr::Literal(s) if s == "{"));
        match &pattern[1] {
            SyntaxExpr::Op(PatternOp::Sep { collection, separator, source }) => {
                assert_eq!(collection.to_string(), "ps");
                assert_eq!(separator, "|");
                assert!(source.is_none(), "Simple #sep should have no source");
            },
            other => panic!("Expected Sep pattern op, got {:?}", other),
        }
        assert!(matches!(&pattern[2], SyntaxExpr::Literal(s) if s == "}"));
    }

    #[test]
    fn parse_sep_method_syntax() {
        // ps.#sep("|") method chain syntax
        let input = r#"
            name: TestSepMethod,
            types { Proc }
            terms {
                PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
            }
        "#;

        let result = syn::parse_str::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse method *sep: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];

        let pattern = rule.syntax_pattern.as_ref().unwrap();

        // Should have: Literal("{"), Op(Sep{...}), Literal("}")
        assert_eq!(pattern.len(), 3, "Pattern should have 3 elements, got {:?}", pattern);

        match &pattern[1] {
            SyntaxExpr::Op(PatternOp::Sep { collection, separator, source }) => {
                assert_eq!(collection.to_string(), "ps");
                assert_eq!(separator, "|");
                assert!(source.is_none(), "Simple #sep should have no source");
            },
            other => panic!("Expected Sep pattern op, got {:?}", other),
        }
    }

    #[test]
    fn parse_zip_syntax() {
        // #zip(ns, xs) syntax
        let input = r#"
            name: TestZip,
            types { Proc Name }
            terms {
                PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- "for" "(" *zip(ns, xs) ")" "{" p "}" : Proc ;
            }
        "#;

        let result = syn::parse_str::<LanguageDef>(input);
        assert!(result.is_ok(), "Failed to parse #zip: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];

        let pattern = rule.syntax_pattern.as_ref().unwrap();

        // Find the Zip op in the pattern
        let has_zip = pattern
            .iter()
            .any(|expr| matches!(expr, SyntaxExpr::Op(PatternOp::Zip { .. })));
        assert!(has_zip, "Pattern should contain Zip operation");
    }
}
