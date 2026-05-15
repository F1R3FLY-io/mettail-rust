#[cfg(test)]
mod tests {
    use crate::grammar::{GrammarItem, TermParam};
    use crate::grammar::{PatternOp, SyntaxExpr};
    use crate::language::LanguageDef;
    use crate::types::{CollectionType, TypeExpr};
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

    #[allow(dead_code)]
    fn make_base_type(name: &str) -> TypeExpr {
        TypeExpr::Base(Ident::new(name, proc_macro2::Span::call_site()))
    }

    #[allow(dead_code)]
    fn make_arrow_type(domain: TypeExpr, codomain: TypeExpr) -> TypeExpr {
        TypeExpr::Arrow {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    // =========================================================================
    // Constructor Signature and Apply Type Inference Tests
    // =========================================================================

    #[allow(dead_code)]
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

    #[test]
    fn parse_term_context_list_int() {
        // Rule with two params: List and Int (e.g. DeleteList)
        let input = quote! {
            name: TestListInt,
            types { List Int }
            terms {
                DeleteList . a:List, i:Int |- "delete" "(" a "," i ")" : List ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let language = result.unwrap();
        let rule = &language.terms[0];
        assert_eq!(rule.label.to_string(), "DeleteList");
        let ctx = rule.term_context.as_ref().expect("term_context");
        assert_eq!(ctx.len(), 2);

        match &ctx[0] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "a");
                assert!(matches!(ty, TypeExpr::Base(id) if id.to_string() == "List"));
            },
            _ => panic!("Expected Simple param a:List"),
        }
        match &ctx[1] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "i");
                assert!(
                    matches!(ty, TypeExpr::Base(id) if id.to_string() == "Int"),
                    "Second param should be Int, got {:?}",
                    ctx[1]
                );
            },
            _ => panic!("Expected Simple param i:Int"),
        }

        // Also verify items (from convert_term_context_to_items) match
        assert_eq!(rule.items.len(), 2);
        if let (
            GrammarItem::NonTerminal { ident: t0, .. },
            GrammarItem::NonTerminal { ident: t1, .. },
        ) = (&rule.items[0], &rule.items[1])
        {
            assert_eq!(t0.to_string(), "List");
            assert_eq!(t1.to_string(), "Int");
        } else {
            panic!("Expected items [List, Int], got {:?}", rule.items);
        }
    }

    #[test]
    fn parse_two_list_rules_second_has_int_param() {
        // Two List rules: ConcatList (List, List) then DeleteList (List, Int)
        let input = quote! {
            name: TestTwoList,
            types { List Int }
            terms {
                ConcatList . a:List, b:List |- "concat" "(" a "," b ")" : List ;
                DeleteList . a:List, i:Int |- "delete" "(" a "," i ")" : List ;
            }
        };

        let result = parse2::<LanguageDef>(input);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let language = result.unwrap();
        assert_eq!(language.terms.len(), 2);

        let concat = &language.terms[0];
        assert_eq!(concat.label.to_string(), "ConcatList");
        let ctx0 = concat.term_context.as_ref().unwrap();
        assert_eq!(ctx0.len(), 2);
        assert!(
            matches!(&ctx0[1], TermParam::Simple { ty: TypeExpr::Base(id), .. } if id.to_string() == "List")
        );

        let delete = &language.terms[1];
        assert_eq!(delete.label.to_string(), "DeleteList");
        let ctx1 = delete.term_context.as_ref().unwrap();
        assert_eq!(ctx1.len(), 2);
        assert!(
            matches!(&ctx1[1], TermParam::Simple { ty: TypeExpr::Base(id), .. } if id.to_string() == "Int"),
            "DeleteList second param should be Int, got {:?}",
            ctx1[1]
        );
        assert_eq!(delete.items.len(), 2);
        if let (
            GrammarItem::NonTerminal { ident: t0, .. },
            GrammarItem::NonTerminal { ident: t1, .. },
        ) = (&delete.items[0], &delete.items[1])
        {
            assert_eq!(t0.to_string(), "List");
            assert_eq!(t1.to_string(), "Int");
        } else {
            panic!("DeleteList items should be [List, Int], got {:?}", delete.items);
        }
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

    // ════════════════════════════════════════════════════════════════════════════
    // B-CG04: is_ground_pattern tests
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn is_ground_pattern_variable_is_not_ground() {
        let input = quote! {
            name: TestGround,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
                PPar . Proc ::= "(" Proc "|" Proc ")" ;
            },
            rewrites {
                R1 . |- (PPar P Q) ~> P ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rw = &language.rewrites[0];
        // LHS is (PPar P Q) — contains variables P, Q → not ground
        assert!(!rw.left.is_ground_pattern(&language));
    }

    #[test]
    fn is_ground_pattern_nullary_constructor_is_ground() {
        let input = quote! {
            name: TestGround2,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
                PPar . Proc ::= "(" Proc "|" Proc ")" ;
            },
            rewrites {
                R1 . |- (PPar PNil PNil) ~> PNil ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rw = &language.rewrites[0];
        // LHS is (PPar PNil PNil) — all positions are nullary constructors → ground
        assert!(rw.left.is_ground_pattern(&language));
        // RHS is PNil — nullary constructor → ground
        assert!(rw.right.is_ground_pattern(&language));
    }

    #[test]
    fn is_ground_pattern_nested_constructors_are_ground() {
        let input = quote! {
            name: TestGround3,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
                PPar . Proc ::= "(" Proc "|" Proc ")" ;
            },
            rewrites {
                R1 . |- (PPar (PPar PNil PNil) PNil) ~> PNil ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rw = &language.rewrites[0];
        // LHS is (PPar (PPar PNil PNil) PNil) — deeply nested, all ground
        assert!(rw.left.is_ground_pattern(&language));
    }

    #[test]
    fn is_ground_pattern_mixed_ground_and_var() {
        let input = quote! {
            name: TestGround4,
            types { Proc },
            terms {
                PNil . Proc ::= "nil" ;
                PPar . Proc ::= "(" Proc "|" Proc ")" ;
            },
            rewrites {
                R1 . |- (PPar PNil P) ~> P ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rw = &language.rewrites[0];
        // LHS is (PPar PNil P) — one ground, one variable → not ground
        assert!(!rw.left.is_ground_pattern(&language));
    }

    // (Phase R-fix 2026-04-08) Two tests `generate_ground_rewrite_seeds_*`
    // were moved from this file to `macros/src/logic/rules.rs::tests`
    // because they reference `crate::logic::rules::generate_ground_rewrite_seeds`,
    // which lives in the `mettail-macros` crate. Without the move, the
    // `mettail-ast → mettail-macros::logic → mettail-ast` cycle would
    // prevent the workspace from compiling after Phase R extraction.

    // ══════════════════════════════════════════════════════════════════════
    // Phase 2C — `?guard:Guard` parser arm tests
    // ══════════════════════════════════════════════════════════════════════

    /// A `?<name>:Guard` parameter parses into `TermParam::GuardBody { name }`.
    #[test]
    fn parse_term_param_accepts_question_guard() {
        let input = quote! {
            name: TestGuardSimple,
            types { Proc Name },
            terms {
                PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
                    |- "for" "(" x "<-" n ")" "where" guard "{" p "}" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rule = &language.terms[0];
        let ctx = rule.term_context.as_ref().expect("has term_context");
        let has_guard_slot = ctx.iter().any(|p| {
            matches!(p, TermParam::GuardBody { name } if name == "guard")
        });
        assert!(has_guard_slot, "expected TermParam::GuardBody {{ name: \"guard\" }}");
    }

    /// The slot name can be any identifier, not just "guard".
    #[test]
    fn parse_term_param_accepts_custom_slot_name() {
        let input = quote! {
            name: TestGuardCustomName,
            types { Proc Name },
            terms {
                PGuardedInput . n:Name, ?pred:Guard, ^x.p:[Name -> Proc]
                    |- "for" "(" x "<-" n ")" "where" pred "{" p "}" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rule = &language.terms[0];
        let ctx = rule.term_context.as_ref().expect("has term_context");
        let has_pred_slot = ctx.iter().any(|p| {
            matches!(p, TermParam::GuardBody { name } if name == "pred")
        });
        assert!(has_pred_slot, "expected TermParam::GuardBody {{ name: \"pred\" }}");
    }

    /// `?name:NotGuard` is rejected with a helpful error.
    #[test]
    fn parse_term_param_rejects_non_guard_type_marker() {
        let input = quote! {
            name: TestGuardBadType,
            types { Proc Name },
            terms {
                PGuardedInput . n:Name, ?guard:Trigger, ^x.p:[Name -> Proc]
                    |- "for" "(" x "<-" n ")" guard "{" p "}" : Proc ;
            }
        };
        let err = parse2::<LanguageDef>(input).expect_err("should reject `Trigger`");
        let msg = err.to_string();
        assert!(
            msg.contains("Guard"),
            "error message should mention `Guard`: {}",
            msg
        );
    }

    /// A constructor with both a regular Simple param and a `?guard:Guard`
    /// slot parses with both appearing in the term_context in order.
    #[test]
    fn parse_term_param_preserves_order_with_guard_slot() {
        let input = quote! {
            name: TestGuardOrdered,
            types { Proc Name },
            terms {
                PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
                    |- "for" "(" x "<-" n ")" "where" guard "{" p "}" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let ctx = language.terms[0]
            .term_context
            .as_ref()
            .expect("has term_context");
        assert_eq!(ctx.len(), 3, "expected 3 term params");
        assert!(
            matches!(&ctx[0], TermParam::Simple { name, .. } if name == "n"),
            "first param must be `n:Name`"
        );
        assert!(
            matches!(&ctx[1], TermParam::GuardBody { name } if name == "guard"),
            "second param must be `?guard:Guard`"
        );
        assert!(
            matches!(&ctx[2], TermParam::Abstraction { binder, body, .. }
                if binder == "x" && body == "p"),
            "third param must be `^x.p:[Name -> Proc]`"
        );
    }

    /// Multiple guarded constructors in the same language parse without
    /// conflicting with each other.
    #[test]
    fn parse_term_param_multiple_guarded_constructors() {
        let input = quote! {
            name: TestGuardMultiple,
            types { Proc Name },
            terms {
                PGuardedInputA . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
                    |- "fora" "(" x "<-" n ")" guard "{" p "}" : Proc ;
                PGuardedInputB . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]
                    |- "forb" "(" x "<-" n ")" guard "{" p "}" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert_eq!(language.terms.len(), 2);
        for rule in &language.terms {
            let ctx = rule.term_context.as_ref().expect("has term_context");
            let has_guard_slot = ctx.iter().any(|p| {
                matches!(p, TermParam::GuardBody { .. })
            });
            assert!(has_guard_slot, "{} should have a guard slot", rule.label);
        }
    }

    /// Constructors without `?guard:Guard` parse unchanged (regression
    /// check: the new parser arm must not affect existing grammars).
    #[test]
    fn parse_term_param_unguarded_constructors_still_work() {
        let input = quote! {
            name: TestNoGuard,
            types { Proc Name },
            terms {
                PZero . |- "0" : Proc ;
                POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc ;
                NQuote . p:Proc |- "@" "(" p ")" : Name ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert_eq!(language.terms.len(), 3);
        for rule in &language.terms {
            if let Some(ctx) = &rule.term_context {
                for p in ctx {
                    assert!(
                        !matches!(p, TermParam::GuardBody { .. }),
                        "{} should not have a guard slot",
                        rule.label
                    );
                }
            }
        }
    }

    // ── Phase 11: #[tier(...)] directive parser ──

    use crate::grammar::TierRequest;

    #[test]
    fn parse_tier_directive_t1() {
        let input = quote! {
            name: T1Lang,
            types { Proc },
            terms {
                #[tier(t1)]
                PZero . |- "0" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let rule = &language.terms[0];
        let directive = rule.tier_directive.as_ref().expect("tier directive");
        assert_eq!(directive.tier, TierRequest::T1);
        assert!(!directive.force);
        assert!(directive.bound.is_none());
        assert!(directive.proof.is_none());
    }

    #[test]
    fn parse_tier_directive_t3_with_bound() {
        let input = quote! {
            name: T3Lang,
            types { Proc },
            terms {
                #[tier(t3, bound = 256)]
                PZero . |- "0" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let directive =
            language.terms[0].tier_directive.as_ref().expect("tier directive");
        assert_eq!(directive.tier, TierRequest::T3);
        assert_eq!(directive.bound, Some(256));
    }

    #[test]
    fn parse_tier_directive_t4_with_force_and_proof() {
        let input = quote! {
            name: T4Lang,
            types { Proc },
            terms {
                #[tier(t4, force, proof = "proofs/foo.v")]
                PZero . |- "0" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let directive =
            language.terms[0].tier_directive.as_ref().expect("tier directive");
        assert_eq!(directive.tier, TierRequest::T4);
        assert!(directive.force);
        assert_eq!(directive.proof, Some("proofs/foo.v".to_string()));
    }

    #[test]
    fn parse_tier_directive_uppercase_works() {
        let input = quote! {
            name: T2Lang,
            types { Proc },
            terms {
                #[tier(T2)]
                PZero . |- "0" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        let directive =
            language.terms[0].tier_directive.as_ref().expect("tier directive");
        assert_eq!(directive.tier, TierRequest::T2);
    }

    #[test]
    fn parse_tier_directive_invalid_tier_rejected() {
        let input = quote! {
            name: BadLang,
            types { Proc },
            terms {
                #[tier(t99)]
                PZero . |- "0" : Proc ;
            }
        };
        let result = parse2::<LanguageDef>(input);
        assert!(result.is_err());
    }

    #[test]
    fn parse_tier_directive_unknown_key_rejected() {
        let input = quote! {
            name: BadLang,
            types { Proc },
            terms {
                #[tier(t1, banana = 5)]
                PZero . |- "0" : Proc ;
            }
        };
        let result = parse2::<LanguageDef>(input);
        assert!(result.is_err());
    }

    #[test]
    fn rules_without_tier_directive_have_none() {
        let input = quote! {
            name: NoTier,
            types { Proc },
            terms {
                PZero . |- "0" : Proc ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert!(language.terms[0].tier_directive.is_none());
    }

    // Port of main's `parse_literals_block` test, adapted for the unified token
    // backend: `literals { ... }` entries desugar into `language.token_defs`
    // with their `name` mapped to the standard `Token::<family>` variant
    // derived from the category's native type, and the original block name
    // preserved in the `category` field.
    #[test]
    fn parse_literals_block_desugars_to_token_defs() {
        let input = r#"
            name: TestLiterals,
            types { ![i32] as Int ![bool] as Bool }
            literals {
                Int {
                    pattern: r"[0-9]+";
                    eval: ![ { text.parse::<i32>().unwrap_or(-1) } ]
                }
                Bool {
                    pattern: r"yes|no";
                    eval: ![ { text == "yes" } ]
                }
            }
            terms { }
        "#;

        let result = syn::parse_str::<LanguageDef>(input);
        assert!(
            result.is_ok(),
            "Failed to parse literals block: {:?}",
            result.err()
        );

        let language = result.unwrap();
        assert_eq!(
            language.token_defs.len(),
            2,
            "literals{{}} should desugar into exactly 2 token_defs"
        );

        // `Int` with native `i32` → standard `Token::Integer(IntLit)` family.
        let int_tok = &language.token_defs[0];
        assert_eq!(int_tok.name.to_string(), "Integer");
        assert_eq!(int_tok.pattern, "[0-9]+");
        assert_eq!(
            int_tok.category.as_ref().map(|c| c.to_string()),
            Some("Int".to_string()),
            "category preserves the user-facing literals{{}} block name"
        );
        assert!(int_tok.rust_code.is_some());
        assert!(int_tok.priority.is_none());

        // `Bool` with native `bool` → standard `Token::Boolean` family.
        let bool_tok = &language.token_defs[1];
        assert_eq!(bool_tok.name.to_string(), "Boolean");
        assert_eq!(bool_tok.pattern, "yes|no");
        assert_eq!(
            bool_tok.category.as_ref().map(|c| c.to_string()),
            Some("Bool".to_string())
        );
    }

    /// Two integer-typed categories sharing the standard `Token::Integer`
    /// variant must coexist — only `(name, pattern)` pairs are unique.
    /// `Int` (i32) and `UInt32` (u32) both have
    /// `NativeKind::standard_token_variant() == Some("Integer")` and so
    /// collapse onto the same unified family variant.
    #[test]
    fn parse_literals_block_shared_family_variant_allowed() {
        let input = r#"
            name: TestSharedFamilyI32U32,
            types { ![i32] as Int ![u32] as UInt32 }
            literals {
                Int {
                    pattern: r"[0-9]+i32";
                    eval: ![ 0_i32 ]
                }
                UInt32 {
                    pattern: r"[0-9]+u32";
                    eval: ![ 0_u32 ]
                }
            }
            terms { }
        "#;

        let language = syn::parse_str::<LanguageDef>(input)
            .expect("Int + UInt32 sharing Token::Integer should parse");
        assert_eq!(language.token_defs.len(), 2);
        // Both share the standard Integer family variant.
        assert!(
            language.token_defs.iter().all(|td| td.name.to_string() == "Integer"),
            "both literals should map to Token::Integer family"
        );
        // The original block names are recoverable via `category`.
        let cats: Vec<String> = language
            .token_defs
            .iter()
            .filter_map(|td| td.category.as_ref().map(|c| c.to_string()))
            .collect();
        assert!(cats.contains(&"Int".to_string()));
        assert!(cats.contains(&"UInt32".to_string()));
    }

    /// Same shared-family invariant exercised across two distinct signed
    /// widths: `Int` (i32) and `Long` (i64). Both have
    /// `NativeKind::standard_token_variant() == Some("Integer")`.
    #[test]
    fn parse_literals_block_shared_family_variant_allowed_i32_i64() {
        let input = r#"
            name: TestSharedFamilyI32I64,
            types { ![i32] as Int ![i64] as Long }
            literals {
                Int {
                    pattern: r"[0-9]+i32";
                    eval: ![ 0_i32 ]
                }
                Long {
                    pattern: r"[0-9]+i64";
                    eval: ![ 0_i64 ]
                }
            }
            terms { }
        "#;

        let language = syn::parse_str::<LanguageDef>(input)
            .expect("Int + Long sharing Token::Integer should parse");
        assert_eq!(language.token_defs.len(), 2);
        assert!(
            language.token_defs.iter().all(|td| td.name.to_string() == "Integer"),
            "both literals should map to Token::Integer family"
        );
        let cats: Vec<String> = language
            .token_defs
            .iter()
            .filter_map(|td| td.category.as_ref().map(|c| c.to_string()))
            .collect();
        assert!(cats.contains(&"Int".to_string()));
        assert!(cats.contains(&"Long".to_string()));
    }

    /// `CanonicalBigInt` does NOT collapse onto `Token::Integer` — its
    /// `Token::BigInt(&'a str)` variant carries the full lexeme so that
    /// arbitrary-precision literals like `32478132567813256718n` are
    /// preserved losslessly. This invariant is load-bearing: the WPDS
    /// backend at `wpda_codegen/prefix.rs:1129-1190` and the trampoline
    /// at `trampoline.rs:5266-5288` BOTH dispatch on `Token::BigInt(text)`
    /// for category `BigInt` and call `parse_int_lit(text, None)` to
    /// reconstruct the full-precision value. See the comment at
    /// `ast/src/language.rs:927-934` for design rationale.
    #[test]
    fn parse_literals_block_canonical_bigint_keeps_own_variant() {
        // Direct invariant pin: the two predicates `is_integer` and
        // `standard_token_variant` are semantically distinct for BigInt.
        assert!(
            crate::language::NativeKind::CanonicalBigInt.is_integer(),
            "CanonicalBigInt is semantically an integer (covered by is_integer)"
        );
        assert_eq!(
            crate::language::NativeKind::CanonicalBigInt.standard_token_variant(),
            None,
            "CanonicalBigInt does NOT collapse onto Token::Integer (preserves precision)"
        );

        // End-to-end: a literals{} block with Int + BigInt produces TWO
        // distinct token_defs — Int collapses to "Integer", BigInt keeps
        // its category-named variant.
        let input = r#"
            name: TestBigIntKeepsOwnVariant,
            types { ![i32] as Int ![mettail_runtime::CanonicalBigInt] as BigInt }
            literals {
                Int {
                    pattern: r"[0-9]+i32";
                    eval: ![ 0_i32 ]
                }
                BigInt {
                    pattern: r"[0-9]+n";
                    eval: ![ 0_i32 ]
                }
            }
            terms { }
        "#;

        let language = syn::parse_str::<LanguageDef>(input)
            .expect("Int + BigInt should parse");
        assert_eq!(language.token_defs.len(), 2);

        let int_td = language.token_defs.iter()
            .find(|td| td.category.as_ref().map(|c| c.to_string()) == Some("Int".to_string()))
            .expect("Int token_def present");
        assert_eq!(
            int_td.name.to_string(), "Integer",
            "Int collapses onto the unified Token::Integer family"
        );

        let bigint_td = language.token_defs.iter()
            .find(|td| td.category.as_ref().map(|c| c.to_string()) == Some("BigInt".to_string()))
            .expect("BigInt token_def present");
        assert_eq!(
            bigint_td.name.to_string(), "BigInt",
            "BigInt keeps its OWN Token::BigInt(&'a str) variant for precision preservation"
        );
    }

    #[test]
    fn parse_literals_block_requires_type_decl() {
        // Undeclared type `Missing` in literals{} should be rejected.
        let input = r#"
            name: TestLitUndeclared,
            types { ![i32] as Int }
            literals {
                Missing {
                    pattern: r"[0-9]+";
                    eval: ![ { 0_i32 } ]
                }
            }
            terms { }
        "#;
        let result = syn::parse_str::<LanguageDef>(input);
        assert!(
            result.is_err(),
            "expected error for literals{{Missing}} without matching types entry"
        );
    }

    // ─── Stage 3.27a (2026-05-04): doc-comment description tests ──────

    #[test]
    fn parse_doc_comment_single_line() {
        let input = quote! {
            name: DocLang,
            types { ![i32] as Int }
            terms {
                /// Adds two integers.
                Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert_eq!(
            language.terms[0].doc_comment.as_deref(),
            Some("Adds two integers."),
            "single-line /// should produce one line of doc text",
        );
    }

    #[test]
    fn parse_doc_comment_multi_line() {
        let input = quote! {
            name: DocLang,
            types { ![i32] as Int }
            terms {
                /// Adds two integers.
                ///
                /// Folded eagerly when both operands are constants.
                Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert_eq!(
            language.terms[0].doc_comment.as_deref(),
            Some("Adds two integers.\n\nFolded eagerly when both operands are constants."),
            "multi-line /// should be joined with \\n preserving blank lines",
        );
    }

    #[test]
    fn parse_doc_comment_with_tier_directive() {
        let input = quote! {
            name: DocTierLang,
            types { ![i32] as Int }
            terms {
                /// Stuck term.
                #[tier(t1)]
                Err . |- "stuck" : Int ;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert_eq!(language.terms[0].doc_comment.as_deref(), Some("Stuck term."));
        assert!(
            language.terms[0].tier_directive.is_some(),
            "tier directive must survive doc-comment consumption",
        );
    }

    #[test]
    fn rules_without_doc_comment_have_none() {
        let input = quote! {
            name: NoDoc,
            types { ![i32] as Int }
            terms {
                Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert!(
            language.terms[0].doc_comment.is_none(),
            "rules without /// must have doc_comment == None",
        );
    }

    #[test]
    fn doc_comment_does_not_swallow_tier_directive() {
        // Regression test: ensure parse_doc_comment uses fork-peek and
        // never accidentally consumes #[tier(...)].
        let input = quote! {
            name: DocOnlyLang,
            types { ![i32] as Int }
            terms {
                #[tier(t2)]
                Plain . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
            }
        };
        let language = parse2::<LanguageDef>(input).expect("parse ok");
        assert!(
            language.terms[0].doc_comment.is_none(),
            "no /// → doc_comment should be None",
        );
        assert!(
            language.terms[0].tier_directive.is_some(),
            "tier directive must be parsed when no doc comment precedes it",
        );
    }
}
