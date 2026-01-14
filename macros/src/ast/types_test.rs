#[cfg(test)]
mod tests {
    use quote::quote;
    use syn::{
        parse2,
        Ident,
    };
    use crate::ast::types::{TheoryDef, TypeExpr, GrammarItem, CollectionType, FreshnessTarget, TypeError, TypeContext, Expr, ConstructorSig, TermParam, SyntaxToken};
    use crate::ast::types::{parse_expr};

    #[test]
    fn parse_hashbag_simple() {
        let input = quote! {
            name: TestBag,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "|" ;
                EZero . Elem ::= "0" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse HashBag: {:?}", result.err());

        let theory = result.unwrap();
        assert_eq!(theory.name.to_string(), "TestBag");
        assert_eq!(theory.terms.len(), 2);

        // Check EBag has a Collection item
        let ebag = &theory.terms[0];
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
    fn parse_parenthesized_collection_freshness() {
        let input = quote! {
            name: TestFresh,
            exports { Proc Name }
            terms {
                PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
                PNew . Proc ::= "new(" <Name> "," Proc ")" ;
                PVar . Proc ::= Var ;
                NVar . Name ::= Var ;
            }
            equations {
                if (x # ...rest) then (PPar {(PNew x P), ...rest}) == (PNew x (PPar {P, ...rest}));
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse parenthesized freshness: {:?}", result.err());
        let theory = result.unwrap();
        assert_eq!(theory.equations.len(), 1);
        let eq = &theory.equations[0];
        assert_eq!(eq.conditions.len(), 1);
        match &eq.conditions[0].term {
            FreshnessTarget::CollectionRest(id) => assert_eq!(id.to_string(), "rest"),
            other => panic!("Expected CollectionRest freshness target, got: {:?}", other),
        }
    }

    #[test]
    fn parse_collection_with_delimiters() {
        let input = quote! {
            name: TestList,
            exports { Elem }
            terms {
                EList . Elem ::= Vec(Elem) sep "," delim "[" "]" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse Vec with delimiters: {:?}", result.err());

        let theory = result.unwrap();
        let elist = &theory.terms[0];

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
            exports { Elem }
            terms {
                ESet . Elem ::= HashSet(Elem) sep "," delim "{" "}" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse HashSet: {:?}", result.err());

        let theory = result.unwrap();
        let eset = &theory.terms[0];

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
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_err(), "Should reject empty separator");
        let err = result.err().unwrap();
        assert!(err.to_string().contains("separator cannot be empty"));
    }

    #[test]
    fn parse_collection_error_missing_sep() {
        let input = quote! {
            name: TestBad,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) "|" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
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
            }
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
                    TypeExpr::Arrow { domain: inner_domain, codomain: inner_codomain } => {
                        assert!(matches!(*inner_domain, TypeExpr::Base(ref id) if id == "A"));
                        assert!(matches!(*inner_codomain, TypeExpr::Base(ref id) if id == "B"));
                    }
                    _ => panic!("Expected inner Arrow type"),
                }
            }
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
                    }
                    _ => panic!("Expected MultiBinder domain, got {:?}", domain),
                }
                assert!(matches!(*codomain, TypeExpr::Base(ref id) if id == "Proc"));
            }
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
            }
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
            }
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
            }
            _ => panic!("Expected Collection type"),
        }
    }

    #[test]
    fn type_expr_equality() {
        // Same types should be equal
        let ty1 = TypeExpr::base("Name");
        let ty2 = TypeExpr::base("Name");
        assert_eq!(ty1, ty2);

        // Different base types should not be equal
        let ty3 = TypeExpr::base("Proc");
        assert_ne!(ty1, ty3);

        // Arrow types
        let arr1 = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        let arr2 = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        assert_eq!(arr1, arr2);

        // Different arrows should not be equal
        let arr3 = TypeExpr::arrow(TypeExpr::base("Proc"), TypeExpr::base("Name"));
        assert_ne!(arr1, arr3);
    }

    #[test]
    fn type_expr_display() {
        let base = TypeExpr::base("Name");
        assert_eq!(format!("{}", base), "Name");

        let arrow = TypeExpr::arrow(TypeExpr::base("Name"), TypeExpr::base("Proc"));
        assert_eq!(format!("{}", arrow), "[Name -> Proc]");

        let multi = TypeExpr::arrow(
            TypeExpr::multi_binder(TypeExpr::base("Name")),
            TypeExpr::base("Proc"),
        );
        assert_eq!(format!("{}", multi), "[Name* -> Proc]");

        let standalone_multi = TypeExpr::multi_binder(TypeExpr::base("Name"));
        assert_eq!(format!("{}", standalone_multi), "Name*");

        let coll = TypeExpr::collection(CollectionType::Vec, TypeExpr::base("Name"));
        assert_eq!(format!("{}", coll), "Vec(Name)");
    }

    // =========================================================================
    // Expr Lambda Tests
    // =========================================================================

    use syn::parse::Parser;

    #[test]
    fn parse_expr_lambda_simple() {
        // ^x.body where body is a variable
        let input = quote! { ^x.p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(ref v) if v == "p"));
            }
            _ => panic!("Expected Lambda, got {:?}", expr),
        }
    }

    #[test]
    fn parse_expr_lambda_nested() {
        // ^x.^y.body - nested lambdas
        let input = quote! { ^x.^y.p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse nested lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                match *body {
                    Expr::Lambda { binder: inner_binder, body: inner_body } => {
                        assert_eq!(inner_binder.to_string(), "y");
                        assert!(matches!(*inner_body, Expr::Var(ref v) if v == "p"));
                    }
                    _ => panic!("Expected nested Lambda"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn parse_expr_multi_lambda() {
        // ^[xs].body - multi-binder lambda
        let input = quote! { ^[xs].p };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse multi-lambda: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::MultiLambda { binder, body } => {
                assert_eq!(binder.to_string(), "xs");
                assert!(matches!(*body, Expr::Var(ref v) if v == "p"));
            }
            _ => panic!("Expected MultiLambda, got {:?}", expr),
        }
    }

    #[test]
    fn parse_expr_lambda_with_apply() {
        // ^x.(Constructor x y) - lambda with constructor application body
        let input = quote! { ^x.(PPar x y) };
        let result = parse_expr.parse2(input);
        assert!(result.is_ok(), "Failed to parse lambda with apply: {:?}", result.err());

        let expr = result.unwrap();
        match expr {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                match *body {
                    Expr::Apply { constructor, args } => {
                        assert_eq!(constructor.to_string(), "PPar");
                        assert_eq!(args.len(), 2);
                    }
                    _ => panic!("Expected Apply in body"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    // =========================================================================
    // Expr free_vars, substitute, apply Tests
    // =========================================================================

    fn make_var(name: &str) -> Expr {
        Expr::Var(Ident::new(name, proc_macro2::Span::call_site()))
    }

    fn make_lambda(binder: &str, body: Expr) -> Expr {
        Expr::Lambda {
            binder: Ident::new(binder, proc_macro2::Span::call_site()),
            body: Box::new(body),
        }
    }

    fn make_apply(constructor: &str, args: Vec<Expr>) -> Expr {
        Expr::Apply {
            constructor: Ident::new(constructor, proc_macro2::Span::call_site()),
            args,
        }
    }

    #[test]
    fn test_free_vars_var() {
        let expr = make_var("x");
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("x"));
    }

    #[test]
    fn test_free_vars_apply() {
        // PPar(x, y) has free vars {x, y}
        let expr = make_apply("PPar", vec![make_var("x"), make_var("y")]);
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 2);
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
    }

    #[test]
    fn test_free_vars_lambda() {
        // ^x.y has free vars {y} (x is bound)
        let expr = make_lambda("x", make_var("y"));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("y"));
        assert!(!fv.contains("x"));
    }

    #[test]
    fn test_free_vars_lambda_bound() {
        // ^x.x has no free vars (x is bound)
        let expr = make_lambda("x", make_var("x"));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 0);
    }

    #[test]
    fn test_free_vars_nested_lambda() {
        // ^x.^y.z has free vars {z}
        let expr = make_lambda("x", make_lambda("y", make_var("z")));
        let fv = expr.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("z"));
    }

    #[test]
    fn test_substitute_var_match() {
        // x[y/x] = y
        let expr = make_var("x");
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("y");
        
        let result = expr.substitute(&var, &replacement);
        assert!(matches!(result, Expr::Var(v) if v == "y"));
    }

    #[test]
    fn test_substitute_var_no_match() {
        // x[z/y] = x
        let expr = make_var("x");
        let var = Ident::new("y", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        assert!(matches!(result, Expr::Var(v) if v == "x"));
    }

    #[test]
    fn test_substitute_apply() {
        // PPar(x, y)[z/x] = PPar(z, y)
        let expr = make_apply("PPar", vec![make_var("x"), make_var("y")]);
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Apply { constructor, args } => {
                assert_eq!(constructor.to_string(), "PPar");
                assert!(matches!(&args[0], Expr::Var(v) if v == "z"));
                assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_substitute_lambda_shadowing() {
        // (^x.x)[y/x] = ^x.x (x is shadowed by binder)
        let expr = make_lambda("x", make_var("x"));
        let var = Ident::new("x", proc_macro2::Span::call_site());
        let replacement = make_var("y");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(v) if v == "x"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_substitute_lambda_body() {
        // (^x.y)[z/y] = ^x.z
        let expr = make_lambda("x", make_var("y"));
        let var = Ident::new("y", proc_macro2::Span::call_site());
        let replacement = make_var("z");
        
        let result = expr.substitute(&var, &replacement);
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "x");
                assert!(matches!(*body, Expr::Var(v) if v == "z"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_apply_lambda() {
        // (^x.PPar(x, y))(z) = PPar(z, y)
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("y")]));
        let arg = make_var("z");
        
        let result = lambda.apply(&arg).expect("apply should succeed");
        match result {
            Expr::Apply { constructor, args } => {
                assert_eq!(constructor.to_string(), "PPar");
                assert!(matches!(&args[0], Expr::Var(v) if v == "z"));
                assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_apply_nested_lambda() {
        // (^x.^y.PPar(x, y))(a) = ^y.PPar(a, y)
        let lambda = make_lambda("x", make_lambda("y", make_apply("PPar", vec![make_var("x"), make_var("y")])));
        let arg = make_var("a");
        
        let result = lambda.apply(&arg).expect("apply should succeed");
        match result {
            Expr::Lambda { binder, body } => {
                assert_eq!(binder.to_string(), "y");
                match *body {
                    Expr::Apply { ref args, .. } => {
                        assert!(matches!(&args[0], Expr::Var(v) if v == "a"));
                        assert!(matches!(&args[1], Expr::Var(v) if v == "y"));
                    }
                    _ => panic!("Expected Apply in body"),
                }
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_apply_non_lambda_fails() {
        let expr = make_var("x");
        let arg = make_var("y");
        
        let result = expr.apply(&arg);
        assert!(result.is_err());
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

    #[test]
    fn test_type_context_empty() {
        let ctx = TypeContext::new();
        assert!(!ctx.contains("x"));
        assert!(ctx.lookup("x").is_none());
    }

    #[test]
    fn test_type_context_with_var() {
        let ctx = TypeContext::new();
        let name_type = make_base_type("Name");
        let extended = ctx.with_var("x", name_type.clone());
        
        assert!(extended.contains("x"));
        assert_eq!(extended.lookup("x"), Some(&name_type));
        
        // Original context should be unchanged
        assert!(!ctx.contains("x"));
    }

    #[test]
    fn test_infer_type_var_bound() {
        let ctx = TypeContext::new().with_var("x", make_base_type("Name"));
        let expr = make_var("x");
        
        let result = expr.infer_type(&ctx);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), make_base_type("Name"));
    }

    #[test]
    fn test_infer_type_var_unbound() {
        let ctx = TypeContext::new();
        let expr = make_var("x");
        
        let result = expr.infer_type(&ctx);
        assert!(result.is_err());
        match result {
            Err(TypeError::UnboundVariable(v)) => assert_eq!(v, "x"),
            _ => panic!("Expected UnboundVariable error"),
        }
    }

    #[test]
    fn test_check_type_lambda() {
        // Check that ^x.x : [Name -> Name]
        let lambda = make_lambda("x", make_var("x"));
        let arrow_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new();
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_check_type_lambda_body_uses_binder() {
        // ^x.PPar(x, y) : [Name -> Proc] in context where y:Proc
        // But we can't fully check Apply yet, so this will fail with CannotInfer
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("y")]));
        let arrow_type = make_arrow_type(make_base_type("Name"), make_base_type("Proc"));
        let ctx = TypeContext::new().with_var("y", make_base_type("Proc"));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        // This will fail because Apply type inference isn't implemented yet
        assert!(result.is_err());
    }

    #[test]
    fn test_check_type_nested_lambda() {
        // Check that ^x.^y.y : [A -> [B -> B]]
        let inner = make_lambda("y", make_var("y"));
        let outer = make_lambda("x", inner);
        
        let inner_arrow = make_arrow_type(make_base_type("B"), make_base_type("B"));
        let outer_arrow = make_arrow_type(make_base_type("A"), inner_arrow);
        let ctx = TypeContext::new();
        
        let result = outer.check_type(&outer_arrow, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_apply_typed() {
        // Apply (^x.x : [Name -> Name]) to (n : Name) = n
        let lambda = make_lambda("x", make_var("x"));
        let arg = make_var("n");
        let func_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new().with_var("n", make_base_type("Name"));
        
        let result = lambda.apply_typed(&arg, &ctx, &func_type);
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Expr::Var(v) if v == "n"));
    }

    #[test]
    fn test_apply_typed_wrong_arg_type() {
        // Apply (^x.x : [Name -> Name]) to (p : Proc) should fail
        let lambda = make_lambda("x", make_var("x"));
        let arg = make_var("p");
        let func_type = make_arrow_type(make_base_type("Name"), make_base_type("Name"));
        let ctx = TypeContext::new().with_var("p", make_base_type("Proc")); // Wrong type!
        
        let result = lambda.apply_typed(&arg, &ctx, &func_type);
        assert!(result.is_err());
        match result {
            Err(TypeError::TypeMismatch { expected, found, .. }) => {
                assert_eq!(expected, make_base_type("Name"));
                assert_eq!(found, make_base_type("Proc"));
            }
            _ => panic!("Expected TypeMismatch error"),
        }
    }

    // =========================================================================
    // Constructor Signature and Apply Type Inference Tests
    // =========================================================================

    fn make_collection_type(coll_type: CollectionType, element: TypeExpr) -> TypeExpr {
        TypeExpr::Collection {
            coll_type,
            element: Box::new(element),
        }
    }

    #[test]
    fn test_constructor_sig_creation() {
        let sig = ConstructorSig::new(
            vec![make_base_type("Name"), make_base_type("Proc")],
            make_base_type("Proc")
        );
        assert_eq!(sig.arg_types.len(), 2);
        assert_eq!(sig.result_type, make_base_type("Proc"));
    }

    #[test]
    fn test_context_with_constructor() {
        let ctx = TypeContext::new()
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let sig = ctx.lookup_constructor("PPar");
        assert!(sig.is_some());
        assert_eq!(sig.unwrap().arg_types.len(), 2);
    }

    #[test]
    fn test_infer_type_apply_simple() {
        // PPar(p, q) : Proc where p:Proc, q:Proc
        let ctx = TypeContext::new()
            .with_var("p", make_base_type("Proc"))
            .with_var("q", make_base_type("Proc"))
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let expr = make_apply("PPar", vec![make_var("p"), make_var("q")]);
        let result = expr.infer_type(&ctx);
        
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
        assert_eq!(result.unwrap(), make_base_type("Proc"));
    }

    #[test]
    fn test_infer_type_apply_with_name() {
        // POut(n, p) : Proc where n:Name, p:Proc
        let ctx = TypeContext::new()
            .with_var("n", make_base_type("Name"))
            .with_var("p", make_base_type("Proc"))
            .with_constructor("POut", ConstructorSig::new(
                vec![make_base_type("Name"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let expr = make_apply("POut", vec![make_var("n"), make_var("p")]);
        let result = expr.infer_type(&ctx);
        
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
        assert_eq!(result.unwrap(), make_base_type("Proc"));
    }

    #[test]
    fn test_infer_type_apply_wrong_arg_type() {
        // PPar(n, p) should fail if n:Name (expected Proc)
        let ctx = TypeContext::new()
            .with_var("n", make_base_type("Name"))
            .with_var("p", make_base_type("Proc"))
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let expr = make_apply("PPar", vec![make_var("n"), make_var("p")]);
        let result = expr.infer_type(&ctx);
        
        assert!(result.is_err());
    }

    #[test]
    fn test_infer_type_apply_wrong_arity() {
        // PPar(p) with only 1 arg should fail
        let ctx = TypeContext::new()
            .with_var("p", make_base_type("Proc"))
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let expr = make_apply("PPar", vec![make_var("p")]);
        let result = expr.infer_type(&ctx);
        
        assert!(result.is_err());
        match result {
            Err(TypeError::CannotInfer(msg)) => {
                assert!(msg.contains("expects 2 arguments, got 1"));
            }
            _ => panic!("Expected CannotInfer error about arity"),
        }
    }

    #[test]
    fn test_infer_type_apply_unknown_constructor() {
        let ctx = TypeContext::new()
            .with_var("p", make_base_type("Proc"));
        
        let expr = make_apply("Unknown", vec![make_var("p")]);
        let result = expr.infer_type(&ctx);
        
        assert!(result.is_err());
        match result {
            Err(TypeError::CannotInfer(msg)) => {
                assert!(msg.contains("not found"));
            }
            _ => panic!("Expected CannotInfer error"),
        }
    }

    // =========================================================================
    // Collection-typed Lambda Tests: ^xs.p:[Vec(Name) -> Proc]
    // =========================================================================

    #[test]
    fn test_check_type_lambda_with_collection_domain() {
        // ^xs.POut(x, PNil) : [Vec(Name) -> Proc]
        // This binds xs to a Vec(Name), so xs:Vec(Name) in the body
        let lambda = make_lambda("xs", make_apply("PNil", vec![]));
        let domain = make_collection_type(CollectionType::Vec, make_base_type("Name"));
        let arrow_type = make_arrow_type(domain.clone(), make_base_type("Proc"));
        let ctx = TypeContext::new()
            .with_constructor("PNil", ConstructorSig::new(vec![], make_base_type("Proc")));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_check_type_lambda_collection_domain_using_binder() {
        // ^xs.Fold(xs) : [Vec(Name) -> Proc]
        // Body uses xs, which has type Vec(Name)
        let lambda = make_lambda("xs", make_apply("Fold", vec![make_var("xs")]));
        let domain = make_collection_type(CollectionType::Vec, make_base_type("Name"));
        let arrow_type = make_arrow_type(domain.clone(), make_base_type("Proc"));
        let ctx = TypeContext::new()
            .with_constructor("Fold", ConstructorSig::new(
                vec![make_collection_type(CollectionType::Vec, make_base_type("Name"))],
                make_base_type("Proc")
            ));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    // =========================================================================
    // Multi-Lambda Tests: ^[xs].p:[Name* -> Proc]
    // =========================================================================

    fn make_multi_lambda(binder: &str, body: Expr) -> Expr {
        Expr::MultiLambda {
            binder: Ident::new(binder, proc_macro2::Span::call_site()),
            body: Box::new(body),
        }
    }

    #[test]
    fn test_check_type_multi_lambda() {
        // ^[xs].p : [Name* -> Proc]
        // xs binds multiple Names, body should be Proc
        let multi_lambda = make_multi_lambda("xs", make_apply("PNil", vec![]));
        let multi_domain = TypeExpr::MultiBinder(Box::new(make_base_type("Name")));
        let arrow_type = make_arrow_type(multi_domain, make_base_type("Proc"));
        let ctx = TypeContext::new()
            .with_constructor("PNil", ConstructorSig::new(vec![], make_base_type("Proc")));
        
        let result = multi_lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_check_type_multi_lambda_non_multi_domain_fails() {
        // ^[xs].p with non-multi domain should fail
        let multi_lambda = make_multi_lambda("xs", make_var("p"));
        let arrow_type = make_arrow_type(make_base_type("Name"), make_base_type("Proc"));
        let ctx = TypeContext::new().with_var("p", make_base_type("Proc"));
        
        let result = multi_lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_err());
        match result {
            Err(TypeError::CannotInfer(msg)) => {
                assert!(msg.contains("multi-binder domain"), "Error message: {}", msg);
            }
            _ => panic!("Expected CannotInfer error about multi-binder domain"),
        }
    }

    // =========================================================================
    // Lambda with Apply body - now works with constructor signatures
    // =========================================================================

    #[test]
    fn test_check_type_lambda_body_with_apply() {
        // ^x.PPar(x, y) : [Proc -> Proc] in context where y:Proc
        // This should now PASS with constructor signatures
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("y")]));
        let arrow_type = make_arrow_type(make_base_type("Proc"), make_base_type("Proc"));
        let ctx = TypeContext::new()
            .with_var("y", make_base_type("Proc"))
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    }

    #[test]
    fn test_check_type_lambda_apply_type_mismatch() {
        // ^x.PPar(x, n) : [Proc -> Proc] where n:Name should FAIL
        let lambda = make_lambda("x", make_apply("PPar", vec![make_var("x"), make_var("n")]));
        let arrow_type = make_arrow_type(make_base_type("Proc"), make_base_type("Proc"));
        let ctx = TypeContext::new()
            .with_var("n", make_base_type("Name")) // Wrong type!
            .with_constructor("PPar", ConstructorSig::new(
                vec![make_base_type("Proc"), make_base_type("Proc")],
                make_base_type("Proc")
            ));
        
        let result = lambda.check_type(&arrow_type, &ctx);
        assert!(result.is_err());
    }

    // =========================================================================
    // New Constructor Syntax Tests (Judgement-style)
    // =========================================================================

    #[test]
    fn parse_new_syntax_simple() {
        // Simple parameter: n:Name |- n : Name ;
        let input = quote! {
            name: TestSimple,
            exports { Name }
            terms {
                NVar . n:Name |- n : Name ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse new syntax: {:?}", result.err());

        let theory = result.unwrap();
        assert_eq!(theory.terms.len(), 1);
        
        let rule = &theory.terms[0];
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
            }
            _ => panic!("Expected Simple param"),
        }
    }

    #[test]
    fn parse_new_syntax_abstraction() {
        // Abstraction: n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
        // All syntax literals must be quoted strings; only parameter references are unquoted
        let input = quote! {
            name: TestAbs,
            exports { Proc Name }
            terms {
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse abstraction syntax: {:?}", result.err());

        let theory = result.unwrap();
        let rule = &theory.terms[0];
        
        assert_eq!(rule.label.to_string(), "PInput");
        assert_eq!(rule.category.to_string(), "Proc");
        
        let ctx = rule.term_context.as_ref().unwrap();
        assert_eq!(ctx.len(), 2);
        
        // First param: n:Name
        match &ctx[0] {
            TermParam::Simple { name, ty } => {
                assert_eq!(name.to_string(), "n");
                assert!(matches!(ty, TypeExpr::Base(id) if id == "Name"));
            }
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
                    }
                    _ => panic!("Expected Arrow type"),
                }
            }
            _ => panic!("Expected Abstraction param for ^x.p"),
        }
        
        // Check syntax pattern
        let pattern = rule.syntax_pattern.as_ref().unwrap();
        // Should have: Literal("for"), Literal("("), Ident(x), Literal("<-"), Ident(n), Literal(")"), Literal("{"), Ident(p), Literal("}")
        assert_eq!(pattern.len(), 9, "Pattern should have 9 tokens");
        assert!(matches!(&pattern[0], SyntaxToken::Literal(s) if s == "for"));
        assert!(matches!(&pattern[1], SyntaxToken::Literal(s) if s == "("));
        assert!(matches!(&pattern[2], SyntaxToken::Ident(id) if id == "x"));
        assert!(matches!(&pattern[3], SyntaxToken::Literal(s) if s == "<-"));
        assert!(matches!(&pattern[4], SyntaxToken::Ident(id) if id == "n"));
        assert!(matches!(&pattern[5], SyntaxToken::Literal(s) if s == ")"));
        assert!(matches!(&pattern[6], SyntaxToken::Literal(s) if s == "{"));
        assert!(matches!(&pattern[7], SyntaxToken::Ident(id) if id == "p"));
        assert!(matches!(&pattern[8], SyntaxToken::Literal(s) if s == "}"));
    }

    #[test]
    fn parse_new_syntax_multi_abstraction() {
        // Multi-binder: ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- ...
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestMulti,
            exports { Proc Name }
            terms {
                PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- "inputs" "(" xs "," ns ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Failed to parse multi-abstraction: {:?}", result.err());

        let theory = result.unwrap();
        let rule = &theory.terms[0];
        
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
                    }
                    _ => panic!("Expected Collection type"),
                }
            }
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
                    }
                    _ => panic!("Expected Arrow type"),
                }
            }
            _ => panic!("Expected MultiAbstraction param"),
        }
    }

    #[test]
    fn parse_old_syntax_still_works() {
        // Old syntax should still work
        let input = quote! {
            name: TestOld,
            exports { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Old syntax should still work: {:?}", result.err());

        let theory = result.unwrap();
        assert_eq!(theory.terms.len(), 2);
        
        // Old syntax should have term_context = None
        assert!(theory.terms[0].term_context.is_none());
        assert!(theory.terms[1].term_context.is_none());
    }

    #[test]
    fn parse_mixed_syntax() {
        // Mix of old and new syntax
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestMixed,
            exports { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Mixed syntax should work: {:?}", result.err());

        let theory = result.unwrap();
        
        // First rule: old syntax
        assert!(theory.terms[0].term_context.is_none());
        
        // Second rule: new syntax
        assert!(theory.terms[1].term_context.is_some());
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
            exports { Proc Name }
            terms {
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok());

        let theory = result.unwrap();
        let rule = &theory.terms[0];
        
        let pattern = rule.syntax_pattern.as_ref().unwrap();
        
        // Pattern should be: Literal("for"), Literal("("), Ident(x), Literal("<-"), Ident(n), ...
        // Find parameter references (unquoted identifiers) in the pattern
        let param_refs: Vec<_> = pattern.iter()
            .filter_map(|t| match t {
                SyntaxToken::Ident(id) => Some(id.to_string()),
                _ => None,
            })
            .collect();
        
        // Only parameter references should be Ident tokens (not "for" which is now Literal)
        assert!(param_refs.contains(&"x".to_string()), "Should contain param 'x'");
        assert!(param_refs.contains(&"n".to_string()), "Should contain param 'n'");
        assert!(param_refs.contains(&"p".to_string()), "Should contain param 'p'");
        assert!(!param_refs.contains(&"for".to_string()), "'for' should be Literal, not Ident");
        
        // Find literals in the pattern
        let literals: Vec<_> = pattern.iter()
            .filter_map(|t| match t {
                SyntaxToken::Literal(s) => Some(s.clone()),
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
        use crate::codegen::parser::generate_lalrpop_grammar;
        
        // All syntax literals must be quoted strings
        let input = quote! {
            name: TestGrammar,
            exports { Proc Name }
            terms {
                PZero . Proc ::= "0" ;
                PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
            }
        };

        let result = parse2::<TheoryDef>(input);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let theory = result.unwrap();
        let grammar = generate_lalrpop_grammar(&theory);
        
        println!("Generated Grammar:\n{}", grammar);
        
        // Verify the grammar contains the expected elements
        assert!(grammar.contains("\"for\""), "Grammar should contain 'for' literal");
        assert!(grammar.contains("\"<-\""), "Grammar should contain '<-' literal");
        assert!(grammar.contains("<n:Name>") || grammar.contains("<n: Name>"), 
                "Grammar should capture 'n' as Name");
        assert!(grammar.contains("<x:Ident>") || grammar.contains("<x: Ident>"), 
                "Grammar should capture binder 'x' as Ident");
        assert!(grammar.contains("<p:Proc>") || grammar.contains("<p: Proc>"), 
                "Grammar should capture body 'p' as Proc");
        assert!(grammar.contains("Scope"), "Grammar should create Scope for binding");
    }
}
