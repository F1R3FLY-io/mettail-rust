use mettail_languages::rhocalc::{Name, Proc};
use mettail_runtime::{Binder, FreeVar, Scope};

type Var = FreeVar<String>;

// #[test]
// fn test_multi_substitute() {
//     // Create free variables
//     let x_var: Var = FreeVar::fresh_named("x");
//     let y_var: Var = FreeVar::fresh_named("y");
    
//     // Create a process: *(@(x)) | *(@(y))
//     // This represents a parallel composition of two dereferences of quoted variables
//     use mettail_runtime::HashBag;
    
//     let x_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x_var.clone())));
//     let y_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(y_var.clone())));
    
//     let drop_x = Proc::PDrop(Box::new(x_name.clone()));
//     let drop_y = Proc::PDrop(Box::new(y_name.clone()));
    
//     let mut bag = HashBag::new();
//     bag.insert(drop_x);
//     bag.insert(drop_y);
//     let par = Proc::PPar(bag);
    
//     // Create replacement names: @(0) and @(0)
//     let zero = Proc::PZero;
//     let repl_x = Name::NQuote(Box::new(zero.clone()));
//     let repl_y = Name::NQuote(Box::new(zero.clone()));
    
//     // Perform multi-substitution
//     let result = par.multi_substitute_name(
//         &[&x_var, &y_var],
//         &[repl_x.clone(), repl_y.clone()]
//     );
    
//     // The result should have both x and y replaced with @(0)
//     // Check that it's a PPar
//     if let Proc::PPar(result_bag) = result {
//         // Both elements should now be *(@(0)) 
//         assert_eq!(result_bag.len(), 2);
//         for (elem, _count) in result_bag.iter() {
//             if let Proc::PDrop(inner_name) = elem {
//                 // inner_name should be @(0), not a variable
//                 assert!(matches!(inner_name.as_ref(), Name::NQuote(_)));
//             } else {
//                 panic!("Expected PDrop, got {:?}", elem);
//             }
//         }
//     } else {
//         panic!("Expected PPar, got {:?}", result);
//     }
// }

// #[test]
// fn test_multi_substitute_shadowing() {
//     // Create free variables
//     let x_var: Var = FreeVar::fresh_named("x");
//     let _y_var: Var = FreeVar::fresh_named("y");
    
//     // Create a process: n?x.{*(@(x))}
//     // where x is bound by the input, so substituting for x should NOT affect it
    
//     let n_var: Var = FreeVar::fresh_named("n");
//     let n_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n_var.clone())));
    
//     // The inner x variable in the scope - this should be bound, not free
//     let inner_x = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x_var.clone())));
//     let body = Proc::PDrop(Box::new(inner_x));
    
//     // Create the binder scope
//     let binder = Binder(x_var.clone());
//     let scope = Scope::new(vec![binder], Box::new(body));
    
//     let input_proc = Proc::PInputs(vec![n_name], scope);
    
//     // Create replacement: @(0)
//     let zero = Proc::PZero;
//     let repl_x = Name::NQuote(Box::new(zero));
    
//     // Substitute x -> @(0)
//     // Since x is bound by the input, this should NOT replace the x in the body
//     let result = input_proc.multi_substitute_name(
//         &[&x_var],
//         &[repl_x]
//     );
    
//     // The structure should be the same (x was shadowed)
//     if let Proc::PInputs(_, result_scope) = result {
//         let (result_binder, result_body) = result_scope.unbind();
//         // The body should still have a variable (the bound one), not @(0)
//         if let Proc::PDrop(inner) = result_body.as_ref() {
//             // This is subtle: after unbinding, we get a fresh variable
//             // The key point is that it's NOT NQuote
//             assert!(matches!(inner.as_ref(), Name::NVar(_)));
//         } else {
//             panic!("Expected PDrop in body, got {:?}", result_body);
//         }
//     } else {
//         panic!("Expected PInput, got {:?}", result);
//     }
// }

// /// Test empty multi_substitute returns original term
// #[test]
// fn test_multi_substitute_empty() {
//     let zero = Proc::PZero;
//     let result = zero.multi_substitute(&[], &[]);
//     assert_eq!(zero, result);
// }

// /// Test PInputs construction with multiple binders
// #[test]
// fn test_pinputs_multi_binder_construction() {
//     // Create: for(x0 <- n0, x1 <- n1){ *(@(x0)) | *(@(x1)) }
//     let x0_var: Var = FreeVar::fresh_named("x0");
//     let x1_var: Var = FreeVar::fresh_named("x1");
//     let n0_var: Var = FreeVar::fresh_named("n0");
//     let n1_var: Var = FreeVar::fresh_named("n1");
    
//     // Channel names
//     let n0_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n0_var.clone())));
//     let n1_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n1_var.clone())));
    
//     // Body: { *(@(x0)) | *(@(x1)) }
//     use mettail_runtime::HashBag;
//     let x0_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x0_var.clone())));
//     let x1_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x1_var.clone())));
//     let drop_x0 = Proc::PDrop(Box::new(x0_name));
//     let drop_x1 = Proc::PDrop(Box::new(x1_name));
//     let mut body_bag = HashBag::new();
//     body_bag.insert(drop_x0);
//     body_bag.insert(drop_x1);
//     let body = Proc::PPar(body_bag);
    
//     // Multi-binder scope with x0, x1
//     let binders = vec![Binder(x0_var.clone()), Binder(x1_var.clone())];
//     let scope = Scope::new(binders, Box::new(body));
    
//     // Construct PInputs
//     let pinputs = Proc::PInputs(vec![n0_name, n1_name], scope);
    
//     // Verify structure
//     if let Proc::PInputs(names, scope) = pinputs {
//         assert_eq!(names.len(), 2);
//         let (binders, _body) = scope.unbind();
//         assert_eq!(binders.len(), 2);
//     } else {
//         panic!("Expected PInputs");
//     }
// }

// /// Test multi-substitution with PInputs multi-binder shadowing
// #[test]
// fn test_pinputs_multi_binder_shadowing() {
//     // Create: for(x0 <- n0, x1 <- n1){ *(@(x0)) | *(@(x1)) }
//     // Then substitute x0 -> @(0), x1 -> @(0)
//     // The x0, x1 in the body should NOT be replaced (they're bound)
//     let x0_var: Var = FreeVar::fresh_named("x0");
//     let x1_var: Var = FreeVar::fresh_named("x1");
//     let n0_var: Var = FreeVar::fresh_named("n0");
//     let n1_var: Var = FreeVar::fresh_named("n1");
    
//     let n0_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n0_var)));
//     let n1_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n1_var)));
    
//     use mettail_runtime::HashBag;
//     let x0_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x0_var.clone())));
//     let x1_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(x1_var.clone())));
//     let drop_x0 = Proc::PDrop(Box::new(x0_name));
//     let drop_x1 = Proc::PDrop(Box::new(x1_name));
//     let mut body_bag = HashBag::new();
//     body_bag.insert(drop_x0);
//     body_bag.insert(drop_x1);
//     let body = Proc::PPar(body_bag);
    
//     let binders = vec![Binder(x0_var.clone()), Binder(x1_var.clone())];
//     let scope = Scope::new(binders, Box::new(body));
//     let pinputs = Proc::PInputs(vec![n0_name, n1_name], scope);
    
//     // Substitutions: x0 -> @(0), x1 -> @(0)
//     let zero = Proc::PZero;
//     let repl0 = Name::NQuote(Box::new(zero.clone()));
//     let repl1 = Name::NQuote(Box::new(zero));
    
//     let result = pinputs.multi_substitute_name(
//         &[&x0_var, &x1_var],
//         &[repl0, repl1]
//     );
    
//     // x0 and x1 are bound by PInputs, so body should be unchanged
//     if let Proc::PInputs(_, result_scope) = result {
//         let (_binders, result_body) = result_scope.unbind();
//         if let Proc::PPar(bag) = result_body.as_ref() {
//             // Body should still have NVar (not NQuote) since x0, x1 were shadowed
//             for (elem, _) in bag.iter() {
//                 if let Proc::PDrop(inner) = elem {
//                     assert!(matches!(inner.as_ref(), Name::NVar(_)), 
//                         "Expected NVar (bound variable), got {:?}", inner);
//                 }
//             }
//         } else {
//             panic!("Expected PPar body");
//         }
//     } else {
//         panic!("Expected PInputs");
//     }
// }

// #[test]
// fn test_pinputs_display() {
//     let x0_var: Var = FreeVar::fresh_named("x0");
//     let x1_var: Var = FreeVar::fresh_named("x1");
//     let n0_var: Var = FreeVar::fresh_named("n0");
//     let n1_var: Var = FreeVar::fresh_named("n1");
    
//     let n0_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n0_var)));
//     let n1_name = Name::NVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(n1_var)));
    
//     let body = Proc::PZero;
//     let binders = vec![Binder(x0_var), Binder(x1_var)];
//     let scope = Scope::new(binders, Box::new(body));
//     let pinputs = Proc::PInputs(vec![n0_name, n1_name], scope);
    
//     // Check that display produces expected format
//     let display = format!("{}", pinputs);
    
//     // Should contain "for" and the binder-channel pairs
//     assert!(display.contains("for"), "Display should contain 'for': {}", display);
//     assert!(display.contains("<-"), "Display should contain '<-': {}", display);
// }
