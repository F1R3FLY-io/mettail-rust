#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::theory;

// Simple integer calculator theory: supports integer literals, + and -
// Uses native i32 type for direct integer support
theory! {
    name: Calculator,
    exports {
        ![i32] as Int
    },
    terms {
        // Variables are now auto-generated as IVar - no explicit declaration needed
        // Literals (NumLit) are now auto-generated for native types - no explicit declaration needed
        // No need for "NumLit . Int ::= Integer" - it's automatic!

        Add . Int ::= Int "+" Int ;
        Sub . Int ::= Int "-" Int ;

        // Assign is now automatically generated for all categories
    },
    equations {
    },
    rewrites {
        // Variable substitution and Assign congruence are now auto-generated
        // Congruence rules: propagate rewrites through Add and Sub
        if S => T then (Add S R) => (Add T R);
        if S => T then (Add L S) => (Add L T);
        if S => T then (Sub S R) => (Sub T R);
        if S => T then (Sub L S) => (Sub L T);
    },
    semantics {
        Add: +,
        Sub: -,
    }
}


