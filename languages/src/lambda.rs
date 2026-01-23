#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// Call-by-value Lambda Calculus
//
// Terms:
//   x           - variable
//   lam x.M     - abstraction (lambda)
//   (M N)       - application
//
// Values:
//   lam x.M     - abstractions are values
//
// CBV Reduction:
//   (lam x.M) V  ~>  M[x := V]   (when V is a value)
//
// We enforce CBV by only reducing when the argument matches Lam.

language! {
    name: Lambda,

    types {
        // Using Proc as main type (macro convention)
        Proc
        // Name type for quoted terms (enables full type infrastructure)
        Name
    },

    terms {
        // Abstraction: lam x.body
        Lam . ^x.body:[Proc -> Proc] |- "lam " x "." body : Proc;

        // Application: (M, N)
        App . fun:Proc, arg:Proc |- "(" fun "," arg ")" : Proc;
    },

    equations {
        // extensionality?
    },

    rewrites {
        // CBV beta reduction: only reduce when argument is a lambda (value)
        (App (Lam ^x.body) (Lam ^y.val))
            ~> (subst ^x.body (Lam ^y.val));

        // Congruence: reduce in function position
        if M0 ~> M1 then (App M0 N) ~> (App M1 N);

        // Congruence: reduce in argument position (CBV evaluates args)
        if N0 ~> N1 then (App M N0) ~> (App M N1);
    },
}
