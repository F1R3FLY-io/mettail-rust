#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Lambda,

    types {
        // Proc
        // Name
        Term
    },

    terms {
        Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;

        App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
    },

    equations {
        // extensionality?
    },

    rewrites {
        (App (Lam fun) arg) ~> (eval fun arg);
        if M0 ~> M1 then (App M0 N) ~> (App M1 N);
        if N0 ~> N1 then (App M N0) ~> (App M N1);
        if S ~> T then (Lam ^x.S) ~> (Lam ^x.T);
    },
}
