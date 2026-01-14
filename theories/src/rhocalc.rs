#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::theory;

// RhoCalc Theory Definition
theory! {
    name: RhoCalc,

    exports {
        Proc
        Name
    },

    terms {
        // PZero . Proc ::= "0" ;
        PZero . |- "0" : Proc;

        PDrop . n:Name |- "*" "(" n ")" : Proc ;

        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
        
        PInput . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;

        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
        // [TODO] PPar . ps:Bag(Proc) |- "{" ps.#sep("|") "}" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name ;
    },

    equations {
        (NQuote (PDrop N)) == N ;
    },

    rewrites {
        // communication
         (PPar {(PInput N x P), (POutput N Q)})
            => (PPar {(subst P x (NQuote Q))});

        (PDrop (NQuote P)) => P;

        if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest});
    },
}

//// GENERATED ////
