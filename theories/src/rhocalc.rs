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
        PZero . Proc ::= "0" ;
        PDrop . Proc ::= "*" "(" Name ")" ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        // PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
        PInput . n:Name, ^x.p:[Name -> Proc] |- for(x<-n){p} : Proc ;

        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;

        NQuote . Name ::= "@" "(" Proc ")" ;
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
