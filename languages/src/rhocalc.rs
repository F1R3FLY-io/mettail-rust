#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: RhoCalc,

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc;

        PDrop . n:Name |- "*" "(" n ")" : Proc ;

        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
        
        PInput . n:Name, ^x.p:[Name -> Proc] |- n "?" x "." "{" p "}" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
            |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name ;
    },

    equations {
        (NQuote (PDrop N)) = N ;
    },

    rewrites {
        (PPar {(PInput n ^x.p), (POutput n q), ...rest})
            ~> (PPar {(eval ^x.p (NQuote q)), ...rest});

        (PPar {(PInputs ns scope), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest}) 
            ~> (PPar {(eval scope qs.*map(|q| (NQuote q))), ...rest});

        (PDrop (NQuote P)) ~> P;

        if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    },
}