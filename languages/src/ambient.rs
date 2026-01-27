#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: Ambient,
    types {
        Proc
        Name
    },
    terms {
        PZero . Proc ::= "0" ;

        PIn . Proc ::= "in(" Name "," Proc ")";
        POut . Proc ::= "out(" Name "," Proc ")";
        POpen . Proc ::= "open(" Name "," Proc ")";

        PAmb . Proc ::= Name "[" Proc "]";
        
        // PNew . Proc ::= "new(" <Name> "," Proc ")";
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;

        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
    },
    equations {
        NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
        ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
        InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
        OutNew . | x # P |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
        OpenNew . | x # P |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
        AmbNew . | x # P |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
    },
    rewrites {
        // {n[{in(m,p), ...q}], m[r]} => {m[{n[{p, ...q}], r}]}
        InRule . |- (PPar {(PAmb N (PPar {(PIn M P) , ...rest1})) , (PAmb M R), ...rest2})
            ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P , ...rest1})), R})), ...rest2});

        // m[{n[{out(m,p), ...q}], r}] => {n[{p, ...q}], m[r]}
        OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
            ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2});

        // {open(n,p), n[q]} => {p, q}
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P,Q, ...rest});

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T);
        AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);
    }
}