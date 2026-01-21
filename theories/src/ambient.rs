#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::theory;

// Ambient Calculus Theory Definition
theory! {
    name: Ambient,
    exports {
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
        (PNew ^x.(PNew ^y.P)) == (PNew ^y.(PNew ^x.P));
        if x # ...rest then
        (PPar {(PNew ^x.P), ...rest}) == (PNew ^x.(PPar {P, ...rest}));
        if x # P then
        (PIn N (PNew ^x.P)) == (PNew ^x.(PIn N P));
        if x # P then
        (POut N (PNew ^x.P)) == (PNew ^x.(POut N P));
        if x # P then
        (POpen N (PNew ^x.P)) == (PNew ^x.(POpen N P));
        if x # P then
        (PAmb N (PNew ^x.P)) == (PNew ^x.(PAmb N P));
    },
    rewrites {
        // {n[{in(m,p), ...q}], m[r]} => {m[{n[{p, ...q}], r}]}
        (PPar {(PAmb N (PPar {(PIn M P) , ...rest1})) , (PAmb M R), ...rest2})
            => (PPar {(PAmb M (PPar {(PAmb N (PPar {P , ...rest1})), R})), ...rest2});

        // m[{n[{out(m,p), ...q}], r}] => {n[{p, ...q}], m[r]}
        (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
            => (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2});

        // {open(n,p), n[q]} => {p, q}
        (PPar {(POpen N P), (PAmb N Q), ...rest})
            => (PPar {P,Q, ...rest});

        if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest});

        if S => T then (PNew ^x.S) => (PNew ^x.T);
        if S => T then (PAmb N S) => (PAmb N T);
    }
}

//// GENERATED ////
