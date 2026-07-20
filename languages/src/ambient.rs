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
    // A-S5.4b (Cardelli–Gordon alignment; USER MA mandate): the structural congruence is the
    // C-G table (Mobile Ambients) with three exact axioms and three documented sound extensions.
    // Every float premise is the CAPTURE-AVOIDANCE condition `x # N` (freshness on the
    // floated-past material), never the vacuous-binder condition `x # P` the pre-A-S5.4b
    // declaration carried. `x # N ⟺ x ∉ fn(N) ⟺ x ≠ N` here because `Name` is variable-only
    // (`fn(N) = {N}`). Verification: scratchpad `a_s5_design/ma_theory_alignment.md`.
    equations {
        // (Struct Res Res): (n)(m)P ≡ (m)(n)P — C-G verbatim, premise-free.
        NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
        // (Struct Res Par): (n)(P | Q) ≡ P | (n)Q if n ∉ fn(P) — C-G verbatim, lifted to the
        // AC bag (freshness on the floated-past residual `...rest`).
        ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
        // Capability-prefix floats: NOT C-G axioms — documented sound extensions (capability
        // prefixes are inert until exercised) with the capture-avoidance condition `x # N`.
        InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
        OutNew . | x # N |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
        OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
        // (Struct Res Amb): (n)(m[P]) ≡ m[(n)P] if n ≠ m — C-G verbatim (`x # N` = `x ≠ N`
        // on the atomic Name).
        AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
    },
    rewrites {
        // C-G (Red In): n[in m.P | Q] | m[R] → m[n[P | Q] | R]
        // {n[{in(m,p), ...q}], m[r]} => {m[{n[{p, ...q}], r}]}
        InRule . |- (PPar {(PAmb N (PPar {(PIn M P) , ...rest1})) , (PAmb M R), ...rest2})
            ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P , ...rest1})), R})), ...rest2});

        // C-G (Red Out): m[n[out m.P | Q] | R] → n[P | Q] | m[R] — the residual R stays
        // INSIDE m. A-S5.4b (AM-1, USER approved): `...rest2` is the WHOLE residual, kept
        // inside M on the RHS; empty rest is legal, so the singleton `m[{n[{out(m,p)}]}]`
        // fires to `{n[{p}], m[{}]}` (`m[{}]` vs C-G `m[0]` is the documented `{}`/`0`
        // fragment deviation). The pre-A-S5.4b declaration ejected `...rest2` through the
        // ambient membrane (boundary ejection, not derivable in C-G) and could never fire
        // on a singleton body.
        // m[{n[{out(m,p), ...q}], ...r}] => {n[{p, ...q}], m[{...r}]}
        OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), ...rest2})) ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))});

        // {open(n,p), n[q]} => {p, q}
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P,Q, ...rest});

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T);
        AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);
    }
}
