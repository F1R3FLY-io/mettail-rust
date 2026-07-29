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
    // #96 (Cardelli-Gordon alignment, SIGNATURE; extends the A-S5.4b equation audit below).
    // Normative source: Luca Cardelli and Andrew D. Gordon, "Mobile Ambients", FoSSaCS 1998,
    // LNCS 1378, 140-155, DOI 10.1007/BFb0053547. Section 2 is the mobility-primitives
    // calculus this block models; section 3 (communication) is out of scope. Every
    // declaration below now carries its verdict against the paper — `C-G verbatim` where the
    // paper has the same construct, `EXTENSION` where this fragment adds or reshapes one, and
    // `ABSENT` where the paper has something this fragment declines — so a reader of the
    // SOURCE, not only of the page, can tell which is which. The construct-by-construct audit,
    // with the paper quoted in full, is `docs/languages/ambient.md` sections 6.1-6.4.
    terms {
        // C-G `0` inactivity — VERBATIM as a term. The Zero LAWS are a separate matter and are
        // ABSENT: neither (Struct Zero Par) `P | 0 = P` nor (Struct Zero Res) `(n)0 = 0` is
        // declared, so `{P | 0}` is a two-member bag distinct from `P` (ambient.md 6.4).
        PZero . Proc ::= "0" ;

        // ** EXTENSION — CAPABILITY/PREFIX FUSION. NOT the C-G signature. **
        //
        // The paper makes the capability a syntactic category of its OWN and applies it with a
        // SEPARATE action former: `P ::= ... | M.P` with `M ::= in n | out n | open n`. `M` is
        // first-class there — the paper gives it its own free-name function
        // (`fn(in n) = fn(out n) = fn(open n) = {n}`, and `fn(M.P) = fn(M) u fn(P)`), which is
        // only well-formed if `M` is a category. Here the two layers are FUSED: `PIn`/`POut`/
        // `POpen` are arity-2 PROCESS formers over (Name, Proc), and `M` exists as no sort.
        //
        // Over section 2 the fusion is CONSERVATIVE, which is why it is admissible: `M` ranges
        // over exactly the three atomic capabilities, so `M.P` and the three formers stand in
        // bijection, and (Struct Action) `P = Q ==> M.P = M.Q` holds BY CONSTRUCTION instead of
        // as a declared axiom.
        //
        // BUYS: one distinct AST head symbol per capability, so the positional set automaton
        // dispatches on the head alone — matching `(PIn M P)` is one symbol test, where `M.P`
        // would mean descending into a capability subterm and discriminating there. That is
        // also what lets the three rewrites below lower as flat AC patterns.
        //
        // FORECLOSES the paper's section-3 layer, every capability feature of which needs `M`
        // to be a value: capability VARIABLES (section 3 writes `P{x <- M}`), PATH FORMATION
        // `(M.M').P` (section 3; nest the formers instead — `in(l1, in(l2, 0))` — operationally
        // the same, but not a capability VALUE), and capability COMMUNICATION. Section 3 is out
        // of scope for this fragment in any case. See ambient.md 6.3 Extension 1.
        PIn . Proc ::= "in(" Name "," Proc ")";
        POut . Proc ::= "out(" Name "," Proc ")";
        POpen . Proc ::= "open(" Name "," Proc ")";

        // C-G `n[P]` ambient — VERBATIM.
        PAmb . Proc ::= Name "[" Proc "]";

        // C-G `(n)P` restriction — VERBATIM: a genuine binder over the `Name` sort. This is the
        // one rule that needs the judgement form, because only that form can declare a binder's
        // arrow type; the commented legacy line is kept for legibility, not as a pending task.
        // PNew . Proc ::= "new(" <Name> "," Proc ")";
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;

        // C-G `P | Q` composition — VERBATIM, with (Struct Par Comm) and (Struct Par Assoc)
        // REPRESENTATIONAL rather than axiomatic: the `HashBag` carrier makes both hold by
        // construction, so neither is declared as an equation below. Note `n[p]` and `n[{p}]`
        // are DISTINCT terms — the capability rewrites fire only on bag-bodied ambients.
        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;

        // ABSENT by design: C-G `!P` REPLICATION, and with it (Struct Repl Par) and
        // (Struct Zero Repl). The fragment is finitary. That absence is load-bearing for the
        // capability-prefix float extensions below: the paper's one explicitly-INVALID
        // restriction float, `!(n)P =/= (n)!P`, cannot even be stated here (ambient.md 6.4).
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

        // C-G (Red Open): open n.P | n[Q] -> P | Q — verbatim modulo the bag-body convention.
        // {open(n,p), n[q]} => {p, q}
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P,Q, ...rest});

        // C-G (Red Par): P -> Q ==> P | R -> Q | R — verbatim; `...rest` is the paper's `R`.
        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        // C-G (Red Res): P -> Q ==> (n)P -> (n)Q — verbatim. `^x.S` here is a PATTERN-level
        // abstraction: the LHS opens the scope and names the body `S`, the RHS re-closes over
        // the same binder with the reduced body.
        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T);
        // C-G (Red Amb): P -> Q ==> n[P] -> n[Q] — verbatim.
        AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);

        // ABSENT and CORRECTLY so: there is no capability congruence (`InCong` and friends).
        // C-G declares no rule permitting reduction UNDER a capability prefix — actions are
        // inert until exercised — so the absence is fidelity, not an omission. (Red =) is
        // realised operationally, by the float normalising before matching, not as a rule.
    }
}
