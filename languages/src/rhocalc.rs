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

        ![i32] as Int
    },

    terms {
        PZero . |- "0" : Proc;

        PDrop . n:Name |- "*" "(" n ")" : Proc ;

        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
            |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name ;

        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;
    },

    rewrites {
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});

        Exec . |- (PDrop (NQuote P)) ~> P;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    },

    logic {
        relation path(Proc, Proc);
        path(p0, p1) <-- rw_proc(p0, p1);
        path(p0, p2) <-- path(p0, p1), path(p1, p2);

        relation recvs_on(Proc, Name);
        recvs_on(p, n.clone()) <--
            proc(p),
            if let Proc::PInputs(ref ns, _) = p,
            for n in ns.iter();
        
        recvs_on(parent, n) <--
            ppar_contains(parent, elem),
            recvs_on(elem, n);
        
        relation loses_recv(Proc, Name);
        loses_recv(p, n) <--
            recvs_on(p, n),
            rw_proc(p, q),
            !recvs_on(q, n);
        
        relation live(Proc, Name);
        live(p, n) <--
            recvs_on(p, n),
            !loses_recv(p, n);
    },
}
