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
        ![i64] as Int
        // ![f64] as Float


    },

    terms {
        PZero . 
        |- "{}" : Proc;

        PDrop . n:Name 
        |- "*" "(" n ")" : Proc ;

        POutput . n:Name, q:Proc 
        |- n "!" "(" q ")" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        PPar . ps:HashBag(Proc) 
        |- "{" ps.*sep("|") "}" : Proc;

        NQuote . p:Proc 
        |- "@" "(" p ")" : Name ;

        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            {if let Proc::CastInt(a) = a {
                if let Proc::CastInt(b) = b {
                    Proc::CastInt(Box::new(*a.clone() + *b.clone()))
                }
                else {
                    Proc::Err
                }
            } else {
                Proc::Err
            }}
        ] fold;

        CastInt . k:Int |- k : Proc;
        // CastFloat . k:Float |- k : Proc;

        Err . |- "error" : Proc;
    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;
    },

    rewrites {
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});

        Exec . |- (PDrop (NQuote P)) ~> P;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);

        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);
    },

    logic {

        // relation garbage(Name,Proc);
        // garbage(n,p) <--
        //     proc(p),
        //     if let Proc::PPar(elems) = p,
        //     for (elem, _) in elems.iter(),
        //     if let Proc::PNew();


        relation rw_weight(Proc, Int, Proc);

        relation is_int(Proc);
        is_int(p) <--
            proc(p),
            if let Proc::CastInt(_) = p;
        
        // is_err(p) <-- 
        //     proc(p),
        //     if let Proc::Err = p;

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
