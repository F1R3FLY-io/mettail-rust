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
    },

    terms {
        PZero . 
        |- "{}" : Proc;

        PDrop . n:Name 
        |- "*" "(" n ")" : Proc ;

        PPar . ps:HashBag(Proc) 
        |- "{" ps.*sep("|") "}" : Proc;

        POutput . n:Name, q:Proc 
        |- n "!" "(" q ")" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        NQuote . p:Proc 
        |- "@" "(" p ")" : Name ;

        Add . a:Proc, b:Proc |- a "+" b : Proc ![{
            if let Proc::CastInt(a) = a {
                if let Proc::CastInt(b) = b {
                    Proc::CastInt(Box::new(*a.clone() + *b.clone()))
                }
                else {
                    Proc::Err
                }
            } else {
                Proc::Err
            }
        }] fold;

        CastInt . k:Int |- k : Proc;

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
        proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
        proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

        // Only apply contexts to the stepped term (step_term), so res is bounded and rw_proc(res,q) can be computed.
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
            let res = app.normalize();
            
        proc(res) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(Box::new(c.clone()), vec![p.clone()]),
            let res = app.normalize();
            
        relation path(Proc, Proc);
        path(p0, p1) <-- rw_proc(p0, p1);
        path(p0, p2) <-- path(p0, p1), path(p1, p2);

        relation trans(Proc, Proc, Proc);
        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::LamProc(_) = c,
            let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
            let res = app.normalize(),
            path(res.clone(), q);

        trans(p,c,q) <--
            step_term(p), proc(c),
            if let Proc::MLamProc(_) = c,
            let app = Proc::MApplyProc(Box::new(c.clone()), vec![p.clone()]),
            let res = app.normalize(),
            path(res.clone(), q);
    },
}
