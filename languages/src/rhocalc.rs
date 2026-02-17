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
        ![f64] as Float

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

        Add . a:Proc, b:Proc |- a "+" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() + *b.clone())),
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        Sub . a:Proc, b:Proc |- a "-" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() - *b.clone())),
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() - *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        Mul . a:Proc, b:Proc |- a "*" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() * *b.clone())),
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() * *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        Div . a:Proc, b:Proc |- a "/" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() / *b.clone())),
                (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() / *b.clone())),
                _ => Proc::Err,
            }}
        ] fold;

        CastInt . k:Int |- k : Proc;
        CastFloat . k:Float |- k : Proc;

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

        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);

        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);

        MulCongL . | S ~> T |- (Mul S X) ~> (Mul T X);

        MulCongR . | S ~> T |- (Mul X S) ~> (Mul X T);

        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);

        DivCongR . | S ~> T |- (Div X S) ~> (Div X T);
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
