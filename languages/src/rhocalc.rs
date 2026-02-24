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
        ![bool] as Bool
        ![str] as Str
    },

    terms {
        PZero .
        |- "{}" : Proc;

        PDrop . n:Name  |- "*" "(" n ")" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        POutput . n:Name, q:Proc
        |- n "!" "(" q ")" : Proc ;

        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;

        NQuote . p:Proc
        |- "@" "(" p ")" : Name ;

        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;

        // customize error handling 
        // (e.g. filter results by =/= Err)
        Err . |- "error" : Proc;

        // cast rust-native types as processes
        CastInt . k:Int |- k : Proc;
        CastFloat . k:Float |- k : Proc;
        CastBool . k:Bool |- k : Proc;
        CastStr . s:Str |- s : Proc;

        // and invoke any methods on them
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

        Eq . a:Proc, b:Proc |- a "==" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i == j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x == y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Ne . a:Proc, b:Proc |- a "!=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i != j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x != y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Gt . a:Proc, b:Proc |- a ">" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i > j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x > y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Lt . a:Proc, b:Proc |- a "<" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i < j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x < y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        GtEq . a:Proc, b:Proc |- a ">=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i >= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x >= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        LtEq . a:Proc, b:Proc |- a "<=" b : Proc ![
            { match (&a, &b) {
                (Proc::CastInt(a), Proc::CastInt(b)) => match (&**a, &**b) {
                    (Int::NumLit(i), Int::NumLit(j)) => Proc::CastBool(Box::new(Bool::BoolLit(i <= j))),
                    _ => Proc::Err,
                },
                (Proc::CastFloat(a), Proc::CastFloat(b)) => match (&**a, &**b) {
                    (Float::FloatLit(x), Float::FloatLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(x <= y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Not . a:Proc |- "not" a : Proc ![
            { match &a {
                Proc::CastBool(b) => match &**b {
                    Bool::BoolLit(v) => Proc::CastBool(Box::new(Bool::BoolLit(!v))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        And . a:Proc, b:Proc |- a "and" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(*x && *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Or . a:Proc, b:Proc |- a "or" b : Proc ![
            { match (&a, &b) {
                (Proc::CastBool(a), Proc::CastBool(b)) => match (&**a, &**b) {
                    (Bool::BoolLit(x), Bool::BoolLit(y)) => Proc::CastBool(Box::new(Bool::BoolLit(*x || *y))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ConcatStr . a:Proc, b:Proc |- "concat" "(" a "," b ")" : Proc ![
            { match (&a, &b) {
                (Proc::CastStr(a), Proc::CastStr(b)) => match (&**a, &**b) {
                    (Str::StringLit(x), Str::StringLit(y)) => Proc::CastStr(Box::new(Str::StringLit(format!("{}{}", x, y)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        Len . p:Proc |- "len" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(inner) => match &**inner {
                    Str::StringLit(x) => Proc::CastInt(Box::new(Int::NumLit(x.len() as i64))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToInt . p:Proc |- "int" "(" p ")" : Proc ![
            { match &p {
                Proc::CastInt(x) => Proc::CastInt(x.clone()),
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastInt(Box::new(Int::NumLit(f.get() as i64))),
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastInt(Box::new(Int::NumLit(if *b { 1 } else { 0 }))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastInt(Box::new(Int::NumLit(s.parse().unwrap_or(0)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToFloat . p:Proc |- "float" "(" p ")" : Proc ![
            { match &p {
                Proc::CastFloat(x) => Proc::CastFloat(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(*i as f64)))),
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(if *b { 1.0 } else { 0.0 })))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastFloat(Box::new(Float::FloatLit(mettail_runtime::CanonicalFloat64::from(s.parse::<f64>().unwrap_or(0.0))))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToBool . p:Proc |- "bool" "(" p ")" : Proc ![
            { match &p {
                Proc::CastBool(x) => Proc::CastBool(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastBool(Box::new(Bool::BoolLit(*i != 0))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastBool(Box::new(Bool::BoolLit(f.get() != 0.0))),
                    _ => Proc::Err,
                },
                Proc::CastStr(x) => match &**x {
                    Str::StringLit(s) => Proc::CastBool(Box::new(Bool::BoolLit(s.parse::<bool>().unwrap_or(false)))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        ToStr . p:Proc |- "str" "(" p ")" : Proc ![
            { match &p {
                Proc::CastStr(x) => Proc::CastStr(x.clone()),
                Proc::CastInt(x) => match &**x {
                    Int::NumLit(i) => Proc::CastStr(Box::new(Str::StringLit(i.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastFloat(x) => match &**x {
                    Float::FloatLit(f) => Proc::CastStr(Box::new(Str::StringLit(f.to_string()))),
                    _ => Proc::Err,
                },
                Proc::CastBool(x) => match &**x {
                    Bool::BoolLit(b) => Proc::CastStr(Box::new(Str::StringLit(b.to_string()))),
                    _ => Proc::Err,
                },
                _ => Proc::Err,
            }}
        ] fold;

        
    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;
    },

    rewrites {

        // communication:
        // (n1 ? x1 , ... , nk ? xk).{ p } | n1!(q1) | ... | nk!(qk) ~> p(@q1,...,@qk)
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});

        Exec . |- (PDrop (NQuote P)) ~> P;

        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});

        // TODO: shorthand to make these in the term declarations
        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);

        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);

        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);

        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);

        MulCongL . | S ~> T |- (Mul S X) ~> (Mul T X);

        MulCongR . | S ~> T |- (Mul X S) ~> (Mul X T);

        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);

        DivCongR . | S ~> T |- (Div X S) ~> (Div X T);

        EqCongL . | S ~> T |- (Eq S X) ~> (Eq T X);
        EqCongR . | S ~> T |- (Eq X S) ~> (Eq X T);
        NeCongL . | S ~> T |- (Ne S X) ~> (Ne T X);
        NeCongR . | S ~> T |- (Ne X S) ~> (Ne X T);
        GtCongL . | S ~> T |- (Gt S X) ~> (Gt T X);
        GtCongR . | S ~> T |- (Gt X S) ~> (Gt X T);
        LtCongL . | S ~> T |- (Lt S X) ~> (Lt T X);
        LtCongR . | S ~> T |- (Lt X S) ~> (Lt X T);
        GtEqCongL . | S ~> T |- (GtEq S X) ~> (GtEq T X);
        GtEqCongR . | S ~> T |- (GtEq X S) ~> (GtEq X T);
        LtEqCongL . | S ~> T |- (LtEq S X) ~> (LtEq T X);
        LtEqCongR . | S ~> T |- (LtEq X S) ~> (LtEq X T);

        NotCong . | S ~> T |- (Not S) ~> (Not T);
        AndCongL . | S ~> T |- (And S X) ~> (And T X);
        AndCongR . | S ~> T |- (And X S) ~> (And X T);
        OrCongL . | S ~> T |- (Or S X) ~> (Or T X);
        OrCongR . | S ~> T |- (Or X S) ~> (Or X T);

        ConcatStrCongL . | S ~> T |- (ConcatStr S X) ~> (ConcatStr T X);
        ConcatStrCongR . | S ~> T |- (ConcatStr X S) ~> (ConcatStr X T);
        LenCong . | S ~> T |- (Len S) ~> (Len T);

        ToIntCong . | S ~> T |- (ToInt S) ~> (ToInt T);
        ToFloatCong . | S ~> T |- (ToFloat S) ~> (ToFloat T);
        ToBoolCong . | S ~> T |- (ToBool S) ~> (ToBool T);
        ToStrCong . | S ~> T |- (ToStr S) ~> (ToStr T);
    },

    logic {
        // many-step to a result
        relation path(Proc, Proc);
        path(p0, p1) <-- rw_proc(p0, p1);
        path(p0, p2) <-- path(p0, p1), path(p1, p2);

        // or we can store every step!
        relation path_vec(Vec<Proc>);
        path_vec(xs) <-- 
            proc(x0), rw_proc(x0,x1), 
            let xs = vec![x0.clone(), x1.clone()];
        path_vec(zs) <--
            path_vec(xs), path_vec(ys), 
            if xs.last() == ys.first(), 
            let zs = [xs.as_slice(), ys.as_slice()].concat();

        // paths where term size (display length) strictly decreases at every step
        // TODO: currently makes execution slow; investigate why
        // relation shrinking_path(Vec<Proc>);
        // shrinking_path(xs) <--
        //     path_vec(xs),
        //     if xs.windows(2).all(|w| w[0].to_string().len() > w[1].to_string().len());

        // context-labelled transition system:
        // p -c-> q if c(p)~>q
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

        // contexts for testing (TODO: auto-generate)
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
        // proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

        // rules to add c(p) to the set of processes
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

        // relation garbage(Name,Proc);
        // garbage(n,p) <--
        //     proc(p),name(n),
        //     !(proc(k), trans(p,k,q), can_comm(q,n));
    },
}
