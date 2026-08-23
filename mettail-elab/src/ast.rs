//! Surface AST for the frozen MeTTaIL module surface.
//!
//! Structure follows plan §3. The gaps enumerated in §3.4 appear here as:
//!   G1 `Builder::Types`
//!   G2 `Sort::Coll`
//!   G3 `Ast::Remainder`
//!   G4 `Ast::Abs` + `Ast::Subst` (two arguments)
//!   G5 handled in the parser: a body opening with a builder takes `Empty`
//!   G6 `Item::ArgRef` / `Item::Projection`

use crate::canonical::RhoValue;
use crate::lex::Span;

pub type Ident = String;
pub type Label = String;
pub type Cat = String;

#[derive(Clone, Debug)]
pub struct ModuleFile {
    pub imports: Vec<Import>,
    pub name: Ident,
    pub decls: Vec<TheoryDecl>,
    /// Every `theory <expr>` statement, in source order. The last one is the
    /// entry point (plan §3.2).
    pub instantiations: Vec<TheoryExpr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Import {
    /// `import "<url>" as u`
    ModuleAs { url: String, alias: Ident, span: Span },
    /// `import Monoid from "<url>"`
    FromModule { name: Ident, url: String, span: Span },
}

impl Import {
    pub fn url(&self) -> &str {
        match self {
            Import::ModuleAs { url, .. } | Import::FromModule { url, .. } => url,
        }
    }
    pub fn span(&self) -> Span {
        match self {
            Import::ModuleAs { span, .. } | Import::FromModule { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct TheoryDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub body: TheoryExpr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: Ident,
    pub ty: DottedPath,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DottedPath(pub Vec<Ident>);

impl DottedPath {
    pub fn last(&self) -> &str {
        self.0.last().map(|s| s.as_str()).unwrap_or("")
    }
    pub fn is_simple(&self) -> bool {
        self.0.len() == 1
    }
    pub fn render(&self) -> String {
        self.0.join(".")
    }
}

/// A theory expression. Atoms, postfix builders, and the three combinators
/// (plan §3.2, D3).
#[derive(Clone, Debug)]
pub enum TheoryExpr {
    Empty(Span),
    Free(DottedPath, Span),
    /// A bare reference, or an application `Ctor(args)`.
    Apply {
        head: DottedPath,
        args: Vec<TheoryExpr>,
        span: Span,
    },
    Let {
        name: Ident,
        bound: Box<TheoryExpr>,
        body: Box<TheoryExpr>,
        span: Span,
    },
    /// `base Builder { .. } Builder { .. }` - the ordered chain (plan §3.2).
    Build {
        base: Box<TheoryExpr>,
        builder: Builder,
        span: Span,
    },
    Meet(Box<TheoryExpr>, Box<TheoryExpr>, Span),
    Join(Box<TheoryExpr>, Box<TheoryExpr>, Span),
    Diff(Box<TheoryExpr>, Box<TheoryExpr>, Span),
}

impl TheoryExpr {
    pub fn span(&self) -> Span {
        match self {
            TheoryExpr::Empty(s)
            | TheoryExpr::Free(_, s)
            | TheoryExpr::Apply { span: s, .. }
            | TheoryExpr::Let { span: s, .. }
            | TheoryExpr::Build { span: s, .. }
            | TheoryExpr::Meet(_, _, s)
            | TheoryExpr::Join(_, _, s)
            | TheoryExpr::Diff(_, _, s) => *s,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Builder {
    /// G1. Category declaration, distinct from export visibility.
    Types(Vec<CatDecl>),
    Exports(Vec<Export>),
    Replacements(Vec<Replacement>),
    Terms(Vec<TermRule>),
    Equations(Vec<Equation>),
    Rewrites(Vec<RewriteDecl>),
    /// A canonical `language/2` partial value. It is decoded through the same
    /// closed schema as a directly published value, then applied in field
    /// order by the elaborator.
    Data(RhoValue),
}

impl Builder {
    pub fn name(&self) -> &'static str {
        match self {
            Builder::Types(_) => "Types",
            Builder::Exports(_) => "Exports",
            Builder::Replacements(_) => "Replacements",
            Builder::Terms(_) => "Terms",
            Builder::Equations(_) => "Equations",
            Builder::Rewrites(_) => "Rewrites",
            Builder::Data(_) => "Data",
        }
    }
}

#[derive(Clone, Debug)]
pub struct CatDecl {
    pub cat: Cat,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Export {
    pub cat: Cat,
    /// `Elem => Proc` renames on export; `None` exports under its own name.
    pub as_name: Option<Cat>,
    pub span: Span,
}

/// `Zero => PZero . |- "0" : Proc;`
///
/// No integer permutation profile: arguments are named, so permutation is
/// expressed by naming (plan §3.2).
#[derive(Clone, Debug)]
pub struct Replacement {
    pub target: Label,
    pub rule: TermRule,
    pub span: Span,
}

/// `PInput . n:Name, ^x.p:[Name -> Proc] |- n "?" x "." "{" p "}" : Proc;`
#[derive(Clone, Debug)]
pub struct TermRule {
    pub label: Label,
    pub context: Vec<Binding>,
    pub syntax: Vec<Item>,
    pub result: Cat,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Binding {
    /// `n:Name` or `ps:HashBag(Proc)`
    Plain { name: Ident, sort: Sort, span: Span },
    /// G4. `^x.p:[Name -> Proc]` - `x` binds in `p`.
    Binder {
        binder: Ident,
        body: Ident,
        from: Cat,
        to: Cat,
        span: Span,
    },
}

impl Binding {
    /// The names this binding introduces into the concrete syntax.
    pub fn names(&self) -> Vec<&str> {
        match self {
            Binding::Plain { name, .. } => vec![name.as_str()],
            Binding::Binder { binder, body, .. } => vec![binder.as_str(), body.as_str()],
        }
    }
    pub fn span(&self) -> Span {
        match self {
            Binding::Plain { span, .. } | Binding::Binder { span, .. } => *span,
        }
    }
}

/// G2. Collection sorts. `Product` is deliberately absent pending plan 9.3.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sort {
    Cat(Cat),
    Coll { kind: CollKind, of: Cat },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollKind {
    HashBag,
    Set,
    List,
}

impl CollKind {
    pub fn parse(s: &str) -> Option<CollKind> {
        match s {
            "HashBag" => Some(CollKind::HashBag),
            "Set" => Some(CollKind::Set),
            "List" => Some(CollKind::List),
            _ => None,
        }
    }
    pub fn name(&self) -> &'static str {
        match self {
            CollKind::HashBag => "HashBag",
            CollKind::Set => "Set",
            CollKind::List => "List",
        }
    }
}

impl Sort {
    pub fn base_cat(&self) -> &str {
        match self {
            Sort::Cat(c) => c,
            Sort::Coll { of, .. } => of,
        }
    }
    pub fn render(&self) -> String {
        match self {
            Sort::Cat(c) => c.clone(),
            Sort::Coll { kind, of } => format!("{}({})", kind.name(), of),
        }
    }
}

/// G6. Concrete-syntax items reference *arguments by name*, not categories by
/// position.
#[derive(Clone, Debug)]
pub enum Item {
    Terminal(String),
    ArgRef(Ident),
    /// `ps.*sep("|")`
    Projection {
        arg: Ident,
        sep: String,
    },
}

#[derive(Clone, Debug)]
pub struct Equation {
    /// Freshness side conditions: `if x # Q then ...`
    pub freshness: Vec<(Ident, Ident)>,
    pub lhs: Ast,
    pub rhs: Ast,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct RewriteDecl {
    pub name: Ident,
    /// Conditional premises: `if S ~> T then ...` (D2 spelling).
    pub premises: Vec<(Ident, Ident)>,
    pub lhs: Ast,
    pub rhs: Ast,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Ast {
    Var(Ident, Span),
    /// `(Label arg ...)`
    SExp(Label, Vec<Ast>, Span),
    /// G4. Two-argument substitution: `(subst ^x.p arg)`.
    Subst(Box<Ast>, Box<Ast>, Span),
    /// G4. `^x.p`
    Abs(Ident, Box<Ast>, Span),
    /// `{a, b, ...rest}`
    Coll(Vec<Ast>, Span),
    /// G3. `...rest`
    Remainder(Ident, Span),
}

impl Ast {
    pub fn span(&self) -> Span {
        match self {
            Ast::Var(_, s)
            | Ast::SExp(_, _, s)
            | Ast::Subst(_, _, s)
            | Ast::Abs(_, _, s)
            | Ast::Coll(_, s)
            | Ast::Remainder(_, s) => *s,
        }
    }

    /// Every constructor label mentioned anywhere in this AST.
    pub fn labels(&self, out: &mut Vec<Label>) {
        match self {
            Ast::SExp(l, args, _) => {
                out.push(l.clone());
                for a in args {
                    a.labels(out);
                }
            },
            Ast::Subst(a, b, _) => {
                a.labels(out);
                b.labels(out);
            },
            Ast::Abs(_, b, _) => b.labels(out),
            Ast::Coll(xs, _) => {
                for a in xs {
                    a.labels(out);
                }
            },
            Ast::Var(..) | Ast::Remainder(..) => {},
        }
    }
}
