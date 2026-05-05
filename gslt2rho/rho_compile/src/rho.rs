//! Output AST for rho-calculus terms.
//!
//! This is a Rust-side mirror of the `RhoCalc` language definition that
//! ships with MeTTaIL (see the repository README). Constructors and arities
//! are deliberately kept identical so that this AST can be serialised
//! straight to MeTTaIL's parsed form.
//!
//! ```text
//! PZero    .                                  |- "0"                      : Proc
//! PDrop    . n:Name                            |- "*" "(" n ")"            : Proc
//! POutput  . n:Name, q:Proc                    |- n "!" "(" q ")"          : Proc
//! PInput   . n:Name, ^x.p:[Name -> Proc]       |- n "?" x "." "{" p "}"    : Proc
//! PPar     . ps:HashBag(Proc)                  |- "{" ps.*sep("|") "}"     : Proc
//! NQuote   . p:Proc                            |- "@" "(" p ")"            : Name
//! ```

use std::fmt;

/// A rho-calculus process.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Proc {
    /// `0`
    Zero,
    /// `*(n)` --- dereference name `n` to the process it quotes.
    Drop(Name),
    /// `n!(q)` --- send process `q` on channel `n`.
    Output { chan: Name, msg: Box<Proc> },
    /// `n?x.{p}` --- bind incoming name to `x` in body `p`, persistent
    /// receive.
    ///
    /// We model the higher-order body as a Rust closure-shaped pair
    /// `(binder_name, body)`; the binder is captured by name in the body
    /// using `Name::Var`.
    Input {
        chan: Name,
        binder: String,
        body: Box<Proc>,
    },
    /// `{ p_1 | p_2 | ... | p_k }`
    Par(Vec<Proc>),
}

/// A rho-calculus name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    /// `@(p)` --- the reflection of process `p`.
    Quote(Box<Proc>),
    /// A free or bound variable. Used both for binder positions in
    /// `PInput` and for substitutional metavariables during compilation.
    Var(String),
}

// ---------------------------------------------------------------------------
// Smart constructors
// ---------------------------------------------------------------------------

impl Proc {
    pub fn zero() -> Self {
        Proc::Zero
    }
    pub fn drop_(n: Name) -> Self {
        Proc::Drop(n)
    }
    pub fn out(chan: Name, msg: Proc) -> Self {
        Proc::Output { chan, msg: Box::new(msg) }
    }
    pub fn input(chan: Name, binder: impl Into<String>, body: Proc) -> Self {
        Proc::Input {
            chan,
            binder: binder.into(),
            body: Box::new(body),
        }
    }

    /// `Par` constructor that flattens nested pars and drops `Zero`s.
    pub fn par(parts: Vec<Proc>) -> Self {
        let mut flat = Vec::with_capacity(parts.len());
        for p in parts {
            match p {
                Proc::Par(inner) => flat.extend(inner),
                Proc::Zero => {}
                other => flat.push(other),
            }
        }
        match flat.len() {
            0 => Proc::Zero,
            1 => flat.into_iter().next().unwrap(),
            _ => Proc::Par(flat),
        }
    }

    /// Sugar: a tuple receive `for ((y_1, ..., y_n) <= chan) { body }`,
    /// elaborated as `n` nested receives on the same channel.
    ///
    /// The receives are nested inside-out so that `y_1` is bound first,
    /// matching the left-to-right semantics of the source-language
    /// pattern.
    pub fn tuple_input(chan: Name, binders: Vec<String>, body: Proc) -> Self {
        let mut acc = body;
        for b in binders.into_iter().rev() {
            acc = Proc::input(chan.clone(), b, acc);
        }
        acc
    }
}

impl Name {
    pub fn quote(p: Proc) -> Self {
        Name::Quote(Box::new(p))
    }
    pub fn var(v: impl Into<String>) -> Self {
        Name::Var(v.into())
    }
}

// ---------------------------------------------------------------------------
// Display: matches MeTTaIL's RhoCalc concrete syntax
// ---------------------------------------------------------------------------

impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Proc::Zero => write!(f, "0"),
            Proc::Drop(n) => write!(f, "*({})", n),
            Proc::Output { chan, msg } => write!(f, "{}!({})", chan, msg),
            Proc::Input { chan, binder, body } => {
                write!(f, "{}?{}.{{ {} }}", chan, binder, body)
            }
            Proc::Par(parts) => {
                write!(f, "{{ ")?;
                for (i, p) in parts.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, " }}")
            }
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Quote(p) => write!(f, "@({})", p),
            Name::Var(v) => write!(f, "{}", v),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn par_flattens_and_normalises() {
        let p = Proc::par(vec![
            Proc::Zero,
            Proc::par(vec![Proc::Drop(Name::var("x")), Proc::Zero]),
            Proc::Drop(Name::var("y")),
        ]);
        match p {
            Proc::Par(parts) => assert_eq!(parts.len(), 2),
            _ => panic!("expected Par"),
        }
    }

    #[test]
    fn tuple_input_nests_correctly() {
        let chan = Name::var("c");
        let body = Proc::out(Name::var("c"), Proc::Drop(Name::var("y1")));
        let p = Proc::tuple_input(
            chan,
            vec!["y1".into(), "y2".into()],
            body,
        );
        // Should be: c?y1.{ c?y2.{ c!(*y1) } }
        let s = format!("{}", p);
        assert!(s.starts_with("c?y1."));
        assert!(s.contains("c?y2."));
    }

    #[test]
    fn print_matches_rhocalc_syntax() {
        // Construct: server!(request) | server?y.{ server!(*y) }
        let p = Proc::par(vec![
            Proc::out(Name::var("server"), Proc::Drop(Name::var("request"))),
            Proc::input(
                Name::var("server"),
                "y",
                Proc::out(Name::var("server"), Proc::Drop(Name::var("y"))),
            ),
        ]);
        let s = format!("{}", p);
        // Sanity: contains both halves.
        assert!(s.contains("server!"));
        assert!(s.contains("server?y."));
    }
}
