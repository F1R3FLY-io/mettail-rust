//! Recursive-descent parser for the frozen MeTTaIL module surface.

use crate::ast::*;
use crate::canonical::RhoValue;
use crate::diag::{Diag, DiagKind};
use crate::lex::{lex, Lexeme, Span, Tok};

pub struct Parser {
    toks: Vec<Lexeme>,
    pos: usize,
}

type PResult<T> = Result<T, Diag>;

pub fn parse_module(src: &str) -> PResult<ModuleFile> {
    let toks = lex(src).map_err(|m| Diag::new(DiagKind::Parse, m, Span { line: 0, col: 0 }))?;
    let mut p = Parser { toks, pos: 0 };
    p.module_file()
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(Diag::new(DiagKind::Parse, msg, self.span()))
    }
    fn expect(&mut self, t: Tok) -> PResult<()> {
        if self.eat(&t) {
            Ok(())
        } else {
            self.err(format!("expected {}, found {}", t.describe(), self.peek().describe()))
        }
    }
    fn ident(&mut self) -> PResult<Ident> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.bump();
                Ok(s)
            },
            other => self.err(format!("expected an identifier, found {}", other.describe())),
        }
    }
    fn string(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Str(s) => {
                self.bump();
                Ok(s)
            },
            other => self.err(format!("expected a string literal, found {}", other.describe())),
        }
    }

    // ---------------------------------------------------------------- module

    fn module_file(&mut self) -> PResult<ModuleFile> {
        let span = self.span();
        let mut imports = Vec::new();
        while self.at(&Tok::KwImport) {
            imports.push(self.import()?);
        }
        self.expect(Tok::KwModule)?;
        let name = self.ident()?;
        self.expect(Tok::LBrace)?;

        let mut decls = Vec::new();
        let mut instantiations = Vec::new();
        while !self.at(&Tok::RBrace) && !self.at(&Tok::Eof) {
            if self.at(&Tok::KwTheoryUpper) {
                decls.push(self.theory_decl()?);
            } else if self.at(&Tok::KwTheoryLower) {
                self.bump();
                instantiations.push(self.theory_expr()?);
            } else {
                return self.err(format!(
                    "expected `Theory` or `theory`, found {}",
                    self.peek().describe()
                ));
            }
        }
        self.expect(Tok::RBrace)?;
        Ok(ModuleFile {
            imports,
            name,
            decls,
            instantiations,
            span,
        })
    }

    fn import(&mut self) -> PResult<Import> {
        let span = self.span();
        self.expect(Tok::KwImport)?;
        // `import "<url>" as u`  |  `import Name from "<url>"`
        if let Tok::Str(_) = self.peek() {
            let url = self.string()?;
            self.expect(Tok::KwAs)?;
            let alias = self.ident()?;
            Ok(Import::ModuleAs { url, alias, span })
        } else {
            let name = self.ident()?;
            self.expect(Tok::KwFrom)?;
            let url = self.string()?;
            Ok(Import::FromModule { name, url, span })
        }
    }

    fn theory_decl(&mut self) -> PResult<TheoryDecl> {
        let span = self.span();
        self.expect(Tok::KwTheoryUpper)?;
        let name = self.ident()?;
        self.expect(Tok::LParen)?;
        let mut params = Vec::new();
        while !self.at(&Tok::RParen) {
            let pspan = self.span();
            let pname = self.ident()?;
            self.expect(Tok::Colon)?;
            let ty = self.dotted()?;
            params.push(Param { name: pname, ty, span: pspan });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen)?;
        self.expect(Tok::LBrace)?;
        let body = self.theory_expr()?;
        self.expect(Tok::RBrace)?;
        Ok(TheoryDecl { name, params, body, span })
    }

    fn dotted(&mut self) -> PResult<DottedPath> {
        let mut parts = vec![self.ident()?];
        while self.at(&Tok::Dot) {
            // Only consume the dot if an identifier follows; `.` also
            // separates a label from its context in term rules.
            if let Tok::Ident(_) = &self.toks[self.pos + 1].tok {
                self.bump();
                parts.push(self.ident()?);
            } else {
                break;
            }
        }
        Ok(DottedPath(parts))
    }

    // --------------------------------------------------------- theory expr
    // Precedence, loosest first:  \   then  \/   then  /\   then builders.

    fn theory_expr(&mut self) -> PResult<TheoryExpr> {
        let mut lhs = self.te_join()?;
        while self.at(&Tok::Diff) {
            let span = self.span();
            self.bump();
            let rhs = self.te_join()?;
            lhs = TheoryExpr::Diff(Box::new(lhs), Box::new(rhs), span);
        }
        Ok(lhs)
    }

    fn te_join(&mut self) -> PResult<TheoryExpr> {
        let mut lhs = self.te_meet()?;
        while self.at(&Tok::Join) {
            let span = self.span();
            self.bump();
            let rhs = self.te_meet()?;
            lhs = TheoryExpr::Join(Box::new(lhs), Box::new(rhs), span);
        }
        Ok(lhs)
    }

    fn te_meet(&mut self) -> PResult<TheoryExpr> {
        let mut lhs = self.te_builders()?;
        while self.at(&Tok::Meet) {
            let span = self.span();
            self.bump();
            let rhs = self.te_builders()?;
            lhs = TheoryExpr::Meet(Box::new(lhs), Box::new(rhs), span);
        }
        Ok(lhs)
    }

    fn at_builder(&self) -> bool {
        matches!(
            self.peek(),
            Tok::KwTypes
                | Tok::KwExports
                | Tok::KwReplacements
                | Tok::KwTerms
                | Tok::KwEquations
                | Tok::KwRewrites
                | Tok::KwData
        )
    }

    fn te_builders(&mut self) -> PResult<TheoryExpr> {
        // G5: a body that opens with a builder takes `Empty` as implicit base.
        let mut base = if self.at_builder() {
            TheoryExpr::Empty(self.span())
        } else {
            self.te_atom()?
        };
        while self.at_builder() {
            let span = self.span();
            let builder = self.builder()?;
            base = TheoryExpr::Build { base: Box::new(base), builder, span };
        }
        Ok(base)
    }

    fn te_atom(&mut self) -> PResult<TheoryExpr> {
        let span = self.span();
        match self.peek().clone() {
            Tok::KwEmpty => {
                self.bump();
                Ok(TheoryExpr::Empty(span))
            },
            Tok::KwFree => {
                self.bump();
                self.expect(Tok::LParen)?;
                let p = self.dotted()?;
                self.expect(Tok::RParen)?;
                Ok(TheoryExpr::Free(p, span))
            },
            Tok::KwLet => {
                self.bump();
                let name = self.ident()?;
                self.expect(Tok::Eq)?;
                let bound = self.theory_expr()?;
                self.expect(Tok::KwIn)?;
                self.expect(Tok::LParen)?;
                let body = self.theory_expr()?;
                self.expect(Tok::RParen)?;
                Ok(TheoryExpr::Let {
                    name,
                    bound: Box::new(bound),
                    body: Box::new(body),
                    span,
                })
            },
            Tok::LBrace => {
                self.bump();
                let inner = self.theory_expr()?;
                self.expect(Tok::RBrace)?;
                Ok(inner)
            },
            Tok::LParen => {
                self.bump();
                let inner = self.theory_expr()?;
                self.expect(Tok::RParen)?;
                Ok(inner)
            },
            Tok::Ident(_) => {
                let head = self.dotted()?;
                let mut args = Vec::new();
                if self.eat(&Tok::LParen) {
                    while !self.at(&Tok::RParen) {
                        args.push(self.theory_expr()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::RParen)?;
                }
                Ok(TheoryExpr::Apply { head, args, span })
            },
            other => self.err(format!("expected a theory expression, found {}", other.describe())),
        }
    }

    // ------------------------------------------------------------- builders

    fn builder(&mut self) -> PResult<Builder> {
        let kw = self.bump();
        if kw == Tok::KwData {
            self.expect(Tok::LParen)?;
            let value = self.rho_value()?;
            self.expect(Tok::RParen)?;
            return Ok(Builder::Data(value));
        }
        self.expect(Tok::LBrace)?;
        let b = match kw {
            Tok::KwTypes => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let span = self.span();
                    let cat = self.ident()?;
                    self.expect(Tok::Semi)?;
                    v.push(CatDecl { cat, span });
                }
                Builder::Types(v)
            },
            Tok::KwExports => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let span = self.span();
                    let cat = self.ident()?;
                    let as_name = if self.eat(&Tok::FatArrow) {
                        Some(self.ident()?)
                    } else {
                        None
                    };
                    self.expect(Tok::Semi)?;
                    v.push(Export { cat, as_name, span });
                }
                Builder::Exports(v)
            },
            Tok::KwReplacements => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    let span = self.span();
                    let target = self.ident()?;
                    self.expect(Tok::FatArrow)?;
                    let rule = self.term_rule()?;
                    v.push(Replacement { target, rule, span });
                }
                Builder::Replacements(v)
            },
            Tok::KwTerms => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    v.push(self.term_rule()?);
                }
                Builder::Terms(v)
            },
            Tok::KwEquations => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    v.push(self.equation()?);
                }
                Builder::Equations(v)
            },
            Tok::KwRewrites => {
                let mut v = Vec::new();
                while !self.at(&Tok::RBrace) {
                    v.push(self.rewrite_decl()?);
                }
                Builder::Rewrites(v)
            },
            _ => unreachable!("builder() called off a builder keyword"),
        };
        self.expect(Tok::RBrace)?;
        Ok(b)
    }

    fn rho_value(&mut self) -> PResult<RhoValue> {
        match self.peek().clone() {
            Tok::Str(value) => {
                self.bump();
                Ok(RhoValue::String(value))
            },
            Tok::Integer(value) => {
                self.bump();
                Ok(RhoValue::Integer(value))
            },
            Tok::KwTrue => {
                self.bump();
                Ok(RhoValue::Boolean(true))
            },
            Tok::KwFalse => {
                self.bump();
                Ok(RhoValue::Boolean(false))
            },
            Tok::KwNil => {
                self.bump();
                Ok(RhoValue::Nil)
            },
            Tok::LBracket => {
                self.bump();
                let mut values = Vec::new();
                while !self.at(&Tok::RBracket) {
                    values.push(self.rho_value()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RBracket)?;
                Ok(RhoValue::List(values))
            },
            Tok::LBrace => {
                self.bump();
                let mut values = std::collections::BTreeMap::new();
                while !self.at(&Tok::RBrace) {
                    let key = self.string()?;
                    self.expect(Tok::Colon)?;
                    let value = self.rho_value()?;
                    if values.insert(key.clone(), value).is_some() {
                        return self.err(format!("duplicate canonical value key `{key}`"));
                    }
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RBrace)?;
                Ok(RhoValue::Map(values))
            },
            other => self.err(format!(
                "expected a canonical Rholang value literal, found {}",
                other.describe()
            )),
        }
    }

    // ------------------------------------------------------------ term rule
    // Label . context |- item* : Cat ;

    fn term_rule(&mut self) -> PResult<TermRule> {
        let span = self.span();
        let label = self.ident()?;
        self.expect(Tok::Dot)?;
        let mut context = Vec::new();
        while !self.at(&Tok::Turnstile) {
            context.push(self.binding()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::Turnstile)?;
        let mut syntax = Vec::new();
        while !self.at(&Tok::Colon) {
            syntax.push(self.item()?);
        }
        self.expect(Tok::Colon)?;
        let result = self.ident()?;
        self.expect(Tok::Semi)?;
        Ok(TermRule { label, context, syntax, result, span })
    }

    fn binding(&mut self) -> PResult<Binding> {
        let span = self.span();
        // G4: `^x.p:[Name -> Proc]`
        if self.eat(&Tok::Caret) {
            let binder = self.ident()?;
            self.expect(Tok::Dot)?;
            let body = self.ident()?;
            self.expect(Tok::Colon)?;
            self.expect(Tok::LBracket)?;
            let from = self.ident()?;
            self.expect(Tok::ThinArrow)?;
            let to = self.ident()?;
            self.expect(Tok::RBracket)?;
            return Ok(Binding::Binder { binder, body, from, to, span });
        }
        let name = self.ident()?;
        self.expect(Tok::Colon)?;
        let sort = self.sort()?;
        Ok(Binding::Plain { name, sort, span })
    }

    /// G2. `Proc` | `HashBag(Proc)` | `Set(Proc)` | `List(Proc)`
    fn sort(&mut self) -> PResult<Sort> {
        let span = self.span();
        let head = self.ident()?;
        if self.at(&Tok::LParen) {
            let kind = match CollKind::parse(&head) {
                Some(k) => k,
                None => {
                    return Err(Diag::new(
                        DiagKind::UnknownCollection,
                        format!(
                            "unknown collection sort `{head}`; expected one of \
                             HashBag, Set, List"
                        ),
                        span,
                    ))
                },
            };
            self.bump();
            let of = self.ident()?;
            self.expect(Tok::RParen)?;
            return Ok(Sort::Coll { kind, of });
        }
        Ok(Sort::Cat(head))
    }

    /// G6. Terminals, argument references, and projections over collections.
    fn item(&mut self) -> PResult<Item> {
        match self.peek().clone() {
            Tok::Str(s) => {
                self.bump();
                Ok(Item::Terminal(s))
            },
            Tok::Ident(name) => {
                self.bump();
                // `ps.*sep("|")`
                if self.at(&Tok::Dot) && self.toks[self.pos + 1].tok == Tok::Star {
                    self.bump();
                    self.bump();
                    let f = self.ident()?;
                    if f != "sep" {
                        return self
                            .err(format!("unknown collection projection `{f}`; expected `sep`"));
                    }
                    self.expect(Tok::LParen)?;
                    let sep = self.string()?;
                    self.expect(Tok::RParen)?;
                    return Ok(Item::Projection { arg: name, sep });
                }
                Ok(Item::ArgRef(name))
            },
            other => self.err(format!(
                "expected a terminal or an argument reference, found {}",
                other.describe()
            )),
        }
    }

    // ------------------------------------------------------ equations, rules

    fn equation(&mut self) -> PResult<Equation> {
        let span = self.span();
        let mut freshness = Vec::new();
        while self.at(&Tok::KwIf) {
            self.bump();
            let a = self.ident()?;
            self.expect(Tok::Hash)?;
            let b = self.ident()?;
            self.expect(Tok::KwThen)?;
            freshness.push((a, b));
        }
        let lhs = self.ast()?;
        self.expect(Tok::EqEq)?;
        let rhs = self.ast()?;
        self.expect(Tok::Semi)?;
        Ok(Equation { freshness, lhs, rhs, span })
    }

    fn rewrite_decl(&mut self) -> PResult<RewriteDecl> {
        let span = self.span();
        let name = self.ident()?;
        self.expect(Tok::Colon)?;
        let mut premises = Vec::new();
        // D2 spelling: `if S ~> T then ...`
        while self.at(&Tok::KwIf) {
            self.bump();
            let a = self.ident()?;
            self.expect(Tok::Squiggle)?;
            let b = self.ident()?;
            self.expect(Tok::KwThen)?;
            premises.push((a, b));
        }
        let lhs = self.ast()?;
        self.expect(Tok::Squiggle)?;
        let rhs = self.ast()?;
        self.expect(Tok::Semi)?;
        Ok(RewriteDecl { name, premises, lhs, rhs, span })
    }

    fn ast(&mut self) -> PResult<Ast> {
        let span = self.span();
        match self.peek().clone() {
            // G3
            Tok::Ellipsis => {
                self.bump();
                let n = self.ident()?;
                Ok(Ast::Remainder(n, span))
            },
            // G4
            Tok::Caret => {
                self.bump();
                let b = self.ident()?;
                self.expect(Tok::Dot)?;
                let body = self.ast()?;
                Ok(Ast::Abs(b, Box::new(body), span))
            },
            Tok::LBrace => {
                self.bump();
                let mut xs = Vec::new();
                while !self.at(&Tok::RBrace) {
                    xs.push(self.ast()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RBrace)?;
                Ok(Ast::Coll(xs, span))
            },
            Tok::LParen => {
                self.bump();
                // G4: two-argument substitution
                if self.at(&Tok::KwSubst) {
                    self.bump();
                    let abs = self.ast()?;
                    let arg = self.ast()?;
                    self.expect(Tok::RParen)?;
                    return Ok(Ast::Subst(Box::new(abs), Box::new(arg), span));
                }
                let label = self.ident()?;
                let mut args = Vec::new();
                while !self.at(&Tok::RParen) {
                    args.push(self.ast()?);
                }
                self.expect(Tok::RParen)?;
                Ok(Ast::SExp(label, args, span))
            },
            Tok::Ident(n) => {
                self.bump();
                Ok(Ast::Var(n, span))
            },
            other => self.err(format!("expected a term, found {}", other.describe())),
        }
    }
}
