//! Explicit-stack parser for the frozen MeTTaIL module surface.

use crate::ast::*;
use crate::canonical::RhoValue;
use crate::diag::{Diag, DiagKind};
use crate::lex::{lex, Lexeme, Span, Tok};
use std::collections::HashSet;

pub struct Parser {
    toks: Vec<Lexeme>,
    pos: usize,
}

type PResult<T> = Result<T, Diag>;

/// Maximum nesting of an accepted theory expression, canonical value, or
/// rule AST. Parsing itself is iterative, and this admission bound ensures
/// every accepted tree is also safe for bounded legacy consumers and drop.
pub const MAX_DDL_STRUCTURAL_DEPTH: usize = 256;

struct Parsed<T> {
    value: T,
    depth: usize,
}

pub fn parse_module(src: &str) -> PResult<ModuleFile> {
    let toks = lex(src).map_err(|m| Diag::new(DiagKind::Parse, m, Span { line: 0, col: 0 }))?;
    let mut p = Parser { toks, pos: 0 };
    p.module_file()
}

/// Parse one standalone Greg/Mike `Theory` declaration.
///
/// This is a real grammar entry point, not a textual wrapper around
/// [`parse_module`]. Requiring end-of-input prevents a declaration-shaped prefix
/// from hiding trailing executable or malformed source.
pub fn parse_theory(src: &str) -> PResult<TheoryDecl> {
    let toks = lex(src).map_err(|m| Diag::new(DiagKind::Parse, m, Span { line: 0, col: 0 }))?;
    let mut parser = Parser { toks, pos: 0 };
    let theory = parser.theory_decl()?;
    parser.expect(Tok::Eof)?;
    Ok(theory)
}

impl Parser {
    fn parsed<T>(&self, value: T, depth: usize, resource: &str) -> PResult<Parsed<T>> {
        if depth > MAX_DDL_STRUCTURAL_DEPTH {
            Err(Diag::new(
                DiagKind::ResourceLimit,
                format!("{resource} nesting exceeds the maximum of {MAX_DDL_STRUCTURAL_DEPTH}"),
                self.span(),
            ))
        } else {
            Ok(Parsed { value, depth })
        }
    }

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

        let mut items = Vec::new();
        let mut declaration_names = HashSet::new();
        while !self.at(&Tok::RBrace) && !self.at(&Tok::Eof) {
            if self.at(&Tok::KwTheoryUpper) {
                let declaration = self.theory_decl()?;
                if !declaration_names.insert(declaration.name.clone()) {
                    return Err(Diag::new(
                        DiagKind::DuplicateTheory,
                        format!(
                            "theory `{}` is declared more than once in module",
                            declaration.name
                        ),
                        declaration.span,
                    ));
                }
                items.push(ModuleItem::TheoryDecl(declaration));
            } else if self.at(&Tok::KwTheoryLower) {
                self.bump();
                items.push(ModuleItem::TheoryEntry(self.theory_expr()?));
            } else {
                return self.err(format!(
                    "expected `Theory` or `theory`, found {}",
                    self.peek().describe()
                ));
            }
        }
        self.expect(Tok::RBrace)?;
        self.expect(Tok::Eof)?;
        Ok(ModuleFile { imports, name, items, span })
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
        enum Job {
            Expr,
            Diff,
            Join,
            Meet,
            Builders,
            Atom,
            AfterDiff(Option<(Parsed<TheoryExpr>, Span)>),
            AfterJoin(Option<(Parsed<TheoryExpr>, Span)>),
            AfterMeet(Option<(Parsed<TheoryExpr>, Span)>),
            AfterAtomBuilders,
            AfterLetBound {
                name: Ident,
                span: Span,
            },
            FinishLet {
                name: Ident,
                span: Span,
                bound: Parsed<TheoryExpr>,
            },
            FinishGroup(Tok),
            ContinueApply {
                head: DottedPath,
                args: Vec<Parsed<TheoryExpr>>,
                span: Span,
            },
            AfterApplyArg {
                head: DottedPath,
                args: Vec<Parsed<TheoryExpr>>,
                span: Span,
            },
        }

        let mut jobs = vec![Job::Expr];
        let mut values = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Expr => jobs.push(Job::Diff),
                Job::Diff => {
                    jobs.push(Job::AfterDiff(None));
                    jobs.push(Job::Join);
                },
                Job::Join => {
                    jobs.push(Job::AfterJoin(None));
                    jobs.push(Job::Meet);
                },
                Job::Meet => {
                    jobs.push(Job::AfterMeet(None));
                    jobs.push(Job::Builders);
                },
                Job::Builders => {
                    if self.at_builder() {
                        let mut base =
                            self.parsed(TheoryExpr::Empty(self.span()), 1, "theory expression")?;
                        while self.at_builder() {
                            let span = self.span();
                            let builder = self.builder()?;
                            let depth = base.depth + 1;
                            base = self.parsed(
                                TheoryExpr::Build {
                                    base: Box::new(base.value),
                                    builder,
                                    span,
                                },
                                depth,
                                "theory expression",
                            )?;
                        }
                        values.push(base);
                    } else {
                        jobs.push(Job::AfterAtomBuilders);
                        jobs.push(Job::Atom);
                    }
                },
                Job::AfterAtomBuilders => {
                    let mut base = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing theory atom", self.span())
                    })?;
                    while self.at_builder() {
                        let span = self.span();
                        let builder = self.builder()?;
                        let depth = base.depth + 1;
                        base = self.parsed(
                            TheoryExpr::Build {
                                base: Box::new(base.value),
                                builder,
                                span,
                            },
                            depth,
                            "theory expression",
                        )?;
                    }
                    values.push(base);
                },
                Job::AfterDiff(prior) => {
                    let rhs = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing difference operand", self.span())
                    })?;
                    let lhs = match prior {
                        Some((lhs, span)) => {
                            let depth = 1 + lhs.depth.max(rhs.depth);
                            self.parsed(
                                TheoryExpr::Diff(Box::new(lhs.value), Box::new(rhs.value), span),
                                depth,
                                "theory expression",
                            )?
                        },
                        None => rhs,
                    };
                    if self.at(&Tok::Diff) {
                        let span = self.span();
                        self.bump();
                        jobs.push(Job::AfterDiff(Some((lhs, span))));
                        jobs.push(Job::Join);
                    } else {
                        values.push(lhs);
                    }
                },
                Job::AfterJoin(prior) => {
                    let rhs = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing join operand", self.span())
                    })?;
                    let lhs = match prior {
                        Some((lhs, span)) => {
                            let depth = 1 + lhs.depth.max(rhs.depth);
                            self.parsed(
                                TheoryExpr::Join(Box::new(lhs.value), Box::new(rhs.value), span),
                                depth,
                                "theory expression",
                            )?
                        },
                        None => rhs,
                    };
                    if self.at(&Tok::Join) {
                        let span = self.span();
                        self.bump();
                        jobs.push(Job::AfterJoin(Some((lhs, span))));
                        jobs.push(Job::Meet);
                    } else {
                        values.push(lhs);
                    }
                },
                Job::AfterMeet(prior) => {
                    let rhs = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing meet operand", self.span())
                    })?;
                    let lhs = match prior {
                        Some((lhs, span)) => {
                            let depth = 1 + lhs.depth.max(rhs.depth);
                            self.parsed(
                                TheoryExpr::Meet(Box::new(lhs.value), Box::new(rhs.value), span),
                                depth,
                                "theory expression",
                            )?
                        },
                        None => rhs,
                    };
                    if self.at(&Tok::Meet) {
                        let span = self.span();
                        self.bump();
                        jobs.push(Job::AfterMeet(Some((lhs, span))));
                        jobs.push(Job::Builders);
                    } else {
                        values.push(lhs);
                    }
                },
                Job::Atom => {
                    let span = self.span();
                    match self.peek().clone() {
                        Tok::KwEmpty => {
                            self.bump();
                            values.push(self.parsed(
                                TheoryExpr::Empty(span),
                                1,
                                "theory expression",
                            )?);
                        },
                        Tok::KwFree => {
                            self.bump();
                            self.expect(Tok::LParen)?;
                            let path = self.dotted()?;
                            self.expect(Tok::RParen)?;
                            values.push(self.parsed(
                                TheoryExpr::Free(path, span),
                                1,
                                "theory expression",
                            )?);
                        },
                        Tok::KwLet => {
                            self.bump();
                            let name = self.ident()?;
                            self.expect(Tok::Eq)?;
                            jobs.push(Job::AfterLetBound { name, span });
                            jobs.push(Job::Expr);
                        },
                        Tok::LBrace => {
                            self.bump();
                            jobs.push(Job::FinishGroup(Tok::RBrace));
                            jobs.push(Job::Expr);
                        },
                        Tok::LParen => {
                            self.bump();
                            jobs.push(Job::FinishGroup(Tok::RParen));
                            jobs.push(Job::Expr);
                        },
                        Tok::Ident(_) => {
                            let head = self.dotted()?;
                            if self.eat(&Tok::LParen) {
                                jobs.push(Job::ContinueApply { head, args: Vec::new(), span });
                            } else {
                                values.push(self.parsed(
                                    TheoryExpr::Apply { head, args: Vec::new(), span },
                                    1,
                                    "theory expression",
                                )?);
                            }
                        },
                        other => {
                            return self.err(format!(
                                "expected a theory expression, found {}",
                                other.describe()
                            ))
                        },
                    }
                },
                Job::AfterLetBound { name, span } => {
                    let bound = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing let-bound expression", self.span())
                    })?;
                    self.expect(Tok::KwIn)?;
                    self.expect(Tok::LParen)?;
                    jobs.push(Job::FinishLet { name, span, bound });
                    jobs.push(Job::Expr);
                },
                Job::FinishLet { name, span, bound } => {
                    let body = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing let body", self.span())
                    })?;
                    self.expect(Tok::RParen)?;
                    let depth = 1 + bound.depth.max(body.depth);
                    values.push(self.parsed(
                        TheoryExpr::Let {
                            name,
                            bound: Box::new(bound.value),
                            body: Box::new(body.value),
                            span,
                        },
                        depth,
                        "theory expression",
                    )?);
                },
                Job::FinishGroup(close) => self.expect(close)?,
                Job::ContinueApply { head, args, span } => {
                    if self.eat(&Tok::RParen) {
                        let depth = 1 + args.iter().map(|arg| arg.depth).max().unwrap_or(0);
                        values.push(self.parsed(
                            TheoryExpr::Apply {
                                head,
                                args: args.into_iter().map(|arg| arg.value).collect(),
                                span,
                            },
                            depth,
                            "theory expression",
                        )?);
                    } else {
                        jobs.push(Job::AfterApplyArg { head, args, span });
                        jobs.push(Job::Expr);
                    }
                },
                Job::AfterApplyArg { head, mut args, span } => {
                    let argument = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing theory argument", self.span())
                    })?;
                    args.push(argument);
                    if self.eat(&Tok::Comma) {
                        jobs.push(Job::ContinueApply { head, args, span });
                    } else {
                        self.expect(Tok::RParen)?;
                        let depth = 1 + args.iter().map(|arg| arg.depth).max().unwrap_or(0);
                        values.push(self.parsed(
                            TheoryExpr::Apply {
                                head,
                                args: args.into_iter().map(|arg| arg.value).collect(),
                                span,
                            },
                            depth,
                            "theory expression",
                        )?);
                    }
                },
            }
        }
        if values.len() != 1 {
            return self.err("theory-expression PDA produced an invalid value stack");
        }
        Ok(values
            .pop()
            .expect("checked one theory-expression value")
            .value)
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
                    let admits_variables =
                        !matches!(self.peek(), Tok::Ident(word) if word == "noadmit");
                    if !admits_variables {
                        self.bump();
                    }
                    let cat = self.ident()?;
                    let carrier = if self.eat(&Tok::Eq) {
                        Some(self.ident()?)
                    } else {
                        None
                    };
                    self.expect(Tok::Semi)?;
                    v.push(CatDecl { cat, admits_variables, carrier, span });
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
                    v.push(TermDecl::Rule(self.term_rule()?));
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
                    if self.at_projection_declaration() {
                        v.push(RewriteEntry::Projection(self.projection_decl()?));
                    } else {
                        v.push(RewriteEntry::Ordinary(self.rewrite_decl()?));
                    }
                }
                Builder::Rewrites(v)
            },
            _ => unreachable!("builder() called off a builder keyword"),
        };
        self.expect(Tok::RBrace)?;
        Ok(b)
    }

    fn rho_value(&mut self) -> PResult<RhoValue> {
        enum Job {
            Value,
            ContinueList {
                values: Vec<Parsed<RhoValue>>,
            },
            AfterListValue {
                values: Vec<Parsed<RhoValue>>,
            },
            ContinueMap {
                values: std::collections::BTreeMap<String, Parsed<RhoValue>>,
            },
            AfterMapValue {
                values: std::collections::BTreeMap<String, Parsed<RhoValue>>,
                key: String,
            },
        }

        let mut jobs = vec![Job::Value];
        let mut output = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Value => match self.peek().clone() {
                    Tok::Str(value) => {
                        self.bump();
                        output.push(self.parsed(RhoValue::String(value), 1, "canonical value")?);
                    },
                    Tok::Bytes(value) => {
                        self.bump();
                        output.push(self.parsed(RhoValue::Bytes(value), 1, "canonical value")?);
                    },
                    Tok::Integer(value) => {
                        self.bump();
                        output.push(self.parsed(RhoValue::Integer(value), 1, "canonical value")?);
                    },
                    Tok::FloatBits(bits) => {
                        self.bump();
                        output.push(self.parsed(
                            RhoValue::FloatBits(bits),
                            1,
                            "canonical value",
                        )?);
                    },
                    Tok::KwTrue => {
                        self.bump();
                        output.push(self.parsed(RhoValue::Boolean(true), 1, "canonical value")?);
                    },
                    Tok::KwFalse => {
                        self.bump();
                        output.push(self.parsed(RhoValue::Boolean(false), 1, "canonical value")?);
                    },
                    Tok::KwNil => {
                        self.bump();
                        output.push(self.parsed(RhoValue::Nil, 1, "canonical value")?);
                    },
                    Tok::LBracket => {
                        self.bump();
                        jobs.push(Job::ContinueList { values: Vec::new() });
                    },
                    Tok::LBrace => {
                        self.bump();
                        jobs.push(Job::ContinueMap {
                            values: std::collections::BTreeMap::new(),
                        });
                    },
                    Tok::Ident(name) if name == "Map" => {
                        self.bump();
                        self.expect(Tok::LParen)?;
                        self.expect(Tok::RParen)?;
                        output.push(self.parsed(
                            RhoValue::Map(std::collections::BTreeMap::new()),
                            1,
                            "canonical value",
                        )?);
                    },
                    other => {
                        return self.err(format!(
                            "expected a canonical Rholang value literal, found {}",
                            other.describe()
                        ))
                    },
                },
                Job::ContinueList { values } => {
                    if self.eat(&Tok::RBracket) {
                        let depth = 1 + values.iter().map(|value| value.depth).max().unwrap_or(0);
                        output.push(self.parsed(
                            RhoValue::List(values.into_iter().map(|value| value.value).collect()),
                            depth,
                            "canonical value",
                        )?);
                    } else {
                        jobs.push(Job::AfterListValue { values });
                        jobs.push(Job::Value);
                    }
                },
                Job::AfterListValue { mut values } => {
                    values.push(output.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing list value", self.span())
                    })?);
                    if self.eat(&Tok::Comma) {
                        jobs.push(Job::ContinueList { values });
                    } else {
                        self.expect(Tok::RBracket)?;
                        let depth = 1 + values.iter().map(|value| value.depth).max().unwrap_or(0);
                        output.push(self.parsed(
                            RhoValue::List(values.into_iter().map(|value| value.value).collect()),
                            depth,
                            "canonical value",
                        )?);
                    }
                },
                Job::ContinueMap { values } => {
                    if self.eat(&Tok::RBrace) {
                        let depth = 1 + values.values().map(|value| value.depth).max().unwrap_or(0);
                        output.push(
                            self.parsed(
                                RhoValue::Map(
                                    values
                                        .into_iter()
                                        .map(|(key, value)| (key, value.value))
                                        .collect(),
                                ),
                                depth,
                                "canonical value",
                            )?,
                        );
                    } else {
                        let key = self.string()?;
                        self.expect(Tok::Colon)?;
                        jobs.push(Job::AfterMapValue { values, key });
                        jobs.push(Job::Value);
                    }
                },
                Job::AfterMapValue { mut values, key } => {
                    let value = output.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing map value", self.span())
                    })?;
                    if values.insert(key.clone(), value).is_some() {
                        return self.err(format!("duplicate canonical value key `{key}`"));
                    }
                    if self.eat(&Tok::Comma) {
                        jobs.push(Job::ContinueMap { values });
                    } else {
                        self.expect(Tok::RBrace)?;
                        let depth = 1 + values.values().map(|value| value.depth).max().unwrap_or(0);
                        output.push(
                            self.parsed(
                                RhoValue::Map(
                                    values
                                        .into_iter()
                                        .map(|(key, value)| (key, value.value))
                                        .collect(),
                                ),
                                depth,
                                "canonical value",
                            )?,
                        );
                    }
                },
            }
        }
        if output.len() != 1 {
            return self.err("canonical-value PDA produced an invalid value stack");
        }
        Ok(output.pop().expect("checked one canonical value").value)
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
        let mut associativity = None;
        let mut prefix_binding_power = None;
        while !self.at(&Tok::Semi) {
            let attribute = self.ident()?;
            if attribute == "prefix" {
                if prefix_binding_power.is_some() {
                    return self.err("duplicate prefix binding power");
                }
                self.expect(Tok::LParen)?;
                let power = match self.bump() {
                    Tok::Integer(value) => match u16::try_from(value) {
                        Ok(power) => power,
                        Err(_) => return self.err("expected a u16 binding power"),
                    },
                    other => {
                        return self.err(format!(
                            "expected integer binding power, found {}",
                            other.describe()
                        ))
                    },
                };
                self.expect(Tok::RParen)?;
                prefix_binding_power = Some(power);
            } else if let Some(value) = TermAssociativity::parse(&attribute) {
                if associativity.replace(value).is_some() {
                    return self.err("duplicate associativity");
                }
            } else {
                return self.err(format!("unsupported term attribute `{attribute}`"));
            }
        }
        self.expect(Tok::Semi)?;
        Ok(TermRule {
            label,
            context,
            syntax,
            result,
            associativity,
            prefix_binding_power,
            span,
        })
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

    fn at_projection_declaration(&self) -> bool {
        matches!(self.peek(), Tok::Ident(word) if word == "projection")
            && matches!(self.toks.get(self.pos + 1).map(|lexeme| &lexeme.tok), Some(Tok::Ident(_)))
    }

    fn at_host_qualifier(&self) -> bool {
        matches!(self.peek(), Tok::Ident(word) if word == "host")
            && matches!(self.toks.get(self.pos + 1).map(|lexeme| &lexeme.tok), Some(Tok::Namespace))
    }

    fn projection_direction(&mut self) -> PResult<ProjectionDirection> {
        let direction = match self.peek() {
            Tok::Squiggle => ProjectionDirection::GuestToHost,
            Tok::BackwardSquiggle => ProjectionDirection::HostToGuest,
            Tok::BothSquiggles => ProjectionDirection::Both,
            other => {
                return self.err(format!("expected a projection arrow, found {}", other.describe()))
            },
        };
        self.bump();
        Ok(direction)
    }

    fn projection_decl(&mut self) -> PResult<ProjectionDecl> {
        let span = self.span();
        self.expect(Tok::Ident("projection".into()))?;
        let name = self.ident()?;
        self.expect(Tok::Colon)?;
        let guest = self.ident()?;
        let direction = self.projection_direction()?;
        self.expect(Tok::Ident("host".into()))?;
        self.expect(Tok::Namespace)?;
        let host = self.ident()?;
        let body = if self.eat(&Tok::Ident("via".into())) {
            self.expect(Tok::Ident("carrier".into()))?;
            self.expect(Tok::Semi)?;
            ProjectionBody::Carrier
        } else {
            self.expect(Tok::LBrace)?;
            let mut rows = Vec::new();
            while !self.at(&Tok::RBrace) {
                rows.push(self.projection_rule(direction)?);
            }
            self.expect(Tok::RBrace)?;
            ProjectionBody::Rules(rows)
        };
        Ok(ProjectionDecl { name, guest, host, direction, body, span })
    }

    fn projection_rule(&mut self, group_direction: ProjectionDirection) -> PResult<ProjectionRule> {
        let span = self.span();
        let name = self.ident()?;
        let mut bindings = Vec::new();
        if self.eat(&Tok::LParen) {
            if !self.at(&Tok::RParen) {
                loop {
                    let binding_name = self.ident()?;
                    self.expect(Tok::Colon)?;
                    let host = self.at_host_qualifier();
                    if host {
                        self.bump();
                        self.expect(Tok::Namespace)?;
                    }
                    let category = self.ident()?;
                    bindings.push(if host {
                        ProjectionBinding::Host { name: binding_name, category }
                    } else {
                        ProjectionBinding::Guest { name: binding_name, category }
                    });
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(Tok::RParen)?;
        }
        self.expect(Tok::Colon)?;
        let mut premises = Vec::new();
        if self.eat(&Tok::KwIf) {
            loop {
                if self.at_projection_declaration() {
                    self.bump();
                    let name = self.ident()?;
                    self.expect(Tok::LParen)?;
                    let guest = self.ident()?;
                    self.expect(Tok::Comma)?;
                    let host = self.ident()?;
                    self.expect(Tok::RParen)?;
                    premises.push(ProjectionPremise::Call { name, guest, host });
                } else {
                    let left = self.ident()?;
                    self.expect(Tok::Squiggle)?;
                    let right = self.ident()?;
                    premises.push(ProjectionPremise::Transition { left, right });
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::KwThen)?;
        }
        let guest = self.projection_term()?;
        let direction = self.projection_direction()?;
        if direction != group_direction {
            return self.err("projection row arrow must match its group arrow");
        }
        let host = self.projection_term()?;
        self.expect(Tok::Semi)?;
        Ok(ProjectionRule {
            name,
            bindings,
            premises,
            guest,
            host,
            direction,
            span,
        })
    }

    fn projection_node(tag: &str, fields: Vec<RhoValue>) -> RhoValue {
        let mut items = Vec::with_capacity(fields.len() + 1);
        items.push(RhoValue::String(tag.into()));
        items.extend(fields);
        RhoValue::List(items)
    }

    fn projection_sequence(values: Vec<Parsed<RhoValue>>) -> RhoValue {
        Self::projection_node("sequence", values.into_iter().map(|value| value.value).collect())
    }

    /// Parse the same structural rule-term algebra as generated DdlRuleAst.
    /// Jobs and values live on the heap; deeply nested authored terms cannot
    /// recurse on the native stack or evade the shared structural-depth gate.
    fn projection_term(&mut self) -> PResult<RhoValue> {
        enum Job {
            Term {
                remainder_allowed: bool,
            },
            FinishAbs(String),
            ContinueCollection(Vec<Parsed<RhoValue>>),
            AfterCollectionValue(Vec<Parsed<RhoValue>>),
            FinishSubstLeft,
            FinishSubst(Parsed<RhoValue>),
            ContinueSExp {
                label: String,
                host: bool,
                args: Vec<Parsed<RhoValue>>,
            },
            AfterSExpArg {
                label: String,
                host: bool,
                args: Vec<Parsed<RhoValue>>,
            },
        }
        let mut jobs = vec![Job::Term { remainder_allowed: false }];
        let mut values = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Term { remainder_allowed } => match self.peek().clone() {
                    Tok::Ident(name) => {
                        self.bump();
                        values.push(self.parsed(
                            Self::projection_node("ast-var", vec![RhoValue::String(name)]),
                            1,
                            "projection term",
                        )?);
                    },
                    Tok::Ellipsis => {
                        if !remainder_allowed {
                            return self.err(
                                "a projection collection remainder must occur inside a collection",
                            );
                        }
                        self.bump();
                        let name = self.ident()?;
                        values.push(self.parsed(
                            Self::projection_node("ast-remainder", vec![RhoValue::String(name)]),
                            1,
                            "projection term",
                        )?);
                    },
                    Tok::KwTrue | Tok::KwFalse => {
                        let tag = if self.eat(&Tok::KwTrue) {
                            "ast-boolean-true"
                        } else {
                            self.expect(Tok::KwFalse)?;
                            "ast-boolean-false"
                        };
                        values.push(self.parsed(
                            Self::projection_node(tag, Vec::new()),
                            1,
                            "projection term",
                        )?);
                    },
                    Tok::Str(value) => {
                        self.bump();
                        values.push(self.parsed(
                            Self::projection_node("ast-string", vec![RhoValue::String(value)]),
                            1,
                            "projection term",
                        )?);
                    },
                    Tok::Integer(value) => {
                        self.bump();
                        if i64::try_from(value).is_err() {
                            return self.err(
                                "projection integer is outside the Rholang i64 literal range",
                            );
                        }
                        values.push(self.parsed(
                            Self::projection_node("ast-integer", vec![RhoValue::Integer(value)]),
                            1,
                            "projection term",
                        )?);
                    },
                    Tok::Caret => {
                        self.bump();
                        let binder = self.ident()?;
                        self.expect(Tok::Dot)?;
                        jobs.push(Job::FinishAbs(binder));
                        jobs.push(Job::Term { remainder_allowed: false });
                    },
                    Tok::LBrace => {
                        self.bump();
                        jobs.push(Job::ContinueCollection(Vec::new()));
                    },
                    Tok::LParen => {
                        self.bump();
                        if self.eat(&Tok::KwSubst) {
                            jobs.push(Job::FinishSubstLeft);
                            jobs.push(Job::Term { remainder_allowed: false });
                        } else {
                            let host = self.at_host_qualifier();
                            if host {
                                self.bump();
                                self.expect(Tok::Namespace)?;
                            }
                            let label = self.ident()?;
                            jobs.push(Job::ContinueSExp { label, host, args: Vec::new() });
                        }
                    },
                    other => {
                        return self
                            .err(format!("expected a projection term, found {}", other.describe()))
                    },
                },
                Job::FinishAbs(binder) => {
                    let body = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing abstraction body", self.span())
                    })?;
                    values.push(self.parsed(
                        Self::projection_node(
                            "ast-abs",
                            vec![RhoValue::String(binder), body.value],
                        ),
                        body.depth + 1,
                        "projection term",
                    )?);
                },
                Job::ContinueCollection(items) => {
                    if self.eat(&Tok::RBrace) {
                        values.push(self.finish_projection_collection(items)?);
                    } else {
                        jobs.push(Job::AfterCollectionValue(items));
                        jobs.push(Job::Term { remainder_allowed: true });
                    }
                },
                Job::AfterCollectionValue(mut items) => {
                    items.push(values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing collection term", self.span())
                    })?);
                    if self.eat(&Tok::Comma) {
                        jobs.push(Job::ContinueCollection(items));
                    } else {
                        self.expect(Tok::RBrace)?;
                        values.push(self.finish_projection_collection(items)?);
                    }
                },
                Job::FinishSubstLeft => {
                    let left = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing substitution abstraction", self.span())
                    })?;
                    jobs.push(Job::FinishSubst(left));
                    jobs.push(Job::Term { remainder_allowed: false });
                },
                Job::FinishSubst(left) => {
                    let right = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing substitution argument", self.span())
                    })?;
                    self.expect(Tok::RParen)?;
                    let depth = 1 + left.depth.max(right.depth);
                    values.push(self.parsed(
                        Self::projection_node("ast-subst", vec![left.value, right.value]),
                        depth,
                        "projection term",
                    )?);
                },
                Job::ContinueSExp { label, host, args } => {
                    if self.eat(&Tok::RParen) {
                        let depth = 1 + args.iter().map(|arg| arg.depth).max().unwrap_or(0);
                        let tag = if host { "ast-host-sexp" } else { "ast-sexp" };
                        values.push(self.parsed(
                            Self::projection_node(
                                tag,
                                vec![RhoValue::String(label), Self::projection_sequence(args)],
                            ),
                            depth,
                            "projection term",
                        )?);
                    } else {
                        jobs.push(Job::AfterSExpArg { label, host, args });
                        jobs.push(Job::Term { remainder_allowed: false });
                    }
                },
                Job::AfterSExpArg { label, host, mut args } => {
                    args.push(values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing constructor argument", self.span())
                    })?);
                    jobs.push(Job::ContinueSExp { label, host, args });
                },
            }
        }
        if values.len() != 1 {
            return self.err("projection-term PDA produced an invalid value stack");
        }
        Ok(values.pop().expect("checked one projection term").value)
    }

    fn finish_projection_collection(
        &self,
        items: Vec<Parsed<RhoValue>>,
    ) -> PResult<Parsed<RhoValue>> {
        let mut remainder = false;
        for (index, item) in items.iter().enumerate() {
            let is_remainder = matches!(&item.value, RhoValue::List(fields) if matches!(fields.first(), Some(RhoValue::String(tag)) if tag == "ast-remainder"));
            if is_remainder {
                if remainder || index + 1 != items.len() {
                    return self.err(
                        "a collection remainder must occur exactly once and in final position",
                    );
                }
                remainder = true;
            }
        }
        let depth = 1 + items.iter().map(|item| item.depth).max().unwrap_or(0);
        self.parsed(
            Self::projection_node("ast-collection", vec![Self::projection_sequence(items)]),
            depth,
            "projection term",
        )
    }

    fn ast(&mut self) -> PResult<Ast> {
        enum Job {
            Ast,
            FinishAbs {
                binder: Ident,
                span: Span,
            },
            ContinueCollection {
                values: Vec<Parsed<Ast>>,
                span: Span,
            },
            AfterCollectionValue {
                values: Vec<Parsed<Ast>>,
                span: Span,
            },
            FinishSubstLeft {
                span: Span,
            },
            FinishSubst {
                left: Parsed<Ast>,
                span: Span,
            },
            ContinueSExp {
                label: Label,
                args: Vec<Parsed<Ast>>,
                span: Span,
            },
            AfterSExpArg {
                label: Label,
                args: Vec<Parsed<Ast>>,
                span: Span,
            },
        }

        let mut jobs = vec![Job::Ast];
        let mut values = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Ast => {
                    let span = self.span();
                    match self.peek().clone() {
                        Tok::Ellipsis => {
                            self.bump();
                            let remainder = self.ident()?;
                            values.push(self.parsed(
                                Ast::Remainder(remainder, span),
                                1,
                                "rule AST",
                            )?);
                        },
                        Tok::Caret => {
                            self.bump();
                            let binder = self.ident()?;
                            self.expect(Tok::Dot)?;
                            jobs.push(Job::FinishAbs { binder, span });
                            jobs.push(Job::Ast);
                        },
                        Tok::LBrace => {
                            self.bump();
                            jobs.push(Job::ContinueCollection { values: Vec::new(), span });
                        },
                        Tok::LParen => {
                            self.bump();
                            if self.eat(&Tok::KwSubst) {
                                jobs.push(Job::FinishSubstLeft { span });
                                jobs.push(Job::Ast);
                            } else {
                                let label = self.ident()?;
                                jobs.push(Job::ContinueSExp { label, args: Vec::new(), span });
                            }
                        },
                        Tok::Ident(name) => {
                            self.bump();
                            values.push(self.parsed(Ast::Var(name, span), 1, "rule AST")?);
                        },
                        other => {
                            return self.err(format!("expected a term, found {}", other.describe()))
                        },
                    }
                },
                Job::FinishAbs { binder, span } => {
                    let body = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing abstraction body", self.span())
                    })?;
                    let depth = body.depth + 1;
                    values.push(self.parsed(
                        Ast::Abs(binder, Box::new(body.value), span),
                        depth,
                        "rule AST",
                    )?);
                },
                Job::ContinueCollection { values: items, span } => {
                    if self.eat(&Tok::RBrace) {
                        values.push(self.finish_collection(items, span)?);
                    } else {
                        jobs.push(Job::AfterCollectionValue { values: items, span });
                        jobs.push(Job::Ast);
                    }
                },
                Job::AfterCollectionValue { values: mut items, span } => {
                    items.push(values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing collection term", self.span())
                    })?);
                    if self.eat(&Tok::Comma) {
                        jobs.push(Job::ContinueCollection { values: items, span });
                    } else {
                        self.expect(Tok::RBrace)?;
                        values.push(self.finish_collection(items, span)?);
                    }
                },
                Job::FinishSubstLeft { span } => {
                    let left = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing substitution abstraction", self.span())
                    })?;
                    jobs.push(Job::FinishSubst { left, span });
                    jobs.push(Job::Ast);
                },
                Job::FinishSubst { left, span } => {
                    let right = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing substitution argument", self.span())
                    })?;
                    self.expect(Tok::RParen)?;
                    let depth = 1 + left.depth.max(right.depth);
                    values.push(self.parsed(
                        Ast::Subst(Box::new(left.value), Box::new(right.value), span),
                        depth,
                        "rule AST",
                    )?);
                },
                Job::ContinueSExp { label, args, span } => {
                    if self.eat(&Tok::RParen) {
                        let depth = 1 + args.iter().map(|arg| arg.depth).max().unwrap_or(0);
                        values.push(self.parsed(
                            Ast::SExp(label, args.into_iter().map(|arg| arg.value).collect(), span),
                            depth,
                            "rule AST",
                        )?);
                    } else {
                        jobs.push(Job::AfterSExpArg { label, args, span });
                        jobs.push(Job::Ast);
                    }
                },
                Job::AfterSExpArg { label, mut args, span } => {
                    args.push(values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Parse, "missing constructor argument", self.span())
                    })?);
                    jobs.push(Job::ContinueSExp { label, args, span });
                },
            }
        }
        if values.len() != 1 {
            return self.err("AST PDA produced an invalid value stack");
        }
        Ok(values.pop().expect("checked one AST value").value)
    }

    fn finish_collection(&self, items: Vec<Parsed<Ast>>, span: Span) -> PResult<Parsed<Ast>> {
        let mut saw_remainder = false;
        for (index, item) in items.iter().enumerate() {
            if matches!(item.value, Ast::Remainder(..)) {
                if saw_remainder || index + 1 != items.len() {
                    return Err(Diag::new(
                        DiagKind::Parse,
                        "a collection remainder must occur exactly once and in final position",
                        item.value.span(),
                    ));
                }
                saw_remainder = true;
            }
        }
        let depth = 1 + items.iter().map(|item| item.depth).max().unwrap_or(0);
        self.parsed(
            Ast::Coll(items.into_iter().map(|item| item.value).collect(), span),
            depth,
            "rule AST",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rholang_literal::render_rholang_value_literal;
    use std::collections::BTreeMap;

    fn projection_entries(source: &str) -> Vec<RewriteEntry> {
        let theory = parse_theory(source).expect("theory with projections parses");
        let TheoryExpr::Build { builder: Builder::Rewrites(entries), .. } = theory.body else {
            panic!("theory ends in a Rewrites builder");
        };
        entries
    }

    #[test]
    fn standalone_projection_surface_preserves_direction_rows_and_native_terms() {
        let entries = projection_entries(
            r#"
            Theory T() { Rewrites {
              projection Boolean : Bool <~> host::Bool {
                Yes : (BTrue) <~> true;
                No : (BFalse) <~> false;
              }
              projection Import : Entry <~ host::Proc {
                Take(x:Entry,h:host::Proc): if projection Boolean(x,h), x ~> h then (Wrap x) <~ (host::Par h);
              }
              projection TextValue : Text <~> host::Str via carrier;
            } }
        "#,
        );
        assert_eq!(entries.len(), 3);
        let RewriteEntry::Projection(boolean) = &entries[0] else {
            panic!("Boolean projection");
        };
        assert_eq!(boolean.direction, ProjectionDirection::Both);
        assert_eq!(boolean.guest, "Bool");
        assert_eq!(boolean.host, "Bool");
        let ProjectionBody::Rules(rows) = &boolean.body else {
            panic!("Boolean rows");
        };
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].name, "Yes");
        assert_eq!(rows[0].direction, ProjectionDirection::Both);
        assert_eq!(
            rows[0].guest,
            Parser::projection_node(
                "ast-sexp",
                vec![RhoValue::String("BTrue".into()), Parser::projection_node("sequence", vec![])]
            )
        );
        assert_eq!(rows[0].host, Parser::projection_node("ast-boolean-true", vec![]));
        assert!(rows[0].span.line < rows[1].span.line);
        let RewriteEntry::Projection(import) = &entries[1] else {
            panic!("Import projection");
        };
        assert_eq!(import.direction, ProjectionDirection::HostToGuest);
        let ProjectionBody::Rules(rows) = &import.body else {
            panic!("Import rows");
        };
        assert_eq!(rows[0].bindings.len(), 2);
        assert!(matches!(rows[0].bindings[1], ProjectionBinding::Host { .. }));
        assert_eq!(rows[0].premises.len(), 2);
        assert!(matches!(rows[0].premises[0], ProjectionPremise::Call { .. }));
        assert!(matches!(rows[0].premises[1], ProjectionPremise::Transition { .. }));
        assert_eq!(
            rows[0].host,
            Parser::projection_node(
                "ast-host-sexp",
                vec![
                    RhoValue::String("Par".into()),
                    Parser::projection_node(
                        "sequence",
                        vec![Parser::projection_node(
                            "ast-var",
                            vec![RhoValue::String("h".into())]
                        )]
                    )
                ]
            )
        );
        let RewriteEntry::Projection(carrier) = &entries[2] else {
            panic!("carrier projection");
        };
        assert!(matches!(carrier.body, ProjectionBody::Carrier));
    }

    #[test]
    fn standalone_projection_surface_refuses_direction_mismatch_and_deep_terms() {
        let wrong_arrow =
            "Theory T() { Rewrites { projection P : A <~ host::B { R : (A) ~> (host::B); } } }";
        assert!(parse_theory(wrong_arrow).is_err());
        let misplaced_remainder =
            "Theory T() { Rewrites { projection P : A ~> host::B { R : ...rest ~> true; } } }";
        assert!(parse_theory(misplaced_remainder).is_err());
        let collection_remainder =
            "Theory T() { Rewrites { projection P : A ~> host::B { R : {x, ...rest} ~> true; } } }";
        assert!(parse_theory(collection_remainder).is_ok());
        let nonfinal_remainder =
            "Theory T() { Rewrites { projection P : A ~> host::B { R : {...rest, x} ~> true; } } }";
        assert!(parse_theory(nonfinal_remainder).is_err());
        let duplicate_remainder =
            "Theory T() { Rewrites { projection P : A ~> host::B { R : {...first, ...second} ~> true; } } }";
        assert!(parse_theory(duplicate_remainder).is_err());
        let mut term = "x".to_string();
        for _ in 0..MAX_DDL_STRUCTURAL_DEPTH {
            term = format!("(Wrap {term})");
        }
        let source = format!(
            "Theory T() {{ Rewrites {{ projection P : A ~> host::B {{ R : {term} ~> true; }} }} }}"
        );
        let result = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || parse_theory(&source))
            .expect("small-stack parser worker")
            .join()
            .expect("projection parser must not overflow");
        assert!(result.is_err(), "overdeep projection term must be refused");
    }

    fn run_on_small_stack(source: String) -> Result<ModuleFile, Diag> {
        std::thread::Builder::new()
            .name("mettail-parser-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(move || parse_module(&source))
            .expect("spawn parser worker")
            .join()
            .expect("parser worker must not overflow or panic")
    }

    fn nested_apply(depth: usize) -> String {
        let mut expression = "Empty".to_string();
        for _ in 1..depth {
            expression = format!("F({expression})");
        }
        format!("Module Deep {{ Theory T() {{ {expression} }} theory T() }}")
    }

    fn nested_data(depth: usize) -> String {
        let mut value = "Nil".to_string();
        for _ in 1..depth {
            value = format!("[{value}]");
        }
        format!("Module Deep {{ Theory T() {{ Data({value}) }} theory T() }}")
    }

    fn nested_ast(depth: usize) -> String {
        let mut ast = "v".to_string();
        for _ in 1..depth {
            ast = format!("^x.{ast}");
        }
        format!("Module Deep {{ Theory T() {{ Equations {{ {ast} == v; }} }} theory T() }}")
    }

    #[test]
    fn theory_operators_keep_declared_precedence_and_left_associativity() {
        let module = parse_module(
            r#"Module P {
                Theory T() { Empty /\ Empty \/ Empty \ Empty \ Empty }
                theory T()
            }"#,
        )
        .expect("valid precedence witness");
        let expression = &module
            .declarations()
            .next()
            .expect("fixture has one declaration")
            .body;
        let TheoryExpr::Diff(lhs, rhs, _) = expression else {
            panic!("outer difference")
        };
        assert!(matches!(rhs.as_ref(), TheoryExpr::Empty(_)));
        let TheoryExpr::Diff(lhs, rhs, _) = lhs.as_ref() else {
            panic!("left associativity")
        };
        assert!(matches!(rhs.as_ref(), TheoryExpr::Empty(_)));
        let TheoryExpr::Join(lhs, rhs, _) = lhs.as_ref() else {
            panic!("join precedence")
        };
        assert!(matches!(rhs.as_ref(), TheoryExpr::Empty(_)));
        assert!(matches!(lhs.as_ref(), TheoryExpr::Meet(..)));
    }

    #[test]
    fn accepted_recursive_values_obey_the_shared_depth_bound() {
        for source in [
            nested_apply(MAX_DDL_STRUCTURAL_DEPTH),
            nested_data(MAX_DDL_STRUCTURAL_DEPTH),
            nested_ast(MAX_DDL_STRUCTURAL_DEPTH),
        ] {
            run_on_small_stack(source).expect("value at the structural bound is accepted");
        }
    }

    #[test]
    fn hostile_nesting_is_rejected_without_native_stack_growth() {
        for source in [nested_apply(20_000), nested_data(20_000), nested_ast(20_000)] {
            let error = run_on_small_stack(source).expect_err("deep value must be rejected");
            assert_eq!(error.kind, DiagKind::ResourceLimit);
            assert!(error.msg.contains("nesting exceeds the maximum"), "{error}");
        }
    }

    #[test]
    fn malformed_deep_grouping_and_trailing_source_fail_closed() {
        let mut grouped = "Module Deep { Theory T() { ".to_string();
        grouped.push_str(&"(".repeat(20_000));
        grouped.push_str("Empty } theory T() }");
        assert_eq!(
            run_on_small_stack(grouped)
                .expect_err("unclosed groups must fail")
                .kind,
            DiagKind::Parse
        );
        assert_eq!(
            parse_module("Module M { Theory T() { Empty } theory T() } garbage")
                .expect_err("trailing source must fail")
                .kind,
            DiagKind::Parse
        );
    }

    #[test]
    fn canonical_value_renderer_and_reader_are_exact_left_inverses() {
        let values = [
            RhoValue::Map(BTreeMap::new()),
            RhoValue::Map(BTreeMap::from([
                ("bytes".into(), RhoValue::Bytes(vec![0x00, 0xab, 0xff])),
                (
                    "nested".into(),
                    RhoValue::List(vec![
                        RhoValue::Integer(i64::MAX as i128 + 1),
                        RhoValue::FloatBits((-0.0f64).to_bits()),
                        RhoValue::String("quote \" slash \\".into()),
                        RhoValue::Boolean(true),
                        RhoValue::Nil,
                    ]),
                ),
            ])),
        ];

        for expected in values {
            let literal = render_rholang_value_literal(&expected).expect("value renders");
            let toks = lex(&literal).expect("rendered value lexes");
            let mut parser = Parser { toks, pos: 0 };
            let actual = parser.rho_value().expect("rendered value parses");
            parser
                .expect(Tok::Eof)
                .expect("reader consumes the value exactly");
            assert_eq!(actual, expected, "canonical literal {literal}");
        }
    }

    #[test]
    fn malformed_empty_map_and_scalar_frames_are_rejected() {
        for literal in ["Map(", "Map(Nil)", "Map)", "map()", r#"b"0""#, "1.0n"] {
            let source = format!("Theory Bad() {{ Data({literal}) }}");
            assert_eq!(
                parse_theory(&source)
                    .expect_err("malformed canonical frame must fail")
                    .kind,
                DiagKind::Parse,
                "{literal}"
            );
        }
    }

    #[test]
    fn collection_remainders_are_unique_and_final() {
        for equation in ["{...rest, x} == x;", "{...left, ...right} == x;"] {
            let source =
                format!("Module Bad {{ Theory T() {{ Equations {{ {equation} }} }} theory T() }}");
            let error = parse_module(&source).expect_err("invalid remainder placement must fail");
            assert_eq!(error.kind, DiagKind::Parse);
            assert!(error.msg.contains("remainder"));
        }
    }
}
