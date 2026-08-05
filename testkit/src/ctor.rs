//! **From a recorded counterexample back to Rust source.**
//!
//! proptest writes a falsifying case to its corpus as two things:
//!
//! ```text
//! cc 26e407af… # shrinks to term = Lam(Scope { pattern: Binder(FreeVar { unique_id: UniqueId(82),
//!              pretty_name: Some("a6") }), body: TVar(OrdVar(Free(FreeVar { … }))) })
//! ```
//!
//! a SEED and the shrunk value's `Debug` TEXT. Promoting that entry to a named regression
//! test means writing the term as Rust. This module is what does it.
//!
//! # Why the seed is not the way in
//!
//! The obvious approach — replay the seed, get the term, print it — does not work, and the
//! reason is structural rather than incidental. proptest persists the seed of the case's
//! FIRST generated input, and separately records the `Debug` of the SHRUNK value
//! (`proptest-1.10.0/src/test_runner/runner.rs`: `PersistedSeed(seed)` comes from
//! `self.rng.gen_get_seed()` before the case runs, while `value` comes out of
//! `TestError::Fail(_, value)` after shrinking). Replaying reconstructs the pre-shrink
//! input, which is a different — and usually far larger — term.
//!
//! Measured, on Lambda's sole corpus entry: the recorded term binds `a6`, and replaying its
//! seed under `arb_term(d)` yields a term binding `a7` for every `d` in `1..=4`, growing
//! with `d`. The recorded term is not in the replayed family at any depth.
//!
//! So the `Debug` text is the only complete record of the counterexample, and reading it is
//! the only faithful route.
//!
//! # Why the text is not already Rust
//!
//! Five reasons, each measured against this repository's own generated output:
//!
//! 1. **`Arc` is erased.** `GtStr(std::sync::Arc<Str>, std::sync::Arc<Str>)` prints
//!    `GtStr(Concat(…), …)`. Every nested node needs an `Arc::new` that is not in the text.
//! 2. **`String` prints as `&str`.** `StringLit(std::string::String)` prints
//!    `StringLit("ae")`, and `"ae"` is a `&'static str` in source position.
//! 3. **Enum qualification is erased AND ambiguous.** The `Debug` emitter writes the bare
//!    variant name. Calculator declares `NumLit` in THREE enums with three payload types —
//!    `Int::NumLit(i32)`, `UInt32::NumLit(u32)`, `BigInt::NumLit(CanonicalBigInt)`. Nothing
//!    in the text distinguishes them; only the expected type at that position does.
//! 4. **Foreign values are not constructible from their `Debug`.** `UniqueId(51)` has a
//!    private field and only `UniqueId::new()`, drawing from a process-global counter.
//! 5. **Some of it is not Rust syntax at all.** `HashBag { counts: {Err: 1}, total_count: 1 }`
//!    — `{K: V}` is not a Rust expression. `Fixed(-2147483648/1)` parses as division.
//!    `Scope { pattern: …, body: … }` is synthesized by the emitter; the API is
//!    `Scope::from_parts_unsafe`.
//!
//! # Why name-based variable reconstruction is FAITHFUL, not an approximation
//!
//! `UniqueId(82)` cannot be written and is not written. It does not need to be, and this is
//! the load-bearing fact that makes the whole approach exact rather than lossy:
//!
//! - The generated strategies build every variable through the name cache —
//!   `macros/src/gen/test_gen/strategies.rs` emits
//!   `OrdVar(Var::Free(get_or_create_var("{name}")))`, and `runtime/src/binding.rs`
//!   shows `get_or_create_var` is a thread-local `HashMap<String, FreeVar>`. Two
//!   occurrences of the same name in one process are therefore the SAME `FreeVar`.
//! - `FreeVar`'s equality is by `unique_id` ALONE (`moniker-0.5.0/src/free_var.rs`).
//!
//! Together: within a process, name determines identity and identity determines equality,
//! so `unique_id` carries no information the `pretty_name` does not already fix.
//! Reconstructing from the name reproduces the term up to the only equality the language
//! has. The [`crate::ctor`] emitter therefore writes `get_or_create_var("a6")` and the
//! promoted test's `Debug` comparison normalizes `UniqueId(\d+)` to `UniqueId(_)` — the one
//! field that is process-global and genuinely not reproducible.
//!
//! # The pipeline
//!
//! ```text
//!   corpus line ──parse_debug_text──▶ DebugNode ──emit──▶ Rust constructor source
//!                                        ▲                          │
//!                        Schema ─────────┘                          ▼
//!         (target/generated/<lang>/rust_ctor.rs)          rustc + the promoted test's
//!                                                          Debug-equality assertion
//! ```
//!
//! The final oracle is not in this module: it is assertion 2 of every promoted test, which
//! constructs the term and requires its normalized `Debug` to equal the recorded text
//! character for character. That is what makes "passes because it constructs the wrong
//! term" impossible, and it is why the emitter is allowed to be a source-to-source
//! transducer rather than something that has to be trusted.

use std::collections::BTreeMap;
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// The schema
// ══════════════════════════════════════════════════════════════════════════════

/// Opening marker of the extractable schema block inside `rust_ctor.rs`.
///
/// Kept in lock-step with `macros/src/gen/syntax/rust_ctor.rs::SCHEMA_BEGIN`;
/// [`Schema::parse`] fails loudly if a file does not carry it, so a drift cannot degrade
/// into an empty schema that silently rejects every term.
pub const SCHEMA_BEGIN: &str = "@@ METTAIL-RUST-CTOR-SCHEMA v1 BEGIN @@";

/// Closing marker. See [`SCHEMA_BEGIN`].
pub const SCHEMA_END: &str = "@@ METTAIL-RUST-CTOR-SCHEMA v1 END @@";

/// How a constructor field is typed, and therefore what shape its `Debug` text has and what
/// Rust must be written for it.
pub enum FieldSpec {
    /// `Arc<C>` for a declared category `C` — a nested term.
    Cat(String),
    /// `OrdVar`.
    Var,
    /// A bare native value; the string is the DECLARED Rust type.
    Native(String),
    /// A category-direct collection field, e.g. `HashBag<Arc<Proc>>`.
    Coll { kind: String, elem: String },
    /// A native collection-literal wrapper, e.g. `HashSetLit<Proc>`.
    CollLit { kind: String, elem: String },
    /// `Scope<Binder<String>, Arc<B>>`.
    Scope1 { binder: String, body: String },
    /// `Scope<Vec<Binder<String>>, Arc<B>>`.
    ScopeN { binder: String, body: String },
    /// A runtime `BehavioralPred` guard slot.
    Pred,
    /// A `v@Tok` token-text capture — `String`.
    OpaqueToken,
    /// A `*flt(...)` guest-body capture — `Arc<FltNode>`.
    OpaqueGuest,
    /// `Option<inner>`.
    Opt(Box<FieldSpec>),
}

mod lifecycle;

/// One constructor of one category.
#[derive(Debug, Clone)]
pub struct Variant {
    pub category: String,
    pub label: String,
    pub kind: String,
    pub fields: Vec<FieldSpec>,
}

/// A language's complete constructor schema.
#[derive(Debug, Clone, Default)]
pub struct Schema {
    pub language: String,
    /// Category name → declared native type, if the category is a native alias.
    pub natives: BTreeMap<String, Option<String>>,
    /// `(category, label)` → variant.
    pub variants: BTreeMap<(String, String), Variant>,
}

impl Schema {
    /// Parse the schema out of a generated `rust_ctor.rs`.
    ///
    /// The block is located by its marker LINES rather than by parsing Rust, so the reader
    /// needs no Rust parser and a formatting change cannot break it. The emitter writes the
    /// schema as a RAW string literal for exactly this reason: an escaped literal would
    /// collapse the block onto one physical line.
    pub fn parse(file_text: &str) -> Result<Schema, String> {
        let begin = file_text
            .find(SCHEMA_BEGIN)
            .ok_or_else(|| format!("no `{SCHEMA_BEGIN}` marker in the generated file"))?;
        let after_begin = begin + SCHEMA_BEGIN.len();
        let end_rel = file_text[after_begin..]
            .find(SCHEMA_END)
            .ok_or_else(|| format!("no `{SCHEMA_END}` marker after the opening marker"))?;
        let body = &file_text[after_begin..after_begin + end_rel];

        let mut schema = Schema::default();
        for (lineno, line) in body.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let mut parts = line.split(' ');
            let tag = parts.next().unwrap_or("");
            match tag {
                "LANG" => {
                    schema.language = parts
                        .next()
                        .ok_or_else(|| format!("line {}: `LANG` with no name", lineno + 1))?
                        .to_string();
                },
                "CAT" => {
                    let name = parts
                        .next()
                        .ok_or_else(|| format!("line {}: `CAT` with no name", lineno + 1))?;
                    let native = parts.next().unwrap_or("-");
                    schema.natives.insert(
                        name.to_string(),
                        if native == "-" {
                            None
                        } else {
                            Some(native.to_string())
                        },
                    );
                },
                "V" => {
                    let category = parts
                        .next()
                        .ok_or_else(|| format!("line {}: `V` with no category", lineno + 1))?
                        .to_string();
                    let label = parts
                        .next()
                        .ok_or_else(|| format!("line {}: `V` with no label", lineno + 1))?
                        .to_string();
                    let kind = parts
                        .next()
                        .ok_or_else(|| format!("line {}: `V` with no kind", lineno + 1))?
                        .to_string();
                    let mut fields = Vec::new();
                    for descriptor in parts {
                        fields.push(parse_field_spec(descriptor).map_err(|e| {
                            format!("line {}: field `{descriptor}`: {e}", lineno + 1)
                        })?);
                    }
                    schema.variants.insert(
                        (category.clone(), label.clone()),
                        Variant { category, label, kind, fields },
                    );
                },
                other => {
                    return Err(format!("line {}: unknown record tag `{other}`", lineno + 1));
                },
            }
        }

        if schema.variants.is_empty() {
            return Err("the schema declares no variants; it would reject every term".to_string());
        }
        Ok(schema)
    }

    /// Every category this schema declares, in declaration-stable (sorted) order.
    pub fn categories(&self) -> Vec<&str> {
        self.natives.keys().map(|s| s.as_str()).collect()
    }

    /// Whether any category declares a variant with this label.
    ///
    /// Used by the Tier-3 reinstatement guards: a constructor that appears in an archived
    /// counterexample and in NO category has genuinely left the grammar.
    pub fn has_label_anywhere(&self, label: &str) -> bool {
        self.variants.keys().any(|(_, l)| l == label)
    }

    /// The categories that declare a variant with this label.
    pub fn categories_declaring(&self, label: &str) -> Vec<&str> {
        self.variants
            .keys()
            .filter(|(_, l)| l == label)
            .map(|(c, _)| c.as_str())
            .collect()
    }
}

fn parse_field_spec(descriptor: &str) -> Result<FieldSpec, String> {
    let mut optional_depth = 0usize;
    let mut descriptor = descriptor;
    while let Some(inner) = descriptor.strip_prefix("opt:") {
        optional_depth += 1;
        descriptor = inner;
    }
    let mut spec = if descriptor == "var" {
        FieldSpec::Var
    } else if descriptor == "pred" {
        FieldSpec::Pred
    } else if descriptor == "opaque:token" {
        FieldSpec::OpaqueToken
    } else if descriptor == "opaque:guest" {
        FieldSpec::OpaqueGuest
    } else if let Some(cat) = descriptor.strip_prefix("cat:") {
        FieldSpec::Cat(cat.to_string())
    } else if let Some(ty) = descriptor.strip_prefix("native:") {
        FieldSpec::Native(ty.to_string())
    } else {
        let mut parsed = None;
        for (prefix, build) in
            [("coll:", 0u8), ("collit:", 1u8), ("scope1:", 2u8), ("scopeN:", 3u8)]
        {
            if let Some(rest) = descriptor.strip_prefix(prefix) {
                let (a, b) = rest
                    .split_once(':')
                    .ok_or_else(|| format!("`{prefix}` needs two colon-separated arguments"))?;
                parsed = Some(match build {
                    0 => FieldSpec::Coll { kind: a.to_string(), elem: b.to_string() },
                    1 => FieldSpec::CollLit { kind: a.to_string(), elem: b.to_string() },
                    2 => FieldSpec::Scope1 {
                        binder: a.to_string(),
                        body: b.to_string(),
                    },
                    _ => FieldSpec::ScopeN {
                        binder: a.to_string(),
                        body: b.to_string(),
                    },
                });
                break;
            }
        }
        parsed.ok_or_else(|| format!("unrecognised field descriptor `{descriptor}`"))?
    };
    for _ in 0..optional_depth {
        spec = FieldSpec::Opt(Box::new(spec));
    }
    Ok(spec)
}

// ══════════════════════════════════════════════════════════════════════════════
// The Debug-text parser
// ══════════════════════════════════════════════════════════════════════════════

/// A node of parsed `Debug` output.
///
/// This is a purely SYNTACTIC tree. It carries no idea which enum a `Call` head belongs to
/// — that is exactly the information `Debug` erased, and it is supplied by the [`Schema`]
/// during emission.
#[derive(Debug, Clone, PartialEq)]
pub enum DebugNode {
    /// `Ident(a, b, …)`
    Call { head: String, args: Vec<DebugNode> },
    /// `Ident { field: v, … }`
    Struct {
        head: String,
        fields: Vec<(String, DebugNode)>,
    },
    /// A bare identifier: a nullary constructor, `None`, `true`, `false`.
    Ident(String),
    /// `"…"`, already unescaped.
    Str(String),
    /// An integer, possibly negative.
    Int(i128),
    /// A decimal.
    Float(f64),
    /// `a/b` — the shape `CanonicalFixedPoint`'s `Debug` uses.
    Ratio(i128, i128),
    /// `[a, b, …]`
    List(Vec<DebugNode>),
    /// `{a, b, …}` — a set or bag-like brace group with no `:`.
    Set(Vec<DebugNode>),
    /// `{k: v, …}`
    Map(Vec<(DebugNode, DebugNode)>),
    /// `(a, b, …)` with no head.
    Tuple(Vec<DebugNode>),
    /// `name=value` — a NAMED argument inside a call.
    ///
    /// Not a `Debug` derive shape: it comes from hand-written `Debug` impls that use
    /// `write!(f, "LexWeight(primary={:?}, src={}, rule={})", …)`. Measured in
    /// `prattail/proptest-regressions/automata/lex_weight.txt`. Kept as its own variant
    /// rather than folded into `Struct` because the two RE-PRINT differently (`name=value`
    /// with no spaces, inside parentheses), and the round-trip proof is byte equality.
    Named { name: String, value: Box<DebugNode> },
    /// `a..b` — a range, as `proc_macro2::Span`'s `Debug` writes inside `bytes(..)`.
    Range(i128, i128),
}

/// One `name = value` binding from a `# shrinks to` line.
#[derive(Debug, Clone)]
pub struct Binding {
    pub name: String,
    pub value: DebugNode,
}

/// Parse a whole `# shrinks to` payload into its bindings.
///
/// proptest writes `term = <value>` for a one-argument property and
/// `blueprint = <value>, left_seed = <value>, …` for several. A binding name may carry a
/// `mut ` prefix (proptest prints the pattern, and `mut cached_joins = …` occurs in this
/// repository's own corpora), which is stripped.
pub fn parse_shrinks_to(text: &str) -> Result<Vec<Binding>, String> {
    let mut parser = Parser::new(text);
    let mut bindings = Vec::new();
    loop {
        parser.skip_ws();
        if parser.at_end() {
            break;
        }
        let mut name = parser.take_ident()?;
        if name == "mut" {
            parser.skip_ws();
            name = parser.take_ident()?;
        }
        parser.skip_ws();
        parser.expect('=')?;
        let value = parser.parse_value()?;
        bindings.push(Binding { name, value });
        parser.skip_ws();
        if parser.peek() == Some(',') {
            parser.bump();
        } else {
            break;
        }
    }
    parser.skip_ws();
    if !parser.at_end() {
        return Err(format!(
            "trailing text after the last binding at byte {}: {:?}",
            parser.pos,
            &parser.src[parser.pos..].iter().collect::<String>()
        ));
    }
    if bindings.is_empty() {
        return Err("no `name = value` binding found".to_string());
    }
    Ok(bindings)
}

/// Parse a single `Debug` value (no `name =` prefix).
pub fn parse_debug_value(text: &str) -> Result<DebugNode, String> {
    let mut parser = Parser::new(text);
    let value = parser.parse_value()?;
    parser.skip_ws();
    if !parser.at_end() {
        return Err(format!("trailing text after the value at byte {}", parser.pos));
    }
    Ok(value)
}

struct Parser {
    src: Vec<char>,
    pos: usize,
}

impl Parser {
    fn new(text: &str) -> Parser {
        Parser { src: text.chars().collect(), pos: 0 }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.src.len()
    }

    fn peek(&self) -> Option<char> {
        self.src.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.src.get(self.pos + offset).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(c) if c.is_whitespace()) {
            self.pos += 1;
        }
    }

    fn expect(&mut self, want: char) -> Result<(), String> {
        self.skip_ws();
        match self.bump() {
            Some(c) if c == want => Ok(()),
            other => Err(format!(
                "expected `{want}` at byte {}, found {:?}",
                self.pos.saturating_sub(1),
                other
            )),
        }
    }

    /// A bare identifier: no path segments. Used for STRUCT FIELD names and binding names,
    /// which are always single identifiers.
    fn take_ident(&mut self) -> Result<String, String> {
        self.skip_ws();
        let start = self.pos;
        while matches!(self.peek(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.pos += 1;
        }
        if self.pos == start {
            return Err(format!("expected an identifier at byte {start}"));
        }
        Ok(self.src[start..self.pos].iter().collect())
    }

    /// A possibly PATH-QUALIFIED head: `Ident`, or `Type::Path`, or
    /// `PathArguments::None`.
    ///
    /// `syn`'s hand-written `Debug` impls print the enum path, not the bare variant — the
    /// opposite of the generated `debug.rs`, which prints the bare name. Both shapes occur
    /// in this repository's corpora (`macros/proptest-regressions/.../grammar_generality_prop.txt`
    /// is full of `Type::Path { qself: None, … }`), so the head parser accepts both.
    ///
    /// ⚠ `::` is consumed only when a `:` is IMMEDIATELY followed by another `:`. A single
    /// `:` separates a struct field from its value and must be left for the caller.
    fn take_path_head(&mut self) -> Result<String, String> {
        self.skip_ws();
        let mut head = self.take_ident()?;
        while self.peek() == Some(':') && self.peek_at(1) == Some(':') {
            self.pos += 2;
            head.push_str("::");
            head.push_str(&self.take_ident()?);
        }
        Ok(head)
    }

    /// Whether what follows the current identifier is `{`, meaning a STRUCT literal rather
    /// than a bare identifier followed by an unrelated brace group.
    ///
    /// `Debug` writes `Ident { … }` with exactly one space, so the lookahead is a single
    /// space then `{`. Being strict here matters: `Scope { pattern: …` must be a struct,
    /// while a set element followed by `}` must not be mistaken for one.
    fn struct_follows(&self) -> bool {
        self.peek() == Some(' ') && self.peek_at(1) == Some('{')
    }

    fn parse_value(&mut self) -> Result<DebugNode, String> {
        self.skip_ws();
        match self.peek() {
            None => Err("unexpected end of input where a value was expected".to_string()),
            Some('"') => self.parse_string().map(DebugNode::Str),
            Some('[') => {
                let items = self.parse_delimited('[', ']')?;
                Ok(DebugNode::List(items))
            },
            Some('{') => self.parse_brace_group(),
            Some('(') => {
                let items = self.parse_delimited('(', ')')?;
                Ok(DebugNode::Tuple(items))
            },
            Some(c) if c == '-' || c.is_ascii_digit() => self.parse_number(),
            Some(c) if c.is_alphabetic() || c == '_' => {
                let head = self.take_path_head()?;
                if self.peek() == Some('(') {
                    let args = self.parse_delimited('(', ')')?;
                    Ok(DebugNode::Call { head, args })
                } else if self.struct_follows() {
                    self.bump(); // the space
                    let fields = self.parse_struct_fields()?;
                    Ok(DebugNode::Struct { head, fields })
                } else {
                    Ok(DebugNode::Ident(head))
                }
            },
            Some(c) => Err(format!("unexpected character {c:?} at byte {}", self.pos)),
        }
    }

    fn parse_delimited(&mut self, open: char, close: char) -> Result<Vec<DebugNode>, String> {
        self.expect(open)?;
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            if self.peek() == Some(close) {
                self.bump();
                break;
            }
            items.push(self.parse_call_argument()?);
            self.skip_ws();
            match self.peek() {
                Some(',') => {
                    self.bump();
                },
                Some(c) if c == close => {
                    self.bump();
                    break;
                },
                other => {
                    return Err(format!(
                        "expected `,` or `{close}` at byte {}, found {:?}",
                        self.pos, other
                    ))
                },
            }
        }
        Ok(items)
    }

    /// One argument of a call or list, which may be `name=value`.
    ///
    /// A hand-written `Debug` may label its arguments — `LexWeight(primary=…, src=0,
    /// rule=0)`. The `=` is checked AFTER parsing an identifier and only when the
    /// identifier is followed directly by `=`, so a bare nullary constructor is unaffected.
    fn parse_call_argument(&mut self) -> Result<DebugNode, String> {
        self.skip_ws();
        let save = self.pos;
        if matches!(self.peek(), Some(c) if c.is_alphabetic() || c == '_') {
            if let Ok(name) = self.take_ident() {
                if self.peek() == Some('=') && self.peek_at(1) != Some('=') {
                    self.bump();
                    let value = self.parse_value()?;
                    return Ok(DebugNode::Named { name, value: Box::new(value) });
                }
            }
            self.pos = save;
        }
        self.parse_value()
    }

    /// `{ … }` is a map when its first element is `k: v`, and a set otherwise.
    ///
    /// The distinction cannot be made from the delimiter alone: `HashMap`'s `Debug` writes
    /// `{k: v}` and `HashSet`'s writes `{v}`. Both occur in this repository's corpora, so
    /// the decision is made by looking for a top-level `:` in the FIRST element.
    fn parse_brace_group(&mut self) -> Result<DebugNode, String> {
        self.expect('{')?;
        self.skip_ws();
        if self.peek() == Some('}') {
            self.bump();
            // An empty brace group is ambiguous between an empty map and an empty set. It is
            // reported as an empty MAP, and every consumer that wants a set accepts an empty
            // map as an empty set — stated here so the choice is not silent.
            return Ok(DebugNode::Map(Vec::new()));
        }
        let first = self.parse_value()?;
        self.skip_ws();
        if self.peek() == Some(':') {
            self.bump();
            let first_value = self.parse_value()?;
            let mut entries = vec![(first, first_value)];
            loop {
                self.skip_ws();
                match self.peek() {
                    Some(',') => {
                        self.bump();
                        self.skip_ws();
                        if self.peek() == Some('}') {
                            self.bump();
                            break;
                        }
                        let k = self.parse_value()?;
                        self.skip_ws();
                        self.expect(':')?;
                        let v = self.parse_value()?;
                        entries.push((k, v));
                    },
                    Some('}') => {
                        self.bump();
                        break;
                    },
                    other => {
                        return Err(format!(
                            "expected `,` or `}}` in a map at byte {}, found {:?}",
                            self.pos, other
                        ))
                    },
                }
            }
            Ok(DebugNode::Map(entries))
        } else {
            let mut items = vec![first];
            loop {
                self.skip_ws();
                match self.peek() {
                    Some(',') => {
                        self.bump();
                        self.skip_ws();
                        if self.peek() == Some('}') {
                            self.bump();
                            break;
                        }
                        items.push(self.parse_value()?);
                    },
                    Some('}') => {
                        self.bump();
                        break;
                    },
                    other => {
                        return Err(format!(
                            "expected `,` or `}}` in a set at byte {}, found {:?}",
                            self.pos, other
                        ))
                    },
                }
            }
            Ok(DebugNode::Set(items))
        }
    }

    fn parse_struct_fields(&mut self) -> Result<Vec<(String, DebugNode)>, String> {
        self.expect('{')?;
        let mut fields = Vec::new();
        loop {
            self.skip_ws();
            if self.peek() == Some('}') {
                self.bump();
                break;
            }
            let name = self.take_ident()?;
            self.skip_ws();
            self.expect(':')?;
            let value = self.parse_value()?;
            fields.push((name, value));
            self.skip_ws();
            match self.peek() {
                Some(',') => {
                    self.bump();
                },
                Some('}') => {
                    self.bump();
                    break;
                },
                other => {
                    return Err(format!(
                        "expected `,` or `}}` in a struct at byte {}, found {:?}",
                        self.pos, other
                    ))
                },
            }
        }
        Ok(fields)
    }

    fn parse_string(&mut self) -> Result<String, String> {
        self.expect('"')?;
        let mut out = String::new();
        loop {
            match self.bump() {
                None => return Err("unterminated string literal".to_string()),
                Some('"') => break,
                Some('\\') => match self.bump() {
                    Some('n') => out.push('\n'),
                    Some('r') => out.push('\r'),
                    Some('t') => out.push('\t'),
                    Some('0') => out.push('\0'),
                    Some('\\') => out.push('\\'),
                    Some('\'') => out.push('\''),
                    Some('"') => out.push('"'),
                    Some('u') => {
                        // Rust's `Debug` for `char`/`str` writes `\u{XXXX}`.
                        self.expect('{')?;
                        let start = self.pos;
                        while matches!(self.peek(), Some(c) if c.is_ascii_hexdigit()) {
                            self.pos += 1;
                        }
                        let hex: String = self.src[start..self.pos].iter().collect();
                        self.expect('}')?;
                        let code = u32::from_str_radix(&hex, 16)
                            .map_err(|e| format!("bad `\\u{{{hex}}}` escape: {e}"))?;
                        out.push(
                            char::from_u32(code)
                                .ok_or_else(|| format!("`\\u{{{hex}}}` is not a scalar value"))?,
                        );
                    },
                    other => {
                        return Err(format!("unsupported escape `\\{}`", other.unwrap_or('?')))
                    },
                },
                Some(c) => out.push(c),
            }
        }
        Ok(out)
    }

    fn parse_number(&mut self) -> Result<DebugNode, String> {
        let start = self.pos;
        if self.peek() == Some('-') {
            self.bump();
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.pos += 1;
        }
        // `CanonicalFixedPoint`'s `Debug` writes `a/b`; `f64`'s writes `1.5`.
        if self.peek() == Some('/') {
            let numer: String = self.src[start..self.pos].iter().collect();
            self.bump();
            let dstart = self.pos;
            if self.peek() == Some('-') {
                self.bump();
            }
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.pos += 1;
            }
            let denom: String = self.src[dstart..self.pos].iter().collect();
            return Ok(DebugNode::Ratio(
                numer
                    .parse()
                    .map_err(|e| format!("bad numerator {numer:?}: {e}"))?,
                denom
                    .parse()
                    .map_err(|e| format!("bad denominator {denom:?}: {e}"))?,
            ));
        }
        // `a..b` — a range, not a float. `proc_macro2::Span`'s `Debug` writes
        // `bytes(26637..26640)`, and the two dots must not be mistaken for a decimal point.
        if self.peek() == Some('.') && self.peek_at(1) == Some('.') {
            let low: String = self.src[start..self.pos].iter().collect();
            self.pos += 2;
            let hstart = self.pos;
            if self.peek() == Some('-') {
                self.bump();
            }
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.pos += 1;
            }
            let high: String = self.src[hstart..self.pos].iter().collect();
            return Ok(DebugNode::Range(
                low.parse()
                    .map_err(|e| format!("bad range start {low:?}: {e}"))?,
                high.parse()
                    .map_err(|e| format!("bad range end {high:?}: {e}"))?,
            ));
        }
        if self.peek() == Some('.') && matches!(self.peek_at(1), Some(c) if c.is_ascii_digit()) {
            self.bump();
            while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                self.pos += 1;
            }
            let text: String = self.src[start..self.pos].iter().collect();
            return Ok(DebugNode::Float(
                text.parse()
                    .map_err(|e| format!("bad float {text:?}: {e}"))?,
            ));
        }
        let text: String = self.src[start..self.pos].iter().collect();
        Ok(DebugNode::Int(
            text.parse()
                .map_err(|e| format!("bad integer {text:?}: {e}"))?,
        ))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// The emitter
// ══════════════════════════════════════════════════════════════════════════════

/// Why a term could not be written as Rust.
///
/// The variants are the campaign's TIER boundaries, not a flat error bag. A corpus entry
/// that fails with [`EmitError::UnknownConstructor`] is a term whose constructor has left
/// the grammar — which is a Tier-2 (renamed, successor identified) or Tier-3 (no successor)
/// case, never a reason to drop the entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EmitError {
    /// No category declares this constructor at all. Tier-3 territory.
    UnknownConstructor { label: String },
    /// The constructor exists, but not in the category expected at this position.
    WrongCategory {
        label: String,
        expected: String,
        found_in: Vec<String>,
    },
    /// The text's shape does not match the field's declared type.
    ShapeMismatch { expected: String, found: String },
    /// The schema declares a field type this emitter does not know how to write.
    UnsupportedFieldType { descriptor: String },
}

impl fmt::Display for EmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EmitError::UnknownConstructor { label } => write!(
                f,
                "no category in this grammar declares a constructor named `{label}` — the \
                 recorded counterexample uses a constructor that has LEFT the language"
            ),
            EmitError::WrongCategory { label, expected, found_in } => write!(
                f,
                "`{label}` is not a constructor of `{expected}` (it is declared by: {})",
                found_in.join(", ")
            ),
            EmitError::ShapeMismatch { expected, found } => {
                write!(f, "expected {expected}, found {found}")
            },
            EmitError::UnsupportedFieldType { descriptor } => write!(
                f,
                "the schema declares field type `{descriptor}`, which this emitter cannot \
                 write; extend `testkit::ctor` rather than dropping the entry"
            ),
        }
    }
}

/// Write `node` as Rust constructor source for a term of category `category`.
///
/// The produced source assumes `mettail_runtime` is in scope by that path and that the
/// language's category enums are in scope unqualified — the shape every hand-written test
/// in `languages/tests/` already uses.
pub fn emit_category(
    schema: &Schema,
    category: &str,
    node: &DebugNode,
) -> Result<String, EmitError> {
    let (head, args): (&str, &[DebugNode]) = match node {
        DebugNode::Call { head, args } => (head.as_str(), args.as_slice()),
        DebugNode::Ident(head) => (head.as_str(), &[]),
        other => {
            return Err(EmitError::ShapeMismatch {
                expected: format!("a constructor of `{category}`"),
                found: describe(other),
            })
        },
    };

    let variant = match schema
        .variants
        .get(&(category.to_string(), head.to_string()))
    {
        Some(v) => v,
        None => {
            let elsewhere = schema.categories_declaring(head);
            return Err(if elsewhere.is_empty() {
                EmitError::UnknownConstructor { label: head.to_string() }
            } else {
                EmitError::WrongCategory {
                    label: head.to_string(),
                    expected: category.to_string(),
                    found_in: elsewhere.into_iter().map(str::to_string).collect(),
                }
            });
        },
    };

    // A `literal` variant carries its CATEGORY's native type, which is what disambiguates
    // `NumLit` across the three Calculator enums that declare it.
    if variant.kind == "literal" || variant.kind == "collit" {
        let native = schema
            .natives
            .get(category)
            .cloned()
            .flatten()
            .unwrap_or_else(|| "-".to_string());
        let payload = args.first().ok_or_else(|| EmitError::ShapeMismatch {
            expected: format!("`{head}(<{native}>)`"),
            found: "a nullary constructor".to_string(),
        })?;
        let inner = if variant.kind == "collit" {
            match variant.fields.first() {
                Some(FieldSpec::CollLit { kind, elem }) => {
                    emit_collection(schema, kind, elem, payload, true)?
                },
                _ => emit_native(&native, payload)?,
            }
        } else {
            emit_native(&native, payload)?
        };
        return Ok(format!("{category}::{head}({inner})"));
    }

    if variant.fields.is_empty() {
        if !args.is_empty() {
            return Err(EmitError::ShapeMismatch {
                expected: format!("`{head}` with no arguments"),
                found: format!("{} argument(s)", args.len()),
            });
        }
        return Ok(format!("{category}::{head}"));
    }

    if args.len() != variant.fields.len() {
        return Err(EmitError::ShapeMismatch {
            expected: format!("`{head}` with {} argument(s)", variant.fields.len()),
            found: format!("{} argument(s)", args.len()),
        });
    }

    let mut rendered = Vec::with_capacity(variant.fields.len());
    for (spec, arg) in variant.fields.iter().zip(args.iter()) {
        rendered.push(emit_field(schema, spec, arg)?);
    }
    Ok(format!("{category}::{head}({})", rendered.join(", ")))
}

fn emit_field(schema: &Schema, spec: &FieldSpec, node: &DebugNode) -> Result<String, EmitError> {
    match spec {
        FieldSpec::Opt(inner) => match node {
            DebugNode::Ident(name) if name == "None" => Ok("None".to_string()),
            DebugNode::Call { head, args } if head == "Some" && args.len() == 1 => {
                Ok(format!("Some({})", emit_field(schema, inner, &args[0])?))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Some(..)` or `None`".to_string(),
                found: describe(other),
            }),
        },

        // A nested category field is `Arc<C>` in the generated enum, and `Debug` erased the
        // wrapper. `Arc::new` is restored here — it is objection 1 of five.
        FieldSpec::Cat(cat) => {
            Ok(format!("std::sync::Arc::new({})", emit_category(schema, cat, node)?))
        },

        FieldSpec::Var => emit_ordvar(node),

        FieldSpec::Native(ty) => emit_native(ty, node),

        FieldSpec::Coll { kind, elem } => emit_collection(schema, kind, elem, node, false),
        FieldSpec::CollLit { kind, elem } => emit_collection(schema, kind, elem, node, true),

        FieldSpec::Scope1 { body, .. } => match node {
            DebugNode::Struct { head, fields } if head == "Scope" => {
                let pattern = field_named(fields, "pattern")?;
                let body_node = field_named(fields, "body")?;
                Ok(format!(
                    "mettail_runtime::Scope::from_parts_unsafe({}, std::sync::Arc::new({}))",
                    emit_binder(pattern)?,
                    emit_category(schema, body, body_node)?
                ))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Scope { pattern: .., body: .. }`".to_string(),
                found: describe(other),
            }),
        },

        FieldSpec::ScopeN { body, .. } => match node {
            DebugNode::Struct { head, fields } if head == "Scope" => {
                let pattern = field_named(fields, "pattern")?;
                let body_node = field_named(fields, "body")?;
                let binders = match pattern {
                    DebugNode::List(items) => items
                        .iter()
                        .map(emit_binder)
                        .collect::<Result<Vec<_>, _>>()?,
                    other => {
                        return Err(EmitError::ShapeMismatch {
                            expected: "a `[Binder(..), ..]` multi-binder pattern".to_string(),
                            found: describe(other),
                        })
                    },
                };
                Ok(format!(
                    "mettail_runtime::Scope::from_parts_unsafe(vec![{}], std::sync::Arc::new({}))",
                    binders.join(", "),
                    emit_category(schema, body, body_node)?
                ))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`Scope { pattern: [..], body: .. }`".to_string(),
                found: describe(other),
            }),
        },

        FieldSpec::OpaqueToken => match node {
            DebugNode::Str(s) => Ok(format!("std::string::String::from({})", quote_rust(s))),
            other => Err(EmitError::ShapeMismatch {
                expected: "a token-text string literal".to_string(),
                found: describe(other),
            }),
        },

        FieldSpec::Pred => Err(EmitError::UnsupportedFieldType {
            descriptor: "pred (BehavioralPred)".to_string(),
        }),
        FieldSpec::OpaqueGuest => Err(EmitError::UnsupportedFieldType {
            descriptor: "opaque:guest (Arc<FltNode>)".to_string(),
        }),
    }
}

/// `OrdVar(Free(FreeVar { unique_id: UniqueId(n), pretty_name: Some("x") }))`.
///
/// `unique_id` is DELIBERATELY dropped: it is drawn from a process-global counter and is
/// unwritable, and it is also redundant — `FreeVar` equality is by `unique_id` alone, and
/// the generated strategies mint every variable through the thread-local name cache, so the
/// NAME determines the identity. See the module docs.
fn emit_ordvar(node: &DebugNode) -> Result<String, EmitError> {
    let inner = match node {
        DebugNode::Call { head, args } if head == "OrdVar" && args.len() == 1 => &args[0],
        other => {
            return Err(EmitError::ShapeMismatch {
                expected: "`OrdVar(..)`".to_string(),
                found: describe(other),
            })
        },
    };
    match inner {
        DebugNode::Call { head, args } if head == "Free" && args.len() == 1 => {
            let name = free_var_name(&args[0])?;
            Ok(format!(
                "mettail_runtime::OrdVar(mettail_runtime::Var::Free(mettail_runtime::get_or_create_var({})))",
                quote_rust(&name)
            ))
        },
        other => Err(EmitError::ShapeMismatch {
            expected: "`Free(FreeVar { .. })` — a bound variable has no name to rebuild from"
                .to_string(),
            found: describe(other),
        }),
    }
}

fn emit_binder(node: &DebugNode) -> Result<String, EmitError> {
    match node {
        DebugNode::Call { head, args } if head == "Binder" && args.len() == 1 => {
            let name = free_var_name(&args[0])?;
            Ok(format!(
                "mettail_runtime::Binder(mettail_runtime::get_or_create_var({}))",
                quote_rust(&name)
            ))
        },
        other => Err(EmitError::ShapeMismatch {
            expected: "`Binder(FreeVar { .. })`".to_string(),
            found: describe(other),
        }),
    }
}

fn free_var_name(node: &DebugNode) -> Result<String, EmitError> {
    match node {
        DebugNode::Struct { head, fields } if head == "FreeVar" => {
            match field_named(fields, "pretty_name")? {
                DebugNode::Call { head, args } if head == "Some" && args.len() == 1 => {
                    match &args[0] {
                        DebugNode::Str(s) => Ok(s.clone()),
                        other => Err(EmitError::ShapeMismatch {
                            expected: "a string `pretty_name`".to_string(),
                            found: describe(other),
                        }),
                    }
                },
                other => Err(EmitError::ShapeMismatch {
                    expected: "`pretty_name: Some(\"..\")` — an anonymous FreeVar carries no \
                               name, and its identity is a process-global counter that cannot \
                               be rebuilt"
                        .to_string(),
                    found: describe(other),
                }),
            }
        },
        other => Err(EmitError::ShapeMismatch {
            expected: "`FreeVar { unique_id: .., pretty_name: .. }`".to_string(),
            found: describe(other),
        }),
    }
}

/// A collection field. `is_literal` selects the native LITERAL wrapper type
/// (`HashSetLit`, `HashMapLit`, `PathMapLit`) over the plain container.
fn emit_collection(
    schema: &Schema,
    kind: &str,
    elem: &str,
    node: &DebugNode,
    is_literal: bool,
) -> Result<String, EmitError> {
    match kind {
        "HashBag" => match node {
            // `HashBag`'s `Debug` is `HashBag { counts: {elem: n, ..}, total_count: t }`. The
            // multiplicities are expanded back into a flat iterator, because `from_iter`
            // counts repeats — reconstructing `total_count` by hand would be a second source
            // of truth for a number the bag derives itself.
            DebugNode::Struct { head, fields } if head == "HashBag" => {
                let counts = field_named(fields, "counts")?;
                let entries = match counts {
                    DebugNode::Map(entries) => entries.as_slice(),
                    DebugNode::Set(items) if items.is_empty() => &[],
                    other => {
                        return Err(EmitError::ShapeMismatch {
                            expected: "`counts: {elem: n, ..}`".to_string(),
                            found: describe(other),
                        })
                    },
                };
                let mut parts: Vec<String> = Vec::with_capacity(entries.len());
                for (key, count) in entries {
                    let repeats = match count {
                        DebugNode::Int(n) if *n >= 0 => *n as usize,
                        other => {
                            return Err(EmitError::ShapeMismatch {
                                expected: "a non-negative multiplicity".to_string(),
                                found: describe(other),
                            })
                        },
                    };
                    // ⚠ Elements are BARE, not `Arc`-wrapped: the generated enums declare
                    // `PPar(HashBag<Proc>)`, not `HashBag<Arc<Proc>>`. Only a category FIELD
                    // is `Arc`-wrapped. Getting this backwards produces source that reads
                    // plausibly and does not compile.
                    let rendered = emit_category(schema, elem, key)?;
                    for _ in 0..repeats {
                        parts.push(rendered.clone());
                    }
                }
                Ok(format!("mettail_runtime::HashBag::from_iter(vec![{}])", parts.join(", ")))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "`HashBag { counts: .., total_count: .. }`".to_string(),
                found: describe(other),
            }),
        },

        "Vec" => match node {
            DebugNode::List(items) => {
                let mut parts = Vec::with_capacity(items.len());
                for item in items {
                    parts.push(emit_category(schema, elem, item)?);
                }
                Ok(format!("vec![{}]", parts.join(", ")))
            },
            other => Err(EmitError::ShapeMismatch {
                expected: "a `[..]` list".to_string(),
                found: describe(other),
            }),
        },

        // ⚠ `HashSetLit`, `HashMapLit` and `PathMapLit` are NEWTYPES with a DERIVED `Debug`,
        // so their text is `HashSetLit({..})` — the type name wrapping the inner container.
        // `HashBag` above is different: it has a hand-written `Debug` that prints its FIELDS
        // (`HashBag { counts: .., total_count: .. }`) and no wrapping call. The two shapes
        // are not interchangeable, and a reader that assumed one would reject the other with
        // a message about the wrong thing.
        "HashSet" => {
            let inner = unwrap_lit_container(node, "HashSetLit")?;
            let items = match inner {
                DebugNode::Set(items) => items.as_slice(),
                // An empty brace group is reported as an empty map by the parser, because
                // `{}` is genuinely ambiguous between the two.
                DebugNode::Map(entries) if entries.is_empty() => &[],
                DebugNode::List(items) => items.as_slice(),
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "a `{..}` set".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut parts = Vec::with_capacity(items.len());
            for item in items {
                parts.push(emit_category(schema, elem, item)?);
            }
            let ctor = if is_literal {
                "mettail_runtime::HashSetLit::from_iter"
            } else {
                "std::collections::HashSet::from_iter"
            };
            Ok(format!("{ctor}(vec![{}])", parts.join(", ")))
        },

        "HashMap" | "PathMap" => {
            let wrapper = if kind == "HashMap" {
                "HashMapLit"
            } else {
                "PathMapLit"
            };
            let inner = unwrap_lit_container(node, wrapper)?;
            let entries = match inner {
                DebugNode::Map(entries) => entries.as_slice(),
                DebugNode::Set(items) if items.is_empty() => &[],
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "a `{k: v, ..}` map".to_string(),
                        found: describe(other),
                    })
                },
            };
            let mut parts = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                parts.push(format!(
                    "({}, {})",
                    emit_category(schema, elem, key)?,
                    emit_category(schema, elem, value)?
                ));
            }
            let ctor = if kind == "HashMap" {
                "mettail_runtime::HashMapLit::from_iter"
            } else {
                "mettail_runtime::PathMapLit::from_iter"
            };
            Ok(format!("{ctor}(vec![{}])", parts.join(", ")))
        },

        other => Err(EmitError::UnsupportedFieldType {
            descriptor: format!("collection kind `{other}`"),
        }),
    }
}

/// A bare native payload.
///
/// The DECLARED type is what the schema records, and it is not always the EMITTED field
/// type: `![str] as Str` is declared `str` and emitted `std::string::String`. That mapping
/// lives here, where the emitter knows it is writing an owned value into a constructor
/// position.
fn emit_native(declared: &str, node: &DebugNode) -> Result<String, EmitError> {
    let last = declared.rsplit("::").next().unwrap_or(declared);
    match last {
        "str" | "String" => match node {
            DebugNode::Str(s) => Ok(format!("std::string::String::from({})", quote_rust(s))),
            other => Err(EmitError::ShapeMismatch {
                expected: "a string literal".to_string(),
                found: describe(other),
            }),
        },
        "bool" => match node {
            DebugNode::Ident(name) if name == "true" || name == "false" => Ok(name.clone()),
            other => Err(EmitError::ShapeMismatch {
                expected: "`true` or `false`".to_string(),
                found: describe(other),
            }),
        },
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64"
        | "u128" | "usize" => match node {
            DebugNode::Int(n) => Ok(format!("{n}{last}")),
            other => Err(EmitError::ShapeMismatch {
                expected: format!("an `{last}` literal"),
                found: describe(other),
            }),
        },
        "f32" | "f64" => match node {
            DebugNode::Float(x) => Ok(format!("{x}{last}")),
            DebugNode::Int(n) => Ok(format!("{n}.0{last}")),
            other => Err(EmitError::ShapeMismatch {
                expected: format!("an `{last}` literal"),
                found: describe(other),
            }),
        },
        // `CanonicalBigInt`'s `Debug` DELEGATES to the inner `BigInt`, so the text is a bare
        // integer with no wrapper to peel. Only `From<BigInt>` exists — there is no
        // `From<i64>` — so the literal is widened explicitly.
        "CanonicalBigInt" => match node {
            DebugNode::Int(n) => Ok(format!(
                "mettail_runtime::CanonicalBigInt::from(num_bigint::BigInt::from({n}i64))"
            )),
            other => Err(EmitError::ShapeMismatch {
                expected: "a big-integer literal".to_string(),
                found: describe(other),
            }),
        },
        // `Ratio`'s derived `Debug` is `Ratio { numer: a, denom: b }` and its fields are
        // private, so `Ratio::new` is the only way in. `CanonicalFixedPoint` prints `a/b`,
        // which parses as DIVISION in Rust — objection 5 of five.
        // `CanonicalBigRat`'s `Debug` delegates to `Ratio<BigInt>`, whose DERIVED `Debug` is
        // `Ratio { numer: a, denom: b }`. Its fields are private, so `Ratio::new` is the only
        // way in — objection 4 of five, verbatim.
        "CanonicalBigRat" | "BigRational" | "Ratio" => match node {
            DebugNode::Struct { head, fields } if head == "Ratio" => {
                let numer = int_field(fields, "numer")?;
                let denom = int_field(fields, "denom")?;
                Ok(format!(
                    "mettail_runtime::CanonicalBigRat::from(num_rational::BigRational::new(num_bigint::BigInt::from({numer}i64), num_bigint::BigInt::from({denom}i64)))"
                ))
            },
            DebugNode::Ratio(n, d) => Ok(format!(
                "mettail_runtime::CanonicalBigRat::from(num_rational::BigRational::new(num_bigint::BigInt::from({n}i64), num_bigint::BigInt::from({d}i64)))"
            )),
            other => Err(EmitError::ShapeMismatch {
                expected: "`Ratio { numer: .., denom: .. }` or `a/b`".to_string(),
                found: describe(other),
            }),
        },
        // `CanonicalFixedPoint`'s hand-written `Debug` is
        // `write!(f, "Fixed({}/{})", unscaled, 10^places)`, so the DENOMINATOR is a power of
        // ten and the constructor wants the EXPONENT, not the denominator itself. `a/b`
        // would parse as division in Rust — objection 5 of five.
        "CanonicalFixedPoint" => {
            let (unscaled, denom) = match node {
                DebugNode::Call { head, args } if head == "Fixed" && args.len() == 1 => {
                    match &args[0] {
                        DebugNode::Ratio(n, d) => (*n, *d),
                        DebugNode::Int(n) => (*n, 1),
                        other => {
                            return Err(EmitError::ShapeMismatch {
                                expected: "`Fixed(a/b)`".to_string(),
                                found: describe(other),
                            })
                        },
                    }
                },
                DebugNode::Ratio(n, d) => (*n, *d),
                other => {
                    return Err(EmitError::ShapeMismatch {
                        expected: "`Fixed(a/b)`".to_string(),
                        found: describe(other),
                    })
                },
            };
            let places = power_of_ten_exponent(denom).ok_or_else(|| EmitError::ShapeMismatch {
                expected: "a `Fixed(a/10^p)` denominator that is a power of ten".to_string(),
                found: format!("the denominator {denom}"),
            })?;
            Ok(format!(
                "mettail_runtime::CanonicalFixedPoint::new(num_bigint::BigInt::from({unscaled}i64), {places}u32)"
            ))
        },
        other => Err(EmitError::UnsupportedFieldType {
            descriptor: format!("native type `{other}` (declared `{declared}`)"),
        }),
    }
}

/// Strip the newtype wrapper a `*Lit` container's DERIVED `Debug` prints.
///
/// `HashMapLit<K, V>(IndexMap<K, V, _>)` derives `Debug`, so its text is
/// `HashMapLit({k: v})`. The bare inner container is also accepted, because the same field
/// type appears in positions where the wrapper has already been consumed — for a
/// `CollectionLiteral` variant, `emit_category` peels `MapLit(..)` and hands on what is
/// inside, which is the wrapper; for a plain collection FIELD the node is the wrapper
/// itself. Accepting both keeps one code path for the two.
fn unwrap_lit_container<'a>(
    node: &'a DebugNode,
    _wrapper: &str,
) -> Result<&'a DebugNode, EmitError> {
    // Peeling is a LOOP, not a single step, because the wrappers NEST:
    // `PathMapLit<K, V>(HashMapLit<K, V>)` is a newtype over a newtype and both derive
    // `Debug`, so a Rholang path map prints `PathMapLit(HashMapLit({}))`. Measured on
    // corpus entries 0 and 22 of `gen_rholang_prop`, which are the only two that reach two
    // levels — a single-step peel left them looking like a shape mismatch rather than a
    // wrapper still in the way.
    //
    // Only these three names are peeled, and they are runtime CONTAINER types rather than
    // grammar constructors, so peeling cannot swallow a language variant: a
    // collection-literal variant is spelled `MapLit`/`SetLit`/`PathmapLit` and is consumed
    // by `emit_category` before the container is ever reached.
    const CONTAINER_WRAPPERS: &[&str] = &["PathMapLit", "HashMapLit", "HashSetLit"];
    let mut current = node;
    loop {
        match current {
            DebugNode::Call { head, args }
                if args.len() == 1 && CONTAINER_WRAPPERS.contains(&head.as_str()) =>
            {
                current = &args[0];
            },
            other => return Ok(other),
        }
    }
}

/// `p` such that `10^p == value`, or `None` if `value` is not a power of ten.
fn power_of_ten_exponent(value: i128) -> Option<u32> {
    if value <= 0 {
        return None;
    }
    let mut remaining = value;
    let mut exponent = 0u32;
    while remaining % 10 == 0 {
        remaining /= 10;
        exponent += 1;
    }
    (remaining == 1).then_some(exponent)
}

fn field_named<'a>(
    fields: &'a [(String, DebugNode)],
    want: &str,
) -> Result<&'a DebugNode, EmitError> {
    fields
        .iter()
        .find(|(name, _)| name == want)
        .map(|(_, value)| value)
        .ok_or_else(|| EmitError::ShapeMismatch {
            expected: format!("a `{want}` field"),
            found: format!(
                "fields {:?}",
                fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>()
            ),
        })
}

fn int_field(fields: &[(String, DebugNode)], want: &str) -> Result<i128, EmitError> {
    match field_named(fields, want)? {
        DebugNode::Int(n) => Ok(*n),
        other => Err(EmitError::ShapeMismatch {
            expected: format!("an integer `{want}`"),
            found: describe(other),
        }),
    }
}

/// Render a Rust string literal for `s`.
///
/// Escaping is explicit rather than `{:?}` so the result is known to be a `&'static str`
/// literal and not, say, a `Debug` rendering that happens to look like one.
fn quote_rust(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn describe(node: &DebugNode) -> String {
    match node {
        DebugNode::Call { head, args } => format!("`{head}(..)` with {} argument(s)", args.len()),
        DebugNode::Struct { head, .. } => format!("`{head} {{ .. }}`"),
        DebugNode::Ident(name) => format!("the bare identifier `{name}`"),
        DebugNode::Str(_) => "a string literal".to_string(),
        DebugNode::Int(n) => format!("the integer {n}"),
        DebugNode::Float(x) => format!("the float {x}"),
        DebugNode::Ratio(n, d) => format!("the ratio {n}/{d}"),
        DebugNode::List(items) => format!("a `[..]` list of {}", items.len()),
        DebugNode::Set(items) => format!("a `{{..}}` set of {}", items.len()),
        DebugNode::Map(entries) => format!("a `{{k: v}}` map of {}", entries.len()),
        DebugNode::Tuple(items) => format!("a `(..)` tuple of {}", items.len()),
        DebugNode::Named { name, .. } => format!("the named argument `{name}=..`"),
        DebugNode::Range(a, b) => format!("the range {a}..{b}"),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Debug normalisation — the promoted test's oracle
// ══════════════════════════════════════════════════════════════════════════════

/// Replace every `UniqueId(<digits>)` with `UniqueId(_)`.
///
/// This is the ONE difference a faithful reconstruction cannot avoid, and naming it
/// precisely is what keeps the promoted tests' second assertion exact everywhere else.
/// `moniker`'s `UniqueId` is minted from a process-global `AtomicUsize`, so its value
/// depends on how many variables the process happened to create first — it is not a
/// property of the term. `FreeVar` equality ignores everything else, so nothing about the
/// term's identity is being waived here.
///
/// Implemented without `regex` so `testkit` gains no dependency for four lines of scanning.
pub fn normalize_unique_ids(text: &str) -> String {
    const NEEDLE: &str = "UniqueId(";
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(idx) = rest.find(NEEDLE) {
        out.push_str(&rest[..idx]);
        let after = &rest[idx + NEEDLE.len()..];
        let digits = after
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(after.len());
        if digits > 0 && after[digits..].starts_with(')') {
            out.push_str("UniqueId(_)");
            rest = &after[digits + 1..];
        } else {
            // Not the shape we mean; copy the needle through verbatim rather than guessing.
            out.push_str(NEEDLE);
            rest = after;
        }
    }
    out.push_str(rest);
    out
}

// ══════════════════════════════════════════════════════════════════════════════
// The round-trip printer — the parser's own anti-vacuity proof
// ══════════════════════════════════════════════════════════════════════════════

/// Re-print a [`DebugNode`] in the exact form `Debug` would have written it.
///
/// # Why this exists
///
/// A parser that silently drops what it does not understand looks exactly like a parser
/// that understood everything. This printer closes that hole: if
/// `render_debug(parse_debug_value(t)) == t` for a text `t`, then the parse retained every
/// byte of `t` — no field skipped, no argument swallowed, no numeric precision lost. The
/// test suite applies it to every one of the recorded counterexamples in the repository's
/// corpora, which is an unbounded-in-principle and 100-strong-in-practice control
/// population that nobody wrote for this purpose.
///
/// It is NOT used by the emitter. Its only job is to be an oracle.
pub fn render_debug(node: &DebugNode) -> String {
    let mut out = String::new();
    render_into(node, &mut out);
    out
}

fn render_into(node: &DebugNode, out: &mut String) {
    match node {
        DebugNode::Call { head, args } => {
            out.push_str(head);
            out.push('(');
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_into(arg, out);
            }
            out.push(')');
        },
        DebugNode::Struct { head, fields } => {
            out.push_str(head);
            out.push_str(" { ");
            for (i, (name, value)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(name);
                out.push_str(": ");
                render_into(value, out);
            }
            out.push_str(" }");
        },
        DebugNode::Ident(name) => out.push_str(name),
        DebugNode::Str(s) => out.push_str(&quote_rust(s)),
        DebugNode::Int(n) => out.push_str(&n.to_string()),
        // `{:?}`, not `{}`. `Display` for `f64` prints `0` for zero while `Debug` prints
        // `0.0`, and `Debug` is what wrote the text being round-tripped — measured on
        // `prattail/proptest-regressions/automata/lex_weight.txt`, whose
        // `TropicalWeight(0.0)` re-printed as `TropicalWeight(0)` until this was fixed.
        DebugNode::Float(x) => out.push_str(&format!("{x:?}")),
        DebugNode::Ratio(n, d) => {
            out.push_str(&n.to_string());
            out.push('/');
            out.push_str(&d.to_string());
        },
        DebugNode::List(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_into(item, out);
            }
            out.push(']');
        },
        DebugNode::Set(items) => {
            out.push('{');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_into(item, out);
            }
            out.push('}');
        },
        DebugNode::Map(entries) => {
            out.push('{');
            for (i, (k, v)) in entries.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_into(k, out);
                out.push_str(": ");
                render_into(v, out);
            }
            out.push('}');
        },
        DebugNode::Tuple(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_into(item, out);
            }
            out.push(')');
        },
        DebugNode::Named { name, value } => {
            out.push_str(name);
            out.push('=');
            render_into(value, out);
        },
        DebugNode::Range(a, b) => {
            out.push_str(&a.to_string());
            out.push_str("..");
            out.push_str(&b.to_string());
        },
    }
}

/// Re-print a whole `# shrinks to` payload, bindings included.
pub fn render_bindings(bindings: &[Binding]) -> String {
    let mut out = String::new();
    for (i, binding) in bindings.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&binding.name);
        out.push_str(" = ");
        render_into(&binding.value, &mut out);
    }
    out
}

/// Canonicalise a `Debug` text so it is a function of the TERM and nothing else.
///
/// # The defect this exists to remove
///
/// `HashBag`, `HashSetLit` and `HashMapLit` print their entries in HASH ORDER. The hash of a
/// term containing a `FreeVar` depends on that variable's `unique_id`, which is drawn from a
/// process-global counter — so the SAME term prints its bag entries in different orders
/// depending on how many variables the process happened to create first.
///
/// Measured: `languages/tests/promoted_corpus_ambient.rs` has a term whose `PPar` bag holds
/// a `PAmb` and a `PIn`. It printed them in the recorded order on its own, and in the
/// opposite order once a mutation to an EARLIER test in the same binary shifted the counter.
/// A promoted test asserting raw text equality would therefore be a flake that fires on
/// unrelated edits — which is worse than no test, because it trains a reader to re-run
/// rather than to look.
///
/// # What is quotiented out, and what is not
///
/// Exactly two things: `UniqueId(n)` (see [`normalize_unique_ids`]) and the ORDER of
/// entries inside a brace group. Both are properties of the process, not of the term:
/// `HashBag` is a multiset and its `PartialEq` does not depend on iteration order. Every
/// other byte — every constructor, every field name, every multiplicity, every literal —
/// still has to match exactly, so the anti-vacuity property is untouched.
///
/// Sorting is by the entries' own rendered text, which is total and deterministic.
pub fn canonicalize_debug(text: &str) -> String {
    let normalized = normalize_unique_ids(text);
    match parse_debug_value(&normalized) {
        Ok(node) => render_debug(&sort_brace_groups(node)),
        // Not a parseable `Debug` value: return the normalised text unchanged rather than
        // guessing. A promoted test comparing two unparseable texts still compares them.
        Err(_) => normalized,
    }
}

/// [`canonicalize_debug`] over a whole `name = value, …` payload.
pub fn canonicalize_shrinks_to(text: &str) -> String {
    let normalized = normalize_unique_ids(text);
    match parse_shrinks_to(&normalized) {
        Ok(bindings) => {
            let sorted: Vec<Binding> = bindings
                .into_iter()
                .map(|b| Binding {
                    name: b.name,
                    value: sort_brace_groups(b.value),
                })
                .collect();
            render_bindings(&sorted)
        },
        Err(_) => normalized,
    }
}

fn sort_brace_groups(node: DebugNode) -> DebugNode {
    match node {
        DebugNode::Call { head, args } => DebugNode::Call {
            head,
            args: args.into_iter().map(sort_brace_groups).collect(),
        },
        DebugNode::Struct { head, fields } => DebugNode::Struct {
            head,
            fields: fields
                .into_iter()
                .map(|(name, value)| (name, sort_brace_groups(value)))
                .collect(),
        },
        // A LIST is ordered by construction (`Vec`), so its order is part of the term and is
        // left alone. Only brace groups — the hash containers — are sorted.
        DebugNode::List(items) => {
            DebugNode::List(items.into_iter().map(sort_brace_groups).collect())
        },
        DebugNode::Tuple(items) => {
            DebugNode::Tuple(items.into_iter().map(sort_brace_groups).collect())
        },
        DebugNode::Set(items) => {
            let mut sorted: Vec<DebugNode> = items.into_iter().map(sort_brace_groups).collect();
            sorted.sort_by_key(render_debug);
            DebugNode::Set(sorted)
        },
        DebugNode::Map(entries) => {
            let mut sorted: Vec<(DebugNode, DebugNode)> = entries
                .into_iter()
                .map(|(k, v)| (sort_brace_groups(k), sort_brace_groups(v)))
                .collect();
            sorted.sort_by_key(|(k, v)| (render_debug(k), render_debug(v)));
            DebugNode::Map(sorted)
        },
        DebugNode::Named { name, value } => DebugNode::Named {
            name,
            value: Box::new(sort_brace_groups(*value)),
        },
        leaf => leaf,
    }
}
