use syn::Ident;

/// Syntax expression in patterns (can include meta-operations)
/// 
/// Example: `"for" "(" #zip(ns,xs).#map(|n,x| x "<-" n).#sep(",") ")" "{" p "}"`
#[derive(Debug, Clone)]
pub enum SyntaxExpr {
    /// Quoted literal: "for", "(", "<-"
    Literal(String),
    /// Parameter reference: n, x, p
    Param(Ident),
    /// Pattern operation: #sep, #zip, #map, #opt
    Op(PatternOp),
}

/// Pattern operation (compile-time meta-syntax)
/// 
/// These operations generate grammar rules and display code at compile time.
#[derive(Debug, Clone)]
pub enum PatternOp {
    /// #sep(coll, "sep") or coll.#sep("sep") or chain.#sep(",")
    /// Generates: `(<elem> "sep")* <elem>?` in grammar
    /// 
    /// For simple collections: source=None, collection=coll_name
    /// For chained operations: source=Some(Map/Zip), collection ignored
    Sep {
        collection: Ident,
        separator: String,
        /// Optional source for chained operations like #zip(...).#map(...).#sep(",")
        source: Option<Box<PatternOp>>,
    },
    /// #zip(a, b) - pairs corresponding elements
    /// Used with #map to generate paired patterns
    Zip {
        left: Ident,
        right: Ident,
    },
    /// #map(source, |x| expr) or source.#map(|x| expr)
    /// Transforms each element according to the pattern
    Map {
        source: Box<PatternOp>,  // Can be Zip result or collection ref
        params: Vec<Ident>,       // Closure parameters
        body: Vec<SyntaxExpr>,    // Pattern body
    },
    /// #opt(expr) - optional element
    /// Generates: `(expr)?` in grammar
    Opt {
        inner: Vec<SyntaxExpr>,
    },
    /// Variable reference (for chaining: coll.#sep)
    Var(Ident),
}