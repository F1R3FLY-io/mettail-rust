# MeTTaIL: Language framework in Rust

---

This package enables you to specify a formal language in a macro, which generates all code needed to make and run its terms.

For example, the rho-calculus is the concurrent language of [f1r3fly](https://github.com/F1R3FLY-io).
```rust
language! {
    name: RhoCalc,

    types {
        Proc
        Name
    },

    terms {
        PZero . |- "0" : Proc;

        PDrop . n:Name |- "*" "(" n ")" : Proc ;

        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
        
        PInput . n:Name, ^x.p:[Name -> Proc] |- n "?" x "." "{" p "}" : Proc ;

        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

        NQuote . p:Proc |- "@" "(" p ")" : Name ;
    },

    equations {
        (NQuote (PDrop N)) = N ;
    },

    rewrites {
        (PPar {(PInput n ^x.p), (POutput n q), ...rest})
            ~> (PPar {(subst ^x.p (NQuote q)), ...rest});

        (PDrop (NQuote P)) ~> P;

        if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    },
}
```

From a language definition, it generates:
- **AST enums** - Type-safe data structures with first-class binding
- **Grammars** - Parser generation with bidirectional display ([lalrpop])
- **Substitution methods** - Capture-avoiding, cross-category substitution ([moniker])
- **Datalog rewrite engine** - Order-independent pattern matching with indexed joins ([ascent])
- **Higher-order lambdas** - Auto-generated `LamX`/`ApplyX`, with type inference
- **Environments** - Named term definitions with eager substitution

---

## REPL Example

The interactive REPL supports term exploration, step-by-step rewriting, and higher-order metaprogramming:

```
$ cargo run
mettail> lang rhocalc
Loading theory: rhocalc
  ✓ 8 definitions from repl/src/examples/rhocalc.txt

rhocalc> env
Environment:
  dup = ^l.{l?x.{{*(x) | l!(*(x))}}}
  rep = ^n.{^a.{^cont.{{$name(dup, n) | n!(a?y.{{$name(cont, y) | $name(dup, n)}})}}}}
  id = ^z.{*(z)}
  fwd = ^src.{^dst.{src?x.{dst!(*(x))}}}

rhocalc> exec { server!(request) | $name($name($name(rep, server), a?y.{$name(id, y)}), id) }
Parsing... ✓
Substituting environment... ✓
Running Ascent... Time taken: 45.2ms
Done!

Computed:
  - 40 terms
  - 33 rewrites
  - 16 normal forms

rhocalc> apply 0
Applied rewrite →
  { $name(id, @(request)) | server?y.{{$name(id, y) | $name(dup, server)}} }

rhocalc> apply 0
Applied rewrite →
  { server?y.{{$name(id, y) | $name(dup, server)}} | *(@(request)) }

rhocalc> apply 0
Applied rewrite →
  { server?y.{{$name(id, y) | $name(dup, server)}} | request }
```

---

## 🙏 Credits

**Core Technologies:**
- [ascent](https://github.com/s-arash/ascent) - Datalog in Rust via macros
- [syn](https://github.com/dtolnay/syn) - Rust parsing
- [quote](https://github.com/dtolnay/quote) - Code generation
- [moniker](https://github.com/brendanzab/moniker) - Variable binding
- [LALRPOP](https://github.com/lalrpop/lalrpop) - Parser generator

**Inspiration:**
- [Rholang](https://rchain.coop/) - Motivating use case
- [K Framework](http://www.kframework.org/) - Rewriting semantics
- [BNFC](https://bnfc.digitalgrammars.com/) - Grammar-driven development
- [egg](https://egraphs-good.github.io/) - E-graph rewriting