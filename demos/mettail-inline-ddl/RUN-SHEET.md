# Inline MeTTaIL DDL in Rholang

This retained application demonstrates that a normal Rholang process can define
two MeTTaIL theories, install both parser images atomically, receive opaque
language handles, and recognize guest text through the handle selected by the
application. It is an end-to-end application, not a Rust grammar fixture.

## Run the complete gate

From the repository root, run exactly:

```console
./scripts/verify-inline-ddl-demo.sh
```

The command runs the committed application on the generated nouveau Rholang
parser and real reducer, the complete installed-language security/resource
tests, the system-process collision tests, the memory-capped Rocq authority
proofs, and the diff-integrity check. It prints the seven labelled application
results and the final installed-language count. Command output is retained beneath
`target/campaign-evidence/inline-ddl-demo/`.

## What the application does

The source is [`inline-ddl.rho`](inline-ddl.rho). `InlineDemo` declares the
independent categories `LeftExpr` and `RightExpr`, whose sole accepted texts are
respectively `left` and `right`. The installer returns one opaque handle for
each theory. Every parser request includes that handle and an explicit category;
neither a theory name, Uniform Resource Identifier (URI), alias, nor fingerprint
can substitute for the handle.

![The application is parsed once, its structural DDL is installed atomically, and only opaque handles can reach bounded parser ports](diagrams/inline-ddl-flow.svg)

The application publishes seven labelled observations on `@"OUT"`:

| Label | Required result | Meaning |
|---|---|---|
| `left-positive` | `accepted` | `left` belongs to `LeftExpr` under the Left handle |
| `right-positive` | `accepted` | `right` belongs to `RightExpr` under the Right handle |
| `left-negative` | `rejected` | unrelated text is not accepted by Left |
| `right-negative` | `rejected` | unrelated text is not accepted by Right |
| `left-crossfire` | `rejected` | Right's text cannot dispatch through Left's handle |
| `right-crossfire` | `rejected` | Left's text cannot dispatch through Right's handle |
| `atomic-failure` | `InvalidSurfaceDdl` | an invalid second theory rejects its entire two-theory batch |

The executable gate additionally inspects the installed-language table after
evaluation. Its cardinality must be exactly two. Therefore `ValidPrefix` from
the rejected batch did not become visible before `InvalidSuffix` failed.

## Security and resource contract

An `InstalledLanguageHandle` is an unforgeable, process-local capability. The
parse port checks its `Parse` right and sealed revocation epoch before parsing,
runs the parser under the intersection of host and grammar limits, and checks
the same authority again before publishing a result. A parse-only reply reports
one of `accepted`, `rejected`, `ambiguous`, or `exhausted`; it contains no
reflected abstract syntax tree, because reflection has a separate authority.

The application uses the registry-empty runtime and performs no filesystem
access. Future file loading remains behind an injected Rholang File I/O
capability and is outside this demonstration.
