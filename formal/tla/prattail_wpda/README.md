# Prattail WPDA Finite Model

This model is a bounded counterexample harness for the active Prattail WPDA
runtime. It checks the separation between the full dispatch cache key and the
quotiented merge key alongside the Rocq and Lean mirrors.

The TLA+ state deliberately abstracts away semiring weights: none of the
bounded quotient or wrap-identity obligations inspect weights, and the Rust
walker plus Rocq runtime model cover the weight-carrying paths separately. The
Rocq model states the merge operation as a commutative monoid over the bounded
runtime abstraction; Rust tests and trait contracts cover the concrete
semiring implementations. Keeping weights out of this finite model halves the
cursor record product that Apalache must explore.

The control-state domain is also limited to states reached by these harness
scenarios: chain iteration, recovery delegation, unwinding, and completion.
The full Rocq and Lean mirrors keep the larger runtime control vocabulary;
`formal/rocq/prattail_wpda_runtime/theories/FiniteHarness.v` records the
embedding, excluded runtime controls, and one-step quotient/config
commutation, including the deduplicated set-level version of the quotient
step. This TLA+ model keeps only the states needed for bounded counterexample
search.

Run the green checks with:

```sh
make -C formal/tla/prattail_wpda check
```

This Makefile defaults `TMPDIR` to the repository-local `target/tmp` directory
for short-lived expected-counterexample logs.

`WrapSensitiveExpectedFail.cfg` is deliberately not part of this directory's
`check` target. The repository-level `make -C formal check` target runs it as
an expected-counterexample harness; it should produce a counterexample if wrap
identity is made directly observable while the cohort quotient still ignores
it.
