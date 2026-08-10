# Experiment 174 failed capture — strict-shell local initialization

This directory is an immutable failed attempt, not a measurement result. The
release build and environment capture completed, but the runner exited before
the first benchmark cell and therefore produced no `driver/*.jsonl` files.

Observed failure:

```text
docs/benchmarks/data/sa-vs-naive/post-d-e5-r3.sh: line 79: matcher: unbound variable
```

The cause was Bash expansion order in a single declaration: the derived output
path referenced `matcher` while the same `local` command was still assigning
it. `set -u` correctly rejected that reference. The repair separates argument
assignment from derived-path construction and is tracked by pgmcp work item
`split-strict-shell-benchmark-cell-locals-before-path-interpolation-9bb6f2`.

This directory will not be overwritten or reused. A repaired execution must
use a distinct run identifier so the failure remains visible and no successful
cell can be selected over a failed attempt.
