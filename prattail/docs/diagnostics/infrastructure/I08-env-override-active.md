# I08: env-override-active

**Severity:** Warning
**Category:** infrastructure
**Feature Gate:** None (always enabled)

## Description

Warns that the `PRATTAIL_AUTO_OPTIMIZE` environment variable is set, overriding
the cost-benefit analysis framework's automatic optimization gate
recommendations. When this variable is active, the pipeline skips the
compile-time cost-benefit evaluation (which considers grammar size, category
count, WFST complexity, and estimated runtime impact) and instead applies the
exact set of optimization gates specified in the environment variable.

The cost-benefit framework (`cost_benefit.rs`) normally evaluates each
optimization candidate against a profile of the grammar, enabling only those
optimizations whose estimated benefit exceeds their estimated cost. The
environment override bypasses this analysis entirely, which is useful for
debugging or benchmarking specific optimization combinations but may produce
suboptimal results in production.

```
  Cost-benefit gate selection flow:

  ┌─────────────────────────────────────┐
  │  PRATTAIL_AUTO_OPTIMIZE set?        │
  │  ├── yes -> parse env value         │
  │  │          └── use specified gates  │
  │  │              └── emit I08 warning │
  │  │                                   │
  │  └── no  -> run cost-benefit analysis│
  │             └── use recommended gates│
  └─────────────────────────────────────┘
```

## Trigger Conditions

All of the following must hold:

- The `PRATTAIL_AUTO_OPTIMIZE` environment variable is set (any value).
- The value parses successfully as a comma-separated list of optimization
  gate names.
- The pipeline invokes `OptimizationGates::from_env_or_recommendations()`.

One diagnostic is emitted per grammar.

## Example

### Environment

```bash
export PRATTAIL_AUTO_OPTIMIZE="BacktrackingElimination,HashConsing,RuleFusion"
```

### Output

```
warning[I08]: PRATTAIL_AUTO_OPTIMIZE override active -- cost-benefit recommendations bypassed
  = hint: unset PRATTAIL_AUTO_OPTIMIZE to use automatic cost-benefit analysis
```

## Resolution

1. **Unset the environment variable.** If the override was set for a previous
   debugging session and is no longer needed:

   ```bash
   unset PRATTAIL_AUTO_OPTIMIZE
   ```

   This restores the automatic cost-benefit analysis.

2. **Keep the override intentionally.** If you are benchmarking or debugging
   a specific optimization combination, the override is working as intended.
   The warning serves as a reminder that automatic tuning is disabled.

3. **Set `PRATTAIL_LINT_LEVEL=error`.** If you want to suppress this warning
   while keeping the override active, raise the lint level to `error` to hide
   warning-level diagnostics. This is not recommended for normal development.

## Hint Explanation

The hint **"unset PRATTAIL_AUTO_OPTIMIZE to use automatic cost-benefit
analysis"** is the simplest remediation: removing the environment variable
restores the default behavior where the pipeline's cost-benefit framework
evaluates each optimization gate against the grammar's profile and enables
only those that are estimated to be beneficial.

## Related Lints

- [I01](I01-transducer-cascade.md) -- Transducer cascade. The optimization
  gates affect which cascade passes run and in what configuration.
- [I17](I17-computed-goto-dispatch.md) -- Computed-goto dispatch. One of the
  optimization gates that can be controlled via `PRATTAIL_AUTO_OPTIMIZE`.
- [G35](../grammar/G35-ground-rewrite-short-circuit.md) -- Ground rewrite
  short-circuit. Another optimization gate controllable via the override.
