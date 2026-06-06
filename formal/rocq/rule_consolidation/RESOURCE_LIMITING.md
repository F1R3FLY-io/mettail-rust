# Resource Limiting for Rocq Proof Compilation

## Standard Build

```bash
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-rule-consolidation
```

## Notes

- The top-level harness applies `MemoryMax=34359738368` (32 GiB),
  `MemorySwapMax=0`, `TasksMax=128`, and serial `make -j1`.
- Direct builds from this directory are refused by `../../capped.mk`; route
  every verification run through `check-capped`.
- These proofs are straightforward case analyses; they should compile in under 30 seconds

## Clean Build

```bash
make -C formal/rocq/rule_consolidation clean
```

## Verification

After successful build, all `.vo` files should be present in `theories/`:
- `Prelude.vo`
- `DisjointPatterns.vo`
- `RuleConsolidation.vo`
- `VariantIndexRebuild.vo`
- `AreaProofs.vo`
