# Resource Limiting for Rocq Proof Compilation

## Standard Build

```bash
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-ascent-optimizations
```

## Notes

- The top-level harness applies `MemoryMax=34359738368` (32 GiB),
  `MemorySwapMax=0`, `TasksMax=128`, and serial `make -j1`.
- Direct builds from this directory are refused by `../../capped.mk`; route
  every verification run through `check-capped`.
- SCCSplitting.v may take slightly longer due to induction on iteration count

## Clean Build

```bash
make -C formal/rocq/ascent_optimizations clean
```

## Verification

After successful build, all `.vo` files should be present in `theories/`:
- `Prelude.vo`
- `GraphReachability.vo`
- `TLSPoolEquiv.vo`
- `TotalOrder.vo`
- `DeadRulePruning.vo`
- `SCCSplitting.vo`
- `ConcreteInstantiations.vo`
