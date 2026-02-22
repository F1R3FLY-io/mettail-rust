# Resource Limiting for Rocq Proof Compilation

## Standard Build

```bash
cd formal/rocq/ascent_optimizations
coq_makefile -f _CoqProject -o CoqMakefile
systemd-run --user --scope -p MemoryMax=16G -p CPUQuota=400% make -f CoqMakefile
```

## Notes

- Memory: 16GB limit is generous for these proofs (they're lightweight)
- CPU: 400% = 4 cores, sufficient for parallel compilation
- SCCSplitting.v may take slightly longer due to induction on iteration count
- Serial compilation (`-j1`) is not needed here -- no memory-intensive modules

## Clean Build

```bash
make -f CoqMakefile clean
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
