# CESK Store Architecture

## Overview

The CESK store provides address-based indirection for the PraTTaIL evaluation engine, extending the CEK machine with explicit mutable state.

## Component Inventory

```
┌─────────────────────────────────────────────────────────────────────┐
│                        CESK Store Layer                              │
│                                                                     │
│  cesk_store.rs          gc.rs              abstract_cesk.rs          │
│  ┌──────────────┐      ┌──────────────┐   ┌──────────────────────┐  │
│  │ StoreAddr     │      │ GcStrategy    │   │ AbstractStore        │  │
│  │ StoreValue    │      │ RefCountGc    │   │ AbstractValue        │  │
│  │ LocalCeskStore│◄────▶│ MarkSweepGc   │   │ abstract_gc()        │  │
│  │ GlobalCeskStore│     │ GcMonitor     │   │ DyckStateGraph       │  │
│  │ PersistentLocal│     │ GcThread      │   │ EvalControlState     │  │
│  │ AllocStrategy │      │ BackpressureTier  │ EvalStackSymbol      │  │
│  │ StoreResolver │      │ live_locations│   │ is_reachable()       │  │
│  └──────────────┘      └──────────────┘   └──────────────────────┘  │
│         │                     │                     │                │
│         ▼                     ▼                     ▼                │
│  ┌──────────────────────────────────────────────────────────────┐    │
│  │                    Evaluation Layer                            │    │
│  │  cek_eval.rs: CekEvaluator (standalone, explicit CEK tools)   │    │
│  │  green_thread.rs: GreenThread (concurrent, M:N scheduler)     │    │
│  │  coordinator.rs: GC snapshot at ParkIdle                      │    │
│  │  scheduler.rs: Backpressure-aware quantum dispatch             │    │
│  │  channel.rs: ChannelHandle gc_refcount lifecycle               │    │
│  └──────────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────────┘
```

## Data Flow

1. **Evaluation request** → `CekEvaluator::new(term)` or `GreenThread::with_control(id, cat, term)`
2. **Bind** → `alloc_with(StoreValue::Simple(v))` → `env[x] = StoreAddr::Local(id)`
3. **Lookup** → `env[x] → StoreAddr → store.get(id) → StoreValue`
4. **Mutate** → `store.set(env[x].id(), new_val)` — env unchanged, store cell overwritten
5. **GC** → `RefCountGc::dec_ref()` or `MarkSweepGc::collect()` at quantum boundaries
6. **Fork** → `PersistentLocalStore::fork()` — O(1) structural sharing clone

## Feature Gates

| Feature | Components |
|---------|-----------|
| `cek-runtime` | StoreAddr, StoreValue, LocalCeskStore, GcStrategy, RefCountGc, MarkSweepGc, CekEvaluator integration, abstract_cesk |
| `green-threads` | GlobalCeskStore, PersistentLocalStore, ChannelRef, GcThread, GcMonitor, BackpressureTier, channel lifecycle |

## Integration Points

- **Explicit CEK tools/tests** (`prattail/src/cek_eval.rs`): Use `CekEvaluator`
  with optional persistent environments across CEK sessions.
- **Generated code** (`macros/src/gen/runtime/language.rs`): Emits
  `decompose_into_cek` hooks for explicit CEK/debug consumers.
- **Green threads** (`prattail/src/green_thread.rs`): Two-tier store with O(1) fork
- **Ascent** (CESK-8): Store-resident relations for incremental fixpoint
- **Pipeline** (`prattail/src/pipeline.rs`): E-graph export after saturation (CESK-11)

The production REPL `exec` path is runtime-backend selected and stores a
`RuntimeBackendReport`. CESK does not sit between parsed terms and the selected
Dovetail or Rho runtime backend.
