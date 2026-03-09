# I18: lint-cache-hit

**Severity:** Info
**Category:** infrastructure
**Feature Gate:** None (always enabled when lint caching is active)

## Description

Reports that the DB04 lint cache optimization detected a cache hit: the
grammar's structural hash matches the hash stored from the previous compilation,
so all lint passes are skipped. This avoids re-running the full lint suite
(approximately 60 passes) when the grammar has not changed between builds.

The lint cache works by computing a deterministic hash of the grammar's
`LintContext` (which includes category metadata, rule specifications, WFST
structure, decision trees, and all other lint inputs). This hash is stored in
`target/prattail/lint_cache.bin`. On subsequent builds, the hash is recomputed
and compared:

```
  Lint cache flow:

  ┌──────────────────────────────────┐
  │  Compute grammar hash            │
  │  Load cached hash from disk      │
  │                                  │
  │  cached_hash == grammar_hash?    │
  │  ├── yes -> emit I18 (cache hit) │
  │  │          return empty diags   │
  │  │                               │
  │  └── no  -> run all lint passes  │
  │             save new hash        │
  │             return diagnostics   │
  └──────────────────────────────────┘
```

When I18 fires, no other lint diagnostics are produced for that grammar. The
assumption is that if the grammar has not changed, the lint results have not
changed either. Deleting the cache file forces a full re-lint on the next build.

## Trigger Conditions

All of the following must hold:

- `run_lints_cached()` is called with `use_cache = true`.
- The `target/prattail/lint_cache.bin` file exists and is readable.
- The stored hash matches the computed grammar hash.

One diagnostic is emitted per grammar on cache hit.

## Example

### First build (cache miss)

```
note[G01] (ExprLang): left recursion detected in category `Expr`
warning[W01] (ExprLang): rule `Dead` is unreachable
... (60 lint passes run, diagnostics emitted, hash saved)
```

### Second build (cache hit, no grammar changes)

```
info[I18] (ExprLang): DB04 lint cache hit (hash=0x00a1b2c3d4e5f678): skipping 60 lint passes
  = hint: delete target/prattail/lint_cache.bin to force re-linting
```

## Resolution

No action required. I18 is an informational diagnostic confirming that the
lint cache is working correctly. The cache saves compilation time by avoiding
redundant lint analysis.

If stale lint results are suspected:

1. **Delete the cache file.** Remove `target/prattail/lint_cache.bin` to force
   a full re-lint on the next build:

   ```bash
   rm -f target/prattail/lint_cache.bin
   ```

2. **Run `cargo clean`.** A full clean removes all cached artifacts, including
   the lint cache.

3. **Disable caching.** If lint caching is causing issues, the pipeline can be
   configured to always run full lints by passing `use_cache = false` to
   `run_lints_cached()`.

## Hint Explanation

The hint **"delete target/prattail/lint_cache.bin to force re-linting"**
provides the simplest way to invalidate the cache. This is useful when:

- The lint implementation has changed (e.g., after upgrading the PraTTaIL
  version) but the grammar has not.
- A suspected hash collision produces incorrect cache behavior (extremely rare).
- Debugging requires seeing the full lint output even though the grammar has
  not changed.

## Related Lints

- [I01](I01-transducer-cascade.md) -- Transducer cascade. Another
  infrastructure diagnostic that reports pipeline progress.
- [I10](I10-ascent-file-write-failed.md) -- Ascent file write failed. Another
  file I/O diagnostic; similar infrastructure concerns (directory permissions,
  disk space).
- [G41](../grammar/G41-normalize-dedup-active.md) -- Normalize dedup active.
  Another caching optimization (at the Ascent term level rather than the lint
  level).
