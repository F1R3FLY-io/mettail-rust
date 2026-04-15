# Chained Cross-Category Comparison Bug

## Finding

`int(x != true > y)` parses OK but `int(x != 0.5 > y)` fails.

The difference: `true` is Bool (NeBool handles it directly) but `0.5` is Float (requires NeFloat via cross-category dispatch). After the cross-category dispatch for `NeFloat`, the Pratt infix loop at the Bool level doesn't correctly continue with `> y`.

## Exact boundary

| Expression | Result | Why |
|---|---|---|
| `int(x != true > y)` | OK | NeBool(x, true) then GtBool chain — all same-category |
| `int(x != 0.5 > y)` | ERR | NeFloat(x, 0.5) via cross-cat dispatch, then `> y` fails |
| `int(y != 0.5)` | OK | Single comparison works fine |
| `x != true > y` (as Bool) | OK | Same-category chaining works |

## Root cause hypothesis

After cross-category infix dispatch resolves `x != 0.5` as `NeFloat` (returning Bool), the Pratt infix loop needs to continue at the Bool level to consume `> y`. But the dispatch.rs ambiguous arm returns `Ok(result)` directly without re-entering the infix loop.

The `return Ok(...)` at the end of the backtracking fix exits the entire dispatch function, returning to the NFA try-all in `int(...)`. The NFA receives `BoolToInt(NeFloat(x, 0.5))` and expects `)` — but `> y` remains unconsumed.

## Status

Needs deeper investigation of how the dispatch.rs ambiguous arm interacts with the Pratt infix loop. The backtracking fix replaced `?` with `match` + fallthrough, but the `Ok` arm still does `return Ok(...)` which exits the dispatch before the infix loop can chain.
