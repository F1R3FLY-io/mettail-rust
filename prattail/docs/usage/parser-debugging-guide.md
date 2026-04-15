# Parser Debugging Guide

## Overview

The CEK machine's reactive architecture enables step-by-step debugging of the parsing process. Each transition emits a `CekTraceEntry` that can be consumed by a DAP (Debug Adapter Protocol) server or other debugging tools.

## Trace Entry Types

| Kind | What It Captures |
|------|-----------------|
| `Drive` | Entering prefix dispatch: token at position, binding power |
| `Push` | Pushing continuation frame: variant name, captured values |
| `Pop` | Popping frame: variant name, action taken |
| `Value` | Value produced: display representation |
| `Error` | Parse error: message |

## Example Trace

Parsing `1 + 2 * 3`:

```
[Expr@0 d=0] DRIVE bp=0 tok=Integer(1)
[Expr@0 d=0] VALUE Lit(1)
[Expr@1 d=0] DRIVE bp=0 tok=Plus
[Expr@1 d=1] PUSH InfixRHS [lhs=Lit(1)]
[Expr@2 d=1] DRIVE bp=11 tok=Integer(2)
[Expr@2 d=1] VALUE Lit(2)
[Expr@3 d=1] DRIVE bp=11 tok=Star
[Expr@3 d=2] PUSH InfixRHS [lhs=Lit(2)]
[Expr@4 d=2] DRIVE bp=13 tok=Integer(3)
[Expr@4 d=2] VALUE Lit(3)
[Expr@5 d=2] POP InfixRHS → construct Mul
[Expr@5 d=1] VALUE Mul(Lit(2), Lit(3))
[Expr@5 d=1] POP InfixRHS → construct Add
[Expr@5 d=0] VALUE Add(Lit(1), Mul(Lit(2), Lit(3)))
```

## DAP Mapping

| DAP Concept | CEK Implementation |
|-------------|-------------------|
| `stackTrace` request | `parse_state.stack_tags` → StackFrame objects |
| `variables` request | Frame captures + `cur_bp`, `running_weight` |
| `scopes` request | One scope per frame + "Locals" scope |
| `evaluate` request | Parse expression in current `CekEnvironment` |
| `stepIn` | One `process_event(Step)` |
| `stepOver` | Step until `stack_depth ≤ current` |
| `stepOut` | Step until `stack_depth < current` |
| `continue` | `run_to_completion()` or until next breakpoint |
| Breakpoints | Predicates on `ParseState` (position, depth, variant) |

## Breakpoint Types

| Type | Predicate |
|------|-----------|
| Position breakpoint | `state.pos == target_pos` |
| Depth breakpoint | `state.stack_depth() >= target_depth` |
| Frame breakpoint | `state.stack_tags.last() == Some(target_variant)` |
| Value breakpoint | Custom predicate on trace entry |

## TraceCollector Statistics

After parsing, the `TraceCollector` provides:

```rust
collector.drive_count      // Total prefix dispatch transitions
collector.unwind_count     // Total frame pop transitions
collector.max_stack_depth  // Peak stack depth reached
collector.hit_count("InfixRHS")  // How many times InfixRHS was pushed
collector.entries.len()    // Total trace entries
```
