# CekEnvironment Usage Guide

## Overview

`CekEnvironment` provides the unified "E" (Environment) component of the CEK machine. It manages per-category variable bindings and guard evaluation context, persisting across REPL submissions.

## Basic Usage

```rust
use mettail_prattail::cek::CekEnvironment;

let mut env = CekEnvironment::new();

// Bind x = 5 in the Int category
env.set("Int", "x", "5".to_string());

// Look up x
assert_eq!(env.get("Int", "x"), Some(&"5".to_string()));

// Remove binding
env.remove("Int", "x");
```

## REPL Integration

The environment persists across REPL submissions:

```
> x = 5         // env.set("Int", "x", "5")
> x + 3         // env.get("Int", "x") → "5", result = 8
> y = x * 2     // env.get("Int", "x") → "5", env.set("Int", "y", "10")
```

## Guard Bindings

Guard evaluation uses temporary bindings that are cleared after each guard check:

```rust
env.set_guard("cond", "true".to_string());
let val = env.get_guard("cond"); // Some("true")
env.clear_guards(); // Remove all guard bindings
```

## Querying the Environment

```rust
// List all variables in a category
let vars = env.category_vars("Int"); // ["x", "y"]

// List all categories with bindings
let cats = env.bound_categories(); // ["Int", "Proc"]

// Check if environment is empty
assert!(!env.is_empty());
```

## Per-Category Isolation

Variables in different categories are isolated:

```rust
env.set("Int", "x", "5".to_string());
env.set("Proc", "x", "PZero".to_string());

// These are different bindings
assert_eq!(env.get("Int", "x"), Some(&"5".to_string()));
assert_eq!(env.get("Proc", "x"), Some(&"PZero".to_string()));
```
