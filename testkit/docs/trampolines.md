# Trampoline Architecture for Stack-Safe AST Operations

> *"Every derived trait that touches `Box<T>` fields is a latent stack overflow
> waiting to happen. Trampolines convert O(n) stack depth to O(1)."*

**Source files:**
- `macros/src/gen/syntax/display.rs`
- `macros/src/gen/syntax/debug.rs`
- `macros/src/gen/term_ops/iterative_clone.rs`
- `macros/src/gen/term_ops/iterative_drop.rs`
- `macros/src/gen/term_ops/iterative_cmp.rs`
- `macros/src/gen/term_ops/iterative_hash.rs`

---

## Table of Contents

1. [The Problem](#1-the-problem)
2. [The Solution](#2-the-solution)
3. [Each Trampolined Operation](#3-each-trampolined-operation)
4. [Safety Argument](#4-safety-argument)
5. [Performance](#5-performance)

---

## 1 The Problem

### 1.1 What Is It?

Deeply nested AST terms cause stack overflow in any derived trait that recurses
through `Box<T>` fields. This is not a theoretical concern: MeTTaIL's rewriting
systems routinely produce terms with 100,000+ nesting depth (e.g., a long chain
of `AddInt(x, AddInt(y, AddInt(z, ...)))` built during evaluation).

### 1.2 Why Does It Happen?

Consider the standard `#[derive(Clone)]` for a recursive enum:

```
    enum Int {
        Lit(i32),
        Add(Box<Int>, Box<Int>),
    }
```

The compiler generates:

```
    impl Clone for Int {
        fn clone(&self) -> Int {
            match self {
                Int::Lit(v) => Int::Lit(v.clone()),
                Int::Add(a, b) => Int::Add(
                    Box::new((*a).clone()),  // recursive call
                    Box::new((*b).clone()),  // recursive call
                ),
            }
        }
    }
```

For a term of depth *d*, this produces *d* recursive calls. The default thread
stack size on most platforms is 2 MiB (configurable via `RUST_MIN_STACK`),
which supports roughly 20,000-50,000 stack frames depending on frame size. A
term of depth 100,000 overflows the stack.

The same problem afflicts `Display`, `Debug`, `Drop`, `PartialEq`, `Eq`,
`PartialOrd`, `Ord`, and `Hash` -- every trait that needs to visit every node
in the tree.

### 1.3 The Scope of the Problem

```
    ┌──────────────────────────────────────────────────────────────────┐
    │           Trait            │  Recurse via     │  Overflow Depth  │
    ├────────────────────────────┼──────────────────┼──────────────────┤
    │  Display                   │  write!("{}")    │  ~20K-50K        │
    │  Debug                     │  write!("{:?}")  │  ~20K-50K        │
    │  Clone                     │  .clone()        │  ~20K-50K        │
    │  Drop                      │  implicit drop   │  ~20K-50K        │
    │  PartialEq / Eq            │  == on children  │  ~30K-60K        │
    │  PartialOrd / Ord          │  .cmp() recurse  │  ~30K-60K        │
    │  Hash                      │  .hash() recurse │  ~30K-60K        │
    └──────────────────────────────────────────────────────────────────┘
```

Each trait has a slightly different frame size, so the exact overflow threshold
varies, but all are within the range that MeTTaIL terms routinely reach.

---

## 2 The Solution

### 2.1 What Is It?

Iterative work-stacks (trampolines). Instead of calling a trait method
recursively on each `Box<T>` child, the generated code pushes child work items
onto an explicit `Vec<Task>` and processes them in a flat loop.

### 2.2 The Architecture

Every trampolined operation follows the same structural pattern:

```
    ┌────────────────────────────────────────────────────────┐
    │                Common Architecture                     │
    │                                                        │
    │  1. {Op}Task enum        One variant per category,     │
    │                          plus glue variants            │
    │                                                        │
    │  2. {OP}_TASK_POOL       Cell<Vec<{Op}Task>> in TLS    │
    │                                                        │
    │  3. {op}_iterative()     The driver loop that pops     │
    │                          tasks and processes them      │
    │                                                        │
    │  4. impl {Trait} for Cat Thin wrapper that pushes      │
    │                          initial task and delegates    │
    └────────────────────────────────────────────────────────┘
```

### 2.3 The TLS Pool Pattern

Every operation uses a thread-local `Cell<Vec<Task>>` pool for zero-allocation
steady-state performance:

```
    thread_local! {
        static {OP}_TASK_POOL: Cell<Vec<{Op}Task>> =
            Cell::new(Vec::new());
    }
```

The `Cell<Vec<T>>` pattern works as follows:

```
    PROCEDURE acquire_pool():
        stack ← POOL.take()       -- atomically swap with empty Vec
        stack.clear()             -- reuse capacity
        RETURN stack

    PROCEDURE release_pool(stack):
        POOL.set(stack)           -- return capacity to the pool
```

**Key property:** `Cell::take()` replaces the cell's content with
`Vec::new()` (an empty, zero-capacity vector). This means:
- The first call allocates a new Vec
- Subsequent calls reuse the existing capacity
- Re-entrant calls (e.g., from collection elements) get empty Vecs;
  the outermost call retains the pool capacity

### 2.4 The `try_with` Fallback

All TLS access uses `try_with` (not `with`) to handle thread shutdown:

```
    PROCEDURE safe_pool_access():
        result ← POOL.try_with(|cell| cell.take())
        MATCH result:
            Ok(stack): RETURN stack
            Err(_):    RETURN Vec::new()  -- TLS destroyed, use local
```

During thread teardown, the thread-local storage may already be destroyed
when `Drop::drop` runs for remaining values. Using `try_with` prevents a
panic in this situation; the fallback creates a local stack that is dropped
normally.

---

## 3 Each Trampolined Operation

### 3.1 Display

**Source:** `macros/src/gen/syntax/display.rs`

#### 3.1.1 The Task Enum

```
    ENUM DisplayTask:
        DisplayInt(*const Int, u8)     -- raw pointer + min_bp
        DisplayFloat(*const Float, u8)
        DisplayBool(*const Bool, u8)
        ...                            -- one per category
        WriteLiteral(&'static str)     -- compile-time string
        WriteString(String)            -- dynamic string
```

The `min_bp` (minimum binding power) parameter enables **precedence-aware
parenthesization**: when an infix operator's `left_bp` is less than the
inherited `min_bp`, the output is wrapped in `(...)`.

#### 3.1.2 The Driver Loop

```
    PROCEDURE display_iterative(stack, formatter):
        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                WriteLiteral(s):
                    formatter.write_str(s)
                WriteString(s):
                    formatter.write_str(s)
                DisplayCat(ptr, min_bp):
                    term ← unsafe { &*ptr }
                    MATCH term:
                        -- Nullary: write label directly
                        Cat::Zero:
                            formatter.write_str("Zero")

                        -- Literal: write value directly
                        Cat::Lit(v):
                            write!(formatter, "{}", v)

                        -- Var: write variable name
                        Cat::Var(ordvar):
                            write variable name

                        -- Infix: precedence-aware output
                        Cat::Add(left, right):
                            -- Lookup binding powers for Add
                            IF bp_info.left_bp < min_bp:
                                -- Need parentheses
                                stack.push(WriteLiteral(")"))
                                stack.push(DisplayInt(right, bp_info.right_bp))
                                stack.push(WriteLiteral(" + "))
                                stack.push(DisplayInt(left, bp_info.left_bp))
                                stack.push(WriteLiteral("("))
                            ELSE:
                                stack.push(DisplayInt(right, bp_info.right_bp))
                                stack.push(WriteLiteral(" + "))
                                stack.push(DisplayInt(left, bp_info.left_bp))

                        -- Binder: decompose scope
                        Cat::Lam(scope):
                            inner ← scope.inner()
                            stack.push(WriteLiteral("}"))
                            stack.push(DisplayCat(body_ptr, 0))
                            stack.push(WriteLiteral(".{"))
                            stack.push(WriteString(var_name))
                            stack.push(WriteLiteral("^"))
```

**Critical ordering:** Because the stack is LIFO, tasks are pushed in *reverse*
order. The first item to be displayed (e.g., `"("`) is pushed *last* so it
is popped *first*.

#### 3.1.3 The `impl Display`

```
    impl Display for Cat {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            let mut stack = DISPLAY_TASK_POOL.try_with(|cell| cell.take())
                .unwrap_or_else(|_| Vec::new());
            stack.push(DisplayTask::DisplayCat(self as *const _, 0));
            let result = display_iterative(&mut stack, f);
            stack.clear();
            let _ = DISPLAY_TASK_POOL.try_with(|cell| cell.set(stack));
            result
        }
    }
```

#### 3.1.4 Raw Pointer Safety

The `*const Cat` pointer is derived from `&self` in `fmt()`. The reference is
valid for the entire duration of `fmt()`, and `display_iterative` runs
synchronously within `fmt()`. Therefore:

- The pointer is never dangling (lifetime containment)
- No aliasing violations (`*const` is read-only)
- No concurrent access (single-threaded within `fmt()`)

See [Section 4](#4-safety-argument) for the full safety argument.


### 3.2 Debug

**Source:** `macros/src/gen/syntax/debug.rs`

#### 3.2.1 The Task Enum

```
    ENUM DebugTask:
        DebugInt(*const Int)
        DebugFloat(*const Float)
        ...                         -- one per category
        WriteStr(&'static str)      -- format glue
        WriteString(String)         -- owned format glue
```

Unlike `DisplayTask`, `DebugTask` does not carry a `min_bp` parameter because
Debug output uses the derived `Debug` format (`Label(field1, field2)`) which
does not require precedence handling.

#### 3.2.2 Output Format

The generated Debug output exactly matches `#[derive(Debug)]`:

```
    ┌───────────────┬───────────────────────────────────────────┐
    │ Variant       │ Output                                    │
    ├───────────────┼───────────────────────────────────────────┤
    │ Nullary       │ PZero                                     │
    │ Literal       │ NumLit(42)                                │
    │ Var           │ IVar(OrdVar(...))                         │
    │ Regular       │ AddInt(left, right)                       │
    │ Collection    │ PPar(HashBag {...})                       │
    │ Binder        │ LamInt(Scope { ... })                     │
    └───────────────┴───────────────────────────────────────────┘
```

For **Regular** variants, each child field is pushed as a `DebugTask`:

```
    PROCEDURE debug_regular(Cat::Add(left, right), stack):
        stack.push(WriteStr(")"))
        stack.push(DebugInt(right as *const _))
        stack.push(WriteStr(", "))
        stack.push(DebugInt(left as *const _))
        stack.push(WriteStr("AddInt("))
```

For **Collection** variants, the collection's own `Debug` implementation is
called inline (since collections are typically small and non-recursive):

```
    PROCEDURE debug_collection(Cat::Par(bag), formatter):
        formatter.write_str("PPar(")?
        Debug::fmt(bag, formatter)?
        formatter.write_str(")")
```


### 3.3 Clone

**Source:** `macros/src/gen/term_ops/iterative_clone.rs`

#### 3.3.1 The Two-Phase Design

Clone is more complex than Display/Debug because it must *produce* a value
rather than just *observe* one. The design uses two phases:

```
    ┌────────────────────────────────────────────────┐
    │  Phase 1: Clone (top-down walk)                │
    │  ─────────────────────────────                 │
    │  For each node:                                │
    │    1. Allocate result slots for children       │
    │    2. Push Assemble task (runs AFTER children) │
    │    3. Push Clone tasks for children            │
    │                                                │
    │  Phase 2: Assemble (bottom-up assembly)        │
    │  ─────────────────────────────                 │
    │  When children are cloned (slots filled):      │
    │    Read children from slots                    │
    │    Construct parent node                       │
    │    Store in parent's slot                      │
    └────────────────────────────────────────────────┘
```

#### 3.3.2 Data Structures

```
    ENUM AnyClonedTerm:
        WrapInt(Int)
        WrapFloat(Float)
        ...  -- one per category

    ENUM CloneTask:
        -- Clone variants: initiate cloning
        CloneInt { src: *const Int, slot: usize }
        CloneFloat { src: *const Float, slot: usize }
        ...

        -- Assemble variants: reconstruct parents
        AssembleInt_AddInt { slot: usize, f0_slot: usize, f1_slot: usize }
        AssembleInt_MulInt { slot: usize, f0_slot: usize, f1_slot: usize }
        ...  -- one per non-leaf constructor

    -- Result buffer
    results: Vec<Option<AnyClonedTerm>>

    -- TLS pools
    CLONE_TASK_POOL:   Cell<Vec<CloneTask>>
    CLONE_RESULT_POOL: Cell<Vec<Option<AnyClonedTerm>>>
```

#### 3.3.3 The Iterative Engine

```
    PROCEDURE clone_iterative(src: &Cat) → Cat:
        stack ← acquire_pool(CLONE_TASK_POOL)
        results ← acquire_pool(CLONE_RESULT_POOL)
        next_slot ← 0

        -- Initial task
        root_slot ← next_slot; next_slot += 1
        results.push(None)
        stack.push(CloneCat{src: src as *const _, slot: root_slot})

        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                CloneCat{src, slot}:
                    term ← unsafe { &*src }
                    MATCH term:
                        -- Leaf: clone directly into slot
                        Cat::Lit(v):
                            results[slot] ← Some(WrapCat(Cat::Lit(v.clone())))

                        Cat::Zero:
                            results[slot] ← Some(WrapCat(Cat::Zero))

                        Cat::Var(v):
                            results[slot] ← Some(WrapCat(Cat::Var(v.clone())))

                        -- Recursive: allocate child slots, push assemble + clone tasks
                        Cat::Add(left, right):
                            left_slot ← next_slot; next_slot += 1
                            right_slot ← next_slot; next_slot += 1
                            results.push(None)  -- left_slot
                            results.push(None)  -- right_slot
                            -- Assemble runs AFTER children (pushed first → popped last)
                            stack.push(AssembleCat_Add{slot, f0_slot: left_slot, f1_slot: right_slot})
                            -- Clone children (pushed last → popped first)
                            stack.push(CloneCat{src: &**right as *const _, slot: right_slot})
                            stack.push(CloneCat{src: &**left as *const _, slot: left_slot})

                AssembleCat_Add{slot, f0_slot, f1_slot}:
                    left ← results[f0_slot].take().unwrap_cat()
                    right ← results[f1_slot].take().unwrap_cat()
                    results[slot] ← Some(WrapCat(Cat::Add(Box::new(left), Box::new(right))))

        result ← results[root_slot].take().unwrap_cat()
        release_pool(CLONE_TASK_POOL, stack)
        release_pool(CLONE_RESULT_POOL, results)
        RETURN result
```

#### 3.3.4 Collection Fields

For `Vec<T>` fields, the Assemble variant stores `(start_slot, count)`:

```
    AssembleCat_Par{ slot, elements_start, elements_count }
```

For `HashBag<T>` fields, it additionally stores the multiplicities:

```
    AssembleCat_Par{ slot, elements_start, elements_count, counts_vec: Vec<usize> }
```

During assembly, elements are extracted from `results[start..start+count]` and
collected into the appropriate container.

#### 3.3.5 Binder Fields

Binder variants (single and multi) require special handling:

1. Pre-scope fields are cloned normally (allocate slots, push clone tasks)
2. The `Scope` is decomposed: `Binder` pattern is cloned inline, body is
   pushed as a clone task
3. During assembly, `Scope::new(binder, Box::new(body))` reconstructs the scope


### 3.4 Drop

**Source:** `macros/src/gen/term_ops/iterative_drop.rs`

#### 3.4.1 The `std::mem::replace` Strategy

Drop cannot use result slots because it does not produce a value. Instead, it
uses `std::mem::replace` to **extract** owned children from `Box<T>` fields,
substituting cheap dummy values:

```
    PROCEDURE extract_children(value: &mut Cat, stack):
        MATCH value:
            Cat::Add(ref mut left, ref mut right):
                child_left ← std::mem::replace(left, Box::new(dummy_int()))
                stack.push(DropInt(*child_left))
                child_right ← std::mem::replace(right, Box::new(dummy_int()))
                stack.push(DropInt(*child_right))
            Cat::Lit(_) | Cat::Zero | Cat::Var(_):
                -- Leaf: nothing to extract
```

After extraction, the original value contains only dummy leaves, which the
compiler drops cheaply via the standard field-by-field drop.

#### 3.4.2 Dummy Values

Each category has a `dummy_cat()` function that returns the cheapest possible
leaf value:

```
    PROCEDURE select_dummy_strategy(category):
        1. IF ∃ Nullary variant:       RETURN Cat::NullaryLabel     -- zero allocation
        2. ELIF ∃ Literal variant:     RETURN Cat::Lit(default)     -- minimal allocation
        3. ELSE:                       RETURN Cat::Var(fresh_var)   -- always available
```

#### 3.4.3 Re-Entrancy Guard

Drop has a unique re-entrancy challenge: when a value with dummy-filled fields
is dropped by the compiler, it triggers `Drop::drop` again for the dummies.
A thread-local flag prevents re-entrant processing:

```
    ENUM DropTask:
        DropInt(Int)
        DropFloat(Float)
        ...

    thread_local:
        DROP_TASK_POOL: Cell<Vec<DropTask>>
        DROP_ACTIVE:    Cell<bool>
```

#### 3.4.4 The Driver

```
    impl Drop for Cat {
        fn drop(&mut self) {
            -- Check re-entrancy flag
            let is_active = DROP_ACTIVE.try_with(|c| c.get())
                .unwrap_or(true);  -- if TLS destroyed, skip

            IF is_active:
                -- Inner drop: compiler handles dummy leaves
                RETURN

            -- Outermost drop: set flag, process iteratively
            let _ = DROP_ACTIVE.try_with(|c| c.set(true));

            let mut stack = DROP_TASK_POOL.try_with(|c| c.take())
                .unwrap_or_else(|_| Vec::new());

            push_drop_children_cat(self, &mut stack);

            WHILE stack is non-empty:
                task ← stack.pop()
                MATCH task:
                    DropCat(mut value):
                        push_drop_children_cat(&mut value, &mut stack)
                        -- `value` now contains only dummies
                        -- compiler drops it when it goes out of scope

            stack.clear();
            let _ = DROP_TASK_POOL.try_with(|c| c.set(stack));
            let _ = DROP_ACTIVE.try_with(|c| c.set(false));
        }
    }
```

#### 3.4.5 Collection Field Extraction

For `Vec<T>` fields, `std::mem::take` extracts the entire vector, then each
element is pushed as a `DropTask`:

```
    for elem in std::mem::take(vec_field) {
        stack.push(DropTask::DropCat(elem));
    }
```

For `HashBag<T>`, only unique elements need to be dropped (count is
multiplicity, not ownership):

```
    for (elem, _count) in std::mem::take(bag_field).into_iter() {
        stack.push(DropTask::DropCat(elem));
    }
```


### 3.5 PartialEq / Eq

**Source:** `macros/src/gen/term_ops/iterative_cmp.rs`

#### 3.5.1 The Task Enum

```
    ENUM CmpTask:
        CmpInt(*const Int, *const Int)       -- left/right pointer pair
        CmpFloat(*const Float, *const Float)
        ...
```

#### 3.5.2 The Equality Engine

```
    PROCEDURE eq_iterative(stack) → bool:
        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                CmpCat(left_ptr, right_ptr):
                    left ← unsafe { &*left_ptr }
                    right ← unsafe { &*right_ptr }

                    -- Different discriminants → not equal
                    IF discriminant(left) ≠ discriminant(right):
                        RETURN false

                    -- Same discriminant: compare fields
                    MATCH (left, right):
                        (Cat::Lit(a), Cat::Lit(b)):
                            IF a ≠ b: RETURN false
                        (Cat::Var(a), Cat::Var(b)):
                            IF a ≠ b: RETURN false
                        (Cat::Zero, Cat::Zero):
                            -- equal
                        (Cat::Add(la, lb), Cat::Add(ra, rb)):
                            -- Push child comparisons
                            stack.push(CmpCat(&**lb as *const _, &**rb as *const _))
                            stack.push(CmpCat(&**la as *const _, &**ra as *const _))
                        (Cat::Par(a_bag), Cat::Par(b_bag)):
                            -- Delegate to collection's own PartialEq
                            IF a_bag ≠ b_bag: RETURN false
                        ...

        RETURN true  -- all comparisons passed
```

**Early exit:** The engine returns `false` immediately on the first inequality,
avoiding unnecessary comparisons.

#### 3.5.3 Collection Re-Entrancy

When a `Vec<Cat>` or `HashBag<Cat>` delegates to its own `PartialEq`, that
implementation calls `PartialEq` on each element, which re-enters the iterative
engine. The `Cell::take()` pattern handles this correctly:

1. Outer call takes the pool → gets the capacity-bearing Vec
2. Inner call takes the pool → gets an empty Vec (from the Cell)
3. Inner call returns the Vec to the pool
4. Outer call continues with its own Vec (was never in the pool)


### 3.6 Ord / PartialOrd

**Source:** `macros/src/gen/term_ops/iterative_cmp.rs`

#### 3.6.1 Variant Ordering

Each category has a `variant_index_cat(val: &Cat) -> usize` function that maps
variants to their declaration-order index. This provides the discriminant
ordering: `Lit < Var < Add < Mul < ...` (or however they are declared).

```
    PROCEDURE variant_index_int(val: &Int) → usize:
        MATCH val:
            Int::Lit(_)    → 0
            Int::Var(_)    → 1
            Int::Add(..)   → 2
            Int::Mul(..)   → 3
            ...
```

#### 3.6.2 The Ordering Engine

```
    PROCEDURE cmp_iterative(stack) → Ordering:
        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                CmpCat(left_ptr, right_ptr):
                    left ← unsafe { &*left_ptr }
                    right ← unsafe { &*right_ptr }

                    idx_left ← variant_index_cat(left)
                    idx_right ← variant_index_cat(right)

                    IF idx_left ≠ idx_right:
                        RETURN idx_left.cmp(idx_right)

                    -- Same variant: compare fields lexicographically
                    MATCH (left, right):
                        (Cat::Lit(a), Cat::Lit(b)):
                            ord ← a.cmp(b)
                            IF ord ≠ Equal: RETURN ord
                        (Cat::Add(la, lb), Cat::Add(ra, rb)):
                            -- Push in reverse for left-to-right comparison
                            stack.push(CmpCat(&**lb, &**rb))  -- second field
                            stack.push(CmpCat(&**la, &**ra))  -- first field
                        (Cat::Par(a_bag), Cat::Par(b_bag)):
                            ord ← a_bag.cmp(b_bag)
                            IF ord ≠ Equal: RETURN ord
                        ...

        RETURN Equal  -- all field comparisons were equal
```

`PartialOrd` simply delegates to `Ord::cmp`, wrapping the result in `Some(...)`.


### 3.7 Hash

**Source:** `macros/src/gen/term_ops/iterative_hash.rs`

#### 3.7.1 The Task Enum

```
    ENUM HashTask:
        HashInt(*const Int)
        HashFloat(*const Float)
        ...
```

Unlike the comparison tasks, hash tasks carry only a single pointer (no pair).

#### 3.7.2 Hasher Threading

The `Hasher` state is **not stored in the task**. Instead, it is passed as a
parameter to the driver function:

```
    PROCEDURE hash_iterative<H: Hasher>(stack, state: &mut H):
        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                HashCat(ptr):
                    val ← unsafe { &*ptr }
                    -- Hash discriminant first (consistent with derive(Hash))
                    Hash::hash(&variant_index_cat(val), state)

                    MATCH val:
                        Cat::Lit(v):
                            Hash::hash(v, state)
                        Cat::Zero:
                            -- discriminant only
                        Cat::Var(v):
                            Hash::hash(v, state)
                        Cat::Add(left, right):
                            stack.push(HashCat(&**right as *const _))
                            stack.push(HashCat(&**left as *const _))
                        Cat::Par(bag):
                            Hash::hash(bag, state)
                        ...
```

This design ensures that the hash of a trampolined term is identical to what
`#[derive(Hash)]` would produce: discriminant first, then fields in declaration
order.

---

## 4 Safety Argument

### 4.1 Raw Pointer Validity

All trampolined operations use raw pointers (`*const Cat`) to avoid borrow
checker limitations (the work stack would need to store references with
self-referential lifetimes). The safety argument is:

**Theorem (Pointer Validity).** Every `*const Cat` in a task enum is valid for
reads for the entire duration of the iterative engine call.

**Proof sketch:**

1. **Provenance:** Each `*const Cat` is derived from either:
   - `&self` in a trait method (`Display::fmt`, `Clone::clone`, `Hash::hash`,
     `PartialEq::eq`, `Ord::cmp`), or
   - `&*box_field` where `box_field: &Box<Cat>` is a reference to a field of
     `self`

2. **Lifetime containment:** The trait method holds a borrow on `self` for its
   entire duration. The iterative engine runs synchronously within this method.
   Therefore, `self` and all its transitively-owned children are alive for the
   entire engine execution.

3. **No aliasing violations:** `*const Cat` is a read-only pointer. The engine
   never writes through these pointers. The only mutation occurs in `Drop`
   (via `std::mem::replace`), which uses `&mut self` -- a distinct, exclusive
   reference.

4. **No concurrent access:** All pointers are dereferenced within the same
   thread that created them (enforced by TLS). No `Send`/`Sync` crossing occurs.

### 4.2 Drop Safety (std::mem::replace)

The `Drop` implementation uses `std::mem::replace` to extract children:

```rust
let child = std::mem::replace(field, Box::new(dummy()));
```

**Safety:** `std::mem::replace` is a safe operation. It returns the old value
and installs the new one atomically (in terms of ownership). The dummy value
is a valid, fully-initialized value of type `Cat`. After replacement:

- The extracted child is pushed onto the work stack for later processing
- The dummy remains in the original field
- When the original value is dropped by the compiler, the dummy is dropped
  cheaply (it has no `Box<T>` children)

### 4.3 Re-Entrancy Safety

**For Drop:** The `DROP_ACTIVE` flag prevents the iterative engine from running
recursively. Inner drops see the flag and return immediately, letting the
compiler's default drop handle the dummy-filled value.

**For Eq/Ord/Hash:** Collection fields (Vec, HashBag, HashSet) may re-enter
the engine via their own trait implementations. The `Cell::take()` pattern
provides isolation: each level of re-entrancy gets its own work stack. The
outermost call retains the pool capacity.

### 4.4 Thread Shutdown Safety

During thread shutdown, TLS may be destroyed before all values are dropped.
The `try_with` fallback ensures:

1. If TLS is available: use the pool (normal path)
2. If TLS is destroyed: use a local stack (fallback path)

In both cases, the operation completes correctly. The only difference is
performance: the fallback path allocates a new Vec every time.

For `Drop` specifically, the fallback is:

```rust
let is_active = DROP_ACTIVE.try_with(|c| c.get()).unwrap_or(true);
```

If TLS is destroyed, `unwrap_or(true)` treats the engine as "already active,"
causing the drop to skip the iterative logic and let the compiler handle it.
This is safe because at thread shutdown, the remaining values are typically
shallow (the deep chains have already been dropped).

### 4.5 `Send` and `Sync` for Task Enums

`CmpTask` and `HashTask` implement `unsafe impl Send` and `unsafe impl Sync`
because they hold `*const` pointers. This is sound because:

1. The pointers are only dereferenced within the thread that created them
2. The task enums never escape to other threads (they live in TLS)
3. The `Send`/`Sync` implementations are required only because Rust's compiler
   cannot prove the pointers are thread-local; the TLS storage pattern
   guarantees it

---

## 5 Performance

### 5.1 Zero-Allocation Steady State

After the first invocation of each operation, the TLS pools contain
capacity-bearing Vecs. Subsequent invocations reuse this capacity via
`Cell::take()` and `Cell::set()`, which are O(1) pointer swaps.

The steady-state cost per operation is:

```
    ┌────────────────┬────────────────────────────────────────┐
    │  Operation     │  Allocations                           │
    ├────────────────┼────────────────────────────────────────┤
    │  Display       │  0 (reuses DISPLAY_TASK_POOL)          │
    │  Debug         │  0 (reuses DEBUG_TASK_POOL)            │
    │  Clone         │  0 pool + O(n) Box::new for children   │
    │  Drop          │  0 pool + O(n) Box::new for dummies    │
    │  PartialEq     │  0 (reuses CMP_TASK_POOL)              │
    │  Ord           │  0 (reuses CMP_TASK_POOL)              │
    │  Hash          │  0 (reuses HASH_TASK_POOL)             │
    └────────────────┴────────────────────────────────────────┘
```

Clone and Drop necessarily allocate `Box<T>` values (for cloned children and
dummy replacements, respectively), but the work-stack itself is allocation-free
after warmup.

### 5.2 TLS Pool Reuse Across Calls

The pool pattern has a particularly favorable property for batch operations:
when the same operation is called many times (e.g., displaying all normal forms
in a result set), the pool grows to accommodate the largest term and then
stays at that size, amortizing the allocation cost over all subsequent calls.

### 5.3 Comparison with Recursive Implementations

```
    ┌──────────────────┬─────────────────────┬───────────────────────┐
    │  Property        │  Recursive (derive) │  Trampolined          │
    ├──────────────────┼─────────────────────┼───────────────────────┤
    │  Stack usage     │  O(depth)           │  O(1) call stack      │
    │                  │                     │  O(n) heap (pool)     │
    │  Max depth       │  ~20K-50K           │  ∞ (limited by RAM)   │
    │  Allocation      │  0                  │  First call: 1 Vec    │
    │  (steady state)  │                     │  Subsequent: 0        │
    │  Cache behavior  │  Good (depth-first) │  Good (stack is LIFO  │
    │                  │                     │  → same access order) │
    │  Correctness     │  Trivial            │  Requires safety arg  │
    └──────────────────┴─────────────────────┴───────────────────────┘
```

The trampoline approach trades a small increase in complexity (the safety
argument and the TLS pool machinery) for **unlimited term depth**. For shallow
terms (depth < 1000), the performance is nearly identical to recursive
implementations. For deep terms, the recursive approach crashes while the
trampoline continues to work.

### 5.4 Memory Usage

The work stack's peak size equals the **maximum width** of the term at any
level, not its depth. For a binary tree of depth *d*, the peak stack size is
O(d) (one task per level on the rightmost path). For a term with branching
factor *b*, the peak is O(b * d). This is the same as the memory consumed by
the recursive call stack -- the trampoline simply moves it from the (small,
fixed) thread stack to the (large, growable) heap.

---

## References

- Clements, J. & Felleisen, M. (2004). *A Tail-Recursive Machine with Stack
  Inspection.* ACM Transactions on Programming Languages and Systems (TOPLAS),
  26(6), 1029-1052.

- Jones, S. P. (1992). *Implementing Lazy Functional Languages on Stock
  Hardware: The Spineless Tagless G-machine.* Journal of Functional Programming,
  2(2), 127-202. (Work-stack evaluation strategies.)

- Rust Reference. *Thread Local Storage.* https://doc.rust-lang.org/std/thread/struct.LocalKey.html

- Rust Reference. *std::mem::replace.* https://doc.rust-lang.org/std/mem/fn.replace.html
