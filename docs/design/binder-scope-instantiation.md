# Scope instantiation under binders

Scope instantiation replaces the variables of one removed scope.
It must preserve references to every other scope.
This operation supports the capture-safety work from Mike's binder-context report, work item 11803.
The explicit rewrite-family syntax and declared-context policy require additional changes.

## The defect

The former procedure opened a scope with fresh variable identities and then substituted those identities.
Moniker opening replaces references to the selected scope.
It does not decrement references beyond that scope.
The generated identity substitution also inserted arguments without shifting their outer references.

These operations work for many closed terms.
They fail when a reduction occurs inside another binder.
Two lambda examples demonstrate both defects:

| Witness | Source | Required result | Former result |
|---|---|---|---|
| W1 | `lam y. (lam x. lam z. x, y)` | `lam y. lam z. y` | `lam y. lam z. z` |
| W2 | `lam a. lam y. (lam x. y, w)` | `lam a. lam y. y` | `lam a. lam y. a` |

The tests compare bindings in the abstract syntax tree.
Display text alone cannot establish capture safety because reconstructed binders can lose their display names.

## Scope coordinates

A bound variable has a scope offset and a binder index.
The scope offset counts enclosing scopes.
The binder index selects one variable from the selected scope's ordered binder list.
A scope with several binders still increases the scope offset by one.

Let $`d`$ be the number of retained scopes between the traversal position and the removed scope.
Let $`s`$ be a variable's scope offset and $`i`$ its binder index.
Scope instantiation applies these rules:

| Condition | Result |
|---|---|
| $`s < d`$ | Preserve the variable. Its scope remains inside the retained body. |
| $`s = d`$ | Select argument $`i`$ and shift its outer references by $`d`$. |
| $`s > d`$ | Decrement the scope offset. Preserve the binder index. |
| Free variable | Preserve the variable identity. |
| Binder body | Increase $`d`$ by one before visiting the body. |
| Other child | Keep $`d`$ unchanged. |

The argument shift has a separate cutoff.
A reference below that cutoff belongs to an internal argument binder and remains unchanged.
A reference at or above that cutoff receives the shift amount.
The cutoff increases once for each argument scope.

```text
Closed scope body + ordered arguments
                  │
                  ▼
        Explicit substitution task stack
                  │
       ┌──────────┼─────────────┐
       ▼          ▼             ▼
 Retained      Removed        Outer
 reference     reference      reference
       │          │             │
       ▼          ▼             ▼
 Preserve     Shift argument  Decrement
                  │
                  ▼
          Reconstruct the result
```

## Implementation

The generator in `macros/src/gen/term_ops/subst.rs` emits two scope operations.
`instantiate_scope_<category>` removes one scope and supplies its ordered arguments.
`shift_bound_scopes` shifts references that point outside a term.
Both operations return `Option` and preserve their source arguments.

The operations use the existing iterative substitution traversal.
Binder reconstruction retains the closed body and its binder list.
It does not close the body again or allocate fresh variable identities.
Replacement storage is shared across nested traversal operations.

The traversal rejects a missing binder index, a replacement with the wrong category, and scope-offset overflow.
A failure returns no result.
The generated normalizer retains the application when instantiation fails.
The Dovetail rule dispatcher declines that rule application.
The multi-binder normalizer and dispatcher also require the argument count to equal the binder count.

The Dovetail beta dispatcher, communication dispatcher, and generated normalizer use this operation.
Ordinary free-variable substitution retains its existing API.
The scope operation is necessary when a rule removes a binder.

## Communication continuations

A matched input supplies a continuation body for substitution.
The body can start with another input prefix or a process variable.
Communication does not require that body to be a value.
The former dispatcher rejected both forms through its continuation-readiness check.

| Source | Required result |
|---|---|
| `new(y, { in(c,x).in(d,z).e!x \| c!y })` | `new(y, { in(d,z).e!y })` |
| `{ in(c,x).p \| c!m }` | `{ p }` |

The dispatcher now extracts and instantiates the continuation without that value check.
Channel matching, sent-name readiness, typed reconstruction, and checked scope instantiation still apply.
The result preserves the output continuation and every residual process, including repeated processes.
Parallel-bag reconstruction flattens nested bags and preserves multiplicity.

The [communication model](../../formal/rocq/rho_bridge/theories/CommContinuationReadiness.v) composes the existing channel guard and de Bruijn substitution specification.
It assumes successful extraction and reconstruction, a ready sent name, and representable scope offsets.
The model represents the reduct and residual processes as a list before bag reconstruction.
It does not establish extraction correctness or the evaluation-context policy.

The pi property generates synchronous and asynchronous interactions, matching and mismatched channels, and nested input and output prefixes.
It checks outer references, local references, process variables, repeated processes, and reported communication firings.
An independent source generator constructs the expected terms with canonical parallel bags.

| Theorem | Implementation evidence |
|---|---|
| `matching_channels_accept_any_continuation` | `communication_depends_on_channels_and_preserves_the_continuation` |
| `different_channels_do_not_communicate` | The same property with mismatched channels |
| `dispatch_corresponds_to_communication` | The same property's result and firing checks |
| `communication_preserves_remainder` | The same property with repeated residual processes and output continuations |
| `old_continuation_gate_rejects_a_valid_step` | Recorded failures before the correction for input-prefix and variable continuations |
| `communication_preserves_nested_binding` | The same property with nested input prefixes and a sent outer reference |

## Formal model and implementation tests

The [Rocq model](../../formal/rocq/rho_bridge/theories/MonikerScopeInstantiation.v) defines the former procedure and the corrected scope operation.
It proves that the corrected single-binder operation equals the existing de Bruijn substitution specification.
The model uses natural-number offsets.
The Rust implementation additionally checks machine-integer overflow.

The [lambda tests](../../languages/tests/binder_context_witness.rs) exercise the generated implementation.
They include reference-model properties, measured defect witnesses, normalization, and a deep traversal.
The [pi test](../../languages/tests/binder_context_pi_witness.rs) exercises communication with a name that an outer restriction binds.

| Theorem | Implementation test |
|---|---|
| `inner_binding_is_unchanged` | `generated_instantiation_matches_scope_model` |
| `outer_binding_loses_one_scope` | `generated_instantiation_matches_scope_model` |
| `replacement_keeps_index_and_depth` | `generated_instantiation_matches_scope_model` |
| `missing_binder_is_rejected` | `generated_instantiation_matches_scope_model` |
| `instantiation_is_debruijn_substitution` | `generated_instantiation_matches_scope_model` |
| `free_names_are_unchanged` | Both generated scope properties |
| `binder_increments_scope_depth` | Both generated scope properties, including multi-binder terms |
| `argument_internal_binding_is_unchanged` | `generated_shift_preserves_internal_bindings` |
| `argument_external_binding_is_shifted` | `generated_shift_preserves_internal_bindings` |
| `old_w1_captures_argument` | Recorded failing W1 runs before the fix |
| `old_w2_keeps_removed_scope` | Recorded failing W2 runs before the fix |
| `corrected_w1_preserves_argument_binding` | `w1_argument_keeps_its_outer_binder`, `normalizer_w1_preserves_argument_binding` |
| `corrected_w2_preserves_body_binding` | `w2_body_keeps_its_outer_binder`, `normalizer_w2_preserves_body_binding` |

The property generators cover free variables, bound variables, applications, single-binder scopes, and multi-binder scopes.
They include absent arguments and invalid binder indices.
They compare the generated operations with the reference model and check that the inputs remain unchanged.
A separate test rejects offset overflow.
The stack test instantiates a term with 100,000 nested binders without increasing the thread stack.

The proofs do not establish the complete evaluator's correctness or the declared-context policy.
They establish the substitution operation and reproduce the two former capture defects.
The existing traversal handles collection and cross-category children.
Full language and cross-engine tests remain necessary for M1 acceptance.

## Verification

Run the Rust checks from the repository root:

```sh
cargo test --locked -p languages --no-default-features \
  --features lambda,pi,dovetail-codegen \
  --test binder_context_witness --test binder_context_pi_witness \
  --test lambda_dovetail --test lambda_dovetail_synthetic \
  --test cross_category_binder_inverse --test pi
```

Run the proof checks from `formal/rocq/rho_bridge`:

```sh
coqc -Q theories RhoBridge theories/MonikerScopeInstantiation.v
coqchk -silent -o -Q theories RhoBridge RhoBridge.MonikerScopeInstantiation
coqc -Q theories RhoBridge theories/CommContinuationReadiness.v
coqchk -silent -o -Q theories RhoBridge RhoBridge.CommContinuationReadiness
```

Use the repository resource limits for these checks.
