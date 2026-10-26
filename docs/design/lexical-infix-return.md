# Lexical infix return

## Required behavior

A lexical fork represents multiple token edges at one input position.
The primary edge has the lexer preference, which normally selects the longest token.
Each operator rule has a binding power that controls whether it can extend the current expression.
The current binding-power floor excludes operators with a lower binding power.

When the primary token cannot extend an expression, the parser must retain the return to its caller.
An alternative token can still start an operator branch.
The parser must preserve both possibilities until the enclosing grammar resolves them.
A return consumes no token. The caller must validate its required literal through the existing literal transition.

For example, consider these two rules:

```text
Remainder . left:Value, right:Value |- left "%" right : Value;
Frame . body:Value, tag:Tag |- "<%" body "%>" "[" tag "]" : Value;
```

In `<%empty == empty%>[tag]`, the primary token `%>` closes the frame.
The alternative `%` can start a remainder expression.
The previous infix fork retained only that operator alternative after the equality operand.
That branch failed on `>`, and no return remained to consume `%>` as the frame literal.
An atomic body did not expose the missing return through the same stack path.

## Existing mechanism and repair

The existing infix lexical fork already emitted a return when precedence excluded every primary operator.
It also retained a return at a required collection delimiter.
The repair extends the first condition to every primary token without an admitted operator.
It preserves the collection condition, operator branches, weights, token targets, and branch order.
The repair changes `prattail/src/wpda_transitions/lexical_fork.rs`.
It introduces no grammar-specific delimiter table or parser generator.

The transition uses this procedure:

1. Collect admitted primary operator branches with the existing rule table.
2. Append one return if no primary operator survives or the collection context requires a delimiter return.
3. Append admitted secondary operator branches with their original token targets.
4. Use the existing single-primary fast path when no fork is necessary.

The return uses the current source category and input position.
An admitted primary operator still controls precedence unless the existing collection condition requires a return.
The repair does not reinterpret every secondary token without an operator as an expression boundary.

## Formal model and property mapping

`formal/rocq/prattail_wpda_runtime/theories/LexicalInfixReturn.v` models the ordered transition branches.
The operator payload is arbitrary, so preservation includes all payload fields rather than a selected rule identifier.
The model proves transition composition. It does not claim a proof of every parser or grammar behavior.

The implementation property `infix_return_preserves_primary_boundary_and_operator_edges` checks 128 generated cases.
Each case checks the supplied primary table and an empty primary table.
Each case also checks absent, primary, secondary, and unrelated collection delimiters.
The generated tables cover infix, postfix, and mixfix operators, precedence floors, categories, rule identifiers, and token targets.

| Formal result | Implementation observation |
|---|---|
| `operator_branches_are_unchanged` | The complete ordered operator sequence matches the admitted primary and secondary rules |
| `return_branch_is_exact` | A return exists exactly when the primary table admits no operator or the collection delimiter matches |
| `nonoperator_primary_keeps_return` | Every empty-primary case retains the return |
| `admitted_primary_keeps_precedence` | An admitted primary without a matching delimiter adds no return |
| `structural_return_remains_available` | Both primary and secondary collection delimiters retain the existing return |
| `at_most_one_return` | Each dispatch contains zero or one return |
| `return_preserves_source_and_position` | The return retains the source category and uses nonconsuming `Advance(Unwinding)` |
| `operator_membership_is_exact` | No admitted operator is missing and no other operator appears |
| `missing_primary_return_counterexample` | An empty primary table retains a return alongside admitted secondary operators |

The property also checks each operator's weight, token target, category, precedence, and continuation state.
The model compile and independent kernel check must pass without axioms or unsafe features.

## Parser checks

`macros/tests/compound_frame_terminator.rs` declares an independent grammar with a compound closer and a colliding operator.
Its fixed cases check an atomic body, an infix body, prefix nesting, and whitespace variants.
Its property checks 64 recursive trees with comparisons, remainder expressions, and nested frames.
Both parser entries must preserve the expected complete tree.
Malformed frame cases must fail through both entries.

`languages/tests/rholang_cost_syntax.rs` retains the original signed-term witnesses.
The nested cases check a signed equality inside a hash and inside an integer expression.
These checks compare complete trees through both parser entries.
