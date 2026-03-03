# G03: ambiguous-prefix

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects multiple non-infix, non-var, non-literal rules within the same category that share the same first terminal token. When the parser encounters this token at a prefix position (the start of an expression), it cannot deterministically choose which rule to apply using a single token of lookahead. This creates an ambiguity that either requires WFST weight-based disambiguation, multi-token lookahead, or grammar restructuring to resolve. Without disambiguation, the parser will attempt the first matching rule in declaration order, which may not be the intended parse.

## Trigger Conditions

A warning is emitted when **all** of the following hold:

1. Two or more rules in the same category are **non-infix** (not handled by the Pratt infix loop), **non-var** (not variable/identifier rules), and **non-literal** (not native literal rules).
2. These rules share at least one common terminal token in their FIRST items (the set of terminals that can begin a parse of that rule).
3. The shared token maps to more than one rule label.

Infix rules are excluded because they are dispatched by the Pratt parser's infix loop after the left operand is parsed -- their operator token is not a prefix ambiguity. Variable and literal rules are excluded because they are dispatched by token type (identifier, integer, string, etc.) rather than by a specific terminal string.

## Example

### Grammar

```
language! {
    name: AmbiguousLambda,
    types {
        Term
    },
    terms {
        // Both rules start with "let" — ambiguous prefix dispatch
        LetVal . ^x.body:[Term -> Term], val:Term
            |- "let" x "=" val "in" body : Term;

        LetRec . ^f.body:[Term -> Term], ^x.rhs:[Term -> Term]
            |- "let" "rec" f x "=" rhs "in" body : Term;

        // These do NOT cause ambiguity with the above:
        App . fun:Term, arg:Term |- "(" fun arg ")" : Term;
        Lam . ^x.body:[Term -> Term] |- "lam" x "." body : Term;
    },
}
```

When the parser sees the token `"let"`, it cannot distinguish between `LetVal` and `LetRec` with a single token of lookahead. The second token (`"rec"` vs an identifier) resolves the ambiguity, but PraTTaIL's prefix dispatch operates on the first terminal.

### Output

```
warning[G03]: ambiguous prefix dispatch for token `let` in category `Term`: rules [LetVal, LetRec] all match
  = in category `Term`
  = hint: add unique dispatch tokens or use WFST weights to disambiguate
```

## Resolution

There are three primary strategies to resolve a G03 warning:

1. **Add unique dispatch tokens.** Give each rule a distinct first terminal so the parser can dispatch deterministically:
   ```
   LetVal . ^x.body:[Term -> Term], val:Term
       |- "let" x "=" val "in" body : Term;

   LetRec . ^f.body:[Term -> Term], ^x.rhs:[Term -> Term]
       |- "letrec" f x "=" rhs "in" body : Term;
   ```

2. **Use WFST weights to disambiguate.** If both rules must share the `"let"` prefix (e.g., for language compatibility), rely on the prediction WFST to assign different weights based on multi-token context. The WFST framework performs lookahead beyond the first token to break ties. This approach works automatically when the grammar has NFA spillover categories, but check for W02 and W03 warnings to confirm disambiguation quality.

3. **Left-factor the grammar.** Extract the common prefix into a shared rule and branch on the distinguishing token:
   ```
   LetExpr . binding:LetBinding, body:Term
       |- "let" binding "in" body : Term;

   // In a separate category:
   ValBinding . ^x.val:[Term -> Term]
       |- x "=" val : LetBinding;
   RecBinding . ^f.^x.rhs:[Term -> Term -> Term]
       |- "rec" f x "=" rhs : LetBinding;
   ```

## Hint Explanation

The hint "add unique dispatch tokens or use WFST weights to disambiguate" describes the two fundamental disambiguation mechanisms in PraTTaIL. Adding unique dispatch tokens is the simplest and most efficient solution: each prefix rule starts with a distinct terminal, enabling O(1) dispatch via a token match. WFST weight disambiguation is the alternative when shared prefixes are a language requirement -- the prediction WFST examines the input beyond the first token and assigns weights to candidate rules, selecting the highest-weighted (lowest-cost) parse. Left-factoring (restructuring the grammar to extract the common prefix) is a grammar-level transformation that achieves the same effect as unique dispatch tokens by pushing the ambiguity into a sub-category.

## Related Lints

- [G01](./G01-left-recursion.md) -- a left-recursive rule that is restructured into prefix form may introduce new ambiguous prefixes if the chosen dispatch token collides with existing rules
- [W02](../wfst/W02-nfa-ambiguous-prefix.md) -- the WFST-level counterpart of this lint, detecting ambiguity specifically in NFA spillover categories where weight-based disambiguation is active
- [W03](../wfst/W03-high-ambiguity-token.md) -- fires when a single token dispatches to 3 or more rules, a more severe form of prefix ambiguity that may degrade parse performance
