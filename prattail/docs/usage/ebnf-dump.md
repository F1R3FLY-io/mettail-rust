# EBNF Debug Dump

PraTTaIL can produce an annotated EBNF representation of each language's grammar,
providing a human-readable intermediate view that was previously available only through
the now-removed LALRPOP `.lalrpop` files.

## Purpose

The EBNF dump is useful for:

- **Debugging grammar definitions** — verify that the DSL is being interpreted as intended
- **Understanding precedence** — see the exact binding power assignments for all operators
- **Inspecting FIRST/FOLLOW sets** — verify parse dispatch decisions
- **Documentation** — generate readable grammar references for language users
- **Regression detection** — diff EBNF output across versions to catch unintended changes

## Activation

Set the `PRATTAIL_DUMP_EBNF` environment variable before building or testing:

```bash
# Write to target/prattail/<Name>.ebnf (default location)
PRATTAIL_DUMP_EBNF=1 cargo test -p mettail-languages

# Write to a custom directory
PRATTAIL_DUMP_EBNF=docs/grammars cargo test -p mettail-languages

# Works with any cargo command that triggers macro expansion
PRATTAIL_DUMP_EBNF=1 cargo build -p mettail-languages
```

The dump runs during proc-macro expansion (at compile time), so it produces output
for every `language! { ... }` invocation that gets compiled.

## Output Location

| `PRATTAIL_DUMP_EBNF` value | Output path                   |
|----------------------------|-------------------------------|
| `1`                        | `target/prattail/<Name>.ebnf` |
| `<directory>`              | `<directory>/<Name>.ebnf`     |

The directory is created automatically if it doesn't exist. Progress is reported to stderr:

```
info: PRATTAIL_DUMP_EBNF: wrote target/prattail/Calculator.ebnf
info: PRATTAIL_DUMP_EBNF: wrote target/prattail/Ambient.ebnf
```

## Format Reference

The output uses ISO 14977 EBNF conventions with practical extensions.

### Productions

```ebnf
Cat = alternative1
    | alternative2
    | alternative3
    ;
```

- `=` introduces a production
- `|` separates alternatives
- `;` terminates
- Juxtaposition for concatenation (no `,` — avoids conflict with literal commas)

### Terminal Strings

Quoted with double quotes:

```ebnf
"+" "-" "==" "lam " "(" ")"
```

### Special Tokens

Angle brackets for parameterized token classes:

| Token | Meaning |
|---|---|
| `<integer>` | Integer literal: `digit, { digit }` |
| `<float>` | Float literal: `digit, { digit }, ".", digit, { digit }` |
| `<boolean>` | Boolean literal: `"true" \| "false"` |
| `<string>` | String literal (double-quoted with escapes) |
| `<ident>` | Identifier: `letter \| "_", { letter \| digit \| "_" }` |

### Optional Groups

Square brackets for `#opt(...)` groups:

```ebnf
"if" Int [ "else" Int ]
```

### Collections

Curly braces with separator and kind annotation:

```ebnf
"{" { Proc / "|" }  (* HashBag *) "}"
"[" { Int / "," }   (* Vec *)     "]"
```

The `(* HashBag *)`, `(* HashSet *)`, or `(* Vec *)` comment indicates the
collection type used in the AST.

### ZipMapSep

Same curly-brace notation with inline body pattern:

```ebnf
"(" { Name "?" ^xs:Proc / "," } ")" "." "{" Proc "}"
```

### Binders

Caret prefix with type annotation:

```ebnf
^x:Term        (* single binder *)
^xs:Proc       (* binder in ZipMapSep *)
```

### Annotations

Every alternative has a comment annotation:

```ebnf
Int = <integer>                       (* NumLit *)
    | <ident>                         (* IVar *)
    | "(" Int ")"                     (* group *)
    | "-" Int                         (* Neg — prefix bp=13 *)
    | Int "+" Int                     (* Add — (6, 7) *)
    | Int "^" Int                     (* Pow — (5, 4) — right *)
    | Int "?" Int ":" Int             (* Tern — (3, 2) — right — mixfix *)
    | Int "!"                         (* Fact — postfix bp=15 *)
    | Int "==" Int                    (* Eq — cross Int → Bool *)
    | "|" Str "|"                     (* Len — cast Str → Int *)
    ;
```

| Annotation | Meaning |
|---|---|
| `(* Label *)` | Constructor name |
| `(* Label — (L, R) *)` | Infix with binding power pair (left_bp, right_bp) |
| `(* Label — (L, R) — right *)` | Right-associative infix |
| `(* Label — (L, R) — right — mixfix *)` | Right-associative mixfix (ternary, etc.) |
| `(* Label — prefix bp=N *)` | Unary prefix with binding power N |
| `(* Label — postfix bp=N *)` | Postfix with left binding power N |
| `(* Label — cast Src → Tgt *)` | Cast rule (parse Src, wrap as Tgt) |
| `(* Label — cross Src → Tgt *)` | Cross-category infix (operands from Src, result in Tgt) |
| `(* Label — binder *)` | Rule with variable binder(s) |
| `(* group *)` | Parenthesized grouping |

### Precedence Tables

Each category with operators includes a precedence table:

```ebnf
(* ── Precedence Table: Int ───────────────────────────── *)
(*                                                       *)
(*  BP       Assoc  Op       Label        Kind            *)
(*  ───────  ─────  ──       ─────        ────            *)
(*  (3, 2)  right  ? :      Tern         mixfix      *)
(*  (5, 4)  right  ^        Pow          infix       *)
(*  (6, 7)  left   +        Add          infix       *)
(*  (8, 9)  left   -        Sub          infix       *)
(*  prefix   ─       -        Neg          bp = 13      *)
(*  postfix  ─       !        Fact         bp = 15      *)
```

**Reading binding powers:**
- `(L, R)` where `L < R` means left-associative (`a + b + c` = `(a + b) + c`)
- `(L, R)` where `L > R` means right-associative (`a ^ b ^ c` = `a ^ (b ^ c)`)
- Higher numbers bind tighter: `*` at `(4,5)` binds tighter than `+` at `(2,3)`
- Prefix operators have a single bp above all non-postfix infix operators
- Postfix operators have the highest bp (bind tightest)

### FIRST/FOLLOW Sets

Each category ends with computed FIRST and FOLLOW sets:

```ebnf
(* FIRST(Int)  = { <integer>, "-", "|" } *)
(* FOLLOW(Int) = { "&&", "!", "^", ":", EOF, "==", "-", "+", "?", "~" } *)
```

- **FIRST(C)**: tokens that can begin a C-expression (used for prefix dispatch)
- **FOLLOW(C)**: tokens that can appear immediately after a C-expression (used for error recovery sync points)

## Full Example: Calculator

```ebnf
(* ═════════════════════════════════════════════════════ *)
(*   Calculator — EBNF Grammar                            *)
(*   Generated by PraTTaIL                                *)
(* ═════════════════════════════════════════════════════ *)

(* ── Lexical Tokens ──────────────────────────────────── *)

<integer> = /[0-9]+/                        (* i32 *) ;
<boolean> = /true|false/             (* bool *) ;
<string>  = /"([^"\\]|\\.)*"/         (* str *) ;
<ident>   = /[a-zA-Z_][a-zA-Z0-9_]*/ ;

(* ── Precedence Table: Int ───────────────────────────── *)
(*                                                       *)
(*  BP       Assoc  Op       Label        Kind            *)
(*  ───────  ─────  ──       ─────        ────            *)
(*  (3, 2)  right  ? :      Tern         mixfix      *)
(*  (5, 4)  right  ^        Pow          infix       *)
(*  (6, 7)  left   +        Add          infix       *)
(*  (8, 9)  left   -        Sub          infix       *)
(*  (10, 11)  left   ~        CustomOp     infix       *)
(*  prefix   ─       -        Neg          bp = 13      *)
(*  postfix  ─       !        Fact         bp = 15      *)

(* ── Int (primary, native: i32) ─────────────────────────────── *)

Int = <integer>                           (* NumLit *)
    | <ident>                             (* IVar *)
    | "(" Int ")"                         (* group *)
    | "|" Str "|"                         (* Len *)
    | "-" Int                             (* Neg — prefix bp=13 *)
    | Int "?" Int ":" Int                 (* Tern — (3, 2) — right — mixfix *)
    | Int "^" Int                         (* Pow — (5, 4) — right *)
    | Int "+" Int                         (* Add — (6, 7) *)
    | Int "-" Int                         (* Sub — (8, 9) *)
    | Int "~" Int                         (* CustomOp — (10, 11) *)
    | Int "!"                             (* Fact — postfix bp=15 *)
    ;

(* FIRST(Int)  = { <integer>, "-", "|" } *)
(* FOLLOW(Int) = { "&&", "!", "^", ":", EOF, "==", "-", "+", "?", "~" } *)

(* ── Bool (native: bool) ─────────────────────────────── *)

Bool = <boolean>                          (* BoolLit *)
     | <ident>                            (* BVar *)
     | "(" Bool ")"                       (* group *)
     | Int "==" Int                       (* Eq — cross Int → Bool *)
     | Str "==" Str                       (* EqStr — cross Str → Bool *)
     | "not" Bool                         (* Not — prefix bp=7 *)
     | Bool "==" Bool                     (* EqBool — (2, 3) *)
     | Bool "&&" Bool                     (* Comp — (4, 5) *)
     ;

(* FIRST(Bool)  = { <boolean>, "not", "-", "|" } *)
(* FOLLOW(Bool) = { "&&", "==" } *)

(* ── Str (native: str) ─────────────────────────────── *)

Str = <string>                            (* StringLit *)
    | <ident>                             (* SVar *)
    | "(" Str ")"                         (* group *)
    | Str "++" Str                        (* Concat — (2, 3) *)
    | Str "+" Str                         (* AddStr — (4, 5) *)
    ;

(* FIRST(Str)  = { <string> } *)
(* FOLLOW(Str) = { "&&", "==", "|", "+", "++" } *)
```

## Full Example: Ambient (Binders + Collections)

```ebnf
(* ═════════════════════════════════════════════════════ *)
(*   Ambient — EBNF Grammar                               *)
(*   Generated by PraTTaIL                                *)
(* ═════════════════════════════════════════════════════ *)

(* ── Lexical Tokens ──────────────────────────────────── *)

<ident>   = /[a-zA-Z_][a-zA-Z0-9_]*/ ;

(* ── Proc (primary) ─────────────────────────────── *)

Proc = <ident>                            (* PVar *)
     | "(" Proc ")"                       (* group *)
     | "0"                                (* PZero *)
     | "in(" Name "," Proc ")"            (* PIn *)
     | "out(" Name "," Proc ")"           (* POut *)
     | "open(" Name "," Proc ")"          (* POpen *)
     | Name "[" Proc "]"                  (* PAmb *)
     | "new" "(" ^x:Proc "," Proc ")"    (* PNew — binder *)
     | "{" { Proc / "|" }  (* HashBag *) "}" (* PPar — HashBag *)
     ;

(* FIRST(Proc)  = { "0", "new", "{", "in(", "open(", "out(" } *)
(* FOLLOW(Proc) = { EOF, "|", "}", "]", ")" } *)
```
