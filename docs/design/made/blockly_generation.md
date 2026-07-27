# Blockly Block Generation from Theory Definitions

**Status:** Design Phase  
**Created:** 2025-01-04  
**Goal:** Generate Blockly visual editor block definitions directly from MeTTaIL theory macros

---

## Overview

Currently, the MeTTaIL `theory!` macro generates:
- Rust AST types (enums with variants)
- LALRPOP parsers
- Ascent-based rewrite engines
- Display, substitution, and term generation

We want to add **Blockly block definition generation** to enable visual programming interfaces for any theory defined in MeTTaIL.

### Motivation

The OSLF-editor team is building a visual editor for Rholang using Blockly. Currently, they manually define blocks. This creates:
- **Duplication**: Same language structure defined twice (in theory macro + Blockly definitions)
- **Drift risk**: Changes to theory don't automatically propagate to editor
- **Manual effort**: Each constructor requires handwritten TypeScript

By generating Blockly definitions from the theory macro, we achieve:
- **Single source of truth**: Theory definition drives both runtime and editor
- **Consistency**: Editor always matches current theory structure
- **Automation**: New constructors automatically get editor support
- **Poly-lingual editors**: Any theory gets a visual editor for free

---

## Design Principles

### 1. One Constructor → One Block

Each constructor in the theory should map to exactly one Blockly block.

**Example:** 
```rust
PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
```

Should generate ONE block `proc_input`, not separate blocks for `proc_for` and `linear_bind`.

**Note:** The OSLF-editor currently has separate blocks for binding constructs (like `linear_bind`) that are used in multiple contexts. For simpler theories like Rholang, we'll generate one block per constructor as specified in the theory.

### 2. Block Structure Mirrors AST Structure

The fields of a block should correspond to the non-terminal arguments of the constructor.

**Example:**
```rust
POutput . Proc ::= Name "!" "(" Proc ")" ;
```

Has two non-terminal arguments:
1. `Name` (the channel)
2. `Proc` (the message)

Should generate:
```typescript
{
    type: "proc_output",
    tooltip: "Send: channel!(message)",
    message0: "%1 ! ( %2 )",
    args0: [
        {
            type: "input_value",
            name: "CHANNEL",
            check: "Name",
        },
        {
            type: "input_value", 
            name: "MESSAGE",
            check: "Proc",
        },
    ],
    inputsInline: true,
    previousStatement: "Proc",  // or output: "Proc" depending on context
    nextStatement: "Proc",
    colour: "208bfe",
}
```

### 3. Respect Category Semantics

- **Terminals** (`"for"`, `"!"`, etc.) appear as literal text in `message0`
- **Non-terminals** (`Name`, `Proc`) become input fields with type checking
- **Binders** (`<Name>`) indicate scope/binding but become input fields in Blockly
- **Collections** (`HashBag(Proc)`) need special handling (see below)
- **Variables** (`Var`) become text input fields

### 4. Block Connection Types

Based on the **category** of a constructor:

- **Process blocks** (`Proc`): Use statement connections (`previousStatement`/`nextStatement`) for imperative constructs, or value outputs (`output: "Proc"`) for expressions
- **Name blocks** (`Name`): Use value outputs (`output: "Name"`)
- **Other categories**: Use value outputs (`output: "<Category>"`)

**Heuristic for statement vs value:**
- Constructors with side effects or sequencing (e.g., `PInput`, `POutput`, `PPar`) → statements
- Constructors that produce values (e.g., `NQuote`, `PVar`) → value outputs
- This can be inferred or explicitly annotated in the theory

---

## Technical Approach

### Phase 1: Generate Static Block Definitions

Add a new code generation module: `macros/src/codegen/blockly.rs`

This module will:
1. Take a `TheoryDef` as input
2. For each `GrammarRule` (constructor), generate a Blockly block definition
3. Output TypeScript code to a file (e.g., `theories/src/generated/<theory>-blocks.ts`)

### Phase 2: Integration with Theory Macro

Update `macros/src/lib.rs` to call the Blockly generator:

```rust
#[proc_macro]
#[proc_macro_error]
pub fn theory(input: TokenStream) -> TokenStream {
    let theory_def = parse_macro_input!(input as TheoryDef);
    
    // ... existing validation and generation ...
    
    // NEW: Generate Blockly definitions
    let blockly_defs = generate_blockly_definitions(&theory_def);
    if let Err(e) = write_blockly_file(&theory_def.name.to_string(), &blockly_defs) {
        eprintln!("Warning: Failed to write Blockly definitions: {}", e);
    }
    
    // ... existing code generation ...
}
```

### Phase 3: Category Information Export

To support the editor, we also need to export category information as a TypeScript module:

```typescript
// Generated: theories/src/generated/rholang-categories.ts
export const categoryInfo = {
    Proc: {
        constructors: ["PZero", "PDrop", "POutput", "PInput", "PPar"],
        colour: "208bfe"
    },
    Name: {
        constructors: ["NQuote", "NVar"],
        colour: "65cda8"
    }
};
```

This allows the editor to:
- Validate block connections
- Apply consistent colors
- Generate toolbox categories

---

## Implementation Details

### Mapping Grammar Items to Blockly Fields

| Grammar Item | Blockly Field |
|--------------|---------------|
| `Terminal(s)` | Literal text in `message0` |
| `NonTerminal(Cat)` | `input_value` with `check: "Cat"` |
| `Binder { category: Cat }` | `input_value` with `check: "Cat"`, special tooltip |
| `Collection { ... }` | See "Collection Handling" below |
| `Var` (pseudo-constructor) | `field_input` with text entry |

### Block Naming Convention

Constructor label → Block type identifier:

- **Convention**: `snake_case` version of the label, with category prefix
  - `POutput` → `proc_output`
  - `NQuote` → `name_quote`
  - `PZero` → `proc_zero`
  
- **Rule**: Lowercase the label, insert underscores before capital letters after the category prefix

### Argument Naming Convention

Arguments are named based on their semantic role:

- First `Name` argument → `CHANNEL` (if output/input context)
- First `Proc` argument → `BODY` (if in binding context)
- Second `Proc` argument → `CONTINUATION` or `MESSAGE`
- Generic fallback → `ARG0`, `ARG1`, etc.

Better approach: Allow **optional field name annotations** in the theory:

```rust
// Future enhancement
POutput . Proc ::= Name@channel "!" "(" Proc@message ")" ;
```

For now, use heuristics based on position and category.

### Collection Handling

Collections (`HashBag`, `HashSet`, `Vec`) need special handling because they:
1. Can have variable-length contents
2. Use separators and delimiters
3. May have rest patterns (`...rest`)

**Phase 1 approach**: Generate collections as **statement blocks with nested blocks**

Example for `PPar`:
```rust
PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
```

Generate:
```typescript
{
    type: "proc_par",
    tooltip: "Parallel composition: { P | Q | ... }",
    message0: "{ %1 }",
    args0: [
        {
            type: "input_statement",
            name: "PROCESSES",
            check: "Proc",
        },
    ],
    previousStatement: "Proc",
    nextStatement: "Proc",
    colour: "208bfe",
}
```

Users nest multiple `Proc` blocks inside using statement connections. Each `Proc` block can connect to the next via `nextStatement`, allowing any number of processes.

**Note**: The separator (`|`) won't be visually rendered in the same way as textual syntax, but the semantic structure (multiple parallel processes) is preserved. This is a reasonable tradeoff for Phase 1.

**Future enhancement**: Custom Blockly field or extension that visually renders separators between items (more complex, deferred to later phases).

### Binding Handling

Binders (`<Name>`) in the grammar indicate lexical scope:

```rust
PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
                                        ^^^^^         ^^^^
                                        binder      scope
```

In Blockly (Phase 1):
- The binder becomes a **text input field** (since it's declaring a new name)
- The scope receives that name implicitly (Blockly doesn't natively enforce scoping)
- No visual distinction from regular text fields

Generated block:
```typescript
{
    type: "proc_input",
    message0: "for ( %1 -> %2 ) { %3 }",
    args0: [
        {
            type: "input_value",
            name: "CHANNEL",
            check: "Name",
        },
        {
            type: "field_input",  // Binder becomes text input
            name: "VAR",
            text: "x",
        },
        {
            type: "input_statement",
            name: "BODY",
            check: "Proc",
        },
    ],
    // ...
}
```

**Current OSLF-editor status**: The editor does NOT currently distinguish binders visually. They are treated as regular text input fields, same as variable references.

**Future enhancement (Stage 3)**: 
- Add visual distinction (e.g., different color, icon)
- Generate variable dropdown fields that list bound names in scope
- Scope-aware validation
- Custom Blockly field type for binders

### Color Assignment

Each category gets a consistent color:

- Hash the category name to a hue value
- Use consistent saturation/brightness
- Or use explicit color mapping:

```rust
// In theory definition (future)
exports {
    Proc@color("#208bfe")
    Name@color("#65cda8")
}
```

For now, generate colors deterministically from category name.

### Tooltip Generation

Tooltips should be informative and concise:

1. Use the **display format** from terminals
2. Add a brief description based on the constructor label

Example:
```rust
POutput . Proc ::= Name "!" "(" Proc ")" ;
```

Tooltip: `"Send: channel!(message)"`

Strategy:
- Extract the "shape" from terminals
- Convert label to human-readable text (POutput → "Send", NQuote → "Quote")
- Combine into tooltip

### Message Format String Generation

The `message0` field is a template string where `%1`, `%2`, etc. are replaced by arguments.

Algorithm:
1. Iterate through `GrammarRule.items`
2. For terminals, add literal text
3. For non-terminals/binders, add `%N` where N is the argument index (1-based)
4. Handle spacing and punctuation

Example:
```rust
PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
```

Items: `["for", "(", Name, "->", <Name>, ")", "{", Proc, "}"]`

Message: `"for ( %1 -> %2 ) { %3 }"`

Arguments:
1. `Name` (CHANNEL)
2. `<Name>` (VAR)
3. `Proc` (BODY)

### Output vs Statement Blocks

**Heuristic to determine connection type:**

- **Value blocks** (use `output: "Category"`):
  - Constructors that represent values/expressions
  - Examples: `NQuote`, `NVar`, `PVar`, `PDrop`
  
- **Statement blocks** (use `previousStatement`/`nextStatement`):
  - Constructors that represent actions/side effects
  - Examples: `PInput`, `POutput`, `PPar`
  
- **Hybrid blocks** (have both output and statement):
  - Rare, but some blocks can be both
  - Example: `POutput` could be used as a value (in `PPar`) or as a statement

**Decision**: Start with **all Proc blocks as statements** for consistency. Can refine later based on usage patterns.

**Exception**: `PVar`, `PZero` should be value blocks since they're leaves.

---

## File Organization

### Generated Files

For each theory (e.g., `Rholang`):

1. **Block definitions**: `theories/src/generated/rholang-blocks.ts`
   - Exports block definitions array
   - One file per theory

2. **Category metadata**: `theories/src/generated/rholang-categories.ts`
   - Exports category information (constructors, colors)
   - Used by editor for validation and theming

3. **Toolbox configuration**: `theories/src/generated/rholang-toolbox.ts`
   - Exports toolbox structure
   - Groups blocks by category

### Integration with OSLF-editor

The OSLF-editor can import generated blocks:

```typescript
// In OSLF-editor/editor/src/blocks/generated/index.ts
import rholangBlocks from "@mettail/theories/generated/rholang-blocks";
import ambientBlocks from "@mettail/theories/generated/ambient-blocks";

export { rholangBlocks, ambientBlocks };
```

Or copy generated files into the editor project during build.

---

## Example: Rholang Theory

### Input Theory Definition

```rust
theory! {
    name: Rholang,
    
    exports {
        Proc
        Name
    },
    
    terms {
        PZero . Proc ::= "0" ;
        PDrop . Proc ::= "*" "(" Name ")" ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
        NQuote . Name ::= "@" "(" Proc ")" ;
        PVar . Proc ::= Var;
        NVar . Name ::= Var;
    },
    
    equations {
        (NQuote (PDrop N)) == N ;
    },
    
    rewrites {
        (PPar {(PInput N x P), (POutput N Q)})
            => (PPar {(subst P x (NQuote Q))});
        
        (PDrop (NQuote P)) => P;

        if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest});
    },
}
```

### Generated Output (Excerpt)

**File**: `theories/src/generated/rholang-blocks.ts`

```typescript
import * as Blockly from "blockly/core";

// Generated Blockly blocks for Rholang theory
// DO NOT EDIT - generated by MeTTaIL theory! macro

const definitions = [
    // PZero - Zero process
    {
        type: "proc_zero",
        tooltip: "Zero process: 0",
        message0: "0",
        output: "Proc",
        colour: "208bfe",
    },
    
    // PDrop - Dereference name to process
    {
        type: "proc_drop",
        tooltip: "Dereference: *(name)",
        message0: "* ( %1 )",
        args0: [
            {
                type: "input_value",
                name: "NAME",
                check: "Name",
            },
        ],
        inputsInline: true,
        output: "Proc",
        colour: "208bfe",
    },
    
    // POutput - Send message on channel
    {
        type: "proc_output",
        tooltip: "Send: channel!(message)",
        message0: "%1 ! ( %2 )",
        args0: [
            {
                type: "input_value",
                name: "CHANNEL",
                check: "Name",
            },
            {
                type: "input_value",
                name: "MESSAGE",
                check: "Proc",
            },
        ],
        inputsInline: true,
        previousStatement: "Proc",
        nextStatement: "Proc",
        colour: "208bfe",
    },
    
    // PInput - Receive message from channel
    {
        type: "proc_input",
        tooltip: "Receive: for(channel->var){body}",
        message0: "for ( %1 -> %2 ) { %3 }",
        args0: [
            {
                type: "input_value",
                name: "CHANNEL",
                check: "Name",
            },
            {
                type: "field_input",
                name: "VAR",
                text: "x",
            },
            {
                type: "input_statement",
                name: "BODY",
                check: "Proc",
            },
        ],
        previousStatement: "Proc",
        nextStatement: "Proc",
        colour: "208bfe",
    },
    
    // PPar - Parallel composition
    {
        type: "proc_par",
        tooltip: "Parallel composition: { P | Q | ... }",
        message0: "{ %1 }",
        args0: [
            {
                type: "input_statement",
                name: "PROCESSES",
                check: "Proc",
            },
        ],
        previousStatement: "Proc",
        nextStatement: "Proc",
        colour: "208bfe",
    },
    
    // NQuote - Quote process as name
    {
        type: "name_quote",
        tooltip: "Quote: @(process)",
        message0: "@ ( %1 )",
        args0: [
            {
                type: "input_value",
                name: "PROCESS",
                check: "Proc",
            },
        ],
        inputsInline: true,
        output: "Name",
        colour: "65cda8",
    },
    
    // PVar - Process variable
    {
        type: "proc_var",
        tooltip: "Process variable",
        message0: "%1",
        args0: [
            {
                type: "field_input",
                name: "VAR",
                text: "P",
            },
        ],
        output: "Proc",
        colour: "208bfe",
    },
    
    // NVar - Name variable
    {
        type: "name_var",
        tooltip: "Name variable",
        message0: "%1",
        args0: [
            {
                type: "field_input",
                name: "VAR",
                text: "x",
            },
        ],
        output: "Name",
        colour: "65cda8",
    },
];

export default Blockly.common.createBlockDefinitionsFromJsonArray(definitions);
```

**File**: `theories/src/generated/rholang-categories.ts`

```typescript
// Generated category metadata for Rholang theory
export const categoryInfo = {
    Proc: {
        constructors: [
            "PZero",
            "PDrop", 
            "POutput",
            "PInput",
            "PPar",
            "PVar",
        ],
        colour: "208bfe",
    },
    Name: {
        constructors: [
            "NQuote",
            "NVar",
        ],
        colour: "65cda8",
    },
};

export const theoryName = "Rholang";
```

**File**: `theories/src/generated/rholang-toolbox.ts`

```typescript
// Generated toolbox configuration for Rholang theory
export const toolboxConfig = {
    kind: "categoryToolbox",
    contents: [
        {
            kind: "category",
            name: "Processes",
            colour: "208bfe",
            contents: [
                { kind: "block", type: "proc_zero" },
                { kind: "block", type: "proc_drop" },
                { kind: "block", type: "proc_output" },
                { kind: "block", type: "proc_input" },
                { kind: "block", type: "proc_par" },
                { kind: "block", type: "proc_var" },
            ],
        },
        {
            kind: "category",
            name: "Names",
            colour: "65cda8",
            contents: [
                { kind: "block", type: "name_quote" },
                { kind: "block", type: "name_var" },
            ],
        },
    ],
};
```

## Implementation Plan

### Stage 1: Basic Block Generation ✅ (This Design)

- Generate block definitions for simple constructors
- Handle terminals, non-terminals, and variables
- Basic collection support (statement-based nesting)
- Output TypeScript files
- Basic color assignment

**Deliverables:**
- `macros/src/codegen/blockly.rs` - Core generator
- `macros/src/codegen/blockly/builder.rs` - Block building logic
- Generated files: `<theory>-blocks.ts`, `<theory>-categories.ts`

**Collection handling in Stage 1:**
- `HashBag`, `HashSet`, `Vec` → `input_statement` fields
- Allows any number of child blocks via statement connections
- Separators not visually rendered (acceptable for Phase 1)

### Stage 2: Enhanced Collection Support

- Visual rendering of separators between items
- Support rest patterns (`...rest`) in collection matching
- Custom Blockly field/extension for better collection UX

**Challenge:** Blockly doesn't natively support multi-item collections with custom separators. Will require custom field implementation or extension plugin.

**Note:** Stage 1 already provides functional collection support (statement nesting); Stage 2 improves the visual presentation.

### Stage 3: Binding and Scope Support

- Distinguish binders from regular inputs
- Generate variable dropdown fields
- Scope-aware validation (optional, advanced)

### Stage 4: Toolbox Generation

- Generate organized toolbox by category
- Include default shadows for common patterns
- Sort blocks logically

### Stage 5: Code Generator (Blockly → Theory AST)

- Generate code that converts Blockly workspace to theory AST
- Bidirectional: Parse theory syntax to create Blockly workspace
- Enable round-tripping between visual and textual representations

### Stage 6: Advanced Features

- Custom block shapes (e.g., for binders)
- Inline input vs external input heuristics
- Custom block colors via annotations
- Multi-language support (generate for multiple Blockly locales)

---

## Design Decisions & Answers to Key Questions

### Q1: How to handle language-specific constructs?

**Decision:** Generate blocks for ALL constructors in the theory. The theory is the single source of truth. If a theory includes arithmetic operators, they get blocks. We're using simpler theories than full Rholang.

### Q2: Single file or multiple files?

**Decision:** Single file per theory for all blocks. Simple and maintainable for theories with reasonable numbers of constructors (< 50).

### Q3: Constructor naming across theories

**Decision:** Prefix block types with theory name in lowercase:
- `rholang_proc_var` vs `ambient_proc_var`

This avoids collisions when multiple theories are used in the same editor.

### Q4: Versioning strategy

**Decision:** No versioning tracking initially. Generated files include a warning comment that they're auto-generated. If theories change, blocks regenerate. Good enough for current development phase.

### Q5: Custom block annotations

**Decision:** Deferred to future. Use convention-based generation for Phase 1. Can add `#[block(...)]` attributes later if needed.

### Q6: Variable pseudo-constructors

**Decision:** Generate simple text input blocks:
```typescript
{
    type: "proc_var",
    message0: "%1",
    args0: [{ type: "field_input", name: "VAR", text: "P" }],
    output: "Proc",
}
```

### Q7: Equation and rewrite visualization

**Decision:** Deferred to future. Focus on term constructors only for Phase 1. Visualizing rewrites would be a meta-editor feature.

---

## Success Criteria

This design is successful when:

1. ✅ **Automated generation**: Blocks are generated automatically from theory definitions
2. ✅ **Correctness**: Generated blocks correctly represent theory constructors (1:1 mapping)
3. ✅ **Type safety**: Block connections enforce category types from theory
4. ✅ **Consistency**: All theories get consistent block generation
5. ✅ **Integration**: Generated blocks work in existing OSLF-editor
6. ✅ **Maintainability**: Changes to theory immediately reflect in editor

**Validation:**
- Generate blocks for `Rholang` and `Ambient` theories
- Import into OSLF-editor and verify they work
- Compare with hand-written Rholang blocks in OSLF-editor
- Ensure no manual editing of generated files is needed

---

## Verification Against OSLF-Editor

### Current OSLF-Editor Structure

Based on review of the existing editor:

1. **Grammar source**: The OSLF-editor blocks are manually written based on `rholang.cf` (a BNFC grammar file with 276 lines defining full Rholang). Our generated blocks will be based on MeTTaIL theory definitions instead.

2. **Block organization**: Blocks are organized by semantic category (processes, names, receipts, collections, control, declarations, ground types)

3. **PPar implementation**: Currently uses a **binary operator** approach with LEFT and RIGHT statement inputs:
   ```typescript
   // Current OSLF-editor approach
   message0: "%1 | %2",
   args0: [
       { type: "input_statement", name: "LEFT", check: "Proc" },
       { type: "input_statement", name: "RIGHT", check: "Proc" }
   ]
   ```
   Our Phase 1 will use a single statement input that allows any number of processes to chain:
   ```typescript
   // Our generated approach
   message0: "{ %1 }",
   args0: [
       { type: "input_statement", name: "PROCESSES", check: "Proc" }
   ]
   ```
   This is functionally equivalent (blocks chain via `nextStatement`) and simpler to generate.

4. **Binder handling**: The editor does NOT currently distinguish binders visually. They're treated as regular text fields, same as our Phase 1 approach.

5. **Connection types**: Mix of statement blocks (for imperative constructs) and value blocks (for expressions), which aligns with our design.

6. **Type checking**: Uses the `check` field extensively to enforce category constraints, matching our approach.

7. **Color scheme**: Uses hexadecimal color codes (e.g., "208bfe" for Proc, "65" for Name). We'll generate similar deterministic colors.

### Compatibility Confirmation

✅ **PPar with statement nesting**: Yes, Blockly statement connections allow any number of blocks to chain together, which suffices for Phase 1.

✅ **Binder distinction**: No, the editor doesn't currently distinguish binders. Our Phase 1 approach (text input fields) matches the current editor behavior.

✅ **Integration path**: Generated blocks will follow the same structure as hand-written OSLF blocks, making integration straightforward.

## Next Steps

1. ✅ **Design review complete** - Verified against existing OSLF-editor
2. **Implement Stage 1**: Basic block generation
   - Create `macros/src/codegen/blockly.rs`
   - Add file writing infrastructure
   - Generate for Rholang as proof-of-concept
3. **Validate**: Import generated blocks into OSLF-editor and test
4. **Iterate**: Handle edge cases, refine heuristics
5. **Document**: Update README with block generation feature

---

## References

- **Blockly Documentation**: https://developers.google.com/blockly/guides/create-custom-blocks/define-blocks
- **MeTTaIL README**: `/Users/cbwells/Documents/GitHub/mettail-rust/README.md`
- **Theory AST Types**: `/Users/cbwells/Documents/GitHub/mettail-rust/macros/src/ast/types.rs`
- **OSLF-editor Blocks**: `/Users/cbwells/Documents/GitHub/mettail-rust/OSLF-editor/editor/src/blocks/`
- **Existing Code Generation**: `/Users/cbwells/Documents/GitHub/mettail-rust/macros/src/codegen/`

---

## Appendix: TypeScript Type Definitions

To improve type safety in generated code, we can also generate TypeScript type definitions:

```typescript
// Generated: theories/src/generated/rholang-types.ts

export type ProcBlockType = 
    | "proc_zero"
    | "proc_drop"
    | "proc_output"
    | "proc_input"
    | "proc_par"
    | "proc_var";

export type NameBlockType =
    | "name_quote"
    | "name_var";

export type RholangBlockType = ProcBlockType | NameBlockType;

// Field definitions for type-safe block access
export interface ProcOutputFields {
    CHANNEL: string;  // Name block ID
    MESSAGE: string;  // Proc block ID
}

export interface ProcInputFields {
    CHANNEL: string;  // Name block ID
    VAR: string;      // Text field value
    BODY: string;     // Proc statement ID
}

// ... etc.
```

This enables type-safe code generation and editor integration.

---

**End of Design Document**

