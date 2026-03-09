# I10: ascent-file-write-failed

**Severity:** Warning
**Category:** infrastructure
**Feature Gate:** None (always enabled)

## Description

Warns that the generated Ascent Datalog source file could not be written to
disk. During macro expansion, the `language!` macro generates Ascent code
(relation declarations, category rules, equation rules, rewrite rules) and
attempts to write the formatted source to a file for inspection and debugging.
When this write fails, I10 fires with the underlying I/O error message.

The generated Ascent file is written to the `target/prattail/` directory by
default, using the grammar name and theory name to construct the filename.
This file is not required for compilation (the generated code is embedded
directly into the macro output), but it is valuable for debugging Ascent rule
interactions, verifying codegen optimizations, and understanding the semantic
evaluation structure.

```
  Ascent file write flow:

  ┌────────────────────────────┐
  │  language! { ... }         │
  │                            │
  │  Generate Ascent source:   │
  │    - relations             │
  │    - category rules        │
  │    - equation rules        │
  │    - rewrite rules         │
  │    - custom logic          │
  └────────────┬───────────────┘
               │
        format & write to disk
        ├── success -> continue
        └── failure -> emit I10 warning
                       continue (compilation proceeds)
```

Compilation is not affected by this failure -- the generated Ascent code is
embedded in the macro output regardless. The diagnostic serves as a notification
that the debug artifact is unavailable.

## Trigger Conditions

All of the following must hold:

- The `language!` macro completes Ascent source generation successfully.
- The call to `writer::write_ascent_file()` returns an `Err`.
- Common causes:
  - The `target/prattail/` directory does not exist and cannot be created.
  - File system permissions prevent writing to the target directory.
  - Disk is full.
  - Path contains invalid characters.

One diagnostic is emitted per failed write attempt.

## Example

### Scenario

The `target/` directory is on a read-only filesystem or the user lacks write
permissions.

### Output

```
warning[I10] (RhoCalc): failed to write Ascent Datalog file: Permission denied (os error 13)
  = hint: check directory permissions
```

## Resolution

1. **Check directory permissions.** Ensure the `target/prattail/` directory
   exists and is writable:

   ```bash
   mkdir -p target/prattail
   chmod u+w target/prattail
   ```

2. **Check disk space.** If the disk is full, free space or redirect the
   target directory to a filesystem with available capacity.

3. **Verify path validity.** If the grammar name contains characters that are
   invalid in file paths on the current operating system, rename the grammar
   to use only ASCII alphanumeric characters and underscores.

4. **Ignore the warning.** If you do not need the debug Ascent source file,
   this warning is harmless. Compilation proceeds regardless.

## Hint Explanation

The hint **"check directory permissions"** identifies the most common root cause:
file system permissions preventing the write. The Ascent source file is written
during macro expansion (at compile time), which runs under the same user account
and working directory as `cargo build`.

## Related Lints

- [I01](I01-transducer-cascade.md) -- Transducer cascade. Pipeline
  infrastructure diagnostics share the I-prefix category.
- [I18](I18-lint-cache-hit.md) -- Lint cache hit. Another infrastructure
  diagnostic related to file I/O (reading/writing the lint cache).
- [G41](../grammar/G41-normalize-dedup-active.md) -- Normalize dedup active.
  Codegen optimization that produces content for the written Ascent file.
