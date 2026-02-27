//! PCRE-subset regex compiler: pattern → NFA fragment (single-pass, trampolined).
//!
//! Compiles regex patterns directly into Thompson NFA fragments suitable for
//! the PraTTaIL lexer generation pipeline. No intermediate AST is allocated —
//! NFA states and transitions are emitted as the pattern is parsed.
//!
//! The parser uses explicit continuation frames (trampolining) for stack safety,
//! following the same pattern as the main PraTTaIL parser's trampoline architecture.
//!
//! ## Supported PCRE subset
//!
//! | Feature | Syntax | Example |
//! |---------|--------|---------|
//! | Literal char | `a`, `1`, `_` | ASCII byte-level |
//! | Escaped metachar | `\.` `\\` `\[` `\]` `\(` `\)` `\|` `\+` `\*` `\?` `\^` `\"` `\{` `\}` `\/` | |
//! | Escape sequences | `\n` `\r` `\t` | Common whitespace |
//! | Shorthand classes | `\d` `\w` `\s` `\D` `\W` `\S` | POSIX-like |
//! | Character class | `[abc]` `[a-z]` `[a-zA-Z0-9_]` | Ranges within `[]` |
//! | Negated class | `[^abc]` `[^"]` | Complement over `[0, 127]` |
//! | Dot | `.` | Any byte except `\n` |
//! | Grouping | `(...)` | Non-capturing |
//! | Alternation | <code>a&#124;b</code> | |
//! | Quantifiers | `*` `+` `?` | Greedy (NFA semantics) |
//! | Bounded repetition | `{n}` `{n,}` `{n,m}` | Count-bounded |
//!
//! **Not supported**: backreferences, lookahead/lookbehind, lazy quantifiers,
//! Unicode categories, named groups, anchors (`^$` outside character classes).

use super::{CharClass, Nfa, NfaFragment, NfaState, TokenKind};
use crate::LiteralPatterns;

// ══════════════════════════════════════════════════════════════════════════════
// Error types
// ══════════════════════════════════════════════════════════════════════════════

/// Error from regex parsing or config file parsing.
#[derive(Debug, Clone)]
pub struct RegexError {
    /// Byte offset into the pattern or config content where the error was detected.
    pub position: usize,
    /// Human-readable description of the error.
    pub message: String,
}

impl std::fmt::Display for RegexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "regex error at byte {}: {}", self.position, self.message)
    }
}

impl std::error::Error for RegexError {}

// ══════════════════════════════════════════════════════════════════════════════
// Continuation frames (trampolining)
// ══════════════════════════════════════════════════════════════════════════════

/// Continuation frame for the trampolined regex parser/compiler.
///
/// Each frame represents a suspended parse context that will resume
/// once the current sub-expression finishes compiling.
enum Frame {
    /// Alternation: left branch compiled, waiting for right branch.
    /// On completion, wires both alternatives via epsilon from `alt_start`
    /// to each branch start, and each branch accept to `alt_accept`.
    Alt {
        alt_start: u32,
        alt_accept: u32,
        left_frag: NfaFragment,
    },

    /// Group `(...)`: marks the boundary so `)` knows where to stop.
    Group { outer_fragments: Vec<NfaFragment> },
}

/// Quantifier kind parsed after an atom.
enum QuantifyKind {
    Star,
    Plus,
    Optional,
    Repeat { min: u32, max: Option<u32> },
}

// ══════════════════════════════════════════════════════════════════════════════
// Public API
// ══════════════════════════════════════════════════════════════════════════════

/// Parse a regex pattern and compile it directly into an NFA fragment.
///
/// Single-pass, lazy, trampolined — no intermediate AST allocated.
/// The `token_kind` is set on the final accept state.
///
/// # Errors
///
/// Returns `RegexError` if the pattern contains invalid syntax.
pub fn compile_regex(
    pattern: &str,
    nfa: &mut Nfa,
    token_kind: TokenKind,
) -> Result<NfaFragment, RegexError> {
    let input = pattern.as_bytes();
    let len = input.len();

    if len == 0 {
        return Err(RegexError { position: 0, message: "empty pattern".to_string() });
    }

    let mut pos: usize = 0;
    let mut stack: Vec<Frame> = Vec::with_capacity(8);
    let mut current_fragments: Vec<NfaFragment> = Vec::with_capacity(4);

    'drive: loop {
        if pos >= len {
            /* Reached end of input — link current concat fragments and unwind */
            let frag = link_concat(nfa, &mut current_fragments)?;
            let mut result = frag;

            'unwind: loop {
                match stack.pop() {
                    None => {
                        /* Done — set accepting state and return */
                        nfa.states[result.accept as usize].accept = Some(token_kind.clone());
                        nfa.states[result.accept as usize].weight =
                            super::semiring::TropicalWeight::from_priority(token_kind.priority());
                        return Ok(result);
                    },
                    Some(Frame::Alt { alt_start, alt_accept, left_frag }) => {
                        /* Wire alternation: alt_start -> left | right -> alt_accept */
                        nfa.add_epsilon(alt_start, left_frag.start);
                        nfa.add_epsilon(alt_start, result.start);
                        nfa.add_epsilon(left_frag.accept, alt_accept);
                        nfa.add_epsilon(result.accept, alt_accept);
                        result = NfaFragment { start: alt_start, accept: alt_accept };
                        continue 'unwind;
                    },
                    Some(Frame::Group { .. }) => {
                        return Err(RegexError {
                            position: pos,
                            message: "unclosed group '('".to_string(),
                        });
                    },
                }
            }
        }

        let byte = input[pos];

        match byte {
            b'|' => {
                /* Alternation: link current concat as the left branch */
                pos += 1;
                let left = link_concat(nfa, &mut current_fragments)?;
                let alt_start = nfa.add_state(NfaState::new());
                let alt_accept = nfa.add_state(NfaState::new());
                stack.push(Frame::Alt { alt_start, alt_accept, left_frag: left });
                current_fragments = Vec::with_capacity(4);
                continue 'drive;
            },
            b'(' => {
                /* Open group: save current concat context */
                pos += 1;
                stack.push(Frame::Group { outer_fragments: std::mem::take(&mut current_fragments) });
                current_fragments = Vec::with_capacity(4);
                continue 'drive;
            },
            b')' => {
                /* Close group: link inner concat, pop Group frame, apply quantifier */
                pos += 1;
                let inner = link_concat(nfa, &mut current_fragments)?;
                let mut result = inner;

                /* Unwind any Alt frames inside this group */
                loop {
                    match stack.pop() {
                        Some(Frame::Alt { alt_start, alt_accept, left_frag }) => {
                            nfa.add_epsilon(alt_start, left_frag.start);
                            nfa.add_epsilon(alt_start, result.start);
                            nfa.add_epsilon(left_frag.accept, alt_accept);
                            nfa.add_epsilon(result.accept, alt_accept);
                            result = NfaFragment { start: alt_start, accept: alt_accept };
                        },
                        Some(Frame::Group { outer_fragments }) => {
                            /* Apply quantifier if present */
                            if pos < len {
                                if let Some((qk, new_pos)) = parse_quantifier(input, pos)? {
                                    pos = new_pos;
                                    result = apply_quantifier(nfa, result, &qk);
                                }
                            }
                            current_fragments = outer_fragments;
                            current_fragments.push(result);
                            continue 'drive;
                        },
                        None => {
                            return Err(RegexError {
                                position: pos - 1,
                                message: "unmatched ')'".to_string(),
                            });
                        },
                    }
                }
            },
            _ => {
                /* Parse an atom (literal, escape, char class, dot) */
                let (atom_frag, new_pos) = parse_atom(nfa, input, pos)?;
                pos = new_pos;

                /* Apply quantifier if present */
                let frag = if pos < len {
                    if let Some((qk, new_pos)) = parse_quantifier(input, pos)? {
                        pos = new_pos;
                        apply_quantifier(nfa, atom_frag, &qk)
                    } else {
                        atom_frag
                    }
                } else {
                    atom_frag
                };

                current_fragments.push(frag);
                continue 'drive;
            },
        }
    }
}

/// Validate a regex pattern without compiling (for compile-time checking).
///
/// Runs the same parser logic but into a throwaway NFA.
pub fn validate_regex(pattern: &str) -> Result<(), RegexError> {
    let mut nfa = Nfa::new();
    compile_regex(pattern, &mut nfa, TokenKind::Ident)?;
    Ok(())
}

/// Skip an EBNF comment `(* ... *)` supporting nesting and backslash escapes.
///
/// - Nested comments: `(* outer (* inner *) still outer *)` is one comment.
/// - Escapes: `\(*` inside a comment does **not** open a nested comment;
///   `\*)` does **not** close. Any `\<byte>` pair skips both bytes.
///
/// `pos` must point at the opening `(` of `(*`. On success, `pos` is advanced
/// past the matching `*)`.
fn skip_ebnf_comment(bytes: &[u8], pos: &mut usize) -> Result<(), RegexError> {
    debug_assert!(
        *pos + 1 < bytes.len() && bytes[*pos] == b'(' && bytes[*pos + 1] == b'*',
        "skip_ebnf_comment called without '(*' at pos"
    );
    let comment_start = *pos;
    *pos += 2; /* skip opening '(*' */
    let mut depth: u32 = 1;
    let len = bytes.len();
    while *pos < len {
        match bytes[*pos] {
            b'\\' if *pos + 1 < len => {
                /* Escaped byte — skip both (prevents \(* from opening, \*) from closing) */
                *pos += 2;
            },
            b'(' if *pos + 1 < len && bytes[*pos + 1] == b'*' => {
                /* Nested comment opens */
                depth += 1;
                *pos += 2;
            },
            b'*' if *pos + 1 < len && bytes[*pos + 1] == b')' => {
                /* Comment closes one level */
                depth -= 1;
                *pos += 2;
                if depth == 0 {
                    return Ok(());
                }
            },
            _ => {
                *pos += 1;
            },
        }
    }
    Err(RegexError {
        position: comment_start,
        message: format!(
            "unclosed EBNF comment (nesting depth {} at end of input)",
            depth
        ),
    })
}

/// Parse the `literal_patterns.ebnf` config file content into a `LiteralPatterns`.
///
/// Format:
/// ```text
/// (* comment — supports nesting and \-escapes *)
/// <name> = /regex/ (* optional comment *) ;
/// ```
///
/// `<name>` must be one of: `integer`, `float`, `string`, `ident`.
/// All four must be defined exactly once.
///
/// # Errors
///
/// Returns `RegexError` if the config has invalid syntax or unknown names.
pub fn parse_literal_patterns_ebnf(content: &str) -> Result<LiteralPatterns, RegexError> {
    let mut integer: Option<String> = None;
    let mut float: Option<String> = None;
    let mut string: Option<String> = None;
    let mut ident: Option<String> = None;

    let bytes = content.as_bytes();
    let len = bytes.len();
    let mut pos: usize = 0;

    loop {
        /* Skip whitespace */
        skip_ws(bytes, &mut pos);
        if pos >= len {
            break;
        }

        /* Skip EBNF comments: (* ... *) — with nesting and escapes */
        if pos + 1 < len && bytes[pos] == b'(' && bytes[pos + 1] == b'*' {
            skip_ebnf_comment(bytes, &mut pos)?;
            continue;
        }

        /* Parse production: <name> = /regex/ (* comment *) ; */
        if bytes[pos] != b'<' {
            return Err(RegexError {
                position: pos,
                message: format!(
                    "expected '<' at start of production, found '{}'",
                    bytes[pos] as char
                ),
            });
        }
        pos += 1;

        /* Read name */
        let name_start = pos;
        while pos < len && bytes[pos] != b'>' {
            pos += 1;
        }
        if pos >= len {
            return Err(RegexError {
                position: name_start,
                message: "unclosed '<name>'".to_string(),
            });
        }
        let name = std::str::from_utf8(&bytes[name_start..pos])
            .map_err(|_| RegexError {
                position: name_start,
                message: "invalid UTF-8 in name".to_string(),
            })?
            .trim();
        pos += 1; /* skip '>' */

        /* Skip whitespace, expect '=' */
        skip_ws(bytes, &mut pos);
        if pos >= len || bytes[pos] != b'=' {
            return Err(RegexError {
                position: pos,
                message: "expected '=' after <name>".to_string(),
            });
        }
        pos += 1;

        /* Skip whitespace, expect '/' (regex start delimiter) */
        skip_ws(bytes, &mut pos);
        if pos >= len || bytes[pos] != b'/' {
            return Err(RegexError {
                position: pos,
                message: "expected '/' to start regex".to_string(),
            });
        }
        pos += 1;

        /* Read regex until unescaped '/' */
        let regex_start = pos;
        while pos < len {
            if bytes[pos] == b'\\' && pos + 1 < len {
                pos += 2; /* skip escaped char */
            } else if bytes[pos] == b'/' {
                break;
            } else {
                pos += 1;
            }
        }
        if pos >= len {
            return Err(RegexError {
                position: regex_start,
                message: "unclosed regex delimiter '/'".to_string(),
            });
        }
        let regex_pattern = std::str::from_utf8(&bytes[regex_start..pos])
            .map_err(|_| RegexError {
                position: regex_start,
                message: "invalid UTF-8 in regex".to_string(),
            })?
            .to_string();
        pos += 1; /* skip closing '/' */

        /* Validate the regex immediately */
        validate_regex(&regex_pattern).map_err(|e| RegexError {
            position: regex_start + e.position,
            message: format!("in pattern for <{}>: {}", name, e.message),
        })?;

        /* Skip to ';' — properly skip nested comments along the way */
        loop {
            skip_ws(bytes, &mut pos);
            if pos >= len {
                return Err(RegexError {
                    position: pos,
                    message: format!("expected ';' after <{}> production", name),
                });
            }
            if bytes[pos] == b';' {
                break;
            }
            if pos + 1 < len && bytes[pos] == b'(' && bytes[pos + 1] == b'*' {
                skip_ebnf_comment(bytes, &mut pos)?;
            } else {
                pos += 1;
            }
        }
        pos += 1; /* skip ';' */

        /* Store the pattern */
        let slot = match name {
            "integer" => &mut integer,
            "float" => &mut float,
            "string" => &mut string,
            "ident" => &mut ident,
            _ => {
                return Err(RegexError {
                    position: name_start,
                    message: format!(
                        "unknown token name '{}' (expected: integer, float, string, ident)",
                        name
                    ),
                });
            },
        };
        if slot.is_some() {
            return Err(RegexError {
                position: name_start,
                message: format!("duplicate definition for <{}>", name),
            });
        }
        *slot = Some(regex_pattern);
    }

    /* All four patterns must be defined */
    let missing: Vec<&str> = [
        integer.is_none().then_some("integer"),
        float.is_none().then_some("float"),
        string.is_none().then_some("string"),
        ident.is_none().then_some("ident"),
    ]
    .into_iter()
    .flatten()
    .collect();
    if !missing.is_empty() {
        return Err(RegexError {
            position: 0,
            message: format!("missing pattern definitions: {}", missing.join(", ")),
        });
    }

    Ok(LiteralPatterns {
        integer: integer.expect("validated above"),
        float: float.expect("validated above"),
        string: string.expect("validated above"),
        ident: ident.expect("validated above"),
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Atom parsing
// ══════════════════════════════════════════════════════════════════════════════

/// Parse a single atom (literal, escape, char class, or dot) and return the
/// NFA fragment and the new position.
fn parse_atom(
    nfa: &mut Nfa,
    input: &[u8],
    pos: usize,
) -> Result<(NfaFragment, usize), RegexError> {
    let byte = input[pos];
    match byte {
        b'[' => parse_char_class_atom(nfa, input, pos),
        b'.' => {
            /* Dot: any byte except newline */
            let start = nfa.add_state(NfaState::new());
            let accept = nfa.add_state(NfaState::new());
            /* [0, 9] ∪ [11, 127] — skip \n (10) */
            for lo_hi in &[(0u8, 9u8), (11u8, 127u8)] {
                nfa.add_transition(start, accept, CharClass::Range(lo_hi.0, lo_hi.1));
            }
            Ok((NfaFragment { start, accept }, pos + 1))
        },
        b'\\' => parse_escape_atom(nfa, input, pos),
        /* Metacharacters that shouldn't appear as bare atoms */
        b'*' | b'+' | b'?' | b'{' => {
            Err(RegexError {
                position: pos,
                message: format!("quantifier '{}' without preceding atom", byte as char),
            })
        },
        b')' => {
            Err(RegexError { position: pos, message: "unexpected ')'".to_string() })
        },
        _ => {
            /* Literal character */
            let start = nfa.add_state(NfaState::new());
            let accept = nfa.add_state(NfaState::new());
            nfa.add_transition(start, accept, CharClass::Single(byte));
            Ok((NfaFragment { start, accept }, pos + 1))
        },
    }
}

/// Parse a backslash escape and return an NFA fragment.
fn parse_escape_atom(
    nfa: &mut Nfa,
    input: &[u8],
    pos: usize,
) -> Result<(NfaFragment, usize), RegexError> {
    if pos + 1 >= input.len() {
        return Err(RegexError {
            position: pos,
            message: "trailing backslash".to_string(),
        });
    }

    let escaped = input[pos + 1];
    let start = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::new());

    match escaped {
        /* Shorthand classes */
        b'd' => {
            nfa.add_transition(start, accept, CharClass::Range(b'0', b'9'));
        },
        b'D' => {
            add_ranges(nfa, start, accept, &complement_ranges(&[(b'0', b'9')]));
        },
        b'w' => {
            for &(lo, hi) in &[(b'0', b'9'), (b'A', b'Z'), (b'_', b'_'), (b'a', b'z')] {
                nfa.add_transition(start, accept, CharClass::Range(lo, hi));
            }
        },
        b'W' => {
            add_ranges(
                nfa,
                start,
                accept,
                &complement_ranges(&[(b'0', b'9'), (b'A', b'Z'), (b'_', b'_'), (b'a', b'z')]),
            );
        },
        b's' => {
            for &b in &[b' ', b'\t', b'\n', b'\r'] {
                nfa.add_transition(start, accept, CharClass::Single(b));
            }
        },
        b'S' => {
            add_ranges(
                nfa,
                start,
                accept,
                &complement_ranges(&[(b'\t', b'\n'), (b'\r', b'\r'), (b' ', b' ')]),
            );
        },
        /* Escape sequences */
        b'n' => {
            nfa.add_transition(start, accept, CharClass::Single(b'\n'));
        },
        b'r' => {
            nfa.add_transition(start, accept, CharClass::Single(b'\r'));
        },
        b't' => {
            nfa.add_transition(start, accept, CharClass::Single(b'\t'));
        },
        /* Escaped metacharacters */
        b'.' | b'\\' | b'[' | b']' | b'(' | b')' | b'|' | b'+' | b'*' | b'?' | b'^'
        | b'"' | b'{' | b'}' | b'/' => {
            nfa.add_transition(start, accept, CharClass::Single(escaped));
        },
        _ => {
            return Err(RegexError {
                position: pos,
                message: format!("invalid escape '\\{}'", escaped as char),
            });
        },
    }

    Ok((NfaFragment { start, accept }, pos + 2))
}

// ══════════════════════════════════════════════════════════════════════════════
// Character class parsing
// ══════════════════════════════════════════════════════════════════════════════

/// Parse a `[...]` character class atom and return its NFA fragment.
fn parse_char_class_atom(
    nfa: &mut Nfa,
    input: &[u8],
    pos: usize,
) -> Result<(NfaFragment, usize), RegexError> {
    debug_assert_eq!(input[pos], b'[');
    let mut i = pos + 1;
    let len = input.len();

    /* Check for negation */
    let negated = i < len && input[i] == b'^';
    if negated {
        i += 1;
    }

    let mut ranges: Vec<(u8, u8)> = Vec::with_capacity(8);

    /* Special case: ] as first char (or first after ^) is literal */
    if i < len && input[i] == b']' {
        ranges.push((b']', b']'));
        i += 1;
    }

    while i < len && input[i] != b']' {
        let ch = if input[i] == b'\\' {
            if i + 1 >= len {
                return Err(RegexError {
                    position: i,
                    message: "trailing backslash in character class".to_string(),
                });
            }
            let esc = input[i + 1];
            i += 2;
            match esc {
                b'd' => {
                    ranges.push((b'0', b'9'));
                    continue;
                },
                b'D' => {
                    ranges.extend_from_slice(&complement_ranges(&[(b'0', b'9')]));
                    continue;
                },
                b'w' => {
                    ranges.extend_from_slice(&[(b'0', b'9'), (b'A', b'Z'), (b'_', b'_'), (b'a', b'z')]);
                    continue;
                },
                b'W' => {
                    ranges.extend_from_slice(&complement_ranges(&[
                        (b'0', b'9'),
                        (b'A', b'Z'),
                        (b'_', b'_'),
                        (b'a', b'z'),
                    ]));
                    continue;
                },
                b's' => {
                    ranges.extend_from_slice(&[(b'\t', b'\n'), (b'\r', b'\r'), (b' ', b' ')]);
                    continue;
                },
                b'S' => {
                    ranges.extend_from_slice(&complement_ranges(&[
                        (b'\t', b'\n'),
                        (b'\r', b'\r'),
                        (b' ', b' '),
                    ]));
                    continue;
                },
                b'n' => b'\n',
                b'r' => b'\r',
                b't' => b'\t',
                b'\\' | b']' | b'[' | b'^' | b'-' | b'/' | b'"' => esc,
                _ => {
                    return Err(RegexError {
                        position: i - 2,
                        message: format!("invalid escape '\\{}' in character class", esc as char),
                    });
                },
            }
        } else {
            let c = input[i];
            i += 1;
            c
        };

        /* Check for range: a-z */
        if i + 1 < len && input[i] == b'-' && input[i + 1] != b']' {
            i += 1; /* skip '-' */
            let hi = if input[i] == b'\\' {
                if i + 1 >= len {
                    return Err(RegexError {
                        position: i,
                        message: "trailing backslash in character class range".to_string(),
                    });
                }
                let esc = input[i + 1];
                i += 2;
                match esc {
                    b'n' => b'\n',
                    b'r' => b'\r',
                    b't' => b'\t',
                    b'\\' | b']' | b'[' | b'^' | b'-' | b'/' | b'"' => esc,
                    _ => {
                        return Err(RegexError {
                            position: i - 2,
                            message: format!(
                                "invalid escape '\\{}' in character class range",
                                esc as char
                            ),
                        });
                    },
                }
            } else {
                let c = input[i];
                i += 1;
                c
            };

            if ch > hi {
                return Err(RegexError {
                    position: pos,
                    message: format!(
                        "character class range [{}-{}] is out of order",
                        ch as char, hi as char
                    ),
                });
            }
            ranges.push((ch, hi));
        } else {
            ranges.push((ch, ch));
        }
    }

    if i >= len {
        return Err(RegexError {
            position: pos,
            message: "unclosed character class '['".to_string(),
        });
    }
    i += 1; /* skip ']' */

    /* Sort and merge ranges */
    let merged = if negated {
        let positive = sort_and_merge_ranges(&ranges);
        complement_ranges(&positive)
    } else {
        sort_and_merge_ranges(&ranges)
    };

    /* Build NFA fragment */
    let start = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::new());
    add_ranges(nfa, start, accept, &merged);

    Ok((NfaFragment { start, accept }, i))
}

/// Sort ranges by start, then merge overlapping/adjacent ranges.
fn sort_and_merge_ranges(ranges: &[(u8, u8)]) -> Vec<(u8, u8)> {
    if ranges.is_empty() {
        return Vec::new();
    }
    let mut sorted = ranges.to_vec();
    sorted.sort_by_key(|&(lo, _)| lo);

    let mut merged: Vec<(u8, u8)> = Vec::with_capacity(sorted.len());
    let (mut cur_lo, mut cur_hi) = sorted[0];

    for &(lo, hi) in &sorted[1..] {
        if lo <= cur_hi.saturating_add(1) {
            cur_hi = cur_hi.max(hi);
        } else {
            merged.push((cur_lo, cur_hi));
            cur_lo = lo;
            cur_hi = hi;
        }
    }
    merged.push((cur_lo, cur_hi));
    merged
}

/// Compute the complement of a set of ranges over `[0, 127]`.
fn complement_ranges(ranges: &[(u8, u8)]) -> Vec<(u8, u8)> {
    let merged = sort_and_merge_ranges(ranges);
    let mut complement: Vec<(u8, u8)> = Vec::with_capacity(merged.len() + 1);
    let mut lo: u8 = 0;
    for &(range_lo, range_hi) in &merged {
        if range_lo > lo {
            complement.push((lo, range_lo - 1));
        }
        lo = range_hi.saturating_add(1);
        if range_hi == 127 {
            return complement;
        }
    }
    if lo <= 127 {
        complement.push((lo, 127));
    }
    complement
}

/// Add NFA transitions for a list of character ranges.
fn add_ranges(nfa: &mut Nfa, from: u32, to: u32, ranges: &[(u8, u8)]) {
    for &(lo, hi) in ranges {
        if lo == hi {
            nfa.add_transition(from, to, CharClass::Single(lo));
        } else {
            nfa.add_transition(from, to, CharClass::Range(lo, hi));
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Quantifier parsing and application
// ══════════════════════════════════════════════════════════════════════════════

/// Try to parse a quantifier at the current position.
/// Returns `None` if no quantifier is present.
fn parse_quantifier(
    input: &[u8],
    pos: usize,
) -> Result<Option<(QuantifyKind, usize)>, RegexError> {
    if pos >= input.len() {
        return Ok(None);
    }
    match input[pos] {
        b'*' => Ok(Some((QuantifyKind::Star, pos + 1))),
        b'+' => Ok(Some((QuantifyKind::Plus, pos + 1))),
        b'?' => Ok(Some((QuantifyKind::Optional, pos + 1))),
        b'{' => parse_bounded_quantifier(input, pos),
        _ => Ok(None),
    }
}

/// Parse `{n}`, `{n,}`, or `{n,m}`.
fn parse_bounded_quantifier(
    input: &[u8],
    pos: usize,
) -> Result<Option<(QuantifyKind, usize)>, RegexError> {
    debug_assert_eq!(input[pos], b'{');
    let len = input.len();
    let mut i = pos + 1;

    /* Parse min */
    let min_start = i;
    while i < len && input[i].is_ascii_digit() {
        i += 1;
    }
    if i == min_start || i >= len {
        return Err(RegexError {
            position: pos,
            message: "invalid bounded repetition: expected digit after '{'".to_string(),
        });
    }
    let min: u32 = std::str::from_utf8(&input[min_start..i])
        .unwrap()
        .parse()
        .map_err(|_| RegexError {
            position: min_start,
            message: "bounded repetition: min too large".to_string(),
        })?;

    if input[i] == b'}' {
        /* Exact: {n} */
        return Ok(Some((QuantifyKind::Repeat { min, max: Some(min) }, i + 1)));
    }
    if input[i] != b',' {
        return Err(RegexError {
            position: i,
            message: "invalid bounded repetition: expected ',' or '}'".to_string(),
        });
    }
    i += 1; /* skip ',' */

    if i >= len {
        return Err(RegexError {
            position: i,
            message: "unclosed bounded repetition".to_string(),
        });
    }
    if input[i] == b'}' {
        /* Unbounded: {n,} */
        return Ok(Some((QuantifyKind::Repeat { min, max: None }, i + 1)));
    }

    /* Parse max */
    let max_start = i;
    while i < len && input[i].is_ascii_digit() {
        i += 1;
    }
    if i == max_start || i >= len || input[i] != b'}' {
        return Err(RegexError {
            position: pos,
            message: "invalid bounded repetition: expected digit and '}'".to_string(),
        });
    }
    let max: u32 = std::str::from_utf8(&input[max_start..i])
        .unwrap()
        .parse()
        .map_err(|_| RegexError {
            position: max_start,
            message: "bounded repetition: max too large".to_string(),
        })?;

    if max < min {
        return Err(RegexError {
            position: pos,
            message: format!("bounded repetition: max ({}) < min ({})", max, min),
        });
    }

    Ok(Some((QuantifyKind::Repeat { min, max: Some(max) }, i + 1)))
}

/// Apply a quantifier to an NFA fragment.
fn apply_quantifier(nfa: &mut Nfa, frag: NfaFragment, kind: &QuantifyKind) -> NfaFragment {
    match kind {
        QuantifyKind::Star => {
            /* a* : new_start -> frag.start, frag.accept -> frag.start, new_start -> new_accept, frag.accept -> new_accept */
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(new_start, new_accept);
            nfa.add_epsilon(frag.accept, frag.start);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Plus => {
            /* a+ : new_start -> frag.start, frag.accept -> frag.start, frag.accept -> new_accept */
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(frag.accept, frag.start);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Optional => {
            /* a? : new_start -> frag.start, new_start -> new_accept, frag.accept -> new_accept */
            let new_start = nfa.add_state(NfaState::new());
            let new_accept = nfa.add_state(NfaState::new());
            nfa.add_epsilon(new_start, frag.start);
            nfa.add_epsilon(new_start, new_accept);
            nfa.add_epsilon(frag.accept, new_accept);
            NfaFragment { start: new_start, accept: new_accept }
        },
        QuantifyKind::Repeat { min, max } => apply_bounded_repeat(nfa, frag, *min, *max),
    }
}

/// Apply bounded repetition `{min,max}` by expanding to concatenated copies.
///
/// - `min` mandatory copies linked in sequence
/// - For each of the `max - min` optional copies, add an epsilon-bypassed copy
/// - For `{n,}` (unbounded), the last mandatory copy gets a Kleene star
fn apply_bounded_repeat(
    nfa: &mut Nfa,
    frag: NfaFragment,
    min: u32,
    max: Option<u32>,
) -> NfaFragment {
    if min == 0 && max == Some(0) {
        /* {0} — match empty string */
        let s = nfa.add_state(NfaState::new());
        return NfaFragment { start: s, accept: s };
    }

    /* Build min mandatory copies */
    let mut copies: Vec<NfaFragment> = Vec::with_capacity(min as usize + 4);
    for _ in 0..min {
        copies.push(clone_fragment(nfa, &frag));
    }

    match max {
        None => {
            /* {min,} — min copies then star */
            let star_copy = clone_fragment(nfa, &frag);
            let star_frag = apply_quantifier(nfa, star_copy, &QuantifyKind::Star);
            copies.push(star_frag);
        },
        Some(max_val) => {
            /* {min, max} — add (max - min) optional copies */
            for _ in 0..(max_val - min) {
                let opt_copy = clone_fragment(nfa, &frag);
                let opt_frag = apply_quantifier(nfa, opt_copy, &QuantifyKind::Optional);
                copies.push(opt_frag);
            }
        },
    }

    /* Link all copies in sequence */
    if copies.is_empty() {
        let s = nfa.add_state(NfaState::new());
        NfaFragment { start: s, accept: s }
    } else {
        let mut result = copies.remove(0);
        for next in copies {
            nfa.add_epsilon(result.accept, next.start);
            result = NfaFragment { start: result.start, accept: next.accept };
        }
        result
    }
}

/// Clone an NFA fragment by creating fresh states with the same transitions.
fn clone_fragment(nfa: &mut Nfa, frag: &NfaFragment) -> NfaFragment {
    /* Collect all reachable states from frag.start via BFS */
    let mut visited: Vec<u32> = Vec::new();
    let mut queue: Vec<u32> = vec![frag.start];
    let mut seen = std::collections::HashSet::new();
    seen.insert(frag.start);

    while let Some(state) = queue.pop() {
        visited.push(state);
        let s = &nfa.states[state as usize];
        for &(_, target) in &s.transitions {
            if seen.insert(target) {
                queue.push(target);
            }
        }
        for &target in &s.epsilon {
            if seen.insert(target) {
                queue.push(target);
            }
        }
    }

    /* Create new states and build old→new mapping */
    let mut mapping: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    for &old_id in &visited {
        let new_id = nfa.add_state(NfaState::new());
        mapping.insert(old_id, new_id);
    }

    /* Copy transitions (clone of nfa.states[old] is needed to avoid borrow conflict) */
    for &old_id in &visited {
        let transitions: Vec<(CharClass, u32)> = nfa.states[old_id as usize].transitions.clone();
        let epsilons: Vec<u32> = nfa.states[old_id as usize].epsilon.clone();
        let new_id = mapping[&old_id];

        for (class, target) in transitions {
            if let Some(&new_target) = mapping.get(&target) {
                nfa.add_transition(new_id, new_target, class);
            }
        }
        for target in epsilons {
            if let Some(&new_target) = mapping.get(&target) {
                nfa.add_epsilon(new_id, new_target);
            }
        }
    }

    NfaFragment {
        start: mapping[&frag.start],
        accept: mapping[&frag.accept],
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Concat linking
// ══════════════════════════════════════════════════════════════════════════════

/// Link a sequence of NFA fragments into a single concatenation fragment.
///
/// Each fragment's accept state is epsilon-connected to the next fragment's start.
fn link_concat(nfa: &mut Nfa, fragments: &mut Vec<NfaFragment>) -> Result<NfaFragment, RegexError> {
    if fragments.is_empty() {
        /* Empty concatenation: single epsilon fragment */
        let s = nfa.add_state(NfaState::new());
        return Ok(NfaFragment { start: s, accept: s });
    }
    if fragments.len() == 1 {
        return Ok(fragments.remove(0));
    }

    let first = fragments.remove(0);
    let mut result = first;
    for next in fragments.drain(..) {
        nfa.add_epsilon(result.accept, next.start);
        result = NfaFragment { start: result.start, accept: next.accept };
    }
    Ok(result)
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Skip ASCII whitespace in a byte slice.
fn skip_ws(input: &[u8], pos: &mut usize) {
    while *pos < input.len() && input[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::minimize::minimize_dfa;
    use crate::automata::nfa::epsilon_closure;
    use crate::automata::partition::compute_equivalence_classes;
    use crate::automata::subset::subset_construction;

    /// Helper: compile a regex, build the full DFA pipeline, then test if it accepts a string.
    fn regex_accepts(pattern: &str, token_kind: TokenKind, input: &str) -> bool {
        let mut nfa = Nfa::new();
        let frag =
            compile_regex(pattern, &mut nfa, token_kind.clone()).expect("regex compilation failed");
        nfa.add_epsilon(nfa.start, frag.start);

        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        /* Simulate DFA on input */
        let bytes = input.as_bytes();
        let mut state = min_dfa.start;
        for &b in bytes {
            let class = partition.classify(b);
            state = min_dfa.transition(state, class);
            if state == super::super::DEAD_STATE {
                return false;
            }
        }
        min_dfa.states[state as usize].accept.is_some()
    }

    /* ── Basic literals ────────────────────────────────────────────────── */

    #[test]
    fn test_single_literal() {
        assert!(regex_accepts("a", TokenKind::Ident, "a"));
        assert!(!regex_accepts("a", TokenKind::Ident, "b"));
        assert!(!regex_accepts("a", TokenKind::Ident, "aa"));
    }

    #[test]
    fn test_concat() {
        assert!(regex_accepts("abc", TokenKind::Ident, "abc"));
        assert!(!regex_accepts("abc", TokenKind::Ident, "ab"));
        assert!(!regex_accepts("abc", TokenKind::Ident, "abcd"));
    }

    /* ── Quantifiers ───────────────────────────────────────────────────── */

    #[test]
    fn test_star() {
        assert!(regex_accepts("a*", TokenKind::Ident, ""));
        assert!(regex_accepts("a*", TokenKind::Ident, "a"));
        assert!(regex_accepts("a*", TokenKind::Ident, "aaa"));
        assert!(!regex_accepts("a*", TokenKind::Ident, "b"));
    }

    #[test]
    fn test_plus() {
        assert!(!regex_accepts("a+", TokenKind::Ident, ""));
        assert!(regex_accepts("a+", TokenKind::Ident, "a"));
        assert!(regex_accepts("a+", TokenKind::Ident, "aaa"));
    }

    #[test]
    fn test_optional() {
        assert!(regex_accepts("a?", TokenKind::Ident, ""));
        assert!(regex_accepts("a?", TokenKind::Ident, "a"));
        assert!(!regex_accepts("a?", TokenKind::Ident, "aa"));
    }

    #[test]
    fn test_bounded_exact() {
        assert!(regex_accepts("a{3}", TokenKind::Ident, "aaa"));
        assert!(!regex_accepts("a{3}", TokenKind::Ident, "aa"));
        assert!(!regex_accepts("a{3}", TokenKind::Ident, "aaaa"));
    }

    #[test]
    fn test_bounded_range() {
        assert!(!regex_accepts("a{2,4}", TokenKind::Ident, "a"));
        assert!(regex_accepts("a{2,4}", TokenKind::Ident, "aa"));
        assert!(regex_accepts("a{2,4}", TokenKind::Ident, "aaa"));
        assert!(regex_accepts("a{2,4}", TokenKind::Ident, "aaaa"));
        assert!(!regex_accepts("a{2,4}", TokenKind::Ident, "aaaaa"));
    }

    #[test]
    fn test_bounded_unbounded() {
        assert!(!regex_accepts("a{2,}", TokenKind::Ident, "a"));
        assert!(regex_accepts("a{2,}", TokenKind::Ident, "aa"));
        assert!(regex_accepts("a{2,}", TokenKind::Ident, "aaaaaaa"));
    }

    /* ── Character classes ─────────────────────────────────────────────── */

    #[test]
    fn test_char_class_range() {
        assert!(regex_accepts("[a-z]", TokenKind::Ident, "a"));
        assert!(regex_accepts("[a-z]", TokenKind::Ident, "m"));
        assert!(regex_accepts("[a-z]", TokenKind::Ident, "z"));
        assert!(!regex_accepts("[a-z]", TokenKind::Ident, "A"));
        assert!(!regex_accepts("[a-z]", TokenKind::Ident, "0"));
    }

    #[test]
    fn test_char_class_multi_range() {
        assert!(regex_accepts("[a-zA-Z0-9_]", TokenKind::Ident, "a"));
        assert!(regex_accepts("[a-zA-Z0-9_]", TokenKind::Ident, "Z"));
        assert!(regex_accepts("[a-zA-Z0-9_]", TokenKind::Ident, "5"));
        assert!(regex_accepts("[a-zA-Z0-9_]", TokenKind::Ident, "_"));
        assert!(!regex_accepts("[a-zA-Z0-9_]", TokenKind::Ident, "+"));
    }

    #[test]
    fn test_negated_char_class() {
        assert!(!regex_accepts("[^a-z]", TokenKind::Ident, "a"));
        assert!(regex_accepts("[^a-z]", TokenKind::Ident, "A"));
        assert!(regex_accepts("[^a-z]", TokenKind::Ident, "0"));
        assert!(regex_accepts("[^a-z]", TokenKind::Ident, "+"));
    }

    /* ── Alternation ───────────────────────────────────────────────────── */

    #[test]
    fn test_alternation() {
        assert!(regex_accepts("a|b", TokenKind::Ident, "a"));
        assert!(regex_accepts("a|b", TokenKind::Ident, "b"));
        assert!(!regex_accepts("a|b", TokenKind::Ident, "c"));
    }

    #[test]
    fn test_alternation_with_concat() {
        assert!(regex_accepts("ab|cd", TokenKind::Ident, "ab"));
        assert!(regex_accepts("ab|cd", TokenKind::Ident, "cd"));
        assert!(!regex_accepts("ab|cd", TokenKind::Ident, "ac"));
    }

    /* ── Groups ────────────────────────────────────────────────────────── */

    #[test]
    fn test_group() {
        assert!(regex_accepts("(ab)+", TokenKind::Ident, "ab"));
        assert!(regex_accepts("(ab)+", TokenKind::Ident, "abab"));
        assert!(!regex_accepts("(ab)+", TokenKind::Ident, "a"));
    }

    #[test]
    fn test_group_alternation() {
        assert!(regex_accepts("(a|b)+", TokenKind::Ident, "a"));
        assert!(regex_accepts("(a|b)+", TokenKind::Ident, "abba"));
        assert!(!regex_accepts("(a|b)+", TokenKind::Ident, "c"));
    }

    /* ── Escapes ───────────────────────────────────────────────────────── */

    #[test]
    fn test_escape_dot() {
        assert!(regex_accepts(r"\.", TokenKind::Ident, "."));
        assert!(!regex_accepts(r"\.", TokenKind::Ident, "a"));
    }

    #[test]
    fn test_shorthand_d() {
        assert!(regex_accepts(r"\d+", TokenKind::Integer, "123"));
        assert!(!regex_accepts(r"\d+", TokenKind::Integer, "abc"));
    }

    #[test]
    fn test_shorthand_w() {
        assert!(regex_accepts(r"\w+", TokenKind::Ident, "hello_42"));
        assert!(!regex_accepts(r"\w+", TokenKind::Ident, "hello world"));
    }

    /* ── Dot ───────────────────────────────────────────────────────────── */

    #[test]
    fn test_dot() {
        assert!(regex_accepts(".", TokenKind::Ident, "a"));
        assert!(regex_accepts(".", TokenKind::Ident, "0"));
        assert!(regex_accepts(".", TokenKind::Ident, "+"));
        assert!(!regex_accepts(".", TokenKind::Ident, "\n"));
    }

    /* ── Default patterns equivalence ──────────────────────────────────── */

    #[test]
    fn test_default_integer_pattern() {
        let pat = &LiteralPatterns::default().integer;
        assert!(regex_accepts(pat, TokenKind::Integer, "0"));
        assert!(regex_accepts(pat, TokenKind::Integer, "42"));
        assert!(regex_accepts(pat, TokenKind::Integer, "1234567890"));
        assert!(!regex_accepts(pat, TokenKind::Integer, ""));
        assert!(!regex_accepts(pat, TokenKind::Integer, "abc"));
    }

    #[test]
    fn test_default_float_pattern() {
        let pat = &LiteralPatterns::default().float;
        assert!(regex_accepts(pat, TokenKind::Float, "3.14"));
        assert!(regex_accepts(pat, TokenKind::Float, "0.0"));
        assert!(regex_accepts(pat, TokenKind::Float, "1.23e10"));
        assert!(regex_accepts(pat, TokenKind::Float, "1.23E10"));
        assert!(regex_accepts(pat, TokenKind::Float, "1.23e+10"));
        assert!(regex_accepts(pat, TokenKind::Float, "1.23e-10"));
        assert!(!regex_accepts(pat, TokenKind::Float, "42"));
        assert!(!regex_accepts(pat, TokenKind::Float, ".5"));
        assert!(!regex_accepts(pat, TokenKind::Float, "1."));
    }

    #[test]
    fn test_default_string_pattern() {
        let pat = &LiteralPatterns::default().string;
        assert!(regex_accepts(pat, TokenKind::StringLit, r#""""#));
        assert!(regex_accepts(pat, TokenKind::StringLit, r#""hello""#));
        assert!(regex_accepts(pat, TokenKind::StringLit, r#""hello world""#));
        assert!(regex_accepts(pat, TokenKind::StringLit, r#""say \"hi\"""#));
        assert!(regex_accepts(pat, TokenKind::StringLit, r#""path\\to\\file""#));
        assert!(!regex_accepts(pat, TokenKind::StringLit, "hello"));
        assert!(!regex_accepts(pat, TokenKind::StringLit, r#""unclosed"#));
    }

    #[test]
    fn test_default_ident_pattern() {
        let pat = &LiteralPatterns::default().ident;
        assert!(regex_accepts(pat, TokenKind::Ident, "x"));
        assert!(regex_accepts(pat, TokenKind::Ident, "_foo"));
        assert!(regex_accepts(pat, TokenKind::Ident, "hello_world"));
        assert!(regex_accepts(pat, TokenKind::Ident, "X42"));
        assert!(!regex_accepts(pat, TokenKind::Ident, "42x"));
        assert!(!regex_accepts(pat, TokenKind::Ident, ""));
        assert!(!regex_accepts(pat, TokenKind::Ident, "+"));
    }

    /* ── Custom patterns ───────────────────────────────────────────────── */

    #[test]
    fn test_hex_integer_pattern() {
        let pat = "0[xX][0-9a-fA-F]+|[0-9]+";
        assert!(regex_accepts(pat, TokenKind::Integer, "42"));
        assert!(regex_accepts(pat, TokenKind::Integer, "0xFF"));
        assert!(regex_accepts(pat, TokenKind::Integer, "0x1a2b"));
        assert!(regex_accepts(pat, TokenKind::Integer, "0X0"));
        assert!(!regex_accepts(pat, TokenKind::Integer, "0xGG"));
    }

    /* ── Validation ────────────────────────────────────────────────────── */

    #[test]
    fn test_validate_ok() {
        assert!(validate_regex("[0-9]+").is_ok());
        assert!(validate_regex(r"[a-zA-Z_]\w*").is_ok());
        assert!(validate_regex(r#""([^"\\]|\\.)*""#).is_ok());
    }

    #[test]
    fn test_validate_errors() {
        assert!(validate_regex("[unclosed").is_err());
        assert!(validate_regex("(unclosed").is_err());
        assert!(validate_regex("*").is_err());
        assert!(validate_regex(r"\").is_err());
        assert!(validate_regex("{3}").is_err());
    }

    /* ── Config file parser ────────────────────────────────────────────── */

    #[test]
    fn test_parse_default_config() {
        let content = include_str!("../literal_patterns.ebnf");
        let patterns =
            parse_literal_patterns_ebnf(content).expect("default config should parse successfully");
        assert_eq!(patterns.integer, "[0-9]+");
        assert_eq!(patterns.float, r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?");
        assert_eq!(patterns.string, r#""([^"\\]|\\.)*""#);
        assert_eq!(patterns.ident, "[a-zA-Z_][a-zA-Z0-9_]*");
    }

    #[test]
    fn test_parse_config_unknown_name() {
        let content = r#"<unknown> = /[0-9]+/ ;"#;
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("unknown token name"));
    }

    #[test]
    fn test_parse_config_invalid_regex() {
        let content = r#"<integer> = /[unclosed/ ;"#;
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_config_missing_semicolon() {
        let content = r#"<integer> = /[0-9]+/"#;
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_config_duplicate_name() {
        let content = "<integer> = /[0-9]+/ ;\n<integer> = /[0-9]+/ ;";
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("duplicate"));
    }

    #[test]
    fn test_parse_config_missing_patterns() {
        let content = "<integer> = /[0-9]+/ ;";
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
        let msg = result.unwrap_err().message;
        assert!(msg.contains("missing pattern definitions"));
        assert!(msg.contains("float"));
        assert!(msg.contains("string"));
        assert!(msg.contains("ident"));
    }

    #[test]
    fn test_parse_config_nested_comments() {
        let content = concat!(
            "(* outer (* inner *) still outer *)\n",
            "<integer> = /[0-9]+/ ;\n",
            "<float>   = /[0-9]+/ ;\n",
            "<string>  = /[a-z]+/ ;\n",
            "<ident>   = /[a-z]+/ ;\n",
        );
        let patterns =
            parse_literal_patterns_ebnf(content).expect("nested comments should parse");
        assert_eq!(patterns.integer, "[0-9]+");
    }

    #[test]
    fn test_parse_config_deeply_nested_comments() {
        let content = concat!(
            "(* level 1 (* level 2 (* level 3 *) back to 2 *) back to 1 *)\n",
            "<integer> = /[0-9]+/ ;\n",
            "<float>   = /[0-9]+/ ;\n",
            "<string>  = /[a-z]+/ ;\n",
            "<ident>   = /[a-z]+/ ;\n",
        );
        parse_literal_patterns_ebnf(content).expect("deeply nested comments should parse");
    }

    #[test]
    fn test_parse_config_escaped_comment_delimiters() {
        /* \(* inside a comment does NOT open a nested comment */
        let content = concat!(
            r"(* \(* bar *)",
            "\n",
            "<integer> = /[0-9]+/ ;\n",
            "<float>   = /[0-9]+/ ;\n",
            "<string>  = /[a-z]+/ ;\n",
            "<ident>   = /[a-z]+/ ;\n",
        );
        parse_literal_patterns_ebnf(content)
            .expect("escaped open-comment delimiter should not nest");
    }

    #[test]
    fn test_parse_config_escaped_close_in_comment() {
        /* \*) inside a comment does NOT close it */
        let content = concat!(
            r"(* has \*) but continues *)",
            "\n",
            "<integer> = /[0-9]+/ ;\n",
            "<float>   = /[0-9]+/ ;\n",
            "<string>  = /[a-z]+/ ;\n",
            "<ident>   = /[a-z]+/ ;\n",
        );
        parse_literal_patterns_ebnf(content)
            .expect("escaped close-comment delimiter should not close");
    }

    #[test]
    fn test_parse_config_unclosed_nested_comment() {
        let content = "(* outer (* inner *)\n<integer> = /[0-9]+/ ;";
        let result = parse_literal_patterns_ebnf(content);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("unclosed EBNF comment"));
    }

    #[test]
    fn test_parse_config_trailing_comment_with_nesting() {
        /* A trailing comment on a production line with nesting */
        let content = concat!(
            "<integer> = /[0-9]+/ (* see also: (* RFC 1234 *) *) ;\n",
            "<float>   = /[0-9]+/ ;\n",
            "<string>  = /[a-z]+/ ;\n",
            "<ident>   = /[a-z]+/ ;\n",
        );
        parse_literal_patterns_ebnf(content)
            .expect("nested comment in trailing position should parse");
    }

    /* ── Epsilon closure sanity check ──────────────────────────────────── */

    #[test]
    fn test_compiled_nfa_has_accepting_state() {
        let mut nfa = Nfa::new();
        let frag = compile_regex("[0-9]+", &mut nfa, TokenKind::Integer)
            .expect("should compile");
        nfa.add_epsilon(nfa.start, frag.start);

        /* The accept state should have TokenKind::Integer */
        assert_eq!(
            nfa.states[frag.accept as usize].accept,
            Some(TokenKind::Integer)
        );

        /* Verify epsilon closure from start includes the fragment start */
        let closure = epsilon_closure(&nfa, &[nfa.start]);
        assert!(
            closure.contains(&frag.start),
            "epsilon closure from NFA start should include fragment start"
        );
    }
}
