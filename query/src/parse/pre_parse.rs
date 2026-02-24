//! Minimal rule parser for type inference.
//!
//! Extracts head (relation name + arg names) and body (list of atoms with relation name + args)
//! without full type information. Handles `<--`, `,`, `!`, `_`, and nested parens.

/// Result of pre-parsing a single rule: head and body structure only.
#[derive(Debug, Clone)]
pub struct PreParsedRule {
    pub head_rel: String,
    /// Head arguments: variable name, or "_" for wildcard.
    pub head_args: Vec<String>,
    pub body_atoms: Vec<PreParsedBodyAtom>,
}

#[derive(Debug, Clone)]
pub struct PreParsedBodyAtom {
    pub negated: bool,
    pub relation: String,
    /// Argument strings: variable name, "_", or constant (e.g. number, quoted string).
    pub args: Vec<String>,
}

#[derive(Debug)]
pub struct PreParseError {
    pub message: String,
}

impl std::fmt::Display for PreParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for PreParseError {}

/// Pre-parse a rule string: "head_rel(a, b) <-- atom1, !atom2."
/// Returns head relation, head args, and body atoms. Trailing '.' is optional for robustness.
pub fn pre_parse_rule(s: &str) -> Result<PreParsedRule, PreParseError> {
    let s = s.trim();
    if s.is_empty() {
        return Err(PreParseError { message: "Empty rule".into() });
    }

    // Split on "<--" at top level (not inside parens)
    let (head_str, body_str) = split_on_arrow(s)?;
    let head_str = head_str.trim();
    let body_str = body_str.trim().strip_suffix('.').unwrap_or(body_str).trim();

    // Parse head: rel(arg1, arg2, ...)
    let (head_rel, head_args) = parse_atom(head_str)?;

    // Parse body: comma-separated atoms at top level
    let body_atoms = parse_body(body_str)?;

    Ok(PreParsedRule { head_rel, head_args, body_atoms })
}

/// Find "<--" not inside parentheses.
fn split_on_arrow(s: &str) -> Result<(&str, &str), PreParseError> {
    let mut depth = 0u32;
    let bytes = s.as_bytes();
    let mut i = 0;
    while i + 2 < bytes.len() {
        match (bytes.get(i), bytes.get(i + 1), bytes.get(i + 2)) {
            (Some(b'<'), Some(b'-'), Some(b'-')) if depth == 0 => {
                return Ok((s[..i].trim(), s[i + 3..].trim()));
            },
            (Some(b'('), _, _) => depth = depth.saturating_add(1),
            (Some(b')'), _, _) => depth = depth.saturating_sub(1),
            _ => {},
        }
        i += 1;
    }
    Err(PreParseError {
        message: "Rule must contain '<--' (head <-- body)".into(),
    })
}

/// Parse "rel(arg1, arg2, ...)" into (rel, args). Args are trimmed strings.
fn parse_atom(s: &str) -> Result<(String, Vec<String>), PreParseError> {
    let s = s.trim();
    let open = s.find('(').ok_or_else(|| PreParseError {
        message: "Atom must be relation(args)".into(),
    })?;
    let rel = s[..open].trim();
    if rel.is_empty()
        || !rel
            .chars()
            .next()
            .map(|c| c.is_alphabetic())
            .unwrap_or(false)
    {
        return Err(PreParseError {
            message: "Relation name must be an identifier".into(),
        });
    }
    let args_str = s[open + 1..].trim();
    let close = find_matching_paren(args_str, b'(').ok_or_else(|| PreParseError {
        message: "Unmatched parentheses in atom".into(),
    })?;
    let args_str = args_str[..close].trim();
    let args = if args_str.is_empty() {
        Vec::new()
    } else {
        split_top_level(args_str, ',')
            .into_iter()
            .map(|a| a.trim().to_string())
            .collect()
    };
    Ok((rel.to_string(), args))
}

/// Split s by comma at top level (depth 0). Does not split inside ().
fn split_top_level(s: &str, sep: char) -> Vec<String> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ if c == sep && depth == 0 => {
                result.push(s[start..i].to_string());
                start = i + 1;
            },
            _ => {},
        }
    }
    result.push(s[start..].to_string());
    result
}

/// Find position of closing ')' that matches the first '(' in s. s should be the content after the opening '('.
fn find_matching_paren(s: &str, _open: u8) -> Option<usize> {
    let mut depth = 1i32;
    for (i, c) in s.bytes().enumerate() {
        if c == b'(' {
            depth += 1;
        } else if c == b')' {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// Parse body: "atom1, atom2, !atom3" into list of PreParsedBodyAtom.
fn parse_body(s: &str) -> Result<Vec<PreParsedBodyAtom>, PreParseError> {
    if s.is_empty() {
        return Ok(Vec::new());
    }
    let parts = split_top_level(s, ',');
    let mut atoms = Vec::new();
    for part in parts {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let (negated, rest) = if let Some(stripped) = part.strip_prefix('!') {
            (true, stripped.trim())
        } else {
            (false, part)
        };
        let (relation, args) = parse_atom(rest)?;
        atoms.push(PreParsedBodyAtom { negated, relation, args });
    }
    Ok(atoms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_rule() {
        let r =
            pre_parse_rule("query(result) <-- path(term, result), !rw_proc(result, _).").unwrap();
        assert_eq!(r.head_rel, "query");
        assert_eq!(r.head_args, ["result"]);
        assert_eq!(r.body_atoms.len(), 2);
        assert_eq!(r.body_atoms[0].negated, false);
        assert_eq!(r.body_atoms[0].relation, "path");
        assert_eq!(r.body_atoms[0].args, ["term", "result"]);
        assert_eq!(r.body_atoms[1].negated, true);
        assert_eq!(r.body_atoms[1].relation, "rw_proc");
        assert_eq!(r.body_atoms[1].args, ["result", "_"]);
    }

    #[test]
    fn test_head_multi_arg() {
        let r = pre_parse_rule("q(a, b, c) <-- r(a), s(b), t(c).").unwrap();
        assert_eq!(r.head_rel, "q");
        assert_eq!(r.head_args, ["a", "b", "c"]);
        assert_eq!(r.body_atoms.len(), 3);
    }
}
