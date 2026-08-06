//! Test-only copy of the recursive LTL precedence equations superseded by the
//! production parser PDA.  Keep this module independent so it remains a useful
//! semantic oracle; bounded inputs only are passed to it.

use super::{parse_ltl, LtlFormula};

#[derive(Debug, Clone, PartialEq)]
enum LtlToken {
    True,
    False,
    Ident(String),
    Not,
    And,
    Or,
    Implies,
    Next,
    Finally,
    Globally,
    Until,
    Release,
    WeakU,
    LParen,
    RParen,
}

fn tokenize(input: &str) -> Result<Vec<LtlToken>, String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            ' ' | '\t' | '\n' | '\r' => i += 1,
            '(' => {
                tokens.push(LtlToken::LParen);
                i += 1;
            },
            ')' => {
                tokens.push(LtlToken::RParen);
                i += 1;
            },
            '!' => {
                tokens.push(LtlToken::Not);
                i += 1;
            },
            '&' => {
                tokens.push(LtlToken::And);
                i += usize::from(i + 1 < chars.len() && chars[i + 1] == '&') + 1;
            },
            '|' => {
                tokens.push(LtlToken::Or);
                i += usize::from(i + 1 < chars.len() && chars[i + 1] == '|') + 1;
            },
            '-' => {
                if i + 1 < chars.len() && chars[i + 1] == '>' {
                    tokens.push(LtlToken::Implies);
                    i += 2;
                } else {
                    return Err(format!("unexpected character '-' at position {}", i));
                }
            },
            c if c.is_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                tokens.push(match word.as_str() {
                    "true" => LtlToken::True,
                    "false" => LtlToken::False,
                    "X" => LtlToken::Next,
                    "F" => LtlToken::Finally,
                    "G" => LtlToken::Globally,
                    "U" => LtlToken::Until,
                    "R" => LtlToken::Release,
                    "W" => LtlToken::WeakU,
                    _ => LtlToken::Ident(word),
                });
            },
            c => return Err(format!("unexpected character '{}' at position {}", c, i)),
        }
    }
    Ok(tokens)
}

struct RecursiveParser {
    tokens: Vec<LtlToken>,
    pos: usize,
}

impl RecursiveParser {
    fn peek(&self) -> Option<&LtlToken> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) -> Option<&LtlToken> {
        let token = self.tokens.get(self.pos);
        if token.is_some() {
            self.pos += 1;
        }
        token
    }

    fn expect(&mut self, expected: &LtlToken) -> Result<(), String> {
        match self.advance() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(format!("expected {:?}, got {:?}", expected, token)),
            None => Err(format!("expected {:?}, got end of input", expected)),
        }
    }

    fn parse_implies(&mut self) -> Result<LtlFormula, String> {
        let lhs = self.parse_or()?;
        if self.peek() == Some(&LtlToken::Implies) {
            self.advance();
            let rhs = self.parse_implies()?;
            Ok(LtlFormula::Implies(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<LtlFormula, String> {
        let mut lhs = self.parse_and()?;
        while self.peek() == Some(&LtlToken::Or) {
            self.advance();
            let rhs = self.parse_and()?;
            lhs = LtlFormula::Or(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<LtlFormula, String> {
        let mut lhs = self.parse_until()?;
        while self.peek() == Some(&LtlToken::And) {
            self.advance();
            let rhs = self.parse_until()?;
            lhs = LtlFormula::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_until(&mut self) -> Result<LtlFormula, String> {
        let lhs = self.parse_unary()?;
        let operator = match self.peek() {
            Some(LtlToken::Until) => Some(0),
            Some(LtlToken::Release) => Some(1),
            Some(LtlToken::WeakU) => Some(2),
            _ => None,
        };
        let Some(operator) = operator else {
            return Ok(lhs);
        };
        self.advance();
        let rhs = self.parse_until()?;
        Ok(match operator {
            0 => LtlFormula::Until(Box::new(lhs), Box::new(rhs)),
            1 => LtlFormula::Release(Box::new(lhs), Box::new(rhs)),
            _ => LtlFormula::WeakUntil(Box::new(lhs), Box::new(rhs)),
        })
    }

    fn parse_unary(&mut self) -> Result<LtlFormula, String> {
        let operator = match self.peek() {
            Some(LtlToken::Not) => Some(0),
            Some(LtlToken::Next) => Some(1),
            Some(LtlToken::Globally) => Some(2),
            Some(LtlToken::Finally) => Some(3),
            _ => None,
        };
        let Some(operator) = operator else {
            return self.parse_primary();
        };
        self.advance();
        let body = self.parse_unary()?;
        Ok(match operator {
            0 => LtlFormula::Not(Box::new(body)),
            1 => LtlFormula::Next(Box::new(body)),
            2 => LtlFormula::Always(Box::new(body)),
            _ => LtlFormula::Eventually(Box::new(body)),
        })
    }

    fn parse_primary(&mut self) -> Result<LtlFormula, String> {
        match self.advance() {
            Some(LtlToken::True) => Ok(LtlFormula::True),
            Some(LtlToken::False) => Ok(LtlFormula::False),
            Some(LtlToken::Ident(name)) => Ok(LtlFormula::Atom(name.clone())),
            Some(LtlToken::LParen) => {
                let inner = self.parse_implies()?;
                self.expect(&LtlToken::RParen)?;
                Ok(inner)
            },
            Some(token) => Err(format!("unexpected token {:?} in primary position", token)),
            None => Err("unexpected end of input".to_string()),
        }
    }

    fn parse(&mut self) -> Result<LtlFormula, String> {
        let result = self.parse_implies()?;
        if self.pos < self.tokens.len() {
            return Err(format!(
                "unexpected token {:?} after complete formula",
                self.tokens[self.pos]
            ));
        }
        Ok(result)
    }
}

fn parse_ltl_recursive(input: &str) -> Result<LtlFormula, String> {
    let tokens = tokenize(input)?;
    if tokens.is_empty() {
        return Err("empty input".to_string());
    }
    RecursiveParser { tokens, pos: 0 }.parse()
}

fn assert_equivalent(input: &str) {
    assert_eq!(
        parse_ltl(input),
        parse_ltl_recursive(input),
        "production PDA diverged from recursive equations for {input:?}"
    );
}

#[test]
fn ltl_parser_pda_matches_the_bounded_recursive_equations() {
    for input in [
        "p",
        "true",
        "false",
        "!!p",
        "X ! G F p",
        "p & q",
        "p || q && r",
        "p && q || r && s",
        "p U q U r",
        "p R q W r U s",
        "p -> q -> r",
        "p -> q || r && s U t",
        "(p)",
        "((p && q) || (!r -> F s))",
        "error_state && token_matched",
        "",
        "   ",
        "-",
        "$",
        "(",
        "(p",
        "(p && q",
        "p)",
        "p q",
        "p ->",
        "!!",
        "p U",
        "&& p",
        "p && && q",
        "p -> -> q",
        "p (q)",
    ] {
        assert_equivalent(input);
    }

    for depth in 1..=64 {
        assert_equivalent(&format!("{}p", "!XGF".repeat(depth)));
        assert_equivalent(&format!("{}p{}", "(".repeat(depth), ")".repeat(depth)));
        assert_equivalent(
            &(0..=depth)
                .map(|index| format!("p{index}"))
                .collect::<Vec<_>>()
                .join(" -> "),
        );
        assert_equivalent(
            &(0..=depth)
                .map(|index| format!("p{index}"))
                .collect::<Vec<_>>()
                .join(if depth % 2 == 0 { " U " } else { " R " }),
        );
    }
}

#[test]
fn ltl_parser_traverses_twenty_thousand_levels_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("ltl-parser-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let unary = format!("{}p", "!".repeat(DEPTH));
            drop(parse_ltl(&unary).expect("parse a 20,000-deep unary chain"));

            let parenthesized = format!("{}p{}", "(".repeat(DEPTH), ")".repeat(DEPTH));
            drop(parse_ltl(&parenthesized).expect("parse 20,000 nested parentheses"));

            let implication = std::iter::repeat_n("p", DEPTH + 1)
                .collect::<Vec<_>>()
                .join(" -> ");
            drop(parse_ltl(&implication).expect("parse a 20,000-deep implication chain"));

            let until = std::iter::repeat_n("p", DEPTH + 1)
                .collect::<Vec<_>>()
                .join(" U ");
            drop(parse_ltl(&until).expect("parse a 20,000-deep until chain"));
        })
        .expect("spawn LTL parser small-stack worker")
        .join()
        .expect("LTL parser small-stack worker must not overflow");
}
