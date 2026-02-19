//! Parsing: pre-parse (structure for type inference) and full parse (ascent + schema → Query).

mod ascent_parse;
mod pre_parse;

pub use ascent_parse::{parse_query, ParseError};
pub use pre_parse::{PreParseError, PreParsedBodyAtom, PreParsedRule, pre_parse_rule};
