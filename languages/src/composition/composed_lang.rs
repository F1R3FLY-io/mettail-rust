//! Composed language combining Calculator and Lambda via `compose_languages!`.
//!
//! This generates a delegating wrapper — no new parser or Ascent program.
//! Parsing tries Calculator first, then Lambda, returning the first success.

use mettail_macros::compose_languages;

compose_languages! {
    name: CalcLambda,
    languages: [crate::calculator::Calculator, crate::lambda::Lambda],
}
