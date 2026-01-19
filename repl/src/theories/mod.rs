// Theory implementations for the REPL
//
// Each theory wrapper implements the Theory trait, providing:
// - Parsing (using the theories crate)
// - Ascent execution
// - Result extraction

pub mod ambient;
// pub mod calculator;
pub mod rhocalc;

pub use ambient::AmbCalculusTheory;
// pub use calculator::CalculatorTheory;
pub use rhocalc::RhoCalculusTheory;
