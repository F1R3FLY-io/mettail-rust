//! Sig-B Blocker-3 M7.0 single-input diagnostic probe (pgmcp experiment #9,
//! 2026-06-01, temporary). Parses ONE input (argv[1]) via either `Int::parse`
//! (default) or `CalculatorLanguage::parse_term` (when argv[2] == "term") in
//! ISOLATION, so the `[SIGB_M70]` span-anchored diagnostic for that single
//! input is not interleaved with any other. Run under `SIGB_CROSSWRAP=1` to
//! emit the M7.0 `[C7-n]` evidence (SPPF span + span-anchored pairing scan)
//! for exactly one residual.
//!
//! Run:
//!   SIGB_CROSSWRAP=1 cargo run -p mettail-languages --release \
//!     --example b3_m70_one -- 'int(y != true > x < "qua")'
//!   SIGB_CROSSWRAP=1 cargo run -p mettail-languages --release \
//!     --example b3_m70_one -- 'float(float(10, 64), 64)' term

use mettail_languages::calculator::{self as calc, Int};
use mettail_runtime::Language;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let input = args.get(1).cloned().unwrap_or_default();
    let mode = args.get(2).map(|s| s.as_str()).unwrap_or("int");
    mettail_runtime::clear_var_cache();
    if mode == "term" {
        let lang = calc::CalculatorLanguage;
        match lang.parse_term(&input) {
            Ok(t) => println!("OK   [parse_term]   {input:?}  ->  {t}"),
            Err(e) => println!("ERR  [parse_term]   {input:?}  ->  {e:?}"),
        }
    } else {
        match Int::parse(&input) {
            Ok(t) => println!("OK   [Int::parse]   {input:?}  ->  {t}"),
            Err(e) => println!("ERR  [Int::parse]   {input:?}  ->  {e:?}"),
        }
    }
}
