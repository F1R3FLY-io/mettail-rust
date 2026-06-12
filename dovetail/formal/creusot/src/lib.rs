#![allow(dead_code)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum AddResult {
    Added(usize),
    Overflow(usize),
}

#[requires(used@ <= budget@)]
#[ensures(match result {
    AddResult::Added(used_prime) =>
        used@ < budget@ && used_prime@ == used@ + 1 && used_prime@ <= budget@,
    AddResult::Overflow(used_prime) =>
        budget@ <= used@ && used_prime@ == used@,
})]
pub fn try_add_with_budget(budget: usize, used: usize) -> AddResult {
    if used < budget {
        AddResult::Added(used + 1)
    } else {
        AddResult::Overflow(used)
    }
}

#[requires(used@ <= budget@)]
#[ensures(match result {
    AddResult::Added(used_prime) => used_prime@ <= budget@,
    AddResult::Overflow(_) => true,
})]
pub fn added_never_overshoots_budget(budget: usize, used: usize) -> AddResult {
    try_add_with_budget(budget, used)
}

#[requires(used@ <= budget@)]
#[requires(budget@ <= used@)]
#[ensures(match result {
    AddResult::Overflow(used_prime) => used_prime@ == used@,
    AddResult::Added(_) => false,
})]
pub fn overflow_preserves_state_at_limit(budget: usize, used: usize) -> AddResult {
    try_add_with_budget(budget, used)
}

#[requires(used@ < budget@)]
#[ensures(match result {
    AddResult::Added(used_prime) => used_prime@ == used@ + 1,
    AddResult::Overflow(_) => false,
})]
pub fn add_succeeds_below_limit(budget: usize, used: usize) -> AddResult {
    try_add_with_budget(budget, used)
}
