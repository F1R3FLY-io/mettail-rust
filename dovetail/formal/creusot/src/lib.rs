#![allow(dead_code)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum AddResult {
    Added(usize),
    Overflow(usize),
}

pub enum BudgetAdmission {
    Existing(usize, bool),
    AddedFresh(usize, bool),
    RefusedFresh(usize, bool),
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

#[requires(used@ <= budget@)]
#[ensures(match result {
    BudgetAdmission::Existing(used_prime, hit_prime) =>
        already_present
        && used_prime@ == used@
        && used_prime@ <= budget@
        && hit_prime == node_limit_hit,
    BudgetAdmission::AddedFresh(used_prime, hit_prime) =>
        !already_present
        && used@ < budget@
        && used_prime@ == used@ + 1
        && used_prime@ <= budget@
        && hit_prime == node_limit_hit,
    BudgetAdmission::RefusedFresh(used_prime, hit_prime) =>
        !already_present
        && budget@ <= used@
        && used_prime@ == used@
        && used_prime@ <= budget@
        && hit_prime,
})]
pub fn admit_enode_with_budget(
    budget: usize,
    used: usize,
    node_limit_hit: bool,
    already_present: bool,
) -> BudgetAdmission {
    if already_present {
        BudgetAdmission::Existing(used, node_limit_hit)
    } else if used < budget {
        BudgetAdmission::AddedFresh(used + 1, node_limit_hit)
    } else {
        BudgetAdmission::RefusedFresh(used, true)
    }
}

#[requires(used@ <= budget@)]
#[ensures(match result {
    BudgetAdmission::Existing(used_prime, _) => used_prime@ <= budget@,
    BudgetAdmission::AddedFresh(used_prime, _) => used_prime@ <= budget@,
    BudgetAdmission::RefusedFresh(used_prime, _) => used_prime@ <= budget@,
})]
pub fn admission_never_overshoots_budget(
    budget: usize,
    used: usize,
    node_limit_hit: bool,
    already_present: bool,
) -> BudgetAdmission {
    admit_enode_with_budget(budget, used, node_limit_hit, already_present)
}

#[requires(used@ <= budget@)]
#[ensures(match result {
    BudgetAdmission::Existing(used_prime, hit_prime) =>
        used_prime@ == used@ && hit_prime == node_limit_hit,
    BudgetAdmission::AddedFresh(_, _) => false,
    BudgetAdmission::RefusedFresh(_, _) => false,
})]
pub fn existing_enode_preserves_budget_state(
    budget: usize,
    used: usize,
    node_limit_hit: bool,
) -> BudgetAdmission {
    admit_enode_with_budget(budget, used, node_limit_hit, true)
}

#[requires(used@ < budget@)]
#[ensures(match result {
    BudgetAdmission::AddedFresh(used_prime, hit_prime) =>
        used_prime@ == used@ + 1 && hit_prime == node_limit_hit,
    BudgetAdmission::Existing(_, _) => false,
    BudgetAdmission::RefusedFresh(_, _) => false,
})]
pub fn fresh_enode_below_limit_adds_once(
    budget: usize,
    used: usize,
    node_limit_hit: bool,
) -> BudgetAdmission {
    admit_enode_with_budget(budget, used, node_limit_hit, false)
}

#[requires(used@ <= budget@)]
#[requires(budget@ <= used@)]
#[ensures(match result {
    BudgetAdmission::RefusedFresh(used_prime, hit_prime) =>
        used_prime@ == used@ && hit_prime,
    BudgetAdmission::Existing(_, _) => false,
    BudgetAdmission::AddedFresh(_, _) => false,
})]
pub fn fresh_enode_at_limit_sets_node_limit(
    budget: usize,
    used: usize,
    node_limit_hit: bool,
) -> BudgetAdmission {
    admit_enode_with_budget(budget, used, node_limit_hit, false)
}
