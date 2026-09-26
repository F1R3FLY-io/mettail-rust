//! Reserved walker actions, never GrammarCore productions. Engine and provider
//! admission keep every real category index strictly below `CATEGORY`.
pub const CATEGORY: u16 = u16::MAX;
pub const GROUPING_RULE: u16 = u16::MAX - 4;
pub const HOLE_RULE: u16 = u16::MAX - 5;
pub const GROUPING_ACTION: u32 = ((CATEGORY as u32) << 16) | GROUPING_RULE as u32;
pub const HOLE_ACTION: u32 = ((CATEGORY as u32) << 16) | HOLE_RULE as u32;

pub fn category_domain_is_disjoint(count: usize) -> bool {
    count <= usize::from(CATEGORY)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn structural_actions_have_checked_disjoint_category_domain() {
        assert!(category_domain_is_disjoint(usize::from(CATEGORY)));
        assert!(!category_domain_is_disjoint(usize::from(CATEGORY) + 1));
        assert_ne!(GROUPING_ACTION, HOLE_ACTION);
        assert_ne!(GROUPING_ACTION, u32::MAX - 1, "optional-present packing");
        for category in [0, CATEGORY - 1] {
            for rule in [0, GROUPING_RULE, HOLE_RULE, u16::MAX] {
                let action = (u32::from(category) << 16) | u32::from(rule);
                assert_ne!(action, GROUPING_ACTION);
                assert_ne!(action, HOLE_ACTION);
            }
        }
    }
}
