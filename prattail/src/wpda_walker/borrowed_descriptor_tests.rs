use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::wpda_rule_analysis::collection::assembly::GeneratedCollectionSpec;
use crate::wpda_runtime::FrameCtx;

struct OwnedDescriptors {
    collection: GeneratedCollectionSpec,
    wrappers: Vec<u16>,
    keyword: String,
}

impl WpdaEngine<LexicographicWeight> for OwnedDescriptors {
    fn step(
        &self,
        _: &WpdaState,
        _: &WpdaGss<LexicographicWeight>,
        _: Option<&WpdaGssNode>,
        _: usize,
        _: &dyn WpdaTokenSource,
        _: FrameCtx<'_>,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }

    fn collection_spec(&self, _: u16, _: u16, _: u8) -> Option<CollectionSpec<'_>> {
        Some(self.collection.as_borrowed())
    }

    fn kv_separator_for_collection(&self, _: u16, _: u16, _: u8) -> Option<&str> {
        self.collection.kv_sep.as_deref()
    }

    fn trigger_unary_wrappers_into(&self, _: u16, _: u16) -> &[u16] {
        &self.wrappers
    }

    fn prefix_cast_keyword(&self, _: u16, _: u16) -> Option<&str> {
        Some(&self.keyword)
    }
}

fn owned_descriptors() -> OwnedDescriptors {
    OwnedDescriptors {
        collection: GeneratedCollectionSpec {
            open: "[owned".into(),
            has_synth_paren: true,
            close: "owned]".into(),
            sep: ";".into(),
            min_elements: 1,
            kv_sep: Some("=>".into()),
            kv_value_optional: true,
            element_src_idx: Some(7),
            close_resumes_via_unwinding: true,
        },
        wrappers: vec![9, 3, 9],
        keyword: "owned_keyword".into(),
    }
}

#[test]
fn owned_descriptor_views_borrow_all_original_fields() {
    let engine = owned_descriptors();
    let spec = engine.collection_spec(2, 3, 4).expect("owned slot");
    assert_eq!(
        spec,
        CollectionSpec {
            open: "[owned",
            has_synth_paren: true,
            close: "owned]",
            sep: ";",
            min_elements: 1,
            kv_sep: Some("=>"),
            kv_value_optional: true,
            element_src_idx: Some(7),
            close_resumes_via_unwinding: true,
        }
    );
    assert_eq!(spec.open.as_ptr(), engine.collection.open.as_ptr());
    assert_eq!(spec.close.as_ptr(), engine.collection.close.as_ptr());
    assert_eq!(spec.sep.as_ptr(), engine.collection.sep.as_ptr());
    assert_eq!(
        spec.kv_sep.expect("kv separator").as_ptr(),
        engine
            .collection
            .kv_sep
            .as_ref()
            .expect("owned kv separator")
            .as_ptr()
    );
    assert_eq!(engine.kv_separator_for_collection(2, 3, 4), Some("=>"));
    assert_eq!(engine.trigger_unary_wrappers_into(7, 2), &[9, 3, 9]);
    assert_eq!(engine.trigger_unary_wrappers_into(7, 2).as_ptr(), engine.wrappers.as_ptr());
    assert_eq!(
        engine.prefix_cast_keyword(2, 9).expect("keyword").as_ptr(),
        engine.keyword.as_ptr()
    );
}

#[test]
fn walker_projects_frame_context_from_owned_storage() {
    let walker = WpdaWalker::<LexicographicWeight, _>::new(owned_descriptors(), 0);
    let frame = walker
        .cgll_pure_project_frame_ctx(CgllPureFrameKey {
            category_src_idx: 2,
            rule_index_in_category: 3,
            slot_idx: 4,
        })
        .expect("owned collection frame");
    assert_eq!(frame.close.as_ptr(), walker.engine.collection.close.as_ptr());
    assert!(frame.matches_delim("owned]"));
    assert!(frame.matches_delim(";"));
    assert!(frame.matches_delim("=>"));
    assert!(!frame.matches_delim("[owned"));
    assert!(!FrameCtx::EMPTY.matches_delim(""));
}
