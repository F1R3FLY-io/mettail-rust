# Installed-lookahead proof-to-property map

Status: in progress for the admitted Regex demo slice. This map distinguishes a compiled theorem, an executable generated property, an example-based regression, and an assumption still requiring runtime refinement. None is substituted for another.

The source model is [InstalledLookaheadEveryTrace.v](../../../formal/rocq/runtime_grammar/theories/InstalledLookaheadEveryTrace.v). The admitted runtime domain is one closed installed root or one exact top-level reflected expression beside ordinary Rholang processes. Nested or transported guests, multiple active guest slots, and provider-aware installed-guest resumption are refused. The broader model's multi-slot statements therefore do not establish that those shapes work in Rust. The [integration contract](../plans/installed-gslt-lookahead-integration.md) describes the public boundary and its diagram.

## Reading the evidence

An executable property below means a generated test that calls production code, not a second implementation of the matcher. An example is useful regression evidence but does not exhaust an input family. A Rocq theorem is conditional on its stated hypotheses: in particular, `CompleteRoster` asserts that enumeration is complete, and the abstract `HostChecker` is not a proof of RSpace matching. The one-step semantic validator checks witness shape and bounds; concrete receipt production and host charge correspondence require separate implementation evidence.

## Declaration inventory and runtime correspondence

### Request channel and legacy separation

Model declarations: `legacy_installed_subject_is_never_authorized`, `legacy_host_or_static_request_is_preserved`, and `request_channel_separates_legacy_data_from_v2_envelopes`.

Production seam: [lookahead request encoding](../../../rholang-runtime/src/lookahead.rs) and [request parsing/admission](../../../rholang-runtime/src/speculation/server.rs). `generated_request_channels_keep_legacy_host_and_installed_authority_disjoint` exercises 128 generated host-expression bags and guest placements. It checks ordinary host preservation on the legacy and v2 channels, refusal of an installed guest without an owner claim, and disjoint v2/v3 decoding in both directions. `request_operands_are_read_or_refused`, `versioned_request_enforces_exact_ordered_binding_paths`, and the public Regex application test remain complementary examples. This property establishes channel separation for the admitted one-top-level-guest domain, not arbitrary multi-slot envelopes.

### Binding paths, authority, and request examples

Model declarations: `path_eqb_eq`, `binding_matches_preserves_path`, `bindings_match_exact_paths`, `admitted_installed_envelope_has_exact_canonical_paths`, `admitted_binding_has_unique_live_authority`, `direct_lexical_request_admits_exact_selector`, `received_request_needs_explicit_owner_binding`, `composite_children_need_exact_distinct_paths`, `forged_ambiguous_and_mismatched_bindings_refuse`, and `revoked_and_unfunded_rights_refuse`.

Production seam: [exact occurrence scanning](../../../rholang-runtime/src/speculation/occurrences.rs), `server::admit_binding`, and the installed language table's live authorization. The generated `exact_top_level_locator_splits_and_rejoins` and `nested_reflected_guest_never_disappears_from_the_scan` properties cover exact v3 location and fail-closed nested scanning.

`generated_top_level_admission_requires_exact_live_owner_and_locator` checks 128 placements with valid and forged handles, exact and wrong indices, categories, contexts, and reflected-language commitments. It also refuses missing, duplicated, nested, and unfunded guests. `generated_native_owner_admission_requires_exact_handle_sort_path_and_context` checks 128 native String values with valid and forged handles, wrong category and carrier sort, non-root, duplicate and overlapping paths, nonzero context, and zero host funding. `generated_native_admission_rechecks_reduce_right_and_revocation_generation` checks 128 generated values before revocation against full and attenuated rights, then 128 values after reinstallation against stale and fresh generations. The `admission` test group passed 16/16 after these additions.

`native_root_rejects_forged_and_revoked_installed_owner_handles`, `top_level_guest_admission_requires_exact_locator_and_live_owner`, and `versioned_request_enforces_exact_ordered_binding_paths` remain complementary examples. The model's two-child *acceptance* example is outside the admitted demo domain; the demo refuses it, and multi-slot acceptance requires the later locator/provenance refinement. The model's `need_observe` parameter is not proof that every published Rust result currently checks `Observe`; the precise `Reduce`/`Observe` publication policy remains a separate authority obligation.

### Checked guest firing and effects

Model declarations: `nth_error_replace_nth`, `guest_fire_preserves_owner_sort_and_host`, `guest_fire_requires_live_reduce_binding_and_pure_step`, `guest_fire_preserves_authority_snapshot`, and `guest_fire_has_no_committable_effects`.

Production seam: [installed provider](../../../rholang-runtime/src/speculation/installed_provider.rs), `InstalledFltAdapter`, and [SemanticTransitionKernel](../../../dovetail-runtime/src/semantic_transition_kernel.rs). `installed_regex_root_uses_checked_rewrite_roster_and_retains_proofs` and `top_level_installed_guest_and_host_comm_share_one_every_trace_search` are examples. Generate one-slot checked rewrites across valid and invalid owner/sort/source/effect cases; assert the host snapshot is unchanged by a guest edge and its exact guest location alone changes. `nth_error_replace_nth` is a proof-local list lemma whose runtime obligation is that frame property, not a separately exported list algorithm.

### Complete roster, receipts, and work

Model declarations: `fired_roster_retains_exact_occurrences`, `fired_roster_receipts_and_work_are_exact`, `fired_roster_has_no_guest_committable_effects`, and `guest_occurrence_has_positive_logical_work`.

Production seam: `InstalledCheckedGuestProvider::complete_roster`, the existing one-step kernel's `ProvenSteps`, and [Explorer](../../../rholang-runtime/src/speculation/search.rs). `checked_equal_target_proofs_survive_existing_bfs_as_distinct_paths` is an example. A generated one-slot roster property must compare every emitted occurrence, proof identity, receipt, and aggregate work with the kernel's single call; no equal-target coalescing is allowed. Full Rust-to-Rocq grade, effects, and component-work refinement is not established by this model and belongs to the broader post-demo correspondence.

### Host-only refinement and trace extension

Model declarations: `host_only_public_path_keeps_process_nodes`, `trace_last_edge_extend`, `map_trace_last_edge_extend`, `last_snoc`, `selected_edge_appends_exactly_one_configuration`, `host_only_roster_orders`, `increasing_seq`, `host_only_roster_is_canonical`, `host_only_roster_refines_checked_host_successors`, and `host_only_expansion_refines_one_every_trace_level`.

Production seam: `ReductionTrace` in [speculation.rs](../../../rholang-runtime/src/speculation.rs) and host rendezvous enumeration in [search.rs](../../../rholang-runtime/src/speculation/search.rs). The generated `generated_mixed_trace_preserves_every_edge_and_terminal_state` and `generated_host_only_trace_preserves_legacy_public_path` properties cover exact trace extension and legacy public-path identity. `trace_last_edge_extend`, `map_trace_last_edge_extend`, and `last_snoc` are proof-local steps discharged by the generated extension property. `host_only_roster_orders` and `increasing_seq` are proof-local order lemmas; a generated production property still needs to compare host enumeration and the every-trace expansion on finite shared-domain stores. The abstract `HostChecker` does not discharge that correspondence by itself.

### Complete expansion, zero bound, refusal, and publication

Model declarations: `rejected_current_authority_cannot_publish`, `every_complete_occurrence_gets_one_trace`, `published_complete_roster_has_no_partial_prefix`, `mixed_host_guest_roster_keeps_two_occurrences`, `zero_step_empty_roster_succeeds`, `zero_step_enabled_roster_is_truncated`, `zero_step_incomplete_cannot_succeed`, `zero_step_revoked_is_refused`, `incomplete_roster_cannot_certify_success_or_no_successor`, `failed_roster_never_publishes_a_partial_prefix`, `published_traces_rechecked_live`, `refusal_and_truncation_never_publish_success`, `revoked_at_publication_discards_complete_traces`, and `process_path_retains_every_successor`.

Production seam: `Explorer::explore`, [service response assembly](../../../rholang-runtime/src/speculation/service.rs), and guarded [server publication](../../../rholang-runtime/src/speculation/server.rs). The generated mixed-trace property covers `process_path_retains_every_successor`. `checked_guest_cut_retains_slots_and_resume_revalidates_before_firing`, `refused_complete_guest_roster_never_returns_partial_exploration`, `installed_publication_commits_once_only_while_every_owner_is_live`, and the public Regex application route are examples. Generate complete versus incomplete roster, zero-step, exhausted, revoked, and failed-provider cases at the production boundary. Assert the entire response is withheld on refusal and that every published leaf is live; a partial prefix must never be mistaken for a complete answer. The model does not itself prove atomicity of the real RSpace produce or its guarded commit.

### Equal targets and public proof identity

Model declarations: `equal_target_different_rule_counterexample`, `equal_target_distinct_proofs_collide_in_process_path`, and `proof_markers_separate_equal_targets_and_leave_terminal_state_last`.

Production seam: `ReductionTrace::extend_guest` and [PathMap delivery](../../../rholang-runtime/src/speculation/delivery.rs). The generated `generated_equal_target_proofs_remain_distinct` property checks exact typed/public nodes; `pathmap_retains_equal_terminal_guest_proofs_as_two_entries` is an example at delivery. Generate PathMap membership for arbitrary distinct proof ordinals with equal terminal processes. Do not claim mathematical digest injectivity: exact proof markers preserve identity, while the digest is a cryptographic commitment.

### Typed top-level locator

Model declarations: `path_eqb_refl`, `locator_eqb_exact`, `locator_domains_disjoint`, and `exact_split_rejoin` in `CompositeLocator`.

Production seam: v2/v3 envelope decoding in [server.rs](../../../rholang-runtime/src/speculation/server.rs) and [the bounded scanner/split helper](../../../rholang-runtime/src/speculation/occurrences.rs). `exact_top_level_locator_splits_and_rejoins` and `generated_top_level_admission_requires_exact_live_owner_and_locator` are generated properties; `typed_top_level_scan_names_exact_expression_and_rejects_nested_guest` is an example. `generated_request_channels_keep_legacy_host_and_installed_authority_disjoint` rejects cross-version envelopes in both directions. `path_eqb_refl` is proof-local. Malformed locator fields within a version still need generated coverage. The model's exact locator equality is a structural law, not a claim that arbitrary nested guests are admitted.

### Resource settlement on response and refusal

Model declarations: `refusal_retains_identical_comm_charge`, `completed_publication_requires_full_charge`, `refusal_never_publishes_but_retains_partial_charge`, and `over_budget_never_publishes` in `ChargeSettlement`.

Production seam: `LookaheadAttempt::settle` and `charge_host_comms`. The generated `comm_settlement_charges_exact_affordable_prefix` property checks 128 affordable and unaffordable count/capacity cases against the production charge loop; `refusal_after_host_comm_retains_and_settles_the_comm_receipt` demonstrates a real post-COMM provider refusal and insufficient-host withholding. The feature-enabled public Regex route passed after the settlement change. The Rocq `capacity` is the number of affordable `reserve_comm` calls at the selected weight, not raw phlogiston. This covers the admitted service settlement boundary, not complete multi-slot work attribution.

## Verification boundary

The property names above are runnable tests, not declarations of campaign completion. The remaining generated properties are explicit M1 verification work for the admitted slice. The general multi-slot abstraction map, concrete enumeration completeness, host-store transport, full receipt/work refinement, and cross-language authority policy require the separate post-demo proof and implementation. No parser, matcher, automaton, or rewrite relation is re-derived to close a test gap.
