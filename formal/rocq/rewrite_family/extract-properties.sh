#!/usr/bin/env bash
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
proof_dir=${1:-"$project_dir/theories"}
repo_root="$project_dir/../../.."
declare -A behavior_tests declared_groups used_groups
while IFS=$'\t' read -r property description; do
  [[ "$property" == property ]] && continue
  [[ -n "$property" && -z "${declared_groups[$property]+present}" ]]
  declared_groups[$property]=1
done < "$project_dir/property-behavior.tsv"
while IFS=$'\t' read -r property tests; do
  [[ "$property" == property ]] && continue
  [[ -n "$property" && -n "$tests" ]]
  [[ -n "${declared_groups[$property]+present}" && -z "${behavior_tests[$property]+present}" ]]
  IFS=';' read -r -a references <<< "$tests"
  for reference in "${references[@]}"; do
    test_path=${reference%#*}
    test_name=${reference##*#}
    [[ "$test_path" != "$reference" && -f "$repo_root/$test_path" ]]
    rg -q --fixed-strings "fn $test_name(" "$repo_root/$test_path"
  done
  behavior_tests[$property]=$tests
done < "$project_dir/behavior-tests.tsv"
[[ ${#behavior_tests[@]} -eq ${#declared_groups[@]} ]]

cd -- "$proof_dir"
printf 'model\tinvariant\tproperty\timplementation_status\timplementation_tests\n' > property-map.tsv

for proof_model in RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyPremises RewriteFamilyBoundary RewriteFamilyAuthored RewriteFamilyFocus RewriteFamilyNames RewriteFamilyAllocator RewriteFamilyAdapterRefinements RewriteFamilyContext RewriteContextSourceNames RewriteContextWireProjection RewriteContextTokenExtension RewriteFamilyDescriptors RootActivationProjection; do
  while read -r proof_kind proof_name proof_rest; do
    case "$proof_name" in
      family_check_is_exact|accepted_family_has_exact_arity)
        property=family_admission ;;
      accepted_family_has_no_escaped_argument|accepted_family_covers_each_introduced_binder|accepted_occurrence_has_exact_scoped_family|two_families_may_share_an_introduced_binder|unrelated_ambient_binder_is_not_required_as_an_argument|each_collected_occurrence_has_its_recorded_path_and_scope)
        property=family_scope ;;
      accepted_family_has_distinct_lexical_occurrences|generated_identity_is_fresh|scope_extension_preserves_distinct_identities|duplicate_lexical_occurrence_is_refused|shadowed_binders_keep_distinct_identities)
        property=lexical_identity ;;
      nearest_lexical_binder_wins|appended_scope_resolves_the_nearest_binder|leaving_a_binder_restores_outer_resolution|appended_scope_retains_the_outer_binder_identity)
        property=lexical_resolution ;;
      normalized_matching_extracts_exact_endpoint|normalized_reconstruction_preserves_context|lowered_matching_extracts_exact_family_endpoints|focused_family_uses_the_existing_single_hole_context|every_instantiated_occurrence_has_a_single_hole_focus)
        property=matching_reconstruction ;;
      write_binding_reads_exact_value|fresh_extension_preserves_other_bindings|transition_premise_preserves_metavariable_bindings|generated_pair_preserves_prior_environment|ordered_premises_preserve_non_target_bindings|source_overlay_reads_the_declared_endpoint|source_overlay_preserves_every_authored_binding)
        property=environment_preservation ;;
      explicit_family_step_iff_existing_premise|checked_family_matching_and_reconstruction_are_equivalent|bound_target_refuses_transition)
        property=single_family_transition ;;
      typed_context_plugging_preserves_endpoint_type|typed_bound_reference_is_in_scope|typed_constructor_has_exact_arity|checked_family_execution_preserves_parent_types|extraction_preserves_constructor_arity|value_sort_is_unique|typed_plugging_decomposes_into_context_and_endpoint|typed_child_step_preserves_parent_sort|typed_family_endpoint_update_preserves_parent_type|finite_declared_endpoint_updates_preserve_parent_type|authored_open_family_steps_preserve_parent_type|normalized_open_family_rules_preserve_parent_type)
        property=signature_typing ;;
      lexical_renaming_commutes_with_plugging|lexical_renaming_commutes_with_normalization|lexical_renaming_preserves_scope_order|injective_lexical_renaming_preserves_family_admission)
        property=lexical_renaming ;;
      extraction_exactly_preserves_both_authored_sides|extraction_rejects_changed_ordinary_metavariable|extraction_rejects_changed_lexical_arguments|extraction_has_unique_shape)
        property=paired_structure ;;
      extraction_commutes_with_ordinary_instantiation|lowering_preserves_instantiation|updating_a_unique_family_is_single_hole_plugging)
        property=ordinary_instantiation ;;
      accepted_shape_has_unique_family_occurrences|accepted_shape_has_unique_declarations|accepted_shape_uses_every_declared_family|accepted_shape_has_no_undeclared_family|accepted_family_roster_is_exact|hole_names_are_exactly_checked_family_ids)
        property=family_roster ;;
      lowering_removes_every_family_projection|normalized_rules_have_no_family_declarations|normalization_is_idempotent)
        property=normalization_idempotence ;;
      generated_source_avoids_authored_names|generated_target_avoids_authored_names|generated_source_names_are_injective|generated_target_names_are_injective|generated_source_and_target_names_are_disjoint|generated_names_are_fresh_in_supported_environment|built_request_sources_and_targets_are_disjoint|built_request_targets_are_unique|source_overlay_keeps_generated_targets_fresh|source_overlay_satisfies_existing_premise_freshness)
        property=generated_name_freshness ;;
      independent_transitions_execute_in_premise_order|ordered_premises_have_independent_transition_results|finite_family_steps_iff_ordered_existing_premises|two_premises_remain_two_ordered_child_transitions|finite_families_reconstruct_one_parent_step)
        property=ordered_family_premises ;;
      built_requests_follow_declaration_order_and_scopes|built_requests_use_checked_occurrence_scopes|admitted_family_rules_always_build_requests|built_request_family_order_equals_declaration_order|built_requests_use_the_proved_name_allocator|declaration_endpoints_equal_constructed_request_endpoints|declaration_transitions_equal_constructed_request_transitions)
        property=request_correspondence ;;
      ordinary_rules_keep_exact_identity|ordinary_rules_may_have_different_sides)
        property=legacy_identity ;;
      normalization_preserves_existing_rule_data)
        property=authored_rule_preservation ;;
      failed_normalization_keeps_the_entire_rule_store|successful_normalization_changes_only_the_selected_rule|a_failed_batch_preserves_every_original_rule|successful_batch_has_a_checked_result_for_every_rule)
        property=atomic_publication ;;
      authored_family_steps_iff_existing_core_rules)
        property=authored_core_correspondence ;;
      family_occurrence_paths_do_not_overlap|family_occurrence_path_has_one_location|collected_family_paths_do_not_overlap|collected_family_path_determines_the_complete_occurrence)
        property=occurrence_paths ;;
      authored_pattern_census_is_exact|authored_census_includes_unused_binder_names|whole_rule_census_covers_each_component)
        property=authored_name_census ;;
      encoded_binder_names_avoid_all_authored_names|encoded_binder_names_are_injective|distinct_occurrences_keep_distinct_encoded_names|generated_endpoints_avoid_encoded_binders)
        property=generated_name_freshness ;;
      encoded_names_preserve_family_admission)
        property=lexical_renaming ;;
      resolved_slot_contains_the_requested_name|slot_resolution_succeeds_exactly_for_present_names|different_names_cannot_share_a_resolved_slot|append_preserves_every_existing_slot|appending_a_fresh_name_assigns_the_next_slot|interning_returns_a_slot_for_the_requested_name|interning_preserves_all_prior_slots|interning_preserves_unique_name_rosters|encoded_binder_slots_cannot_collapse|fresh_typed_allocation_has_exact_admission|fresh_typed_allocation_preserves_every_existing_slot|fresh_typed_allocation_retains_requested_sort_and_role|full_slot_capacity_refuses_fresh_allocation|existing_binder_references_keep_the_binder_role|existing_inputs_use_the_requested_role|conflicting_slot_sorts_are_refused)
        property=compiler_slot_correspondence ;;
      selective_encoding_preserves_unique_binder_spellings|repeated_spellings_require_distinct_encoded_names|selective_encoding_is_injective_on_the_binder_roster|preserved_authored_alias_has_no_new_binder_collision|accepted_external_references_keep_their_exact_binder_names|ambiguous_external_references_are_refused|selective_encoded_binders_have_distinct_compiler_slots)
        property=selective_binder_encoding ;;
      search_success_contract|search_refusal_is_exact|checked_allocation_preserves_counter_bound|exhausted_counter_refuses_atomically|successful_allocations_with_monotone_counters_are_distinct|one_free_representable_candidate_guarantees_success)
        property=checked_name_allocator ;;
      path_eligibility_requires_matching_sort_evidence|disabled_context_disables_all_descendants|sibling_eligibility_uses_the_unchanged_parent|eligible_paths_preserve_the_existing_normalized_result|root_projection_needs_no_parent_edge|admitted_typed_child_step_preserves_parent_sort)
        property=typed_context_admission ;;
      materialization_preserves_every_indexed_leaf|materialized_reader_roster_is_the_original_roster|cached_reader_access_retains_original_payload_and_optional_flag|materialized_roster_preserves_arity_and_out_of_range)
        property=parameter_roster ;;
      diagnostic_metadata_erasure_preserves_the_original_scan|diagnostic_metadata_preserves_success_and_refusal|reported_index_resolves_the_offending_name_and_external_site|reported_ambiguity_is_refused_by_the_existing_name_contract)
        property=ambiguity_diagnostics ;;
      family_decoder_matches_the_independent_shape|family_shape_preserves_complete_domain_and_result_types|family_shapes_are_disjoint_from_ordinary_types|codomain_scan_preserves_the_ordered_domain_roster|encoded_family_context_round_trips|ordinary_contexts_keep_the_exact_legacy_value|ordinary_context_admission_is_exact|family_context_admission_is_exact|equation_and_intrinsic_contexts_cannot_admit_families|nested_rewrite_in_a_domain_is_refused)
        property=canonical_context_syntax ;;
      context_name_observation_matches_independent_relation|context_name_observation_refuses_strings_and_nonwords|context_name_validation_is_exact)
        property=source_context_names ;;
      canonical_type_wire_preserves_complete_values|legacy_context_wire_encodings_are_unchanged|selected_context_wire_decodes_to_the_original_type|extended_context_children_are_canonical_and_ordered|legacy_tags_cannot_be_nested_as_canonical_types|context_wire_preserves_admission_and_refusal)
        property=generated_context_wire ;;
      custom_reservation_preserves_exact_membership|lower_priority_custom_extension_preserves_prior_roster|custom_extension_preserves_old_primary|secondary_capture_keeps_existing_fork|custom_batch_preserves_exact_old_prefix)
        property=generated_context_tokens ;;
      registered_lookup_is_exact|unknown_registered_name_is_refused)
        property=canonical_registered_lookup ;;
      constructor_projection_is_exact|constructor_nth_preserves_order_and_range|product_projection_is_exact|product_nth_preserves_order_and_range|matching_descriptor_evidence_keeps_existing_path_admission)
        property=canonical_ordered_fields ;;
      unary_projection_is_exact|multiple_function_cannot_supply_unary_binders)
        property=canonical_unary_binders ;;
      collection_projection_is_exact)
        property=canonical_collection_fields ;;
      unknown_descriptor_supplies_no_fields|syntax_and_opaque_descriptors_do_not_supply_structural_fields|missing_or_incompatible_edge_disables_all_descendants)
        property=canonical_missing_evidence ;;
      pathmap_set_projection_matches_existing_kernel|pathmap_map_projection_matches_existing_kernel|pathmap_neutral_and_absent_modes_keep_existing_final_restrictions)
        property=canonical_pathmap_final_admission ;;
      reverse_lookup_has_last_binding_precedence|latest_exact_scoped_binding_wins|projection_exactly_matches_root_binding_specification|projection_preserves_exact_grounded_values|successful_projection_preserves_roster_order|absent_root_binding_is_omitted|undeclared_root_binding_is_omitted|unique_roster_has_no_projected_alias|declaration_roles_do_not_change_visibility)
        property=root_projection_values ;;
      different_activation_cannot_alias_root|local_append_preserves_every_root_lookup|local_only_history_publishes_no_bindings|local_bindings_preserve_projection_with_stable_grounding)
        property=root_projection_scopes ;;
      head_grounding_failure_returns_exact_error|later_grounding_failure_discards_projected_prefix|failed_projection_cannot_publish_any_prefix)
        property=root_projection_refusal ;;
      present_root_binder_survives_projection)
        property=root_binder_reconstruction ;;
      *) printf 'Unmapped theorem: %s.%s\n' "$proof_model" "$proof_name" >&2; exit 1 ;;
    esac
    [[ -n "${behavior_tests[$property]+present}" ]]
    used_groups[$property]=1
    printf '%s\t%s\t%s\tmapped_to_tests\t%s\n' "$proof_model" "$proof_name" "$property" "${behavior_tests[$property]}" >> property-map.tsv
  done < <(rg --no-filename '^Theorem ' "$proof_model.v")
done

[[ ${#used_groups[@]} -eq ${#behavior_tests[@]} ]]
