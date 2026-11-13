// SPDX-License-Identifier: MIT

//! The throwaways, one module per root witness beside this directory, each claiming `false` from its
//! witness's requires. tools/check-throwaways.py writes them and expects Verus to refuse each;
//! compiled only under cfg(throwaway). design/witness-per-way-an-operation-succeeds/.
pub mod boot_space_switch;
pub mod built_process_sealed;
pub mod check_current_kept;
pub mod check_current_moved_off;
pub mod dead_device_space_freed;
pub mod dead_frame_freed;
pub mod dead_large_frame_freed;
pub mod dead_table_page_freed;
pub mod destroyed_thread_freed;
pub mod device_frame_reused_after_iommu_flush;
pub mod inspect;
pub mod kernel_init;
pub mod nested_frame_mapped;
pub mod process_binds_a_device;
pub mod process_block_retyped;
pub mod process_holds_capability;
pub mod process_moves_a_device_between_spaces;
pub mod process_space_cut;
pub mod root_begins_zeroing_a_2m_frame;
pub mod root_claims_a_capability;
pub mod root_dispatches;
pub mod root_enters_the_kernel;
pub mod root_links_a_table_into_its_own_space;
pub mod root_maps_a_frame_into_its_own_space;
pub mod root_maps_one_frame_into_two_processes;
pub mod root_powers_off;
pub mod root_prints;
pub mod root_probes_and_unmaps_its_frame;
pub mod root_receives_a_device;
pub mod root_retypes_a_freed_2m_frame;
pub mod root_revokes_a_shared_frame;
pub mod root_revokes_at_the_epoch_limit;
pub mod root_revokes_more_than_a_budget;
pub mod root_suspends_itself;
pub mod root_thread_enters;
pub mod switch_between_processes;
pub mod thread_registers;
pub mod thread_switch;
