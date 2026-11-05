use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::pptr::PointsTo;
use crate::trap::*;
use crate::array::Array;
use crate::process_manager::endpoint::*;
use crate::process_manager::process::*;
use crate::process_manager::container::*;
use crate::process_manager::thread::*;
use crate::process_manager::cpu::*;
use crate::pptr::PPtr;
use crate::process_manager::thread_util_t::*;
use crate::process_manager::proc_util_t::*;
use crate::process_manager::container_util_t::*;
use crate::process_manager::endpoint_util_t::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::array_set::ArraySet;
use core::mem::MaybeUninit;
use crate::trap::Registers;
use crate::process_manager::container_tree::*;
use crate::process_manager::process_tree::*;
use crate::process_manager::spec_proof::*;
use crate::quota::Quota;

impl ProcessManager {
    #[verifier::rlimit(200)]
    pub fn new_container_with_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        pt_regs: Registers,
        new_pcid: Pcid,
        new_quota: &Quota,
        page_ptr_1: PagePtr,
        page_perm_1: Tracked<PagePerm4k>,
        page_ptr_2: PagePtr,
        page_perm_2: Tracked<PagePerm4k>,
        page_ptr_3: PagePtr,
        page_perm_3: Tracked<PagePerm4k>,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr_1) == false,
            old(self).page_closure().contains(page_ptr_2) == false,
            old(self).page_closure().contains(page_ptr_3) == false,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).depth != usize::MAX,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k - 3 >= new_quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.spec_greater(new_quota),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children.len() < CONTAINER_CHILD_LIST_LEN,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr,endpoint_index).unwrap().rf_counter_is_full() == false 
            || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),).rf_counter_is_full() == false,
            forall|p_ptr_i: ProcPtr|
                #![trigger old(self).proc_dom().contains(p_ptr_i) ]
                old(self).proc_dom().contains(p_ptr_i) ==> old(self).get_proc(p_ptr_i).pcid != new_pcid,
            page_perm_1@.is_uninit(),
            page_perm_1@.addr() == page_ptr_1,
            crate::util::page_ptr_util_u::page_ptr_valid(page_ptr_1),
            page_perm_2@.is_uninit(),
            page_perm_2@.addr() == page_ptr_2,
            crate::util::page_ptr_util_u::page_ptr_valid(page_ptr_2),
            page_perm_3@.is_uninit(),
            page_perm_3@.addr() == page_ptr_3,
            crate::util::page_ptr_util_u::page_ptr_valid(page_ptr_3),
            page_ptr_1 != page_ptr_2,
            page_ptr_1 != page_ptr_3,
            page_ptr_2 != page_ptr_3,
        ensures
            final(self).wf(),
            final(self).page_closure() =~= old(self).page_closure().insert(page_ptr_1).insert(
                page_ptr_2,
            ).insert(page_ptr_3),
            final(self).proc_dom() =~= old(self).proc_dom().insert(page_ptr_2),
            final(self).endpoint_dom() == old(self).endpoint_dom(),
            final(self).container_dom() == old(self).container_dom().insert(page_ptr_1),
            final(self).thread_dom() == old(self).thread_dom().insert(page_ptr_3),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                - 3 - new_quota.mem_4k == final(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_2m
                - new_quota.mem_2m == final(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_2m,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_1g
                - new_quota.mem_1g == final(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_1g,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.pcid
                - new_quota.pcid == final(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).quota.pcid,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.ioid
                - new_quota.ioid == final(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).quota.ioid,
            forall|p_ptr: ProcPtr|
                #![trigger final(self).get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> final(self).get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|c_ptr: ContainerPtr|
                #![trigger final(self).get_container(c_ptr)]
                old(self).container_dom().contains(c_ptr) && c_ptr != old(self).get_thread(
                    thread_ptr,
                ).owning_container ==> final(self).get_container(c_ptr).owned_procs =~= old(
                    self,
                ).get_container(c_ptr).owned_procs && final(self).get_container(c_ptr).parent =~= old(
                    self,
                ).get_container(c_ptr).parent && final(self).get_container(c_ptr).parent_rev_ptr =~= old(
                    self,
                ).get_container(c_ptr).parent_rev_ptr && final(self).get_container(c_ptr).children =~= old(
                    self,
                ).get_container(c_ptr).children && final(self).get_container(c_ptr).owned_endpoints
                    =~= old(self).get_container(c_ptr).owned_endpoints && final(self).get_container(
                    c_ptr,
                ).quota =~= old(self).get_container(c_ptr).quota
                // &&
                // self.get_container(c_ptr).mem_used =~= old(self).get_container(c_ptr).mem_used
                 && final(self).get_container(c_ptr).owned_cpus =~= old(self).get_container(
                    c_ptr,
                ).owned_cpus && final(self).get_container(c_ptr).scheduler =~= old(self).get_container(
                    c_ptr,
                ).scheduler && final(self).get_container(c_ptr).owned_threads =~= old(self).get_container(
                    c_ptr,
                ).owned_threads && final(self).get_container(c_ptr).depth =~= old(self).get_container(
                    c_ptr,
                ).depth && final(self).get_container(c_ptr).uppertree_seq =~= old(self).get_container(
                    c_ptr,
                ).uppertree_seq,
            forall|c_ptr: ContainerPtr|
                #![trigger final(self).get_container(c_ptr)]
                final(self).container_dom().contains(c_ptr) && final(self).get_container(
                    page_ptr_1,
                ).uppertree_seq@.contains(c_ptr) ==> final(self).get_container(c_ptr).subtree_set@
                    =~= final(self).get_container(c_ptr).subtree_set@.insert(page_ptr_1),
            forall|c_ptr: ContainerPtr|
                #![trigger final(self).get_container(c_ptr)]
                final(self).container_dom().contains(c_ptr) && final(self).get_container(
                    page_ptr_1,
                ).uppertree_seq@.contains(c_ptr) == false ==> final(self).get_container(c_ptr).subtree_set
                    =~= final(self).get_container(c_ptr).subtree_set,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_procs,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).parent,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).children@ =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).children@.push(
                page_ptr_1,
            ),
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_endpoints,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                - 3 - new_quota.mem_4k == final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_2m
                - new_quota.mem_2m == final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_2m,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_1g
                - new_quota.mem_1g == final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_1g,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.pcid
                - new_quota.pcid == final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.pcid,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.ioid
                - new_quota.ioid == final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.ioid,
            // self.get_container(old(self).get_thread(thread_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_used,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_cpus,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_threads,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).depth,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).uppertree_seq
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).uppertree_seq,
            final(self).get_container(old(self).get_thread(thread_ptr).owning_container).subtree_set@
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).subtree_set@.insert(page_ptr_1),
            final(self).get_container(page_ptr_1).owned_procs@ =~= Seq::<ProcPtr>::empty().push(
                page_ptr_2,
            ),
            final(self).get_container(page_ptr_1).parent =~= Some(
                old(self).get_thread(thread_ptr).owning_container,
            ),
            final(self).get_container(page_ptr_1).children@ =~= Seq::<ContainerPtr>::empty(),
            final(self).get_container(page_ptr_1).owned_endpoints@ =~= Set::<EndpointPtr>::empty(),
            final(self).get_container(page_ptr_1).quota =~= *new_quota,
            // self.get_container(page_ptr_1).mem_used =~= 0,
            final(self).get_container(page_ptr_1).owned_cpus.wf(),
            final(self).get_container(page_ptr_1).owned_cpus@ =~= Set::<CpuId>::empty(),
            final(self).get_container(page_ptr_1).scheduler.wf(),
            final(self).get_container(page_ptr_1).scheduler@ =~= Seq::<ThreadPtr>::empty().push(
                page_ptr_3,
            ),
            final(self).get_container(page_ptr_1).owned_threads@.finite(),
            final(self).get_container(page_ptr_1).owned_threads@ =~= Set::<ThreadPtr>::empty().insert(
                page_ptr_3,
            ),
            final(self).get_container(page_ptr_1).depth as int =~= final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).depth + 1,
            final(self).get_container(page_ptr_1).uppertree_seq@ =~= final(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).uppertree_seq@.push(old(self).get_thread(thread_ptr).owning_container),
            final(self).get_container(page_ptr_1).subtree_set@ =~= Set::<ContainerPtr>::empty(),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) ==> old(self).get_thread(t_ptr)
                    =~= final(self).get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger final(self).get_endpoint(e_ptr)]
                final(self).endpoint_dom().contains(e_ptr) && e_ptr != old(
                    self,
                ).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap() ==> old(
                    self,
                ).get_endpoint(e_ptr) =~= final(self).get_endpoint(e_ptr),
            final(self).get_container(page_ptr_1).children@ == Seq::<ContainerPtr>::empty(),
            final(self).get_container(page_ptr_1).owned_procs@ == Seq::<ProcPtr>::empty().push(page_ptr_2),
            final(self).get_container(page_ptr_1).owned_threads@ == Set::<ThreadPtr>::empty().insert(
                page_ptr_3,
            ),
            final(self).get_container(page_ptr_1).quota == new_quota,
            final(self).get_proc(page_ptr_2).pcid =~= new_pcid,
            final(self).get_proc(page_ptr_2).ioid.is_None(),
            final(self).get_proc(page_ptr_2).owned_threads@ == Seq::<ThreadPtr>::empty().push(page_ptr_3),
            final(self).get_proc(page_ptr_2).owning_container == page_ptr_1,
            final(self).get_thread(page_ptr_3).owning_container == page_ptr_1,
            final(self).get_thread(page_ptr_3).endpoint_descriptors@ =~= Seq::new(
                MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
                |i: int| { None },
            ).update(
                0,
                Some(
                    old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
                ),
            ),
            final(self).get_container(final(self).get_thread(thread_ptr).owning_container).children@ =~= old(
                self,
            ).get_container(final(self).get_thread(thread_ptr).owning_container).children@.push(
                page_ptr_1,
            ),
            final(self).get_container(final(self).get_thread(thread_ptr).owning_container).owned_procs@ =~= old(
                self,
            ).get_container(final(self).get_thread(thread_ptr).owning_container).owned_procs@,
            final(self).get_container(final(self).get_thread(thread_ptr).owning_container).owned_endpoints@
                =~= old(self).get_container(
                final(self).get_thread(thread_ptr).owning_container,
            ).owned_endpoints@,
            final(self).get_container(final(self).get_thread(thread_ptr).owning_container).owned_threads@ =~= old(
                self,
            ).get_container(final(self).get_thread(thread_ptr).owning_container).owned_threads@,
            final(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@ =~= old(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@.insert((page_ptr_3, 0)),
    {
        proof {
            seq_push_lemma::<ThreadPtr>();
        }
        broadcast use ProcessManager::reveal_specs_to_wf;
        broadcast use ProcessManager::reveal_wf_to_memory_disjoint;

        let old_container_ptr = self.get_thread(thread_ptr).owning_container;
        let mut old_quota = self.get_container(old_container_ptr).quota;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let new_upper_tree_ghost = Ghost(
            self.get_container(old_container_ptr).uppertree_seq@.push(old_container_ptr),
        );
        let old_depth = self.get_container(old_container_ptr).depth;

        assert(forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).children]
            #![trigger self.get_container(c_ptr).uppertree_seq]
            self.container_dom().contains(c_ptr) ==> self.get_container(c_ptr).children@.contains(
                page_ptr_1,
            ) == false && self.get_container(c_ptr).uppertree_seq@.contains(page_ptr_1) == false
                && self.get_container(c_ptr).uppertree_seq@.contains(c_ptr) == false) by {
            broadcast use ProcessManager::reveal_wf_to_container_tree_wf;
            container_tree_wf_imply_childern_uppertree_specs(
                self.root_container,
                self.container_perms@,
            );
        };
        old_quota.subtract_mem_4k(3);
        old_quota.subtract_new_quota(new_quota);
        let mut old_container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(old_container_ptr),
        );
        container_set_quota(old_container_ptr, &mut old_container_perm, &old_quota);
        let child_list_node_ref = container_push_child(
            old_container_ptr,
            &mut old_container_perm,
            page_ptr_1,
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(
                old_container_ptr,
                old_container_perm.get(),
            );
        }

        let (new_container_ptr, mut new_container_perm) = page_to_container_tree_version_1(
            page_ptr_1,
            page_perm_1,
            old_container_ptr,
            child_list_node_ref,
            *new_quota,
            ArraySet::<NUM_CPUS>::new(),
            old_depth + 1,
            Ghost(Set::<ContainerPtr>::empty()),
            new_upper_tree_ghost,
            Some(page_ptr_2),
        );

        let proc_list_node_ref = container_push_proc(
            new_container_ptr,
            &mut new_container_perm,
            page_ptr_2,
        );
        let scheduler_node_ref = scheduler_push_thread(
            new_container_ptr,
            &mut new_container_perm,
            &page_ptr_3,
        );
        container_set_owned_threads(
            new_container_ptr,
            &mut new_container_perm,
            Ghost(Set::<ThreadPtr>::empty().insert(page_ptr_3)),
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(
                new_container_ptr,
                new_container_perm.get(),
            );
        }

        assert(container_ancestors_wf(self.container_perms@, new_upper_tree_ghost@)
            && new_upper_tree_ghost@.contains(new_container_ptr) == false) by {
            broadcast use ProcessManager::reveal_wf_to_container_tree_wf;
            assert(old(self).container_tree_wf());
            assert(old(self).container_perms@.dom().contains(new_container_ptr) == false);
            container_ancestors_push(
                old(self).root_container,
                old(self).container_perms@,
                self.container_perms@,
                old_container_ptr,
                new_container_ptr,
            );
        };
        container_perms_update_subtree_set(
            &mut self.container_perms,
            new_upper_tree_ghost,
            new_container_ptr,
            old_container_ptr,
            old_depth + 1,
        );

        let (new_proc_ptr, mut proc_perm, proc_thread_list_node_ref) =
            page_to_proc_with_first_thread(
            page_ptr_2,
            page_perm_2,
            new_container_ptr,
            proc_list_node_ref,
            new_pcid,
            None,
            page_ptr_3,
            None,
            None,
            Ghost(Seq::empty()),
            Ghost(Set::empty()),
            0,
        );
        proof {
            self.process_perms.borrow_mut().tracked_insert(new_proc_ptr, proc_perm.get());
        }
        let (new_thread_ptr, thread_perm) = page_to_thread_with_endpoint(
            page_ptr_3,
            page_perm_3,
            &pt_regs,
            new_container_ptr,
            new_proc_ptr,
            proc_thread_list_node_ref,
            scheduler_node_ref,
            endpoint_ptr,
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(new_thread_ptr, thread_perm.get());
        }

        assert(self.endpoint_dom().contains(endpoint_ptr)) by {
            broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
        }        
        assert(self.get_endpoint(endpoint_ptr).get_owning_threads().contains((new_thread_ptr,0)) == false) by {
            broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;};
        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        endpoint_add_ref(endpoint_ptr, &mut endpoint_perm, new_thread_ptr, 0);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        assert(self.container_perms_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.container_tree_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_container_tree_wf;
            // assert(self.get_container(new_container_ptr).uppertree_seq =~= new_upper_tree_ghost);
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
            container_tree_wf_imply_uppertree_subset_of_tree(
                self.root_container,
                old(self).container_perms@,
            );
            new_container_preserve_tree_inv(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
                old_container_ptr,
                new_container_ptr,
            );
        };
        assert(self.proc_perms_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.process_trees_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_processes_container_wf;
            broadcast use ProcessManager::reveal_wf_to_process_trees_wf;
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();

            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                if c_ptr != new_container_ptr {
                    old(self).wf_imply_container_owned_proc_disjoint();
                    assert(self.get_container(c_ptr).owned_procs@.to_set().contains(new_proc_ptr)
                        == false);
                    process_no_change_to_tree_fields_imply_wf(
                        self.get_container(c_ptr).root_process.unwrap(),
                        self.get_container(c_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                        self.process_perms@,
                    );
                    assert(self.process_tree_wf(c_ptr));
                } else {
                    // assert(self.get_container(new_container_ptr).owned_procs@ == seq![new_proc_ptr]);
                    assume(self.get_container(new_container_ptr).owned_procs@.to_set()
                        == set![new_proc_ptr]);  // TODO @xiangdong
                    new_proc_tree_infer_wf(
                        self.get_container(new_container_ptr).root_process.unwrap(),
                        self.get_container(new_container_ptr).owned_procs@.to_set(),
                        self.process_perms@,
                        new_proc_ptr,
                    );
                }
            };

        };

        proof {
            let s0 = *old(self);
            let s1 = *self;
            assert(new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid)) by {
                broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
                assert forall|c_ptr: ContainerPtr|
                    #![trigger s1.container_perms@[c_ptr]]
                    s0.container_dom().contains(c_ptr) && c_ptr != old_container_ptr implies container_same_but_subtree_set(
                    s1.container_perms@[c_ptr],
                    s0.container_perms@[c_ptr],
                ) by {
                    assert(s1.container_dom().contains(c_ptr));
                };
            };
            new_container_with_endpoint_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
        }
    }
}

/// One element pushed on the empty sequence is the only element it contains.
pub proof fn seq_singleton_contains<A>(x: A, p: A)
    ensures
        Seq::<A>::empty().push(x).contains(p) <==> p == x,
{
    let s = Seq::<A>::empty().push(x);
    assert(s.len() == 1);
    assert(s[0] == x);
    if s.contains(p) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == p;
        assert(i == 0);
    }
}

/// How the process manager after new_container_with_endpoint relates to the one before it:
/// a container, a process and a thread were added, one endpoint gained a reference, and the
/// ancestors of the new container gained it in their subtree sets.
pub open spec fn new_container_with_endpoint_rel(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
) -> bool {
    &&& s1.root_container == s0.root_container
    &&& s1.cpu_list == s0.cpu_list
    &&& s0.page_closure().contains(new_container_ptr) == false
    &&& s0.page_closure().contains(new_proc_ptr) == false
    &&& s0.page_closure().contains(new_thread_ptr) == false
    &&& new_container_ptr != new_proc_ptr
    &&& new_container_ptr != new_thread_ptr
    &&& new_proc_ptr != new_thread_ptr
    // the calling thread and the endpoint it shares
    &&& s0.thread_dom().contains(thread_ptr)
    &&& s0.get_thread(thread_ptr).owning_container == old_container_ptr
    &&& 0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS
    &&& s0.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] == Some(endpoint_ptr)
    // containers
    &&& s0.container_dom().contains(old_container_ptr)
    &&& s1.container_dom() == s0.container_dom().insert(new_container_ptr)
    &&& forall|c_ptr: ContainerPtr|
        #![trigger s1.container_perms@[c_ptr]]
        s0.container_dom().contains(c_ptr) && c_ptr != old_container_ptr
            ==> container_same_but_subtree_set(s1.container_perms@[c_ptr], s0.container_perms@[c_ptr])
    &&& forall|c_ptr: ContainerPtr|
        #![trigger s1.container_perms@[c_ptr].value().subtree_set]
        s0.container_dom().contains(c_ptr) && s1.get_container(new_container_ptr).uppertree_seq@.contains(c_ptr)
            ==> s1.get_container(c_ptr).subtree_set@
                == s0.get_container(c_ptr).subtree_set@.insert(new_container_ptr)
    &&& forall|c_ptr: ContainerPtr|
        #![trigger s1.container_perms@[c_ptr].value().subtree_set]
        s0.container_dom().contains(c_ptr) && s1.get_container(new_container_ptr).uppertree_seq@.contains(c_ptr) == false
            ==> s1.get_container(c_ptr).subtree_set == s0.get_container(c_ptr).subtree_set
    &&& s1.container_perms@[old_container_ptr].is_init()
    &&& s1.container_perms@[old_container_ptr].addr() == old_container_ptr
    &&& s1.get_container(old_container_ptr).parent == s0.get_container(old_container_ptr).parent
    &&& s1.get_container(old_container_ptr).parent_rev_ptr == s0.get_container(old_container_ptr).parent_rev_ptr
    &&& s1.get_container(old_container_ptr).depth == s0.get_container(old_container_ptr).depth
    &&& s1.get_container(old_container_ptr).uppertree_seq == s0.get_container(old_container_ptr).uppertree_seq
    &&& s1.get_container(old_container_ptr).root_process == s0.get_container(old_container_ptr).root_process
    &&& s1.get_container(old_container_ptr).owned_procs == s0.get_container(old_container_ptr).owned_procs
    &&& s1.get_container(old_container_ptr).owned_endpoints == s0.get_container(old_container_ptr).owned_endpoints
    &&& s1.get_container(old_container_ptr).owned_threads == s0.get_container(old_container_ptr).owned_threads
    &&& s1.get_container(old_container_ptr).owned_cpus == s0.get_container(old_container_ptr).owned_cpus
    &&& s1.get_container(old_container_ptr).scheduler == s0.get_container(old_container_ptr).scheduler
    &&& s1.get_container(old_container_ptr).can_have_children == s0.get_container(old_container_ptr).can_have_children
    &&& s1.get_container(old_container_ptr).children@ == s0.get_container(old_container_ptr).children@.push(new_container_ptr)
    &&& s1.get_container(old_container_ptr).children.wf()
    &&& s1.get_container(old_container_ptr).children.unique()
    // the new container
    &&& s1.container_perms@[new_container_ptr].is_init()
    &&& s1.container_perms@[new_container_ptr].addr() == new_container_ptr
    &&& s1.get_container(new_container_ptr).parent == Some(old_container_ptr)
    &&& s1.get_container(new_container_ptr).children@ == Seq::<ContainerPtr>::empty()
    &&& s1.get_container(new_container_ptr).children.wf()
    &&& s1.get_container(new_container_ptr).owned_procs.wf()
    &&& s1.get_container(new_container_ptr).owned_procs.unique()
    &&& s1.get_container(new_container_ptr).owned_procs@ == Seq::<ProcPtr>::empty().push(new_proc_ptr)
    &&& s1.get_container(new_container_ptr).owned_procs.get_node_ref(new_proc_ptr) == s1.get_proc(new_proc_ptr).rev_ptr
    &&& s1.get_container(new_container_ptr).scheduler.wf()
    &&& s1.get_container(new_container_ptr).scheduler.unique()
    &&& s1.get_container(new_container_ptr).scheduler@ == Seq::<ThreadPtr>::empty().push(new_thread_ptr)
    &&& s1.get_thread(new_thread_ptr).scheduler_rev_ptr == Some(s1.get_container(new_container_ptr).scheduler.get_node_ref(new_thread_ptr))
    &&& s1.get_container(new_container_ptr).owned_threads@ == Set::<ThreadPtr>::empty().insert(new_thread_ptr)
    &&& s1.get_container(new_container_ptr).owned_endpoints@ == Set::<EndpointPtr>::empty()
    &&& s1.get_container(new_container_ptr).owned_cpus.wf()
    &&& s1.get_container(new_container_ptr).owned_cpus@ == Set::<CpuId>::empty()
    &&& s1.get_container(new_container_ptr).depth as int == s0.get_container(old_container_ptr).depth + 1
    &&& s1.get_container(new_container_ptr).uppertree_seq@ == s0.get_container(old_container_ptr).uppertree_seq@.push(old_container_ptr)
    &&& s1.get_container(new_container_ptr).subtree_set@ == Set::<ContainerPtr>::empty()
    &&& s1.get_container(new_container_ptr).root_process == Some(new_proc_ptr)
    // processes
    &&& s1.proc_dom() == s0.proc_dom().insert(new_proc_ptr)
    &&& forall|p_ptr: ProcPtr|
        #![trigger s1.process_perms@[p_ptr]]
        s0.proc_dom().contains(p_ptr) ==> s1.process_perms@[p_ptr] == s0.process_perms@[p_ptr]
    &&& forall|p_ptr: ProcPtr|
        #![trigger s0.proc_dom().contains(p_ptr)]
        s0.proc_dom().contains(p_ptr) ==> s0.get_proc(p_ptr).pcid != new_pcid
    &&& s1.process_perms@[new_proc_ptr].is_init()
    &&& s1.process_perms@[new_proc_ptr].addr() == new_proc_ptr
    &&& s1.get_proc(new_proc_ptr).owning_container == new_container_ptr
    &&& s1.get_proc(new_proc_ptr).pcid == new_pcid
    &&& s1.get_proc(new_proc_ptr).ioid.is_None()
    &&& s1.get_proc(new_proc_ptr).owned_threads.wf()
    &&& s1.get_proc(new_proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty().push(new_thread_ptr)
    &&& s1.get_proc(new_proc_ptr).owned_threads.get_node_ref(new_thread_ptr) == s1.get_thread(new_thread_ptr).proc_rev_ptr
    // threads
    &&& s1.thread_dom() == s0.thread_dom().insert(new_thread_ptr)
    &&& forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@[t_ptr]]
        s0.thread_dom().contains(t_ptr) ==> s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]
    &&& s1.thread_perms@[new_thread_ptr].is_init()
    &&& s1.thread_perms@[new_thread_ptr].addr() == new_thread_ptr
    &&& s1.get_thread(new_thread_ptr).owning_container == new_container_ptr
    &&& s1.get_thread(new_thread_ptr).owning_proc == new_proc_ptr
    &&& s1.get_thread(new_thread_ptr).state == ThreadState::SCHEDULED
    &&& s1.get_thread(new_thread_ptr).blocking_endpoint_ptr.is_None()
    &&& s1.get_thread(new_thread_ptr).endpoint_rev_ptr.is_None()
    &&& s1.get_thread(new_thread_ptr).running_cpu.is_None()
    &&& s1.get_thread(new_thread_ptr).endpoint_descriptors.wf()
    &&& s1.get_thread(new_thread_ptr).endpoint_descriptors@ == Seq::new(
        MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
        |i: int| None::<EndpointPtr>,
    ).update(0, Some(endpoint_ptr))
    &&& s1.get_thread(new_thread_ptr).ipc_payload.is_None()
    // endpoints
    &&& s1.endpoint_dom() == s0.endpoint_dom()
    &&& s0.endpoint_dom().contains(endpoint_ptr)
    &&& forall|e_ptr: EndpointPtr|
        #![trigger s1.endpoint_perms@[e_ptr]]
        s0.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr ==> s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]
    &&& s1.endpoint_perms@[endpoint_ptr].is_init()
    &&& s1.endpoint_perms@[endpoint_ptr].addr() == endpoint_ptr
    &&& s1.get_endpoint(endpoint_ptr).queue == s0.get_endpoint(endpoint_ptr).queue
    &&& s1.get_endpoint(endpoint_ptr).queue_state == s0.get_endpoint(endpoint_ptr).queue_state
    &&& s1.get_endpoint(endpoint_ptr).owning_container == s0.get_endpoint(endpoint_ptr).owning_container
    &&& s1.get_endpoint(endpoint_ptr).rf_counter == s0.get_endpoint(endpoint_ptr).rf_counter + 1
    &&& s0.get_endpoint(endpoint_ptr).owning_threads@.contains((new_thread_ptr, 0)) == false
    &&& s1.get_endpoint(endpoint_ptr).owning_threads@ == s0.get_endpoint(endpoint_ptr).owning_threads@.insert((new_thread_ptr, 0))
}

/// The three new pages were in none of the old maps.
pub proof fn new_container_with_endpoint_fresh(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s0.container_dom().contains(new_container_ptr) == false,
        s0.proc_dom().contains(new_container_ptr) == false,
        s0.thread_dom().contains(new_container_ptr) == false,
        s0.endpoint_dom().contains(new_container_ptr) == false,
        s0.container_dom().contains(new_proc_ptr) == false,
        s0.proc_dom().contains(new_proc_ptr) == false,
        s0.thread_dom().contains(new_proc_ptr) == false,
        s0.endpoint_dom().contains(new_proc_ptr) == false,
        s0.container_dom().contains(new_thread_ptr) == false,
        s0.proc_dom().contains(new_thread_ptr) == false,
        s0.thread_dom().contains(new_thread_ptr) == false,
        s0.endpoint_dom().contains(new_thread_ptr) == false,
{
}

/// A container the change left alone, or the parent, keeps every field but children, quota and subtree_set.
pub proof fn new_container_with_endpoint_old_container(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
    c_ptr: ContainerPtr,
)
    requires
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
        s0.container_dom().contains(c_ptr),
    ensures
        s1.container_dom().contains(c_ptr),
        c_ptr != new_container_ptr,
        s1.get_container(c_ptr).parent == s0.get_container(c_ptr).parent,
        s1.get_container(c_ptr).depth == s0.get_container(c_ptr).depth,
        s1.get_container(c_ptr).uppertree_seq == s0.get_container(c_ptr).uppertree_seq,
        s1.get_container(c_ptr).root_process == s0.get_container(c_ptr).root_process,
        s1.get_container(c_ptr).owned_procs == s0.get_container(c_ptr).owned_procs,
        s1.get_container(c_ptr).owned_endpoints == s0.get_container(c_ptr).owned_endpoints,
        s1.get_container(c_ptr).owned_threads == s0.get_container(c_ptr).owned_threads,
        s1.get_container(c_ptr).owned_cpus == s0.get_container(c_ptr).owned_cpus,
        s1.get_container(c_ptr).scheduler == s0.get_container(c_ptr).scheduler,
        forall|x: ContainerPtr|
            #![trigger s0.get_container(c_ptr).subtree_set@.contains(x)]
            s0.get_container(c_ptr).subtree_set@.contains(x) ==> s1.get_container(c_ptr).subtree_set@.contains(x),
{
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    if c_ptr != old_container_ptr {
        assert(container_same_but_subtree_set(s1.container_perms@[c_ptr], s0.container_perms@[c_ptr]));
    }
    if s1.get_container(new_container_ptr).uppertree_seq@.contains(c_ptr) {
        assert(s1.get_container(c_ptr).subtree_set@ == s0.get_container(c_ptr).subtree_set@.insert(new_container_ptr));
    } else {
        assert(s1.get_container(c_ptr).subtree_set == s0.get_container(c_ptr).subtree_set);
    }
}

pub proof fn new_container_with_endpoint_container_fields_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.container_fields_wf(),
{
    assert forall|c_ptr: ContainerPtr|
        #![trigger s1.container_dom().contains(c_ptr)]
        s1.container_dom().contains(c_ptr) implies s1.get_container(c_ptr).owned_cpus.wf()
        && s1.get_container(c_ptr).scheduler.wf()
        && s1.get_container(c_ptr).scheduler.unique()
        && s1.get_container(c_ptr).owned_procs.wf()
        && s1.get_container(c_ptr).owned_procs.unique() by {
        if c_ptr != new_container_ptr {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_cpus.wf());
            assert(s0.get_container(c_ptr).scheduler.wf());
            assert(s0.get_container(c_ptr).scheduler.unique());
            assert(s0.get_container(c_ptr).owned_procs.wf());
            assert(s0.get_container(c_ptr).owned_procs.unique());
        }
    };
}

pub proof fn new_container_with_endpoint_process_fields_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.process_fields_wf(),
{
    assert forall|p_ptr: ProcPtr|
        #![trigger s1.proc_dom().contains(p_ptr)]
        s1.proc_dom().contains(p_ptr) implies s1.get_proc(p_ptr).owned_threads.wf()
        && s1.get_proc(p_ptr).owned_threads.unique() by {
        if p_ptr == new_proc_ptr {
            assert(s1.get_proc(p_ptr).owned_threads@.len() == 1);
        } else {
            assert(s0.proc_dom().contains(p_ptr));
            assert(s1.process_perms@[p_ptr] == s0.process_perms@[p_ptr]);
            assert(s0.get_proc(p_ptr).owned_threads.wf());
            assert(s0.get_proc(p_ptr).owned_threads.unique());
        }
    };
}

pub proof fn new_container_with_endpoint_cpus_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.cpus_wf(),
        s1.container_cpu_wf(),
        s1.threads_cpu_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_cpus_wf;
    broadcast use ProcessManager::reveal_wf_to_container_cpu_wf;
    broadcast use ProcessManager::reveal_wf_to_threads_cpu_wf;
    assert(s0.cpus_wf());
    assert(s0.container_cpu_wf());
    assert(s0.threads_cpu_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert(s1.cpu_list == s0.cpu_list);
    assert forall|cpu_i: CpuId|
        #![trigger s1.cpu_list@[cpu_i as int]]
        0 <= cpu_i < NUM_CPUS implies s1.container_dom().contains(s1.cpu_list@[cpu_i as int].owning_container)
        && s1.get_container(s1.cpu_list@[cpu_i as int].owning_container).owned_cpus@.contains(cpu_i) by {
        let c_ptr = s0.cpu_list@[cpu_i as int].owning_container;
        assert(s0.container_dom().contains(c_ptr));
        assert(s0.get_container(c_ptr).owned_cpus@.contains(cpu_i));
        new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
    };
    assert forall|c_ptr: ContainerPtr, cpu_i: CpuId|
        #![trigger s1.get_container(c_ptr).owned_cpus@.contains(cpu_i)]
        s1.container_dom().contains(c_ptr) && s1.get_container(c_ptr).owned_cpus@.contains(cpu_i) implies 0 <= cpu_i
        < NUM_CPUS && s1.cpu_list[cpu_i as int].owning_container == c_ptr by {
        if c_ptr != new_container_ptr {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_cpus@.contains(cpu_i));
        }
    };
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@[t_ptr].value().running_cpu]
        s1.thread_perms@.dom().contains(t_ptr) implies (s1.thread_perms@[t_ptr].value().running_cpu.is_Some()
            <==> s1.thread_perms@[t_ptr].value().state == ThreadState::RUNNING)
        && (s1.thread_perms@[t_ptr].value().running_cpu.is_Some() ==> 0 <= s1.thread_perms@[t_ptr].value().running_cpu.unwrap()
            < NUM_CPUS && s1.cpu_list@[s1.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.is_Some()
            && s1.cpu_list@[s1.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.unwrap() == t_ptr) by {
        if t_ptr != new_thread_ptr {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        }
    };
}

pub proof fn new_container_with_endpoint_memory_disjoint(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.memory_disjoint(),
{
    broadcast use ProcessManager::reveal_wf_to_memory_disjoint;
    assert(s0.memory_disjoint());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|a: usize| s1.container_dom().contains(a) implies !s1.proc_dom().contains(a) && !s1.thread_dom().contains(a) && !s1.endpoint_dom().contains(a) by {
        if a != new_container_ptr {
            assert(s0.container_dom().contains(a));
        }
    };
    assert forall|a: usize| s1.proc_dom().contains(a) implies !s1.thread_dom().contains(a) && !s1.endpoint_dom().contains(a) by {
        if a != new_proc_ptr {
            assert(s0.proc_dom().contains(a));
        }
    };
    assert forall|a: usize| s1.thread_dom().contains(a) implies !s1.endpoint_dom().contains(a) by {
        if a != new_thread_ptr {
            assert(s0.thread_dom().contains(a));
        }
    };
}

pub proof fn new_container_with_endpoint_processes_container_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.processes_container_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_processes_container_wf;
    assert(s0.processes_container_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|c_ptr: ContainerPtr|
        #![trigger s1.get_container(c_ptr).owned_procs]
        s1.container_dom().contains(c_ptr) implies s1.get_container(c_ptr).owned_procs@.to_set().subset_of(
            s1.process_perms@.dom(),
        ) by {
        if c_ptr == new_container_ptr {
            assert forall|p: ProcPtr| #![trigger s1.get_container(c_ptr).owned_procs@.to_set().contains(p)] s1.get_container(c_ptr).owned_procs@.to_set().contains(p) implies s1.process_perms@.dom().contains(p) by {
                assert(s1.get_container(c_ptr).owned_procs@.contains(p));
                seq_singleton_contains(new_proc_ptr, p);
            };
        } else {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_procs@.to_set().subset_of(s0.process_perms@.dom()));
            assert forall|p: ProcPtr| #![trigger s1.get_container(c_ptr).owned_procs@.to_set().contains(p)] s1.get_container(c_ptr).owned_procs@.to_set().contains(p) implies s1.process_perms@.dom().contains(p) by {
                assert(s0.process_perms@.dom().contains(p));
            };
        }
    };
    assert forall|c_ptr: ContainerPtr, child_p_ptr: ProcPtr|
        #![trigger s1.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
        s1.container_dom().contains(c_ptr) && s1.get_container(c_ptr).owned_procs@.contains(child_p_ptr) implies s1.process_perms@[child_p_ptr].value().owning_container
            == c_ptr by {
        if c_ptr == new_container_ptr {
            seq_singleton_contains(new_proc_ptr, child_p_ptr);
        } else {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_procs@.contains(child_p_ptr));
            assert(s0.process_perms@[child_p_ptr].value().owning_container == c_ptr);
            assert(s0.get_container(c_ptr).owned_procs@.to_set().contains(child_p_ptr));
            assert(s0.process_perms@.dom().contains(child_p_ptr));
            assert(s1.process_perms@[child_p_ptr] == s0.process_perms@[child_p_ptr]);
        }
    };
    assert forall|p_ptr: ProcPtr|
        #![trigger s1.process_perms@[p_ptr].value().owning_container]
        s1.process_perms@.dom().contains(p_ptr) implies s1.container_dom().contains(
            s1.process_perms@[p_ptr].value().owning_container,
        ) && s1.get_container(s1.process_perms@[p_ptr].value().owning_container).owned_procs@.contains(p_ptr)
            && s1.get_container(s1.process_perms@[p_ptr].value().owning_container).owned_procs.get_node_ref(p_ptr)
            == s1.process_perms@[p_ptr].value().rev_ptr by {
        if p_ptr == new_proc_ptr {
            seq_singleton_contains(new_proc_ptr, new_proc_ptr);
        } else {
            assert(s0.proc_dom().contains(p_ptr));
            assert(s1.process_perms@[p_ptr] == s0.process_perms@[p_ptr]);
            let c_ptr = s0.process_perms@[p_ptr].value().owning_container;
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
        }
    };
}

pub proof fn new_container_with_endpoint_threads_process_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.threads_process_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_threads_process_wf;
    assert(s0.threads_process_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|p_ptr: ProcPtr, child_t_ptr: ThreadPtr|
        #![trigger s1.process_perms@.dom().contains(p_ptr), s1.thread_perms@[child_t_ptr].value().owning_proc]
        #![trigger s1.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
        s1.process_perms@.dom().contains(p_ptr) && s1.process_perms@[p_ptr].value().owned_threads@.contains(
            child_t_ptr,
        ) implies s1.thread_perms@.dom().contains(child_t_ptr) && s1.thread_perms@[child_t_ptr].value().owning_proc
            == p_ptr by {
        if p_ptr == new_proc_ptr {
            seq_singleton_contains(new_thread_ptr, child_t_ptr);
        } else {
            assert(s0.proc_dom().contains(p_ptr));
            assert(s1.process_perms@[p_ptr] == s0.process_perms@[p_ptr]);
            assert(s0.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr));
            assert(s0.thread_perms@.dom().contains(child_t_ptr));
            assert(s1.thread_perms@[child_t_ptr] == s0.thread_perms@[child_t_ptr]);
        }
    };
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@[t_ptr].value().owning_proc]
        #![trigger s1.process_perms@[s1.thread_perms@[t_ptr].value().owning_proc].value().owned_threads]
        s1.thread_perms@.dom().contains(t_ptr) implies s1.container_dom().contains(
            s1.thread_perms@[t_ptr].value().owning_container,
        ) && s1.process_perms@.dom().contains(s1.thread_perms@[t_ptr].value().owning_proc)
            && s1.process_perms@[s1.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
            && s1.process_perms@[s1.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.get_node_ref(t_ptr)
            == s1.thread_perms@[t_ptr].value().proc_rev_ptr
            && s1.process_perms@[s1.thread_perms@[t_ptr].value().owning_proc].value().owning_container
            == s1.thread_perms@[t_ptr].value().owning_container by {
        if t_ptr == new_thread_ptr {
            seq_singleton_contains(new_thread_ptr, new_thread_ptr);
        } else {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
            let p_ptr = s0.thread_perms@[t_ptr].value().owning_proc;
            assert(s0.proc_dom().contains(p_ptr));
            assert(s1.process_perms@[p_ptr] == s0.process_perms@[p_ptr]);
            assert(s0.container_dom().contains(s0.thread_perms@[t_ptr].value().owning_container));
        }
    };
}

pub proof fn new_container_with_endpoint_perms_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.threads_perms_wf(),
        s1.endpoint_perms_wf(),
{
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@.dom().contains(t_ptr)]
        s1.thread_perms@.dom().contains(t_ptr) implies s1.thread_perms@[t_ptr].is_init()
        && s1.thread_perms@[t_ptr].addr() == t_ptr
        && s1.thread_perms@[t_ptr].value().endpoint_descriptors.wf()
        && (s1.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().is_Some()
            ==> s1.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().unwrap().wf()) by {
        if t_ptr == new_thread_ptr {
            assert(s1.get_thread(t_ptr).endpoint_descriptors@.len() == MAX_NUM_ENDPOINT_DESCRIPTORS);
            assert(s1.get_thread(t_ptr).ipc_payload.get_payload_as_va_range().is_None());
        } else {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        }
    };
    assert forall|e_ptr: EndpointPtr|
        #![trigger s1.endpoint_perms@.dom().contains(e_ptr)]
        s1.endpoint_perms@.dom().contains(e_ptr) implies s1.endpoint_perms@[e_ptr].is_init()
        && s1.endpoint_perms@[e_ptr].addr() == e_ptr
        && s1.endpoint_perms@[e_ptr].value().queue.wf()
        && s1.endpoint_perms@[e_ptr].value().queue.unique()
        && s1.endpoint_perms@[e_ptr].value().owning_threads@.finite()
        && s1.endpoint_perms@[e_ptr].value().rf_counter == s1.endpoint_perms@[e_ptr].value().owning_threads@.len() by {
        assert(s0.endpoint_dom().contains(e_ptr));
        if e_ptr == endpoint_ptr {
            assert(s0.get_endpoint(e_ptr).owning_threads@.finite());
            assert(s1.get_endpoint(e_ptr).owning_threads@.len() == s0.get_endpoint(e_ptr).owning_threads@.len() + 1);
        } else {
            assert(s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]);
        }
    };
}

pub proof fn new_container_with_endpoint_threads_endpoint_descriptors_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.threads_endpoint_descriptors_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
    assert(s0.threads_endpoint_descriptors_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|t_ptr: ThreadPtr, e_idx: EndpointIdx|
        #![trigger s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int]]
        s1.thread_perms@.dom().contains(t_ptr) && 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS
            && s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some() implies s1.endpoint_perms@.dom().contains(
            s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap(),
        )
            && s1.endpoint_perms@[s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()].value().owning_threads@.contains(
            (t_ptr, e_idx),
        ) by {
        if t_ptr == new_thread_ptr {
            assert(e_idx == 0);
            assert(s1.thread_perms@[t_ptr].value().endpoint_descriptors@[0] == Some(endpoint_ptr));
        } else {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
            let e_ptr = s0.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap();
            assert(s0.endpoint_dom().contains(e_ptr));
            assert(s0.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx)));
            if e_ptr != endpoint_ptr {
                assert(s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]);
            }
        }
    };
    assert forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr, e_idx: EndpointIdx|
        #![trigger s1.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))]
        s1.endpoint_perms@.dom().contains(e_ptr) && s1.endpoint_perms@[e_ptr].value().owning_threads@.contains(
            (t_ptr, e_idx),
        ) implies 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS && s1.thread_perms@.dom().contains(t_ptr)
            && s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
            && s1.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap() == e_ptr by {
        assert(s0.endpoint_dom().contains(e_ptr));
        if e_ptr == endpoint_ptr && t_ptr == new_thread_ptr && e_idx == 0 {
            assert(s1.thread_perms@[t_ptr].value().endpoint_descriptors@[0] == Some(endpoint_ptr));
        } else {
            if e_ptr != endpoint_ptr {
                assert(s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]);
            }
            assert(s0.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx)));
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        }
    };
}

pub proof fn new_container_with_endpoint_endpoints_queue_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.endpoints_queue_wf(),
        s1.endpoints_container_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_endpoints_queue_wf;
    broadcast use ProcessManager::reveal_wf_to_endpoints_container_wf;
    assert(s0.endpoints_queue_wf());
    assert(s0.endpoints_container_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|e_ptr: EndpointPtr|
        #![trigger s1.endpoint_perms@[e_ptr]]
        s0.endpoint_dom().contains(e_ptr) implies s1.endpoint_perms@[e_ptr].value().queue == s0.endpoint_perms@[e_ptr].value().queue
        && s1.endpoint_perms@[e_ptr].value().owning_container == s0.endpoint_perms@[e_ptr].value().owning_container by {
        if e_ptr != endpoint_ptr {
            assert(s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]);
        }
    };
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@[t_ptr].value().state]
        #![trigger s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr]
        #![trigger s1.thread_perms@[t_ptr].value().endpoint_rev_ptr]
        s1.thread_perms@.dom().contains(t_ptr) && s1.thread_perms@[t_ptr].value().state == ThreadState::BLOCKED implies s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr.is_Some()
            && s1.thread_perms@[t_ptr].value().blocking_endpoint_index.is_Some() && 0
            <= s1.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap() < MAX_NUM_ENDPOINT_DESCRIPTORS
            && s1.thread_perms@[t_ptr].value().endpoint_descriptors@[s1.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap() as int]
            == Some(s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap())
            && s1.thread_perms@[t_ptr].value().endpoint_rev_ptr.is_Some() && s1.endpoint_perms@.dom().contains(
            s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap(),
        )
            && s1.endpoint_perms@[s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(t_ptr)
            && s1.endpoint_perms@[s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.get_node_ref(t_ptr)
            == s1.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap() by {
        assert(t_ptr != new_thread_ptr);
        assert(s0.thread_dom().contains(t_ptr));
        assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        let e_ptr = s0.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap();
        assert(s0.endpoint_dom().contains(e_ptr));
    };
    assert forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr|
        #![trigger s1.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr)]
        s1.endpoint_perms@.dom().contains(e_ptr) && s1.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr) implies s1.thread_perms@.dom().contains(
            t_ptr,
        ) && s1.thread_perms@[t_ptr].value().blocking_endpoint_ptr == Some(e_ptr)
            && s1.thread_perms@[t_ptr].value().state == ThreadState::BLOCKED by {
        assert(s0.endpoint_dom().contains(e_ptr));
        assert(s0.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr));
        assert(s0.thread_dom().contains(t_ptr));
        assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
    };
    assert forall|c_ptr: ContainerPtr, child_e_ptr: EndpointPtr|
        #![trigger s1.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
        s1.container_dom().contains(c_ptr) && s1.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr) implies s1.endpoint_perms@.dom().contains(
            child_e_ptr,
        ) && s1.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr by {
        assert(c_ptr != new_container_ptr);
        assert(s0.container_dom().contains(c_ptr));
        new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
        assert(s0.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr));
        assert(s0.endpoint_dom().contains(child_e_ptr));
    };
    assert forall|e_ptr: EndpointPtr|
        #![trigger s1.endpoint_perms@[e_ptr].value().owning_container]
        s1.endpoint_perms@.dom().contains(e_ptr) implies s1.container_dom().contains(
            s1.endpoint_perms@[e_ptr].value().owning_container,
        ) && s1.get_container(s1.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints@.contains(e_ptr) by {
        assert(s0.endpoint_dom().contains(e_ptr));
        let c_ptr = s0.endpoint_perms@[e_ptr].value().owning_container;
        assert(s0.container_dom().contains(c_ptr));
        new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
    };
}

pub proof fn new_container_with_endpoint_schedulers_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
    ensures
        s1.schedulers_wf(),
        s1.threads_container_wf(),
        s1.pcid_ioid_wf(),
{
    broadcast use ProcessManager::reveal_wf_to_schedulers_wf;
    broadcast use ProcessManager::reveal_wf_to_threads_container_wf;
    broadcast use ProcessManager::reveal_wf_to_pcid_ioid_wf;
    assert(s0.schedulers_wf());
    assert(s0.threads_container_wf());
    assert(s0.pcid_ioid_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.thread_perms@[t_ptr].value().scheduler_rev_ptr]
        s1.thread_perms@.dom().contains(t_ptr) && s1.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED implies s1.get_container(
            s1.thread_perms@[t_ptr].value().owning_container,
        ).scheduler@.contains(t_ptr) && s1.thread_perms@[t_ptr].value().scheduler_rev_ptr.is_Some()
            && s1.get_container(s1.thread_perms@[t_ptr].value().owning_container).scheduler.get_node_ref(t_ptr)
            == s1.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap() by {
        if t_ptr == new_thread_ptr {
            seq_singleton_contains(new_thread_ptr, new_thread_ptr);
        } else {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
            let c_ptr = s0.thread_perms@[t_ptr].value().owning_container;
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
        }
    };
    assert forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
        #![trigger s1.get_container(c_ptr).scheduler@.contains(t_ptr)]
        #![trigger s1.container_dom().contains(c_ptr), s1.thread_perms@[t_ptr].value().owning_container]
        #![trigger s1.container_dom().contains(c_ptr), s1.thread_perms@[t_ptr].value().state]
        s1.container_dom().contains(c_ptr) && s1.get_container(c_ptr).scheduler@.contains(t_ptr) implies s1.thread_perms@.dom().contains(
            t_ptr,
        ) && s1.thread_perms@[t_ptr].value().owning_container == c_ptr
            && s1.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED by {
        if c_ptr == new_container_ptr {
            seq_singleton_contains(new_thread_ptr, t_ptr);
        } else {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).scheduler@.contains(t_ptr));
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        }
    };
    assert forall|c_ptr: ContainerPtr|
        #![trigger s1.get_container(c_ptr).owned_threads]
        s1.container_dom().contains(c_ptr) implies s1.get_container(c_ptr).owned_threads@.subset_of(s1.thread_perms@.dom()) by {
        if c_ptr == new_container_ptr {
            assert forall|t: ThreadPtr| #![trigger s1.get_container(c_ptr).owned_threads@.contains(t)] s1.get_container(c_ptr).owned_threads@.contains(t) implies s1.thread_perms@.dom().contains(t) by {
                assert(t == new_thread_ptr);
            };
        } else {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_threads@.subset_of(s0.thread_perms@.dom()));
            assert forall|t: ThreadPtr| #![trigger s1.get_container(c_ptr).owned_threads@.contains(t)] s1.get_container(c_ptr).owned_threads@.contains(t) implies s1.thread_perms@.dom().contains(t) by {
                assert(s0.thread_perms@.dom().contains(t));
            };
        }
    };
    assert forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
        #![trigger s1.get_container(c_ptr).owned_threads, s1.get_thread(t_ptr)]
        s1.container_dom().contains(c_ptr) && s1.get_container(c_ptr).owned_threads@.contains(t_ptr) implies s1.get_thread(t_ptr).owning_container
            == c_ptr by {
        if c_ptr == new_container_ptr {
            assert(t_ptr == new_thread_ptr);
        } else {
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
            assert(s0.get_container(c_ptr).owned_threads@.contains(t_ptr));
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
        }
    };
    assert forall|t_ptr: ThreadPtr|
        #![trigger s1.container_dom().contains(s1.thread_perms@[t_ptr].value().owning_container)]
        s1.thread_perms@.dom().contains(t_ptr) implies s1.container_dom().contains(
            s1.thread_perms@[t_ptr].value().owning_container,
        ) && s1.get_container(s1.thread_perms@[t_ptr].value().owning_container).owned_threads@.contains(t_ptr) by {
        if t_ptr != new_thread_ptr {
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
            let c_ptr = s0.thread_perms@[t_ptr].value().owning_container;
            assert(s0.container_dom().contains(c_ptr));
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
        }
    };
    assert forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
        #![trigger s1.process_perms@[p_ptr_i].value().pcid, s1.process_perms@[p_ptr_j].value().pcid]
        s1.process_perms@.dom().contains(p_ptr_i) && s1.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j implies s1.process_perms@[p_ptr_i].value().pcid
            != s1.process_perms@[p_ptr_j].value().pcid by {
        if p_ptr_i != new_proc_ptr {
            assert(s0.proc_dom().contains(p_ptr_i));
            assert(s1.process_perms@[p_ptr_i] == s0.process_perms@[p_ptr_i]);
        }
        if p_ptr_j != new_proc_ptr {
            assert(s0.proc_dom().contains(p_ptr_j));
            assert(s1.process_perms@[p_ptr_j] == s0.process_perms@[p_ptr_j]);
        }
    };
    assert forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
        #![trigger s1.process_perms@[p_ptr_i].value().ioid, s1.process_perms@[p_ptr_j].value().ioid]
        s1.process_perms@.dom().contains(p_ptr_i) && s1.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
            && s1.process_perms@[p_ptr_i].value().ioid.is_Some() && s1.process_perms@[p_ptr_j].value().ioid.is_Some() implies s1.process_perms@[p_ptr_i].value().ioid.unwrap()
            != s1.process_perms@[p_ptr_j].value().ioid.unwrap() by {
        assert(p_ptr_i != new_proc_ptr);
        assert(p_ptr_j != new_proc_ptr);
        assert(s0.proc_dom().contains(p_ptr_i));
        assert(s1.process_perms@[p_ptr_i] == s0.process_perms@[p_ptr_i]);
        assert(s0.proc_dom().contains(p_ptr_j));
        assert(s1.process_perms@[p_ptr_j] == s0.process_perms@[p_ptr_j]);
    };
}

pub proof fn new_container_with_endpoint_endpoints_within_subtree(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
        s1.container_perms_wf(),
        s1.container_tree_wf(),
    ensures
        s1.endpoints_within_subtree(),
{
    broadcast use ProcessManager::reveal_wf_to_endpoints_within_subtree;
    broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
    broadcast use ProcessManager::reveal_wf_to_endpoints_container_wf;
    assert(s0.endpoints_within_subtree());
    assert(s0.threads_endpoint_descriptors_wf());
    assert(s0.endpoints_container_wf());
    new_container_with_endpoint_fresh(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    // the new thread's container is in the subtree of the endpoint's container
    let e_container = s0.get_endpoint(endpoint_ptr).owning_container;
    assert(s0.container_dom().contains(e_container));
    assert(s1.get_endpoint(endpoint_ptr).owning_container == e_container);
    assert(s0.get_endpoint(endpoint_ptr).owning_threads@.contains((thread_ptr, endpoint_index)));
    assert(old_container_ptr == e_container || s0.get_container(e_container).subtree_set@.contains(old_container_ptr));
    assert(s1.get_container(old_container_ptr).subtree_set@.contains(new_container_ptr)) by {
        seq_push_lemma::<ContainerPtr>();
        assert(s1.get_container(old_container_ptr).children@.contains(new_container_ptr));
        in_child_imply_in_subtree(s1.root_container, s1.container_perms@, old_container_ptr, new_container_ptr);
    };
    assert(new_container_ptr == e_container || s1.get_container(e_container).subtree_set@.contains(new_container_ptr)) by {
        if old_container_ptr != e_container {
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, e_container);
            assert(s1.get_container(e_container).subtree_set@.contains(old_container_ptr));
            in_subtree_impy_in_subsubtree(s1.root_container, s1.container_perms@, e_container, old_container_ptr, new_container_ptr);
        }
    };
    assert forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr, edp_idx: EndpointIdx|
        #![trigger s1.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx))]
        s1.endpoint_perms@.dom().contains(e_ptr) && s1.endpoint_perms@[e_ptr].value().owning_threads@.contains(
            (t_ptr, edp_idx),
        ) implies (s1.thread_perms@[t_ptr].value().owning_container == s1.endpoint_perms@[e_ptr].value().owning_container
            || s1.container_perms@[s1.endpoint_perms@[e_ptr].value().owning_container].value().subtree_set@.contains(
            s1.thread_perms@[t_ptr].value().owning_container,
        )) by {
        assert(s0.endpoint_dom().contains(e_ptr));
        if e_ptr == endpoint_ptr && t_ptr == new_thread_ptr && edp_idx == 0 {
        } else {
            if e_ptr != endpoint_ptr {
                assert(s1.endpoint_perms@[e_ptr] == s0.endpoint_perms@[e_ptr]);
            }
            assert(s0.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx)));
            assert(s0.thread_dom().contains(t_ptr));
            assert(s1.thread_perms@[t_ptr] == s0.thread_perms@[t_ptr]);
            let c_ptr = s0.endpoint_perms@[e_ptr].value().owning_container;
            assert(s0.container_dom().contains(c_ptr));
            assert(s1.endpoint_perms@[e_ptr].value().owning_container == c_ptr);
            new_container_with_endpoint_old_container(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid, c_ptr);
        }
    };
}

/// The process manager after new_container_with_endpoint is well formed.
pub proof fn new_container_with_endpoint_wf(
    s0: ProcessManager,
    s1: ProcessManager,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    old_container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
    new_proc_ptr: ProcPtr,
    new_thread_ptr: ThreadPtr,
    endpoint_ptr: EndpointPtr,
    new_pcid: Pcid,
)
    requires
        s0.wf(),
        new_container_with_endpoint_rel(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid),
        s1.container_perms_wf(),
        s1.container_tree_wf(),
        s1.proc_perms_wf(),
        s1.process_trees_wf(),
    ensures
        s1.wf(),
{
    broadcast use ProcessManager::reveal_specs_to_wf;
    new_container_with_endpoint_container_fields_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_process_fields_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_cpus_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_memory_disjoint(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_processes_container_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_threads_process_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_perms_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_threads_endpoint_descriptors_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_endpoints_queue_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_schedulers_wf(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    new_container_with_endpoint_endpoints_within_subtree(s0, s1, thread_ptr, endpoint_index, old_container_ptr, new_container_ptr, new_proc_ptr, new_thread_ptr, endpoint_ptr, new_pcid);
    assert(s1.internal_wf());
}

} // verus!
