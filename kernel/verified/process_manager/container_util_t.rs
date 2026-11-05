use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::pptr::{PPtr, PointsTo};
use crate::process_manager::container::*;
use crate::slinkedlist::spec_impl_u::StaticLinkedList;
use crate::array_set::ArraySet;
use crate::quota::Quota;

pub fn scheduler_push_thread(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    thread_ptr: &ThreadPtr,
) -> (ret: SLLIndex)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        old(container_perm)@.value().scheduler@.contains(*thread_ptr) == false,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        // container_perm@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().scheduler.wf(),
        final(container_perm)@.value().scheduler@ == old(container_perm)@.value().scheduler@.push(
            *thread_ptr,
        ),
        final(container_perm)@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() + 1,
        forall|t_ptr:ThreadPtr|
            #![auto]
            old(container_perm)@.value().scheduler@.contains(t_ptr) ==> 
                old(container_perm)@.value().scheduler.get_node_ref(t_ptr) == 
                    final(container_perm)@.value().scheduler.get_node_ref(t_ptr),
        final(container_perm)@.value().scheduler.get_node_ref(*thread_ptr) == ret,
        final(container_perm)@.value().scheduler.unique(),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.scheduler.push(thread_ptr);
    return ret;
}

pub fn scheduler_pop_head(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
) -> (ret: (ThreadPtr, SLLIndex))
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler.len() != 0,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().scheduler.wf(),
        final(container_perm)@.value().scheduler.unique(),
        final(container_perm)@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() - 1,
        final(container_perm)@.value().scheduler@ == old(container_perm)@.value().scheduler@.skip(1),
        ret.0 == old(container_perm)@.value().scheduler@[0],
        forall|v:ThreadPtr|
            #![auto]
            final(container_perm)@.value().scheduler@.contains(v) ==> 
                old(container_perm)@.value().scheduler.get_node_ref(v) == 
                    final(container_perm)@.value().scheduler.get_node_ref(v),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.scheduler.pop();
    ret
}


pub fn scheduler_remove_thread(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    rev_ptr: SLLIndex,
    thread_ptr_g: Ghost<ThreadPtr>,
) -> (ret: ThreadPtr)
    requires
        old(container_perm)@.value().scheduler.unique(),
        old(container_perm)@.value().scheduler@.contains(thread_ptr_g@),
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().scheduler.wf(),
        old(container_perm)@.value().scheduler.get_node_ref(thread_ptr_g@) == rev_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().scheduler.wf(),
        final(container_perm)@.value().scheduler.len() == old(container_perm)@.value().scheduler.len() - 1,
        ret == thread_ptr_g@,
        final(container_perm)@.value().scheduler.unique(),
        final(container_perm)@.value().scheduler@ =~= old(container_perm)@.value().scheduler@.remove_value(ret),
        forall|v:ThreadPtr|
            #![auto]
            final(container_perm)@.value().scheduler@.contains(v) ==> 
                old(container_perm)@.value().scheduler.get_node_ref(v) == 
                    final(container_perm)@.value().scheduler.get_node_ref(v),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.scheduler.remove(rev_ptr, thread_ptr_g);
    ret
}

pub fn container_push_proc(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    p_ptr: ProcPtr,
) -> (ret: SLLIndex)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_procs.wf(),
        old(container_perm)@.value().owned_procs.unique(),
        old(container_perm)@.value().owned_procs.len() < CONTAINER_PROC_LIST_LEN,
        old(container_perm)@.value().owned_procs@.contains(p_ptr) == false,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        // container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_procs.wf(),
        final(container_perm)@.value().owned_procs@ == old(container_perm)@.value().owned_procs@.push(
            p_ptr,
        ),
        final(container_perm)@.value().owned_procs.len() == old(container_perm)@.value().owned_procs.len() + 1,
        final(container_perm)@.value().owned_procs.unique(),
        forall|v:ThreadPtr|
            #![auto]
            old(container_perm)@.value().owned_procs@.contains(v) ==> 
                old(container_perm)@.value().owned_procs.get_node_ref(v) == 
                    final(container_perm)@.value().owned_procs.get_node_ref(v),
        final(container_perm)@.value().owned_procs.get_node_ref(p_ptr) == ret,
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.owned_procs.push(&p_ptr);
    return ret;
}

pub fn container_remove_proc(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    rev_ptr: SLLIndex,
    p_ptr: Ghost<ProcPtr>,
) -> (ret: ProcPtr)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_procs.wf(),
        old(container_perm)@.value().owned_procs.unique(),
        old(container_perm)@.value().owned_procs@.contains(p_ptr@),
        old(container_perm)@.value().owned_procs.get_node_ref(p_ptr@) == rev_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        // container_perm@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_procs.wf(),
        final(container_perm)@.value().owned_procs@ == old(container_perm)@.value().owned_procs@.remove_value(
            p_ptr@,
        ),
        final(container_perm)@.value().owned_procs@.len() == old(container_perm)@.value().owned_procs@.len() - 1,
        final(container_perm)@.value().owned_procs.unique(),
        forall|v:ThreadPtr|
            #![auto]
            final(container_perm)@.value().owned_procs@.contains(v) ==> 
                old(container_perm)@.value().owned_procs.get_node_ref(v) == 
                    final(container_perm)@.value().owned_procs.get_node_ref(v),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.owned_procs.remove(rev_ptr, p_ptr);
    return ret;
}

pub fn container_push_child(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    c_ptr: ContainerPtr,
) -> (ret: SLLIndex)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().children.wf(),
        old(container_perm)@.value().children.unique(),
        old(container_perm)@.value().children.len() < CONTAINER_CHILD_LIST_LEN,
        old(container_perm)@.value().children@.contains(c_ptr) == false,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        // container_perm@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().children.wf(),
        final(container_perm)@.value().children@ == old(container_perm)@.value().children@.push(c_ptr),
        final(container_perm)@.value().children.len() == old(container_perm)@.value().children.len() + 1,
        final(container_perm)@.value().children.unique(),
        forall|v:ThreadPtr|
            #![auto]
            old(container_perm)@.value().children@.contains(v) ==> 
                old(container_perm)@.value().children.get_node_ref(v) == 
                    final(container_perm)@.value().children.get_node_ref(v),
        final(container_perm)@.value().children.get_node_ref(c_ptr) == ret,
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.children.push(&c_ptr);
    return ret;
}

pub fn container_remove_child(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    rev_ptr: SLLIndex,
    c_ptr: Ghost<ContainerPtr>,
) -> (ret: ContainerPtr)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().children.wf(),
        old(container_perm)@.value().children.unique(),
        old(container_perm)@.value().children@.contains(c_ptr@),
        old(container_perm)@.value().children.get_node_ref(c_ptr@) == rev_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        // container_perm@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().children.wf(),
        final(container_perm)@.value().children@ == old(container_perm)@.value().children@.remove_value(c_ptr@),
        final(container_perm)@.value().children.len() == old(container_perm)@.value().children.len() - 1,
        final(container_perm)@.value().children.unique(),
        forall|v:ThreadPtr|
            #![auto]
            final(container_perm)@.value().children@.contains(v) ==> 
                old(container_perm)@.value().children.get_node_ref(v) == 
                    final(container_perm)@.value().children.get_node_ref(v),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    let ret = container.children.remove(rev_ptr, c_ptr);
    return ret;
}

#[verifier(external_body)]
// external_body(unproven): updates ghost state only, so its body is empty; the update is assumed, not proven
pub fn container_push_endpoint(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    e_ptr: EndpointPtr,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_endpoints@.contains(e_ptr) == false,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        // container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_endpoints@ == old(
            container_perm,
        )@.value().owned_endpoints@.insert(e_ptr),
{
}

#[verifier(external_body)]
// external_body(unproven): updates ghost state only, so its body is empty; the update is assumed, not proven
pub fn container_pop_endpoint(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    e_ptr: EndpointPtr,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_endpoints@.contains(e_ptr),
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        // container_perm@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_endpoints@ == old(
            container_perm,
        )@.value().owned_endpoints@.remove(e_ptr),
{
}

pub fn container_set_quota_mem_4k(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    value: usize,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota.spec_set_mem_4k(value),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    container.quota.set_mem_4k(value);
}

pub fn container_insert_cpu(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    cpu_id: CpuId,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_cpus.wf(),
        0 <= cpu_id < NUM_CPUS,
        old(container_perm)@.value().owned_cpus@.contains(cpu_id) == false,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        // container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_cpus.wf(),
        final(container_perm)@.value().owned_cpus@ =~= old(container_perm)@.value().owned_cpus@.insert(cpu_id),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    container.owned_cpus.insert(cpu_id);
}

pub fn container_remove_cpu(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    cpu_id: CpuId,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
        old(container_perm)@.value().owned_cpus.wf(),
        0 <= cpu_id < NUM_CPUS,
        old(container_perm)@.value().owned_cpus@.contains(cpu_id),
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        // container_perm@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_cpus.wf(),
        final(container_perm)@.value().owned_cpus@ =~= old(container_perm)@.value().owned_cpus@.remove(cpu_id),
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    container.owned_cpus.remove(cpu_id);
}

pub fn container_set_quota(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    new_quota: &Quota,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        // container_perm@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().quota =~= *new_quota,
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    container.quota = *new_quota;
}

#[verifier(external_body)]
// external_body(unproven): updates ghost state only, so its body is empty; the update is assumed, not proven
pub fn container_set_owned_threads(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    owned_threads: Ghost<Set<ThreadPtr>>,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        // container_perm@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        final(container_perm)@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().owned_threads =~= owned_threads,
{
}

pub fn container_set_root_proc(
    container_ptr: ContainerPtr,
    container_perm: &mut Tracked<PointsTo<Container>>,
    root_proc: Option<ProcPtr>,
)
    requires
        old(container_perm)@.is_init(),
        old(container_perm)@.addr() == container_ptr,
    ensures
        final(container_perm)@.is_init(),
        final(container_perm)@.addr() == container_ptr,
        final(container_perm)@.value().owned_procs =~= old(container_perm)@.value().owned_procs,
        final(container_perm)@.value().parent =~= old(container_perm)@.value().parent,
        final(container_perm)@.value().parent_rev_ptr =~= old(container_perm)@.value().parent_rev_ptr,
        final(container_perm)@.value().children =~= old(container_perm)@.value().children,
        final(container_perm)@.value().owned_endpoints =~= old(container_perm)@.value().owned_endpoints,
        final(container_perm)@.value().quota =~= old(container_perm)@.value().quota,
        // container_perm@.value().mem_used =~= old(container_perm)@.value().mem_used,
        final(container_perm)@.value().owned_cpus =~= old(container_perm)@.value().owned_cpus,
        final(container_perm)@.value().scheduler =~= old(container_perm)@.value().scheduler,
        final(container_perm)@.value().owned_threads =~= old(container_perm)@.value().owned_threads,
        final(container_perm)@.value().depth =~= old(container_perm)@.value().depth,
        final(container_perm)@.value().uppertree_seq =~= old(container_perm)@.value().uppertree_seq,
        final(container_perm)@.value().subtree_set =~= old(container_perm)@.value().subtree_set,
        final(container_perm)@.value().can_have_children =~= old(
            container_perm,
        )@.value().can_have_children,
        // container_perm@.value().root_process =~= old(container_perm)@.value().root_process,
        final(container_perm)@.value().root_process =~= root_proc,
{
    let tracked owned = container_perm.borrow_mut();
    let container = PPtr::<Container>::from_usize(container_ptr).borrow_mut(Tracked(owned));
    container.root_process = root_proc;
}

pub fn container_to_page(
    container_ptr: ContainerPtr,
    container_perm: Tracked<PointsTo<Container>>,
) -> (ret: (PagePtr, Tracked<PagePerm4k>))
    requires
        container_perm@.is_init(),
        container_perm@.addr() == container_ptr,
    ensures
        ret.1@.is_uninit(),
        ret.0 == container_ptr,
{
    let tracked mut perm = container_perm.get();
    proof {
        perm.leak_contents();
    }
    (container_ptr, Tracked(crate::layouts::container_into_page(perm)))
}

pub fn page_to_container_tree_version_1(
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
    parent_container: ContainerPtr,
    parent_rev_ptr: SLLIndex,
    init_quota: Quota,
    new_cpus: ArraySet<NUM_CPUS>,
    depth: usize,
    subtree_set: Ghost<Set<ContainerPtr>>,
    uppertree_seq: Ghost<Seq<ContainerPtr>>,
    root_process: Option<ProcPtr>,
) -> (ret: (ContainerPtr, Tracked<PointsTo<Container>>))
    requires
        page_perm@.is_uninit(),
        page_perm@.addr() == page_ptr,
        crate::util::page_ptr_util_u::page_ptr_valid(page_ptr),
    ensures
        ret.1@.is_init(),
        ret.0 == page_ptr,
        ret.1@.addr() == page_ptr,
        ret.1@.value().owned_procs.wf(),
        ret.1@.value().owned_procs@ =~= Seq::<ProcPtr>::empty(),
        ret.1@.value().parent =~= Some(parent_container),
        ret.1@.value().parent_rev_ptr =~= Some(parent_rev_ptr),
        ret.1@.value().children.wf(),
        ret.1@.value().children@ =~= Seq::<ContainerPtr>::empty(),
        ret.1@.value().children.len() == 0,
        ret.1@.value().owned_endpoints@ =~= Set::<EndpointPtr>::empty(),
        ret.1@.value().quota =~= init_quota,
        // ret.1@.value().mem_used =~= 0,
        ret.1@.value().owned_cpus =~= new_cpus,
        ret.1@.value().scheduler.wf(),
        ret.1@.value().scheduler@ =~= Seq::<ThreadPtr>::empty(),
        ret.1@.value().owned_threads@ =~= Set::<ThreadPtr>::empty(),
        ret.1@.value().depth =~= depth,
        ret.1@.value().subtree_set =~= subtree_set,
        ret.1@.value().uppertree_seq =~= uppertree_seq,
        ret.1@.value().root_process == root_process,
        ret.1@.value().can_have_children =~= false,
{
    let tracked mut perm = crate::layouts::page_into_container(page_perm.get());
    let mut owned_procs = StaticLinkedList::new();
    owned_procs.init();
    let mut children = StaticLinkedList::new();
    children.init();
    let mut scheduler = StaticLinkedList::new();
    scheduler.init();
    let container = Container {
        parent: Some(parent_container),
        parent_rev_ptr: Some(parent_rev_ptr),
        children,
        depth,
        uppertree_seq,
        subtree_set,
        root_process,
        owned_procs,
        owned_endpoints: Ghost(Set::empty()),
        owned_threads: Ghost(Set::empty()),
        quota: init_quota,
        owned_cpus: new_cpus,
        scheduler,
        can_have_children: false,
    };
    PPtr::<Container>::from_usize(page_ptr).put(Tracked(&mut perm), container);
    (page_ptr, Tracked(perm))
}

/// Everything in a container's permission but its subtree_set is the same.
pub open spec fn container_same_but_subtree_set(
    a: PointsTo<Container>,
    b: PointsTo<Container>,
) -> bool {
    &&& a.is_init() == b.is_init()
    &&& a.addr() == b.addr()
    &&& a.value().parent == b.value().parent
    &&& a.value().parent_rev_ptr == b.value().parent_rev_ptr
    &&& a.value().children == b.value().children
    &&& a.value().depth == b.value().depth
    &&& a.value().uppertree_seq == b.value().uppertree_seq
    &&& a.value().root_process == b.value().root_process
    &&& a.value().owned_procs == b.value().owned_procs
    &&& a.value().owned_endpoints == b.value().owned_endpoints
    &&& a.value().owned_threads == b.value().owned_threads
    &&& a.value().quota == b.value().quota
    &&& a.value().owned_cpus == b.value().owned_cpus
    &&& a.value().scheduler == b.value().scheduler
    &&& a.value().can_have_children == b.value().can_have_children
}

pub fn container_perms_update_subtree_set(
    perms: &mut Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    uppertree_seq: Ghost<Seq<ContainerPtr>>,
    new_container_ptr: ContainerPtr,
    start_ptr: ContainerPtr,
    depth: usize,
)
    requires
        crate::process_manager::container_tree::container_ancestors_wf(old(perms)@, uppertree_seq@),
        uppertree_seq@.len() == depth,
        depth > 0,
        uppertree_seq@[depth - 1] == start_ptr,
        old(perms)@.dom().contains(new_container_ptr),
        uppertree_seq@.contains(new_container_ptr) == false,
    ensures
        old(perms)@.dom() =~= final(perms)@.dom(),
        forall|c_ptr: ContainerPtr|
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger final(perms)@.dom().contains(c_ptr)]
            #![trigger final(perms)@[c_ptr]]
            final(perms)@.dom().contains(c_ptr) && uppertree_seq@.contains(c_ptr) == false
                ==> final(perms)@[c_ptr] =~= old(perms)@[c_ptr],
        forall|c_ptr: ContainerPtr|
         // #![trigger perms@[c_ptr].value().owning_container]

            #![trigger final(perms)@.dom().contains(c_ptr)]
            #![trigger final(perms)@[c_ptr]]
            final(perms)@.dom().contains(c_ptr) ==> final(perms)@[c_ptr].is_init() =~= old(
                perms,
            )@[c_ptr].is_init() && final(perms)@[c_ptr].addr() =~= old(perms)@[c_ptr].addr()
                && final(perms)@[c_ptr].value().parent =~= old(perms)@[c_ptr].value().parent
                && final(perms)@[c_ptr].value().parent_rev_ptr =~= old(
                perms,
            )@[c_ptr].value().parent_rev_ptr && final(perms)@[c_ptr].value().children =~= old(
                perms,
            )@[c_ptr].value().children && final(perms)@[c_ptr].value().depth =~= old(
                perms,
            )@[c_ptr].value().depth && final(perms)@[c_ptr].value().uppertree_seq =~= old(
                perms,
            )@[c_ptr].value().uppertree_seq
            // &&
            // perms@[c_ptr].value().subtree_set =~= old(perms)@[c_ptr].value().subtree_set
             && final(perms)@[c_ptr].value().root_process =~= old(perms)@[c_ptr].value().root_process
                && final(perms)@[c_ptr].value().owned_procs =~= old(perms)@[c_ptr].value().owned_procs
                && final(perms)@[c_ptr].value().owned_endpoints =~= old(
                perms,
            )@[c_ptr].value().owned_endpoints && final(perms)@[c_ptr].value().owned_threads =~= old(
                perms,
            )@[c_ptr].value().owned_threads && final(perms)@[c_ptr].value().quota =~= old(
                perms,
            )@[c_ptr].value().quota
            // &&
            // perms@[c_ptr].value().mem_used =~= old(perms)@[c_ptr].value().mem_used
             && final(perms)@[c_ptr].value().owned_cpus =~= old(perms)@[c_ptr].value().owned_cpus
                && final(perms)@[c_ptr].value().scheduler =~= old(perms)@[c_ptr].value().scheduler
                && final(perms)@[c_ptr].value().can_have_children =~= old(
                perms,
            )@[c_ptr].value().can_have_children,
        forall|c_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger final(perms)@[c_ptr].value().subtree_set]
            #![trigger old(perms)@[c_ptr].value().subtree_set]
            uppertree_seq@.contains(c_ptr) ==> final(perms)@[c_ptr].value().subtree_set@ =~= old(
                perms,
            )@[c_ptr].value().subtree_set@.insert(new_container_ptr),
        final(perms)@[new_container_ptr].value().subtree_set =~= old(
            perms,
        )@[new_container_ptr].value().subtree_set,
{
    let mut cur = start_ptr;
    let mut i = depth;
    let ghost old_perms = perms@;
    let ghost upper = uppertree_seq@;
    while i > 0
        invariant
            0 <= i <= depth,
            depth == upper.len(),
            upper == uppertree_seq@,
            i > 0 ==> cur == upper[i - 1],
            old_perms == old(perms)@,
            crate::process_manager::container_tree::container_ancestors_wf(old_perms, upper),
            perms@.dom() == old_perms.dom(),
            forall|c_ptr: ContainerPtr|
                #![trigger perms@[c_ptr]]
                old_perms.dom().contains(c_ptr) ==> container_same_but_subtree_set(perms@[c_ptr], old_perms[c_ptr]),
            forall|c_ptr: ContainerPtr|
                #![trigger perms@[c_ptr]]
                old_perms.dom().contains(c_ptr) && !upper.contains(c_ptr) ==> perms@[c_ptr] == old_perms[c_ptr],
            forall|j: int|
                #![trigger upper[j]]
                0 <= j < i ==> perms@[upper[j]] == old_perms[upper[j]],
            forall|j: int|
                #![trigger upper[j]]
                i <= j < upper.len() ==> perms@[upper[j]].value().subtree_set@
                    =~= old_perms[upper[j]].value().subtree_set@.insert(new_container_ptr),
        decreases i,
    {
        i = i - 1;
        let tracked mut perm = perms.borrow_mut().tracked_remove(cur);
        let container = PPtr::<Container>::from_usize(cur).borrow_mut(Tracked(&mut perm));
        proof {
            container.subtree_set = Ghost(container.subtree_set@.insert(new_container_ptr));
        }
        let parent = container.parent;
        proof {
            perms.borrow_mut().tracked_insert(cur, perm);
        }
        if i > 0 {
            cur = parent.unwrap();
        }
    }
}

pub fn container_perms_subset_remove(
    perms: &mut Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    uppertree_seq: Ghost<Seq<ContainerPtr>>,
    container_ptr: ContainerPtr,
    start_ptr: ContainerPtr,
    depth: usize,
)
    requires
        crate::process_manager::container_tree::container_ancestors_wf(old(perms)@, uppertree_seq@),
        uppertree_seq@.len() == depth,
        depth > 0,
        uppertree_seq@[depth - 1] == start_ptr,
        old(perms)@.dom().contains(container_ptr),
        uppertree_seq@.contains(container_ptr) == false,
    ensures
        old(perms)@.dom() =~= final(perms)@.dom(),
        forall|c_ptr: ContainerPtr|
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger final(perms)@.dom().contains(c_ptr)]
            #![trigger final(perms)@[c_ptr]]
            final(perms)@.dom().contains(c_ptr) && uppertree_seq@.contains(c_ptr) == false
                ==> final(perms)@[c_ptr] =~= old(perms)@[c_ptr],
        forall|c_ptr: ContainerPtr|
            #![trigger final(perms)@.dom().contains(c_ptr)]
            #![trigger final(perms)@[c_ptr]]
            final(perms)@.dom().contains(c_ptr) ==> final(perms)@[c_ptr].is_init() =~= old(
                perms,
            )@[c_ptr].is_init() && final(perms)@[c_ptr].addr() =~= old(perms)@[c_ptr].addr()
                && final(perms)@[c_ptr].value().parent =~= old(perms)@[c_ptr].value().parent
                && final(perms)@[c_ptr].value().parent_rev_ptr =~= old(
                perms,
            )@[c_ptr].value().parent_rev_ptr && final(perms)@[c_ptr].value().children =~= old(
                perms,
            )@[c_ptr].value().children && final(perms)@[c_ptr].value().depth =~= old(
                perms,
            )@[c_ptr].value().depth && final(perms)@[c_ptr].value().uppertree_seq =~= old(
                perms,
            )@[c_ptr].value().uppertree_seq
            &&
            (uppertree_seq@.contains(c_ptr) == false ==> final(perms)@[c_ptr].value().subtree_set =~= old(perms)@[c_ptr].value().subtree_set)
             && final(perms)@[c_ptr].value().root_process =~= old(perms)@[c_ptr].value().root_process
                && final(perms)@[c_ptr].value().owned_procs =~= old(perms)@[c_ptr].value().owned_procs
                && final(perms)@[c_ptr].value().owned_endpoints =~= old(
                perms,
            )@[c_ptr].value().owned_endpoints && final(perms)@[c_ptr].value().owned_threads =~= old(
                perms,
            )@[c_ptr].value().owned_threads && final(perms)@[c_ptr].value().quota =~= old(
                perms,
            )@[c_ptr].value().quota
            // &&
            // perms@[c_ptr].value().mem_used =~= old(perms)@[c_ptr].value().mem_used
             && final(perms)@[c_ptr].value().owned_cpus =~= old(perms)@[c_ptr].value().owned_cpus
                && final(perms)@[c_ptr].value().scheduler =~= old(perms)@[c_ptr].value().scheduler
                && final(perms)@[c_ptr].value().can_have_children =~= old(
                perms,
            )@[c_ptr].value().can_have_children,
        forall|c_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(c_ptr)]
            #![trigger final(perms)@[c_ptr].value().subtree_set]
            #![trigger old(perms)@[c_ptr].value().subtree_set]
            uppertree_seq@.contains(c_ptr) ==> final(perms)@[c_ptr].value().subtree_set@ =~= old(
                perms,
            )@[c_ptr].value().subtree_set@.remove(container_ptr),
        final(perms)@[container_ptr].value() =~= old(
            perms,
        )@[container_ptr].value(),
{
    let mut cur = start_ptr;
    let mut i = depth;
    let ghost old_perms = perms@;
    let ghost upper = uppertree_seq@;
    while i > 0
        invariant
            0 <= i <= depth,
            depth == upper.len(),
            upper == uppertree_seq@,
            i > 0 ==> cur == upper[i - 1],
            old_perms == old(perms)@,
            crate::process_manager::container_tree::container_ancestors_wf(old_perms, upper),
            perms@.dom() == old_perms.dom(),
            forall|c_ptr: ContainerPtr|
                #![trigger perms@[c_ptr]]
                old_perms.dom().contains(c_ptr) ==> container_same_but_subtree_set(perms@[c_ptr], old_perms[c_ptr]),
            forall|c_ptr: ContainerPtr|
                #![trigger perms@[c_ptr]]
                old_perms.dom().contains(c_ptr) && !upper.contains(c_ptr) ==> perms@[c_ptr] == old_perms[c_ptr],
            forall|j: int|
                #![trigger upper[j]]
                0 <= j < i ==> perms@[upper[j]] == old_perms[upper[j]],
            forall|j: int|
                #![trigger upper[j]]
                i <= j < upper.len() ==> perms@[upper[j]].value().subtree_set@
                    =~= old_perms[upper[j]].value().subtree_set@.remove(container_ptr),
        decreases i,
    {
        i = i - 1;
        let tracked mut perm = perms.borrow_mut().tracked_remove(cur);
        let container = PPtr::<Container>::from_usize(cur).borrow_mut(Tracked(&mut perm));
        proof {
            container.subtree_set = Ghost(container.subtree_set@.remove(container_ptr));
        }
        let parent = container.parent;
        proof {
            perms.borrow_mut().tracked_insert(cur, perm);
        }
        if i > 0 {
            cur = parent.unwrap();
        }
    }
}

} // verus!
