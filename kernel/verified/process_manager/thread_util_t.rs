use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::array::Array;
use crate::pptr::{PPtr, PointsTo};
use crate::trap::TrapFrameOption;
use crate::process_manager::thread::*;
use crate::trap::Registers;

pub fn page_to_thread(
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
    pt_regs: &Registers,
    owning_container: ContainerPtr,
    owning_proc: ProcPtr,
    proc_rev_ptr: SLLIndex,
    scheduler_rev_ptr: SLLIndex,
) -> (ret: (ThreadPtr, Tracked<PointsTo<Thread>>))
    requires
        page_perm@.is_uninit(),
        page_perm@.addr() == page_ptr,
        crate::util::page_ptr_util_u::page_ptr_valid(page_ptr),
    ensures
        ret.1@.value().endpoint_descriptors.wf(),
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().owning_proc == owning_proc,
        ret.1@.value().state == ThreadState::SCHEDULED,
        ret.1@.value().proc_rev_ptr == proc_rev_ptr,
        ret.1@.value().scheduler_rev_ptr == Some(scheduler_rev_ptr),
        ret.1@.value().blocking_endpoint_ptr.is_None(),
        ret.1@.value().endpoint_rev_ptr.is_None(),
        ret.1@.value().running_cpu.is_None(),
        ret.1@.value().endpoint_descriptors@ =~= Seq::new(
            MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
            |i: int| { None },
        ),
        ret.1@.value().ipc_payload.is_None(),
        ret.1@.value().error_code.is_None(),
        ret.1@.value().trap_frame.unwrap() =~= pt_regs,
{
    let tracked mut perm = crate::layouts::page_into_thread(page_perm.get());
    let mut endpoint_descriptors = Array::new();
    endpoint_descriptors.init2none();
    let mut trap_frame = TrapFrameOption::zeroed_none();
    trap_frame.set_self(pt_regs);
    let thread = Thread {
        owning_container,
        owning_proc,
        state: ThreadState::SCHEDULED,
        proc_rev_ptr,
        scheduler_rev_ptr: Some(scheduler_rev_ptr),
        blocking_endpoint_ptr: None,
        blocking_endpoint_index: None,
        endpoint_rev_ptr: None,
        running_cpu: None,
        endpoint_descriptors,
        ipc_payload: IPCPayLoad::Empty,
        error_code: None,
        trap_frame,
    };
    PPtr::<Thread>::from_usize(page_ptr).put(Tracked(&mut perm), thread);
    (page_ptr, Tracked(perm))
}

pub fn thread_to_page(
    thread_ptr: ThreadPtr,
    thread_perm: Tracked<PointsTo<Thread>>,
) -> (ret: (PagePtr, Tracked<PagePerm4k>))
    requires
        thread_perm@.is_init(),
        thread_perm@.addr() == thread_ptr,
    ensures
        ret.0 == thread_ptr,
        ret.1@.is_uninit(),
        ret.1@.addr() == ret.0,
{
    let tracked mut perm = thread_perm.get();
    proof {
        perm.leak_contents();
    }
    (thread_ptr, Tracked(crate::layouts::thread_into_page(perm)))
}

pub fn page_to_thread_with_endpoint(
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
    pt_regs: &Registers,
    owning_container: ContainerPtr,
    owning_proc: ProcPtr,
    proc_rev_ptr: SLLIndex,
    scheduler_rev_ptr: SLLIndex,
    endpoint_ptr: EndpointPtr,
) -> (ret: (ThreadPtr, Tracked<PointsTo<Thread>>))
    requires
        page_perm@.is_uninit(),
        page_perm@.addr() == page_ptr,
        crate::util::page_ptr_util_u::page_ptr_valid(page_ptr),
    ensures
        ret.1@.value().endpoint_descriptors.wf(),
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().owning_proc == owning_proc,
        ret.1@.value().state == ThreadState::SCHEDULED,
        ret.1@.value().proc_rev_ptr == proc_rev_ptr,
        ret.1@.value().scheduler_rev_ptr == Some(scheduler_rev_ptr),
        ret.1@.value().blocking_endpoint_ptr.is_None(),
        ret.1@.value().endpoint_rev_ptr.is_None(),
        ret.1@.value().running_cpu.is_None(),
        ret.1@.value().endpoint_descriptors@ =~= Seq::new(
            MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
            |i: int| { None },
        ).update(0, Some(endpoint_ptr)),
        ret.1@.value().ipc_payload.is_None(),
        ret.1@.value().error_code.is_None(),
        ret.1@.value().trap_frame.unwrap() =~= pt_regs,
{
    let tracked mut perm = crate::layouts::page_into_thread(page_perm.get());
    let mut endpoint_descriptors = Array::new();
    endpoint_descriptors.init2none();
    endpoint_descriptors.set(0, Some(endpoint_ptr));
    let mut trap_frame = TrapFrameOption::zeroed_none();
    trap_frame.set_self(pt_regs);
    let thread = Thread {
        owning_container,
        owning_proc,
        state: ThreadState::SCHEDULED,
        proc_rev_ptr,
        scheduler_rev_ptr: Some(scheduler_rev_ptr),
        blocking_endpoint_ptr: None,
        blocking_endpoint_index: None,
        endpoint_rev_ptr: None,
        running_cpu: None,
        endpoint_descriptors,
        ipc_payload: IPCPayLoad::Empty,
        error_code: None,
        trap_frame,
    };
    PPtr::<Thread>::from_usize(page_ptr).put(Tracked(&mut perm), thread);
    (page_ptr, Tracked(perm))
}

pub fn thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    blocking_endpoint_ptr: Option<EndpointPtr>,
    endpoint_rev_ptr: Option<SLLIndex>,
    scheduler_rev_ptr: Option<SLLIndex>,
    state: ThreadState,
    ipc_payload: IPCPayLoad,
    blocking_endpoint_index: Option<EndpointIdx>,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == blocking_endpoint_ptr,
        final(thread_perm)@.value().endpoint_rev_ptr == endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu.is_None(),
        final(thread_perm)@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        final(thread_perm)@.value().ipc_payload == ipc_payload,
        final(thread_perm)@.value().error_code == old(thread_perm)@.value().error_code,
        final(thread_perm)@.value().trap_frame == old(thread_perm)@.value().trap_frame,
        final(thread_perm)@.value().blocking_endpoint_index == blocking_endpoint_index,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.state = state;
    thread.scheduler_rev_ptr = scheduler_rev_ptr;
    thread.blocking_endpoint_ptr = blocking_endpoint_ptr;
    thread.endpoint_rev_ptr = endpoint_rev_ptr;
    thread.ipc_payload = ipc_payload;
    thread.blocking_endpoint_index = blocking_endpoint_index;
    thread.running_cpu = None;
}

pub fn thread_set_endpoint_descriptor(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    endpoint_index: EndpointIdx,
    endpoint_op: Option<EndpointPtr>,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
        old(thread_perm)@.value().endpoint_descriptors.wf(),
        0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    ensures
        final(thread_perm)@.value().endpoint_descriptors.wf(),
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == old(thread_perm)@.value().state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == old(thread_perm)@.value().scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == old(
            thread_perm,
        )@.value().blocking_endpoint_ptr,
        final(thread_perm)@.value().endpoint_rev_ptr == old(thread_perm)@.value().endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu == old(thread_perm)@.value().running_cpu,
        final(thread_perm)@.value().endpoint_descriptors@ == old(
            thread_perm,
        )@.value().endpoint_descriptors@.update(endpoint_index as int, endpoint_op),
        final(thread_perm)@.value().ipc_payload == old(thread_perm)@.value().ipc_payload,
        final(thread_perm)@.value().error_code == old(thread_perm)@.value().error_code,
        final(thread_perm)@.value().trap_frame == old(thread_perm)@.value().trap_frame,
        final(thread_perm)@.value().blocking_endpoint_index == old(
            thread_perm,
        )@.value().blocking_endpoint_index,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.endpoint_descriptors.set(endpoint_index, endpoint_op);
}

pub fn thread_set_state(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    state: ThreadState,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == old(thread_perm)@.value().scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == old(
            thread_perm,
        )@.value().blocking_endpoint_ptr,
        final(thread_perm)@.value().endpoint_rev_ptr == old(thread_perm)@.value().endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu == old(thread_perm)@.value().running_cpu,
        final(thread_perm)@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        final(thread_perm)@.value().ipc_payload == old(thread_perm)@.value().ipc_payload,
        final(thread_perm)@.value().error_code == old(thread_perm)@.value().error_code,
        final(thread_perm)@.value().trap_frame == old(thread_perm)@.value().trap_frame,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.state = state;
}

pub fn thread_set_current_cpu(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    cpu_id: Option<CpuId>,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == old(thread_perm)@.value().state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == old(thread_perm)@.value().scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == old(
            thread_perm,
        )@.value().blocking_endpoint_ptr,
        final(thread_perm)@.value().endpoint_rev_ptr == old(thread_perm)@.value().endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu == cpu_id,
        final(thread_perm)@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        final(thread_perm)@.value().ipc_payload == old(thread_perm)@.value().ipc_payload,
        final(thread_perm)@.value().error_code == old(thread_perm)@.value().error_code,
        final(thread_perm)@.value().trap_frame == old(thread_perm)@.value().trap_frame,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.running_cpu = cpu_id;
}

pub fn thread_set_error_code(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    error_code: Option<RetValueType>,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == old(thread_perm)@.value().state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == old(thread_perm)@.value().scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == old(
            thread_perm,
        )@.value().blocking_endpoint_ptr,
        final(thread_perm)@.value().blocking_endpoint_index == old(
            thread_perm,
        )@.value().blocking_endpoint_index,
        final(thread_perm)@.value().endpoint_rev_ptr == old(thread_perm)@.value().endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu == old(thread_perm)@.value().running_cpu,
        final(thread_perm)@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        final(thread_perm)@.value().ipc_payload == old(thread_perm)@.value().ipc_payload,
        final(thread_perm)@.value().error_code == error_code,
        final(thread_perm)@.value().trap_frame == old(thread_perm)@.value().trap_frame,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.error_code = error_code;
}

pub fn thread_set_trap_frame(
    thread_ptr: ThreadPtr,
    thread_perm: &mut Tracked<PointsTo<Thread>>,
    pt_regs: &Registers,
)
    requires
        old(thread_perm)@.is_init(),
        old(thread_perm)@.addr() == thread_ptr,
    ensures
        final(thread_perm)@.is_init(),
        final(thread_perm)@.addr() == thread_ptr,
        final(thread_perm)@.value().owning_container == old(thread_perm)@.value().owning_container,
        final(thread_perm)@.value().owning_proc == old(thread_perm)@.value().owning_proc,
        final(thread_perm)@.value().state == old(thread_perm)@.value().state,
        final(thread_perm)@.value().proc_rev_ptr == old(thread_perm)@.value().proc_rev_ptr,
        final(thread_perm)@.value().scheduler_rev_ptr == old(thread_perm)@.value().scheduler_rev_ptr,
        final(thread_perm)@.value().blocking_endpoint_ptr == old(
            thread_perm,
        )@.value().blocking_endpoint_ptr,
        final(thread_perm)@.value().endpoint_rev_ptr == old(thread_perm)@.value().endpoint_rev_ptr,
        final(thread_perm)@.value().running_cpu == old(thread_perm)@.value().running_cpu,
        final(thread_perm)@.value().endpoint_descriptors == old(thread_perm)@.value().endpoint_descriptors,
        final(thread_perm)@.value().ipc_payload == old(thread_perm)@.value().ipc_payload,
        final(thread_perm)@.value().error_code == old(thread_perm)@.value().error_code,
        final(thread_perm)@.value().blocking_endpoint_index == old(
            thread_perm,
        )@.value().blocking_endpoint_index,
        final(thread_perm)@.value().trap_frame.is_Some(),
        final(thread_perm)@.value().trap_frame.unwrap() == *pt_regs,
{
    let tracked owned = thread_perm.borrow_mut();
    let thread = PPtr::<Thread>::from_usize(thread_ptr).borrow_mut(Tracked(owned));
    thread.trap_frame.set_self(pt_regs);
}

} // verus!
