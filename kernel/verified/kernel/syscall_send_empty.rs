use vstd::prelude::*;
verus! {

use crate::define::*;

use crate::kernel::Kernel;

use crate::process_manager::thread::IPCPayLoad;
use crate::trap::Registers;

impl Kernel {
    ///
    /// pass payload only below are satisified
    /// &&& endpoint must be well formed
    /// &&& sender payload must be well formed
    /// &&& receiver payload must be well formed
    /// &&& endpoint state is correct with respect to send.
    ///
    /// endpoint state
    /// | queue state | queue len | action |
    /// | send        | >= 0      | block  |
    /// | receive     | == 0      | block + changed queue state |
    /// | receive     | > 0       | success |
    ///
    pub fn syscall_send_empty_no_block(
        &mut self,
        sender_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(sender_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(sender_thread_ptr).state == ThreadState::RUNNING,
        ensures
            final(self).wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
        let blocking_endpoint_ptr_op = self.proc_man.get_thread(
            sender_thread_ptr,
        ).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        assert(self.receiver_exist(sender_thread_ptr, blocking_endpoint_index));

        let receiver_thread_ptr = self.proc_man.get_endpoint(
            blocking_endpoint_ptr,
        ).queue.get_head();
        let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;

        if self.proc_man.get_container(receiver_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            // cannot schedule the receiver
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }

    pub fn syscall_send_empty_block(
        &mut self,
        sender_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
        pt_regs: &Registers,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(sender_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(sender_thread_ptr).state == ThreadState::RUNNING,
        ensures
            final(self).wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
        let blocking_endpoint_ptr_op = self.proc_man.get_thread(
            sender_thread_ptr,
        ).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            self.proc_man.block_running_thread_and_set_trap_frame(
                sender_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Empty,
                pt_regs,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoNextThreadNew(RetValueType::Error);  //Come Back
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            self.proc_man.block_running_thread_and_change_queue_state_and_set_trap_frame(
                sender_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Empty,
                EndpointState::SEND,
                pt_regs,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoNextThreadNew(RetValueType::Error);  //Come Back
        }
        assert(self.receiver_exist(sender_thread_ptr, blocking_endpoint_index));

        let receiver_thread_ptr = self.proc_man.get_endpoint(
            blocking_endpoint_ptr,
        ).queue.get_head();
        let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;

        if self.proc_man.get_container(receiver_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            // cannot schedule the receiver
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }
}

} // verus!
