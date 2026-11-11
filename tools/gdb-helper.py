# SPDX-License-Identifier: MIT

# Sourced by tools/gdb.py once gdb is attached to a guest whose loader waits for it
# (aloader/src/debugger.rs) and the kernel's and dom0's symbols are added at their biases: lets the
# loader go on into the kernel, and stops where the kernel calls kernel::debugger::breakpoint.
#
# Reference:
# - RedLeaf Vermilion

import gdb

# What rax holds while the loader waits (aloader/src/arch/x86_64.rs).
LOADER_WAITING = 0x6764627761697421
# The instructions a stop may land before the wait loop sets rax: the end of the log call before it.
MAX_STEPS_TO_WAIT = 100000

KERNEL_BREAKPOINT = 'kernel::debugger::breakpoint'

def rax():
    return int(gdb.parse_and_eval('$rax')) & 0xffffffffffffffff

def release_loader():
    # The loader runs on the boot processor, the first CPU and so gdb's thread 1.
    gdb.execute('thread 1', to_string=True)
    steps = 0
    while rax() != LOADER_WAITING:
        if steps == MAX_STEPS_TO_WAIT:
            raise gdb.GdbError(f'The loader did not reach its wait within {steps} instructions')
        gdb.execute('stepi', to_string=True)
        steps += 1
    gdb.execute('set $rax = 0')
    print('Released the loader into the kernel')

class KernelBreakpoint(gdb.Breakpoint):
    def __init__(self):
        super().__init__(KERNEL_BREAKPOINT)

    def stop(self):
        global frame

        frame = gdb.selected_frame()
        if not frame:
            print('No current frame')

        frames_to_rewind = int(gdb.parse_and_eval('frames_to_rewind'))
        print(f'Unwind {frames_to_rewind} frames')

        for _ in range(frames_to_rewind):
            caller = frame.older()
            if caller:
                frame = caller
            else:
                break

        # An assembly stub's frame has no function, only a name gdb may not know either.
        print(f'Found parent frame: {frame.name()}')

        def post():
            # A command queued behind the stop, as under -batch, may have resumed the guest.
            if gdb.selected_thread().is_stopped():
                frame.select()
                gdb.execute('frame')

        gdb.post_event(post)

        return True

release_loader()
KernelBreakpoint()
