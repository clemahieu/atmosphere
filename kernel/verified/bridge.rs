#[derive(Debug)]
#[repr(u8)]
pub enum SwitchDecision {
    /// The kernel will return to the same thread.
    NoSwitching = 0,

    /// The kernel will switch to a thread it preempted.
    SwitchToPreempted = 1,
}
