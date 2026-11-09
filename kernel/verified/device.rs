use vstd::prelude::*;

verus! {

/// One slot per bus, device and function a PCI segment can address.
pub const NUM_DEVICE_IDS: usize = 65536;

/// The slot a PCI function takes: its 16-bit routing id.
pub open spec fn device_index(bus: int, device: int, function: int) -> int {
    bus * 256 + device * 8 + function
}

pub open spec fn device_in_range(bus: int, device: int, function: int) -> bool {
    0 <= bus < 256 && 0 <= device < 32 && 0 <= function < 8
}

/// A PCI function that can exist. Only `new` builds one, so holding it is the range check.
#[derive(Clone, Copy)]
pub struct DeviceId {
    index: usize,
}

impl DeviceId {
    pub closed spec fn spec_index(self) -> int {
        self.index as int
    }

    pub closed spec fn wf(self) -> bool {
        self.index < NUM_DEVICE_IDS
    }

    /// The check for a device id from user space.
    pub fn new(bus: usize, device: usize, function: usize) -> (ret: Option<DeviceId>)
        ensures
            ret.is_some() == device_in_range(bus as int, device as int, function as int),
            ret.is_some() ==> ret.unwrap().wf(),
            ret.is_some() ==> ret.unwrap().spec_index() == device_index(
                bus as int,
                device as int,
                function as int,
            ),
    {
        if bus < 256 && device < 32 && function < 8 {
            proof {
                lemma_device_index_bounds(bus as int, device as int, function as int);
            }
            Some(DeviceId { index: bus * 256 + device * 8 + function })
        } else {
            None
        }
    }

    pub fn index(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.spec_index(),
            ret < NUM_DEVICE_IDS,
    {
        self.index
    }
}

proof fn lemma_device_index_bounds(bus: int, device: int, function: int)
    requires
        device_in_range(bus, device, function),
    ensures
        0 <= bus * 256 <= 255 * 256,
        0 <= device * 8 <= 31 * 8,
        0 <= device_index(bus, device, function) < NUM_DEVICE_IDS,
{
}

} // verus!
