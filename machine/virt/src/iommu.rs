//! The IOMMU items of a machine without one. design/machine-glue-below-the-kernel/.

fn assert_device(bus: usize, device: usize, function: usize) {
    assert!(bus < 256 && device < 32 && function < 8, "Device id out of range");
}

/// Does nothing: this machine has no IOMMU.
pub unsafe fn iommu_init() {}

/// Refuses: this machine has no IOMMU.
pub unsafe fn iommu_map(bus: usize, device: usize, function: usize, root: u64) -> Result<(), &'static str> {
    assert_device(bus, device, function);
    let _ = root;
    Err("No IOMMU available")
}

/// Refuses: this machine has no IOMMU.
pub unsafe fn iommu_invalidate(bus: usize, device: usize, function: usize, page: u64) -> Result<(), &'static str> {
    assert_device(bus, device, function);
    let _ = page;
    Err("No IOMMU hardware")
}

/// Refuses: this machine has no IOMMU.
pub fn iommu_fault_dump() -> Result<(), &'static str> {
    Err("No IOMMU hardware")
}
