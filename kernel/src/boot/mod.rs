// SPDX-License-Identifier: MIT

//! Bootloader integration.
//!
//! The early loader (`aloader`) enters the kernel with a `BootInfo`.

pub mod command_line;
pub mod free_ranges;
pub mod mapped_runs;

// The loader, the boot checks and the verified kernel use one page size. The map check uses the
// same page limit, identity-mapped span and node space as the verified kernel, and the 2M and 1G regions tile the pages
// under that limit. The run check keeps user mappings out of the low entries that space keeps for
// the kernel.
const _: () = {
    assert!(astd::boot::PAGE_BYTES == verified::define::PAGE_SZ as u64);
    assert!(
        free_ranges::MAX_PAGE_ADDRESS
            == verified::define::NUM_PAGES as u64 * astd::boot::PAGE_BYTES
    );
    {
        use verified::capability::block::{NUM_1G, NUM_2M};
        use verified::define::{PAGES_PER_1G, PAGES_PER_2M};
        assert!(NUM_2M * PAGES_PER_2M == verified::define::NUM_PAGES);
        assert!(NUM_1G * PAGES_PER_1G == verified::define::NUM_PAGES);
    }
    assert!(free_ranges::NODE_SPACE == verified::capability::list::NODE_SPACE as u64);
    assert!(free_ranges::IDENTITY_SPAN == verified::define::IDENTITY_SPAN as u64);
    assert!(
        astd::memory::USERSPACE_BASE == (verified::define::KERNEL_MEM_END_L4INDEX as u64) << 39
    );
};

use astd::boot::BootInfo;

pub use command_line::get_command_line;

/// Written once by `init` on CPU 0, before anything reads it and before the second core starts;
/// only read after that.
static mut BOOT_INFO: BootInfo = BootInfo::empty();

pub unsafe fn init(boot_info: *const BootInfo) {
    BOOT_INFO = (*boot_info).clone();
    let boot_info = get_boot_info();
    command_line::init(boot_info.command_line.as_str()).expect("Invalid kernel command-line");
}

pub fn get_boot_info() -> &'static BootInfo {
    // Shared: init's write is the only one, and it is done before any caller.
    unsafe { &*&raw const BOOT_INFO }
}

/// Returns the raw kernel command line.
pub fn get_raw_command_line() -> &'static str {
    get_boot_info().command_line.as_str()
}

