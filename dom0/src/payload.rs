//! Starts the payload the boot gave dom0 as a child process.
//!
//! The loader copies the payload's ELF image as-is into dom0's address space. dom0 maps fresh pages
//! for its segments and a stack, lays the image out in them with its relocations applied, and hands
//! those pages to a new process. The payload reports on descriptor 0, which sys_new_proc gives it,
//! once it is done, and dom0 waits for that.

use aelf::{ContiguousMapping, ElfHandle, PAddr, VAddr, VirtualMapper};
use astd::io::Cursor;
use astd::memory::PageProtection;

const PAGE: usize = 4096;
/// Where the payload's segments and stack go, in dom0's address space and the child's.
const IMAGE_VA: usize = 0x90_0000_0000;
const STACK_PAGES: usize = 16;
const ENDPOINT: usize = 5;

/// Maps the image's whole extent on the first call, which asks for an arbitrary address; aelf's
/// later calls name segments inside that extent, which are mapped already.
struct Mapper {
    end: usize,
}

impl VirtualMapper for Mapper {
    unsafe fn map_anonymous(&mut self, base: VAddr, size: usize, _protection: PageProtection) -> ContiguousMapping {
        let va = if base.0 == 0 {
            assert!(self.end == 0, "the payload's extent is mapped once");
            let ret = asys::sys_mmap(IMAGE_VA, 0x2, size.div_ceil(PAGE));
            assert!(ret == 0, "mmap of the payload image: {}", ret);
            self.end = IMAGE_VA + size;
            IMAGE_VA
        } else {
            let va = base.0 as usize;
            assert!(IMAGE_VA <= va && va + size <= self.end, "a segment outside the payload's extent");
            va
        };
        // The child shares dom0's pages at the same addresses, so dom0 writes them where they are.
        ContiguousMapping { vaddr: VAddr(va as u64), paddr: PAddr(va as u64) }
    }
}

/// Runs the payload until it reports on its endpoint.
pub fn start(base: *const u8, size: usize) {
    assert!(size != 0, "the boot gave dom0 no payload");
    let image = unsafe { core::slice::from_raw_parts(base, size) };
    let elf = ElfHandle::parse(Cursor::new(image), PAGE).expect("parse the payload");
    let mut mapper = Mapper { end: 0 };
    let (mapping, _) = elf.load(&mut mapper).expect("load the payload");
    log::info!("payload load bias {:#x}, entry {:?}", mapping.load_bias, mapping.entry_point);

    let image_pages = mapping.load_size / PAGE;
    let stack = IMAGE_VA + mapping.load_size;
    let ret = unsafe { asys::sys_mmap(stack, 0x2, STACK_PAGES) };
    assert!(ret == 0, "mmap of the payload stack: {}", ret);
    let ret = unsafe { asys::sys_new_endpoint(ENDPOINT) };
    assert!(ret == 0, "new_endpoint (payload): {}", ret);
    let sp = stack + STACK_PAGES * PAGE - 8;
    let ret = unsafe {
        asys::sys_new_proc(ENDPOINT, mapping.entry_point as usize, sp, IMAGE_VA, image_pages + STACK_PAGES)
    };
    assert!(ret == 0, "new_proc (payload): {}", ret);
    unsafe { asys::sys_receive_empty(ENDPOINT) };
    log::info!("payload done");
}
