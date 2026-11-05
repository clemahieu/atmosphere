//! Compile-time checks that the kernel's arrays start from valid values. Const evaluation rejects a
//! value holding uninitialised memory or an invalid bit pattern, so these are checks at each element
//! type `Kernel` holds. One element is enough: an array is valid when its element type is.

use verified::allocator::page::Page;
use verified::array::Array;
use verified::define::{EndpointPtr, PagePtr, ProcPtr};
use verified::device::DeviceTable;
use verified::process_manager::cpu::Cpu;
use verified::memory_manager::root_table::RootTable;
use verified::pagetable::pagetable_spec::PageTable;
use verified::slinkedlist::spec_impl_u::StaticLinkedList;
use verified::trap::Registers;

const _: Array<Page, 1> = Array::new();
const _: Array<Cpu, 1> = Array::new();
const _: Array<usize, 1> = Array::new();
const _: Array<Option<PageTable>, 1> = Array::new();
const _: Array<Option<ProcPtr>, 1> = Array::new();
const _: Array<Option<EndpointPtr>, 1> = Array::new();
const _: StaticLinkedList<PagePtr, 1> = StaticLinkedList::new();
const _: DeviceTable = DeviceTable::new();
const _: RootTable = RootTable::new();
const _: Registers = Registers::random();
