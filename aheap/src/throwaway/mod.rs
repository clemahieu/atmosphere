// SPDX-License-Identifier: MIT

//! The throwaways, one module per root witness beside this directory, each claiming `false` from its
//! witness's requires. tools/check-throwaways.py writes them and expects Verus to refuse each;
//! compiled only under cfg(throwaway). design/witness-per-way-an-operation-succeeds/.
pub mod backed_run;
pub mod block_buddy;
pub mod classes;
pub mod free_emptied;
pub mod free_emptied_two;
pub mod free_partial;
pub mod heap;
pub mod heap_alloc;
pub mod heap_objects;
pub mod large;
pub mod one_page;
pub mod page_buddy;
pub mod page_buddy_many;
pub mod page_buddy_spare;
pub mod record;
pub mod slab;
pub mod slab_full;
pub mod slab_pair;
pub mod slab_top;
pub mod small_classes;
pub mod two_classes;
