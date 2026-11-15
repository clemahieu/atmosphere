// SPDX-License-Identifier: MIT

//! The throwaways, one module per root witness beside this directory, each claiming `false` from its
//! witness's requires. tools/check-throwaways.py writes them and expects Verus to refuse each;
//! compiled only under cfg(throwaway). design/witness-per-way-an-operation-succeeds/.
pub mod bytes;
pub mod u16_be;
pub mod u16_le;
pub mod u32_be;
pub mod u32_le;
pub mod u64_be;
pub mod u64_le;
pub mod u8;
