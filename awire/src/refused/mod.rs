// SPDX-License-Identifier: MIT

//! Combinators that claim the interface falsely, one module each, which Verus must refuse at the
//! postconditions each names. tools/check-refused.py runs them and holds each refusal to those
//! postconditions; compiled only under cfg(refused), which nothing else sets, so they are in no
//! image and no verify count. design/wire-combinators-written-here/.
pub mod u16_be_le;
