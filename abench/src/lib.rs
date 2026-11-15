// SPDX-License-Identifier: MIT

//! User-space synthetic benchmark runner following Fuchsia `perftest` semantics.
//!
//! Collects serialized hardware timestamp deltas and optional extended core PMU counters across
//! warm-up iterations and fixed-size batches, computes batch summary statistics, and formats
//! results as summary tables and runtime `fuchsiaperf.json` arrays (`design/synthetic-benchmark-suite/`).

#![no_std]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod counter;
pub mod results;
pub mod runner;
pub mod stats;
