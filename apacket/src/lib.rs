// SPDX-License-Identifier: MIT

//! The wire formats of the network stack, each written in awire's combinators and so inheriting
//! what they prove: a parse that accepts or refuses every byte string, the round trip each way, and
//! steps linear in the bytes (design/network-stack-proven-at-tier-1/, rule 1). Each format's value
//! names its fields through `Mapped`, so the protocol above reads a field by its name.
//!
//! The formats here: `Arp`, ARP for Ethernet and IPv4. Nothing allocates.
#![cfg_attr(not(test), no_std)]

mod arp;
pub use arp::*;
#[cfg(refused)]
mod refused;
#[cfg(throwaway)]
mod throwaway;
#[cfg(verus_keep_ghost)]
mod witness;
