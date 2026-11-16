// SPDX-License-Identifier: MIT

//! CoreBridge::send's ensures at an unchanged requester token, still idle.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/core_bridge.rs	CoreBridge::send	returns
//! refused: unchanged: post_req.pending()

use vstd::prelude::*;

verus! {

use crate::core_bridge::{ChannelOp, CoreBridge, Req};

impl super::CoreBridgeSend for () {
    proof fn unchanged<T, Op: ChannelOp<T>>(bridge: &CoreBridge<T, Op>, cpu: usize, pre_req: Req<T, Op>, post_req: Req<T, Op>, val: T) {}
}

} // verus!
