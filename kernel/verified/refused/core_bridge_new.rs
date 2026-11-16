// SPDX-License-Identifier: MIT

//! CoreBridge::new's ensures at a bridge that is not well-formed.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/core_bridge.rs	CoreBridge::new	returns
//! refused: wrong: bridge.wf()

use vstd::prelude::*;

verus! {

use crate::core_bridge::{ChannelOp, CoreBridge, Req, Srv};

impl super::CoreBridgeNew for () {
    proof fn wrong<T, Op: ChannelOp<T>>(bridge: CoreBridge<T, Op>, reqs: Map<int, Req<T, Op>>, srvs: Map<int, Srv<T, Op>>) {}
}

} // verus!
