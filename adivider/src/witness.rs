// SPDX-License-Identifier: MIT

//! The witness: a verified call of `check` on a layout constructed from its types, built into no image.

use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use crate::*;

verus! {

/// Tenants 1 and 2 divide the gigabyte from 1 GiB and share an endpoint at 1 GiB + 6 MiB, tenant 1
/// holding the grant right and tenant 2 receiving, with the two tenants joined.
pub fn witness_layout() -> (ok: bool)
    ensures
        ok,
{
    proof {
        lemma2_to64();
        lemma_u64_shl_is_mul(PAGE_BYTES, 18);
        lemma_u64_shl_is_mul(PAGE_BYTES, 9);
    }
    let gig: u64 = PAGE_BYTES << 18u64;
    let two_meg: u64 = PAGE_BYTES << 9u64;
    let held: [Block; 1] = [Block { base: gig, order: 18 }];
    let rows: [Row; 2] = [
        Row {
            tenant: 1,
            kind: Kind::Endpoint,
            block: Block { base: gig + 3 * two_meg, order: 0 },
            rights: SEND | GRANT,
            shared: true,
        },
        Row {
            tenant: 2,
            kind: Kind::Endpoint,
            block: Block { base: gig + 3 * two_meg, order: 0 },
            rights: RECEIVE,
            shared: true,
        },
    ];
    let joins: [Join; 1] = [Join { a: 2, b: 1 }];
    proof {
        assert(held@[0] == example_held()[0]);
        assert(held@ =~= example_held());
        assert(rows@[0] == endpoint_rows()[0]);
        assert(rows@[1] == endpoint_rows()[1]);
        assert(rows@ =~= endpoint_rows());
        assert(joins@[0] == example_joins()[0]);
        assert(joins@ =~= example_joins());
        example_grant_joined_passes();
    }
    check(&held, &rows, &joins)
}

} // verus!
