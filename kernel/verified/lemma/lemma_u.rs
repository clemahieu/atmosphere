use vstd::prelude::*;
use vstd::seq::*;

verus! {
use crate::util::page_ptr_util_u::*;

pub broadcast proof fn map_equal_implies_submap_each_other<K, V>(a: Map<K, V>, b: Map<K, V>)
    requires
        a =~= b,
    ensures
        #[trigger] a.submap_of(b),
        b.submap_of(a),
{
}

} // verus!
