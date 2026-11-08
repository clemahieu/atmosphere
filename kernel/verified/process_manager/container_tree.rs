use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::array_set::*;
use crate::process_manager::container::*;
use crate::pptr::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::process_manager::container_util_t::*;

pub open spec fn container_perms_wf(
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].is_init()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].addr() == c_ptr
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children.wf()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children.unique()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().uppertree_seq@.no_duplicates()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children@.contains(
            c_ptr,
        ) == false
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().subtree_set@.finite()
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr)
            ==> container_perms[c_ptr].value().uppertree_seq@.len()
            == container_perms[c_ptr].value().depth
}

pub closed spec fn container_root_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& container_perms.dom().contains(root_container)
    &&& container_perms[root_container].value().depth == 0
    &&& forall|c_ptr: ContainerPtr|

        #![trigger container_perms.dom().contains(c_ptr)]
        container_perms.dom().contains(c_ptr) && c_ptr != root_container
            ==> container_perms[c_ptr].value().depth != 0
    &&& forall|c_ptr: ContainerPtr|

        #![trigger container_perms.dom().contains(c_ptr)]
        container_perms.dom().contains(c_ptr) && c_ptr != root_container
            ==> container_perms[c_ptr].value().parent.is_Some()
}

pub closed spec fn container_childern_parent_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr, child_c_ptr: ContainerPtr|
        #![trigger container_perms[c_ptr].value().children@.contains(child_c_ptr)]
        container_perms.dom().contains(c_ptr) && container_perms[c_ptr].value().children@.contains(
            child_c_ptr,
        ) ==> container_perms.dom().contains(child_c_ptr)
            && container_perms[child_c_ptr].value().parent.unwrap() == c_ptr
            && container_perms[child_c_ptr].value().depth == container_perms[c_ptr].value().depth
            + 1
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
        container_perms.dom().contains(c_ptr) && container_perms[c_ptr].value().parent.is_Some()
            ==> container_perms.dom().contains(container_perms[c_ptr].value().parent.unwrap())
            && container_perms[container_perms[c_ptr].value().parent.unwrap()].value().children@.contains(
        c_ptr)
}

pub closed spec fn containers_linkedlist_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(container_perms[c_ptr].value().parent.unwrap())]

        container_perms.dom().contains(c_ptr) && c_ptr != root_container
            ==> container_perms[c_ptr].value().parent.is_Some() && container_perms.dom().contains(
            container_perms[c_ptr].value().parent.unwrap(),
        )
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]
        container_perms.dom().contains(c_ptr) && c_ptr != root_container
            ==> container_perms[c_ptr].value().parent_rev_ptr.is_Some()
            && container_perms[container_perms[c_ptr].value().parent.unwrap()].value().children@.contains(
        c_ptr)
            && container_perms[container_perms[c_ptr].value().parent.unwrap()].value().children.get_node_ref(c_ptr) == 
        container_perms[c_ptr].value().parent_rev_ptr.unwrap()
}

pub closed spec fn container_childern_depth_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr|
        #![trigger container_perms.dom().contains(c_ptr)]

        container_perms.dom().contains(c_ptr) && c_ptr != root_container
            ==> container_perms[c_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            - 1] == container_perms[c_ptr].value().parent.unwrap()
}

pub closed spec fn container_subtree_set_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr, sub_c_ptr: ContainerPtr|

        #![trigger container_perms[c_ptr].value().subtree_set@.contains(sub_c_ptr)]
        container_perms.dom().contains(c_ptr)
            && container_perms[c_ptr].value().subtree_set@.contains(sub_c_ptr)
            ==> container_perms.dom().contains(sub_c_ptr)
            && container_perms[sub_c_ptr].value().uppertree_seq@.len()
            > container_perms[c_ptr].value().depth
            && container_perms[sub_c_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth as int]
            == c_ptr
}

pub closed spec fn container_uppertree_seq_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr, u_ptr: ContainerPtr|
        #![trigger container_perms[c_ptr].value().uppertree_seq@.contains(u_ptr)]
        container_perms.dom().contains(c_ptr)
            && container_perms[c_ptr].value().uppertree_seq@.contains(u_ptr)
            ==> container_perms.dom().contains(u_ptr)
            && container_perms[c_ptr].value().uppertree_seq@[container_perms[u_ptr].value().depth as int]
            == u_ptr && container_perms[u_ptr].value().depth
            == container_perms[c_ptr].value().uppertree_seq@.index_of(u_ptr)
            && container_perms[u_ptr].value().subtree_set@.contains(c_ptr)
            && container_perms[u_ptr].value().uppertree_seq@
            =~= container_perms[c_ptr].value().uppertree_seq@.subrange(
            0,
            container_perms[u_ptr].value().depth as int,
        )
}

pub closed spec fn container_subtree_set_exclusive(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    &&& forall|c_ptr: ContainerPtr, sub_c_ptr: ContainerPtr|
        #![trigger container_perms[c_ptr].value().subtree_set@.contains(sub_c_ptr), container_perms[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)]
        container_perms.dom().contains(c_ptr) && container_perms.dom().contains(sub_c_ptr) ==> (
        container_perms[c_ptr].value().subtree_set@.contains(sub_c_ptr)
            == container_perms[sub_c_ptr].value().uppertree_seq@.contains(c_ptr))
}

pub open spec fn container_tree_wf(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
) -> bool {
    // &&&
    // container_perms_wf(container_perms)
    &&& container_root_wf(root_container, container_perms)
    &&& container_childern_parent_wf(root_container, container_perms)
    &&& containers_linkedlist_wf(root_container, container_perms)
    &&& container_childern_depth_wf(root_container, container_perms)
    &&& container_subtree_set_wf(root_container, container_perms)
    &&& container_uppertree_seq_wf(root_container, container_perms)
    &&& container_subtree_set_exclusive(root_container, container_perms)
}

/// `upper` lists existing containers from the root down, each the parent of the next.
pub open spec fn container_ancestors_wf(
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    upper: Seq<ContainerPtr>,
) -> bool {
    &&& upper.no_duplicates()
    &&& forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() ==> container_perms.dom().contains(upper[i])
            && container_perms[upper[i]].is_init() && container_perms[upper[i]].addr() == upper[i]
    &&& forall|i: int|
        #![trigger upper[i]]
        0 < i < upper.len() ==> container_perms[upper[i]].value().parent == Some(upper[i - 1])
}

/// A container's uppertree_seq walks its parent links, ends at its parent, and does not include the container.
pub proof fn container_ancestors_inv(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
    ensures
        container_ancestors_wf(container_perms, container_perms[c_ptr].value().uppertree_seq@),
        container_perms[c_ptr].value().uppertree_seq@.contains(c_ptr) == false,
        container_perms[c_ptr].value().depth > 0 ==> container_perms[c_ptr].value().parent
            == Some(container_perms[c_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth - 1]),
{
    assert(container_perms.dom().contains(c_ptr));
    let upper = container_perms[c_ptr].value().uppertree_seq@;
    assert(upper.no_duplicates());
    assert forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() implies {
        let u = upper[i];
        &&& container_perms.dom().contains(u)
        &&& container_perms[u].value().depth == i
        &&& container_perms[u].value().uppertree_seq@ =~= upper.subrange(0, i)
    } by {
        let u = upper[i];
        assert(upper.contains(u));
        assert(container_perms.dom().contains(u));
        let k = upper.index_of(u);
        assert(0 <= k < upper.len() && upper[k] == u);
        assert(k == i) by {
            if k != i {
                assert(upper[k] != upper[i]);
            }
        };
        assert(container_perms[u].value().depth == k);
    };
    assert forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() implies container_perms.dom().contains(upper[i])
        && container_perms[upper[i]].is_init() && container_perms[upper[i]].addr() == upper[i] by {
        assert(container_perms.dom().contains(upper[i]));
    };
    assert forall|i: int|
        #![trigger upper[i]]
        0 < i < upper.len() implies container_perms[upper[i]].value().parent == Some(upper[i - 1]) by {
        let u = upper[i];
        assert(container_perms.dom().contains(u));
        assert(container_perms[u].value().depth == i);
        assert(u != root_container);
        assert(container_perms[u].value().parent.is_Some());
        assert(container_perms[u].value().uppertree_seq@[i - 1] == upper[i - 1]);
        assert(container_perms[u].value().uppertree_seq@[i - 1] == container_perms[u].value().parent.unwrap());
    };
    if upper.contains(c_ptr) {
        assert(upper.index_of(c_ptr) == container_perms[c_ptr].value().depth);
        assert(upper.len() == container_perms[c_ptr].value().depth);
        assert(false);
    }
    if container_perms[c_ptr].value().depth > 0 {
        assert(c_ptr != root_container);
        assert(container_perms[c_ptr].value().parent.is_Some());
        assert(upper[container_perms[c_ptr].value().depth - 1] == container_perms[c_ptr].value().parent.unwrap());
    }
}

/// A container's uppertree_seq pushed with the container lists the ancestors of a new child of it,
/// in a map that differs from the well-formed one only at the container (its parent kept) and at the child.
pub proof fn container_ancestors_push(
    root_container: ContainerPtr,
    old_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
    new_ptr: ContainerPtr,
)
    requires
        container_perms_wf(old_perms),
        container_tree_wf(root_container, old_perms),
        old_perms.dom().contains(c_ptr),
        old_perms.dom().contains(new_ptr) == false,
        forall|p: ContainerPtr|
            #![trigger new_perms[p]]
            old_perms.dom().contains(p) && p != c_ptr ==> new_perms.dom().contains(p) && new_perms[p]
                == old_perms[p],
        new_perms.dom().contains(c_ptr),
        new_perms[c_ptr].is_init(),
        new_perms[c_ptr].addr() == c_ptr,
        new_perms[c_ptr].value().parent == old_perms[c_ptr].value().parent,
    ensures
        container_ancestors_wf(new_perms, old_perms[c_ptr].value().uppertree_seq@.push(c_ptr)),
        old_perms[c_ptr].value().uppertree_seq@.push(c_ptr).contains(new_ptr) == false,
{
    container_ancestors_inv(root_container, old_perms, c_ptr);
    let old_upper = old_perms[c_ptr].value().uppertree_seq@;
    let new_upper = old_upper.push(c_ptr);
    assert(old_upper.len() == old_perms[c_ptr].value().depth);
    assert(old_upper.contains(c_ptr) == false);
    assert(old_upper.contains(new_ptr) == false) by {
        if old_upper.contains(new_ptr) {
            assert(old_perms.dom().contains(new_ptr));
        }
    };
    assert(c_ptr != new_ptr);
    assert(new_upper.no_duplicates()) by {
        assert forall|i: int, j: int|
            0 <= i < new_upper.len() && 0 <= j < new_upper.len() && i != j implies new_upper[i]
            != new_upper[j] by {
            if i < old_upper.len() && j < old_upper.len() {
                assert(old_upper[i] != old_upper[j]);
            } else if i == old_upper.len() {
                assert(old_upper[j] == new_upper[j]);
                assert(old_upper.contains(old_upper[j]));
            } else {
                assert(old_upper[i] == new_upper[i]);
                assert(old_upper.contains(old_upper[i]));
            }
        };
    };
    assert forall|i: int|
        #![trigger new_upper[i]]
        0 <= i < new_upper.len() implies new_perms.dom().contains(new_upper[i])
        && new_perms[new_upper[i]].is_init() && new_perms[new_upper[i]].addr() == new_upper[i] by {
        if i < old_upper.len() {
            assert(new_upper[i] == old_upper[i]);
            assert(old_upper.contains(old_upper[i]));
            assert(new_perms[old_upper[i]] == old_perms[old_upper[i]]);
        } else {
            assert(new_upper[i] == c_ptr);
        }
    };
    assert forall|i: int|
        #![trigger new_upper[i]]
        0 < i < new_upper.len() implies new_perms[new_upper[i]].value().parent == Some(
        new_upper[i - 1],
    ) by {
        if i < old_upper.len() {
            assert(new_upper[i] == old_upper[i]);
            assert(new_upper[i - 1] == old_upper[i - 1]);
            assert(old_upper.contains(old_upper[i]));
            assert(new_perms[old_upper[i]] == old_perms[old_upper[i]]);
        } else {
            assert(new_upper[i] == c_ptr);
            assert(new_upper[i - 1] == old_upper[i - 1]);
            assert(old_perms[c_ptr].value().depth > 0);
        }
    };
    if new_upper.contains(new_ptr) {
        let k = choose|k: int| 0 <= k < new_upper.len() && new_upper[k] == new_ptr;
        if k < old_upper.len() {
            assert(old_upper[k] == new_ptr);
            assert(old_upper.contains(new_ptr));
        }
        assert(false);
    }
}

pub proof fn container_subtree_inv(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr: ContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]

            container_perms.dom().contains(c_ptr)
                ==> container_perms[c_ptr].value().subtree_set@.subset_of(container_perms.dom())
                && container_perms[c_ptr].value().subtree_set@.contains(c_ptr) == false,
{
}

pub proof fn same_or_deeper_depth_imply_none_ancestor(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    a_ptr: ContainerPtr,
    child_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(a_ptr),
        container_perms.dom().contains(child_ptr),
        container_perms[a_ptr].value().depth >= container_perms[child_ptr].value().depth,
    ensures
        container_perms[a_ptr].value().subtree_set@.contains(child_ptr) == false,
{
    assert(container_perms[a_ptr].value().uppertree_seq@.len()
        == container_perms[a_ptr].value().depth);
    assert(container_perms[child_ptr].value().uppertree_seq@.len()
        == container_perms[child_ptr].value().depth);
}

pub proof fn no_child_imply_no_subtree(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
        container_perms[c_ptr].value().children@ =~= Seq::empty(),
    ensures
        container_perms[c_ptr].value().subtree_set@ =~= Set::empty(),
{
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.contains(c_ptr));
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.subrange(
            0,
            container_perms[c_ptr].value().depth as int,
        ) == container_perms[c_ptr].value().uppertree_seq@);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr) ==> s_ptr != root_container);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[c_ptr].value().children@.contains(s_ptr) == false);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().parent.unwrap() != c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@[container_perms[s_ptr].value().depth
            - 1] != c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth as int]
            == c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.len()
            > container_perms[c_ptr].value().depth);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.len()
            != container_perms[c_ptr].value().depth + 1);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.contains(
            container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms.dom().contains(s_ptr));
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms.dom().contains(
            container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.contains(
            container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.subrange(
            0,
            container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
                + 1]].value().depth as int,
        )
            =~= container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().uppertree_seq@);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.no_duplicates());
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[s_ptr].value().uppertree_seq@.index_of(
            container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
        ) == container_perms[c_ptr].value().depth + 1);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().depth == container_perms[c_ptr].value().depth + 1);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().uppertree_seq@[container_perms[c_ptr].value().depth as int] == c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().uppertree_seq@[container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().depth - 1] == c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().parent.unwrap() == c_ptr);
    assert(forall|s_ptr: ContainerPtr|
        #![auto]
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr)
            ==> container_perms[c_ptr].value().children@.contains(
            container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
        ));
}

pub proof fn in_child_imply_in_subtree(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
    child_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
        container_perms[c_ptr].value().children@.contains(child_ptr),
    ensures
        container_perms[c_ptr].value().subtree_set@.contains(child_ptr),
{    assert(container_perms[child_ptr].value().parent.unwrap() == c_ptr);
    assert(container_perms[child_ptr].value().depth == container_perms[c_ptr].value().depth + 1);
    assert(container_perms[child_ptr].value().uppertree_seq@.len()
        == container_perms[child_ptr].value().depth);
    assert(container_perms[c_ptr].value().uppertree_seq@.len()
        == container_perms[c_ptr].value().depth);
    assert(container_perms[child_ptr].value().uppertree_seq@[container_perms[child_ptr].value().depth
        - 1] == c_ptr);
    assert(container_perms[child_ptr].value().uppertree_seq@.contains(c_ptr));
    }

pub proof fn in_child_impy_in_subtree(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
    child_ptr: ContainerPtr,
    s_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
        container_perms[c_ptr].value().children@.contains(child_ptr),
        container_perms[child_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr),
{
    assert(container_perms[child_ptr].value().parent.unwrap() == c_ptr);
    assert(container_perms[child_ptr].value().depth == container_perms[c_ptr].value().depth + 1);
    assert(container_perms[child_ptr].value().uppertree_seq@.len()
        == container_perms[child_ptr].value().depth);
    assert(container_perms[c_ptr].value().uppertree_seq@.len()
        == container_perms[c_ptr].value().depth);
    assert(container_perms[child_ptr].value().uppertree_seq@[container_perms[child_ptr].value().depth
        - 1] == c_ptr);
    assert(container_perms[s_ptr].value().uppertree_seq@.contains(child_ptr));
    assert(container_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        container_perms[child_ptr].value().depth as int,
    ) == container_perms[child_ptr].value().uppertree_seq@);
    assert(container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth as int]
        == c_ptr);
    assert(container_perms[s_ptr].value().uppertree_seq@.contains(c_ptr));
}

pub proof fn in_subtree_impy_in_subsubtree(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
    child_ptr: ContainerPtr,
    s_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
        container_perms[c_ptr].value().subtree_set@.contains(child_ptr),
        container_perms[child_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr),
{
    assert(container_perms.dom().contains(s_ptr));
    assert(container_perms[child_ptr].value().uppertree_seq@.contains(c_ptr));
    assert(container_perms[s_ptr].value().uppertree_seq@.contains(child_ptr));
    assert(container_perms[s_ptr].value().uppertree_seq@.subrange(0, container_perms[child_ptr].value().depth as int) 
        == container_perms[child_ptr].value().uppertree_seq@);
    assert(container_perms[s_ptr].value().uppertree_seq@.contains(c_ptr));
}

pub proof fn in_subtree_imply_exist_in_child(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    c_ptr: ContainerPtr,
    s_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(c_ptr),
        container_perms[c_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        container_perms[c_ptr].value().children@.contains(s_ptr) || (exists|child_ptr: ContainerPtr|

            #![auto]
            container_perms[c_ptr].value().children@.contains(child_ptr)
                && container_perms[child_ptr].value().subtree_set@.contains(s_ptr)),
{
    assert(container_perms[s_ptr].value().uppertree_seq@.contains(c_ptr));
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        container_perms[c_ptr].value().depth as int,
    ) == container_perms[c_ptr].value().uppertree_seq@);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false ==> s_ptr
        != root_container);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().parent.unwrap() != c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.len()
        > container_perms[c_ptr].value().depth);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@[container_perms[s_ptr].value().depth - 1]
        != c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth as int]
        == c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.len()
        > container_perms[c_ptr].value().depth);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.len()
        != container_perms[c_ptr].value().depth + 1);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.len()
        > container_perms[c_ptr].value().depth + 1);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.contains(
        container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
    ));
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms.dom().contains(
        container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
    ));
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
            + 1]].value().depth as int,
    )
        =~= container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().uppertree_seq@);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.no_duplicates());
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[s_ptr].value().uppertree_seq@.index_of(
        container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
    ) == container_perms[c_ptr].value().depth + 1);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().depth == container_perms[c_ptr].value().depth + 1);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().uppertree_seq@.len() == container_perms[c_ptr].value().depth + 1);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().uppertree_seq@[container_perms[c_ptr].value().depth as int] == c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().uppertree_seq@[container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().depth - 1] == c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().parent.unwrap() == c_ptr);
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[c_ptr].value().children@.contains(
        container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth + 1],
    ));
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false
        ==> container_perms[container_perms[s_ptr].value().uppertree_seq@[container_perms[c_ptr].value().depth
        + 1]].value().subtree_set@.contains(s_ptr));
    assert(container_perms[c_ptr].value().children@.contains(s_ptr) == false ==> (exists|
        child_ptr: ContainerPtr,
    |
        #![auto]
        container_perms[c_ptr].value().children@.contains(child_ptr)
            && container_perms[child_ptr].value().subtree_set@.contains(s_ptr)));
}

pub proof fn not_in_dom_imply_not_in_any_children_set(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    s_ptr: ContainerPtr,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(s_ptr) == false,
{
    assert(forall|c_ptr: ContainerPtr|
        #![auto]
        container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children@.contains(
            s_ptr,
        ) == false);
}

pub proof fn container_tree_wf_imply_uppertree_subset_of_tree(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr: ContainerPtr, parent_c_ptr: ContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
                && container_perms[c_ptr].value().uppertree_seq@.contains(parent_c_ptr)
                ==> container_perms.dom().contains(parent_c_ptr),
{
}

pub proof fn container_tree_wf_imply_childern_uppertree_specs(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr: ContainerPtr, child_c_ptr: ContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
                && container_perms[c_ptr].value().children@.contains(child_c_ptr)
                ==> container_perms.dom().contains(child_c_ptr),
        forall|c_ptr: ContainerPtr, parent_c_ptr: ContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
                && container_perms[c_ptr].value().uppertree_seq@.contains(parent_c_ptr)
                ==> container_perms.dom().contains(parent_c_ptr),
        forall|c_ptr: ContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
                ==> container_perms[c_ptr].value().uppertree_seq@.contains(c_ptr) == false,
{
}

pub proof fn container_tree_wf_imply_childern_have_parent(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr: ContainerPtr|
        #![auto]
        container_perms.dom().contains(c_ptr) && container_perms[c_ptr].value().depth != 0
            ==> container_perms[c_ptr].value().parent.is_Some()
            && container_perms.dom().contains(container_perms[c_ptr].value().parent.unwrap())
            && container_perms[c_ptr].value().parent_rev_ptr.is_Some()
            && container_perms[container_perms[c_ptr].value().parent.unwrap()].value().children@.contains(c_ptr)
            && container_perms[container_perms[c_ptr].value().parent.unwrap()].value().children.get_node_ref(c_ptr)
            == container_perms[c_ptr].value().parent_rev_ptr.unwrap()
            && 
            container_perms[c_ptr].value().parent.unwrap() != c_ptr
{
}

pub proof fn container_tree_inv(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr: ContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr) ==> container_perms[c_ptr].value().children.wf(),
{
}

pub proof fn container_childern_disjoint_inv(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
        container_perms.dom().contains(container_ptr),
    ensures
        forall|c_ptr_i: ContainerPtr, child_c_ptr: ContainerPtr|
        #![trigger container_perms[c_ptr_i].value().children@.contains(child_c_ptr)]
        container_perms.dom().contains(c_ptr_i) 
            && c_ptr_i != container_ptr && container_perms[container_ptr].value().children@.contains(child_c_ptr) 
            ==> container_perms[c_ptr_i].value().children@.contains(child_c_ptr) == false
{}

pub proof fn container_subtree_disjoint_inv(
    root_container: ContainerPtr,
    container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_perms_wf(container_perms),
        container_tree_wf(root_container, container_perms),
    ensures
        forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
            #![trigger  container_perms[c_ptr_i].value(), container_perms[c_ptr_j].value()]
            #![trigger  container_perms[c_ptr_i].value().subtree_set@.insert(c_ptr_i), container_perms[c_ptr_j].value().subtree_set@.insert(c_ptr_j)]
            container_perms.dom().contains(c_ptr_i) && container_perms.dom().contains(c_ptr_j)
                && c_ptr_i != c_ptr_j && container_perms[c_ptr_i].value().depth
                == container_perms[c_ptr_j].value().depth
                ==> container_perms[c_ptr_i].value().subtree_set@.disjoint(
                container_perms[c_ptr_j].value().subtree_set@,
            ) && container_perms[c_ptr_i].value().subtree_set@.contains(c_ptr_j) == false
                && container_perms[c_ptr_j].value().subtree_set@.contains(c_ptr_i) == false
                && container_perms[c_ptr_i].value().subtree_set@.insert(c_ptr_i).disjoint(
                container_perms[c_ptr_j].value().subtree_set@.insert(c_ptr_j),
            ),
{
    assert(forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
        #![trigger  container_perms[c_ptr_i].value().subtree_set, container_perms[c_ptr_j].value().subtree_set]
        container_perms.dom().contains(c_ptr_i) && container_perms.dom().contains(c_ptr_j)
            && c_ptr_i != c_ptr_j && container_perms[c_ptr_i].value().depth
            == container_perms[c_ptr_j].value().depth ==> c_ptr_i != root_container && c_ptr_j
            != root_container && container_perms[c_ptr_i].value().depth != 0
            && container_perms[c_ptr_j].value().depth != 0);

    assert(forall|
        c_ptr_i: ContainerPtr,
        c_ptr_j: ContainerPtr,
        sub_c_ptr_i: ContainerPtr,
        sub_c_ptr_j: ContainerPtr,
    |
        #![trigger  container_perms[c_ptr_i].value().subtree_set@.contains(sub_c_ptr_i), container_perms[c_ptr_j].value().subtree_set@.contains(sub_c_ptr_j)]
        container_perms.dom().contains(c_ptr_i) && container_perms.dom().contains(c_ptr_j)
            && c_ptr_i != c_ptr_j && container_perms[c_ptr_i].value().depth
            == container_perms[c_ptr_j].value().depth
            && container_perms[c_ptr_i].value().subtree_set@.contains(sub_c_ptr_i)
            && container_perms[c_ptr_j].value().subtree_set@.contains(sub_c_ptr_j)
            ==> container_perms[sub_c_ptr_i].value().uppertree_seq@[container_perms[c_ptr_i].value().depth as int]
            == c_ptr_i
            && container_perms[sub_c_ptr_j].value().uppertree_seq@[container_perms[c_ptr_j].value().depth as int]
            == c_ptr_j);
}

pub proof fn container_no_change_to_tree_fields_imply_wf(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
)
    requires
        container_tree_wf(root_container, old_container_perms),
        container_perms_wf(new_container_perms),
        old_container_perms.dom() =~= new_container_perms.dom(),
        forall|c_ptr: ContainerPtr|

            #![trigger old_container_perms.dom().contains(c_ptr)]
            old_container_perms.dom().contains(c_ptr) ==> new_container_perms[c_ptr].is_init()
                && old_container_perms[c_ptr].value().parent
                =~= new_container_perms[c_ptr].value().parent
                && old_container_perms[c_ptr].value().parent_rev_ptr
                =~= new_container_perms[c_ptr].value().parent_rev_ptr
                && old_container_perms[c_ptr].value().children
                =~= new_container_perms[c_ptr].value().children
                && old_container_perms[c_ptr].value().depth
                =~= new_container_perms[c_ptr].value().depth
                && old_container_perms[c_ptr].value().uppertree_seq
                =~= new_container_perms[c_ptr].value().uppertree_seq
                && old_container_perms[c_ptr].value().subtree_set
                =~= new_container_perms[c_ptr].value().subtree_set,
    ensures
        container_tree_wf(root_container, new_container_perms),
{
}

pub open spec fn new_container_tree_ensures(
    root_container: ContainerPtr,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_ptr: ContainerPtr,
) -> bool {
    &&& root_container == new_container_ptr
    &&& container_perms_wf(new_container_perms)
    &&& new_container_perms.dom() == set![new_container_ptr]
    &&& new_container_perms[new_container_ptr].value().parent.is_None()
    &&& new_container_perms[new_container_ptr].value().parent_rev_ptr.is_None()
    &&& new_container_perms[new_container_ptr].value().children@ =~= Seq::empty()
    &&& new_container_perms[new_container_ptr].value().uppertree_seq@ =~= Seq::empty()
    &&& new_container_perms[new_container_ptr].value().depth == 0
    &&& new_container_perms[new_container_ptr].value().subtree_set@ =~= Set::<ContainerPtr>::empty()
    &&& new_container_perms[new_container_ptr].value().children.unique()
}

pub proof fn new_container_tree_infer_wf(
    root_container: ContainerPtr,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_tree_ensures(root_container, new_container_perms, new_container_ptr),
    ensures
        container_root_wf(root_container, new_container_perms),
        container_childern_parent_wf(root_container, new_container_perms),
        containers_linkedlist_wf(root_container, new_container_perms),
        container_childern_depth_wf(root_container, new_container_perms),
        container_subtree_set_wf(root_container, new_container_perms),
        container_uppertree_seq_wf(root_container, new_container_perms),
        container_subtree_set_exclusive(root_container, new_container_perms),
        container_tree_wf(root_container, new_container_perms),
{
}

pub open spec fn new_container_ensures(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
) -> bool {
    &&& container_perms_wf(old_container_perms)
    &&& container_perms_wf(new_container_perms)
    &&& container_tree_wf(root_container, old_container_perms)
    &&& old_container_perms.dom().contains(container_ptr)
    &&& old_container_perms.dom().contains(new_container_ptr) == false
    &&& old_container_perms[container_ptr].value().children.len() < PROC_CHILD_LIST_LEN
    &&& old_container_perms[container_ptr].value().depth < usize::MAX
    &&& new_container_perms.dom() == old_container_perms.dom().insert(new_container_ptr)
    &&& new_container_perms[new_container_ptr].value().parent =~= Some(container_ptr)
    &&& new_container_perms[new_container_ptr].value().parent_rev_ptr.is_Some()
    &&& new_container_perms[new_container_ptr].value().children@ =~= Seq::empty()
    &&& new_container_perms[new_container_ptr].value().uppertree_seq@
        =~= old_container_perms[container_ptr].value().uppertree_seq@.push(container_ptr)
    &&& new_container_perms[new_container_ptr].value().depth as int
        =~= old_container_perms[container_ptr].value().depth + 1
    &&& new_container_perms[new_container_ptr].value().uppertree_seq@
        =~= old_container_perms[container_ptr].value().uppertree_seq@.push(container_ptr)
    &&& new_container_perms[new_container_ptr].value().subtree_set@ =~= Set::<ContainerPtr>::empty()
    &&& forall|c_ptr: ContainerPtr|

        #![trigger old_container_perms.dom().contains(c_ptr)]
        old_container_perms.dom().contains(c_ptr) && c_ptr != container_ptr
            ==> new_container_perms[c_ptr].value().parent
            =~= old_container_perms[c_ptr].value().parent
            && new_container_perms[c_ptr].value().parent_rev_ptr
            =~= old_container_perms[c_ptr].value().parent_rev_ptr
            && new_container_perms[c_ptr].value().children
            =~= old_container_perms[c_ptr].value().children
            && new_container_perms[c_ptr].value().depth =~= old_container_perms[c_ptr].value().depth
            && new_container_perms[c_ptr].value().uppertree_seq
            =~= old_container_perms[c_ptr].value().uppertree_seq
    &&& forall|c_ptr: ContainerPtr|

        #![trigger new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)]
        new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)
            ==> new_container_perms[c_ptr].value().subtree_set@
            =~= old_container_perms[c_ptr].value().subtree_set@.insert(new_container_ptr)
    &&& forall|c_ptr: ContainerPtr|
        #![trigger old_container_perms.dom().contains(c_ptr)]

        old_container_perms.dom().contains(c_ptr)
            && new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)
            == false ==> new_container_perms[c_ptr].value().subtree_set
            =~= old_container_perms[c_ptr].value().subtree_set
    &&& new_container_perms[container_ptr].value().parent
        =~= old_container_perms[container_ptr].value().parent
    &&& new_container_perms[container_ptr].value().parent_rev_ptr
        =~= old_container_perms[container_ptr].value().parent_rev_ptr
    &&& new_container_perms[container_ptr].value().children@
        =~= old_container_perms[container_ptr].value().children@.push(new_container_ptr)
    &&& new_container_perms[container_ptr].value().depth
        =~= old_container_perms[container_ptr].value().depth
    &&& new_container_perms[container_ptr].value().uppertree_seq
        =~= old_container_perms[container_ptr].value().uppertree_seq
    &&& new_container_perms[container_ptr].value().children.wf()
    &&& new_container_perms[container_ptr].value().children@
        == old_container_perms[container_ptr].value().children@.push(new_container_ptr)
    &&& new_container_perms[container_ptr].value().children.len()
        == old_container_perms[container_ptr].value().children.len() + 1
    &&&
    forall|v:ContainerPtr|
        #![auto]
        old_container_perms[container_ptr].value().children@.contains(v) ==> 
            old_container_perms[container_ptr].value().children.get_node_ref(v) == 
                new_container_perms[container_ptr].value().children.get_node_ref(v)
    &&&
    new_container_perms[container_ptr].value().children.get_node_ref(new_container_ptr) == 
        new_container_perms[new_container_ptr].value().parent_rev_ptr.unwrap()
    &&& new_container_perms[container_ptr].value().children.unique()
}

pub proof fn new_container_preserve_tree_inv(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
// new_container_ensures(root_container, old_container_perms, new_container_perms, container_ptr, new_container_ptr),

        container_perms_wf(old_container_perms),
        container_perms_wf(new_container_perms),
        container_tree_wf(root_container, old_container_perms),
        old_container_perms.dom().contains(container_ptr),
        old_container_perms.dom().contains(new_container_ptr) == false,
        old_container_perms[container_ptr].value().children.len() < PROC_CHILD_LIST_LEN,
        old_container_perms[container_ptr].value().depth < usize::MAX,
        new_container_perms.dom() == old_container_perms.dom().insert(new_container_ptr),
        new_container_perms[new_container_ptr].value().parent =~= Some(container_ptr),
        new_container_perms[new_container_ptr].value().parent_rev_ptr.is_Some(),
        new_container_perms[new_container_ptr].value().children@ =~= Seq::empty(),
        new_container_perms[new_container_ptr].value().uppertree_seq@
            =~= old_container_perms[container_ptr].value().uppertree_seq@.push(container_ptr),
        new_container_perms[new_container_ptr].value().depth as int
            =~= old_container_perms[container_ptr].value().depth + 1,
        new_container_perms[new_container_ptr].value().uppertree_seq@
            =~= old_container_perms[container_ptr].value().uppertree_seq@.push(container_ptr),
        new_container_perms[new_container_ptr].value().subtree_set@ =~= Set::<
            ContainerPtr,
        >::empty(),
        forall|c_ptr: ContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]

            old_container_perms.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> new_container_perms[c_ptr].value().parent
                =~= old_container_perms[c_ptr].value().parent
                && new_container_perms[c_ptr].value().parent_rev_ptr
                =~= old_container_perms[c_ptr].value().parent_rev_ptr
                && new_container_perms[c_ptr].value().children
                =~= old_container_perms[c_ptr].value().children
                && new_container_perms[c_ptr].value().depth
                =~= old_container_perms[c_ptr].value().depth
                && new_container_perms[c_ptr].value().uppertree_seq
                =~= old_container_perms[c_ptr].value().uppertree_seq,
        forall|c_ptr: ContainerPtr|
            #![trigger new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)]
            #![trigger new_container_perms[c_ptr].value().subtree_set]
            #![trigger old_container_perms[c_ptr].value().subtree_set]
            new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)
                ==> new_container_perms[c_ptr].value().subtree_set@
                =~= old_container_perms[c_ptr].value().subtree_set@.insert(new_container_ptr),
        forall|c_ptr: ContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]

            old_container_perms.dom().contains(c_ptr)
                && new_container_perms[new_container_ptr].value().uppertree_seq@.contains(c_ptr)
                == false ==> new_container_perms[c_ptr].value().subtree_set
                =~= old_container_perms[c_ptr].value().subtree_set,
        new_container_perms[container_ptr].value().parent
            =~= old_container_perms[container_ptr].value().parent,
        new_container_perms[container_ptr].value().parent_rev_ptr
            =~= old_container_perms[container_ptr].value().parent_rev_ptr,
        new_container_perms[container_ptr].value().children@
            =~= old_container_perms[container_ptr].value().children@.push(new_container_ptr),
        new_container_perms[container_ptr].value().depth
            =~= old_container_perms[container_ptr].value().depth,
        new_container_perms[container_ptr].value().uppertree_seq
            =~= old_container_perms[container_ptr].value().uppertree_seq,
        new_container_perms[container_ptr].value().children.wf(),
        new_container_perms[container_ptr].value().children@
            == old_container_perms[container_ptr].value().children@.push(new_container_ptr),
        new_container_perms[container_ptr].value().children.len()
            == old_container_perms[container_ptr].value().children.len() + 1,
        forall|v:ContainerPtr|
            #![auto]
            old_container_perms[container_ptr].value().children@.contains(v) ==> 
                old_container_perms[container_ptr].value().children.get_node_ref(v) == 
                    new_container_perms[container_ptr].value().children.get_node_ref(v),
        new_container_perms[container_ptr].value().children.get_node_ref(new_container_ptr) == 
            new_container_perms[new_container_ptr].value().parent_rev_ptr.unwrap(),
        new_container_perms[container_ptr].value().children.unique(),
    ensures

        container_tree_wf(root_container, new_container_perms),
{
    new_container_preserve_tree_inv_1(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_2(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_3(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_4(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_5(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_6(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
    new_container_preserve_tree_inv_7(
        root_container,
        old_container_perms,
        new_container_perms,
        container_ptr,
        new_container_ptr,
    );
}

pub proof fn new_container_preserve_tree_inv_1(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures
        container_root_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_2(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures
// container_root_wf(root_container, new_container_perms),

        container_childern_parent_wf(
            root_container,
            new_container_perms,
        ),  //// containers_linkedlist_wf(root_container, new_container_perms),FORMATTER_NOT_INLINE_MARKER

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_3(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures

        container_childern_depth_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_4(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures

        container_subtree_set_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_5(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures

        container_uppertree_seq_wf(
            root_container,
            new_container_perms,
        ),
// container_subtree_set_exclusive(root_container, new_container_perms),

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_6(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures

        container_subtree_set_exclusive(root_container, new_container_perms),
{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub proof fn new_container_preserve_tree_inv_7(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
    new_container_ptr: ContainerPtr,
)
    requires
        new_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
            new_container_ptr,
        ),
    ensures

        containers_linkedlist_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_push_lemma::<ContainerPtr>();
    seq_push_unique_lemma::<ContainerPtr>();
}

pub open spec fn remove_container_ensures(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    // parent_container_ptr: ContainerPtr,
    container_ptr: ContainerPtr,
) -> bool {
    &&& container_perms_wf(old_container_perms)
    &&& container_perms_wf(new_container_perms)
    &&& container_tree_wf(root_container, old_container_perms)
    &&& old_container_perms.dom().contains(container_ptr)
    &&& container_ptr != root_container
    &&& old_container_perms[container_ptr].value().children@ == Seq::<ContainerPtr>::empty()
    &&& old_container_perms[container_ptr].value().parent.is_Some()
    &&& old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@.remove_value(container_ptr) ==
            new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@
    &&& new_container_perms.dom() == old_container_perms.dom().remove(container_ptr)
    &&& forall|c_ptr: ContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]
            old_container_perms.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> new_container_perms[c_ptr].value().parent
                =~= old_container_perms[c_ptr].value().parent
                && new_container_perms[c_ptr].value().parent_rev_ptr
                =~= old_container_perms[c_ptr].value().parent_rev_ptr
                && (c_ptr != old_container_perms[container_ptr].value().parent.unwrap() ==>
                new_container_perms[c_ptr].value().children
                =~= old_container_perms[c_ptr].value().children)
                && new_container_perms[c_ptr].value().depth =~= old_container_perms[c_ptr].value().depth
                && new_container_perms[c_ptr].value().uppertree_seq
                =~= old_container_perms[c_ptr].value().uppertree_seq
    &&& forall|c_ptr: ContainerPtr|
            #![trigger old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr)]
            old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr)
                ==> new_container_perms[c_ptr].value().subtree_set@
                =~= old_container_perms[c_ptr].value().subtree_set@.remove(container_ptr)
    &&& forall|c_ptr: ContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]
            new_container_perms.dom().contains(c_ptr)
                && old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr) == false 
                ==> new_container_perms[c_ptr].value().subtree_set
                    =~= old_container_perms[c_ptr].value().subtree_set
    &&& forall|v:ContainerPtr|
            #![auto]
            new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@.contains(v) ==> 
                old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.get_node_ref(v) == 
                    new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.get_node_ref(v)
}

pub proof fn remove_container_preserve_tree_inv_1(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_root_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
}

pub proof fn remove_container_preserve_tree_inv_2(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_childern_parent_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
    old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
    assert(forall|c_ptr: ContainerPtr, child_c_ptr: ContainerPtr|
        #![trigger new_container_perms[c_ptr].value().children@.contains(child_c_ptr)]
        new_container_perms.dom().contains(c_ptr) && new_container_perms[c_ptr].value().children@.contains(
            child_c_ptr,
        ) ==> new_container_perms.dom().contains(child_c_ptr)
            && new_container_perms[child_c_ptr].value().parent.unwrap() == c_ptr
            && new_container_perms[child_c_ptr].value().depth == new_container_perms[c_ptr].value().depth
            + 1);
    assert( forall|c_ptr: ContainerPtr|
        #![trigger new_container_perms.dom().contains(c_ptr)]
        new_container_perms.dom().contains(c_ptr) && new_container_perms[c_ptr].value().parent.is_Some()
            ==> new_container_perms.dom().contains(new_container_perms[c_ptr].value().parent.unwrap())
            && new_container_perms[new_container_perms[c_ptr].value().parent.unwrap()].value().children@.contains(
        c_ptr)
    );
}

pub proof fn remove_container_preserve_tree_inv_3(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        containers_linkedlist_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
    old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
}

pub proof fn remove_container_preserve_tree_inv_4(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_childern_depth_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
    old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
}

pub proof fn remove_container_preserve_tree_inv_5(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_subtree_set_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
    old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();

}

pub proof fn remove_container_preserve_tree_inv_6(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_uppertree_seq_wf(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
    old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
    no_child_imply_no_subtree(
        root_container,
        old_container_perms,
        container_ptr,
    );
}

pub proof fn remove_container_preserve_tree_inv_7(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        remove_container_ensures(
            root_container,
            old_container_perms,
            new_container_perms,
            container_ptr,
        ),
    ensures
        container_subtree_set_exclusive(
            root_container,
            new_container_perms,
        ),

{
    seq_remove_lemma::<ContainerPtr>();
    seq_remove_lemma_2::<ContainerPtr>();
}

pub proof fn remove_container_preserve_tree_inv(
    root_container: ContainerPtr,
    old_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    new_container_perms: Map<ContainerPtr, PointsTo<Container>>,
    container_ptr: ContainerPtr,
)
    requires
        // remove_container_ensures(
        //     root_container,
        //     old_container_perms,
        //     new_container_perms,
        //     container_ptr,
        // ),
    container_perms_wf(old_container_perms),
     container_perms_wf(new_container_perms),
     container_tree_wf(root_container, old_container_perms),
     old_container_perms.dom().contains(container_ptr),
     container_ptr != root_container,
     old_container_perms[container_ptr].value().children@ == Seq::<ContainerPtr>::empty(),
     old_container_perms[container_ptr].value().parent.is_Some(),
     old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@.remove_value(container_ptr) ==
        new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@,
     new_container_perms.dom() == old_container_perms.dom().remove(container_ptr),
     forall|c_ptr: ContainerPtr|
        #![trigger old_container_perms.dom().contains(c_ptr)]
        old_container_perms.dom().contains(c_ptr) && c_ptr != container_ptr
            ==> new_container_perms[c_ptr].value().parent
            =~= old_container_perms[c_ptr].value().parent
            && new_container_perms[c_ptr].value().parent_rev_ptr
            =~= old_container_perms[c_ptr].value().parent_rev_ptr
            && (c_ptr != old_container_perms[container_ptr].value().parent.unwrap() ==>
            new_container_perms[c_ptr].value().children
            =~= old_container_perms[c_ptr].value().children)
            && new_container_perms[c_ptr].value().depth =~= old_container_perms[c_ptr].value().depth
            && new_container_perms[c_ptr].value().uppertree_seq
            =~= old_container_perms[c_ptr].value().uppertree_seq,
     forall|c_ptr: ContainerPtr|
        #![trigger old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr)]
        old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr)
            ==> new_container_perms[c_ptr].value().subtree_set@
            =~= old_container_perms[c_ptr].value().subtree_set@.remove(container_ptr),
     forall|c_ptr: ContainerPtr|
        #![trigger old_container_perms.dom().contains(c_ptr)]

        new_container_perms.dom().contains(c_ptr)
            && old_container_perms[container_ptr].value().uppertree_seq@.contains(c_ptr) == false 
            ==> new_container_perms[c_ptr].value().subtree_set
                =~= old_container_perms[c_ptr].value().subtree_set,
    
    forall|v:ContainerPtr|
        #![auto]
        new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children@.contains(v) ==> 
            old_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.get_node_ref(v) == 
                new_container_perms[old_container_perms[container_ptr].value().parent.unwrap()].value().children.get_node_ref(v),
    ensures
        container_tree_wf(
            root_container,
            new_container_perms,
        ),
{
    remove_container_preserve_tree_inv_1(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_2(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_3(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_4(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_5(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_6(root_container, old_container_perms, new_container_perms,container_ptr,);
    remove_container_preserve_tree_inv_7(root_container, old_container_perms, new_container_perms,container_ptr,);
}

//exec
pub fn container_tree_check_is_ancestor(
    root_container: ContainerPtr,
    container_perms: &Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    a_ptr: ContainerPtr,
    child_ptr: ContainerPtr,
) -> (ret: bool)
    requires
        container_perms_wf(container_perms@),
        container_tree_wf(root_container, container_perms@),
        container_perms@.dom().contains(a_ptr),
        container_perms@.dom().contains(child_ptr),
        container_perms@[a_ptr].value().depth < container_perms@[child_ptr].value().depth,
    ensures
        ret == container_perms@[child_ptr].value().uppertree_seq@.contains(a_ptr),
        ret == container_perms@[a_ptr].value().subtree_set@.contains(child_ptr),
{
    proof {
        seq_push_lemma::<ContainerPtr>();
    }
    assert(container_perms@[child_ptr].value().parent.is_Some());
    let tracked child_perm = container_perms.borrow().tracked_borrow(child_ptr);
    let child: &Container = PPtr::<Container>::from_usize(child_ptr).borrow(Tracked(child_perm));
    let mut current_parent_ptr = child.parent.unwrap();
    let mut depth = child.depth;
    assert(current_parent_ptr == container_perms@[child_ptr].value().uppertree_seq@[depth - 1]);

    if current_parent_ptr == a_ptr {
        return true;
    }
    while depth != 1
        invariant
            1 <= depth <= container_perms@[child_ptr].value().depth,
            container_perms_wf(container_perms@),
            container_tree_wf(root_container, container_perms@),
            container_perms@.dom().contains(a_ptr),
            container_perms@.dom().contains(child_ptr),
            container_perms@[a_ptr].value().depth < container_perms@[child_ptr].value().depth,
            child_ptr != root_container,
            current_parent_ptr == container_perms@[child_ptr].value().uppertree_seq@[depth - 1],
            forall|i: int|
                #![auto]
                depth - 1 <= i < container_perms@[child_ptr].value().depth
                    ==> container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
        ensures
            depth == 1,
            forall|i: int|
                #![auto]
                0 <= i < container_perms@[child_ptr].value().depth
                    ==> container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
        decreases depth,
    {
        assert(container_perms@[child_ptr].value().uppertree_seq@.contains(current_parent_ptr));
        assert(container_perms@.dom().contains(current_parent_ptr));
        assert(container_perms@[child_ptr].value().uppertree_seq@.no_duplicates());
        assert(container_perms@[child_ptr].value().uppertree_seq@.index_of(current_parent_ptr)
            == depth - 1);
        assert(container_perms@[current_parent_ptr].value().depth == depth - 1);
        assert(container_perms@[current_parent_ptr].value().parent.is_Some());
        let tracked current_parent_perm = container_perms.borrow().tracked_borrow(
            current_parent_ptr,
        );
        assert(current_parent_perm.addr() == current_parent_ptr);
        let current_parent: &Container = PPtr::<Container>::from_usize(current_parent_ptr).borrow(
            Tracked(current_parent_perm),
        );
        let current_parent_ptr_tmp = current_parent.parent.unwrap();
        if current_parent_ptr_tmp == a_ptr {
            assert(container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1]
                == current_parent_ptr_tmp);
            return true;
        }
        assert(container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1]
            == current_parent_ptr_tmp);
        current_parent_ptr = current_parent_ptr_tmp;
        depth = depth - 1;
    }
    false
}

} // verus!
