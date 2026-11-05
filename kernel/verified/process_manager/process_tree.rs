use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::array_set::*;
use crate::process_manager::process::Process;
use crate::pptr::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::process_manager::proc_util_t::*;

// use crate::process_manager::spec_proof::ProcessManager;
pub open spec fn proc_perms_wf(proc_perms: Map<ProcPtr, PointsTo<Process>>) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].is_init()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].is_init()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].addr()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].addr() == p_ptr
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children.wf()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children.wf()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children.unique()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children.unique()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.no_duplicates()]

        proc_perms.dom().contains(p_ptr)
            ==> proc_perms[p_ptr].value().uppertree_seq@.no_duplicates()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().children@.contains(p_ptr)]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().children@.contains(p_ptr)
            == false
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().subtree_set@.finite()]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().subtree_set@.finite()
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_perms.dom().contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.len(), proc_perms[p_ptr].value().depth]

        proc_perms.dom().contains(p_ptr) ==> proc_perms[p_ptr].value().uppertree_seq@.len()
            == proc_perms[p_ptr].value().depth
}

pub open spec fn proc_tree_dom_subset_of_proc_dom(
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger proc_perms.dom().contains(p_ptr)]

        proc_tree_dom.contains(p_ptr) ==> proc_perms.dom().contains(p_ptr)
}

pub closed spec fn proc_root_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& proc_tree_dom.contains(root_proc)
    &&& proc_perms[root_proc].value().depth == 0
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc ==> proc_perms[p_ptr].value().depth != 0
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent.is_Some()
}

pub closed spec fn proc_childern_parent_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, child_p_ptr: ProcPtr|
        #![trigger proc_perms[p_ptr].value().children@.contains(child_p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().children@.contains(child_p_ptr)
            ==> proc_tree_dom.contains(child_p_ptr)
            && proc_perms[child_p_ptr].value().parent.unwrap() == p_ptr
            && proc_perms[child_p_ptr].value().depth == proc_perms[p_ptr].value().depth + 1
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().parent.is_Some()
            ==> proc_tree_dom.contains(proc_perms[p_ptr].value().parent.unwrap())
            && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children@.contains(
            p_ptr,
        )
}

pub closed spec fn procs_linkedlist_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(proc_perms[p_ptr].value().parent.unwrap())]
    // #![trigger proc_tree_dom.contains(p_ptr)]

        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent.is_Some() && proc_tree_dom.contains(
            proc_perms[p_ptr].value().parent.unwrap(),
        )
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().parent_rev_ptr.is_Some()
            && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children@.contains(
            p_ptr,
        ) && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children.get_node_ref(p_ptr) 
        == 
        proc_perms[p_ptr].value().parent_rev_ptr.unwrap()
}

pub closed spec fn proc_childern_depth_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth - 1]]

        proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> proc_perms[p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth - 1]
            == proc_perms[p_ptr].value().parent.unwrap()
}

pub closed spec fn proc_subtree_set_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, sub_p_ptr: ProcPtr|
     // //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@.len(), proc_perms[p_ptr].value().depth]
    // //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]]
    // //#![trigger proc_tree_dom.contains(p_ptr), proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_tree_dom.contains(sub_p_ptr)]
    //#![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)]
    //#![trigger proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]]

        #![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)
            ==> proc_tree_dom.contains(sub_p_ptr)
            && proc_perms[sub_p_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth
            && proc_perms[sub_p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
            == p_ptr
}

pub closed spec fn proc_uppertree_seq_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, u_ptr: ProcPtr|
     //#![trigger proc_tree_dom.contains(p_ptr), proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr), proc_tree_dom.contains(u_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.subrange(0, proc_perms[u_ptr].value().depth as int)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.index_of(u_ptr)]
    //#![trigger proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)]

        #![trigger proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().uppertree_seq@.contains(u_ptr)
            ==> proc_tree_dom.contains(u_ptr)
            && proc_perms[p_ptr].value().uppertree_seq@[proc_perms[u_ptr].value().depth as int]
            == u_ptr && proc_perms[u_ptr].value().depth
            == proc_perms[p_ptr].value().uppertree_seq@.index_of(u_ptr)
            && proc_perms[u_ptr].value().subtree_set@.contains(p_ptr)
            && proc_perms[u_ptr].value().uppertree_seq@
            =~= proc_perms[p_ptr].value().uppertree_seq@.subrange(
            0,
            proc_perms[u_ptr].value().depth as int,
        )
}

pub closed spec fn proc_subtree_set_exclusive(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    &&& forall|p_ptr: ProcPtr, sub_p_ptr: ProcPtr|
        #![trigger proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr), proc_perms[sub_p_ptr].value().uppertree_seq@.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && proc_tree_dom.contains(sub_p_ptr) ==> (
        proc_perms[p_ptr].value().subtree_set@.contains(sub_p_ptr)
            == proc_perms[sub_p_ptr].value().uppertree_seq@.contains(p_ptr))
}

pub open spec fn proc_tree_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
) -> bool {
    // &&&
    // proc_perms_wf(proc_perms)
    &&& proc_root_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_childern_parent_wf(root_proc, proc_tree_dom, proc_perms)
    &&& procs_linkedlist_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_childern_depth_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_subtree_set_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_uppertree_seq_wf(root_proc, proc_tree_dom, proc_perms)
    &&& proc_subtree_set_exclusive(root_proc, proc_tree_dom, proc_perms)
}

/// `upper` lists existing processes from the root down, each the parent of the next.
pub closed spec fn proc_ancestors_wf(
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    upper: Seq<ProcPtr>,
) -> bool {
    &&& upper.no_duplicates()
    &&& forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() ==> proc_perms.dom().contains(upper[i])
            && proc_perms[upper[i]].is_init() && proc_perms[upper[i]].addr() == upper[i]
    &&& forall|i: int|
        #![trigger upper[i]]
        0 < i < upper.len() ==> proc_perms[upper[i]].value().parent == Some(upper[i - 1])
}

/// What one step of a parent walk reads of a well-formed ancestor list at position `i`.
pub proof fn proc_ancestors_wf_at(
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    upper: Seq<ProcPtr>,
    i: int,
)
    requires
        proc_ancestors_wf(proc_perms, upper),
        0 <= i < upper.len(),
    ensures
        proc_perms.dom().contains(upper[i]),
        proc_perms[upper[i]].is_init(),
        proc_perms[upper[i]].addr() == upper[i],
        i > 0 ==> proc_perms[upper[i]].value().parent == Some(upper[i - 1]),
        upper.contains(upper[i]),
        forall|j: int| #![trigger upper[j]] 0 <= j < upper.len() && j != i ==> upper[j] != upper[i],
{
}

/// A process's uppertree_seq walks its parent links, ends at its parent, and does not include the process.
pub proof fn proc_ancestors_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(p_ptr),
    ensures
        proc_ancestors_wf(proc_perms, proc_perms[p_ptr].value().uppertree_seq@),
        proc_perms[p_ptr].value().uppertree_seq@.contains(p_ptr) == false,
        proc_perms[p_ptr].value().depth > 0 ==> proc_perms[p_ptr].value().parent
            == Some(proc_perms[p_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth - 1]),
{
    assert(proc_tree_dom.contains(p_ptr));
    let upper = proc_perms[p_ptr].value().uppertree_seq@;
    assert(upper.no_duplicates());
    assert forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() implies {
        let u = upper[i];
        &&& proc_tree_dom.contains(u)
        &&& proc_perms[u].value().depth == i
        &&& proc_perms[u].value().uppertree_seq@ =~= upper.subrange(0, i)
    } by {
        let u = upper[i];
        assert(upper.contains(u));
        assert(proc_tree_dom.contains(u));
        let k = upper.index_of(u);
        assert(0 <= k < upper.len() && upper[k] == u);
        assert(k == i) by {
            if k != i {
                assert(upper[k] != upper[i]);
            }
        };
        assert(proc_perms[u].value().depth == k);
    };
    assert forall|i: int|
        #![trigger upper[i]]
        0 <= i < upper.len() implies proc_perms.dom().contains(upper[i])
        && proc_perms[upper[i]].is_init() && proc_perms[upper[i]].addr() == upper[i] by {
        assert(proc_tree_dom.contains(upper[i]));
    };
    assert forall|i: int|
        #![trigger upper[i]]
        0 < i < upper.len() implies proc_perms[upper[i]].value().parent == Some(upper[i - 1]) by {
        let u = upper[i];
        assert(proc_tree_dom.contains(u));
        assert(proc_perms[u].value().depth == i);
        assert(u != root_proc);
        assert(proc_perms[u].value().parent.is_Some());
        assert(proc_perms[u].value().uppertree_seq@[i - 1] == upper[i - 1]);
        assert(proc_perms[u].value().uppertree_seq@[i - 1] == proc_perms[u].value().parent.unwrap());
    };
    if upper.contains(p_ptr) {
        assert(upper.index_of(p_ptr) == proc_perms[p_ptr].value().depth);
        assert(upper.len() == proc_perms[p_ptr].value().depth);
        assert(false);
    }
    if proc_perms[p_ptr].value().depth > 0 {
        assert(p_ptr != root_proc);
        assert(proc_perms[p_ptr].value().parent.is_Some());
        assert(upper[proc_perms[p_ptr].value().depth - 1] == proc_perms[p_ptr].value().parent.unwrap());
    }
}

/// The ancestor facts a new child needs, on the permission map as the tracked remove and inserts leave it:
/// the parent's permission replaced by one with the same parent link, the child's permission added.
pub proof fn proc_ancestors_push_perms(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_perms: Map<ProcPtr, PointsTo<Process>>,
    new_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
    p_perm: PointsTo<Process>,
    new_ptr: ProcPtr,
    new_perm: PointsTo<Process>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_perms),
        proc_perms_wf(old_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_perms),
        proc_tree_dom.contains(p_ptr),
        old_perms.dom().contains(new_ptr) == false,
        new_perms == old_perms.remove(p_ptr).insert(p_ptr, p_perm).insert(new_ptr, new_perm),
        p_perm.is_init(),
        p_perm.addr() == p_ptr,
        p_perm.value().parent == old_perms[p_ptr].value().parent,
    ensures
        proc_ancestors_wf(new_perms, old_perms[p_ptr].value().uppertree_seq@.push(p_ptr)),
        old_perms[p_ptr].value().uppertree_seq@.push(p_ptr).contains(new_ptr) == false,
        old_perms[p_ptr].value().uppertree_seq@.push(p_ptr).len() == old_perms[p_ptr].value().depth
            + 1,
        old_perms[p_ptr].value().uppertree_seq@.push(p_ptr)[old_perms[p_ptr].value().depth as int]
            == p_ptr,
        new_perms.dom().contains(new_ptr),
{
    assert(old_perms.dom().contains(p_ptr));
    assert(p_ptr != new_ptr);
    assert forall|q: ProcPtr|
        #![trigger new_perms[q]]
        old_perms.dom().contains(q) && q != p_ptr implies new_perms.dom().contains(q)
        && new_perms[q] == old_perms[q] by {
        assert(q != new_ptr);
    };
    assert(new_perms.dom().contains(p_ptr));
    assert(new_perms[p_ptr] == p_perm);
    proc_ancestors_inv(root_proc, proc_tree_dom, old_perms, p_ptr);
    let old_upper = old_perms[p_ptr].value().uppertree_seq@;
    let new_upper = old_upper.push(p_ptr);
    assert(old_upper.len() == old_perms[p_ptr].value().depth);
    assert(old_upper.contains(p_ptr) == false);
    assert(old_upper.contains(new_ptr) == false) by {
        if old_upper.contains(new_ptr) {
            assert(old_perms.dom().contains(new_ptr));
        }
    };
    assert(p_ptr != new_ptr);
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
            assert(new_upper[i] == p_ptr);
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
            assert(new_upper[i] == p_ptr);
            assert(new_upper[i - 1] == old_upper[i - 1]);
            assert(old_perms[p_ptr].value().depth > 0);
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

//proof
pub proof fn proc_subtree_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        forall|p_ptr: ProcPtr|
            #![trigger proc_tree_dom.contains(p_ptr)]
        //#![trigger proc_perms[p_ptr].value()]

            proc_tree_dom.contains(p_ptr) ==> proc_perms[p_ptr].value().subtree_set@.subset_of(
                proc_tree_dom,
            ) && proc_perms[p_ptr].value().subtree_set@.contains(p_ptr) == false,
{
}

pub proof fn proc_tree_wf_imply_root_depth(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        proc_perms[root_proc].value().depth == 0,
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().depth == 0
            ==> 
            p_ptr == root_proc,
{

}

pub proof fn same_or_deeper_depth_imply_none_ancestor(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    a_ptr: ProcPtr,
    child_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(a_ptr),
        proc_tree_dom.contains(child_ptr),
        proc_perms[a_ptr].value().depth >= proc_perms[child_ptr].value().depth,
    ensures
        proc_perms[a_ptr].value().subtree_set@.contains(child_ptr) == false,
{
    assert(proc_perms[a_ptr].value().uppertree_seq@.len() == proc_perms[a_ptr].value().depth);
    assert(proc_perms[child_ptr].value().uppertree_seq@.len()
        == proc_perms[child_ptr].value().depth);
}

pub proof fn no_child_imply_no_subtree(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(p_ptr),
        proc_perms[p_ptr].value().children@ =~= Seq::empty(),
    ensures
        proc_perms[p_ptr].value().subtree_set@ =~= Set::empty(),
{
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.contains(p_ptr));
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
            0,
            proc_perms[p_ptr].value().depth as int,
        ) == proc_perms[p_ptr].value().uppertree_seq@);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr) ==> s_ptr != root_proc);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[p_ptr].value().children@.contains(s_ptr) == false);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().parent.unwrap() != p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[s_ptr].value().depth - 1]
            != p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
            == p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.len() != proc_perms[p_ptr].value().depth
            + 1);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.contains(
            proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr) ==> proc_tree_dom.contains(s_ptr));
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr) ==> proc_tree_dom.contains(
            proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.contains(
            proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
        ));
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
            0,
            proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
                + 1]].value().depth as int,
        ) =~= proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().uppertree_seq@);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.no_duplicates());
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[s_ptr].value().uppertree_seq@.index_of(
            proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
        ) == proc_perms[p_ptr].value().depth + 1);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().depth == proc_perms[p_ptr].value().depth + 1);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int] == p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().uppertree_seq@[proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().depth - 1] == p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().parent.unwrap() == p_ptr);
    assert(forall|s_ptr: ProcPtr|
        #![auto]
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr)
            ==> proc_perms[p_ptr].value().children@.contains(
            proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
        ));
}

pub proof fn in_child_impy_in_subtree(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
    child_ptr: ProcPtr,
    s_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(p_ptr),
        proc_perms[p_ptr].value().children@.contains(child_ptr),
        proc_perms[child_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr),
{
    assert(proc_perms[child_ptr].value().parent.unwrap() == p_ptr);
    assert(proc_perms[child_ptr].value().depth == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[child_ptr].value().uppertree_seq@.len()
        == proc_perms[child_ptr].value().depth);
    assert(proc_perms[p_ptr].value().uppertree_seq@.len() == proc_perms[p_ptr].value().depth);
    assert(proc_perms[child_ptr].value().uppertree_seq@[proc_perms[child_ptr].value().depth - 1]
        == p_ptr);
    assert(proc_perms[s_ptr].value().uppertree_seq@.contains(child_ptr));
    assert(proc_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        proc_perms[child_ptr].value().depth as int,
    ) == proc_perms[child_ptr].value().uppertree_seq@);
    assert(proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
        == p_ptr);
    assert(proc_perms[s_ptr].value().uppertree_seq@.contains(p_ptr));
}

pub proof fn in_subtree_imply_exist_in_child(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    p_ptr: ProcPtr,
    s_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(p_ptr),
        proc_perms[p_ptr].value().subtree_set@.contains(s_ptr),
    ensures
        proc_perms[p_ptr].value().children@.contains(s_ptr) || (exists|child_ptr: ProcPtr|
            #![auto]
            proc_perms[p_ptr].value().children@.contains(child_ptr)
                && proc_perms[child_ptr].value().subtree_set@.contains(s_ptr)),
{
    assert(proc_perms[s_ptr].value().uppertree_seq@.contains(p_ptr));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        proc_perms[p_ptr].value().depth as int,
    ) == proc_perms[p_ptr].value().uppertree_seq@);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> s_ptr != root_proc);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().parent.unwrap() != p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[s_ptr].value().depth - 1] != p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int]
        == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() != proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.len() > proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> proc_tree_dom.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.subrange(
        0,
        proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
            + 1]].value().depth as int,
    ) =~= proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.no_duplicates());
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[s_ptr].value().uppertree_seq@.index_of(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ) == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().depth == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@.len() == proc_perms[p_ptr].value().depth + 1);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@[proc_perms[p_ptr].value().depth as int] == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().uppertree_seq@[proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().depth - 1] == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().parent.unwrap() == p_ptr);
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[p_ptr].value().children@.contains(
        proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth + 1],
    ));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false
        ==> proc_perms[proc_perms[s_ptr].value().uppertree_seq@[proc_perms[p_ptr].value().depth
        + 1]].value().subtree_set@.contains(s_ptr));
    assert(proc_perms[p_ptr].value().children@.contains(s_ptr) == false ==> (exists|
        child_ptr: ProcPtr,
    |
        #![auto]
        proc_perms[p_ptr].value().children@.contains(child_ptr)
            && proc_perms[child_ptr].value().subtree_set@.contains(s_ptr)));
}

pub proof fn not_in_dom_imply_not_in_any_children_set(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    s_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(s_ptr) == false,
{
    assert(forall|p_ptr: ProcPtr|
        #![auto]
        proc_tree_dom.contains(p_ptr) ==> proc_perms[p_ptr].value().children@.contains(s_ptr)
            == false);
}

pub proof fn proc_tree_wf_imply_uppertree_subset_of_tree(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        forall|p_ptr: ProcPtr, parent_p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().uppertree_seq@.contains(
                parent_p_ptr,
            ) ==> proc_tree_dom.contains(parent_p_ptr),
{
}

pub proof fn proc_tree_wf_imply_childern_uppertree_specs(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        forall|p_ptr: ProcPtr, child_p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().children@.contains(
                child_p_ptr,
            ) ==> proc_perms.dom().contains(child_p_ptr),
        forall|p_ptr: ProcPtr, parent_p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().uppertree_seq@.contains(
                parent_p_ptr,
            ) ==> proc_perms.dom().contains(parent_p_ptr),
        forall|p_ptr: ProcPtr|
            #![trigger proc_perms[p_ptr].value().uppertree_seq@.contains(p_ptr)]
            proc_tree_dom.contains(p_ptr) ==> proc_perms[p_ptr].value().uppertree_seq@.contains(
                p_ptr,
            ) == false,
{
    // assert(
    //     forall|p_ptr:ProcPtr, child_p_ptr:ProcPtr|
    //     #![auto]
    //     proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().children@.contains(child_p_ptr)
    //     ==>
    //     proc_tree_dom.contains(child_p_ptr)
    // );
}

pub proof fn proc_tree_wf_imply_uppertree_contains_no_self(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_tree_dom.contains(proc_ptr),
    ensures
         proc_perms[proc_ptr].value().uppertree_seq@.contains(proc_ptr) == false,
{
}

pub proof fn proc_tree_wf_imply_root_with_no_child_has_empty_dom(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        proc_perms[root_proc].value().children@ == Seq::<ProcPtr>::empty(),
    ensures
        proc_tree_dom =~= set!(root_proc),
{
    no_child_imply_no_subtree(            
        root_proc,
        proc_tree_dom,
        proc_perms,
        root_proc,
    );
    proc_tree_wf_imply_root_is_in_upper_tree(
        root_proc,
        proc_tree_dom,
        proc_perms, 
    );
    assert(
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> 
            proc_perms[p_ptr].value().uppertree_seq@[0] == root_proc
    );    
    assert(
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> 
            proc_perms[p_ptr].value().uppertree_seq@.contains(root_proc)
    );
    assert(
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && p_ptr != root_proc
            ==> 
            proc_perms[root_proc].value().subtree_set@.contains(p_ptr)
    );
    assert(
         forall|p_ptr: ProcPtr|
            #![auto]
            p_ptr != root_proc
            ==> 
            proc_tree_dom.contains(p_ptr) == false
    );
}

pub proof fn proc_tree_wf_imply_root_is_in_upper_tree(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
        
    ensures
         forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().depth != 0
            ==> 
            proc_perms[p_ptr].value().uppertree_seq@[0] == root_proc,
{
    assert(
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().depth != 0
            ==> 
            proc_perms[p_ptr].value().uppertree_seq@.contains(proc_perms[p_ptr].value().uppertree_seq@[0])
    );
}

pub proof fn proc_tree_wf_imply_childern_has_parent(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
         forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) && proc_perms[p_ptr].value().depth != 0
             ==> proc_perms[p_ptr].value().parent.is_Some()
             && proc_tree_dom.contains(proc_perms[p_ptr].value().parent.unwrap())
             && proc_perms[p_ptr].value().parent_rev_ptr.is_Some()
             && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children@.contains(p_ptr)
             && proc_perms[proc_perms[p_ptr].value().parent.unwrap()].value().children.get_node_ref(p_ptr)
                == proc_perms[p_ptr].value().parent_rev_ptr.unwrap()
{

}

pub proof fn proc_tree_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        forall|p_ptr: ProcPtr|
            #![auto]
            proc_tree_dom.contains(p_ptr) ==> proc_perms[p_ptr].value().children.wf(),
{
}

pub proof fn proc_subtree_disjoint_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, proc_perms),
        proc_perms_wf(proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, proc_perms),
    ensures
        forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
            #![trigger  proc_perms[p_ptr_i].value(), proc_perms[p_ptr_j].value()]
            #![trigger  proc_perms[p_ptr_i].value().subtree_set@.insert(p_ptr_i), proc_perms[p_ptr_j].value().subtree_set@.insert(p_ptr_j)]
            proc_tree_dom.contains(p_ptr_i) && proc_tree_dom.contains(p_ptr_j) && p_ptr_i != p_ptr_j
                && proc_perms[p_ptr_i].value().depth == proc_perms[p_ptr_j].value().depth
                ==> proc_perms[p_ptr_i].value().subtree_set@.disjoint(
                proc_perms[p_ptr_j].value().subtree_set@,
            ) && proc_perms[p_ptr_i].value().subtree_set@.contains(p_ptr_j) == false
                && proc_perms[p_ptr_j].value().subtree_set@.contains(p_ptr_i) == false
                && proc_perms[p_ptr_i].value().subtree_set@.insert(p_ptr_i).disjoint(
                proc_perms[p_ptr_j].value().subtree_set@.insert(p_ptr_j),
            ),
{
    assert(forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
        #![trigger  proc_perms[p_ptr_i].value().subtree_set, proc_perms[p_ptr_j].value().subtree_set]
        proc_tree_dom.contains(p_ptr_i) && proc_tree_dom.contains(p_ptr_j) && p_ptr_i != p_ptr_j
            && proc_perms[p_ptr_i].value().depth == proc_perms[p_ptr_j].value().depth ==> p_ptr_i
            != root_proc && p_ptr_j != root_proc && proc_perms[p_ptr_i].value().depth != 0
            && proc_perms[p_ptr_j].value().depth != 0);

    assert(forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr, sub_p_ptr_i: ProcPtr, sub_p_ptr_j: ProcPtr|
        #![trigger  proc_perms[p_ptr_i].value().subtree_set@.contains(sub_p_ptr_i), proc_perms[p_ptr_j].value().subtree_set@.contains(sub_p_ptr_j)]
        proc_tree_dom.contains(p_ptr_i) && proc_tree_dom.contains(p_ptr_j) && p_ptr_i != p_ptr_j
            && proc_perms[p_ptr_i].value().depth == proc_perms[p_ptr_j].value().depth
            && proc_perms[p_ptr_i].value().subtree_set@.contains(sub_p_ptr_i)
            && proc_perms[p_ptr_j].value().subtree_set@.contains(sub_p_ptr_j)
            ==> proc_perms[sub_p_ptr_i].value().uppertree_seq@[proc_perms[p_ptr_i].value().depth as int]
            == p_ptr_i
            && proc_perms[sub_p_ptr_j].value().uppertree_seq@[proc_perms[p_ptr_j].value().depth as int]
            == p_ptr_j);
}

pub proof fn process_no_change_to_trees_fields_imply_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms),
        proc_perms_wf(new_proc_perms),
        old_proc_perms.dom() =~= new_proc_perms.dom(),
        forall|p_ptr: ProcPtr|
        //#![trigger old_proc_perms[p_ptr]]
        //#![trigger new_proc_perms[p_ptr]]

            #![trigger old_proc_perms.dom().contains(p_ptr)]
            old_proc_perms.dom().contains(p_ptr) ==> new_proc_perms[p_ptr].is_init()
                && old_proc_perms[p_ptr].value().parent =~= new_proc_perms[p_ptr].value().parent
                && old_proc_perms[p_ptr].value().parent_rev_ptr
                =~= new_proc_perms[p_ptr].value().parent_rev_ptr
                && old_proc_perms[p_ptr].value().children =~= new_proc_perms[p_ptr].value().children
                && old_proc_perms[p_ptr].value().depth =~= new_proc_perms[p_ptr].value().depth
                && old_proc_perms[p_ptr].value().uppertree_seq
                =~= new_proc_perms[p_ptr].value().uppertree_seq
                && old_proc_perms[p_ptr].value().subtree_set
                =~= new_proc_perms[p_ptr].value().subtree_set,
    ensures
        proc_tree_wf(root_proc, proc_tree_dom, new_proc_perms),
{
}

pub proof fn process_no_change_to_tree_fields_imply_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms),
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, new_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms),
        proc_perms_wf(new_proc_perms),
        // old_proc_perms.dom() =~= new_proc_perms.dom(),
        forall|p_ptr: ProcPtr|
        //#![trigger old_proc_perms[p_ptr]]
        //#![trigger new_proc_perms[p_ptr]]

            #![trigger proc_tree_dom.contains(p_ptr)]
            proc_tree_dom.contains(p_ptr) ==> new_proc_perms[p_ptr].is_init()
                && old_proc_perms[p_ptr].value().parent =~= new_proc_perms[p_ptr].value().parent
                && old_proc_perms[p_ptr].value().parent_rev_ptr
                =~= new_proc_perms[p_ptr].value().parent_rev_ptr
                && old_proc_perms[p_ptr].value().children =~= new_proc_perms[p_ptr].value().children
                && old_proc_perms[p_ptr].value().depth =~= new_proc_perms[p_ptr].value().depth
                && old_proc_perms[p_ptr].value().uppertree_seq
                =~= new_proc_perms[p_ptr].value().uppertree_seq
                && old_proc_perms[p_ptr].value().subtree_set
                =~= new_proc_perms[p_ptr].value().subtree_set,
    ensures
        proc_tree_wf(root_proc, proc_tree_dom, new_proc_perms),
{
}

pub open spec fn new_proc_tree_ensures(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_ptr: ProcPtr,
) -> bool {
    &&& root_proc == new_proc_ptr
    &&& proc_perms_wf(new_proc_perms)
    &&& proc_tree_dom == set![new_proc_ptr]
    &&& proc_tree_dom_subset_of_proc_dom(proc_tree_dom, new_proc_perms)
    &&& new_proc_perms[new_proc_ptr].value().parent.is_None()
    &&& new_proc_perms[new_proc_ptr].value().parent_rev_ptr.is_None()
    &&& new_proc_perms[new_proc_ptr].value().children@ =~= Seq::empty()
    &&& new_proc_perms[new_proc_ptr].value().uppertree_seq@ =~= Seq::empty()
    &&& new_proc_perms[new_proc_ptr].value().depth == 0
    &&& new_proc_perms[new_proc_ptr].value().subtree_set@ =~= Set::<ProcPtr>::empty()
    &&& new_proc_perms[new_proc_ptr].value().children.unique()
}

pub proof fn new_proc_tree_infer_wf(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_ptr: ProcPtr,
)
    requires
// new_proc_tree_ensures(root_proc, proc_tree_dom, new_proc_perms, new_proc_ptr),

        root_proc == new_proc_ptr,
        proc_perms_wf(new_proc_perms),
        proc_tree_dom == set![new_proc_ptr],
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, new_proc_perms),
        new_proc_perms[new_proc_ptr].value().parent.is_None(),
        new_proc_perms[new_proc_ptr].value().parent_rev_ptr.is_None(),
        new_proc_perms[new_proc_ptr].value().children@ =~= Seq::empty(),
        new_proc_perms[new_proc_ptr].value().uppertree_seq@ =~= Seq::empty(),
        new_proc_perms[new_proc_ptr].value().depth == 0,
        new_proc_perms[new_proc_ptr].value().subtree_set@ =~= Set::<ProcPtr>::empty(),
        new_proc_perms[new_proc_ptr].value().children.unique(),
    ensures
        proc_root_wf(root_proc, proc_tree_dom, new_proc_perms),
        proc_childern_parent_wf(root_proc, proc_tree_dom, new_proc_perms),
        procs_linkedlist_wf(root_proc, proc_tree_dom, new_proc_perms),
        proc_childern_depth_wf(root_proc, proc_tree_dom, new_proc_perms),
        proc_subtree_set_wf(root_proc, proc_tree_dom, new_proc_perms),
        proc_uppertree_seq_wf(root_proc, proc_tree_dom, new_proc_perms),
        proc_subtree_set_exclusive(root_proc, proc_tree_dom, new_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, new_proc_perms),
{
}

pub open spec fn new_proc_ensures(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
) -> bool {
    &&& proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms)
    &&& proc_perms_wf(old_proc_perms)
    &&& proc_perms_wf(new_proc_perms)
    &&& proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms)
    &&& proc_tree_dom.contains(proc_ptr)
    &&& proc_tree_dom.contains(new_proc_ptr) == false
    &&& old_proc_perms[proc_ptr].value().children.len() < PROC_CHILD_LIST_LEN
    &&& old_proc_perms[proc_ptr].value().depth < usize::MAX
    &&& new_proc_perms.dom() == old_proc_perms.dom().insert(new_proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().parent =~= Some(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().parent_rev_ptr.is_Some()
    &&& new_proc_perms[new_proc_ptr].value().children@ =~= Seq::empty()
    &&& new_proc_perms[new_proc_ptr].value().uppertree_seq@
        =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().depth as int =~= old_proc_perms[proc_ptr].value().depth
        + 1
    &&& new_proc_perms[new_proc_ptr].value().uppertree_seq@
        =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr)
    &&& new_proc_perms[new_proc_ptr].value().subtree_set@ =~= Set::<ProcPtr>::empty()
    &&& forall|p_ptr: ProcPtr|
     //#![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger new_proc_perms[p_ptr].is_init()]
    //#![trigger new_proc_perms[p_ptr].addr()]
    //#![trigger new_proc_perms[p_ptr].value().parent]
    //#![trigger new_proc_perms[p_ptr].value().parent_rev_ptr]
    //#![trigger new_proc_perms[p_ptr].value().children]
    //#![trigger new_proc_perms[p_ptr].value().depth]
    //#![trigger new_proc_perms[p_ptr].value().uppertree_seq]

        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != proc_ptr ==> new_proc_perms[p_ptr].value().parent
            =~= old_proc_perms[p_ptr].value().parent && new_proc_perms[p_ptr].value().parent_rev_ptr
            =~= old_proc_perms[p_ptr].value().parent_rev_ptr
            && new_proc_perms[p_ptr].value().children =~= old_proc_perms[p_ptr].value().children
            && new_proc_perms[p_ptr].value().depth =~= old_proc_perms[p_ptr].value().depth
            && new_proc_perms[p_ptr].value().uppertree_seq
            =~= old_proc_perms[p_ptr].value().uppertree_seq
    &&& forall|p_ptr: ProcPtr|
     //#![trigger new_proc_perms.dom().contains(p_ptr)]
    //#![trigger new_proc_perms[p_ptr].value().subtree_set]

        #![trigger new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)]
        new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)
            ==> new_proc_perms[p_ptr].value().subtree_set@
            =~= old_proc_perms[p_ptr].value().subtree_set@.insert(new_proc_ptr)
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
    //#![trigger old_proc_perms[p_ptr].value().subtree_set]
    //#![trigger new_proc_perms[p_ptr].value().subtree_set]

        proc_tree_dom.contains(p_ptr)
            && new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr) == false
            ==> new_proc_perms[p_ptr].value().subtree_set
            =~= old_proc_perms[p_ptr].value().subtree_set
    &&& new_proc_perms[proc_ptr].value().parent =~= old_proc_perms[proc_ptr].value().parent
    &&& new_proc_perms[proc_ptr].value().parent_rev_ptr
        =~= old_proc_perms[proc_ptr].value().parent_rev_ptr
    &&& new_proc_perms[proc_ptr].value().children@
        =~= old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr)
    &&& new_proc_perms[proc_ptr].value().depth =~= old_proc_perms[proc_ptr].value().depth
    &&& new_proc_perms[proc_ptr].value().uppertree_seq
        =~= old_proc_perms[proc_ptr].value().uppertree_seq
    &&& new_proc_perms[proc_ptr].value().children.wf()
    &&& new_proc_perms[proc_ptr].value().children@
        == old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr)
    &&& new_proc_perms[proc_ptr].value().children.len()
        == old_proc_perms[proc_ptr].value().children.len() + 1
    &&&
    forall|v:ProcPtr|
    #![auto]
    old_proc_perms[proc_ptr].value().children@.contains(v) ==> 
        old_proc_perms[proc_ptr].value().children.get_node_ref(v) == 
            new_proc_perms[proc_ptr].value().children.get_node_ref(v)
    &&& new_proc_perms[proc_ptr].value().children.get_node_ref(new_proc_ptr) ==
        new_proc_perms[new_proc_ptr].value().parent_rev_ptr.unwrap()
    &&& new_proc_perms[proc_ptr].value().children.unique()
}

pub proof fn new_proc_preserve_tree_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
// new_proc_ensures(root_proc, proc_tree_dom, old_proc_perms, new_proc_perms, proc_ptr, new_proc_ptr),

        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms),
        proc_perms_wf(old_proc_perms),
        proc_perms_wf(new_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms),
        proc_tree_dom.contains(proc_ptr),
        proc_tree_dom.contains(new_proc_ptr) == false,
        old_proc_perms[proc_ptr].value().children.len() < PROC_CHILD_LIST_LEN,
        old_proc_perms[proc_ptr].value().depth < usize::MAX,
        new_proc_perms.dom() == old_proc_perms.dom().insert(new_proc_ptr),
        new_proc_perms[new_proc_ptr].value().parent =~= Some(proc_ptr),
        new_proc_perms[new_proc_ptr].value().parent_rev_ptr.is_Some(),
        new_proc_perms[new_proc_ptr].value().children@ =~= Seq::empty(),
        new_proc_perms[new_proc_ptr].value().uppertree_seq@
            =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr),
        new_proc_perms[new_proc_ptr].value().depth as int =~= old_proc_perms[proc_ptr].value().depth
            + 1,
        new_proc_perms[new_proc_ptr].value().uppertree_seq@
            =~= old_proc_perms[proc_ptr].value().uppertree_seq@.push(proc_ptr),
        new_proc_perms[new_proc_ptr].value().subtree_set@ =~= Set::<ProcPtr>::empty(),
        forall|p_ptr: ProcPtr|
            #![trigger proc_tree_dom.contains(p_ptr)]
        //#![trigger new_proc_perms[p_ptr].value().parent]
        //#![trigger new_proc_perms[p_ptr].value().parent_rev_ptr]
        //#![trigger new_proc_perms[p_ptr].value().children]
        //#![trigger new_proc_perms[p_ptr].value().depth]
        //#![trigger new_proc_perms[p_ptr].value().uppertree_seq]

            proc_tree_dom.contains(p_ptr) && p_ptr != proc_ptr
                ==> new_proc_perms[p_ptr].value().parent =~= old_proc_perms[p_ptr].value().parent
                && new_proc_perms[p_ptr].value().parent_rev_ptr
                =~= old_proc_perms[p_ptr].value().parent_rev_ptr
                && new_proc_perms[p_ptr].value().children =~= old_proc_perms[p_ptr].value().children
                && new_proc_perms[p_ptr].value().depth =~= old_proc_perms[p_ptr].value().depth
                && new_proc_perms[p_ptr].value().uppertree_seq
                =~= old_proc_perms[p_ptr].value().uppertree_seq,
        forall|p_ptr: ProcPtr|
            #![trigger new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)]
        //#![trigger new_proc_perms[p_ptr].value().subtree_set]
        //#![trigger old_proc_perms[p_ptr].value().subtree_set]

            new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr)
                ==> new_proc_perms[p_ptr].value().subtree_set@
                =~= old_proc_perms[p_ptr].value().subtree_set@.insert(new_proc_ptr),
        forall|p_ptr: ProcPtr|
            #![trigger proc_tree_dom.contains(p_ptr)]
        //#![trigger old_proc_perms[p_ptr].value().subtree_set]
        //#![trigger new_proc_perms[p_ptr].value().subtree_set]

            proc_tree_dom.contains(p_ptr)
                && new_proc_perms[new_proc_ptr].value().uppertree_seq@.contains(p_ptr) == false
                ==> new_proc_perms[p_ptr].value().subtree_set
                =~= old_proc_perms[p_ptr].value().subtree_set,
        new_proc_perms[proc_ptr].value().parent =~= old_proc_perms[proc_ptr].value().parent,
        new_proc_perms[proc_ptr].value().parent_rev_ptr
            =~= old_proc_perms[proc_ptr].value().parent_rev_ptr,
        new_proc_perms[proc_ptr].value().children@
            =~= old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr),
        new_proc_perms[proc_ptr].value().depth =~= old_proc_perms[proc_ptr].value().depth,
        new_proc_perms[proc_ptr].value().uppertree_seq
            =~= old_proc_perms[proc_ptr].value().uppertree_seq,
        new_proc_perms[proc_ptr].value().children.wf(),
        new_proc_perms[proc_ptr].value().children@
            == old_proc_perms[proc_ptr].value().children@.push(new_proc_ptr),
        new_proc_perms[proc_ptr].value().children.len()
            == old_proc_perms[proc_ptr].value().children.len() + 1,
        forall|v:ProcPtr|
            #![auto]
            old_proc_perms[proc_ptr].value().children@.contains(v) ==> 
                old_proc_perms[proc_ptr].value().children.get_node_ref(v) == 
                    new_proc_perms[proc_ptr].value().children.get_node_ref(v),
        new_proc_perms[proc_ptr].value().children.get_node_ref(new_proc_ptr) == 
            new_proc_perms[new_proc_ptr].value().parent_rev_ptr.unwrap(),
        new_proc_perms[proc_ptr].value().children.unique(),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_tree_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
{
    new_proc_preserve_tree_inv_1(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_2(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_3(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_4(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_5(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_6(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
    new_proc_preserve_tree_inv_7(
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
        new_proc_ptr,
    );
}

pub proof fn new_proc_preserve_tree_inv_1(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
        proc_root_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub proof fn new_proc_preserve_tree_inv_2(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_childern_parent_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),  //// procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),FORMATTER_NOT_INLINE_MARKER
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub proof fn new_proc_preserve_tree_inv_3(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_childern_depth_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub proof fn new_proc_preserve_tree_inv_4(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_subtree_set_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub proof fn new_proc_preserve_tree_inv_5(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_uppertree_seq_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
    let new_dom = proc_tree_dom.insert(new_proc_ptr);
    let old_upper = old_proc_perms[proc_ptr].value().uppertree_seq@;
    let new_upper = old_upper.push(proc_ptr);
    let d = old_proc_perms[proc_ptr].value().depth as int;
    assert(old_upper.len() == d);
    assert(old_upper.no_duplicates());
    proc_tree_wf_imply_uppertree_contains_no_self(root_proc, proc_tree_dom, old_proc_perms, proc_ptr);
    assert(old_upper.contains(proc_ptr) == false);
    assert(new_upper.no_duplicates());
    assert(new_upper.index_of(proc_ptr) == d);
    assert(new_upper[d] == proc_ptr);
    assert(old_upper =~= new_upper.subrange(0, d));
    assert(new_proc_perms[new_proc_ptr].value().uppertree_seq@ =~= new_upper);
    assert(new_proc_perms[new_proc_ptr].value().depth == d + 1);
    assert(new_proc_perms[proc_ptr].value().uppertree_seq@ =~= old_upper);
    assert(new_proc_perms[proc_ptr].value().depth == d);
    assert(proc_tree_dom.contains(new_proc_ptr) == false);

    assert forall|p: ProcPtr, u: ProcPtr|
        #![trigger new_proc_perms[p].value().uppertree_seq@.contains(u)]
        new_dom.contains(p) && new_proc_perms[p].value().uppertree_seq@.contains(u)
        implies new_dom.contains(u)
        && new_proc_perms[p].value().uppertree_seq@[new_proc_perms[u].value().depth as int] == u
        && new_proc_perms[u].value().depth == new_proc_perms[p].value().uppertree_seq@.index_of(u)
        && new_proc_perms[u].value().subtree_set@.contains(p)
        && new_proc_perms[u].value().uppertree_seq@ =~= new_proc_perms[p].value().uppertree_seq@.subrange(
            0,
            new_proc_perms[u].value().depth as int,
        ) by {
        if p == new_proc_ptr {
            assert(new_upper.contains(u));
            if u == proc_ptr {
                assert(new_dom.contains(u));
                assert(new_upper[new_proc_perms[u].value().depth as int] == u);
                assert(new_proc_perms[u].value().depth == new_upper.index_of(u));
                assert(new_proc_perms[u].value().subtree_set@ =~= old_proc_perms[u].value().subtree_set@.insert(new_proc_ptr));
                assert(new_proc_perms[u].value().subtree_set@.contains(p));
                assert(new_proc_perms[u].value().uppertree_seq@ =~= new_upper.subrange(0, d));
            } else {
                assert(old_upper.contains(u)) by {
                    let k = choose|k: int| 0 <= k < new_upper.len() && new_upper[k] == u;
                    assert(k < old_upper.len());
                    assert(old_upper[k] == u);
                };
                // the old tree's uppertree fact for (proc_ptr, u)
                assert(proc_tree_dom.contains(u));
                let du = old_proc_perms[u].value().depth as int;
                assert(old_upper[du] == u);
                assert(du == old_upper.index_of(u));
                assert(old_proc_perms[u].value().uppertree_seq@ =~= old_upper.subrange(0, du));
                assert(u != new_proc_ptr);
                assert(new_proc_perms[u].value().depth == du);
                assert(new_proc_perms[u].value().uppertree_seq@ =~= old_proc_perms[u].value().uppertree_seq@);
                assert(new_dom.contains(u));
                assert(0 <= du < old_upper.len());
                assert(new_upper[du] == u);
                assert(new_upper.index_of(u) == old_upper.index_of(u));
                assert(new_proc_perms[u].value().subtree_set@ =~= old_proc_perms[u].value().subtree_set@.insert(new_proc_ptr));
                assert(new_proc_perms[u].value().subtree_set@.contains(p));
                assert(new_upper.subrange(0, du) =~= old_upper.subrange(0, du));
            }
        } else {
            assert(proc_tree_dom.contains(p));
            assert(new_proc_perms[p].value().uppertree_seq@ =~= old_proc_perms[p].value().uppertree_seq@);
            let p_upper = old_proc_perms[p].value().uppertree_seq@;
            assert(p_upper.contains(u));
            // the old tree's uppertree fact for (p, u)
            assert(proc_tree_dom.contains(u));
            let du = old_proc_perms[u].value().depth as int;
            assert(p_upper[du] == u);
            assert(du == p_upper.index_of(u));
            assert(old_proc_perms[u].value().subtree_set@.contains(p));
            assert(old_proc_perms[u].value().uppertree_seq@ =~= p_upper.subrange(0, du));
            assert(u != new_proc_ptr);
            assert(new_proc_perms[u].value().depth == du);
            assert(new_proc_perms[u].value().uppertree_seq@ =~= old_proc_perms[u].value().uppertree_seq@);
            assert(new_dom.contains(u));
            if new_upper.contains(u) {
                assert(new_proc_perms[u].value().subtree_set@ =~= old_proc_perms[u].value().subtree_set@.insert(new_proc_ptr));
            } else {
                assert(new_proc_perms[u].value().subtree_set =~= old_proc_perms[u].value().subtree_set);
            }
            assert(new_proc_perms[u].value().subtree_set@.contains(p));
        }
    };
}

pub proof fn new_proc_preserve_tree_inv_6(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// // procs_linkedlist_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
{
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub proof fn new_proc_preserve_tree_inv_7(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
    new_proc_ptr: ProcPtr,
)
    requires
        new_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
            new_proc_ptr,
        ),
    ensures
// proc_root_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_childern_parent_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

        procs_linkedlist_wf(
            root_proc,
            proc_tree_dom.insert(new_proc_ptr),
            new_proc_perms,
        ),
// proc_childern_depth_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_uppertree_seq_wf(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),
// proc_subtree_set_exclusive(root_proc, proc_tree_dom.insert(new_proc_ptr), new_proc_perms),

{
    // assert(false);
    seq_push_lemma::<ProcPtr>();
    seq_push_unique_lemma::<ProcPtr>();
}

pub open spec fn remove_proc_ensures(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
) -> bool {
    &&& proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms)
    &&& proc_perms_wf(old_proc_perms)
    &&& proc_perms_wf(new_proc_perms)
    &&& proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms)
    &&& proc_tree_dom.contains(proc_ptr)
    &&& old_proc_perms[proc_ptr].value().children@ == Seq::<ProcPtr>::empty()
    &&& old_proc_perms[proc_ptr].value().depth != 0
    &&& new_proc_perms.dom() == old_proc_perms.dom().remove(proc_ptr)
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.contains(p_ptr) && p_ptr != proc_ptr
        ==> new_proc_perms[p_ptr].value().parent
            =~= old_proc_perms[p_ptr].value().parent && new_proc_perms[p_ptr].value().parent_rev_ptr
            =~= old_proc_perms[p_ptr].value().parent_rev_ptr
            && (p_ptr != old_proc_perms[proc_ptr].value().parent.unwrap() ==> new_proc_perms[p_ptr].value().children =~= old_proc_perms[p_ptr].value().children)
            && new_proc_perms[p_ptr].value().depth =~= old_proc_perms[p_ptr].value().depth
            && new_proc_perms[p_ptr].value().uppertree_seq
            =~= old_proc_perms[p_ptr].value().uppertree_seq
    &&& forall|p_ptr: ProcPtr|
        #![trigger old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr)]
        old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr)
            ==> new_proc_perms[p_ptr].value().subtree_set@
            =~= old_proc_perms[p_ptr].value().subtree_set@.remove(proc_ptr)
    &&& forall|p_ptr: ProcPtr|
        #![trigger proc_tree_dom.contains(p_ptr)]
        proc_tree_dom.remove(proc_ptr).contains(p_ptr)
            && old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr) == false
            ==> new_proc_perms[p_ptr].value().subtree_set
            =~= old_proc_perms[p_ptr].value().subtree_set
    &&& new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@ 
        =~= old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@.remove_value(proc_ptr)
    &&&
    forall|v:ProcPtr|
    #![auto]
    new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@.contains(v) ==> 
        old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.get_node_ref(v) == 
            new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.get_node_ref(v)
}

pub proof fn remove_proc_preserve_tree_inv_1(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_root_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
}

pub proof fn remove_proc_preserve_tree_inv_2(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_childern_parent_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
    old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
}

pub proof fn remove_proc_preserve_tree_inv_3(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_childern_depth_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
    old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
}

pub proof fn remove_proc_preserve_tree_inv_4(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_subtree_set_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
}

pub proof fn remove_proc_preserve_tree_inv_5(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_uppertree_seq_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
    old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
    no_child_imply_no_subtree(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        proc_ptr,
    );
}

pub proof fn remove_proc_preserve_tree_inv_6(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        proc_subtree_set_exclusive(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
}

pub proof fn remove_proc_preserve_tree_inv_7(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        remove_proc_ensures(
            root_proc,
            proc_tree_dom,
            old_proc_perms,
            new_proc_perms,
            proc_ptr,
        ),
    ensures
        procs_linkedlist_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        ),
{
    seq_remove_lemma::<ProcPtr>();
    seq_remove_lemma_2::<ProcPtr>();
    old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.unique_implys_no_duplicates();
}

pub proof fn remove_proc_preserve_tree_inv(
    root_proc: ProcPtr,
    proc_tree_dom: Set<ProcPtr>,
    old_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    new_proc_perms: Map<ProcPtr, PointsTo<Process>>,
    proc_ptr: ProcPtr,
)
    requires
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom, old_proc_perms),
        proc_perms_wf(old_proc_perms),
        proc_perms_wf(new_proc_perms),
        proc_tree_wf(root_proc, proc_tree_dom, old_proc_perms),
        proc_tree_dom.contains(proc_ptr),
        old_proc_perms[proc_ptr].value().children@ == Seq::<ProcPtr>::empty(),
        old_proc_perms[proc_ptr].value().depth != 0,
        new_proc_perms.dom() == old_proc_perms.dom().remove(proc_ptr),
        forall|p_ptr: ProcPtr|
            #![trigger proc_tree_dom.contains(p_ptr)]
            proc_tree_dom.contains(p_ptr) && p_ptr != proc_ptr
            ==> new_proc_perms[p_ptr].value().parent
                =~= old_proc_perms[p_ptr].value().parent && new_proc_perms[p_ptr].value().parent_rev_ptr
                =~= old_proc_perms[p_ptr].value().parent_rev_ptr
                && (p_ptr != old_proc_perms[proc_ptr].value().parent.unwrap() ==> new_proc_perms[p_ptr].value().children =~= old_proc_perms[p_ptr].value().children)
                && new_proc_perms[p_ptr].value().depth =~= old_proc_perms[p_ptr].value().depth
                && new_proc_perms[p_ptr].value().uppertree_seq
                =~= old_proc_perms[p_ptr].value().uppertree_seq,
        forall|p_ptr: ProcPtr|
            #![trigger old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr)]
            old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr)
                ==> new_proc_perms[p_ptr].value().subtree_set@
                =~= old_proc_perms[p_ptr].value().subtree_set@.remove(proc_ptr),
        forall|p_ptr: ProcPtr|
            #![trigger proc_tree_dom.contains(p_ptr)]
            proc_tree_dom.remove(proc_ptr).contains(p_ptr)
                && old_proc_perms[proc_ptr].value().uppertree_seq@.contains(p_ptr) == false
                ==> new_proc_perms[p_ptr].value().subtree_set
                =~= old_proc_perms[p_ptr].value().subtree_set,
        new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@ 
            =~= old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@.remove_value(proc_ptr),
        forall|v:ProcPtr|
            #![auto]
            new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children@.contains(v) ==> 
                old_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.get_node_ref(v) == 
                    new_proc_perms[old_proc_perms[proc_ptr].value().parent.unwrap()].value().children.get_node_ref(v),
        // remove_proc_ensures(
        //     root_proc,
        //     proc_tree_dom,
        //     old_proc_perms,
        //     new_proc_perms,
        //     proc_ptr,
        // ),
    ensures
        proc_tree_wf(
            root_proc,
            proc_tree_dom.remove(proc_ptr),
            new_proc_perms,
        )
{
    remove_proc_preserve_tree_inv_1(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_2(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_3(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_4(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_5(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_6(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
    remove_proc_preserve_tree_inv_7(            
        root_proc,
        proc_tree_dom,
        old_proc_perms,
        new_proc_perms,
        proc_ptr,
    );
}

//exec
pub fn proc_tree_check_is_ancestor(
    root_proc: ProcPtr,
    proc_tree_dom: Ghost<Set<ProcPtr>>,
    proc_perms: &Tracked<Map<ProcPtr, PointsTo<Process>>>,
    a_ptr: ProcPtr,
    child_ptr: ProcPtr,
) -> (ret: bool)
    requires
        proc_perms_wf(proc_perms@),
        proc_tree_wf(root_proc, proc_tree_dom@, proc_perms@),
        proc_tree_dom_subset_of_proc_dom(proc_tree_dom@, proc_perms@),
        proc_tree_dom@.contains(a_ptr),
        proc_tree_dom@.contains(child_ptr),
        proc_perms@[a_ptr].value().depth < proc_perms@[child_ptr].value().depth,
        child_ptr != root_proc,
    ensures
        ret == proc_perms@[child_ptr].value().uppertree_seq@.contains(a_ptr),
{
    // assert(false);
    proof {
        seq_push_lemma::<ProcPtr>();
    }
    assert(proc_perms@[child_ptr].value().parent.is_Some());
    let tracked child_perm = proc_perms.borrow().tracked_borrow(child_ptr);
    let child: &Process = PPtr::<Process>::from_usize(child_ptr).borrow(Tracked(child_perm));
    let mut current_parent_ptr = child.parent.unwrap();
    let mut depth = child.depth;
    assert(current_parent_ptr == proc_perms@[child_ptr].value().uppertree_seq@[depth - 1]);

    if current_parent_ptr == a_ptr {
        return true;
    }
    while depth != 1
        invariant
            1 <= depth <= proc_perms@[child_ptr].value().depth,
            proc_perms_wf(proc_perms@),
            proc_tree_wf(root_proc, proc_tree_dom@, proc_perms@),
            proc_tree_dom_subset_of_proc_dom(proc_tree_dom@, proc_perms@),
            proc_tree_dom@.contains(a_ptr),
            proc_tree_dom@.contains(child_ptr),
            proc_perms@[a_ptr].value().depth < proc_perms@[child_ptr].value().depth,
            child_ptr != root_proc,
            current_parent_ptr == proc_perms@[child_ptr].value().uppertree_seq@[depth - 1],
            forall|i: int|
                #![auto]
                depth - 1 <= i < proc_perms@[child_ptr].value().depth
                    ==> proc_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
        ensures
            depth == 1,
            forall|i: int|
                #![auto]
                0 <= i < proc_perms@[child_ptr].value().depth
                    ==> proc_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
        decreases depth,
    {
        assert(proc_perms@[child_ptr].value().uppertree_seq@.contains(current_parent_ptr));
        assert(proc_perms@.dom().contains(current_parent_ptr));
        assert(proc_perms@[child_ptr].value().uppertree_seq@.no_duplicates());
        assert(proc_perms@[child_ptr].value().uppertree_seq@.index_of(current_parent_ptr) == depth
            - 1);
        assert(proc_perms@[current_parent_ptr].value().depth == depth - 1);
        assert(proc_perms@[current_parent_ptr].value().parent.is_Some());
        let tracked current_parent_perm = proc_perms.borrow().tracked_borrow(current_parent_ptr);
        assert(current_parent_perm.addr() == current_parent_ptr);
        let current_parent: &Process = PPtr::<Process>::from_usize(current_parent_ptr).borrow(
            Tracked(current_parent_perm),
        );
        let current_parent_ptr_tmp = current_parent.parent.unwrap();
        if current_parent_ptr_tmp == a_ptr {
            assert(proc_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1]
                == current_parent_ptr_tmp);
            return true;
        }
        assert(proc_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1]
            == current_parent_ptr_tmp);
        current_parent_ptr = current_parent_ptr_tmp;
        depth = depth - 1;
    }
    false
}

} // verus!
