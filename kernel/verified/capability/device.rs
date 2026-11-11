// SPDX-License-Identifier: MIT

//! Devices. A device is boot-sized and never retyped, so the table of them is filled once, at boot, from what
//! the boot glue found, and each device gets one capability under the list's first node. A device is bound to
//! one space at a time, so its capability moves and is never derived: at most one capability names a device.
//! A device's IOid on its IOMMU is its device number, fixed, so nothing allocates one. A device's binding to
//! a device space is a node of the list's first page, live exactly while the device is bound, under the
//! space capability that bound it. See design/sharing-by-derive/, design/capability-names-a-block/,
//! design/address-spaces-as-objects/ and design/device-binding-under-the-space-capability/.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
use crate::define::*;

/// The most devices the table holds: each has a binding node in the list's first page, after its first
/// node.
pub const MAX_DEVICES: usize = NODES_PER_PAGE - 1;

/// How many device numbers an IOMMU has: a DeviceID is 16 bits. AMD IOMMU specification 48882 §2.2.
pub const IOMMU_DEVICES: usize = 0x10000; // not a page size: a count of device numbers

/// The steps of unbinding a device: the one page, its space's root, that its record_run writes.
/// See design/one-lock-bounded-steps/.
pub const UNBIND_DEVICE_STEPS: usize = 1;

/// A device capability carries no right: holding it is the authority.
pub const DEVICE_RIGHTS: u32 = 0;

/// What boot found of one device: the IOMMU it sits behind and its device number there.
#[derive(Clone, Copy)]
pub struct DeviceInfo {
    pub iommu: usize,
    pub number: usize,
}

/// One device. Its IOid on its IOMMU is its device number.
#[derive(Clone, Copy)]
pub struct DeviceRecord {
    pub iommu: usize,
    pub number: usize,
    /// The device space the device is bound to, if any.
    pub space: Option<usize>,
    /// The flush epoch of its last unbind, zero if it has none.
    pub unbound: usize,
}

pub struct Devices {
    pub records: Array<DeviceRecord, MAX_DEVICES>,
    pub count: usize,
    /// The list's first page. Device d's binding node is its node 1 + d.
    pub page: usize,
    /// The node of the capability each device object was given at boot. A device capability is the
    /// one its object's entry names, so at most one names each device.
    pub holder: Ghost<Map<usize, usize>>,
}

/// A device's record before anything binds it.
pub open spec fn unbound_record(info: DeviceInfo) -> DeviceRecord {
    DeviceRecord { iommu: info.iommu, number: info.number, space: None, unbound: 0 }
}

/// A record after its device's unbind at this epoch.
pub open spec fn unbound_at(r: DeviceRecord, epoch: usize) -> DeviceRecord {
    DeviceRecord { iommu: r.iommu, number: r.number, space: None, unbound: epoch }
}

/// A record after its device is bound to the space at s.
pub open spec fn bound_record(r: DeviceRecord, s: usize) -> DeviceRecord {
    DeviceRecord { iommu: r.iommu, number: r.number, space: Some(s), unbound: r.unbound }
}

/// What device d's capability says.
pub open spec fn device_payload(d: int) -> Payload {
    Payload { kind: CapKind::Device, order: 0, rights: DEVICE_RIGHTS, base: device_object(d), badge: 0, reserved: 0 }
}

/// Device d's object names device d.
pub proof fn lemma_device_object(d: int)
    requires
        0 <= d < MAX_DEVICES,
    ensures
        DEVICE_OBJECTS <= device_object(d),
        device_object(d) % PAGE_SZ == 0,
        device_of(device_object(d)) == d,
{
    assert(DEVICE_OBJECTS % PAGE_SZ == 0);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(d, DEVICE_OBJECTS as int, PAGE_SZ as int);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(d, PAGE_SZ as int);
}

/// The device whose object o is.
pub open spec fn device_of(o: usize) -> int {
    (o - DEVICE_OBJECTS) / PAGE_SZ as int
}

/// Device d's binding node, node 1 + d of the list's first page.
pub open spec fn binding_node(devices: &Devices, d: int) -> usize {
    (devices.page + 1 + d) as usize
}

/// The device whose binding node x is.
pub open spec fn binding_device(devices: &Devices, x: usize) -> int {
    x - devices.page - 1
}

impl Devices {
    pub fn new(page: usize) -> (ret: Self)
        requires
            page % PAGE_SZ == 0,
            page + PAGE_SZ <= NODE_SPACE,
        ensures
            ret.wf(),
            ret.count == 0,
            ret.page == page,
            ret.holder@ == Map::<usize, usize>::empty(),
    {
        Devices { records: Array::new(DeviceRecord { iommu: 0, number: 0, space: None, unbound: 0 }), count: 0, page, holder: Ghost(Map::empty()) }
    }

    /// Records d and e are on different IOMMUs or have different numbers.
    pub open spec fn distinct(&self, d: int, e: int) -> bool {
        self.records@[d].iommu != self.records@[e].iommu || self.records@[d].number != self.records@[e].number
    }

    /// Each record names an IOMMU and a device number on it, and no two name the same. The binding nodes
    /// lie in one node page.
    pub open spec fn wf(&self) -> bool {
        &&& self.records.wf()
        &&& self.count <= MAX_DEVICES
        &&& self.page % PAGE_SZ == 0
        &&& self.page + PAGE_SZ <= NODE_SPACE
        &&& forall|d: int| 0 <= d < self.count ==> {
            &&& (#[trigger] self.records@[d]).iommu < NUM_IOMMUS
            &&& self.records@[d].number < IOMMU_DEVICES
        }
        &&& forall|d: int, e: int| #![trigger self.records@[d], self.records@[e]]
            0 <= d < self.count && 0 <= e < self.count && d != e ==> self.distinct(d, e)
    }

    /// No record names this device.
    pub open spec fn fresh(&self, info: DeviceInfo) -> bool {
        forall|d: int| 0 <= d < self.count ==>
            (#[trigger] self.records@[d]).iommu != info.iommu || self.records@[d].number != info.number
    }

    /// Whether a record already names this device, in at most MAX_DEVICES loads.
    pub fn recorded(&self, info: DeviceInfo, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
        ensures
            final(steps).count <= old(steps).count + MAX_DEVICES,
            ret == !self.fresh(info),
    {
        let ghost start = steps.count;
        let mut e = 0;
        while e < self.count
            invariant
                self.wf(),
                0 <= e <= self.count,
                start == old(steps).count,
                steps.count == start + e,
                forall|d: int| 0 <= d < e ==>
                    (#[trigger] self.records@[d]).iommu != info.iommu || self.records@[d].number != info.number,
            decreases self.count - e,
        {
            proof {
                steps.step();
            }
            let r = *self.records.get(e);
            if r.iommu == info.iommu && r.number == info.number {
                return true;
            }
            e = e + 1;
        }
        false
    }

    /// Records a device no record names, unbound, its capability to be node.
    pub fn record(&mut self, info: DeviceInfo, Ghost(node): Ghost<usize>)
        requires
            old(self).wf(),
            old(self).count < MAX_DEVICES,
            info.iommu < NUM_IOMMUS,
            info.number < IOMMU_DEVICES,
            old(self).fresh(info),
        ensures
            final(self).wf(),
            final(self).count == old(self).count + 1,
            final(self).page == old(self).page,
            final(self).records@ == old(self).records@.update(old(self).count as int, unbound_record(info)),
            final(self).holder@ == old(self).holder@.insert(device_object(old(self).count as int), node),
    {
        let ghost pre = *old(self);
        let d = self.count;
        self.records.set(d, DeviceRecord { iommu: info.iommu, number: info.number, space: None, unbound: 0 });
        self.count = d + 1;
        self.holder = Ghost(pre.holder@.insert(device_object(d as int), node));
        proof {
            let me = *self;
            assert forall|x: int, y: int| #![trigger me.records@[x], me.records@[y]]
                0 <= x < me.count && 0 <= y < me.count && x != y implies me.distinct(x, y) by {
                if x == d {
                    assert(pre.records@[y] == me.records@[y]);
                } else if y == d {
                    assert(pre.records@[x] == me.records@[x]);
                } else {
                    assert(pre.distinct(x, y));
                }
            }
        }
    }

    /// The table has a record for device object o.
    pub open spec fn names(&self, o: usize) -> bool {
        &&& DEVICE_OBJECTS <= o
        &&& o % PAGE_SZ == 0
        &&& device_of(o) < self.count
    }

    /// Device d is bound to nothing, its last unbind at this epoch.
    pub fn unbind(&mut self, d: usize, epoch: usize)
        requires
            old(self).wf(),
            d < old(self).count,
        ensures
            final(self).wf(),
            final(self).count == old(self).count,
            final(self).page == old(self).page,
            final(self).holder == old(self).holder,
            final(self).records@ == old(self).records@.update(
                d as int,
                unbound_at(old(self).records@[d as int], epoch),
            ),
    {
        let ghost pre = *old(self);
        let r = *self.records.get(d);
        self.records.set(d, DeviceRecord { iommu: r.iommu, number: r.number, space: None, unbound: epoch });
        proof {
            let me = *self;
            assert forall|x: int, y: int| #![trigger me.records@[x], me.records@[y]]
                0 <= x < me.count && 0 <= y < me.count && x != y implies me.distinct(x, y) by {
                assert(pre.distinct(x, y));
            }
        }
    }

    /// Device d is bound to the space at s.
    pub fn bind(&mut self, d: usize, s: usize)
        requires
            old(self).wf(),
            d < old(self).count,
        ensures
            final(self).wf(),
            final(self).count == old(self).count,
            final(self).page == old(self).page,
            final(self).holder == old(self).holder,
            final(self).records@ == old(self).records@.update(d as int, bound_record(old(self).records@[d as int], s)),
    {
        let ghost pre = *old(self);
        let r = *self.records.get(d);
        self.records.set(d, DeviceRecord { iommu: r.iommu, number: r.number, space: Some(s), unbound: r.unbound });
        proof {
            let me = *self;
            assert forall|x: int, y: int| #![trigger me.records@[x], me.records@[y]]
                0 <= x < me.count && 0 <= y < me.count && x != y implies me.distinct(x, y) by {
                assert(pre.distinct(x, y));
            }
        }
    }
}

/// Every device capability names one device, a record of the table, and is the one that device was
/// given. Its parent is the list's first node, which nobody holds, so only its holder reaches the
/// device directly: add_device puts it there, derive refuses a device capability and a move keeps a
/// node's parent. Opaque, so a step that leaves the list, the tables and the devices alone carries it
/// without unfolding it.
#[verifier::opaque]
pub open spec fn devices_wf(list: &Tree, tables: &Tables, devices: &Devices) -> bool {
    &&& devices.wf()
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Device ==> {
        &&& tables.payload_of(n).order == 0
        &&& devices.names(tables.payload_of(n).base)
        &&& devices.holder@.contains_key(tables.payload_of(n).base)
        &&& devices.holder@[tables.payload_of(n).base] == n
        &&& n < NODE_SPACE
        &&& list.parent@.contains_key(n)
        &&& list.parent@[n] == devices.page
    }
}

/// So at most one live capability names each device.
pub proof fn lemma_device_cap_unique(list: &Tree, tables: &Tables, devices: &Devices, n: usize, m: usize)
    requires
        devices_wf(list, tables, devices),
        tables.is_cap(list, n),
        tables.is_cap(list, m),
        tables.payload_of(n).kind is Device,
        tables.payload_of(m).kind is Device,
        tables.payload_of(n).base == tables.payload_of(m).base,
    ensures
        n == m,
{
    reveal(devices_wf);
}

/// The device capabilities of b were capabilities of a, saying the same, so the device table needs
/// nothing new.
pub open spec fn devices_kept(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Device ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
}

/// Every node live in a has the parent it had: a derive gives one only to a node that was dead, and a
/// removal takes none away.
pub open spec fn live_parents_kept(a: &Tree, b: &Tree) -> bool {
    forall|x: usize| x < NODE_SPACE && a.nodes@[x as int].live && #[trigger] a.parent@.contains_key(x)
        ==> b.parent@.contains_key(x) && b.parent@[x] == a.parent@[x]
}

pub proof fn lemma_devices_kept(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables, devices: &Devices)
    requires
        devices_wf(list_a, tables_a, devices),
        devices_kept(list_a, tables_a, list_b, tables_b),
        live_parents_kept(list_a, list_b),
    ensures
        devices_wf(list_b, tables_b, devices),
{
    reveal(devices_wf);
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Device implies {
        &&& tables_b.payload_of(n).order == 0
        &&& devices.names(tables_b.payload_of(n).base)
        &&& devices.holder@.contains_key(tables_b.payload_of(n).base)
        &&& devices.holder@[tables_b.payload_of(n).base] == n
        &&& n < NODE_SPACE
        &&& list_b.parent@.contains_key(n)
        &&& list_b.parent@[n] == devices.page
    } by {
        assert(tables_a.is_cap(list_a, n));
        assert(list_a.parent@.contains_key(n));
        assert(list_b.parent@.contains_key(n));
    }
}

/// The device capabilities read only the device table's count and holders, so a step that changes
/// only records' bindings keeps them.
pub proof fn lemma_devices_records(list: &Tree, tables: &Tables, a: &Devices, b: &Devices)
    requires
        devices_wf(list, tables, a),
        b.wf(),
        b.count == a.count,
        b.page == a.page,
        b.holder == a.holder,
    ensures
        devices_wf(list, tables, b),
{
    reveal(devices_wf);
}

/// Node x's parent is a live capability to the device space at s.
pub open spec fn device_binding_parent(list: &Tree, tables: &Tables, x: usize, s: usize) -> bool {
    let n = list.parent@[x];
    &&& list.parent@.contains_key(x)
    &&& tables.is_cap(list, n)
    &&& tables.payload_of(n).kind is Space
    &&& tables.payload_of(n).base == s
}

/// A live device binding node is the binding node of a device whose record names a space, and its parent
/// is a capability to that space; a device whose record names a space has its binding node live and is
/// in that space's bound set; and a member of a space's bound set is a device whose record names the space.
/// So unlinking a device binding node finds what to undo from the node alone. Opaque, so that its node
/// quantifier does not chain into the tables in every proof that mentions a node. See
/// design/device-binding-under-the-space-capability/.
#[verifier::opaque]
pub open spec fn device_bindings_wf(list: &Tree, tables: &Tables, bound: IMap<usize, Set<usize>>, devices: &Devices) -> bool {
    &&& forall|x: usize| x < NODE_SPACE && (#[trigger] list.nodes@[x as int]).live && list.nodes@[x as int].kind is DeviceBinding ==> {
        let d = binding_device(devices, x);
        &&& 0 <= d < devices.count
        &&& devices.records@[d].space is Some
        &&& device_binding_parent(list, tables, x, devices.records@[d].space->Some_0)
    }
    &&& forall|d: int| 0 <= d < devices.count && (#[trigger] devices.records@[d]).space is Some ==> {
        let x = binding_node(devices, d);
        let s = devices.records@[d].space->Some_0;
        &&& x < NODE_SPACE
        &&& list.nodes@[x as int].live
        &&& list.nodes@[x as int].kind is DeviceBinding
        &&& bound.contains_key(s)
        &&& bound[s].contains(d as usize)
    }
    &&& forall|s: usize, d: usize| bound.contains_key(s) && #[trigger] bound[s].contains(d)
        ==> d < devices.count && devices.records@[d as int].space == Some(s)
}

/// The binding nodes are nodes of the list's first page, and a bound device sits behind an IOMMU the
/// machine has, which acknowledged the device's last unbind, so nothing it cached under the device's IOid
/// from the space it was bound to before survives.
pub open spec fn devices_placed(list: &Tree, present: Seq<bool>, acked: Seq<usize>, devices: &Devices) -> bool {
    &&& devices.page == list.seq@[0]
    &&& forall|d: int| 0 <= d < devices.count && (#[trigger] devices.records@[d]).space is Some ==> {
        &&& present[devices.records@[d].iommu as int]
        &&& devices.records@[d].unbound <= acked[devices.records@[d].iommu as int]
    }
}

/// The device table after a step that bound and unbound nothing: the same page, each record bound as it
/// was, and any record added bound to nothing.
pub open spec fn device_spaces_kept(a: &Devices, b: &Devices) -> bool {
    &&& b.page == a.page
    &&& a.count <= b.count
    &&& forall|d: int| 0 <= d < a.count ==> (#[trigger] b.records@[d]).space == a.records@[d].space
    &&& forall|d: int| a.count <= d < b.count ==> (#[trigger] b.records@[d]).space is None
}

/// Each space has the same devices bound.
pub open spec fn bound_kept(a: IMap<usize, Set<usize>>, b: IMap<usize, Set<usize>>) -> bool {
    forall|s: usize, d: usize| #![trigger a[s].contains(d)] #![trigger b[s].contains(d)]
        (b.contains_key(s) && b[s].contains(d)) == (a.contains_key(s) && a[s].contains(d))
}

/// A space whose bound set is empty gains or loses its entry, and the bound sets say the same.
pub proof fn lemma_bound_kept_empty(a: IMap<usize, Set<usize>>, s: usize)
    requires
        a.contains_key(s) ==> a[s] == Set::<usize>::empty(),
    ensures
        bound_kept(a, a.insert(s, Set::<usize>::empty())),
        bound_kept(a, a.remove(s)),
{
}

/// The device bindings after a step that kept every live device binding node, its parent and what that
/// says, and bound and unbound nothing.
pub proof fn lemma_device_bindings_kept(
    la: &Tree,
    ta: &Tables,
    ba: IMap<usize, Set<usize>>,
    da: &Devices,
    lb: &Tree,
    tb: &Tables,
    bb: IMap<usize, Set<usize>>,
    db: &Devices,
)
    requires
        device_bindings_wf(la, ta, ba, da),
        forall|x: usize| x < NODE_SPACE ==> ((#[trigger] lb.nodes@[x as int]).live && lb.nodes@[x as int].kind is DeviceBinding)
            == (la.nodes@[x as int].live && la.nodes@[x as int].kind is DeviceBinding),
        forall|x: usize, s: usize| x < NODE_SPACE && la.nodes@[x as int].live && la.nodes@[x as int].kind is DeviceBinding
            && #[trigger] device_binding_parent(la, ta, x, s) ==> device_binding_parent(lb, tb, x, s),
        device_spaces_kept(da, db),
        bound_kept(ba, bb),
    ensures
        device_bindings_wf(lb, tb, bb, db),
{
    reveal(device_bindings_wf);
    assert forall|x: usize| x < NODE_SPACE && (#[trigger] lb.nodes@[x as int]).live && lb.nodes@[x as int].kind is DeviceBinding implies {
        let d = binding_device(db, x);
        &&& 0 <= d < db.count
        &&& db.records@[d].space is Some
        &&& device_binding_parent(lb, tb, x, db.records@[d].space->Some_0)
    } by {
        assert(la.nodes@[x as int].live && la.nodes@[x as int].kind is DeviceBinding);
        let d = binding_device(da, x);
        assert(db.records@[d].space == da.records@[d].space);
        assert(device_binding_parent(la, ta, x, da.records@[d].space->Some_0));
    }
    assert forall|d: int| 0 <= d < db.count && (#[trigger] db.records@[d]).space is Some implies {
        let x = binding_node(db, d);
        let s = db.records@[d].space->Some_0;
        &&& x < NODE_SPACE
        &&& lb.nodes@[x as int].live
        &&& lb.nodes@[x as int].kind is DeviceBinding
        &&& bb.contains_key(s)
        &&& bb[s].contains(d as usize)
    } by {
        assert(d < da.count);
        assert(da.records@[d].space == db.records@[d].space);
        let x = binding_node(da, d);
        let s = da.records@[d].space->Some_0;
        assert(la.nodes@[x as int].live && la.nodes@[x as int].kind is DeviceBinding);
        assert(x < NODE_SPACE);
        assert(lb.nodes@[x as int].live && lb.nodes@[x as int].kind is DeviceBinding);
        assert(ba[s].contains(d as usize));
    }
    assert forall|s: usize, d: usize| bb.contains_key(s) && #[trigger] bb[s].contains(d)
        implies d < db.count && db.records@[d as int].space == Some(s) by {
        assert(ba.contains_key(s) && ba[s].contains(d));
    }
}

impl CapKernel {
    /// The device bindings after a step that changed no node but n and m, neither a device binding before
    /// or after, renamed n to m in the parent map at most, and bound and unbound nothing. A binding's
    /// parent is a capability with a child, so it is n or m only when n, renamed m, says the same.
    pub proof fn lemma_device_bindings_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !(pre.list.nodes@[n as int].live && pre.list.nodes@[n as int].kind is DeviceBinding),
            !(post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is DeviceBinding),
            !(pre.list.nodes@[m as int].live && pre.list.nodes@[m as int].kind is DeviceBinding),
            !(post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is DeviceBinding),
            forall|x: usize| x != n && x != m && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == rename(pre.list.parent@[x], n, m),
            pre.is_cap(n) ==> pre.list.childless(n) || (post.is_cap(m) && post.payload_of(m) == pre.payload_of(n)),
            pre.is_cap(m) && m != n ==> pre.list.childless(m),
            device_spaces_kept(&pre.devices, &post.devices),
            bound_kept(pre.spaces.bound@, post.spaces.bound@),
        ensures
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        assert forall|x: usize| x < NODE_SPACE implies
            ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is DeviceBinding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding) by {
            if x != n && x != m {
                assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                assert(post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind);
            }
        }
        assert forall|x: usize, s: usize| x < NODE_SPACE && pre.list.nodes@[x as int].live
            && pre.list.nodes@[x as int].kind is DeviceBinding && #[trigger] device_binding_parent(&pre.list, &pre.tables, x, s)
            implies device_binding_parent(&post.list, &post.tables, x, s) by {
            assert(x != n && x != m);
            let a = pre.list.parent@[x];
            assert(pre.is_cap(a));
            let q = pre.list.seq@;
            assert(has(q, x));
            lemma_has(q, x);
            assert(pre.list.nodes@[q[0] as int].kind is Capability);
            assert(pre.list.is_child(a, x));
            assert(pre.list.nodes@[a as int].live);
            if a == n {
                if pre.list.childless(n) {
                    pre.list.lemma_childless(n, x);
                }
                assert(post.is_cap(m) && post.payload_of(m) == pre.payload_of(n));
            } else if a == m {
                pre.list.lemma_childless(m, x);
            } else {
                Self::lemma_caps_frame(pre, post, n, m, a);
            }
        }
        lemma_device_bindings_kept(
            &pre.list, &pre.tables, pre.spaces.bound@, &pre.devices,
            &post.list, &post.tables, post.spaces.bound@, &post.devices,
        );
    }

    /// The device bindings after a step that made and unlinked no device binding, kept every live node's
    /// parent and every space capability saying the same, and bound and unbound nothing.
    pub proof fn lemma_device_bindings_space_caps(pre: Self, post: Self)
        requires
            device_bindings_wf(&pre.list, &pre.tables, pre.spaces.bound@, &pre.devices),
            forall|x: usize| x < NODE_SPACE ==> ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is DeviceBinding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding),
            forall|x: usize| x < NODE_SPACE && pre.list.nodes@[x as int].live && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == pre.list.parent@[x],
            forall|x: usize| #[trigger] pre.is_cap(x) && pre.payload_of(x).kind is Space
                ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            device_spaces_kept(&pre.devices, &post.devices),
            bound_kept(pre.spaces.bound@, post.spaces.bound@),
        ensures
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        assert forall|x: usize, s: usize| x < NODE_SPACE && pre.list.nodes@[x as int].live
            && pre.list.nodes@[x as int].kind is DeviceBinding && #[trigger] device_binding_parent(&pre.list, &pre.tables, x, s)
            implies device_binding_parent(&post.list, &post.tables, x, s) by {
            assert(pre.list.parent@.contains_key(x));
            assert(pre.is_cap(pre.list.parent@[x]));
        }
        lemma_device_bindings_kept(
            &pre.list, &pre.tables, pre.spaces.bound@, &pre.devices,
            &post.list, &post.tables, post.spaces.bound@, &post.devices,
        );
    }

    /// The device bindings after a step that made and unlinked no device binding, kept every live node's
    /// parent and every capability saying the same, and bound and unbound nothing.
    pub proof fn lemma_device_bindings_same_caps(pre: Self, post: Self)
        requires
            device_bindings_wf(&pre.list, &pre.tables, pre.spaces.bound@, &pre.devices),
            same_bindings(&pre.list, &post.list),
            forall|x: usize| x < NODE_SPACE && pre.list.nodes@[x as int].live && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == pre.list.parent@[x],
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            device_spaces_kept(&pre.devices, &post.devices),
            bound_kept(pre.spaces.bound@, post.spaces.bound@),
        ensures
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        assert forall|x: usize| x < NODE_SPACE implies
            ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is DeviceBinding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding) by {
            assert(same_bindings(&pre.list, &post.list));
        }
        Self::lemma_device_bindings_space_caps(pre, post);
    }

    /// A device bound to s is bound through a capability to s, so s is a device space.
    pub proof fn lemma_bound_is_space(&self, s: usize, d: usize)
        requires
            self.wf(),
            self.spaces.bound@.contains_key(s),
            self.spaces.bound@[s].contains(d),
        ensures
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind is Device,
    {
        reveal(device_bindings_wf);
        reveal(devices_wf);
        assert(self.devices.wf());
        assert(d < self.devices.count);
        let x = binding_node(&self.devices, d as int);
        assert(self.devices.records@[d as int].space == Some(s));
        assert(self.list.nodes@[x as int].live && self.list.nodes@[x as int].kind is DeviceBinding);
        assert(binding_device(&self.devices, x) == d);
        assert(device_binding_parent(&self.list, &self.tables, x, s));
        self.lemma_space_cap(self.list.parent@[x]);
    }

    /// Only a device space has devices bound.
    pub proof fn lemma_bound_empty(&self, s: usize)
        requires
            self.wf(),
            !(self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device),
        ensures
            self.spaces.bound@.contains_key(s) ==> self.spaces.bound@[s] == Set::<usize>::empty(),
    {
        let a = self.spaces.bound@;
        if a.contains_key(s) {
            assert forall|d: usize| !a[s].contains(d) by {
                if a[s].contains(d) {
                    self.lemma_bound_is_space(s, d);
                }
            }
            assert(a[s] =~= Set::<usize>::empty());
        }
    }

    /// A space that is not one yet has nothing bound, so giving it an empty bound set keeps every space's.
    pub proof fn lemma_bound_kept_new_space(&self, s: usize)
        requires
            self.wf(),
            !self.spaces.roots@.contains_key(s),
        ensures
            bound_kept(self.spaces.bound@, self.spaces.bound@.insert(s, Set::<usize>::empty())),
    {
        self.lemma_bound_empty(s);
        lemma_bound_kept_empty(self.spaces.bound@, s);
    }

    /// What unlinking device binding node n did: the device is bound to nothing, it left its space's
    /// bound set, the reference it held on the space's block went, the root's page is recorded stale at a
    /// new epoch, since an IOMMU may cache a walk from a root that has no parent entry to cut, and the
    /// device's record keeps that epoch as its last unbind. See
    /// design/device-binding-under-the-space-capability/.
    pub open spec fn device_unbound(pre: Self, post: Self, n: usize) -> bool {
        let d = binding_device(&pre.devices, n);
        let s = pre.devices.records@[d].space->Some_0;
        let br = BlockRef::Small(s / PAGE_SZ);
        &&& 0 <= d < pre.devices.count
        &&& pre.devices.records@[d].space is Some
        &&& pre.spaces.bound@.contains_key(s)
        &&& pre.spaces.bound@[s].contains(d as usize)
        &&& device_binding_parent(&pre.list, &pre.tables, n, s)
        &&& post.flush_epoch == pre.flush_epoch + 1
        &&& post.stale_epoch.written(post.flush_epoch, s / PAGE_SZ)
        &&& post.devices.count == pre.devices.count
        &&& post.devices.page == pre.devices.page
        &&& post.devices.holder == pre.devices.holder
        &&& post.devices.records@ == pre.devices.records@.update(d, unbound_at(pre.devices.records@[d], post.flush_epoch))
        &&& post.spaces.bound@ == pre.spaces.bound@.insert(s, pre.spaces.bound@[s].remove(d as usize))
        &&& blocks_refs_changed(
            &pre.blocks,
            &post.blocks,
            br,
            (block_refs(&pre.blocks, br) - 1) as usize,
            block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
        )
        &&& post.spaces.roots == pre.spaces.roots
        &&& post.spaces.records == pre.spaces.records
        &&& post.spaces.loaded == pre.spaces.loaded
        &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
        &&& post.spaces.holders == pre.spaces.holders
    }

    /// Unbinds the device whose binding node n is, before n is unlinked.
    pub fn unbind_device(&mut self, n: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).list.nodes@[n as int].kind is DeviceBinding,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + UNBIND_DEVICE_STEPS,
            Self::device_unbound(*old(self), *final(self), n),
            final(self).blocks.wf(),
            final(self).devices.wf(),
            final(self).stale_epoch.wf(),
            final(self).tlb_wf(),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).tlb == old(self).tlb,
            final(self).iommus == old(self).iommus,
            final(self).mapped == old(self).mapped,
            final(self).table_pages == old(self).table_pages,
            final(self).mappings == old(self).mappings,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).holders == old(self).holders,
            final(self).stop_ipis == old(self).stop_ipis,
            final(self).flush_ipis == old(self).flush_ipis,
    {
        let ghost pre = *old(self);
        proof {
            reveal(device_bindings_wf);
            reveal(devices_wf);
            let d = binding_device(&pre.devices, n);
            let s = pre.devices.records@[d].space->Some_0;
            assert(device_binding_parent(&pre.list, &pre.tables, n, s));
            pre.lemma_space_cap(pre.list.parent@[n]);
        }
        let d = n - self.devices.page - 1;
        let record = *self.devices.records.get(d);
        let s = match record.space {
            Some(s) => s,
            None => {
                proof {
                    assert(false);
                }
                0
            },
        };
        drop_block_ref(&mut self.blocks, BlockRef::Small(s / PAGE_SZ));
        self.spaces.bound = Ghost(pre.spaces.bound@.insert(s, pre.spaces.bound@[s].remove(d)));
        self.flush_epoch = self.flush_epoch + 1;
        let epoch = self.flush_epoch;
        self.stale_epoch.record_run(s / PAGE_SZ, 1, epoch, Tracked(steps));
        self.devices.unbind(d, epoch);
        proof {
            assert(self.stale_epoch.written(epoch, s / PAGE_SZ));
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] self.acked(c) <= self.flush_epoch by {
                assert(pre.acked(c) <= pre.flush_epoch);
            }
            assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) implies self.loaded(c, e.space) by {
                assert(pre.loaded(c, e.space));
            }
            assert forall|c: int, e: TlbEntry|
                0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.acked(c), e.page) by {
                assert(pre.acked(c) <= pre.flush_epoch);
                assert(pre.stale_epoch.above(pre.acked(c), e.page));
            }
            assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) implies self.iommu_present(i) by {
                assert(pre.iommus.tlb@[i].contains(e));
            }
            assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] self.iommu_acked(i) <= self.flush_epoch by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
            }
            assert forall|i: int, e: TlbEntry|
                0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.iommu_acked(i), e.page) by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
                assert(pre.iommus.tlb@[i].contains(e));
                assert(pre.stale_epoch.above(pre.iommu_acked(i), e.page));
            }
        }
    }

    /// The refusals: a full table, an IOMMU or device number out of range, a device already recorded,
    /// or an index that names no free slot. Boot's list of devices comes from firmware tables.
    pub open spec fn can_add_device(&self, root: usize, slot: usize, info: DeviceInfo) -> bool {
        &&& self.devices.count < MAX_DEVICES
        &&& info.iommu < NUM_IOMMUS
        &&& info.number < IOMMU_DEVICES
        &&& self.devices.fresh(info)
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& !self.list.nodes@[self.tables.node_of(root, slot) as int].live
    }

    /// Device k of boot's list can be added after the ones before it: it is in range, no device
    /// before it in the list is the same device, and index slot + k names a free slot of the table
    /// at root. The table of devices is empty before boot fills it, so no recorded device refuses it.
    pub open spec fn can_add_device_at(&self, root: usize, slot: usize, devices: Seq<DeviceInfo>, k: int) -> bool {
        &&& devices[k].iommu < NUM_IOMMUS
        &&& devices[k].number < IOMMU_DEVICES
        &&& forall|j: int| 0 <= j < k ==> (#[trigger] devices[j]).iommu != devices[k].iommu || devices[j].number != devices[k].number
        &&& self.tables.has_slot(&self.list, root, (slot + k) as usize)
        &&& !self.list.nodes@[self.tables.node_of(root, (slot + k) as usize) as int].live
    }

    /// When add_devices succeeds: each of the first count devices in boot's list can be added after
    /// the ones before it.
    pub open spec fn can_add_devices(&self, root: usize, slot: usize, devices: Seq<DeviceInfo>, count: usize) -> bool {
        forall|k: int| 0 <= k < count ==> #[trigger] self.can_add_device_at(root, slot, devices, k)
    }

    /// Records a device boot found and puts its capability at index `slot` of the table at root, a
    /// child of the list's first node. A refusal changes nothing.
    pub fn add_device(&mut self, first: usize, root: usize, slot: usize, info: DeviceInfo, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            first == old(self).list.seq@[0],
        ensures
            final(steps).count <= old(steps).count + MAX_DEVICES,
            final(self).wf(),
            ret == old(self).can_add_device(root, slot, info),
            !ret ==> *final(self) == *old(self),
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.seq@[0] == old(self).list.seq@[0],
            final(self).blocks == old(self).blocks,
            final(self).iommus == old(self).iommus,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            ret ==> final(self).list.parent@ == old(self).list.parent@.insert(old(self).tables.node_of(root, slot), first),
            ret ==> {
                let n = old(self).tables.node_of(root, slot);
                let d = old(self).devices.count;
                &&& forall|i: int| #![trigger final(self).list.nodes@[i]] 0 <= i < NODE_SPACE && i != n ==> {
                    &&& final(self).list.nodes@[i].live == old(self).list.nodes@[i].live
                    &&& final(self).list.nodes@[i].kind == old(self).list.nodes@[i].kind
                    &&& final(self).list.nodes@[i].depth == old(self).list.nodes@[i].depth
                }
                &&& final(self).devices.count == d + 1
                &&& final(self).devices.records@ == old(self).devices.records@.update(d as int, unbound_record(info))
                &&& final(self).is_cap(n)
                &&& final(self).payload_of(n) == device_payload(d as int)
                &&& final(self).list.is_child(first, n)
                &&& Self::adds_cap(*old(self), *final(self), n)
            },
    {
        let ghost pre = *old(self);
        proof {
            reveal(devices_wf);
        }
        if self.devices.count >= MAX_DEVICES || info.iommu >= NUM_IOMMUS || info.number >= IOMMU_DEVICES
            || self.devices.recorded(info, Tracked(steps)) {
            return false;
        }
        let child = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found.0,
            None => { return false; },
        };
        if self.list.get(child).live {
            return false;
        }
        let d = self.devices.count;
        proof {
            pre.lemma_slot(root, slot);
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(first);
            pre.list.lemma_valid_bound(first);
            self.list.lemma_seq_fits();
            self.list.lemma_valid_bound(child);
            lemma_device_object(d as int);
        }
        let payload = Payload { kind: CapKind::Device, order: 0, rights: DEVICE_RIGHTS, base: DEVICE_OBJECTS + d * PAGE_SZ, badge: 0, reserved: 0 };
        self.list.derive(first, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(&self.list, root, slot, payload);
        self.devices.record(info, Ghost(child));
        proof {
            let post = *self;
            assert(post.payload_of(child) == device_payload(d as int));
            assert(0u32 & 128u32 == 0) by (bit_vector);
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            Self::lemma_add_untracked_holders(pre, post, child);
            pre.lemma_first_page_apart();
            Self::lemma_add_device_devices(pre, post, child, d as int);
            lemma_parents_derived(pre.list, post.list, first, child);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_derive_step_adds_cap(pre, post, child);
        }
        true
    }

    /// The blocks, frames, spaces, threads and processes after a capability no record tracks is added,
    /// an untyped's, a device's, the console's or power's, and nothing else changed.
    pub proof fn lemma_add_untracked_holders(pre: Self, post: Self, child: usize)
        requires
            Self::derive_step(pre, post, child),
            child % PAGE_SZ != 0,
            !tracked_kind(post.payload_of(child).kind),
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.zeroing == pre.zeroing,
            post.table_pages == pre.table_pages,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
        lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
        lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
        lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
    }

    /// The devices after device d's capability is added: it is d's, and every other device capability
    /// names a device recorded before.
    proof fn lemma_add_device_devices(pre: Self, post: Self, child: usize, d: int)
        requires
            Self::derive_step(pre, post, child),
            d == pre.devices.count,
            d < MAX_DEVICES,
            post.payload_of(child) == device_payload(d),
            post.devices.wf(),
            post.devices.count == d + 1,
            post.devices.holder@ == pre.devices.holder@.insert(device_object(d), child),
            post.devices.page == pre.devices.page,
            post.list.parent@ == pre.list.parent@.insert(child, pre.devices.page),
            child < NODE_SPACE,
        ensures
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        reveal(devices_wf);
        lemma_device_object(d);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Device implies {
            &&& post.tables.payload_of(x).order == 0
            &&& post.devices.names(post.tables.payload_of(x).base)
            &&& post.devices.holder@.contains_key(post.tables.payload_of(x).base)
            &&& post.devices.holder@[post.tables.payload_of(x).base] == x
            &&& x < NODE_SPACE
            &&& post.list.parent@.contains_key(x)
            &&& post.list.parent@[x] == post.devices.page
        } by {
            if x != child {
                Self::lemma_caps_frame(pre, post, child, child, x);
                assert(pre.tables.is_cap(&pre.list, x));
                assert(device_of(pre.payload_of(x).base) < d);
                assert(pre.list.parent@.contains_key(x));
            }
        }
    }

    /// Gives each device boot found a record and a capability under the list's first node, device k
    /// at index slot + k of the table at root. Boot fills the table once, and it stops at the first
    /// device refused, so false means boot fails, and what the devices before it were given stays.
    pub fn add_devices(&mut self, first: usize, root: usize, slot: usize, devices: &Array<DeviceInfo, MAX_DEVICES>, count: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            first == old(self).list.seq@[0],
            old(self).devices.count == 0,
            devices.wf(),
            count <= MAX_DEVICES,
            slot + count <= usize::MAX,
        ensures
            final(steps).count <= old(steps).count + MAX_DEVICES * (MAX_DEVICES + 1),
            final(self).wf(),
            ret == old(self).can_add_devices(root, slot, devices@, count),
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.seq@[0] == old(self).list.seq@[0],
            final(self).blocks == old(self).blocks,
            final(self).iommus == old(self).iommus,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            ret ==> {
                &&& final(self).devices.count == count
                &&& forall|k: int| 0 <= k < count ==> {
                    let n = old(self).tables.node_of(root, (slot + k) as usize);
                    &&& #[trigger] final(self).devices.records@[k] == unbound_record(devices@[k])
                    &&& final(self).is_cap(n)
                    &&& final(self).payload_of(n) == device_payload(k)
                    &&& final(self).list.is_child(first, n)
                }
            },
    {
        let ghost pre = *old(self);
        let ghost start = steps.count;
        let mut k = 0;
        while k != count
            invariant
                self.wf(),
                0 <= k <= count,
                start == old(steps).count,
                steps.count <= start + k * (MAX_DEVICES + 1),
                count <= MAX_DEVICES,
                slot + count <= usize::MAX,
                devices.wf(),
                self.tables.roots == pre.tables.roots,
                self.tables.owner == pre.tables.owner,
                self.tables.roots@.contains_key(root),
                first == self.list.seq@[0],
                self.devices.count == k,
                forall|j: int| 0 <= j < k ==> {
                    let n = pre.tables.node_of(root, (slot + j) as usize);
                    &&& #[trigger] self.devices.records@[j] == unbound_record(devices@[j])
                    &&& self.is_cap(n)
                    &&& self.payload_of(n) == device_payload(j)
                    &&& self.list.is_child(first, n)
                },
                pre == *old(self),
                pre.wf(),
                first == pre.list.seq@[0],
                self.blocks == pre.blocks,
                self.iommus == pre.iommus,
                self.processes == pre.processes,
                self.spaces == pre.spaces,
                forall|j: int| 0 <= j < k ==> #[trigger] pre.can_add_device_at(root, slot, devices@, j),
                // Only the devices' nodes came to life, none at the start of a page, and none of a
                // later device's slot.
                forall|i: int| #![trigger self.list.nodes@[i]] 0 <= i < NODE_SPACE && pre.list.nodes@[i].live ==> self.list.nodes@[i].live,
                forall|i: int| #![trigger self.list.nodes@[i]] 0 <= i < NODE_SPACE && i % PAGE_SZ as int == 0
                    ==> self.list.nodes@[i].live == pre.list.nodes@[i].live,
                forall|m: int| k <= m < count && #[trigger] pre.tables.has_slot(&pre.list, root, (slot + m) as usize)
                    ==> self.list.nodes@[pre.tables.node_of(root, (slot + m) as usize) as int].live
                        == pre.list.nodes@[pre.tables.node_of(root, (slot + m) as usize) as int].live,
            decreases count - k,
        {
            let ghost before = *self;
            proof {
                steps.step();
                assert((k + 1) * (MAX_DEVICES + 1) == k * (MAX_DEVICES + 1) + MAX_DEVICES + 1) by (nonlinear_arith);
                assert((k + 1) * (MAX_DEVICES + 1) <= MAX_DEVICES * (MAX_DEVICES + 1)) by (nonlinear_arith)
                    requires
                        k < count,
                        count <= MAX_DEVICES,
                ;
            }
            let info = *devices.get(k);
            if !self.add_device(first, root, slot + k, info, Tracked(steps)) {
                proof {
                    // Device k could be added after the ones before it, add_device would take it.
                    let i = (slot + k) as usize;
                    if pre.can_add_device_at(root, slot, devices@, k as int) {
                        Self::lemma_slot_stays(pre, before, root, i);
                        assert(pre.tables.has_slot(&pre.list, root, (slot + k) as usize));
                        assert forall|d: int| 0 <= d < before.devices.count implies
                            (#[trigger] before.devices.records@[d]).iommu != info.iommu || before.devices.records@[d].number != info.number by {
                            assert(before.devices.records@[d] == unbound_record(devices@[d]));
                        }
                        assert(before.can_add_device(root, i, info));
                    }
                    assert(!pre.can_add_device_at(root, slot, devices@, k as int));
                }
                return false;
            }
            proof {
                // The records' length, for the update.
                reveal(devices_wf);
                let i = (slot + k) as usize;
                let n = pre.tables.node_of(root, i);
                assert(before.tables.node_of(root, i) == n);
                // Device k could be added after the ones before it: its slot is the one add_device
                // filled, whose leaf is at the start of a page and lived before.
                let leaf = before.tables.leaf(root, index_entry(i));
                before.tables.lemma_entry(root, index_entry(i));
                before.tables.lemma_leaf(&before.list, leaf);
                before.lemma_slot(root, i);
                before.lemma_slot_bound(n);
                assert(leaf % PAGE_SZ == 0);
                assert(before.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
                assert(pre.tables.has_slot(&pre.list, root, i));
                assert(!before.list.nodes@[n as int].live);
                assert(!pre.list.nodes@[n as int].live);
                assert forall|j: int| 0 <= j < k implies
                    (#[trigger] devices@[j]).iommu != devices@[k as int].iommu || devices@[j].number != devices@[k as int].number by {
                    assert(before.devices.records@[j] == unbound_record(devices@[j]));
                }
                assert(pre.can_add_device_at(root, slot, devices@, k as int));
                // A later device's slot is not device k's.
                assert forall|m: int| k + 1 <= m < count && #[trigger] pre.tables.has_slot(&pre.list, root, (slot + m) as usize) implies
                    self.list.nodes@[pre.tables.node_of(root, (slot + m) as usize) as int].live
                        == pre.list.nodes@[pre.tables.node_of(root, (slot + m) as usize) as int].live by {
                    let im = (slot + m) as usize;
                    Self::lemma_slot_stays(pre, before, root, im);
                    before.tables.lemma_slots_distinct(&before.list, root, i, root, im);
                    before.lemma_slot(root, im);
                    before.lemma_slot_bound(pre.tables.node_of(root, im));
                }
                assert forall|j: int| 0 <= j < k + 1 implies {
                    let m = pre.tables.node_of(root, (slot + j) as usize);
                    &&& #[trigger] self.devices.records@[j] == unbound_record(devices@[j])
                    &&& self.is_cap(m)
                    &&& self.payload_of(m) == device_payload(j)
                    &&& self.list.is_child(first, m)
                } by {
                    let m = pre.tables.node_of(root, (slot + j) as usize);
                    if j < k {
                        assert(before.devices.records@[j] == unbound_record(devices@[j]));
                        assert(before.is_cap(m));
                        assert(before.payload_of(m) == device_payload(j));
                        assert(m != n);
                        assert(self.is_cap(m));
                        assert(self.payload_of(m) == before.payload_of(m));
                        assert(self.list.is_child(first, m)) by {
                            assert(before.list.is_child(first, m));
                            assert(self.list.nodes@[m as int].live);
                            lemma_has(self.list.seq@, m);
                            assert(self.list.parent@[m] == before.list.parent@[m]);
                        }
                        assert(self.devices.records@[j] == before.devices.records@[j]);
                    } else {
                        assert(m == n);
                        assert(self.devices.records@[j] == unbound_record(devices@[j]));
                        assert(self.is_cap(m));
                        assert(self.payload_of(m) == device_payload(j));
                        assert(self.list.is_child(first, m));
                    }
                }
            }
            k = k + 1;
        }
        proof {
            assert(k * (MAX_DEVICES + 1) <= MAX_DEVICES * (MAX_DEVICES + 1)) by (nonlinear_arith)
                requires
                    k <= MAX_DEVICES,
            ;
        }
        true
    }

    /// Every device capability after the step was one before, saying the same.
    pub proof fn lemma_devices_same_caps(pre: Self, post: Self)
        requires
            devices_wf(&pre.list, &pre.tables, &pre.devices),
            post.devices == pre.devices,
            forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                ==> pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x),
            live_parents_kept(&pre.list, &post.list),
        ensures
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Device implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            assert(post.is_cap(x));
        }
        lemma_devices_kept(&pre.list, &pre.tables, &post.list, &post.tables, &pre.devices);
    }

    /// A step that adds at most one capability, not a device's, and changes no other.
    pub proof fn lemma_devices_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            devices_wf(&pre.list, &pre.tables, &pre.devices),
            post.devices == pre.devices,
            live_parents_kept(&pre.list, &post.list),
            post.is_cap(n) ==> !(post.payload_of(n).kind is Device),
            post.is_cap(m) ==> !(post.payload_of(m).kind is Device),
        ensures
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
            implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
            Self::lemma_caps_frame(pre, post, n, m, x);
        }
        Self::lemma_devices_same_caps(pre, post);
    }

    /// The list's first page, which holds the device binding nodes, is a page the list holds whose first
    /// node is the list's first, a live capability. So it is no leaf, and no node page of a table page or
    /// a device space, whose first node is hidden, a mapping or dead.
    pub proof fn lemma_first_page_apart(&self)
        requires
            self.wf(),
        ensures
            self.devices.page == self.list.seq@[0],
            self.devices.page % PAGE_SZ == 0,
            self.devices.page + PAGE_SZ <= NODE_SPACE,
            page_of(self.devices.page) == self.devices.page,
            self.list.pages@.dom().contains(self.devices.page),
            self.list.nodes@[self.devices.page as int].live,
            self.list.nodes@[self.devices.page as int].kind is Capability,
            !self.tables.owner@.contains_key(self.devices.page),
            forall|u: usize, k: usize| #![trigger table_node_page(u, k)]
                self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES ==> table_node_page(u, k) != self.devices.page,
            forall|s: usize, k: usize| #![trigger table_node_page(s, k)]
                self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
                ==> table_node_page(s, k) != self.devices.page,
    {
        reveal(devices_wf);
        let p = self.devices.page;
        assert(self.devices.wf());
        self.list.lemma_link(0);
        self.list.lemma_live_valid(p);
        assert(page_of(p) == p);
        assert forall|u: usize, k: usize| #![trigger table_node_page(u, k)]
            self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES implies table_node_page(u, k) != p by {
            if table_node_page(u, k) == p {
                self.lemma_table_node_in_block(u, k, 0);
                assert(table_node(u, k, 0) == p);
                if k == 0 {
                    assert(u == p);
                    assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, u));
                } else {
                    assert(self.list.nodes@[table_node(u, k, 0) as int].kind is Mapping);
                }
            }
        }
        assert forall|s: usize, k: usize| #![trigger table_node_page(s, k)]
            self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
            implies table_node_page(s, k) != p by {
            if table_node_page(s, k) == p {
                self.lemma_space_node_in_block(s, k, 0);
                assert(table_node(s, k, 0) == p);
                assert(!self.list.nodes@[table_node(s, k, 0) as int].live);
            }
        }
    }

    /// Device d's binding node lies in the list's first page, past its first node, so in no leaf, table
    /// page, thread, mapping or device space, and it is no capability: live, it is a device binding, and
    /// it is live only while its device is bound.
    pub proof fn lemma_binding_node_apart(&self, d: int)
        requires
            self.wf(),
            0 <= d < self.devices.count,
        ensures
            binding_node(&self.devices, d) < NODE_SPACE,
            binding_node(&self.devices, d) % PAGE_SZ == 1 + d,
            page_of(binding_node(&self.devices, d)) == self.devices.page,
            binding_device(&self.devices, binding_node(&self.devices, d)) == d,
            self.list.valid(binding_node(&self.devices, d)),
            binding_node(&self.devices, d) != self.list.seq@[0],
            !self.tables.owner@.contains_key(binding_node(&self.devices, d)),
            !self.tables.owner@.contains_key(page_of(binding_node(&self.devices, d))),
            !self.table_pages.maps@.contains_key(binding_node(&self.devices, d)),
            !self.threads.records@.contains_key(binding_node(&self.devices, d)),
            !self.mappings@.contains_key(binding_node(&self.devices, d)),
            !self.is_cap(binding_node(&self.devices, d)),
            self.list.nodes@[binding_node(&self.devices, d) as int].live
                ==> self.list.nodes@[binding_node(&self.devices, d) as int].kind is DeviceBinding,
            self.devices.records@[d].space is None ==> !self.list.nodes@[binding_node(&self.devices, d) as int].live,
            forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
                self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> table_node(u, k, i) != binding_node(&self.devices, d),
            forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
                self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device
                    && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> table_node(s, k, i) != binding_node(&self.devices, d),
    {
        reveal(devices_wf);
        self.lemma_first_page_apart();
        let p = self.devices.page;
        let x = binding_node(&self.devices, d);
        assert(self.devices.wf());
        assert(1 + d < NODES_PER_PAGE);
        assert(NODES_PER_PAGE < PAGE_SZ);
        assert(x == p + 1 + d);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(p as int, 1 + d, PAGE_SZ as int);
        vstd::arithmetic::div_mod::lemma_small_mod((1 + d) as nat, PAGE_SZ as nat);
        assert(x % PAGE_SZ == 1 + d);
        assert(page_of(x) == p);
        assert(self.list.valid(x));
        self.lemma_slot_not_owned(x);
        self.lemma_slot_not_table_page(x);
        if self.threads.records@.contains_key(x) {
            self.lemma_thread_node_apart(x);
        }
        assert forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
            self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            implies table_node(u, k, i) != x by {
            self.lemma_table_node_in_block(u, k, i);
            if table_node(u, k, i) == x {
                assert(table_node_page(u, k) == p);
            }
        }
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device
                && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            implies table_node(s, k, i) != x by {
            self.lemma_space_node_in_block(s, k, i);
            if table_node(s, k, i) == x {
                assert(table_node_page(s, k) == p);
            }
        }
        if self.mappings@.contains_key(x) {
            let r = self.mappings@[x];
            assert(mapping_wf(&self.list, &self.tables, tree_of(&self.table_pages, &self.spaces), &self.blocks, self.holders@, self.mappings@, x));
            self.lemma_table_page_room(r.table);
            lemma_mapping_node_place(r.table, r.entry);
            let k = ((r.entry + 1) / (NODES_PER_PAGE as int)) as usize;
            let i = ((r.entry + 1) % (NODES_PER_PAGE as int)) as usize;
            assert(table_node(r.table, k, i) == mapping_node(r.table, r.entry));
        }
        if self.list.nodes@[x as int].live {
            let kind = self.list.nodes@[x as int].kind;
            if kind is Capability {
                assert(self.tables.is_cap(&self.list, x));
            } else if kind is Hidden {
                assert(self.tables.owner@.contains_key(x) || self.table_pages.maps@.contains_key(x));
            } else if kind is Mapping {
                assert(self.mappings@.contains_key(x));
            } else if kind is Binding {
                reveal(thread_bound);
                assert(thread_bound(&self.threads, x));
            }
        }
        if self.devices.records@[d].space is None && self.list.nodes@[x as int].live {
            reveal(device_bindings_wf);
            assert(binding_device(&self.devices, x) == d);
        }
    }

    /// The refusals of bind: index i of the table at root must hold a device capability and index j a
    /// device space capability, below the depth limit, whose block can take one more reference; the
    /// device must be bound to nothing; and its IOMMU must be one the machine has, which acknowledged an
    /// invalidate started at or past the device's last unbind, so nothing it cached under the device's
    /// IOid from the space the device was bound to before survives. Both indices come from user space.
    /// See design/device-binding-under-the-space-capability/.
    pub open spec fn can_bind_device(&self, root: usize, i: usize, j: usize) -> bool {
        let n = self.tables.node_of(root, i);
        let m = self.tables.node_of(root, j);
        let r = self.devices.records@[device_of(self.payload_of(n).base)];
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Device
        &&& self.tables.has_slot(&self.list, root, j)
        &&& self.is_cap(m)
        &&& self.payload_of(m).kind is Space
        &&& self.list.nodes@[m as int].depth < MAX_DEPTH
        &&& block_refs(&self.blocks, BlockRef::Small(self.payload_of(m).base / PAGE_SZ)) != usize::MAX
        &&& r.space is None
        &&& self.iommu_present(r.iommu as int)
        &&& r.unbound <= self.iommu_acked(r.iommu as int)
    }

    /// Device d, bound to nothing, is bound to the device space capability m names: its binding node is
    /// a child of m, the space's block has one reference more, the space counts d among its bound
    /// devices, and d's record names the space. Nothing else changed.
    pub open spec fn device_bound(pre: Self, post: Self, m: usize, d: int) -> bool {
        let s = pre.payload_of(m).base;
        let br = BlockRef::Small(s / PAGE_SZ);
        let x = binding_node(&pre.devices, d);
        &&& 0 <= d < pre.devices.count
        &&& pre.devices.records@[d].space is None
        &&& post.list.wf()
        &&& post.list.is_child(m, x)
        &&& post.list.parent@ == pre.list.parent@.insert(x, m)
        &&& post.list.pages@.dom() == pre.list.pages@.dom()
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& !pre.list.nodes@[x as int].live
        &&& post.list.nodes@[x as int].live
        &&& post.list.nodes@[x as int].kind is DeviceBinding
        &&& forall|y: int| #![trigger post.list.nodes@[y]] 0 <= y < NODE_SPACE && y != x ==> {
            &&& post.list.nodes@[y].live == pre.list.nodes@[y].live
            &&& post.list.nodes@[y].kind == pre.list.nodes@[y].kind
        }
        &&& post.blocks.wf()
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        &&& post.spaces.roots == pre.spaces.roots
        &&& post.spaces.records == pre.spaces.records
        &&& post.spaces.loaded == pre.spaces.loaded
        &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
        &&& post.spaces.holders == pre.spaces.holders
        &&& post.spaces.bound@ == pre.spaces.bound@.insert(s, pre.spaces.bound@[s].insert(d as usize))
        &&& post.devices.wf()
        &&& post.devices.count == pre.devices.count
        &&& post.devices.page == pre.devices.page
        &&& post.devices.holder == pre.devices.holder
        &&& post.devices.records@ == pre.devices.records@.update(d, bound_record(pre.devices.records@[d], s))
        &&& post.holders == pre.holders
        &&& post.tables == pre.tables
        &&& post.frames == pre.frames
        &&& post.zeroing == pre.zeroing
        &&& post.cores == pre.cores
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.table_pages == pre.table_pages
        &&& post.mappings == pre.mappings
        &&& post.stop_ipis == pre.stop_ipis
        &&& post.flush_ipis == pre.flush_ipis
    }

    /// The kinds of node after a bind: the new node is a device binding, outside every leaf, table page
    /// and device space, so no clause about capability, hidden, table or space nodes changes.
    proof fn lemma_bind_device_nodes(pre: Self, post: Self, m: usize, d: int)
        requires
            pre.wf(),
            pre.is_cap(m),
            Self::device_bound(pre, post, m, d),
        ensures
            forall|y: usize| #[trigger] post.is_cap(y) == pre.is_cap(y),
            Self::caps_frame(pre, post, binding_node(&pre.devices, d), binding_node(&pre.devices, d)),
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
            table_nodes_are_mappings(&post.list, &post.table_pages),
            space_nodes_dead(&post.list, &post.spaces),
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        let x = binding_node(&pre.devices, d);
        pre.lemma_binding_node_apart(d);
        pre.lemma_slot_bound(m);
        assert(Self::caps_frame(pre, post, x, x));
        assert forall|y: usize| #[trigger] post.is_cap(y) == pre.is_cap(y) by {
            if y == x {
                assert(!(post.list.nodes@[y as int].kind is Capability));
            } else {
                Self::lemma_caps_frame(pre, post, x, x, y);
            }
        }
        pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
        assert forall|y: usize| #[trigger] post.tables.is_cap(&post.list, y)
            implies cap_wf(post.tables.payload_of(y)) by {
            assert(pre.tables.is_cap(&pre.list, y));
        }
        assert forall|y: usize| y < NODE_SPACE && (#[trigger] post.list.nodes@[y as int]).live && post.list.nodes@[y as int].kind is Hidden
            implies post.tables.owner@.contains_key(y) || post.table_pages.maps@.contains_key(y) by {
            assert(y != x);
            assert(pre.list.nodes@[y as int].live && pre.list.nodes@[y as int].kind is Hidden);
        }
        lemma_parents_derived(pre.list, post.list, m, x);
        assert forall|y: usize| y < NODE_SPACE && (#[trigger] post.list.nodes@[y as int]).live && post.list.nodes@[y as int].kind is Capability
            && y != post.list.seq@[0] implies post.tables.is_cap(&post.list, y) by {
            assert(y != x);
            assert(pre.list.nodes@[y as int].live && pre.list.nodes@[y as int].kind is Capability);
            assert(pre.tables.is_cap(&pre.list, y));
        }
        assert forall|y: usize| #[trigger] post.list.nodes@[y as int].live && post.tables.owner@.contains_key(page_of(y))
            && y % PAGE_SZ != 0 && y % PAGE_SZ < NODES_PER_PAGE implies post.list.nodes@[y as int].kind is Capability by {
            assert(y != x);
            pre.lemma_slot_bound(y);
            assert(pre.list.nodes@[y as int].live);
        }
        assert forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
            post.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
                && post.list.nodes@[table_node(u, k, i) as int].live
            implies post.list.nodes@[table_node(u, k, i) as int].kind is Mapping by {
            pre.lemma_table_node_in_block(u, k, i);
            assert(table_node(u, k, i) != x);
        }
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
                && i < NODES_PER_PAGE
            implies !post.list.nodes@[table_node(s, k, i) as int].live by {
            pre.lemma_space_node_in_block(s, k, i);
            assert(table_node(s, k, i) != x);
        }
        assert forall|y: usize| #[trigger] post.tables.is_cap(&post.list, y) && post.tables.payload_of(y).kind is Device implies {
            &&& pre.tables.is_cap(&pre.list, y)
            &&& pre.tables.payload_of(y) == post.tables.payload_of(y)
        } by {
            assert(post.is_cap(y));
        }
        assert forall|y: usize| y < NODE_SPACE && pre.list.nodes@[y as int].live && #[trigger] pre.list.parent@.contains_key(y)
            implies post.list.parent@.contains_key(y) && post.list.parent@[y] == pre.list.parent@[y] by {
            assert(y != x);
        }
        lemma_devices_kept(&pre.list, &pre.tables, &post.list, &post.tables, &pre.devices);
        lemma_devices_records(&post.list, &post.tables, &pre.devices, &post.devices);
    }

    /// The counted parts after a bind: the space's block has one reference more, counted among its bound
    /// devices, and no capability, holder, leaf, table page, thread, process or mapping changed.
    proof fn lemma_bind_device_objects(pre: Self, post: Self, m: usize, d: int)
        requires
            pre.wf(),
            pre.is_cap(m),
            pre.payload_of(m).kind is Space,
            block_refs(&pre.blocks, BlockRef::Small(pre.payload_of(m).base / PAGE_SZ)) != usize::MAX,
            Self::device_bound(pre, post, m, d),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
            bindings_wf(&post.list, &post.threads, &post.processes),
            current_wf(post.cores@, post.threads.records@),
    {
        let s = pre.payload_of(m).base;
        let br = BlockRef::Small(s / PAGE_SZ);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        let x = binding_node(&pre.devices, d);
        Self::lemma_bind_device_nodes(pre, post, m, d);
        pre.lemma_binding_node_apart(d);
        pre.lemma_space_cap(m);
        assert forall|y: usize| y != x implies {
            &&& #[trigger] post.tables.is_cap(&post.list, y) == pre.tables.is_cap(&pre.list, y)
            &&& pre.tables.is_cap(&pre.list, y) ==> post.tables.payload_of(y) == pre.tables.payload_of(y)
        } by {
            Self::lemma_caps_frame(pre, post, x, x, y);
        }
        assert(!pre.is_cap(x));
        assert(!post.is_cap(x));
        assert forall|y: usize| #[trigger] post.tables.is_cap(&post.list, y) == pre.tables.is_cap(&pre.list, y) by {
            assert(post.is_cap(y) == pre.is_cap(y));
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_processes(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        assert(!pre.holders@.contains_key(br)) by {
            if pre.holders@.contains_key(br) {
                assert(pre.blocks.pages@[(s / PAGE_SZ) as int].object is Frame);
            }
        }
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / PAGE_SZ, refs, dead);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / PAGE_SZ, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            pre.lemma_slot_bound(l);
            assert(l != x);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
        assert forall|u: usize| #[trigger] pre.table_pages.maps@.contains_key(u) implies {
            &&& post.list.nodes@[u as int].live == pre.list.nodes@[u as int].live
            &&& post.list.nodes@[u as int].kind == pre.list.nodes@[u as int].kind
        } by {
            pre.lemma_table_page_valid(u);
            assert(u != x);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        assert(!pre.spaces.bound@[s].contains(d as usize)) by {
            reveal(device_bindings_wf);
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            if pre.spaces.bound@[s].contains(d as usize) {
                assert(pre.devices.records@[d].space == Some(s));
            }
        }
        Self::lemma_spaces_bound_added(pre, post, s, d as usize);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
            let c = pre.list.parent@[n];
            assert(n != x);
            assert(c != x);
            Self::lemma_caps_frame(pre, post, x, x, c);
        }
        assert(Self::same_tree(pre, post));
        Self::lemma_mappings_same_tree(pre, post);
        assert forall|y: usize| y < NODE_SPACE implies ((#[trigger] post.list.nodes@[y as int]).live && post.list.nodes@[y as int].kind is Binding)
            == (pre.list.nodes@[y as int].live && pre.list.nodes@[y as int].kind is Binding) by {
            if y != x {
                assert(post.list.nodes@[y as int].live == pre.list.nodes@[y as int].live);
            }
        }
        lemma_bindings_same(&pre.list, &post.list, &pre.threads, &pre.processes);
    }

    /// The device bindings after a bind: the new binding node is device d's, below a capability to the
    /// space its record now names, which counts d among its bound devices; every other binding, record
    /// and bound set is as it was.
    proof fn lemma_bind_device_bindings(pre: Self, post: Self, m: usize, d: int)
        requires
            pre.wf(),
            pre.is_cap(m),
            pre.payload_of(m).kind is Space,
            Self::device_bound(pre, post, m, d),
        ensures
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        reveal(device_bindings_wf);
        let x = binding_node(&pre.devices, d);
        let s = pre.payload_of(m).base;
        let ba = pre.spaces.bound@;
        let bb = post.spaces.bound@;
        Self::lemma_bind_device_nodes(pre, post, m, d);
        pre.lemma_binding_node_apart(d);
        pre.lemma_space_cap(m);
        assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        assert(ba.contains_key(s));
        assert(post.is_cap(m));
        assert(bb[s] == ba[s].insert(d as usize));
        assert forall|y: usize| y < NODE_SPACE && (#[trigger] post.list.nodes@[y as int]).live && post.list.nodes@[y as int].kind is DeviceBinding implies {
            let e = binding_device(&post.devices, y);
            &&& 0 <= e < post.devices.count
            &&& post.devices.records@[e].space is Some
            &&& device_binding_parent(&post.list, &post.tables, y, post.devices.records@[e].space->Some_0)
        } by {
            if y == x {
                assert(binding_device(&post.devices, y) == d);
                assert(post.devices.records@[d] == bound_record(pre.devices.records@[d], s));
                assert(post.list.parent@[x] == m);
            } else {
                assert(pre.list.nodes@[y as int].live && pre.list.nodes@[y as int].kind is DeviceBinding);
                let e = binding_device(&pre.devices, y);
                assert(pre.devices.records@[e].space is Some);
                assert(e != d);
                assert(post.devices.records@[e] == pre.devices.records@[e]);
                let a = pre.list.parent@[y];
                assert(device_binding_parent(&pre.list, &pre.tables, y, pre.devices.records@[e].space->Some_0));
                assert(pre.is_cap(a));
                assert(post.is_cap(a));
                assert(post.list.parent@[y] == a);
            }
        }
        assert forall|e: int| 0 <= e < post.devices.count && (#[trigger] post.devices.records@[e]).space is Some implies {
            let y = binding_node(&post.devices, e);
            let t = post.devices.records@[e].space->Some_0;
            &&& y < NODE_SPACE
            &&& post.list.nodes@[y as int].live
            &&& post.list.nodes@[y as int].kind is DeviceBinding
            &&& bb.contains_key(t)
            &&& bb[t].contains(e as usize)
        } by {
            if e != d {
                assert(post.devices.records@[e] == pre.devices.records@[e]);
                assert(pre.devices.records@[e].space is Some);
                let y = binding_node(&pre.devices, e);
                let t = pre.devices.records@[e].space->Some_0;
                assert(pre.list.nodes@[y as int].live);
                assert(y != x);
                assert(ba[t].contains(e as usize));
                if t == s {
                    assert(bb[s].contains(e as usize));
                } else {
                    assert(bb[t] == ba[t]);
                }
            }
        }
        assert forall|t: usize, e: usize| bb.contains_key(t) && #[trigger] bb[t].contains(e)
            implies e < post.devices.count && post.devices.records@[e as int].space == Some(t) by {
            if t == s {
                if e as int != d {
                    assert(ba[s].contains(e));
                    assert(pre.devices.records@[e as int].space == Some(s));
                    assert(post.devices.records@[e as int] == pre.devices.records@[e as int]);
                }
            } else {
                assert(bb[t] == ba[t]);
                assert(ba.contains_key(t) && ba[t].contains(e));
                assert(pre.devices.records@[e as int].space == Some(t));
                assert(e as int != d);
                assert(post.devices.records@[e as int] == pre.devices.records@[e as int]);
            }
        }
    }

    /// Everything the invariant says after a bind. The device's IOMMU is present and acknowledged its
    /// last unbind, as devices_placed asks of a bound device.
    proof fn lemma_bind_device_wf(pre: Self, post: Self, m: usize, d: int)
        requires
            pre.wf(),
            pre.is_cap(m),
            pre.payload_of(m).kind is Space,
            block_refs(&pre.blocks, BlockRef::Small(pre.payload_of(m).base / PAGE_SZ)) != usize::MAX,
            pre.iommu_present(pre.devices.records@[d].iommu as int),
            pre.devices.records@[d].unbound <= pre.iommu_acked(pre.devices.records@[d].iommu as int),
            Self::device_bound(pre, post, m, d),
        ensures
            post.wf(),
    {
        let x = binding_node(&pre.devices, d);
        Self::lemma_bind_device_nodes(pre, post, m, d);
        Self::lemma_bind_device_objects(pre, post, m, d);
        Self::lemma_bind_device_bindings(pre, post, m, d);
        pre.lemma_binding_node_apart(d);
        assert forall|t: usize| t < NODE_SPACE && (#[trigger] post.list.nodes@[t as int]).live && post.list.nodes@[t as int].kind is Binding
            implies pre.list.nodes@[t as int].live && pre.list.nodes@[t as int].kind is Binding by {
            assert(t != x);
        }
        assert forall|y: usize| y < NODE_SPACE && pre.list.nodes@[y as int].live && #[trigger] pre.list.parent@.contains_key(y)
            implies post.list.parent@.contains_key(y) && post.list.parent@[y] == pre.list.parent@[y] by {
            assert(y != x);
        }
        assert forall|y: usize| #[trigger] pre.tables.is_cap(&pre.list, y) && pre.tables.payload_of(y).kind is Process implies {
            &&& post.tables.is_cap(&post.list, y)
            &&& post.tables.payload_of(y) == pre.tables.payload_of(y)
        } by {
            assert(pre.is_cap(y));
            assert(post.is_cap(y));
        }
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|e: int| 0 <= e < post.devices.count && (#[trigger] post.devices.records@[e]).space is Some implies {
            &&& post.iommus.present@[post.devices.records@[e].iommu as int]
            &&& post.devices.records@[e].unbound <= post.iommus.acked@[post.devices.records@[e].iommu as int]
        } by {
            if e != d {
                assert(post.devices.records@[e] == pre.devices.records@[e]);
            }
        }
        assert(tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces));
        Self::lemma_tlb_same(pre, post);
        assert(process_tables_wf(&post.tables, &post.processes));
        assert(process_spaces_wf(&post.spaces, &post.processes));
        assert(post.frames_wf());
    }

    /// Binds the device whose capability is at index i of the table at root to the device space whose
    /// capability is at index j: the device's binding node, in the list's first page, becomes a child of
    /// the space capability, holding a reference on the space's block, the space counts the device among
    /// its bound devices, the device's record names the space, and the view's binds gain the device bound
    /// to the space and nothing else. The caller holds the device's only capability, so no one else gains
    /// a reach. Writing the IOMMU's device table entry is the glue's, on success. See
    /// design/device-binding-under-the-space-capability/.
    pub fn bind_device(&mut self, root: usize, i: usize, j: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret == old(self).can_bind_device(root, i, j),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::device_bound(
                *old(self),
                *final(self),
                old(self).tables.node_of(root, j),
                device_of(old(self).payload_of(old(self).tables.node_of(root, i)).base),
            ),
            ret ==> final(self).view().binds == old(self).view().binds.insert(
                old(self).payload_of(old(self).tables.node_of(root, i)).base,
                old(self).payload_of(old(self).tables.node_of(root, j)).base,
            ),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, device) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return false; },
        };
        let node = self.list.get(n);
        let live_device = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_device {
            return false;
        }
        proof {
            pre.lemma_slot(root, i);
            assert(pre.tables.is_cap(&pre.list, n));
            assert(device == pre.payload_of(n));
        }
        let is_device = match device.kind {
            CapKind::Device => true,
            _ => false,
        };
        if !is_device {
            return false;
        }
        let (m, space) = match self.tables.lookup(&self.list, root, j) {
            Some(found) => found,
            None => { return false; },
        };
        let space_node = self.list.get(m);
        let live_space = match space_node.kind {
            NodeKind::Capability => space_node.live,
            _ => false,
        };
        if !live_space {
            return false;
        }
        proof {
            pre.lemma_slot(root, j);
            assert(pre.tables.is_cap(&pre.list, m));
            assert(space == pre.payload_of(m));
        }
        let is_space = match space.kind {
            CapKind::Space => true,
            _ => false,
        };
        if !is_space || space_node.depth >= MAX_DEPTH {
            return false;
        }
        proof {
            reveal(devices_wf);
            assert(pre.devices.wf());
            assert(pre.devices.names(device.base));
            pre.lemma_space_cap(m);
        }
        let s = space.base;
        if self.blocks.pages.get(s / PAGE_SZ).refs == usize::MAX {
            return false;
        }
        let d = (device.base - DEVICE_OBJECTS) / PAGE_SZ;
        proof {
            assert(d as int == device_of(device.base));
            assert(d < pre.devices.count);
            assert(pre.devices.records@[d as int].iommu < NUM_IOMMUS);
        }
        let record = *self.devices.records.get(d);
        match record.space {
            Some(_) => { return false; },
            None => {},
        }
        if !*self.iommus.present.get(record.iommu) || *self.iommus.acked.get(record.iommu) < record.unbound {
            return false;
        }
        proof {
            pre.lemma_binding_node_apart(d as int);
            pre.list.lemma_seq_fits();
            pre.lemma_slot_bound(m);
        }
        let added = add_block_ref(&mut self.blocks, BlockRef::Small(s / PAGE_SZ));
        assert(added);
        let x = self.devices.page + 1 + d;
        self.list.derive(m, x, NodeKind::DeviceBinding);
        self.spaces.bound = Ghost(pre.spaces.bound@.insert(s, pre.spaces.bound@[s].insert(d)));
        self.devices.bind(d, s);
        proof {
            let post = *self;
            assert(Self::device_bound(pre, post, m, d as int));
            Self::lemma_bind_device_wf(pre, post, m, d as int);
            let (pv, sv) = (post.view(), pre.view());
            let o = device.base;
            assert((o - DEVICE_OBJECTS) % (PAGE_SZ as int) == 0);
            assert(o == device_object(d as int));
            lemma_device_object(d as int);
            // The binds gain o, bound to s, and nothing else.
            assert forall|y: ObjectId| #[trigger] pre.devices.names(y) implies y == device_object(device_of(y)) by {
                assert((y - DEVICE_OBJECTS) % (PAGE_SZ as int) == 0);
            }
            assert forall|y: ObjectId| #[trigger] pv.binds.contains_key(y) == sv.binds.insert(o, s).contains_key(y) by {
                if y != o && pre.devices.names(y) {
                    assert(device_of(y) != d as int);
                }
            }
            assert forall|y: ObjectId| #[trigger] pv.binds.contains_key(y) implies pv.binds[y] == sv.binds.insert(o, s)[y] by {
                if y != o {
                    assert(device_of(y) != d as int);
                }
            }
            assert(pv.binds =~= sv.binds.insert(o, s));
            // Only root reaches the device directly, and root holds the space capability.
            assert(pre.devices.holder@[o] == n);
            assert(sv.holds(root, n));
            assert(sv.holds(root, m));
            vstd::arithmetic::power2::lemma_pow2_pos(pre.payload_of(m).order as nat);
            vstd::arithmetic::div_mod::lemma_mod_mod(s as int, PAGE_SZ as int, 8);
            assert(sv.covers(m, s));
            assert(sv.descends(m, m, 0));
            assert(sv.direct(root, s));
            assert forall|q: ObjectId| #[trigger] sv.direct(q, o) implies sv.sees(q, s) by {
                pre.lemma_direct_device_held(q, d as int);
                assert(q == root);
            }
            Self::lemma_binding_added_discharges(pre, post, root, m, x, o, s);
        }
        true
    }

    /// A bound device's space is a live device space whose block its binding holds a reference on, so
    /// no device is bound to a freed table; its IOMMU is one the machine has and acknowledged the
    /// device's last unbind; and no other device has its IOMMU and IOid.
    pub proof fn lemma_bound_device(&self, d: int)
        requires
            self.wf(),
            0 <= d < self.devices.count,
            self.devices.records@[d].space is Some,
        ensures
            self.spaces.roots@.contains_key(self.devices.records@[d].space->Some_0),
            self.spaces.records@[self.devices.records@[d].space->Some_0].value().kind is Device,
            block_typed(&self.blocks, BlockRef::Small(self.devices.records@[d].space->Some_0 / PAGE_SZ)),
            block_refs(&self.blocks, BlockRef::Small(self.devices.records@[d].space->Some_0 / PAGE_SZ)) > 0,
            self.devices.records@[d].iommu < NUM_IOMMUS,
            self.iommu_present(self.devices.records@[d].iommu as int),
            self.devices.records@[d].unbound <= self.iommu_acked(self.devices.records@[d].iommu as int),
            forall|e: int| 0 <= e < self.devices.count && e != d ==> #[trigger] self.devices.distinct(d, e),
    {
        reveal(device_bindings_wf);
        reveal(devices_wf);
        let x = binding_node(&self.devices, d);
        let s = self.devices.records@[d].space->Some_0;
        assert(x < NODE_SPACE);
        assert(self.list.nodes@[x as int].live && self.list.nodes@[x as int].kind is DeviceBinding);
        self.lemma_binding_node_apart(d);
        assert(device_binding_parent(&self.list, &self.tables, x, s));
        self.lemma_space_cap(self.list.parent@[x]);
        assert forall|e: int| 0 <= e < self.devices.count && e != d implies #[trigger] self.devices.distinct(d, e) by {
            assert(self.devices.records@[d] == self.devices.records@[d]);
            assert(self.devices.records@[e] == self.devices.records@[e]);
        }
    }
}

} // verus!
