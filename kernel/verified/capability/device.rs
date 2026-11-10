//! Devices. A device is boot-sized and never retyped, so the table of them is filled once, at boot, from what
//! the boot glue found, and each device gets one capability under the list's first node. A device is bound to
//! one space at a time, so its capability moves and is never derived: at most one capability names a device.
//! A device's IOid on its IOMMU is its device number, fixed, so nothing allocates one. See
//! design/sharing-by-derive/, design/capability-names-a-block/ and design/address-spaces-as-objects/.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::mapping::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::process::*;
use crate::capability::thread::*;
use crate::define::*;

/// The most devices the table holds.
pub const MAX_DEVICES: usize = 128;

/// How many device numbers an IOMMU has: a DeviceID is 16 bits. AMD IOMMU specification 48882 §2.2.
pub const IOMMU_DEVICES: usize = 0x10000;

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
    /// The node of the capability each device object was given at boot. A device capability is the
    /// one its object's entry names, so at most one names each device.
    pub holder: Ghost<Map<usize, usize>>,
}

/// A device's record before anything binds it.
pub open spec fn unbound_record(info: DeviceInfo) -> DeviceRecord {
    DeviceRecord { iommu: info.iommu, number: info.number, space: None, unbound: 0 }
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
        device_object(d) % 4096 == 0,
        device_of(device_object(d)) == d,
{
    assert(DEVICE_OBJECTS % 4096 == 0);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(d, DEVICE_OBJECTS as int, 4096);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(d, 4096);
}

/// The device whose object o is.
pub open spec fn device_of(o: usize) -> int {
    (o - DEVICE_OBJECTS) / 4096
}

impl Devices {
    pub fn new() -> (ret: Self)
        ensures
            ret.wf(),
            ret.count == 0,
            ret.holder@ == Map::<usize, usize>::empty(),
    {
        Devices { records: Array::new(), count: 0, holder: Ghost(Map::empty()) }
    }

    /// Records d and e are on different IOMMUs or have different numbers.
    pub open spec fn distinct(&self, d: int, e: int) -> bool {
        self.records@[d].iommu != self.records@[e].iommu || self.records@[d].number != self.records@[e].number
    }

    /// Each record names an IOMMU and a device number on it, and no two name the same.
    pub open spec fn wf(&self) -> bool {
        &&& self.records.wf()
        &&& self.count <= MAX_DEVICES
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
    pub fn recorded(&self, info: DeviceInfo) -> (ret: bool)
        requires
            self.wf(),
        ensures
            ret == !self.fresh(info),
    {
        let mut e = 0;
        while e < self.count
            invariant
                self.wf(),
                0 <= e <= self.count,
                forall|d: int| 0 <= d < e ==>
                    (#[trigger] self.records@[d]).iommu != info.iommu || self.records@[d].number != info.number,
            decreases self.count - e,
        {
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
        &&& o % 4096 == 0
        &&& device_of(o) < self.count
    }
}

/// Every device capability names one device, a record of the table, and is the one that device was
/// given. Opaque, so
/// a step that leaves the list, the tables and the devices alone carries it without unfolding it.
#[verifier::opaque]
pub open spec fn devices_wf(list: &Tree, tables: &Tables, devices: &Devices) -> bool {
    &&& devices.wf()
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Device ==> {
        &&& tables.payload_of(n).order == 0
        &&& devices.names(tables.payload_of(n).base)
        &&& devices.holder@.contains_key(tables.payload_of(n).base)
        &&& devices.holder@[tables.payload_of(n).base] == n
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

pub proof fn lemma_devices_kept(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables, devices: &Devices)
    requires
        devices_wf(list_a, tables_a, devices),
        devices_kept(list_a, tables_a, list_b, tables_b),
    ensures
        devices_wf(list_b, tables_b, devices),
{
    reveal(devices_wf);
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Device implies {
        &&& tables_b.payload_of(n).order == 0
        &&& devices.names(tables_b.payload_of(n).base)
        &&& devices.holder@.contains_key(tables_b.payload_of(n).base)
        &&& devices.holder@[tables_b.payload_of(n).base] == n
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

impl CapKernel {
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

    /// Records a device boot found and puts its capability at index `slot` of the table at root, a
    /// child of the list's first node. A refusal changes nothing.
    pub fn add_device(&mut self, first: usize, root: usize, slot: usize, info: DeviceInfo) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            first == old(self).list.seq@[0],
        ensures
            final(self).wf(),
            ret == old(self).can_add_device(root, slot, info),
            !ret ==> *final(self) == *old(self),
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.seq@[0] == old(self).list.seq@[0],
            ret ==> final(self).list.parent@ == old(self).list.parent@.insert(old(self).tables.node_of(root, slot), first),
            ret ==> {
                let n = old(self).tables.node_of(root, slot);
                let d = old(self).devices.count;
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
            || self.devices.recorded(info) {
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
        let payload = Payload { kind: CapKind::Device, order: 0, rights: DEVICE_RIGHTS, base: DEVICE_OBJECTS + d * 4096, badge: 0, reserved: 0 };
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
            child % 4096 != 0,
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
        } by {
            if x != child {
                Self::lemma_caps_frame(pre, post, child, child, x);
                assert(pre.tables.is_cap(&pre.list, x));
                assert(device_of(pre.payload_of(x).base) < d);
            }
        }
    }

    /// Gives each device boot found a record and a capability under the list's first node, device k
    /// at index slot + k of the table at root. Boot fills the table once, and it stops at the first
    /// device refused, so false means boot fails.
    pub fn add_devices(&mut self, first: usize, root: usize, slot: usize, devices: &Array<DeviceInfo, MAX_DEVICES>, count: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            first == old(self).list.seq@[0],
            old(self).devices.count == 0,
            devices.wf(),
            count <= MAX_DEVICES,
            slot + count <= usize::MAX,
        ensures
            final(self).wf(),
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
        let mut k = 0;
        while k != count
            invariant
                self.wf(),
                0 <= k <= count,
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
            decreases count - k,
        {
            let ghost before = *self;
            let info = *devices.get(k);
            if !self.add_device(first, root, slot + k, info) {
                return false;
            }
            proof {
                // The records' length, for the update.
                reveal(devices_wf);
                let n = pre.tables.node_of(root, (slot + k) as usize);
                assert(before.tables.node_of(root, (slot + k) as usize) == n);
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
        true
    }

    /// Every device capability after the step was one before, saying the same.
    pub proof fn lemma_devices_same_caps(pre: Self, post: Self)
        requires
            devices_wf(&pre.list, &pre.tables, &pre.devices),
            post.devices == pre.devices,
            forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                ==> pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x),
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
}

} // verus!
