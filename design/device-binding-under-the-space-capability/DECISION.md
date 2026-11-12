---
title: "A device's binding to its device space is a node of the device's, under the space capability that bound it"
date: 2026-11-10
status: active
tags: [capability, device, iommu, reach, verified]
one_line: "Each device has one binding node, a slot of the list's first node page past the list's first node, live exactly while the device is bound. Bind names a device capability and a device space capability in the caller's table and derives the node under the space capability, holding one of the space block's references, so revoking that capability's lineage unbinds the device and delete of it is refused while bound. The binder is the device's only holder, since a device capability does not derive, and every holder of a device space capability reaches what the space maps, so bind grows no reach; moving a bound device grants what its space maps, and mapping into a device space is a grant by the mapper."
revisit_if: "A device must be bound to two spaces at once (PASID-tagged DMA, where one device walks several tables), which one binding node per device cannot express; or a device capability must derive, which ends the sole-holder argument and makes bind a growth the theorem does not admit."
confidence: "The node's place, the invariant tying it to the device's record and the space's bound set, bind with its refusals, revoke's unbind and the explicit unbind through the device capability are proven in kernel/verified/capability/device.rs and revoke.rs, bind and the explicit unbind discharging the reach lemma as local steps, and a bind straight after an unbind shown refused until the IOMMU acknowledges. The sole holder is proven too: devices_wf keeps each device capability a child of the list's first node, which nobody holds, and lemma_direct_device_held in kernel/verified/capability/view.rs shows that only its holder reaches the device directly. That bind grows no reach is arithmetic on the model once a device space's holders reach what it maps; choosing that reading over a narrower one is judgement, argued below."
---

# A device's binding hangs under the device space capability

## Decision

A device is boot-sized and never retyped, and each device has one binding node fixed at boot: device d's is the node 1 + d past the list's first node, in the node page that holds it, so the device table holds at most one page's nodes less one devices (`MAX_DEVICES` in `kernel/verified/capability/device.rs`). The node is live exactly while the device is bound. Bind names, as indices into the caller's table, a device capability and a device space capability. Both indices come from user space, and bind is refused, changing nothing, exactly when one of these holds (`can_bind_device` in `kernel/verified/capability/device.rs`):

- the first index names no slot of the caller's table, or a slot holding no capability, or a capability that is not a device's;
- the second index names no slot of the caller's table, or a slot holding no capability, or a capability that is not a device space's;
- the space capability is at the deepest depth, `MAX_DEPTH`, since the binding node is its child one depth below and depth is a byte, as for any derive, `design/sharing-by-derive/`;
- the space's block already holds as many references as its count can record, since the binding takes one more, as a derive of a space capability is refused at the same count;
- the device is bound already;
- the device's IOMMU is not one the machine has;
- the device's IOMMU has not acknowledged an invalidate started at or past the epoch of the device's last unbind, since a rebind repeats the device's IOid, `design/address-spaces-as-objects/`, and entries cached under the old table must not serve the new one, `design/flush-without-waiting/`.

On success the binding node is derived as a leaf child of the named space capability, the space's block gains one reference, which `kernel/verified/capability/space.rs` `space_wf` counts beside the space capabilities, the device joins the space's bound set, and the device's record names the space. Two devices bound to one space tag their translations under two IOids, each its device number on its IOMMU. A process's own space has no space capability, `design/process-holds-capabilities/`, so bind cannot name one: a device reaches a process's memory through a device space that maps the same frames.

Unbinding undoes all of that, reached two ways: explicitly through the device capability, or by revoking a lineage that contains the space capability, whose revoke reaches the binding node like any other child, `design/revoke-by-depth-first-list/`. Delete of the space capability is refused while the binding stands, as for any capability with a child, `design/sharing-by-derive/`. An IOMMU may cache a walk from the space's root while the device is bound, and a root has no parent entry whose cut would record it stale, so unbind records the root's block stale and bumps the flush epoch, and the space's free waits for the IOMMUs' acknowledgement. The device's record keeps the epoch of its unbind for the next bind's refusal. Writing the IOMMU's device table entry is the IOMMU driver's, unverified machine glue (`design/machine-glue-below-the-kernel/`), called on the proven decision's success.

Reach reads the binding. Every holder of a capability covering a device space reaches what the space maps, and so does the holder of each device bound to it: the space is one of their address spaces in the sense of `design/theorem-over-reach/`. With that reading every device operation keeps the theorem's wording, `design/thread-bound-at-retype/`: reach grows only by a grant from a holder or a retype from an untyped held.

- Bind grows nobody's reach. A device capability does not derive, so the binder is the device's only holder, and the binder holds the space capability, so it reached what the space maps before the step. This is the sole-holder form of `design/thread-bound-at-retype/`, the one that record keeps for an object that exists before the authority it is bound to.
- Moving a bound device to another process, by a placement or a claim, keeps the binding, so the receiver gains what the space maps: a grant by the mover, who reached it. A claim is through control, so the claimer reached it already.
- Mapping a frame into a device space, which takes the space capability's write right, grants the frame to everyone who reaches what the space maps. The mapper holds the frame, so it is a grant from a holder, like a send whose receiver the sender does not pick.
- Unbinding and revoking only shrink reach.

## Context

A device has one IO table and its capability moves, never derives, so at most one capability names it; that landed with the device table. What was open was where the binding lives and what it means: the general rule says a binding is a node, a leaf child of the capability used to make it, stored in the object doing the holding, and a device is bound with two capabilities, its own and the space's. A device exists from boot, before any space it could be bound to, so the construction form a thread uses does not fit, and reach had not said whether it reads a device's space.

## Reasoning

Under the space capability, because that is the authority the binding uses up. The binding holds one of the space block's references; the space capability's holder is who must be able to take it back, or a device's holder could keep a space alive, and DMA into whatever it maps, against the wishes of whoever made the space. Revoke is how a holder takes back everything below a capability, so the binding has to be below it. The device's own capability is the other parent a binding could have, and it is the wrong one: it is at depth one under the list's first node and moves, so revoking it is not something the space's holder can do.

In the device's record, because the device does the holding. A device space's node pages hold no live node, `kernel/verified/capability/kernel.rs` `space_nodes_dead`: a mapping's node lies in its own table page's node pages and a root maps no frame. Reclaiming a dead device space relies on that instead of walking its node pages. A binding node in the list's first page keeps that invariant as it stands, and a dead space has nothing bound, since a binding holds a reference. One node per device, fixed at boot, also means bind allocates nothing, so it cannot fail for want of a node and cannot be used to exhaust one.

Reading a device space's holders as reaching what it maps is the reading that makes bind local. The narrower reading, only a bound device's holder reaches the space's frames, leaves a holder of a derived space capability able to bind a device it holds and gain frames another holder mapped, by its own act and without a grant: the sideways growth `design/thread-bound-at-retype/` rules out. Under the wider reading that holder reached those frames already, which matches what its capability lets it do; the cost is that reach over-approximates for a holder with no device to bind, as it does for every latent authority.

## Alternatives rejected

- **The binding under the device capability.** Revoking the space capability would not reach it, so the space's holder could not withdraw the device or free the space while the device's holder kept it bound.
- **The binding node in the space's node pages.** A space would need a node for every device that might bind it, or bind would allocate one; and a dead space's node pages would no longer be free of live nodes, which its reclaim relies on.
- **A field in the device's record with no node.** Revoke walks the list and would not find it, so revoking the space capability could not unbind the device, and delete of the space capability would not be refused while bound.
- **Bind through the space capability alone.** Binding uses the device's one IO table, which is its holder's to give; without the device capability any space holder could steer a device it does not hold.
- **A derivable device capability.** A device has one IO table, so its holders would contend for it, and a bind would grow the reach of every other holder by one holder's act.
- **Only a bound device's holder reaches the space's frames.** See above: bind would be a growth without a grant.

## What this does not settle

- Which argument words of the bind and unbind calls carry the two indices.
- Interrupts from a device: how its MSIs are remapped and delivered, and whether that is a second binding.
- A device bound to more than one space at once, named in `revisit_if`.
