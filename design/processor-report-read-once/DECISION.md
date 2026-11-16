---
title: "A core reads what its processor reports once, at its own boot, and the flushes and the PCID branch take that value"
date: 2026-11-16
status: active
tags: [arch, tlb, boot, verified]
one_line: "Each core, in its own boot, reads the features its processor reports into an exec value of the arch module held in that core's Cpu block and passed into the flush; where the value reports INVPCID the every-context flush is INVPCID type 2 and no CR4 write, and otherwise the CR4.PGE toggle, and the claim that type 2 empties the paging-structure caches holds because boot clears EFER.TCE and nothing sets it again. The core-share flush's commands and the PCID branch of a translation-root load read the same value."
revisit_if: "INVPCID type 2 is shown to drop every cached upper-level entry while EFER.TCE is set, which is when boot stops clearing TCE; or a logical processor can gain or lose a feature after its boot read."
confidence: "What INVPCID type 2 invalidates, and what EFER.TCE changes about cached upper-level entries, is the manuals' word, cited below. That the read is per core, and that the value lives in the core's block rather than the kernel value, follows from CPUID and EFER being per logical processor and from the flush running before the kernel value exists."
---

# A core's processor report, read once

## Decision

Each core reads, once, during its own init, what its processor reports, and keeps the result for the life of the boot. The read is not repeated in a flush: CPUID exits under KVM, and a flush is on the path that already costs a targeted core its TLB.

The result is an exec value of the arch module, `Processor` in `kernel/verified/arch/mod.rs`, the same type on both targets. Its fields are private to the arch module. It is `Copy`, unlike `BaseRegister`: it names a fact that does not change, so every caller on the core passes the same bits. A value with any bit set is made only by the cited boot read, `read_processor`, a hardware leaf in the form of `design/who-vouches-for-an-unproven-claim/`. The zero value, every bit clear, is what a core's block holds before that read, and it is the only value code outside the arch module can build. The zero value selects every fallback. It cannot turn a feature on.

The value is a field of the core's `Cpu` in `kernel/src/cpu.rs`, the block the core pointer names. `kernel/verified` has no static that could hold it, `design/one-kernel-instance/`, and the leaf's body is in `kernel/verified`, so it cannot read the block itself. Callers pass the value in. `flush_every_context` and `load_translation_root` each gain it as an argument, on both targets, and a target that does not branch on it ignores the argument. The core-share flush of `design/flush-on-a-change-of-core-share/` takes the same value when its commands run.

The bits, set only by that core's read:

- `invpcid`: CPUID Fn0000_0007 with ECX 0, EBX bit 10 (amd-apm3, INVPCID, the #UD cause, and appendix E, CPUID Fn0000_0007_EBX_x0).
- `ibpb`: CPUID Fn8000_0008 EBX bit 12. `l1d_flush`: CPUID Fn0000_0007 with ECX 0, EDX bit 28. What those commands do is `design/flush-on-a-change-of-core-share/`.
- `pcid`: CPUID function 1, ECX[PCID] (amd-apm2 5.5.1), and only when this core's CR4.PCIDE is set at the read. The manual names the flag and does not number the bit; the loader tests ECX bit 17 before it sets CR4.PCIDE, and the boot read tests that same bit.
- `specres`: on aarch64, one read of ID_AA64ISAR1_EL1.SPECRES. On x86_64 this bit is clear. On aarch64 the three x86 bits are clear.

`flush_every_context` on x86_64, when `invpcid` is set, runs INVPCID type 2 and does not write CR4. Type 2 is "Invalidate all TLB entries including Global" (amd-apm3, INVPCID, p. 401). The descriptor is 16 bytes: the PCID in bits 11:0, bits 63:12 zero, the linear address in bits 127:64. Type 2 names no one address, so the address is 0, which is canonical, and the PCID is 0. With CR4.PCIDE clear, types 2 and 3 invalidate mappings for PCID 0 only, and every entry is then held under PCID 0, so that is every entry. With CR4.PCIDE set, type 2 is not limited to one PCID. The instruction acts on the local logical processor, is serializing, and is CPL 0; without the feature it is a #UD. When `invpcid` is clear, the leaf toggles CR4.PGE as it does today, which invalidates the whole TLB including global pages (amd-apm2 5.5.3, Implicit Invalidations), and that branch keeps the citations it has.

The leaf's specification is unchanged in what it ensures: that core's set in the TLB model is emptied, paging-structure caches included, and no other core's set changes, `design/flush-without-waiting/`. INVPCID follows INVLPG's rule for cached upper-level entries, and that rule is EFER.TCE (amd-apm3, INVPCID; amd-apm2 3.1.7, Translation Cache Extension, bit 15 of EFER, MSR C000_0080h). When TCE is 0, or the processor has no such feature, the instruction removes every cached upper-level entry along with its target. When TCE is 1, it may leave upper-level entries that do not lead to the target. Type 2 names no single target entry, and the manual does not say that type 2 drops every cached upper-level entry while TCE is 1. The model-empty claim on the INVPCID branch is therefore warranted only where EFER.TCE is clear. Each core's init clears bit 15 and no later write sets it. That is a glue claim of the same shape as the one beside `tags_tlb`: the loader sets CR4.PCIDE where CPUID reports PCID, the trampoline sets it on an AP, and no CR4 write of the kernel's clears it. The two claims are named together. CPUID Fn8000_0001_ECX bit 17 says the processor supports TCE (amd-apm3 E.4.2). Clearing bit 15 does not set an enable, so a processor that does not support TCE, whose bit reads clear, stays clear.

`load_translation_root` on x86_64 branches on `pcid` and does not read CR4. Where the bit is set it writes the PCID and the no-flush bit; where it is clear it writes the root alone, and the tag is then 0. `tags_tlb` for that core is the bit. The glue claim that nothing clears CR4.PCIDE is what keeps the stored bit true. On aarch64 `tags_tlb` stays true, and the load ignores the value.

The core-share commands run where the matching bit is set, and they do not execute CPUID or read an ID register. On aarch64 that bit is `specres`.

## Context

The every-context flush on x86_64 is two writes of CR4.PGE. Under KVM on this host, a Ryzen 9 9950X3D with two vCPUs, a flush_cost boot measured those two writes at about 111,000 TSC cycles above an IPI that flushed nothing, against 1,000 to 1,100 cycles for a local INVPCID of one context and about 200 for one page. A TSC cycle there is about 1/4300 of a microsecond. INVPCID is not intercepted under nested paging. The all-entries kind itself was not in that run; the flush_cost boot retakes it once the leaf uses type 2. The same cost is why the read of the feature is once: a CPUID in the flush would be another exit.

The core-share flush already says its x86_64 commands run where CPUID reports them, and its aarch64 commands where the ID register reports FEAT_SPECRES, and the PCID branch reads CR4.PCIDE on every load of a translation root. Nothing in the tree reads the two command bits yet, and the CR4 read is on the load. One value has to serve all three, or each site grows its own read.

## Reasoning

CPUID and EFER are per logical processor. A machine can pair processors that do not report the same bits, and an AP's EFER is its own, so the boot core's report is not copied out to the others. Each core runs the read in its own init, after its control registers are in the state that core boots with, which is when CR4.PCIDE already reflects the loader or the trampoline.

The flush that empties a core's model runs in the boot test before the kernel value exists, and the IPI handler flushes before it takes the kernel. A copy kept only inside the kernel value would be absent for both. The `Cpu` block exists from the core's init, which is before either flush. The kernel value does not hold a second copy: two stores of one fact is a second source of truth the moment anything writes one of them, and nothing is supposed to write this one again.

Verified code cannot set a bit, so the INVPCID branch runs only on a value the boot read returned. The zero value is how a `Cpu` can be built as a constant before any core has run CPUID, and passing it takes the CR4.PGE path, which still meets the specification.

Keeping EFER.TCE clear is what makes type 2 match the claim the model already makes. TCE set would let a selective invalidation leave unrelated upper-level entries, which is a performance choice for a kernel whose proven flush is selective. This kernel's proven flush empties the core. A later selective flush that wants TCE set has to revise this record, because the type-2 claim would then need a different warrant.

## Alternatives rejected

- **One read for the machine, taken by the boot core or by the loader and handed down in the boot arguments.** The loader runs on one core. An AP would inherit a report that is not its own, including another core's EFER.TCE. Per core is the reading that stays right when two logical processors differ.
- **A static in the verified crate, or a per-CPU word the leaf loads itself.** `kernel/verified` has no statics, and the leaf would be reading the glue's memory from inside the arch module. The caller passes the value, which is the same shape as `BaseRegister`.
- **Held in the kernel value, beside the core's other proven state.** The flush runs where that value is not there yet, and the fact is about the processor, not about a capability. The core's block is where the GDT and the interrupt stacks already live.
- **A CR4 bit, read on each flush, as `tags_tlb` reads PCIDE today.** No CR4 bit means INVPCID, IBPB or L1D_FLUSH. PCIDE itself moves into the value so the load stops reading CR4; the architectural enable stays the glue's to keep set.
- **Leaving EFER.TCE as firmware left it and claiming type 2 empties every upper-level entry anyway.** The manual does not say that. It says INVPCID follows INVLPG, and INVLPG under TCE may keep upper-level entries that do not lead to the target.

## What this does not settle

- The bodies of the core-share commands. Which instructions run, and what they clear, is `design/flush-on-a-change-of-core-share/`. This record says only which value they test.
- An Intel core's reporting of IBPB, which that record already leaves to a document `tools/hardware-documents` does not list. Until it is listed the x86_64 read uses AMD's bit, and an Intel core's `ibpb` bit is clear.
- The cycles of INVPCID type 2. The single-context and one-page kinds were measured; the all-entries kind is measured when the leaf uses it.
