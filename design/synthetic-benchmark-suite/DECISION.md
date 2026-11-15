---
title: "Synthetic benchmark suite: perftest runner, JSON schema, and Fuchsia mapping"
date: 2026-11-15
status: active
tags: [abi, bench, ipc, memory, scheduling, test]
one_line: "Adopt Fuchsia perftest's execution model (warm-up, fixed batches, pre-faulted sample storage, multi-step *_ignore, min/median/mean) and runtime JSON array ({label, test_suite, unit, values}) with fenced TSC and RDPMC companion series measured in separate pinned KVM runs, and map every file of Fuchsia's src/tests/microbenchmarks onto Atmosphere operations or exclude POSIX, Starnix, FIDL, and kernel-VFS tests with reasons."
revisit_if: "Real application workloads supersede synthetic primitives as the primary regression signal, multiple kernel instances exist on one machine, Fuchsia's fuchsiaperf JSON format changes away from {label, test_suite, unit, values}, or bare-metal PMU access replaces boot-programmed CR4.PCE counters."
confidence: "All 90 BSD-2-Clause files of Fuchsia src/tests/microbenchmarks (76 files) and zircon/system/ulib/perftest (14 files) at commit 3a111afac557ea92fd5f315810201a5871b4e37f were inspected directly and cross-checked against kernel/verified/capability/operation.rs, asys/src/operation.rs, dom0/src/main.rs, aheap, aeager, aring, amailbox, afanin, pager-policy, and tools/measure-pinned.py; neither Fuchsia's binary on this host nor the Atmosphere runner exists yet."
---

# Synthetic benchmark suite: perftest runner, JSON schema, and Fuchsia mapping

## Decision

Atmosphere builds its synthetic microbenchmark suite by interpretive mapping, not translation: benchmarks measure Atmosphere's own operations and user-space libraries while adopting the execution model, result naming, and JSON wire format of Fuchsia's `perftest` library so host runs of Fuchsia's suite under the same KVM pinning can be joined by label.

### Sources and licensing

- **Fuchsia microbenchmarks and perftest runner**: `https://fuchsia.googlesource.com/fuchsia`, branch `main`, commit `3a111afac557ea92fd5f315810201a5871b4e37f`, paths `src/tests/microbenchmarks` (76 files) and `zircon/system/ulib/perftest` (14 files). License: BSD-2-Clause (`The Fuchsia Authors`).
- **Barrelfish `usr/bench`**: mapped beside Fuchsia in a companion update to this directory.

### Runner method (`perftest`)

The user-space harness adopts the semantics of `zircon/system/ulib/perftest` (`runner.cc`, `results.cc`, `include/perftest/perftest.h`, `include/perftest/results.h`) and `src/tests/microbenchmarks/test_runner.h`:

1. **Named registry and modes**: Each benchmark registers under a hierarchical `/` name (`"Syscall/Null"`, `"Mmu/MapUnmap"`, etc.) with optional regex filtering (`--filter`) and deterministic sorted or shuffled execution order (`--random-order`). Two modes exist:
   - *Unit-test check mode* (default in gate boots): runs every registered benchmark for a small fixed count (`kRunCount = 3`) to assert status-clean correctness without printing or checking timings.
   - *Perf-test mode* (`--runs N`, default `1000` in `perftest`, `120` per boot over multiple boots in infra): collects `N` timed samples per registered case.
2. **Pre-faulting and warm-up**: Sample buffers (`run_count * step_count + 1` entries) are allocated and zero-filled before iteration `0` so writing timestamps never triggers demand faults or page-table walks mid-measurement (`RepeatStateImpl::KeepRunning` in `runner.cc`). Each parameterized benchmark executes at least one untimed warm-up pass before sample `0` (`test_runner.h`) to populate instruction/data caches and synchronize helper threads.
3. **No I/O inside timed runs**: `PRINT` (operation `14`) enters the kernel synchronously and drives serial UART output. During perf-test runs, no logging occurs between sample `0` and completion of all cases; summary statistics and the JSON document are printed afterward.
4. **Multi-step instrumentation and optimization barriers**: Benchmarks with setup/action phases within an iteration declare ordered steps (`DeclareStep(name)` / `NextStep()`). Single-step tests emit `<label>`; multi-step tests emit `<label>.<step>`, discarding any step whose name ends in `_ignore` (`runner.cc`) after timing it. Compiler dead-code elimination is blocked around timed operations (`core::hint::black_box`, matching `perftest::DoNotOptimize`).
5. **Counters and `pmu=on` separation under KVM**:
   - Wall intervals read serialized hardware counters (`rdtscp` or `lfence; rdtsc` on `x86_64`, `isb; mrs cntvct_el0` on `aarch64`) converted to nanoseconds once TSC/timer frequency is supplied (or raw ticks when calibrating externally).
   - Where hardware extended core counters are enabled (`CPUID Fn8000_0001 ECX[23]` and `CR4.PCE`, `design/arch-module/`), `RDPMC` reads counters `0..3` programmed at boot (`cycles` not halted `0x430076`, retired `instructions` `0x4300C0`, DC `fills` `0x435F44`, cross-CCX `ccx_fills` `0x430444`).
   - **Rule on KVM `pmu=on`**: KVM's perf-based vPMU slows VM exits roughly threefold (measured on flush IPIs). Wall latency runs (`nanoseconds`) therefore execute under `tools/measure-pinned.py` pinning *without* `pmu=on` (matching Fuchsia's KVM run conditions), and PMU counter runs (`--counters`) execute as a separate pass for deterministic instruction counts and cache-fill attribution rather than mixing both numbers as if from one quiescent clock.
6. **Batch statistics and cross-boot comparison**: Within a boot, the runner computes `min`, `max`, `mean`, `std_dev`, and interpolated `median` across the batch (`GetSummaryStatistics` in `results.cc`), printing the fixed-width summary table (`Mean Std dev Min Max Median Unit Test case`). Across boots (`tools/bench.py`), pinned host runs (`within0`, `within1`, `across` via `tools/measure-pinned.py` on physical cores isolated from SMT siblings and host IRQs) interleave baseline and candidate across at least `5` boots; a benchmark counts as moved when its boot medians fall outside the baseline's boot-to-boot spread.

### Result JSON schema

`zircon/system/ulib/perftest` contains two different schema artifacts:

- `performance-results-schema.json`: a draft-06 JSON schema describing objects with `{"label", "unit", "samples": [{"label"?, "values": [...]}]}` and `"additionalProperties": false`.
- `results.cc` (`TestCaseResults::WriteJSON`, verified by `test/results-test.cc` and `src/tests/microbenchmarks/README.md`): the runtime format actually emitted by `perftest` (`fuchsiaperf.json`), which is a flat array of flat objects:

```json
[
  {
    "label": "Syscall/Null",
    "test_suite": "atmosphere.microbenchmarks",
    "unit": "nanoseconds",
    "values": [123.000000, 125.000000]
  }
]
```

Atmosphere adopts the **runtime format emitted by `results.cc`** (`[{"label", "test_suite", "unit", "values"}]`) because that is what Fuchsia's own benchmark binary writes and what host analysis scripts ingest when joining Fuchsia and Atmosphere runs by `label`.

To preserve 1:1 label matching with Fuchsia while carrying hardware counter data:

- Primary latency series keep the canonical benchmark name (e.g. `"Syscall/Null"`) and `"unit": "nanoseconds"` (matching Fuchsia's unit string verbatim), with `"test_suite": "atmosphere.microbenchmarks"`.
- Raw TSC ticks and optional PMU counters from `--counters` runs are emitted as sibling objects in the same array using dotted metric suffixes: `"<label>.tsc_cycles"` (`"unit": "cycles"`), `"<label>.cycles"` (`"unit": "cycles"`), `"<label>.instructions"` (`"unit": "instructions"`), `"<label>.fills"` (`"unit": "count"`), and `"<label>.ccx_fills"` (`"unit": "count"`). Consumers join wall latency on exact `label` and filter out metric suffixes when comparing against Fuchsia's `values`.

### Fuchsia microbenchmark file mapping (`src/tests/microbenchmarks`)

Every one of the 76 files in `src/tests/microbenchmarks` is listed below.

#### 1. Harness, build config, helpers, and manifests (23 files)

| Fuchsia file | Role in Fuchsia | Atmosphere counterpart or disposition |
|---|---|---|
| `main.cc`, `main.h` | `PerfTestMain` entry, flag handling, startup | Replaced by Atmosphere user-space benchmark runner in `dom0` / bench binary and host orchestrator. |
| `test_runner.h` | Warm-up `test.Run()` then `KeepRunning()` loop | Adopted directly in the Atmosphere runner (`TestCase` trait / warm-up before timed batch). |
| `assert.h`, `util.cc`, `util.h` | `ASSERT_OK` macros, temp file helper, sleeps | Assertion checks map to `asys::operation::STATUS_OK` checks; temp-file helpers omitted (no POSIX VFS). |
| `scoped_mapping.h` | RAII `zx_vmar_map` / `zx_vmar_unmap` wrapper | Maps to explicit `asys::operation::{map, unmap}` and `aeager` / region-map guards; no VMAR object. |
| `simple_latch.h` | Atomic barrier (`count_down`, `arrive_and_wait`) | Maps to `core::sync::atomic` barrier across threads pinned on distinct `CoreCapability` slots (or notification wake once wired). |
| `no_op_executable.cc` | Minimal spawned target process binary | Maps to minimal position-independent child entry or `user/hello`-style ELF started via `retype` + `map` + `write_registers` + `place` + `start`. |
| `context_switch_overhead_helper.cc` | Helper spawning pinned worker pairs per CPU | Replaced by child thread/process creation via `retype`, `place`, and `start` over shared endpoint/notification caps. |
| `get_info_helper.cc` | Idle `P x T` process/thread tree for `get_info` | Excluded: Atmosphere has no job/process enumeration API. |
| `round_trips.h` | Shared single- vs multi-process helper declaration for `round_trips.cc` | Subsumed by Atmosphere benchmark harness parameterization. |
| `async_loop.fidl`, `round_tripper.fidl` | FIDL interface definitions | Excluded: no FIDL compiler or wire runtime (`awire` / 5-word register messages / `aring` used directly). |
| `BUILD.gn`, `OWNERS`, `README.md`, `config/BUILD.gn` | GN build rules, documentation | Atmosphere uses Cargo workspace crates and `tools/bench.py`. |
| `config/microbenchmarks.profiles` | Scheduler role profiles (`Default`, `Realtime`) | Replaced by `place(thread, core_cap, priority)` priority bounds (`design/cpu-time-as-capability/`). |
| `meta/fuchsia_microbenchmarks.cml`, `meta/fuchsia_microbenchmarks_shared_process.cml`, `meta/starnix_microbenchmarks.cml`, `meta/starnix_microbenchmarks_common.shard.cml` | Component v2 / Starnix runtime capabilities and tmp/tracing routes | Replaced by boot capabilities in root table (`design/root-process-at-boot/`) delegated via `derive` / `move` / grant. |

#### 2. Kept benchmark files (30 files)

Each kept benchmark file below maps to one or more explicit Atmosphere operations and libraries.

| Fuchsia file | What it measures | Atmosphere counterpart & operations | What differs & prerequisites |
|---|---|---|---|
| `null.cc` | `Null`, `Null5Step`: runner call and multi-step timestamp overhead. | `Null`, `Null5Step` in user-space runner. | Serialized TSC + optional `RDPMC` instead of `zx_ticks_get_boot()`. Built with runner. |
| `example.cc` | `ExampleNoOpLoop`, `NoOpLoop/{100,1000,10000}`: barriered CPU loop. | `NoOpLoop/{100,1000,10000}` using `core::hint::black_box`. | Pure user-space calibration smoke test. Built with runner. |
| `syscalls.cc` | `Syscall/Null` (0-arg), `Syscall/ManyArgs` (8-arg overflow test syscall). | `Syscall/Null` (`invoke(NO_OPERATION, ...)` returning `STATUS_UNKNOWN`), `Syscall/Inspect` (`operation::inspect` returning 5 words in registers), `Syscall/Refused`. | Atmosphere passes slot + 5 args and returns status + 5 words strictly in registers (`design/syscall-abi-in-registers/`); no user-memory arg spill; accepted calls acquire the single kernel lock (`design/one-lock-bounded-steps/`). Moves existing `dom0` syscall timing onto runner; contended variant also tracked with multicore lock checks. |
| `handle.cc` | `HandleValid/{1,CpuCount}Threads`: concurrent handle validation scaling. | `Capability/Inspect/{1,CpuCount}Threads`: `operation::inspect(slot)` from 1 vs all pinned cores. | Lookup is 2-level capability table indexing under the single global kernel lock rather than per-process handle table; measures global lock contention directly. Runs today once runner lands. |
| `handle_creation.cc` | `HandleCreate_*`: kernel object allocation and close. | `Capability/RetypeFree/{Frame4K,LargeFrame2M}`, `Capability/RetypeDestroy/{Process,Thread}`, and `Endpoint`/`Notification`/`Reply` create+delete. | Objects come from explicit physical `Untyped` blocks via `retype` and reclaim via `destroy` + `delete` + `retype(RETYPE_FREE)`, not kernel heap objects (`design/untyped-memory/`, `design/teardown-driven-by-retype/`). Frame/table/process/thread run today; IPC object retype waits on wired IPC. |
| `events.cc` | `Duplicate`, `Replace`; `Signal`, `WaitForAlreadySignaledEvent`, `WaitForManyWithAlreadySignaledEvent`. | `Capability/DeriveDelete`, `Capability/Move`; `Notification/Signal`, `Notification/WaitAlreadySignaled`. | Handle dup/replace map to `derive` (with tree child links) + `delete` and `move_capability` (runs today). Signaling uses 1 notification word (`design/notification-word-reserves-the-waiter-bit/`) instead of 2 signal bits; no `wait_many` array (multi-source wait uses `afanin` + notification; waits on wired notifications). |
| `get_info.cc` | `GetInfo/Runtime/{ThreadOnly,ConcurrentThreads}` and `P=*/T=*` job tree enumeration. | `Thread/InspectConsumed/{ThreadOnly,ConcurrentThreads}` via `operation::inspect(thread)` result `5` (`consumed`). | Atmosphere returns per-thread `consumed` cycles directly in `inspect` without copying structs. No job/task enumeration counterpart (`P=*/T=*` dropped: no ambient task hierarchy, `design/one-kernel-instance/`). `inspect` result `5` runs today. |
| `channels.cc` | Single-thread `zx_channel_write` + `read` (64B–64K, 0/1 handle, iovecs). | Split by size: (a) 2-thread rendezvous `Endpoint/CallReplyRecv/{0,1}Cap`, (b) shared-frame `aring` bulk transfer (`64B..64K`) + notification doorbell. | Atmosphere copies zero bytes from user memory (`design/syscall-abi-in-registers/`), has no unbuffered single-thread channel FIFO or iovecs, and splits small control words (registers) from bulk data (`aring` in user memory). Raw `aring` runs today; endpoints/doorbell wait on wired IPC. |
| `fifos.cc` | `Fifo/WriteRead/{16,32,64}bytes_{1,4,64}batch`: kernel-buffered fixed-record ring. | `Ring/SingleThread/{16,32,64}bytes_{1,4,64}batch` over `aring` (`Producer::publish`, `Consumer::observe`/`consume`). | Ring storage and head/tail indices live in shared frames instead of kernel memory (`aring`, proven against untrusted peer), entering kernel via notification only when sleeping peer needs wakeup. Memory-ring path runs today. |
| `sockets.cc` | `Socket/{Stream,Datagram}/{WriteRead,Concurrent}`: kernel byte/dgram pipe. | `Ring/Payload/...` (`aring` pair, single-thread and 2-core pinned) + notification doorbell (including two-process ring). | No kernel stream/datagram socket object; byte/frame streaming uses TX/RX `aring` shared frames (and `amailbox` for 3-slot latest state, `design/latest-value-by-three-slot-exchange/`). In-process `aring` runs today; cross-process doorbell waits on wired IPC. |
| `ports.cc` | `Port/QueueWait`: self-queue + dequeue of kernel packet. | `Notification/QueueWait` (non-blocking `signal` + `wait` on same thread) and `aring` push/pop. | Atmosphere kernel ports do not allocate/copy 48-byte packets; kernel carries only notification bits while user rings hold packet structs. `aring` runs today; notification `signal`/`wait` waits on wired IPC. |
| `round_trips.cc` | Ping-pong & throughput across threads/processes (`BasicChannel`, `ChannelCall`, `EventPort`, `ChannelPort`, `SocketPort`, `Deadline`, `Fidl`). | `Endpoint/RoundTrip_{SameCore,DiffCore}`, `Notification/RoundTrip_{SameCore,DiffCore}`, `Endpoint/CallReplyRecv`, `Ring/TwoProcessThroughput`, `Endpoint/Call_Deadline`. | Register `call`/`reply_recv` with one-shot reply capability (`design/ipc-with-reply-object/`) replaces `txid`-matched channel calls; paired notifications replace event/port waits; deadline uses fixed priority + absolute TSC timer (`design/cpu-time-as-capability/`). `RoundTrip_Fidl` has no counterpart. Waits on wired IPC (and cross-core IPC measurement). |
| `round_trips_futex.cc` | `RoundTrip_Futex_SingleProcess`: 2-thread futex ping-pong. | `Notification/RoundTrip_SameProcess` (`signal` + `wait`) and atomic spin / scheduler yield comparison. | No kernel futex syscall (`zx_futex`); threads wait on explicit notification caps avoiding VA-hashed kernel wait queues. Waits on wired notifications. |
| `futex.cc` | `FutexWakeOne/1..2048Waiting`: kernel futex hash-table scalability. | `Notification/WakeOne/{1..64}Waiting` (distinct notification queues + `signal`). | O(1) wakeup directly via capability slot rather than global VA-indexed kernel futex hash table; bounded lock step still applies across contended entries. Waits on wired notifications. |
| `threads.cc` | `Thread/CreateAndJoin`: stack VMO + map + `thread_create/start` + wait terminated + cleanup. | `Thread/CreateStartJoin`: `retype(RETYPE_FRAME)` + `map` + `retype(RETYPE_THREAD)` + `write_registers` + `place` + `start` + join notification + `destroy` + `unmap` + `delete` + `RETYPE_FREE`. | Stack and core placement are explicit capabilities (`place(..., core_cap, prio)`). Raw create/start/suspend/destroy run today; notification-based join waits on wired notifications. |
| `fdio_spawn.cc` | `Fdio/Spawn`: launch minimal executable (`no_op_executable`) and wait termination. | `Process/SpawnWait`: `retype(RETYPE_PROCESS)` + `retype` tables/frames + `map` via `through` + `retype(RETYPE_THREAD)` + `write_registers` + `place` + `start` + exit wait + `destroy`/`revoke`/`RETYPE_FREE`. | No `fdio`/POSIX loader/argv/fd table; parent directly constructs child's capability table and space (`design/process-holds-capabilities/`). Waits on wired notifications for clean exit handshake. |
| `context_switch_overhead.cc` | `ContextSwitch/1000`: cross-process thread-pair round-trip switches across cores. | `ContextSwitch/{SameProcess,CrossProcess}` on one `CoreCapability` via notification ping-pong (plus `switch` syscall later). | Measures save/restore, `cr3`/`TTBR0_EL1` switch, `GS`/`TPIDR_EL0` clearing (`design/gs-base-swapped-at-ring-3/`, `design/thread-pointer-cleared-on-switch/`), and later predictor/L1D flush across core caps (`design/flush-on-a-change-of-core-share/`). Separate from interrupt-to-thread latency. Waits on wired notifications. |
| `mmu.cc` | `Mmu/MapUnmap` (eager 1 MiB) and `Mmu/MapUnmapWithFaults` (511 x 4K demand fault + unmap). | Split: `Mmu/MapUnmap/{4K,2M}` (`link`, `map`, `unmap`, `probe`, plus remote-core shootdown); fault path moves to user-pager group below. | No VMAR; `map`/`unmap`/`probe` directly mutate hardware page tables (`unmap` flushes asynchronously via epoch, `design/flush-without-waiting/`), while demand faults travel to user pager over fault IPC (`design/region-map-owns-the-address-space/`). `Mmu/MapUnmap` runs today; `WithFaults` waits on fault delivery & standard pager. |
| `vmar.cc` | `Vmar/{Protect,Decommit,Allocate}`: VMAR interval tree, mprotect, decommit, ASLR. | `Span/EagerReserveBackRelease` (`aeager`) and `Mmu/{UnmapRemapRights,BatchUnmap}` (`derive` + `unmap`/`map`/`probe`). | Kernel has no VMAR interval tree or ASLR (`Vmar/Allocate` has no kernel counterpart); address space bookkeeping and decommit live in user region map (`aeager` / user pager). Eager span & page-table operations run today. |
| `vmo.cc` | `Vmo/{Read,Write,Map,Clone,TransferData,ManyMappingsReadWriteDecommit/8192}`. | Kept: `Mmu/ManyMappingsReadWriteUnmap/8192`, `Mmu/MapReadWrite/{4K,2M}` (zeroed `retype` + `map` + touch). Dropped: `Vmo/Read`, `Vmo/Write`, `Vmo/TransferData`, `Vmo/Clone`, `Vmo/Memcpy/{With,Without}Precommit`. | Atmosphere has no kernel VMO object, no kernel page cache, no kernel `vmo_read/write` copy syscall, and no kernel CoW clones (`design/untyped-memory/`); mapped memory operations run today (`link`, `map`, `probe`, `unmap`), while CoW/eviction policy belongs to user pager. |
| `user_pager.cc` | `UserPager/PageFault/Sequential`: 4 MiB pager-backed VMO fault loop. | `UserPager/PageFault/Sequential`, `UserPager/BatchedFault`, `UserPager/EvictAndRefault` (fault IPC -> user pager `map` + reply; S3-FIFO cold eviction via `probe` + `unmap`). | Core Atmosphere path (`design/region-map-owns-the-address-space/`, `pager-policy` S3-FIFO) without any kernel `zx_pager` or port buffer; kernel delivers fault directly to handler endpoint (`reply` resumes). Waits on fault delivery & standard user pager library. |
| `clock.cc` | `ClockGetMonotonic`, `TicksGet`: vDSO monotonic & raw ticks read. | `TicksGet` (raw `rdtsc`/`rdtscp` or `cntvct_el0`) and `ClockGetMonotonic` (`astd` monotonic ns clock). | Unprivileged hardware counter read in user space rather than vDSO atomic clock-transformation struct. `TicksGet` runs today; `ClockGetMonotonic` waits on `astd` frequency-calibrated clock. |
| `timer.cc` | `Timer/1msWait/Slack*`: relative/deadline timer with slack coalescing. | `Timer/1msWait/Deadline`: arm per-core timer capability for `now + 1ms` TSC deadline, wait on bound notification. | Per-core timer caps arm exact absolute TSC deadlines with no kernel slack coalescing and run tickless with one runnable thread. Waits on timer capability & wired notification/interrupt delivery. |
| `sleep.cc` | `Sleep/{0,1,10,100,1000,10000}ns`: minimum `zx_nanosleep` floor. | `Sleep/{0,10,100,1000,10000}ns`: timer-bound notification wait / deadline poll over `astd` clock+sleep. | `zx_nanosleep` short-circuits in kernel; Atmosphere programs per-core timer notification for absolute deadline or yields. Waits on timer delivery & `astd` sleep. |
| `atomics.cc` | `Atomic/{Increment,Cmpxchg}/{32bit,64bit}`. | `Atomic/{Increment,Cmpxchg}/{32bit,64bit}` + `Atomic/ContendedCmpxchg/DiffCore` via shared frame. | Pure CPU `core::sync::atomic` microbenchmark measuring core & interconnect CAS latency under pinned `within0` / `across`. Runs today. |
| `mutex.cc` | `MutexLockUnlock`: uncontended `sync_mutex` fast path. | `Mutex/FastLockUnlock` on `astd::sync::Mutex` (and notification-backed mutex once wired). | Measures uncontended user atomic lock/unlock fast path (distinct from multi-core kernel spinlock contention benchmarks). Runs today. |
| `malloc.cc` | `MallocFree/{100,1024,8192,65536}bytes`: allocator alloc+free loop. | `MallocFree/{100,1024,8192,65536}bytes` over `astd::heap` (`aheap::heap::Heap` + `aeager`, later swappable with user pager). | Measures verified size-class slab allocator (`design/heap-size-classes/`, `design/page-buddy-metadata-in-the-span/`) and large-object list (`65536B`). Runs today over `aeager`. |
| `mem_alloc.cc` | `MemAlloc/*/{AllocAndFree,RetainAndFreeOldest,RetainAndFreeRandom}`: sustained working-set churn. | `MemAlloc/Aheap/{AllocAndFree,RetainAndFreeOldest,RetainAndFreeRandom}/{8..2048}Kbytes`. | Exercises `aheap` small slab reuse, partial/full lists, and page-buddy block coalesce/split over `aeager` today (and later user pager). Runs today. |
| `memcpy.cc`, `random_memcpy.cc` | `Memcpy/{1000,100000}bytes`, `RandomMemcpy`: sequential & random block copies in multi-MB buffers. | `Memcpy/{1000,100000}bytes`, `RandomMemcpy/{64,4096}bytes` via `core::ptr::copy_nonoverlapping` over `aheap`/`aeager` buffers. | No `stdcompat` C++ `span` wrapper; slice copy covers the same generated code. Runs today. |

#### 3. Excluded benchmark files (23 files)

Every remaining file has no Atmosphere counterpart (or duplicates another test via a foreign runtime/API):

| Fuchsia file(s) | What it measures | Reason excluded in Atmosphere |
|---|---|---|
| `object_wait.cc` | `ObjectWaitAsync` + port packet cancellation | Kernel allocates no async per-waiter port packets; hardware interrupts, timers, and producers signal notifications directly, and fan-in scans `afanin` shared rings (`design/fan-in-over-private-rings/`). |
| `async_loop.cc` | `AsyncLoopProcessBatch/{1..16}` over FIDL channel + C++ `async::Loop` | No FIDL or C++ `libasync` dispatch framework; message batching uses `aring` + `afanin`. |
| `streams.cc` | `Stream/{WriteAt,ReadAt}` kernel VMO seek streams | No kernel VMO or seekable kernel stream object; file I/O lives in `file-service` and shared frames. |
| `stdcompat.cc` | `cpp20::span` wrapper over `RandomMemcpy` loop | C++ stdcompat header wrapper; Rust slice copy in `random_memcpy.cc` counterpart covers the operation. |
| `clock_posix.cc` | `ClockGettimeMonotonic`, `ClockGettimeRealTime` | POSIX `clock_gettime`; native `ClockGetMonotonic` lives under `clock.cc` mapping, with no POSIX ABI or wall RTC in kernel. |
| `pthreads.cc` | `PThreadCreateAndJoinTest{,/100Existing,/1000Existing}` | POSIX `pthread` library; native thread create/join lives under `threads.cc` mapping (Rust `std` threads come later). |
| `process_spawn_posix.cc` | `ProcessSpawn` via `posix_spawn` | POSIX spawn + PATH/fd inheritance; native process spawn lives under `fdio_spawn.cc` mapping. |
| `round_trips_posix.cc` | `RoundTrip_PthreadCondvar_SingleProcess` | POSIX mutex + condvar; native synchronization ping-pong lives under notifications (`round_trips_futex.cc` / `round_trips.cc` mapping). |
| `inspect.cc` | `Inspect/*` (28 tests) C++ `lib/inspect` VMO heap/histograms | Fuchsia-specific observability VMO heap format; Atmosphere has fixed-register capability `inspect` and serial JSON benchmark logs. |
| `tracing.cc` | `Tracing/*` (4 tests) Fuchsia KTrace trace-buffer macros | No kernel/userspace trace-buffer daemon or `trace_engine` ABI in native system. |
| `prng.cc` | `Prng/{Zx/CprngDraw,LibCpp/RandomDevice,LibC/Rand,Random}` | Kernel has no `cprng_draw` entropy pool syscall; hardware RNG (`RDRAND`/`RNDR`) or VirtIO-RNG belongs in arch/driver modules outside kernel capabilities. |
| `filesystem.cc`, `lazy_dir.cc`, `pseudo_dir.cc` | POSIX `stat`/`open`/`fstat` and Fuchsia C++ VFS (`LazyDir`, `PseudoDir`) | Atmosphere native ABI has no kernel VFS or POSIX file descriptors; `file-service` storage benchmarks belong to the persistence workload, not microkernel primitives. |
| `clone.cc`, `fork.cc`, `getpid.cc`, `prctl.cc`, `unshare.cc` (5 files) | Linux host / Starnix `clone`, `fork`, `getpid`, `prctl`, `unshare` | Purity rule: zero POSIX or Linux compatibility layer in the native kernel; Linux workloads run unmodified inside guest VMs (`design/vmm-over-svm/`). |
| `restricted_enter.cc` | `zx_restricted_enter` / Starnix Linux-syscall trap loop | Atmosphere uses hardware virtualization (SVM/EL2 VMM) for foreign OS binaries, not Fuchsia restricted-mode trap loops. |
| `starnix_filesystem.cc`, `starnix_mm.cc`, `starnix_tracefs.cc` (3 files) | Starnix Linux VFS (`/proc`, `ext4`, `bpf`), `madvise`/`msync`, `tracefs` | Linux/Starnix kernel-emulation benchmarks with no native equivalent. |

### Kept benchmark groups and readiness

The kept Fuchsia benchmarks split cleanly by prerequisite into two waves, avoiding overlap with benchmarks already planned (standalone and contended syscall latency, two-process `aring` over endpoints, cross-core IPC, interrupt-to-thread latency, 4/8/16-core lock contention, and `inspect` consumed-cycle growth):

1. **Ready once the user-space runner lands (runs on today's kernel and `dom0` runtime)**:
   - *Runner self-calibration* (with the runner itself): `Null`, `Null5Step`, `NoOpLoop/{100,1000,10000}`, `Syscall/Null`.
   - *Capability lifecycle & table inspect*: `Capability/Inspect/{1,CpuCount}Threads`, `Capability/DeriveDelete`, `Capability/Move`, `Capability/Revoke/{1,64}`, `Capability/RetypeFree/{Frame4K,LargeFrame2M}`, `Capability/RetypeDestroy/{Process,Thread}`.
   - *Address space & MMU*: `Mmu/MapUnmap/4K`, `Mmu/MapUnmap/2M`, `Mmu/MapUnmap/{Loaded,Unloaded}RemoteCore`, `Mmu/Probe/64`, `Mmu/ManyMappingsReadWriteUnmap/8192`, `Mmu/MapReadWrite/{4K,2M}`, `Span/EagerReserveBackRelease` (`aeager`).
   - *CPU atomics, mutex fast-path & memcpy*: `Atomic/{Increment,Cmpxchg}/{32bit,64bit}`, `Atomic/ContendedCmpxchg/DiffCore`, `Mutex/FastLockUnlock`, `Memcpy/{1000,100000}bytes`, `RandomMemcpy/{64,4096}bytes`, `TicksGet`.
   - *Heap allocator (`aheap` + `aeager`)*: `MallocFree/{100,1024,8192,65536}bytes`, `MemAlloc/Aheap/{AllocAndFree,RetainAndFreeOldest,RetainAndFreeRandom}`.
   - *Shared-frame ring & mailbox floor (`aring` + `amailbox`)*: `Ring/SingleThread/{16,32,64}bytes_{1,4,64}batch`, `Ring/Payload/{64,1024,32768,65536}bytes` (1-core & pinned 2-core), `Mailbox/ThreeSlot/PublishObserve`.
2. **Blocked on pending kernel or runtime wiring**:
   - *Endpoints, notifications, capability transfer & wake scalability*: `Notification/{Signal,WaitAlreadySignaled,QueueWait,RoundTrip_*,WakeOne/*}`, `Endpoint/CallReplyRecv/{0,1}Cap_SameCore`, `Capability/RetypeFree/{Endpoint,Notification,Reply}` (waits for endpoints, replies, and notifications to be wired).
   - *Thread create/join, process spawn & same-core context switch*: `Thread/CreateStartJoin`, `Process/SpawnWait`, `ContextSwitch/{SameProcess,CrossProcess}` (waits for notification wakeup; later reflects predictor/L1D flush and directed `switch`).
   - *User pager & demand faults*: `UserPager/PageFault/Sequential`, `UserPager/BatchedFault`, `UserPager/EvictAndRefault`, `UserPager/MapUnmapWithFaults` (waits for fault IPC delivery and the standard S3-FIFO user pager library).
   - *Calibrated clock, TSC-deadline timer & sleep floor*: `ClockGetMonotonic`, `Timer/1msWait/Deadline`, `Sleep/{0,10,100,1000,10000}ns` (waits for `astd` nanosecond clock/sleep and the tickless absolute-TSC timer capability).

## Context

Today performance numbers in `dom0` are one-shot prints beside historical values (`null`, `4k` map loop, `retype` threads) with no shared harness, no warm-up, no distribution statistics, and no machine-readable baseline across commits. Meanwhile `kernel/verified` has implemented capability lifecycle, memory mapping/probing, processes, threads, `place`/`start`/`suspend`/`destroy`, and multi-core boot (`x86_64` and `aarch64`), plus `aheap`, `aeager`, `aring`, `amailbox`, `afanin`, and `pager-policy` as verified libraries—while IPC (`Send`/`Receive`/`Call`/`ReplyRecv`/notifications), interrupts/timers, fault IPC, and the user-space runtime (`pager`, calibrated clock/sleep) remain active work.

Cataloguing an existing published benchmark suite preserves coverage of every primitive a microkernel gets judged on without inventing bespoke tests piecemeal, and pinning the runner contract now allows immediately runnable groups (`aheap`, `aring`, `MMU`, capability lifecycle, atomics) to build history before IPC and paging land.

## Reasoning

- **Interpretive mapping over translation**: Fuchsia benchmarks assume Zircon's VMO, VMAR, 64 KiB buffered channels, handle refcounting, and per-waitee port packets. Translating those literally either fails to compile or invents POSIX/Zircon compatibility shims that violate Atmosphere's design. Splitting `channels.cc` into unbuffered 5-word register `Endpoint` rendezvous and shared-frame `aring` bulk transfer measures what Atmosphere actually executes.
- **`fuchsiaperf.json` runtime format over `performance-results-schema.json`**: Although `performance-results-schema.json` documents an older `{"label", "unit", "samples": [...]}` object, `perftest`'s C++ implementation (`results.cc`, `results-test.cc`) and Fuchsia's own benchmark docs use `[{"label", "test_suite", "unit", "values"}]`. Matching the runtime serializer lets Fuchsia and Atmosphere outputs feed one comparison script unmodified.
- **Separate timing runs from `--counters` runs**: Under KVM, enabling `pmu=on` adds substantial exit latency (observed 3x slower flush IPIs). Emitting `"nanoseconds"` under non-`pmu` pinned runs and deterministic PMU counts (`.instructions`, `.cycles`, `.fills`, `.ccx_fills`) under `--counters` preserves valid cross-kernel latency comparisons while still providing instruction-level regression signal.
- **No dynamic allocation or UART print inside timed regions**: Pre-faulting sample vectors and printing strictly after the suite follows `perftest`'s anti-noise design cleanly inside a `no_std` single-address-space bootstrap binary where serial output is synchronous kernel I/O.

## Alternatives rejected

- **Porting Fuchsia's C++ suite into a POSIX/Zircon shim layer**: Rejected because Atmosphere's native ABI intentionally omits POSIX/Zircon handle tables, buffered channels, VMOs, VMAR trees, and futex hash tables; benchmarking a shim would hide the native fast paths (`aring`, 5-word registers, user-space `aeager`/`aheap`/`pager`).
- **Emitting only raw TSC cycles instead of `"nanoseconds"` + companion PMU objects**: Rejected because raw TSC cycles depend on host CPU base frequency and cannot join directly against Fuchsia's `"nanoseconds"` output (`Clock` conversion + `.tsc_cycles`/PMU companion entries keep both).
- **Enabling `RDPMC` counters inside the latency-comparison boot**: Rejected because KVM's virtualized PMU distorts kernel-exit and IPI timings by ~3x, invalidating any latency comparison against Fuchsia's non-vPMU QEMU/KVM run.

## What this does not settle

- **Barrelfish `usr/bench` mapping**: cross-core capability agreement protocols (`distops`), `ump_bench`, `lrpc_bench`, and multikernel vs single-instance comparisons will be added beside Fuchsia's table in the companion Barrelfish mapping.
- **Multi-process benchmark packaging**: whether `Process/SpawnWait`, two-process `aring`, and cross-process context switching compile test payloads as separate ELF binaries loaded by a tiny runner harness or reuse multiple entry symbols over shared text frames (before `std` and loader packaging settle).
- **Host TSC frequency source inside `dom0`**: until the user-space monotonic clock exposes calibrated TSC frequency from ACPI/CPUID/`cntfrq_el0`, `tools/bench.py` can convert `.tsc_cycles` or feed the pinned host's invariant TSC rate when producing comparable `"nanoseconds"` JSON alongside guest-calibrated numbers.
